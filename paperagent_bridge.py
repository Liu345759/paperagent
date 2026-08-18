"""Local API for paperagent_v59.html — live six-step results from arXiv, Semantic Scholar, and uploads."""

from __future__ import annotations

import base64
import csv
import html
import io
import json
import math
import os
import re
import statistics
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import zipfile
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent
HTML_FILE = ROOT / "paperagent_v59.html"
HISTORY_DIR = ROOT / "paper_history"
HOST = "127.0.0.1"
PORT = 8766
ARXIV = "http://export.arxiv.org/api/query"
ATOM = "{http://www.w3.org/2005/Atom}"
S2_SEARCH = "https://api.semanticscholar.org/graph/v1/paper/search"
S2_FIELDS = "title,authors,venue,year,abstract,citationCount,externalIds,url,publicationDate,journal"
_S2_LAST = 0.0


def h(text) -> str:
    return html.escape("" if text is None else str(text), quote=True)


YEAR_SPAN_RE = re.compile(
    r"(?:从|介于|between)?\s*(19\d{2}|20\d{2})\s*年?\s*"
    r"(?:到|至|-|—|–|~|/|and|to|和|与)\s*"
    r"(19\d{2}|20\d{2})\s*年?(?:之间|间|以内|期间)?",
    re.I,
)


def parse_year_range(*texts) -> tuple[int | None, int | None]:
    blob = " ".join(str(t or "") for t in texts)
    this = date.today().year
    m = YEAR_SPAN_RE.search(blob)
    if m:
        lo, hi = int(m.group(1)), int(m.group(2))
        return (min(lo, hi), max(lo, hi))
    m = re.search(r"(?:近|最近)\s*(\d+)\s*年", blob)
    if m:
        n = max(1, int(m.group(1)))
        return (this - n + 1, this)
    m = re.search(r"(19\d{2}|20\d{2})\s*(?:年)?\s*(?:以后|以来|之后|及以后|起)", blob)
    if m:
        return (int(m.group(1)), this)
    m = re.search(r"(?:after|since|from)\s*(19\d{2}|20\d{2})", blob, re.I)
    if m:
        return (int(m.group(1)), this)
    return (None, None)


def strip_year_constraints(text: str) -> str:
    t = text or ""
    t = YEAR_SPAN_RE.sub(" ", t)
    t = re.sub(r"(?:论文)?(?:的)?(?:发表)?年份\s*(?:要在|限制在|限定在|范围[为是在]?|介于)?", " ", t)
    t = re.sub(r"(?:近|最近)\s*\d+\s*年", " ", t)
    t = re.sub(r"(19\d{2}|20\d{2})\s*(?:年)?\s*(?:以后|以来|之后|及以后|起)", " ", t)
    t = re.sub(r"(?:after|since|from)\s*(19\d{2}|20\d{2})", " ", t, flags=re.I)
    t = re.sub(r"(?:between)\s*(19\d{2}|20\d{2})\s*(?:and)\s*(19\d{2}|20\d{2})", " ", t, flags=re.I)
    return re.sub(r"\s+", " ", t).strip()


def year_ok(paper: dict, lo: int | None, hi: int | None) -> bool:
    if not lo and not hi:
        return True
    y = paper_year(paper)
    if y is None:
        return False
    if lo and y < lo:
        return False
    if hi and y > hi:
        return False
    return True


def arxiv_date_clause(lo: int | None, hi: int | None) -> str:
    if not lo:
        return ""
    end = hi or date.today().year
    return "submittedDate:[%s01010000 TO %s12312359]" % (lo, end)


def paper_year(paper: dict) -> int | None:
    y = (paper or {}).get("year")
    if y in (None, ""):
        pub = str((paper or {}).get("published") or "")
        m = re.search(r"(19\d{2}|20\d{2})", pub)
        y = m.group(1) if m else None
    try:
        return int(y) if y not in (None, "") else None
    except (TypeError, ValueError):
        return None


def norm_title(title: str) -> str:
    t = re.sub(r"[^a-z0-9\u4e00-\u9fff]+", " ", (title or "").lower())
    return re.sub(r"\s+", " ", t).strip()


def paper_identity_keys(paper: dict) -> set[str]:
    keys: set[str] = set()
    aid = str((paper or {}).get("arxiv_id") or "").strip().lower()
    doi = str((paper or {}).get("doi") or "").strip().lower()
    title = norm_title((paper or {}).get("title") or "")
    if aid:
        keys.add(aid)
        keys.add("arxiv:" + aid)
    if doi:
        keys.add(doi)
        keys.add("doi:" + doi)
    if title:
        keys.add("title:" + title)
    return keys


def paper_merge_key(paper: dict) -> str:
    aid = str((paper or {}).get("arxiv_id") or "").strip().lower()
    if aid:
        return "arxiv:" + aid
    doi = str((paper or {}).get("doi") or "").strip().lower()
    if doi:
        return "doi:" + doi
    return "title:" + norm_title((paper or {}).get("title") or "")


def parse_cite_nums(text: str) -> set[int]:
    out: set[int] = set()
    for inner in re.findall(r"\[([^\[\]]+)\]", text or ""):
        chunk = inner.strip()
        if not re.fullmatch(r"[\d\s,，\-–]+", chunk):
            continue
        for part in re.split(r"[,，]", chunk):
            part = part.strip()
            m = re.fullmatch(r"(\d+)\s*[-–]\s*(\d+)", part)
            if m:
                a, b = int(m.group(1)), int(m.group(2))
                out.update(range(min(a, b), max(a, b) + 1))
            elif part.isdigit():
                out.add(int(part))
    return out


def min_cite_count(n: int, ratio: float = 0.5) -> int:
    n = int(n or 0)
    if n <= 0:
        return 0
    if n <= 2:
        return n
    return max(3, min(n, math.ceil(n * ratio)))


def closure_check(papers: list, paper_html: str, question: str, note: str, instruction: str = "") -> dict:
    items = [p for p in (papers or []) if isinstance(p, dict)]
    n = len(items)
    lo, hi = parse_year_range(question, note, instruction)
    problems: list[str] = []
    if n == 0:
        return {"ok": False, "status": "fail", "detail": "闭环检验未通过：没有可用于闭合的文献。"}
    missing = sum(1 for p in items if not (p.get("doi") or p.get("arxiv_id")))
    if missing:
        problems.append(f"{missing} 篇缺少 DOI 或 arXiv 编号")
    if lo or hi:
        bad = [p for p in items if not year_ok(p, lo, hi)]
        if bad:
            label = f"{lo or '—'}–{hi or '—'}"
            problems.append(f"{len(bad)} 篇不在要求年份 {label}")
    body = paper_html or ""
    split_at = re.search(r"参考文献", body)
    if split_at:
        body = body[: split_at.start()]
    cites = parse_cite_nums(body)
    valid = {i for i in cites if 1 <= i <= n}
    dangling = {i for i in cites if i < 1 or i > n}
    if dangling:
        problems.append("正文引用编号对不上文献列表")
    need = min_cite_count(n)
    if n >= 3 and len(valid) < need:
        problems.append(f"正文引用不足（至少 {need} 篇，当前 {len(valid)} 篇）")
    if problems:
        return {"ok": False, "status": "fail", "detail": "闭环检验未通过：" + "；".join(problems) + "。"}
    if lo or hi:
        return {
            "ok": True,
            "status": "pass",
            "detail": f"闭环检验通过：文献可溯源，年份在 {lo or '—'}–{hi or '—'}。",
        }
    return {"ok": True, "status": "pass", "detail": "闭环检验通过：文献可溯源，引用编号闭合。"}


def fill_year_range(papers: list, question: str, note: str, instruction: str = "", limit: int = 12) -> list[dict]:
    lo, hi = parse_year_range(question, note, instruction)
    kept = [p for p in (papers or []) if isinstance(p, dict) and p.get("title") and year_ok(p, lo, hi)]
    if not lo and not hi:
        return kept
    if len(kept) >= max(6, min(limit, 8)):
        return kept[: max(limit, len(kept))]
    exclude = list(paper_identity_keys(p) for p in kept)
    skip = [k for keys in exclude for k in keys]
    extra, _ = search_topic(question, note, limit=max(limit, 14), exclude=skip)
    seen: set[str] = set()
    for p in kept:
        seen.update(paper_identity_keys(p))
    for p in extra:
        keys = paper_identity_keys(p)
        if keys & seen or not year_ok(p, lo, hi):
            continue
        kept.append(p)
        seen.update(keys)
        if len(kept) >= limit:
            break
    return kept


def search_arxiv(query: str, limit: int = 10, start: int = 0, sort_by: str = "relevance") -> list[dict]:
    if sort_by not in {"relevance", "lastUpdatedDate", "submittedDate"}:
        sort_by = "relevance"
    start = max(0, int(start or 0))
    params = urllib.parse.urlencode(
        {
            "search_query": f"all:{query}",
            "start": start,
            "max_results": limit,
            "sortBy": sort_by,
            "sortOrder": "descending",
        }
    )
    req = urllib.request.Request(
        f"{ARXIV}?{params}",
        headers={"User-Agent": "paperagent-bridge/0.1"},
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        xml_text = resp.read().decode("utf-8", errors="replace")

    root = ET.fromstring(xml_text)
    papers: list[dict] = []
    for entry in root.findall(f"{ATOM}entry"):
        title = " ".join((entry.findtext(f"{ATOM}title") or "").split())
        summary = " ".join((entry.findtext(f"{ATOM}summary") or "").split())
        authors = [
            (author.findtext(f"{ATOM}name") or "").strip()
            for author in entry.findall(f"{ATOM}author")
        ]
        published = entry.findtext(f"{ATOM}published") or ""
        year_match = re.search(r"(\d{4})", published)
        link = ""
        for node in entry.findall(f"{ATOM}link"):
            href = node.attrib.get("href") or ""
            if node.attrib.get("rel") == "alternate" or node.attrib.get("type") == "text/html":
                link = href
        doi = ""
        doi_node = entry.find("{http://arxiv.org/schemas/atom}doi")
        if doi_node is not None and doi_node.text:
            doi = doi_node.text.strip()
        arxiv_id = (entry.findtext(f"{ATOM}id") or "").rsplit("/", 1)[-1]
        papers.append(
            {
                "title": title,
                "authors": [a for a in authors if a],
                "year": int(year_match.group(1)) if year_match else None,
                "published": (published or "")[:10],
                "doi": doi,
                "journal": "arXiv",
                "url": link or (f"https://arxiv.org/abs/{arxiv_id}" if arxiv_id else ""),
                "source": "arxiv",
                "arxiv_id": arxiv_id,
                "abstract": summary[:4000],
            }
        )
    return papers


GLOSSARY = [
    ("类地行星", "terrestrial planet"),
    ("岩石行星", "rocky planet"),
    ("地外行星", "exoplanet"),
    ("系外行星", "exoplanet"),
    ("感应磁场", "induced magnetic field"),
    ("电磁感应", "electromagnetic induction"),
    ("磁感应", "magnetic induction"),
    ("磁层", "magnetosphere"),
    ("电离层", "ionosphere"),
    ("电导率", "electrical conductivity"),
    ("导电性", "electrical conductivity"),
    ("内部结构", "interior structure"),
    ("木卫二", "Europa"),
    ("木卫三", "Ganymede"),
    ("木卫四", "Callisto"),
    ("欧罗巴", "Europa"),
    ("磁场", "magnetic field"),
    ("火星", "Mars"),
    ("金星", "Venus"),
    ("水星", "Mercury"),
    ("地球", "Earth"),
    ("卫星", "satellite moon"),
    ("行星", "planet"),
    ("感应", "induction"),
    ("文献综述", ""),
    ("综述", ""),
]

SEARCH_STOP = {
    "the", "and", "for", "with", "from", "that", "this", "are", "was", "were",
    "review", "literature", "survey", "study", "based", "using", "into", "about",
}

# Longest-first English → Chinese for restating abstracts, not for search.
ZH_PHRASES = [
    ("terrestrial planets", "类地行星"),
    ("terrestrial planet", "类地行星"),
    ("induced magnetic field", "感应磁场"),
    ("induced field", "感应场"),
    ("inducing field", "感应外场"),
    ("induced", "感应"),
    ("electromagnetic induction", "电磁感应"),
    ("magnetic induction", "磁感应"),
    ("electrical conductivity", "电导率"),
    ("crustal conductivity", "地壳电导率"),
    ("interior structure", "内部结构"),
    ("magnetic field", "磁场"),
    ("magnetometer flybys", "磁强计飞越观测"),
    ("magnetometer data", "磁强计数据"),
    ("nightside observations", "夜侧观测"),
    ("inducing spectrum", "感应频谱"),
    ("water layers", "含水层"),
    ("ionospheric currents", "电离层电流"),
    ("rocky planet", "岩石行星"),
    ("the results show that", "结果表明"),
    ("results indicate that", "结果表明"),
    ("we demonstrate that", "研究表明"),
    ("we show that", "研究表明"),
    ("we find that", "研究发现"),
    ("we found that", "研究发现"),
    ("this paper investigates", "本文考察"),
    ("this work investigates", "本文考察"),
    ("this paper presents", "本文给出"),
    ("this paper studies", "本文研究"),
    ("we investigate", "考察"),
    ("we present", "给出"),
    ("we propose", "提出"),
    ("we develop", "建立"),
    ("we measure", "测量"),
    ("we use", "采用"),
    ("based on", "基于"),
    ("in order to", "以便"),
    ("however", "但"),
    ("nevertheless", "尽管如此"),
    ("remain limited", "仍受限制"),
    ("poorly constrained", "约束较弱"),
    ("not well constrained", "约束不足"),
    ("open question", "仍待解决"),
    ("numerical model", "数值模型"),
    ("forward model", "正演模型"),
    ("inverse model", "反演模型"),
    ("induction equation", "感应方程"),
    ("conductivity profile", "电导率剖面"),
    ("interior constraints", "内部约束"),
    ("sparse", "稀少的"),
    ("amplitude", "幅度"),
    ("controls", "控制"),
    ("constrain", "约束"),
    ("constrained", "被约束"),
    ("magnetosphere", "磁层"),
    ("ionosphere", "电离层"),
    ("exoplanet", "系外行星"),
    ("satellite", "卫星"),
    ("conductivity", "电导率"),
    ("induction", "感应"),
    ("magnetometer", "磁强计"),
    ("simulation", "模拟"),
    ("observations", "观测"),
    ("observation", "观测"),
    ("measurement", "测量"),
    ("measurements", "测量"),
    ("estimate", "估计"),
    ("estimated", "估计得到"),
    ("detect", "探测"),
    ("detected", "探测到"),
    ("model", "模型"),
    ("models", "模型"),
    ("method", "方法"),
    ("approach", "方法"),
    ("using", "采用"),
    ("planet", "行星"),
    ("planets", "行星"),
    ("mars", "火星"),
    ("martian", "火星"),
    ("venusian", "金星"),
    ("conductivity model", "电导率模型"),
    ("build", "建立"),
    ("develop", "建立"),
    ("construct", "建立"),
    ("venus", "金星"),
    ("mercury", "水星"),
    ("earth", "地球"),
    ("europa", "木卫二"),
    ("ganymede", "木卫三"),
    ("callisto", "木卫四"),
    ("moon", "月球"),
    ("interior", "内部"),
    ("crustal", "地壳"),
    ("crust", "地壳"),
    ("core", "核"),
    ("mantle", "地幔"),
    ("field", "场"),
    ("fields", "场"),
    ("current", "电流"),
    ("currents", "电流"),
    ("layer", "层"),
    ("layers", "层"),
    ("ocean", "海洋"),
    ("water", "水"),
    ("flybys", "飞越"),
    ("flyby", "飞越"),
]

ZH_WORDS = {
    "show": "表明", "shown": "表明", "find": "发现", "found": "发现",
    "suggest": "表明", "indicate": "表明", "conclude": "得出",
    "reveal": "揭示", "obtain": "得到", "obtained": "得到",
    "study": "研究", "studied": "研究了", "analyze": "分析",
    "analyse": "分析", "compare": "比较", "compared": "比较了",
    "provide": "给出", "provided": "给出", "allow": "使得",
    "can": "能够", "may": "可能", "might": "可能",
    "if": "若", "when": "当", "where": "其中", "while": "同时",
    "and": "与", "or": "或", "but": "但", "not": "不",
    "from": "来自", "into": "进入", "with": "结合", "without": "在没有",
    "between": "之间", "over": "在", "under": "在", "within": "在",
    "known": "已知", "unknown": "未知", "limited": "有限",
    "strong": "强", "weak": "弱", "high": "高", "low": "低",
    "large": "大", "small": "小", "new": "新的",
    "our": "", "their": "", "its": "", "this": "", "these": "",
    "that": "", "those": "", "such": "", "than": "于",
    "also": "还", "both": "两者", "more": "更", "most": "最",
    "very": "", "highly": "高度", "mainly": "主要",
    "in": "在", "on": "在", "for": "用于", "to": "", "of": "",
    "a": "", "an": "", "the": "", "as": "作为", "by": "通过",
    "we": "", "is": "", "are": "", "was": "", "were": "",
    "be": "", "been": "", "being": "", "has": "", "have": "",
    "had": "", "do": "", "does": "", "did": "",
}

DROP_EN = ZH_WORDS  # used as skip-empty map
ACRONYMS = {
    "MHD", "EM", "MAVEN", "MESSENGER", "INSIGHT", "JUNO", "MGS",
    "BEPICOLOMBO", "VEX", "MEX", "THEMIS", "CLUSTER", "SWARM",
}


def to_english_query(text: str) -> str:
    mapped = " " + (text or "").strip() + " "
    for zh, en in sorted(GLOSSARY, key=lambda x: len(x[0]), reverse=True):
        mapped = mapped.replace(zh, f" {en} " if en else " ")
    mapped = re.sub(r"[\u4e00-\u9fff]", " ", mapped)
    return " ".join(mapped.split())


def topic_terms(question: str, note: str = "") -> list[str]:
    en = to_english_query(f"{question} {note}".strip())
    words = [w.lower() for w in re.findall(r"[A-Za-z][A-Za-z\-]+", en)]
    terms = []
    for w in words:
        if len(w) < 4 or w in SEARCH_STOP:
            continue
        if w not in terms:
            terms.append(w)
    return terms[:8]


def paper_blob(paper: dict) -> str:
    return f"{paper.get('title') or ''} {paper.get('abstract') or ''} {paper.get('fulltext') or ''}".lower()


def score_paper(paper: dict, terms: list[str]) -> int:
    blob = paper_blob(paper)
    score = sum(1 for t in terms if t in blob)
    planetish = bool(re.search(r"planet|mars|venus|mercury|europa|ganymede|callisto|\bmoon\b|\bearth\b", blob))
    if re.search(r"\binduct", blob) and planetish:
        score += 3
    if re.search(r"conductiv", blob) and planetish:
        score += 2
    if re.search(r"magnetospher|ionospher", blob) and planetish:
        score += 1
    return score


def s2_api_key() -> str:
    return (os.environ.get("SEMANTIC_SCHOLAR_API_KEY") or "").strip()


def s2_request(params: dict, timeout: int = 12) -> dict | None:
    global _S2_LAST
    wait = 1.05 - (time.monotonic() - _S2_LAST)
    if wait > 0:
        time.sleep(wait)
    headers = {"User-Agent": "paperagent-bridge/0.3"}
    key = s2_api_key()
    if key:
        headers["x-api-key"] = key
    qs = urllib.parse.urlencode(params)
    req = urllib.request.Request(f"{S2_SEARCH}?{qs}", headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            _S2_LAST = time.monotonic()
            if getattr(resp, "status", 200) >= 400:
                return None
            return json.loads(resp.read().decode("utf-8", "replace"))
    except urllib.error.HTTPError as exc:
        _S2_LAST = time.monotonic()
        if exc.code == 429:
            time.sleep(1.5)
            try:
                with urllib.request.urlopen(req, timeout=timeout) as resp:
                    return json.loads(resp.read().decode("utf-8", "replace"))
            except Exception:
                return None
        return None
    except Exception:
        _S2_LAST = time.monotonic()
        return None


def paper_from_s2(item: dict) -> dict | None:
    if not isinstance(item, dict) or not item.get("title"):
        return None
    ext = item.get("externalIds") if isinstance(item.get("externalIds"), dict) else {}
    doi = str(ext.get("DOI") or "").strip()
    arxiv_id = str(ext.get("ArXiv") or "").strip()
    authors = []
    for author in item.get("authors") or []:
        if isinstance(author, dict) and author.get("name"):
            authors.append(str(author["name"]).strip())
        elif isinstance(author, str) and author.strip():
            authors.append(author.strip())
    journal = str(item.get("venue") or "").strip()
    jinfo = item.get("journal")
    if isinstance(jinfo, dict):
        journal = journal or str(jinfo.get("name") or "").strip()
    try:
        year = int(item["year"]) if item.get("year") not in (None, "") else None
    except (TypeError, ValueError):
        year = None
    pub = str(item.get("publicationDate") or "")[:10]
    url = str(item.get("url") or "").strip()
    if not url and doi:
        url = "https://doi.org/" + doi
    if not url and arxiv_id:
        url = "https://arxiv.org/abs/" + arxiv_id
    return {
        "title": " ".join(str(item.get("title")).split()),
        "authors": authors,
        "year": year,
        "published": pub,
        "doi": doi,
        "journal": journal or "Semantic Scholar",
        "url": url,
        "source": "semantic-scholar",
        "arxiv_id": arxiv_id,
        "abstract": re.sub(r"\s+", " ", str(item.get("abstract") or ""))[:4000],
        "citation_count": item.get("citationCount") or 0,
    }


def merge_s2_into(dst: dict, src: dict) -> None:
    if not dst.get("doi") and src.get("doi"):
        dst["doi"] = src["doi"]
    if not dst.get("year") and src.get("year"):
        dst["year"] = src["year"]
    if not dst.get("published") and src.get("published"):
        dst["published"] = src["published"]
    if src.get("citation_count"):
        dst["citation_count"] = src["citation_count"]
    if not dst.get("url") and src.get("url"):
        dst["url"] = src["url"]
    if not dst.get("arxiv_id") and src.get("arxiv_id"):
        dst["arxiv_id"] = src["arxiv_id"]
    if not dst.get("abstract") and src.get("abstract"):
        dst["abstract"] = src["abstract"]


def search_s2(query: str, year_lo: int | None = None, year_hi: int | None = None, limit: int = 12) -> list[dict]:
    query = re.sub(r"\s+", " ", (query or "").strip())
    if not query:
        return []
    params = {
        "query": query[:300],
        "limit": min(max(int(limit or 10), 1), 20),
        "fields": S2_FIELDS,
    }
    if year_lo or year_hi:
        lo = year_lo or 1900
        hi = year_hi or date.today().year
        params["year"] = f"{lo}-{hi}"
    data = s2_request(params)
    if not isinstance(data, dict):
        return []
    out: list[dict] = []
    for item in data.get("data") or []:
        paper = paper_from_s2(item)
        if paper:
            out.append(paper)
    return out


def absorb_s2_papers(seen: dict[str, dict], extras: list[dict]) -> None:
    by_title = {norm_title(p.get("title") or ""): p for p in seen.values() if p.get("title")}
    for extra in extras or []:
        if not extra.get("title"):
            continue
        title = norm_title(extra.get("title") or "")
        matched = by_title.get(title)
        if not matched:
            for old in seen.values():
                if paper_identity_keys(old) & paper_identity_keys(extra):
                    matched = old
                    break
        if matched:
            merge_s2_into(matched, extra)
            continue
        key = paper_merge_key(extra)
        seen.setdefault(key, extra)
        by_title[title] = extra


def search_arxiv_raw(search_query: str, limit: int = 15, start: int = 0, sort_by: str = "relevance") -> list[dict]:
    if sort_by not in {"relevance", "lastUpdatedDate", "submittedDate"}:
        sort_by = "relevance"
    params = urllib.parse.urlencode(
        {
            "search_query": search_query,
            "start": max(0, int(start or 0)),
            "max_results": limit,
            "sortBy": sort_by,
            "sortOrder": "descending",
        }
    )
    req = urllib.request.Request(
        f"{ARXIV}?{params}",
        headers={"User-Agent": "paperagent-bridge/0.1"},
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        xml_text = resp.read().decode("utf-8", errors="replace")
    # reuse parser by temporarily calling search_arxiv's XML walk via a dummy
    root = ET.fromstring(xml_text)
    papers: list[dict] = []
    for entry in root.findall(f"{ATOM}entry"):
        title = " ".join((entry.findtext(f"{ATOM}title") or "").split())
        summary = " ".join((entry.findtext(f"{ATOM}summary") or "").split())
        authors = [
            (author.findtext(f"{ATOM}name") or "").strip()
            for author in entry.findall(f"{ATOM}author")
        ]
        published = entry.findtext(f"{ATOM}published") or ""
        year_match = re.search(r"(\d{4})", published)
        link = ""
        for node in entry.findall(f"{ATOM}link"):
            href = node.attrib.get("href") or ""
            if node.attrib.get("rel") == "alternate" or node.attrib.get("type") == "text/html":
                link = href
        doi = ""
        doi_node = entry.find("{http://arxiv.org/schemas/atom}doi")
        if doi_node is not None and doi_node.text:
            doi = doi_node.text.strip()
        arxiv_id = (entry.findtext(f"{ATOM}id") or "").rsplit("/", 1)[-1]
        papers.append(
            {
                "title": title,
                "authors": [a for a in authors if a],
                "year": int(year_match.group(1)) if year_match else None,
                "published": (published or "")[:10],
                "doi": doi,
                "journal": "arXiv",
                "url": link or (f"https://arxiv.org/abs/{arxiv_id}" if arxiv_id else ""),
                "source": "arxiv",
                "arxiv_id": arxiv_id,
                "abstract": summary[:4000],
            }
        )
    return papers


OFFTOPIC_RE = re.compile(
    r"underwater|tri-axis coil|wireless communication|power line|"
    r"cosmic rays?|uhecr|ultra high energy|"
    r"cyclotron maser|compact binar|"
    r"hot jupiter|"
    r"rfid|antenna coil|undersea|acoustic communication",
    re.I,
)


def search_topic(question: str, note: str = "", limit: int = 10, start: int = 0, sort_by: str = "relevance", exclude: list | None = None) -> tuple[list[dict], str]:
    year_lo, year_hi = parse_year_range(question, note)
    q_search = strip_year_constraints(question)
    n_search = strip_year_constraints(note)
    raw = f"{q_search} {n_search}".strip() or f"{question} {note}".strip()
    en = to_english_query(raw) or raw
    terms = topic_terms(q_search, n_search)
    words = [w for w in en.split() if len(w) > 2 and w.lower() not in SEARCH_STOP]
    core_a = {"planet", "terrestrial", "mars", "venus", "mercury", "europa", "exoplanet", "moon", "ganymede"}
    core_b = {"magnetic", "induction", "magnetosphere", "conductivity", "ionosphere"}
    need_a = any(t in core_a for t in terms)
    need_b = any(t in core_b for t in terms)
    date_q = arxiv_date_clause(year_lo, year_hi)
    queries = []
    if words:
        queries.append(" AND ".join(f"all:{w}" for w in words[:6]))
        queries.append("all:" + " ".join(words[:8]))
    if need_b:
        mag_q = [
            'all:"magnetic induction" AND (all:planet OR all:mars OR all:venus OR all:mercury OR all:europa OR all:moon)',
            "all:electromagnetic AND all:induction AND (all:planet OR all:europa OR all:mars OR all:ganymede)",
            "all:conductivity AND all:magnetic AND (all:planet OR all:interior OR all:europa)",
            "all:induced AND all:magnetic AND all:field AND (all:europa OR all:ganymede OR all:callisto OR all:mars)",
            "all:magnetotelluric AND (all:mars OR all:moon OR all:planet)",
        ]
        queries = mag_q + queries
    elif any(w.lower() in core_a for w in words):
        queries.append("cat:astro-ph.EP AND all:" + " ".join(words[:5]))
    if not queries:
        queries.append(f"all:{raw}")
    if date_q:
        queries = [f"({q}) AND {date_q}" for q in queries] + queries

    seen: dict[str, dict] = {}
    starts = [start] + ([start + 10, start + 20, start + 30, start + 40] if year_lo else [])
    for q in queries:
        for st in starts:
            try:
                batch = search_arxiv_raw(q, limit=max(limit, 20), start=st, sort_by=sort_by)
            except Exception:
                continue
            for p in batch:
                seen.setdefault(p.get("arxiv_id") or p.get("title") or str(len(seen)), p)
    try:
        s2_query = " ".join(words[:8]) if words else en
        absorb_s2_papers(seen, search_s2(s2_query, year_lo, year_hi, limit=max(limit, 10)))
    except Exception:
        pass
    papers = list(seen.values())
    for p in papers:
        blob = paper_blob(p)
        p["score"] = score_paper(p, terms) if terms else 0
        if need_a and not any(k in blob for k in core_a):
            p["score"] = 0
        if need_b and not re.search(r"\binduct|conductiv|magnetospher|ionospher", blob):
            p["score"] = 0
        if OFFTOPIC_RE.search(blob):
            p["score"] = 0
        if not year_ok(p, year_lo, year_hi):
            p["score"] = 0
    papers.sort(key=lambda p: (-(p.get("score") or 0), -(p.get("year") or 0)))
    keep = [p for p in papers if (p.get("score") or 0) >= 2 and year_ok(p, year_lo, year_hi)]
    if not need_b and len(keep) < 4:
        keep = [p for p in papers if (p.get("score") or 0) >= 1 and year_ok(p, year_lo, year_hi)]
    if need_b:
        keep = [
            p
            for p in papers
            if (p.get("score") or 0) >= 1
            and year_ok(p, year_lo, year_hi)
            and re.search(r"\binduct|conductiv|magnetospher|ionospher", paper_blob(p))
            and not OFFTOPIC_RE.search(paper_blob(p))
        ]
        keep = keep[:14]
    if exclude:
        skip = {str(x).strip().lower() for x in exclude if x}
        keep = [
            p
            for p in keep
            if not (paper_identity_keys(p) & skip)
            and str(p.get("arxiv_id") or "").lower() not in skip
        ]
    keep = [p for p in keep if year_ok(p, year_lo, year_hi)]
    return keep[: max(limit, 8 if need_b else limit)], en


def short_title(paper: dict, n: int = 72) -> str:
    return " ".join((paper.get("title") or "Untitled").split())[:n]


def repair_literature(question: str, note: str, current: list, limit: int = 12, rerun: int = 0) -> tuple[list[dict], str, dict]:
    """Keep on-topic papers, drop off-topic ones, then fill with new on-topic hits."""
    terms = topic_terms(question, note)
    keep: list[dict] = []
    drop: list[dict] = []
    year_lo, year_hi = parse_year_range(question, note)
    for p in current or []:
        if not isinstance(p, dict) or not p.get("title"):
            continue
        blob = paper_blob(p)
        p["score"] = score_paper(p, terms) if terms else int(p.get("score") or 0)
        d = fluent_digest(p, question, note)
        p["digest"] = d
        weak = (p["score"] or 0) <= 0 or not d.get("finding")
        bad = bool(
            d.get("off_topic")
            or OFFTOPIC_RE.search(blob)
            or weak
            or not year_ok(p, year_lo, year_hi)
        )
        (drop if bad else keep).append(p)
    keep.sort(key=lambda x: (-(x.get("score") or 0), -(x.get("year") or 0)))

    exclude: list[str] = []
    for p in keep + drop:
        exclude.extend(paper_identity_keys(p))
    need = max(limit - len(keep), 3 if drop else 2)
    found, en = search_topic(
        question, note, limit=max(limit, 14), start=max(0, int(rerun or 0)) * 6, exclude=exclude
    )
    added: list[dict] = []
    seen: set[str] = set()
    for p in keep:
        seen.update(paper_identity_keys(p))
    for p in found:
        keys = paper_identity_keys(p)
        if keys & seen:
            continue
        d = fluent_digest(p, question, note)
        p["digest"] = d
        if d.get("off_topic") or (p.get("score") or 0) <= 0 or not year_ok(p, year_lo, year_hi):
            continue
        added.append(p)
        seen.update(keys)
        if len(added) >= need:
            break

    # If nothing was off-topic, only swap the weakest keeper when a new paper scores higher.
    if not drop and keep and added:
        swapped = []
        keep_sorted = list(keep)
        for cand in list(added):
            if not keep_sorted:
                break
            worst = keep_sorted[-1]
            if (cand.get("score") or 0) > (worst.get("score") or 0):
                drop.append(worst)
                keep_sorted.pop()
                swapped.append(cand)
        keep = keep_sorted
        added = swapped + [a for a in added if a not in swapped]

    papers = (keep + added)[:limit]
    return papers, en, {
        "kept": len(keep),
        "dropped": [short_title(p) for p in drop],
        "added": [short_title(p) for p in added],
        "dropped_n": len(drop),
        "added_n": len(added),
    }


def gb_author_name(name: str) -> str:
    name = " ".join((name or "").replace(",", " ").split())
    if not name:
        return "佚名"
    if re.search(r"[\u4e00-\u9fff]", name):
        return name
    parts = name.split()
    if len(parts) == 1:
        return parts[0].upper()
    surname = parts[-1].upper()
    initials = " ".join(p[0].upper() + "." for p in parts[:-1] if p)
    return f"{surname} {initials}".strip()


def gb_author_list(authors: list) -> str:
    names = [gb_author_name(a) for a in (authors or []) if a]
    if not names:
        return "佚名"
    text = ", ".join(names[:3])
    if len(names) > 3:
        text += ", 等"
    return text


def gb_t_ref(item: dict, index: int) -> str:
    authors = gb_author_list(item.get("authors") or [])
    title = (item.get("title") or "Untitled").rstrip(".")
    year = item.get("year") or "n.d."
    published = (item.get("published") or "")[:10]
    pub_part = f"({published})" if published else f"({year})"
    cited = date.today().isoformat()
    arxiv_id = item.get("arxiv_id") or ""
    url = item.get("url") or (f"https://arxiv.org/abs/{arxiv_id}" if arxiv_id else "")
    doi = item.get("doi") or ""
    doi_part = f" DOI:{doi}." if doi else ""
    return f"[{index}] {authors}. {title}[EB/OL]. {pub_part}[{cited}]. {url}.{doi_part}"


def cite_list(indices: list[int]) -> str:
    indices = sorted({i for i in indices if i})
    if not indices:
        return ""
    ranges: list[tuple[int, int]] = []
    start = prev = indices[0]
    for n in indices[1:]:
        if n == prev + 1:
            prev = n
            continue
        ranges.append((start, prev))
        start = prev = n
    ranges.append((start, prev))
    parts = [str(a) if a == b else f"{a}-{b}" for a, b in ranges]
    return "[" + ",".join(parts) + "]"


def lead_author(paper: dict) -> str:
    authors = paper.get("authors") or []
    name = gb_author_name(authors[0]) if authors else "已有研究"
    return name + ("等" if len(authors) > 1 else "")


def make_title(question: str) -> str:
    q = re.sub(r"[？?。.!！\s]+$", "", (question or "").strip())
    if not q:
        return "文献综述"
    if re.search(r"[\u4e00-\u9fff]", q):
        if any(k in q for k in ("综述", "进展")):
            return q.replace("综述", "").replace("进展", "").strip() or q
        return q
    return q


def make_keywords(question: str, papers: list[dict]) -> list[str]:
    mag = any(k in (question or "") for k in ("磁感应", "电磁感应", "电导率", "感应磁场", "磁层"))
    if mag:
        kws = ["类地行星磁感应", "电磁感应", "电导率", "导电性", "感应磁场"]
    else:
        parts = [p for p in re.split(r"[\s,，、;；:：/\\？?]+", question or "") if 2 <= len(p) <= 18]
        kws = [p for p in parts[:4] if p not in {"感应", "行星", "综述"}]
    blob = " ".join(paper_body(p) for p in (papers or [])[:6]) + " " + (question or "")
    for zh in objects_zh(blob):
        if zh not in kws and zh not in {"感应", "行星", "场", "层", "水"}:
            kws.append(zh)
    return kws[:8]


def paper_body(paper: dict) -> str:
    if paper.get("fulltext"):
        return paper["fulltext"]
    if paper.get("abstract"):
        return paper["abstract"]
    excerpts = paper.get("excerpts") or []
    if excerpts:
        return " ".join(excerpts)
    return paper.get("title") or ""


def strip_html_text(raw: str) -> str:
    raw = re.sub(r"(?is)<(script|style).*?>.*?</\1>", " ", raw)
    raw = re.sub(r"(?is)<[^>]+>", " ", raw)
    return " ".join(html.unescape(raw).split())


def fetch_arxiv_fulltext(arxiv_id: str) -> tuple[str, str]:
    aid = (arxiv_id or "").split("/")[-1].strip()
    if not aid:
        return "", ""
    urls = [
        f"https://arxiv.org/html/{aid}",
        f"https://ar5iv.labs.arxiv.org/html/{aid}",
    ]
    for url in urls:
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "paperagent-bridge/0.2"})
            with urllib.request.urlopen(req, timeout=12) as resp:
                if getattr(resp, "status", 200) >= 400:
                    continue
                text = strip_html_text(resp.read()[:450000].decode("utf-8", "replace"))
                if len(text) > 500:
                    return text[:14000], "html全文"
        except Exception:
            continue
    return "", ""


def enrich_papers_fulltext(papers: list[dict], limit: int = 6) -> None:
    todo = [
        p
        for p in papers[:limit]
        if p.get("arxiv_id") and len(p.get("fulltext") or "") < 600
    ]
    if not todo:
        for p in papers:
            p.setdefault("fulltext", p.get("abstract") or "")
            p.setdefault("parse_kind", p.get("parse_kind") or "摘要")
        return

    def job(paper: dict) -> tuple[str, str, str]:
        body, kind = fetch_arxiv_fulltext(paper.get("arxiv_id") or "")
        return paper.get("arxiv_id") or "", body, kind

    found: dict[str, tuple[str, str]] = {}
    with ThreadPoolExecutor(max_workers=min(4, len(todo))) as pool:
        for arxiv_id, body, kind in pool.map(job, todo):
            if body:
                found[arxiv_id] = (body, kind)
    for p in papers:
        hit = found.get(p.get("arxiv_id") or "")
        if hit:
            p["fulltext"], p["parse_kind"] = hit
        else:
            p["fulltext"] = p.get("abstract") or ""
            p["parse_kind"] = "摘要（无公开全文）"


def extract_pdf_text(raw: bytes) -> str:
    try:
        from pypdf import PdfReader

        reader = PdfReader(io.BytesIO(raw))
        parts = [(page.extract_text() or "") for page in reader.pages[:40]]
        text = "\n".join(parts).strip()
        if text:
            return text[:20000]
    except Exception:
        pass
    chunks = []
    for block in re.finditer(rb"BT\s*(.*?)\s*ET", raw, re.S):
        for item in re.finditer(rb"\((?:\\.|[^\\)])+\)\s*Tj", block.group(1)):
            piece = item.group(0)[:-2].strip()[1:-1]
            chunks.append(piece.decode("latin-1", "replace").replace("\\n", " "))
    return " ".join(chunks)[:20000]


def extract_docx_text(raw: bytes) -> str:
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as zf:
            xml = zf.read("word/document.xml").decode("utf-8", "replace")
        return " ".join(re.findall(r"<w:t[^>]*>([^<]*)</w:t>", xml))[:20000]
    except Exception:
        return ""


def extract_xlsx_text(raw: bytes) -> str:
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as zf:
            names = zf.namelist()
            if "xl/sharedStrings.xml" not in names:
                return ""
            xml = zf.read("xl/sharedStrings.xml").decode("utf-8", "replace")
            return "\n".join(re.findall(r"<t[^>]*>([^<]*)</t>", xml))[:20000]
    except Exception:
        return ""


def decode_upload_text(item: dict) -> str:
    name = str(item.get("name") or "").lower()
    encoding = str(item.get("encoding") or "")
    data_b64 = str(item.get("data") or "")
    text = str(item.get("text") or "")
    if encoding == "base64" and data_b64:
        try:
            raw = base64.b64decode(data_b64)
        except Exception:
            return text
        if name.endswith(".pdf"):
            return extract_pdf_text(raw)
        if name.endswith(".docx"):
            return extract_docx_text(raw)
        if name.endswith(".xlsx") or name.endswith(".xls"):
            return extract_xlsx_text(raw)
        try:
            return raw.decode("utf-8", "replace")
        except Exception:
            return text
    return text


def first_sentence(text: str) -> str:
    text = (text or "").strip()
    if not text:
        return ""
    parts = re.split(r"(?<=[。.!？?])\s+", text, maxsplit=1)
    return parts[0][:220]


def gap_sentence(text: str) -> str:
    text = (text or "").strip()
    if not text:
        return ""
    parts = re.split(r"(?<=[。.!？?])\s+", text)
    for sent in parts:
        if re.search(
            r"however|remain|uncertain|poorly|limited|unknown|challenge|nevertheless|"
            r"not well|open question|still unclear|不足|未知|不确定|有限",
            sent,
            re.I,
        ):
            return sent[:220]
    return ""


def split_sents(text: str) -> list[str]:
    parts = re.split(r"(?<=[。.!？?])\s+", text or "")
    return [s.strip() for s in parts if len(s.strip()) >= 24]


def is_junk_sent(sent: str) -> bool:
    low = (sent or "").lower().strip()
    if len(low) < 40:
        return True
    if re.match(r"^(figure|table|fig\.|tab\.)\s*\d", low):
        return True
    if re.search(
        r"copyright|all rights reserved|arxiv\.org|corresponding author|"
        r"this paper is organized|keywords:|acknowledg|funding:",
        low,
    ):
        return True
    if re.search(r"\b(prisma|systematic literature review|bibliometric)\b", low) and len(low) < 220:
        return True
    return False


PURPOSE_RE = re.compile(
    r"\b(this paper|this work|this study|we |our aim|the present study)\b.{0,80}\b"
    r"(investigate|study|examine|explore|propose|present|address|focus|consider|aim|develop|introduce)\b",
    re.I,
)
METHOD_RE = re.compile(
    r"\b(model|method|using|based on|simulation|inversion|equation|magnetometer|"
    r"numerical|approach|algorithm|we (use|apply|solve|simulate|develop|derive))\b",
    re.I,
)
FINDING_RE = re.compile(
    r"\b(we (find|show|demonstrate|conclude|obtain)|results? (show|indicate|suggest)|"
    r"found that|indicate that|demonstrate that|reveal|detect|constrain|estimate)\b",
    re.I,
)
def cjk_count(text: str) -> int:
    return len(re.findall(r"[\u4e00-\u9fff]", text or ""))


def clip_zh(text: str, limit: int = 100) -> str:
    text = re.sub(r"\s+", "", (text or "").strip())
    text = text.replace("...", "……")
    if not text:
        return ""
    if len(text) <= limit:
        return text.rstrip("，、；")
    cut = text[:limit]
    for sep in ("。", "；", "，"):
        i = cut.rfind(sep)
        if i >= 20:
            return cut[: i + 1]
    return cut.rstrip("，、；") + "……"


def tidy_zh(text: str) -> str:
    text = (text or "").replace(",", "，").replace(";", "；").replace(".", "。")
    text = re.sub(r"\s+", " ", text).strip()
    text = re.sub(r"([\u4e00-\u9fff])\s+([\u4e00-\u9fff])", r"\1\2", text)
    text = re.sub(r"([\u4e00-\u9fff])\s+([A-Z0-9])", r"\1\2", text)
    text = re.sub(r"([A-Z0-9])\s+([\u4e00-\u9fff])", r"\1\2", text)
    text = re.sub(r"[，；、]{2,}", "，", text)
    text = re.sub(r"。+", "。", text)
    return text.strip("，；、 ")


def leftover_en_words(text: str) -> list[str]:
    words = []
    for w in re.findall(r"[A-Za-z][A-Za-z\-]{3,}", text or ""):
        if w.upper() in ACRONYMS:
            continue
        words.append(w)
    return words


def fix_mojibake(text: str) -> str:
    text = html.unescape(text or "")
    if "\ufffd" in text or "�" in text:
        text = text.replace("\ufffd", "").replace("�", "")
    weird = len(re.findall(r"[ÃÂÄÅÆÇÈÉÌÍÐÑÒÓÕÖØÙÚÛÜÝÞßàáâãäåæçèéêëìíîï]", text))
    if weird >= 2 and cjk_count(text) < 8:
        try:
            repaired = text.encode("latin-1").decode("utf-8")
            if cjk_count(repaired) > cjk_count(text):
                text = repaired
        except Exception:
            pass
    return text


def strip_en_lead(sent: str) -> str:
    sent = " ".join((sent or "").split())
    sent = re.sub(
        r"^(in this paper|in this work|in this study|here|recently|"
        r"in recent years)[,:\s]+",
        "",
        sent,
        flags=re.I,
    )
    sent = re.sub(
        r"^(we|the authors|this study|this paper|this work)\s+"
        r"(presents?|proposes?|investigates?|studies|reports?|shows?|finds?|uses?|develops?|considers?)\s+"
        r"(a |an |the )?",
        "",
        sent,
        flags=re.I,
    )
    sent = re.sub(
        r"^(the results|our results|results)\s+(show|indicate|suggest|demonstrate)\s+(that )?",
        "",
        sent,
        flags=re.I,
    )
    sent = re.sub(
        r"^(however|nevertheless|nonetheless)[,:\s]+",
        "",
        sent,
        flags=re.I,
    )
    return sent.strip(" ;,")


def uniq(items: list[str]) -> list[str]:
    out = []
    for x in items:
        if x and x not in out:
            out.append(x)
    return out


JUNK_ZH = re.compile(
    r"在与|与在|与与|在在|作为通过|通过与|能够结合|但与|与不的|来自，|其中结合|"
    r"发现有限|水来自|采用模型研究|方法作为|电流类地|不的类地|用于，发现|"
    r"与发现|在与发现|作为通过与"
)


def is_fluent_zh(text: str) -> bool:
    t = (text or "").strip()
    if cjk_count(t) < 6:
        return False
    if JUNK_ZH.search(t):
        return False
    if re.search(r"(.{2,8})与\1", t):
        return False
    func = len(re.findall(r"在|与|作为|通过|能够|结合|来自|其中|用于|但是", t))
    if func >= 4:
        return False
    return True


def np_to_zh(en: str) -> str:
    """Map a captured English noun phrase to Chinese terms only. No function-word glue."""
    out = " " + " ".join((en or "").split()) + " "
    for src, zh in sorted(ZH_PHRASES, key=lambda x: len(x[0]), reverse=True):
        if src.lower() in {"using", "however", "build", "develop", "construct"}:
            continue
        out = re.sub(r"\b" + re.escape(src) + r"\b", f" {zh} ", out, flags=re.I)
    bits = []
    for part in re.findall(r"[\u4e00-\u9fff]+|[A-Z]{2,6}|\d[\d.eE+\-]*", out):
        if re.search(r"[\u4e00-\u9fff]", part):
            bits.append(part)
        elif part.upper() in ACRONYMS:
            bits.append(part.upper())
    bits = uniq(bits)
    planets = [x for x in bits if x in {"火星", "金星", "水星", "地球", "木卫二", "木卫三", "木卫四", "月球"}]
    others = [x for x in bits if x not in planets and x not in {"感应", "行星", "场", "层", "水"}]
    rest = ""
    for x in others:
        if not rest:
            rest = x
        elif rest.endswith("的") or len(x) <= 3 or len(rest) <= 4:
            rest += x
        else:
            rest += "、" + x
    if len(planets) >= 2:
        head = "与".join(planets)
        text = f"{head}的{rest}" if rest else head
    elif planets and rest:
        text = f"{planets[0]}的{rest}"
    else:
        text = rest or "、".join(planets)
    text = tidy_zh(text)
    text = re.sub(r"的+", "的", text)
    return text.strip("的，；、 ")


def restyle_en(sent: str) -> str:
    raw = strip_en_lead(sent).rstrip(". ")
    if not raw:
        return ""
    if cjk_count(raw) >= max(8, len(raw) // 4):
        out = tidy_zh(raw)
        return out if is_fluent_zh(out) else ""
    for pat, fmt in CLAUSE_PATTERNS:
        m = pat.search(raw)
        if not m:
            continue
        args = [np_to_zh(g) for g in m.groups() if g is not None]
        if not args or not all(cjk_count(a) >= 2 or a.upper() in ACRONYMS for a in args):
            continue
        try:
            out = tidy_zh(fmt(*args))
        except Exception:
            continue
        if is_fluent_zh(out):
            return out
    return ""


def to_zh(text: str, limit: int = 100) -> str:
    raw = fix_mojibake(" ".join((text or "").split()))
    if not raw:
        return ""
    if cjk_count(raw) >= max(8, len(raw) // 4):
        out = clip_zh(tidy_zh(raw), limit)
        return out if is_fluent_zh(out) else ""
    local = restyle_en(raw[:220])
    local = fix_mojibake(local).replace("诱导磁场", "感应磁场").replace("诱导场", "感应场")
    local = re.sub(r"的+", "的", local)
    if not is_fluent_zh(local):
        return ""
    return clip_zh(local, limit)


PLANET_PAIRS = [
    ("terrestrial planet", "类地行星"),
    ("rocky planet", "岩石行星"),
    ("exoplanet", "系外行星"),
    ("martian", "火星"),
    ("venusian", "金星"),
    ("mercury", "水星"),
    ("ganymede", "木卫三"),
    ("callisto", "木卫四"),
    ("europa", "木卫二"),
    ("mars", "火星"),
    ("venus", "金星"),
    ("earth", "地球"),
    ("moon", "月球"),
]
TOPIC_PAIRS = [
    ("electromagnetic induction", "电磁感应"),
    ("magnetic induction", "磁感应"),
    ("induced magnetic field", "感应磁场"),
    ("electrical conductivity", "电导率"),
    ("crustal conductivity", "地壳电导率"),
    ("interior structure", "内部结构"),
    ("magnetic field", "磁场"),
    ("magnetosphere", "磁层"),
    ("ionosphere", "电离层"),
    ("conductivity", "电导率"),
]


def term_hits(blob: str, pairs: list[tuple[str, str]]) -> list[str]:
    low = (blob or "").lower()
    found = []
    for en, zh in sorted(pairs, key=lambda x: len(x[0]), reverse=True):
        if en.lower() in low and zh not in found:
            found.append(zh)
    return found


CUE_TOPICS = [
    (r"magnetic induction|electromagnetic induction|induced magnetic", "磁感应"),
    (r"electrical conductivity|crustal conductivity", "电导率"),
    (r"magnetospher", "磁层"),
    (r"ionospher", "电离层"),
    (r"carbon cycle", "碳循环"),
    (r"collision chain|collision", "碰撞演化"),
    (r"disk-planet|disk planet", "盘星相互作用"),
    (r"secular resonance|resonance", "轨道共振"),
    (r"giant planet instability|instability", "轨道不稳定性"),
    (r"atmospheric circulation|atmosphere", "大气环流"),
    (r"planet formation|terrestrial planet formation|accretion", "形成过程"),
    (r"binary star", "双星系统中的行星"),
    (r"\bwater\b", "水的分布"),
]

FACT_CUES = [
    (r"subsurface ocean|internal ocean|water ocean|conductive ocean", "内部导电海洋会在变化外场中产生强感应"),
    (r"basal magma ocean", "基底岩浆洋的高电导率会同时影响热演化与磁场演化"),
    (r"magnetotelluric|\bem sounding\b", "电磁测深把电场与磁场联合起来反演电导率"),
    (r"joule heat", "感应电流的焦耳加热会改变能量收支"),
    (r"poynting", "坡印廷通量给出电磁能量向内部的输入"),
    (r"stellar wind", "恒星风驱动的外场变化是感应的重要源"),
    (r"ionospheric current", "电离层电流会叠加在内部感应信号上"),
    (r"crustal magneti", "地壳剩磁与感应场叠加，解释时需要分离"),
    (r"skin depth", "趋肤深度决定不同周期能够探测到的深度"),
    (r"phase (lag|shift)|induced-field phase", "感应场相位滞后反映电导率随深度的变化"),
    (r"induced magnetic field", "变化外场会在导电内部激发可观测的感应磁场"),
]


def fluent_digest(paper: dict, question: str = "", note: str = "", skip: int = 0) -> dict:
    blob = f"{paper.get('title') or ''} {paper_body(paper)}"
    low = blob.lower()
    q_terms = topic_terms(question, note)
    q_mag = any(t in {"magnetic", "induction", "conductivity", "magnetosphere", "ionosphere"} for t in q_terms)
    q_mag = q_mag or any(k in f"{question} {note}" for k in ("磁感应", "电磁感应", "电导率", "感应磁场", "磁层"))
    p_mag = bool(re.search(r"\binduct|conductiv|magnetospher|ionospher", low))
    off_topic = bool(OFFTOPIC_RE.search(low) or (q_mag and not p_mag))
    planets = term_hits(low, PLANET_PAIRS)
    cues = []
    for pat, zh in CUE_TOPICS:
        if re.search(pat, low) and zh not in cues:
            cues.append(zh)
        if len(cues) >= 2:
            break
    if q_mag:
        mag_cues = [c for c in cues if c in {"磁感应", "电导率", "磁层", "电离层"}]
        cues = mag_cues or cues[:1]
    p_str = "、".join(planets[:3])
    subject = p_str or "类地行星"
    cue0 = cues[0] if cues else ""

    fact = ""
    if not off_topic:
        facts = [zh for pat, zh in FACT_CUES if re.search(pat, low)]
        if facts:
            fact = facts[max(0, int(skip or 0)) % len(facts)]

    finding = ""
    if off_topic:
        finding = ""
    elif fact and p_str:
        finding = f"{subject}中，{fact}"
    elif fact:
        finding = fact
    elif cue0 == "电导率" and re.search(r"control|govern|dominat|profile", low):
        finding = f"{subject}内部电导率结构会决定感应场的振幅与相位"
    elif cue0 == "电导率":
        finding = f"{subject}的内部电导率是感应反演的主要未知量"
    elif cue0 == "磁感应" and planets:
        finding = f"{subject}在变化外场中会产生可观测的电磁感应响应"
    elif cue0 == "磁层":
        finding = f"{subject}磁层与内部感应场叠加，观测解释需要把两者分开"
    elif cue0 == "电离层":
        finding = f"{subject}电离层电流会干扰内部感应信号的分离"
    elif cue0 and p_str:
        finding = f"{subject}的{cue0}受内部导电结构控制"
    elif cue0:
        finding = f"{cue0}可作为内部结构的观测约束"

    method = ""
    if re.search(r"magnetometer", low):
        method = "依据磁强计观测"
    elif re.search(r"magnetotelluric|\bem sounding", low):
        method = "依据电磁测深"
    elif re.search(r"mhd|magnetohydro", low):
        method = "依据磁流体模拟"
    elif re.search(r"invers", low):
        method = "依据感应反演"
    elif re.search(r"numerical simulat|simulation", low):
        method = "依据数值模拟"
    elif re.search(r"analytic", low):
        method = "依据解析模型"

    purpose = ""
    if p_str and cue0:
        purpose = f"考察{p_str}的{cue0}"
    elif cue0:
        purpose = f"考察{cue0}"
    elif p_str:
        purpose = f"考察{p_str}相关问题"

    gap = ""
    if re.search(r"poorly constrained|not well constrained|still uncertain|remain(?:s)? unclear|degeneracy|non-unique", low):
        gap = f"{subject}的内部电导率剖面仍缺少足够的观测约束"

    finding = finding if finding and is_fluent_zh(finding) else ""
    method = method if method and is_fluent_zh(method) else ""
    purpose = purpose if purpose and is_fluent_zh(purpose) else ""
    gap = gap if gap and is_fluent_zh(gap) else ""
    return {
        "purpose": purpose,
        "method": method,
        "finding": finding,
        "gap": gap,
        "objects": uniq(planets + cues)[:4],
        "cues": cues,
        "planets": planets,
        "off_topic": off_topic,
    }


CLAUSE_PATTERNS = [
    (
        re.compile(r"^(.+?)\s+in\s+(.+?)\s+and\s+(.+)$", re.I),
        lambda a, b, c: f"考察{b}与{c}的{a}" if "磁" in a or "感应" in a or "场" in a else f"{b}与{c}的{a}",
    ),
    (
        re.compile(r"^(.+?)\s+in\s+(.+)$", re.I),
        lambda a, b: f"{b}的{a}",
    ),
    (
        re.compile(r"^(.+?)\s+controls?\s+(.+)$", re.I),
        lambda a, b: f"{a}控制{b}",
    ),
    (
        re.compile(r"^(.+?)\s+(?:is|are)\s+controlled by\s+(.+)$", re.I),
        lambda a, b: f"{a}受{b}控制",
    ),
    (
        re.compile(r"^(.+?)\s+remain(?:s)? limited by\s+(.+)$", re.I),
        lambda a, b: f"{a}仍受{b}的限制",
    ),
    (
        re.compile(r"^(.+?)\s+(?:is|are) limited by\s+(.+)$", re.I),
        lambda a, b: f"{a}受{b}限制",
    ),
    (
        re.compile(r"^(.+?)\s+can be constrained if\s+(.+)$", re.I),
        lambda a, b: f"若{b}已知，则可约束{a}",
    ),
    (
        re.compile(r"^(.+?)\s+can be constrained$", re.I),
        lambda a: f"可以约束{a}",
    ),
    (
        re.compile(r"^(.+?)\s+to (?:build|construct|develop|create)\s+(.+)$", re.I),
        lambda a, b: f"采用{a}来建立{b}",
    ),
    (
        re.compile(r"^(?:we |this paper )?(?:use|used)\s+(.+?)\s+to\s+(.+)$", re.I),
        lambda a, b: f"采用{a}来{b}",
    ),
    (
        re.compile(
            r"^(?:this paper |this work |we )?(?:investigate|study|examine|explore)s?\s+(.+)$",
            re.I,
        ),
        lambda a: f"考察{a}",
    ),
    (
        re.compile(r"^(?:we )?measure[sd]?\s+(.+)$", re.I),
        lambda a: f"测量了{a}",
    ),
]


def objects_zh(text: str) -> list[str]:
    blob = (text or "").lower()
    found = []
    for zh, en in sorted(GLOSSARY, key=lambda x: len(x[1] or x[0]), reverse=True):
        if not en:
            continue
        if en.lower() in blob and zh not in found:
            found.append(zh)
        if zh in (text or "") and zh not in found:
            found.append(zh)
    return found[:4]


def pick_role_sent(sents: list[str], pattern: re.Pattern, skip: int = 0, used: set | None = None) -> str:
    used = used or set()
    hits = [s for s in sents if pattern.search(s) and s not in used]
    if not hits:
        return ""
    return hits[min(max(0, skip), len(hits) - 1)]


def useful_sents(text: str, terms: list[str], limit: int = 4, skip: int = 0) -> list[str]:
    sents = [s for s in split_sents(text) if not is_junk_sent(s)]
    if not sents:
        raw = " ".join((text or "").split())
        return [raw[:220]] if len(raw) > 40 else []
    scored = []
    for sent in sents:
        low = sent.lower()
        score = sum(2 for t in terms if t in low)
        if FINDING_RE.search(sent) or PURPOSE_RE.search(sent) or METHOD_RE.search(sent):
            score += 3
        scored.append((score, min(len(sent), 240), sent))
    scored.sort(key=lambda x: (-x[0], -x[1]))
    picked = []
    for _, _, sent in scored[skip:]:
        compact = " ".join(sent.split())[:220]
        if compact not in picked:
            picked.append(compact)
        if len(picked) >= limit:
            break
    return picked


def paper_digest(paper: dict, question: str = "", note: str = "", skip: int = 0) -> dict:
    d = fluent_digest(paper, question, note, skip)
    extra_gap = to_zh(gap_sentence(paper_body(paper)))
    if extra_gap and is_fluent_zh(extra_gap) and not d.get("gap"):
        d["gap"] = extra_gap
    return d


def digest_blocks(papers: list[dict], question: str, note: str = "", rerun: int = 0) -> list[dict]:
    skip = max(0, int(rerun or 0))
    blocks = []
    for i, p in enumerate(papers, 1):
        d = p.get("digest") if isinstance(p.get("digest"), dict) and skip == 0 else None
        if not d or not d.get("finding"):
            d = paper_digest(p, question, note, skip)
        if d.get("off_topic"):
            continue
        blocks.append(
            {
                "i": i,
                "author": lead_author(p),
                "year": p.get("year") or "",
                "title": p.get("title") or "",
                "purpose": d.get("purpose") or "",
                "method": d.get("method") or "",
                "finding": d.get("finding") or "",
                "gap": d.get("gap") or "",
                "objects": d.get("objects") or [],
                "cues": d.get("cues") or [],
                "planets": d.get("planets") or [],
            }
        )
    return blocks


def strip_wrap(text: str, kind: str = "") -> str:
    text = fix_mojibake((text or "").strip())
    text = re.sub(r"^(本文|该文|本研究|该研究)(研究了|考察了|分析了|提出了|给出了)?", "", text)
    if kind == "gap":
        text = re.sub(r"^(然而|但是|但|不过|尽管如此)[，, ]*", "", text)
    return text.rstrip("。；; ")


def paper_claim(block: dict) -> str:
    method = strip_wrap(block.get("method") or "")
    finding = strip_wrap(block.get("finding") or "")
    if finding and is_fluent_zh(finding):
        if method and is_fluent_zh(method) and method not in finding:
            return f"{method}，{finding}。"
        return finding.rstrip("。") + "。"
    if method and is_fluent_zh(method):
        return method.rstrip("。") + "。"
    return ""


def cite_join(pairs: list[tuple[int, str]], limit: int = 6) -> str:
    groups: dict[str, list[int]] = {}
    order: list[str] = []
    for i, text in pairs:
        t = strip_wrap(text)
        if not t or not is_fluent_zh(t):
            continue
        if t not in groups:
            groups[t] = []
            order.append(t)
        if i not in groups[t]:
            groups[t].append(i)
    bits = [h(t) + cite_list(groups[t]) for t in order[:limit]]
    return "。".join(bits) + "。" if bits else ""


def topic_claim_pairs(blocks: list[dict]) -> list[tuple[int, str]]:
    pairs = []
    for b in blocks:
        claim = paper_claim(b)
        if claim:
            pairs.append((b["i"], claim))
    return pairs


def paper_zh_para(block: dict) -> str:
    return paper_claim(block)


def mag_topic(question: str, note: str = "") -> bool:
    blob = f"{question} {note}"
    if any(k in blob for k in ("磁感应", "电磁感应", "电导率", "感应磁场", "磁层", "电离层", "导电")):
        return True
    terms = topic_terms(question, note)
    return any(t in {"magnetic", "induction", "conductivity", "magnetosphere", "ionosphere"} for t in terms)


def on_topic_papers(papers: list[dict], question: str, note: str = "", rerun: int = 0) -> list[dict]:
    skip = max(0, int(rerun or 0))
    out = []
    for p in papers or []:
        d = p.get("digest") if isinstance(p.get("digest"), dict) and skip == 0 else None
        if not d:
            d = paper_digest(p, question, note, skip)
        if d.get("off_topic"):
            continue
        if not year_ok(p, *parse_year_range(question, note)):
            continue
        item = dict(p)
        item["digest"] = d
        out.append(item)
    return out


def theme_key(block: dict) -> str:
    blob = " ".join(
        [" ".join(block.get("cues") or []), " ".join(block.get("objects") or []), block.get("finding") or ""]
    )
    if any(x in blob for x in ("磁层", "电离层")):
        return "msphere"
    if any(x in blob for x in ("电导率", "磁感应", "感应")):
        return "induct"
    if any(x in blob for x in ("火星", "金星", "水星", "地球", "月球", "木卫", "系外", "类地")):
        return "body"
    return "other"


def cite_end(text: str, indices) -> str:
    if isinstance(indices, int):
        indices = [indices]
    c = cite_list(list(indices or []))
    t = (text or "").rstrip("。；; ")
    if not t:
        return ""
    return t + c + "。"


def paper_sentence(block: dict) -> str:
    finding = h(strip_wrap(block.get("finding") or ""))
    method = h(strip_wrap(block.get("method") or ""))
    if finding and method and method not in finding:
        sent = f"{finding}，{method}"
    elif finding:
        sent = finding
    elif method:
        sent = method
    else:
        return ""
    return cite_end(sent, block.get("i"))


def join_chunk(blocks: list[dict]) -> str:
    groups: dict[str, dict] = {}
    order: list[str] = []
    for b in blocks or []:
        finding = strip_wrap(b.get("finding") or "")
        method = strip_wrap(b.get("method") or "")
        key = finding or method
        if not key or not is_fluent_zh(key):
            continue
        if key not in groups:
            groups[key] = {"finding": finding, "method": method, "ids": []}
            order.append(key)
        i = b.get("i")
        if i and i not in groups[key]["ids"]:
            groups[key]["ids"].append(i)
    bits = []
    for key in order:
        g = groups[key]
        sent = g["finding"]
        if g["method"] and g["method"] not in sent:
            sent = f"{sent}，{g['method']}" if sent else g["method"]
        bits.append(cite_end(h(sent), g["ids"]))
    return "".join(bits)


def html_paras(texts: list[str]) -> str:
    return "".join(p_indent(t) for t in texts if t and str(t).strip())


def chunked(items: list, n: int = 2) -> list:
    return [items[i : i + n] for i in range(0, len(items), n)]


def split_three(items: list) -> tuple[list, list, list]:
    n = len(items)
    if n == 0:
        return [], [], []
    if n == 1:
        return items, items, items
    if n == 2:
        return items[:1], items, items[1:]
    a = (n + 2) // 3
    b = (2 * n + 2) // 3
    return items[:a], items[a:b], items[b:]


def unique_objects(blocks: list[dict]) -> list[str]:
    found = []
    for b in blocks:
        for x in b.get("objects") or []:
            if x not in found:
                found.append(x)
    return found


def take_themes(blocks: list[dict], keys: set[str], used: set[int]) -> list[dict]:
    picked = []
    for b in blocks:
        i = b.get("i")
        if i in used:
            continue
        if theme_key(b) in keys:
            picked.append(b)
            used.add(i)
    return picked


def section_paras(opener: str, blocks: list[dict], closer: str = "", expand: int = 0) -> str:
    texts = [opener] if opener else []
    size = 1 if int(expand or 0) >= 2 else 2
    for ch in chunked(blocks, size):
        texts.append(join_chunk(ch))
    if closer:
        texts.append(closer)
    return html_paras(texts)


def split_write_intent(note: str, instruction: str = "") -> tuple[str, int]:
    blob = f"{note or ''} {instruction or ''}"
    expand = 0
    if re.search(r"太短|过短|太少|加长|写长|再长|篇幅|不够长|再充实|写长一点", blob):
        expand = 3
    elif re.search(r"详细|展开|写详细", blob):
        expand = 2
    cleaned = re.sub(
        r"太短|过短|太少|加长|写长|再长|再写长|展开|详细|篇幅|不够长|再充实|写详细|写长一点",
        " ",
        note or "",
    )
    cleaned = re.sub(r"[；;、,，\s]+", "；", cleaned).strip("；;、,， ")
    return cleaned, expand


def expand_paras(mag: bool, level: int) -> dict[str, list[str]]:
    if level < 1:
        return {"intro": [], "body2": [], "body3": [], "body4": [], "disc": [], "conc": []}
    if mag:
        out = {
            "intro": [
                "把感应问题写成可计算的形式，关键是给定外源场的频谱和极化，求解导体内的电流分布，再把次级场投到观测点上。"
                "导体可以简化成壳层、海洋或岩浆层、地幔和金属核。每一层用厚度和电导率描述，观测只看到它们对振幅和相位的积分贡献。"
            ],
            "body2": [
                "对时间谐波外场，趋肤深度随电导率和周期同时变化。电导率升高时，同样周期只能看到更浅的深度；周期变长时，同样电导率才能看到更深的结构。"
                "因此，单一周期只能给出一个积分约束。要把海洋与地幔、薄高导层与厚中导层分开，必须覆盖足够宽的频段，并同时使用振幅和相位。",
                "反演时还要交代外源场是否均匀、是否有高阶空间结构。外源场的横向不均匀会在内部感应中引入额外模态，如果仍按均匀外场解释，导电层深度会被放错。",
            ],
            "body3": [
                "木星系统卫星的背景场强、变化周期明确，感应信号相对清楚；火星和金星主要受太阳风驱动，外源频谱更宽、也更不规则。"
                "地球可以同时使用地面电磁测深和卫星磁测，约束条件最多；月球没有全球内禀场，感应解释相对干净，但长周期覆盖仍然有限。",
                "有内禀场的天体必须先去掉发电机场，再谈感应。把两种场混在一个球谐展开里，导电层厚度可以在很宽的范围内滑动，拟合看起来很好，结构并不唯一。",
            ],
            "body4": [
                "电离层电流随地方时、太阳天顶角和磁层活动变化，夜侧通常更弱，所以夜侧或低活动时段更适合分离内部感应。"
                "地壳剩磁是静态的，不随外源周期变化，可以在频谱上与感应场区分；但它会抬高总场水平，影响短周期振幅的标定。",
                "实际拟合应同时给出外源场模型、内部电导率模型和不确定度，而不是只报一组“最佳”剖面。",
            ],
            "disc": [
                "即使数据足够，电导率剖面仍然允许等效模型：把高导层变薄、电导率变高，短周期振幅可以几乎不变。"
                "要打破这种等价，需要独立的密度、温度或组成约束，或者把感应结果与热演化、岩石实验电导率放到同一套内部模型里。",
            ],
            "conc": [
                "因此，磁感应能够回答导电层是否存在、大致在什么深度，但还不能单独给出唯一的内部成分剖面。"
                "下一步应把多周期磁测、外源场重构和实验室电导率一起使用，而不是继续增加单一频段上的拟合参数。",
            ],
        }
    else:
        out = {
            "intro": ["问题本身包含机制、观测和对象三个层面，需要分开写清楚，避免把不同前提的结果直接拼在一起。"],
            "body2": ["方法能约束什么、不能约束什么，应在给出数字之前先交代。"],
            "body3": ["主要认识只在对应对象和观测覆盖内成立。"],
            "body4": ["对象更换时，边界条件和资料密度一起变，结论不能平移。"],
            "disc": ["资料缺口和方法假设会进入最终表述，需要单独写出来。"],
            "conc": ["能确定的部分和仍可滑动的部分应分开陈述。"],
        }
    if level >= 2:
        if mag:
            out["intro"].append(
                "本文把感应当作内部结构的观测手段来写：先给出物理图像，再按电导率、行星对象和观测分离展开，最后讨论非唯一性和资料限制。"
            )
            out["body2"].append(
                "数值上，感应方程对电导率是非线性的。浅部高导层会屏蔽深部信号，使长周期看起来“已经饱和”。"
                "若不检查饱和，会误以为金属核的电导率已经被约束，实际上观测只要求深部导体足够高导，并不能给出精确数值。"
            )
            out["body3"].append(
                "把不同天体放到同一套无量纲参数下比较时，应同时对齐外源场强度、自转或轨道周期、以及可能的海洋厚度。"
                "只比较感应振幅的大小，会把环境差别写成内部结构差别。"
            )
            out["disc"].append(
                "此外，模型网格、层数和正则化都会改变剖面形状。报告结果时应给出可替换模型，而不是只保留最光滑的一条曲线。"
            )
        else:
            for k in out:
                out[k].append("把前提、方法和结论写成可以核对的句子，篇幅不足时优先补机制与限制，而不是重复同一句判断。")
    if level >= 3:
        if mag:
            out["intro"].extend(
                [
                    "短周期磁测对浅部高导层敏感，却几乎看不见核幔边界附近的导体；长周期能够加深趋肤深度，却更容易混入磁层和电离层电流。"
                    "因此必须把物理机制、对象差异和观测分离写成相互制约的三部分，而不是先堆文献条目再补一句结论。",
                    "把问题写成可计算形式时，给定的是外源场频谱与极化，求解的是导体内电流，输出的是观测点上次级场的振幅和相位。"
                    "导体可分成壳层、海洋或岩浆层、地幔和金属核；每一层用厚度和电导率描述，观测只看到它们对响应函数的积分贡献。",
                ]
            )
            out["body2"].extend(
                [
                    "给定外源场和观测点上的次级场，反演得到的是电导率对半径的积分核，而不是逐层真值。"
                    "把响应曲线拟合成两层或三层模型时，层数本身就是先验：增加一层总能改善拟合，但不等于内部真的多了一层海洋或岩浆。",
                    "趋肤深度公式只在均匀半空间里严格成立。行星内部电导率随深度跳跃时，真实穿透由球谐感应方程或传输矩阵决定。"
                    "仍用半空间公式估计深度，会把海洋放得过深或过浅。",
                    "实验室电导率是温度、含水量、熔融度和氧逸度的函数；磁感应给出的是行星内部的有效电导率。"
                    "二者必须通过热演化模型衔接，否则高导层既可以解释成含水地幔，也可以解释成部分熔融。",
                    "相位比振幅更敏感于电导率随深度的变化。只有振幅时，薄高导层与厚中导层可以给出相近的曲线；补上相位后，可滑动的模型空间会明显缩小。",
                ]
            )
            out["body3"].extend(
                [
                    "木卫二和木卫三的轨道周期提供了相对单一的外源频率，感应解释因此比太阳风驱动的类地行星更直接。"
                    "即便如此，等离子体层电流和阿尔芬翼也会进入磁测，不能把飞掠期间的全部扰动都算成海洋感应。",
                    "火星没有全球偶极场，外壳剩磁和电离层电流是主要背景。感应信号要在地方时和太阳天顶角变化中提取，连续频段覆盖比木星卫星更困难。",
                    "金星的感应环境更接近电离层导体加内部低导地幔。若把电离层电导率误写入内部剖面，会得到过浅的高导层。",
                    "地球既有发电机，也有海洋和含水地幔，是唯一能够用地面台站和卫星同时约束的对象。"
                    "把地球上成熟的电磁感应方法迁到其他行星时，缺少的是台站密度和长周期标定，而不是方程本身。",
                    "月球没有全球内禀场，感应解释相对干净，但现有飞掠和轨道数据的长周期覆盖仍然有限，深部导体往往只能给出下限。",
                ]
            )
            out["body4"].extend(
                [
                    "内外场分离不是事后校正，而是反演的一部分。外源场球谐系数若定错，内部响应系数会跟着错，电导率剖面会整体平移。",
                    "夜侧观测、不同地方时差分，以及利用已知轨道周期做相干检测，是目前最有效的分离途径。"
                    "只比较总场均方根，无法区分内部感应与磁层压缩。",
                    "地壳剩磁不随外源周期变化，可以在频谱上与感应场区分；但它会抬高总场水平，影响短周期振幅的标定，所以分离时仍要进入误差预算。",
                ]
            )
            out["disc"].extend(
                [
                    "非唯一性不会因为增加文献数量而消失。同一组振幅曲线可以被薄高导层、厚中导层或部分熔融层同时拟合。",
                    "要把模型空间缩小，需要把感应结果写成与密度、转动惯量和热流相容的内部结构，而不是单独优化电磁拟合。",
                    "外源场本身往往不是理想的均匀交变场。横向不均匀会在内部感应中引入额外模态；若仍按均匀外场解释，导电层深度会被放错。",
                ]
            )
            out["conc"].extend(
                [
                    "本文的结论因此应读作：磁感应能够判断导电层是否存在及其深度范围；在现有频段和外源场模型下，还不能单独给出唯一的成分剖面。",
                    "要把这一判断推进到定量内部结构，需要更完整的多周期覆盖、可检验的外源场模型，以及与实验室电导率一致的热演化约束。",
                ]
            )
        else:
            extra = (
                "把同一判断写成更长的论述时，应补上对象范围、方法边界和不能外推的条件，而不是重复摘要里的那句话。"
            )
            for k in out:
                out[k].append(extra)
                out[k].append("资料覆盖不足的部分要单独成段，避免用概括句把缺口写成已经解决。")
    if level >= 4:
        if mag:
            out["body2"].append(
                "实际反演还应报告可替换模型，而不是只保留最光滑的一条电导率曲线。"
                "正则化、层数和网格都会改变剖面形状；不给出这些选择，读者无法判断约束来自数据还是来自先验。"
            )
            out["body3"].append(
                "同一卫星在不同飞掠几何下看到的感应振幅可以不同。这并不自动意味着内部结构变了，更常见的原因是外源场投影和飞行路径采样不同。"
            )
            out["disc"].append(
                "把感应结果写成论文时，应同时给出：所用周期、外源场假设、内外场分离方法和可滑动的电导率区间。"
                "缺少其中任何一项，导电层深度都可以被改写。"
            )
        else:
            out["disc"].append("加长之后仍应保持判断可核对：每段都要能指出它依赖哪一类观测或哪一种模型假设。")
    return out


def review_parts(question: str, note: str, blocks: list[dict], rerun: int = 0, expand: int = 0) -> dict[str, str]:
    mag = mag_topic(question, note)
    q = re.sub(r"[？?。.!！\s]+$", "", question or "").strip() or "该问题"
    if rerun and blocks:
        k = int(rerun) % len(blocks)
        blocks = blocks[k:] + blocks[:k]
    n = len(blocks)
    objs = "、".join(unique_objects(blocks)[:6])
    used: set[int] = set()
    g2 = take_themes(blocks, {"induct"}, used)
    g3 = take_themes(blocks, {"body"}, used)
    g4 = take_themes(blocks, {"msphere", "other"}, used)
    rest = [b for b in blocks if b.get("i") not in used]
    if rest:
        g3.extend(rest)
    if not g2 or not g3 or not g4:
        g2, g3, g4 = split_three(blocks)

    if mag:
        intro = html_paras(
            [
                (
                    f"本文讨论{h(q)}。导电行星内部在随时间变化的外磁场中会产生感应电流，并形成可观测的感应磁场。"
                    "外源场可以来自行星磁层、太阳风，或卫星在背景磁场中运动时所扫过的变化分量。"
                    "导体中的感应电流产生次级磁场，其振幅和相位由电导率随深度的分布决定，因而磁感应观测被用来约束海洋、岩浆层、地幔和金属核等导电结构。"
                ),
                (
                    "电磁感应的物理图像可以概括为：变化外场在导体中激发涡旋电场，涡旋电场驱动电流，电流再产生感应磁场。"
                    "观测到的次级场相对于外源场既有振幅变化，也有相位滞后；二者都是电导率剖面的函数。"
                    "趋肤深度随周期增加而加深，短周期主要约束浅部高导层，长周期才能看到深部地幔或金属核。"
                ),
                (
                    "与内禀发电机场不同，感应场随外源频谱变化。要把内部感应与磁层电流、电离层电流和地壳剩磁分开，是观测解释中的核心步骤。"
                    "本文依次讨论电磁感应与电导率、类地行星及卫星中的感应响应，以及磁层—电离层对观测的影响。"
                ),
            ]
        )
        t2, t3, t4 = (
            "2　电磁感应与电导率",
            "3　类地行星与卫星中的感应响应",
            "4　磁层、电离层与内外场分离",
        )
        body2 = section_paras(
            "电磁感应把变化外场与内部电流联系起来。电导率越高、导电层越厚，感应场通常越强；不同周期对应不同趋肤深度，频谱观测因此能够分层约束内部结构。"
            "反演的主要未知量是电导率随半径的分布。若把观测磁场直接当成内禀场，会把感应贡献误读成发电机强度或磁层结构。"
            "对类地行星而言，常用的外源包括太阳风压缩、磁层波动，以及卫星穿越巨行星磁场时看到的交变分量。",
            g2,
            "把这些结果放到反演框架中看，振幅给出导电层的积分约束，相位则对电导率随深度的变化更敏感。缺少相位信息时，高导薄层与中导厚层往往无法区分。",
            expand,
        )
        body3 = section_paras(
            "类地行星和大型卫星的感应环境并不相同。有的天体具有内禀场，有的主要暴露在太阳风或巨行星磁层中；内部若存在海洋、岩浆洋或金属核，都会改变感应响应的强度和频谱。"
            + (f"讨论对象包括{h(objs)}。" if objs else "")
            + "同一方法迁到不同对象时，必须同时改外源场模型和内部电导率模型，而不能只改行星半径。",
            g3,
            "对象之间的差别，首先来自外源场是否稳定、内部是否存在高导层，以及观测能否覆盖足够的周期。木星系统卫星的背景场强、地球和火星的太阳风驱动，以及金星以电离层为主的叠加，都不能用同一套边界条件处理。",
            expand,
        )
        body4 = section_paras(
            "卫星和地面磁测记录的是叠加场。磁层电流、电离层电流和地壳剩磁都会进入观测，若不加分离，内部电导率容易被高估或低估。"
            "分离的常用途径是利用夜侧、不同地方时或不同周期上外源场与内部响应的相位差，而不是只比较总场强度。",
            g4,
            "因此，感应解释必须同时给出外源场模型和内部电导率模型，而不能只拟合总场振幅。对有内禀场的天体，还要把发电机场从感应场中减去，否则导电层深度会被系统性放错。",
            expand,
        )
        abstract_zh = (
            f"本文讨论{h(q)}：用变化外场激发的感应电流，约束内部电导率与导电层结构。"
            "论述从电磁感应与电导率、类地行星及卫星的感应响应、磁层与电离层对观测的干扰三个方面展开。"
            + (f"主要对象包括{h(objs)}。" if objs else "")
            + "感应场振幅与相位主要由内部电导率结构控制；内外场分离不足、频段覆盖有限，仍限制对电导率剖面的唯一反演。"
        )
        abstract_en = (
            "This paper discusses magnetic induction as a means to constrain interior electrical conductivity "
            "using time-varying external fields. It treats electromagnetic induction and conductivity, "
            "induction responses of planets and moons, and magnetospheric or ionospheric contamination of the observed field. "
            "Induced-field amplitude and phase are controlled by the conductivity profile; separating internal and external sources remains a central difficulty."
        )
        conc = html_paras(
            [
                f"本文表明，{h(q)}的核心是用感应场约束内部电导率，而不是把磁测信号直接当成内禀场。",
                "感应场振幅与相位主要受电导率结构控制；行星与卫星的差异首先来自外源场环境和内部导电层配置。"
                "短周期约束浅部高导层，长周期才可能看到深部地幔或金属核，因此频谱不完整会直接造成深度误判。",
                "要把这一方法推进到更定量的内部结构，还需要更完整的外源频谱、更审慎的内外场分离，以及对电导率非唯一反演给出明确的不确定度。"
                "在这些条件补齐之前，已有约束更适合判断导电层是否存在及其大致深度，而不宜写成唯一的内部剖面。",
            ]
        )
        gap_open = (
            "感应反演的固有困难是电导率剖面的非唯一性：有限频段只能约束一定深度范围内的电导率积分，薄高导层与厚中导层在部分周期上可以给出相近的振幅。"
            "磁层和电离层电流、地壳剩磁也会污染内部感应信号；分离不充分时，导电层厚度和电导率会被系统性误估。"
            "此外，外源场本身往往不是理想的均匀交变场，模型里对外源频谱的简化会进入内部电导率的误差。"
        )
    else:
        intro = html_paras(
            [
                (
                    f"本文讨论{h(q)}。"
                    + (f"主要对象包括{h(objs)}。" if objs else "")
                    + "问题可以从机制、观测约束和典型对象三个方面展开。"
                ),
                "下文先说明方法与观测，再给出主要认识与对象案例，最后讨论不足。",
            ]
        )
        t2, t3, t4 = ("2　方法与观测", "3　主要认识", "4　对象与案例")
        body2 = section_paras("观测与计算所约束的量并不相同，需要把方法与未知量对应起来。", g2, expand=expand)
        body3 = section_paras("下面按对象与机制陈述主要认识。", g3, expand=expand)
        body4 = section_paras("不同对象上的结果不能直接外推，需要对照前提、方法和观测覆盖。", g4, expand=expand)
        abstract_zh = (
            f"本文讨论{h(q)}。"
            + (f"内容集中在{h(objs)}。" if objs else "")
            + "全文按引言、方法、主要认识、对象案例、讨论与结论组织。"
        )
        abstract_en = f"This paper discusses {h(q)} in terms of methods, findings, and cases."
        conc = html_paras(
            [
                f"本文表明，{h(q)}可以得到若干可核对的认识，但结论强度取决于对象和方法，不宜外推到未覆盖的情形。",
                "后续工作需要在同一对象上补充更完整的观测，并明确模型假设与不足。",
            ]
        )
        gap_open = "方法边界和资料缺口并不均衡，需要把已经能够确定的不足单独集中起来。"

    gap_blocks = [b for b in blocks if strip_wrap(b.get("gap") or "", "gap")]
    if gap_blocks:
        disc = html_paras(
            [
                gap_open,
                join_chunk(
                    [
                        {
                            **b,
                            "finding": strip_wrap(b.get("gap") or "", "gap"),
                            "purpose": "",
                            "method": "",
                        }
                        for b in gap_blocks
                    ]
                ),
                "这些不足说明，结论应限制在所用频段、对象和模型假设之内。",
            ]
        )
    else:
        disc = html_paras(
            [
                gap_open,
                "频谱覆盖、模型假设和观测分离仍是解释中必须交代的条件。"
                "没有这些条件，电导率剖面可以移动，导电层深度也可以改写，表面上的拟合优度并不能证明内部结构已经被唯一确定。",
            ]
        )

    extras = expand_paras(mag, max(0, int(expand or 0)))
    intro += html_paras(extras.get("intro") or [])
    body2 += html_paras(extras.get("body2") or [])
    body3 += html_paras(extras.get("body3") or [])
    body4 += html_paras(extras.get("body4") or [])
    disc += html_paras(extras.get("disc") or [])
    conc += html_paras(extras.get("conc") or [])

    return {
        "intro": intro,
        "t2": t2,
        "t3": t3,
        "t4": t4,
        "body2": body2,
        "body3": body3,
        "body4": body4,
        "disc": disc,
        "conc": conc,
        "abstract_zh": abstract_zh,
        "abstract_en": abstract_en,
    }


def section_review(papers: list[dict], question: str, note: str = "", rerun: int = 0, expand: int = 0, parts: dict | None = None) -> str:
    papers = on_topic_papers(papers, question, note, rerun)
    if not papers:
        return (
            "<h1>信息抽取与综述生成</h1>"
            f"<p>关于「{h(question)}」目前还没有可写入的对题结论。请改补充说明后重跑检索。</p>"
        )
    if parts is None:
        blocks = digest_blocks(papers, question, note, rerun)
        parts = review_parts(question, note, blocks, rerun, expand)
    return (
        f"<h1>{h(question)}</h1>"
        + parts["intro"]
        + f"<h2>{h(parts['t2'])}</h2>"
        + parts["body2"]
        + f"<h2>{h(parts['t3'])}</h2>"
        + parts["body3"]
        + f"<h2>{h(parts['t4'])}</h2>"
        + parts["body4"]
        + "<h2>尚未解决的问题</h2>"
        + parts["disc"]
        + "<h2>小结</h2>"
        + parts["conc"]
    )


def parse_csv_text(name: str, text: str) -> dict | None:
    try:
        sample = text[:4096]
        dialect = csv.Sniffer().sniff(sample, delimiters=",\t;")
    except csv.Error:
        dialect = csv.excel
    reader = csv.reader(io.StringIO(text), dialect)
    rows = [row for row in reader if any(cell.strip() for cell in row)]
    if len(rows) < 2:
        return None
    header = [c.strip() or f"col{i+1}" for i, c in enumerate(rows[0])]
    body = rows[1:]
    stats = []
    for idx, col in enumerate(header):
        nums = []
        for row in body:
            if idx >= len(row):
                continue
            raw = row[idx].strip().replace("%", "")
            try:
                nums.append(float(raw))
            except ValueError:
                continue
        if len(nums) < 3:
            continue
        stats.append(
            {
                "name": col,
                "n": len(nums),
                "mean": round(statistics.fmean(nums), 4),
                "stdev": round(statistics.stdev(nums), 4) if len(nums) > 1 else 0,
                "min": round(min(nums), 4),
                "max": round(max(nums), 4),
            }
        )
    return {"name": name, "rows": len(body), "cols": header, "stats": stats}


def parse_uploads(files: list) -> list[dict]:
    parsed = []
    for item in files or []:
        name = str(item.get("name") or "unnamed")
        text = decode_upload_text(item if isinstance(item, dict) else {})
        if not text.strip():
            parsed.append(
                {
                    "name": name,
                    "chars": 0,
                    "blocks": 0,
                    "preview": "未能抽出正文（图片无法直接读字；PDF 请确认不是扫描件）。",
                    "csv": None,
                    "kind": "local",
                }
            )
            continue
        sentences = [s.strip() for s in re.split(r"(?<=[。.!？?\n])\s*", text) if s.strip()]
        blocks = sentences[:8] or [text[:240]]
        csv_stats = (
            parse_csv_text(name, text)
            if re.search(r"\.(csv|tsv|txt|xlsx|xls)$", name, re.I) or "," in text[:200]
            else None
        )
        parsed.append(
            {
                "name": name,
                "chars": len(text),
                "blocks": len(sentences),
                "preview": " ".join(blocks[:3])[:360],
                "csv": csv_stats,
                "kind": "local",
                "text": text[:12000],
            }
        )
    return parsed


def section_lit(papers: list[dict], question: str, note: str = "", en_query: str = "", repair: dict | None = None, llm_meta: dict | None = None) -> str:
    comments = {}
    for c in (llm_meta or {}).get("lit_comments") or []:
        if not isinstance(c, dict):
            continue
        try:
            idx = int(c.get("i") or 0)
        except (TypeError, ValueError):
            continue
        if idx:
            comments[idx] = str(c.get("reason") or "").strip()
    rows = []
    for i, p in enumerate(papers, 1):
        reason = comments.get(i) or ""
        rows.append(
            "<tr>"
            f"<td>{h(p.get('title'))}</td>"
            f"<td>{h(', '.join((p.get('authors') or [])[:3]))}</td>"
            f"<td>{h(p.get('year') or '')}</td>"
            f"<td>{h(p.get('source') or '')}</td>"
            f"<td>{h(p.get('doi') or p.get('arxiv_id') or '—')}</td>"
            + (f"<td>{h(reason or '—')}</td>" if comments or llm_meta else "")
            + "</tr>"
        )
    extra_col = bool(comments or llm_meta)
    body = "".join(rows) or f"<tr><td colspan='{6 if extra_col else 5}'>未检索到文献</td></tr>"
    note_p = f"<p>补充说明已并入检索：{h(note)}</p>" if note else ""
    q_p = f"<p>检索式：{h(en_query)}</p>" if en_query else ""
    sources = sorted({str(p.get("source") or "") for p in papers if p.get("source")})
    src_p = f"<p>来源：{'、'.join(h(s) for s in sources)}。</p>" if sources else ""
    repair_html = ""
    if repair:
        dropped = repair.get("dropped") or []
        added = repair.get("added") or []
        repair_html = (
            f"<p>本步重跑只处理不对题的条目：保留 <b>{repair.get('kept', 0)}</b> 篇，"
            f"去掉 <b>{len(dropped)}</b> 篇，补入 <b>{len(added)}</b> 篇。没有整批更换。</p>"
        )
        if dropped:
            repair_html += "<p>去掉：" + "；".join(h(t) for t in dropped[:8]) + "</p>"
        if added:
            repair_html += "<p>补入：" + "；".join(h(t) for t in added[:8]) + "</p>"
        if not dropped and not added:
            repair_html += "<p>复核后当前清单都对题，因此没有替换。</p>"
    lead = str((llm_meta or {}).get("lit_lead") or "").strip()
    lead_html = as_paras(lead) if lead else (
        f"<p>问题：{h(question)}。按相关度筛选后保留 <b>{len(papers)}</b> 篇对题文献。</p>"
    )
    head = "<th>文献</th><th>作者</th><th>年份</th><th>来源</th><th>DOI / arXiv</th>"
    if extra_col:
        head += "<th>筛选理由</th>"
    return (
        "<h1>文献检索与递归筛选</h1>"
        + lead_html
        + repair_html
        + note_p
        + q_p
        + src_p
        + f"<table class='lit-table'><thead><tr>{head}</tr></thead>"
        f"<tbody>{body}</tbody></table>"
    )


def section_parse(papers: list[dict], uploads: list[dict], note: str = "", rerun: int = 0, llm_meta: dict | None = None) -> str:
    rows = []
    for u in uploads:
        rows.append(
            "<tr>"
            f"<td>{h(u['name'])}</td>"
            f"<td>{u['chars']}</td>"
            f"<td>{u['blocks']}</td>"
            "<td>本地文件</td>"
            f"<td>{'已抽出正文' if u['chars'] else '未抽出正文'}</td>"
            "</tr>"
        )
    for i, p in enumerate(papers, 1):
        body = paper_body(p)
        words = len(body.split())
        kind = p.get("parse_kind") or "摘要"
        rows.append(
            "<tr>"
            f"<td>{h(p.get('title'))}</td>"
            f"<td>{words}</td>"
            f"<td>{max(1, math.ceil(words / 80))}</td>"
            f"<td>{h(kind)}</td>"
            "<td>完成</td>"
            "</tr>"
        )
    body = "".join(rows) or "<tr><td colspan='5'>没有可解析材料</td></tr>"
    snippets = []
    for u in uploads[:4]:
        if u.get("preview"):
            snippets.append(
                f"<li><span class='pg'>本地</span><span class='snip'>{h(u['name'])}：{h(u['preview'])}</span></li>"
            )
    skip = max(0, int(rerun or 0))
    show = (papers[skip:] + papers[:skip]) if papers else []
    for i, p in enumerate(show[:4], 1):
        d = p.get("digest") if isinstance(p.get("digest"), dict) else {}
        snip = d.get("finding") or d.get("purpose") or "已读取该文，待概括目的与结论。"
        snippets.append(
            f"<li><span class='pg'>{h(p.get('parse_kind') or '文献')}</span>"
            f"<span class='snip'>{h(snip)}</span></li>"
        )
    if uploads:
        lead = f"已解析你上传的 <b>{len(uploads)}</b> 个本地文件"
        if papers:
            lead += f"，并读取 <b>{len(papers)}</b> 篇检索文献（优先全文，没有全文再用摘要）"
        lead += "。"
    elif papers:
        html_n = sum(1 for p in papers if "全文" in (p.get("parse_kind") or ""))
        lead = (
            f"未上传本地文件。已尝试读取检索文献全文：成功 {html_n} 篇，其余 {len(papers) - html_n} 篇暂无公开 HTML，改用摘要。"
            "上传 PDF / Word / 文本后，这一步会以本地文件为主。"
        )
    else:
        lead = "没有可解析材料。"
    note_p = f"<p>补充说明：{h(note)}</p>" if note else ""
    llm_lead = str((llm_meta or {}).get("parse_lead") or "").strip()
    if llm_lead:
        lead_html = as_paras(llm_lead)
    else:
        lead_html = f"<p>{lead}</p>"
    points = (llm_meta or {}).get("parse_points") or []
    if isinstance(points, list) and points:
        snippets = [
            f"<li><span class='pg'>抽取</span><span class='snip'>{h(str(x).strip())}</span></li>"
            for x in points if str(x).strip()
        ]
    return (
        "<h1>文献解析</h1>"
        + lead_html
        + note_p
        + "<table class='lit-table'><thead><tr><th>来源</th><th>字词量</th><th>块数</th><th>类型</th><th>状态</th></tr></thead>"
        f"<tbody>{body}</tbody></table>"
        "<h2>中文要点</h2>"
        f"<ul class='provenance-list'>{''.join(snippets) or '<li>暂无片段</li>'}</ul>"
    )


def year_chart_svg(years: list[int]) -> str:
    counts = Counter(years)
    if not counts:
        return "<p>没有年份数据，无法绘图。</p>"
    keys = sorted(counts)
    max_v = max(counts.values())
    width = max(360, 48 * len(keys) + 40)
    height = 140
    bars = []
    gap = 12
    bar_w = max(18, (width - 40) / len(keys) - gap)
    for i, year in enumerate(keys):
        v = counts[year]
        bh = 8 if max_v == 0 else round(90 * v / max_v)
        x = 24 + i * (bar_w + gap)
        y = 110 - bh
        bars.append(
            f"<rect x='{x:.1f}' y='{y}' width='{bar_w:.1f}' height='{bh}' rx='3' fill='#2a5fff'/>"
            f"<text x='{x + bar_w/2:.1f}' y='126' text-anchor='middle' font-size='11' fill='#5b6780'>{year}</text>"
            f"<text x='{x + bar_w/2:.1f}' y='{y-4}' text-anchor='middle' font-size='11' fill='#1b2550'>{v}</text>"
        )
    return (
        f"<svg viewBox='0 0 {width} {height}' width='100%' height='{height}' "
        "xmlns='http://www.w3.org/2000/svg'>"
        f"{''.join(bars)}</svg>"
    )


def section_data(papers: list[dict], uploads: list[dict], question: str = "", note: str = "", rerun: int = 0, llm_meta: dict | None = None) -> str:
    blocks = digest_blocks(papers, question, note)
    if rerun:
        blocks = sorted(blocks, key=lambda b: (str(b.get("year") or ""), str(b.get("author") or "")), reverse=bool(rerun % 2))
    llm_rows = (llm_meta or {}).get("data_rows") or []
    rows = []
    if isinstance(llm_rows, list) and llm_rows:
        for item in llm_rows:
            if not isinstance(item, dict):
                continue
            rows.append(
                "<tr>"
                f"<td>{h(item.get('object') or '—')}</td>"
                f"<td>{h(item.get('constraint') or '—')}</td>"
                f"<td>{h(item.get('cite') or '—')}</td>"
                "</tr>"
            )
    if not rows:
        for b in blocks:
            obj = "、".join((b.get("planets") or b.get("objects") or [])[:3]) or "—"
            claim = strip_wrap(b.get("finding") or b.get("purpose") or "—")
            rows.append(
                "<tr>"
                f"<td>{h(obj)}</td>"
                f"<td>{h(claim)}</td>"
                f"<td>{cite_list([b['i']])}</td>"
                "</tr>"
            )
    extra = ""
    for u in uploads:
        csv_stats = u.get("csv")
        if not csv_stats or not csv_stats.get("stats"):
            continue
        extra += f"<h2>上传表 {h(csv_stats['name'])}</h2><p>{csv_stats['rows']} 行，按原文数值统计。</p>"
        extra += "<table class='lit-table'><thead><tr><th>列</th><th>n</th><th>均值</th><th>标准差</th><th>最小</th><th>最大</th></tr></thead><tbody>"
        for s in csv_stats["stats"]:
            extra += (
                f"<tr><td>{h(s['name'])}</td><td>{s['n']}</td><td>{s['mean']}</td>"
                f"<td>{s['stdev']}</td><td>{s['min']}</td><td>{s['max']}</td></tr>"
            )
        extra += "</tbody></table>"
    body = "".join(rows) or "<tr><td colspan='3'>没有可写入的数据</td></tr>"
    lead = str((llm_meta or {}).get("data_lead") or "").strip()
    lead_html = as_paras(lead) if lead else "<p>抽出对象、约束和出处编号，供论文表格使用。</p>"
    return (
        "<h1>实验数据初步统计</h1>"
        + lead_html
        + "<table class='lit-table'><thead><tr><th>对象</th><th>约束</th><th>出处</th></tr></thead>"
        f"<tbody>{body}</tbody></table>"
        + extra
    )


def paper_fig(svg: str, caption: str) -> str:
    return (
        f"<figure class='paper-fig'>{svg}"
        f"<figcaption>{h(caption)}</figcaption></figure>"
    )


def induction_schematic_svg() -> str:
    return """
<svg viewBox="0 0 640 270" width="100%" height="270" xmlns="http://www.w3.org/2000/svg" role="img">
  <text x="70" y="28" font-size="13" fill="#1b2550">外源场 B₀</text>
  <path d="M40 50 L40 210" stroke="#2a5fff" stroke-width="2" fill="none" marker-end="url(#arrB)"/>
  <path d="M58 50 L58 210" stroke="#2a5fff" stroke-width="2" fill="none"/>
  <path d="M76 50 L76 210" stroke="#2a5fff" stroke-width="2" fill="none"/>
  <circle cx="320" cy="135" r="92" fill="#eef3fb" stroke="#1b2550" stroke-width="2"/>
  <circle cx="320" cy="135" r="58" fill="#d7e4ff" stroke="#2a5fff" stroke-width="2"/>
  <circle cx="320" cy="135" r="28" fill="#f7f1d6" stroke="#b08900" stroke-width="1.5"/>
  <text x="320" y="132" text-anchor="middle" font-size="12" fill="#1b2550">金属核</text>
  <text x="320" y="148" text-anchor="middle" font-size="11" fill="#3d4d6b">或深部导体</text>
  <text x="320" y="78" text-anchor="middle" font-size="12" fill="#2a5fff">导电层 / 海洋</text>
  <path d="M248 135 A72 72 0 0 1 392 135" stroke="#c45c26" stroke-width="2.5" fill="none"/>
  <polygon points="392,135 382,128 382,142" fill="#c45c26"/>
  <text x="410" y="108" font-size="12" fill="#c45c26">感应电流</text>
  <text x="500" y="28" font-size="13" fill="#1b2550">感应场 B_ind</text>
  <path d="M560 210 L560 50" stroke="#0a7a4a" stroke-width="2" fill="none"/>
  <path d="M542 210 L542 50" stroke="#0a7a4a" stroke-width="2" fill="none"/>
  <path d="M578 210 L578 50" stroke="#0a7a4a" stroke-width="2" fill="none"/>
  <polygon points="560,50 554,62 566,62" fill="#0a7a4a"/>
  <text x="320" y="255" text-anchor="middle" font-size="12" fill="#5b6780">变化外场在导电内部激发电流，电流再产生可观测的次级磁场</text>
</svg>
""".strip()


def skin_depth_svg() -> str:
    pts = []
    for i in range(0, 11):
        t = 0.4 + i * 0.9
        x = 70 + i * 48
        y = 200 - 42 * (t ** 0.5)
        pts.append(f"{x:.1f},{y:.1f}")
    return f"""
<svg viewBox="0 0 640 240" width="100%" height="240" xmlns="http://www.w3.org/2000/svg" role="img">
  <line x1="70" y1="200" x2="600" y2="200" stroke="#1b2550" stroke-width="1.5"/>
  <line x1="70" y1="200" x2="70" y2="30" stroke="#1b2550" stroke-width="1.5"/>
  <text x="335" y="228" text-anchor="middle" font-size="13" fill="#1b2550">周期 T（示意）</text>
  <text x="18" y="120" font-size="13" fill="#1b2550" transform="rotate(-90 18 120)">趋肤深度 δ</text>
  <polyline points="{' '.join(pts)}" fill="none" stroke="#2a5fff" stroke-width="2.5"/>
  <circle cx="118" cy="158" r="3.5" fill="#2a5fff"/>
  <circle cx="502" cy="74" r="3.5" fill="#2a5fff"/>
  <text x="128" y="154" font-size="12" fill="#2a5fff">短周期 · 浅部</text>
  <text x="430" y="64" font-size="12" fill="#2a5fff">长周期 · 深部</text>
  <text x="80" y="24" font-size="12" fill="#5b6780">δ ∝ √T，用于说明分层约束，不是某一篇论文的实测曲线</text>
</svg>
""".strip()


def bar_chart_svg(items: list[tuple[str, float]], ylabel: str = "篇数", color: str = "#2a5fff") -> str:
    if not items:
        return "<p>没有可绘图的数据。</p>"
    max_v = max(v for _, v in items) or 1
    width = max(420, 56 * len(items) + 80)
    height = 200
    bar_w = max(22, min(42, (width - 90) / len(items) - 12))
    bars = []
    for i, (label, val) in enumerate(items):
        bh = 8 if max_v == 0 else round(120 * val / max_v)
        x = 56 + i * (bar_w + 14)
        y = 160 - bh
        bars.append(
            f"<rect x='{x:.1f}' y='{y}' width='{bar_w:.1f}' height='{bh}' rx='3' fill='{color}'/>"
            f"<text x='{x + bar_w/2:.1f}' y='176' text-anchor='middle' font-size='11' fill='#1b2550'>{h(label)}</text>"
            f"<text x='{x + bar_w/2:.1f}' y='{y-6}' text-anchor='middle' font-size='11' fill='#1b2550'>{h(str(int(val) if val == int(val) else round(val, 2)))}</text>"
        )
    return (
        f"<svg viewBox='0 0 {width} {height}' width='100%' height='{height}' "
        "xmlns='http://www.w3.org/2000/svg' role='img'>"
        f"<text x='12' y='24' font-size='12' fill='#5b6780'>{h(ylabel)}</text>"
        f"{''.join(bars)}</svg>"
    )


def hbar_chart_svg(items: list[tuple[str, float]], color: str = "#c45c26") -> str:
    if not items:
        return "<p>没有可绘图的数据。</p>"
    max_v = max(v for _, v in items) or 1
    height = 36 + 28 * len(items)
    bars = []
    for i, (label, val) in enumerate(items):
        bw = 20 if max_v == 0 else round(360 * val / max_v)
        y = 20 + i * 28
        bars.append(
            f"<text x='8' y='{y+12}' font-size='12' fill='#1b2550'>{h(label)}</text>"
            f"<rect x='96' y='{y}' width='{bw}' height='16' rx='3' fill='{color}'/>"
            f"<text x='{104+bw}' y='{y+13}' font-size='12' fill='#1b2550'>{int(val)}</text>"
        )
    return (
        f"<svg viewBox='0 0 640 {height}' width='100%' height='{height}' "
        "xmlns='http://www.w3.org/2000/svg' role='img'>"
        f"{''.join(bars)}</svg>"
    )


def pie_chart_svg(items: list[tuple[str, float]]) -> str:
    if not items:
        return "<p>没有可绘图的数据。</p>"
    total = sum(v for _, v in items) or 1
    colors = ["#2a5fff", "#c45c26", "#0a7a4a", "#b08900", "#7a5a00", "#5b6780", "#3d6b9a"]
    cx, cy, r = 180, 120, 78
    angle = -90.0
    slices = []
    legend = []
    for i, (label, val) in enumerate(items):
        frac = val / total
        sweep = frac * 360
        a0 = math.radians(angle)
        a1 = math.radians(angle + sweep)
        x0, y0 = cx + r * math.cos(a0), cy + r * math.sin(a0)
        x1, y1 = cx + r * math.cos(a1), cy + r * math.sin(a1)
        large = 1 if sweep > 180 else 0
        color = colors[i % len(colors)]
        slices.append(
            f"<path d='M {cx} {cy} L {x0:.1f} {y0:.1f} A {r} {r} 0 {large} 1 {x1:.1f} {y1:.1f} Z' fill='{color}'/>"
        )
        legend.append(
            f"<rect x='300' y='{18+i*22}' width='12' height='12' fill='{color}'/>"
            f"<text x='318' y='{29+i*22}' font-size='12' fill='#1b2550'>{h(label)} {int(val)}</text>"
        )
        angle += sweep
    return (
        "<svg viewBox='0 0 640 240' width='100%' height='240' xmlns='http://www.w3.org/2000/svg' role='img'>"
        f"{''.join(slices)}{''.join(legend)}</svg>"
    )


def interior_layer_svg() -> str:
    return """
<svg viewBox="0 0 640 260" width="100%" height="260" xmlns="http://www.w3.org/2000/svg" role="img">
  <circle cx="220" cy="130" r="100" fill="#f4efe3" stroke="#1b2550"/>
  <circle cx="220" cy="130" r="78" fill="#d7e4ff" stroke="#2a5fff"/>
  <circle cx="220" cy="130" r="50" fill="#f3d9c4" stroke="#c45c26"/>
  <circle cx="220" cy="130" r="24" fill="#f7f1d6" stroke="#b08900"/>
  <text x="220" y="126" text-anchor="middle" font-size="12" fill="#1b2550">金属核</text>
  <text x="220" y="142" text-anchor="middle" font-size="11" fill="#7a5a00">高电导率</text>
  <text x="360" y="70" font-size="13" fill="#1b2550">壳层：低电导率，短周期先看到</text>
  <text x="360" y="108" font-size="13" fill="#2a5fff">海洋 / 岩浆层：高导，感应最强</text>
  <text x="360" y="146" font-size="13" fill="#c45c26">地幔：中等电导率</text>
  <text x="360" y="184" font-size="13" fill="#b08900">金属核：长周期才能约束</text>
  <text x="320" y="242" text-anchor="middle" font-size="12" fill="#5b6780">电导率随深度分层，对应不同探测周期</text>
</svg>
""".strip()


def amplitude_curve_svg() -> str:
    amp, phase = [], []
    for i in range(12):
        x = 70 + i * 42
        amp.append(f"{x},{188 - 90 * (1 - math.exp(-(i+1)/4)):.1f}")
        phase.append(f"{x},{80 + 70 * math.exp(-(i+1)/5):.1f}")
    return f"""
<svg viewBox="0 0 640 240" width="100%" height="240" xmlns="http://www.w3.org/2000/svg" role="img">
  <line x1="70" y1="200" x2="600" y2="200" stroke="#1b2550"/>
  <line x1="70" y1="200" x2="70" y2="28" stroke="#1b2550"/>
  <polyline points="{' '.join(amp)}" fill="none" stroke="#2a5fff" stroke-width="2.5"/>
  <polyline points="{' '.join(phase)}" fill="none" stroke="#c45c26" stroke-width="2.5" stroke-dasharray="6 4"/>
  <text x="90" y="44" font-size="12" fill="#2a5fff">振幅（随内部电导率升高而增大）</text>
  <text x="90" y="64" font-size="12" fill="#c45c26">相位滞后（对深度更敏感）</text>
  <text x="320" y="228" text-anchor="middle" font-size="13" fill="#1b2550">周期 →</text>
</svg>
""".strip()


def induction_flow_svg() -> str:
    boxes = [
        (30, 90, "变化外源场 B₀"),
        (175, 90, "涡旋电场"),
        (300, 90, "感应电流"),
        (430, 90, "次级场 B_ind"),
    ]
    rects = []
    for i, (x, y, t) in enumerate(boxes):
        rects.append(
            f"<rect x='{x}' y='{y}' width='120' height='52' rx='8' fill='#eef3fb' stroke='#2a5fff'/>"
            f"<text x='{x+60}' y='{y+32}' text-anchor='middle' font-size='13' fill='#1b2550'>{t}</text>"
        )
        if i < len(boxes) - 1:
            rects.append(f"<path d='M {x+122} {y+26} L {x+148} {y+26}' stroke='#1b2550' stroke-width='2'/>")
            rects.append(f"<polygon points='{x+148},{y+26} {x+140},{y+21} {x+140},{y+31}' fill='#1b2550'/>")
    return (
        "<svg viewBox='0 0 640 230' width='100%' height='230' xmlns='http://www.w3.org/2000/svg' role='img'>"
        + "".join(rects)
        + "<text x='320' y='190' text-anchor='middle' font-size='13' fill='#5b6780'>观测到的是叠加场，需要把外源、电离层电流和内部感应分开</text>"
        + "</svg>"
    )


def period_band_svg() -> str:
    return """
<svg viewBox="0 0 640 220" width="100%" height="220" xmlns="http://www.w3.org/2000/svg" role="img">
  <rect x="40" y="40" width="170" height="120" rx="8" fill="#eef3fb" stroke="#2a5fff"/>
  <text x="125" y="88" text-anchor="middle" font-size="14" fill="#1b2550">短周期</text>
  <text x="125" y="112" text-anchor="middle" font-size="13" fill="#2a5fff">浅部壳层</text>
  <rect x="235" y="40" width="170" height="120" rx="8" fill="#f8e6dc" stroke="#c45c26"/>
  <text x="320" y="88" text-anchor="middle" font-size="14" fill="#1b2550">中周期</text>
  <text x="320" y="112" text-anchor="middle" font-size="13" fill="#c45c26">海洋 / 岩浆层</text>
  <rect x="430" y="40" width="170" height="120" rx="8" fill="#f7f1d6" stroke="#b08900"/>
  <text x="515" y="88" text-anchor="middle" font-size="14" fill="#1b2550">长周期</text>
  <text x="515" y="112" text-anchor="middle" font-size="13" fill="#b08900">地幔 / 金属核</text>
  <text x="320" y="198" text-anchor="middle" font-size="12" fill="#5b6780">频谱不完整会直接造成深度误判</text>
</svg>
""".strip()


def object_counts(blocks: list[dict]) -> list[tuple[str, float]]:
    c = Counter()
    for b in blocks or []:
        for obj in b.get("planets") or b.get("objects") or []:
            if obj in {"磁感应", "电导率", "磁层", "电离层", "感应"}:
                continue
            c[obj] += 1
    return [(k, float(v)) for k, v in c.most_common(8)]


def csv_mean_items(uploads: list[dict]) -> list[tuple[str, float]]:
    items = []
    for u in uploads or []:
        stats = (u.get("csv") or {}).get("stats") or []
        for s in stats[:8]:
            name = str(s.get("name") or "列")[:10]
            items.append((name, float(s.get("mean") or 0)))
    return items


def make_review_figures(question: str, note: str, blocks: list[dict], uploads: list[dict] | None = None, rerun: int = 0) -> dict[str, str]:
    uploads = uploads or []
    variant = max(0, int(rerun or 0)) % 3
    draft = f"（第{max(1, int(rerun or 0) + 1)}稿）" if rerun else ""
    figs: dict[str, str] = {"after_intro": "", "after_s2": "", "after_s3": "", "extra": ""}
    n = 1
    mag = mag_topic(question, note)
    if mag and variant == 0:
        figs["after_intro"] = paper_fig(
            induction_schematic_svg(),
            f"图{n}　类地行星磁感应示意：变化外源场、导电层中的感应电流与次级感应磁场{draft}",
        )
        n += 1
        figs["after_s2"] = paper_fig(
            skin_depth_svg(),
            f"图{n}　趋肤深度随周期增大的示意，说明短周期约束浅部、长周期约束深部{draft}",
        )
        n += 1
    elif mag and variant == 1:
        figs["after_intro"] = paper_fig(
            interior_layer_svg(),
            f"图{n}　内部电导率分层示意：壳层、海洋/岩浆层、地幔与金属核{draft}",
        )
        n += 1
        figs["after_s2"] = paper_fig(
            amplitude_curve_svg(),
            f"图{n}　感应响应振幅与相位随周期变化的示意{draft}",
        )
        n += 1
    elif mag:
        figs["after_intro"] = paper_fig(
            induction_flow_svg(),
            f"图{n}　磁感应观测链条：外源场、感应电流、次级场与叠加干扰{draft}",
        )
        n += 1
        figs["after_s2"] = paper_fig(
            period_band_svg(),
            f"图{n}　不同周期对应的探测深度{draft}",
        )
        n += 1
    objs = object_counts(blocks)
    if objs:
        if variant == 0:
            chart = bar_chart_svg(objs, "文献篇数", "#2a5fff")
            cap = f"图{n}　主要对象分布（柱状图）{draft}"
        elif variant == 1:
            chart = hbar_chart_svg(objs, "#c45c26")
            cap = f"图{n}　主要对象分布（条形图）{draft}"
        else:
            chart = pie_chart_svg(objs)
            cap = f"图{n}　主要对象分布（构成）{draft}"
        figs["after_s3"] = paper_fig(chart, cap)
        n += 1
    csv_items = csv_mean_items(uploads)
    if csv_items:
        figs["extra"] = paper_fig(
            bar_chart_svg(csv_items, "均值", "#0a7a4a"),
            f"图{n}　上传表格各列均值（按原文数值）{draft}",
        )
    return figs


def section_figure(papers: list[dict], question: str = "", note: str = "", uploads: list | None = None, rerun: int = 0, llm_meta: dict | None = None) -> str:
    papers = on_topic_papers(papers, question, note, 0)
    blocks = digest_blocks(papers, question, note, 0)
    figs = make_review_figures(question, note, blocks, uploads or [], rerun)
    body = "".join(v for v in (figs["after_intro"], figs["after_s2"], figs["after_s3"], figs["extra"]) if v)
    note_html = as_paras((llm_meta or {}).get("figure_note") or "")
    if not body:
        return (
            "<h1>图表生成与插入</h1>"
            + (note_html or "<p>目前还没有可写入论文的研究图。请先保证检索到对题文献，或上传带数值的表格。</p>")
        )
    lead = note_html or "<p>下面这些图会写入论文正文：感应机制示意、趋肤深度分层约束，以及本次文献的对象分布。</p>"
    return (
        "<h1>图表生成与插入</h1>"
        + lead
        + f"{body}"
        + "<p>图题已按出现顺序编号，正文对应章节会引用这些图。</p>"
    )


def section_refs(papers: list[dict], rerun: int = 0, llm_meta: dict | None = None) -> str:
    items = list(papers or [])
    if rerun % 2:
        items = sorted(items, key=lambda p: p.get("year") or 0, reverse=True)
    llm_items = (llm_meta or {}).get("refs_items") or []
    if isinstance(llm_items, list) and any(str(x).strip() for x in llm_items):
        refs = [str(x).strip() for x in llm_items if str(x).strip()]
    else:
        refs = [gb_t_ref(p, i + 1) for i, p in enumerate(items)]
    body = "".join(f"<p>{h(r)}</p>" for r in refs) or "<p>暂无参考文献。</p>"
    lead = str((llm_meta or {}).get("refs_lead") or "").strip()
    lead_html = as_paras(lead) if lead else (
        f"<p>目标格式：<span class='highlight'>GB/T 7714</span>。共 {len(refs)} 条，来自本次检索。</p>"
    )
    return (
        "<h1>参考文献格式化</h1>"
        + lead_html
        + body
    )


def p_indent(text: str) -> str:
    return f"<p class='indent'>{text}</p>"


def three_line_table(caption: str, headers: list[str], rows: list[list[str]]) -> str:
    head = "".join(f"<th>{h(col)}</th>" for col in headers)
    body = "".join("<tr>" + "".join(f"<td>{cell}</td>" for cell in row) + "</tr>" for row in rows)
    return (
        f"<table class='paper-table'><caption>{h(caption)}</caption>"
        f"<thead><tr>{head}</tr></thead><tbody>{body}</tbody></table>"
    )


def build_paper(question: str, note: str, papers: list[dict], uploads: list[dict], rerun: int = 0, fig_rerun: int = 0, review_rerun: int = 0, expand: int = 0, parts: dict | None = None, llm_meta: dict | None = None) -> str:
    papers = on_topic_papers(papers, question, note, review_rerun)
    title = make_title(question)
    keywords = make_keywords(question, papers)
    csv_blocks = [u for u in uploads if u.get("csv") and u["csv"].get("stats")]
    blocks = digest_blocks(papers, question, note, review_rerun)
    if not blocks:
        abstract_zh = f"关于「{h(question)}」，现有材料还写不出可核对的结论。请调整补充说明后重新检索。"
        abstract_en = f"No on-topic findings were available for “{h(question)}”."
        parts = parts or {
            "intro": p_indent(abstract_zh),
            "t2": "2　电磁感应与电导率",
            "t3": "3　类地行星与卫星中的感应响应",
            "t4": "4　磁层、电离层与内外场分离",
            "body2": p_indent("目前没有可写入的对题文献。"),
            "body3": p_indent("目前没有可写入的对题文献。"),
            "body4": p_indent("目前没有可写入的对题文献。"),
            "disc": p_indent("在获得对题文献之前，还不能归纳明确的不足。"),
            "conc": p_indent(abstract_zh),
            "abstract_zh": abstract_zh,
            "abstract_en": abstract_en,
        }
    elif parts is None:
        parts = review_parts(question, note, blocks, rerun, expand)

    kw_map = {z: e for z, e in GLOSSARY if e}
    kw_map["类地行星磁感应"] = "terrestrial planet magnetic induction"
    kw_map["导电性"] = "conductivity"
    kw_zh = "；".join(keywords)
    kw_en_list = []
    for k in keywords:
        e = kw_map.get(k, k)
        if e not in kw_en_list:
            kw_en_list.append(e)
    kw_en = "; ".join(kw_en_list)

    extra_tables = ""
    extra_html = ""
    if csv_blocks:
        extra_html = "<h2 class='sec'>附录　上传数据</h2>"
        for offset, u in enumerate(csv_blocks):
            csv_stats = u["csv"]
            rows = [
                [h(s["name"]), str(s["n"]), str(s["mean"]), str(s["stdev"]), str(s["min"]), str(s["max"])]
                for s in csv_stats["stats"]
            ]
            extra_tables += three_line_table(
                f"表{offset + 2}  {csv_stats['name']}（{csv_stats['rows']} 行）",
                ["变量", "n", "均值", "标准差", "最小", "最大"],
                rows,
            )

    upload_extracts = []
    for u in uploads:
        text = u.get("text") or ""
        if len(text) < 80:
            continue
        fake = {"title": u.get("name"), "abstract": text[:4000], "authors": ["上传材料"], "year": ""}
        claim = paper_claim(paper_digest(fake, question, note))
        if claim:
            upload_extracts.append(p_indent(h(claim)))
    if upload_extracts:
        extra_html = (extra_html or "<h2 class='sec'>附录　上传材料</h2>") + "".join(upload_extracts)

    table1 = ""
    if blocks:
        rows = []
        for b in blocks:
            rows.append(
                [
                    h("、".join((b.get("planets") or b.get("objects") or [])[:3]) or "—"),
                    h(strip_wrap(b.get("finding") or b.get("purpose") or "—")[:48]),
                    cite_list([b["i"]]),
                ]
            )
        table1 = three_line_table("表1  主要对象与约束", ["对象", "约束", "出处"], rows)

    figs = make_review_figures(question, note, blocks, uploads, fig_rerun)
    fig_note = ""
    if mag_topic(question, note) and figs.get("after_intro"):
        fig_note = p_indent("图1给出感应机制，图2给出分层约束，图3给出对象分布。")
    elif figs.get("after_s3") or figs.get("extra"):
        fig_note = p_indent("下文用图给出对象分布；若有上传数值表，均值图一并给出。")
    extra_fig = as_paras((llm_meta or {}).get("figure_note") or "")
    if extra_fig:
        fig_note += extra_fig

    refs = "".join(f"<p>{h(gb_t_ref(p, i + 1))}</p>" for i, p in enumerate(papers)) or "<p>暂无参考文献。</p>"

    return f"""
<h1 class="paper-title">{h(title)}</h1>
<div class="paper-abs-block">
  <p><span class="lab">摘　要：</span>{parts["abstract_zh"]}</p>
  <p><span class="lab">关键词：</span>{h(kw_zh)}</p>
  <p><span class="lab">Abstract: </span>{parts["abstract_en"]}</p>
  <p><span class="lab">Keywords: </span>{h(kw_en)}</p>
</div>
<h2 class="sec">1　引言</h2>
{parts["intro"]}{fig_note}
{figs.get("after_intro") or ""}
<h2 class="sec">{h(parts["t2"])}</h2>
{parts["body2"]}
{figs.get("after_s2") or ""}
<h2 class="sec">{h(parts["t3"])}</h2>
{parts["body3"]}
{figs.get("after_s3") or ""}
<h2 class="sec">{h(parts["t4"])}</h2>
{parts["body4"]}
<h2 class="sec">5　讨论与尚未解决的问题</h2>
{parts["disc"]}
<h2 class="sec">6　结论</h2>
{parts["conc"]}
{table1}
{figs.get("extra") or ""}
{extra_html}{extra_tables}
<h2 class="sec">参考文献</h2>
<div class="paper-refs">{refs}</div>
""".strip()


def build_sections(question: str, papers: list[dict], uploads: list[dict], note: str = "", en_query: str = "", rerun: int = 0, module: str = "", repair: dict | None = None, variants: dict | None = None, expand: int = 0, parts: dict | None = None, llm_meta: dict | None = None) -> dict[str, str]:
    variants = variants or {}
    def n(mid: str) -> int:
        if module == mid:
            return max(0, int(rerun or 0))
        return max(0, int(variants.get(mid) or 0))
    return {
        "module-lit-search": section_lit(papers, question, note, en_query, repair if module == "module-lit-search" else None, llm_meta),
        "module-parse": section_parse(papers, uploads, note, n("module-parse"), llm_meta),
        "module-review": section_review(papers, question, note, n("module-review"), expand, parts),
        "module-data": section_data(papers, uploads, question, note, n("module-data"), llm_meta),
        "module-figure": section_figure(papers, question, note, uploads, n("module-figure"), llm_meta),
        "module-reference": section_refs(papers, n("module-reference"), llm_meta),
    }


LLM_PRESETS = {
    "deepseek": ("https://api.deepseek.com/v1", "deepseek-chat"),
    "qwen": ("https://dashscope.aliyuncs.com/compatible-mode/v1", "qwen-plus"),
    "openai": ("https://api.openai.com/v1", "gpt-4o"),
}


def writer_endpoint(writer: dict) -> tuple[str, str, str]:
    provider = str(writer.get("provider") or "custom").strip().lower()
    preset_base, preset_model = LLM_PRESETS.get(provider, ("", ""))
    base = str(writer.get("base_url") or os.environ.get("PAPERAGENT_API_BASE") or preset_base).strip()
    model = str(writer.get("model") or os.environ.get("PAPERAGENT_MODEL") or preset_model).strip()
    key = str(writer.get("api_key") or os.environ.get("PAPERAGENT_API_KEY") or "").strip()
    if not key:
        raise RuntimeError("未填写 API Key")
    if not base:
        raise RuntimeError("未填写 API 地址")
    if not model:
        raise RuntimeError("未填写模型名")
    return base, model, key


def chat_completions(base_url: str, api_key: str, model: str, messages: list[dict], timeout: int = 120) -> str:
    url = base_url.rstrip("/")
    if not url.endswith("/chat/completions"):
        url = url + "/chat/completions"
    body = json.dumps(
        {"model": model, "messages": messages, "temperature": 0.3},
        ensure_ascii=False,
    ).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=body,
        headers={
            "Content-Type": "application/json",
            "Authorization": "Bearer " + api_key,
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        err = exc.read().decode("utf-8", errors="replace")[:400]
        raise RuntimeError("HTTP %s：%s" % (exc.code, err)) from exc
    except urllib.error.URLError as exc:
        raise RuntimeError("无法连接接口：%s" % exc.reason) from exc
    try:
        return str(data["choices"][0]["message"]["content"] or "").strip()
    except (KeyError, IndexError, TypeError) as exc:
        raise RuntimeError("接口返回格式无法解析") from exc


def parse_llm_json(text: str) -> dict:
    raw = (text or "").strip()
    if raw.startswith("```"):
        raw = re.sub(r"^```(?:json)?\s*", "", raw)
        raw = re.sub(r"\s*```$", "", raw)
    start = raw.find("{")
    end = raw.rfind("}")
    if start < 0 or end <= start:
        raise RuntimeError("大模型没有返回 JSON")
    data = json.loads(raw[start : end + 1])
    if not isinstance(data, dict):
        raise RuntimeError("大模型 JSON 不是对象")
    return data


def as_paras(value) -> str:
    if isinstance(value, list):
        return html_paras([h(str(x).strip()) for x in value if str(x).strip()])
    text = str(value or "").strip()
    if not text:
        return ""
    if "<p" in text.lower():
        text = re.sub(r"(?is)<script.*?>.*?</script>", "", text)
        return text
    bits = [p.strip() for p in re.split(r"\n{2,}", text) if p.strip()]
    return html_paras([h(p.replace("\n", "")) for p in bits])


def literature_blob(papers: list[dict]) -> str:
    lines = []
    for i, p in enumerate(papers, 1):
        abs_ = re.sub(r"\s+", " ", (p.get("abstract") or "")[:1200]).strip()
        authors = ", ".join((p.get("authors") or [])[:3])
        ident = p.get("doi") or p.get("arxiv_id") or ""
        src = p.get("source") or ""
        lines.append(
            "[%s] %s. %s. %s. %s DOI/arXiv:%s\n%s"
            % (
                i,
                authors or "佚名",
                p.get("year") or "",
                p.get("title") or "",
                src,
                ident,
                abs_,
            )
        )
    return "\n\n".join(lines)


def cite_rules(papers: list[dict]) -> str:
    n = len(papers or [])
    need = min_cite_count(n, 0.7)
    nums = "、".join(f"[{i}]" for i in range(1, n + 1)) or "无"
    return (
        f"只能引用下面列出的 {n} 篇文献，编号必须是 {nums}。"
        "禁止编造未列出的作者、年份、DOI、arXiv 编号或新文献。"
        f"全文至少引用其中 {need} 篇，句末用[n]。"
        "不要写某某指出、该文考察了、加以讨论。"
    )


def parts_from_llm_data(data: dict, question: str) -> dict:
    return {
        "intro": as_paras(data.get("intro")),
        "t2": str(data.get("t2") or "2　方法与机制"),
        "t3": str(data.get("t3") or "3　主要认识"),
        "t4": str(data.get("t4") or "4　对象与观测"),
        "body2": as_paras(data.get("body2")),
        "body3": as_paras(data.get("body3")),
        "body4": as_paras(data.get("body4")),
        "disc": as_paras(data.get("disc")),
        "conc": as_paras(data.get("conc")),
        "abstract_zh": str(data.get("abstract_zh") or "").strip() or f"本文讨论{question}。",
        "abstract_en": str(data.get("abstract_en") or "").strip()
        or "This paper discusses the topic using the retrieved literature.",
    }


def meta_from_llm_data(data: dict) -> dict:
    comments = data.get("lit_comments") if isinstance(data.get("lit_comments"), list) else []
    rows = data.get("data_rows") if isinstance(data.get("data_rows"), list) else []
    points = data.get("parse_points") if isinstance(data.get("parse_points"), list) else []
    refs_items = data.get("refs_items") if isinstance(data.get("refs_items"), list) else []
    return {
        "lit_lead": str(data.get("lit_lead") or "").strip(),
        "lit_comments": comments,
        "parse_lead": str(data.get("parse_lead") or "").strip(),
        "parse_points": [str(x).strip() for x in points if str(x).strip()],
        "data_lead": str(data.get("data_lead") or "").strip(),
        "data_rows": rows,
        "figure_note": str(data.get("figure_note") or "").strip(),
        "refs_lead": str(data.get("refs_lead") or "").strip(),
        "refs_items": [str(x).strip() for x in refs_items if str(x).strip()],
    }


def merge_meta(base: dict | None, extra: dict | None) -> dict:
    out = dict(base or {})
    for key, value in (extra or {}).items():
        if value in (None, "", [], {}):
            continue
        out[key] = value
    return out


def llm_ask(writer: dict, user: str, timeout: int = 180) -> dict:
    base, model, key = writer_endpoint(writer)
    content = chat_completions(
        base,
        key,
        model,
        [
            {"role": "system", "content": "你是中文学术写作助手。只输出 JSON，不要解释，不要用 Markdown 围栏。"},
            {"role": "user", "content": user},
        ],
        timeout=timeout,
    )
    return parse_llm_json(content)


def llm_pipeline(question: str, note: str, papers: list[dict], instruction: str, expand: int, writer: dict) -> tuple[dict, dict]:
    length = "每个主体章节至少4段，全文不少于2500汉字。" if int(expand or 0) >= 3 else "每个主体章节至少2段，写成完整中文论文。"
    extra = ("用户补充：" + instruction.strip()) if instruction.strip() else ""
    prompt = (
        "检索已经完成。请用中文撰写六个步骤的全部文字。\n"
        f"{cite_rules(papers)}\n"
        "用本文……口吻。不要编造未给出的数据。\n"
        f"{length}\n研究问题：{question}\n补充说明：{note or '无'}\n{extra}\n\n文献：\n"
        + literature_blob(papers)
        + "\n\n只输出一个 JSON 对象，键必须包括：\n"
        "lit_lead（字符串，说明如何检索与筛选）；"
        "lit_comments（数组，每项 {i:文献序号, reason:保留理由}）；"
        "parse_lead（字符串）；parse_points（中文要点字符串数组）；"
        "abstract_zh, abstract_en, t2, t3, t4；"
        "intro, body2, body3, body4, disc, conc（均为字符串数组）；"
        "data_lead；data_rows（数组，每项 {object, constraint, cite}）；"
        "figure_note（字符串，解释将插入论文的图在说明什么）；"
        "refs_lead；refs_items（GB/T 7714 格式的字符串数组，序号从[1]开始）。"
    )
    data = llm_ask(writer, prompt)
    return parts_from_llm_data(data, question), meta_from_llm_data(data)


STEP_WRITE_HINT = {
    "module-lit-search": "只写 lit_lead 和 lit_comments。lit_comments 每项为 {i, reason}。",
    "module-parse": "只写 parse_lead 和 parse_points（中文要点数组）。",
    "module-review": "只写 abstract_zh, abstract_en, t2, t3, t4, intro, body2, body3, body4, disc, conc。段落字段用字符串数组。",
    "module-data": "只写 data_lead 和 data_rows。data_rows 每项 {object, constraint, cite}。",
    "module-figure": "只写 figure_note，说明这些图与研究问题的关系。",
    "module-reference": "只写 refs_lead 和 refs_items。refs_items 必须是 GB/T 7714 条目。",
}


def llm_one_step(
    module: str,
    question: str,
    note: str,
    papers: list[dict],
    instruction: str,
    expand: int,
    writer: dict,
    keep_parts: dict | None,
    keep_meta: dict | None,
) -> tuple[dict | None, dict]:
    hint = STEP_WRITE_HINT.get(module) or "按该步骤需要的键输出 JSON。"
    extra = ("用户补充：" + instruction.strip()) if instruction.strip() else ""
    prompt = (
        f"检索已经完成。请用中文重写步骤「{module}」。\n{hint}\n"
        f"{cite_rules(papers)}\n"
        "不要编造未给出的数据。\n"
        f"研究问题：{question}\n补充说明：{note or '无'}\n{extra}\n\n文献：\n"
        + literature_blob(papers)
        + "\n\n只输出 JSON。"
    )
    data = llm_ask(writer, prompt, timeout=120)
    meta = merge_meta(keep_meta, meta_from_llm_data(data))
    parts = keep_parts
    if module in ("", "module-review") or data.get("intro") or data.get("abstract_zh"):
        if data.get("intro") or data.get("body2") or data.get("abstract_zh"):
            parts = parts_from_llm_data(data, question)
    return parts, meta


def run_payload(body: dict) -> tuple[int, dict]:
    question = str(body.get("question") or "").strip()
    note = str(body.get("note") or "").strip()
    files = body.get("files") if isinstance(body.get("files"), list) else []
    if not question:
        return 400, {"ok": False, "error": "请先填写研究问题"}
    try:
        start = int(body.get("start") or 0)
        rerun = int(body.get("rerun") or 0)
        sort_by = str(body.get("sort") or "relevance")
        module = str(body.get("module") or "")
        exclude = body.get("exclude") if isinstance(body.get("exclude"), list) else []
        instruction = str(body.get("instruction") or "")
        try:
            req_expand = int(body.get("expand") or 0)
        except (TypeError, ValueError):
            req_expand = 0
        note, expand = split_write_intent(note, instruction)
        expand = max(expand, req_expand, 1)
        keep_papers = body.get("keep_papers") if isinstance(body.get("keep_papers"), list) else None
        variants = body.get("variants") if isinstance(body.get("variants"), dict) else {}
        search_note = "；".join(x for x in (note, instruction) if str(x).strip()) or note
        repair = None
        if module == "module-lit-search" and keep_papers:
            papers, en_query, repair = repair_literature(
                question, search_note, keep_papers, limit=12, rerun=rerun
            )
        elif keep_papers and module not in ("", "module-lit-search"):
            papers = [p for p in keep_papers if isinstance(p, dict) and p.get("title")]
            en_query = to_english_query(f"{question} {strip_year_constraints(note)}".strip())
        else:
            papers, en_query = search_topic(
                question, search_note, limit=12, start=start, sort_by=sort_by, exclude=exclude
            )
        papers = fill_year_range(papers, question, search_note, "", limit=12)
    except Exception as exc:
        return 502, {"ok": False, "error": f"检索失败：{exc}"}
    uploads = parse_uploads(files)
    enrich_papers_fulltext(papers, limit=8)
    review_n = rerun if module == "module-review" else int(variants.get("module-review") or 0)
    fig_n = rerun if module == "module-figure" else int(variants.get("module-figure") or 0)
    for p in papers:
        p["digest"] = paper_digest(p, question, note, review_n)
    year_lo, year_hi = parse_year_range(question, note, instruction)
    papers = [
        p
        for p in papers
        if not (p.get("digest") or {}).get("off_topic") and year_ok(p, year_lo, year_hi)
    ]
    writer = body.get("writer") if isinstance(body.get("writer"), dict) else {}
    writer_mode = str(writer.get("mode") or "local").strip().lower()
    keep_parts = body.get("keep_parts") if isinstance(body.get("keep_parts"), dict) else None
    keep_meta = body.get("keep_meta") if isinstance(body.get("keep_meta"), dict) else None
    parts = None
    llm_meta = None
    if writer_mode == "api" and papers:
        try:
            if module in ("",) or (instruction and module in ("", "module-review")):
                parts, llm_meta = llm_pipeline(question, note, papers, instruction, expand, writer)
            elif module:
                parts, llm_meta = llm_one_step(
                    module, question, note, papers, instruction, expand, writer, keep_parts, keep_meta
                )
            else:
                parts, llm_meta = keep_parts, keep_meta
        except Exception as exc:
            return 502, {"ok": False, "error": f"大模型调用失败：{exc}"}
    sections = build_sections(question, papers, uploads, note, en_query, rerun, module, repair, variants, expand, parts, llm_meta)
    paper = build_paper(
        question, note, papers, uploads, rerun, fig_rerun=fig_n, review_rerun=review_n, expand=expand, parts=parts, llm_meta=llm_meta
    )
    refs = [gb_t_ref(p, i + 1) for i, p in enumerate(papers)]
    closure = closure_check(papers, paper, question, note, instruction)
    slim = []
    for p in papers:
        item = {k: v for k, v in p.items() if k not in {"abstract", "fulltext", "score", "excerpts"}}
        item["abstract"] = (p.get("abstract") or "")[:2500]
        item["fulltext"] = (p.get("fulltext") or "")[:8000]
        item["digest"] = p.get("digest") or {}
        item["parse_kind"] = p.get("parse_kind") or "摘要"
        item["score"] = p.get("score") or 0
        slim.append(item)
    out = {
        "ok": True,
        "question": question,
        "note": note,
        "query": en_query,
        "source": "arxiv",
        "papers": slim,
        "references": refs,
        "count": len(papers),
        "sections": sections,
        "paper": paper,
        "repair": repair,
        "parts": parts,
        "llm_meta": llm_meta,
        "writer_mode": writer_mode,
        "year_range": [year_lo, year_hi] if year_lo or year_hi else None,
        "closure": closure,
    }
    try:
        rec = save_history_record(out)
        out["history_id"] = rec.get("id")
    except Exception:
        out["history_id"] = None
    return 200, out


def _history_stem(question: str) -> str:
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    title = re.sub(r'[\\/:*?"<>|\s]+', "_", (question or "论文").strip())[:36].strip("_") or "论文"
    return f"{stamp}-{title}"


def save_history_record(payload: dict) -> dict:
    HISTORY_DIR.mkdir(parents=True, exist_ok=True)
    stem = _history_stem(str(payload.get("question") or ""))
    papers = []
    for p in payload.get("papers") or []:
        if not isinstance(p, dict):
            continue
        papers.append(
            {
                "title": p.get("title"),
                "authors": p.get("authors") or [],
                "year": p.get("year"),
                "doi": p.get("doi"),
                "arxiv_id": p.get("arxiv_id"),
                "url": p.get("url"),
                "source": p.get("source"),
                "journal": p.get("journal"),
                "published": p.get("published"),
                "abstract": (p.get("abstract") or "")[:2500],
                "fulltext": (p.get("fulltext") or "")[:8000],
                "digest": p.get("digest") if isinstance(p.get("digest"), dict) else {},
                "parse_kind": p.get("parse_kind") or "",
                "score": p.get("score") or 0,
            }
        )
    rec = {
        "id": stem,
        "saved_at": datetime.now().isoformat(timespec="seconds"),
        "question": payload.get("question") or "",
        "note": payload.get("note") or "",
        "paper": payload.get("paper") or "",
        "papers": papers,
        "references": payload.get("references") or [],
        "sections": payload.get("sections") or {},
        "parts": payload.get("parts"),
        "llm_meta": payload.get("llm_meta"),
        "year_range": payload.get("year_range"),
        "closure": payload.get("closure"),
        "count": payload.get("count") or len(papers),
        "snapshot": payload.get("snapshot") if isinstance(payload.get("snapshot"), dict) else {},
    }
    (HISTORY_DIR / f"{stem}.json").write_text(json.dumps(rec, ensure_ascii=False), encoding="utf-8")
    if rec["paper"]:
        html_doc = (
            "<!DOCTYPE html><html lang=\"zh-CN\"><head><meta charset=\"utf-8\">"
            f"<title>{h(rec['question'] or '论文')}</title></head><body>{rec['paper']}</body></html>"
        )
        (HISTORY_DIR / f"{stem}.html").write_text(html_doc, encoding="utf-8")
    rec["file"] = f"{stem}.json"
    return rec


def list_history() -> dict:
    HISTORY_DIR.mkdir(parents=True, exist_ok=True)
    papers = []
    for path in sorted(HISTORY_DIR.glob("*.json"), key=lambda p: p.stat().st_mtime, reverse=True):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        papers.append(
            {
                "id": data.get("id") or path.stem,
                "saved_at": data.get("saved_at") or "",
                "question": data.get("question") or path.stem,
                "note": (data.get("note") or "")[:120],
                "count": data.get("count") or len(data.get("papers") or []),
                "has_paper": bool(data.get("paper")),
            }
        )
    return {"ok": True, "dir": str(HISTORY_DIR), "items": papers}


def delete_history(item_id: str) -> bool:
    if not item_id or "/" in item_id or "\\" in item_id:
        return False
    removed = False
    for suffix in (".json", ".html"):
        path = HISTORY_DIR / f"{item_id}{suffix}"
        if path.is_file():
            path.unlink()
            removed = True
    return removed


def clear_history() -> int:
    HISTORY_DIR.mkdir(parents=True, exist_ok=True)
    n = 0
    for path in list(HISTORY_DIR.glob("*.json")) + list(HISTORY_DIR.glob("*.html")):
        if path.is_file():
            path.unlink()
            n += 1
    return n


def patch_history(item_id: str, patch: dict) -> dict | None:
    rec = load_history(item_id)
    if rec is None:
        return None
    snap = rec.get("snapshot") if isinstance(rec.get("snapshot"), dict) else {}
    incoming = patch.get("snapshot") if isinstance(patch.get("snapshot"), dict) else {}
    snap.update(incoming)
    rec["snapshot"] = snap
    for key in ("sections", "paper", "papers", "references", "parts", "llm_meta", "note", "question", "year_range", "closure"):
        if key in patch and patch[key] is not None:
            rec[key] = patch[key]
    if rec.get("papers"):
        rec["count"] = len(rec["papers"])
    path = HISTORY_DIR / f"{item_id}.json"
    path.write_text(json.dumps(rec, ensure_ascii=False), encoding="utf-8")
    return rec


def load_history(item_id: str) -> dict | None:
    if not item_id or "/" in item_id or "\\" in item_id:
        return None
    path = HISTORY_DIR / f"{item_id}.json"
    if not path.is_file():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt: str, *args) -> None:
        sys.stderr.write("%s - %s\n" % (self.address_string(), fmt % args))

    def _cors(self) -> None:
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, DELETE, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")

    def _json(self, code: int, payload: dict) -> None:
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self._cors()
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _bytes(self, code: int, data: bytes, content_type: str) -> None:
        self.send_response(code)
        self._cors()
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_OPTIONS(self) -> None:
        self.send_response(204)
        self._cors()
        self.end_headers()

    def do_GET(self) -> None:
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        qs = urllib.parse.parse_qs(parsed.query)
        if path in ("/", "/paperagent_v59.html"):
            raw = HTML_FILE.read_bytes()
            self._bytes(200, raw, "text/html; charset=utf-8")
            return
        if path.startswith("/api/health"):
            self._json(200, {"ok": True, "html": str(HTML_FILE), "steps": 6, "history": str(HISTORY_DIR)})
            return
        if path == "/api/history":
            item_id = (qs.get("id") or [""])[0]
            if item_id:
                rec = load_history(item_id)
                if not rec:
                    self._json(404, {"ok": False, "error": "没有这条历史"})
                    return
                self._json(200, {"ok": True, "item": rec})
                return
            self._json(200, list_history())
            return
        self._json(404, {"ok": False, "error": "not found"})

    def do_POST(self) -> None:
        length = int(self.headers.get("Content-Length") or 0)
        raw = self.rfile.read(length) if length else b"{}"
        try:
            body = json.loads(raw.decode("utf-8") or "{}")
        except json.JSONDecodeError:
            self._json(400, {"ok": False, "error": "JSON 无效"})
            return
        parsed = urllib.parse.urlparse(self.path)
        if parsed.path in ("/api/run", "/api/chat"):
            code, payload = run_payload(body if isinstance(body, dict) else {})
            self._json(code, payload)
            return
        if parsed.path == "/api/history":
            body = body if isinstance(body, dict) else {}
            action = str(body.get("action") or "save").strip().lower()
            try:
                if action == "delete":
                    ok = delete_history(str(body.get("id") or ""))
                    if not ok:
                        self._json(404, {"ok": False, "error": "没有这条历史"})
                        return
                    self._json(200, {"ok": True})
                    return
                if action == "clear":
                    n = clear_history()
                    self._json(200, {"ok": True, "removed": n})
                    return
                if action == "replace":
                    clear_history()
                    rec = save_history_record(body)
                    self._json(200, {"ok": True, "id": rec.get("id")})
                    return
                if action == "patch":
                    rec = patch_history(str(body.get("id") or ""), body)
                    if not rec:
                        self._json(404, {"ok": False, "error": "没有这条历史"})
                        return
                    self._json(200, {"ok": True, "id": rec.get("id")})
                    return
                rec = save_history_record(body)
            except Exception as exc:
                self._json(500, {"ok": False, "error": f"保存历史失败：{exc}"})
                return
            self._json(200, {"ok": True, "id": rec.get("id"), "dir": str(HISTORY_DIR)})
            return
        self._json(404, {"ok": False, "error": "not found"})


def main() -> None:
    if not HTML_FILE.exists():
        raise SystemExit(f"找不到前端文件：{HTML_FILE}")
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    print(f"paperagent: http://{HOST}:{PORT}/paperagent_v59.html", flush=True)
    print(f"api:        http://{HOST}:{PORT}/api/run", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
