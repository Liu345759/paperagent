# paperagent

中文文献综述工作区。按六个步骤检索文献、解析、写综述、整理数据、插入图表、格式化 GB/T 7714 参考文献。

完整说明见 [使用手册.md](使用手册.md)。

## 文件

- `paperagent_v59.html`：页面
- `paperagent_bridge.py`：本机接口（`127.0.0.1:8766`）
- `使用手册.md`：使用说明

## 启动

```text
py -3.13 paperagent_bridge.py
```

浏览器打开 `http://127.0.0.1:8766/paperagent_v59.html`。
