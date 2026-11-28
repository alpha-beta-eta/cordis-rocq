# errors：错误处理进模型

设计见 [DESIGN.md](DESIGN.md)。

本目录与现有形式化隔离：

- 代码放在 `errors/theories/`，逻辑名 `CordisErr`，可以 import 核心（`Cordis.*`），核心与
  `theories/Ext/` 不 import 它（`grep -rn CordisErr theories/` 应为空）；
- 有自己的 `_CoqProject` 与 `build.sh`，根目录的构建不变；
- 每个模块给出对核心的保守性定理。

要处理的三类错误：外部失败（`apply` 中 await 的 IO 抛错）、接纳冲突（差异 c，
[cordiverse/cordis#358](https://github.com/cordiverse/cordis/issues/358)）、disposer 失败（差异 f）。

## 构建

先构建核心（根目录 `sh build.sh`），再：

```sh
sh errors/build.sh
```

## 进度

| 文件 | 内容 | 状态 |
|---|---|---|
| `theories/Superseded.v` | 4.0：过时的加载不记失败；核心的精化，安全性、进展、终止直接搬过来 | 完成 |
| `theories/Admit.v` | 4.2：`O-Insert` 不检查冲突（Cordis 现状），#358 的两次执行 | `fail` 变体与反例完成 |
