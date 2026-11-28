# errors：错误处理进模型

设计见 [DESIGN.md](DESIGN.md)。目前只有设计，没有 Rocq 代码。

本目录与现有形式化隔离：

- 代码将放在 `errors/theories/`，逻辑名 `CordisErr`，可以 import 核心（`Cordis.*`），核心与
  `theories/Ext/` 不 import 它（`grep -rn CordisErr theories/` 应为空）；
- 有自己的 `_CoqProject` 与 `build.sh`，根目录的构建不变；
- 每个模块给出对核心的保守性定理。

要处理的三类错误：外部失败（`apply` 中 await 的 IO 抛错）、接纳冲突（差异 c，
[cordiverse/cordis#358](https://github.com/cordiverse/cordis/issues/358)）、disposer 失败（差异 f）。
