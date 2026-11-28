# errors：错误处理进模型

设计见 [DESIGN.md](DESIGN.md)。

目标是一个自足的演算，规则按原则取舍（DESIGN.md 0.2 节），不照搬 Cordis；Cordis 的现状是证据，
不同之处整理成给 Cordis 的建议（DESIGN.md 第 6 节）。

本目录与现有形式化隔离：

- 代码放在 `errors/theories/`，逻辑名 `CordisErr`，可以 import 核心（`Cordis.*`），核心与
  `theories/Ext/` 不 import 它（`grep -rn CordisErr theories/` 应为空）；
- 有自己的 `_CoqProject` 与 `build.sh`，根目录的构建不变；
- 每个模块给出对核心的保守性定理。

要处理的错误：调度决定的失败、外部失败、暂时的接纳冲突
（[cordiverse/cordis#358](https://github.com/cordiverse/cordis/issues/358) 是 Cordis 中的例子）、逆的失败。

## 构建

先构建核心（根目录 `sh build.sh`），再：

```sh
sh errors/build.sh
```

## 进度

| 文件 | 内容 | 状态 |
|---|---|---|
| `theories/Superseded.v` | 4.0：过时的加载不记失败；核心的精化，安全性、进展、终止直接搬过来 | 完成 |
| `theories/Admit.v` | 4.1：Cordis 接纳做法的反例（`O-Insert` 不检查冲突）下 #358 的两次执行 | 完成 |
| `theories/Queue.v` | 5.1：与已退役 fiber 冲突时排队；对应核心执行，终止，quiet 时队列为空，#358 只有一种结局 | 完成 |
| `theories/ViewFail.v` | 失败按视图记录：对应核心执行，安全性，quiet 时失败都在当前视图下，计算的对比例子 | 完成 |
| `theories/VTermination.v` | 新度量下的终止：失败按视图记录之后生命周期步仍不会无限进行 | 完成 |
| `theories/Classify.v` | 合流包含失败：第 1 层（失败集合相同时控制状态合流）完成；第 2 层（失败集合相同）待做 | 进行中 |
| `theories/Async.v` | 确定的外部读取 | 待做 |
| `theories/Resource.v` | 外部资源的释放失败 | 待做 |
