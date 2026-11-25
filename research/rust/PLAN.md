# 调研计划:Rust 版 Cordis

## 1. 问题

将来可能用 Rust 重写 Cordis。这次调研回答:

> (a) 演算的哪些概念在 Rust 中有现成的语言机制可以承载,哪些会和语言冲突;
> (b) 插件以什么形式加载(原生动态库、WASM 组件、脚本宿主),各自对生命周期保证意味着什么;
> (c) 已有的 Rust 框架里有没有可借鉴或可直接用的部件;
> (d) 怎样让 Rust 实现与 Rocq 演算保持一致:验证、抽取、差分测试。

产出是设计层面的判断和可动手的课题,不是实现。

## 2. 锚点

沿用 [../PLAN.md](../PLAN.md) 的特征 F1–F10。Rust 特有的问题另列:

| 编号 | 问题 | 涉及 |
|---|---|---|
| R1 | 撤销日志 `acc` 与 `Drop`/RAII 的关系;`mem::forget` 是安全的,析构不保证运行 | F1,`Recovery.v` |
| R2 | 共享服务状态 `s` 被提供者与依赖者共同读写,与所有权、借用的冲突 | F5 |
| R3 | 卸载必须串行、可等待(守卫 `¬held`、父等子),Rust 没有 async drop | F2 F6 |
| R4 | async 取消就是 drop future,与 `L-Divert` 的"落地或放弃"、取消安全性 | F7 |
| R5 | 组件声明 `d`/`p`、提供状态检查能否进类型系统(类型状态、const 泛型、宏) | F4;research 第一梯队课题 1 |
| R6 | 插件的加载与卸载:动态库卸载的已知问题、ABI 稳定性、WASM 组件模型 | F10 |
| R7 | fiber 与 pid 的身份:代际索引、弱引用 | `O-Insert`、ω |

## 3. 子方向

| 文件 | 内容 | 主要问题 |
|---|---|---|
| [language.md](language.md) | 语言机制:所有权与共享、Drop 与线性类型的缺失、async 取消与结构化并发、类型状态 | R1–R5 R7 |
| [plugins.md](plugins.md) | 插件形态与生态:动态库与 ABI、WASM 组件模型与能力隔离、热重载、已有框架(Bevy 插件、actor 与监督、tower、依赖注入) | R6,F3 F10 |
| [assurance.md](assurance.md) | 保证手段:Rust 验证工具(Verus、Creusot、Prusti、Aeneas、Kani)、RustBelt、并发测试(loom、shuttle)、Rocq 与 Rust 之间的抽取与差分测试 | 与 [../verification.md](../verification.md) 衔接 |

每个文件沿用 [../PLAN.md](../PLAN.md) 第 3 节的五段结构:概览、对照表、差异、候选课题、参考文献。

## 4. 不做的事

- 不写 Rust 代码,不改仓库中其他文件。
- 不评估 dsh 整体迁移到 Rust;dsh 插件是 TS,Rust 版 Cordis 如何承载 JS 插件只作为插件形态的一种来讨论。
