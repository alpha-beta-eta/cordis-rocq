# Cordis 的渐进原型

把 Cordis 的生命周期演算拆成七层，用 Racket 一层一层写出来。每层只引入一个新概念，并且有三样东西：

- **反例**：没有这个概念时会出什么错；
- **性质**：加上它之后，测试里能跑通的检查；
- **问题**：留给下一层的问题。

每层是一个**完整的、自足的文件**，不 `require` 前一层。相邻两层的差别在 [diffs/](diffs/) 里，读 diff 就能看到这一层改了什么。

| 层 | 新概念 | 性质（`module+ test` 里的检查） | 反例 | 对应的 Rocq |
|---|---|---|---|---|
| [L0](L0.rkt) 可撤销的服务 | 服务 Σ：`run a t s` 交出新状态、逆 g、结果；令牌 t | 见证：`g s' ≃ s` | `OnByCallback`：按回调删的逆删错了项 | `Service.v`, `Services/Registry.v`, `Services/EventBus.v`, `Compose.v` (Sum) |
| [L1](L1.rkt) 组件的生命周期 | 程序 `Done/Fail/Call`；fiber、`Inactive/Loading/Active/Unloading`；累加器 acc 按 LIFO 撤销。存储在初始状态给定 | 保持性；恢复精确性（影子存储）；进展（quiet ⇒ settled）；附录A：程序的解释与单独加载一致 | 加载到一半失败（`bad`）；两个 `old-ping` 移除第二个，删掉的却是第一个的钩子 | `Calculus.v` 的一部分, `Recovery.v`, `Progress.v`, `Bridge.v` (⟦·⟧) |
| [L2](L2.rkt) 依赖与提供 | 组件 ⟨d, p⟩；`Provide`、绑定 ⟨ι, q, s⟩、视图 ω；`L-Divert/L-Leave` 比较视图；守卫 held；`EUnresolved/EConflict` | 不变式第3–8条；依赖者在提供者之后加载、之前卸载（在手写的执行上检查）；守卫作用于整个卸载；恢复精确性、进展 | 两个组件提供同一个键（插入时拒绝）；一个程序重复提供（EConflict）；在还没提供的键上操作（EUnresolved）；没有提供者 | `Calculus.v`, `Preservation.v`, `Ordering.v`, `Recovery.v`, `Progress.v`, `Termination.v` |
| [L3](L3.rkt) 调度无关（合流） | **规则不变**。问题变了：插入次序和调度都任意，静止状态在观察下唯一吗？新增服务 `Listeners`（满足合流假设）、`Vars`（不满足） | 合流：200 个随机种子，插入次序与调度都打乱，观察相同；附录B：观察等价 | 有序事件总线：分发看得到次序；变量存储：最后写的赢 | `Confluence.v`, `StateConf.v`, `Compose.v`, `Observe.v`, `Services/Listeners.v` |
| [L4](L4.rkt) 子 fiber | `Spawn`、父 fiber π、`USpawn`；`L-RetireChild`；有子 fiber 的不能移除 | 不变式第2条，第1条也覆盖 `USpawn`；父 fiber 等子 fiber；合流（子 fiber 也在观察之内） | 父 fiber 撤到 `USpawn` 时子 fiber 还在 | `SpawnConf.v` |
| [L5](L5.rkt) 运行时反应 | 组件的 `reacts`；`O-React`：一次反应就是一个子 fiber，**不需要新的生命周期规则** | 运行时效应的精确性：单独移除一次反应只撤掉它自己的效应；父 fiber 卸载时剩下的反应先退出 | — | `Runtime.v` |
| [L6](L6.rkt) 编排者 | **规则不变**。编排标签与生命周期步穿插（`interleave`），不必等静止 | 动态合流：穿插着插入、重启、移除，最后与幸存者的静态组装一致；穿插执行下的保持性、恢复精确性、进展 | 加载到一半提供者重启：在途的一步走完、改道、撤销、重来 | `Dynamic.v`, `Ext/Orchestrator.v` |

L3 和 L6 都不加规则，只换问题。这是有意的：合流不是规则白给的，要靠服务满足的假设（L3），以及编排者只是一个输入源（L6）。

可选依赖、交集生命期这两项扩展不在主线上，见 `theories/Ext/` 和 [programs/cordis3.rkt](../programs/cordis3.rkt)。命令式运行时见 [programs/cordis.rkt](../programs/cordis.rkt)。

## 运行

```sh
racket L2.rkt        # 演示: 一幕一幕施加编排标签, 打印生命周期步和状态
raco test L2.rkt     # 本层的全部检查
sh build.sh          # 测试全部各层, 重新生成 diffs/
```

## 与 programs/ 的关系

L6 的演算（第2–5节：程序、状态、派生概念、规则）与 [programs/cordis1.rkt](../programs/cordis1.rkt) 逐行相同，只有三行注释略有出入；不变式的条目编号也一致。检查部分的不同：

- 合流的观察不用规范名（没有 `canonical`），而是用组件名：fiber 记为（组件、父 fiber 的组件、是否 Active），绑定记为（键、提供者的组件、状态）。所以插入次序也可以打乱。代价是观察更粗：同一个组件的两个 fiber 中哪个 Active、哪个提供了某个键，看不出来；本仓库的测试用不到这种区分。
- 多了调度用的 `run-script`（每施加一项编排就等静止）、`shuffle-by` 与 `assemble`（打乱插入次序的静态组装）。`interleave` 到 L6 才出现。

## 维护

每层都是前一层的副本加修改。改某一层时，要把同样的改动带到它之后的每一层，再运行 `sh build.sh` 重新生成 diff。diff 里只应该出现这一层引入的概念。
