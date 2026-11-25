# 增量计算与声明式协调

对照特征:F3(target 驱动)、F9(合流)、F10(热重载)。

本文要回答三个问题:

1. 演算的"target 驱动收敛 + 合流",是不是"协调循环最终稳定到期望状态"?
2. Anvil 的 ESR 性质与本仓库的 Progress、Termination、Dynamic 定理怎么对照?
3. 演算现在一旦 target 变就整体卸载、整体重载。增量计算能否给出"只重做受影响部分"的设计,它会破坏哪些已证性质?

简短的回答:

1. 是,而且比一般的协调循环强。演算的 target 只由当前状态决定(level-triggered),生命周期只执行有限步(不需要公平性假设),停下来的状态稳定,并且与调度无关、等于静态组装。Kubernetes 和 Anvil 没有第三点,因为它们的期望状态是用户直接写出来的;演算里没有显式的期望状态,合流正是让"期望状态"有定义的那个定理。
2. ESR 的"最终达到"对应 `termination_reachable` 加 `quiet_settled`(打包为 `orch_live`),"之后一直保持"在演算里平凡成立,"达到的是期望状态"对应 `static_assembly` / `dynamic_agree`。见第 2 节的表和第 3.1 节。
3. 能,但代价落在两处:差异 g 的整体守卫(`unload_waits`)和不变式 `WF` 中"已安装 fiber 的 ω 的定义域恰为 d"。合流在第 2 层服务假设下多半能保住,这是本文最有意思的发现:理想轨迹(`Episode.v`)只依赖所解析 provision 的**初始**状态和本 fiber 自己的操作,所以别的 fiber 在后缀上的重做不影响它。提前截断(early cutoff)在本演算中基本做不到,原因是服务状态共享且可变,依赖者的写入住在提供者的绑定里。见第 3.3、4 节。

## 1. 领域概览

只写与本演算有关的部分。

### 1.1 自调整计算

Acar、Blelloch、Harper 的自适应函数式编程 [AcarBH02] 把程序执行记成一张依赖图(trace):每次读可修改引用(modifiable)都记下读到的值和读之后的计算。输入改变时,变化传播(change propagation)找到读了被改引用的那些点,只重新执行它们之后的部分,其余照旧。后续工作把这一套扩展到命令式程序 [AcarAB08],并给出机器检查的元理论 [AcarBD07]:**变化传播的结果与从头执行一致**(from-scratch consistency),在 Twelf 中证明。

与演算相关的三点:

- trace 是"读 + 读之后的续延",演算的 `acc` 只记逆,不记读到的值(`Out` 由鬼记录 `oplog` 记录,规则不读)。
- 重新执行的粒度是"从某次读开始的后缀",演算的粒度是整个 fiber。
- "增量结果 = 从头结果"是自调整计算的核心正确性定理,它在演算里的对应是 `static_assembly`(任意执行的终态 = 静态组装的终态)。

### 1.2 Adapton

Adapton [HammerPHF14] 把变化传播拆成两步:输入改变时只把依赖图上受影响的节点标脏(dirtying),等外部真的需要某个结果时才按需重算(propagation)。它把计算分成内层的增量计算和外层的观察者,形式化为一个核心演算 λ^cdd_ic。Nominal Adapton [HammerDHLFHV15] 加入一等的**名字**:分配点由程序员命名,两次执行之间按名字匹配重用,并证明了从头一致性。

与演算相关:

- 演算是急切的,没有"按需"。所有能加载的 fiber 都加载,不论是否有人用到它的 provision。
- Nominal Adapton 的名字解决的问题,演算在合流证明里也碰到了:两次执行分配的名字不同,要比较就得有一个与调度无关的命名。`SpawnConf.v` 的规范名 `CName`(根 fiber 用标签,子 fiber 用"父的规范名 + 在父的 spawn 项中的位置")就是这样一个命名(`cn_inj`、`cn_fun`)。区别是 Adapton 用名字来**重用**,演算只用它来**比较**。

### 1.3 增量 λ 演算与变化理论

Cai、Giarrusso、Rendel、Ostermann [CaiGRO14] 给每个类型配一个变化结构(change structure):变化的类型 Δv,更新 v ⊕ dv,差 v ⊖ u。对高阶 λ 演算静态求导,导出程序把输入的变化映射到输出的变化,正确性在 Agda 中证明。后续的缓存传递风格(cache-transfer style)[GiarrussoRS19] 让导出程序能用上原程序的中间结果,并推广到无类型 λ 演算。

与演算相关:演算没有"变化"这一层。target 从 ω 变成 ω' 时,演算不计算差,只撤销整个 `acc` 再从 `body` 重跑。撤销项 `UOp` 的逆 g 可以看成一个"负变化",但它只能把状态退回去,不能把旧结果推到新结果。这一节只提供词汇,不直接给课题。

### 1.4 FRP、glitch 与资源

FRP 始于 Elliott 与 Hudak 的 Fran [ElliottH97]:行为(随时间变化的值)和事件。实现上有两个与本演算相关的问题:

- **glitch**:菱形依赖(c 依赖 a 和 b,b 也依赖 a)中,a 变化后 c 可能先用新 a 和旧 b 算一次,露出一个不一致的中间值。FrTime [CooperK06] 按拓扑序传播来避免它;综述 [BainomugishaCVMD13] 把 glitch 避免列为反应式语言的一个分类维度。并发下的 glitch freedom 有 REScala 一系的工作 [DrechslerMSM18],把一次变化的传播当作事务,保证可串行化。
- **资源**:旧值、旧订阅何时释放。Krishnaswami [Krishnaswami13] 用模态类型静态排除时空泄漏,允许及早回收旧值。

细粒度响应式(SolidJS、TC39 Signals 提案)是工程界当前的主流形态:

- SolidJS 的 `onCleanup` 在所属的响应式作用域(`createEffect`、`createMemo`、`createRoot`)被重新执行或被销毁时运行;`createRoot` 返回的 dispose 拆掉其中注册的全部信号、effect 和 cleanup [SolidDocs]。这是一棵所有权树,effect 重跑 = 先跑完 cleanup 再整体重新执行。
- TC39 Signals 提案(Stage 1)采用"脏标记急切推送、计算惰性拉取"的模型,并以 glitch-free 读为目标 [TC39Signals]。

在本次检索范围内,没有找到对 effect cleanup 语义的形式化(Signals 或 SolidJS)。

### 1.5 React 的 effect 与 cleanup

React 官方文档 [ReactUseEffect] 规定:

- 依赖变化后的每次提交,先用**旧的** props 和 state 运行 cleanup,再用新的运行 setup;卸载时 cleanup 再运行一次。
- 依赖与上次的值按 `Object.is` 比较,也就是按引用身份比较,内容相同的新对象也算变化。
- 开发模式下 Strict Mode 在第一次真正 setup 之前多跑一轮 setup + cleanup,用来检查 cleanup 是否"镜像"了 setup;用户应当分辨不出 setup 跑了一次还是 setup → cleanup → setup。

形式化方面,React-tRace [LeeAY25] 给出 `useState` 与 `useEffect` 的操作语义和一个可视化工具,证明了与文档一致的两条性质,以及 React 的一项优化不改变输出行为。但它明确只考虑最简形式的 `useEffect`:每次渲染后无条件运行,**不含依赖数组**;论文正文中也没有 cleanup。React 16 时代还有基于 λJS 的 React 语义(Madsen 等),早于 hooks,本文未核实其出处。

### 1.6 Kubernetes 控制器与协调循环

Kubernetes 的控制器是一个不终止的控制循环:观察集群状态,把它往资源 `spec` 写明的期望状态推 [K8sController]。官方文档也明说,集群可能永远到不了稳定状态。控制器应当是 level-triggered 的 [Hockin17](经 [SunMGM+24] 的参考文献核实):`reconcile()` 能从任意当前状态出发去匹配任意期望状态,不假定自己看到了完整的变化历史。这一设计源自 Borg、Omega 的经验 [BurnsGOBW16]。

与演算相关的两个机制:

- **级联删除**:前台级联删除时,owner 先得到 `deletionTimestamp` 和 `foregroundDeletion` finalizer,垃圾回收先删 dependents,删完才删 owner [K8sGC]。
- **使用中保护**:用户删除一个正被 Pod 使用的 PVC 时,PVC 不会立即删除,而是由 finalizer `kubernetes.io/pvc-protection` 推迟到没有 Pod 使用它为止 [K8sPV]。
- **替换策略**:Deployment 的 `Recreate` 先杀掉全部旧 Pod 再建新的,`RollingUpdate`(默认)逐步缩旧扩新 [K8sDeploy]。

**Anvil** [SunMGM+24](OSDI 2024 最佳论文)把控制器正确性写成一条 TLA 活性性质,叫最终稳定协调(eventually stable reconciliation, ESR):

```
∀d. □(□desire(d) ⇒ ◇□match(d))        即  model ⊨ ∀d. □desire(d) ↝ □match(d)
```

意思是:只要期望状态描述 d 从某时起不再变化,集群最终会达到匹配 d 的状态,并且此后一直保持。最外层的 □ 说明这对任何历史都成立。证明需要的假设:

- 控制器和环境中其他组件的动作满足弱公平性;
- 故障(如控制器崩溃)可以发生任意多次,但最终不再发生(在模型中加一个带弱公平性的"关闭故障"动作);
- 与其他控制器(如内置 StatefulSet 控制器)的冲突最终停止。

证明分两条引理:(1)环境最终稳定(无故障、无冲突、d 不变);(2)在稳定环境中,从任意状态(`any_state()`,包括崩溃后的残留)出发最终一直匹配 d。两者用 leads-to 的传递性合成。Anvil 建在 Verus(Rust 验证器)上,验证了 ZooKeeper、RabbitMQ、FluentBit 三个控制器。同组之前的 Sieve [SunLGG+22] 与 Acto [GuSZJ+23] 用测试找控制器的协调与稳定性缺陷。

### 1.7 构建系统

Build Systems à la Carte [MokhovMPJ18, MokhovMPJ20] 把构建系统分解为两个正交的选择:调度器(拓扑、重启、挂起)和重建器(脏位、验证 trace、构造 trace、深构造 trace),并给出两条定义:

- **正确性**(定义 3.1):输入键的值不被改动;每个非输入键上存的值,等于在结果存储上重新执行它的任务得到的值。所有讨论的系统都只在任务描述无环时正确。
- **最小性**(定义 2.1):每次构建每个任务至多执行一次,而且只执行传递依赖于已改变输入的任务。

另外两个与本演算相关的概念:

- **静态依赖与动态依赖**:applicative 任务的依赖可以在运行前提取,monadic 任务的依赖只在运行中发现。重启调度器(Excel、Bazel)遇到过期依赖就放弃当前任务,先建依赖再重来,因而不是最小的。
- **提前截断**(early cutoff):一个任务重新执行后结果与上次相同,就不必重建依赖它的任务。Shake [Mitchell12]、Bazel 支持,Make、Excel 不支持。

## 2. 对照表

精确 = 定义层面一一对应;近似 = 对应但有本质条件差异;形似 = 只是类比。

| 领域概念 | 演算中的规则、定义或定理 | 程度 | 说明 |
|---|---|---|---|
| level-triggered:动作只取决于当前状态 | `target n`(`Calculus.v`,只读 `τ` 与 `visible`,即当前 `B` 与 provider 的生命周期) | 精确 | target 是状态的函数,不读历史。可选依赖扩展在"在场集合"变化时重载(`Ext/Optional.v` 的说明),正是为了让终态不依赖 provider 出现的时机 |
| 期望状态 `desire(d)` 不再变化 | 最后一个编排输入之后(`DRun`,`Ext/Orchestrator.v` 的义务 O2:输入有限) | 近似 | ESR 的 d 是用户写下的描述;演算的"期望"由幸存组件序列 `scomps` 隐式决定 |
| `match(d)` | 稳定 `settled`(`Progress.v`)且终态与静态组装在重命名意义下一致(`static_assembly`、`AgreeL`) | 近似 | Anvil 的 match 是对集群状态的谓词;演算没有显式的期望描述,"期望状态"由合流定义 |
| ESR 的"最终"(◇) | `termination_reachable`、`no_infinite_run`(`Termination.v`)+ `quiet_settled`(`Progress.v`);打包为 `summary_live`、`orch_live` | 近似(演算更强) | 演算对**每个**调度都终止,不需要公平性;Anvil 在弱公平性下证明 |
| ESR 的"一直保持"(□) | Rocq 的 `quiet`(`Calculus.v`:没有生命周期规则可用) | 精确(封闭模型中平凡) | 没有编排输入时状态不再改变。Kubernetes 中这一条不平凡,因为环境会扰动 |
| Anvil 引理 2:从任意状态出发 | `termination_reachable`、`progress_reachable`:从初始状态经任意执行(含编排步)到达的状态 | 近似 | 演算的"任意"限于满足不变式的可达状态;Anvil 的 `any_state()` 包括崩溃留下的任意残留 |
| 故障最终停止 | `Fail` 停在 `Inactive (Some ξ)`,`O-Reset` 由外部触发;合流以"没有失败 fiber"为前提 | 近似 | 演算不自动重试,失败是终态的一部分 |
| 控制器之间的冲突最终停止 | `O-Insert` 前提:`p` 两两不相交;共享状态上的冲突由 `HCom`、`HRI` 处理 | 近似 | 演算静态排除"两个 owner 争同一个对象",Kubernetes 只能假设冲突最终停止 |
| 前台级联删除:`deletionTimestamp` + finalizer,先删 dependents | `τ`(`O-Dispose`)、`L-RetireChild`、`parent_waits_child`、`L-Remove` | 近似 | Kubernetes 先删所有 dependents 再删 owner;演算按 LIFO 撤到 `USpawn m` 时才请子 fiber 退出,晚于 spawn 的效应先撤 |
| PVC 使用中保护:被 Pod 使用时推迟删除 | 守卫 `¬held`;`withdraw_waits`、`unload_waits`(`Ordering.v`) | 近似 | 方向相同(被使用者等使用者)。演算更强:整个卸载都等,不只是 provision 本身(差异 g) |
| Deployment `Recreate` | `O-Restart`、`L-Leave` 之后整体撤销再 `L-Begin` | 精确(在策略层面) | 演算只有这一种策略 |
| Deployment `RollingUpdate`(新旧并存) | 无 | — | 同一键只有一个绑定,`p` 两两不相交,新旧 provider 不能并存 |
| 变化传播的从头一致性 [AcarBD07, HammerDHLFHV15] | `static_assembly`、`dynamic_agree`(`Dynamic.v`) | 近似 | 都是"任意过程的结果 = 从头执行的结果"。演算比较的是不同调度,不是增量与从头;粒度为 fiber,状态按 ≃ |
| trace / 动态依赖图 | `acc`(LIFO 撤销日志)| 形似 | trace 记读和续延,用于重新执行;`acc` 只记逆,用于撤销 |
| 变化传播:只重做受影响的后缀 | 无。最接近的是 `L-Divert`、`L-Leave` 后整体撤销重来 | 形似 | 见第 4 节课题 B |
| Nominal Adapton 的名字 | 规范名 `CName`(`SpawnConf.v`,`cn_total`、`cn_fun`、`cn_inj`) | 近似 | 都给分配点一个与调度无关的身份;Adapton 用于重用,演算用于比较 |
| Adapton 的按需(demand-driven) | 无 | — | 演算是急切的 |
| 构建正确性(定义 3.1):每个非输入键等于重算的结果 | `settled`;静止时 Active 集合满足的不动点方程 `active_iff`,其唯一性 `fix_unique`(`Confluence.v`) | 近似 | 都是"每个节点与其依赖一致"的不动点条件,都靠无环得到唯一性 |
| 任务描述无环 | `Above` 没有无限上升链(`Progress.v` 的良基假设);秩 `rank` 与上界 `Rb`(`Termination.v`) | 精确 | — |
| applicative 任务(静态依赖) | 组件静态声明 `d(c)`;`L-Begin` 要求全部依赖可见(`begin_requires_deps`) | 精确 | 依赖在运行前已知,所以调度能按拓扑序 |
| monadic 任务(动态依赖) | `Prog` 的续延 `κ : Out → Prog`:后续操作和 spawn 取决于前面操作的结果 | 近似 | 演算的动态性只在 fiber 内部,不影响 `d` |
| 重启调度器(遇到过期依赖就放弃) | `L-Divert`;target 转向后仍可落地的 `L-Step`(差异 h) | 近似 | 两者都不最小。演算的放弃由 target 变化触发,不是由读到过期值触发 |
| 最小性(定义 2.1) | 无对应定理 | — | 一个 fiber 在一次"构建"中可能被 divert 多次再重来;`termination` 只给出步数上界 |
| 提前截断 | 无;差异 b 故意不做:提供者重新 provide 就换 pid,依赖者必然重载 | — | 见第 3.3 节 |
| glitch freedom(菱形依赖中不见新旧混合) | `WF` 中"已解析的每个依赖都有绑定,pid 与 ω 一致"(`Preservation.v`);`provider_outlives`、`begin_requires_deps`、`step_coherent`(`Ordering.v`) | 近似 | 每个键只有一个绑定,所以所有已安装 fiber 在同一键上解析到同一个 pid,不可能"新 a 配旧 b"。但在途的 `L-Step` 可以在 target 已转向后继续落地,这是有界的、不能收尾的"旧视图上的执行" |
| SolidJS effect 重跑:先跑 cleanup,再整体重执行 | `L-Leave`/`L-Divert` → 逐项 `L-Undo` → `L-Unloaded` → `L-Begin` | 精确(在设计层面) | 粒度都是整个作用域 |
| SolidJS 所有权树,`createRoot` 的 dispose 拆掉整棵 | 父子 fiber,`USpawn`、`L-RetireChild` | 近似 | 演算还规定了父子撤销的相对顺序(LIFO) |
| React:cleanup 用旧 props,setup 用新 props | Unloading 保留旧的 `ω`,`L-Begin` 取新的 target | 近似 | React 一次提交里先跑完所有 cleanup 再跑 setup;演算按 fiber 交错 |
| React 依赖按 `Object.is` 比较 | ω 记录 pid(provision 身份)而不是服务状态(差异 b) | 精确(在设计取向上) | 都按身份比较,内容相同的新对象也算变化 |
| Strict Mode 的 setup → cleanup → setup 不可区分 | `recovery_exact`(`Recovery.v`)、`effect_exact`(`Runtime.v`) | 近似 | React 在开发期用运行测试要求它;演算在 `Revertible` 假设下证明它 |
| 变化结构 Δv、⊕ | `UOp` 的逆 g;`Bridge.v` 的复合逆 | 形似 | 演算没有导数 |

## 3. 差异

### 3.1 收敛 + 合流是不是"协调最终稳定"

是,而且分成三件事,只有前两件是 ESR 有的:

1. **最终到达**。ESR 在弱公平性下证明;演算的生命周期规则构成一个强正规化的关系(`termination`:满足不变式的状态在生命周期步关系下 Acc),任何调度都在有限步内停下,停下的状态稳定(`quiet_settled`)。不需要公平性,是因为演算没有环境:没有故障、没有别的控制器、没有网络。
2. **一直保持**。演算中 `quiet` 的定义就是"没有生命周期规则可用",没有编排输入时状态冻结,这一条平凡。
3. **到达的是哪个状态**。ESR 不需要讨论这个,因为 d 是显式的,match(d) 是对集群的谓词。演算没有显式的 d:用户给的只是插入、dispose、restart 的序列,"该是什么样"要由演算本身回答。`dynamic_agree` 说两次执行只要幸存组件相同,终态就在重命名意义下一致;`static_assembly` 说这个终态等于"只按原顺序插入幸存组件"的执行的终态。所以合流在这里扮演的角色是**定义期望状态**,使 match 有意义。

由此,"target 驱动 + 合流"可以读成:以静态组装为 d 的 ESR,在一个没有环境扰动的封闭模型中,对所有调度成立。

有一处要注意:`static_assembly` 把"静态组装的执行能到达无失败的 quiet 状态"作为前提(RULES.md 第 6 节第 4 层)。ESR 的对应陈述也需要这条前提,或者把失败的 fiber 算进 match。

### 3.2 演算有、这些领域没有的

- **撤销日志与精确恢复**。Kubernetes 控制器靠比较当前与期望来计算动作,不记逆;FRP、自调整计算的 trace 用于重新执行,不用于撤销对共享状态的写。演算的 `acc` 加 `recovery_exact` 给出"撤掉一个 fiber 后,共享状态等于它从没出现过"。React 只在开发期用 Strict Mode 测试这一要求。
- **使用者先走,被使用者后走,且等整个卸载**。PVC 保护只推迟 PVC 本身的删除;演算的 `unload_waits` 让提供者的全部效应都比依赖者活得久(差异 g)。
- **合流作为定理**。Kubernetes 文档明说集群可能永远不稳定;多个控制器之间没有合流保证。

### 3.3 这些领域有、演算没有的

- **最小性与提前截断**。这是增量计算和构建系统的立身之本,演算两样都没有。
  - 最小性:演算的调度是"重启式"的,一个 fiber 可能在一次输入后被 divert 多次。若调度按秩从低到高进行,每个 fiber 至多加载一次,但没有定理陈述这一点。
  - 提前截断:构建系统能截断,是因为任务的输出是**不可变的值**,比较新旧输出就知道依赖者要不要重做。演算的 provision 是**共享可变状态**:依赖者在其上的操作住在提供者的绑定里,提供者一撤销 `UProv`,绑定连同依赖者的写入一起消失。所以即使提供者重新 provide 了 ≃ 原来的初始状态,依赖者的效应也已经丢了,必须重做。差异 b 选择按 pid 比较,与 React 按 `Object.is` 比较是同一个取向,也是同一个原因:内容比较既贵,又在可变状态上不可靠。
- **只重做后缀**。自调整计算从受影响的那次读开始重做;演算从 `body` 开头重做。
- **按需**。Adapton 只算被需要的部分;演算加载所有能加载的 fiber。
- **新旧并存**(`RollingUpdate`)。演算的 `p` 两两不相交、每键一个绑定,新 provider 只能在旧 provider 撤回后出现,对依赖者来说是 `Recreate`。
- **故障模型与公平性**。Anvil 处理崩溃、网络超时和控制器之间的竞争,演算在这些方面不设模型。这是范围差异,不是缺陷:DESIGN 差异 f 已把 disposer 失败划出保证范围。

### 3.4 演算目前怎样"整体重载"

为第 4 节做准备,把现状写清楚:

- 一个提供者 A 被 `O-Restart` 后进入 Unloading,`visible` 不再计入它,所以所有声明了 A 的键的 fiber 的 target 变为 ⊥。
- A 的守卫 `¬held` 阻止 A 撤销任何一项,直到所有依赖者都离开(`unload_waits`)。依赖者 B 若也是提供者,它的依赖者 C 又要先离开 B。于是 A 的整个上闭包都按秩从高到低卸载完,A 才开始撤销。
- A 重新加载、重新 provide 时 pid 是新的,于是整个上闭包再按秩从低到高重新加载。

所以"整体重载"有两层:**纵向**,一个 fiber 撤销整个 `acc`;**横向**,受影响的是提供者的整个上闭包。增量计算对两层各有一个对应:纵向是"只重做后缀",横向是"提前截断"。

## 4. 候选课题

### 课题 A:把 ESR 写成 Rocq 中的一条定理

- **目标**:给出一条与 Anvil 的 ESR 形状一致的陈述,把第 3.1 节的论证变成可引用的定理,为演算在"声明式协调"一类工作中定位。
- **做法**:
  1. 在 `Ext/` 下新建一个文件,不改核心。定义 `Desire ins`:编排输入序列已经消耗完(`DRun` 到达 γ);`Match γ`:`settled γ`,且 γ 与静态组装的终态在 `AgreeL` 意义下一致。
  2. 陈述:对任意 `DRun init [] ins γ rs`,在 `Obligations` 与 `ConfHyps` 下,(i)从 γ 出发的生命周期步关系是良基的;(ii)任意极大的生命周期执行终于某个 γ';(iii)若 γ' 无失败 fiber,则 `Match γ'`;(iv)γ' 之后没有生命周期步(□)。(i)(ii)来自 `orch_live`,(iii)来自 `static_assembly`,(iv)来自 `quiet` 的定义。
  3. 可选:用余归纳的无限执行(输入流加生命周期步)写成 TLA 风格的"输入最终不变 ↝ 一直匹配",说明演算不需要公平性假设。这一步要定义带公平性的无限迹,也可以只写有限版本。
- **预期产出**:一个文件,一条主定理和若干推论;RULES.md 中可以加一句"这是以静态组装为期望状态的 ESR"。
- **风险**:低。主要是陈述上的取舍:`static_assembly` 把静态组装能到达无失败 quiet 状态作为前提,主定理要么带上它,要么把 Match 改成"与静态组装的某个终态一致"。无限迹版本若要做,会比预想的繁琐。
- **工作量**:小(有限版本);中(带无限迹)。

### 课题 B:局部回卷,只重做受影响的后缀

- **目标**:target 变化时,不撤销整个 `acc`,只撤到"第一次碰到变化的键"之前,再从那里继续,对应自调整计算的变化传播。弄清它会破坏哪些已证性质,哪些能保住。
- **设计草案**:
  - 记录每个撤销项对应的程序位置。`acc` 已经是 LIFO,只需在 `UOp` 中已有的 pid 之外,能从程序的后续恢复出"回卷点"。`Prov` 不变式已经说明正在执行的程序是组件程序的后续,撤销项来自程序中的操作,可以借用。
  - 新增一个状态或一条规则 `L-Rewind n K'`:`n` 的 target 只在键集 K' 上与 ω 不同(或 K' 上的 provider 不再可见)时,撤销 `acc` 直到其中不再有 K' 上的 `UOp`,把 `ω` 在 K' 上置为"待定",让守卫 `held` 不再把 `n` 算作 K' 上旧 provision 的解析者。之后 K' 上的新 provision 可见时,恢复 Loading,从回卷点的程序后续继续。
  - 前缀上的操作不读 K',它们的结果不受影响。但前缀中若有 `Spawn` 或 `Provide`,它们保留,子 fiber 和 provision 都不动:这正是横向上省下来的部分,依赖 `n` 的 fiber 不必重载。
- **会破坏的**:
  1. `WF` 中"已安装 fiber 的 ω 的键序列恰为 d"。回卷中的 fiber 的 ω 有待定的键。要改成"定义域为 d,值为 pid 或待定",并相应修改 `resolves`。
  2. `unload_waits` / 差异 g 的整体守卫。若 `n` 本身是提供者,它在自己的 provision 仍被别人解析时撤销了后缀上的效应,依赖者会看到"被拆了一部分的服务",这正是差异 g 当初要排除的情形。只有当后缀上的操作与依赖者的操作满足 `HCom`、`HRI`(都是 `CoPair` 内的操作对)时,依赖者才察觉不到。所以局部回卷要么只对不提供任何键、或 provision 未被解析的 fiber 开放,要么以 `ConfHyps` 为前提。
  3. `begin_requires_deps` 要改写:恢复时只要求 K' 上的依赖可见,其余依赖须仍是原来的 pid,否则回卷得更深。
  4. `termination` 的度量 μ 要重写。回卷的 fiber 不回到 Inactive,"剩余步数"从回卷点算起;`lstep_effects`(一个 fiber 的步骤不影响秩不高于它的 fiber)应仍成立,但要重新检查。
- **能保住的**(推测,需证明):
  - 保持性、顺序中的其他条目、`recovery_exact`:`R_step` 对每一步成立,回卷只是一串 `L-Undo`,`recovery_exact` 的陈述不变;另可加一条"回卷到前缀时,实际存储 ≃ 略去后缀操作的影子存储",由 `R` 和 `omission` 得到。
  - **合流**。这是最有希望的一点。第 2 层的理想轨迹 `Tr` 中,每个操作的结果按所解析 provision 的**初始**状态加本 fiber 此前在该键上的操作(`ownIt`)计算,别的 fiber 的操作都可以后移且不影响结果(`replay_shuffle_ex`、`outcome_after`)。局部回卷后的执行在 `n` 上仍是程序的一条路径:前缀不变,后缀从同一个回卷点在新的 provision 上重跑,而新 provision 的初始状态来自低秩提供者的轨迹。于是 `tr_done_eq`、`final_evs` 的沿秩归纳看起来照样适用,终态与从头重载一致。这正是自调整计算的"从头一致性"在本演算中的形式。
- **预期产出**:一个扩展(仿照 `Ext/Optional.v` 的做法:扩展步要么是核心步,要么是新规则,证明保守性 `xstep_conservative` 的对应物);一张"哪些定理成立、在什么附加假设下成立"的表;合流的证明或反例。
- **风险**:高。(1)回卷点的记录可能需要改 `Prog` 或 `acc` 的表示,触及大量证明;(2)差异 g 的放宽需要说服自己这不是倒退:dsh 的服务中只有满足 `ConfHyps` 的那部分能享受局部回卷;(3)合流的推测可能在 spawn(第 3 层)上失败:前缀中 spawn 的子 fiber 保留,而从头执行中它们是新名字,规范名应能处理,但 `SLInv` 要重新验证。
- **工作量**:大。可以先做一个不 spawn、只回卷不提供键的 fiber 的版本(中),确认合流推测,再扩展。

### 课题 C:提前截断的边界,一个正面结论和一个负面结论

- **目标**:回答"提供者重启后若重新提供了 ≃ 的初始状态,依赖者能否不重载"。第 3.3 节已说明一般情形做不到,本课题把它变成定理。
- **做法**:
  1. **负面**:构造一个例子,依赖者在提供者的 provision 上写入(例如注册表上的注册),提供者重启后绑定重建,依赖者若不重载,终态少了它的写入,与静态组装不一致。这说明 ω 只能按 pid 比较,除非服务另有性质。可以放在 `Examples/` 下。
  2. **正面**:对"只读依赖者"(在该键上只执行逆为恒等的操作,如 `get`)证明:提供者重启并重新提供 ≃ 初始状态时,依赖者保留原状态继续运行,终态仍与静态组装一致。依据是理想轨迹只依赖 provision 的初始状态(`Episode.v`、`tr_done_eq`):只读依赖者的结果在两次执行中相同,它在该绑定上没有待定的写入。
  3. 正面结论需要一条新规则,让只读依赖者的 ω 从旧 pid 改指到新 pid,而不经过卸载;同时提供者在这些依赖者仍解析它时就要卸载,所以 `held` 要把只读依赖者排除在外。
- **预期产出**:一个反例文件;一个小扩展和其合流证明;对 DESIGN.md 差异 b 的一段补充说明(为什么按 pid,以及在什么条件下可以放宽)。
- **风险**:中。正面结论要判定"≃ 初始状态",这在实现中需要服务提供比较函数;而且"只读"必须是静态可查的(程序中该键上只出现读操作),否则无法在运行时决定。即使只得到负面结论,也有文档价值。
- **工作量**:中(负面结论单独做是小)。

### 课题 D:glitch freedom 与调度最小性的显式定理

- **目标**:把第 2 节表中两条"已经蕴含但没写出来"的性质写成定理,便于和 FRP、构建系统对照。
- **做法**:
  1. `view_coherent`:任意可达状态中,两个已安装 fiber 若在同一键上都有解析,则解析到同一个 pid,且该 pid 是当前绑定的 pid。由 `WF` 直接得到。推论:菱形依赖中不会出现"新 a 配旧 b"。
  2. 最小性:定义"按秩调度"(总是先走秩最低的可走 fiber),证明在一次编排输入之后的按秩调度执行中,每个 fiber 至多 `L-Begin` 一次。反过来给一个任意调度下某 fiber 加载两次的例子,说明 `termination` 只给上界。
- **预期产出**:两三个引理和一个例子。
- **风险**:低(第 1 条);中(第 2 条:按秩调度下"至多一次"可能因落地步与 divert 的交互而需要额外条件)。
- **工作量**:小。

### 课题 E(探索):新旧并存的替换

- **目标**:研究 `RollingUpdate` 式的替换:新 provider 先加载并就绪,依赖者再切换,旧 provider 最后撤回。对应 Cordis 的 `registry.replace()`(DESIGN 2.1 节 l 行)想要而模型不提供的东西。
- **做法**:允许同一键在过渡期内有两个绑定(旧的只对已解析者可见,新的对新解析可见);依赖者的 target 指向新的,于是 `L-Leave` 后重新加载到新 provision 上;旧 provider 等依赖者全部离开后撤回。
- **会破坏的**:`p` 两两不相交、每键至多一个绑定(`WF`),合流的"每个键由对应的 fiber 提供"。
- **预期产出**:一份设计说明,判断是否值得做成扩展。
- **风险**:高,收益不确定。依赖者仍要整体重载,只是提供者不再有空窗期,而演算本身没有"空窗期"的代价模型。
- **工作量**:中(只做设计);大(形式化)。

### 排序建议

1. 课题 A:工作量小,直接回答"演算在声明式协调中处于什么位置",与 Anvil 的对照可以写进 README 的总体结论。
2. 课题 B:本方向最实质的课题,回答"最小重载"。先做受限版本,核心是验证"局部回卷保持合流"这一推测。
3. 课题 C:与 B 互补(横向对纵向),负面结论成本低,能解释差异 b 为什么必须按 pid。

## 5. 参考文献

每条都经检索核对了作者、题目、会议或期刊、年份。

- [AcarBH02] Umut A. Acar, Guy E. Blelloch, Robert Harper. Adaptive Functional Programming. POPL 2002, pp. 247–259. 期刊版:ACM TOPLAS 28(6), 2006, pp. 990–1034.
- [AcarAB08] Umut A. Acar, Amal Ahmed, Matthias Blume. Imperative Self-Adjusting Computation. POPL 2008, pp. 309–322.
- [AcarBD07] Umut A. Acar, Matthias Blume, Jacob Donham. A Consistent Semantics of Self-Adjusting Computation. ESOP 2007;期刊版:Journal of Functional Programming 23, 2013, pp. 249–292。
- [HammerPHF14] Matthew A. Hammer, Khoo Yit Phang, Michael Hicks, Jeffrey S. Foster. Adapton: Composable, Demand-Driven Incremental Computation. PLDI 2014, pp. 156–166.
- [HammerDHLFHV15] Matthew A. Hammer, Jana Dunfield, Kyle Headley, Nicholas Labich, Jeffrey S. Foster, Michael Hicks, David Van Horn. Incremental Computation with Names. OOPSLA 2015.
- [CaiGRO14] Yufei Cai, Paolo G. Giarrusso, Tillmann Rendel, Klaus Ostermann. A Theory of Changes for Higher-Order Languages: Incrementalizing λ-Calculi by Static Differentiation. PLDI 2014.
- [GiarrussoRS19] Paolo G. Giarrusso, Yann Régis-Gianas, Philipp Schuster. Incremental λ-Calculus in Cache-Transfer Style: Static Memoization by Program Transformation. ESOP 2019, LNCS 11423, pp. 553–580.
- [ElliottH97] Conal Elliott, Paul Hudak. Functional Reactive Animation. ICFP 1997.(页码各处记载不一,163–173 或 SIGPLAN Notices 32(8) 263–273。)
- [CooperK06] Gregory H. Cooper, Shriram Krishnamurthi. Embedding Dynamic Dataflow in a Call-by-Value Language. ESOP 2006, LNCS 3924, pp. 294–308.
- [BainomugishaCVMD13] Engineer Bainomugisha, Andoni Lombide Carreton, Tom Van Cutsem, Stijn Mostinckx, Wolfgang De Meuter. A Survey on Reactive Programming. ACM Computing Surveys 45(4), Article 52, 2013.
- [Krishnaswami13] Neelakantan R. Krishnaswami. Higher-Order Functional Reactive Programming without Spacetime Leaks. ICFP 2013, pp. 221–232.
- [DrechslerMSM18] Joscha Drechsler, Ragnar Mogk, Guido Salvaneschi, Mira Mezini. Thread-Safe Reactive Programming. Proc. ACM Program. Lang. 2(OOPSLA), Article 107, 2018.
- [LeeAY25] Jay Lee, Joongwon Ahn, Kwangkeun Yi. React-tRace: A Semantics for Understanding React Hooks. Proc. ACM Program. Lang. 9(OOPSLA2), Article 289, 2025. arXiv:2507.05234。核对了正文:只建模无依赖数组的 `useEffect`,不含 cleanup。
- [SunMGM+24] Xudong Sun, Wenjie Ma, Jiawei Tyler Gu, Zicheng Ma, Tej Chajed, Jon Howell, Andrea Lattuada, Oded Padon, Lalith Suresh, Adriana Szekeres, Tianyin Xu. Anvil: Verifying Liveness of Cluster Management Controllers. OSDI 2024. 核对了正文中的 ESR 公式、公平性与故障假设、证明结构。
- [SunLGG+22] X. Sun, W. Luo, J. T. Gu, A. Ganesan, R. Alagappan, M. Gasch, L. Suresh, T. Xu. Automatic Reliability Testing for Cluster Management Controllers. OSDI 2022.(经 [SunMGM+24] 的参考文献核对,作者名按该文献只列缩写。)
- [GuSZJ+23] J. T. Gu, X. Sun, W. Zhang, Y. Jiang, C. Wang, M. Vaziri, O. Legunsen, T. Xu. Acto: Automatic End-to-End Testing for Operation Correctness of Cloud System Management. SOSP 2023.(经 [SunMGM+24] 的参考文献核对,作者名按该文献只列缩写。)
- [BurnsGOBW16] Brendan Burns, Brian Grant, David Oppenheimer, Eric Brewer, John Wilkes. Borg, Omega, and Kubernetes. Communications of the ACM 59(5), 2016, pp. 50–57.(经 [SunMGM+24] 的参考文献核对。)
- [Hockin17] Tim Hockin. Kubernetes: Edge vs. Level Triggered Logic. 演讲幻灯片,2017 年 6 月。(经 [SunMGM+24] 的参考文献核对,未打开原幻灯片。)
- [MokhovMPJ18] Andrey Mokhov, Neil Mitchell, Simon Peyton Jones. Build Systems à la Carte. Proc. ACM Program. Lang. 2(ICFP), Article 79, 2018. 核对了正文中的定义 2.1(最小性)、定义 3.1(正确性)与提前截断。
- [MokhovMPJ20] Andrey Mokhov, Neil Mitchell, Simon Peyton Jones. Build Systems à la Carte: Theory and Practice. Journal of Functional Programming 30, e11, 2020.
- [Mitchell12] Neil Mitchell. Shake Before Building: Replacing Make with Haskell. ICFP 2012, pp. 55–66.
- [ReactUseEffect] React 官方文档,`useEffect` 参考页(react.dev/reference/react/useEffect)。核对了 cleanup 时机、`Object.is` 比较与 Strict Mode 的说明。
- [SolidDocs] SolidJS 官方文档,`onCleanup` 与 `createRoot`(docs.solidjs.com)。
- [TC39Signals] TC39 Signals 提案仓库(github.com/tc39/proposal-signals),Stage 1。关于 glitch-free 与推拉模型的描述来自提案作者的说明文章与仓库议题,未逐条核对规范文本。
- [K8sController] Kubernetes 文档,Controllers(kubernetes.io/docs/concepts/architecture/controller/)。
- [K8sGC] Kubernetes 文档,Garbage Collection(kubernetes.io/docs/concepts/architecture/garbage-collection/)。
- [K8sPV] Kubernetes 文档,Persistent Volumes 中的使用中保护(kubernetes.io/docs/concepts/storage/persistent-volumes/)。
- [K8sDeploy] Kubernetes 文档,Deployments 的 Strategy 一节(kubernetes.io/docs/concepts/workloads/controllers/deployment/)。

未核实:Madsen 等人基于 λJS 的 React 语义(第 1.5 节只提及,未列入正式条目)。
