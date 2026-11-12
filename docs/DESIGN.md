# 设计文档

## 1. 目标、范围与原则

- **当前阶段**:在 Rocq 中形式化 dsh(DeepSeek Harness)背后的理论,也就是论文
  *A Programming Paradigm for Spatiotemporal Composability* 第 3–4 章讲的内容:
  可撤销效应、反应式余效应,以及动态组合演算和它的元理论。
- **最终目的**:验证 dsh 插件。因此要求这套理论能对真实插件陈述性质,
  并为将来自动检查插件留出接口。
- **范围**:只关心生命周期性质,包括:
  - 卸载不泄漏(恢复精确性);
  - 依赖顺序(提供者比依赖者活得久);
  - 不死锁且会终止;
  - 最终状态与静态组装的结果一致(合流)。

  插件业务逻辑的正确性不在范围内。

**决策原则**

1. 论文和 Cordis 都不是权威。每个设计点都选**合理、直接、简单**的方案。
2. 如果 Cordis 的做法体现了某种局部最佳实践,就跟着它,不刻意违反。
3. 我们的选择与 Cordis 不同时,在下面第 2 节记为**对 Cordis 的改进建议**。
   形式化本身也是推动 Cordis 改进的依据。

最终要得到的定理形状:

> 若每个服务满足它的规格 S,每个插件满足它的义务 C,则系统满足生命周期性质 G。

## 2. 逐项决定

第 2 列引用的源文件都在 `D:\deepseek-harness\vendor\cordis\src` 下。
"取向"一列的含义:**Cordis** = 跟随 Cordis;**论文** = 跟随论文;**新** = 两者都不跟;
**暂缓** = 第一版不做。

| # | 设计点 | Cordis 现状 | 取向 | 决定与理由 | 对 Cordis 的建议 |
|---|---|---|---|---|---|
| a | 生命周期状态 | 六态 PENDING / LOADING / ACTIVE / FAILED / UNLOADING / DISPOSED(`fiber.ts:147`) | 新 | 用四态 Inactive(ζ) / Loading / Active / Unloading,外加错误标记 ζ。FAILED 就是 Inactive(ξ);DISPOSED 就是条目不存在 | — |
| a′ | 移除 fiber | `dispose` 一个调用完成全部工作(`fiber.ts:271`) | Cordis | 只保留一个外部请求 `O-Dispose`(置退役标记)。条目在"已退役、已 Inactive、没有子 fiber"时由生命周期规则自动删除。这比论文的 Retire 加 Remove 两条规则简单,而且不会因为过早删除而泄漏 | — |
| b | 承诺视图 ω 记录什么 | 记录每次 provide 的身份 `impl.uid`(`fiber.ts:617`) | Cordis | ω : d → ProvisionId。提供者撤掉再重新提供时,依赖它的 fiber 会重新加载,这样依赖者绝不会拿着过期的值继续运行 | — |
| c | 提供集合 | provide 在运行时执行,重名时抛错(`reflect.ts:291`, `reflect.ts:303`) | 新 | 组件静态声明 p,运行时实际 provide 的键必须落在 p 内(这是插件义务)。O-Insert 的前提保证不同 fiber 的 p 两两不相交。依赖关系 ≺ 是否无环因此可以静态判定,而进展和合流都需要无环 | 强制执行已有的 `Plugin.provide` 元数据,在插入 fiber 时就拒绝冲突,而不是等到运行时失败 |
| d | 提供方的可用性谓词 `check` | 有(`reflect.ts:130`)。每次通知依赖者时(`fiber.ts:603` 的 `_checkImpl`)对当前的值求一次;dsh 从不传 check | 新(派生) | 不加规则。若在提供时求值,check 就是程序自己能做的判断:`Derived.provide_checked`(检查通过才 provide)。Cordis 在任意通知时刻对可变的值重新求值,依赖者能否加载就取决于通知的时机,这会破坏合流 | 在提供时求值一次,或者删去(dsh 未使用) |
| e | 卸载时 disposer 的执行顺序 | `Promise.all` 并发执行(`fiber.ts:720`) | 论文 | 单个 fiber 内部按 LIFO 顺序**串行**执行。后注册的效应往往依赖先注册的效应(例如先建连接池,再在池上注册监听),LIFO 不需要任何额外假设就能保证正确(Thm 16) | 改为串行 LIFO,或者只对声明为独立的效应并发 |
| f | 逆(disposer)失败 | 记录日志后吞掉(`fiber.ts:727`) | 新 | 理论中逆是全函数,不会失败。disposer 失败属于越过边界,不在保证范围内 | — |
| g | 守卫 | 每个 provision 维护 `dependents` 集合(`fiber.ts:716`) | Cordis/论文 | 两者本质相同:按绑定判断"是否仍被依赖" | — |
| h | 中途放弃加载(divert) | 异步迭代器在每步之间检查是否放弃;同步迭代器一次跑完(`fiber.ts:396`) | 论文 | 每次服务操作是一个原子步,步与步之间都可以放弃。不保留论文中"让在途迭代落地"的分支,因为 JS 的 `await` 只出现在操作之间 | — |
| i | 失败之后 | `update()` 清除错误后可以恢复(`fiber.ts:790`) | Cordis | 增加编排规则 `O-Reset`:把 Inactive(ξ) 变为 Inactive(⊥)。失败后由外部决定是否重试,比论文"永不重入"更实用 | — |
| j | 父 fiber 与子 fiber 卸载的先后 | 父 fiber 等待子 fiber 卸载完毕(`fiber.ts:299`) | Cordis | 卸载逐项撤销;撤到 spawn 对应的项时,先请求子 fiber 退出,等它被移除后再继续。拆除顺序因此是结构化的,父子之间不需要独立性假设 | — |
| k | 单独撤销某个效应 | `ctx.effect` 构成子效应树,每个子效应可以单独撤销(`fiber.ts:421`) | 新 | 组件声明事件处理器 `reacts`;编排规则 `O-React n i` 在 Active 的 `n` 下以子 fiber 运行第 i 个处理器,并在 `n` 的累加器上记一个 `USpawn`。一次反应就是一个运行期效应,单独撤销就是 `O-Dispose` 这个子 fiber,累加器不必改成树。恢复精确性对它成立(`Runtime.effect_exact`),只要求两个 fiber 可能在同一键上做的操作彼此独立(`CoPair`)。合流仍是启动定理,不含 `O-React` | 运行期效应用子 fiber 或 `ctx.effect` 承载,与模型一致 |
| l | 配置、重启、热更新 | `restart` 增加 revision,使 epoch 改变,fiber 卸载后重新加载(`fiber.ts:768`);`update` 先改配置,再经 `internal/update` waterfall 重启,监听者可以拦下重启(热更新,`fiber.ts:783`) | 新 | 编排规则 `O-Restart n`:未退役的 Loading 或 Active fiber 直接进入 Unloading,之后由已有规则重新加载。不给 target 加 revision。换配置建模为 `O-Dispose` 加 `O-Insert` 新组件,这正是 dsh 的做法(模块版本变化时替换,`client/modules/src/client/entries.ts:233`);dsh 只用同样的配置调用 `fiber.update` 来重试 FAILED 的 fiber,也就是 `O-Reset`。被拦下的热更新不改变生命周期状态 | — |
| m | 读取未声明的服务 | `ctx.get` 可以绕过 inject(`reflect.ts:247`);dsh 非测试代码中有 368 处 | 新 | 局部视图只包含已声明的依赖,限定性由构造保证。读未声明的服务不在保证范围内 | 对读取未注入服务给出警告,或者提供显式的"可选依赖"机制 |
| n | isolate 与 intercept | `isolate(name, label)` 让子上下文中的 `name` 解析到另一个作用域(`context.ts:121`);`intercept` 给下面的插件附加服务配置(`context.ts:141`)。dsh 都没有使用(gateway 的 `rpc.intercept` 是另一个 API) | 新(派生) | 不加规则。键是服务名加作用域标签,isolate 就是对组件表做键重命名(`Derived.scoped`),所有对任意组件表陈述的定理都适用。重命名保持各定理对组件的假设(`scoped_bounded`、`scoped_total`、`scoped_rank`、`scoped_ind`)。只有一点变化:同一组件可以在多个作用域中同时运行,所以独立性要对同一服务名上任意两个组件的操作成立(`CoPairAny`)。intercept 是传给服务的数据,不影响生命周期 | — |
| o | 元层钩子(`internal/*`) | 有:`internal/get`、`internal/plugin`、`internal/update`、`internal/service` 等 | 范围外 | 这些是运行时自身的扩展点,不属于插件模型。其中 `internal/update` 拦下重启已在 l 中处理。dsh 只用 `internal/service` 清除缓存(`api/gateway/src/index.ts:245`) | — |
| p | 注销事件监听器 | 删除第一个回调相同的 hook(`events.ts:275`) | 新 | 按顺序比较时,按回调删除不是精确的逆(`EventBus.on_by_callback_not_witnessed`);忽略顺序时它是精确的逆(`Listeners.listeners_well_behaved`)。所以只有分发顺序会受影响:同一回调注册两次再注销一次后,剩下那一项的位置可能不对 | 上游已按 hook 身份注销(见 2.1);dsh 的分支需要同步 |
| q | 直接 dispose 子 fiber | 允许,且 dsh 大量使用。子 fiber 的 `dispose` 本身是登记在父 fiber 上的一个效应(`fiber.ts:271`),调用它会卸载子 fiber,并把这一项从父 fiber 的 disposer 列表中移除(`fiber.ts:526` 处登记、撤销时移除),父 fiber 不受影响。dsh 中的子 fiber 多数是在事件处理器里动态创建和回收的,例如按 agent 创建的提示片段(`context/file-reference-local/src/index.ts:84`)和作用域(`core/scope/src/index.ts:116`) | 分情况 | 模型里的 `PSpawn` 只对应插件**启动程序**中的 spawn。(1) 启动时 spawn 的子 fiber 若被直接 dispose,父 fiber 在一次执行里保留原生命期,在另一次执行里重新加载并重新 spawn,两次的终态不同,所以合流定理以 `SLInv` 排除这种情况;这在 Cordis 中同样成立,不是模型的人为限制。(2) 事件处理器里动态创建的子 fiber 由 `O-React` 建模(差异 k),可以单独 dispose,恢复精确性成立。模型中 `O-Dispose` 一个子 fiber 会在父 fiber 中留下失效的 spawn 项,撤销时什么都不做;Cordis 则直接移除该项。两者对恢复结果没有影响 | 不建议禁止。建议在文档中约定:启动时 spawn 的子 fiber 不单独 dispose;需要单独回收的子 fiber 在事件处理器或 `ctx.effect` 中动态创建 |
| r | 对服务内部条目的依赖 | dsh 用"监听注册事件加检查当前状态"手工实现,例如子 agent 工具等待名为 X 的提供者(`subagent/tool-subagent/src/index.ts:347`);见 [EMIT-AUDIT.md](EMIT-AUDIT.md) | 新(编码) | 不加规则。把每个条目当作独立的键(例如键 `entry X`):登记条目的插件提供这个键,等待它的插件把它声明为依赖。这样加载顺序由 `L-Begin` 保证(`begin_requires_deps`),卸载顺序由守卫保证(`provider_outlives`),都不需要新的证明。dsh 中手写的"监听加检查"写法本身仍不在模型内:它与激活顺序无关,但模型不跟踪事件回调里对依赖的判断 | 可考虑让插件以声明方式依赖服务内部的条目,由运行时负责加载顺序 |

### 2.1 上游 Cordis 的现状

上表第 2 列引用的是 dsh 中 vendored 的分支(4.0.6-alpha.1)。上游仓库 `D:\cordis`(`packages/core/src`,4.0.0-rc.12,提交 `a6a38a0`,2026-11-06)与它对照如下。

| # | 上游现状 | 对结论的影响 |
|---|---|---|
| p | 已修复:按 hook 身份注销(`events.ts:175`),分发中途被注销的 hook 也会跳过(`removed` 标记,#242) | 建议已落实,上游不再有这个问题;dsh 需要同步上游 |
| e | 仍然并发,但改为按注册的逆序**启动**(`fiber.ts:492`,#296),并在注释中约定:互相依赖的效应放进同一个效应迭代器或服务。单个 `ctx.effect` 内部的 disposer 按 LIFO 串行(`fiber.ts:298`) | 这是有意的设计,不是疏漏。但最自然的写法不满足这个约定:子 fiber 不经 inject 就能读到父 fiber 自己提供的服务(`locate` 沿父链查找 `provisions`,`reflect.ts:89`),它不在 `dependents` 中;父 fiber 卸载时,provide 的 disposer 只让出一个微任务(`reflect.ts:236` 的注释),子 fiber 的异步清理若之后再读这个服务就会失败。按 LIFO 串行(模型的 `USpawn` 逐项等待)没有这个问题。**已由测试确认**(`D:/cordis/packages/core/tests/teardown-order.spec.ts`,上游 `a6a38a0`):子 fiber 直接 spawn,或放在与 provide 分开的组合效应里,清理时都读不到服务;只有把 provide 和 spawn 放进同一个效应迭代器才能读到。上游已有的 27 个销毁测试全部通过,它们只覆盖显式 inject、经祖先 inject、以及同步清理的情况 |
| c | 不变:冲突在 provide 时抛错(`reflect.ts:225`);`Plugin.provide` 只用作 `Service` 的默认名字(`service.ts:21`) | 建议不变。另外,上游也不检查依赖是否无环:一个插件 inject 只有它自己的后代才会提供的服务时,它永远停在 PENDING,不报错(进展定理以 `Hwf` 排除这种情况) |
| m | 不变:`ctx.get` 仍然混入上下文(`reflect.ts:182`),不检查 inject | 建议不变 |
| d | 不变:`_checkImpl` 在通知时求值(`fiber.ts:387`)。check 也可以由 `Service` 子类的 `[Service.check]` 方法给出(`service.ts:35`),上游的 loader 用到了(`loader/src/index.ts:71`) | 结论不变;dsh 两种方式都没有用到 |
| l | 新增 `registry.replace()`(#266):原地把 fiber 换成新插件,保留 fiber 身份,清除错误、revision 加一后重新加载(`fiber.ts:401`) | 模型用 `O-Dispose` 加 `O-Insert` 编码;合流本来就在重命名意义下成立,所以保留身份不影响结论 |
| h | 异步迭代器效应在每步之间检查 epoch,改变时调用 `iter.return()` 关闭(#268,`fiber.ts:275`) | 与模型一致:每个操作原子执行,步与步之间可以放弃 |
| g | 卸载先等全部 provision 的依赖者退出,再启动任何 disposer(`fiber.ts:485`,#196);单个 provide 的 disposer 也等待(`reflect.ts:240`) | 比模型逐项的守卫粗,但同样满足"提供者比依赖者活得久" |
| n | 服务查找在隔离边界停止(#209,`locate`) | 与 `Derived.scoped` 的键重命名一致 |
| i | 失败的 fiber 只能经 `update()` 或 `replace()` 恢复(`fiber.ts:436`) | 与 `O-Reset` 一致 |

## 3. 形式化的结构性决定

### D1 状态与效应:结构性限定
- 状态 = 注册表 × 服务绑定。每个绑定带有 provision 编号、owner 和服务状态;
  服务状态被 provider 和依赖者共同操作。
- **所有跨组件共享的可变状态都是某个服务的状态**,不设单独的环境部分。
- 组件放在状态之外的程序表里,fiber 只记组件编号。
- 插件模型 = 服务操作上的程序(论文 Def 41)。程序看不到状态,只能通过操作结果决定下一步,
  限定性由构造保证。

### D2 程序、注册、累加器
- 程序是归纳类型 `Prog`,构造子有:`Op` / `Provide` / `Spawn` / `Fail` / `Done`。
- 名字和 provision 编号由规则层分配,程序不接触。
- 累加器是撤销项的列表,按 LIFO 逐项撤销。单独撤销的效应用子 fiber 表示(见 k),不需要树。
  通过解释函数 `⟦·⟧`(`Bridge.denote`)与 §3.1 的代数衔接:程序解释为存储上带见证的效应函数,
  每个操作步、provide 步是它的一段,撤销项是这一段的逆(`Bridge.op_stage`、`op_undo` 等)。

完整规则见 [RULES.md](RULES.md)。

### D3 步骤:带标签的确定性单步
`step : State → Label → option State`。

### D4 名字
名字取 `nat`,由全局计数器分配。合流定理在重命名意义下成立。

### D5 等价
- 服务状态从一开始就用 setoid(≃)。
- 控制字段用严格相等。
- §3.1 本身(`Twisted.v`、`EffectFun.v`、`Independence.v`)仍用严格相等。`Bridge.v` 给出 setoid
  与部分函数下的读法(定义 37、引理 38 的核心:⋄ 与按结果的组合保持见证),取 ≃ 为相等、函数为
  全函数时退回定义 8。定理 20、推论 21 的 setoid 版本没有做:演算的恢复与合流不经过它们,
  而是直接以操作级的假设证明(`Recovery.v`、`ServiceSeq.v`)。

## 3.1 与论文的逐条对照

"关系"一列:**忠实** = 按论文的陈述证明;**改写** = 对应物形式不同,见右列;**更强** / **更弱** =
结论或假设比论文强 / 弱;**未做**;**无对应** = 证明路线不同,用不到。

| 论文 | Rocq | 关系 | 说明 |
|---|---|---|---|
| §3.1 定义 1–推论 21 | `Twisted.v`、`EffectFun.v`、`Independence.v` | 忠实 | 严格相等、全函数 |
| 定义 22–23(余效应上下文,get/set) | `Calculus.v` 的 `binds` 与 `PProvide`;`Bridge.setk` | 改写 | 演算中由绑定承载;`setk` 是定义 23 的 `set` 本身 |
| 定义 24(键上的余效应) | `Service.v` | 改写 | 全系统一个服务 Σ(多个服务用 `Compose.Sum` 组合);操作多一个令牌参数 |
| 定义 25–26(规格,notify) | `Calculus.target`、`visible` | 改写 | 分类函数 notify 本身未形式化,由 target 的变化驱动规则 |
| 定义 27(两种实现) | — | 未做 | |
| 定义 28–29(isolation) | `Derived.scoped` | 改写 | 键重命名,不设 realm 表;论文的演算同样不含 realm |
| 定义 30–31(interception) | — | 未做 | 视为传给服务的数据 |
| 定义 32(Γ∞) | — | 未做 | 演算状态取代 |
| 定义 33(上下文的 ≃) | `Bridge.store_eq` | 忠实 | |
| 定义 34、引理 35 | `Observe.v` | 忠实 | 另有 `bus_no_commute` |
| 定义 36–37、引理 38 | `Bridge.PWitnessed`、`pdiamond_witnessed`、`pbind_witnessed` | 部分 | ⋄ 与式 (36) 已证;定理 20、推论 21 的 ≃ 版未做(演算不经过它们) |
| 定义 39(键可交换) | `Bridge.PaperIndep` | 改写 | `Maybe` 读法,多"不改对方定义域";只在生成元上要求 |
| 定理 40 | `Bridge.distinct_keys` | 忠实 | |
| 定义 41、定理 42 | `Bridge.denote`、`lone_denote`、`paper_confhyps`、`paper_hind` | 改写 | 程序的解释与单独激活一致(`lone_denote`);不经效应函数的独立性(定义 19),直接由定义 39 推出演算的操作级假设 |
| §4.1–4.3(组件、fiber、十条规则) | `Calculus.v` | 改写 | 重新设计,差异见第 2 节(a、a′、b、e、h、i、j、k、l、q) |
| 引理 54–57、71、72 | — | 无对应 | 恢复用影子存储,合流用不动点唯一性、理想轨迹与规范名 |
| 定理 59(保持性) | `Preservation.preservation` | 更强 | 不变式 10 条,论文 4 条 |
| 定理 61、推论 62(恢复精确性) | `Recovery.recovery_exact`、`Runtime.effect_exact` | 更强 | 只要求可能相遇的操作对撤销独立,不要求前向可交换;覆盖运行期效应 |
| 定理 63(顺序) | `Ordering.v` | 更弱 | 第 3 条(读到的值不变)有意去掉:服务状态共享可变,固定的是 provision 身份 |
| 定理 64(解析一致) | `Ordering.step_coherent` 等 | 忠实 | |
| 定理 66(进展、终止) | `Progress.progress`、`Termination.termination` | 更弱 | 没有定量界 S(n) ≤ (K+4)(V(n)+1);终止要求秩有界 |
| 引理 68、70(支持集) | `Confluence.fix_unique`、`active_iff` | 部分 | 只在无 spawn 的控制层;有 spawn 时由规范名对应 |
| 定理 73(1)(规范形) | `Dynamic.static_assembly` | 更弱 | 只断言终态与静态组装一致,不构造按 ⊲ 排列 episode 的执行;静态组装能否无失败地到达 quiet 作为前提 |
| 定理 73(2)(合流) | `Dynamic.dynamic_confluence`、`dynamic_agree` | 部分 | 编排可任意穿插;不含 `O-React`,只 dispose 根 fiber;`dynamic_agree` 还允许输入不同 |
| — | `O-Reset`、`O-Restart`、`O-React`;`Runtime.v` | 新增 | 论文没有的规则及其元理论 |

## 4. 路线

| 阶段 | 内容 |
|---|---|
| R0 | 本文档;规则草案见 [RULES.md](RULES.md) |
| R1 | 服务规格层(已完成:`Service.v`、`Services/Registry.v`、`Services/EventBus.v`) |
| R2 | 演算(已完成:`Calculus.v`;例子 `Examples/Basic.v`) |
| R3 | 元理论:保持性(已完成:`Preservation.v`)→ 顺序与解析一致(已完成:`Ordering.v`)→ 恢复精确性(已完成:`Recovery.v`)→ 进展(已完成:`Progress.v`、`Termination.v`)→ 合流(已完成:控制层面 `Confluence.v`,服务状态 `ServiceSeq.v`、`StateInv.v`、`Episode.v`、`StateConf.v`,含 spawn 的系统 `SpawnConf.v`,编排与生命周期交错、与静态组装一致 `Dynamic.v`)|
| R3′ | 服务覆盖(已完成):忽略顺序的监听器 `Services/Listeners.v`,注册表的合流假设 `Services/RegistryConf.v`,和服务组合子与通用合流定理 `Compose.v`,例子 `Examples/Composed.v` |
| R4 | §3.2–3.3 的必要部分(已完成):独立性假设按键、按 fiber 放宽(`CoPair`,`Recovery.v`、`ServiceSeq.v` 及合流各部分);观察等价 `Observe.v` |
| R5 | 运行期效应 k(已完成):`Calculus.v` 的 `O-React`,各元理论文件的对应情形,`Runtime.v` |
| R6 | 其余暂缓项(已完成):重启 `O-Restart`(`Calculus.v` 及各元理论文件);派生形式 `Derived.v`(isolate、check);r 用"条目即键"编码;o 定为范围外 |
| R7 | §3 与 §4 的衔接(已完成,`Bridge.v`):§3.1 的 setoid 与部分函数读法;`⟦·⟧` 及其与步骤的对应;定理 40;定义 39 推出演算的独立性假设 |
| 以后 | 插件模型的抽取与自动检查;先按 [PLUGIN-AUDIT.md](PLUGIN-AUDIT.md) 扩充模型:可选依赖、交集生命周期的效应、外部持久世界 |

## 5. 待定问题

1. 用户编写的 `ctx.effect` disposer 采用什么信任模型?
2. p 是否确实是 Cordis 的问题,要写测试确认。
3. 建议 c、e、m、p 什么时候、以什么形式反馈给 Cordis?
