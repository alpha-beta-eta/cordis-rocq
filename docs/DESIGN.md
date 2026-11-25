# 设计文档

## 1. 目标、范围与原则

- **当前阶段**:在 Rocq 中形式化 dsh(DeepSeek Harness)背后的理论,也就是论文
  *A Programming Paradigm for Spatiotemporal Composability*(arXiv:2608.25512v1;本仓库引用的论文编号都按这一版)第 3–4 章讲的内容:
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
| c | 提供集合 | provide 在运行时执行,重名时抛错(`reflect.ts:291`, `reflect.ts:303`) | 论文 | 组件静态声明 p,运行时实际 provide 的键必须落在 p 内(这是插件义务)。O-Insert 的前提保证不同 fiber 的 p 两两不相交。论文的做法相同:组件声明它的提供集合,fiber 的表只含其中的键(定义 48),O-Insert 的最后一个前提不接纳与已有 fiber 的提供集合相交的组件,单一提供者由此保证(§4.2.1)。依赖关系 ≺ 是否无环因此可以静态判定,而进展和合流都需要无环 | 强制执行已有的 `Plugin.provide` 元数据,在插入 fiber 时就拒绝冲突,而不是等到运行时失败。论文的演算本身就这样要求,运行时抛错是实现与论文的差距 |
| d | 提供方的可用性谓词 `check` | 有(`reflect.ts:130`)。每次通知依赖者时(`fiber.ts:603` 的 `_checkImpl`)对当前的值求一次;dsh 从不传 check | 新(派生) | 不加规则。若在提供时求值,check 就是程序自己能做的判断:`Derived.provide_checked`(检查通过才 provide)。Cordis 在任意通知时刻对可变的值重新求值,依赖者能否加载就取决于通知的时机,这会破坏合流 | 在提供时求值一次,或者删去(dsh 未使用) |
| e | 卸载时 disposer 的执行顺序 | `Promise.all` 并发执行(`fiber.ts:720`) | 论文 | 单个 fiber 内部按 LIFO 顺序**串行**执行。后注册的效应往往依赖先注册的效应(例如先建连接池,再在池上注册监听),LIFO 不需要任何额外假设就能保证正确(Thm 16) | 改为串行 LIFO,或者只对声明为独立的效应并发(判据见 D6:逆以任意顺序施加结果都 ≃) |
| f | 逆(disposer)失败 | 记录日志后吞掉(`fiber.ts:727`) | 新 | 理论中逆是全函数,不会失败。disposer 失败属于越过边界,不在保证范围内 | — |
| g | 守卫 | 每个 provision 维护 `dependents` 集合(`fiber.ts:716`);卸载先等全部 provision 的依赖者退出,再启动任何 disposer | Cordis | 按绑定判断"是否仍被依赖"(`resolves`),但守卫 `held` 作用于整个卸载:只要还有 provision 被别的已安装 fiber 解析,就不撤销任何一项、不请子 fiber 退出。依赖者因此在提供者的全部效应都还在时完成卸载(`unload_waits`)。早先只在 `UProv` 一项上设守卫,提供者会先撤掉 provide 之后的效应,依赖者看到被拆了一部分的服务 | — |
| h | 中途放弃加载(divert) | 异步迭代器只在两次迭代之间检查是否放弃;检查通过后发出的那次 `await iter.next()`,即使等待期间 epoch 变了,返回后它给出的逆也照样收进累加器,然后才停(`fiber.ts:395-398`)。同步迭代器一次跑完(`fiber.ts:384`)。这就是论文 §4.4 所说的 inertial:`L-Divert` 只取"让在途迭代落地"一支 | 论文(两支都保留) | 每次服务操作是一个原子步。target 变化后,`L-Step` 仍可再走(落地),`L-Divert` 随时可以放弃;只有收尾的 `Done` 要求 `target n = ω`(同论文 `L-Finish`,也同 Cordis:reload 结束时 target 已转向就直接进入 UNLOADING)。论文的 inertial 宿主只落地一次迭代,这里允许落地任意多步,所以 Cordis 的两种行为(异步迭代器落地在途的一次,同步迭代器跑完)都是演算的执行,各定理覆盖它们。见 D6"在途操作" | — |
| i | 失败之后 | `update()` 清除错误后可以恢复(`fiber.ts:790`) | Cordis | 增加编排规则 `O-Reset`:把 Inactive(ξ) 变为 Inactive(⊥)。失败后由外部决定是否重试。论文 4.4 节同样不让失败的 fiber 自行重入,重试要经修订(退役、移除、重新插入);这里给成一条规则 | — |
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
| c | 不变:冲突在 provide 时抛错(`reflect.ts:225`);`Plugin.provide` 只用作 `Service` 的默认名字(`service.ts:21`) | 建议不变。上游与论文的 O-Insert(插入时拒绝相交的提供集合)仍不一致。另外,上游也不检查依赖是否无环:一个插件 inject 只有它自己的后代才会提供的服务时,它永远停在 PENDING,不报错(进展定理以 `Hwf` 排除这种情况) |
| m | 不变:`ctx.get` 仍然混入上下文(`reflect.ts:182`),不检查 inject | 建议不变 |
| d | 不变:`_checkImpl` 在通知时求值(`fiber.ts:387`)。check 也可以由 `Service` 子类的 `[Service.check]` 方法给出(`service.ts:35`),上游的 loader 用到了(`loader/src/index.ts:71`) | 结论不变;dsh 两种方式都没有用到 |
| l | 新增 `registry.replace()`(#266):原地把 fiber 换成新插件,保留 fiber 身份,清除错误、revision 加一后重新加载(`fiber.ts:401`) | 模型用 `O-Dispose` 加 `O-Insert` 编码;合流本来就在重命名意义下成立,所以保留身份不影响结论 |
| h | 异步迭代器效应在每步之间检查 epoch,改变时调用 `iter.return()` 关闭(#268,`fiber.ts:275`)。在途的那次 `await iter.next()` 仍会落地:返回后先 `safeCollect` 它的逆,下一轮检查才退出(`fiber.ts:276-278`) | 与 dsh 分支相同,是 inertial 的。落地是演算的 `L-Step`(target 已转向时仍可走),随后的停止是 `L-Divert`,与模型一致(差异 h) |
| g | 卸载先等全部 provision 的依赖者退出,再启动任何 disposer(`fiber.ts:485`,#196);单个 provide 的 disposer 也等待(`reflect.ts:240`) | 模型已改为同样的整体守卫(`held`)。早先模型逐项设守卫,只保证 provision 本身比依赖者活得久,提供者 provide 之后的效应可能先被撤掉;整体守卫保证全部效应都比依赖者活得久 |
| n | 服务查找在隔离边界停止(#209,`locate`) | 与 `Derived.scoped` 的键重命名一致 |
| i | 失败的 fiber 只能经 `update()` 或 `replace()` 恢复(`fiber.ts:436`) | 与 `O-Reset` 一致 |

## 3. 形式化的结构性决定

### D1 状态与效应:结构性限定
- 状态 = 注册表 × 服务绑定。每个绑定带有 provision 编号、owner 和服务状态;
  服务状态被 provider 和依赖者共同操作。
- **所有跨组件共享的可变状态都是某个服务的状态**,不设单独的环境部分。
- 组件放在状态之外的程序表里,fiber 只记组件编号。
- 插件模型 = 服务操作上的程序(论文 Def 30)。程序看不到状态,只能通过操作结果决定下一步,
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
  与部分函数下的读法(定义 36、引理 38 的核心:⋄ 与按结果的组合保持见证),取 ≃ 为相等、函数为
  全函数时退回定义 8。定理 43 的 setoid 版本没有做:演算的恢复与合流不经过它,
  而是直接以操作级的假设证明(`Recovery.v`、`ServiceSeq.v`)。

### D6 并发与原子性(设计,尚未形式化)

精化之前的第一步是差分测试([difftest/](../difftest/README.md)):在真实 Cordis 上记下事件,在抽取出的 `step` 上重放并比较状态;
那里的事件到标签的映射表就是精化关系的草稿。目前只在差异 c 与 e 处对不上。

**现状。** 演算考虑的是交错并发:每个服务操作是一个原子步,不同 fiber 的步任意交错,调度不在演算之内。
恢复精确性("不论其他 fiber 同时做了什么")和合流("不同调度的终态一致")都是关于交错的定理。
单个 fiber 内部串行 LIFO(差异 e)。"操作是原子步"是演算的**前提**,目前由 EDSL 强制:
插件体是生成器,每个 `yield` 是一个原子操作,操作内部不 `await`(差异 h,[EDSL.md](EDSL.md))。
真实 Cordis 不强制这一点,启动函数中可以任意 `await`。

**不考虑并行。** Cordis 运行在 Node.js 上,用户代码单线程,服务状态是普通 JS 对象,不在 worker 之间共享。
JS 的 CAS(`Atomics.compareExchange`)只作用于 `SharedArrayBuffer` 上的整数数组,这里用不到。
若将来服务跨线程共享,"操作是原子步"就是要求服务操作可线性化,下面的逻辑原子性规格原样适用。

**把前提变成服务的义务:逻辑原子性。** 服务操作 `run a t` 本来就是抽象状态上的原子动作。
要求每个操作**相对抽象状态 S/≃ 逻辑原子**(TaDA、HOCAP、Iris 的原子三元组;逻辑原子性蕴涵可线性化):
操作有唯一的线性化点,在那一点按 `run` 作用于 S,线性化点之外对 S 没有可见效果;它给出的逆 g
同样逻辑原子(撤销时施加 g 是演算中的一步)。在 Node 中这归结为三条可检查的条件:

1. 每个操作对 S 的修改集中在**一个同步片段**里。JS 按 run-to-completion 执行,同步片段天然原子。
   片段之前若有 `await`,提交前用版本号做乐观校验;比较和写入在同一个同步片段中,这就是单线程下的 CAS。
   典型的错误是先读状态、`await`、再按旧值写回(丢失更新)。
2. 操作执行期间**不调用会重入同一服务的回调**。单线程下干扰的来源不是别的线程而是同步重入:
   回调在操作中途对同一服务发起操作,线性化点就不唯一了。有序事件总线的分发**返回**回调列表而不调用它们
   (`Services/EventBus.v`),正好避开重入;若 `emit` 在操作内部直接调用监听器,应拆成"取快照"(原子步)
   和"逐个调用"(之后进行),或让回调发起的操作排队。
3. 给出的逆满足同样两条。

不用锁:按键串行的异步互斥锁一旦跨 `await` 持有,可能与生命周期的两处等待(卸载守卫 `held`、`USpawn`)
形成演算看不到的死锁。

**能得到什么:精化。** 若每个操作都逻辑原子,真实执行中一个操作在线性化点之前对演算而言"这一步还没走",
到达线性化点就是一次 `L-Step`,所以每个真实执行对应演算的一个执行。保持性、顺序、恢复精确性、合流这些
安全性结论因此适用于真实的 Cordis 代码,而不只是 EDSL 生成的代码。最终定理的义务分成三方:

| 角色 | 义务 |
|---|---|
| 服务作者 | 相对 G 可撤销、可合流;操作和逆都逻辑原子 |
| 插件作者 | 有界、有秩、相遇受控、完整提供 |
| 运行时作者 | 每条控制规则在一个同步片段内完成(见下) |

逻辑原子性对服务的和封闭(状态不相交),所以和 `Compose.v` 一样,每个服务可以分开证明。

**在途操作。** 允许操作内部 `await` 之后,我们删掉的"在途迭代落地"分支(差异 h,论文 `L-Divert` 的第二种选择)会回来:
操作 a 在 `await` 时 `target` 改变,a 随后到达线性化点并提交。这时有两种处理:

- **落地**:a 照样提交,撤销项进入累加器,fiber 之后再进入 Unloading。论文 §4.4 说异步宿主只能这样做
  (inertial),Cordis 也正是这样做的(2.1 节 h:在途的 `iter.next()` 返回后先收下逆,再检查 epoch)。
  演算覆盖它:`L-Step` 只在收尾(`Done`)时要求 `target n = ω`,其余各步在 target 变化后照样可走,
  这一步就是 a 的线性化点;之后 `L-Divert`。证明上只有终止要改度量:target 已转向的 Loading fiber
  记作"放弃后卸载所需的上界加上剩余步数"(`Termination.mu`、`OptTermination.xmu`);
  其余元理论(保持性、顺序、恢复、进展、合流)的证明都不依赖这条前提。
- **放弃**:在线性化点处检查 epoch,提交与"这个 fiber 是否已被放弃"的检查在同一个同步片段中,
  已放弃就返回 `None` 而不提交。被放弃的操作在演算中根本没走这一步,同样是演算的执行。它还让
  `L-Divert` 可以立即执行,不必等在途 IO 完成。上游 Cordis 不这样做:它在两次迭代**之间**检查 epoch。

两种都在演算之内,运行时取哪一种都不影响各定理;下面 `prepare`/`commit` 形状取的是"放弃"。
在可选依赖扩展中,`X-Step` 仍要求在场集未变(`fresh`):在场集变化之后的落地还不在扩展之内(EXTENSIONS.md)。

**运行时一侧:控制层也要原子。** 规则会读写全局的 B 和 F,这些步骤本身必须原子,否则有 TOCTOU 竞态:
依赖者 `L-Begin` 读到 `visible k = ι`(提供者仍 Active);提供者随即进入 Unloading,守卫 `held`
发现还没有 fiber 解析到 ι,开始撤销并删除绑定;依赖者再写入 ω(k) = ι,违反良构性第 4 条。在 Node 中只要每条规则
在一个同步片段内完成即可。`L-Step` 不必整步原子:累加器归 fiber 独占,解析出的绑定由
`provider_outlives` 保证不会被删,所以只有中间那次服务操作需要原子。

**推论。**

- **异步初始化**(EDSL.md 6.2 的第 4 条,如 dsh-pet 先下载 Electron 再登记):只要登记是唯一的线性化点,
  就合法。恢复精确性和安全性照样成立;合流不再成立,除非外部读取是确定的,因为外部数据决定了操作参数
  和程序分支,"理想轨迹只由程序和初始状态决定"(`Episode.v`)这一步断了。
- **`Promise.all` 的判据**(差异 e):每个撤销原子,所以并发执行一个 fiber 的 disposer 等于按某个排列
  依次施加这些逆。对一个 fiber 的撤销项用 `Promise.all` 是正确的,当且仅当这些逆以任意顺序施加的结果
  都 ≃;撤销独立第 2 条(逆两两可交换)是它的充分条件。
- **由构造保证。** 服务操作可以设计成两段:

  ```ts
  interface Op<S, D, O> {
    prepare(signal: AbortSignal): Promise<D>;                   // 可以 await,不碰 S
    commit(s: S, d: D, tok: Tok): Maybe<[S, (s: S) => S, O]>;  // 同步、纯函数,就是 run
  }
  ```

  运行时 `await prepare`,然后在同一个同步片段中检查 epoch 并执行 `commit`。`commit` 就是 `run`,
  外部数据 D 并进操作参数,线性化点由运行时保证唯一,服务作者不需要懂 Iris。这与"程序是归纳类型,
  限定性由构造保证"(D1)是同一条原则。

**得不到的。**

- 外部 IO 的活性:`prepare` 可能永远不返回;终止定理只说生命周期步不会无限进行。
- 外部数据下的合流(见上)。
- 外部世界的恢复:`prepare` 中起的子进程、写的文件仍只能靠 `resource` 原语保证不泄漏(EDSL.md 6.2 的第 1 条)。
- 真并行下的活性:Iris 的原子三元组只给部分正确性;服务实现内部的锁与生命周期等待组合可能死锁,
  需要公平调度与无锁的服务操作。

## 3.1 与论文的逐条对照

"关系"一列:**忠实** = 按论文的陈述证明;**改写** = 对应物形式不同,见右列;**更强** / **更弱** =
结论或假设比论文强 / 弱;**未做**;**无对应** = 证明路线不同,用不到;**不采用** = 有意不做,理由见右列。

| 论文 | Rocq | 关系 | 说明 |
|---|---|---|---|
| §3.1 定义 1–定理 16 | `Twisted.v`、`EffectFun.v` | 忠实 | 严格相等、全函数 |
| 定义 17–18(效应迭代器) | `Calculus.v` 的 `Prog`;`Bridge.denote` | 改写 | 程序是迭代器的语法形式,每个操作、provide 是一段;解释时读成效应函数 |
| 定义 19–20(余效应上下文,get/set) | `Calculus.v` 的 `binds` 与 `PProvide`;`Bridge.setk` | 改写 | 演算中由绑定承载;`setk` 是定义 20 的 `set` 本身 |
| 定义 21–22(规格,notify) | `Calculus.target`、`visible` | 改写 | 分类函数 notify 本身未形式化,由 target 的变化驱动规则 |
| 定义 23(两种实现) | — | 未做 | |
| 定义 24–25(isolation) | `Derived.scoped` | 改写 | 键重命名,不设 realm 表;与 4.4 节 Isolation 扩展把键读成 (k, realm) 对是同一思路 |
| 定义 26–27(interception) | — | 未做 | 视为传给服务的数据 |
| 定义 28(Γ∞) | — | 不采用 | 演算状态取代:Σ 加 fiber 树,累加器是一阶的撤销项列表。∂-塔不必要,Γ∞ 的定义本身也有问题,见 3.2 节 |
| 定义 29(键上的余效应) | `Service.v` | 改写 | 全系统一个服务 Σ(多个服务用 `Compose.Sum` 组合);操作多一个令牌参数;≃ 作为服务的参数给出 |
| 定义 30(经上下文的迭代器) | `Bridge.denote`、`pbind_witnessed` | 改写 | 按结果选后续(式 (32))读成效应函数上的组合 |
| 定义 31、引理 32(测试,不可区分) | `Observe.v` | 改写 | 论文把 ≃ₖ 定义为不可区分;这里 ≃ 是参数,证明良好服务的 ≃ 包含于不可区分,不可区分是最粗的容许等价;另有 `bus_no_commute` |
| 定义 33(上下文的 ≃) | `Bridge.store_eq` | 部分 | 只取 S = K,不设相对于键集的 ≃_S |
| 定义 34–37、引理 35、38 | `Bridge.PWitnessed`、`pdiamond_witnessed`、`pbind_witnessed` | 部分 | 只取 S = K 的效应函数;⋄ 与按结果的组合保持见证已证 |
| §3.4.1 定义 40–定理 43(效应独立) | `Independence.v` | 忠实 | 对效应函数陈述(论文对迭代器陈述);严格相等;定理 43 的 ≃ 版未做(演算不经过它) |
| 定义 44(键可交换) | `Bridge.PaperIndep` | 改写 | `Maybe` 读法,多"不改对方定义域";只在生成元上要求 |
| 定理 45 | `Bridge.distinct_keys` | 忠实 | |
| 定义 46(带见证的余效应) | — | 无对应 | 论文要求每个键都可交换;这里只要求可能相遇的操作对的性质(见定理 68 一行) |
| 定理 47 | `Bridge.lone_denote`、`paper_confhyps`、`paper_hind` | 改写 | 不经迭代器的独立性(定义 42),直接由定义 44 推出演算的操作级假设;程序的解释与单独激活一致(`lone_denote`) |
| §4.1–4.2(组件、fiber、规则) | `Calculus.v` | 改写 | 重新设计,差异见第 2 节(a、a′、b、e、g、h、i、j、k、l、q) |
| §4.4 Asynchrony | `Calculus.v` 的 `L-Divert`、`L-Step`、`may_step` | 更强 | 论文:异步宿主是 inertial 的,只取 `L-Divert` 的落地一支,且只落地一次迭代。这里落地是 target 变化后的 `L-Step`(收尾的 `Done` 除外),可以落地任意多步,放弃仍随时可用,所以 inertial 的执行和同步迭代器跑完的执行都在演算中。见差异 h 与 D6"在途操作" |
| §4.4 Failure | `PFail`、Inactive(ξ)、`O-Reset` | 改写 | 论文把失败作为扩展,这里在核心中(差异 a、i)。两边都不让失败的 fiber 自行重入,失败也不传给父 fiber。合流两边都排除失败的 fiber:论文说一种调度可能让某个 fiber 失败、另一种让它完成;这里 `dynamic_confluence`、`static_assembly` 以终态没有失败的 fiber 为前提(`Summary.v` 第 4 条)。重试:论文是修订(退役、移除、重新插入),这里是 `O-Reset` |
| §4.4 Isolation | `Derived.scoped` | 改写 | 论文把键读成 (键, realm) 对,规则与 §4.3 的结果照搬;这里是对组件表做键重命名,同一思路。两边都不覆盖在运行中改 realm(论文把它算作修订) |
| §4.4 Configuration | `O-Restart`;`O-Dispose` 加 `O-Insert` | 改写 | 论文中修订是规则的组合,以定理 80 约束终点;这里重启是一条规则(差异 l),换配置是撤掉旧组件、插入新组件,在新名字上进行。合流在重命名意义下成立,用新名字不影响结论 |
| 引理 59–62、66、67、78、79 | — | 无对应 | 恢复用影子存储,合流用不动点唯一性、理想轨迹与规范名;不需要"每次执行两两独立"(引理 66) |
| 定理 64(保持性) | `Preservation.preservation` | 更强 | 不变式 10 条,论文 4 条 |
| 定理 68、推论 69(恢复精确性) | `Recovery.recovery_exact`、`Runtime.effect_exact` | 更强 | 论文经定义 46 要求每个键可交换;这里只要求可能相遇的操作对撤销独立,不要求前向可交换;覆盖运行期效应 |
| 定理 70(顺序) | `Ordering.v` | 忠实 | 第 3 条:表项存在(`provider_outlives`),值只被声明或提供该键的 fiber 的操作或其撤销改变(`value_moves`,论文说"声明该键");另有更强的 `unload_waits` |
| 定理 71(解析一致) | `Ordering.step_coherent` 等 | 改写 | 每一步都按承诺视图执行;只有收尾一步要求 target 与它一致,落地的步不要求(差异 h) |
| 定理 73(进展、终止) | `Progress.progress`、`Termination.termination` | 更弱 | 没有定量界 S(n) ≤ (K+3)(V(n)+1);终止要求秩有界 |
| 引理 75、77(支持集) | `Confluence.fix_unique`、`active_iff` | 部分 | 只在无 spawn 的控制层;有 spawn 时由规范名对应 |
| 定理 80(1)(规范形) | `Dynamic.static_assembly` | 更弱 | 只断言终态与静态组装一致,不构造按 ⊲ 排列 episode 的执行;静态组装能否无失败地到达 quiet 作为前提 |
| 定理 80(2)(合流) | `Dynamic.dynamic_confluence`、`dynamic_agree` | 部分 | 编排可任意穿插;不含 `O-React`,只 dispose 根 fiber;`dynamic_agree` 还允许输入不同 |
| 4.4 节 Failure、Configuration 段 | `O-Reset`、`O-Restart` | 改写 | 论文中重试与重启是规则的组合(退役、卸载、移除、重新插入);这里各是一条规则 |
| — | `O-React`;`Runtime.v` | 新增 | 论文没有的规则及其元理论 |

## 3.2 定义 28 与 ∂-塔

论文 §3.1 在定义 2 之后迭代 ∂Γ ≔ Γ × (Γ → Γ),得到塔 Γ, ∂Γ, ∂²Γ, ⋯;§3.3.1 的定义 28 把它收成
Γ∞ ≔ μΓ. Γ × (Γ → Γ) × Σ,说这样"把 ∂-塔统一成一个自相似的类型",并用这个递归结构表达上下文的层级
(§3.3.1 "Hierarchical composition";§5.1.1 说子效应的 dispose 挂到父累加器上"就是 ∂²Γ 的递归结构";
§5.1.3 说 `fiber.parent` 构成的层级"就是 Γ∞ 的递归结构")。这个塔来自 Koishi 文档中更早的一篇文章
(《可逆的插件系统》,koishi.chat/zh-CN/cookbook/design/disposable),那里写作 C_{n+1} = C_n × (C_n → C_n),称为"高阶资源"。

**塔不必要。**

1. 逆始终作用在底层状态上。卸载要撤销的是对世界的修改(关端口、注销监听、撤掉 provide),都是 Γ → Γ。
   层级只决定这些逆按什么顺序运行,不需要某个逆去作用在另一个累加器上。
2. 论文举的 ∂² 例子是一阶的。父层对子层只是**运行**它的累加器,而不是**编辑**它;父累加器多出的一项
   "调用子层的 dispose"仍是 Γ 上的函数。只有父层的逆去改写子层的累加器时才真正需要 ∂²,而恢复从不需要这样做。
3. 第二层的累加器没有新信息。若 g ∘ f = id,则 track(g, f) 就是 track(f, g) 在 ∂Γ 上的左逆:
   track(g, f)(track(f, g)(γ, φ)) = (g f γ, φ ∘ g ∘ f) = (γ, φ)。第二层的逆可由第一层机械得到;
   recover₁ 已经回到初始状态,第二层只是另把累加器清回 id。
4. Cordis 中唯一编辑累加器的操作,是直接 dispose 子 fiber 时从父 fiber 的 disposer 列表删掉对应项(差异 q)。
   它是记账,没有人撤销它。
5. 本仓库不用塔:状态是 fiber 注册表加服务绑定,每个 fiber 的累加器是撤销项列表,`USpawn` 只是指向子 fiber
   的引用(D2)。恢复精确性和合流都照样成立。

需要的是**累加器组成的树**,不是**函数空间的塔**。

**定义 28 本身的问题。**

- (a) 按 μ 读是空类型。右边每个值都要含一个同类型的更小的值,没有基本情形;X ↦ X × A 的初始代数是 0。
  论文在 §3.3.2 又说递归类型上的各条款"按余归纳读",那是 ν 的读法,与 μ 不一致。
- (b) 在 Set 中只有平凡解。Γ 出现在函数空间的左侧(负位置),函子不是严格正的,初始代数和终余代数都不存在。
  直接解 X ≅ X × Xˣ × Σ:若 |X| ≥ 2,由 Cantor 定理 |Xˣ| > |X|,矛盾;若 |X| = 1,则 |Σ| = 1。
  所以只要 Σ 不平凡,唯一解是空集。非平凡解要走 Scott 的 D∞ 构造(带 ⊥ 的 cpo、连续函数、嵌入-投影对的逆极限),
  而 §3.1 用的是全函数和严格相等,论文没有做这套域论。
- (c) 塔是线性的,层级是树形的。∂ⁿΓ 每层只有一个累加器,Γ∞ 的"当前状态"分量也只容纳一个嵌套的 Γ∞;
  一个父上下文下有几个各自增减效应的子插件,两者都表达不了。定义 28 把嵌套深度(父子关系,应是树)和
  函数空间的阶(在效应上下文上的效应,用不到)混在了一起。

**替代。** 把逆限定在固定的 Σ 上,层级写成严格正的归纳类型:

    Ctx ≔ Σ × T,  T ≔ μT. List((Σ → Σ) + T)

T 是玫瑰树,每项要么是 Σ 上的逆,要么是子上下文;Σ 不参与递归,Σ → Σ 不构成负出现,μ 良定义。
恢复是按 LIFO 遍历这棵树。这基本就是本仓库演算的状态,只是把 `USpawn` 的引用换成了内联的子树。

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
| R7 | §3 与 §4 的衔接(已完成,`Bridge.v`):§3.1 的 setoid 与部分函数读法;`⟦·⟧` 及其与步骤的对应;定理 45;定义 44 推出演算的独立性假设 |
| 以后 | 插件模型的抽取与自动检查;先按 [PLUGIN-AUDIT.md](PLUGIN-AUDIT.md) 扩充模型:可选依赖、交集生命周期的效应、外部持久世界 |

## 5. 待定问题

1. ~~用户编写的 `ctx.effect` disposer 采用什么信任模型?~~ 已定,与论文一致:信任作者,运行时不检查。
   论文 §5.1.1 说,逆是否撤销了它所伴随的效应,是组件作者的义务,运行时不验证;键上发布的操作是否可交换(定义 46 的见证)同样不检查,是提供该键的组件的义务;义务的边界在 §6.1 划定。
   这里的对应:模型中的逆都由服务操作给出,所以这项义务落在服务作者身上(`Summary.Revertible`:操作良好、`G` 相关的操作撤销独立)。用户直接写的 disposer 不在模型内,disposer 失败也越过边界(差异 f)。
2. p 是否确实是 Cordis 的问题,要写测试确认。
3. 建议 c、e、m、p 什么时候、以什么形式反馈给 Cordis?
4. D6 的精化定理(逻辑原子的实现精化演算)是否形式化,以什么形式:在 Iris 中给原子三元组,
   还是只对 `prepare`/`commit` 形状的运行时证明它实现 `step`?Cordis 的 `emit` 是否在操作内部调用监听器,
   需要核对。
