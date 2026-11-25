# 结构化并发、取消与监督

对照特征:F6(父子 fiber,父卸载时先请子退出再等待)、F7(加载中途可放弃、可落地,失败带错误停住,外部重置)。
顺带涉及 F1(LIFO 撤销)、F2(守卫 `held`)、F10(重启)。

本文的三个重点问题和简短回答:

1. **`L-RetireChild` 加 `parent_waits_child` 是不是结构化并发的"子任务不逃逸"不变量?** 是,而且演算里已有它的状态形式:
   `Preservation.WF` 的 `wf_parent`(子 fiber 存在 ⇒ 父 fiber 已安装且累加器里有对应的 `USpawn`)。
   `parent_waits_child` 是"作用域退出时等子任务"的操作形式。差别在三处:Cordis 的作用域退出总是取消子 fiber
   (子 fiber 不会自己"做完");子 fiber 失败不传给父 fiber(相当于 Kotlin 的 `SupervisorJob`);
   生命期嵌套不只沿父子树,还沿依赖边(`held`、`provider_outlives`),是一个 DAG。
2. **`L-Divert` 的"在途迭代落地"与取消点、`mask` 怎么对照?** 每个 `L-Step` 是原子步,`L-Divert` 只能发生在两步之间,
   这就是"取消只在检查点生效"的协作式取消(Trio、Kotlin、Swift)。落地几步由调度决定,不由程序决定,
   所以它不是 `mask`:演算里没有程序可控的屏蔽区间,有的是两条硬性的"不可中断":单个操作连同登记逆是原子的
   (正是 `bracket` 要靠 `mask` 才能得到的那一点),以及卸载一旦开始不可打断(相当于清理代码总在屏蔽或 shield 下运行)。
3. **`O-Reset` 与 OTP 监督树、能否作为编排扩展加入演算?** `O-Reset` 就是 one_for_one 下对单个子进程的一次重启,
   而依赖者的重启是演算自动完成的(按依赖关系的 rest_for_one)。监督者可以做成 `Ext/Orchestrator.v` 意义下的输入源:
   安全、恢复两层直接继承;重启次数上限给出编排义务 O2(有限输入);`IReset`、`IRestart` 不改变存活组件序列 `scomps`,
   所以监督重启不影响合流结论。见课题 C2。

## 1. 领域概览

### 1.1 结构化并发

核心主张:并发任务的生命期服从词法作用域,子任务不比创建它的作用域活得久。

- **Trio(Python)。** N. J. Smith 2018 年的文章提出 nursery:`async with` 块退出前等待块内启动的所有任务结束;
  任一子任务抛出未处理异常时,nursery 立即取消其余任务,异常在父任务中重新抛出(Trio 文档)。
  取消以 cancel scope 为单位,只在检查点(checkpoint,每个 Trio 异步调用的 `await`)生效。
  Trio 文档对可取消操作给出的保证是:抛出 `Cancelled` 就意味着操作没有发生,没有部分效果。
  `shield = True` 的 scope 屏蔽外层取消,用于清理代码。
- **Kotlin 协程。** Elizarov(Onward! 2021)概述了设计。`Job` 的状态有 New、Active、Completing、Cancelling、Cancelled、
  Completed:协程体结束后进入 Completing,等所有子 job 结束才 Completed;取消父 job 递归取消子 job;
  Cancelling 的 job 也要等子 job 全部结束才变为 Cancelled(kotlinx.coroutines 的 `Job` 文档)。
  普通 `Job` 下子 job 的非取消异常会取消父 job 及兄弟;`SupervisorJob`/`supervisorScope` 下子 job 的失败不向上、不向兄弟传播,
  但父 scope 仍等所有子 job 结束(异常处理文档)。
- **Swift。** SE-0304(McCall、Groff、Gregor、Malawski,Swift 5.5 实现)规定子任务不持续到创建它的作用域之外;
  作用域先退出时隐式等待子任务,若因抛错退出则先取消再等待。取消完全是协作式的:只设一个标志并运行已登记的取消处理器,
  不检查就没有效果。
- **Java。** JEP 428(JDK 19 孵化)、437(JDK 20)、453(JDK 21 预览)、462、480,之后 505(JDK 25)改为静态工厂方法。
  `StructuredTaskScope` 把子任务限定在一个作用域内,作用域所有者被中断或作用域关闭时取消子任务。
- **OCaml Eio。** switch 把一组 fiber 绑在一起等待,每个 switch 带一个取消上下文;取消上下文在每个 domain 内成树,
  上下文被取消时其中的 fiber 运行取消函数;清理推荐用 `Switch.on_release`(Eio 文档与 README)。
- **更早的同类构造。** X10 的 `async`/`finish`:`finish` 等待其中(包括传递地)启动的所有 `async`。
  Lee 与 Palsberg 的 FX10(PPoPP 2010)给出核心演算,用于 may-happen-in-parallel 分析。
  Racket 的 custodian(Flatt 等 ICFP 1999)按层次管理线程和端口,关闭 custodian 即关闭它管理的一切;
  Flatt 与 Findler(PLDI 2004)进一步提出"共同监护"(joint custody):一个线程可以同时属于多个 custodian,
  共享的同步抽象在任一使用者仍需要时继续运行。
- **形式化现状。** 检索没有找到专门给 nursery/cancel scope 或 Kotlin/Swift 结构化并发做操作语义并证明"不逃逸"的论文。
  Chen 与 You 的综述(ICPP Workshops 2022)是非形式的。Gangamreddypalli、Enea、Qadeer 的 RedPL(ESOP 2026)
  对树状线程状态的结构化并发程序做归约推理,不涉及取消。最接近的形式工作是 FX10 和 Leijen 用代数效应实现的
  结构化异步(TyDe 2017,摘要提到块作用域的交错、取消与超时)。这一点本身是一个结论:Cordis 的 `wf_parent`、
  `parent_waits_child`、`unload_waits` 已经是一个机械化的结构化生命期性质,而领域里少有对应物。

### 1.2 异步取消的语义

- **Haskell 异步异常。** Marlow、Peyton Jones、Moran、Reppy(PLDI 2001)给 Concurrent Haskell 加入线程间异步投递的异常,
  给出操作语义,引入作用域化的屏蔽/解除屏蔽组合子,以及可挂起操作的特殊语义(屏蔽状态下阻塞的操作仍可被打断),
  并由此写出可组合的 `timeout`。今天 `base` 中的接口是 `mask`:屏蔽期间 `throwTo` 本线程的一方被阻塞;
  `MaskedInterruptible` 下阻塞操作仍可被打断;`uninterruptibleMask` 不可打断,文档警告慎用。
  `bracket` 抽象的正是"屏蔽下获取,登记释放"的模式:获取资源与登记释放之间不能插进异步异常,否则资源泄漏。
- **代数效应中的异步。** Ahman 与 Pretnar(POPL 2021)的 λæ 把操作调用拆成信号与中断,计算通过预先安装的中断处理器
  对中断作出反应,有小步语义和类型与效应系统,类型安全在 Agda 中证明。它是"取消作为中断"的一种演算化。
- **协作式取消的共识。** Trio、Kotlin、Swift、Eio 都是协作式:取消请求是一个标志或一个在检查点抛出的异常,
  任务在检查点响应;清理代码需要显式屏蔽(Trio 的 shield)。

### 1.3 Erlang/OTP:link、monitor、监督树

- Armstrong 的博士论文(2003)阐述"let it crash"与监督层次。
- **监督策略**(OTP 设计原则文档):`one_for_one` 只重启终止的子进程;`one_for_all` 终止其余所有子进程后全部重启;
  `rest_for_one` 终止并重启在失败者**之后**启动的子进程;`simple_one_for_one` 是动态添加同类子进程的 one_for_one。
  子进程类型 `permanent`(总是重启)、`transient`(异常退出才重启)、`temporary`(从不重启)。
  `intensity`/`period` 限制单位时间内的重启次数,超出则监督者终止所有子进程和自身,由上一层处理(升级)。
  子进程**按列表顺序启动、按逆序终止**。关闭方式有 `brutal_kill` 和带超时的请求退出。
- **link 与 monitor。** link 双向,一方终止时向另一方发出退出信号;monitor 单向,只通知。
- **形式化。** Svensson、Fredlund、Benac Earle(Erlang Workshop 2010)给出分布式 Erlang 的统一语义;
  Castro 等(ENTCS 2011)用 McErlang 模型检测一个替代 OTP supervisor 的实现,检查了若干安全与活性性质;
  Cassar 等(PrePost 2017)指出 Erlang 的恢复策略只有非形式描述,用编排(choreography)给出语义;
  Neykova 与 Yoshida(CC 2017)从多方协议抽取进程间的因果依赖,静态计算故障后需要恢复的最小范围,
  在部分协议可安全恢复时优于 Erlang 内建的静态策略。Lanese、Nishida、Palacios、Vidal(JLAMP 2018)给 Erlang 子集
  可逆语义(与 reversibility.md 交叉)。检索没有找到对 OTP 监督树(含重启强度)的完整机械化语义。

### 1.4 actor 的生命期与终止检测

- Agha(1986)给出 actor 模型的语法与指称模型。actor 本身没有父子生命期约束,结构来自监督层次(Erlang、Akka)。
- Dijkstra 与 Scholten(IPL 1980)的扩散计算终止检测:每条边维护"已发消息减已返回信号"的亏欠,
  子树全部归还后发起者得知终止。
- Clebsch 与 Drossopoulou(OOPSLA 2013)的 Pony actor 并发回收(MAC),按消息检测 actor 之间的引用环。

### 1.5 资源安全的作用域

- Tofte 与 Talpin(Inf. Comput. 1997)的区域:`letregion` 嵌套,释放按 LIFO,由类型与效应系统保证安全。
- Fluet、Morrisett、Ahmed(ESOP 2006)用线性能力编码区域,允许非 LIFO 的区域(Cyclone 的动态区域)。
- Kiselyov 与 Shan(Haskell 2008)把嵌套区域用于文件句柄,静态保证句柄不逃出区域。
- RAII 与 Python 的 `contextlib.ExitStack` 都是"按逆序执行登记的清理",与 `acc` 的 LIFO 同构。

## 2. 对照表

"程度"一列:**精确** = 同一性质,可直接互译;**近似** = 主体一致,有明确差别;**形似** = 只有外形相同。

| 领域概念 | 演算中的对应 | 程度 | 说明 |
|---|---|---|---|
| 子任务不逃出作用域(Swift:不持续到作用域之外) | `Preservation.WF` 的 `wf_parent`;RULES §6.1 的推论"卸载完毕时子 fiber 已不存在" | 精确 | 作用域 = 父 fiber 已安装且 `acc` 含 `USpawn m` 的区间。每个可达状态成立(`wf_reachable`) |
| nursery 块退出前等待子任务 | `L-Undo` 的 `USpawn m` 情形要求 `m ∉ dom F`;`Ordering.parent_waits_child` | 精确 | Cordis 中"块"不是整个父 fiber,而是 `acc` 中 `USpawn m` 以上的后缀:晚于 spawn 注册的效应先撤销,再请子 fiber 退出,这与嵌套的 `with` 块退出顺序相同 |
| 作用域退出时取消子任务(cancel scope、Kotlin 取消父 job) | `L-RetireChild`:置 `τₘ := true` | 近似 | Cordis 退出作用域时**总是**取消;nursery 正常退出时是等待子任务自然结束。Cordis 的子 fiber 是长期运行的服务,没有"做完"的概念 |
| 取消是一个标志,任务在检查点响应 | `τₘ` 使 `target m = ⊥`;子 fiber 随后 `L-Divert`(Loading)或 `L-Leave`(Active) | 精确 | Swift 文档的说法(设标志、不检查就无效)与 `L-RetireChild` 只改 `τ` 一致;响应发生在子 fiber 自己的下一步 |
| Kotlin Completing(体已结束,等子 job) | `Active acc ω` | 近似 | Cordis 的 Active 不会自行转为完成,只能因 target 变化离开 |
| Kotlin Cancelling → Cancelled(取消后仍等子 job) | `Unloading` → `L-Unloaded` → `Inactive` | 精确 | 两边都在取消状态下等子任务全部结束才进入终态 |
| 子任务失败取消父与兄弟(Trio、Kotlin 普通 `Job`) | 无 | — | Cordis 中子 fiber `Fail` 后停在 `Inactive (Some ξ)`,父 fiber 不受影响(DESIGN 3.1 节 Failure 行) |
| `SupervisorJob`/`supervisorScope`(失败不传播,父仍等子) | 子 fiber 失败不影响父;父卸载仍经 `parent_waits_child` | 精确 | Cordis 的默认语义就是 supervisor 语义 |
| X10 `finish` 等待传递启动的所有 `async` | `parent_waits_child` 逐层成立,子 fiber 的卸载又等它自己的子 fiber | 近似 | 传递性由递归得到;Cordis 没有不属于任何 fiber 的游离任务 |
| 检查点之间的原子性(Trio:每个 `await` 是检查点) | `L-Step` 原子;`L-Divert` 只在两步之间 | 精确 | 演算的"操作是原子步"由 EDSL 的 `yield` 强制(DESIGN D6),每个 `yield` 就是检查点 |
| Trio:抛出 `Cancelled` 即操作没有发生 | DESIGN D6"放弃":在线性化点检查 epoch,与提交在同一同步片段 | 精确(设计层) | 演算里只有"走了 `L-Step`"或"走了 `L-Divert`"两种结果,没有半步;D6 尚未形式化 |
| 在途操作不可打断,完成后再响应取消(inertial) | target 变化后 `L-Step` 仍可走(落地),`Done` 要求 `target n = ω`;`Ordering.divert_when_changed` | 近似 | 落地多少步由调度决定。Haskell 中由程序用 `mask` 决定,演算里程序无法声明屏蔽区间 |
| `mask` 区间内延迟异步异常 | 落地的若干 `L-Step` | 形似 | `mask` 可无限期延迟;演算中落地有界(`Bounded Kb`,`Termination.mu` 中 `2·Kb + 1 + …` 一项) |
| `bracket`:获取与登记释放之间不插入异步异常 | `L-Step` 一步内写回 `s'` 并压入 `UOp pid g` | 精确 | 演算把"操作与它的逆同时登记"做成规则的原子性;`Recovery.recovery_exact` 依赖它 |
| 清理不可被取消(`bracket` 释放在屏蔽下、Trio shield、Eio `on_release`) | `Unloading` 没有出口规则回到 Loading/Active;`O-Restart` 只作用于 Loading/Active | 精确 | 而且逆是全函数(DESIGN 差异 f),不会像 Haskell 的释放那样再抛异常 |
| `uninterruptibleMask` 可能导致不可杀的线程 | 卸载中的等待(`held`、`USpawn`) | 近似 | 演算中等待必然结束:`Progress.progress`、`Termination.termination`;Haskell 无此保证 |
| λæ 的中断与中断处理器 | target 变化(由 `O-Dispose`、`O-Restart`、提供者离开引起) | 形似 | λæ 的计算可以对中断编程;Cordis 插件看不到 target 变化,反应由运行时规则固定 |
| OTP `one_for_one` + `temporary` | `Fail` 停在 `Inactive (Some ξ)`,不自动重试 | 精确 | |
| OTP `one_for_one` + `permanent`/`transient` | 外部发 `O-Reset n`(或 `O-Restart n`) | 近似 | 重启由编排者决定,演算本身不重试;对应 DESIGN 差异 i |
| OTP `rest_for_one`(重启之后启动的子进程) | 提供者离开 Active 后依赖者 target 变化而卸载;提供者以新 pid 重新提供后依赖者自动重新加载(差异 b,`begin_requires_deps`) | 近似 | "之后"按依赖关系 `Above` 而不是按启动顺序;Cordis 不需要外部输入就完成依赖者的重启 |
| OTP `one_for_all` | 无直接对应 | — | 可编码为对一组根各发一次 `IRestart` |
| 重启强度 `intensity`/`period` | 无 | — | 演算没有时间;可用"每个序号最多 B 次重置"代替(课题 C2) |
| 升级:强度超限时监督者终止自身 | `O-Dispose` 监督者所在的根 fiber,`L-RetireChild` 逐个取消其子 fiber | 近似 | |
| 按启动顺序启动、按逆序终止 | `acc` 的 LIFO;`Spawn` 顺序决定 `USpawn` 在 `acc` 中的顺序 | 精确 | OTP 的启动表就是 `acc` 中 spawn 项的顺序 |
| link(双向退出信号) | 无 | — | 父终止取消子(单向);子失败不影响父 |
| monitor(单向通知) | 依赖解析:`visible` 只计入 Active 的提供者,提供者离开即改变依赖者的 target | 近似 | Cordis 中通知后的反应固定为"卸载并在提供者回来后重新加载" |
| Racket 共同监护(多个使用者时共享抽象继续运行) | 守卫 `held`:任一依赖者仍解析时提供者不撤销任何一项;`Ordering.unload_waits` | 近似 | Racket 是"有人需要就一直活";Cordis 是"等依赖者走完再撤",而依赖者因 target 变化必然离开,不会永远等 |
| Dijkstra–Scholten 亏欠计数 | `L-Remove` 要求没有 `πₘ = n` 的子 fiber;`parent_waits_child` | 形似 | 演算中有全局视图,不需要分布式协议 |
| 区域 `letregion` 按 LIFO 释放 | 单个 fiber 内 `acc` 的 LIFO | 精确(单 fiber) | 跨 fiber 不是 LIFO:提供者与依赖者的生命期沿 DAG 嵌套(`provider_outlives`),接近 Fluet 等的非 LIFO 区域,但由运行时守卫而非线性类型保证 |

## 3. 差异

**演算有而结构化并发没有的。**

1. **依赖边上的生命期约束。** 结构化并发只保证树形嵌套。Cordis 还保证提供者的全部效应比依赖者活得久
   (`unload_waits`、`provider_outlives`),而且依赖者不是提供者的子任务。合起来,生命期沿 `Above`(spawn 边加提供边)
   嵌套,这是一个 DAG。Trio、Kotlin、Swift 中两个兄弟任务之间若有服务依赖,只能靠手工的启动、关闭顺序。
2. **自动的依赖重启。** 提供者重启(`O-Restart`)或失败后被重置(`O-Reset`),依赖者的卸载与重新加载由生命周期规则完成。
   这是一个按依赖关系计算的 rest_for_one,而且有合流定理保证终态与调度无关(`Dynamic.dynamic_agree`)。
3. **恢复精确性。** 结构化并发只保证"子任务结束了",不说它留下的状态。Cordis 证明了 fiber 卸载完毕后存储 ≃ 略去它全部操作的影子存储
   (`Recovery.recovery_exact`,运行期效应为 `Runtime.effect_exact`)。
4. **取消必然完成。** 卸载中的等待有终止证明(`Termination.termination`),这依赖程序有界与秩有界。
   结构化并发的运行时不保证子任务响应取消。

**结构化并发有而演算没有的。**

1. **失败向上传播。** Trio 和 Kotlin 普通 `Job` 中子任务失败会取消父任务与兄弟;Cordis 只有 supervisor 语义。
   这是有意的选择(插件失败不应拖垮宿主),但演算目前无法表达"这个子 fiber 是父 fiber 的必需部分,它失败则父失败"。
2. **程序可控的屏蔽。** Haskell 的 `mask`、Trio 的 shield 让程序声明一段不可取消的区间。演算的落地是调度的非确定选择,
   程序不能要求"这三步要么都走完要么都不走"。D6 的 `prepare`/`commit` 形状把一步之内的原子性交给服务,
   跨多步的原子区间不在模型内。
3. **超时与截止时间。** cancel scope 可带 deadline,`timeout` 是取消的主要来源之一。演算没有时间。
4. **子任务的返回值。** nursery、`StructuredTaskScope` 收集子任务结果;Cordis 子 fiber 没有返回值,只通过服务交互。

**与 OTP 的差异。**

1. OTP 由监督者进程在运行时决定重启;Cordis 的自动部分(依赖者重启)在规则里,需要决定的部分(失败者是否重试)在外部。
2. OTP 的重启强度依赖时间窗口;演算中只能按次数。
3. OTP 子进程崩溃即丢失状态,"重启"从头初始化;Cordis 中失败的 fiber 先经 `Unloading` 按 LIFO 撤销全部效应
   (`Fail` 的效果是 `Unloading acc ω (Some ξ)`),重启前状态已经回到"它从未运行"(恢复精确性)。这比 let-it-crash 多一层保证:
   崩溃的组件在共享服务里留下的痕迹也被清除。

## 4. 候选课题

### C1 结构化生命期定理(小)

- **目标。** 把"子 fiber 不逃出父作用域,且与父的其他效应按 LIFO 嵌套"写成执行级的定理,作为与结构化并发文献对照时可以直接引用的陈述。
- **做法。** 由 `wf_parent`、`wf_reachable`、`parent_waits_child` 与 LIFO 推出:对任意执行,子 fiber `m` 存在的区间包含于
  父 fiber 已安装且 `acc` 含 `USpawn m` 的区间;父 fiber 在 `USpawn m` 之后压入的撤销项都在 `m` 被移除之前撤销,之前压入的都在之后撤销。
  再把依赖边并进来:沿 `Above` 的任意路径,下游的存在区间包含于上游的已安装区间(由 `provider_outlives` 与 `unload_waits`)。
  放在新文件(如 `theories/Structured.v`),只用已有定理。
- **预期产出。** 两三个定理(`child_scoped`、`nested_teardown`、`dag_scoped`),以及 RULES §6 中一段与 Swift SE-0304、Trio、Kotlin 的对照说明。
- **风险。** 低。执行级陈述需要在 `run_labels` 上做区间推理,记号可能比证明麻烦。
- **工作量。** 小。

### C2 监督者作为编排扩展(中)

- **目标。** 在 `Ext/Orchestrator.v` 的框架内定义监督者,给出 OTP 监督策略在演算中的语义,并证明它们继承的保证。
- **做法。**
  1. 监督策略是一个函数:观察状态中失败的 fiber(`Inactive (Some _)`),给出 `IReset`/`IRestart`/`IDis` 输入;
     带每个序号的重置预算 B(代替 `intensity`/`period`),预算用完则对监督者所在的根发 `IDis`(升级)。
     由于 `drun_labels` 对任意输入序列成立,依赖状态选择输入不影响第 0–2 层(`orch_wf`、`orch_recovery`)。
  2. 预算 ⇒ 有限输入(义务 O2)⇒ `orch_live`。
  3. 合流:`scomps` 只看 `IIns` 与 `IDis`(`Dynamic.live_ix`),所以插入任意多个 `IReset`/`IRestart` 不改变存活组件序列。
     直接由 `dynamic_agree` 得到:两次监督执行只要插入与 dispose 的输入相同、终态 quiet 且无失败,就在重命名意义下一致,
     与重启的次数和时机无关。这把"失败是合流唯一的例外"缩小为"重试之后仍失败"。
  4. 依赖者的 rest_for_one 是自动的:陈述"失败的提供者被重置并重新 Active 后,若终态稳定,则其依赖者都回到 Active"
     (由 `quiet_settled` 与 `settled` 的定义)。
  5. 监督非根 fiber:`Input` 只能指称根(O1)。`Dynamic.sl_reset`、`sl_restart` 对任意 fiber 成立,
     所以给 `Input` 加按规范名(`SpawnConf.CName`)指称子 fiber 的 `IReset`,只需扩展台账 `Ledger`,不必改 `SLInv`。
- **预期产出。** `Ext/Supervisor.v`:策略定义、`sup_live`、`sup_agree`(第 3 条)、`sup_rest_for_one`(第 4 条);
  EXTENSIONS.md 新增一节,列出 one_for_one、rest_for_one、one_for_all、temporary/transient/permanent 在演算中的读法。
- **风险。** 第 5 条中规范名在执行中途不一定稳定(父 fiber 重新加载后子 fiber 换名),台账的陈述可能变复杂,可先只做根。
  时间窗口语义的强度无法表达,只能用次数近似,需在文档中说明。
- **工作量。** 中(1–4 条偏小,第 5 条偏中)。

### C3 两段式运行时对演算的模拟:落地与放弃(中到大)

- **目标。** 形式化 DESIGN D6 的 `prepare`/`commit`:操作先 `await` 外部数据,再在一个同步片段中检查 epoch 并提交。
  证明它的每个执行对应演算的一个执行,两种策略(落地:提交后再检查;放弃:检查后再决定是否提交)都被覆盖。
  这正好把 Trio 的"`Cancelled` 即操作没有发生"和 Cordis 的 inertial 行为放进同一个模拟定理。
- **做法。** 定义一个细粒度的运行时语义:fiber 可处于"等待 prepare"的中间态,target 可在其间变化;
  模拟关系把中间态映射为演算中"这一步还没走"。落地策略下提交对应一次 target 已变的 `L-Step`,随后 `L-Divert`;
  放弃策略下直接对应 `L-Divert`。证明前向模拟(每个运行时步对应零或一个演算步),于是保持性、顺序、恢复、合流都转移过来。
  `prepare` 不终止的情形只影响活性,单独说明。
- **预期产出。** `theories/Runtime2.v`(或 `Ext/Async.v`)与模拟定理;D6 从"设计,尚未形式化"变为已证。
  可与 Haskell 的 `MaskedInterruptible`(屏蔽中阻塞仍可被打断)对照:`prepare` 期间可放弃,`commit` 不可打断。
- **风险。** 运行时语义里控制规则也要原子(D6 的 TOCTOU 段),建模时需要决定粒度;若把服务操作的内部状态也纳入,工作量会上升到大。
- **工作量。** 中(只建 epoch 与两段操作)到大(含服务内部)。

### C4 失败局部性定理(小到中)

- **目标。** 陈述 Cordis 的 supervisor 语义:一个 fiber 失败只影响它的依赖下游与子孙,对应 one_for_one 的隔离保证。
- **做法。** 证明:`L-Step n` 走到 `Fail`(或操作失败)之后,只有沿 `Above` 依赖于 `n` 所提供的键、或是 `n` 的后代的 fiber,
  其 target 可能因此改变;其余 fiber 的 target 与生命周期不受影响。工具是 `Termination.lstep_effects`、`mu_other`
  (一个 fiber 的步不影响秩不高于它的其他 fiber)与 `target` 的定义。
- **预期产出。** `fail_local` 一类定理,放在 `Ordering.v` 旁的新文件;为 C2 的 rest_for_one 读法提供依据。
- **风险。** 低。要小心 `Provide` 失败时绑定未建立、依赖者本来就看不到的情形。
- **工作量。** 小到中。

### C5 可选的失败传播(中,优先级低)

- **目标。** 评估"必需子 fiber"(子失败则父失败,Trio/Kotlin 普通 `Job` 的语义)能否作为扩展加入,而不破坏已有定理。
- **做法。** 在组件里给 spawn 标记 `required`;新增规则:子 fiber 进入 `Inactive (Some ξ)` 且标记为 required 时,
  父 fiber 若处于 Loading/Active,则进入 `Unloading acc ω (Some ξ')`。按 EXTENSIONS.md 第 0 节的隔离方法放在 `Ext/` 下。
  检查保持性、顺序、恢复、进展、终止是否仍成立;合流本来就排除失败,预计不受影响。
- **预期产出。** 一个扩展及其各层定理状态表,或一个反例说明为什么不该加。
- **风险。** 终止度量可能要改:子 fiber 失败导致父卸载,父的秩低于子,字典序度量需要检查。dsh 是否需要这个语义尚无证据。
- **工作量。** 中。

**排序建议。** C2 > C1 > C4 > C3 > C5。C2 与现有 `Ext/Orchestrator.v` 贴合最紧,第 3 条几乎是现成推论,却回答了"失败后重试是否影响合流";
C1、C4 工作量小,给对外表述提供可引用的定理;C3 价值高但工作量最大。

## 5. 参考文献

每条都用检索核对过作者、题目、会议或期刊、年份;核对不全的在条目后注明。

1. Simon Marlow, Simon Peyton Jones, Andrew Moran, John Reppy. Asynchronous Exceptions in Haskell. PLDI 2001, pp. 274–285. DOI 10.1145/378795.378858.
2. Daan Leijen. Structured Asynchrony with Algebraic Effects. TyDe 2017(ICFP 2017 联合研讨会);MSR-TR-2017-21. DOI 10.1145/3122975.3122977.
3. Danel Ahman, Matija Pretnar. Asynchronous Effects. Proc. ACM Program. Lang. 5(POPL), Article 24, 2021.
4. Roman Elizarov 等. Kotlin Coroutines: Design and Implementation. Onward! 2021, pp. 68–84. DOI 10.1145/3486607.3486751.(Crossref 记录只列出 Elizarov 一人;其余作者未核实。)
5. John McCall, Joe Groff, Doug Gregor, Konrad Malawski. SE-0304: Structured Concurrency. Swift Evolution 提案,Swift 5.5 实现(2021)。
6. JEP 453: Structured Concurrency (Preview). OpenJDK,JDK 21(2023)。前后版本:JEP 428(JDK 19)、437(JDK 20)、462、480(JDK 23)、505(JDK 25)。作者 Ron Pressler、Alan Bateman 是按 JEP 437 与 480 核实的,JEP 453 页面本身未能打开,其作者行**未核实**。
7. Nathaniel J. Smith. Notes on Structured Concurrency, or: Go Statement Considered Harmful. 博客文章,vorpus.org,2018 年 4 月。
8. Trio 文档,Core functionality(cancel scope、checkpoint、nursery、shield)。trio.readthedocs.io,2026 年 11 月查阅。
9. kotlinx.coroutines 文档:`Job` API 与 Coroutine exceptions handling。2026 年 11 月查阅。
10. Eio 文档与 README(switch、取消上下文)。github.com/ocaml-multicore/eio,2026 年 11 月查阅。
11. Erlang/OTP 文档,Supervision Principles(重启策略、强度、子进程类型、启动与终止顺序)。erlang.org,2026 年 11 月查阅。
12. Jonathan K. Lee, Jens Palsberg. Featherweight X10: A Core Calculus for Async-Finish Parallelism. PPoPP 2010, pp. 25–36.
13. Matthew Flatt, Robert Bruce Findler, Shriram Krishnamurthi, Matthias Felleisen. Programming Languages as Operating Systems (or, Revenge of the Son of the Lisp Machine). ICFP 1999, pp. 138–147. DOI 10.1145/317636.317793.
14. Matthew Flatt, Robert Bruce Findler. Kill-Safe Synchronization Abstractions. PLDI 2004, pp. 47–58. DOI 10.1145/996841.996849.
15. Yi-An Chen, Yi-Ping You. Structured Concurrency: A Review. ICPP Workshops 2022. DOI 10.1145/3547276.3548519.(第一作者经 Crossref 核实;第二作者只见于一处索引,**未完全核实**。)
16. Namratha Gangamreddypalli, Constantin Enea, Shaz Qadeer. Reduction for Structured Concurrent Programs. ESOP 2026;arXiv:2601.13341。
17. Joe Armstrong. Making Reliable Distributed Systems in the Presence of Software Errors. 博士论文,2003。(题目与年份已核实;授予单位通常记为 KTH,检索中**未核实**。)
18. Hans Svensson, Lars-Åke Fredlund, Clara Benac Earle. A Unified Semantics for Future Erlang. 9th ACM SIGPLAN Erlang Workshop, 2010, pp. 23–32. DOI 10.1145/1863509.1863514.
19. David Castro, Víctor M. Gulías, Clara Benac Earle, Lars-Åke Fredlund, Samuel Rivas. A Case Study on Verifying a Supervisor Component Using McErlang. ENTCS 271, 2011, pp. 23–40.
20. Ian Cassar, Adrian Francalanza, Claudio Antares Mezzina, Emilio Tuosto. Reliability and Fault-Tolerance by Choreographic Design. PrePost 2017, EPTCS 254, pp. 69–80. DOI 10.4204/EPTCS.254.6.
21. Rumyana Neykova, Nobuko Yoshida. Let It Recover: Multiparty Protocol-Induced Recovery. CC 2017, pp. 98–108.
22. Ivan Lanese, Naoki Nishida, Adrián Palacios, Germán Vidal. A Theory of Reversibility for Erlang. JLAMP 100, 2018, pp. 71–97. DOI 10.1016/j.jlamp.2018.06.004.
23. Simon Fowler, Sam Lindley, J. Garrett Morris, Sára Decova. Exceptional Asynchronous Session Types: Session Types without Tiers. Proc. ACM Program. Lang. 3(POPL), 2019. DOI 10.1145/3290341.(与 session-types.md 交叉:对端失败时会话被取消,与依赖者随提供者离开相近。)
24. Gul Agha. Actors: A Model of Concurrent Computation in Distributed Systems. MIT Press, 1986.
25. Edsger W. Dijkstra, C. S. Scholten. Termination Detection for Diffusing Computations. Information Processing Letters 11(1): 1–4, 1980.
26. Sylvan Clebsch, Sophia Drossopoulou. Fully Concurrent Garbage Collection of Actors on Many-Core Machines. OOPSLA 2013, pp. 553–570. DOI 10.1145/2509136.2509557.
27. Mads Tofte, Jean-Pierre Talpin. Region-Based Memory Management. Information and Computation 132(2): 109–176, 1997.
28. Matthew Fluet, Greg Morrisett, Amal Ahmed. Linear Regions Are All You Need. ESOP 2006, LNCS 3924, pp. 7–21.
29. Oleg Kiselyov, Chung-chieh Shan. Lightweight Monadic Regions. Haskell Symposium 2008, pp. 1–12. DOI 10.1145/1411286.1411288.
30. Haskell `base` 库文档,Control.Exception(`mask`、`uninterruptibleMask`、`bracket`)。hackage,base-4.22.0.0,2026 年 11 月查阅。
