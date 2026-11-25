# 动态组件模型与动态软件更新

主要对照 F3(target 驱动)、F4(依赖声明)、F10(热重载),顺带涉及 F2(守卫 `¬held`)与 F9(合流)。
规则名见 [docs/RULES.md](../docs/RULES.md),设计点见 [docs/DESIGN.md](../docs/DESIGN.md),扩展见
[docs/EXTENSIONS.md](../docs/EXTENSIONS.md)。文中 Rocq 名字都在 `theories/` 下核对过。

## 1. 领域概览

### 1.1 动态重配置:quiescence、tranquility、版本一致性

- **Kramer 与 Magee [KM90]** 把系统看成由事务连接的节点,重配置操作是增删节点和连线。
  修改一个节点之前,它必须处于 quiescent 状态:不在事务中,也不会再发起或接受新事务。
  做法是先让节点"被动"(passive,不再发起新事务),并让所有可能向它发起事务的节点也被动,
  等在途事务结束。代价是被动化的范围大,打扰正常运行。
- **Vandewoude 等 [VEBD07]** 提出更弱的 tranquility:只要求节点本身和与它直接相连、
  可能再次让它参与在途事务的邻居满足局部条件,不必冻结所有潜在调用者。它更容易达到,
  但依赖组件是"黑盒"、事务不嵌套地重入等前提。
- **Ma、Baresi、Ghezzi 等 [MBG+11]** 提出版本一致性(version consistency):每个分布式事务
  要么全程看到旧版本,要么全程看到新版本。他们给出分布式检查算法,用图变换系统形式化,
  再用模型检测验证。

这一脉的共同点:**更新的安全条件是"何时可以动手"的局部条件**,保护对象是跨组件的在途事务。

### 1.2 OSGi 与 Declarative Services

- **服务层 [OSGi-Core]**:bundle 向注册表注册服务对象,别的 bundle 查找并使用。服务随时可能
  出现和消失,这就是"服务动态性"。注销时,框架在注销完成之前**同步**投递 `UNREGISTERING`
  事件,使用者应当在回调中释放;不释放的,框架在注销时强行收回 [OSGi-Javadoc]。
  停止一个 bundle 时,先调用它的 `BundleActivator.stop`,之后框架才注销它残留的服务
  (Core 规范 4.4.8、4.5 节)。
- **Declarative Services(DS)[OSGi-DS]** 让组件以声明方式描述引用(reference),由 SCR
  负责激活与绑定:
  - **满足(satisfied)**:所有引用的目标数达到最小基数时,组件配置是满足的;满足才激活,
    提供的服务也只在满足时注册。激活的配置一旦不满足,必须停用(112.5.2)。
  - **基数**:`0..1`、`1..1`(默认)、`0..n`、`1..n`。可选引用不阻止激活。
  - **绑定策略 static(默认)**:一次激活期间绑定的服务固定。"被绑定的服务变得不可用之前,
    SCR 停用该组件配置;若有替代的目标服务,再激活并绑定替代者"(112.3.7.1)。
  - **绑定策略 dynamic**:SCR 在不停用配置的情况下改变绑定集合,通过 bind/unbind 回调通知组件。
  - **policy-option**:reluctant(默认)尽量不重绑,新出现的或更好的服务不触发重新激活;
    greedy 则会为更好的服务重新激活(static)或重绑(dynamic)。具体动作见表 112.1。
  - **环**:SCR 检测引用环;若环上有可选引用,就让它绑定零个目标来打破环(112.3.11)。
- **对 OSGi 的形式化**:Blech 给出 OSGi 框架的一个形式化草案,用于行为类型、运行时监控和组合
  兼容性检查 [Ble12],以及基于有限自动机的组件行为规格框架 [Ble13]。我们没有找到对 DS 生命周期
  (满足、停用、重绑)的机械化证明,更没有关于终态唯一性的结论。

### 1.3 Fractal、GCM 与 Coq 中的重配置

- **Fractal [BCL+06]** 是分层组件模型:组件有内容、绑定、生命周期等控制器,可以嵌套与共享;
  重配置通过这些控制器在运行时改结构。Merle 与 Stefani 用 Alloy 写了 Fractal 参考规范的完整
  形式化 [MS08]。
- **Mefresa [GHM14]** 在 Coq 中给出 GCM(Fractal 的分布式扩展)应用结构的形式规格,用来证明
  结构重配置的可靠性,即重配置操作保持结构良构。
- **Boyer、Gruber、Pous [BGP13]** 在 Coq 中证明了一个能承受任意多次失败的重配置协议。
  他们的重配置契约有四条架构不变式,其中三条是:(I1) 已启动的组件,强制导入都已连线;
  (I2) 已启动的组件只连到已启动的组件;(I4) 强制导入之间无环。生命周期是 STOPPED、STARTED、
  FAILED 三态。协议先算当前架构与目标架构的差,把"拆掉某条强制连线"传播成"先停掉依赖它的
  组件",排成一个"递增一致"的操作序列,先执行 down 阶段再执行 up 阶段。失败时可以回滚或前滚。
  论文明确说,执行序列时所需的 quiescence 交给组件运行时去保证。
- **Coqcots/Pycots [BDLM16]**:在组件模型中引入 DSU 式的替换,重配置脚本在 Coq 中先证明
  正确再导出执行。
- **Aeolus [DMZZ14]**:组件带有限状态机,每个状态激活一组 provide/require 端口;研究"能否到达
  目标配置"的可达性问题:完整模型不可判定,去掉非功能需求后可判定但 Ackermann 难,再去掉冲突后
  多项式时间。
- **Concerto [CCR21]**:组件生命周期由 place 与 transition 组成,端口挂在 place 和 transition 上,
  用来协调重配置动作,并给出执行时间的预测模型;去中心化版本 Concerto-D 用 Maude 形式化
  [ACL+24]。

### 1.4 依赖注入

依赖注入(DI)几乎没有对"容器语义"本身的形式化。我们找到的两类相关工作:

- **Grapht [EL16]**:Java DI 容器,把依赖注入表示成对象图上的数学结构,配置好的对象图可以
  提前静态分析;支持按图中位置选实现(context-aware policy)。
- **隐式演算 [OSC+12]**:Scala implicits 的核心演算 λ⇒,按类型解析隐式参数,支持部分解析和
  高阶规则。按类型自动供给依赖,与 DI 同构。

两者都只处理**静态装配**:装配一次,不讨论运行中依赖出现、消失、替换。余效应方面见
[effects-coeffects.md](effects-coeffects.md)。

### 1.5 动态软件更新(DSU)

- **有效性 [GJB96]**:Gupta、Jalote、Barua 定义在线版本切换的有效性(切换后的状态是新程序
  可达的状态),证明一般情况下不可判定,并给出过程式语言下的充分条件。
- **Hicks 与 Nettles [HN05]**:补丁带新代码和从旧版本迁到新版本的代码,以可验证的本地代码
  (PCC/TAL)形式加载。
- **Proteus [SHB+05](期刊版 TOPLAS 2007)**:C 风格语言的 DSU 演算,用户给类型变换函数
  迁移旧类型的值;静态"可更新性分析"预测更新点上更新是否会失败。
- **Bierman 等 [BHSS03]**:仿照 Erlang 的小型更新演算,扩展带类型的 λ 演算。
- **Ginseng [NHSO06]**:Proteus 在 C 上的实现,应用于 vsftpd、sshd、Zebra。
- **Kitsune [HSD+12](期刊版 TOPLAS 2014)**:整程序更新:在显式更新点停下,启动新版本,
  由程序员标注、工具生成的代码把状态搬到新版本,再让控制流走到对应位置。
- **Rubah [PVH14]**:Kitsune 的思路搬到未修改的 JVM 上。
- **更新正确性 [HMH+12]**:Hayden 等把旧版本和更新合并成一个模拟"运行中更新"的程序,按客户端
  可见行为写规格(向后兼容的规格,或描述更新前后行为的规格),再用自动验证器检查。
- **向后兼容 [SB15]**:Shen 与 Bazzi 对与未更新环境交互的程序给出向后兼容的一般定义。
- **分布式升级 [ALS06]**:Ajmani、Liskov、Shrira 的模块化升级:transform function 迁移节点
  持久状态,simulation object 让节点在升级期间同时扮演多个版本。

### 1.6 Erlang/OTP 热代码加载

- 同一模块可以同时有两个版本(当前与旧);清除旧版本时,仍在执行旧代码的进程被杀掉
  [OTP-RH][OTP-Appup]。
- 有状态的行为进程(如 `gen_server`)升级时,release handler 先挂起进程,加载新代码,
  调用 `code_change(OldVsn, State, Extra)` 把状态变换到新版本,再恢复进程。进程身份(pid)不变,
  别的进程手里的引用照样有效。
- appup 中的 `DepMods` 声明模块间依赖,决定加载顺序(升级与降级方向相反)。升级路径是
  由工具生成的 relup 脚本,也就是一个**计划**。
- 形式化方面,我们只找到 Bierman 等仿照 Erlang 的更新演算 [BHSS03];没有找到对
  `code_change` 或 release handling 的机械化语义。Armstrong 的博士论文 [Arm03] 讨论了热更新在
  OTP 可靠性设计中的位置。

### 1.7 Nix 与声明式部署

- **Nix [DdJV04]**:每个构件实例的存储路径由其全部构建输入的密码学哈希决定。依赖变了,
  依赖者的路径也变,只能重新构建;同一路径的内容不变。
- **NixOS [DL08](期刊版 [DLP10])**:整个系统配置由纯函数式规格构建,切换配置是原子的,可回滚。

## 2. 对照表

记号:**精确** = 精确对应;**近似** = 近似对应;**形似** = 仅形似。

| 领域概念 | 演算中的对应 | 程度 | 说明 |
|---|---|---|---|
| KM quiescence(修改节点的前提) | 守卫 `¬held`(`L-Undo`、`L-RetireChild` 的前提);`unload_waits`、`unload_blocked` | 近似 | 都是"别人还要用我时不动手"。演算更强:依赖者不只是被动,而是整个卸载完毕(见 2.1) |
| KM 的 passive(不再发起新事务) | 无 | — | 演算中每个服务操作是原子的 `L-Step`,没有跨步的事务概念 |
| KM 的被动化传播 | provider 离开 Active 使依赖者 `target` 变化,`L-Divert`/`L-Leave` 可走;`divert_when_changed`、`leave_when_changed` | 近似 | 演算不冻结依赖者,而是让它们卸载并稍后按新 target 重载 |
| "Cordis 的 quiet" 与 KM quiescence | `Calculus.quiet`:没有生命周期规则可用;`quiet_settled` | 形似 | 只是名字相近:前者是全局收敛,后者是单个节点可改的前提 |
| tranquility | 无 | — | 演算的守卫按整个 fiber 判断,不区分哪些效应被依赖者用过 |
| 版本一致性 | 承诺视图 ω:一次激活期间每个依赖解析到固定 pid;`step_coherent`、`provider_outlives`、`fiber_step`(已安装期间 ω 不变) | 近似 | 粒度是 fiber 的一次激活,不是一次事务;且更强:provider 在依赖者卸载完之前不撤销任何效应 |
| OSGi 服务注册表 | 绑定 `B : K ⇀ Binding`,`visible` | 近似 | OSGi 一个接口可有多个服务、带排序;演算一个键至多一个提供者(`O-Insert` 前提,设计点 c) |
| DS 的 satisfied | `target n ≠ ⊥`(每个依赖可见) | 精确 | 对 `1..1` 引用、每个接口唯一提供者的子集 |
| DS 激活前提 | `L-Begin`;`begin_requires_deps` | 精确 | 同上 |
| DS static 策略:服务不可用前先停用依赖者 | `withdraw_waits`、`withdraw_blocked` | 精确 | provision 一级的守卫 |
| DS static 策略:有替代者则重新激活 | `L-Leave` → `L-Undo`… → `L-Unloaded` → `L-Begin`(新 ω);设计点 b | 精确 | ω 记 pid,provider 重新提供即依赖者重载,正是 static |
| DS dynamic 策略 | 无 | — | 演算从不就地改 ω(`fiber_step`),见 2.1 问题 2 |
| DS `0..1` static greedy | 可选依赖扩展:在场集变化一律重载(`Ext/Optional.v`,`fresh`、`present`) | 精确 | EXTENSIONS 1.2 |
| DS `0..1` static reluctant | 无(EXTENSIONS 1.2 明确不建模) | — | 新服务出现不重载,终态与调度有关,破坏合流 |
| DS `0..n`、`1..n` | 无;设计点 r 的"每个条目一个键"可部分编码 | 近似 | 演算没有"一组 provision"的依赖 |
| DS 打破引用环 | 无;进展与终止都要求 `Above` 无无限上升链(`Progress.Above`),可选依赖边也要升秩 | — | DS 允许经可选引用成环,演算不允许 |
| OSGi bundle 停止顺序(先 `stop` 后注销服务) | 与 `unload_waits` 相反 | 形似 | 演算要求依赖者在 provider 的**全部**效应都在时卸载;OSGi 只保证服务一级 |
| Fractal/BGP13 的 (I1) | `begin_requires_deps` 与 WF 中"已解析的依赖都有绑定" | 精确 | "已启动 ⇒ 强制导入已连线" |
| BGP13 的 (I2) | `provider_outlives` | 近似 | (I2) 要求被连的组件已启动;演算只要求 provider 处于已安装状态(可在 Unloading,但守卫使它不撤销任何项) |
| BGP13 的 (I4) 无强制环 | `Above` 良基(`Progress.v`、`Termination.v` 的假设) | 精确 | 两边都用它保证传播或卸载终止 |
| BGP13 的"拆连线 ⇒ 先停依赖者"传播 | target 级联变 ⊥;`L-Leave` | 近似 | BGP13 是中心化地算出计划;演算由局部规则逐步收敛 |
| BGP13 的失败与回滚/前滚 | `Fail` → Unloading(带 ζ),`O-Reset`;恢复精确性 `recovery_exact` | 近似 | 演算的失败只回滚该 fiber;没有"前滚" |
| Mefresa:重配置保持结构良构 | `preservation`、`wf_reachable` | 近似 | Mefresa 的良构是架构层面的,WF 还包含累加器与绑定的对应 |
| Aeolus 的目标可达性 | `exists_quiet`(quiet 状态总能到达);`static_assembly` 把"能否无失败到达"留作前提 | 近似 | Aeolus 问是否**存在**计划;演算证明**任意**调度都收敛到同一终态 |
| Concerto 的 place/transition 生命周期 | `Θ` 四态与 `fiber_step` 的自动机 | 形似 | Concerto 的生命周期由组件作者自定义,演算的是固定的 |
| DI 按类型/名字解析依赖 | `d(c)`、`resolve`、`visible` | 近似 | DI 装配一次;演算装配随 provider 出现消失而反复 |
| Grapht 提前计算依赖图 | `Above` 关系与秩;`active_iff`、`fix_unique` | 近似 | 演算的 Active 集合是一个不动点方程的唯一解,可以提前算(课题 C4) |
| DSU 的更新点 | `L-Step` 的原子粒度;target 变化后可落地也可放弃(`L-Divert`,设计点 h) | 近似 | Proteus/Kitsune 的更新点由程序员放;演算中任意两步之间都可以转向 |
| Kitsune 整程序重启 | `O-Restart`:卸载后由 `L-Begin` 重新运行启动程序 | 近似 | Kitsune 搬运状态,演算不搬运(见 2.1 问题 3) |
| 状态迁移(Proteus 类型变换、Kitsune xfgen、`code_change`、Ajmani transform function) | 无 | — | 候选课题 C2 |
| 更新正确性(Hayden 等的客户可见规格) | `static_assembly`:更新后终态与直接部署新版本一致;`wb_indist`(≃ 蕴含不可区分) | 近似 | 演算给出的是"与重新部署不可区分",不需要逐个更新写规格 |
| GJB96 的有效性(切换后状态是新程序可达状态) | `static_assembly`、`self_update`(`Ext/Orchestrator.v`) | 近似 | 演算在无状态迁移时证明了比"可达"更强的"等于静态组装" |
| Erlang 两版本并存,清除时杀进程 | 守卫 `¬held`(等待而非杀死) | 形似 | 方向相反:Erlang 杀掉仍用旧代码的进程,演算等依赖者自己卸载 |
| Erlang 挂起 → `code_change` → 恢复 | 无(最接近的是 `O-Restart`,但它丢弃状态) | — | |
| appup `DepMods` 决定加载顺序 | `begin_requires_deps`、秩 | 近似 | Erlang 的顺序写在计划里,演算由规则前提自动保证 |
| Nix:依赖哈希变则依赖者重建 | 设计点 b:ω 记 pid,provider 重新提供则依赖者重载 | 近似 | 同一原则(依赖身份变,依赖者必须重来),Nix 在构建期,演算在运行期 |
| NixOS:系统状态由声明唯一决定 | `static_assembly`、`dynamic_agree` | 近似 | Nix 由纯性**构造性**保证;演算对任意交错的运行期调度**证明**了它 |

### 2.1 四个重点问题

**问题 1:Kramer–Magee 的 quiescence 与 `quiet`、守卫 `¬held` 的对应。**

- `quiet`(`Calculus.quiet`)与 quiescence 只是同名。`quiet` 说的是"整个系统没有生命周期规则
  可用",由 `quiet_settled` 等价于稳定(`settled`);它是收敛的终点,不是"可以动手"的前提。
- 真正对应 quiescence 的是守卫 `¬held`。KM 要求:修改节点 N 之前,没有别的节点正在或将要向 N
  发起事务。演算要求:撤销 fiber n 的任何一项之前,没有别的**已安装** fiber 解析到 n 的 provision
  (`unload_waits`、`unload_blocked`)。
- 演算比 KM 强,也比 KM 粗:
  - KM 只要求潜在调用者被动(活着,但不发起新事务);演算要求依赖者整个卸载完毕(Inactive),
    它们的效应已按 LIFO 撤掉。代价是依赖者必须重载,收益是依赖者在 provider 的全部效应都还在的
    状态上完成自己的撤销,不需要任何事务模型。
  - 演算没有"在途事务",因为每个服务操作是一个原子的 `L-Step`。KM 关心的"事务做到一半"在
    演算里只剩下"启动程序做到一半",由 `L-Divert` 与落地(设计点 h)处理,而且 `step_coherent`
    保证在途的每一步都按承诺视图执行。
  - KM 需要论证被动化最终能达成;演算的对应结论是不死锁(`progress`、`quiet_settled`)与终止
    (`termination`),证明沿 `Above` 做良基归纳,与 BGP13 的 (I4) 是同一个前提。
- 与版本一致性 [MBG+11] 比较:ω 在一次激活期间固定(`fiber_step`),provider 在依赖者卸载完之前
  不撤销任何效应(`unload_waits`),所以**每个依赖者的一次激活从头到尾只看到同一个 provision
  版本**。这是 fiber 激活粒度上的版本一致性,而且比 MBG+11 强:旧版本的 provider 连内部效应
  都保持不动。现有定理已经蕴含这一点,但没有作为单独的命题陈述(课题 C3)。
- tranquility 在演算里没有对应,也不应该有:RULES §5 第 2 条记录了早先把守卫只放在 `UProv`
  一项上的版本,依赖者会看到被拆了一半的服务。这正是 tranquility 式"只看局部"放宽的风险。

**问题 2:OSGi 服务动态性与 target 驱动重载的异同。**

- **相同**:DS 的 static 策略就是"依赖变则重启组件"。被绑定的服务不可用之前先停用依赖者
  (`withdraw_waits`),有替代者则按新绑定重新激活(`L-Leave` … `L-Begin`)。演算的设计点 b
  (ω 记 pid,provider 撤掉再提供,依赖者就重载)与 static 策略在 `1..1`、单一提供者的子集上
  逐条吻合。可选依赖扩展(EXTENSIONS 1)则恰好是 `0..1` 的 static **greedy**。
- **不同 1:reluctant。** DS 默认 reluctant:可选服务后出现时不重新激活。EXTENSIONS 1.2 指出这会
  让在场集取决于提供者激活的时机,终态与调度有关。所以演算的合流定理给 DS 一个具体结论:
  在 static reluctant 的可选引用下,SCR 的终态一般不唯一;要终态唯一,应选 greedy。这一点我们
  没有在 DS 文献中看到(课题 C1 要把它做成反例)。
- **不同 2:dynamic 策略。** dynamic 在不停用组件的情况下换绑定。演算不允许:已安装期间 ω 不变
  (`fiber_step`),这是 `provider_outlives`、恢复精确性(`UOp` 记录的 pid 在撤销时仍有绑定,
  RULES §8 第 2 条)的基础。要模型化 dynamic,至少要一条"重绑"规则,并要求被重绑的依赖在旧 pid
  上没有未撤销的 `UOp`,否则这些撤销项会悬空。
- **不同 3:守卫的范围。** OSGi 停止 bundle 时先调用 `BundleActivator.stop`,再由框架注销残留
  服务;`UNREGISTERING` 只保证使用者在服务注销之前被通知。依赖者因此可能在 provider 的内部
  资源已拆掉、服务还挂着的状态下运行。演算的 `unload_waits` 排除了这种情况。
- **不同 4:多提供者与排序。** OSGi 允许同一接口有多个服务并按 ranking 选择;演算以 `O-Insert`
  的不相交前提禁止,合流因此不需要考虑"更好的服务"。DS 用可选引用打破环,演算要求 `Above`
  良基,可选边也要升秩。

**问题 3:状态迁移能否作为新扩展。**

先说一个观察:在核心演算里,**卸载时没有状态可以迁移**。provider 撤到 `UProv k pid` 时,守卫保证
没有别的已安装 fiber 解析到 pid;解析过它的依赖者都已卸载,它们的操作已撤掉;provider 自己在
provide 之后的操作按 LIFO 也已撤掉。按第 2 层的单次执行不变式 `INV`(`StateInv.v`:绑定状态 ≃
初始状态依次施加仍待撤销的操作),此时待撤销列表为空,绑定状态 ≃ `inilog pid`,即 provide 时的
初始状态。换句话说,演算中的服务状态全部是"效应状态",随时可由程序重建;重载丢掉的东西,
重新加载后会原样回来(这就是 `static_assembly` 能成立的原因)。

所以 DSU 意义下的状态迁移,在演算里需要先引入**不随卸载撤销的状态**,也就是 EXTENSIONS 开头
排除在外的"外部持久世界":运行期反应写进去、卸载时不撤销的那部分。有了它,状态迁移才有对象。
可行的形状见课题 C2。它会改动两条元定理的陈述:恢复精确性要改成"除持久部分外精确";合流要以
持久部分为输入,终态与"以 τ(旧持久状态) 为初值的静态组装"一致。GJB96 的有效性正好可以当作
τ 的义务:τ 把旧版本可达的持久状态映到新版本可达的持久状态。

**问题 4:合流定理在这些文献中有无对应。**

基本没有。

- KM、tranquility、版本一致性都是"某一刻能否安全动手"的条件,不讨论不同调度的终态是否相同。
- DS 规范描述 SCR 的行为,没有终态唯一性的陈述;reluctant 策略下它也不成立(问题 2)。
- BGP13 在 Coq 中证明了重配置协议总产生架构一致的装配,并到达目标(失败允许的范围内)。但目标由
  管理者给出,协议是中心化地按计划执行;演算的目标(target)由声明与当前状态推出,规则局部地
  任意交错。
- Aeolus 研究目标配置是否**可达**(存在计划),不研究任意执行是否**汇合**。
- Concerto 关心执行时间的可预测性,Concerto-D 有 Maude 可执行语义。
- Erlang/OTP 的升级由 relup 计划给定顺序,顺序本身就是正确性的一部分。
- 最接近的是 Nix/NixOS:系统状态由声明唯一决定。但那是构建期由纯性与哈希构造性保证的,而且
  不涉及运行中依赖出现与消失的交错。
- DSU 的正确性 [HMH+12][SB15][GJB96] 针对一次更新:更新后的行为与某规格或某个新程序可达状态
  一致。`static_assembly` 在没有状态迁移时给出了更强的形式:任意多次插入、移除、重启与生命周期
  步任意交错后,终态与只部署幸存组件的执行一致。

所以 F9 是本方向文献中缺的一块,属于 PLAN 中的 (c):Cordis 的特征是这些领域还没处理好的。

## 3. 差异

**演算有、这些领域没有的:**

1. **任意调度的终态唯一**(`dynamic_agree`、`static_assembly`、扩展中的 `xstatic_assembly`、
   `dynamic_agree_perm`)。见问题 4。
2. **整个 fiber 的守卫**(`unload_waits`):依赖者在 provider 的全部效应都在时卸载。OSGi 只有服务一级,
   KM 只有被动化,BGP13 把 quiescence 交给运行时。
3. **撤销即逆**:卸载按 LIFO 施加记录下来的逆,且有恢复精确性(`recovery_exact`、`effect_exact`)。
   OSGi/DS 的停用是组件自己写的 `deactivate`,Fractal 的 stop 同样由组件实现,都没有"撤销后回到
   没有该组件时的状态"这一保证。
4. **服务状态的共享与可交换性条件**:合流要求可能相遇的操作对可交换(`HCom`、`CoPair`)。
   组件模型文献把服务当黑盒,不讨论多个依赖者对同一服务状态的写入顺序。
5. **target 由声明推出**:没有外部给的"目标架构",也没有计划;BGP13、Aeolus、Erlang relup 都有计划。

**这些领域有、演算没有的:**

1. **状态迁移**(Proteus、Kitsune、Rubah、`code_change`、Ajmani)。见问题 3 与课题 C2。
2. **就地换绑定**(DS dynamic、Fractal 运行时改绑定、Erlang 进程身份不变)。演算换依赖只能重载。
3. **多提供者、排序、多重引用**(OSGi ranking、`0..n`)。演算一个键一个提供者。
4. **类型或接口随版本变化**:Proteus 处理类型变换。演算用统一服务 Σ(RULES §0),键和状态类型都
   不随版本变。
5. **可选引用打破环**(DS)。演算要求 `Above` 良基。
6. **失败后的前滚**(BGP13)。演算失败只回滚该 fiber,由外部 `O-Reset` 重试。
7. **组件作者自定义的生命周期**(Concerto、Aeolus 的状态机)。演算的四态是固定的。
8. **分布式与多版本并存**(MBG+11、Ajmani)。演算是单机、单版本的。

## 4. 候选课题

按建议的先后排列。

### C1. DS static 子集嵌入演算,并给出 reluctant 的反例(小到中)

- **目标**:把"DS static 策略就是 target 驱动重载"从类比变成定理,并把"reluctant 破坏终态唯一"
  做成可检查的反例。
- **做法**:
  1. 定义 DS 的一个子集:每个接口唯一提供者,引用为 `1..1` 或 `0..1`,策略 static,
     policy-option 可选 greedy 或 reluctant;组件激活体是一个 `Prog`。
  2. 写出 SCR 的小步语义(满足、激活、停用、重新激活),证明 greedy 子集的每一步是演算(加可选
     依赖扩展)的一步或若干步,于是 `xpreservation`、`xquiet_settled`、`xtermination`、
     `xstatic_assembly` 直接适用。
  3. 对 reluctant:在 `theories/Ext/` 下构造两个组件(A 可选依赖 B 提供的键)和两次调度
     (B 先于 A 激活 / A 先于 B 激活),证明两个 quiet 终态中 A 的在场集不同,作为
     `reluctant_not_confluent`。
- **预期产出**:一份 DS ↔ 演算对照(可放进本目录),一个短 Rocq 文件。反例本身可以作为对
  DS 使用者的建议:要终态唯一,可选引用用 greedy。
- **风险**:DS 还有工厂组件、配置管理(Configuration Admin)、`0..n`、ranking,只能覆盖子集;
  SCR 的线程模型不在模型内。第 3 步几乎没有风险。
- **工作量**:反例小(一两百行);嵌入中。

### C2. 持久状态与状态迁移扩展(中到大)

- **目标**:给演算加上 DSU 的状态迁移,同时说清楚它让哪些定理改变陈述。
- **做法**:
  1. **先证一个小引理**(小):在第 2 层的服务假设下,`L-Undo` 撤到 `UProv k pid` 的那一步,
     绑定状态 ≃ `inilog pid`。由 `INV`、`PendList` 与守卫可得,形式化"核心演算中卸载时没有可迁移
     的状态"。
  2. **持久部分**:把服务状态拆成 `S = Sₑ × Sₚ`,持久部分 `Sₚ` 上的操作不记逆(或记恒等逆),
     只允许出现在反应(`O-React`)中;卸载时 `UProv` 不删除持久部分,而是把它存进一张按键索引的
     持久表。
  3. **迁移**:新规则 `O-Upgrade i c' τ`(按插入序号指称根,同 `Dynamic.Input`),语义为
     `IDis i` 加 `IIns c'`,外加:c' 首次 provide 键 k 时,持久部分取 `τ(持久表 k)`。
  4. **定理**:第 0、1 层保守(迁移不碰累加器);恢复精确性改为"在 `Sₑ` 上精确"
     (投影后套用核心 `recovery_exact`);合流改为:两次执行若持久表按 ≃ 相同,且 τ 尊重 ≃,
     则终态一致。GJB96 的有效性作为 τ 的义务单独陈述。
- **预期产出**:`theories/Ext/` 下的新扩展与一节 EXTENSIONS 文档;对 Cordis 的建议是把持久状态
  显式分出来(dsh 中目前写在外部文件里)。
- **风险**:持久部分上的写入顺序取决于运行期反应的调度,合流对持久部分一般不成立,只能以它为
  输入;第 2 层的轨迹不变式(`EPInv`、`Tr`)要处理"初始状态来自持久表",改动可能较深。
- **工作量**:第 1 步小;全部大。

### C3. 激活粒度的版本一致性定理(小)

- **目标**:把问题 1 的结论写成一个命题,作为与 KM/MBG+11 对照的锚点。
- **做法**:沿一次执行,对 fiber n 从 `L-Begin` 到回到 Inactive 的一段(一次激活),证明:
  (1) 其间 n 的每个 `L-Step` 在键 k 上作用于同一个 pid;(2) 该 pid 的提供者在 `L-Begin` 时是
  Active;(3) 在这一段结束之前,提供者不撤销累加器中的任何一项。由 `begin_requires_deps`、
  `fiber_step`、`provider_outlives`、`unload_waits` 组合得到,是推论。另加一个反例,说明把守卫
  只放在 `UProv` 上(tranquility 式放宽)时 (3) 不成立。
- **预期产出**:一个推论与一个反例,可放在 `Ordering.v` 之外的新文件中;文档里可直接引用。
- **风险**:低。需要先定义"一次激活"这一执行片段。
- **工作量**:小。

### C4. 静态预测终态配置(小到中)

- **目标**:在启动前,仅由组件表的 `d`、`p` 算出哪些插件最终会 Active,并证明预测正确。
  这相当于 DS 的"satisfied"计算、Grapht 的提前建图,但带证明。
- **做法**:由 `active_iff` 与 `fix_unique`,quiet 状态的 Active 集合是一个不动点方程的唯一解。
  写一个可计算函数 `predict`(按秩迭代或求最小不动点),证明它等于任意无失败 quiet 状态的
  Active 集合(先对不 spawn 的组件,用 `control_confluence`;再推广到 spawn 与可选依赖)。
  可以抽取到 `checker/`,对 dsh 的插件清单给出"哪些会因缺依赖停在 Inactive"。
- **预期产出**:`predict` 与 `predict_correct`;一个对插件清单运行的检查工具。
- **风险**:程序中的 `Fail` 无法静态预测,定理以"无失败"为前提;含 spawn 时子 fiber 是否出现取决于
  操作结果,只能给出上界。
- **工作量**:不 spawn 的情形小,推广中。

### C5. 就地重绑(DS dynamic)扩展(中)

- **目标**:回答"DS dynamic 能否在保持定理的前提下加入演算"。
- **做法**:新规则 `L-Rebind n k`:Active 的 n,`ω k` 指向的 provision 已不可见而 `visible k` 给出
  新 pid,且 n 的累加器中没有 pid 为旧值的 `UOp`(只读过或从未操作),则就地把 `ω k` 改为新 pid。
  检查 WF、`provider_outlives`、恢复精确性;合流要求重绑与重载产生相同终态,需要"未操作过的依赖
  不影响轨迹"的引理。
- **预期产出**:一个扩展,或一个清楚的否定结论(哪条定理在哪里失败)。
- **风险**:`get` 的结果已经影响了后续程序,换 provider 后"只读过"也不等于无影响,很可能只能对
  "从未在该键上操作"的依赖成立,适用面窄。
- **工作量**:中。优先级低于 C1–C4。

**最有价值的三个**:C2 的第 1 步加持久部分的设计(回答"状态迁移"且揭示核心演算的一个性质)、
C1(把 OSGi DS 的 static/greedy/reluctant 与合流挂钩,有对外可讲的反例)、C4(直接产出可用的检查
工具)。C3 工作量最小,适合作为对照文献时的引用锚点。

## 5. 参考文献

核实方式:作者、题目、会议或期刊、年份经网络检索(出版社页面、DBLP、作者主页、HAL、arXiv 等)
逐条核对。正文中对论文内容的转述,凡未读到原文、只依据摘要或二手材料的,已在下面注明。

- **[KM90]** Jeff Kramer, Jeff Magee. The evolving philosophers problem: dynamic change management.
  IEEE Transactions on Software Engineering 16(11):1293–1306, 1990。
  quiescence 与 passive 的定义依据二手材料转述(Vandewoude 等、Wermelinger 对它的引述),未读原文。
- **[VEBD07]** Yves Vandewoude, Peter Ebraert, Yolande Berbers, Theo D'Hondt. Tranquility: A low disruptive
  alternative to quiescence for ensuring safe dynamic updates. IEEE Transactions on Software Engineering
  33(12):856–868, 2007。tranquility 的具体条件依据摘要与记忆转述,未读原文。
- **[MBG+11]** Xiaoxing Ma, Luciano Baresi, Carlo Ghezzi, Valerio Panzica La Manna, Jian Lü. Version-consistent
  dynamic reconfiguration of component-based distributed systems. ESEC/FSE 2011, pp. 245–255。依据摘要。
- **[OSGi-Core]** OSGi Alliance. OSGi Core Release 8, Chapter 4 "Life Cycle Layer"(4.4.8、4.5 节)与
  Chapter 5 "Service Layer"。docs.osgi.org/specification/osgi.core/8.0.0/。bundle 停止顺序依据 4.4.8、
  4.5 节的文字推断。
- **[OSGi-Javadoc]** OSGi Core Release 8 Javadoc, `org.osgi.framework.ServiceEvent`(`UNREGISTERING`)。
- **[OSGi-DS]** OSGi Alliance. OSGi Compendium Release 8, Chapter 112 "Declarative Services Specification",
  Version 1.5。docs.osgi.org/specification/osgi.cmpn/8.0.0/service.component.html。112.3.7、112.3.11、
  112.5 节已读。
- **[Ble12]** Jan Olaf Blech. Towards a formalization of the OSGi component framework. arXiv:1208.2563, 2012。
- **[Ble13]** Jan Olaf Blech. Towards a framework for behavioral specifications of OSGi components.
  FESCA 2013, EPTCS 108, pp. 79–93, 2013。
- **[BCL+06]** Eric Bruneton, Thierry Coupaye, Matthieu Leclercq, Vivien Quéma, Jean-Bernard Stefani.
  The FRACTAL component model and its support in Java. Software: Practice and Experience 36(11–12):1257–1284, 2006。
- **[MS08]** Philippe Merle, Jean-Bernard Stefani. A formal specification of the Fractal component model in Alloy.
  INRIA Research Report RR-6721, 2008。
- **[GHM14]** Nuno Gaspar, Ludovic Henrio, Eric Madelaine. Bringing Coq into the world of GCM distributed
  applications. International Journal of Parallel Programming 42(4):643–662, 2014。依据摘要。
- **[BGP13]** Fabienne Boyer, Olivier Gruber, Damien Pous. Robust reconfigurations of component assemblies.
  ICSE 2013, pp. 13–22。架构不变式 (I1)(I2)(I4) 与传播规则读自作者主页上的论文 PDF。
- **[BDLM16]** Jérémy Buisson, Fabien Dagnat, Elena Leroux, Sébastien Martinez. Safe reconfiguration of
  Coqcots and Pycots components. Journal of Systems and Software 122:430–444, 2016。依据摘要。
- **[DMZZ14]** Roberto Di Cosmo, Jacopo Mauro, Stefano Zacchiroli, Gianluigi Zavattaro. Aeolus: A component
  model for the cloud. Information and Computation 239:100–121, 2014。
- **[CCR21]** Maverick Chardet, Hélène Coullon, Simon Robillard. Toward safe and efficient reconfiguration
  with Concerto. Science of Computer Programming 203, 2021。place/transition/端口的说法依据作者报告
  幻灯片与 Concerto-D 论文的概述,未读原文。
- **[ACL+24]** Farid Arfi, Hélène Coullon, Frédéric Loulergue, Jolan Philippe, Simon Robillard. An overview
  of the decentralized reconfiguration language Concerto-D through its Maude formalization. ICE 2024,
  EPTCS 414, 2024。
- **[EL16]** Michael D. Ekstrand, Michael Ludwig. Dependency injection with static analysis and context-aware
  policy. Journal of Object Technology 15(1), 2016。
- **[OSC+12]** Bruno C. d. S. Oliveira, Tom Schrijvers, Wontae Choi, Wonchan Lee, Kwangkeun Yi. The implicit
  calculus: a new foundation for generic programming. PLDI 2012, pp. 35–44。
- **[GJB96]** Deepak Gupta, Pankaj Jalote, Gautam Barua. A formal framework for on-line software version change.
  IEEE Transactions on Software Engineering 22(2):120–131, 1996。作者名 Deepak 未在检索结果中直接看到,
  按 IIT Kanpur 的作者记录写出,名字部分**未核实**。
- **[HN05]** Michael Hicks, Scott Nettles. Dynamic software updating. ACM TOPLAS 27(6):1049–1096, 2005。
- **[SHB+05]** Gareth Stoyle, Michael Hicks, Gavin Bierman, Peter Sewell, Iulian Neamtiu. Mutatis Mutandis:
  Safe and predictable dynamic software updating. POPL 2005, pp. 183–194;期刊版 ACM TOPLAS 29(4), 2007。
- **[BHSS03]** Gavin Bierman, Michael Hicks, Peter Sewell, Gareth Stoyle. Formalizing dynamic software updating.
  Second International Workshop on Unanticipated Software Evolution (USE), 2003。
- **[NHSO06]** Iulian Neamtiu, Michael Hicks, Gareth Stoyle, Manuel Oriol. Practical dynamic software updating
  for C. PLDI 2006, pp. 72–83。
- **[HSD+12]** Christopher M. Hayden, Edward K. Smith, Michail Denchev, Michael Hicks, Jeffrey S. Foster.
  Kitsune: Efficient, general-purpose dynamic software updating for C. OOPSLA 2012;期刊版作者为
  Hayden, Saur, Smith, Hicks, Foster,ACM TOPLAS 36(4):13, 2014。
- **[PVH14]** Luís Pina, Luís Veiga, Michael Hicks. Rubah: DSU for Java on a stock JVM. OOPSLA 2014, pp. 103–119。
- **[HMH+12]** Christopher M. Hayden, Stephen Magill, Michael Hicks, Nate Foster, Jeffrey S. Foster. Specifying
  and verifying the correctness of dynamic software updates. VSTTE 2012, LNCS 7152, pp. 278–293。
- **[SB15]** Jun Shen, Rida A. Bazzi. A formal study of backward compatible dynamic software updates.
  SEFM 2015;arXiv:1503.07235。
- **[ALS06]** Sameer Ajmani, Barbara Liskov, Liuba Shrira. Modular software upgrades for distributed systems.
  ECOOP 2006, LNCS 4067, pp. 452–476。transform function 与 simulation object 的说法依据同一组作者的
  HotOS 2003 论文与技术报告概述。
- **[OTP-RH]** Erlang/OTP 文档, System Documentation, "Release Handling"。erlang.org/doc/system/release_handling。
- **[OTP-Appup]** Erlang/OTP 文档, System Documentation, "Appup Cookbook"。erlang.org/doc/system/appup_cookbook。
- **[Arm03]** Joe Armstrong. Making reliable distributed systems in the presence of software errors.
  博士论文, Royal Institute of Technology (KTH), Stockholm, 2003。
- **[DdJV04]** Eelco Dolstra, Merijn de Jonge, Eelco Visser. Nix: A safe and policy-free system for software
  deployment. LISA 2004, pp. 79–92。(USENIX 的一处记录只列前两位作者,论文正文为三位。)
- **[DL08]** Eelco Dolstra, Andres Löh. NixOS: A purely functional Linux distribution. ICFP 2008。
- **[DLP10]** Eelco Dolstra, Andres Löh, Nicolas Pierron. NixOS: A purely functional Linux distribution.
  Journal of Functional Programming 20(5–6):577–615, 2010。

未核实条目:1 条([GJB96] 第一作者的名字部分)。另有若干条只核实了书目信息、内容转述依据摘要或
二手材料,已逐条注明。
