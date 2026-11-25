# 会话类型、共享会话、优先级与无死锁、取消、类型状态

对照特征:F2(守卫 `¬held`)、F5(共享服务)、F6(父子 fiber)、F7(divert、失败、重置)。

**先说结论。**

- 提供者与依赖者之间的关系,**生命周期的骨架**像一个共享会话(获取、使用、释放,拥有者等全部客户释放后才回收),
  **交互内容**不像:依赖者对服务状态的操作没有协议顺序,也不是与提供者交换消息,提供者 fiber 根本不参与。
  所以会话类型能借给演算的主要是"谁持有引用、谁负责回收、谁等谁"这一层,不是协议层。
- 与 F2 对应最精确的不是经典会话类型,而是 Jacobs 与 Balzer 的带引用计数的高阶锁:
  "唯一的拥有者引用,零或多个客户引用,拥有者先等所有客户放下引用再回收"几乎逐字就是
  `wf_bind`、`wf_uprov`、`wf_uprov_unique` 加上 `withdraw_waits`。
- 卸载无死锁(`Progress.quiet_settled`)的证明结构与优先级类型(Kobayashi、Padovani、Dardha 与 Gay)相同:
  等待只指向优先级严格更高(这里是秩更高)的一方,沿良基序归纳。但优先级在组件上而不在动作上,也没有类型系统,
  所以是近似对应。演算能避开共享会话里的获取死锁,是因为获取(`L-Begin`)一次取齐全部依赖且不阻塞。
- fiber 的四态生命周期**不适合**作为用户代码的类型状态:状态由运行时和别的 fiber 异步改变,持有句柄的一方
  没有唯一权限。适合做类型状态检查的是插件启动程序里的**提供状态**(哪些键已经 provide),见课题 B。

## 1. 领域概览

### 1.1 二元与多方会话类型

会话类型把一条通道上的通信协议写成类型:发送、接收、选择、分支、结束。经典的二元会话类型始于 Honda(1993),
Honda、Vasconcelos、Kubo(1998)给出了带会话建立原语的语言与类型纪律。端点是线性的:一个端点恰好由一方持有,
协议走完之前不能丢弃。多方会话类型(Honda、Yoshida、Carbone 2008)用全局类型描述 n 方交互,投影到各方的局部类型,
保证通信安全、会话保真与进展。参与者数在会话开始时固定。

与本演算有关的只有两点:线性端点"不能丢、必须走完",以及"一方必须等对端结束才能回收资源"(`close`/`wait`)。

### 1.2 线性逻辑会话类型与拓扑无环

Caires 与 Pfenning(2010)把会话类型解释为直觉主义线性逻辑的命题,Wadler(2012)给出经典线性逻辑版本 CP 与
函数式语言 GV。在这一路线里,无死锁来自切消:进程之间的连接结构必须是树(两个进程至多共享一条通道,
连接图无环)。代价是表达力:环形拓扑(如哲学家就餐)写不出来。

### 1.3 共享会话

线性端点不能有多个客户。Caires 与 Pfenning 的复制通道允许多个客户,但每个客户得到的是一份独立的副本,不共享状态。

- **manifest sharing**(Balzer、Pfenning 2017):类型分为线性层和共享层,用模态连接。客户对共享进程执行
  `acquire` 得到线性会话,用完 `release` 回到共享层;要求释放时的类型与获取时一致(equi-synchronizing)。
  保留会话保真,但**失去无死锁**:多个客户争用共享进程可能循环等待。
- **共享会话的无死锁**(Balzer、Toninho、Pfenning 2019):在类型中跟踪获取共享进程的顺序,排除获取与同步点之间的
  循环依赖,恢复无死锁。
- **分阶段**(Sano、Balzer、Pfenning 2021):放宽 equi-synchronizing 为 subsynchronizing,让客户类型中可见
  共享进程所处的阶段。
- **共享可变状态的命题即类型**(Rocha、Caires 2021;CLASS,Rocha、Caires 2023):在线性逻辑会话语言中保守地加入
  共享的(仿射的)可变状态,无死锁仍由切消得出。

### 1.4 优先级与无死锁

另一条路线不限制拓扑,而是给通道动作标优先级(层级):一个进程只能在完成更低优先级的义务之后才阻塞在更高优先级的动作上,
于是全局最低优先级的待决动作总能执行。

- Kobayashi(2006):π 演算上带层级的无死锁类型系统,支持类型推断。
- Padovani(2014):线性 π 演算上的无死锁与无锁(lock freedom)两种精化,后者要求每个待决的线性通信最终完成。
- Dardha、Gay(2018):把 Kobayashi 式优先级引入经典线性逻辑(PCLL),允许环形证明结构,仍保证无死锁。
- Kokke、Dardha(2023,LMCS):Priority GV,把通道创建与线程派生分开,用优先级恢复环形结构下的无死锁。

### 1.5 带引用计数的锁、无泄漏与机械化

- **高阶锁**(Jacobs、Balzer 2023):锁引用分为唯一的拥有者引用和任意多个客户引用;客户可以放下引用,
  拥有者要回收锁,必须先等所有客户放下引用,再取回锁中的内容。线程与锁之间的引用图无环保证无死锁与无内存泄漏;
  扩展 lock++ 在锁组内用可动态变化的局部锁序允许环。证明在 Coq 中机械化。
- **连通图**(Jacobs、Balzer、Krebbers 2022):把"实体之间的引用图保持无环"抽成分离逻辑中的局部图变换规则,
  配上一条沿无环图的"等待归纳"原理,在 Coq 中得到高阶会话类型语言的无死锁与无泄漏证明。
- **Actris**(Hinrichsen、Bengtson、Krebbers 2020)把会话式协议放进 Iris 分离逻辑;**LinearActris**(Jacobs、
  Hinrichsen、Krebbers 2024)让线性性直接给出无死锁与无泄漏。

### 1.6 取消与故障

- **仿射会话**(Mostrous、Vasconcelos 2018):允许弱化,即会话可以被显式取消,对端得到通知,进展性不受影响。
- **异常与取消**(Fowler、Lindley、Morris、Decova 2019):在异步会话类型的函数式语言(Links 的 EGV 核心)中加入
  异常处理与端点取消;核心演算保持性、进展、无死锁、合流、终止都成立。按我们的理解(未对照全文核实细节):
  取消一个端点后,对端在其上接收时引发异常,运行时负责回收被取消端点及其缓冲中携带的端点。
- **故障下的多方会话**:MAGπ(Le Brun、Dardha 2023)处理消息丢失、节点崩溃等非拜占庭故障;
  Viering、Hu、Eugster、Ziarek(2021)把故障检测作为事件纳入多方会话,证明多会话下的全局进展。

### 1.7 动态参与者

- 动态多角色会话类型(Deniélou、Yoshida 2011):全局类型描述"角色"(一类参与者),参与者可以在会话进行中加入、离开。
- 显式连接动作(Hu、Yoshida 2017):在多方会话类型中加入 `connect`/`disconnect`,描述可选参与者与动态加入。
- EnsembleS(Harvey、Fowler、Dardha、Gay 2021):带会话类型的 actor 语言,支持运行时替换 actor 的自适应。

### 1.8 类型状态

类型状态(typestate,Strom、Yemini 1986)给类型加上"当前状态",每个操作有前置状态和后置状态,编译期跟踪,
排除"语法合法但语义未定义"的调用序列。核心困难是别名:多个引用指向同一对象时,谁能改变状态。

- DeLine、Fähndrich(2004,Fugue):借 Vault 的线性类型处理别名,给 .NET 对象做模块化的类型状态检查。
- Bierhoff、Aldrich(2007,Plural):访问权限(unique、full、share、pure、immutable)把别名信息与类型状态结合;
  `share`/`pure` 引用只能依赖"状态保证",不能假定别人不改状态。
- 类型状态导向编程(Aldrich、Sunshine、Saini、Sparks 2009,Plaid);其形式基础与渐进版本 GFT
  (Garcia、Tanter、Wolff、Aldrich 2014),在静态信息不足处插入运行时检查。
- Obsidian(Coblenz 等 2020):智能合约语言,类型状态管对象状态,线性的"资产"类型保证资产不被意外丢失,
  核心演算 Silica 证明了可靠性与资产保留。

## 2. 对照

### 2.1 对照表

对应程度:**精确**(定义或定理一一对应,只差记号)、**近似**(结构相同,有实质差别)、**形似**(只有类比)。

| 领域概念 | 演算中的规则、定义或定理 | 程度 | 说明 |
|---|---|---|---|
| 锁的唯一拥有者引用 + 客户引用(Jacobs、Balzer 的 Principle 5) | `WF` 的 `wf_bind`(每个绑定的 owner 已安装且累加器中有对应 `UProv`)、`wf_uprov`、`wf_uprov_unique`;客户引用是依赖者 ω 中的 pid(`wf_view`) | 精确 | `UProv k pid` 就是拥有者引用,ω 的条目就是客户引用 |
| 拥有者先等全部客户放下引用,再回收 | `L-Undo` 的 `UProv` 情形;`Ordering.withdraw_waits`、`withdraw_blocked` | 精确 | 演算更强一步:`unload_waits`、`unload_blocked` 让拥有者在任何撤销之前就等,见 2.3 |
| 会话中 `acquire` 共享进程 | `L-Begin`:`target n = ω ≠ ⊥` 时按 ω 开始加载;`Ordering.begin_requires_deps` | 近似 | 一次取齐全部依赖,且不阻塞:取不到就停在 `Inactive None`,不会持有一部分再等另一部分 |
| `release` 回到共享层 | 依赖者走完卸载(`L-Unloaded`),不再 `installed`,`resolves` 为假 | 近似 | 释放不是依赖者自愿的:提供者离开 Active 后依赖者的 target 变为 ⊥,被迫离开(`leave_when_changed`、`divert_when_changed`) |
| 会话内的一次交互 | `L-Step` 的 `Op k` 对绑定状态执行 `run` | 形似 | 没有协议顺序(任何时刻可执行 `Opₖ` 中任何操作),不是消息,提供者 fiber 不参与;更像对共享内存单元的一次原子读改写 |
| equi-synchronizing(释放时类型不变) | 已安装期间 ω 不变(`Ordering.fiber_step`);provision 身份由 pid 固定(`provider_outlives`) | 形似 | 演算固定的是"连到哪个 provision",不是协议状态 |
| 分阶段的共享会话(Sano 等) | `visible` 只计 Active 的提供者:提供者进入 Unloading 后对新解析不可见,已解析的依赖者仍可读写 | 近似 | 提供者生命期分为"可获取"与"只服务老客户"两阶段,但不在任何类型中可见 |
| 无泄漏(leak freedom) | `WF` 的推论:卸载完毕的 fiber 没有子 fiber 也没有绑定;`Recovery.recovery_exact`、`Runtime.effect_exact` | 近似 | 会话类型说的是"内存/端点不泄漏",演算说的是"服务状态恢复到 ≃ 没装过",后者更强也更具体 |
| 优先级/层级(Kobayashi、Padovani、PCLL、PGV) | 组件秩 `rank`、`Above`;`Progress.Hwf`、`quiet_settled` 沿 `Above` 良基归纳;`Termination.Hrank` | 近似 | 证明结构相同,见 2.4。优先级在组件上不在动作上;没有类型系统,秩是链接期的全局检查 |
| 拓扑为树保证无死锁(CP、GV) | 父子 spawn 树(`wf_parent`、`SpawnOwn`) | 近似 | spawn 关系是树,但依赖关系是 DAG,无向意义下有环,见 2.4 |
| 获取顺序(Balzer、Toninho、Pfenning 2019) | 无 | — | 获取不阻塞,不需要获取顺序 |
| lock++ 的局部动态锁序 | 无;秩是全局静态的 | — | 演算目前不需要,见第 3 节 |
| 端点取消(Fowler 等;仿射会话) | `L-Divert`;`Fail ξ` → `Unloading acc ω (Some ξ)` | 近似 | 演算的取消是**补偿**:按 LIFO 撤销已做的效应,不是丢弃 |
| 取消向对端传播 | 提供者离开 Active → 依赖者 target 为 ⊥ → `L-Leave`/`L-Divert` | 近似 | 不抛异常,而是有序退出;提供者在依赖者撤销完之前一项也不撤(`unload_waits`) |
| 运行时回收被取消的端点 | `L-Remove`;撤销 `USpawn` | 形似 | |
| fork 出的子线程与父线程的会话(GV `fork`,结束时 `wait`) | `L-RetireChild` 置 `τₘ`,之后 `L-Undo` 的 `USpawn m` 情形等 `m ∉ dom F`;`Ordering.parent_waits_child` | 近似 | 父对子的"关闭请求 + 等待关闭"就是线性会话的 close/wait,但子 fiber 的退出由 target 驱动,不由协议驱动 |
| 线性端点不能交给第三方使用 | `SLInv`、DESIGN 差异 q、编排者义务 O1(只 dispose 根 fiber) | 近似 | 启动时 spawn 的子 fiber 被别人 dispose,相当于线性端点被第三方使用;合流因此排除它 |
| 动态多角色、显式连接 | 一个 provision 的依赖者集合随 `L-Begin` 与卸载变化;可选依赖的在场集(`Ext/Optional.v`) | 形似 | 所有依赖者扮演同一个"客户"角色,协议平凡 |
| 故障处理与外部恢复 | `Fail ξ` 停在 `Inactive (Some ξ)`,`O-Reset` 外部重置 | 形似 | 会话类型文献里没有"停住等外部重置"的对应,更接近监督树(见 concurrency.md) |
| 类型状态的状态机 | 生命周期自动机:`Ordering.fiber_step`(只沿 Inactive → Loading → Active → Unloading → Inactive 及 Loading → Unloading) | 近似 | 状态机一致,但改变状态的是运行时,不是持有句柄的代码,见 2.5 |
| 操作的前置状态 | `O-Reset` 要求 `Inactive (Some ξ)`;`O-Restart` 要求 Loading/Active 且 `τ = false`;`O-React` 要求 Active | 近似 | 这些是编排输入,发出时的静态知识随时可能过期 |
| 访问权限 unique/share/pure | 无 | — | 演算里没有"唯一持有 fiber 句柄"的一方 |
| 提供状态的类型状态 | `Provide k` 要求 `k ∈ p` 且 `B k` 未定义(否则 `EConflict`);`Op k` 对自己的键要求 owner 为 `n`(否则 `EUnresolved`);`Confluence.AllDoneProv`、`Total`、`Summary.TotalProv` | 近似,可做成精确 | 课题 B |
| Obsidian 的资产保留 | 累加器中每个 `UProv`、`USpawn` 都会在卸载中被处理(`WF` 推论) | 形似 | |

### 2.2 提供者与依赖者的交互是不是一个会话

分两层看。

**生命周期层是。** 把 provision `pid` 看成一个共享资源:

1. 提供者执行 `Provide k s`,创建资源并持有唯一的拥有者引用 `UProv k pid`。
2. 依赖者 `L-Begin` 时把 `pid` 写进 ω,得到客户引用。
3. 依赖者通过 `Op k` 读写资源。
4. 依赖者卸载完毕,客户引用消失。
5. 提供者撤销 `UProv`,资源回收。

第 2 步到第 4 步是"获取—使用—释放",第 5 步要求所有客户都已释放。这正是 manifest sharing 的
acquire/release 加上 Jacobs、Balzer 的拥有者回收纪律。

**交互层不是。** 会话类型的核心是协议:双方按类型规定的顺序交换消息。演算里:

- 依赖者对服务状态执行哪个操作、按什么顺序,没有任何约束;`Opₖ` 中的任何操作随时可做。
- 依赖者不和提供者通信。`run` 由依赖者自己在绑定上执行,提供者 fiber 此时可能在做别的事,甚至已在 Unloading。
- 服务状态是被动的数据,不是一个进程。

因此,硬要写成会话类型,依赖者一侧的类型只能是"获取之后,反复在所有操作中任选一个,最后释放",
协议部分是平凡的。会话类型的保真性(session fidelity)在这里没有内容。演算里关于共享状态的真正难点,
即别的 fiber 的操作穿插进来之后能否精确撤销(`RevertIndep`、`Recovery.v`)、两次调度能否合流(`HCom`、
`CoPair`、`ServiceSeq.v`),都是关于操作语义的代数性质,会话类型不涉及。

比会话更贴切的模型是"带拥有者的共享内存单元":每次 `Op` 是一次原子的获取—读改写—释放(DESIGN D6 已要求操作逻辑原子),
所以不需要互斥锁,只需要引用纪律。

### 2.3 守卫 `¬held` 与"会话未关不能回收"

线性会话类型中的"不能回收"有两个不同来源,要分开:

- **线性性**:持有端点的一方不能丢弃它,必须把协议走完。这约束的是**客户**。
- **close/wait**:提供方要结束,必须等对端发出关闭。这约束的是**提供方**。

`¬held` 对应的是后者,而且是多客户的版本:拥有者要等**所有**客户引用消失。这与 Jacobs、Balzer 的锁一致:
客户可以随时放下引用(不必走完协议),拥有者回收前必须等全部客户放下。`withdraw_waits` 就是这条纪律在
`UProv` 一项上的陈述。

演算比锁的纪律多两点:

1. **守卫作用于整个卸载,不只是回收那一项**(`unload_waits`、`unload_blocked`,DESIGN 差异 g)。锁的拥有者
   在等客户之前可以先做别的事;演算的提供者在任何依赖者还解析着它的 provision 时,连 provide 之后注册的
   效应也不撤销。依赖者因此在提供者的全部效应都在时完成卸载。会话类型文献里没有这条"整体延迟拆除"的纪律,
   最接近的是嵌套的 close/wait:提供者先关闭对外服务、再拆内部。
2. **客户的释放由运行时强制**。锁和会话里,客户放下引用是客户自己的动作,活性要靠客户的类型(必须最终 release)
   保证。演算里依赖者是否离开由 target 决定:提供者一离开 Active,`visible` 变为 `None`,依赖者的 target 变为 ⊥,
   于是 `L-Leave`/`L-Divert` 可用。这把活性义务从"每个客户的代码"移到了"运行时规则",是演算能证明无死锁而
   不需要类型系统的原因之一。

反方向,线性性约束客户的那一半在演算中由构造满足:依赖者不能"丢掉"ω 中的引用,ω 在已安装期间不变,
只能随卸载整体消失。

### 2.4 卸载无死锁与优先级类型

**演算中的论证**(`Progress.quiet_settled`,RULES 6.5)。可能等待的只有两处:

- Unloading 的 `n` 因 `held` 而停:有 `m ≠ n` 解析 `n` 的某个 provision,于是 `m` 的组件声明了 `n` 的组件提供的键,
  即 `Above (c n) (c m)`。
- `n` 停在 `USpawn m`:子 fiber `m` 尚未移除,`Spawns (c n) (c m)`,也有 `Above (c n) (c m)`。

所以等待关系包含在 `Above` 中,而 `Above` 良基(`Hwf`)。证明沿 `Above` 从上往下归纳:被等待的 `m` 秩更高,
由归纳它不可能也停在 Unloading;它又不可能是 Loading(总能走或放弃)或 Active(提供者已离开 Active,它的 target
已变,可以离开);所以它不是已安装的,矛盾。终止(`Termination.termination`)用同一个秩把度量分层成字典序向量,
关键引理是一个 fiber 的步骤不影响秩不高于它的 fiber(`lstep_effects`、`mu_other`)。

**与优先级类型的对应。** Kobayashi、Padovani 的论证是:每个动作有优先级;一个进程只在优先级更低的义务都完成后
才阻塞;于是全局优先级最低的待决动作没有被任何东西挡住,总能执行。取优先级为 −rank,演算的论证就是同一形状:
等待只指向优先级严格更低(秩更高)的一方,沿良基序归纳。

差别是实质性的,所以记为**近似**:

| | 优先级类型 | 演算 |
|---|---|---|
| 优先级挂在哪里 | 通道上的每个动作 | 组件(所有 fiber 共享组件的秩) |
| 如何检查 | 局部的类型规则,可组合 | 链接期对整张组件表检查 `Above` 无环,全局 |
| 被等待方为何最终响应 | 它自己的类型要求它执行对偶动作 | 运行时规则:target 变化迫使它离开 |
| 结论 | 无死锁或无锁 | 无死锁(`progress`)且终止(`termination`) |

**为什么拓扑类的方法不够。** CP/GV 要求连接结构是树。spawn 关系是树,但依赖关系不是:两个依赖者 `m₁`、`m₂`
都依赖提供者 `A` 和 `B` 时,无向图 `A–m₁–B–m₂–A` 成环。Jacobs、Balzer 的基本演算同样要求线程—锁引用图(无向)无环,
也会拒绝这种菱形。演算能接受菱形,靠的是秩(一种全局锁序),对应 PCLL/PGV 的优先级或 lock++ 的锁序,而不是拓扑。

**为什么没有共享会话里的获取死锁。** manifest sharing 的死锁来自"持有一个共享进程再阻塞地获取另一个"。
演算的 `L-Begin` 一次解析全部依赖(`target` 要求每个依赖都 visible),取不到就不开始,也不阻塞;加载中途依赖变化
则放弃(`L-Divert`)。依赖者从不等提供者,只有提供者等依赖者、父等子。Balzer、Toninho、Pfenning 的获取顺序因此
没有对应物,也不需要。代价是表达力:依赖者不能"先拿到 A,用 A 的结果决定要不要 B"(可选依赖扩展用"在场集变化即重载"
处理这一类,见 EXTENSIONS 1.2)。

### 2.5 共享服务对线性会话类型的障碍,manifest sharing 能否解决

**障碍。** F5 的共享服务有三个特征,每个都与线性会话冲突:

1. **多客户**:一个 provision 被任意多个依赖者同时解析。线性端点只有一个持有者。
2. **共享可变状态**:所有依赖者读写同一个 `s`,彼此看得见对方的写。复制通道(`!`)给每个客户一份独立副本,不共享状态。
3. **客户集合动态变化**:依赖者随时加入(`L-Begin`)和离开。多方会话的参与者数在开始时固定。

**manifest sharing 能解决前两点的类型问题。** 把服务写成共享进程,每次 `Op` 是 `acquire`、一次操作、`release`;
释放时类型不变,equi-synchronizing 自然满足。第三点在 manifest sharing 中也不是问题:共享通道本来就允许任意多个
客户随时获取。这样写出的系统有会话保真;由于每次获取只做一个原子操作、不嵌套获取,也不会有获取死锁。

**但它解决的不是演算关心的问题。**

- 会话保真在这里没有内容(2.2)。
- 演算关于共享服务的定理全部是语义的:恢复精确性需要撤销独立(`RevertIndep`、`Recovery.Hind`),合流需要
  可交换(`HCom`、`HRI`),且只针对 `CoPair`。manifest sharing 不说两个客户的操作交换后结果如何。
- manifest sharing 的共享进程是持久的,理论中不回收;演算的 provision 会被撤回,而且撤回的纪律(`¬held`)
  恰恰是这一节最有内容的部分。这一点 Jacobs、Balzer 的锁做了,manifest sharing 没做。
- Rocha、Caires 的共享状态单元最接近"多个客户读写同一个 `s`",但同样不涉及撤销与可交换性。

结论:manifest sharing 可以给 F5 一个类型上的定位("共享层的服务,一次获取一个原子操作"),但不提供可借用的元理论。
真正可借用的是 Jacobs、Balzer 的拥有者/客户引用纪律和 Coq 中的无泄漏证明方法。

### 2.6 fiber 的四态生命周期能否作为类型状态静态检查

**状态机本身已经验证过了**:`Ordering.fiber_step` 证明每一步只沿规定的边改变生命周期。问题是谁来做静态检查。

- **插件代码不改变自己的生命周期状态。** 启动程序 `Prog` 只能 `Op`、`Provide`、`Spawn`、`Done`、`Fail`,
  生命周期迁移全部由 `L-*` 规则完成。类型状态检查的对象(调用者对一个对象执行状态相关的操作)在插件代码里不存在。
- **编排者发出的命令有前置状态**(`O-Reset`、`O-Restart`、`O-React`)。但状态由运行时和别的 fiber 异步改变:
  编排者发出 `reset` 时以为 fiber 失败了,下一刻它可能已被重置或被移除。经典类型状态要求持有者对状态有唯一控制
  (Bierhoff、Aldrich 的 unique/full 权限);这里编排者最多只有 `share`/`pure` 权限,只能依赖"状态保证",
  而生命周期没有这种保证(任何状态都可能因 target 变化而离开)。最终只能退回运行时检查,也就是 GFT 式的渐进类型状态,
  而演算的规则本来就在前提不满足时返回 `None`,已经是运行时检查。
- **运行时实现内部**(Cordis 的 `fiber.ts`)可以用类型状态让"Unloading 的 fiber 不会被 `L-Begin`"这类错误在编译期暴露。
  这是有用的工程手段,但它检查的是运行时自己,性质已由 `fiber_step` 和 `step` 的定义给出,不是新保证。

所以,四态生命周期**不适合**作为面向插件或编排者的类型状态。插件代码里真正状态相关的是**提供状态**:
`Provide k` 只能做一次、只能对 `k ∈ p` 做;对自己提供的键执行 `Op` 必须在 `Provide` 之后;每条到 `Done` 的路径都要提供全部 `p`。
这是一个标准的类型状态(每个键两态:未提供、已提供,单向迁移,终态要求全部已提供),见课题 B。
同理,启动时 spawn 的子 fiber 句柄是一个"线性能力",不应交给别人 dispose,见课题 C。

## 3. 差异

**演算有,这些领域没有或处理得不好的:**

1. **整体延迟拆除**:提供者在依赖者离开之前一项效应也不撤(`unload_waits`)。锁与会话只约束回收那一个资源。
2. **取消即补偿**:`L-Divert` 与 `Fail` 之后按 LIFO 撤销已做的效应,恢复到 ≃ 没做过(`recovery_exact`)。
   Fowler 等的取消与仿射会话是丢弃加通知,不回滚对共享状态的修改。
3. **由运行时强制的释放**:客户何时释放由 target 决定,不靠客户代码的类型义务。
4. **共享状态上的代数义务**:撤销独立、可交换,以及按"可能相遇"(`CoPair`)放宽。会话类型不谈并发操作的交换性。
5. **合流**:不同调度的终态一致(`dynamic_confluence`、`static_assembly`)。Fowler 等的核心演算也有合流,但那是
   λ 演算意义上的,不涉及共享状态与调度。
6. **获取不阻塞**:一次解析全部依赖,取不到就不开始。
7. **一个秩同时管依赖和 spawn**(`Above` 包含两者),一次归纳同时处理"等依赖者"与"等子 fiber"。
8. **失败停住、外部重置**(`Inactive (Some ξ)`、`O-Reset`)。

**这些领域有,演算没有的:**

1. **协议**:服务操作没有顺序约束。若某个服务确有协议(例如先 `open` 后 `write`),演算不检查,
   只能由服务在 `run` 中返回 `None` 让调用者失败。
2. **引用的传递**:会话类型可以把通道作为消息传出去(高阶)。演算的 ω 不能传给别的 fiber,依赖关系完全静态。
3. **局部、可组合的检查**:优先级类型逐个进程检查。演算的秩是链接期对整张组件表的全局检查(EDSL.md 第 5 节)。
4. **动态锁序**:lock++ 允许锁组内的顺序动态变化。演算要求 `Above` 全局无环,同一组件的多个 fiber 共享秩。
   目前没有看到 dsh 需要组件间互相依赖的实例,所以这不是缺陷,只是表达力边界。
5. **异常通知对端**:EGV 中对端会收到异常。演算的依赖者在提供者失败时只看到 target 变为 ⊥,不知道原因(课题 D)。
6. **真并行与异步缓冲**:会话类型处理异步消息队列;演算是交错语义,DESIGN D6 明确不考虑并行。

## 4. 候选课题

### 课题 A:等待关系与按秩无死锁的抽象

- **目标**:把 `Progress.quiet_settled` 中沿 `Above` 的归纳抽成一条与具体规则无关的引理,让"卸载无死锁"
  成为两条局部条件的推论:(1)等待只指向秩更高的 fiber;(2)没被挡住的未稳定 fiber 总能走。这样与优先级类型的
  对应从"证明形状相同"变成"同一条引理的实例",并把拥有者/客户引用的结构(2.3)显式写出。
- **做法**:
  1. 定义 `WaitsOn γ n m`:`n` 处于 `Unloading (u :: acc) _ _`,且 `m ≠ n` 解析 `n` 的累加器中某个 `UProv` 的 pid,
     或者 `u = USpawn m` 且 `m ∈ dom F`。
  2. 证明 `waits_above`:`WF γ → Inv2 γ → WaitsOn γ n m → Above (c n) (c m)`。材料都在 `Progress.v` 的 `NoRelied`、
     `wf_bind`、`SpawnProv` 里。
  3. 证明 `blocked_waits`:Unloading 且累加器非空的 `n` 若 `L-Undo`、`L-RetireChild` 都不可用,则存在 `m` 使 `WaitsOn γ n m`。
  4. 证明通用引理 `rank_progress`:等待关系包含于一个良基关系,且被等待者不能停在 Loading/Active,则不存在停住的 Unloading fiber。
     用它重证 `quiet_settled`,并看 `Ext/OptProgress.v` 的 `xquiet_settled` 能否复用(`XAbove`)。
  5. 顺带把 Principle 5 写成 `WF` 的推论:每个绑定恰有一个拥有者引用(`wf_bind` 加 `wf_uprov_unique`),
     客户引用都来自 `Above` 更高的 fiber。
- **预期产出**:一个新的 Rocq 文件(例如 `theories/Waits.v`)与上述引理;对照表中"优先级"一行可标为"结构精确";
  等待关系可直接作为课题 E 中连通图的边。
- **风险**:主要是重构,新的结论不多;若 `OptProgress` 的论证经过的转换与核心不同,复用收益有限。
- **工作量**:小。

### 课题 B:提供状态的类型状态检查

- **目标**:用一个归纳判断静态排除插件自身造成的三类问题:重复 provide 或 provide 不在 `p` 中的键(`EConflict`);
  在 provide 之前对自己的键执行 `Op`(`EUnresolved`);某条到 `Done` 的路径没有提供全部 `p`(`Total` 不成立)。
  把 `Confluence.Total`、`Summary.TotalProv` 从假设变成检查结果。
- **做法**:
  1. 定义 `ProvOK d p : list K → Prog → Prop`,参数 `S` 是已提供的键:
     `PDone` 要求 `p ⊆ S`;`PFail` 总成立;`POp k a κ` 要求 `k ∈ d ∨ k ∈ S`,且对所有结果 `o` 有 `ProvOK S (κ o)`;
     `PProvide k s P` 要求 `k ∈ p`、`k ∉ S`,且 `ProvOK (k :: S) P`;`PSpawn c P` 要求 `ProvOK S P`。
  2. `provok_total`:`ProvOK d p [] body → ∀ k ∈ p. AllDoneProv k body`,于是 `Total` 由检查推出。
  3. `provok_no_self_fail`:引入不变式"Loading 的 fiber 的剩余程序满足 `ProvOK S'`,`S'` 是其累加器中 `UProv` 的键集",
     证明它被 `step` 保持;由此 `L-Step` 不会因 `Provide` 产生 `EConflict`(别的 fiber 的冲突已由 `wf_disjoint` 排除),
     也不会因对自己的键 `Op` 产生 `EUnresolved`(依赖键的解析由 `wf_view`、`wf_view_keys` 保证)。
  4. 对齐 EDSL:EDSL.md 第 5 节的"完整提供"已靠枚举到 `Done` 的路径检查;补上前两项检查。OCaml 版可以按 4.2 节提到的
     indexed monad 把 `S` 放进类型参数,`provide` 改变它,这就是类型状态的标准编码。
- **预期产出**:Rocq 判断与两条定理;EDSL 分析器多两项检查;汇总定理中"完整提供"一项由检查给出。
- **风险**:`κ : Out → Prog` 可以无穷分支,判断对所有 `o` 量化,能在 Rocq 中陈述,但实际检查只能在 EDSL 层做,
  需要说明分析器对 `if/r`、`case/r` 的抽象是保守的。spawn 子组件的冲突与调度有关,不在本课题范围。
- **工作量**:小到中。

### 课题 C:启动时 spawn 的子 fiber 句柄作为线性能力

- **目标**:把 DESIGN 差异 q 的约定("启动时 spawn 的子 fiber 不单独 dispose")和编排者义务 O1 变成 EDSL 层的构造保证,
  使 `SLInv` 由构造成立。理论依据:父对子的关系是线性会话(请求关闭、等待关闭,`L-RetireChild`、`parent_waits_child`),
  第三方 dispose 子 fiber 等于使用别人的线性端点。
- **做法**:先核对 EDSL 当前的 `spawn` 是否返回可 dispose 的句柄。若返回,则把启动程序中的 `spawn` 改为不返回句柄
  (句柄只存在于父的累加器里,即 `USpawn m`),反应中动态创建的子 fiber(`O-React`)返回可 dispose 的仿射句柄。
  在 Rocq 一侧,陈述"启动程序中不存在 dispose 子 fiber 的原语"时 `SLInv` 在生命周期步与根上的编排步下保持
  (已有 `sl_step`、`sl_insert`、`sl_dispose` 等,主要是把前提对齐)。
- **预期产出**:EDSL 的接口调整与一条说明性定理;审计中"直接 dispose 启动时子 fiber"的写法在新 EDSL 中写不出来。
- **风险**:dsh 现有代码大量直接 dispose 子 fiber(差异 q 中的例子),多数在事件处理器里,迁移时要逐个确认它们属于反应。
  TypeScript 无法真正强制线性,只能靠不暴露句柄。
- **工作量**:小。

### 课题 D:取消原因的传播(为什么没运行)

- **目标**:借 EGV"取消向对端传播并携带原因"的思路,给稳定状态中每个"不该运行"的 fiber 一条有限的归因链,
  回答 dsh 用户最常见的问题:插件为什么停在 PENDING。目前依赖者在提供者失败后只是 target 变为 ⊥,原因丢失(第 3 节第 5 条)。
- **做法**:在 `settled` 状态中,对 `Inactive None`、`target n = ⊥`、未退役的 `n`,存在某个依赖键 `k` 不 visible。
  由 `WF`(Inactive 的 fiber 没有绑定)与 `settled`,`B k` 未定义,于是只有四种情况:没有任何 fiber 的 `p` 含 `k`;
  提供 `k` 的 fiber 失败(`Inactive (Some ξ)`);它已退役;它自己也是 `Inactive None` 且 target 为 ⊥(秩更低,递归);
  或它 Active 却没提供 `k`(违反 `Total`)。沿 `Above` 归纳得到 `blame_chain`:链有限,终点是前四种之一(在 `Total` 下排除第五种)。
  可选地给 `Inactive` 加一个只供诊断的鬼字段,不影响规则。
- **预期产出**:定理 `blame_chain`(与 `quiet_settled` 同一处归纳);Cordis 或 EDSL 运行时据此输出"x 未运行,因为 y 提供的 k 失败"这类诊断。
- **风险**:定理本身不难,价值在于工程上真的用起来;若 Cordis 已有类似日志,收益只在"保证链完整"。
- **工作量**:小到中。

### 课题 E:在分离逻辑中用连通图重证无死锁与无泄漏

- **目标**:把演算的守卫纪律放到 Jacobs、Balzer、Krebbers 的连通图方法或 LinearActris 中,对一个更接近真实运行时的
  λ 演算模型(带 `await`、带堆)证明无死锁与无泄漏,作为 DESIGN D6"精化"一节和 verification.md 的衔接。
- **做法**:顶点取 fiber 与 provision,边取 ω 中的客户引用、累加器中的拥有者引用与 `USpawn`,标签取生命周期状态。
  证明每条规则是保持"无环"的局部图变换。难点:连通图要求的是无向无环,演算的依赖图允许菱形(2.4),需要引入秩作为
  lock++ 式的序,或修改等待归纳原理使其只依赖有向的 `Above`。
- **预期产出**:一份 Iris/Coq 证明,说明真实运行时(而不只是演算)无死锁、拥有者回收时没有残留客户引用。
- **风险**:大。方法本身要扩展(无向无环到按秩);与本仓库的 Rocq 基础设施(不依赖 Iris)不同,需要引入新的依赖。
  在课题 A 之后做,能复用其等待关系。
- **工作量**:大。

**不建议做的。** 给服务操作加会话类型协议(2.5):演算的服务没有协议,共享服务的难点是撤销与交换,不是协议顺序。
把四态生命周期做成面向插件或编排者的类型状态(2.6):没有唯一持有者,最后仍是运行时检查。

## 5. 参考文献

均经检索核对作者、题目、出处、年份。"内容细节未对照全文"表示书目已核实,但正文中引述的个别技术细节凭摘要或记忆,未逐页核对。

1. Kohei Honda. Types for Dyadic Interaction. CONCUR 1993, LNCS 715, pp. 509–523. doi:10.1007/3-540-57208-2_35。
2. Kohei Honda, Vasco T. Vasconcelos, Makoto Kubo. Language Primitives and Type Discipline for Structured
   Communication-Based Programming. ESOP 1998, LNCS 1381, pp. 122–138. doi:10.1007/BFb0053567。
3. Kohei Honda, Nobuko Yoshida, Marco Carbone. Multiparty Asynchronous Session Types. POPL 2008, pp. 273–284.
   doi:10.1145/1328897.1328472。
4. Luís Caires, Frank Pfenning. Session Types as Intuitionistic Linear Propositions. CONCUR 2010, LNCS 6269, pp. 222–236.
   doi:10.1007/978-3-642-15375-4_16。
5. Philip Wadler. Propositions as Sessions. ICFP 2012, pp. 273–286. doi:10.1145/2364527.2364568(期刊版 JFP 24(2–3), 2014)。
6. Stephanie Balzer, Frank Pfenning. Manifest Sharing with Session Types. PACMPL 1(ICFP), Article 37, 2017.
   doi:10.1145/3110281。
7. Stephanie Balzer, Bernardo Toninho, Frank Pfenning. Manifest Deadlock-Freedom for Shared Session Types.
   ESOP 2019, LNCS 11423, pp. 611–639. doi:10.1007/978-3-030-17184-1_22。
8. Chuta Sano, Stephanie Balzer, Frank Pfenning. Manifestly Phased Communication via Shared Session Types.
   COORDINATION 2021, LNCS 12717, pp. 23–40. doi:10.1007/978-3-030-78142-2_2。
9. Pedro Rocha, Luís Caires. Propositions-as-Types and Shared State. PACMPL 5(ICFP), 2021. doi:10.1145/3473584。
10. Pedro Rocha, Luís Caires. Safe Session-Based Concurrency with Shared Linear State. ESOP 2023, LNCS 13990, pp. 421–450.
    doi:10.1007/978-3-031-30044-8_16。
11. Naoki Kobayashi. A New Type System for Deadlock-Free Processes. CONCUR 2006, LNCS 4137, pp. 233–247.
    doi:10.1007/11817949_16。内容细节未对照全文。
12. Luca Padovani. Deadlock and Lock Freedom in the Linear π-Calculus. CSL-LICS 2014. doi:10.1145/2603088.2603116。
    内容细节未对照全文。
13. Ornela Dardha, Simon J. Gay. A New Linear Logic for Deadlock-Free Session-Typed Processes. FoSSaCS 2018,
    LNCS 10803, pp. 91–109. doi:10.1007/978-3-319-89366-2_5。
14. Wen Kokke, Ornela Dardha. Prioritise the Best Variation. Logical Methods in Computer Science 19(4), 2023
    (arXiv:2103.14466)。其会议版本(FORTE 2021)未核实。
15. Jules Jacobs, Stephanie Balzer. Higher-Order Leak and Deadlock Free Locks. PACMPL 7(POPL), Article 36, 2023.
    doi:10.1145/3571229。拥有者/客户引用与"拥有者先等所有客户放下引用"已对照原文第 2 节。
16. Jules Jacobs, Stephanie Balzer, Robbert Krebbers. Connectivity Graphs: A Method for Proving Deadlock Freedom
    Based on Separation Logic. PACMPL 6(POPL), 2022. doi:10.1145/3498662。
17. Jonas Kastberg Hinrichsen, Jesper Bengtson, Robbert Krebbers. Actris: Session-Type Based Reasoning in Separation Logic.
    PACMPL 4(POPL), Article 6, 2020. doi:10.1145/3371074。
18. Jules Jacobs, Jonas Kastberg Hinrichsen, Robbert Krebbers. Deadlock-Free Separation Logic: Linearity Yields Progress
    for Dependent Higher-Order Message Passing. PACMPL 8(POPL), Article 47, 2024. doi:10.1145/3632889。
19. Dimitris Mostrous, Vasco T. Vasconcelos. Affine Sessions. Logical Methods in Computer Science 14(4:14), 2018
    (扩展摘要见 COORDINATION 2014)。
20. Simon Fowler, Sam Lindley, J. Garrett Morris, Sára Decova. Exceptional Asynchronous Session Types: Session Types
    without Tiers. PACMPL 3(POPL), Article 28, 2019. doi:10.1145/3290341。取消语义的细节未对照全文。
21. Matthew Alan Le Brun, Ornela Dardha. MAGπ: Types for Failure-Prone Communication. ESOP 2023.
    doi:10.1007/978-3-031-30044-8_14。
22. Malte Viering, Raymond Hu, Patrick Eugster, Lukasz Ziarek. A Multiparty Session Typing Discipline for Fault-Tolerant
    Event-Driven Distributed Programming. PACMPL 5(OOPSLA), Article 124, 2021. doi:10.1145/3485501。
23. Pierre-Malo Deniélou, Nobuko Yoshida. Dynamic Multirole Session Types. POPL 2011, pp. 435–446.
    doi:10.1145/1926385.1926435。
24. Raymond Hu, Nobuko Yoshida. Explicit Connection Actions in Multiparty Session Types. FASE 2017, LNCS 10202,
    pp. 116–133. doi:10.1007/978-3-662-54494-5_7。
25. Paul Harvey, Simon Fowler, Ornela Dardha, Simon J. Gay. Multiparty Session Types for Safe Runtime Adaptation in an
    Actor Language. ECOOP 2021, LIPIcs. doi:10.4230/LIPIcs.ECOOP.2021.10。
26. Robert E. Strom, Shaula Yemini. Typestate: A Programming Language Concept for Enhancing Software Reliability.
    IEEE Transactions on Software Engineering SE-12(1), pp. 157–171, 1986. doi:10.1109/TSE.1986.6312929。
27. Robert DeLine, Manuel Fähndrich. Typestates for Objects. ECOOP 2004, LNCS 3086, pp. 465–490.
    doi:10.1007/978-3-540-24851-4_21。
28. Kevin Bierhoff, Jonathan Aldrich. Modular Typestate Checking of Aliased Objects. OOPSLA 2007, pp. 301–320.
    doi:10.1145/1297027.1297050。
29. Jonathan Aldrich, Joshua Sunshine, Darpan Saini, Zachary Sparks. Typestate-Oriented Programming. Onward! 2009,
    pp. 1015–1022. doi:10.1145/1639950.1640073。
30. Ronald Garcia, Éric Tanter, Roger Wolff, Jonathan Aldrich. Foundations of Typestate-Oriented Programming.
    ACM TOPLAS 36(4), Article 12, 2014. doi:10.1145/2629609。
31. Michael Coblenz, Reed Oei, Tyler Etzel, Paulette Koronkevich, Miles Baker, Yannick Bloem, Brad A. Myers,
    Joshua Sunshine, Jonathan Aldrich. Obsidian: Typestate and Assets for Safer Blockchain Programming.
    ACM TOPLAS 42(3), Article 14, 2020. doi:10.1145/3417516。
