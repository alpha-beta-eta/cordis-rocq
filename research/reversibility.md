# 可逆计算与补偿

对照特征:F1(LIFO 撤销日志)、F2(守卫 `¬held`)、F7(divert、失败、重置)、F8(运行期效应)。
附带回答 [PLAN.md](PLAN.md) 列出的三个问题:守卫 `¬held` 是不是因果一致性的约束;`recovery_exact`
能否写成 Loop Lemma 或因果一致性定理;LIFO 撤销与因果序撤销差在哪里。

## 1. 领域概览

只写与本演算有关的部分。

### 1.1 因果一致可逆性(无控制)

- **RCCS**(Danos & Krivine, CONCUR 2004)。给 CCS 的每个线程配一个**记忆栈**,前向一步把这一步压栈,
  后向一步从栈顶弹出;两个线程的同步在双方的记忆里留下同一个标识,撤销同步时双方一起退。核心结果:
  Loop Lemma(每个前向步都有回到原状态的后向步,反之亦然)、Parabolic Lemma(任何路径都因果等价于
  "先后退、再前进"的路径)、因果一致性(共始的两条路径因果等价当且仅当共终)。"因果等价"指:只差在
  交换独立的步,以及插入或删去"一步加它的逆"。同组作者随后在 RCCS 上加了不可逆动作来表达事务提交
  (Transactions in RCCS, CONCUR 2005)。
- **CCSK**(Phillips & Ulidowski, FoSSaCS 2006 / JLAP 2007)。不用外置的记忆,而把已执行的前缀留在
  进程项里,打上**键**(key)作标记,"静态"地保留历史。同步的双方用同一个键,撤销时按键配对。
  RCCS 与 CCSK 的关系见 Lanese、Medić、Mezzina(Acta Informatica 2019)。
- **可逆 π**。Lanese、Mezzina、Stefani 的 ρπ(高阶 π,CONCUR 2010,期刊版 TCS 2016);Cristescu、
  Krivine、Varacca 的 Rπ(一阶 π,LICS 2013)。π 中名字的外泄带来"对象因果",独立关系比 CCS 复杂。
- **公理化**(Lanese、Phillips、Ulidowski, FoSSaCS 2020;期刊版 ACM TOCL 2024)。在"带独立关系的 LTS"
  (LTSI)上,假设每个转移都可逆(即 Loop Lemma),从三条公理推出上面这些性质:
  - SP(Square Property):共始且独立的两个转移 t、u,存在共终的 u′、t′ 补成方块;
  - BTI(后向转移相互独立):从同一状态出发的两个不同后向转移彼此独立;
  - WF(良基):没有无限的后向计算。

  由 BTI 与 SP 得 Parabolic Lemma(该文 Prop. 3.4),再得因果一致性。该文另提出两条更贴近非形式说法的性质:
  **因果安全**(CS:一个动作在它引起的动作都撤销之前不能撤销)与**因果活性**(CL:按任何与 CS
  相容的顺序都可以撤销,不必是前向顺序的逆),并指出因果一致性本身不等于 CS+CL。该文明确说,带控制的
  可逆性(不可逆动作、rollback 算子)不满足 Loop Lemma,通常先研究无控制的底层模型,再看控制机制改变了什么。
- **乱序可逆**(out-of-causal-order)。为建模生化反应,允许不按因果序撤销(Phillips、Ulidowski、Yuen,
  RC 2012;Danos & Krivine 的 CCS-R)。本演算不需要这一支,只用来说明"因果序"不是唯一选择。

### 1.2 受控可逆性

- **roll-π**(Lanese、Mezzina、Schmitt、Stefani, CONCUR 2011)。在 ρπ 上加 `roll γ` 原语:撤销键为 γ
  的那次通信,以及**因果上依赖它的全部动作**,别的不动。也就是说,rollback 的范围是一个因果闭包。
  我们对该文的理解是:它把 rollback 的正确性归结到底层无控制语义的因果一致性(rollback 的效果可由后向步达到);
  这一点凭记忆,未逐条对照原文。
- **croll-π**(Lanese、Lienhardt、Mezzina、Schmitt、Stefani, ESOP 2013)。rigid rollback 回到过去后会
  重跑同一段计算,可能反复失败;croll-π 在消息上附加**替代项**(alternative),rollback 时释放替代项而不是
  原消息。名字中的 c 就是 compensating。Lanese、Mezzina、Stefani(RC 2012,LNCS 2013 刊出)讨论了用补偿
  处理不可逆动作的必要性。
- **检查点与因果日志**。Vassor & Stefani(RC 2018)比较分布式检查点/回滚方案 Manetho(基于因果日志)
  与带命令式 rollback 的 π 演算;只核对了摘要开头,结论未核对。
- **可逆 Erlang**。Lanese、Nishida、Palacios、Vidal(JLAMP 2018)给 Core Erlang 子集一个无控制的可逆语义,
  证明因果一致性,再加 rollback 算子:把一个进程撤销到检查点,并把撤销传播到依赖它的进程。工具 CauDEr
  (FLOPS 2018)把它用于调试;Lami 等(RC 2022)把进程注册表这一**跨进程共享的可变映射**纳入可逆语义;
  Lanese & Medić(CONCUR 2020)给出从前向语义机械地导出因果一致可逆语义的一般方法。

### 1.3 saga 与补偿事务

- **Sagas**(Garcia-Molina & Salem, SIGMOD 1987)。长事务拆成子事务序列 T₁ … Tₙ,每个 Tᵢ 配补偿 Cᵢ;
  在 Tₖ 处中止时执行 Cₖ₋₁ … C₁(逆序)。不提供隔离:补偿执行时别的事务可能已经读写过同样的数据,
  "补偿语义上撤销了 Tᵢ"是应用的责任。
- **补偿的演算**。StAC(Butler & Ferreira, COORDINATION 2004);cCSP(Butler、Hoare、Ferreira,
  CSP 25 周年文集 2005,迹语义);Sagas 演算(Bruni、Melgratti、Montanari, POPL 2005);两者的比较
  (Bruni、Butler、Ferreira、Hoare、Melgratti、Montanari, CONCUR 2005)。共同点:顺序组合的补偿按**逆序**
  累积,并行组合的补偿**并行**累积;并行分支中一支中止时,是否打断兄弟分支、补偿集中还是分散执行,是几种
  语义的分歧点。π 风格的长事务演算有 πt(Bocchi、Laneve、Zavattaro, FMOODS 2003)、join 中的事务
  (Bruni、Laneve、Montanari, CONCUR 2002)。补偿处理器可以在运行中**动态安装**(Lanese & Zavattaro
  的动态方式;Lanese, ICE 2010 比较了静态与动态 saga;Lanese、Vaz、Ferreira, ESOP 2010 比较补偿原语的
  表达力;Caires、Ferreira、Vieira, TGC 2008)。
- **语义并发控制中的"可恢复性"**。数据库一侧,Badrinath & Ramamritham(TODS 1992)在可交换性之外
  提出 recoverability:b 相对 a 可恢复,大意是 b 的返回值不因 a 是否执行而改变,于是 a 可以在 b 之后撤销。
  这一内容凭记忆,未核对原文。Weihl(IEEE TC 1988)是按可交换性做抽象数据类型并发控制的经典工作。

### 1.4 可逆会话类型

Tiezzi & Yoshida(JLAMP 2015)给会话 π 演算加可逆性;Mezzina & Pérez 用监视器(EPTCS 2016)、
在 choreography 上(PPDP 2017)、在多方协议上(LMCS 2021)研究因果一致的可逆会话;Castellani、
Dezani-Ciancaglini、Giannini(Acta Informatica 2019)研究带灵活选择的可逆会话;Barbanera、
Dezani-Ciancaglini、de'Liguoro(FAoC 2016)研究可逆的 client/server 相容性;Mezzina、Tiezzi、Yoshida
(LMCS 2025)研究会话编程中基于检查点的回滚恢复。这些工作处理的是**通道两端**一起回退协议,本演算没有通道,
对应关系弱(见 3.2)。

### 1.5 机械化

已知的可逆进程演算机械化很少:Cecilia(ICE 2025)在 Beluga 中形式化了 CCSKP。没有找到 Rocq/Coq 中的
因果一致性证明(检索有限,不代表不存在)。本仓库的 `Recovery.v` 若按第 4 节课题 1 重新表述,会是 Rocq 中
较早的一份"因果等价推出共终"的证明,但对象是带共享状态的组件系统,不是进程演算。

## 2. 对照表

"精确"指定义或定理可以直接互译;"近似"指结构相同但有实质的附加条件或差别;"形似"指只有直觉上的相似。

| 领域概念 | 演算中的规则、定义或定理 | 对应程度 | 说明 |
|---|---|---|---|
| RCCS 线程的记忆栈,后向步从栈顶弹出 | 每个 fiber 的 `acc`,`L-Undo` 从表头撤销(F1) | 近似 | 都是"每个顺序执行单元一个 LIFO 历史"。差别:RCCS 的后向步是语义的一部分,任何时刻都可走;这里 `L-Undo` 只在 Unloading 且 `¬held` 时可走,是受控的 |
| Loop Lemma(每步可逆) | 服务层的 `Witnessed a t`(`Service.v`):`run a t s = Some (s', g, o) → g s' ≃ s` | 近似 | 单个操作上就是 Loop Lemma,但只按 ≃ 回到原状态,而且只针对服务状态。演算整体不满足 Loop Lemma:计数器 `next` 单调,pid 与 fiber 名字不复用,卸载后的 fiber 是 `Inactive None` 而不是"未执行过" |
| 程序的 Loop Lemma(整段可逆) | `Bridge.denote_witnessed`:操作良好时 `⟦P⟧` 带见证 | 近似 | 单个组件单独运行再撤销,存储按 ≃ 回到原样 |
| SP:后向 ā 与前向 b 独立时补成方块 | `RevertIndep a ta b tb` 第 (1) 条(`shifted`):b 在 `g x` 与 `x` 上同时成功或失败,后继差一个 g,结果相同 | 近似 | 正是"先 b 后 g"与"先 g 后 b"共终(按 ≃),并且 b 的结果不变。SP 不要求结果不变,因为 LTS 的标签本身就是观察;这里结果决定程序后续,所以必须相同 |
| SP / BTI:两个后向转移独立 | `RevertIndep` 第 (2) 条:g 与 b 产出的逆可交换 | 近似 | 两个逆的方块。BTI 说"不同的后向转移总是独立",这里是按 `CoPair` 与令牌不同**假设**的(`Recovery.Hind`) |
| 独立关系 ι | `CoPair k a b` 加令牌不同,再加 `RevertIndep` | 近似 | LTSI 的 ι 是模型给定的;这里"独立"是服务作者的义务,只在可能相遇的操作对上要求(R4) |
| 因果等价 ≍(交换独立步、删去 a·ā) | `Service.omission`:a 之后跟一串外来步 ts,再施加 g,≃ 只跑 ts,且 ts 中各步结果不变 | 近似 | omission 就是"把 ā 逐个左移越过 ts(用 SP),再与 a 抵消"的结论,只是对单个服务、按 ≃ 陈述 |
| 因果一致性的"≍ ⇒ 共终"方向 | `Recovery.recovery_exact`、`recovery_from_init`;`R_step` 是其中的归纳不变式 | 近似 | 见 2.2。影子执行 `shadow_run` 就是把 n 的全部"操作加撤销"对删去的那条路径;结论是两条路径在存储投影上共终(按 ≃)。"共终 ⇒ ≍"方向没有对应物,也不需要 |
| 运行期效应的单独撤销 | `Runtime.effect_exact`(F8) | 近似 | 同上,对象是 `O-React` 生成的子 fiber |
| 因果安全 CS(结果撤销之前不撤销原因) | `Ordering.withdraw_waits`、`withdraw_blocked`:撤回 provision 时没有别的已安装 fiber 解析它 | 精确(就 provide→resolve 这一条因果边而言) | 依赖者卸载完毕时累加器为空,它在该 provision 上的操作都已撤销。见 2.1 |
| 守卫 `¬held` 作用于整个卸载 | `Ordering.unload_waits`、`unload_blocked` | 近似 | 比 CS 强:提供者那些**不是**依赖者原因的效应(如依赖者加载之后才发生的运行期子 fiber)也被一起冻结。因此不满足按真实因果关系定义的 CL。见 2.1 |
| 父子撤销顺序 | `L-RetireChild`、`Ordering.parent_waits_child` | 近似 | spawn 是子 fiber 全部动作的原因,子 fiber 先撤完、父再撤 spawn 之前的项,符合 CS。spawn 之后的父效应先于子撤销,这是 LIFO 的要求,不是因果的要求 |
| roll γ:撤销一个动作及其因果闭包 | `O-Restart n`、`O-Dispose n`;依赖者因 target 变化离开(`L-Leave`、`L-Divert`),再由 `¬held` 保证它们先撤完 | 近似 | 闭包是沿"解析了 n 的 provision"与"是 n 的子 fiber"传递的。与 roll-π 不同:依赖者撤完后会在提供者回来时**重新加载**(target 驱动),roll-π 没有这一半 |
| rigid rollback 的重复失败;croll-π 的替代项 | `Fail` 进入 `Inactive (Some ξ)` 后停住,`O-Reset` 由外部触发 | 近似 | 本演算用"失败后停住"避开 rollback 后重跑同一路径的发散;没有替代项。见课题 4 |
| 不可逆动作(Transactions in RCCS 的提交) | 无 | — | 本演算的每个效应都可撤销。越过边界的效应(外部 IO、disposer 失败,差异 f)不在模型内 |
| saga 后向恢复:Tₖ 处中止,执行 Cₖ₋₁ … C₁ | `L-Step` 的 `Fail ξ` 与 `Op` 失败分支进入 `Unloading acc ω (Some ξ)`,随后 `L-Undo` 按 LIFO 撤销 | 精确 | 补偿就是累加器里的逆,顺序就是 saga 要求的逆序。F7 |
| saga 被外部取消 | `L-Divert`(target 变化时放弃加载) | 精确 | 同样走 Unloading 撤销已做的部分 |
| saga 的前向恢复(重试) | `O-Reset` 后从头重新加载 | 近似 | 只能从头重试,不能从中止点继续 |
| 补偿的动态安装 | `run` 在执行时产出逆 g,写入 `UOp` | 精确 | 逆依赖执行时的状态与令牌,正是"动态安装补偿"。合流假设里的 `UniformInv`(同一令牌下逆与状态无关,`Compose.ConfHyps`)是合流才需要的额外限制 |
| 嵌套 saga、子事务的补偿 | `Spawn` 与 `USpawn`,`O-React` 的子 fiber | 近似 | 子 fiber 是一棵子补偿树,父撤到 `USpawn` 时整体撤销子树 |
| 并行 saga 的补偿并行执行 | 不同 fiber 的 `L-Undo` 交错 | 近似 | 不同 fiber 的撤销可以交错;单个 fiber 内部串行(差异 e) |
| saga 的补偿正确性(语义上撤销 Tᵢ,无隔离) | `recovery_exact` 在 `Hind` 下给出 | 近似 | saga 文献一般把补偿正确性留给应用;这里给出了在交错下仍成立的精确陈述,义务是操作级的撤销独立 |
| recoverability(Badrinath & Ramamritham) | `RevertIndep` 第 (1) 条中"结果相同"的部分 | 近似(原文内容未核实) | 两者都是"b 的返回值与 a 是否已撤销无关"。`RevertIndep` 还要求后继状态差一个 g、两个逆可交换 |
| 可逆会话类型、可逆 choreography | 无直接对应 | 形似 | 本演算的交互是对共享服务状态的操作,不是通道上的消息,见 3.2 |

### 2.1 守卫 `¬held` 是不是因果一致性的约束

结论:**沿 provide→resolve 这条边,`¬held` 蕴含因果安全;但它比因果安全强,按真实因果关系不满足因果活性。**

1. **哪条边是因果边。** 依赖者 m 的 `L-Begin` 读取 `visible k = pid`(要求提供者 n Active),此后 m 在 pid
   上的每个操作都以 n 的 `UProv k pid` 为原因。`begin_requires_deps` 说 m 开始加载时它的依赖都由 Active 的
   提供者绑定。
2. **CS 成立。** `withdraw_waits` 说撤回 provision 时没有别的已安装 fiber 解析它。m 不再已安装时处于
   `Inactive`,累加器为空,所以它在 pid 上的操作都已经撤销。这就是 CS 对这条边的要求:原因(provide)
   在其结果(m 的全部操作)撤销之后才撤销。
3. **`¬held` 更强。** `unload_waits` 说只要 n 还有 provision 被别人解析,n 就**不撤销任何一项**,包括 n 自己
   在 pid 上做的操作和它的运行期子 fiber。按因果关系看:
   - n 在 provide 之后、Active 之前做的操作,确实先于 m 的全部动作(m 只能在 n Active 后开始),但它们是不是
     m 的**原因**,取决于 m 是否读到了它们的效果;本演算不跟踪这种数据依赖,只有服务层的独立性假设。
   - n 的运行期子 fiber(`O-React`)可能在 m 开始之后才生成,它们不是 m 的原因,按 CL 应当可以先撤销,
     `¬held` 却不允许(连 `L-RetireChild` 也被挡住)。
4. **为什么这样设计。** DESIGN 差异 g 的理由不是因果安全,而是"依赖者在提供者的全部效应都还在的状态上完成
   卸载"。用因果一致性的语言说:演算选的因果关系是**粗粒度的**,把"m 解析了 n 的某个 provision"看成
   "m 的每个动作都在 n 当时的全部效应之后"。粗粒度的因果关系下 `¬held` 就是 CS;在细粒度(按操作的数据依赖)
   下它是 CS 加上一部分额外的等待。
5. **这条边上的副产品。** 由 1 与 3,对一对提供者与依赖者 (n, m),n 的操作全部在 m 的操作之前,m 的撤销全部
   在 n 的撤销之前:它们的"执行—撤销"区间是**正确嵌套**的。嵌套的两段历史按 LIFO 撤销,不需要任何独立性假设
   (这正是因果一致性理论里"按逆因果序撤销总是可行"的情形)。现在的 `Recovery.Hind` 仍对这一对要求撤销独立,
   因为 `CoPair` 不区分有没有依赖关系。课题 2 利用这一点。

### 2.2 `recovery_exact` 能否写成 Loop Lemma 或因果一致性定理

结论:**可以写成"因果等价推出共终"在存储投影上的一个实例,前提是用服务层的独立性定义 ι;Loop Lemma 对应的是
`Witnessed`,不是 `recovery_exact` 本身。** 具体对应:

- 一次执行看成路径 r。把 n 的每个操作 a 记为前向步,`L-Undo` 撤销它的那一步记为 ā。`shadow_run` 计算的是从
  r 中删去 n 的全部 a 与 ā 得到的路径 r∖n 在存储上的效果(`event`、`shadow_apply`)。
- 因果等价的定义允许"交换独立步"与"删去 a·ā"。若 n 的每个 ā 都能越过 r 中位于 a 与 ā 之间的外来步左移,
  就有 r ≍ r∖n。能否越过,正是 `RevertIndep`(SP 的两个实例,见对照表)。n 自己的步之间不需要越过:LIFO
  保证 n 的 a 与 ā 之间,n 自己的步已经两两抵消。
- "≍ ⇒ 共终"在 SP 成立的 LTSI 里是直接的。`recovery_exact` 的结论"实际存储 ≃ 影子存储"就是 r 与 r∖n 在
  存储投影上共终。证明里的不变式 `R`(把 n 尚未撤销的逆按 LIFO 作用于实际状态 ≃ 影子状态)就是"把还没抵消的
  ā 先行虚拟地施加"的记账。
- 不对应的部分:
  - 因果一致性的另一方向"共终 ⇒ ≍"依赖历史信息完整地记录在状态里。本演算的状态按 ≃ 比较,并且丢掉了历史
    (撤销后的条目不留痕迹),这一方向不成立,也不需要。
  - 公理化框架要求所有转移可逆(Loop Lemma 在整个 LTS 上成立)。本演算是受控的:后向步只能在 Unloading
    中、按 `¬held` 与 `USpawn` 等待走;LTS 的状态还包含计数器、fiber 注册表,这些不回退。合理的读法是 roll-π
    的做法:先定义一个**无控制**的底层可逆语义(只含服务存储与每个 fiber 的撤销项),证明它满足 SP、BTI、WF,
    再证明演算的每次 `L-Undo` 都是底层的一次后向步。课题 1 按这个思路做。
  - 结论按 ≃,不是按相等;独立关系 ι 只在 `CoPair` 内、令牌不同时定义。这需要把公理化框架推广到 setoid 与
    部分定义的独立关系,工作量主要在这里。

### 2.3 LIFO 撤销与因果序撤销

- **单个 fiber 内部。** 程序顺序是数据依赖的超集,所以逆程序顺序(LIFO)总是一种因果安全的撤销顺序,而且不需要
  任何假设(差异 e,`R_step` 对同一 fiber 不用 `Hind`)。代价是不满足 CL:两个彼此独立的 disposer 也必须串行、
  按固定顺序跑。DESIGN D6 给出的 `Promise.all` 判据("这些逆以任意顺序施加结果都 ≃")正是"在这些项之间
  CL 成立"的条件;`RevertIndep` 第 (2) 条是充分条件。这个判据还没有形式化。
- **跨 fiber。** 全局的撤销顺序**不是** LIFO:不同 fiber 的撤销与别人的前向操作任意交错。约束只有三条:
  `¬held`(提供者等依赖者)、`USpawn` 等待(父等子)、各 fiber 内部 LIFO。其余的先后关系不跟踪,而是由
  服务层的撤销独立(`Hind`)保证无所谓。这与 RCCS 的结构一致:线程内是栈,线程间按同步关系配对;区别是
  RCCS 的线程间因果只来自同步,这里来自对共享状态的读写,本演算选择用独立性假设代替跟踪。
- **树形顺序。** 父撤到 `USpawn m` 时先等子撤完,这是 LIFO 在 fiber 树上的推广(DESIGN 3.2 的玫瑰树
  `T ≔ μT. List((Σ → Σ) + T)`,按后序遍历撤销)。因果序允许不同子树之间、子树与父的无关项之间交错,本演算
  在跨 fiber 层面已经允许交错,只在同一 fiber 的项之间坚持顺序。
- **乱序可逆**不适用:撤销 provide 之后再撤销依赖者的操作,会让依赖者的逆作用在不存在的绑定上
  (`L-Undo` 的 `UOp` 分支会什么都不做,破坏恢复)。

## 3. 差异

### 3.1 演算有而可逆计算文献没有的

1. **共享可变状态上的逆由服务给出,不由语义构造。** 进程演算里后向步由历史机械地确定(弹栈、按键配对);这里
   逆 g 是服务操作返回的函数,正确性是服务义务(`WellBehaved`)。因此独立性也是服务义务,而不是由"在不同进程中"
   推出。最接近的是可逆 Erlang 对进程注册表的处理(Lami 等, RC 2022),但那里共享状态是固定的内建映射。
2. **按 ≃ 的恢复。** 文献中的 Loop Lemma 与因果一致性都按状态相等;这里服务状态有 setoid,结论都按 ≃。
   `Observe.v` 说明合法的 ≃ 都包含于"不可区分"。
3. **target 驱动的撤销与重做。** 撤销不是由用户发起的 `roll`,而是 target 变化的结果;撤销之后,只要 target
   回来就重做。可逆计算文献中 rollback 之后的行为一般是"从过去状态继续非确定地执行",没有"收敛到期望状态"的概念
   (F3 属于 incremental 方向)。
4. **全局计数器与新鲜身份。** provision 撤掉再提供时 pid 变化,依赖者因此重新加载(差异 b)。CCSK 的键与 RCCS 的
   标识在撤销后可以复用,回到的是同一个状态;这里刻意不复用。
5. **合流。** 本演算还证明了前向执行的合流(`Confluence.v` … `Dynamic.v`),需要可交换(`Commute`)。可逆计算文献
   关心的是后向执行与前向执行之间的关系,很少讨论前向调度无关性;两种独立性(撤销独立与可交换)的区分
   (RULES 第 7 节)在文献中没有现成对应。

### 3.2 可逆计算文献有而演算没有的

1. **无控制的后向语义与 Loop Lemma。** 本演算没有"任意时刻可以后退"的语义,所以没有可逆调试那样的应用
   (CauDEr)。若要做 Cordis 插件的回放与调试,需要先补这一层(课题 1 的副产品)。
2. **不可逆动作与提交。** 本演算所有效应都可撤销;外部 IO 只能靠 `resource` 原语(EDSL.md)。
3. **rollback 的替代项(croll-π)与 saga 的前向恢复。** 本演算失败后只能停住或由外部从头重试。
4. **通道与会话。** 可逆会话类型讨论的是通信双方一起回退、回退后协议仍合法。本演算的 fiber 之间没有消息通道,
   交互全部通过服务状态;唯一形似之处是"依赖者与提供者一起回退"(2.1)。若将来给服务接口加类型状态
   (见 session-types 方向),可逆会话类型里"回退保持协议合法"的结论才有用。
5. **细粒度因果。** 文献按动作跟踪因果;本演算按 fiber 与 provision 的粒度,数据依赖交给独立性假设。

## 4. 候选课题

### 课题 1:`recovery_exact` 重述为因果一致性的"≍ ⇒ 共终"

- **目标**:把 `Recovery.v` 的结论放进 Lanese–Phillips–Ulidowski 的公理框架,使"恢复精确性"有标准名字,也让
  `Hind` 有标准读法(它就是 SP 的两个实例)。
- **做法**:
  1. 新文件 `theories/Reversible.v`。定义服务存储上的 LTSI:状态是 (存储, 每个 fiber 的待撤销逆的栈),
     前向转移是带令牌的操作,后向转移是弹出栈顶并施加逆;独立关系为不同 fiber 且满足 `CoPair` 与令牌不同。
  2. 推广框架到 setoid:转移结果按 ≃,方块按 ≃ 共终。证明 `Witnessed` 给出 Loop Lemma,`RevertIndep` 给出
     (前向, 后向) 与 (后向, 后向) 对的 SP;同一 fiber 的后向转移只有栈顶一个,BTI 平凡成立;WF 由栈有限得到。
  3. 证明"因果等价推出共终(按 ≃)",并把 `omission` 与 `R_step` 改写成它的推论。
  4. 证明演算的投影:每个 `L-Step` 的 `Op` 分支与 `L-Undo` 的 `UOp` 分支是底层的一个前向或后向转移
     (可借用 `Bridge.op_stage`、`op_undo`),再得到 `recovery_exact` 的新证明。
- **预期产出**:一个与公理框架对齐的 Rocq 文件;`recovery_exact` 的第二个证明;一段说明 `RevertIndep` 与 SP
  关系的文档。副产品是 Cordis 的无控制可逆语义,可作为回放、调试工具的依据。
- **风险**:公理框架用状态相等与转移身份("同一事件"的转移),推广到 ≃ 与部分定义的独立关系时,框架的
  若干性质(如 CS、CL 的事件版本)可能不再直接成立;只做"≍ ⇒ 共终"这一方向可以控制风险。现有证明已经成立,
  这个课题的收益主要是定位与可复用性,不是新结论。
- **工作量**:中。

### 课题 2:沿依赖边免去撤销独立假设;多个 fiber 的恢复精确性

- **目标**:利用 2.1 第 5 点的区间嵌套,把 `Hind` 收窄到"可能相遇且没有依赖关系"的操作对;并给出一组 fiber
  (例如一个提供者连同它的全部依赖者)整体撤销后的恢复精确性。
- **做法**:
  1. 证明嵌套引理:若 m 解析了 n 的 provision,则一次执行中 n 对该 pid 的每个操作都先于 m 的 `L-Begin`,
     m 在该 pid 上的每个撤销都先于 n 对该 pid 的任何撤销。前一半来自 `begin_requires_deps` 与"Active 的 fiber
     没有自己的服务操作",后一半来自 `unload_waits`。需要处理 `O-Restart` 后同一组件重新提供(新 pid)的情形。
  2. 定义 `DepPair k a b`:a、b 分别出现在提供 k 的组件与声明 k 的组件中。把 `Hind` 改成只对
     `CoPair k a b ∧ ¬DepPair k a b ∧ ¬DepPair k b a` 要求;重做 `R_step` 中用到 `Hind` 的分支,对依赖对改用嵌套引理。
  3. 把影子执行从"跳过一个 fiber"推广为"跳过一个 fiber 集合 S",证明 `recovery_exact` 的集合版本;对 S 内部的
     依赖对同样不需要独立性。
  4. 注意运行期子 fiber:n 的 `O-React` 子 fiber 与 m 之间没有嵌套关系,仍需 `Hind`。
- **预期产出**:更弱假设下的 `recovery_exact`;`Summary.v` 中服务义务的收窄(提供者与依赖者之间的操作不再要求撤销
  独立)。对 dsh 的直接意义:服务的提供者可以在启动时做"先注册、依赖者再读取自己注册的条目"一类操作,不受
  `Registry.v` 中"读取别人注册的条目不撤销独立"的限制。需要先核对这种模式在 dsh 中是否真的出现在提供者与依赖者之间。
- **风险**:`CoPair` 是按组件定义的,同一组件可能既是某键的提供者又通过别的键成为依赖者;`DepPair` 的定义要与
  运行时的实际解析一致。合流一侧的 `HRI`、`HCom` 能否同样收窄是另一个问题,不在本课题内。
- **工作量**:中到大(第 1、2 步中,第 3 步加大)。

### 课题 3:单个 fiber 内的因果序撤销(`Promise.all` 判据的形式化)

- **目标**:形式化 DESIGN D6 的判据,允许一个 fiber 内部彼此独立的撤销项以任意顺序(或并发)执行,即在 fiber 内
  恢复因果活性。
- **做法**:
  1. 服务层(小):对一串逆 gs,若两两可交换(按 ≃,且各自尊重 ≃),则任意排列施加的结果 ≃。再证明 `RevertIndep`
     第 (2) 条推出两两可交换。放在 `Service.v` 之外的新文件,只依赖 `apply_all` 一类定义。
  2. 演算层(大):新规则 `L-UndoAny n i`:撤销 `acc` 的第 i 项,前提是它与表头到第 i−1 项都"撤销独立"
     (同一 fiber 的两项之间的独立性需要新的服务义务,现在的 `Hind` 只管不同 fiber)。重做 `Recovery.v` 的
     `R_undo`、`Preservation.v` 中与 `acc` 结构有关的不变式(`UProv` 唯一、`USpawn` 对应子 fiber)、
     `Termination.v` 的度量。`UProv` 与 `USpawn` 项不参与重排,只重排 `UOp`,可以显著降低工作量。
- **预期产出**:第 1 步给出可直接引用的判据定理,支持差异 e 对 Cordis 的建议("只对声明为独立的效应并发");第 2 步
  给出一个允许乱序撤销 `UOp` 的演算变体及其恢复精确性。
- **风险**:第 2 步牵涉的文件多;同一 fiber 内操作的独立性在实践中可能很少成立(后注册的效应常依赖先注册的效应,
  这正是选 LIFO 的理由)。建议先做第 1 步,看 dsh 中有多少 disposer 满足判据再决定是否做第 2 步。
- **工作量**:第 1 步小,第 2 步大。

### 课题 4:带替代项的失败处理(croll-π / saga 前向恢复)

- **目标**:给程序加 `Try P Q`:P 失败时撤销 P 已做的效应,然后执行 Q,而不是整个 fiber 进入 `Inactive (Some ξ)`。
  对应 croll-π 的替代项与 saga 的"补偿后改走另一条路"。
- **做法**:在 `Loading` 中引入撤销标记(一个 `UMark` 撤销项),`Fail` 时若累加器中有标记,就进入一个新的局部撤销状态,
  撤到标记后继续执行 Q。需要的定理:保持性、顺序不变;终止的度量把 Q 的长度计入 `Bounded`;恢复精确性在 fiber 局部
  也成立(局部撤销只是 `L-Undo` 的一段)。
- **预期产出**:一个扩展(可放在 `theories/Ext/` 下,与现有扩展的组织方式一致)及其元理论。
- **风险**:局部撤销发生在 Loading 中,此时没有依赖者(提供者 Active 之前没人能解析它),所以不需要 `¬held`;但
  局部撤销会撤掉已经 `Provide` 的键,若 Q 再次提供同一键,pid 变化,要检查 `ProvideInv` 与合流的全性假设。
  dsh 是否需要这个结构未调查;若需求不明确,优先级低。
- **工作量**:中。

### 课题 5(低优先级):把守卫与 CS/CL 的关系写成定理

- **目标**:把 2.1 的论述形式化:定义 fiber 级与 provision 级两种因果关系,证明 `¬held` 在前者下等价于 CS,在后者下
  只蕴含 CS。
- **做法**:在课题 1 的 LTSI 上定义事件与因果序,陈述 CS、CL;用 `withdraw_waits`、`unload_waits`、`parent_waits_child`
  证明 CS;给一个小例子(提供者在依赖者加载后生成运行期子 fiber)说明细粒度 CL 不成立。
- **预期产出**:一个短文件和一段文档;帮助回答"为什么守卫作用于整个卸载"时有形式依据。
- **风险**:主要是定义的选择,结论预计不难。依赖课题 1。
- **工作量**:小(在课题 1 之后)。

## 5. 参考文献

元数据(作者、题目、会议或期刊、年份)经 Crossref 元数据接口或出版方、arXiv、DROPS 页面核对,DOI 列在后面。
内容层面的描述大多只核对了摘要;个别描述凭记忆,已在正文中标出。

**因果一致可逆性**

1. Vincent Danos, Jean Krivine. Reversible Communicating Systems. CONCUR 2004, LNCS. doi:10.1007/978-3-540-28644-8_19
2. Vincent Danos, Jean Krivine. Transactions in RCCS. CONCUR 2005, LNCS. doi:10.1007/11539452_31
3. Vincent Danos, Jean Krivine. Formal Molecular Biology Done in CCS-R. ENTCS, 2007. doi:10.1016/j.entcs.2004.01.040
4. Iain Phillips, Irek Ulidowski. Reversing Algebraic Process Calculi. FoSSaCS 2006, LNCS(doi:10.1007/11690634_17);
   期刊版 Journal of Logic and Algebraic Programming, 2007(doi:10.1016/j.jlap.2006.11.002)。
5. Iain Phillips, Irek Ulidowski, Shoji Yuen. A Reversible Process Calculus and the Modelling of the ERK Signalling Pathway.
   Reversible Computation (RC 2012), LNCS, 2013. doi:10.1007/978-3-642-36315-3_18
6. Iain Phillips, Irek Ulidowski. Reversibility and Asymmetric Conflict in Event Structures. CONCUR 2013, LNCS
   (doi:10.1007/978-3-642-40184-8_22);期刊版 JLAMP, 2015(doi:10.1016/j.jlamp.2015.07.004)。
7. Ivan Lanese, Claudio Antares Mezzina, Jean-Bernard Stefani. Reversing Higher-Order Pi. CONCUR 2010, LNCS
   (doi:10.1007/978-3-642-15375-4_33);期刊版 Reversibility in the higher-order π-calculus, Theoretical Computer Science,
   2016(doi:10.1016/j.tcs.2016.02.019)。
8. Ioana Cristescu, Jean Krivine, Daniele Varacca. A Compositional Semantics for the Reversible π-Calculus. LICS 2013.
   doi:10.1109/LICS.2013.45
9. Ivan Lanese, Claudio Antares Mezzina, Francesco Tiezzi. Causal-Consistent Reversibility. Bulletin of the EATCS 114, 2014.
   (dblp 记录与机构仓库核对;正文未读到)
10. Ivan Lanese, Doriana Medić, Claudio Antares Mezzina. Static versus dynamic reversibility in CCS. Acta Informatica, 2019.
    doi:10.1007/s00236-019-00346-6
11. Ivan Lanese, Iain Phillips, Irek Ulidowski. An Axiomatic Approach to Reversible Computation. FoSSaCS 2020, LNCS
    (doi:10.1007/978-3-030-45231-5_23);期刊版 An Axiomatic Theory for Reversible Computation, ACM Transactions on
    Computational Logic 25(2), 2024(doi:10.1145/3648474;arXiv:2307.13360)。正文第 1.1 节的公理与性质据 arXiv v2 核对。
12. Ivan Lanese, Doriana Medić. A General Approach to Derive Uncontrolled Reversible Semantics. CONCUR 2020, LIPIcs.
    doi:10.4230/LIPIcs.CONCUR.2020.33
13. Alexis Bernadet, Ivan Lanese. A Modular Formalization of Reversibility for Concurrent Models and Languages. ICE 2016,
    EPTCS. doi:10.4204/EPTCS.223.7
14. Gabriele Cecilia. A Formalization of the Reversible Concurrent Calculus CCSKP in Beluga. ICE 2025, EPTCS 425.
    arXiv:2508.13612

**受控可逆性与可逆 Erlang**

15. Ivan Lanese, Claudio Antares Mezzina, Alan Schmitt, Jean-Bernard Stefani. Controlling Reversibility in Higher-Order Pi.
    CONCUR 2011, LNCS. doi:10.1007/978-3-642-23217-6_20
16. Ivan Lanese, Michael Lienhardt, Claudio Antares Mezzina, Alan Schmitt, Jean-Bernard Stefani. Concurrent Flexible
    Reversibility. ESOP 2013, LNCS. doi:10.1007/978-3-642-37036-6_21
17. Ivan Lanese, Claudio Antares Mezzina, Jean-Bernard Stefani. Controlled Reversibility and Compensations. Reversible
    Computation (RC 2012), LNCS, 2013. doi:10.1007/978-3-642-36315-3_19
18. Martin Vassor, Jean-Bernard Stefani. Checkpoint/Rollback vs Causally-Consistent Reversibility. Reversible Computation
    (RC 2018), LNCS. doi:10.1007/978-3-319-99498-7_20
19. Ivan Lanese, Naoki Nishida, Adrián Palacios, Germán Vidal. A theory of reversibility for Erlang. JLAMP, 2018.
    doi:10.1016/j.jlamp.2018.06.004
20. Ivan Lanese, Naoki Nishida, Adrián Palacios, Germán Vidal. CauDEr: A Causal-Consistent Reversible Debugger for Erlang.
    FLOPS 2018, LNCS. doi:10.1007/978-3-319-90686-7_16
21. Pietro Lami, Ivan Lanese, Jean-Bernard Stefani, Claudio Sacerdoti Coen, Giovanni Fabbretti. Reversibility in Erlang:
    Imperative Constructs. Reversible Computation (RC 2022), LNCS. doi:10.1007/978-3-031-09005-9_13
22. Elena Giachino, Ivan Lanese, Claudio Antares Mezzina. Causal-Consistent Reversible Debugging. FASE 2014, LNCS.
    doi:10.1007/978-3-642-54804-8_26

**saga 与补偿**

23. Hector Garcia-Molina, Kenneth Salem. Sagas. SIGMOD 1987. doi:10.1145/38713.38742
24. Michael Butler, Carla Ferreira. An Operational Semantics for StAC, a Language for Modelling Long-Running Business
    Transactions. COORDINATION 2004, LNCS. doi:10.1007/978-3-540-24634-3_9
25. Michael Butler, Tony Hoare, Carla Ferreira. A Trace Semantics for Long-Running Transactions. Communicating Sequential
    Processes: The First 25 Years, LNCS, 2005. doi:10.1007/11423348_8
26. Roberto Bruni, Hernán Melgratti, Ugo Montanari. Theoretical Foundations for Compensations in Flow Composition Languages.
    POPL 2005. doi:10.1145/1040305.1040323
27. Roberto Bruni, Michael Butler, Carla Ferreira, Tony Hoare, Hernán Melgratti, Ugo Montanari. Comparing Two Approaches to
    Compensable Flow Composition. CONCUR 2005, LNCS. doi:10.1007/11539452_30
28. Roberto Bruni, Cosimo Laneve, Ugo Montanari. Orchestrating Transactions in Join Calculus. CONCUR 2002, LNCS.
    doi:10.1007/3-540-45694-5_22
29. Laura Bocchi, Cosimo Laneve, Gianluigi Zavattaro. A Calculus for Long-Running Transactions. FMOODS 2003, LNCS.
    doi:10.1007/978-3-540-39958-2_9
30. Ivan Lanese, Cátia Vaz, Carla Ferreira. On the Expressive Power of Primitives for Compensation Handling. ESOP 2010, LNCS.
    doi:10.1007/978-3-642-11957-6_20
31. Luís Caires, Carla Ferreira, Hugo Vieira. A Process Calculus Analysis of Compensations. TGC 2008, LNCS, 2009.
    doi:10.1007/978-3-642-00945-7_6
32. Ivan Lanese. Static vs Dynamic SAGAs. ICE 2010, EPTCS 38. doi:10.4204/EPTCS.38.7
33. Ivan Lanese, Gianluigi Zavattaro. Decidability Results for Dynamic Installation of Compensation Handlers. COORDINATION
    2013, LNCS. doi:10.1007/978-3-642-38493-6_10
34. B. R. Badrinath, Krithi Ramamritham. Semantics-based concurrency control: Beyond commutativity. ACM Transactions on
    Database Systems, 1992. doi:10.1145/128765.128771(元数据已核实;正文中关于 recoverability 的描述凭记忆,未核实)
35. William E. Weihl. Commutativity-based concurrency control for abstract data types. IEEE Transactions on Computers, 1988.
    doi:10.1109/12.9728
36. Henry F. Korth, Eliezer Levy, Abraham Silberschatz. A Formal Approach to Recovery by Compensating Transactions. VLDB 1990.
    **未核实**(Crossref 未检索到,检索额度用尽前没有找到其他来源)。正文未引用其内容,列出供后续核对:它讨论补偿事务的
    正确性标准,若属实,与课题 2 中"无隔离下的补偿正确性"相关。

**可逆会话类型**

37. Francesco Tiezzi, Nobuko Yoshida. Reversible session-based pi-calculus. JLAMP, 2015. doi:10.1016/j.jlamp.2015.03.004
38. Claudio A. Mezzina, Jorge A. Pérez. Reversible Sessions Using Monitors. PLACES 2016, EPTCS. doi:10.4204/EPTCS.211.6
39. Claudio Antares Mezzina, Jorge A. Pérez. Causally consistent reversible choreographies. PPDP 2017. doi:10.1145/3131851.3131864
40. Claudio Antares Mezzina, Jorge A. Pérez. Causal Consistency for Reversible Multiparty Protocols. Logical Methods in Computer
    Science 17(4), 2021. doi:10.46298/lmcs-17(4:1)2021
41. Ilaria Castellani, Mariangiola Dezani-Ciancaglini, Paola Giannini. Reversible sessions with flexible choices. Acta Informatica,
    2019. doi:10.1007/s00236-019-00332-y
42. Franco Barbanera, Mariangiola Dezani-Ciancaglini, Ugo de'Liguoro. Reversible client/server interactions. Formal Aspects of
    Computing, 2016. doi:10.1007/s00165-016-0358-2
43. Claudio Antares Mezzina, Francesco Tiezzi, Nobuko Yoshida. Checkpoint-based rollback recovery in session programming.
    Logical Methods in Computer Science 21(1), 2025. doi:10.46298/lmcs-21(1:2)2025

未核实的条目:1 条(第 36 条)。另有两处内容描述凭记忆、未对照原文:roll-π 把 rollback 正确性归结到无控制语义
(1.2 节,第 15 条),Badrinath & Ramamritham 的 recoverability 定义(1.3 节,第 34 条)。第 38 条的会议名 PLACES 2016
取自 EPTCS 211 卷的归属,未单独核对。
