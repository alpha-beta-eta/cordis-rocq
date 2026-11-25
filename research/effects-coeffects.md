# 效应系统、余效应、分级类型、代数效应与处理器

对照特征:F1(LIFO 撤销日志)、F4(依赖是对上下文的需求)、F8(运行期效应)。

先说一个译名上的区分,后文反复用到。论文(arXiv:2608.25512v1)说的"反应式余效应",指的是**运行期的上下文本身**:
按键存取的存储(定义 19–20)和它随 provide 变化而通知依赖者的机制(定义 21–22)。Petricek、Orchard、Mycroft
一系的"余效应"(coeffect)指的是**类型判断上的静态标注**:一段程序要求上下文提供什么。两者是同一枚硬币的两面:
`d(c)` 是静态标注,`View ω` 与 `binds` 是满足这个标注的运行期上下文。本文的"余效应"默认指后者的静态意义,
说到论文的用法时会注明。

## 1. 领域概览

### 1.1 效应系统

- **起点**:Lucassen 与 Gifford(POPL 1988)给类型加上效应标注,记录表达式可能读写哪些区域,用来判断两个表达式
  能否并行求值:效应不相交即互不干扰。Talpin 与 Jouvelot(LICS 1992,期刊版 1994)给出带区域的类型与效应
  的推断。
- **行多态效应**:Koka(Leijen,MSFP 2014)用允许重复标签的效应行表示效应,类型推断按 Hindley-Milner 进行。
  关键的是语义保证:一个表达式若能不带 `exn` 定型,就不会抛出未处理的异常。这类"效应安全"定理的形状是:
  类型里没写的效应,运行时不会发生。
- **通用框架**:Marino 与 Millstein(TLDI 2009)把效应系统看作授予与检查"特权",参数化于特权的语法与两个
  检查函数。这一读法与能力(capability)很接近。
- **语义**:Katsumata(POPL 2014)的参数化效应单子(即分级单子)给出效应系统的指称语义:单子按一个幺半群分级,
  顺序组合对应分级的乘法。Tate(POPL 2013)讨论了同一方向的另一种推广。Atkey(JFP 2009)的参数化单子按
  前后条件对分级,适合表达"做完之后状态类型变了"。Orchard、Wadler、Eades(MSFP 2020)的范畴分级单子把两者
  统一起来。

### 1.2 余效应与分级余单子

- Petricek、Orchard、Mycroft(ICALP 2013)提出余效应:效应系统描述计算对环境**做了什么**,余效应描述计算
  **要求**环境提供什么。例子有活性分析、隐式参数、数据流的缓存需求。语义用索引余单子。这是"平坦"余效应:
  一个标注描述整个上下文。
- 同一组作者在 ICFP 2014 推广到"结构"余效应:按变量逐个标注,标注的形状可以变化。
- 隐式参数(Lewis 等,POPL 2000)是平坦余效应的典型例子:动态作用域的变量放进静态类型,标注就是所需隐式
  参数的集合。Uustalu 与 Vene(ENTCS 2008)更早用余单子组织依赖上下文的计算(数据流、属性求值)。
- Granule(Orchard、Liepelt、Eades,ICFP 2019)把线性类型、分级模态 `□_r A` 与索引类型合在一门语言里。
  分级取自一个半环:自然数表示恰好用几次,区间表示用量的上下界,安全等级表示信息流。
- Gaboardi 等(ICFP 2016)把效应与余效应放进同一个演算,模型用效应分级的单子、余效应分级的余单子,以及
  分级分配律连接两者。

### 1.3 代数效应与处理器

- Plotkin 与 Power(2003)证明"通用效应"与"代数操作"可以互相转换:一个操作 `op : A → T B` 等价于
  一族以 `B` 为元数的代数操作。程序就是操作签名上的自由单子(加上方程时是自由模型)。
- Plotkin 与 Pretnar(ESOP 2009,期刊版 LMCS 2013)提出处理器:处理器是从自由模型出发的同态,
  也就是对程序语法的一次折叠。Eff(Bauer、Pretnar,JLAMP 2015)、Kammar、Lindley、Oury(ICFP 2013)
  把它做成语言与库。Haskell 的实现路线有"数据类型点菜"(Swierstra,JFP 2008)与更自由的单子
  (Kiselyov、Ishii,Haskell 2015);后者的应用里就有用于资源管理的单子区域。
- **作用域效应与高阶效应**:`catch`、`once`、`local` 这类操作本身带一段子计算。Wu、Schrijvers、Hinze
  (Haskell 2014)指出用处理器模拟作用域会限制效应之间的交互;Piróg 等(LICS 2018)把带作用域的操作
  当作语法处理。Hefty 代数(Bach Poulsen、van der Rest,POPL 2023)的做法是把高阶操作**展开**成一阶操作,
  展开本身可以模块化地组合。
- **异步效应**:Ahman 与 Pretnar(POPL 2021)把操作调用拆成"发出信号"和"以中断送回结果",计算可以安装
  中断处理器对中断做出反应。

### 1.4 资源、终结器与处理器

- 处理器可以不恢复续延(比如异常),也可以恢复多次。这让资源清理变难:持有资源的那段计算可能永远不再继续。
- Haskell 的 `bracket` 背后是 Marlow 等(PLDI 2001)的异步异常:获取资源与登记释放之间若能被打断,就会泄漏,
  所以要用 `block`/`unblock`(今天的 `mask`)把两者放进一个不可打断的片段。
- Leijen 的技术报告(MSR-TR-2018-10)给处理器加上"深终结":操作不恢复时,沿处理器栈的终结器仍然可靠地执行;
  另有带线性约束的初始化器。
- Runner(Ahman、Bauer,ESOP 2020)把代数效应的余模型作为资源管理的模型,演算 λcoop 的指称语义保证资源
  线性使用、终结代码一定执行。
- OCaml 5 的效应处理器(Sivaramakrishnan 等,PLDI 2021)不检查效应类型;被丢弃的续延要显式 `discontinue`
  才会运行其中的清理代码。

### 1.5 能力与效应

- Effekt(Brachthäuser、Schuster、Ostermann,OOPSLA 2020)把效应类型读成"计算需要上下文提供哪些能力",
  语义是显式传递能力的演算。这正是把效应读成余效应。Frank(Lindley、McBride、McLaughlin,POPL 2017)
  的 ability 也是"调用一组命令的许可"。
- 捕获类型(Boruch-Gruszecki 等,TOPLAS 2023)在类型里记录闭包捕获了哪些能力,用作用域受限的能力实现效应
  多态,防止能力逃出它的作用域。
- 对象能力(Miller 的博士论文,2006)从安全的角度讲同一件事:没有环境权限(ambient authority),
  一段代码只能通过别人交给它的引用行事。Maffeis、Mitchell、Taly(S&P 2010)给出 JavaScript 的权限安全子集。

## 2. 对照表

"关系"一列:**精确** = 定义或定理层面一一对应;**近似** = 结构相同、细节不同;**形似** = 只有直观上的相似。

### 2.1 程序与处理器

| 领域概念 | 演算中的对应 | 关系 | 说明 |
|---|---|---|---|
| 操作签名上的自由单子 | `Calculus.Prog`:`PDone`、`PFail`、`POp k a κ`、`PProvide k s P`、`PSpawn c P` | 精确 | 签名为 `{Op k a : 元数 Out Σ; Provide k s : 元数 1; Spawn c : 元数 1; Fail : 元数 0}`,`PDone` 是 `return ()`。没有定义 bind,但程序是归纳类型、续延 `κ : Out Σ → Prog`,正是自由单子的树形式。注意 Rocq 中 `PFail` 不带错误参数(RULES.md 写的是 `Fail ξ`),错误由规则给出 `EUser` |
| 通用效应 `op : A → T B`(Plotkin–Power) | `POp k a κ`,参数并入 `Op Σ`,结果类型 `Out Σ` | 精确 | RULES.md 第 0 节"参数直接放进 `Opₖ`" |
| 处理器 = 自由模型上的折叠 | `Bridge.denote`(解释到 `PEff Store`);EDSL 的各个解释(JS 生成、演算执行、静态分析、初始 AST,EDSL.md 3.1) | 精确 | `denote` 就是一个处理器,把每个操作解释成存储上带逆的部分函数。tagless final 的签名是处理器的类型,每个解释是一个处理器 |
| 处理器的正确性 / 两个处理器一致 | `Bridge.lone_denote`:单独激活时,规则执行与 `denote` 一致 | 近似 | 一边是小步规则(`load_step`),一边是折叠。领域里通常证"处理器满足方程",这里证的是两种解释在单 fiber 情形一致 |
| 处理器把效应解释到某个单子 | `Service.run : Op → Tok → S → option (S × (S → S) × Out)` | 近似 | 操作的解释落在"带逆的部分状态单子"里。用户**不能**写处理器:全系统只有运行时这一个处理器,服务的 `run` 是它的参数 |
| 程序看不到状态、只能按结果分支 | RULES.md 第 1 节;EDSL.md 3.2 用 HOAS 与参数性保证 | 精确 | 自由单子的程序本来就只能经续延接收结果。OCaml 原型 `edsl/ocaml/sym.ml` 用 functor 隐藏 `value` 的表示,即参数性 |
| tagless final 与初始代数的对应 | EDSL.md 3.3:签名写成 record,`Prog` 是初始代数 | 精确 | `∀ repr. Sym repr ⇒ repr` 与自由单子同构(Church 编码),这是标准结论 |

### 2.2 撤销日志与终结器(F1)

| 领域概念 | 演算中的对应 | 关系 | 说明 |
|---|---|---|---|
| 写入单子,幺半群取逆的复合 | `acc : list Undo`;§3.1 的 `Twisted.v`、`EffectFun.v`;`Bridge.uinterp` | 精确 | 累加器是一个写入单子的日志,幺半群是 `Γ → Γ` 在复合下的反幺半群(LIFO)。`uinterp` 把日志读成存储上的映射 |
| 按足迹分级的单子(Katsumata) | `Bridge.distinct_keys`(定理 45)、`LocalAt` | 近似 | 若把操作按所触及的键集合分级(幺半群 `(P(K), ∪)`),定理 45 就是"足迹不相交则可交换"。演算没有把分级写进类型,而是在服务层作为引理 |
| 效应不相交 ⇒ 不干扰(Lucassen–Gifford) | `distinct_keys`;`CoPair` 与 `Covers G`(`Recovery.v`、`Summary.v`) | 近似 | 两者都用效应判断交换。演算更细:同一个键上也只要求"可能相遇"的操作对满足 `RevertIndep`/`Commute`,而不是整键互斥 |
| 效应安全:类型中没有的效应不会发生 | `Ordering.value_moves`、`decl_step`、`decl_reachable`(不变式 `Decl`:`UOp` 撤销项只出现在声明或提供该键的 fiber 中) | 近似 | 形状相同:"只有声明了键的 fiber 能改这个键的值"。但演算的保证由语义给出(`load_step` 对未声明的键直接失败 `EUnresolved`),不是类型 |
| `bracket` / 获取与登记释放原子 | `load_step` 的 `POp` 分支:`run` 一次同时给出新状态与逆,写回与压栈在同一步 | 精确(设计层面) | Marlow 等要防的"获取之后、登记之前被打断",在演算里不可能发生。D6 的 `prepare`/`commit` 把这一点交给运行时保证 |
| 不恢复的续延仍要终结(深终结、`finally`) | `PFail` 与操作失败都转入 `Unloading acc ω (Some ξ)`,随后 `L-Undo` 逐项撤销 | 精确 | 失败就是不恢复的操作。演算中失败一定触发全部已登记逆的执行,这正是审计项 R1"含中途抛错"要的性质 |
| Runner 保证终结代码执行(λcoop) | `Termination.termination` 加 `Progress.progress`:卸载一定走完;`Recovery.recovery_exact`:走完后存储 ≃ 影子 | 近似 | λcoop 保证终结代码**运行**;演算还保证终结**正确**(≃ 略去该 fiber 的执行),代价是逆只能由服务操作给出,用户不能写任意终结器(DESIGN 差异 f) |
| 可逆效应(逆箭头) | `Service.Witnessed`、`WellBehaved` | 形似 | Heunen 等研究的是整个计算可逆;演算只要求每个操作附带一个逆,而且逆只在应用处成立。可逆计算一侧见 reversibility.md |

### 2.3 依赖与余效应(F4)

| 领域概念 | 演算中的对应 | 关系 | 说明 |
|---|---|---|---|
| 平坦余效应 / 隐式参数集合 | `Component.deps`(`d(c)`) | 精确 | 组件要求上下文提供的键集合,在组合下取并 |
| 余效应环境(满足需求的上下文) | `View ω : d → pid`;`binds` | 精确 | ω 是"隐式参数的当前绑定",按 pid 记录 |
| 需求在使用前得到满足 | `Ordering.begin_requires_deps`:`L-Begin` 时每个依赖都由 Active 的提供者绑定 | 精确 | 静态余效应系统在类型检查时保证;演算在运行期以 `target ≠ ⊥` 作为 `L-Begin` 的前提 |
| 上下文在计算期间一直可用(词法作用域包含) | `Ordering.provider_outlives`、`unload_waits` | 近似 | 隐式参数的 `let ?x = v in e` 由词法嵌套保证 `e` 运行时 `?x` 还在。演算的组件不是词法嵌套的,所以用守卫 `held` 在动态上恢复这一性质 |
| 结构余效应,按变量分级 | `OpAt k a P`(`Recovery.v`):每个键上可能执行的操作集合;EDSL 的 `ops_k` 分析 | 近似 | 把"每个键上的操作集合"当作按键的分级,就是结构余效应;`CoPair` 与 `Covers G` 是在两个组件的分级上做的检查。现在它是 Rocq 中的谓词,不是类型 |
| 分级半环中的"恰好一次" | `TotalProv`(`AllDoneProv`,`Confluence.v`)加不变式"一个累加器中每个键至多有一个 `UProv`" | 近似 | `p(c)` 中的每个键在每条到 `Done` 的路径上**恰好** provide 一次,对应 Granule 自然数半环里的分级 1 |
| 参数化单子:前后条件 | `PProvide` 改变"已提供的键集合";`POp` 对自己的键要求已提供(`load_step` 中 `owner b = n`) | 近似 | 用 Atkey 的 `M i j a`,`i`、`j` 是 provide 前后的键集合,即可在类型里表达这两条。演算目前在运行期检查 |
| 可选的余效应(用量区间 `[0,1]`) | `Ext/Optional.v` 的可选依赖,按在场集选变体 | 近似 | 分级取区间时,"可能用到"就是 `[0,1]`。扩展中程序按在场集分支,比单纯的用量标注多了"出现或消失时重载" |
| 效应实例重命名 / 命名处理器 | `Derived.scoped`(isolate 读作键重命名)、`CoPairAny` | 形似 | 同一组件在多个作用域中运行,相当于同一效应的多个实例;Effekt 的能力实例、Koka 的 `mask` 处理的是类似问题 |
| 子计算继承父上下文(动态作用域) | 演算中**没有**:子组件只看到自己的 `d`。Cordis 的 `locate` 沿父链查找 provision(DESIGN 2.1 节 e) | 无对应 | Cordis 的写法就是隐式参数的动态作用域,而子 fiber 不在父 provision 的 `dependents` 中,由此产生了 `teardown-order.spec.ts` 确认的清理顺序问题 |

### 2.4 运行期效应(F8)

| 领域概念 | 演算中的对应 | 关系 | 说明 |
|---|---|---|---|
| 安装中断处理器,中断到来时运行(异步效应) | `Component.reacts`;`O-React n i` | 近似 | 处理器在 Active 期间"安装",事件到来时以子 fiber 运行。演算的事件来自编排输入,没有信号与中断的往返 |
| 处理器调用的效应可以单独撤销 | `Runtime.effect_exact`、`effect_exact_inactive` | 无现成对应 | 处理器文献里没有"撤销某一次处理器调用的全部效应、且与其他并发计算无关"的定理。这是演算的新东西 |
| 高阶操作展开成一阶操作(Hefty) | `ctx.effect` 的子效应树在演算中编码成 `O-React`/`Spawn` 的子 fiber,累加器不改成树(RULES 第 5 节第 4 条) | 近似 | 把带子计算的操作展开为"spawn 一个组件 + 一个 `USpawn` 撤销项";DESIGN 3.2 节的玫瑰树 `T ≔ μT. List((Σ → Σ) + T)` 是未展开的形式 |
| 作用域效应的作用域 | `USpawn m` 在父累加器中的位置;`Ordering.parent_waits_child` | 近似 | 子 fiber 的生命期被嵌在父累加器的一段里,父撤销到这一项时先等子 fiber 移除,作用域按 LIFO 关闭 |

## 3. 差异

### 3.1 演算有,该领域没有的

1. **撤销是一等公民,而且是精确的。** 效应文献里的终结器是用户写的任意代码,只保证运行,不保证"撤销后等于没做"。
   演算的 `recovery_exact` 是关于影子执行的等式,还允许别的 fiber 在其间任意交错。
2. **共享状态上的并发与交换性按操作对给出。** 效应系统的交换判据多是"足迹不相交";演算允许同一个键上的操作
   相遇,只要求 `CoPair` 内的对满足 `RevertIndep`(恢复)或 `Commute` 等(合流)。
3. **余效应的满足是动态、反应式的。** 静态余效应系统假定上下文在检查时就确定;演算中提供者会出现、消失、替换,
   依赖者靠 `target` 的变化重新加载(`L-Leave`、`L-Divert`、`L-Begin`)。"需求在整段运行期间被满足"靠
   `provider_outlives` 与守卫 `held` 保证。论文称其为"反应式余效应",这在 Petricek 一系中没有对应。
4. **用户不能写处理器。** 全系统只有一个处理器(运行时),服务操作的语义 `run` 是固定参数。合流与恢复都依赖这一点:
   若插件能拦截别人的操作,`CoPair` 这种按程序文本计算的相遇关系就不成立。

### 3.2 该领域有,演算没有的

1. **效应与余效应进入类型。** 演算的组件义务(访问的键在 `d ∪ p` 中、provide 的键在 `p` 中、`TotalProv`、
   `Covers G`)要么在运行期检查(失败为 `EUnresolved`、`EConflict`),要么是关于程序文本的 Rocq 谓词,
   没有类型系统。
2. **效应多态。** `Prog` 是单态的;组件的键集合是常量列表。
3. **用户定义的处理器、多次恢复、深浅处理器。** 演算不需要,而且需要排除(见 3.1 第 4 条)。
4. **定量分级。** 演算只区分"用"与"不用",不计次数;唯一需要计数的地方("恰好 provide 一次")由不变式与
   `TotalProv` 表达。
5. **高阶操作。** 演算里没有带子计算的操作,一律展开成 spawn(见 2.4)。

## 4. 回答重点问题

### 4.1 `Prog` 作为自由单子,处理器视角能给什么

1. **一个统一的折叠。** `denote`、EDSL 的分析解释、初始 AST 解释、`Recovery` 中的 `OpAt`、`Termination` 中的
   `Bounded`、`Confluence` 中的 `AllDoneProv` 都是对 `Prog` 的结构递归。把它们写成同一个 `fold` 的实例,
   可以一次证明"分析解释给出的键集合与 `OpAt` 一致"这类引理,也使 EDSL 的可信基缩小到"Racket/OCaml 的
   AST 解释与 Rocq 的 `Prog` 一致"这一处。
2. **把规则读成处理器。** `load_step` 对单个 fiber 是一个小步处理器:状态是 `(γ, acc, ω)`,处理 `POp` 时调用
   `run` 并压入逆。`lone_denote` 是两个处理器(小步的与折叠的)在单 fiber 情形一致。领域里的"处理器正确性"
   可以作为陈述 `lone_denote` 推广形式的语言。
3. **作用域操作的展开。** `ctx.effect(body)` 是高阶操作。Hefty 代数的做法说明,把它展开成"spawn 一个匿名组件"
   是有原则的,而且展开可以按操作分别定义。这为 EDSL 提供 `effect`/`bracket` 语法而不改演算给出了依据。
4. **处理器视角给不了的。** 并发交错、守卫 `held`、`target` 驱动的重载都不在自由单子之内,它们属于运行时这个
   "处理器"的内部,而且这个处理器不是组合式的(它同时运行许多程序并让它们共享状态)。所以处理器视角帮助
   组件一侧,不帮助元理论的主体。

### 4.2 能否用类型系统静态保证两条性质

**(1) 实际依赖与提供和声明的 `d(c)`、`p(c)` 一致。**

可以,而且大部分已经接近完成:

- **上界(用到的 ⊆ 声明的)**:OCaml 原型 `edsl/ocaml/sym.ml` 已经用多态变体的幻影类型 `('a, 'o, 'p) prog`
  记录可访问的键,插件标注成闭的变体,用到别的键就是类型错误。这就是 Koka 式的效应行,只不过行是闭的、
  不做推断。Racket 版在展开期检查(`define-plugin`)。
- **前后条件(只在 provide 之后才操作自己的键,每个键至多 provide 一次)**:需要参数化单子(Atkey)或带索引的
  归纳类型。`load_step` 的解析规则恰好是:`k ∈ d` 时查 ω,否则要求 `B k` 的 owner 是自己。所以类型
  `IProg (D : 依赖) (S : 已提供)` 中 `POp k` 要求 `k ∈ D ∪ S`,`PProvide k` 要求 `k ∉ S` 并把 `S` 变为 `k :: S`,
  这与规则逐字对应。
- **下界(声明的 `p` 在每条路径上都提供,即 `TotalProv`)**:让 `PDone` 只在 `S = p(c)` 时可构造即可。
  这是"恰好一次"的线性要求,Granule 用自然数分级表达,这里用索引更简单。
- **声明了却不用的依赖**:幻影类型只给上界。多声明的依赖不会破坏任何定理,但会让组件无谓地等待、
  重新加载,并让 `held` 多挡住提供者的卸载。可以由分析解释报告,不必进类型。
- **相遇受控(`Covers G`)**:这是两个组件之间的性质,进不了单个组件的类型。但若每个组件的类型带上按键的
  操作集合(结构余效应),`Covers G` 就是链接期对标注的检查:`ops_c(k) × ops_c'(k) ⊆ G`。在 OPLIB 的贡献
  模型下 `G` 是全关系,这一检查消失。

**(2) 所有副作用都经过带逆的 `Op`,不会漏记进 `acc`。**

- **在演算内部这是构造给出的**:`Prog` 只有五个构造子,`POp` 一步同时写回状态并压入逆。演算里不存在
  "漏记"的程序。
- **问题在宿主语言**。真实插件是 JS,可以不经 `Op` 做任何事。要静态保证,需要宿主层面"没有环境权限":
  - **纯宿主 + 参数性**:Haskell 中 `∀ m. CordisOps m ⇒ m ()` 的值只能调用 `CordisOps` 的方法。
    OCaml 原型靠 functor 隐藏 `value` 得到类似效果,但 OCaml 本身的效应(引用、IO、OCaml 5 的未定型效应)
    不受追踪,所以只是近似。
  - **效应类型**:在 Koka 中,把插件体的类型定为效应行恰为 `<cordis>`(不含 `io`、`st<global>`、`ndet`),
    效应安全定理就给出"所有效应都经过 cordis 的操作"。
  - **能力**:Effekt 的读法最贴切:插件体只拿到 `d ∪ p` 中每个键的能力对象,没有其他权限。
    生成的 JS 若只把这些能力交给插件,再配合冻结内建对象与全局对象(对象能力的做法),
    插件代码就无从触及别的状态。
- **剩下的缺口是载荷**。EDSL 的 `(js "...")` 载荷(工具的 `execute`、路由处理器)是不透明的 JS,
  它们在运行期执行,能做任何事。能力传递能限制载荷拿到什么,但载荷对外部世界(文件、子进程、网络)的作用
  需要的是 `resource` 原语(EDSL.md 第 6 节),不是逆。
- **逆是否正确不归类型管**。类型只能保证"每个效应都是某个服务的操作";该操作的逆是否真的撤销它
  (`Witnessed`),是服务作者的义务(`Summary.Revertible`)。OPLIB 的贡献模型让这一义务随构造成立,
  所以"能力化的 EDSL + 贡献模型"在组件与服务两侧合起来封闭。

### 4.3 与 PLUGIN-AUDIT.md 中问题的关系

| 审计中的写法 | 用效应/余效应的语言说 | 对应的静态手段 |
|---|---|---|
| 未注入读取(`ctx.get`,S1;差异 m) | 余效应**少报**:实际需求不在声明的 `d` 内 | 余效应推断:从代码中收集读取的键,与 `inject` 比较;能力传递让未声明的键根本拿不到 |
| 按"服务在不在"分支(C2) | 可选余效应,分级 `[0,1]`,且程序在分级上分支 | `Ext/Optional.v` 的可选依赖;类型中把它标成 `'o`(OCaml 原型已有 `read_opt`) |
| 子 fiber 不经 inject 读父 fiber 的服务(DESIGN 2.1 节 e) | 隐式参数的**动态作用域**:子计算从调用者的上下文取值,却不出现在自己的余效应里 | 要求子组件把它声明为依赖(演算的做法),或在类型上让父 provision 作为能力显式传给子组件 |
| 猴补丁服务实例或原型(S3) | 对服务状态这个"区域"做了**不经操作接口**的写效应(Talpin–Jouvelot 的区域效应) | 能力只暴露操作,不暴露服务对象;冻结服务对象与原型 |
| `globalThis` 跨实例共享(S3) | 写全局状态,Koka 中的 `st<global>`;演算中是没有的 `Amb`(差异 m) | 效应行中不给全局状态;生成的代码在冻结的全局对象下运行 |
| `internal/*` 元层钩子(S3) | 用户**安装处理器**去拦截别的插件的操作 | 签名中不提供;这正是 3.1 第 4 条要排除的东西 |
| 把效应挂到别人的 ctx 上(S3) | 用别人的能力执行效应,效应记进了别人的累加器 | 能力不可伪造、不外传;交集生命期扩展(`Ext/Intersect.v`)给出受控的替代 |
| 登记推迟、中途抛错泄漏(R1) | `bracket` 被破坏:获取与登记释放之间隔着 `await` 或可能抛错的代码 | 操作原子地返回逆(演算的 `POp`、D6 的 `commit`);EDSL 中所有资源经 `resource` 原语 |
| 运行期资源不归 fiber、在 promise 回调里往主 fiber 挂效应(R2) | 能力**逃出**作用域:回调捕获了 fiber 的上下文,在 fiber 的加载阶段结束后才用它 | 捕获类型(Boruch-Gruszecki 等)或 Effekt 的二等能力:禁止加载期能力被存进运行期回调;运行期效应只能用反应子 fiber 自己的能力 |
| 登记名撞车(R3) | 两个组件在同一键上的分级相交且不在 `G` 内 | 链接期检查 `ops_c(k) × ops_c'(k) ⊆ G`;贡献模型下消失 |

要点:审计的"不在模型内"五类中,猴补丁、`globalThis`、`internal/*`、挂到别人的 ctx 上四类,在能力化的宿主里
**写不出来**;编排者一类是另一种义务(`Ext/Orchestrator.v`),与效应类型无关。R1、R2 两类泄漏在演算中由
构造排除,在宿主中要靠"操作原子地给出逆"和"能力不逃逸"。

## 5. 候选课题

### 课题 A:带索引的程序类型 `IProg`,组件义务随类型成立

- **目标**:在 Rocq 中定义带索引的程序 `IProg D P S`(`D` 依赖,`P` 声明的提供集合,`S` 已提供的键),
  证明良类型的组件满足 `Summary.v` 中与程序文本有关的全部组件义务,并且不会以 `EUnresolved` 失败、
  不会因重复 provide 以 `EConflict` 失败。
- **做法**:
  1. 构造子:`IDone : IProg D P P`;`IOp k a κ` 要求 `k ∈ D ∪ S`;`IProvide k s P'` 要求 `k ∈ P`、`k ∉ S`,
     后继为 `IProg D P (k :: S)`;`ISpawn`、`IFail` 不改索引。
  2. 擦除函数 `erase : IProg D P S → Prog`。证明 `erase` 的结果满足 `AllDoneProv`(对 `P \ S` 中每个键),
     从而对 `S = []` 给出 `TotalProv`。
  3. 引理:良类型 fiber 的每次 `L-Step` 不走 `fail EUnresolved`,`PProvide` 分支不走 `fail EConflict`。
     这需要用到 `WF` 中"现存 fiber 的 `p` 两两不相交"与"每个键至多一个 `UProv`"。
  4. 可选:再加一个索引 `O : K → list Op` 记录每个键上的操作集合,证明 `OpAt k a (erase P) → In a (O k)`,
     从而 `Covers G` 归结为对标注的有限检查。
- **预期产出**:`theories/Ext/Typed.v`(核心不导入它);一个把 `Examples/Basic.v` 的组件改写成 `IProg` 的例子;
  OCaml 原型 `sym.ml` 的类型与 `IProg` 的对应说明。
- **风险**:续延 `κ : Out Σ → IProg …` 要求所有分支以同一个索引结束,对"不同分支提供不同键"的程序不友好
  (但 `TotalProv` 本来就要求每条路径都提供全部键,所以这正是要的)。键集合用列表时,索引的相等要处理排列,
  可以把 `S` 取为按 `P` 的顺序的布尔向量来回避。
- **工作量**:中。

### 课题 B:能力化的 EDSL 运行时,把"所有效应都经过 `Op`"变成宿主层面的保证

- **目标**:让 EDSL 生成的插件在宿主中只拥有 `d ∪ p` 中键的能力,使审计 S3 的四类写法(猴补丁、`globalThis`、
  `internal/*`、挂到别人的 ctx 上)无法写出;载荷对外部世界的作用只能经 `resource` 原语。
- **做法**:
  1. `edsl/runtime/rt.js` 不再把 Cordis 的 `ctx` 交给生成的代码,而是为每个声明的键构造一个只含其操作的
     能力对象(Effekt 的读法);反应子 fiber 得到自己的一组能力。
  2. 载荷在冻结了内建对象与全局对象的环境中求值(对象能力的标准做法),只接收显式传入的能力与 `resource` 句柄。
  3. 在 `edsl/test/run.js` 中加反例:试图改服务原型、写全局对象、注册 `internal/*` 钩子、在回调中使用加载期能力,
     都应当失败或被拒绝。
  4. 对照审计中各插件的 S3 证据,逐条说明改写成 EDSL 后哪些写法消失、哪些功能需要宿主新原语。
- **预期产出**:修改后的 `rt.js` 与测试;一份对照表,说明能力化之后汇总定理的第 0 层前提(S1、S3)哪些由运行时
  保证、哪些仍是信任边界。
- **风险**:冻结全局对象可能与 Cordis 或 dsh 宿主自身的做法冲突,需要只对载荷的求值环境生效;
  JS 中能力纪律可以被反射等手段绕过,保证是"诚实但出错的作者"级别,不是安全级别;载荷常常确实需要文件与网络,
  `resource` 原语的覆盖面决定可用性。
- **工作量**:中。

### 课题 C:结构余效应推断与跨插件相遇检查

- **目标**:对每个组件推断"每个键上的操作集合"这一结构余效应,并在链接期检查 `Covers G`;
  对现有 TS 插件,推断实际读取的键,与 `inject` 比较(S1)。
- **做法**:
  1. EDSL 一侧:分析解释已经计算 `ops_k`(EDSL.md 3.1);把结果写成每个组件的签名文件,链接期对整张组件表
     计算 `CoPair` 并对每个服务的 `G` 检查。用 Rocq 一侧的 `OpAt` 定义作为规格,写一个小引理说明分析解释与
     `OpAt` 一致(依赖课题 D 的 `fold`,或直接对初始 AST 证)。
  2. TS 一侧:在 `checker/` 中加一个静态扫描,收集 `ctx.get('k')`、`ctx.k` 的字面键与工具名、provider id、
     provide 键,报告未注入读取与跨插件撞名。审计"对形式化的影响"第 3 条已经指出登记名多为字面量。
- **预期产出**:EDSL 的链接期检查;`checker` 的静态扫描报告,与 PLUGIN-AUDIT 的人工结论对比漏报与误报。
- **风险**:TS 中的动态键与间接访问会漏报,只能作为 lint;`G` 按服务给出,服务一侧需要写出机器可读的 `G`。
- **工作量**:小到中。

### 课题 D:`Prog` 的通用折叠与 EDSL 的对应定理

- **目标**:在 Rocq 中定义 `Prog` 上的通用处理器 `fold`,把 `denote`、`OpAt`、`Bounded`、`AllDoneProv`
  的判定版本写成它的实例,并说明 EDSL 的初始 AST 解释产生的数据就是 `Prog`。
- **做法**:定义签名的代数 `ProgAlg R`,`fold : ProgAlg R → Prog → R`;证明 `denote = fold denoteAlg`
  (按定义展开即可);给出 `OpAt`、`Bounded` 的可判定版本并证明与归纳定义一致;把 OCaml 原型输出的 AST
  打印成 Rocq 项,在 Rocq 中对示例插件计算 `TotalProv` 与 `Bounded`。
- **预期产出**:`theories/Fold.v`;一个从 EDSL 示例到 Rocq 的端到端检查。
- **风险**:续延是函数,AST 打印只能对有限的结果类型展开分支;收益主要是工程上的,理论上没有新东西。
- **工作量**:小。

### 课题 E:`effect`/`bracket` 作为高阶操作,展开成 spawn

- **目标**:给 EDSL 加 `effect(body)`(对应 Cordis 的 `ctx.effect`)与 `bracket(acquire, release, body)`,
  按 Hefty 代数的思路展开成演算已有的 `PSpawn` 加匿名组件,不改演算。
- **做法**:定义带高阶操作的源语言 `HProg`,展开函数 `elab : HProg → (Prog × 新组件表)`;证明展开保持
  `Bounded`、秩(新组件只被父组件 spawn,秩为父的秩加一)、`TotalProv`;由 `parent_waits_child` 得到
  "body 的效应在 release 之前撤销"的作用域性质。
- **预期产出**:`theories/Ext/Scoped.v`;EDSL 中的 `effect` 语法。
- **风险**:匿名组件让组件表依赖于程序,`prog : C → Component` 需要扩成可生成的;启动时 spawn 的子 fiber
  不能单独 dispose(差异 q、`SLInv`),所以 `effect` 的单独撤销只在反应中可用,这一限制要写进语法。
- **工作量**:中。

### 排序

| 课题 | 贴合现有成果 | 收益 | 工作量 |
|---|---|---|---|
| A 带索引的程序类型 | 高:直接产出 `Summary.v` 的前提 | 组件义务从谓词变成类型 | 中 |
| B 能力化运行时 | 高:接 `rt.js` 与 PLUGIN-AUDIT | 第 0 层前提由运行时保证 | 中 |
| C 余效应推断与相遇检查 | 高:接 `OpAt`、`CoPair`、审计第 3 条 | 找真实 bug | 小到中 |
| D 通用折叠 | 中 | 缩小 EDSL 可信基 | 小 |
| E 高阶操作展开 | 中 | 语法便利,`ctx.effect` 进模型 | 中 |

## 6. 参考文献

核实方式:用网络检索核对作者、题目、会议或期刊、年份。全部检索于 2026-11-25。

1. J. M. Lucassen, D. K. Gifford. Polymorphic Effect Systems. POPL 1988, pp. 47–57. 已核实(有一处二手引用把题目写作 "Polymorphic effect analysis",以会议记录为准)。
2. J.-P. Talpin, P. Jouvelot. The Type and Effect Discipline. LICS 1992, pp. 162–173;期刊版 Information and Computation 111(2):245–296, 1994. 已核实。
3. D. Leijen. Koka: Programming with Row Polymorphic Effect Types. MSFP 2014, EPTCS 153(arXiv:1406.2061). 已核实(EPTCS 卷号据 arXiv 记录,检索摘要中卷号被截断,作者页注明早先版本有一条引理有误)。
4. D. Marino, T. Millstein. A Generic Type-and-Effect System. TLDI 2009, pp. 39–50. 已核实(页码来自二手引用)。
5. S. Katsumata. Parametric Effect Monads and Semantics of Effect Systems. POPL 2014, pp. 633–645. 已核实。
6. R. Tate. The Sequential Semantics of Producer Effect Systems. POPL 2013. 已核实(只核对了题目、作者与会议)。
7. R. Atkey. Parameterised Notions of Computation. Journal of Functional Programming 19(3–4):335–376, 2009. 已核实。
8. D. Orchard, P. Wadler, H. Eades III. Unifying Graded and Parameterised Monads. MSFP 2020, EPTCS 317, pp. 18–38. 已核实。
9. T. Petricek, D. Orchard, A. Mycroft. Coeffects: Unified Static Analysis of Context-Dependence. ICALP 2013, LNCS 7966, pp. 385–397. 已核实。
10. T. Petricek, D. Orchard, A. Mycroft. Coeffects: A Calculus of Context-Dependent Computation. ICFP 2014, pp. 123–135. 已核实。
11. J. R. Lewis, J. Launchbury, E. Meijer, M. B. Shields. Implicit Parameters: Dynamic Scoping with Static Types. POPL 2000, pp. 108–118. 已核实(不同来源作者顺序不同)。
12. T. Uustalu, V. Vene. Comonadic Notions of Computation. ENTCS 203:263–284, 2008. 已核实(所属研讨会未能确认)。
13. D. Orchard, V.-B. Liepelt, H. Eades III. Quantitative Program Reasoning with Graded Modal Types. PACMPL 3(ICFP), Article 110, 2019. 已核实。
14. M. Gaboardi, S. Katsumata, D. Orchard, F. Breuvart, T. Uustalu. Combining Effects and Coeffects via Grading. ICFP 2016, pp. 476–489. 已核实。
15. G. Plotkin, J. Power. Algebraic Operations and Generic Effects. Applied Categorical Structures 11:69–94, 2003. 已核实。
16. G. Plotkin, M. Pretnar. Handlers of Algebraic Effects. ESOP 2009, LNCS 5502, pp. 80–94;期刊版 Handling Algebraic Effects, LMCS 9(4:23), 2013. 已核实。
17. A. Bauer, M. Pretnar. Programming with Algebraic Effects and Handlers. Journal of Logical and Algebraic Methods in Programming 84(1):108–123, 2015. 已核实。
18. O. Kammar, S. Lindley, N. Oury. Handlers in Action. ICFP 2013, pp. 145–158. 已核实。
19. W. Swierstra. Data Types à la Carte. Journal of Functional Programming 18(4):423–436, 2008. 已核实。
20. O. Kiselyov, H. Ishii. Freer Monads, More Extensible Effects. Haskell 2015, pp. 94–105. 已核实。
21. N. Wu, T. Schrijvers, R. Hinze. Effect Handlers in Scope. Haskell 2014. 已核实(页码各来源不一,未列)。
22. M. Piróg, T. Schrijvers, N. Wu, M. Jaskelioff. Syntax and Semantics for Operations with Scopes. LICS 2018, pp. 809–818. 已核实。
23. C. Bach Poulsen, C. van der Rest. Hefty Algebras: Modular Elaboration of Higher-Order Algebraic Effects. PACMPL 7(POPL), Article 62, 2023. 已核实。
24. D. Ahman, M. Pretnar. Asynchronous Effects. PACMPL 5(POPL), Article 24, 2021. 已核实。
25. S. Marlow, S. Peyton Jones, A. Moran, J. Reppy. Asynchronous Exceptions in Haskell. PLDI 2001, pp. 274–285. 已核实(检索结果未直接出现 "bracket" 一词,文中用 `block`/`unblock` 讲资源的获取与释放)。
26. D. Leijen. Algebraic Effect Handlers with Resources and Deep Finalization. Microsoft Research 技术报告 MSR-TR-2018-10, 2018 年 4 月. 已核实。
27. D. Ahman, A. Bauer. Runners in Action. ESOP 2020, LNCS, pp. 29–55, DOI 10.1007/978-3-030-44914-8_2. 已核实(LNCS 卷号未核对,故未列)。
28. K. C. Sivaramakrishnan, S. Dolan, L. White, T. Kelly, S. Jaffer, A. Madhavapeddy. Retrofitting Effect Handlers onto OCaml. PLDI 2021. 已核实。
29. J. I. Brachthäuser, P. Schuster, K. Ostermann. Effects as Capabilities: Effect Handlers and Lightweight Effect Polymorphism. PACMPL 4(OOPSLA), 2020. 已核实。
30. S. Lindley, C. McBride, C. McLaughlin. Do Be Do Be Do. POPL 2017, pp. 500–514. 已核实。
31. A. Boruch-Gruszecki, M. Odersky, E. Lee, O. Lhoták, J. Brachthäuser. Capturing Types. ACM TOPLAS 45(4), Article 21, 2023. 已核实。
32. M. S. Miller. Robust Composition: Towards a Unified Approach to Access Control and Concurrency Control. 博士论文, Johns Hopkins University, 2006. 已核实。
33. S. Maffeis, J. C. Mitchell, A. Taly. Object Capabilities and Isolation of Untrusted Web Applications. IEEE S&P 2010, pp. 125–140. 已核实。
34. C. Heunen, R. Kaarsgaard, M. Karvonen. Reversible Effects as Inverse Arrows. MFPS 2018, ENTCS 341:179–199. 已核实。
35. 本仓库所依据的论文 *A Programming Paradigm for Spatiotemporal Composability*(arXiv:2608.25512v1)。按 docs/DESIGN.md 引用,未在网上另行核实。
