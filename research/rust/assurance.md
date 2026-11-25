# 保证手段:让 Rust 版 Cordis 与 Rocq 演算保持一致

本文是 [PLAN.md](PLAN.md) 问题 (d) 的报告:Rust 版 Cordis 写出来以后,用什么手段让它和 `theories/` 中的演算
保持一致。它接着 [../verification.md](../verification.md) 往下写。那份报告讨论的是 TS 版 Cordis,结论是
lockstep 测运行时、证明分四档、第 4 档(Iris 精化)没有地基。这里不重复那些内容,只回答换成 Rust 之后哪些地方变了:

1. Rust 有哪些现成的演绎验证工具,哪一个最可能证明"Rust 控制层精化 `Calculus.step`";
2. 有界检查与测试工具(Kani、loom、shuttle、proptest、cargo-fuzz、Miri)各自能查什么;
3. Rocq 与 Rust 之间有哪些桥(抽取、反向翻译),各条路线的代价与可信基;
4. Rust 版控制层怎样组织,上面这些工具才用得上。

工具现状均于 2026-11-25 前检索核对,版本号取自 crates.io 与各项目发布页。核对不了的在正文与第 5 节标"未核实"。

## 0. 结论先行

**能用来证明的工具都不碰 async。** 2026 年 10 月的 RefinedRust 后续论文明确说,trait object 与 async Rust
"据作者所知,目前没有任何 Rust 验证工具支持" [Gäher 2026];Verus 的特性表把 async 函数、async 块、`await`
都列为不支持(trait object 列为部分支持)[Verus 特性表];Aeneas 不支持 unsafe 和并发 [Aeneas README];
Kani 不支持并发代码 [Kani 对比页]。所以"证明 Rust 版 Cordis 整体精化演算"在 2026 年没有现成工具可用,
和 TS 版的第 4 档处境相同。

**出路是把演算放进一个同步、一阶、不含 IO 的纯核。** 演算本身已经是这个形状:
`step : State → Label → option State` 是一个确定的全函数,异步性已经编码成标签(落地是 target 变化后的
`L-Step`,放弃是 `L-Divert`,见 `may_step` 与 DESIGN 差异 h)。Rust 版只要把控制层写成同样形状的纯状态机,
外面套一个异步外壳负责调度、调用服务、执行撤销句柄,验证工具就只需要面对纯核。这正是 verification.md
第 3 档"验证过的核心,不验证的外壳",换到 Rust 上可以走得更远:那里第 3 档只能靠抽取,这里可以手写纯核再证明它。

**推荐路线(按先后):**

| 步 | 做法 | 一致性来自 | 工作量 |
|---|---|---|---|
| 1 | Rocq 侧先做两件准备:可计算的精化版 `step`(有限映射、二进制数)与可判定的 `WF`;以及"控制投影"`ctl_step`,把服务状态和插件程序从 `step` 中剥出去,得到 Rust 核的精确接口(课题 V1、V2) | 证明 | 小到中 |
| 2 | Rust 手写纯核,对抽取出的 oracle 做 lockstep 差分测试(proptest-state-machine);外壳用 shuttle 查交错,服务用线性一致性测试查 D6(课题 V3) | 测试 | 中 |
| 3 | 用 Aeneas 把纯核翻译成 Rocq(或 Lean)中的纯函数,证明它与 `ctl_step` 一致(课题 V4)。Aeneas 的 Coq 后端不够用时,退到 Verus,规格照 `ctl_step` 手抄,再用第 2 步的 oracle 交叉检查规格 | 证明 | 中到大 |

不推荐把 Rocq 抽取出的 Rust 代码直接当生产核:现有的 Rust 抽取 [rocq-rust-extraction] 用区域分配器
(bumpalo)管理内存、闭包一律装成 `&dyn Fn` [Annenkov 2022],适合短生命期的智能合约,不适合常驻的运行时。
但它很适合当**测试 oracle**:生成的 Rust 与被测核在同一个 `cargo test` 里运行,每个测试用例一个区域,省掉跨语言胶水。

## 1. 领域概览

### 1.1 出发点:`Calculus.v` 的 `step` 能算吗,能抽取吗

能。`step`、`load_step`、`undo_step` 都是 `Definition`,只用模式匹配、`existsb`、`nth_error`、可判定相等
(`K_eq_dec`、`Nat.eqb`、`view_eq_dec` 以 `Defined` 结束),没有 `Prop` 参与计算。`run_labels` 与
`lifecycle_labels` 也可计算。仓库里目前没有任何 `Extraction` 命令(已检索)。直接抽取能跑,但有六处
不适合拿去当 oracle 以外的东西,也影响任何"Rust 核对应 `step`"的陈述:

1. **状态里的映射是函数。** `fibers : nat → option Fiber`、`binds : K → option Binding`,更新用 `fupd`、`bupd`
   套一层闭包。抽取后每次查找要穿过此前全部更新,代价随历史增长。
2. **鬼字段也在算。** `oplog`、`inilog` 规则不读,但 `log_op`、`log_ini` 每次都给它们再套一层闭包,内存只增不减。
3. **全名扫描。** `names γ = seq 0 (next γ)`,`relied`、`has_child`、`conflict` 都对所有曾分配的名字扫一遍;
   `held` 对累加器里每个 `UProv` 调一次 `relied`。
4. **一元自然数。** `next`、pid、令牌都是 `nat`,抽取要重映射到机器整数,重映射表进入可信基。
5. **高阶数据。** `Prog` 的 `POp k a κ` 带续延 `κ : Out Σ → Prog`;`UOp` 带逆 `g : St Σ → St Σ`。
   OCaml 里没有问题;Rust 里只能是装箱闭包;对 Aeneas、hax 这类翻译工具,数据里的闭包是难点(见 1.2)。
6. **≃ 是命题。** `st_eq : St → St → Prop`,做 oracle 时比较服务状态要有可判定的版本(verification.md 差异 3 已指出)。

这六点决定了课题 V1 要做什么:写一个用有限映射、去掉鬼字段、整数用 `N` 的 `step_fm`,证明它与 `step`
在抽象函数下一致。不论最终走哪条路线,这一步都省不掉。

### 1.2 Rust 演绎验证工具

| 工具 | 做法 | 现状(2026-11) | async | trait object | 内部可变性 | 并发 | unsafe | 证明落在哪里 |
|---|---|---|---|---|---|---|---|---|
| Verus | 规格与证明写在 Rust 里,ghost/tracked 模式,SMT(Z3) | 滚动发布,最新 0.2026.11.22,`vstd` 2026-11-22 | 不支持 | 部分支持 | 用 `PCell` 加权限令牌代替 `UnsafeCell` | `spawn`/`join` 支持;tokenized state machine | 原始指针部分支持 | Verus 自身;语义基础 VerusBelt(Iris/Rocq) |
| Creusot | 翻译到 Why3 的 WhyML,预言(prophecy)处理可变借用 | 月度发布,`creusot-std` 0.15.0(2026-11-10,devlog 2026-11-20) | 未核实 | 未核实 | 未核实 | 0.9.0 起初步支持(带 ghost 的原子类型包装) | 由 Gillian-Rust 补 | Why3 与 SMT;语义基础 RustHornBelt |
| Prusti | 基于 Viper 的分离逻辑 | 自称原型;只从镜像页看到 2026 年有提交,维护状况未核实 | 未核实 | 未核实 | 未核实 | 未核实 | 不支持(以安全 Rust 为主) | Viper |
| Aeneas | 经 Charon 把 Rust 变成 LLBC,再函数式翻译成纯函数 | 活跃,无发布标签;后端 F*、Coq、HOL4、Lean,其中 Lean 与 HOL4 最成熟 | 不支持(并发整体不支持) | 未核实 | 不支持(ICFP 2022 论文的前提) | 不支持 | 不支持 | 目标证明助手;翻译本身未验证,借用检查部分有 ICFP 2024 的可靠性证明 |
| hax | 把 Rust 的函数式子集翻译到 F*、Rocq、Lean、SSProve、ProVerif | `hax-lib` 0.5.0(2026-11-09);Rocq 后端标为 Experimental;0.4 起 Lean 后端改走 Charon+Aeneas | 未核实(面向函数式子集,推测不支持) | 未核实 | 未核实 | 未核实 | 未核实 | 目标证明助手;F* 后端有 2026 年的语义缺口批评 [Kobeissi 2026] |
| rocq-of-rust | 从 THIR 深嵌入到 Rocq,单子化;再"链接"(类型类解析 trait)、"模拟"(改写成纯函数) | 活跃(3400+ 提交),无发布标签;要求 Rocq ≥ 9.0 且 < 9.1 | 未核实 | 未核实 | 未核实 | 未核实 | 深嵌入原则上可表达 | Rocq |
| Gillian-Rust | Gillian 平台上的半自动分离逻辑,嵌入 RustBelt 寿命逻辑与参数化预言;与 Creusot 混合 | PLDI 2025;README 自称不稳定的原型 | 未核实 | 未核实 | 是其目标之一(unsafe) | 未核实 | 支持(主要对象) | Gillian(OCaml)与 Z3 |
| RefinedRust | Rocq 中基于 Iris 的精化所有权类型,自动化来自 Lithium | PLDI 2024;OOPSLA 2026 加上 trait、闭包、迭代器、递归类型,验证了 ACE 安全监控器约 600 行内存子系统 | 不支持(论文自述) | 不支持(论文自述) | 未核实 | 未核实 | 支持 | Rocq(基础性证明) |

表中"不支持"凡出自 RefinedRust 论文的,是该文对全部工具的一般性陈述;它与 Verus 特性表"trait object 部分支持"
不一致,两者都照原文列出。

各工具与本课题相关的要点:

- **Verus** [Lattuada 2023;Lattuada 2024]。最成熟、自动化程度最高(据一份 2026 年的第三方综述,已在 Microsoft 与 Amazon 使用,未见一手来源)。它和本仓库最近的先例是
  **Anvil** [Sun 2024]:用 Verus 写 Kubernetes 控制器并证明 ESR(最终稳定协调),为此在 Verus 里自建了 TLA
  风格的时序逻辑嵌入,环境(API 服务器、网络、其他控制器、故障)建模为状态机,假设公平调度。增量计算报告
  ([../incremental.md](../incremental.md))已经把演算的收敛加合流对应到 ESR,所以 Anvil 是"Rust 实现的协调器
  证明了与本演算同类的性质"的现成例子。代价是规格写在 Verus 的逻辑里,与 Rocq 中的 `step` 是两份真相。
  语义基础方面,VerusBelt [Hance 2026] 在 Iris/Rocq 中给 Verus 的一大部分(含 cell、不变式、并发)证明了可靠性。
- **Aeneas** [Ho 2022;Ho 2024;Ho 2025]。输出是纯函数,可变借用变成"前向函数加后向函数"。对一个本来就是纯函数、
  不用内部可变性、不用 unsafe、不用并发的状态机,它的翻译结果几乎就是手写的 Rocq 函数,最适合与 `step` 直接比较。
  限制:循环中嵌套的 `return` 与跨层 `break` 暂不支持;泛型以可变引用实例化不支持;闭包、trait object、
  标准库映射类型的支持情况本次未核实。Coq 后端在 README 中列出,但成熟度没有说明,Lean 后端是主力。
- **hax** [Bhargavan 2025]。面向密码学代码的函数式子集;Rocq 后端由奥胡斯大学维护,标为实验性;
  2026 年的主要工作是把 Aeneas 接进 hax。对本课题,它在 Rocq 一侧没有比 Aeneas 更多的东西。
- **rocq-of-rust**。唯一一个和本仓库同在 Rocq、又能处理较完整 Rust 的翻译器,用于 revm 的验证。
  三段式(翻译、链接、模拟)意味着纯核要先手工证明"模拟"一步,工作量大;版本约束是 Rocq 9.0,本仓库用 9.1。
- **RefinedRust** [Gäher 2024;Gäher 2026]。在 Rocq/Iris 中给出基础性证明,而且是 Iris,也就是 verification.md
  第 4 档所需要的那种地基。但它不支持 async,用它证明纯核等于杀鸡用牛刀,用它证明外壳又缺 async。
- **Creusot** [Denis 2022]。自动化好,预言机制有 RustHornBelt 的语义基础;2026 年开始支持并发。证明落在 Why3,
  与 Rocq 的连接同样要手抄规格。

**哪一个最可能证明"Rust 控制层精化 `step`"。** 前提是控制层按 1.6 节组织成纯核。在这个前提下:

1. **Aeneas** 最可能,而且结论能落在 Rocq 里,直接与 `step` 写成一条定理。风险集中在 Coq 后端的成熟度,
   退路是用 Lean 后端,把 `ctl_step` 手抄到 Lean(多一份真相,但抄的是一个几百行的纯函数)。
2. **Verus** 其次:工具最成熟,不怕纯核里有 `Vec`、`HashMap` 等,还能做活性(Anvil)。代价是规格两份真相。
3. RefinedRust、rocq-of-rust 都能把结论落在 Rocq,但人工证明量大,用在纯核上不划算。
4. 如果目标是外壳(async、并发)的精化,2026 年没有候选,只能测试(1.4 节)。

### 1.3 语义基础与 unsafe

- **RustBelt** [Jung 2018]:λRust 上的第一个机器检查的 Rust 安全性证明,建在 Iris 上;对每个用 unsafe 实现的库,
  给出它要满足的验证条件,满足就算语言的安全扩展。
- **RustHorn** [Matsushita 2020] 把指针程序借所有权翻成 CHC,消去堆;**RustHornBelt** [Matsushita 2022] 用参数化预言
  在 RustBelt 模型里证明 RustHorn 式函数规格的可靠性,也覆盖 unsafe 实现的 API。Creusot 的预言、Gillian-Rust 的
  预言都以它为基础。
- **VerusBelt** [Hance 2026]:Verus 证明导向扩展(cell、不变式、并发)的语义基础。
- **别名模型**:Tree Borrows [Villani 2025] 用树替换 Stacked Borrows 的栈,在下载量最高的三万个 crate 上被判 UB 的
  测试少 54%,性质在 Rocq 中证明。**Miri** [Jung 2026] 按这类模型解释执行,检查 UB、数据竞争、弱内存;
  对确定性程序能找出全部事实上的 UB,对非确定性程序只跑一次。

对本课题的含义:RustBelt 的"unsafe 库负责满足语义验证条件,安全的客户代码由类型系统保证"与 DESIGN D6 的义务划分
同构(服务作者证明 `WellBehaved`、`RevertIndep`,演算的定理就对所有插件成立),但只是形似,两者保证的东西不同
(内存安全对生命周期性质)。实际建议是:**纯核与外壳都不写 unsafe**。插件以动态库或 WASM 形式加载时会有 FFI
边界(见 [plugins.md](plugins.md)),那部分交给 Miri 与 Kani,不进入与演算一致性的论证。

### 1.4 有界检查与测试

| 工具 | 查什么 | 现状 | 对本课题的用处与局限 |
|---|---|---|---|
| Kani | CBMC 上的有界模型检测;函数契约、循环契约 | 0.68.0(2026-09-16),ASE 2026 有论文;支持 trait object 与动态分派闭包 [VanHattum 2022] | 只做顺序代码,不支持并发;async 只有实验性的 `block_on`/`spawn`(2026 年状态未核实)。适合在纯核上对小规模状态穷举检查"`WF` 保持"等,见课题 V5 |
| loom | 在 C11 内存模型下穷举线程交错,带状态约简 | 0.7.3(2026-11-08),tokio-rs 维护 | 对象是原子操作与锁的实现;`SeqCst` 当作 `AcqRel`、不探索 load buffering,README 自认在这些地方不可靠。纯核不需要它;外壳若用无锁结构才用得上。对 async 的支持本次未核实 |
| shuttle | 随机调度与 PCT [Burckhardt 2010],自带 async 执行器 | 0.9.10(2026-11-05),awslabs | 不保证可靠,但能放大到大测试。最适合测外壳:让插件 future、服务 `prepare`、撤销句柄在受控调度下交错,检查每条执行都是演算的执行。与 tokio 的集成细节本次未核实 |
| proptest + proptest-state-machine | 性质测试与收缩;参考状态机与被测系统对照 | proptest 1.12.0,proptest-state-machine 0.9.0(均 2026-10-10) | 参考状态机就是 `step`(verification.md 对照表已指出"精确"对应)。目前只支持顺序执行转移,并发要自己配 shuttle |
| cargo-fuzz | libFuzzer 驱动的覆盖率引导模糊测试 | cargo-fuzz 0.13.2,libfuzzer-sys 0.4.13 | 把标签序列当输入喂纯核,与 oracle 比较;能找到 proptest 生成器碰不到的角落 |
| Miri | UB、数据竞争、弱内存 | 随 Rust 工具链发布;POPL 2026 论文 | 与演算一致性无关,守住 FFI 与插件加载那部分 unsafe |

另有 turmoil(0.7.2,tokio 的确定性网络模拟)与 bolero(0.13.7,统一模糊测试与性质测试的前端),本报告不依赖它们;
bolero 与 Kani 的集成方式未核实。

2026 年 10 月的 arXiv 预印本 [Li 2026] 用一组静态分析验证 Rust 异步运行时的"最终推进"(提交的任务最终有进展),
将发表于 ESOP 2027。本次只读到摘要。它说明异步外壳的活性有人在做,但对象是执行器本身,不是执行器之上的协议。

### 1.5 Rocq 与 Rust 之间的桥

**Rocq 自带的抽取没有 Rust 后端。** Rocq 9.3 参考手册:输出语言只有 OCaml、Haskell、Scheme,外加主要供调试用的 JSON
[Rocq 手册]。

**第三方 Rust 抽取有一条,且仍在维护。**

- 源头是 ConCert 项目 [Annenkov 2022]:在 MetaCoq 已验证的擦除之上加类型信息(λT□),带证明地做若干变换,
  再用 Coq 中写的打印器输出 Liquidity、CameLIGO、Elm 与 Rust 的子集。可信基是 Coq 本身、MetaCoq 的 quote
  与各打印器;类型的擦除未验证,但论文论证它不影响可靠性。Rust 输出的特点:整个程序是一个持有 bumpalo 区域的
  `Program` 结构的方法,内存只在 `Program` 销毁时整体释放;闭包都分配在区域里并作为 `&dyn Fn` 传递。
- 现在的包是 **rocq-rust-extraction 0.2.1**(2026-03-13,peregrine-project/rocq-typed-extraction,依赖
  `rocq-typed-extraction-common`,仓库 README 说兼容 Rocq 9.1)。旧名 coq-rust-extraction 0.1.0 只支持 Coq 8.17–8.19。
  仓库关注度很低(1 star),当前版本的打印器与类型擦除是否已验证,本次未核实。
- **Peregrine** [Nielsen 2026,TYPES 2026]:以 MetaRocq 的已验证擦除为前端,把已有的 OCaml、C、WebAssembly、
  Rust、Elm 抽取管线收作后端,另加 CakeML 后端;作者表示希望将来验证全部前后端,即目前未验证。
- 另有 Bloomberg 的 Crane(Rocq 到 C++),与 Rust 无关。

**反方向(Rust 到 Rocq)**:Aeneas 的 Coq 后端、hax 的 Rocq 后端、rocq-of-rust,见 1.2 节。

### 1.6 四条路线的代价与可信基

设被验证的对象是 1.7 节的纯核,规格是 Rocq 中的 `ctl_step`(课题 V2)。

| 路线 | 一致性从哪里来 | 可信基(除 rustc 外) | Rust 代码 | 代价 | 主要风险 |
|---|---|---|---|---|---|
| A. 抽取 oracle,差分测试 | 测试 | Rocq 内核;抽取(OCaml 或 Rust);胶水与观察函数;测试覆盖 | 随意写 | 小到中 | 只是测试;观察函数写错会掩盖分歧 |
| B. 抽取出 Rust 当生产核 | 构造 | MetaRocq 擦除(已验证);类型擦除与打印器(未验证);重映射表;bumpalo | 生成代码,`&dyn Fn`,区域分配 | 中 | 常驻进程的内存回收要每步复制出区域;工具成熟度 |
| C. 手写纯核,Aeneas/hax 翻译回 Rocq,证明等于 `ctl_step` | 证明 | Charon 与 Aeneas 的翻译(借用部分有可靠性证明,整体未验证);Rocq 内核 | 受限子集,一阶 | 中到大 | Coq 后端成熟度;子集限制改变代码写法 |
| D. 手写纯核,Verus 证明它满足手抄的规格 | 证明(另一逻辑) | Verus、Z3;手抄规格与 `ctl_step` 一致(靠 A 交叉检查) | 较自由,带 ghost 注解 | 中到大 | 两份真相;Verus 版本漂移(Anvil 仓库已注明论文所用版本与现在不同) |
| E. RefinedRust 或 rocq-of-rust | 证明(基础性,落在 Rocq) | Rocq 内核;前端翻译 | 较自由,可含 unsafe | 大 | 人工证明量;rocq-of-rust 的 Rocq 版本约束 |

A 不与其他路线冲突,应当最先做,并在 C、D 中继续使用:C 的翻译器、D 的手抄规格,都靠 A 的 oracle 兜底。
B 的生成代码当 oracle 用时没有内存问题(每个测试用例一个区域),所以 B 最好的位置是 A 的一个实现方式。

### 1.7 设计建议:控制层怎样组织

**原则:演算的一步 = 纯核的一次同步调用;IO、等待、取消都在外壳。**

1. **纯核。** 一个不含 `async`、不含内部可变性、不含 unsafe、不含闭包字段的 `struct Core`,状态对应
   `State` 去掉鬼字段与服务状态:`next`、fiber 表、绑定表(只记 pid 与 owner)。方法 `step(&mut self, l: Label, obs: Obs)
   -> Result<Vec<Cmd>, NotEnabled>` 对应 `step γ ℓ`,`NotEnabled` 对应 `None`;`enabled(&self)` 返回当前可走的
   生命周期标签,对应 `lifecycle_labels` 过滤。fiber 名用整数索引或代际索引(R7,[language.md](language.md))。
2. **把高阶数据去函数化。**
   - 逆 `g`:演算里每个 `UOp` 已经带一个新鲜令牌 `tok`(取自 `next`),纯核只记 `(k, pid, tok)`,外壳用 `tok`
     作键保存真正的撤销句柄。投影时丢掉 `g`、保留 `tok`,恰好不失信息。
   - 程序 `Prog`:真实插件是不透明的 Rust/WASM/JS 代码,纯核本来就不该看到它。`L-Step` 改由外壳把"插件请求的下一个
     动作"(`Op k`、`Provide k`、`Spawn c`、`Done`、`Fail`)和服务的结果(成功或失败)作为 `obs` 传进来。课题 V2
     要证明这样做与 `load_step` 一致。
3. **外壳是单个 actor。** 一个任务独占 `Core`,其余任务(插件 future、服务的 `prepare`、撤销句柄)只通过消息与它交互。
   于是 DESIGN D6 对运行时作者的义务"每条控制规则在一个同步片段内完成"变成结构性质:`Core` 只在 actor 的消息处理里被
   `&mut` 借用,Rust 的借用检查保证没有第二个写者。
4. **服务操作用 D6 的两段形状。** `prepare` 是 `async`,可以等外部 IO,不碰服务状态;`commit` 同步、纯函数,就是 `run`。
   actor 在同一次消息处理中先问纯核解析出的 pid,再在该绑定上 `commit`,再调用 `step(LStep n, obs)`。三件事之间没有
   `.await`,所以这次 `L-Step` 是原子的。
5. **取消就是 `L-Divert`,不靠 `Drop`。** Rust 的取消是丢弃 future(R4)。`commit` 之前丢弃,操作在演算中没有发生
   (DESIGN D6 的"放弃");`commit` 与 `step` 同在一次处理中,不存在"提交了一半"。撤销日志是纯核里的数据,不是
   RAII 守卫,所以 `mem::forget` 或没有 async drop(R1、R3)都不影响恢复:`L-Undo` 由外壳按纯核给出的 `Cmd::RunUndo(tok)`
   逐项执行、逐项确认,串行 LIFO(差异 e)。
6. **调度选择随意。** 外壳从 `enabled()` 里任选一个生命周期标签执行。无失败时合流定理(`dynamic_agree`)保证选择不影响
   落定状态,所以外壳可以按性能选调度,不需要证明调度策略。

这样组织以后,各工具的分工是:纯核由路线 C 或 D 证明、由 A 测试、由 Kani 做有界检查;外壳由 shuttle 测交错;
服务由线性一致性测试查 D6;FFI 由 Miri 查。

## 2. 对照表

"精确"指概念与定义一一对应;"近似"指结构相同但范围或粒度不同;"形似"指只有类比。

| 工具或文献中的概念 | 演算中的对应 | 程度 | 说明 |
|---|---|---|---|
| Aeneas 输出的纯函数(状态进、状态出,失败为 `Result`) | `step : State → Label → option State` | 精确(形状) | 都是确定的全函数;`option` 对 `Result`。要比较还需要抽象函数(课题 V4) |
| proptest-state-machine 的参考状态机、转移前置条件 | `step`;`step γ ℓ ≠ None` | 精确 | 同 verification.md 对 lockstep 的判断 |
| proptest 的不变式检查 | `WF`(`Preservation.wf_reachable`) | 近似 | 要先有可判定的 `wfb` 并证明它反映 `WF`(课题 V1) |
| Kani 的有界证明 | `preservation` 在固定规模下的实例 | 近似 | 有界,对象是 Rust 纯核而不是 Rocq 定义 |
| Verus 的 spec fn 与 exec fn 之间的精化 | `ctl_step` 与纯核 | 近似 | spec 要从 Rocq 手抄 |
| Verus tokenized state machine 把全局状态机分成各线程持有的令牌 | 每个 fiber 独占自己的累加器 `acc`;绑定由 owner 持有(`WF` 中的 owner 条款) | 形似 | 演算是单个转移系统,没有分片;D6 已说明 `L-Step` 只有服务操作需要原子,正是因为 `acc` 归 fiber 独占 |
| Anvil 的 ESR(最终协调到期望状态并保持) | `termination`、`quiet_settled`、`dynamic_agree` | 近似 | 见 incremental.md;Anvil 要公平性,演算的收敛对每个调度成立 |
| shuttle、loom 探索的交错 | 演算中不同 fiber 的标签任意交错;D6 的原子性前提 | 近似 | 工具探索的是真实线程或任务的交错,演算的交错以规则为粒度 |
| PCT 的"缺陷深度" | 无 | 形似 | 只是测试策略 |
| 取消(丢弃 future) | `L-Divert`;D6 的"放弃" | 近似 | 在 `commit` 之前丢弃时精确;之后不可能丢弃(同一次处理) |
| RAII/`Drop` 撤销 | `acc` 的 LIFO 撤销,`L-Undo` | 形似 | `Drop` 不保证运行、不能 `await`;本设计不用它承载撤销(R1) |
| RustBelt 中 unsafe 库的语义验证条件 | D6 中服务作者的义务(`WellBehaved`、`RevertIndep`、`ConfHyps`) | 形似 | 都是"库满足条件,客户定理就成立";保证的性质不同 |
| 线性 ghost 权限(Verus `PCell` 的 `PointsTo`) | 绑定的唯一 owner,`withdraw_waits` | 形似 | 演算没有权限令牌;owner 是数据 |
| 预言(Creusot、RustHornBelt) | 无 | 无 | 纯核不需要可变借用的规格 |
| Rocq 抽取 / Rust 抽取作为 oracle | verification.md 课题 T1 | 精确(方法) | 被测系统从 TS 换成 Rust |
| 区域分配(bumpalo) | 无 | 无 | 只影响抽取代码能否常驻 |
| 撤销句柄按令牌存放 | `UOp k pid tok g` 的 `tok` | 精确 | 令牌本来就新鲜且全局唯一(`Prov` 不变式中"不同 fiber 的撤销项令牌互不相同") |
| 外壳任意选择可走的生命周期标签 | `dynamic_agree`、`static_assembly` | 精确 | 无失败时;有失败时终态依赖调度,与演算一致 |
| 单 actor 独占 `&mut Core` | DESIGN D6"每条控制规则在一个同步片段内完成" | 近似 | 由借用检查保证只有一个写者;仍要保证处理中途没有 `.await` |

## 3. 差异

**演算有、这些工具没有处理好的。**

1. **异步。** 能证明的工具都不支持 async(1.2 节)。演算里的异步已经编码成标签,所以只要实现也把异步留在纯核之外,
   这个缺口就不影响纯核。代价是外壳只能测试。
2. **对一切服务、一切插件的量化。** Rocq 中的定理以 `Service` 为参数、以组件表为参数。Rust 纯核若泛型于服务,
   就需要 trait 与关联类型,而 Aeneas、hax 对 trait 的支持有限。1.7 节的做法是让纯核根本不接触服务状态,
   把服务只留在外壳;投影引理(课题 V2)负责说明这样剥离不丢东西。
3. **交错与合流。** 工具验证的是单个函数的功能正确性。演算的恢复精确性、合流是关于交错执行的定理,已在 Rocq 中证明;
   Rust 一侧只需要逐步的模拟("纯核的每一步就是 `ctl_step` 的一步"),交错留在 Rocq。这是按 1.7 节组织的主要收益:
   需要工具证明的东西从"并发系统精化"降到了"顺序函数相等"。
4. **活性。** 演算证明了终止(`termination`、`no_infinite_run`)与无死锁(`progress`、`quiet_settled`)。
   在 Rust 工具里只有 Verus 加 Anvil 式的 TLA 嵌入做过活性;但纯核每一步都终止,纯核与 `ctl_step` 逐步相等之后,
   生命周期步的终止直接从 Rocq 传过来,外壳只需保证"会调用 `step`"。
5. **鬼字段。** `oplog`、`inilog` 只为元理论存在。Rust 纯核不要它们;Rocq 侧要有一条引理说明 `step` 的非鬼部分不读它们
   (RULES 已说明规则不读,但还没有写成可引用的引理)。

**这些工具有、演算没有的。**

1. **实现层面的数据表示。** 演算用函数表示映射、用 `nat` 计数;Rust 纯核用 `Vec`、代际索引、`u64`。
   这个差距要由数据精化(课题 V1)在 Rocq 中弥合,不能指望翻译工具。
2. **溢出与 panic。** `next` 是无界自然数;Rust 中是 `u64`,溢出要么证明不发生(Kani、Verus 可以),要么规定为错误。
   演算没有这个概念。
3. **内存安全与 UB。** RustBelt、Tree Borrows、Miri 关心的东西演算不涉及;这部分只在 FFI 与插件加载边界出现。
4. **并发测试的覆盖度量。** PCT 给出按缺陷深度的概率下界;演算侧的 checker 没有对应的度量。

## 4. 候选课题

### V1. 可计算的精化版 `step` 与可判定的 `WF`

- **目标。** 得到一个能高效执行、能抽取的 `step_fm`,并证明它与 `Calculus.step` 一致;得到可判定的 `wfb`,并证明它反映
  `Preservation.WF`。对应定义:`step`、`load_step`、`undo_step`、`held`、`relied`、`conflict`;对应定理:`wf_reachable`。
- **做法。** 新建一个 Rocq 文件,不改现有文件。fiber 表与绑定表用有限映射(Stdlib 的 `FMapAVL`,或按名字排序的关联表),
  计数器用 `N`,去掉 `oplog`、`inilog`;`relied`、`has_child` 改为遍历映射的定义域而不是 `seq 0 next`。
  定义抽象函数 `abs : State_fm → State`(鬼字段任取),证明 `step_fm s ℓ` 与 `step (abs s) ℓ` 在 `abs` 下对应。
  `wfb` 逐条翻译 `WF` 的 10 条;对 `Inv2`、`Prov` 等辅助不变式视需要也写可判定版本。最后加 `Extraction` 命令输出 OCaml。
- **预期产出。** 一个可以当 oracle、也可以当 V2、V4 规格基础的 `step_fm`;`wfb` 可以在测试中逐步检查,也可以抽取后变成
  Rust 纯核的调试断言。
- **风险。** `step` 的状态里 `fibers` 是全函数,有限映射版要处理"定义域外为 `None`"的外延性问题;服务状态 `St Σ` 与逆 `g`
  仍在状态里,抽取要选一个具体的 Σ(如 `Compose.Sum` 加 `Registry`、`Listeners`)。
- **工作量。** 小到中。

### V2. 控制投影 `ctl_step`:Rust 纯核的精确接口

- **目标。** 证明 `step` 对服务状态与插件程序"可以剥离":存在只看控制状态的 `ctl_step`,使得
  `proj (step γ ℓ) = ctl_step (proj γ) (obs γ ℓ)`。`proj` 丢掉每个绑定的 `bst`、每个 `UOp` 的 `g`、每个 `Loading` 的程序 `P`;
  `obs` 是外壳能提供的观察:对 `LStep n`,是程序头部的动作种类(`POp k`、`PProvide k`、`PSpawn c`、`PDone`、`PFail`)
  以及 `run` 是否成功。
- **做法。** 在 V1 的 `step_fm` 上做(或直接在 `step` 上做)。逐个标签检查:`O-*` 与 `L-Begin`、`L-Divert`、`L-Leave`、
  `L-RetireChild`、`L-Unloaded`、`L-Remove` 本来就不读 `bst` 与 `P` 的内部;`L-Step` 只读 `P` 的头部与 `run` 的成败;
  `L-Undo` 的 `UOp` 分支写 `bst` 但不影响控制。再证明 `ctl_step` 的执行可以提升回 `step` 的执行(给定每步 `run` 的结果),
  这样 Rocq 中关于 `step` 的定理(`unload_waits`、`parent_waits_child`、`step_coherent` 等控制性质)都能陈述到纯核上。
  顺带补上第 3 节差异 5 的引理:`step` 的非鬼部分不读 `oplog`、`inilog`。
- **预期产出。** 一个几百行的一阶纯函数 `ctl_step`,作为 Rust 纯核的规格;一张"哪些已证性质只依赖控制状态"的清单。
  恢复精确性与合流涉及服务状态,不在投影内,仍由 Rocq 中的原定理加外壳的义务(D6)覆盖。
- **风险。** `L-Step` 的 `POp` 分支在解析失败时也要读 `binds` 中的 owner 与 pid,这些在控制状态里,没有问题;
  但 `run` 失败时计数器仍加一(`bump`),观察必须区分"解析失败"与"`run` 失败"两种 `EOp`/`EUnresolved`,要逐条核对。
- **工作量。** 中。

### V3. Rust 纯核加双 oracle 的差分测试;外壳的交错测试

- **目标。** 在写证明之前,先用测试把 Rust 纯核钉在 `ctl_step` 上,把外壳钉在 D6 上。
- **做法。**
  1. 按 1.7 节写 Rust 纯核。
  2. oracle 两种:V1、V2 抽取到 OCaml,经子进程以 JSON 交换标签与观察;或用 rocq-rust-extraction 抽取到 Rust,
     同进程调用(先做一次小试验,判断它能否处理 `step_fm` 用到的有限映射与记录)。
  3. proptest-state-machine:参考状态机是 oracle,被测系统是纯核,每步比较投影后的状态,`check_invariants` 调用抽取出的 `wfb`。
     cargo-fuzz 以字节串解码成标签序列,做同样的比较。
  4. Kani:对纯核写有界证明框架(见 V5)。
  5. 外壳:shuttle 的随机与 PCT 调度下,让插件 future、服务 `prepare`、撤销句柄交错;记录纯核收到的标签序列,
     用 oracle 重放,要求每步可走(verification.md 第 1 档的轨迹检查,换到 Rust 上可以不插桩,因为纯核的输入就是标签)。
  6. 服务:按 verification.md 课题 T3 的做法做线性一致性测试,顺序规格用 `Services/Registry.v`、`Services/Listeners.v` 抽取。
- **预期产出。** 纯核与 `ctl_step` 在随机与模糊输入下一致;外壳在受控调度下只产生演算的执行;反例自动收缩。
  它同时是 V4 的回归测试。
- **风险。** 观察函数与状态比较写错会掩盖分歧,要先用故意改错的纯核检验测试能抓到(变异测试);
  proptest-state-machine 只支持顺序执行,外壳部分要自己把 shuttle 与 oracle 接起来。
- **工作量。** 中。

### V4. 证明 Rust 纯核精化 `ctl_step`

- **目标。** 一条 Rocq 定理:Aeneas 翻译出的纯核函数 `core_step` 与 `ctl_step` 在抽象函数下逐步一致。由此 V2 中列出的控制性质
  对 Rust 纯核成立。
- **做法。**
  1. 先用 Aeneas 翻译 V3 的纯核,记下子集限制要求的改写(循环中的 `return`、泛型以 `&mut` 实例化等),回头改 Rust 代码。
  2. 首选 Coq 后端,在本仓库同一个 Rocq 里证明 `core_step` 与 `ctl_step`(或 `step_fm` 的控制部分)一致;
     证明按标签分情况,大部分是展开定义后的数据精化。
  3. Coq 后端不能用时,改用 Lean 后端:把 `ctl_step` 手抄到 Lean,在 Lean 中证明;手抄的一致性由 V3 的 oracle 用同一批
     随机输入交叉检查。或者改用 Verus:在 Verus 中写 `ctl_step` 的 spec 版本,证明 exec 纯核满足它,同样用 oracle 检查 spec。
- **预期产出。** 第一个"插件运行时的 Rust 控制层精化生命周期演算"的机械化证明,范围是控制层;可信基为 Charon、Aeneas 的翻译
  与 rustc。对外可以说:控制规则由证明保证,外壳由测试保证,服务由义务加线性一致性测试保证。
- **风险。** Aeneas 的 Coq 后端成熟度未核实,最近的活跃开发都在 Lean;Aeneas 不支持的写法可能迫使纯核写得不自然;
  Rocq 9.1 与 Aeneas 生成代码的兼容性未核实。Verus 退路的风险是两份真相与版本漂移。
- **工作量。** 中到大。依赖 V2 与 V3。

### V5. Kani 有界检查纯核的不变式保持

- **目标。** 在不写任何证明的情况下,对小规模状态穷举检查:任意满足 `wfb` 的状态,任意标签,`step` 之后仍满足 `wfb`;
  以及纯核不 panic、计数器不溢出。对应定理:`preservation`。
- **做法。** 在纯核 crate 里加 `#[kani::proof]` 框架:用 `kani::any()` 生成至多 3 个 fiber、2 个键的状态,`kani::assume(wfb(s))`,
  对任意标签调用 `step`,断言 `wfb`。`wfb` 用 Rust 手写或从 V1 的抽取结果移植。
- **预期产出。** 纯核在小规模下的不变式保持证据;Rust 纯核若与 Rocq 的 `WF` 有偏差,通常在这里最先暴露。
- **风险。** CBMC 对映射类型的建模代价高,状态规模可能只能很小;有界结论不能替代 V4。
- **工作量。** 小。

### 排序

V1、V2 是 Rocq 侧的地基,小到中,而且即使 Rust 重写推迟,它们对 TS 版的 lockstep(verification.md T1)同样有用,应当先做。
V3 紧随其后,V5 可以与 V3 并行。V4 在 V3 稳定之后再开始;它的路线选择(Aeneas 的 Coq 后端、Lean 后端、Verus)
建议先花一两天做 Aeneas 对纯核的翻译试验再定。外壳的精化证明(async)在 2026 年没有工具,不列为课题。

## 5. 参考文献

核实方式:WebSearch 检索出版记录(出版方页面、DOI、作者主页、arXiv)或项目页面,核对作者、题目、会议或期刊、年份;
工具版本取自 crates.io API 与 GitHub 发布页(2026-11-25 查询)。

**论文。**

- [Annenkov 2022] Danil Annenkov, Mikkel Milo, Jakob Botsch Nielsen, Bas Spitters. Extracting functional programs from Coq, in Coq. Journal of Functional Programming 32, 2022. doi:10.1017/S0956796822000077。会议版为 Extracting Smart Contracts Tested and Verified in Coq,CPP 2021。Rust 一节的内存管理(bumpalo)与闭包表示(`&dyn Fn`)取自 arXiv:2108.02995 全文。
- [Bhargavan 2025] Karthikeyan Bhargavan, Maxime Buyse, Lucas Franceschino, Lasse Letager Hansen, Franziskus Kiefer, Jonas Schneider-Bensch, Bas Spitters. hax: Verifying Security-Critical Rust Software using Multiple Provers. VSTTE 2025(IACR ePrint 2025/142)。
- [Burckhardt 2010] Sebastian Burckhardt, Pravesh Kothari, Madanlal Musuvathi, Santosh Nagarakatte. A Randomized Scheduler with Probabilistic Guarantees of Finding Bugs. ASPLOS 2010, pp. 167–178.
- [Denis 2022] Xavier Denis, Jacques-Henri Jourdan, Claude Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, LNCS 13478.
- [Gäher 2024] Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers, Derek Dreyer. RefinedRust: A Type System for High-Assurance Verification of Rust Programs. PLDI 2024(PACMPL 8, pp. 1115–1139),doi:10.1145/3656422。
- [Gäher 2026] Lennard Gäher, Vincent Lafeychine, Sascha Kehrli, Avraham Shinnar, Wojciech Ozga, Guerney Hunt, Derek Dreyer. Bringing Foundational Verification to Real-World Rust Code. OOPSLA 2026(PACMPL 10, OOPSLA2, Article 352),doi:10.1145/3839484。"trait object 与 async 目前没有工具支持"一语出自其引言的局限一段。
- [Hance 2026] Travis Hance, Laila Elbeheiry, Yusuke Matsushita, Derek Dreyer. VerusBelt: A Semantic Foundation for Verus's Proof-Oriented Extensions to the Rust Type System. PLDI 2026(PACMPL 10, PLDI, Article 247)。(题目后半以会议页面为准,正文内容依据摘要与检索摘录。)
- [Ho 2022] Son Ho, Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. ICFP 2022(PACMPL 6)。
- [Ho 2024] Son Ho, Aymeric Fromherz, Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. ICFP 2024。(只由 Aeneas README 核实题目与会议,作者表未逐一核对。)
- [Ho 2025] Son Ho, Guillaume Boisseau, Lucas Franceschino, Yoann Prak, Aymeric Fromherz, Jonathan Protzenko. Charon: An Analysis Framework for Rust. CAV 2025(工具论文,Springer LNCS;arXiv:2410.18042)。
- [Jung 2018] Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. RustBelt: Securing the Foundations of the Rust Programming Language. POPL 2018(PACMPL 2, Article 66),doi:10.1145/3158154。
- [Jung 2026] Ralf Jung, Benjamin Kimock, Christian Poveda, Eduardo Sánchez Muñoz, Oli Scherer, Qian Wang. Miri: Practical Undefined Behavior Detection for Rust. POPL 2026(PACMPL 10, POPL, Article 48),doi:10.1145/3776690。
- [Kobeissi 2026] Nadim Kobeissi. (题为 Verification Facade 的分析)IACR ePrint 2026/670,2026 年 4 月修订。只核实了编号、作者与"hax 到 F* 的三类语义缺口"这一结论,完整题目未核实。
- [Lattuada 2023] Andrea Lattuada, Travis Hance, Chanhee Cho, Matthias Brun, Isitha Subasinghe, Yi Zhou, Jon Howell, Bryan Parno, Chris Hawblitzel. Verus: Verifying Rust Programs using Linear Ghost Types. OOPSLA 2023(PACMPL 7, Article 85),doi:10.1145/3586037。
- [Lattuada 2024] Andrea Lattuada, Travis Hance, Jay Bosamiya, Matthias Brun, Chanhee Cho, Hayley LeBlanc, Pranav Srinivasan, Reto Achermann, Tej Chajed, Chris Hawblitzel, Jon Howell, Jacob R. Lorch, Oded Padon, Bryan Parno. Verus: A Practical Foundation for Systems Verification. SOSP 2024.
- [Li 2026] Yanze Li, Ivan Beschastnikh, Alexander J. Summers. Modular Responsiveness Verification of Rust Async Runtimes. arXiv:2610.09198,将发表于 ESOP 2027。只读了摘要。
- [Matsushita 2020] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, LNCS 12075, pp. 484–514.
- [Matsushita 2022] Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, Derek Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022.
- [Nielsen 2026] Eske Hoy Nielsen, Simon Dima, Lucas Escot, Orestis Melkonian, Hugo Segoufin-Cholet, James Chapman, Yannick Forster, Matthieu Sozeau, Bas Spitters. Peregrine: a middle-end for code generation from proof assistants. TYPES 2026(摘要)。
- [Sun 2024] Xudong Sun 等. Anvil: Verifying Liveness of Cluster Management Controllers. OSDI 2024。(完整作者表未逐一核对。)
- [VanHattum 2022] Alexa VanHattum, Daniel Schwartz-Narbonne, Nathan Chong, Adrian Sampson. Verifying Dynamic Trait Objects in Rust. ICSE-SEIP 2022,doi:10.1145/3510457.3513031。
- [Villani 2025] Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows. PLDI 2025(PACMPL 9, Article 188),doi:10.1145/3735592。
- Ayoun, Denis, Maksimović, Gardner. A Hybrid Approach to Semi-automated Rust Verification. PLDI 2025(PACMPL 9, Article 186),doi:10.1145/3729289。即 Gillian-Rust 的论文。
- Astrauskas, Bílý, Fiala, Grannan, Matheja, Müller, Poli, Summers. The Prusti Project: Formal Verification for Rust. NFM 2022, LNCS 13260, pp. 88–108.

**软件与文档。**

- [Verus 特性表] verus-lang.github.io/verus/guide/features.html:async 函数与 async 块不支持,trait object 部分支持,闭包支持(不含可变捕获),`spawn`/`join` 支持,内部可变性经 `vstd` 支持。页面日期未显示。Verus 发布页:最新 0.2026.11.22(2026-11-23)。
- [Aeneas README] github.com/AeneasVerif/aeneas:后端 F*、Coq、HOL4、Lean;Lean 与 HOL4 最成熟;不支持 unsafe 与并发。无发布标签。
- hax:github.com/cryspen/hax README(Rocq 后端为 `cargo hax into coq`,Experimental);hax.cryspen.com 2026 年博客;crates.io `hax-lib` 0.5.0(2026-11-09)。
- rocq-of-rust:github.com/formal-land/rocq-of-rust;`RocqOfRust/rocq-of-rust.opam` 要求 `rocq-core >= 9.0 & < 9.1`。
- Creusot:devlog.creusot.rs(0.10.0 至 0.15.0 的发布记录,0.15.0 为 2026-11-20);0.9.0 的并发支持取自 2026-01-19 的 devlog 检索摘要。crates.io `creusot-std` 0.15.0。
- Gillian-Rust:GillianPlatform/gillian-rust 的 README(经镜像读取),自述为不稳定的原型。
- [Kani 对比页] model-checking.github.io/kani/tool-comparison.html:Kani 目前不支持验证并发代码;loom 穷举交错,shuttle 随机选择交错。Kani 发布页:0.68.0。
- loom:github.com/tokio-rs/loom README(C11 内存模型下的穷举,`SeqCst` 与 load buffering 两处已知不可靠);crates.io 0.7.3。
- shuttle:github.com/awslabs/shuttle 与 docs.rs(随机调度、PCT、自带 async 执行器);crates.io 0.9.10。
- proptest-state-machine:docs.rs 0.9.0(`prop_state_machine!` 目前只支持 `sequential`);proptest 1.12.0。
- cargo-fuzz 0.13.2、libfuzzer-sys 0.4.13、turmoil 0.7.2、bolero 0.13.7:crates.io。
- [Rocq 手册] rocq-prover.org/doc/v9.3/refman/addendum/extraction.html:抽取输出语言为 OCaml、Haskell、Scheme(另有 JSON)。
- [rocq-rust-extraction] rocq-prover.org/p/rocq-rust-extraction:0.2.1,2026-03-13,维护者 Danil Annenkov,主页 github.com/peregrine-project/rocq-typed-extraction(README 称兼容 Rocq 9.1)。旧包 coq-rust-extraction 0.1.0 要求 Coq 8.17–8.19。

**未核实(共 13 条)。**

1. Aeneas 的 Coq 后端成熟度,以及它生成的代码与 Rocq 9.1 的兼容性。
2. Aeneas 对闭包、trait object、`HashMap`/`BTreeMap` 等标准库映射的支持。
3. hax 的 Rocq 后端所需的 Rocq 版本与可处理的 Rust 子集(包括 async、内部可变性、并发、unsafe 各项)。
4. rocq-of-rust 对 async、trait object、内部可变性、并发的支持。
5. Creusot 对 async、trait object、内部可变性的支持(只有 RefinedRust 论文的一般性陈述)。
6. Prusti 的维护状况(只见到第三方镜像页上的 2026 年提交日期)与各项特性支持。
7. Gillian-Rust 官方仓库的近况(只读到镜像)。
8. shuttle 与 tokio 集成的具体方式。
9. loom 对 async 的支持。
10. bolero 与 Kani 的集成方式。
11. rocq-rust-extraction 当前版本中类型擦除与打印器是否已验证(只有 2022 年论文的说法)。
12. Kani 实验性 async 库(`block_on`、`spawn`)在 2026 年的状态。
13. Anvil 中控制器实现与 Verus 规格之间的具体分层方式(只核实了 ESR、Verus、TLA 嵌入与环境建模)。

另外,VerusBelt、Kobeissi 2026、Ho 2024、Sun 2024 四条只核实了部分字段,已在各条目中注明。
