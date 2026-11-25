# 验证与测试:精化证明、模型检测、状态机性质测试

本文对照特征 F9(合流)和 [checker/](../checker/),回答三个问题:

1. checker 现在枚举调用序列、以自身比较为判据,能否改为以 Rocq 的 `step` 抽取出的参考实现做 lockstep 模型测试?
2. 证明真实 Cordis(JS,异步)精化演算,最现实的路线是什么,代价多大?
3. 哪些性质用模型检测比用 Rocq 证明更划算?

简短的回答在第 0 节,依据在后面各节。

## 0. 结论先行

**问题 1。** 能,但对象要换。lockstep 需要模型知道插件的程序,真实 dsh 插件是不透明的 TS,
其中的裸 disposer 根本不是演算里带逆的操作,所以对真实插件,现有的自身比较判据(卸载前后比、两种次序比)
仍然是对的,不应替换。lockstep 适合测的是**运行时**:用随机生成的 `Prog` 组件当插件,
比较真实 Cordis(以及 EDSL 的垫片 `edsl/runtime/rt.js`)和抽取出的 `step`。两者检查的是信任链上
不同的假设:checker 找的是"插件违反义务",lockstep 找的是"运行时不按演算走"。
关键的技术点是:演算的大多数步是内部的生命周期步,测试者选不了;但合流定理(`dynamic_agree`、
`final_agree`)保证无失败时 quiet 状态在重命名意义下唯一,所以在"落定"这个粒度上模型是确定的,
可以直接当 oracle。有失败时合流不成立,模型要给出可达 quiet 状态的集合(终止定理保证它有限)。

**问题 2。** 分四档,按代价从小到大:

| 档 | 做法 | 得到什么 | 工作量 |
|---|---|---|---|
| 1 | 轨迹检查:给 vendored Cordis 打日志,把每次运行的轨迹映射为 `Label` 序列,用抽取出的 `step` 重放 | 观察到的运行都是演算的运行;不是证明 | 中 |
| 2 | 受控调度下的 lockstep 测试(课题 T1、T2) | 系统地探索交错,覆盖差异 e、h 等已知分歧 | 中 |
| 3 | 让 Cordis 的控制层直接调用抽取出的 `step`("验证过的核心,不验证的外壳") | 控制规则由构造正确,剩下的义务是 DESIGN D6 的逻辑原子性,可以用线性一致性测试检查 | 中到大 |
| 4 | 把 Cordis 核心(或先拿 `rt.js`)翻译到 Iris 中的一个带 promise 的语言,证明轨迹精化 | 真正的精化证明 | 大,研究项目级别 |

第 4 档没有现成的地基:JSCert、KJS 只覆盖 ES5,没有 promise 与 async/await;JaVerT.Click 覆盖 promise
与 async/await,但做的是有界符号测试,不是精化证明;本次检索没有找到 Iris 中现成的 JS 事件循环与 promise
语言。现实的路线是先做第 1、2 档,再看是否值得做第 3 档;第 4 档建议先对 `rt.js` 做,而不是对 Cordis。

**问题 3。** 模型检测更划算的,是"固定一个小配置、改一条规则或放宽一个原子性假设,看会不会坏"这类问题:
放宽 D6 的原子性(把 `L-Begin` 拆成读和写)看 TOCTOU、`Promise.all` 并发执行 disposer(差异 e)、
Cordis 实际的六态算法与 epoch 检查(差异 a、h)对演算的有界精化、编排输入下带公平性的活性、
可选依赖扩展的活锁。参数化的结论(任意程序、任意满足假设的服务)仍然只能靠 Rocq。

## 1. 领域概览

### 1.1 Iris 与基于它的精化证明

Iris 是 Rocq 中的高阶并发分离逻辑框架 [Jung 2018]。和本仓库有关的是它上面的三类精化技术:

- **ReLoC** [Frumin 2018]:关系逻辑,判断"程序 e₁ 在类型 τ 下精化 e₂",并给出逻辑原子的关系规格。
  两边是同一种语言的程序,适合证明"细粒度并发实现精化粗粒度实现"。
- **Simuliris** [Gäher 2022]:基于(去掉步索引的)Iris 的模拟框架,证明程序变换保持终止(公平调度下)。
  它说明在 Iris 里可以做保持活性的模拟,但对象是编译器变换。
- **Trillium** [Timany 2024]:把"实现的执行轨迹精化一个抽象模型"做成分离逻辑框架,并用它证明了具体分布式实现精化
  TLA+ 风格的抽象模型,还实例化出公平调度下的活性逻辑。在三者里它的形状最接近我们要的东西:
  抽象一侧是一个转移系统(`step`),实现一侧是另一种语言的程序。

逻辑原子性来自 TaDA 的原子三元组 [da Rocha Pinto 2014],ReLoC 与 Iris 都有对应物。DESIGN D6 已经把
"服务操作相对 S/≃ 逻辑原子"定为服务作者的义务,并指出它蕴涵可线性化 [Herlihy 1990]。

用 Iris 证明真实系统代码的先例是 Perennial 与 Goose [Chajed 2019]:Goose 把 Go 的一个子集翻译成 Iris
中的模型语言,再在其上证明。这条"翻译受限子集 + 在 Iris 中证明"的路线,是我们证明 TS 版 Cordis 时唯一可以
直接参照的工程模板。

### 1.2 JavaScript 的机械化语义与验证

- **JSCert / JSRef** [Bodin 2014]:ES5 的 Coq 形式化,外加从 Coq 抽取到 OCaml 的参考解释器 JSRef,
  证明 JSRef 相对 JSCert 正确,并用 test262 测试。方法上它就是"从证明助手抽取参考实现,再用测试集对照",
  与本文课题 T1 同构。
- **KJS** [Park 2015]:K 框架中可执行的 ES5.1 语义,通过全部核心一致性测试,支持符号执行。
- **JaVerT** [Fragoso Santos 2018]、**Gillian** [Fragoso Santos 2020]:基于分离逻辑的 JS 验证与符号执行,
  JS 先编译到中间语言再分析。**JaVerT.Click** [Sampaio 2020](及 Sampaio 2022 的博士论文)
  把 DOM 事件、promise 与 async/await 纳入,做有界的符号分析。

这些工作都不覆盖 Node.js 的 promise 加 async 生成器加 TS 这一整套,而 Cordis 的 `fiber.ts` 正好用到
async 迭代器、`Promise.all`、epoch 检查(DESIGN 差异 e、h)。所以在完整 JS 语义上验证 Cordis 不现实;
这些工作的价值在于方法(抽取参考实现、对照一致性测试)和事件模型的形式化。

### 1.3 Promise 与异步的形式化

- **λp** [Madsen 2017]:ES6 promise 的核心演算,并由此定义 promise graph 用于查错。
- **Node.js 异步执行模型** [Loring 2017]:事件循环、各类队列与 async context 的形式化。

对我们有用的是两点:(1)DESIGN D6 的"每条控制规则在一个同步片段内完成"可以在这类模型里精确陈述
(run-to-completion 的片段就是两个 await 之间的执行);(2)差异 h 中"在途的 `iter.next()` 落地后再检查 epoch"
是 promise 反应排队顺序的问题,λp 一类模型能说清楚它对应演算的哪几步。

### 1.4 模型检测

- **TLA+ 与 TLC** [Lamport 2002],**PlusCal** [Lamport 2009](翻译到 TLA+ 再用 TLC 检查)。
  TLA+ 原生支持"实现 ⇒ 规格"的精化检查(在给定的精化映射下),对小实例可以穷举。
- **Alloy** [Jackson 2002]:关系逻辑与有界检查,擅长结构不变式与最小反例。
- **SPIN** [Holzmann 1997]:Promela 进程模型,适合消息传递协议。
- **实现对照 TLA+ 规格**:MongoDB 的经验 [Davis 2020] 是,对高度抽象的规格做实现轨迹检查很难(粒度对不上),
  而从规格生成测试用例很成功;Cirstea 等 [Cirstea 2024] 给出了把(可以不完整的)实现轨迹化为受限模型检测问题的做法,
  在几个分布式程序上都找到了规格与实现的分歧。

### 1.5 状态机性质测试与 model-based testing

- **QuickCheck** [Claessen 2000];Erlang 版的状态机测试用于电信协议 [Arts 2006];
  **PULSE** 在 QuickCheck 之上控制调度以找竞态 [Claessen 2009];
  对 Dropbox 等同步服务的模型测试 [Hughes 2016] 处理了"后台动作对测试者不可见"带来的非确定性,
  这与 Cordis 的生命周期步对编排者不可见是同一类问题。
- **lockstep 风格**:同一串随机 API 调用同时作用于被测系统和模型,按某种可观察性比较响应。
  Haskell 的 quickcheck-lockstep [de Vries, Hackage] 是这种风格的库。
- **Hypothesis** [MacIver 2019](Python)与 **fast-check**(JS)都有状态机测试;fast-check 的
  `scheduledModelRun` 配合调度器控制 promise 的完成次序,用来复现竞态 [fast-check 文档]。
  对我们,fast-check 能直接在 Node 里驱动真实 Cordis,是现成的工具。
- **Node.js 的调度模糊测试**:Node.fz [Davis 2017] 在 libuv 中打乱事件队列;NodeRacer [Endo 2020]
  按 happens-before 有选择地推迟事件,完全用 JS 实现,不改 Node 内部。
- **线性一致性检查** [Herlihy 1990;Lowe 2017]:记录并发历史,判断是否存在与顺序规格一致的线性化;
  单条历史的判定是 NP 完全的,但小历史上实用。

### 1.6 从证明助手抽取参考实现做差分测试

- Coq/Rocq 的抽取机制 [Letouzey 2002] 把函数式定义抽取为 OCaml 等语言。抽取出的 OCaml 可以经
  js_of_ocaml [Vouillon 2014] 编译成 JS,与 Cordis 在同一个 Node 进程里运行。
- **QuickChick** [Paraskevopoulou 2015]:Rocq 中的 QuickCheck,测试代码本身可以验证。
- **差分测试** [McKeeman 1998];Csmith [Yang 2011] 是最有名的例子,它在已验证的 CompCert 的**未验证部分**
  找到了错误。这提示我们:即使演算已证,垫片 `rt.js`、checker 的宿主桩、Cordis 本身都在证明之外,正是差分测试的对象。
- **interaction trees** [Xia 2020]:Rocq 中表示不纯程序的余归纳自由单子,可抽取执行;
  Li 等 [Li 2021] 用它写非确定的服务器模型,导出测试器检查 Apache、Nginx。我们的 `Prog`
  (`POp k a κ` 带续延)是一个有限的、签名固定的自由单子,与之近似。

## 2. 对照表

"精确"指概念与定义一一对应;"近似"指结构相同但范围或粒度不同;"形似"指只有类比。

| 领域概念 | 演算或 checker 中的对应 | 程度 | 说明 |
|---|---|---|---|
| lockstep 的模型状态与命令 | `Calculus.State`、`Label` | 精确 | `step : State → Label → option State` 确定性,正好是状态机测试要的模型 |
| 命令的前置条件 | `step γ ℓ ≠ None` | 精确 | 不适用的标签就是不能发出的命令 |
| 模型转移 | `step`;多步用 `run_labels` | 精确 | `lifecycle_labels n` 已枚举一个 fiber 的全部生命周期标签,可直接用于"跑到 quiet" |
| "按可观察性比较响应" | `Observe.v` 的 ≃;checker 快照不含令牌与 uid;`reloadView` 改名 | 近似 | Rocq 侧的重命名是规范名 `CName`/`CN` 与 `AgreeL`;checker 侧用场景里固定的安装编号,两者不是同一个函数 |
| 隐藏的后台动作(Dropbox 模型测试) | 生命周期规则 `L-*` 对编排者不可见 | 近似 | 合流定理让无失败时的落定状态唯一,比 Dropbox 的情形容易 |
| 蜕变测试:两种调度结果相同 | checker `pair`(ab 与 ba)、`late`;定理 `dynamic_agree`、`static_assembly` | 近似 | checker 只试两两次序与单个服务晚到,定理量化所有调度 |
| 卸载后与从未安装相同 | checker `recovery()`;定理 `recovery_from_init` | 近似 | checker 的 `before` 快照在 `plain` 场景中恰为影子存储;有别的 fiber 同时活动时,应比较的是 `recovery_exact` 的影子存储,checker 没有 |
| 故障注入 | checker `fault(site, k)`;`load_step` 中 `run` 返回 `None` 的分支(进入 `Unloading acc w (Some EOp)`) | 精确 | 在规则层面一一对应 |
| 落定(quiescence) | checker `settle()`(若干轮 `setImmediate` 加 5ms);`quiet`、`exists_quiet` | 形似 | checker 是启发式,停在 LOADING 时判无结论;演算的 quiet 是精确定义 |
| 线性一致性 | DESIGN D6 的逻辑原子性义务;顺序规格 = 服务的 `run` | 近似 | D6 还要求逆同样原子,线性一致性检查通常不管逆 |
| 原子三元组 [TaDA、Iris] | D6 中服务作者的义务 | 近似 | DESIGN 已直接引用 |
| 轨迹精化(Trillium) | D6 的"每个真实执行对应演算的一个执行" | 近似 | 形状一致;Trillium 的实现语言不是 JS |
| 上下文精化(ReLoC) | 同上 | 形似 | ReLoC 两边是同一语言的程序,我们一边是转移系统 |
| TLA+ 精化映射 | DESIGN 差异 a:FAILED = `Inactive (Some ξ)`,DISPOSED = 条目不存在 | 精确(形状) | 映射已经写在 DESIGN 里,差的是把它写成 TLA+ |
| 带公平性的活性 | `progress`、`termination`、`quiet_settled` | 近似 | Rocq 证的是只走生命周期步时终止、静止即稳定;TLA+ 可以在编排输入穿插时陈述"最终落定" |
| 自由单子 / interaction trees | `Prog`(`POp k a κ`、`PProvide`、`PSpawn`) | 近似 | `Prog` 是归纳的,有限;事件签名固定 |
| 抽取参考实现 + 一致性测试(JSRef) | 抽取 `step` 对照 Cordis(课题 T1) | 近似 | 方法同构 |
| 调度控制(PULSE、fast-check 调度器、NodeRacer) | checker 没有;REPORT 的 C 类"预测的次序依赖在真实宿主上没有出现" | 近似 | checker 无法控制异步交错,只能观察 |

## 3. 差异

**演算有、这些领域没有处理好的。**

1. **大多数转移是内部的。** 标准的 lockstep 里每个命令都由测试者发出;这里编排者只能发 `O-*`,
   `L-*` 由运行时自己走。一般需要非确定的模型(Dropbox、Li 等的做法)。我们手上有合流定理:
   无失败时任何调度到达的 quiet 状态在重命名意义下相同(`final_agree`、`dynamic_agree`),
   模型可以按任意固定调度跑到 quiet,再与被测系统比较。这在 model-based testing 文献中少见,是可以写出来的一点。
2. **观察要按重命名比较。** 演算中 fiber 名、pid、令牌共用一个计数器 `next`,Cordis 的 uid 是另一个计数器。
   Rocq 已经有规范名(`CName`),但 `CN` 是归纳关系,不是函数;要做 oracle 得先写一个可计算的版本并证明它与 `CN` 一致。
3. **服务状态按 ≃ 比较。** `Service` 的 ≃ 是命题;抽取后的比较要求可判定的 ≃(注册表是相等,监听器是"互为排列",都可判定)。
4. **动态加载的运行时精化。** 文献中的精化对象是数据结构、编译器变换、分布式协议;
   "插件运行时的控制层精化一个生命周期演算"没有先例。JS 的 async 生成器与 `Promise.all` 也没有现成的 Iris 语言。

**这些领域有、演算或 checker 没有的。**

1. **调度控制。** checker 的 `settle()` 只等待,不控制。C 类见证(次序依赖)在真实宿主上没复现,原因正是异步延迟让同一方总赢
   (REPORT)。PULSE、fast-check 调度器、NodeRacer 都能系统地改变交错。
2. **最短化。** QuickCheck 系的工具自带收缩;checker README 说"还没有自由搜索和最短化"。
3. **有界精化检查。** TLC 能对小实例检查"实现 ⇒ 规格";Rocq 证明是参数化的,但每改一条规则都要修证明。
4. **线性一致性工具。** D6 把逻辑原子性定为义务,但仓库里没有检查它的手段。

## 4. 候选课题

### T1. 抽取 `step`,对 `rt.js` 与真实 Cordis 做落定粒度的 lockstep 测试

- **目标。** 检查运行时(先 `edsl/runtime/rt.js`,再 vendored Cordis 4.1.0)在每次编排输入落定之后,
  与演算的 quiet 状态在重命名意义下一致。对应定理:`dynamic_agree`、`static_assembly`(无失败时),
  `recovery_from_init`(卸载之后)。
- **做法。**
  1. 新建一个 Rocq 文件(不改现有文件),实例化 `K := nat`、`C := nat` 加一张程序表、`Σ := Sum Registry Listeners`
     (`Compose.v`);写 `quietb`(对 `names γ` 中每个 n,`lifecycle_labels n` 全部返回 `None`)和带燃料的
     `settle_model`(按固定次序反复走第一个可用的生命周期标签)。燃料由 `termination` 保证够用,可以顺手证明
     `settle_model` 在燃料足够时到达 quiet。
  2. 写可计算的规范名函数,证明它与 `CN` 一致,作为观察函数;≃ 用可判定版本。
  3. 抽取到 OCaml,用 js_of_ocaml 编译成 JS 模块。
  4. 在 Node 中用 fast-check 的状态机测试:命令是 `Insert c`、`Dispose i`、`Restart i`、`Reset i`(按插入序号,
     同 `Dynamic.v` 的 `Input`);每条命令后被测系统 settle,模型 `settle_model`,比较观察。
  5. 适配器把随机生成的 `Prog` 组件变成插件:`POp` 变成对一个宿主注册表服务的调用,`PProvide` 变成提供服务,
     `PSpawn` 变成 `ctx.plugin`。生成器只产生满足 `Total`、有秩、`Bounded` 的组件(`Summary.v` 的义务)。
     复用 checker 的 `exec.mjs` 进程隔离和 `cordisSnapshot()`。
  6. 有失败的组件单独一组:模型对每个可达 quiet 状态做有界穷举(终止定理保证有限),检查被测系统落在集合内。
- **预期产出。** 对 `rt.js`:应完全一致,任何分歧都是可信基中的错误(EDSL.md 把垫片列为可信基)。
  对 Cordis:一张"预期分歧表",逐条对应 DESIGN 的差异(c:提供冲突在运行时抛错;e:disposer 并发;
  p:按回调注销),每条有最短反例;以及可能的新分歧。
- **风险。** Cordis 内部状态要读私有字段,抽象函数可能随版本变;`settle()` 是启发式,落定判断不可靠时要判无结论;
  抽取后的状态用函数表示偏函数(`fupd`、`bupd`),鬼字段 `oplog`、`inilog` 会拖慢,要在实例化时去掉或忽略。
- **工作量。** 中(只对 `rt.js` 为小到中)。

### T2. 受控调度下的轨迹级精化检查

- **目标。** 不只比落定状态,而是检查 Cordis 的**每一步**都是演算的一步,覆盖 DESIGN D6 的前提:
  每条控制规则在一个同步片段内完成;差异 h 的"在途迭代落地"对应 target 已变时的 `L-Step` 加随后的 `L-Divert`;
  守卫 `held`(`unload_waits`)在真实 Cordis 中确实先于任何 disposer。
- **做法。** 在 vendored Cordis 的状态转换处和 disposer 调用处打日志;插件的每个服务操作包成由测试控制完成时机的 promise
  (fast-check 调度器,或照 NodeRacer 的做法推迟事件);把日志映射成 `Label` 序列,用抽取出的 `step` 逐步重放,
  每步要求 `Some` 且抽象状态一致。日志不完整时(例如两次 disposer 之间没有观察点),像 Cirstea 等那样在模型侧做有界搜索补齐。
- **预期产出。** 对 Cordis 的若干行为给出"符合演算"或"不符合,反例如下"的结论;差异 e 会以"非 LIFO 的 `L-Undo` 次序"出现,
  可以据此量化"什么服务上 `Promise.all` 真的出问题"(D6 的判据:逆两两可交换时无害)。
- **风险。** 映射 `Promise.all` 并发撤销到逐项 `L-Undo` 需要允许模型侧选排列;插桩改动 vendored 代码,结论只对该版本成立;
  MongoDB 的经验说明粒度不匹配是主要风险,不过这里演算本来就是照 `fiber.ts` 的结构写的,粒度差距比 RaftMongo 小。
- **工作量。** 中。依赖 T1 的抽取与观察函数。

### T3. 服务操作的线性一致性测试(D6 逻辑原子性)

- **目标。** 检查 dsh 宿主服务(webServer、tools、settings 等,checker 的 `host.mjs` 已有桩的那些)的真实实现,
  在操作内部带 `await` 时是否仍然可线性化,逆是否同样原子。这是精化路线第 3 档留给服务作者的义务。
- **做法。** 顺序规格用 Rocq 中对应服务的 `run`(`Services/Registry.v`、`Services/Listeners.v`)抽取;
  用调度器生成并发的异步调用历史(包括 disposer);用 Wing-Gong 式或 Lowe 的算法判定小历史。
  专门构造 D6 列出的典型错误:先读、`await`、再按旧值写回;操作中途同步调用回调造成重入。
- **预期产出。** 逐服务的结论表,与 PLUGIN-AUDIT 的服务一侧互补;违反者给出最短历史。
- **风险。** 宿主服务离开 dsh 可能跑不起来(checker 用的是桩,不是实现);真实服务的状态比 Rocq 模型丰富,需要投影。
- **工作量。** 小到中。

### T4. TLA+ 中检查 Cordis 实际算法对演算的有界精化

- **目标。** 用模型检测回答 Rocq 改起来贵的问题:Cordis 的六态算法、epoch 检查、`Promise.all` 撤销在小配置下是否精化演算;
  放宽原子性后会坏在哪里。
- **做法。** 把演算写成 TLA+ 规格 Spec;把 `fiber.ts` 的控制逻辑写成 PlusCal 的 Impl,每个 await 是一个标号(原子步的边界);
  精化映射照 DESIGN 差异 a。用 TLC 对 2–3 个组件、短程序检查 Impl ⇒ Spec,以及:
  (1)把 `L-Begin` 拆成"读 visible"与"写 ω"两步,复现 D6 所说的 TOCTOU 与良构性第 4 条的违反;
  (2)disposer 并发时恢复是否仍成立;(3)编排输入穿插时、弱公平下"最终落定";
  (4)可选依赖扩展在违反两条义务时的活锁(manager README 中 M7 的反例)。
- **预期产出。** 有界的精化证据和最短反例轨迹;给 DESIGN 中"对 Cordis 的建议"一列(如差异 e 改串行 LIFO)提供具体依据。
- **风险。** TLA+ 规格与 Rocq 演算成为两份真相,可能不一致。缓解:用 T1 的抽取物随机生成轨迹,检查 TLA+ 规格接受同样的轨迹。
  状态爆炸限制了配置大小。
- **工作量。** 中。

### T5. 证明之前先用 QuickChick 测试猜想

- **目标。** 对演算中尚未证明、或明确排除在定理之外的说法,先找反例或建立信心,再决定是否投入证明。
- **做法。** 在 Rocq 内为小组件写生成器,把性质写成可判定的布尔函数,对象包括:
  `O-React` 穿插时的合流(RULES 第 5 节第 4 条说合流不覆盖运行期);直接 dispose 启动时 spawn 的子 fiber
  破坏 `SLInv` 并使两次执行终态不同(DESIGN 差异 q 的论断);可选依赖在在场集变化后的落地(EXTENSIONS 说尚不在扩展内);
  D6 的 `Promise.all` 判据。
- **预期产出。** 反例(写进文档作为"为什么定理要这条前提"的例子)或回归测试;每个找不到反例的性质附测试规模。
- **风险。** QuickChick 与 Rocq 9.1 的兼容情况本次没有核实;性质中的 ≃ 必须可判定;生成满足 `Total` 与秩约束的组件不容易,生成器可能偏。
- **工作量。** 小到中。

### T6. Iris 中的精化证明(研究级,建议后置)

- **目标。** 证明一个 JS 运行时精化演算,使安全性定理(`summary_wf`、`summary_recovery`、`summary_confluence`)
  传到实现上;先对 `rt.js`,而不是 Cordis。
- **做法。** 仿 Goose:定义 TS 的一个受限子集(async 函数、生成器、`Promise`、对象),翻译到 Iris 中的一个语言,
  该语言要有事件循环与 promise 的语义(可参照 λp 与 Loring 等的模型);用 Trillium 风格的轨迹精化把实现与 `step` 联系起来;
  服务操作用原子三元组作为接口(D6)。
- **预期产出。** 第一个"插件运行时精化生命周期演算"的机械化证明。
- **风险。** 地基全要自建(本次检索没有找到 Iris 中现成的 JS 异步语言);翻译器进入可信基;活性(终止、进展)需要公平性,
  Trillium 一类框架能做但更难;Cordis 版本变化会使证明失效。
- **工作量。** 大。在 T1、T2 证明 `rt.js` 与演算一致之前不建议开始。

### 排序

按贴合度、收益、工作量:T1 最先(复用 checker 基础设施,产出直接);T3、T5 小而独立,可以并行;
T2 依赖 T1;T4 用于回答 Cordis 改动建议的取舍;T6 后置。

## 5. 参考文献

核实方式:WebSearch 检索出版记录(出版方页面、DBLP、researchr、作者主页或 arXiv),核对作者、题目、会议或期刊、年份。

- [Arts 2006] Thomas Arts, John Hughes, Joakim Johansson, Ulf Wiger. Testing telecoms software with Quviq QuickCheck. ACM SIGPLAN Erlang Workshop, 2006, pp. 2–10.
- [Bodin 2014] Martin Bodin, Arthur Charguéraud, Daniele Filaretti, Philippa Gardner, Sergio Maffeis, Daiva Naudžiūnienė, Alan Schmitt, Gareth Smith. A Trusted Mechanised JavaScript Specification. POPL 2014, pp. 87–100.
- [Chajed 2019] Tej Chajed, Joseph Tassarotti, M. Frans Kaashoek, Nickolai Zeldovich. Verifying concurrent, crash-safe systems with Perennial. SOSP 2019.
- [Cirstea 2024] Horatiu Cirstea, Markus A. Kuppe, Benjamin Loillier, Stephan Merz. Validating Traces of Distributed Programs Against TLA+ Specifications. SEFM 2024, LNCS(arXiv:2404.16075)。
- [Claessen 2000] Koen Claessen, John Hughes. QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs. ICFP 2000, pp. 268–279.
- [Claessen 2009] Koen Claessen, Michał Pałka, Nicholas Smallbone, John Hughes, Hans Svensson, Thomas Arts, Ulf Wiger. Finding Race Conditions in Erlang with QuickCheck and PULSE. ICFP 2009, pp. 149–160.(作者表以 DBLP 为准,有的来源少列 Svensson。)
- [da Rocha Pinto 2014] Pedro da Rocha Pinto, Thomas Dinsdale-Young, Philippa Gardner. TaDA: A Logic for Time and Data Abstraction. ECOOP 2014, LNCS 8586, pp. 207–231.
- [Davis 2017] James Davis, Arun Thekumparampil, Dongyoon Lee. Node.fz: Fuzzing the Server-Side Event-Driven Architecture. EuroSys 2017, pp. 145–160.
- [Davis 2020] A. Jesse Jiryu Davis, Max Hirschhorn, Judah Schvimer. eXtreme Modelling in Practice. PVLDB 13(9), 2020, pp. 1346–1358.
- [de Vries, Hackage] Edsko de Vries. quickcheck-lockstep: Library for lockstep-style testing with quickcheck-dynamic. Hackage 上的 Haskell 库(软件,不是论文)。
- [Endo 2020] André Takeshi Endo, Anders Møller. NodeRacer: Event Race Detection for Node.js Applications. ICST 2020, pp. 120–130.
- [fast-check 文档] fast-check 官方文档的 Model based testing 与 Race conditions 两节(fast-check.dev)。软件文档,不是论文;核实了 `modelRun`、`asyncModelRun`、`scheduledModelRun` 与调度器的存在。
- [Fragoso Santos 2018] José Fragoso Santos, Petar Maksimović, Daiva Naudžiūnienė, Thomas Wood, Philippa Gardner. JaVerT: JavaScript Verification Toolchain. POPL 2018(PACMPL 2, Article 50)。
- [Fragoso Santos 2020] José Fragoso Santos, Petar Maksimović, Sacha-Élie Ayoun, Philippa Gardner. Gillian, Part I: A Multi-language Platform for Symbolic Execution. PLDI 2020.
- [Gäher 2022] Lennard Gäher 等. Simuliris: A Separation Logic Framework for Verifying Concurrent Program Optimizations. POPL 2022(PACMPL 6)。(完整作者表未逐一核对,第一作者与出处已核实。)
- [Herlihy 1990] Maurice P. Herlihy, Jeannette M. Wing. Linearizability: A Correctness Condition for Concurrent Objects. ACM TOPLAS 12(3), 1990, pp. 463–492.
- [Holzmann 1997] Gerard J. Holzmann. The Model Checker SPIN. IEEE Transactions on Software Engineering 23(5), 1997, pp. 279–295.
- [Hughes 2016] John Hughes, Benjamin C. Pierce, Thomas Arts, Ulf Norell. Mysteries of DropBox: Property-Based Testing of a Distributed Synchronization Service. ICST 2016, pp. 135–145.
- [Jackson 2002] Daniel Jackson. Alloy: A Lightweight Object Modelling Notation. ACM TOSEM 11(2), 2002, pp. 256–290.
- [Jung 2018] Ralf Jung, Robbert Krebbers, Jacques-Henri Jourdan, Aleš Bizjak, Lars Birkedal, Derek Dreyer. Iris from the ground up: A modular foundation for higher-order concurrent separation logic. Journal of Functional Programming 28, e20, 2018.
- [Frumin 2018] Dan Frumin, Robbert Krebbers, Lars Birkedal. ReLoC: A Mechanised Relational Logic for Fine-Grained Concurrency. LICS 2018, pp. 442–451.(扩展版 ReLoC Reloaded,LMCS 2021。)
- [Lamport 2002] Leslie Lamport. Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers. Addison-Wesley, 2002.
- [Lamport 2009] Leslie Lamport. The PlusCal Algorithm Language. ICTAC 2009, LNCS 5684, pp. 36–60.
- [Letouzey 2002] Pierre Letouzey. A New Extraction for Coq. TYPES 2002, LNCS 2646, pp. 200–219(印行于 2003)。
- [Li 2021] Yishuai Li, Benjamin C. Pierce, Steve Zdancewic. Model-Based Testing of Networked Applications. ISSTA 2021, pp. 529–539.
- [Loring 2017] Matthew C. Loring, Mark Marron, Daan Leijen. Semantics of Asynchronous JavaScript. DLS 2017, pp. 51–62.
- [Lowe 2017] Gavin Lowe. Testing for Linearizability. Concurrency and Computation: Practice and Experience 29(4), 2017.
- [MacIver 2019] David R. MacIver, Zac Hatfield-Dodds 等. Hypothesis: A new approach to property-based testing. Journal of Open Source Software 4(43), 1891, 2019.(Hypothesis 的状态机测试功能未在该文中核实。)
- [Madsen 2017] Magnus Madsen, Ondřej Lhoták, Frank Tip. A Model for Reasoning About JavaScript Promises. OOPSLA 2017(PACMPL 1, Article 86)。
- [McKeeman 1998] William M. McKeeman. Differential Testing for Software. Digital Technical Journal 10(1), 1998, pp. 100–107.(书目信息由多处二手引用核实,原文未读到。)
- [Paraskevopoulou 2015] Zoe Paraskevopoulou, Cătălin Hriţcu, Maxime Dénès, Leonidas Lampropoulos, Benjamin C. Pierce. Foundational Property-Based Testing. ITP 2015, LNCS 9236, pp. 325–343.
- [Park 2015] Daejun Park, Andrei Stefănescu, Grigore Roşu. KJS: A Complete Formal Semantics of JavaScript. PLDI 2015, pp. 346–356.
- [Sampaio 2020] Gabriela Sampaio, José Fragoso Santos, Petar Maksimović, Philippa Gardner. A Trusted Infrastructure for Symbolic Analysis of Event-Driven Web Applications. ECOOP 2020(LIPIcs 166)。另见 Gabriela Cunha Sampaio 的博士论文 A Trusted Infrastructure for Symbolic Analysis of Event-based Web APIs,Imperial College London,2022,其中覆盖 promise 与 async/await。
- [Timany 2024] Amin Timany, Simon Oddershede Gregersen, Léo Stefanesco, Jonas Kastberg Hinrichsen, Léon Gondelman, Abel Nieto, Lars Birkedal. Trillium: Higher-Order Concurrent and Distributed Separation Logic for Intensional Refinement. POPL 2024(PACMPL 8, Article 9)。
- [Vouillon 2014] Jérôme Vouillon, Vincent Balat. From bytecode to JavaScript: the Js_of_ocaml compiler. Software: Practice and Experience 44(8), 2014, pp. 951–972.
- [Xia 2020] Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, Steve Zdancewic. Interaction Trees: Representing Recursive and Impure Programs in Coq. POPL 2020(PACMPL 4, Article 51)。
- [Yang 2011] Xuejun Yang, Yang Chen, Eric Eide, John Regehr. Finding and Understanding Bugs in C Compilers. PLDI 2011, pp. 283–294.

**未核实。**

- quickcheck-state-machine(Haskell 的状态机测试库):本次没有检索核实,正文未依赖它。
- QuickChick 对 Rocq 9.1 的支持情况:检索配额用完,未核实(见 T5 的风险)。
- "Iris 中没有现成的 JS 事件循环与 promise 语言"是本次检索未见的结论,不是文献断言。
