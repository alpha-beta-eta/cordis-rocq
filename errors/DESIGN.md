# 错误处理：设计

本目录把错误处理放进演算，与现有形式化隔离。

**定位。** 目标是一个自足的演算：每条规则按它自己的道理取舍，即让定理成立、让一个好的运行时有据可依，
而不是贴近 Cordis 现在的实现。Cordis 的现状（第 2 节）是动机和证据：它在哪里出错、哪里已经做对了。
演算与 Cordis 不同的地方，整理成给 Cordis 的改进或新功能建议（第 6 节）。Cordis 的行为只在两种情况下
进入形式化：作为反例（说明某种做法为什么不好），或作为 difftest 的对照对象。

## 0. 为什么，原则，隔离

### 0.1 核心演算怎样对待错误

核心（`theories/Calculus.v`）里错误只有一种去处：fiber 带着错误标记进入 Unloading，撤销完停在
`Inactive (Some ξ)`，之后只能由编排者 `O-Reset`。错误标记有四种：

| ξ | 来源 | 什么时候 |
|---|---|---|
| `EUser` | 程序走到 `PFail` | 由程序决定 |
| `EOp` | 服务操作返回 `None` | 由服务状态决定，而服务状态可能与调度有关（同名登记，谁先谁成功） |
| `EUnresolved` | 操作的键解析不到视图中的 pid | 不变式下不会发生 |
| `EConflict` | `PProvide` 的键已被绑定，或 `PSpawn` 的子组件与在场 fiber 的提供集合相交 | `PSpawn` 的检查与调度有关 |

各条定理对错误的态度：

- 保持性、顺序、恢复精确性、终止、进展：对含失败的执行照样成立。进展的"稳定"把失败的 fiber 算作停下
  （`Progress.settled_fiber`）。
- 合流：所有版本都以终态**没有失败的 fiber** 为前提（`Summary.v` 第 4 条，`NoFailed`），因为有的失败
  与调度有关。

演算没有的：

- **外部失败**：启动程序中读外部世界（文件、网络）失败。演算没有外部读取。
- **逆的失败**：服务操作给出的逆 g 在撤销时失败。演算假定 g 是全函数。
- **暂时的接纳冲突**：新组件与一个已退役、但还没被移除的 fiber 提供同一个键。核心直接拒绝 `O-Insert`，
  编排者得不到"稍后可以"的信号。

### 0.2 原则

| # | 原则 | 含义 |
|---|---|---|
| P1 | **失败由程序与环境决定，不由调度决定** | 同样的程序、同样的外部结果，哪些 fiber 失败、带什么标记，与调度无关。合流因此可以把失败包括进来 |
| P2 | **暂时的障碍是等待，不是失败** | 一定会消失的障碍（一个正在被移除的 fiber 占着键）让 fiber 等；只有不会自行消失的条件才是失败 |
| P3 | **失败是局部的，运行时自己的动作不失败** | 失败不传播给父 fiber 和依赖者；撤销一定走完。能失败的只有用户提供的东西：程序、服务操作、逆、外部读取 |
| P4 | **失败可归因** | 错误标记说明原因；没能撤销的效应有记录，恢复精确性的差额恰好是这些记录 |
| P5 | **保守** | 不出错时就是核心 |

### 0.3 隔离

- 代码放在 `errors/theories/`，逻辑名 `CordisErr`。它可以 `Require` 核心（`Cordis.*`）和需要的
  `Cordis.Ext.*`；核心与 `theories/Ext/` 都不 import 它（`grep -rn "CordisErr" theories/` 应为空）。
- 有自己的 `errors/_CoqProject` 与 `errors/build.sh`，根目录的构建不变，先编译核心再编译本目录。
- 每个模块给一条保守性定理（P5）。能归约到核心的模块，安全性等结论直接从核心搬过来。
- 文档只放在本目录，定稿之前不改 `docs/` 下的文件。

## 1. 核心中违反原则的地方

- **P1。** `L-Step` 在 target 改变之后仍然可以走（`may_step` 只在 `PDone` 处检查 target），所以加载中途
  target 已经转向时，`PFail` 与 `L-Divert` 都可走：前者得到 `Inactive (Some EUser)`，后者得到
  `Inactive None`。结局由调度决定。第 4.0 节处理。
- **P1。** `PSpawn` 的冲突检查、服务操作因别的 fiber 先操作而被拒，都与调度有关。第 3 节处理。
- **P2。** `O-Insert` 遇到与已退役 fiber 的冲突也直接拒绝。第 4.2 节处理。
- **P1 与重试。** 失败的 fiber 只能由 `O-Reset` 重新开始，即使它的依赖已经换了提供者、失败的理由不再成立。
  第 4.4 节讨论。

## 2. Cordis 的现状（证据）

依据：上游 `D:\cordis\packages\core\src`（`7f92195`，2026-11-07）与 dsh vendored 版本
（`D:\deepseek-harness\vendor\cordis\src`，dsh `fcc0ad4`）。只读代码和上游测试得出，没有另写测试复现。
行号指上游，除非注明。两份代码没有 `AbortSignal`，也没有 `internal/error` 事件；错误存在私有字段
`Fiber._error`（`fiber.ts:130`），状态由 `_getState()` 按 `uid === null` → DISPOSED、`_error` → FAILED、
epoch ≠ INACTIVE → ACTIVE、否则 PENDING 的顺序算出（`fiber.ts:365-370`）。

### 2.1 各类错误

| 错误 | Cordis 的处理 | 终态 | 对照原则 |
|---|---|---|---|
| `apply` 同步抛错、promise 拒绝（含 await 的外部 IO）、生成器 `next()` 抛错 | `_reload` 捕获（`fiber.ts:462-470`），记日志；epoch 未变时置 `_error`，然后 `_unload` 撤掉已登记的效应 | FAILED | 程序失败与外部失败不区分（P4） |
| `provide` 的键已登记 | `reflect.ts:225` 抛错，在 `apply` 中即 `apply` 失败。旧 owner 的 `uid` 置空并**不**删除它的 impl，impl 要等它的撤回 disposer 运行（`reflect.ts:234`），而 `_unload` 先等全部依赖者退出（`fiber.ts:485-487`） | FAILED，旧绑定删掉之后也不重试 | 违反 P2、P1（#358） |
| 运行期 `provide`、`ctx.effect` 抛错（如在监听器里） | 只抛给调用者 | fiber 状态不变 | 符合 P3 |
| fiber 级 disposer 抛错 | `_unload` 中每个顶层 disposer 单独 `try/catch` 记日志，`Promise.all` 照常完成（`fiber.ts:492-502`） | 与没出错时相同，不置 `_error` | 符合 P3；泄漏没有记录（P4） |
| 同一个 `ctx.effect` 内的子 disposer 抛错 | 子 disposer 按顺序串行；同步抛错会中断循环，而条目已经 `splice(0)` 移走，**同组剩下的 disposer 不再调用**；异步拒绝时后面的 `.then(dispose)` 同样跳过（`fiber.ts:298-311`，vendored `fiber.ts:437-446` 相同） | 泄漏同组较早登记的资源 | 违反 P3：一项失败连带别的项 |
| 依赖缺失 | 不是错误，epoch 为 INACTIVE（`fiber.ts:418-430`） | PENDING | 符合 P2 |
| 提供者失败 | 依赖者被通知后卸载 | 依赖者 PENDING，不是 FAILED；提供者经 `update()` 恢复后自动重载 | 符合 P3 |
| 子 fiber 失败 | 只记在子 fiber 上；父 fiber 的 `apply` 若 `await ctx.plugin(child)` 则父 fiber 也失败 | | 显式等待时传播，其余符合 P3 |
| 父 fiber 失败、重启、dispose | `_unload` 运行子 fiber 的 dispose 效应 | 子 fiber DISPOSED | 与核心的 `L-RetireChild` 一致 |

### 2.2 时机

- **加载中途 target 转向，之后 `apply` 失败**：`fiber.ts:466` 的守卫使错误只记日志，不置 `_error`；
  随后按新的 epoch 卸载，再进入 LOADING、PENDING 或 DISPOSED。被取代的加载永远不会以 FAILED 结束。
  这一点 Cordis 已经做对了（P1），注释原话是 "cannot fail the new target"。
- **promise 形式的 `apply` 不能中途取消**：`_reload` 等整个 promise 完成，在此之前 `dispose()`、`restart()`
  都挂起。异步生成器在两次 `yield` 之间检查 epoch 并 `iter.return()`（vendored 版本不调 `return()`）。
- **重启过程中 disposer 抛错**：吞掉，照常重新加载。

### 2.3 失败之后

- `_error` 只由 `update()`（`fiber.ts:543`）和 `_replace()`（`fiber.ts:413`）清除，对应 `O-Reset`。
- `restart()` 对 FAILED 无效：`_setEpoch` 见 `_error` 直接返回（`fiber.ts:436`）。
- 依赖变化不会让 FAILED 的 fiber 重新加载（上游测试 `fiber.spec.ts:93`）。

### 2.4 顺带发现的 Cordis 问题

只读代码得出，都还没有写测试确认，留作 issue 候选：

1. 上游 `update()`/`_replace()` 作用于依赖缺失的 FAILED fiber 时，新 epoch 与旧 epoch 同为 INACTIVE，
   `_setEpoch` 提前返回，`state` 停在过时的 FAILED，不发 `internal/status`。
2. 上游对 PENDING 或 FAILED 的 fiber `dispose()` 不运行 `_unload`，失败之后登记在它上面的效应泄漏。
   vendored 版本已修（总是 `_unload`）。
3. 构造期 `_refresh` 中 `internal/status` 监听器抛错，fiber 被置 `_error` 但 `apply` 照样运行，最终 FAILED
   且效应从不卸载；`_reload`/`_unload` 中它抛错会使 `inertia` 拒绝，并跳过依赖者通知。
4. 同一个 `ctx.effect` 内一个 disposer 抛错，同组剩下的 disposer 不再调用（2.1 表中）。
5. 撤回 provide 时 `notify` 抛错，impl 已离开 `store` 却留在 `provisions` 中。

## 3. 失败按由什么决定分类（P1）

| 类别 | 例子 | 对合流的影响 | 处理方向 |
|---|---|---|---|
| **程序决定** | `PFail`；对只在本 fiber 内可见的状态操作被拒 | 无：同样的输入，每次执行都失败 | 合流可以把这些失败包括进来 |
| **环境决定** | 外部读取失败；逆失败 | 终态依赖外部结果 | 合流相对于外部结果的**预言**陈述（第 4.1、4.3 节） |
| **调度决定** | 加载中途 target 转向时 `PFail` 与 `L-Divert` 的竞争；`PSpawn` 冲突；同名登记谁先谁赢 | 破坏合流 | 第一种由 4.0 消除；其余或者消除（改成等待，或者让服务对可能相遇的操作不拒绝），或者列为义务 |

核心用 `NoFailed` 把三类一起排除，结论因此偏弱：一个插件只要可能因自身逻辑失败，合流就不再对它说任何话。
目标定理：

> 在没有**调度决定**的失败的执行上，终态（包括哪些 fiber 失败、带什么错误标记）与调度无关。

做法是证明判据成立时，失败的发生与否由理想轨迹决定，进入 `Episode.v` 的路径确定性论证。

## 4. 模块

### 4.0 过时的加载不记失败（`Superseded.v`，已完成）

**规则。** 加载中的 fiber 在 target 已经转向时走到失败（`PFail`、操作被拒、provide 冲突、4.1 的外部失败），
不记错误标记，按 `L-Divert` 进入 `Unloading acc w None`。

**理由（P1）。** 这次加载针对的视图已经过时，它的失败说明不了当前 target 下会怎样；记下失败，终态就取决于
失败和转向谁先发生。去掉这一支之后，一个 fiber 只在当前有效的加载里失败。Cordis 恰好也是这样做的（2.2 节）。

**要证的。**

1. 它是核心的精化：新规则的每一步都是核心的一步，所以核心的全部安全性结论直接适用。
2. 它消除一种调度决定的失败：一次加载以失败结束，当且仅当这次加载按理想轨迹走到失败，且直到失败那一步
   target 都没变。

**完成情况。** `Superseded.v`，约 270 行，没有新公理：

| 结论 | 名字 |
|---|---|
| 每个 `sstep` 都是核心的一步，标签相同，或以 `LDivert n` 代替 `LStep n` | `sstep_core` |
| 每个 `sstep` 执行都是核心的执行；核心保持的性质 `sstep` 也保持 | `srun_core`、`sinv_step` |
| 安全性 | `swf_reachable` |
| 两者在同样的标签上可走，静止相同；进展 | `sstep_some`、`squiet_iff`、`sprogress_reachable` |
| 终止 | `stermination`、`stermination_reachable` |
| 加载以失败结束，只发生在 target 仍是这次加载承诺的视图时 | `sfail_current` |

第 2 条只证了一个方向（失败蕴涵 target 未变）；"按理想轨迹走到失败"那一半留给第 3 节。

### 4.1 外部读取与外部失败（`Async.v`）

**构造。** 程序多一个外部读取：

```coq
Inductive EProg :=
| EDone | EFail
| EOp (k : K) (a : Op Σ) (κ : Out Σ -> EProg)
| EProvide (k : K) (s : St Σ) (P : EProg)
| ESpawn (c : C) (P : EProg)
| EExt (e : Ext) (κ : R -> EProg).        (* R：外部结果的统一类型 *)
```

外部读取不碰 S，不进累加器。结果由环境给出：成功给出 `r : R`，失败让 fiber 带新的错误标记 `EExt` 进入
Unloading（P4：与程序失败区分开，编排者可以据此决定是否重试）。服务操作仍然是原子步；需要外部数据的操作写成
"`EExt` 之后跟一个 `EOp`，外部数据作为操作参数"（D6 的 `prepare`/`commit`）。

**两种语义，取哪一种是设计决定。**

- **确定的外部读取**：结果是组件和视图的函数 `ρ : C → View → nat → option R`（同样的依赖，读到同样的结果）。
  演算就是核心的一个实例：组件表取 `prog' c = 按 ρ 展开 body`，外部读取不占步骤，合流直接成立。
  运行时要做到这一点，需要把外部结果按视图缓存：同一视图下重新加载时复用上次的结果。
- **每次加载各自的外部结果**：`ρ` 在每次加载时重新选定，同 `Ext/Optional.v` 的 `(c, S)`：fiber 的组件
  取成 `(c, ρ)`，Inactive 时重选。安全性、恢复、终止、进展仍由归约得到；合流只能相对于每个 fiber 最后一次
  加载的预言来陈述，证明不能直接复用 Optional 的机器。

倾向于以前者为主（P1 在它之下没有例外），后者作为"外部世界不可重复"时的弱保证。

**等待外部结果。** 归约里外部读取不占步骤，"在等"这个状态看不见。安全性不受影响；要谈外部 IO 的公平性
（进展需要在途读取最终返回）时，再给不归约的版本。和 4.0 组合时，target 转向之后的外部失败按 divert 处理。

### 4.2 暂时的接纳冲突（`Admit.v`）

**问题。** 核心中组件静态声明提供集合，`O-Insert` 拒绝与在场 fiber 相交的组件（论文的 O-Insert）。这个
设计本身是对的：单一提供者由构造保证，依赖是否无环可以静态判定。但"在场"包括已退役、尚未移除的 fiber，
于是"dispose 旧提供者后立即插入新提供者"被拒绝，编排者得不到"稍后可以"的信号（违反 P2）。

**设计：退役冲突时排队。**

- 新组件只与**已退役**的 fiber 冲突时，`O-Insert` 接纳它，但它处于**排队**状态，不能 `L-Begin`，直到冲突的
  fiber 全部被移除。
- 与**未退役**的 fiber 冲突时，照旧拒绝。未退役的 fiber 会继续存在，或者卸载后重新加载、再次提供同一个键，
  这时排队会让两者争抢，结果与调度有关（P1）。

排队发生在 `L-Begin` 之前，排队的 fiber 没有任何效应，这是静态提供集合带来的好处。若提供集合只在运行时知道
（如 Cordis），冲突只能在 `provide` 时发现，那时 fiber 已经带着部分效应，只能等在 `provide` 处或失败；
#358 中建议的"owner 在 unloading 就等在 provide 处"就是这种情况，而且条件过宽（包括会重新加载的 owner）。

**要证的。**

1. 保守性：不出现退役冲突时就是核心。
2. 与核心的对应：每次执行对应核心里一次"把 `O-Insert` 推迟到冲突的 fiber 移除之后"的执行。排队的 fiber
   没有效应，这个推迟是平凡的；唯一的麻烦是名字（核心在插入时分配名字），对应关系要在重命名意义下陈述，
   而合流本来就是在重命名意义下的。安全性、终止、合流由此从核心得到。
3. 进展：quiet 状态中没有排队的 fiber，因为退役的 fiber 终将被移除（终止加进展）。

**反例（已完成）。** 先算清楚不这样做会怎样。`astep` 是 Cordis 的做法：`O-Insert` 不检查冲突，冲突由
`PProvide` 发现，失败且永久。把 #358 的序列（插入 P、插入依赖者 D、dispose P 后不等落定再插入 P）写成
计算出来的两次执行，沿用 `Examples/Basic.v` 的登记表例子。编排输入相同，只有生命周期步的先后不同：
新 P 先加载时停在 `Inactive (Some EConflict)`，D 停在 Inactive，`tools` 未绑定，两者都不能再开始
（`early_obs`、`early_stuck`）；旧 P 先被移除时全部 Active（`late_obs`）。同一时刻核心拒绝这次插入
（`core_refuses`）。新 P 的依赖为空、target 从未改变，所以 4.0 救不了它：这是接纳的问题，不是时机的问题。

### 4.3 逆的失败（`UndoFail.v`）

**构造。** 撤销一项 `UOp` 时，环境可以让逆 g 失败。这一项照样出栈，g 不施加，绑定状态不变，撤销继续
（P3：卸载一定走完，一项失败不连带别的项）。失败的令牌记进 `leaked`（P4）。`UProv`、`USpawn` 的撤销是
运行时自己的动作，不会失败（P3）。

**设计决定：泄漏要不要标在 fiber 上。** 泄漏的操作仍留在服务状态里，fiber 若随后重新加载，可能撞上自己
留下的东西（比如同名登记还在，重新登记被拒）。两种做法：

- 只记录，不影响生命周期：重新加载照常，撞上时按 `EOp` 失败，原因可以追溯到 `leaked`。
- 卸载结束时若有泄漏，fiber 停在 `Inactive (Some ELeak)`，等编排者 `O-Reset`。

前者保持"卸载的结局只由 target 决定"，后者让问题在源头暴露。倾向于前者，`ELeak` 留作运行时的诊断信息。

**要证的。**

1. 生命周期对逆的失败是鲁棒的：保持性、顺序、终止、进展照样成立。
2. 恢复精确性的精确版本：一个效应来了又走之后，每个绑定的状态 ≃ 省去该效应中**撤销成功**的那些操作之后的
   执行所达到的状态；与理想状态的差恰好是 `leaked`。没有逆失败时退回 `Recovery.recovery_exact`。
3. 合流：相对于逆的结果的预言。

**复用。** 撤销失败后的状态与核心的结果只差一个绑定的 `bst`。`WF`、`Ordering`、`Termination`、`Progress`
的不变式与度量都不看 `bst`，证一条迁移引理即可；恢复与服务状态部分要重写，复用 `ServiceSeq.v` 的重放引理。

### 4.4 失败之后（讨论，暂不形式化）

- **传播。** 核心中失败不传给父 fiber，父 fiber 失败时子 fiber 随撤销退役，提供者失败时依赖者回到 Inactive。
  符合 P3，保持不变。
- **失败按视图记录。** 现在 `Inactive (Some ξ)` 永久挡住 `L-Begin`。按 P1，程序决定的失败只对它所在的视图
  成立：换一个视图（依赖换了提供者），失败的理由未必还在。候选规则：失败标记带上视图 w，target 变得不同于 w
  时失败自动清除，fiber 可以重新开始；target 仍是 w 时保持失败，等 `O-Reset`。它与 4.0 正好互补：4.0 保证
  失败只在当前视图下记下，这条保证失败只对那个视图有效。quiet 终态中失败的 fiber，都是在终态的 target 下失败的。
- **反应中的失败。** `O-React` 起的子 fiber 失败只影响它自己，核心已覆盖（`Runtime.v`）。

## 5. 定理目标汇总

| 模块 | 保持性、顺序 | 恢复 | 终止、进展 | 合流 |
|---|---|---|---|---|
| 4.0 过时的加载不记失败 | 核心的子集（已证） | 核心的子集 | 核心的子集（已证） | 第 3 节的第一块 |
| 4.1 确定的外部读取 | 核心的实例 | 核心的实例 | 核心的实例 | 核心的实例 |
| 4.1 每次加载的外部结果 | 归约 | 归约 | 归约（不含外部 IO 的公平性） | 相对于最后一次加载的预言 |
| 4.2 排队 | 推迟插入的对应 | 同上 | 同上，加 quiet 时无排队 | 同上，在重命名意义下 |
| 4.2 Cordis 的做法 | — | — | — | 反例（已完成） |
| 4.3 逆的失败 | 迁移引理 | 精确到泄漏的操作 | 迁移引理 | 相对于逆的预言 |
| 第 3 节 | — | — | — | 合流包含程序决定的失败 |

## 6. 给 Cordis 的建议

按上面的设计整理，都需要先在演算里证完再提：

| # | 建议 | 依据 |
|---|---|---|
| 1 | 提供集合静态声明（强制执行 `Plugin.provide` 元数据），在插入时检查冲突；与正在 dispose 的 fiber 冲突时排队，而不是在 `provide` 时抛错 | 4.2；#358 |
| 2 | 失败记下它所在的视图，依赖换了提供者时自动重试 | 4.4 |
| 3 | 区分程序失败与外部失败（错误种类），供编排者决定是否重试；外部结果可按视图缓存 | 4.1 |
| 4 | 每个 disposer 单独隔离，一项失败不连带同组的其余项；记录泄漏 | 4.3；2.4 第 4 条 |
| 5 | 2.4 中的代码问题 | 2.4 |

## 7. 与 difftest 的联系

difftest 量的是 Cordis 与演算的距离，分歧就是第 6 节建议的证据。

- 组件规格新增两条指令：`['ext', ok]`（一次 await，按 `ok` 成功或抛错）和 disposer 抛错的操作。
- 编排脚本新增"dispose 之后不等落定就 insert"一类，覆盖 #358。
- 现状的 Cordis 对照 `astep`，按建议修改过的 Cordis 对照演算本身。

## 8. 文件计划

| 文件 | 内容 |
|---|---|
| `errors/_CoqProject`、`errors/build.sh` | 独立构建 |
| `errors/theories/Superseded.v` | 4.0（已完成） |
| `errors/theories/Admit.v` | 4.2：Cordis 做法的反例（已完成） |
| `errors/theories/Queue.v` | 4.2：排队，与推迟插入的核心执行对应 |
| `errors/theories/Async.v` | 4.1：确定的外部读取（核心的实例）；每次加载的外部结果（归约） |
| `errors/theories/UndoFail.v` | 4.3 |
| `errors/theories/Classify.v` | 第 3 节：失败的分类与包含失败的合流 |

建议顺序：4.2 排队 → 4.1 确定的版本 → 4.3 → 第 3 节（含 4.4 的按视图记录）→ 4.1 每次加载的版本。

## 9. 待定问题

1. 4.1：每次加载各自的外部结果，要不要做？还是只承认确定的外部读取？
2. 4.2：排队的 fiber 在核心状态里怎样表示（`Inactive None` 加一个标记，还是新的生命周期状态）？
3. 4.3：泄漏要不要标在 fiber 上？
4. 第 3 节：同名登记"谁先谁赢"，作为服务义务排除（服务对可能相遇的操作不拒绝），还是保留为合流的前提？
5. 4.4：失败按视图记录，要不要进第 3 节一起做？
