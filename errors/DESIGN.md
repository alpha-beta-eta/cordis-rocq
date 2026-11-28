# 错误处理：设计

本目录把错误处理放进模型，与现有形式化隔离。本文只做设计，不含证明与实现。

## 0. 为什么，以及怎样隔离

### 0.1 现在的模型怎样对待错误

核心演算（`theories/Calculus.v`）里错误只有一种去处：fiber 带着错误标记进入 Unloading，撤销完停在
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
- 合流：所有版本都以终态**没有失败的 fiber** 为前提（`Summary.v` 第 4 条，`NoFailed`）。理由是有的失败
  与调度有关（RULES.md 第 6 节："spawn 时的冲突检查与调度有关，但冲突导致失败，已由'没有失败 fiber'
  排除"）。

模型外的错误：

- **外部失败。** Cordis 的 `apply` 中途 `await` 外部 IO，IO 抛错时 fiber 进入 FAILED。演算没有 `await`，
  这种失败只能写成 `PFail`，"在等外部结果"这个状态也不存在（DESIGN.md D6"异步初始化"）。
- **disposer 失败。** Cordis 记日志后吞掉（DESIGN.md 差异 f）。演算假定逆是全函数，把它定为越过边界。
- **接纳冲突。** Cordis 在 `provide` 时才发现提供集合相交（差异 c），演算在 `O-Insert` 时就拒绝。
  difftest 的 1 452 个分歧都是这一类；[cordiverse/cordis#358](https://github.com/cordiverse/cordis/issues/358)
  是其中后果最重的一种：冲突的旧提供者已经在被 dispose，冲突是暂时的，新 fiber 却永久 FAILED。

### 0.2 目标

1. 让上面三类错误进入模型，各自给出 Cordis 现在的语义和一个改进的语义。
2. 把"失败"按**由什么决定**分类（第 3 节），尽量把合流的前提从"没有失败"缩小成"没有由调度决定的
   失败"。
3. 给 difftest 提供更细的对照对象：Cordis 的错误路径目前在重放时只能对上 `PFail`/`EOp`。

### 0.3 隔离

- 代码放在 `errors/theories/`，逻辑名 `CordisErr`。它可以 `Require` 核心（`Cordis.*`）和需要的
  `Cordis.Ext.*`；核心与 `theories/Ext/` 都不 import 它。检查：

  ```sh
  grep -rn "CordisErr" theories/    # 应为空
  ```

- 有自己的 `errors/_CoqProject` 与 `errors/build.sh`（`-Q ../theories Cordis -Q theories CordisErr`），
  根目录的 `build.sh` 不变，先编译核心再编译本目录。
- 和 `theories/Ext/` 的做法一样，每个模块都给一条**保守性**定理：不用本模块新增的构造时，它的每一步
  就是核心的一步。能归约到核心的模块，安全性等结论直接从核心搬过来。
- 文档也只放在本目录，正文定稿之前不改 `docs/` 下的文件；需要的话在根 README 加一行链接。

## 1. 核心的错误路径（摘要）

- `load_step` 中的失败一律是 `set_life γ n f (Unloading acc w (Some z))`：保留已有的累加器，逐项撤销。
  失败的 fiber 不传播给父 fiber，也不影响子 fiber 以外的任何东西；子 fiber 由撤销 `USpawn` 时退役。
- `L-Step` 在 target 改变之后仍然可以走（`may_step` 只在 `PDone` 处检查 target），所以加载中途
  target 已经转向时，`PFail` 与 `L-Divert` 都可走：前者得到 `Inactive (Some EUser)`，后者得到
  `Inactive None`。哪一个发生由调度决定，这是核心里另一处与调度有关的失败。Cordis 在这里总是取
  后者（第 2.2 节），第 4.0 节把这一点做成规则。
- `O-Reset` 只作用于 `Inactive (Some _)`，把错误清掉；之后由 `L-Begin` 重新加载。

## 2. Cordis 的错误路径

依据：上游 `D:\cordis\packages\core\src`（`7f92195`，2026-11-07）与 dsh vendored 版本
（`D:\deepseek-harness\vendor\cordis\src`，dsh `fcc0ad4`）。只读代码和上游测试得出，没有另写测试复现。
行号指上游，除非注明。两份代码没有 `AbortSignal`，也没有 `internal/error` 事件；错误存在私有字段
`Fiber._error`（`fiber.ts:130`），状态由 `_getState()` 按 `uid === null` → DISPOSED、`_error` → FAILED、
epoch ≠ INACTIVE → ACTIVE、否则 PENDING 的顺序算出（`fiber.ts:365-370`）。

### 2.1 各类错误

| 错误 | Cordis 的处理 | 终态 | 与核心的对应 |
|---|---|---|---|
| `apply` 同步抛错、promise 拒绝（含 await 的外部 IO）、生成器 `next()` 抛错 | `_reload` 捕获（`fiber.ts:462-470`），记日志；epoch 未变时置 `_error`，然后 `_unload` 撤掉已登记的效应 | FAILED | 程序中的失败走 `PFail`；外部 IO 失败核心没有，见 4.1 |
| `provide` 的键已登记 | `reflect.ts:225` 抛错；在 `apply` 中即 `apply` 失败。旧 owner 的 `uid` 置空并**不**删除它的 impl，impl 要等它的撤回 disposer 运行（`reflect.ts:234`），而 `_unload` 先等全部依赖者退出（`fiber.ts:485-487`） | FAILED，旧绑定删掉之后也不重试 | 差异 c，核心在 `O-Insert` 拒绝；见 4.2 |
| 运行期 `provide`、`ctx.effect` 抛错（如在监听器里） | 只抛给调用者 | fiber 状态不变 | 核心中反应是子 fiber，失败只影响子 fiber |
| fiber 级 disposer 抛错 | `_unload` 中每个顶层 disposer 单独 `try/catch` 记日志，`Promise.all` 照常完成（`fiber.ts:492-502`） | 与没出错时相同，不置 `_error` | 差异 f；见 4.3 |
| 同一个 `ctx.effect` 内的子 disposer 抛错 | 子 disposer 按顺序串行；同步抛错会中断循环，而条目已经 `splice(0)` 移走，**同组剩下的 disposer 不再调用**；异步拒绝时后面的 `.then(dispose)` 同样跳过（`fiber.ts:298-311`，vendored `fiber.ts:437-446` 相同） | 泄漏同组较早登记的资源 | 见 4.3 的"中断同组"变体 |
| 依赖缺失 | 不是错误，epoch 为 INACTIVE（`fiber.ts:418-430`） | PENDING | `target = None` |
| 提供者失败 | 依赖者被通知后卸载 | 依赖者 PENDING，不是 FAILED；提供者经 `update()` 恢复后自动重载 | 与核心一致：失败不传播 |
| 子 fiber 失败 | 只记在子 fiber 上；父 fiber 的 `apply` 若 `await ctx.plugin(child)` 则父 fiber 也失败 | | 核心的 `PSpawn` 不等子 fiber，后一种传播不在模型内 |
| 父 fiber 失败、重启、dispose | `_unload` 运行子 fiber 的 dispose 效应 | 子 fiber DISPOSED | 撤销 `USpawn`：`L-RetireChild` |

### 2.2 时机

- **加载中途 target 转向，之后 `apply` 失败**：`fiber.ts:466` 的守卫使错误只记日志，不置 `_error`；
  随后按新的 epoch 卸载，再进入 LOADING（restart、依赖换了提供者）、PENDING（依赖消失）或 DISPOSED。
  **被取代的加载永远不会以 FAILED 结束。**
- **promise 形式的 `apply` 不能中途取消**：`_reload` 等整个 promise 完成，在此之前 `dispose()`、`restart()`
  都挂起，fiber 停在 LOADING。异步生成器在两次 `yield` 之间检查 epoch 并 `iter.return()`（vendored 版本
  不调 `return()`，生成器的 `finally` 不运行）。同步 `apply` 一次跑完。三者都是核心的执行：target 转向后
  `L-Step` 照样可走（落地），最后一步 `PDone` 不可走、失败按上一条处理，都归结为 `L-Divert`。
- **重启过程中 disposer 抛错**：吞掉，照常重新加载。

### 2.3 失败之后

- `_error` 只由 `update()`（`fiber.ts:543`）和 `_replace()`（`fiber.ts:413`）清除，对应 `O-Reset`。
- `restart()` 对 FAILED 无效：`_setEpoch` 见 `_error` 直接返回（`fiber.ts:436`），`await()` 抛出原错误。
- 依赖变化不会让 FAILED 的 fiber 重新加载（上游测试 `fiber.spec.ts:93`）。#358 中暂时冲突导致的失败
  因此是永久的。

### 2.4 顺带发现的 Cordis 问题

只读代码得出，都还没有写测试确认，不属于本模块的建模范围，记下来留作 issue 候选：

1. 上游 `update()`/`_replace()` 作用于依赖缺失的 FAILED fiber 时，新 epoch 与旧 epoch 同为 INACTIVE，
   `_setEpoch` 提前返回，`state` 停在过时的 FAILED，不发 `internal/status`。
2. 上游对 PENDING 或 FAILED 的 fiber `dispose()` 不运行 `_unload`，失败之后登记在它上面的效应泄漏。
   vendored 版本已修（总是 `_unload`）。
3. 构造期 `_refresh` 中 `internal/status` 监听器抛错，fiber 被置 `_error` 但 `apply` 照样运行，最终 FAILED
   且效应从不卸载；`_reload`/`_unload` 中它抛错会使 `inertia` 拒绝，并跳过依赖者通知。
4. 同一个 `ctx.effect` 内一个 disposer 抛错，同组剩下的 disposer 不再调用（2.1 表中）。
5. 撤回 provide 时 `notify` 抛错，impl 已离开 `store` 却留在 `provisions` 中。

## 3. 失败按由什么决定分类

| 类别 | 例子 | 对合流的影响 | 处理方向 |
|---|---|---|---|
| **程序决定** | `PFail`；对只在本 fiber 内可见的状态操作被拒 | 无：同样的输入，每次执行都失败 | 合流可以把这些失败包括进来 |
| **环境决定** | 外部 IO 失败；disposer 失败 | 终态依赖外部结果 | 合流相对于外部结果的**预言**陈述（第 4.1、4.3 节） |
| **调度决定** | #358；`PSpawn` 冲突；同名登记谁先谁赢；加载中途 target 转向时 `PFail` 与 `L-Divert` 的竞争 | 破坏合流 | 最后一种由第 4.0 节消除（Cordis 已经这样做）；接纳冲突改成等待（第 4.2 节）；其余列为义务，或者作为模型对 Cordis 的建议 |

第三类是要害。核心用 `NoFailed` 把三类一起排除，结论因此偏弱：一个插件只要可能因自身逻辑失败
（第一类），合流就不再对它说任何话。目标定理的形状：

> 在没有**调度决定**的失败的执行上，终态（包括哪些 fiber 失败、带什么错误标记）与调度无关。

做法是给每种失败一个"由什么决定"的判据，再证明判据成立时失败的发生与否由理想轨迹决定，进入
`Episode.v` 的路径确定性论证。

## 4. 模块

### 4.0 过时的加载不记失败（`Superseded.v`，已完成）

**规则。** 加载中的 fiber 在 target 已经转向时走到失败（`PFail`、操作被拒、provide 冲突、4.1 的外部失败），
不记错误标记，按 `L-Divert` 进入 `Unloading acc w None`。这就是 Cordis 的行为（2.2 节第一条）。

**要证的。**

1. **它是核心的精化**：新规则的每一步都是核心的一步。target 已转向时核心的 `L-Divert` 本来就可走，
   新规则只是删去了失败那一支。所以核心的全部安全性结论直接适用。
2. **它消除一种调度决定的失败**：一个 fiber 以失败结束某次加载，当且仅当这次加载按理想轨迹走到失败，
   且直到失败那一步 target 都没变。quiet 终态中失败的 fiber，它的最后一次加载的 target 就是终态的 target，
   失败与否由理想轨迹决定。这是第 3 节"合流包含程序决定的失败"的第一块。

这一模块最小，而且只是在核心的执行中挑出一部分，适合作为起点。

**完成情况。** `Superseded.v`，约 270 行，没有新公理：

| 结论 | 名字 |
|---|---|
| 每个 `sstep` 都是核心的一步，标签相同，或以 `LDivert n` 代替 `LStep n` | `sstep_core` |
| 每个 `sstep` 执行都是核心的执行；核心保持的性质 `sstep` 也保持 | `srun_core`、`sinv_step` |
| 安全性 | `swf_reachable` |
| 两者在同样的标签上可走，静止相同；进展 | `sstep_some`、`squiet_iff`、`sprogress_reachable` |
| 终止 | `stermination`、`stermination_reachable` |
| 加载以失败结束，只发生在 target 仍是这次加载承诺的视图时 | `sfail_current` |

上面第 2 条的"当且仅当"只证了一个方向（失败蕴涵 target 未变）；"按理想轨迹走到失败"那一半留给第 3 节，
与 `Episode.v` 的理想轨迹一起做。

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

外部读取不碰 S，不进累加器。结果由环境给出：成功给出 `r : R`，失败让 fiber 带新的错误标记 `EExt`
进入 Unloading。D6 的 `prepare`/`commit` 就是"`EExt` 之后跟一个 `EOp`，外部数据作为操作参数"，
服务操作仍然是原子步。

**归约到核心。** 一次加载中第 i 个外部读取的结果记作 `ρ i : option R`（`None` 为失败），`ρ` 称为
这次加载的**预言**。给定 `ρ`，`EProg` 展开成核心的 `Prog`：`EExt e κ` 换成 `κ r`（`ρ i = Some r`）
或 `PFail`（`ρ i = None`）。和 `Ext/Optional.v` 的 `(c, S)` 一样，fiber 的组件取成 `(c, ρ)`，`ρ` 在
fiber 处于 Inactive 时重新选定（每次加载可以得到不同的外部结果）。于是：

- 扩展的每一步是核心的一步，或者是"Inactive 时重选 `ρ`"；后者保持核心不变式 `WF`。
- 保持性、顺序、恢复精确性、终止、进展直接从核心得到。
- 合流：固定每次加载的预言，终态与调度无关。这把 D6 中"异步初始化下合流不再成立，除非外部读取
  是确定的"变成一条精确的定理。

**丢失的信息。** 归约里外部读取不占步骤，"在等外部结果"这个状态看不见。对安全性无所谓；对 difftest
的事件映射，它意味着 Cordis 在 await 期间不产生事件，是对的。要谈外部 IO 的公平性（进展需要在途读取
最终返回）时，才需要一个显式的等待状态，那时再给不归约的版本。

**错误标记。** 归约把外部失败映射到 `PFail`，核心只能给出 `EUser`。扩展的错误标记通过组件 `(c, ρ)`
恢复：`ρ` 中有失败的那次加载，`EUser` 读作 `EExt`。

**target 转向之后的外部失败。** Cordis 当作 divert，不置 FAILED（2.2 节）。归约下两者都可走，
与核心 `PFail` 对 `L-Divert` 的竞争相同；和 4.0 组合时只剩 divert。

**promise 形式的 `apply`。** Cordis 不能中途放弃它，要等整个 promise 完成（2.2 节）。归约里 `L-Divert`
随时可走，比 Cordis 宽；Cordis 的行为是"全部落地之后再转向"，仍是归约后的一个执行，所以不影响定理，
只影响 difftest 的事件映射。

### 4.2 动态提供集合与接纳（`Admit.v`）

**构造。** 组件的提供集合不再在 `O-Insert` 时检查。`provs` 仍然作为上界保留（`PProvide` 的键要在其中，
用于秩与无环的静态判断），但 `O-Insert` 去掉 `conflict` 前提，冲突改在 `PProvide` 时处理。
两个变体：

- **`fail`（Cordis 现状）**：键已被绑定就以 `EConflict` 失败。
- **`wait`（改进）**：键的现有绑定属于一个**已退役**的 fiber（`disposed = true`）时，`PProvide` 不可走，
  等绑定删除后再走；属于未退役的 fiber 时，仍以 `EConflict` 失败。

只在 owner 已退役时等待，是因为退役的 fiber 一定会被移除（终止），且不会再 provide。owner 只是处在
Unloading（restart、依赖变化导致的 divert）时，它卸载完会重新加载并再次 provide 同一个键；这时等待
会让两者争抢，谁先 provide 谁赢，与调度有关。#358 中建议的"owner 在 unloading 就等待"因此太宽。

**要证的。**

1. **`fail` 的反例（已完成，`Admit.v`）**：把 #358 的序列（插入 P、插入依赖者 D、dispose P 之后不等落定
   再插入 P）写成计算出来的两次执行，沿用 `Examples/Basic.v` 的登记表例子。编排输入相同，只有生命周期步
   的先后不同：新 P 先加载时停在 `Inactive (Some EConflict)`，D 停在 Inactive，`tools` 未绑定，且两者都
   不能再开始（`early_obs`、`early_stuck`）；旧 P 先被移除时全部 Active（`late_obs`）。同一时刻核心拒绝
   这次插入（`core_refuses`）。`astep` 只是去掉 `O-Insert` 的冲突检查，冲突由核心原有的 `PProvide`
   检查报出；核心允许的插入 `astep` 也允许（`astep_conservative`）。另外，新 P 的依赖为空、target 从未
   改变，所以 4.0 的规则救不了它：这是接纳本身的问题，不是时机的问题。
2. **`wait` 无死锁**：等待关系加进进展的论证。新 P 等旧 P 被移除，旧 P 等依赖者退出（`held`），
   依赖者等的是旧 P 的提供（不可见，不会开始加载）。需要说明等待关系沿秩无环；新 P 自己依赖旧 P
   提供的键时，它在 `L-Begin` 就停住，不会等在 `PProvide`。
3. **`wait` 的合流**：在"任意时刻没有两个未退役的 fiber 声明同一个键"的编排输入下，终态与调度无关，
   并且等于核心中"推迟到旧 fiber 移除之后再 `O-Insert`"的那次执行。

**一个设计上的选择：在哪里等。** 在 `PProvide` 处等，fiber 可能已经做了 provide 之前的操作，
带着部分效应等待；在 `L-Begin` 处等（按 `provs` 上界判断），等待期间没有效应，但要求提供集合静态已知，
Cordis 做不到（`Plugin.provide` 元数据不强制）。暂定在 `PProvide` 处等，第 3 条的对应关系需要把
"provide 之前的前缀"挪到旧 fiber 移除之后，这是证明的主要工作。

### 4.3 撤销失败（`UndoFail.v`）

**构造。** `L-Undo` 撤一项 `UOp` 时，环境可以让它失败。按 Cordis 的做法吞掉：这一项照样出栈，但逆 g
不施加，绑定状态不变；失败的令牌记进一个鬼记录 `leaked`，规则不读它。`UProv`、`USpawn` 的撤销不会失败
（它们是运行时自己的动作）。

**要证的。**

1. **生命周期对撤销失败是鲁棒的**：保持性、顺序、终止、进展照样成立。这正是 Cordis 选择吞掉错误的理由，
   现在可以作为定理陈述。
2. **恢复精确性的精确版本**：一个效应来了又走之后，每个绑定的状态 ≃ 省去该效应中**撤销成功**的那些操作
   之后的执行所达到的状态。也就是说，与理想状态的差恰好是 `leaked` 中那些操作。没有撤销失败时退回
   `Recovery.recovery_exact`。
3. **合流**：相对于撤销结果的预言。

**两个变体。** Cordis 对顶层 disposer 是"吞掉继续"，对同一个 `ctx.effect` 内的子 disposer 却是"中断同组"：
一个抛错，同组剩下的都不再调用（2.1 节）。核心的累加器是平的，要表达后者需要给撤销项加上分组。
模型取"吞掉继续"，"中断同组"只作为反例：写出一次执行，说明它让恢复精确性的差额超出失败的那一项，
作为给 Cordis 的建议的依据。

**归约？** 撤销失败不能直接归约到核心，核心的 `LUndo` 一定施加 g。可以把每个操作的逆换成"按预言决定
施加 g 还是恒等"，但恒等不满足 `WellBehaved` 中逆的要求，所以这一模块需要自己的证明，复用
`ServiceSeq.v` 的重放引理。

### 4.4 失败之后（讨论，暂不形式化）

- **传播。** 核心中失败不传给父 fiber，父 fiber 失败时子 fiber 随撤销退役，提供者失败时依赖者回到
  Inactive 而不是失败，都与 Cordis 一致（2.1 节）。唯一的出入是父 fiber 的 `apply` 显式
  `await ctx.plugin(child)` 时子 fiber 的失败会传上来，核心的 `PSpawn` 不等子 fiber，这一条不建模。
- **重试。** 核心只有 `O-Reset`，与 Cordis 的 `update()`/`replace()` 一致（差异 i，Cordis #95 不自动重试；
  `restart()` 对 FAILED 无效，2.3 节）。
  一个候选是"target 改变时自动清除失败"：失败的 fiber 在它的依赖重新解析到不同的提供者时回到
  `Inactive None`。它能让 #358 那类暂时失败自行恢复，但失败的 fiber 是否重试就取决于依赖变化的时机，
  需要和第 3 节的分类一起看。
- **反应中的失败。** `O-React` 起的子 fiber 失败只影响它自己，核心已覆盖（`Runtime.v`）。

## 5. 定理目标汇总

| 模块 | 保持性、顺序 | 恢复 | 终止、进展 | 合流 |
|---|---|---|---|---|
| 4.0 过时的加载不记失败 | 核心的子集（已证） | 核心的子集 | 核心的子集（已证；两者在同样的标签上可走） | 第 3 节的第一块 |
| 4.1 外部读取 | 归约 | 归约 | 归约（不含外部 IO 的公平性） | 相对于加载的预言 |
| 4.2 `fail` | 核心论证改写 | 同核心 | 同核心 | 反例 |
| 4.2 `wait` | 核心论证改写 | 同核心 | 新的等待关系 | 在不冲突的编排输入下成立，并与推迟插入的核心执行对应 |
| 4.3 撤销失败 | 需要证明，预计平凡 | 精确到泄漏的操作 | 鲁棒 | 相对于撤销的预言 |
| 第 3 节 | — | — | — | 合流包含程序决定的失败 |

## 6. 与 difftest 的联系

- 组件规格新增两条指令：`['ext', ok]`（一次 await，按 `ok` 成功或抛错）和 disposer 抛错的操作。
- 编排脚本新增"dispose 之后不等落定就 insert"一类，覆盖 #358。
- 重放驱动加上新标签：外部失败映射到 `LStep`（展开后的 `PFail`），disposer 失败映射到带失败的 `LUndo`。
- 第 4.2 节的两个变体正好对应两个目标：Cordis 现状应当与 `fail` 一致，打了补丁的 Cordis 应当与 `wait` 一致。

## 7. 文件计划

| 文件 | 内容 |
|---|---|
| `errors/_CoqProject`、`errors/build.sh` | 独立构建 |
| `errors/theories/Superseded.v` | 4.0：过时的加载不记失败，核心的精化（已完成） |
| `errors/theories/Async.v` | 4.1：`EProg`、预言、展开、归约与保守性 |
| `errors/theories/AsyncConf.v` | 4.1：相对于预言的合流 |
| `errors/theories/Admit.v` | 4.2：`fail` 变体的 step、#358 的计算执行（已完成）；`wait` 变体待做 |
| `errors/theories/AdmitLive.v` | 4.2：`wait` 的无死锁与合流 |
| `errors/theories/UndoFail.v` | 4.3 |
| `errors/theories/Classify.v` | 第 3 节：失败的分类与包含失败的合流 |

建议顺序：4.0（最小，核心的子集）→ 4.2 的反例（直接对上 #358）→ 4.1（归约，便宜）→ 4.3 → 4.2 `wait`
→ 第 3 节。

## 8. 待定问题

1. 4.0 与 4.1 组合后，外部失败在 target 转向时一律 divert；不组合时是否还保留两支？（倾向于默认组合。）
2. 4.2 中，在 `PProvide` 处等还是在 `L-Begin` 处等？
3. 4.3 中，`UProv` 的撤销（从 `reflect.store` 删除）在 Cordis 里会不会失败？
4. 第 3 节的判据：同名登记"谁先谁赢"算调度决定，要不要作为服务义务（服务对可能相遇的操作不拒绝）排除，
   还是保留为合流的前提？
5. 4.4 的自动重试要不要做？
