# 错误处理：设计

本目录把错误处理放进演算，与现有形式化隔离。

**定位。** 目标是一个自足的演算：每条规则按它自己的道理取舍，即让定理成立、让一个好的运行时有据可依，
而不是贴近 Cordis 现在的实现。Cordis 的现状（第 2 节）是动机和证据：它在哪里出错、哪里已经做对了。
演算与 Cordis 不同的地方，整理成给 Cordis 的改进或新功能建议（第 7 节）。Cordis 的行为只在两种情况下
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

各条定理对错误的态度：保持性、顺序、恢复精确性、终止、进展对含失败的执行照样成立；合流的所有版本都以终态
**没有失败的 fiber** 为前提（`Summary.v` 第 4 条，`NoFailed`），因为有的失败与调度有关。

演算没有的：外部读取及其失败；外部资源及其释放失败；"稍后可以"的接纳（与已退役、尚未移除的 fiber
冲突时，核心直接拒绝 `O-Insert`）。

### 0.2 原则

| # | 原则 | 含义 |
|---|---|---|
| P1 | **失败由程序与输入决定，不由调度决定** | 同样的程序、同样的编排输入与外部结果，哪些 fiber 失败、带什么标记，与调度无关。合流因此可以把失败包括进来 |
| P2 | **暂时的障碍是等待，不是失败** | 一定会消失的障碍让 fiber 等；只有不会自行消失的条件才是失败 |
| P3 | **失败是局部的，运行时与受管状态上的撤销不失败** | 失败不传播给父 fiber 和依赖者；撤销一定走完；受管状态 S 上的逆是全函数（服务义务，贡献模型按构造满足）。能失败的只有程序、服务操作、外部读取、外部资源的释放 |
| P4 | **失败可归因** | 错误标记说明原因；没能释放的外部资源有记录 |
| P5 | **保守** | 不出错时就是核心 |

### 0.3 隔离

- 代码放在 `errors/theories/`，逻辑名 `CordisErr`。它可以 `Require` 核心（`Cordis.*`）和需要的
  `Cordis.Ext.*`；核心与 `theories/Ext/` 都不 import 它（`grep -rn "CordisErr" theories/` 应为空）。
- 有自己的 `errors/_CoqProject` 与 `errors/build.sh`，根目录的构建不变，先编译核心再编译本目录。
- 每个部分给一条保守性定理（P5）。能归约到核心的，安全性等结论直接从核心搬过来。
- 文档只放在本目录，定稿之前不改 `docs/` 下的文件。

## 1. 核心判断：失败只对它所在的视图有效

第 3 节的目标是合流包含失败。推演下来，这离不开一条新规则。反例：

- 调度 A：F 在视图 w₁ 下加载，按程序逻辑失败；之后它的一个依赖被重新 provide，target 变成 w₂。F 仍停在失败。
- 调度 B：F 等到 w₂ 出现才开始加载，成功。

编排输入相同，终态不同。失败本身由程序决定，但**失败一直留着**，取决于调度。所以：

**规则（失败按视图记录）。** 失败标记带上它所在的视图 w；target 不再是 w 时，标记自动清除，fiber 回到
`Inactive None`。视图记的是 provision id（DESIGN.md 差异 b），依赖被重新 provide 就是新的 pid，所以
"target ≠ w"等价于"某个依赖换了一次提供"。同一视图下的重试仍然只能靠 `O-Reset`，那是编排输入。

**推论。** 4.0（过时的加载不记失败）由它推出：过时的加载即使记下失败，target ≠ w，标记立即清除。
4.0 已证完、代价很小，保留作"错误标记一次也不出现"的更强版本。

**已完成的部分（`ViewFail.v`，约 450 行，没有新公理）。** 状态多一张表 `fview`，`L-Unloaded` 时记下 fiber
卸载自的视图；新的生命周期规则 `VClear n` 在失败的 fiber 的 target 不再是那个视图时清除失败，它就是核心的
`O-Reset n`，只是由运行时而不是编排者发起。

| 结论 | 名字 |
|---|---|
| 每一步都是核心的一步（`VClear` 即 `O-Reset`）；安全性 | `vstep_core`、`vrun_core`、`vwf_reachable` |
| 失败的 fiber 只由 `L-Unloaded` 产生（核心的每条规则逐条检查） | `failed_after` |
| 每个失败的 fiber 都记有视图 | `vinv_step`、`vinv_reachable` |
| quiet 的可达状态是稳定的，且每个失败的 fiber 都是在当前 target 下失败的 | `vquiet_current` |
| 计算的例子：同样的编排输入，核心里一种调度让使用者永久失败、另一种全部 Active；加上 `VClear`，前一种继续走到与后一种相同的终态 | `core_diverges`、`core_stuck`、`view_agrees` |

**另外两块。**

1. **终止（已完成，`VTermination.v`，约 550 行，没有新公理）。** 不能从核心搬：`VClear` 之后 fiber 会重新
   加载，增加工作量，而核心的度量 `Termination.mu` 把失败的 fiber 记为几乎为零。新度量 `vmu` 只在三处与
   `mu` 不同：视图过时的失败 fiber 记为"比有同样 target 的 `Inactive None` 多一步"；视图过时、带错误的
   Unloading fiber 记为撤销项加收尾再加同样的量；target 已转向的 Loading fiber 比核心多 1（它现在可能以
   过时的失败结束，比 divert 多走一步）。证明沿用 `Termination.v` 的结构：走一步的 fiber 的度量下降
   （`vmu_drop`）；秩不高于它的其他 fiber 不变（`vmu_other`）；于是按秩的字典序下降（`vphi_drop`）；
   `VClear` 只降低本 fiber 的度量，其余全不变（`vclear_drop`、`vclear_other`）。结论：生命周期步（核心的
   加上 `VClear`）不会无限进行（`vtermination`、`vtermination_reachable`）。核心关于 target、撤销权重、
   秩的引理（`lstep_effects`、`target_stable`、`mu_other`、`Wt_*`、`own_item_ne`）原样复用。成立的原因
   与核心相同：失败的视图过时，只能是更低秩的提供者换了一次提供，而那一步已经让更低秩的度量下降。
2. **合流包含失败（`Classify.v`）。** 这是主体中最大的一块，拆成两层，先做不含 spawn 的版本。

   **第 1 层（已完成）：失败集合相同时，控制状态合流。** `vcontrol_confluence`：从同一个状态出发、只走生命周期
   步（含 `VClear`）、终于 quiet 的两次执行，若失败的 fiber 相同，则 fiber 集合、组件、Active 集合、每个键的
   提供者都相同。证明就是核心 `Confluence.control_confluence` 的证明，只改两处：Active 当且仅当没有失败、且
   声明的每个键都由 Active 的 fiber 提供（`vactive_iff`）；带一个固定"守卫"集合的不动点仍然只有一个解
   （`fix_unique_guard`）。稳定状态的形状多一种"失败"（`vsettled_shape`）。核心的 `Total`（走到 `Done` 的
   路径都提供声明的键）本来就允许程序在某些路径上失败，不用改。

   **第 2 层（已完成）：两次执行的失败集合相同。** `IdealFail.v`（约 120 行）与 `FailCrux.v`（约 900 行），
   没有新公理。主定理 `vconfluence_failures`：从可达状态出发、只走生命周期步（含 `VClear`）、终于 quiet 的
   两次执行，失败的 fiber 相同，fiber 集合、组件、Active 集合、每个键的提供者也相同。

   | 步骤 | 内容 | 名字 |
   |---|---|---|
   | 理想失败 | 程序 c 在 ρ 下理想失败：某条理想轨迹停在失败点（`PFail`；操作的键解析不到；操作在理想状态上被拒）。与理想走到 `Done` 互斥，且只取决于 ρ 在依赖上的取值 | `IdealFails`、`ideal_excl`、`ideal_fails_ext` |
   | 实际被拒即理想被拒 | 照核心 `Episode.ep_op` 的证明：实际状态是初始状态、本 fiber 的操作、再加别的 fiber 可能相遇的操作；新义务 `HNoRej` 保证理想上成功的操作在相遇的操作之后仍成功 | `outcome_before`、`op_fail_ideal` |
   | 每种失败都是理想失败 | 加上两条静态义务：不 spawn；程序只 provide 声明过的键、每条路径上每个键至多一次（`HProv`） | `load_fail_ideal` |
   | 不变式 `FailInv` | 带错误卸载中的 fiber、以及失败的 fiber 在它记录的视图下，都理想失败；每一步保持 | `finv_step`、`finv_reachable` |
   | quiet 状态的刻画 | 失败的 fiber 在当前 target 下理想失败；Active 的 fiber 在当前 target 下理想走到 `Done` | `quiet_failed_ideal`、`quiet_active_done` |
   | 跨两次执行 | 沿秩归纳：依赖由同样的 Active fiber 以同样的理想轨迹提供，于是看到同样的初始状态，理想失败与否相同 | `failed_same` |
   | 合流 | 由第 1 层 | `vconfluence_failures` |

   **新增的义务。** 与核心的合流相比，前提多三条：
   - `HNoRej`（服务）：对可能相遇的 a、b，a 在 x 上成功，b 在 x 上成功，则 b 在 a 之后仍成功。核心的交换性
     `Commute` 允许对称的拒绝（同名登记），那时失败由调度决定。贡献模型（OPLIB、E6）按构造满足它。
   - `NoSpawn`（组件）：与第 1 层相同。
   - `HProv`（组件）：程序只 provide 声明过的键，每条路径上每个键至多一次。
   不再需要的是核心合流的前提"终态没有失败的 fiber"。

   **服务状态（已完成，`StateConfF.v`）。** 核心 `StateConf.v` 对"没有失败的 fiber"的依赖只在一条引理里：终态
   的 fiber 要么是未失败的 Inactive，要么是带完整理想轨迹的 Active（`final_fiber`）。失败的 fiber 也是 Inactive，
   累加器为空，所以其余证明不受影响。`StateConfF.v` 复制 `StateConf.v` 到 `final_evs` 为止，`Final` 不再要求
   `NoFailed`，`final_fiber` 允许任意错误标记；`state_confluence` 改写为以控制层的一致为前提的 `state_agree`。
   `vstate_confluence` 与 `vconfluence_failures` 合起来：两次执行终态中每个绑定的服务状态 ≃。

   **含 spawn（已完成，`SpawnConfF.v`，义务 A）。** spawn 冲突导致的失败由调度决定（两个父 fiber 是否同时
   在场），所以需要一条关于 spawn 的义务。先取最简单的义务 A：spawn 出的组件不提供任何键，于是 `PSpawn`
   永远不会冲突，spawn 不再是失败的来源。为此 `FailCrux.v` 的义务从"不 spawn"放宽为 A（`HSpawnNP`），
   跨两次执行的不含 spawn 部分移到 `FailConf.v`。`SpawnConfF.v` 复制核心 `SpawnConf.v`：

   - `Final` 取自 `StateConfF.v`（不要求 `NoFailed`）；
   - 沿规范名的对应（`Corresp`）多一项"失败与否相同"；归纳步 `corr_pair` 按 `failed_same` 的办法把 fiber 分成
     无 target、Active（理想轨迹走到 `Done`）、失败（理想轨迹失败）三类，两次执行中它看到同样的初始状态，
     所以类别相同；
   - `final_agree`：根对应的两个终态在重命名意义下一致，失败的 fiber 也对应（`AgreeL` 多一项）；
   - `vspawn_confluence`：从可达状态出发、只走生命周期步（含 `VClear`）、终于 quiet 的两次执行在重命名意义下
     一致。`VClear` 即 `O-Reset`，补证了它保持 `SLInv` 与根 fiber（`sl_oreset`、`rk_oreset`）。

   **还没做的。** 把义务 A 放宽到精确的义务 B（提供键的子组件有唯一的 spawn 位置等）；与编排交错的版本
   （核心 `Dynamic.v`）。

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
| fiber 级 disposer 抛错 | `_unload` 中每个顶层 disposer 单独 `try/catch` 记日志，`Promise.all` 照常完成（`fiber.ts:492-502`） | 与没出错时相同，不置 `_error` | 符合 P3；服务登记与资源释放不分，泄漏没有记录（P4） |
| 同一个 `ctx.effect` 内的子 disposer 抛错 | 子 disposer 按顺序串行；同步抛错会中断循环，而条目已经 `splice(0)` 移走，**同组剩下的 disposer 不再调用**；异步拒绝时后面的 `.then(dispose)` 同样跳过（`fiber.ts:298-311`，vendored `fiber.ts:437-446` 相同） | 泄漏同组较早登记的资源 | 违反 P3：一项失败连带别的项 |
| 依赖缺失 | 不是错误，epoch 为 INACTIVE（`fiber.ts:418-430`） | PENDING | 符合 P2 |
| 提供者失败 | 依赖者被通知后卸载 | 依赖者 PENDING，不是 FAILED；提供者经 `update()` 恢复后自动重载 | 符合 P3 |
| 子 fiber 失败 | 只记在子 fiber 上；父 fiber 的 `apply` 若 `await ctx.plugin(child)` 则父 fiber 也失败 | | 显式等待时传播，其余符合 P3 |
| 父 fiber 失败、重启、dispose | `_unload` 运行子 fiber 的 dispose 效应 | 子 fiber DISPOSED | 与核心的 `L-RetireChild` 一致 |

### 2.2 时机与失败之后

- **加载中途 target 转向，之后 `apply` 失败**：`fiber.ts:466` 的守卫使错误只记日志，不置 `_error`。
  被取代的加载永远不会以 FAILED 结束（"cannot fail the new target"），这一点 Cordis 做对了。
- **promise 形式的 `apply` 不能中途取消**：`_reload` 等整个 promise 完成，在此之前 `dispose()`、`restart()`
  都挂起。异步生成器在两次 `yield` 之间检查 epoch 并 `iter.return()`（vendored 版本不调 `return()`）。
- `_error` 只由 `update()`（`fiber.ts:543`）和 `_replace()`（`fiber.ts:413`）清除，对应 `O-Reset`；
  `restart()` 对 FAILED 无效（`fiber.ts:436`）；依赖变化不会让 FAILED 的 fiber 重新加载（`fiber.spec.ts:93`），
  这正是第 1 节反例的情形。

### 2.3 顺带发现的 Cordis 问题

只读代码得出，都还没有写测试确认，留作 issue 候选：

1. 上游 `update()`/`_replace()` 作用于依赖缺失的 FAILED fiber 时，新 epoch 与旧 epoch 同为 INACTIVE，
   `_setEpoch` 提前返回，`state` 停在过时的 FAILED，不发 `internal/status`。
2. 上游对 PENDING 或 FAILED 的 fiber `dispose()` 不运行 `_unload`，失败之后登记在它上面的效应泄漏。
   vendored 版本已修（总是 `_unload`）。
3. 构造期 `_refresh` 中 `internal/status` 监听器抛错，fiber 被置 `_error` 但 `apply` 照样运行，最终 FAILED
   且效应从不卸载；`_reload`/`_unload` 中它抛错会使 `inertia` 拒绝，并跳过依赖者通知。
4. 同一个 `ctx.effect` 内一个 disposer 抛错，同组剩下的 disposer 不再调用（2.1 表中）。
5. 撤回 provide 时 `notify` 抛错，impl 已离开 `store` 却留在 `provisions` 中。

## 3. 合流包含失败（P1）

**失败的分类。**

| 类别 | 例子 | 处理 |
|---|---|---|
| 程序决定 | `PFail`；对本 fiber 独占的状态操作被拒 | 进入合流 |
| 输入决定 | 外部读取失败（第 5.2 节）；外部资源释放失败（第 5.3 节） | 外部结果是输入的函数，进入合流 |
| 调度决定 | 失败留在过时的视图上；加载中途 target 转向时 `PFail` 与 `L-Divert` 的竞争；同名登记谁先谁赢；`PSpawn` 冲突 | 前两种由第 1 节的规则消除；后两种由静态义务消除（下文） |

**两条静态义务。**

- **相遇的操作不拒绝**：两个 fiber 可能在同一个键上执行的操作（`CoPair`）不返回 `None`。贡献模型满足它
  （放入与撤回贡献不会失败）。有拒绝的服务（如登记表）留在核心里，但不进入本节的定理。
- **spawn 的提供集合静态不交**：父 fiber 重启时撤销 `USpawn` 要等旧的子 fiber 被移除，所以不存在"新子 fiber
  与正在退役的旧子 fiber 冲突"这种暂时冲突；剩下的只有两个不同的活 fiber spawn 出提供集合相交的子组件，
  在组件表上静态检查，与"有秩"同为链接期义务。

**目标定理。** 在核心的服务假设与组件义务、加上这两条义务之下，相同编排输入（含 `O-Reset`）的两次执行，
quiet 终态在重命名意义下一致，**包括哪些 fiber 失败、带什么标记、在什么视图下失败**。

**做法。** 沿用 `Episode.v` 的理想轨迹：一次加载是否失败、带什么标记，由程序、视图（以及第 5.2 节的
外部结果）决定。第 1 节的规则保证 quiet 终态中失败的 fiber 都是在终态的 target 下失败的；于是
`Confluence.active_iff` 的不动点方程改为"Active 当且仅当依赖都被 Active 的 fiber 提供，且在这个视图下
的理想轨迹不失败"，失败的 fiber 满足对偶的方程，解仍唯一（沿秩归纳）。

## 4. 已完成的部分

### 4.0 过时的加载不记失败（`Superseded.v`）

规则：加载中的 fiber 在 target 已经转向时走到失败，不记错误标记，按 `L-Divert` 进入 `Unloading acc w None`。
理由见第 1 节；它是那条规则的更强版本。约 270 行，没有新公理：

| 结论 | 名字 |
|---|---|
| 每个 `sstep` 都是核心的一步，标签相同，或以 `LDivert n` 代替 `LStep n` | `sstep_core` |
| 每个 `sstep` 执行都是核心的执行；核心保持的性质 `sstep` 也保持 | `srun_core`、`sinv_step` |
| 安全性 | `swf_reachable` |
| 两者在同样的标签上可走，静止相同；进展 | `sstep_some`、`squiet_iff`、`sprogress_reachable` |
| 终止 | `stermination`、`stermination_reachable` |
| 加载以失败结束，只发生在 target 仍是这次加载承诺的视图时 | `sfail_current` |

### 4.1 Cordis 接纳做法的反例（`Admit.v`）

`astep` 是 Cordis 的做法：`O-Insert` 不检查冲突，冲突由 `PProvide` 发现，失败且永久。它不是设计，只用来说明
问题。把 #358 的序列（插入 P、插入依赖者 D、dispose P 后不等落定再插入 P）写成计算出来的两次执行，
沿用 `Examples/Basic.v` 的登记表例子。编排输入相同，只有生命周期步的先后不同：新 P 先加载时停在
`Inactive (Some EConflict)`，D 停在 Inactive，`tools` 未绑定，两者都不能再开始（`early_obs`、`early_stuck`）；
旧 P 先被移除时全部 Active（`late_obs`）。同一时刻核心拒绝这次插入（`core_refuses`）。新 P 的依赖为空、
target 从未改变，所以第 1 节的规则救不了它：这是接纳的问题，不是时机的问题。

## 5. 待做的部分

### 5.1 接纳队列（`Queue.v`，P2，已完成）

**问题。** 核心中组件静态声明提供集合，`O-Insert` 拒绝与在场 fiber 相交的组件。这个设计是对的：单一提供者
由构造保证，依赖是否无环可以静态判定。但"在场"包括已退役、尚未移除的 fiber，于是"dispose 旧提供者后立即
插入新提供者"被拒绝，编排者得不到"稍后可以"的信号。

**设计。** 排队的组件还不是 fiber：

- 状态多一个队列，元素是 (票据, 组件)。
- `Q-Insert c`：c 与某个**未退役**的 fiber 冲突，或与队列中的某个组件冲突，就拒绝；否则 c 进入队尾，得到票据。
  队列中的组件算作占用者，所以队列中的组件两两不交，也不与未退役的 fiber 相交。
- `L-Admit`（生命周期规则）：队首的组件与在场 fiber 都不冲突时，把它插入 fiber 表，这时才分配名字，
  与核心的 `O-Insert` 完全相同。
- `Q-Cancel t`：编排者凭票据撤回排队中的组件。

**理由。** 与已退役 fiber 的冲突一定会消失（退役的 fiber 终将被移除），所以是等待（P2）；与未退役 fiber
的冲突不会自行消失，且排队会让两者争抢，所以拒绝（P1）。排队发生在 fiber 存在之前，没有任何效应，这是静态
提供集合带来的好处；若提供集合只在运行时知道（如 Cordis），冲突只能在 `provide` 时发现，那时已经带着部分
效应。先进先出让插入顺序、从而名字的分配，由输入决定。

**要证的。**

1. 与核心的对应：每个 `qstep` 或者不改核心状态（`Q-Insert`、`Q-Cancel`），或者是核心的一步（`L-Admit` 是
   核心的 `O-Insert`，其余标签原样）。所以每次执行对应一次核心执行，名字一致，不需要重命名；安全性由此得到。
2. 终止：生命周期步（核心的加上 `L-Admit`）不会无限进行（队列长度与核心度量的字典序）。
3. 进展：quiet 状态中队列为空。理由：quiet 时核心状态稳定，稳定状态中没有退役的 fiber；队首只可能被未退役的
   fiber 挡住，而不变式排除了这一点。保持这个不变式需要知道新出现的未退役 fiber 只来自 `L-Admit` 和 spawn，
   且 spawn 出的子组件不与队列中的组件相交（第 3 节的第二条义务）。
4. #358 的序列在队列下只有一种结局：全部 Active。

**完成情况。** `Queue.v`，约 500 行，没有新公理：

| 结论 | 名字 |
|---|---|
| 每一步或者不改核心状态，或者是核心的一步（`L-Admit` 即 `O-Insert`） | `qstep_core` |
| 每次执行对应一次核心执行，名字一致；安全性 | `qrun_core`、`qwf_reachable` |
| 终止（队列长度与核心度量的字典序） | `qtermination`、`qtermination_reachable` |
| 不变式：队列两两不交，且不与未退役的 fiber 相交 | `qinv_step`、`qinv_reachable` |
| quiet 的可达状态队列为空 | `qquiet_empty` |
| #358：新提供者排队，旧 fiber 移除后接纳，全部 Active | `q358_queued`、`q358_blocked`、`q358_obs` |

不变式与 `qquiet_empty` 用的假设是 `HSpawnRoot`：spawn 出的组件不提供任何"可由编排者插入的组件"提供的键。
可插入的组件由 `rootb` 给出，`Q-Insert` 拒绝不可插入的组件，不变式多一条"队列中只有可插入的组件"
（`QRoot`）。这正是第 3 节对 spawn 的静态义务：子组件的提供集合与根组件静态不交；一个组件若既会被 spawn
又可插入，它就不能提供任何键。早先的版本用的是更强的 `HKids`（spawn 出的组件不提供任何键），它是
`rootb` 取任意值时的特例。
保持不变式时，生命周期步直接复用核心的 `Termination.lstep_effects`（一步只改本 fiber、只新增 spawn 出的
子 fiber），只有四条编排规则要单独处理。

### 5.2 确定的外部读取（`Async.v`，已完成）

程序多一个外部读取 `EExt e κ`：发出请求 e，按回答继续，外部拒绝时失败。它不碰 S，不进累加器。需要外部
数据的服务操作写成"`EExt` 之后跟一个 `EOp`，外部数据作为操作参数"（D6 的 `prepare`/`commit`）。

**实际采用的形式（与原先的设想不同）。** 外部世界是 `world : 组件 → 请求 → option 回答`，一次运行中同一个
请求得到同一个回答。原先设想的"组件 × 视图 × 重置代数"做了两处调整：

- **不单列视图。** 程序对视图的依赖要经过服务操作的结果才能进入程序，而请求 e 本身可以由这些结果构造
  （先读配置，再按配置里的路径请求文件），所以"同样的依赖，同样的结果"已经由"同样的请求，同样的回答"
  覆盖。去掉视图之后，展开不必在每次加载时重选，组件表就是一张普通的核心组件表。
- **重置代数改为替换组件。** 重新读取外部世界由编排者完成：dispose 旧组件，插入带新世界的组件，与核心对
  配置变更的建模相同（DESIGN.md 差异 l）。这样 `O-Reset` 保持核心的含义。

于是扩展不是新的演算：把每个读取按世界展开（`unfold`）就得到核心程序，`prog'` 是普通的核心组件表，**核心
与本目录其他文件的每一条定理都对它原样成立**。唯一的工作是把组件义务写在扩展程序上，使之对任何世界成立：
有界（读取不计步，`ebounded_unfold`）、走到 `Done` 的路径提供声明的键（`eadp_unfold`）、spawn 与秩按扩展
程序判断（`spawn_unfold`、`above_eabove`）。`atermination` 与 `acontrol_confluence` 示范两条核心定理这样使用。
合流说的是相同输入的执行，世界是输入之一：同一个世界下的两次运行结论一致。

**外部失败的归因（`AsyncKind.v`，已完成）。** 展开之后，外部拒绝与程序自己的 `EFail` 在核心状态里都是
`EUser`。区分放在扩展程序的理想轨迹上做：`ETr` 是扩展程序的理想轨迹，成功的读取是一步（`XRead`），不产生
别的事件；轨迹是确定的（`etr_det`），所以一条理想轨迹至多有一个失败点（`efail_unique`）；抹去读取之后，
扩展轨迹就是展开后组件表的核心理想轨迹（`etr_tr`、`tr_etr`）。于是：一个组件在展开后的表中理想失败，当且
仅当它的扩展轨迹停在被拒的读取、程序失败或操作失败上（`kinds_cover`），而且恰好是其中一种
（`kinds_exclusive`）；种类只取决于 ρ 在依赖上的取值（`kind_ext`）。配合 `FailCrux.quiet_failed_ideal`，
quiet 状态中每个失败的 fiber 都有唯一的失败种类，且在相同输入的每次运行中相同，运行时可以据此报告。

### 5.3 外部资源的释放失败（`Resource.v`，已完成）

受管状态 S 上的逆不失败（P3）。会失败的是外部资源的释放：关闭子进程、清除计时器、删除文件。

**实际采用的形式。** 不新增程序构造：获取资源就是服务标记为 `IsAcq` 的操作（S 记下句柄），释放就是撤销
这个操作。S 照常去掉记录；外部世界是否真的放手是另一件事，由运行时记录。状态多两个令牌日志 `released`
与 `leaked`：`RCore (LUndo n)` 撤销一个获取并记为已释放；`RFail n` 同样在 S 上撤销，但记为泄漏。

- **鲁棒（`rstep_core`、`rrun_core`）。** 每一步都是核心的一步（`RFail n` 即 `LUndo n`），所以无论哪些释放
  失败，S 上的安全性、进展、终止、恢复精确性都照核心成立。
- **没有静默的泄漏（`rinv_step`、`rinv_reachable`）。** 曾经执行过的每个获取，要么仍由某个 fiber 持有（撤销项
  在累加器里），要么已释放，要么记为泄漏。证明用到：撤销项只在被弹出时离开累加器（`item_after`），新的操作
  由执行它的 fiber 持有（`oplog_after`）。
- **全部卸载之后（`all_unloaded`）。** 没有已安装的 fiber 时，每个获取都已释放或记为泄漏。
- **泄漏不标在 fiber 上。** 演算判断不了残留是否造成问题，标上则一个不稳定的释放就能让整个插件停下。泄漏
  只作为诊断信息。

这与 EDSL.md 5.2 中 `resource` 原语的义务（`release` 逆 `acquire`）是同一件事。

### 5.4 失败的传播

核心中失败不传给父 fiber，父 fiber 失败时子 fiber 随撤销退役，提供者失败时依赖者回到 Inactive。符合 P3，
保持不变。`O-React` 起的子 fiber 失败只影响它自己，核心已覆盖（`Runtime.v`）。

## 6. 定理目标汇总

| 部分 | 保持性、顺序 | 恢复 | 终止、进展 | 合流 |
|---|---|---|---|---|
| 4.0 过时的加载不记失败 | 核心的子集（已证） | 核心的子集 | 核心的子集（已证） | 第 3 节的一块 |
| 4.1 Cordis 的接纳做法 | — | — | — | 反例（已完成） |
| 5.1 接纳队列 | 对应核心执行（已证） | 同 | 字典序；quiet 时队列为空（已证） | 同输入同插入顺序 |
| 第 1、3 节 失败按视图记录 | 对应核心执行（已证） | 同核心 | 进展、终止（新度量）已证 | 包含失败（已证：控制状态与服务状态，不含 spawn） |
| 5.2 确定的外部读取 | 核心的实例（已证） | 核心的实例 | 核心的实例（终止已示范） | 核心的实例（控制合流已示范） |
| 5.3 资源释放失败 | 核心的一步（已证） | S 上同核心；没有静默的泄漏（已证） | 同核心 | 同核心 |

## 7. 给 Cordis 的建议

都需要先在演算里证完再提：

| # | 建议 | 依据 |
|---|---|---|
| 1 | 提供集合静态声明（强制执行 `Plugin.provide` 元数据），在插入时检查冲突；与正在 dispose 的插件冲突时排队，而不是在 `provide` 时抛错 | 5.1；#358 |
| 2 | 失败记下它所在的视图，依赖换了提供者时自动重试 | 第 1 节 |
| 3 | 区分程序失败与外部失败；外部结果按视图缓存，`update()` 时重新读取 | 5.2 |
| 4 | 把服务上的登记（不能失败）与资源的释放（可能失败、要记录）分开；每个 disposer 单独隔离 | 5.3；2.3 第 4 条 |
| 5 | 2.3 中的代码问题 | 2.3 |

## 8. 与 difftest 的联系

difftest 量的是 Cordis 与演算的距离，分歧就是第 7 节建议的证据。组件规格新增 `['ext', ok]` 和释放会失败的
资源；编排脚本新增"dispose 之后不等落定就 insert"一类。现状的 Cordis 对照 `astep`，按建议修改过的 Cordis
对照演算本身。

## 9. 文件与顺序

| 文件 | 内容 | 状态 |
|---|---|---|
| `theories/Superseded.v` | 4.0 | 完成 |
| `theories/Admit.v` | 4.1 | 完成 |
| `theories/Queue.v` | 5.1 | 完成 |
| `theories/ViewFail.v` | 第 1 节：失败按视图记录；对应核心、安全性、quiet 时失败都在当前视图下 | 完成 |
| `theories/VTermination.v` | 第 1 节：新度量下的终止 | 完成 |
| `theories/Classify.v` | 第 3 节第 1 层：失败集合相同时控制状态合流 | 完成 |
| `theories/IdealFail.v`、`theories/FailCrux.v`、`theories/FailConf.v` | 第 3 节第 2 层：每种失败都是理想失败（FailCrux，义务：spawn 出的组件不提供键）；失败集合相同、合流包含失败（FailConf，不含 spawn） | 完成 |
| `theories/StateConfF.v` | 第 3 节：合流包含失败，服务状态 ≃ | 完成 |
| `theories/SpawnConfF.v` | 第 3 节：合流包含失败，含 spawn（义务 A：spawn 出的组件不提供键） | 完成 |
| `theories/Async.v` | 5.2 | 完成 |
| `theories/AsyncKind.v` | 5.2：外部失败的归因 | 完成 |
| `theories/Resource.v` | 5.3 | 完成 |

顺序：接纳队列 → 失败按视图记录与合流包含失败（主体）→ 确定的外部读取 → 资源释放失败。
