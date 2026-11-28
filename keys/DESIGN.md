# 键的卫生：默认私有，显式导出（设计）

本目录把贡献键（[../docs/CONTRIB.md](../docs/CONTRIB.md)）的卫生思路从"键里面"推广到"键本身"：一个插件
`provide` 的服务默认只给它自己的子树用，要给别的插件用必须显式导出；导出的名字有多个提供者时，冲突是一个
确定的值，而不是失败。实现与证明的进度见第 6 节。

定位与 `errors/` 相同：目标是一个自足的演算，规则按原则取舍；Cordis 的现状是证据，不同之处整理成给 Cordis
的建议。

## 0. 为什么

### 0.1 现在的模型怎样对待键

核心演算里键是一个全局名字：

- 组件静态声明提供集合 `provs`，`O-Insert` 要求在场 fiber 的提供集合两两不交，`PSpawn` 做同样的检查；
  于是**提供键的组件同一时刻至多一个 fiber**。
- 依赖按名字解析到唯一的绑定；绑定的提供者是唯一的。
- `Derived.scoped` 把 Cordis 的 `isolate` 建模为对组件表做键重命名（键 = 作用域标签 × 名字，作用域是静态的）。

### 0.2 由此带来的问题

| 问题 | 出处 |
|---|---|
| 不同插件用同一个内部服务名就会冲突；冲突只能在插入或 provide 时报告 | 差异 c；`errors/` 的 #358 分析 |
| 同一个插件不能有两个实例，只要它提供任何键 | 核心的 `wf_disjoint` |
| 子组件提供键时 spawn 可能冲突，于是需要 spawn 义务 B、接纳队列的 `HSpawnRoot` | `errors/FailCrux.v`、`errors/Queue.v` |
| 子 fiber 不经 inject 就沿父链读到父 fiber 的服务，不在依赖者集合里，父 fiber 卸载时不等它（上游已由测试确认） | 差异 e |
| `ctx.get` 可以读任何服务，dsh 非测试代码中 368 处 | 差异 m |
| 两个插件都提供 `dshRemote`：键层面的冲突，贡献键不覆盖 | CONTRIB.md 第 6 节 |

前三条都来自"每个键都在一个全局命名空间里"；后三条都来自"读服务不必声明"。

### 0.3 原则

| # | 原则 |
|---|---|
| K1 | **默认私有**：fiber 提供的键只在它的子树（它 spawn 出的子孙）中可见 |
| K2 | **显式导出**：要给子树之外用，组件必须声明导出这个名字 |
| K3 | **私有键按实例区分**：同一组件的两个实例的私有键互不相干 |
| K4 | **导出名的冲突是值，不是失败**：多个提供者导出同一个名字时，解析结果只取决于在场的提供者集合，与次序无关（与贡献键相同） |
| K5 | **依赖必须声明**：私有的和导出的都一样；没有隐式读取 |
| K6 | **保守**：所有键都导出、每个名字至多一个提供者、没有私有依赖时，就是核心 |

## 1. 模型

### 1.1 名字与键

关键的一步：**运行时的键总是带实例的**，名字到键的映射是一次解析。

- 名字 `x`：程序与组件声明里写的服务名。
- 键 `(n, x)`：fiber `n` 提供的名字 `x`。每个 fiber 有自己的键，所以**绑定永远不冲突**：`PProvide x` 在
  fiber `n` 里写的是键 `(n, x)`，别的 fiber 碰不到。`O-Insert` 与 `PSpawn` 不再需要冲突检查。
- 组件声明：
  - `provs : list Name`（提供的名字），其中 `exports ⊆ provs` 是导出的；
  - `prio : Name → nat`（导出名的优先级，见 1.3）；
  - `deps : list Dep`，`Dep := Local x | Global x`。

### 1.2 解析

一个 fiber 的依赖在 `L-Begin` 时解析成键，记进视图（视图仍然是名字 → pid，pid 是那个键上绑定的标识）。

- **`Local x`（私有依赖）**：沿父链向上，找最近的、组件私有地提供 `x` 的祖先 `a`，解析为键 `(a, x)`。
  这是词法作用域；与 Cordis 现在的 `locate` 沿父链查找一致，区别是必须声明。
- **`Global x`（导出依赖）**：在**导出名空间**里解析，见 1.3。

可见性（核心的 `visible`）照旧：键有绑定，且提供者是 Active。target 照旧是"全部依赖都能解析"时的视图，
否则为 ⊥。

### 1.3 导出名：像贡献键一样

导出名 `x` 的候选是所有**导出 `x` 且键 `(n, x)` 可见**（已绑定、提供者 Active）的 fiber。解析规则与贡献键的 `classify` 同构：

```
select x := 候选中优先级最高者；
            恰好一个  ⇒ 解析为它的键 (n, x)
            没有      ⇒ 未解析
            多于一个  ⇒ 冲突：未解析，并作为诊断报告
```

所以导出名的冲突不让任何 fiber 失败：依赖它的 fiber 只是 target 为 ⊥（等待），与"依赖缺失"同样处理（P2）。
冲突的一方离开，或者优先级改变，解析就落到唯一的一方，依赖者照常加载。规则可以换（CONTRIB.md 列出的
"都不生效并报告"或"唯一最高优先级者生效"），唯一的要求是**只取决于候选集合**。

候选必须是 Active 的：Unloading 的提供者不参与解析。于是 #358 的情形自然消失：旧提供者已退役、在卸载，
新提供者 Active 之后就是唯一候选，依赖者绑定到它；不需要接纳队列，也不会冲突。

### 1.4 依赖关系与秩

- 私有依赖 `Local x` 只能指向祖先，静态上要求：每条 spawn 路径上都有祖先组件私有地提供 `x`（在组件表上检查）。
- 秩：`Global x` 的依赖者高于每个导出 `x` 的组件；`Local x` 的依赖者高于提供 `x` 的祖先组件（本来就因 spawn
  边而更高）。`Above` 的定义只需把"提供 → 依赖"一项按两种依赖分别写。

### 1.5 卸载

私有依赖是真正的依赖：父 fiber 的私有键被子 fiber 解析，守卫 `held` 就让父 fiber 等子 fiber 退出后才撤销这个
服务。这修正了差异 e（子 fiber 异步清理时读不到父 fiber 的服务），不需要额外的规则。

## 2. 与核心、与已有扩展的关系

### 2.1 演算改在哪里

改动集中在两处：

1. **键带实例**：`PProvide x` 写键 `(n, x)`；去掉 `O-Insert`、`PSpawn` 的冲突检查和 `PProvide` 的 `EConflict`
   （只剩"同一 fiber 重复提供"，由 `HProv` 排除）。
2. **解析函数**：`resolve` 对每个依赖按 1.2 / 1.3 求键。它读父链和导出候选的 Active 状态，所以 target 可能
   因为候选的出现、消失或优先级更高者变为 Active 而改变；这与核心里"提供者重新 provide 导致依赖者重新加载"
   是同一种机制（差异 b），依赖者经 `L-Leave` / `L-Divert` 重新加载。

这不能归约为 `Derived.scoped`：那里的作用域是静态标签，这里的作用域是实例（运行时的 fiber 名字）。所以做成
与 `errors/` 同样隔离的扩展，`keys/theories/`，逻辑名 `CordisKeys`，核心不 import 它。

### 2.2 保守性（K6）

所有名字都导出、每个名字至多一个组件导出、没有 `Local` 依赖时：导出名至多一个候选，解析与核心的"按名字找绑定"
一致；键 `(n, x)` 与核心的键 `x` 一一对应（因为至多一个 fiber 提供 `x`）。要证明：这时扩展的每一步就是核心的
一步，核心的定理全部搬过来。

### 2.3 要证的

| 性质 | 说明 |
|---|---|
| 安全性 | 不变式比核心简单：不再需要 `wf_disjoint`，每个键的绑定天然唯一 |
| 终止 | 新增的重新加载（候选变化导致 target 改变）都由更低秩的步骤触发，度量结构与核心相同（参考 `errors/VTermination.v`） |
| 进展 | "稳定"的定义里，target 为 ⊥ 的原因多一种：导出名冲突。quiet 状态中冲突是确定的（见合流） |
| 恢复精确性 | 键按实例分开，两个 fiber 的私有键上的操作不会相遇；相遇只发生在导出名解析到的同一个键上 |
| 合流 | quiet 终态中，每个导出名的候选集合由不动点决定（候选的 Active 与否沿秩归纳确定），解析结果因而确定；私有键沿规范名对应（`SpawnConf` 的 `CN`，实例身份正好由它给出） |
| 与 `errors/` 合起来 | 失败按视图记录、外部读取、资源等都与键的结构无关，预期可以直接叠加 |

### 2.4 对已有义务的影响

- spawn 义务 B 与 `HKidParent`、接纳队列的 `HSpawnRoot`、核心的"提供键的组件至多一个 fiber"：**都不再需要**。
  spawn 与插入永远不冲突。
- `HNoRej`（相遇的操作不拒绝）仍然需要，但相遇的范围缩小到"解析到同一个导出键的依赖者"之间。
- 插件义务"有秩、相遇受控、完整提供"不变；新增的静态义务只有 1.4 的"私有依赖有祖先提供"。

## 3. 给 Cordis 的建议（草拟）

```js
export const name = 'dsh-remote'
export const provide = {
  export: { dshRemote: { priority: 10 } },   // 导出名与优先级
  private: ['state', 'dispatcher'],           // 只给自己的子插件
}
export const inject = ['webServer', 'local:state']   // 导出依赖与私有依赖
```

- 宿主按实例给私有键分作用域（相当于自动 `isolate`），插件不需要起全局唯一的名字；
- 导出名冲突时不抛错：按优先级确定一个，并列时谁都不生效，宿主在诊断中报告；
- `ctx.get` 只能读声明过的依赖；子插件读父插件的服务要写 `local:`，宿主因此知道这条依赖，卸载时会等它；
- 迁移：旧插件的 provide 全部视为导出、优先级相同；新写法逐步采用。

## 4. 待定问题

1. **私有依赖的解析**：最近的祖先（允许遮蔽），还是要求唯一的提供者？前者与 `locate` 一致，后者更容易检查。
2. **导出冲突的默认策略**：都不生效（最安全），还是唯一最高优先级者生效？优先级由组件声明还是由用户配置覆盖？
3. **运行期反应（`O-React`）起的子 fiber** 是否也在父 fiber 的私有作用域里？倾向于是。
4. **一个组件能否既导出又私有地提供同一个名字**：倾向于不允许。
5. ~~导出名的候选只算 Active 的~~ **已定：只算 Active 的**（准确地说，键可见的）。代价是依赖者可能先绑到
   低优先级者、再改绑到高优先级者（`Examples.v` 的 `single_leaves`）；好处是卡住的候选挡不住别人。改绑由
   终止定理兜底。

## 5. 文件与顺序

| 文件 | 内容 |
|---|---|
| `keys/theories/Scoped.v` | 名字、依赖、带实例的键；解析函数；`kstep`；保守性 |
| `keys/theories/ScopedSafety.v` | 不变式、安全性、恢复 |
| `keys/theories/ScopedTerm.v` | 终止（已完成）；进展在 `ScopedProgress.v`（已完成） |
| `keys/theories/ScopedConf.v` | 合流：导出名候选的不动点；私有键沿规范名对应 |
| `keys/theories/Examples.v` | #358（不再冲突）、`dshRemote`（冲突成为值）、同一插件两个实例、差异 e（父 fiber 等子 fiber） |

顺序：先写 `Scoped.v` 与计算的例子，确认模型的行为；再证保守性和安全性；终止、合流最后。

## 6. 状态

**`Scoped.v`（已完成）**：归约到核心，做法与 `theories/Ext/Optional.v` 相同。

- 作用域是规范路径：插入为名字 `n` 的根 fiber 作用域是 `[Rt n]`；作用域为 `s` 的 fiber，体中第 `j` 个 spawn
  是 `Sp j :: s`；第 `i` 个反应处理器的一次触发若创建名为 `t` 的 fiber，作用域是 `Re i t :: s`。spawn 的作用域
  静态可算；反应的作用域靠盖戳：`X-React` 先把父 fiber 组件的 `tick` 设为 `next`，再做核心 `O-React`。
- fiber 的组件是记录 `XC`：基组件、作用域、祖先私有名的环境 `env`（近者在前）、导出依赖的选择 `sel`。核心
  组件表 `prog'` 把它读成键为 `Scope * N` 的组件：`PProvide x` 写 `(scope, x)`；`Local x` 在 spawn 时由
  `env` 定为 `(s, x)`；`Global x` 为 `(sel x, x)`，`sel` 在 `X-Begin` 选定。
- `select`：候选中优先级唯一最高者；没有或并列时为 `None`，并列由 `tied` 作为诊断报告。
- `kstep`：`X-Begin` 要求每个导出依赖都已解析，选定后做核心 `L-Begin`；`X-Step` 要求选择未变；选择变了
  （更高者出现、出现并列）时 `X-Divert` / `X-Leave` 强制卸载，即核心的 `O-Restart`；`X-React` 盖戳后做核心
  `O-React`。

| 定理 | 内容 |
|---|---|
| `kstep_core` | 每一步是 `prog'` 的核心一步、选定选择后的核心 `L-Begin`、核心 `O-Restart`，或盖戳后的核心 `O-React` |
| `kstep_fresh` | 选择未变时，扩展步就是核心步 |
| `conflict_scope` | 没有在场 fiber 与之同作用域的组件不会冲突：核心的冲突检查归结为作用域唯一 |
| `wf_recomp`、`kpreservation`、`kwf_reachable` | 扩展执行保持核心 `WF`，核心的次序定理全部成立 |
| `kstep_conservative` | 没有导出依赖时（导出名可以有），扩展步就是核心步（`O-React` 先盖戳） |

**`ScopedSafety.v`（已完成，不用任何公理）**：作用域唯一，核心的冲突检查因此永不触发。

不变式 `SI`：在场 fiber 的作用域两两不同（`si_uniq`）；作用域里的根名字与反应戳都小于 `next`（`si_bound`），
所以由 `next` 造出的作用域是新的；作用域为 `Sp j :: s` 的 fiber 有作用域为 `s` 的在场父 fiber（`si_parent`）；
Loading 的 fiber 运行 `lift x j Q`，且它在场的 `Sp j' :: scope x` 子 fiber 都有 `j' < j`（`si_load`），所以下一次
spawn 是新的。

| 定理 | 内容 |
|---|---|
| `si_step`、`si_kstep`、`si_reachable` | 每个核心步（插入在新的根作用域、反应已盖戳）与每个扩展步都保持 `SI` |
| `insert_enabled` | 插入总是可行 |
| `spawn_ok` | Loading fiber 将要 spawn 的组件不冲突 |
| `react_enabled` | fiber Active、未 dispose、有这个处理器时，反应总是可行（同一处理器可以并发多次） |
| `provide_self` | fiber 自己作用域上的绑定属于它自己：`PProvide` 只会与同一 fiber 先前的同名提供相遇 |

`Examples.v`（计算验证）：同一插件两个实例各自提供私有 `state`、子 fiber 各读各的；两个同优先级导出者并列，
依赖者等待且 `tied` 报告；更高优先级者出现后依赖者绑定到它；已绑定的依赖者在更好的候选 Active 后离开并改绑；
同一反应处理器并发触发两次，两个子 fiber 各自提供私有 `state`。

**`ScopedTerm.v`（已完成，不用任何公理）**：扩展的生命周期步单独不能无限进行（`ktermination`、
`kno_infinite_run`），从任何可达状态出发都如此（`ktermination_reachable`）。做法照 `theories/Ext/OptTermination.v`。

- 秩义务 `KAbove`：名字的提供者（私有或导出）低于依赖这个名字的组件（`Local` 或 `Global`）；父组件低于它
  spawn 的组件。于是导出者低于 `Global` 依赖者，改绑只由更低秩的步骤触发。
- 度量 `kmu` 与核心同形，两处改动：Loading / Active 的 fiber "在目标上"要求选择仍是当前的、核心目标等于视图
  （`ktis`）；卸载将完或 Inactive 的 fiber 是否会再开始，看的是重新选择之后的目标（`bt`）。
- 关键的稳定性：`n` 的一步不改变秩不高于 `n` 的 fiber 依赖的名字上的键的可见性，也不改变这些名字的选择
  （`vis_stable`、`select_stable`）。后者要用作用域唯一（`ScopedSafety.SI`）：只有作用域为 `s` 的 fiber 在 `s`
  上绑定。
- 核心的 `lstep_effects`、`tinv_step` 经表 `progG γ` 复用：X-Begin 重选子 fiber 的选择、X-React 给父 fiber 盖戳，
  子 fiber 的组件不再字面上是父组件创建的那个，只有基组件对得上（`KSpawnProv`）；`progG γ` 把在场子 fiber 的
  组件加进父组件的处理器列表，满足核心的 `Inv2`。

**`ScopedProgress.v`（已完成，不用任何公理）**：没有死锁。扩展的生命周期规则都不适用时，每个 fiber 都
settled（`kquiet_settled`，可达状态见 `kquiet_settled_reachable`）：

- 没有 fiber 在 Loading 或 Unloading；
- Active 的 fiber 目标等于视图，且选择是当前的；
- Inactive 且无错误的 fiber 未 dispose，且重新选择后没有目标（`bt = None`）。原因只有两种（`bt_none_reason`）：
  某个导出依赖没有唯一候选（没有候选，或最高优先级并列，`tied` 报告），或某个依赖键不可见。

核心定理不能像 `Ext/OptProgress.v` 那样经表套用：过时的选择可能仍能解析，核心的 `L-Begin` 可用而 X-Begin
被挡住，扩展的 quiet 状态未必是核心意义上的 quiet。证明照核心的写，归纳沿秩（`KAbove`）。

**`ScopedConf.v`（已完成，不用任何公理）**：控制层合流，组件不 spawn（与核心 `Confluence.v` 相同的范围）。
从同一状态出发、各自以 quiet 且无失败结束的两次扩展生命周期执行，结果有（`kcontrol_confluence`）：

- 同样的 fiber，基组件、作用域、私有环境都相同；
- 同样的 fiber 是 Active 的；
- 每个键由同一个 fiber 绑定；
- 每个导出名的候选列表相同，因而解析相同、并列（冲突诊断）也相同（`kselect_confluence`）；
- 每个 Active fiber 的导出依赖选择相同。

不动点方程换了形式：quiet 无失败的状态中，fiber 是 Active 的当且仅当重新选择后有目标（`act_bt`，来自
`ScopedProgress`）。这个目标只读依赖名字上的键是否可见（提供者秩更低）和导出依赖的候选（秩也更低），所以两个
终态的活跃性沿秩归纳一致，其余随之而来。核心的 `active_iff`、`owner_iff` 不能直接用：quiet 的扩展状态中，
Inactive fiber 过时的选择可能仍能解析，状态未必是核心意义上的 settled；只复用 `active_binds`。

**`ScopedSpawn.v`（已完成，不用任何公理）**：带 spawn 的合流，含服务状态（核心 `SpawnConf.v` 的对应）。
从同一状态出发、各自以 quiet 且无失败结束的两次扩展生命周期执行，在把 Inactive fiber 过时的选择规范化之后
（`norm`，只改 Inactive fiber 的 `sel`）按规范名对应（`kspawn_confluence`）：

- 规范名各命名每个 fiber 一次；同样的名字出现，组件（作用域与选择在内）与活跃性相同；
- 对应的 fiber 拥有每个键，每个键的服务状态 ≃；
- 每个导出名的解析相同，并列也相同。

静态义务：父组件声明子组件依赖的每个导出名（`kSub`）。子 fiber 在 spawn 时继承父 fiber 的选择
（`Scoped.inherit`），之后不再重新选择，所以它的组件始终是父 fiber spawn 出的那一个，核心的轨迹不变式
`Episode.Corr` 检查的正是这一点；quiet 状态下子 fiber 的选择是当前的，因为父 fiber 的是（`quiet_child_fresh`）。
最初的版本要求子组件根本不声明导出依赖（`NoGlobalChild`），已由继承取代，见下文。

证明在核心之上加的：终态规范化，使每个 fiber 的选择都是当前的（`Fresh`）；核心的秩归纳只改一处——对应的根
fiber 除选择外都相同，选择相同由更低秩的对应推出（`select_corr`）：导出名的候选秩更低，对应的候选作用域、
优先级与活跃性都相同，两边的候选列表互为排列，而解析与次序无关。导出者可以是子 fiber，两次执行中名字不同，
所以需要排列而不是逐点相等。作用域唯一（`SI`）把 fiber 作用域上的键的所有者认定为该 fiber 本身。

为此先做了两处基础调整（提交 `7a970b9`）：`fresh` 改为字面比较（存下的选择等于现在选择会给出的），使对应的
fiber 组件可以字面相等；`SI` 增加 `si_ne`（在场 fiber 的作用域非空），未解析的导出名读作空作用域，因而不可见。

**子 fiber 继承选择（取代 `NoGlobalChild`）**：

- 规则：根 fiber 在 `X-Begin` 时选择；子 fiber 不选择，spawn 时由 `inherit` 从父 fiber 的选择取得自己导出依赖的
  解析（`child` 的 `sel`），`X-Begin` 只要求它是当前的（`fresh`）。选择过时时，父 fiber 也过时，经 `X-Leave` /
  `X-Divert` 重新加载并带走子树。
- 静态义务 `kSub`：子组件依赖的导出名父组件也声明（父组件为子树声明依赖）。
- 不变式 `SI.si_child`：每个子 fiber 的选择是从父 fiber 当前组件继承的。父 fiber 的选择只在它 Inactive 时改变，
  那时它没有子 fiber。
- 由此 `ScopedProgress.child_fresh`：父 fiber 当前则子 fiber 当前；quiet 状态下的子 fiber 都是当前的，进展定理的
  形式不变。终止、控制层合流、带 spawn 的合流都照常成立，不用任何公理。
- `Examples.v` 的 `inherited`：依赖 `svc` 的父组件 spawn 也依赖 `svc` 的子组件，子 fiber 继承选择并加载。

**根作用域由实例 id 给出**（提交 `006021f`）：根 fiber 的作用域原先是它的运行时名字 `[Rt n]`，而运行时名字随调度
变化（生命周期步也推进 `next`），同样的输入交错不同，同一个根就有不同的作用域与键。改为编排者给出的实例 id：组件
声明 `xinst`（相当于 Cordis 的配置项），根作用域为 `[Rt (xinst c)]`；`X-Insert` 在已有 fiber 占用该作用域时拒绝
（`taken`）。`SI` 不再用 `next` 约束根段，插入的新鲜性来自这项检查；`insert_enabled` 相应地要求实例 id 未被占用。
`Examples.v`：两个实例是两个 id 不同的组件；同一实例插入两次被拒绝（`duplicate_rejected`）。

**`ScopedDynamic.v`（已完成，不用任何公理）**：与编排交错的合流（核心 `Dynamic.v` 的对应）。从初始状态出发，编排
输入（插入基组件、dispose、restart、reset）与扩展生命周期步任意交错，以 quiet 且无失败结束；若两次执行的输入留下
同样的存活组件、次序相同，则把 Inactive 根 fiber 过时的选择规范化后按标签对应，且每个导出名解析相同、并列相同
（`kdynamic_agree`）。推论：同样的输入任意交错（`kdynamic_confluence`）；任何历史的终态与只按次序插入存活组件
的执行一致（`kstatic_assembly`）。根账本 `KLedger` 记录基组件，并记录根 fiber 的作用域是 `[Rt (xinst c)]`、私有
环境为空、戳为 0，于是对应的根组件除选择外都相同，选择相同由 `ScopedSpawn` 的秩归纳给出。

下一步：

- 对基核心的保守性（K6 的完整形式：所有名字导出、每个名字至多一个提供者时与基组件表上的核心互模拟）需要
  键 `x ↔ (s, x)` 的模拟关系。此处的 `kstep_conservative` 是较弱的形式。
- 与 `errors/` 的失败合起来。
