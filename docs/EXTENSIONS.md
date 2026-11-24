# 模型扩展:可选依赖、编排者、交集生命期

[PLUGIN-AUDIT.md](PLUGIN-AUDIT.md) 的"对形式化的影响"一节列出了真实 dsh 插件需要、而核心模型没有的机制。本文按影响的插件数排序,给出前三项的设计:

1. 可选依赖;
2. 编排者义务;
3. 交集生命期的效应。

第四项"外部持久世界"不在本文范围内。

## 0. 隔离与方法

**隔离。**

- 扩展放在 `theories/Ext/`,逻辑名 `Cordis.Ext.*`,列在 `_CoqProject` 末尾,由 `build.sh` 一并编译。
- 依赖是单向的:扩展 import 核心,核心不 import 扩展。可以用 `grep -rn "Cordis.Ext\|Ext\.Optional" theories/*.v theories/Services theories/Examples` 检查,结果应为空。
- 核心文件 (`theories/*.v`,包括 `Summary.v` 的四层汇总定理)、[DESIGN.md](DESIGN.md)、[RULES.md](RULES.md) 和博客笔记 `dsh0.rkt` 都不因扩展而改动。

**方法:归约到核心。** 能归约的地方,扩展的一步定义为"在为该状态选定的组件表下走一步核心 `step`",外加少量不碰服务状态、不碰累加器的簿记步。

- 核心的定理都对任意组件表 `prog` 陈述,所以单步性质 (`preservation`、`Ordering` 中的各条、`quiet_settled`) 对扩展直接成立。
- 只有核心没有的步需要新证明。

每项扩展的结论按汇总定理的四层分列:

| 记号 | 含义 |
|---|---|
| **保守** | 由核心定理加一个小引理导出,不重证 |
| **推广** | 需要新的证明,但沿用核心的证明结构 |
| **不覆盖** | 扩展后不再成立,或不在本扩展范围内 |

## 1. 可选依赖 (`Ext/Optional.v`、`Ext/OptProgress.v`,已形式化)

### 1.1 动机

审计中过半插件的 S1 (读未注入的服务) 和 C2 (启动分支依赖服务在不在) 来自同一种写法:

```ts
const llm = ctx.get('llm')   // 没有 inject
if (llm) { ... 登记 A ... } else { ... 登记 B ... }
```

作者这样写,是为了在缺少该服务的宿主上不停在 PENDING。核心模型只有必需依赖,这种写法只能记为越界 (差异 m)。

### 1.2 语义

**组件声明** (`XComponent`):

| 字段 | 含义 |
|---|---|
| `xdeps` | 必需依赖,同核心 |
| `xopt` | 可选依赖:有就用,没有不等 |
| `xprovs`、`xreacts` | 同核心 |
| `xbody : (K → bool) → Prog` | 启动程序,按可选依赖是否在场选择变体 |

**在场集 S**:加载开始时 (`L-Begin`),`xopt` 中提供者处于 Active 的键 (`present`)。

- 启动程序取 `xbody (∈ S)`,覆盖 C2。
- S 中的键进入视图 ω,程序可以对它执行 `POp`,覆盖 S1。
- 不在 S 中的可选键与未声明的键一样,读取会失败。

**在场集变化时一律重载。** 加载中或已 Active 的 fiber,只要当前的在场集不再等于加载时的 S (`fresh` 为假),扩展目标就是 ⊥,fiber 中途放弃或离开,之后按新的在场集重新加载。

- 出现和消失两个方向都重载。
- 否则 S 取决于提供者恰好何时激活,终态与调度有关,合流必然失败。
- "可选依赖出现时不重载"的写法不建模。它只能保住第 0–2 层;运行期才去读的服务应放进反应 (`O-React`)。

**可选依赖不阻止激活。** fiber 是否 Active 只取决于必需依赖。

**组件义务**,在核心义务之外再加两条:

1. `xopt c` 与 `xprovs c` 不相交。否则 fiber 一激活,自己就出现在自己的在场集里,随即重载、撤回、再加载,无限循环。这一条由第 2 条推出:提供者到可选依赖者也是 `XAbove` 的边,自己提供自己的可选依赖会让秩严格小于自己。
2. 秩沿可选依赖边也严格递增 (`XAbove`)。否则两个互为可选依赖的组件可能互相触发重载,永不停止。

### 1.3 规则

fiber 的组件记为二元组 (c, S),S 是加载开始时的在场集。核心组件表 `prog'` 把 (c, S) 读作:

```
deps  (c,S) = xdeps c ++ (S ∩ xopt c)
provs (c,S) = xprovs c
body  (c,S) = lift (xbody c (∈ S))     -- lift:spawn 出的子组件记为 (c', [])
reacts(c,S) = [(c', []) | c' ← xreacts c]
```

| 标签 | 规则 |
|---|---|
| `X-Begin n` | `θₙ = Inactive None`:先把 n 的组件换成 (c, present γ c) (`recomp`),再走核心 `L-Begin` |
| `X-Step n` | 在场集未变 (`fresh`) 时走核心 `L-Step`,否则不能走。核心 `L-Step` 在 target 变化后仍可落地 (DESIGN.md 差异 h);在场集变化之后的落地不在扩展之内 |
| `X-Divert n` | 在场集未变时走核心 `L-Divert`;变了时,`Loading _ acc ω` 直接进入 `Unloading acc ω None` |
| `X-Leave n` | 同上,对 `Active acc ω` |
| 其他标签 | 核心规则;`O-Insert c` 插入 (c, []) |

**与核心的对应:**

- `xstep_core`:扩展的每一步是以下三者之一:
  - 核心的一步;
  - 换组件 (`recomp`) 再走核心 `L-Begin`;
  - 核心的 `O-Restart`。在场集变化而核心目标未变时的 `X-Divert`/`X-Leave` 就是 `O-Restart`:fiber 未退役,否则核心目标已是 ⊥,走的是核心 `L-Divert`/`L-Leave`。
- `xstep_fresh`:反过来,在场集未变的 fiber 上,`X-Step`/`X-Divert`/`X-Leave` 就是核心规则。
- `xstep_conservative` (保守性):没有任何可选依赖时 (`NoOpt`),在所有组件都是 (c, []) 的状态上 (`Plain`),扩展的一步就是 `prog'` 下核心的一步。

### 1.4 哪些定理成立

| 层 | 状态 | Rocq |
|---|---|---|
| 0 安全 | **保守**。`WF` 只在 fiber 已安装时读依赖,且提供集合与 S 无关,所以给 Inactive 的 fiber 换组件保持 `WF` (`wf_recomp`)。其余步由核心 `preservation` 保持。于是核心 `Ordering` 的单步定理 (`provider_outlives`、`withdraw_waits`、`unload_waits`、`parent_waits_child` 等) 在每个扩展可达状态上成立,对其中的核心步直接适用 | `wf_recomp`、`xpreservation`、`xwf_reachable` |
| 1 活性:不死锁 | **保守**,经过一处转换,见下文 | `xquiet_settled`、`xquiet_settled_reachable` |
| 1 活性:终止 | **推广**,已证,不需要子组件限制。见 1.4.1 | `xtermination`、`xno_infinite_run`、`xtermination_reachable` |
| 2 恢复 | **保守**,已证,不需要子组件限制。重选在场集不碰存储和累加器,保持核心的不变式 `R` (`R_transfer`) 与 `Prov` (`prov_recomp`);其余步就是核心步,用核心的 `R_step`。覆盖任意扩展执行 (含编排与 `O-React`) | `xrecovery_exact`、`xrecovery_from_init` (`Ext/OptRecovery.v`) |
| 3 合流:控制状态,不含 spawn | **推广**,已证。见 1.5 | `xcontrol_confluence` |
| 3 合流:服务状态,不含 spawn | **推广**,已证。见 1.5 | `xstate_confluence` |
| 3 合流:含 spawn | **推广**,已证,限子组件无可选依赖。见 1.5 | `xspawn_confluence` |
| 3 合流:与编排交错 (论文定理 80) | **推广**,已证,限子组件无可选依赖。见 1.5 | `xdynamic_agree`、`xdynamic_confluence`、`xstatic_assembly` |

#### 1.4.1 终止 (`Ext/OptTermination.v`)

核心的度量不能照用。它读核心目标,而一个可选依赖刚出现的 fiber 核心目标没变,却必须重载。新的度量 `xmu` 与核心的形状相同,只改两处:

- 加载中或 Active 的 fiber 算"在目标上",要求在场集仍是当前的,且核心目标等于它的视图 (`xtis`)。
- 卸载将尽或 Inactive 的 fiber 会不会再加载,按它重选在场集后的目标判断 (`bt`)。

状态的度量和核心一样,是按秩分层求和的向量,每一步都使它按字典序下降 (`xphi_drop`)。

**成立的原因。** 一个 fiber 的一步,不改变秩不高于它的 fiber 所读的键 (必需与可选) 的可见性,也就不改变它们的在场集 (`vis_stable`、`present_stable`)。这依赖秩沿可选依赖边也递增。

**复用核心。**
- 核心的 `lstep_effects`、`tinv_step` 经 `OptProgress.progG` 使用。这张表满足核心的 `Inv2`,而 `prog'` 在子 fiber 重选在场集后未必满足。
- 不变式是 `XTInv`:`XInv` 加上核心的 `LoadBound`、`SpawnOwn`。

**结论。**
- `xtermination`:满足 `XTInv` 的状态在扩展生命周期步下可及 (Acc)。
- `xno_infinite_run`:不存在无限的扩展生命周期步序列。
- `xtermination_reachable`:任意扩展执行 (含编排与反应) 到达的状态都是如此。

不需要子组件限制,不依赖任何公理。

**不死锁定理的转换。** 核心 `quiet_settled` 要求 `Inv2`,其中一条是"子 fiber 的组件是父组件可能创建的"。X-Begin 会把子 fiber 的组件从 (c, []) 换成 (c, S),这条不再字面成立;按基组件 c 来说仍然成立 (`XSpawnProv`)。

- 于是把核心定理用在表 `progG γ` 上。它与 `prog'` 只差在处理器列表:`progG γ` 把 γ 中现存子 fiber 的组件加了进去。
- 生命周期规则不读处理器列表,所以两张表的生命周期步相同 (`step_G`)。
- 良基性由基组件上的秩给出 (`above_G`)。

结论:扩展意义下静止的状态,按核心的意义是稳定的 (`settled`);而且每个 Active 的 fiber 的在场集都是当前的 (`fresh`)。扩展可达状态满足所需的不变式 (`XInv`:`WF`、`Prov`、pid 唯一、`XSpawnProv`,见 `xinv_reachable`)。

### 1.5 合流

对应核心第 3 层的前两部分 (`Confluence.control_confluence`、`StateConf.state_confluence`,组件不 spawn)。在核心的条件 (程序有界、秩有界、完整提供、服务的合流假设、终态无失败) 之外,对基组件再要求:

- 每个变体 `xbody c T` 都有界、不 spawn,并且完整提供 c 可能提供的每个键 (`xHK`、`xNoSpawn`、`xTotal`);
- 秩沿可选依赖边也递增 (`XAbove`)。

服务假设 (`HRI`、`HCom` 等) 对表 `prog'` 的 `CoPair` 陈述,即对两个可能相遇的组件的任意变体中的操作陈述。

**控制状态** (`Ext/OptConfluence.v`,`xcontrol_confluence`)。从同一个满足核心不变式 `CInv` 的状态出发,两次只含扩展生命周期步 (`XLRun`)、终于静止且没有失败的执行,得到:

- 相同的 fiber 集合、相同的基组件;
- 相同的 Active 集合,每个键由同一个 fiber 提供;
- 每个组件的当前在场集相同 (`present γ1 c = present γ2 c`),所以对应的 Active fiber 的组件 (c, S) 完全相同,即运行的是同一个变体。

证明:

1. **不变式。** `CInv` 与"fiber 集合和基组件不变"(`XStatic`) 沿扩展执行保持。核心步用核心的 `cinv_step`、`lstep_static`;`O-Restart` 只改生命期;换组件只改 Inactive fiber 的 S (`cinv_recomp`)。
2. **不动点方程。** 静止时,一个 fiber 是 Active,当且仅当它的**必需**依赖都由 Active 的 fiber 提供 (`xactive_iff`)。
   - 一个方向取自核心的 `active_iff`。
   - 另一个方向:否则这个 fiber 是 `Inactive None`,而换上当前在场集后它的目标可解析,`X-Begin` 可走,与静止矛盾。
   - 这个方程只涉及基组件,不涉及 Inactive fiber 可能过时的 S。沿秩它只有一个解 (`xfix_unique`)。
3. **在场集。** 静止时,一个键可见当且仅当它由 Active 的 fiber 提供 (`visible_iff`)。提供者与 Active 集合都相同,所以在场集相同。再由 `xquiet_settled`,Active fiber 的 S 就是当前在场集。

**服务状态** (`Ext/OptState.v`,`xstate_confluence`)。在上述条件下,两次执行的终态中同一个键上的绑定,服务状态 ≃。复用核心的第 2 层,改动两处:

- **不变式 `PInv`。** 对 Inactive fiber 换组件 (只要基组件不变) 保持 `PInv` (`RF`、`rf_pinv`),因为 Inactive fiber 不持有撤销项,也没有轨迹。`O-Restart` 与核心步由核心的 `pinv_step` 保持。
- **规范化终态 (`norm`)。** 终态中 Inactive fiber 的 S 可能过时,两个终态的组件在那里未必相等,所以先把每个 Inactive fiber 的 S 换成终态的在场集。
  - 规范化保持 `PInv`、绑定和稳定性 (`final_norm`)。
  - 由控制状态的结论,两个规范化终态的组件处处相等。
  - 然后套用核心的终态比较 (`final_evs`、`final_blocks`、`replay_tokens`);这部分抽成与执行无关的 `final_states_agree`。

`xstate_confluence` 不依赖任何公理 (`Print Assumptions`:Closed under the global context)。

**含 spawn** (`Ext/OptSpawn.v`,`xspawn_confluence`)。对应核心的 `SpawnConf.spawn_confluence`:从同一个满足 `PInv`、`SLInv` 的状态出发,两次扩展生命周期执行终于静止且没有失败时,在重命名意义下一致 (核心的 `Agree`)。
- 规范名给每个 fiber 恰好一个名字。
- 同名的 fiber 组件相同 (Active 的 fiber 连在场集也相同)、活跃性相同。
- 对应的 fiber 提供每个键。
- 每个键上的服务状态 ≃。

比较的是两个**规范化**的终态 `norm γ1`、`norm γ2`:Inactive fiber 过时的在场集换成终态的在场集,其余一概不变 (绑定、父指针、生命期、基组件)。

**限制:子组件没有可选依赖** (`NoOptChild`)。可能被 spawn 或作为处理器运行的组件不声明可选依赖,只有插入的根组件可以声明。
- 原因:核心的轨迹不变式 (`Episode.Corr`) 按组件的**完整**值检查父 fiber spawn 出的子 fiber,而子 fiber 的组件总是 (c', [])。给子 fiber 重选在场集会破坏它。
- 只影响第 3 层。安全、不死锁、终止、恢复对任意组件成立,不需要这条限制。审计中读可选服务的多是顶层插件,不是被 spawn 的子插件。
- 不能靠换编码绕过。子 fiber 的组件必须记下它的在场集,因为在场集决定它运行哪个变体、依赖哪些键。而 `Corr` 要求这个组件等于父程序里写死的 spawn 目标。两者不可兼得。
- 去掉这条限制的路线 (估计 1500–2500 行,暂不做):
  1. 在 `Ext` 中把 `Corr` 读在按基组件投影的状态上 (每个组件的在场集清空),spawn 检查就只比较基组件。照抄 `Episode` 中保持它的部分 (`ep_keep` … `ep_op` … `pinv_step`),把 `Corr` 的状态参数换成投影状态。
  2. 核心的 `Inv2` (子 fiber 的组件出现在父组件程序的 spawn 中) 同样会被破坏,而核心的 `sinv_step`、`sl_step` 依赖它。改用 `OptProgress.progG` 作为 `SInv` 的表,需要 `Tr`、`Corr` 在两张只差处理器列表的表之间转换的引理。
  3. 终态一层照抄 `StateConf` 的 `final_fiber`、`final_items`、`final_blocks` 与 `SpawnConf` 的 `corr_pair`、`final_agree`。子 fiber 的情形改为和根相同的论证:基组件由 spawn 事件给出,在场集由更低秩上的对应给出 (`present_corr`)。
  4. 在此之上重做 `OptSpawn.v`、`OptDynamic.v`。

  核心仍然不改,新文件都在 `theories/Ext/` 下。

在这个限制下,证明的结构是:

1. **不变式。**
   - 由 `Inv2` 和 `NoOptChild`,子 fiber 的组件总是 (c', []),且 c' 没有可选依赖 (`child_plain`),所以给子 fiber 重选在场集什么也不改变 (`recomp_child`)。
   - 给 Inactive 的根换组件 (`RF2`:被改的只有根) 保持 `PInv` 与 `SLInv` (`rf2_pinv`、`rf2_sl`)。根不出现在任何 spawn 项中,所以 `Corr` 不受影响。
   - 于是 `PInv`、`SLInv` 与"根按基组件保留"(`XRootKeep`) 沿扩展执行保持 (`xlrun_inv`)。核心步用核心的 `pinv_step`、`sl_step`、`rk_step`;`O-Restart` 用 `Dynamic.sl_restart`。
2. **规范化终态。**
   - `norm γ` 满足核心的 `FinalS` (`final_norm2`)。
   - 其中每个 fiber 的在场集都是当前的 (`Fresh`、`fresh_norm`)。
3. **秩归纳。** 重做核心的 `corr_step` (`corr_stepX`),只改根的情形:两个对应的根起初只知道基组件相同 (`RootsMatchX`)。
   - 在场集相同,由更低秩上的对应得到 (`present_corr`):每个可选键的提供者秩更低,在两边对应、同为 Active,所以同为可见。
   - 由 `Fresh`,两个根的完整组件相同。
   - 子 fiber 的情形和 `corr_pair` 原样取自核心。
4. **终态比较。** `final_agreeX` 是核心 `final_agree` 的照抄,只换成 `corresp_allX`。

唯一的公理是函数外延性 (核心的 `Prelude` 已引入)。

**与编排交错** (`Ext/OptDynamic.v`)。对应核心的 `Dynamic.v`,即论文定理 80。

**执行 `XDRun`。** 从初始状态出发,按顺序消耗编排输入,其间任意穿插扩展生命周期步。
- 输入是核心的 `Dynamic.Input`,按插入序号指称根 fiber。
- 编排步是核心的 `step`。
- 生命周期步是 `xstep`。

**定理。**
- `xdynamic_agree`:两次执行的输入留下相同的幸存**基**组件序列 (`xscomps`) 时,规范化后的终态在重命名意义下一致。根以它在幸存者中的位置 (核心的 `slab`) 为标签。
- `xdynamic_confluence`:输入相同时的特例。
- `xstatic_assembly`:任意执行的终态,与"只按原插入顺序各插入一次幸存组件"的执行的终态一致。

**与核心证明的区别。**
- **根台账 (`XLedger`) 按基组件记录。** 给根重选在场集会把它的组件从 (c, S) 改成 (c, S'),c 不变。
- **扩展生命周期步保持台账。** 这只用到这一步的四个性质 (`XFrame`,`xledger_frame`):
  - 计数器不减;
  - 新 fiber 取新名字;
  - 父指针不变;
  - 根按基组件保留 (`XRootKeep`)。

  这四条对核心步由核心的 `step_next`、`new_fiber`、`fiber_step`、`rk_step` 给出;对重选在场集的那一步另证 (`xstep_frame`)。
- **编排步。** 证明照抄核心的 `ledger_orch`,只把组件换成基组件 (`xledger_orch`)。
- **终态比较。** 用 `final_agreeX`。规范化保持台账 (`xledger_rf`)。

唯一的公理是函数外延性。

**剩下的限制:子组件没有可选依赖** (`NoOptChild`),原因见上。

### 1.6 对审计的影响

可选依赖落地后:

- S1 中"读未注入的服务"只要声明为 `xopt`,就成为 ✓;
- C2 中"按服务在不在决定登记什么",只要分支写成 `xbody` 的变体、且依赖出现时重载,就成为 ✓。

审计中卡在 C2 上的 dsh-token-diet (按 `connection`、`sessionPersistence` 是否在场选传输) 即属此类。按 [PLUGIN-AUDIT.md](PLUGIN-AUDIT.md) 的估计,多数这类插件能升一层,但前提是合流的推广 (1.5) 完成。

## 2. 编排者义务 (`Ext/Orchestrator.v`,已形式化)

### 2.1 模型

审计里的编排者 (dshmarket、dsh-mobile-plugin、dsh-free-search、dsh-mnemon、ds-harness-remote、dsh-remote 的自热重载、dsh-ops 客户端) 做三件事:安装和卸载别的插件、自更新、装配一组子插件 (bundle)。

它们装上的插件**不随编排者卸载而消失**:安装写在配置里,下次启动仍在。这与 spawn 不同,spawn 出的子 fiber 是父 fiber 的效应。所以编排者不建模为父 fiber,而是建模为一个**输入源**:

- 它发出 `Dynamic.Input` 的序列 (`IIns c`、`IDis i`、`IRestart i`、`IReset i`),按插入序号指称根 fiber;
- 这些输入交给核心的 `DRun`;
- 它依据的"状态"是外部持久的配置,不是服务。

编排者作为插件,自身的生命周期部分仍是普通组件。

### 2.2 编排者义务

| 义务 | 内容 | 用于 |
|---|---|---|
| O1 只编排根 | 只对自己 (或宿主) 插入的根 fiber 发 `IDis`/`IRestart`/`IReset`,从不 dispose 启动时 spawn 的子 fiber | 合流 (`SLInv`) |
| O2 有限 | 在一次会话中只发出有限多个输入;或者说,最后一个输入之后不再发出 | 活性 |
| O3 结果确定 | 存活的组件 (按多重集) 只由配置决定,不由调度决定 | 合流 |
| O4 不在启动中自我重启 | 自己的启动程序中不发 `IRestart self`/`IDis self`;自更新放在反应或外部进程中 | 活性 |
| O5 走受控原语 | 不改 loader 条目、不用 `internal/*` 钩子、不自我 SIGTERM | 第 0 层 (否则不在模型内) |

### 2.3 哪些定理成立

全部由核心定理导出,不改核心,不依赖任何公理。

| 层 | 状态 | Rocq |
|---|---|---|
| 0 安全 | **保守**,只需 O5 | `orch_wf` |
| 1 活性 | **保守**,需要 O2 | `orch_live` |
| 2 恢复 | **保守**,只需 O5 | `orch_recovery` |
| 3 合流 | **推广**,需要 O1、O3 | `dynamic_agree_perm`、`install_order`、`self_update` |

**第 0–2 层。** 编排执行 (`DRun`:编排输入与生命周期步任意交错) 本身就是演算的一次执行 (`drun_labels`),所以汇总定理的前三层直接适用:
- `orch_wf`:可达状态良构。
- `orch_live`:最后一个输入之后,生命周期步终止,静止即稳定。
- `orch_recovery`:未安装的 fiber 不留痕迹,影子存储由执行给出。

**第 3 层:存活组件相差一个排列。**
- `O3` 读作 `SameOutcome`:两次编排留下的存活组件是同一个多重集,顺序可以不同。
- `dynamic_agree_perm`:两次编排满足 `SameOutcome` 时,终态在重命名意义下一致。
  - 第二次执行的根按排列重新标号:标准库的 `Permutation_nth_error_bis` 给出一个单射 π,有界单射即满射 (`bInjective_bSurjective`)。
  - 其余交给核心的 `SpawnConf.final_agree`。
  - 核心的 `dynamic_agree` 要求存活组件顺序相同,这里去掉了这个要求。
- `install_order`:插件市场按下载完成的任意顺序安装同一组插件,终态一致。
- `self_update`:自更新 (dispose 旧版本、插入新版本,穿插在任意时刻) 的终态与直接安装存活组件一致。这就是核心的 `static_assembly`。

O1 内建在 `Input` 中:输入只能按插入序号指称根。O4、O5 在模型之外:违反它们的插件不是输入源,而是在修改运行时。

## 3. 交集生命期的效应 (`Ext/Intersect.v`、`Ext/IntersectLive.v`,已形式化)

### 3.1 编码

插件 P 给 agent A 的上下文挂一个效应 (例如 `tools.restrict`、`agent.ctx.plugin`),要求 P 与 A 任一方结束时撤销。核心已有的机制可以表达它:

- 效应是 P 的一个**反应子 fiber** (`O-React`)。
- 这个子 fiber 声明依赖 A 的条目键 (例如 `agent A`,用差异 r 的"条目即键"编码)。

两个方向的撤销:

- **P 结束**:P 卸载时先等运行期子 fiber 退出 (`parent_waits_child`)。
- **A 结束**:A 离开 Active,子 fiber 的目标变为 ⊥,子 fiber 卸载。同时核心的卸载守卫 (`held`,同 Cordis 的 `_unload`) 保证:只要子 fiber 还解析 A 的条目,A 就一项也不撤销、也不请子 fiber 退出 (`unload_blocked`)。所以效应总在 agent 上下文的任何部分消失之前撤销,而不只是在条目本身撤回之前。

### 3.2 核心缺的一样:带参数的反应

agent id 是运行时数据,而 `reacts : list C` 是静态列表,不能为每个 agent 列一个组件。

**新标签 `I-React n i e`** (`Intersect.istep`)。组件的处理器是一族 `E → C` (`ireacts`),e 是事件载荷 (如 agent id)。
- `I-React n i e` 就是核心的 `O-React n i`,用的组件表 `progE (Some e)` 把每个处理器族实例化在 e 处。
- 其余标签都是核心步,用不带处理器的表 `progN`。
- 两张表只差在处理器列表,而除 `O-React` 外没有规则读它 (`step_tables`)。

| 层 | 状态 | Rocq |
|---|---|---|
| 0 安全 | **保守**:`WF` 不读处理器列表 | `ipreservation`、`iwf_reachable` |
| 包含 | **保守**:效应的生命期在父 fiber 与它所解析的每个提供者的生命期之内;提供者的 provision 仍被解析时,它的卸载整体停住,一项也不撤销 | `effect_within`、`unload_blocked_i`、`withdraw_blocked_i`、`parent_waits_i` |
| 1 活性 | **推广**:秩沿提供、spawn 与每个处理器实例递增 (`IAbove`)。核心的 `termination`、`quiet_settled` 用于一张按状态选的表 `tbl`:它的处理器列表含当前这一步的实例与现存子 fiber 的组件,因而满足核心的 `Inv2`;基层不变式 `ISpawnProv` (子 fiber 由父程序 spawn,或是父组件某个处理器族的实例) 逐步传下去 | `itermination`、`itermination_reachable`、`iquiet_settled` (`IntersectLive.v`) |
| 2 恢复 | **保守**:独立性对任意两个组件 (含任意处理器实例) 可能在同一键上执行的操作陈述,即核心的 `CoPair progN`,它本来就遍历所有组件。同一处理器族的不同实例两两相遇受控,通常由登记名带 agent id 得到 | `irecovery_exact`、`ieffect_exact` |
| 3 合流 | **不覆盖**:与核心一样,合流不含 `O-React` | — |

`ieffect_exact` 是交集生命期的恢复结论:效应 fiber 出现之前到它不再安装之后 (agent 结束、插件卸载,或被直接 dispose),每个绑定都 ≃ 同一次执行中略去该效应全部操作的结果,不论其他 fiber 同时做了什么。

以上定理都不依赖任何公理。

**agent 的编码** (未单独写成 Rocq 例子,上面的定理对任意组件表成立):
- agent a 的上下文提供键 `entry a`;
- 插件 P 的处理器族是 `fun a => Restrict a`;
- `Restrict a` 依赖 `entry a`。
- 取秩 rank(P) = rank(Agent a) = 0、rank(Restrict a) = 1,`IAbove` 的要求即成立。

**撤销后不复活。** A 结束后子 fiber 停在 Inactive,直到 P 卸载才被移除。若 A 的条目键再次出现 (同一 id 的 agent 重建),子 fiber 会重新加载。对 dsh 的 agent 这不会发生,因为 agent id 不复用。需要"一次性"语义时,P 在"agent 结束"事件的处理器里 `O-Dispose` 这个子 fiber 即可,不加规则。

## 4. 例子与通用结论

### 4.1 例子 (`Ext/Examples.v`)

两个用按名注册表搭的小系统,用计算检查结果,做法同核心的 `Examples/Basic.v`。每个例子还证明了它所在扩展对组件表的义务,说明这些假设能同时满足,定理不是空真。

**可选依赖 (`OptEx`)。** 插件 B 可选依赖 A 提供的 `llm`:
- 有 `llm` 时,B 往自己的注册表登记 7 ↦ 1,并往 `llm` 写一项;
- 没有时,只登记 7 ↦ 0。

两种调度:
- `a_first`:A 先激活,B 一开始就选"有 `llm`"的变体。
- `b_first`:B 先激活,选了"没有 `llm`"的变体。A 随后激活时,B 的核心目标没变 (核心的 `L-Leave` 不适用),但扩展的 `X-Leave` 适用 (`b_must_reload`)。B 卸载、撤销登记、按新的在场集重新加载。

两者终于同一个可观察状态 (`schedules_agree`),此时没有生命周期规则可走。义务:`rank_ok` (秩沿可选边递增)、`bounded`、`total` (每个变体都完整提供)、`no_opt_child`。

**交集生命期 (`AgentEx`)。** 插件对 agent 3 的事件反应,以载荷 3 实例化处理器,挂上一个限制 (在 agent 的注册表里登记一项)。
- agent 结束时:它的卸载被守卫停住 (`agent_held`),限制先离开、撤销登记 (`effect_gone`),agent 才拆除自己 (`agent_gone`)。
- 插件结束时:限制随插件撤销并移除,agent 照常运行,上下文完整 (`plugin_gone`)。

义务:`rank_ok` (秩沿处理器实例递增)、`bounded`。

**可运行的原型** (`programs/cordis3.rkt`)。复制 `cordis.rkt` 的核心部分,加上三项扩展:
- 可选依赖:在场的可选依赖进入视图,已有的"视图不符就卸载"规则因此在在场集变化时重载;程序可以是"在场集到程序"的函数。
- 编排者:不加规则,测试中演示按任意顺序安装、自更新。
- 交集生命期:`react!` 带载荷,运行处理器族的实例。

它与 `cordis.rkt` 互不依赖,核心改动时两边都要改。测试覆盖上面两个例子,以及各种调度顺序下结果一致。博客笔记 dsh1 讲解它。

### 4.2 谁能改变一个值 (`Ext/ExtOrdering.v`)

核心的 `Ordering.decl_step`、`value_moves` (论文定理 70(3) 后半) 对两项改变了步骤关系的扩展照样成立:
- **可选依赖** (`xdecl_step`、`xdecl_reachable`、`xvalue_moves`):一个绑定在保持 pid 的一步中,值要么不变,要么被某个 fiber 的 `L-Step` 或 `L-Undo` 改变,而这个 fiber 的基组件读取或提供这个键 (必需依赖、可选依赖或提供)。重选在场集只动 Inactive 的 fiber,它不持有撤销项,也不改任何绑定。
- **带参数的反应** (`idecl_step`、`idecl_reachable`、`ivalue_moves`):实例化后的组件表声明的键相同。

### 4.3 扩展版汇总定理 (`Ext/ExtSummary.v`)

仿照核心的 `Summary.v`:对每项扩展,把组件表 (或编排者) 要满足的义务打包,给出它们换来的各层保证。服务规格沿用核心的两档:可撤销档 `Revertible G` 与可合流档 `ConfHyps Σ G`,且 `G` 覆盖程序允许的操作对 (`Covers`)。

| 层 | 可选依赖 | 编排者 | 交集生命期 |
|---|---|---|---|
| 0 安全 | 无假设 (`xsum_wf`) | 无假设 (`orch_wf`) | 无假设,另有包含性质 (`isum_wf`) |
| 1 活性 | `XObligations` (`xsum_live`) | `Obligations` (`orch_live`) | `IObligations` (`isum_live`) |
| 2 恢复 | 可撤销档 (`xsum_recovery`) | 可撤销档 (`orch_recovery`) | 可撤销档 (`isum_recovery`) |
| 3 合流 | 可合流档、`XObligations`、`XTotal`、`NoOptChild` (`xsum_confluence`) | 可合流档、`Obligations`、`TotalProv`、`SameOutcome` (`osum_confluence`) | 不覆盖 |

各项义务的含义:
- `XObligations`:每个变体有界;秩有界,并沿提供、spawn、处理器与可选依赖递增。
- `XTotal`:每个变体都完整提供。
- `NoOptChild`:子组件没有可选依赖 (只合流需要)。
- `IObligations`:程序有界;秩有界,并沿提供、spawn 与每个处理器实例递增。
- 编排者的义务就是核心的 `Obligations`、`TotalProv`,外加 O3 (`SameOutcome`:存活组件是同一个多重集)。

每条都是扩展文件中已证定理的推论,这个文件只负责打包假设、检查它们拼得起来。`xsum_confluence` 用到函数外延性 (核心的 `Prelude` 已引入),其余不依赖任何公理。

这张表就是将来插件检查器对准的目标:对一个插件 (或一组插件) 逐项检查表中的义务,就知道它落在哪一层。

## 5. 与论文 v1 的关系

论文 (arXiv:2608.25512v1) §4.4 给出四个扩展:异步、失败、隔离、配置。它们在本仓库的核心中已有对应 (DESIGN.md 3.1 节),都不是本文的三项。重合与互补在下面几处。

| 论文 | 本文 | 关系 |
|---|---|---|
| §5.2.1 Reconciliation:由定理 80,加载器"whatever instantiations and retirements … and in whatever order"都停在从头加载最终配置的状态 | 编排者扩展的 `dynamic_agree_perm`、`install_order` | **补上证明**。核心的 `dynamic_agree` 要求存活组件顺序相同,覆盖不到"任意顺序";`dynamic_agree_perm` 只要求存活组件是同一个多重集 |
| §4.4 Configuration:修订是退役、卸载、移除、重新插入的组合,终点等于从头加载修订后的配置 | `self_update` (即核心的 `static_assembly`) | **一致**。论文在同一名字上重新插入,这里用新名字,按插入序号标号;合流本来就在重命名意义下成立 |
| §5.2.1:组件修改自己的配置或禁用自己时,改动写回它的条目 | 编排者 O4:自更新走持久配置,不在自己的启动程序里自我重启 | **一致**。论文没有讨论插件本身充当编排者 (插件市场、bundle) 时的义务,O1–O3 是本文按审计加的 |
| §4.4 Configuration:"one such component bound to two payloads is two components" | 交集生命期:处理器族的实例 `h e` 各是一个组件 | **同一想法,用在别处**。论文把载荷绑定在插入时 (配置),这里绑定在反应时 (事件载荷)。论文没有 `O-React`,交集生命期是新的 |
| §4.4 Configuration、定理 70:L-Unload 的守卫让撤回排在它引起的停用之后 | 核心的 `held`,交集生命期的 `unload_blocked_i` | **依赖它**。效应在 agent 上下文的任何部分拆除之前撤销,正是因为整个卸载被守卫停住 |
| §5.1.4 Algorithm 6:经代理读未声明的键抛 `UNDECLARED_ACCESS`,而 `ctx.get` "never fails" | 可选依赖 | **论文未覆盖**。审计中的 S1/C2 写法正是绕道 `ctx.get`;可选依赖给它一个有保证的形式 |
| §5.2.1:组件只在部分配置下装上它声明的键时,加载结果"answers to those configurations as well" | 可选依赖要求每个变体都完整提供 (`xTotal`) | **相关**。在场集相当于一种由环境决定的配置,完整提供要对每一种成立 |

## 6. 路线

| 阶段 | 内容 | 状态 |
|---|---|---|
| E1a | 可选依赖:规则,与核心的对应,保守性,安全,不死锁 | 已完成 (`Ext/Optional.v`、`Ext/OptProgress.v`) |
| E1b | 可选依赖:终止、恢复 | 已完成 (`Ext/OptTermination.v`、`Ext/OptRecovery.v`) |
| E1c | 可选依赖:合流,不含 spawn:控制状态与服务状态 (1.5) | 已完成 (`Ext/OptConfluence.v`、`Ext/OptState.v`) |
| E1d | 可选依赖:合流,含 spawn (子组件无可选依赖) | 已完成 (`Ext/OptSpawn.v`) |
| E1e | 可选依赖:合流,与编排交错 (子组件无可选依赖) | 已完成 (`Ext/OptDynamic.v`) |
| E1f | 可选依赖:去掉子组件的限制 (路线见 1.5 "限制") | 暂不做 |
| E2 | 编排者义务与四层打包;置换版 `dynamic_agree` | 已完成 (`Ext/Orchestrator.v`) |
| E3 | 带参数的反应与交集生命期 | 已完成 (`Ext/Intersect.v`、`Ext/IntersectLive.v`) |
| E3′ | 例子 (`Ext/Examples.v`);`Decl`/`value_moves` 在扩展执行上 (`Ext/ExtOrdering.v`) | 已完成 |
| E4 | 扩展版汇总定理 (`Ext/ExtSummary.v`):在核心汇总定理之上加入三项扩展的义务 | 已完成 |
| E5 | 按扩展给 26 个插件重新分层 ([PLUGIN-AUDIT.md](PLUGIN-AUDIT.md) "按已形式化的扩展重新分层") | 已完成 |
