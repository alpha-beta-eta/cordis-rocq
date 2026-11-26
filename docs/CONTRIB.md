# 贡献键：让登记按构造合流 (设计草案)

2026-11-26。状态：E6a–E6d 已形式化 (`theories/Services/Contrib.v`、`ContribConf.v`、`ContribOrder.v`，`theories/Ext/Hygiene.v`)；E6e、E6f 是实验，尚未做。

## 0. 动机

checker 与真实宿主上的结果 ([../checker/REPORT.md](../checker/REPORT.md)) 说明，插件之间、以及插件新旧实例之间的冲突，几乎都发生在**键里面的登记表**上，而不是键本身：

- **新旧实例相遇。** A 类与 A′ 类共 15 个见证 (A 类 13 个、A′ 类 2 个)，都是中途失败或卸载之后还留着登记；其中 14 个是路由，再装时旧实例的路由挡住新实例。演算里每个操作都经 L-Step 压入撤销项，这种情况不会发生；它发生在真实宿主上，是因为 `webServer.register` 返回裸 disposer，登记从演算所假定的 owned 形式退化成了一次 `set!`。
- **不同插件相遇。** 25 个插件合起来登记了 224 条路由、82 个工具、127 条 fetch 路由，没有一处跨插件重名。名字不撞靠的是命名约定，宿主不检查。真正的跨插件相遇只有两处：服务名 `dshRemote`，以及 3 条有多个插件参与的中间件链 (`agent/pre-step` 6 个插件、`system-prompt/assemble` 3 个、`tools/pre-execute` 2 个)。

现有的两个服务模型对这两种相遇的处理都不够：

| 模型 | 做法 | 不足 |
|---|---|---|
| `Services/Registry.v` + `RegistryConf.v` | 状态是 `Name -> option V`；同名的第二次 `Register` 失败 | 撞名时哪一方失败取决于次序。合流定理要求 `NoFailed`，于是对撞名的执行是空真的。`reg_meet` 还排除了对别人登记的名字做 `Lookup` (free-search 的"复用") |
| `Services/Listeners.v` | 状态是回调列表，`≃` 是 `Permutation` | 合流只保证**同一个多重集**。次序被 `≃` 抹掉了，所以分发结果不在模型内 (文件头注释、`EventBus.on_not_commute`)。中间件链的次序恰恰是语义 |

本文提出一类新的服务，**贡献键**：插件不去改一张共享的表，而是声明一份带有自己标记的贡献；表是从当前全部贡献**推导**出来的，推导与贡献的先后无关。目标是让上面两处不足按构造消失，并把 R3 (相遇受控) 从插件的义务变成宿主 API 的性质。

## 1. 思路：卫生与 parameter

这个设计来自两个类比。

**卫生宏：名字带上归属。** 卫生宏给展开引入的名字打上标记，两段代码写同一个 `foo`，绑定的是两个不同的标识符。对应到这里：每份贡献带一个**标记** (tag)，由宿主按调用者的身份填写，插件无法伪造。名字分两种：

- **私有名**：按 `(tag, name)` 区分，不同标记之间永不冲突。插件内部用的路由、工具 id 属于这一种。
- **公开名**：对外可见的路径、给 LLM 看的工具名、服务名。它们是全局命名空间，卫生帮不上忙，只能**把冲突变成一个确定的值**，而不是让先到者赢。

**parameter：绑定的寿命等于作用域。** `parameterize` 的绑定在离开动态范围时自动恢复，非局部退出也一样。Cordis 的 ctx 在**键**这一层已经是这样：`ctx.provide`、`ctx.isolate` 相当于 `parameterize`，fiber 卸载时绑定自然消失。缺的是**键里面**：`webServer.register` 是对共享表的 `set!`，它的撤销要另外记账。贡献键把它改成绑定：贡献随 fiber 存亡，表是存活贡献的函数，而不是登记历史的函数。

与定理的联系：汇总定理第 3 层说干净终态"等于静态组装"。贡献键相当于把静态组装直接当成实现：对这类键，状态只取决于存活的贡献构成的多重集。`Bridge.v` 把键上的值叫作余效应上下文 (Definition 19)；在这个意义上，贡献键把"登记"从效应改写成了对余效应上下文的贡献，读取则是对推导结果的余效应。

## 2. 服务模型

贡献键是一个普通的 `Service`，演算本身不变。参数：

- `Tag`：贡献者的标记，可判定相等；在宿主里对应 loader 条目 id，在演算里对应组件 `c`；
- `Name`：名字，带一个 `public : Name -> bool`；
- `V`：贡献的值 (路由的处理器、工具定义……)，带优先级 `prio : V -> nat`；
- `≤ₑ`：条目上一个可判定的全序，用来给中间件定次序。

**状态与操作。**

```
Entry := Tag × Name × V
St    := list Entry,        s ≃ s'  :=  Permutation s s'
Op    := Contribute (e : Entry)  |  Read (q : Tag) (x : Name)
run (Contribute e) _ s := Some (e :: s, remove_first e, None)            -- 从不失败
run (Read q x)     _ s := Some (s, id, Some (resolve s q x))
```

`Contribute` 从不失败，这是与 `Registry` 最大的不同：撞名不再让某个 fiber 失败，而是体现在推导结果里。逆是"删掉一个等于 `e` 的条目"，与 `Listeners.v` 的 `remove_first` 相同，在 `Permutation` 下是精确的逆。

**推导：表。** `Read q x` 是标记 `q` 读名字 `x`，结果是

```
Res := RAbsent | ROne (t : Tag) (v : V) | RConflict
```

先取 `q` 看得见的贡献：私有名只看标记为 `q` 的贡献，公开名看全部贡献。再取其中优先级最高的、去重后的条目：没有就是 `RAbsent`，恰好一个就是 `ROne`，否则是 `RConflict`。这里的规则可以换，唯一的要求是 **对置换不变**：`Permutation s s' -> resolve s q x = resolve s' q x`。

`RConflict` 本身不列出冲突各方；各方由 E6c 的 `parties` 给出：最高优先级的贡献按全序排好，对置换不变。

**推导：链。** 中间件按 `≤ₑ` 排序后组成链：`chain s := sort (≤ₑ) s`。只要 `≤ₑ` 是全序，排序结果只取决于多重集：`Permutation s s' -> chain s = chain s'`。宿主可以按 (优先级, 标记, 值的键) 排序；插件需要排在别人前面时，显式提高优先级，而不是靠"先装"。

前缀路由也落在这里：分派时按最长前缀匹配，是解析结果上的一个确定函数。两个插件的前缀互相覆盖时，结果仍是确定的。

## 3. 与核心的接口

**不改演算。** 贡献键是 `Service` 的一个实例，与 `Registry`、`Listeners` 并列，放在 `theories/Services/`。多个服务的组合沿用 `Compose.v`。

**标记由宿主填。** 程序里写的是不带标记的 `Contribute (x, v)`；组件表在构造时把它改写成 `Contribute (c, x, v)`，就像 `Ext/Optional.v` 的 `lift` 改写子组件那样。这一层放在 `theories/Ext/Hygiene.v`，只 import 核心与 `Services/Contrib.v`、`ContribConf.v`，核心不 import 它。用组件 `c` 而不是 pid 做标记，是因为合流在重命名意义下陈述：两次调度给同一个组件的 pid 不同，但 `c` 相同。

**插件剩下的义务：启动期不读别人的贡献。** `Read` 与别的 fiber 的 `Contribute` 不可交换：读到的表取决于对方是否已经贡献。这与审计里的 C5 (启动期不读有序分发的结果) 同源，也是 free-search"复用"别人路由的形状。所以相遇关系取

```
contrib_meet a b  :=  ¬ (a = Read ∧ b 是 Contribute)  ∧  ¬ (b = Read ∧ a 是 Contribute)
```

启动程序在贡献键上只做 `Contribute`，`Covers contrib_meet` 就自动成立，不需要逐对检查名字。运行期的分派 (处理请求、调用中间件) 发生在反应或宿主里，不在启动程序中。

## 4. 要证的命题

`Services/Contrib.v` (E6a，已完成，不依赖任何公理)：

| 命题 | 内容 |
|---|---|
| `resolve_perm` | `Permutation s s' -> resolve s q x = resolve s' q x` |
| `contrib_well_behaved` | 每个操作良态：逆在应用处撤销它，尊重 `≃`。`Read` 尊重 `≃` 正是由 `resolve_perm` 得到 |
| `contrib_inverse_uniform`、`contrib_token_irrelevant` | `UniformInv`、`TokIrr` |
| `contribute_total` | `Contribute` 从不失败 |
| `contribute_commute`、`read_commute` | 两个 `Contribute` 可交换；两个 `Read` 可交换 |
| `contribute_read_not_commute` | 对 `q` 看得见的名字，`Contribute` 与 `Read` 不可交换。这说明 E6b 的相遇关系必须排除这一对 |
| `resolve_private_local`、`private_isolated` | 私有名的解析只取决于本标记的贡献：别的标记的贡献怎么变都不影响它 (原列在 `Ext/Hygiene.v` 下，它是服务本身的性质，挪到这里) |

`Services/ContribConf.v` (E6b，已完成，不依赖任何公理)：

| 命题 | 内容 |
|---|---|
| `contrib_hyps` | `ConfHyps Contrib contrib_meet`：合流层的服务假设全部成立。`contrib_meet` 允许任意两次贡献、任意两次读取，只排除贡献与读取相遇 |
| `covers_no_read` | 组件的启动程序在贡献键上从不 `Read`，`Covers contrib_meet` 就成立，不论贡献什么名字 |
| `contrib_confluence` | 汇总定理的合流层读到 `resolve` 上：两次编排执行静止且无失败时，两边都绑定的键上，每个名字解析结果相同 |
| `contrib_static` | 同上，与静态组装比较 |
| `contrib_revertible` | 恢复层的服务假设对 `contrib_rev` 成立：`contrib_meet` 再要求两次贡献的条目不同 |
| `covers_rev_no_read` | 不读，且没有两个 fiber 会贡献同一个条目时，`Covers contrib_rev` 成立 |
| `contrib_recovery` | 汇总定理的恢复层读到 `resolve` 上：fiber 卸载后，每个名字的解析结果与略去它全部操作的影子执行相同 |

原计划的 `contrib_no_fail` 不单独陈述：`contribute_total` (E6a) 已经说明 `Contribute` 从不失败，撞名因此不会让 fiber 失败，合流定理的 `NoFailed` 前提不会因撞名而落空。

**恢复层为什么要求条目不同。** 汇总定理的恢复层要求逆在**任意**状态上都与对方的操作独立 (`RevertIndep`)，而不只是在操作发生之后的状态上 (合流层的 `RevAfter`)。从一个不含 `e` 的状态里删一个 `e` 什么也不做，再补上一个 `e` 就多出来了，所以两次相同的贡献在这样的状态上不独立。这些状态在真实执行中到不了，但定理的陈述覆盖它们。E6d 的标记让不同组件的条目天然不同；剩下的情形是同一个组件的两个副本 (不提供键、可以有多个 fiber 的组件) 贡献同一条目，需要单独排除，或者把恢复定理的前提也弱化到"操作发生之后"。后者是对核心的改进，留作未决问题。

`Services/ContribOrder.v` (E6c，已完成，不依赖任何公理)：

| 命题 | 内容 |
|---|---|
| `sort_unique`、`isort_perm_eq` | 按全序排好的两个列表互为置换时相等；所以插入排序的结果只取决于多重集。Stdlib 没有这条唯一性，在这里证了 |
| `prio_order` | "优先级高者在前，同优先级按任意全序决胜"本身是全序。宿主按这个规则排序即可满足前提 |
| `chain_perm` | 名字 `x` 下的链 (该名字的全部贡献，排好序) 只取决于多重集 |
| `parties_perm`、`parties_in` | 冲突各方 (最高优先级的贡献，排好序) 只取决于多重集，且都是 `q` 看得见的存活贡献。这补上了 E6a 里 `RConflict` 不列出各方的缺口 |
| `chain_confluence`、`chain_static` | 汇总定理读到链与冲突各方上：两次调度、以及静态组装，在每个名字下得到同一条链、同一组冲突方。这是 `Listeners.v` 给不出的结论 |

链只决定谁先运行，不让两个互不交换的处理器变得一致；它让结果只取决于贡献的集合，这正是合流所要求的。

`Ext/Hygiene.v` (E6d，已完成，不依赖任何公理)。组件表 `hprog` 把组件 `c` 启动程序里的每个贡献改成带标记 `c`，每次读取改成以 `c` 的身份读 (`retag`)；依赖、提供、子组件、处理器都不变。

| 命题 | 内容 |
|---|---|
| `opat_retag`、`hprog_tagged` | 改写后组件 `c` 的每个操作都带标记 `c`，且来自原程序的某个操作 |
| `hyg_hyps` | 合流层的服务假设对 `hyg_meet` 成立。它比 E6b 的 `contrib_meet` 宽：允许读取与**别的标记**下的贡献相遇，只要读的是私有名 |
| `hyg_revertible` | 恢复层的服务假设对 `hyg_rev` 成立 (`hyg_meet` 再要求两次贡献的条目不同) |
| `hyg_covers` | 只看程序形状就能得到覆盖条件：启动期只读私有名 (`ReadsOwn`)，且读取的组件提供某个键、因而同一时刻只有一个 fiber |
| `hyg_covers_rev` | 再加上贡献的组件同一时刻只有一个 fiber (`ContribSingle`)，恢复层的覆盖条件也成立：不同组件的条目标记不同，自然不同 |
| `hyg_confluence`、`hyg_static`、`hyg_recovery` | 汇总定理对改写后的组件表读到 `resolve` 上 |

这一层解决了原来的未决问题 1：组件在启动期读自己的私有名是允许的，它与别的组件的贡献可交换 (`read_other_cons`)。代价是读取的组件要单实例：同一个组件的两个 fiber 标记相同，彼此的贡献会出现在对方的私有名里。

原计划的 `public_conflict_det` 由 E6c 的 `parties_perm` 覆盖：冲突各方 (带标记，也就是组件) 由多重集决定。原计划的 `hyg_summary` 即上表最后一行。

## 5. 宿主侧的对应

模型对宿主提出三条要求，可以拿去对照 dsh 的实现，也可以由 checker 检查：

- **H1 owned。** 贡献经调用者的 fiber 登记：调用 `ctx.effect`，或者用生成器效应逐条 `yield`。这一条让演算里"每个操作都压入撤销项"在宿主上成立，A 类与 A′ 类因此消失。
- **H2 推导。** 宿主的表是存活贡献的函数：撞名不抛错，而是记成冲突；查询结果与登记次序无关。
- **H3 标记不可伪造。** 标记由宿主按调用者所属的 loader 条目填写，插件传不进来。

对 dsh 的 API，草拟如下 (保持 `register` 的签名，便于迁移)：

```js
// 私有路由：挂在 /plugins/<entry-id>/ 下，不与任何别的插件冲突
ctx.webServer.register({ path: 'state', handler })

// 公开路由：显式声明；撞名时双方都不生效，宿主在诊断中报告冲突
ctx.webServer.register({ path: '/token-diet', public: true, handler })

// 中间件：按 (priority, entry-id) 排序，与装载次序无关
ctx.on('tools/pre-execute', handler, { priority: 10 })
```

返回值仍是 disposer，用于提前撤销；不调用它也不会泄漏。冲突策略有两种都满足置换不变：默认"都不生效并报告"，或者"唯一最高优先级者生效" (类似 Nix 模块系统的 `mkOverride`)。不能用的是现在的"先到者生效"。

## 6. 覆盖与不覆盖

按报告的类别：

| 报告里的问题 | 贡献键 | 说明 |
|---|---|---|
| A 类、A′ 类：泄漏与"装不回去" | **消除** (经 H1) | 这是宿主一致性，不是新定理：演算本来就假定 owned |
| free-search 让出路由 | **消除** | 撞名成为 `Conflict`，不再"复用"别人的登记；启动期读别人的贡献被 `contrib_meet` 排除 |
| 跨插件撞名 (路由、工具名、提示段) | **按构造合流** | 私有名不冲突；公开名冲突与次序无关，且不让 fiber 失败 |
| 中间件链次序 | **确定** | 次序是贡献集合的函数。两个中间件语义上不可交换时，谁在前仍要有人决定，但决定写在优先级里，不取决于调度 |
| dsh-ops 的提示段序号 | 不覆盖 | 序号表是插件自己的状态，问题在插件内部先做效应、后登记逆 |
| `dshRemote` 冲突 | 不覆盖 | 这是**键**层面的冲突 (`PProvide`)。把同样的想法用到提供者选择上 (候选提供者都挂着，按优先级确定一个) 需要改演算，留作后续 |
| C2：读一次服务、复用 ctx | 不覆盖 | 由可选依赖 (`Ext/Optional.v`) 处理 |
| B 类：进程级状态 | 不覆盖 | 不在任何键上 |
| 外部资源 (端口、子进程、文件、计时器) | 不覆盖 | 它们无法推导，只能做了再撤，仍然需要 `ctx.effect` |

## 7. 验证计划

| 阶段 | 内容 |
|---|---|
| E6a | `Services/Contrib.v`：服务定义、良态、`resolve_perm`、私有名隔离。**已完成** |
| E6b | `Services/ContribConf.v`：`contrib_hyps`、`contrib_revertible`、合流与恢复的推论。**已完成** |
| E6c | `Services/ContribOrder.v`：`chain_perm`、冲突各方、中间件链的合流。**已完成** |
| E6d | `Ext/Hygiene.v`：标记改写、读自己的私有名、覆盖条件、汇总。**已完成** |
| E6e | checker 实验：宿主桩加一个"贡献模式" (`webServer`、`settings.configure` 改为 owned；撞名记为冲突值；中间件按优先级排序)，插件代码不动，重跑全部场景 |
| E6f | 真实宿主：在 dsh 的 `webServer` 上实现 H1–H3，重跑 `real/scenarios/` 下的 A 类与 free-search 场景 |

E6e 的预期 (都是待检验的假设)：

- A 类中 12 个留下路由的故障注入见证和 2 个 A′ 见证消失。故障点不限于 `webServer`：windows-mcp 在 `tools.register` 抛错时同样留下路由，因为它从不保存路由的 disposer；
- dsh-ops 的见证保留 (它的问题在插件内部)；
- `pair-ds-harness-remote-dsh-remote` 保留 (键层面)；
- 不应出现新见证。出现的话，多半是插件依赖了"先到者生效"或撞名时抛错，这本身就是要报告的结果。

## 8. 未决问题

1. ~~**启动期合法地读自己的贡献。**~~ 已由 E6d 解决：标记之后，读自己的私有名与别的组件的贡献可交换 (`hyg_meet`)，前提是读取的组件同一时刻只有一个 fiber。
2. **公开名的冲突策略。** "都不生效"最安全，但会让两个本来能各自工作的插件同时失效；"唯一最高优先级"需要宿主或用户给出优先级。这是产品决定，模型两种都支持。
3. **`chain_perm` 要求全序。** 两个条目在 (优先级, 标记, 值的键) 上完全相同时，它们是同一个组件的两次相同贡献，排序结果仍唯一。但"值的键"在宿主里要能比较，处理器函数本身不可比较，需要用登记时给的名字。
4. **与 `Registry` 的关系。** `Registry` 的"先到者生效"不是置换不变的，所以 `Registry` 不是贡献键的特例。两者会长期并存：现有的 owned 登记 (`tools.register`) 满足 `Registry` 的前提即可，贡献键给想要"按构造合流"的宿主一个更强的选项。
5. **键层面的推广。** 若把 `PProvide` 的冲突也改成"候选都挂着，按优先级确定一个"，`dshRemote` 一类问题也能按构造合流。这需要改演算的绑定规则，与本文分开做。
6. **恢复层的前提能否弱化到"操作发生之后"。** 合流层用的 `RevAfter` 只在操作已经发生的状态上要求独立；恢复层的 `RevertIndep` 要求在任意状态上独立，于是贡献键要排除两个 fiber 贡献同一条目 (见 E6b)。若核心的恢复定理只需要 `RevAfter` 那样的前提，这个限制就可以去掉，`Listeners` 也能得到恢复层的推论。这是对核心的改动，影响面需要单独评估。
