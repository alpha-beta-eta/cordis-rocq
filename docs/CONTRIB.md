# 贡献键：让登记按构造合流 (设计草案)

2026-11-26。状态：E6a 已形式化 (`theories/Services/Contrib.v`)，其余阶段为草案。

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

`RConflict` 暂不列出冲突各方的标记：要让这个列表对置换不变，得先给标记一个全序并排序，与下面的链共用 E6c 的排序引理。在那之前，冲突各方可以逐个查询。

**推导：链。** 中间件按 `≤ₑ` 排序后组成链：`chain s := sort (≤ₑ) s`。只要 `≤ₑ` 是全序，排序结果只取决于多重集：`Permutation s s' -> chain s = chain s'`。宿主可以按 (优先级, 标记, 值的键) 排序；插件需要排在别人前面时，显式提高优先级，而不是靠"先装"。

前缀路由也落在这里：分派时按最长前缀匹配，是解析结果上的一个确定函数。两个插件的前缀互相覆盖时，结果仍是确定的。

## 3. 与核心的接口

**不改演算。** 贡献键是 `Service` 的一个实例，与 `Registry`、`Listeners` 并列，放在 `theories/Services/`。多个服务的组合沿用 `Compose.v`。

**标记由宿主填。** 程序里写的是不带标记的 `Contribute (x, v)`；组件表在构造时把它改写成 `Contribute (c, x, v)`，就像 `Ext/Optional.v` 的 `lift` 改写子组件那样。这一层放在 `theories/Ext/Hygiene.v`，只 import 核心与 `Services/Contrib.v`，核心不 import 它。用组件 `c` 而不是 pid 做标记，是因为合流在重命名意义下陈述：两次调度给同一个组件的 pid 不同，但 `c` 相同。

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

`Services/ContribConf.v`：

| 命题 | 内容 |
|---|---|
| `contrib_hyps` | `ConfHyps Contrib contrib_meet` |
| `contrib_no_fail` | `Contribute` 从不失败，所以撞名不产生失败的 fiber，合流定理的 `NoFailed` 前提不因撞名而落空 |
| `contrib_confluence` | 两次调度静止且无失败时，每个贡献键上的 `resolve` 逐名字相等。由 `listeners_confluence` 的同一路线加 `resolve_perm` 得到 |
| `contrib_recovery` | 卸载后的 `resolve` 等于略去该 fiber 全部贡献的影子的 `resolve`。由核心的恢复定理加 `resolve_perm` 得到 |

`Services/ContribOrder.v`：

| 命题 | 内容 | 预期难度 |
|---|---|---|
| `chain_perm` | `Permutation s s' -> chain s = chain s'` | 中。需要"同一多重集的两个按全序排好的列表相等"；Stdlib 的 `Sorted` 与 `Permutation` 有零件，唯一性可能要自己证 |
| `chain_confluence` | 两次调度后中间件链逐项相等，所以任何按链组合的分发结果相同 | 由前两项得到。这是 `Listeners.v` 给不出的结论 |

`Ext/Hygiene.v`：

| 命题 | 内容 |
|---|---|
| `hyg_covers` | 启动程序在贡献键上只做 (改写后的) `Contribute` 时，`Covers contrib_meet` 成立 |
| `public_conflict_det` | 公开名的 `Conflict ts` 中，`ts` 恰好是贡献了这个名字的组件集合 (按需加上优先级)，与次序无关 |
| `hyg_summary` | 把以上并入汇总定理的形状：第 2、3 层对贡献键不再需要 R3 |

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
| E6b | `Services/ContribConf.v`：`contrib_hyps`、`contrib_no_fail`、合流与恢复的推论 |
| E6c | `Services/ContribOrder.v`：`chain_perm` 与中间件链的合流 |
| E6d | `Ext/Hygiene.v`：标记改写、`hyg_covers`、私有名隔离、汇总 |
| E6e | checker 实验：宿主桩加一个"贡献模式" (`webServer`、`settings.configure` 改为 owned；撞名记为冲突值；中间件按优先级排序)，插件代码不动，重跑全部场景 |
| E6f | 真实宿主：在 dsh 的 `webServer` 上实现 H1–H3，重跑 `real/scenarios/` 下的 A 类与 free-search 场景 |

E6e 的预期 (都是待检验的假设)：

- A 类中 12 个留下路由的故障注入见证和 2 个 A′ 见证消失。故障点不限于 `webServer`：windows-mcp 在 `tools.register` 抛错时同样留下路由，因为它从不保存路由的 disposer；
- dsh-ops 的见证保留 (它的问题在插件内部)；
- `pair-ds-harness-remote-dsh-remote` 保留 (键层面)；
- 不应出现新见证。出现的话，多半是插件依赖了"先到者生效"或撞名时抛错，这本身就是要报告的结果。

## 8. 未决问题

1. **启动期合法地读自己的贡献。** 插件读自己贡献过的名字是无害的 (同一 fiber 的操作不互相比较)，但 `contrib_meet` 按操作而不是按标记划分，会把"读自己"和"读别人"一起排除。可以把 `Read` 细化为 `ReadOwn` 与 `ReadAll`，只排除后者。
2. **公开名的冲突策略。** "都不生效"最安全，但会让两个本来能各自工作的插件同时失效；"唯一最高优先级"需要宿主或用户给出优先级。这是产品决定，模型两种都支持。
3. **`chain_perm` 要求全序。** 两个条目在 (优先级, 标记, 值的键) 上完全相同时，它们是同一个组件的两次相同贡献，排序结果仍唯一。但"值的键"在宿主里要能比较，处理器函数本身不可比较，需要用登记时给的名字。
4. **与 `Registry` 的关系。** `Registry` 的"先到者生效"不是置换不变的，所以 `Registry` 不是贡献键的特例。两者会长期并存：现有的 owned 登记 (`tools.register`) 满足 `Registry` 的前提即可，贡献键给想要"按构造合流"的宿主一个更强的选项。
5. **键层面的推广。** 若把 `PProvide` 的冲突也改成"候选都挂着，按优先级确定一个"，`dshRemote` 一类问题也能按构造合流。这需要改演算的绑定规则，与本文分开做。
