# 演算规则草案(v1)

本文是 [DESIGN.md](DESIGN.md) 的 R0 产物:给出 v1 演算的语法、状态、派生概念和全部规则,
以及要证明的性质。记号尽量贴近将来的 Rocq 定义。

## 0. 参数

| 参数 | 含义 |
|---|---|
| `K` | 服务名(键),相等可判定 |
| `Ξ` | 错误 |
| `C` | 组件编号,配合程序表 `prog : C → Component` |
| 对每个 `k : K` 的服务规格 `Spec k` | 状态类型 `Sₖ`(带 setoid `≃ₖ`)、操作集合 `Opₖ`,以及操作的语义 `run_op`(见下) |

操作语义:

```
run : Opₖ → Tok → Sₖ → option (Sₖ × (Sₖ → Sₖ) × Outₖ)
```

参数直接放进 `Opₖ`,结果类型 `Outₖ` 由各服务自定。`Tok` 是运行时交给这次操作的新鲜令牌,
用于事件钩子这类生成出来的身份(JS 中由对象身份充当)。
一次操作要么失败(`None`),要么给出新状态、逆和结果。
已在 Rocq 中定义,见 `theories/Service.v`。`get` 是逆为恒等、不改状态、结果为观察值的操作;
Cordis 的 `ctx.set`、`ctx.on`、`tools.register` 等都是某个服务上的操作。
服务规格层(R1)对每个操作要求:带见证(逆在应用处撤销它)、尊重 `≃ₖ`;
以及哪些操作两两可交换。

**所有跨组件共享的可变状态都是某个服务的状态。** v1 不设"环境部分" `Amb`:
不经过服务的共享状态在保证范围之外(DESIGN 差异 m)。

**R2 的实现选择:** Rocq 中 v1 全系统只用**一个统一的服务 Σ**,而不是给每个键一个服务
(第 8 节第 1 条的决定)。需要多种服务时,预先把它们组合成一个服务。这样避开了
依赖类型的映射。演算实现在 `theories/Calculus.v`,例子在 `theories/Examples/Basic.v`。
错误类型 Ξ 取为 `EUser | EOp | EUnresolved | EConflict`。

## 1. 组件与程序

```
Component := { d : finset K        (* 依赖 *)
             ; p : finset K        (* 可能提供的服务 *)
             ; body : Prog
             ; reacts : list C }  (* 事件处理器 *)

Prog := Done
      | Fail (ξ : Ξ)
      | Op (k : K) (a : Opₖ) (x : Arg) (κ : Out → Prog)
      | Provide (k : K) (s : Sₖ) (P : Prog)
      | Spawn (c : C) (P : Prog)
```

- `Prog` 是归纳类型,所以每个程序都有限。程序看不到状态,只能通过操作的结果 `Out`
  决定下一步(论文 Def 30 的形式),因此限定性(论文 Def 55)由构造保证。
- `Op k`:对服务 `k` 执行操作。`k` 必须是已声明的依赖或自己提供的服务。
- `Provide k s`:以初始状态 `s` 提供服务 `k`,对应 `ctx.provide`。
- `Spawn c`:注册子组件,对应 `ctx.plugin`。
- `reacts`:组件 Active 期间的事件处理器。每次反应是一个子组件,见 `O-React`。

**组件义务(静态,可机械检查)**:`body` 中每个 `Op k` 满足 `k ∈ d ∪ p`;
每个 `Provide k` 满足 `k ∈ p`。

## 2. 状态

```
State := { next : nat                          (* 新鲜名字与 provision 编号的计数器 *)
         ; F    : N ⇀ Fiber                    (* 注册表,N = nat *)
         ; B    : K ⇀ Binding }                (* 当前的服务绑定 *)

Fiber   := ⟨ c : C ; π : N + root ; τ : bool ; θ : Θ ⟩
Binding := ⟨ pid : nat ; owner : N ; s : Sₖ ⟩

Θ := Inactive (ζ : option Ξ)
   | Loading   (P : Prog) (acc : list Undo) (ω : View)
   | Active    (acc : list Undo) (ω : View)
   | Unloading (acc : list Undo) (ω : View) (ζ : option Ξ)

View := K ⇀ nat                                (* 定义域恰为 d:每个依赖解析到的 pid *)

Undo := UOp   (k : K) (pid : nat) (tok : nat) (g : S → S)   (* 某个服务状态上的逆,及操作所用的令牌 *)
      | UProv (k : K) (pid : nat)              (* 撤销一次 provide *)
      | USpawn (m : N)                         (* 撤销一次 spawn:让子 fiber 卸载并移除 *)
```

- `acc` 的表头是最近的一项,撤销时从表头开始,也就是 LIFO(差异 e)。
- `τ` 是"已请求移除"标记;Cordis 中由 `dispose` 设置。
- 以 pid 作为 provision 的身份(差异 b)。Binding 中的服务状态 `s` 被 provider
  和所有依赖者共同操作。

## 3. 派生概念

```
installed n    := θₙ ∉ { Inactive _ }
visible k      := B k = ⟨pid, o, _⟩ ∧ θₒ = Active _ _      ⇒ Some pid, 否则 None
target n       := ⊥                    若 τₙ
                  ⊥                    若 ∃ k ∈ d(cₙ). visible k = None
                  (k ∈ d ↦ visible k)  否则
quiet          := ∀ n. 下列之一成立:
                    θₙ = Inactive (Some _)
                    θₙ = Inactive None ∧ target n = ⊥
                    θₙ = Active _ ω    ∧ target n = ω
                  且不存在可以执行的 L-Remove
resolves m pid := installed m ∧ ∃ k ∈ d(cₘ). ωₘ k = pid
held n acc     := ∃ UProv k pid ∈ acc. ∃ m ≠ n. resolves m pid
```

`held n acc`:`n` 尚未撤回的某个 provision 仍被别的已安装 fiber 解析。它是卸载的守卫,见 4.2。

`visible` 只计入 Active 的 provider,所以 provider 一进入 Unloading,它的服务就对新解析不可见;
而已经解析到它的依赖者仍持有 ω,可以继续读写,直到自己卸载完毕。

## 4. 规则

所有规则都写作 `γ —ℓ→ γ'`,标签 `ℓ` 决定唯一的后继(若存在),也就是
`step : State → Label → option State`。

### 4.1 编排规则(外部输入)

| 标签 | 前提 | 效果 |
|---|---|---|
| `O-Insert c` | `p(c)` 与所有现存 fiber 的 `p` 两两不相交 | `m := next`,`next += 1`;`F m := ⟨c, root, false, Inactive None⟩` |
| `O-Dispose n` | `n ∈ dom F` | `τₙ := true` |
| `O-Reset n` | `θₙ = Inactive (Some ξ)` | `θₙ := Inactive None` |
| `O-Restart n` | `θₙ ∈ {Loading _ acc ω, Active acc ω}`,`τₙ = false` | `θₙ := Unloading acc ω None` |
| `O-React n i` | `θₙ = Active acc ω`,`τₙ = false`,`reacts(cₙ)` 的第 i 项为 `c`,`p(c)` 不冲突 | `m := next`,`next += 1`;`F m := ⟨c, n, false, Inactive None⟩`;`θₙ := Active (USpawn m :: acc) ω` |

`O-Restart` 对应 Cordis 的 `restart`:不管 target 是否改变,都强制卸载;卸载完成后 fiber 回到 `Inactive None`,由 `L-Begin` 重新加载。

`O-React` 把一次事件反应建模成 `n` 的子 fiber:反应的操作就是子 fiber 的操作,构成一个运行期效应。提前撤销这个效应就是 `O-Dispose m`;`n` 卸载时会先等所有运行期子 fiber 退出(`parent_waits_child`)。

### 4.2 生命周期规则(系统自动)

**加载**

| 标签 | 前提 | 效果 |
|---|---|---|
| `L-Begin n` | `θₙ = Inactive None`,`target n = ω ≠ ⊥` | `θₙ := Loading body(cₙ) [] ω` |
| `L-Divert n` | `θₙ = Loading P acc ω`,`target n ≠ ω` | `θₙ := Unloading acc ω None` |
| `L-Step n` | `θₙ = Loading P acc ω`;`P = Done` 时还要求 `target n = ω` | 按 `P` 分情况,见下 |

`L-Step n` 按 `P` 分情况。除 `Done` 外,target 变化之后照样可以走:这是在途迭代的落地(差异 h)。
target 变化后 `L-Divert` 随时可用,所以落地几步、何时放弃都由调度决定;收尾的 `Done` 只在 target 未变时走。

- `Done`:`θₙ := Active acc ω`。
- `Fail ξ`:`θₙ := Unloading acc ω (Some ξ)`。
- `Op k a x κ`:先解析 pid:`k ∈ d` 时取 `ω k`;否则取 `B k`(要求其 owner 为 `n`);
  解析失败视为 `Fail`。然后取令牌 `tok := next`,`next += 1`,
  对 `B` 中该 pid 的状态 `s` 执行 `run a tok s`:
  - 失败:`θₙ := Unloading acc ω (Some ξ_op)`;
  - 成功 `(s', g, o)`:写回 `s'`,`θₙ := Loading (κ o) (UOp pid g :: acc) ω`。
- `Provide k s P'`:要求 `k ∈ p(cₙ)` 且 `B k` 未定义(否则视为 `Fail`)。
  `pid := next`,`next += 1`;`B k := ⟨pid, n, s⟩`;
  `θₙ := Loading P' (UProv k pid :: acc) ω`。
- `Spawn c P'`:要求 `p(c)` 与所有现存 fiber 的 `p` 不相交(否则视为 `Fail`)。
  `m := next`,`next += 1`;`F m := ⟨c, n, false, Inactive None⟩`;
  `θₙ := Loading P' (USpawn m :: acc) ω`。

**卸载**

| 标签 | 前提 | 效果 |
|---|---|---|
| `L-Leave n` | `θₙ = Active acc ω`,`target n ≠ ω` | `θₙ := Unloading acc ω None` |
| `L-Undo n` | `θₙ = Unloading (u :: acc) ω ζ`,`¬ held n (u :: acc)`,且见下方按 `u` 分的前提 | 见下 |
| `L-RetireChild n` | `θₙ = Unloading (USpawn m :: acc) _ _`,`¬ held n (USpawn m :: acc)`,`m ∈ dom F`,`τₘ = false` | `τₘ := true` |
| `L-Unloaded n` | `θₙ = Unloading [] ω ζ` | `θₙ := Inactive ζ` |
| `L-Remove n` | `τₙ`,`θₙ = Inactive _`,没有 `m` 满足 `πₘ = n` | 删除 `F n` |

`L-Undo n` 按表头 `u` 分情况:

- `UOp pid g`:若 `B` 中有该 pid,把它的状态 `s` 改为 `g s`;若绑定已不存在,
  则不做任何事。按不变量,这种情况不会发生。
- `UProv k pid`:删除 `B k`。由守卫,此时没有 `m ≠ n` 满足 `resolves m pid`。
- `USpawn m`:要求 `m ∉ dom F`,即子 fiber 已经被移除。

三种情况的共同效果:`θₙ := Unloading acc ω ζ`。

**守卫** `¬ held` 作用于整个卸载:只要 `n` 还没撤回的任何一个 provision 仍被别的已安装
fiber 解析,`n` 就既不撤销任何一项,也不请子 fiber 退出。依赖者因此在提供者的全部效应
(不只是 provision 本身)都还在的状态上完成自己的卸载。这对应 Cordis 的 `_unload`:先等
全部 provision 的依赖者退出,再启动任何 disposer(差异 g)。不会因此死锁:被等待的依赖者
秩更高,而提供者一离开 Active,它们的 target 就变了,必然离开。

由此,父 fiber 按 LIFO 撤到 `USpawn m` 时,先用 `L-RetireChild` 请求子 fiber 退出,
然后**等待**子 fiber 卸载并移除,再继续撤销更早的项(差异 j)。
在 `USpawn m` 之后注册的效应此时已经撤销完毕。

## 5. 与 DESIGN.md 的细化

1. **差异 j**:不再给卸载加"没有已安装子 fiber"的整体守卫,而是让 `USpawn` 撤销项逐项等待。
   这和 Cordis 中"子 fiber 的 dispose 是父 fiber 的一个 disposer"一致,
   而且父 fiber 中晚于 spawn 的效应先撤销。
2. **卸载逐项进行**(`L-Undo`),不再像论文那样一步应用整个累加器。
   这样 `USpawn` 才能等待子 fiber。守卫 `held` 则按 fiber 整体判断(差异 g,同 Cordis):
   早先的版本把守卫只放在 `UProv` 这一项上,提供者会在依赖者离开之前先撤掉 provide
   之后的效应,依赖者卸载时看到的是被拆了一部分的服务。
3. **差异 h**:论文 `L-Divert` 的两支(放弃在途迭代、让它落地)都保留,但不合在 `L-Divert` 里:
   每个 `L-Step` 是原子的服务操作,target 变化后仍可再走(落地),`L-Divert` 随时可以放弃。
   只有收尾的 `Done` 要求 `target n = ω`,与论文的 `L-Finish` 和 Cordis 的 reload 一致
   (target 已转向就直接进入 UNLOADING,不变成 ACTIVE)。论文的 inertial 宿主只落地一次迭代;
   这里允许落地任意多步,覆盖 Cordis 的两种行为:异步迭代器让在途的那一次落地,同步迭代器一口气跑完。
   见 DESIGN.md 差异 h 与 D6"在途操作"。
4. **差异 k**(单独撤销某个效应):用 `O-React` 把每次反应编码为子 fiber,不把 `acc` 改为树。
   子 fiber 本身就是一棵子效应树,单独撤销就是 `O-Dispose`。恢复精确性对它直接成立
   (`Runtime.v`: `effect_exact`):效应出现之前到消失之后,每个绑定的状态都 ≃
   同一次执行中略去该效应全部操作得到的状态,不论其他 fiber 同时做了什么。
   合流不覆盖运行期:它的执行可以穿插 `O-Insert`、根 fiber 上的 `O-Dispose`、`O-Restart`、
   `O-Reset`(第 4 层),但不含 `O-React`;`cinv_step`、`pinv_step`
   这类只在没有运行期效应时成立的不变量明确排除 `O-React`。保持性、顺序、恢复精确性、进展、终止都覆盖 `O-React`。
5. **不设 `Amb`**(见第 0 节)。

## 6. 要证明的性质(v1 版本)

1. **保持性**(**已证**,`theories/Preservation.v` 中的 `preservation` 与 `wf_reachable`):
   不变式 `WF` 在初始状态成立,且被每条规则保持。它由 10 条组成:
   - 现存名字、pid、`USpawn` 中的子名字都小于计数器;
   - 子 fiber 的父 fiber 存在、处于已安装状态,且累加器中有对应的 `USpawn`;
   - 现存 fiber 的 `p` 两两不相交;
   - 已解析的每个依赖都有绑定,pid 与 ω 一致,且 owner 不是自己;
   - 已安装 fiber 的 ω 的键序列恰为 `d`;
   - 每个绑定的 owner 存在、处于已安装状态、`k ∈ p(owner)`,且 owner 的累加器中有对应的 `UProv`;
   - 累加器中的每个 `UProv k p` 都对应一个现存绑定(pid 为 p,owner 为自己);
   - 一个累加器中每个键至多有一个 `UProv`。

   推论:有子 fiber 或绑定的 fiber 一定处于已安装状态;一个 fiber 卸载完毕时,
   它的子 fiber 和绑定都已经不存在了。`UOp` 项不需要任何不变式。
2. **顺序**(**已证**,`theories/Ordering.v`):
   - 生命周期自动机(`fiber_step`):每一步之后,每个仍然存在的 fiber 的生命周期只沿
     Inactive → Loading → Active → Unloading → Inactive(以及 Loading → Unloading)变化,
     组件和父指针不变;只要它前后都处于已安装状态,ω 就不变。新 fiber 都以
     `Inactive None` 出现,名字为当时的计数器(`new_fiber`)。
   - `L-Begin n` 时 `n` 的全部依赖都由 Active 的提供者绑定,`n` 针对恰好这些 provision
     开始加载(`begin_requires_deps`);
   - 提供者比依赖者活得久:依赖者处于已安装状态时,它解析到的每个 provision 都存在、
     pid 不变,提供者处于已安装状态(`provider_outlives`)。服务状态按设计是共享且可变的,
     固定的是 provision 的身份;
   - 值只被声明或提供该键的 fiber 改变(论文定理 70 的第 3 条):一步之后 pid 不变的绑定,
     要么值不变,要么是某个声明或提供该键的 fiber 的 `L-Step` 或 `L-Undo` 改了它
     (`value_moves`)。撤销的情形靠不变式 `Decl`:`UOp` 撤销项只出现在声明或提供其键的
     fiber 的累加器里(`decl_step`、`decl_reachable`);
   - 撤回 provision 时没有其他已安装 fiber 解析到它(`withdraw_waits`);只要还有,
     撤回就不适用(`withdraw_blocked`);
   - 更强地,只要提供者尚未撤回的某个 provision 还被别的已安装 fiber 解析,它就不撤销
     任何一项、也不请子 fiber 退出(`unload_waits`、`unload_blocked`):提供者的全部效应
     比依赖者活得久;
   - 父 fiber 撤销到 `USpawn m` 时,子 fiber `m` 已被移除(`parent_waits_child`)。
3. **解析一致**(**已证**,同上):每个 `L-Step n` 都按承诺视图 ωₙ 执行,不论 target 此后变成什么;
   收尾的 `Done` 一步还要求 `target n = ωₙ`(`step_coherent`)。target 变化后,Loading 的 fiber
   可以中途放弃,不能收尾,剩下的迭代仍可落地(`divert_when_changed`),Active 的 fiber 可以离开
   (`leave_when_changed`);
   反过来,只有 target 变化时才能放弃或离开(`divert_only_when_changed`、
   `leave_only_when_changed`)。
4. **恢复精确性**(**已证**,`theories/Recovery.v`):选定 fiber `n`,沿执行维护一个
   影子存储:其他 fiber 的操作与撤销、所有绑定的创建与删除都照常进行,只跳过 `n` 自己的
   操作与撤销(`event`、`shadow_apply`、`shadow_run`)。不变式 `R`:对每个键,把 `n`
   在该绑定上尚未撤销的逆按 LIFO 依次作用于实际状态,结果 ≃ 影子状态(`R_step`)。
   - `recovery_exact`:从 `n` 没有待撤销操作的状态出发,执行到 `n` 再次没有待撤销操作
     (比如卸载完毕)时,实际存储 ≃ 影子存储;`recovery_from_init` 是从初始状态出发的特例。
   - 需要的假设只有两条:所有服务操作良好;任意两个组件可能执行的操作,令牌不同时撤销独立
     (R1 的 `RevertIndep`)。不需要前向操作可交换,同一 fiber 内部不需要任何假设(LIFO)。
   - 为此 `UOp` 撤销项记录了操作用的令牌,并维护了辅助不变式 `Prov`:正在执行的程序是组件
     程序的后续;每个撤销项的逆都来自组件程序中某个操作;不同 fiber 的撤销项令牌互不相同。
5. **进展**
   - **不死锁**(**已证**,`theories/Progress.v`):定义"稳定"(`settled`):失败的 fiber 停在
     Inactive;不该运行的停在 Inactive;该运行的处于 Active 且 ω 等于 target;没有 Loading 或
     Unloading 的 fiber。定理 `quiet_settled`:没有生命周期规则可用的状态一定稳定;
     `progress`:任意状态要么稳定,要么有某条生命周期规则可走;`progress_reachable` 是从初始
     状态可达的特例。
   - 假设:组件间的 `Above` 关系(c 提供了 c' 声明的某个键,或 c 的程序可能 spawn c')没有
     无限上升链,对应论文"≺ 无环且注册有界"。
   - 唯一可能等待的地方是卸载:等依赖者离开(在撤销任何一项之前),或等子 fiber 被移除。证明沿 `Above` 做良基归纳。
     为此新增两条不变式(`Inv2`,`inv2_step` 证明其保持性):不同绑定的 pid 互不相同;子 fiber
     的组件出现在父组件程序的某个 spawn 中。
   - **终止**(**已证**,`theories/Termination.v`):只执行生命周期规则时步数有限。
     `termination`:满足不变式的状态在生命周期步关系下可及(Acc);`no_infinite_run`:不存在
     无限的生命周期步序列;`termination_reachable`:从初始状态经任意执行(含编排步)到达的
     状态也是如此。
     - 假设:组件上有一个秩,沿 `Above` 严格递增,且有上界 `Rb`(组件有限时就是一个拓扑序);
       每个组件程序任一路径的步数不超过 `Kb`(`Bounded`,对应论文的 len ≤ K)。
     - 证明:给每个 fiber 一个度量 μ(在 target 不变时它还能走的步数的上界),状态的度量是
       按秩分层求和得到的向量,每一步生命周期规则都使它按字典序严格下降。target 已转向的 Loading fiber
       记作"放弃后卸载所需的上界加上剩余步数"(`2·Kb + 1 + μ_U([]) + (Kb − |acc|)`),落地一步使剩余步数减一,
       放弃使它落到卸载的度量之下。关键事实是一个
       fiber 的步骤不影响秩不高于它的其他 fiber(`lstep_effects`、`mu_other`)。
     - 新增两条不变式:Loading 的 fiber 剩余程序受剩余步数预算约束(`LoadBound`);撤销
       spawn 的项指向的子 fiber 的父指针指回持有者(`SpawnOwn`)。
6. **合流**:在相同的编排输入下,任意两次执行到达的 quiet 状态,经名字与 pid 的重命名后相等,
   而且等于按依赖顺序静态组装的结果。失败是唯一的例外,同论文(4.4 节 Failure 段)。分三层:
   - **第 1 层:控制状态(已证,`theories/Confluence.v`,限于不 spawn 的组件)。**
     `control_confluence`:从同一个满足不变式的状态出发,任意两次只含生命周期步、终于
     quiet 且没有失败 fiber 的执行,得到相同的 fiber 集合、相同的组件、相同的 Active 集合,
     每个键由同一个 fiber 提供。`exists_quiet`:这样的 quiet 状态总能到达(由终止与进展)。
     证明不重排执行:静止状态下 Active 集合满足同一个不动点方程(一个 fiber 是 Active 当且仅当
     它声明的每个键都由某个 Active 的 fiber 提供,`active_iff`),定义域由出发状态确定,而该
     方程只有一个解(`fix_unique`,沿秩归纳)。pid 不同不影响结论,因为比较的是提供者的名字。
     假设:组件不 spawn(`NoSpawn`);全性(`Total`,论文 Def 76:走到 `Done` 的每条路径都
     提供组件声明的每个键)。新增不变式:`ProvideInv`(Loading 的 fiber 已经提供或在每条
     到 `Done` 的路径上都会提供它的键;Active 的 fiber 已经提供全部)、`NoSpawnInv`。
   - **第 2 层:服务状态(已证,`theories/ServiceSeq.v`、`theories/StateInv.v`、`theories/Episode.v`、`theories/StateConf.v`)。**
     `state_confluence`:在第 1 层的条件下,两次执行终止时同一个键上的两个绑定,
     其服务状态 ≃。证明分三步:
     1. 单次执行不变式(`INV`、`sinv_step`):每个绑定的状态 ≃ 它的初始状态依次施加其上
        仍未撤销的操作,顺序按令牌从小到大。撤销一项时用 `replay_remove`(撤销独立)。
     2. 路径确定性(`EPInv`、`pinv_step`):Loading 或 Active 的 fiber 的累积器是其程序的一条
        "理想轨迹"(`Tr`):每个操作的结果,按所解析到的 provision 的**初始**状态、再加上
        本 fiber 此前在该键上的操作(`ownIt`)计算。实际执行中,别的 fiber 的操作都可以移到
        后面(`replay_shuffle_ex`),且不影响结果(`outcome_after`)。理想轨迹由程序和这些
        初始状态唯一确定(`tr_done_eq`),而初始状态来自更低秩的提供者的轨迹,于是沿秩归纳,
        两次执行中每个 Active fiber 的轨迹相同(`final_evs`)。
     3. 终态上一个键的待定操作,可以重排成"逐个 fiber 的操作块"(`final_blocks`);两次执行
        的块相同(第 3 层里差一个块的排列),由 `replay_tokens`(第 3 层为 `replay_blocks`)
        得到 ≃。
     - 鬼记录:状态新增 `oplog`(令牌 → 操作)和 `inilog`(pid → 初始状态),规则不读它们。
     - 新增服务假设:`HUI`(同一令牌下产出的逆与状态无关)、`HTI`(结果与令牌无关),以及
       只针对"可能相遇"的操作对的 `HCom`(令牌不同时可交换)与 `HRI`(撤销 a 不受其后的 b
       干扰)。"可能相遇"是 `CoPair k a b`(`Recovery.v`):两个 fiber 可能在同一个键 `k` 上
       分别执行 a 和 b,即 a、b 出现在两个组件的程序中,或出现在同一个可以同时有多个 fiber
       的组件(它不提供任何键)的程序中(R4,见下)。
     - `HRI` 还只要求在 a 之后可达的状态上(`After`:a 的结果,再经过与它相遇的操作)、且 b
       在该状态成功时成立(`shifted_ok`),比 R1 的 `RevertIndep` 弱(`revert_indep_after`)。
       放宽的原因都是执行中到达不了的情形:同一回调注册两次时,"撤掉一个"在不含该回调的状态上
       与另一次注册不交换;同名注册两次时,第二次在第一次之后必然失败,不会与它同时待定。
     - 带令牌的有序事件总线不满足 `HCom`;忽略顺序的监听器模型满足(第 7 节)。
   - **第 3 层:含 spawn 的系统(已证,`theories/SpawnConf.v`)。**
     `spawn_confluence`:去掉 `NoSpawn`,在第 2 层的服务假设下,两次只含生命周期步、终于 quiet
     且没有失败 fiber 的执行,在重命名意义下一致:
     1. **规范名**(`CName`、`CN`):根 fiber(无父)保留原名;子 fiber 记作(父的规范名,它在父的
        spawn 项中自最早起的位置)。终态中每个 fiber 恰有一个规范名(`cn_total`、`cn_fun`),
        不同 fiber 的规范名不同(`cn_inj`)。
     2. 两个终态有相同的规范名集合,对应的 fiber 组件相同、同为 Active 或同为 Inactive。
     3. 每个键由对应的 fiber 提供,两边绑定的服务状态 ≃。
     - 为什么第 1、2 层必须合并:父 fiber 是否走到某个 spawn,取决于它之前操作的结果。证明沿秩
       归纳(`corr_step`、`corresp_all`),秩沿提供依赖和 spawn 都递增(`Above` 本来就包含两者)。
       每个秩较低的规范名在两边都存在、组件相同、活跃性相同,Active 时理想轨迹相同。子 fiber 的
       对应由父 fiber 轨迹中第 j 个 spawn 事件给出(`Corr` 的 `co_spawn` 记录子 fiber 的组件)。
       待定操作的多重集沿规范名的双射对应(`perm_bij`)。
     - 新不变式(出发状态需满足,生命周期步保持,`sl_step`):`SLInv`。Loading 或 Active 的 fiber
       的每个 spawn 项指向一个存在且未 dispose 的子 fiber,唯一例外是 Unloading 累积器顶上的那一项;
       同一累积器的 spawn 项互不相同;父的名字小于子的名字。直接 dispose 启动时 spawn 的子 fiber
       会破坏它;Cordis 允许这样做,dsh 也常这样回收事件处理器里动态创建的子 fiber,后者不在本模型内
       (DESIGN.md 差异 q)。
     - 辅助性质:`NamesFixed`(名字一旦分配,组件不变)、`RootKeep`(根 fiber 在生命周期执行中
       既不新增也不消失)。
     - spawn 时的冲突检查与调度有关,但冲突导致失败,已由"没有失败 fiber"排除。
     - 证明里与出发状态有关的只有两点:两个终态都满足不变式,根 fiber 一一对应。把这两点
       提成前提,就得到与执行无关的 `final_agree`:两个终态(`FinalS`),只要根 fiber 按标签
       一一对应、组件相同(`RootsMatch`,标签单射 `RootInj`),就在重命名意义下一致
       (`AgreeL`)。规范名的根部分由标签给出(`CRoot (rt n)`);`spawn_confluence` 取恒等标签。
   - **第 4 层:编排与生命周期交错(已证,`theories/Dynamic.v`),对应论文定理 80。**
     前三层比较的是从同一状态出发、只含生命周期步的执行;论文的定理 80 允许编排步穿插其间。
     1. **输入按插入序号指称根 fiber**(`Input`:`IIns c`、`IDis i`、`IRestart i`、`IReset i`)。
        根 fiber 的名字取自计数器,而计数器也被生命周期步推进,所以同一输入在不同调度下得到
        不同的名字。执行 `DRun` 从初始状态出发,按顺序消耗输入,其间可以任意插入生命周期步,
        并记下每次插入取得的名字。
     2. **根台账**(`Ledger`,`drun_inv` 证明其保持性):第 i 次插入的名字或者已被移除(此时
        序号 i 被 dispose 过),或者是第 i 个插入组件的根 fiber,且 disposed 当且仅当序号 i
        被 dispose 过;每个根 fiber 都在台账中。另证 `SLInv` 在 `O-Insert`、根上的
        `O-Dispose`、`O-Restart`、`O-Reset` 下保持(`sl_insert`、`sl_dispose`、`sl_restart`、
        `sl_reset`)。
     3. **结论**。终态(quiet 且无失败)中,根 fiber 恰为未被 dispose 的序号上的 fiber。根以它
        在幸存者中的位置为标签(`slab`)。
        - `dynamic_agree`:两次执行的输入留下相同的幸存组件序列(`scomps`)时,终态在重命名
          意义下一致。两次的输入可以不同,与生命周期步的交错方式也可以不同。
        - `dynamic_confluence`:输入相同时的特例,即论文定理 80(2)。
        - `static_assembly`:任意执行的终态,与"只按原插入顺序各插入一次幸存组件"的执行的
          终态一致,即论文定理 80(1) 的"等于静态组装"。插入之后,生命周期步按任意顺序进行。
     - 范围:不含 `O-React`;只 dispose 根 fiber(dispose 启动时 spawn 的子 fiber 会破坏
       `SLInv`,见 DESIGN.md 差异 q)。插入时的冲突检查与调度有关:一种调度下插入成功、
       另一种下被拒绝时,后者不构成以这些输入为输入的执行,不在定理范围内。
     - 与论文的区别:论文的规范形还给出 episode 的顺序(按 ⊲ 线性化各一个 episode);这里
       不构造那样的执行,只断言终态与静态组装一致。静态组装的执行能否到达无失败的 quiet
       状态,作为前提给出,不另行证明。

## 6′. R4:由服务的可交换性推出插件之间的独立性(§3.3–3.4)

论文的定理 45(不同键上的操作天然独立)与定理 47(只在双方都操作的键上需要可交换)在本形式化
中的对应:

- **按键、按 fiber 放宽假设。** 恢复(`Recovery.Hind`)与合流(`HRI`、`HCom`)的独立性假设
  只针对 `CoPair k a b`:同一个键上、可能来自两个不同 fiber 的操作对。不同键上的操作从不
  相遇(每个键有自己的绑定),同一个 fiber 自己的操作之间也从不需要比较。原来"插件先注册、
  再读取自己的条目"不满足假设的限制因此消失。同一组件只有在没有提供任何键时才可能同时有
  多个 fiber(提供集合两两不相交),所以只有这种组件自己的操作对仍要满足假设。
- 证明上的变化:
  - 撤销一项时,它之后的待定操作都来自别的 fiber(`sinv_pop_hit`);
  - 理想轨迹计入 fiber 自己此前的操作(`ownIt`);
  - 比较终态时只在不同 fiber 的操作之间重排(`replay_shuffle_ex`、`replay_blocks`,`ServiceSeq.v`)。
- 服务一侧:`Compose.ConfHyps Σ R` 以"可能相遇"的关系 `R` 给出假设,`service_confluence`
  要求 `CoPair` 落在 `R` 内。注册表的 `reg_meet`(`RegistryConf.v`)允许任意注册、任意查询,
  以及注册与查询不同的名字;查询别的 fiber 在同一键上注册的名字仍被排除,因为结果取决于
  对方是否已注册。论文所说"可交换是提供该键的组件的义务"(定义 46 之后),在这里就是给出 `R`
  与 `ConfHyps`。
- **观察等价**(定义 31、引理 32,`Observe.v`):"不可区分"(任意测试结果相同)是所有操作都
  尊重的最粗等价(`admissible_indist`、`indist_admissible`);良好服务的 ≃ 都包含于它
  (`wb_indist`)。应用:有序事件总线含分发时,任何合法的 ≃ 都不能让两次注册可交换
  (`bus_no_commute`),所以分发必须留在启动模型之外。监听器模型没有分发,不可区分在那里
  是全关系;`Listeners.v` 选的"互为排列"更细,结论也更强。

## 6″. R7:§3 的代数与 §4 的演算的衔接(`theories/Bridge.v`)

演算没有直接使用 §3.1 的 `Twisted`/`Eff`:它的服务操作是部分的,状态按 ≃ 比较,独立性假设是
操作级的。`Bridge.v` 把两边接起来,分四部分。

1. **§3.1 的 setoid 与部分函数读法**(定义 36、引理 38 的核心)。`PEff Γ := Γ → option (Γ × (Γ → Γ))`,
   前提不满足时为 `None`(定义 19 所说的 `Maybe` 读法)。`PWitnessed`:逆在应用处按 ≃ 回到原状态,
   逆尊重 ≃,效应本身尊重 ≃(结果与逆都按 ≃ 比较)。
   - `pdiamond_witnessed`:⋄ 保持见证(定理 11);`pbind_witnessed`:定义 30 中按结果选择后续的
     组合(式 (32))保持见证;`pdiamonds_witnessed`:序列。
   - `witnessed_total_iff`、`pdiamond_total`:取 ≃ 为相等、函数为全函数时,`PWitnessed` 就是定义 8,
     `pdiamond` 就是 `EffectFun.diamond`。
2. **`⟦·⟧`:程序作为存储上的效应函数**。存储 `Store := K → option St`,≃ 按定义 33(定义域相同,
   值相关)。操作按式 (31) 提升(`oplift`:只读写键 k 上的绑定),provide 是定义 20 的 `set`
   (`setk`:k 未绑定时才有定义,逆为删除),程序按定义 30 组合(`denote`,令牌从 t 起依次取)。
   spawn 不是存储上的效应(定义 52),解释为空。
   - `denote_witnessed`:操作良好时,每个程序都解释为带见证的效应函数。单独运行再撤销一个组件,
     存储按 ≃ 回到原样,即局部的时间可组合性。
   - `distinct_keys`(定理 45):操作的前向映射与每个逆都"局限于"它的键(`LocalAt`:不改别的键,
     在本键上的值只取决于本键);局限于不同键的映射可交换,而且互不改变对方的定义域、逆与结果。
3. **定义 44 推出演算的假设**。`PaperIndep a ta b tb`:两个操作的生成元(前向映射与产出的逆,
   引理 41(1) 说明在生成元上检查即可)两两可交换(部分映射意义下:两边同时有定义,有定义时 ≃),
   且每一方的生成元都不改变另一方的定义域、逆与结果(式 (40)、(41))。`Maybe` 读法多出的一点是
   "不改变定义域"。
   - `paper_revert_indep`:推出撤销独立(`RevertIndep`);`paper_commute`:推出可交换(`Commute`)。
   - `paper_confhyps`:对"可能相遇"的关系 `G` 内、令牌不同的操作对满足定义 44,再加上良好性、
     `UniformInv`、`TokIrr`,就得到 `ConfHyps Σ G`,于是 `service_confluence` 适用。
     `paper_hind`:同理得到恢复精确性的假设 `Hind`。
   - 所以 §4 的定理在论文自己的假设下成立(定义 46 让每个键都可交换)。反过来,演算要求的更少:只针对可能相遇的操作对和不同
     的令牌,不要求一个操作与自己独立。`UniformInv` 与 `TokIrr` 不由定义 44 推出,是额外的服务假设。
4. **`⟦·⟧` 与步骤的对应**。通过存储投影 `cstore`(每个已绑定键上的服务状态)看:
   - `op_stage`:`L-Step` 执行一个操作,就是对存储施加 `oplift`,并把它产出的逆的底层函数记为
     撤销项 `UOp`;`op_undo`:`L-Undo` 这一项时,只要它当初所在的绑定(pid 相同)还在,就对存储
     施加同一个逆,否则不做任何事。
   - `prov_stage`、`prov_undo`:provide 与撤销 provide 分别是 `setk` 及其逆。
   - 因此累加器就是 §3.1 的复合逆,按 LIFO 逐项执行。
   - `lone_denote`(整次激活):一个 fiber 单独地从 `Loading P acc w` 走到 Active(`Lone`:其间只有它
     的 `L-Step`),则 `denote P`(令牌从当时的计数器起)在原存储上有定义,终点 ≃ 实际存储;新加入
     累加器的撤销项 `pre`(`acc' = pre ++ acc`)按 LIFO 读成存储上的映射(`uinterp`)后,≃ `denote P`
     产出的逆。为使令牌对齐,`denote` 中 provide 与 spawn 也各占一个编号,与演算的计数器一致。
     反方向不成立:`denote` 不检查依赖解析与 spawn 冲突,演算可能在 `denote` 有定义处失败。
     与别的 fiber 交错时的情形由恢复精确性(`Recovery.v`)处理,不经过 `denote`。

## 7. R1 的结论:两种独立性

R1(`theories/Service.v`)把论文的"独立性"拆成了两个层次。

- **撤销独立**(`RevertIndep a b`):a 产出的每个逆 g 都满足两点。
  (1) 先撤 a 不影响 b:b 在 `g x` 上与在 `x` 上同时失败或同时成功;成功时后继相差一个 g,
  产出逐点相等的逆和相同的结果。(2) g 与 b 产出的逆可交换。
  它**不要求 a、b 的前向操作可交换**。`omission` 定理证明了:撤销独立就足以
  "撤掉 a 而保留其后的外来操作"。因此恢复精确性(第 6 节第 4 条)只需要撤销独立。
- **可交换**(`Commute a b`):先 a 后 b 与先 b 后 a 的结果相同。合流(第 6 节第 6 条)需要它。

两个服务模型上已证明的结论:

| 服务 | 结论 |
|---|---|
| 按名注册表(`Registry.v`) | 操作都良好;不同名字的注册撤销独立且可交换;同名注册不撤销独立;读取别人注册的条目不撤销独立 |
| 注册表,合流假设(`RegistryConf.v`) | 以全部注册操作(任意名字)为 `G`,合流所需的全部服务假设成立(`registry_hyps`);查询不在 `G` 内 |
| 有序事件总线(`EventBus.v`) | 注册与分发都良好;不同令牌的注册撤销独立,但**不可交换**(钩子顺序不同);分发能观察到注册;Cordis 现行的"按回调注销"不是逆操作(差异 p) |
| 监听器注册,忽略顺序(`Listeners.v`) | 状态是回调列表,≃ 为互为排列;操作为追加与前插,逆为 Cordis 现行的"按回调删除第一个";全部服务假设成立;`listeners_confluence`:两次调度后每个键上的回调多重集相同 |

由此对合流的影响:事件监听器的顺序取决于各插件的激活顺序。所以合流只能在
"忽略监听器顺序"的意义下成立;如果某个事件的分发依赖顺序(`waterfall`、`bail`),
系统的结果就和调度有关。这是理论对 Cordis 的又一处具体约束。

覆盖方式(`Listeners.v`):
- 它就是 Cordis 的实际语义,只把 ≃ 放宽为"互为排列"。演算规则不读 ≃,所以合流定理直接
  适用于 Cordis 的真实执行,不需要另证模拟关系。
- 在这个 ≃ 下,按回调注销是精确的逆:删错了同回调的另一项只改变顺序。所以差异 p 只影响顺序。
- 分发不在模型内:它的结果是有序回调列表,任何忽略顺序的 ≃ 都不尊重它。启动程序若读取
  分发结果,就不在定理范围内。
- 排查结果(docs/EMIT-AUDIT.md):dsh 中读取分发结果的 38 处调用全部在运行期,
  启动期间只有注册时发出的变更通知,不读结果,其监听器按"监听加当前状态"编写。
- 多个服务:见下一小节的和服务。

### 组合多个服务(`Compose.v`)

- `ConfHyps Σ G`:合流定理所需的服务假设打包在一起(良好性、逆与状态无关、结果与令牌无关、
  放宽后的撤销独立、可交换),`G` 是组件可能执行的操作集合。`service_confluence`:组件程序
  的操作都在 `G` 内时,`spawn_confluence` 的结论 `Agree` 成立。
- `Sum Σ1 Σ2`:两个服务并列。一个绑定的状态属于其中一个服务;一个服务的操作作用在另一个
  服务的状态上时失败。`sum_hyps`:两边各自满足 `ConfHyps` 时,和服务也满足(取
  `sumG G1 G2`)。不同服务的操作不会作用在同一个状态上,所以总是可交换、互不干扰。
- 例子(`Examples/Composed.v`):注册表加监听器,启动程序只做注册时,`composed_confluence`
  给出两次调度的终态在重命名意义下一致,注册表键上的条目相同,事件键上的回调多重集相同。

## 8. 待定

1. ~~服务状态类型随 `k` 变化如何表示~~:R2 已定为统一服务 Σ。
   ~~"和服务"组合子~~:已完成,见第 7 节末尾。
2. `L-Undo` 遇到 `UOp` 而绑定已不存在时:按不变量不会发生,但 `step` 函数仍需给出
   定义。目前定为不做任何事。
