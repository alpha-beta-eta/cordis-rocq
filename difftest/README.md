# difftest：演算与 Cordis 的差分测试

在真实的 Cordis 上运行由同一份规格生成的插件，记下每个生命周期事件，再把事件序列在
`theories/Calculus.v` 的 `step` 上重放：每个事件都必须是演算允许的一步，走完之后演算的状态必须与
Cordis 的快照一致。这是 [DESIGN.md](../docs/DESIGN.md) D6"精化"的第一步：在证明精化之前，先用测试找出
模型与实现对不上的地方，每一处都给出能重放的最短见证。

它检查的方向是**实现 ⊆ 演算**：观察到的每个 Cordis 执行，都应当是演算的某个执行。反方向（演算能走的
Cordis 都能走）不检查；只在 Cordis 落定时要求演算也走不动（下面的"静止"）。用例是有界枚举，
属于欠近似：报出的分歧一定真实存在，没报的不等于没有。

## 运行

在 WSL 中运行，需要 node 22 和 OCaml（opam 的 `ocamlopt`）。Cordis 源码与 TS 转译沿用
[checker/](../checker/) 的加载钩子（首次运行时 `checker/setup.sh` 会准备好）。

```sh
sh run.sh 4                       # 长度不超过 4 的编排脚本, 约 27 万个用例, 半分钟
DIFFTEST_STYLE=gen NAME=dsh-gen sh run.sh 4          # 插件写成 async 生成器
CORDIS_ENTRY=/mnt/d/cordis/packages/core/src/index.ts NAME=upstream sh run.sh 4   # 上游 Cordis
DIFFTEST_MUTANT=fifo NAME=mutant-fifo sh run.sh 3     # 种一个已知错误, 检查测试本身
```

汇总写到 `.out/summary-<NAME>.md`：按分歧归组，每组给出最短见证和到分歧为止的事件。
`calc/calculus.ml` 是抽取出来的代码，已提交；改了演算之后在仓库根目录重新抽取：

```sh
coqc -Q theories Cordis difftest/Extract.v
```

## 结构

| 文件 | 内容 |
|---|---|
| `Extract.v` | 演算的实例（键、名字、值都是自然数，唯一的服务是 `Services/Registry.v` 的登记表，组件以编号命名），加上读状态的几个函数；抽取到 OCaml |
| `calc/calculus.ml` | 抽取结果：演算自己的 `step`，以及 `denabled`（当前能走的生命周期规则） |
| `calc/replay.ml` | 重放驱动：把事件映射成标签，调 `step`，比较状态 |
| `cordis/gen.mjs` | 组件库与编排脚本的枚举 |
| `cordis/run.mjs` | 在 Cordis 上运行用例，记下事件和快照 |
| `cordis/summarize.mjs` | 归组，挑最短见证 |

## 怎样对应

**插件。** 组件规格是演算的程序：`['op', k, x, v]` 是 `POp k (Register x v)`，`['provide', k]` 是
`PProvide k ∅`，`['spawn', c]` 是 `PSpawn c`，`['fail']` 是 `PFail`。生成的 Cordis 插件 inject 声明的依赖
（服务名 `s<k>`），每条指令之前 `await` 一次。键 k 的服务值是一张登记表：`register` 在名字被占用时抛错
（对应 `rrun` 返回 `None`），返回的 disposer 删掉这一项（对应逆 `upd · x None`）。插件有两种写法：
async 函数（操作经 `ctx.effect` 登记逆）和 async 生成器（每个操作 `yield` 它的逆，即 EDSL 的写法）。

**事件到标签。** Cordis 一侧记下的事件有：fiber 创建（`internal/plugin`）、状态变化（`internal/status`）、
登记表上的操作与撤销、provide 与撤回（从 `reflect.store` 删除）、编排请求。每个事件对应的标签：

| Cordis 事件 | 演算 |
|---|---|
| 编排者创建 fiber | `OInsert c` |
| fiber p 在加载中创建子 fiber | `LStep p`（p 的下一条指令是 `PSpawn c`） |
| 操作成功 / provide | `LStep n`（下一条指令须是这个操作 / 这个键） |
| PENDING → LOADING | `LBegin n` |
| LOADING → ACTIVE | `LStep n`（`PDone`，要求 target 未变） |
| LOADING → UNLOADING | 加载失败时 `LStep n`（`PFail`、被拒的 `POp`、键已被占的 `PProvide`）；有未生效的 restart 时 `ORestart n`；否则 `LDivert n` |
| ACTIVE → UNLOADING | 有未生效的 restart 时 `ORestart n`，否则 `LLeave n` |
| 撤销一项 / 撤回一个键 | `LUndo n`（累加器的头必须正是这一项） |
| UNLOADING → PENDING / FAILED / LOADING / DISPOSED | `LUnloaded n`，之后分别不再走 / 不再走 / `LBegin n` / `LRemove n` |
| FAILED → PENDING / LOADING（`update`） | `OReset n`（之后 `LBegin n`） |
| fiber 的 uid 被清空（开始 dispose） | 顶层 fiber：`ODispose n`；p 的子 fiber：`LRetireChild p` |

另外每个事件之后，若某个 Unloading fiber 的累加器头是 `USpawn m` 而 m 已被移除，就走它的 `LUndo`
（Cordis 没有对应的事件）。

编排请求（restart、update）在 Cordis 里不立即生效：加载中的 fiber 被 restart 时，apply 照样跑完，
到加载结束时才转入 UNLOADING。所以 `ORestart` 记在它**第一次可见的时刻**，即那次状态变化，而不是发出
请求的时刻。这是把外部输入线性化到它生效的那一点，得到的仍是演算的一个执行。被拒绝的请求
（例如 restart 已移除的 fiber）要求演算也拒绝。

**比较什么。** 每个事件之后比较：每个 fiber 的状态（PENDING ↔ `Inactive ⊥`，FAILED ↔ `Inactive ξ`，
LOADING / ACTIVE / UNLOADING ↔ 同名状态，DISPOSED ↔ 不存在），每个键的绑定（提供者，登记表在全部名字上
的内容）。只放过一处：从未加载过的 fiber 被 dispose 时，dsh 的 Cordis 让它经过一次 UNLOADING（清理激活前
登记的效应），演算在它开始 dispose 时就把它从 Inactive 移除（`LRemove` 记在这一刻）。每次 Cordis 落定（没有 fiber 有在途的加载或卸载）时，要求演算**静止**：
没有任何生命周期规则能走（`denabled` 为空）。

**组件库**（`cordis/gen.mjs`）：

| 组件 | 依赖 | 提供 | 程序 | 针对 |
|---|---|---|---|---|
| P | | k0 | provide k0 | 提供者 |
| C, C2, C3 | k0 | | 1、2、3 个操作 | 依赖、LIFO 撤销、中途放弃（差异 h） |
| Cx | k0 | | 与 C 同名的操作 | 操作被拒 |
| F | k0 | | 一个操作，然后 fail | 加载失败与回滚 |
| Sp / Ch | k0 | | 操作、spawn Ch、操作 / 一个操作 | 子 fiber（差异 j） |
| Pw, PF | | k0 | provide 后操作 / provide 后 fail | 提供者用自己的服务；提供者失败；提供冲突（差异 c） |
| Q / R | k0 / k1 | k1 / | 链式依赖 | 依赖链上的级联 |

编排脚本：insert、dispose、restart、reset（`fiber.update`）的序列，每步之后落定；另有一类脚本在某个
组件加载到第 j 条指令之前插入一个动作（加载中途的 dispose、restart、insert）。长度超过 2 的脚本
不再插入与在场 fiber 提供同一个键的组件：这个分歧（差异 c）已知，而重放停在第一个分歧处，它会遮住之后的
一切。

## 结果（2026-11-25）

dsh vendored 的 Cordis（4.0.6-alpha.1，dsh `fcc0ad4`）与上游 Cordis（`D:\cordis`，`7f92195`），
编排脚本长度不超过 4：

| 目标 | 插件写法 | 用例 | 一致 | 差异 c | 差异 e |
|---|---|---|---|---|---|
| dsh | async 函数 | 269 799 | 262 582 | 1 452 | 5 765 |
| dsh | async 生成器 | 269 799 | 262 936 | 1 452 | 5 411 |
| 上游 | async 函数 | 269 799 | 262 582 | 1 452 | 5 765 |
| 上游 | async 生成器 | 269 799 | 262 936 | 1 452 | 5 411 |

dsh 与上游对每个用例的判定都相同；有 72 个用例分歧所在的事件序号差一，因为 dsh 让从未加载过的子 fiber
在 dispose 时多经过一次 UNLOADING（上游直接置为 DISPOSED）。这个 fiber 没有效应可撤，演算在它开始 dispose
时就把它移除，两者都在演算之内（见"比较什么"）。

除了这两类，没有别的分歧：没有状态不一致、没有演算不允许的加载或卸载步骤、没有守卫被越过，
Cordis 落定时演算也总是静止。差异 h 的两种行为都在演算之内：async 函数写法让加载跑完（落地任意多步），
生成器写法落地在途的一次迭代后停下（例如 C3 加载到一半时 P 被 dispose，第二个操作落地，第三个被放弃）。

### 差异 c：插入时不检查提供冲突

最短见证：`insert P, insert P`。Cordis 接受第二个 P，它的 fiber 开始加载，到 `ctx.provide` 时才因重名失败；
演算的 `O-Insert` 不接纳提供集合与在场 fiber 相交的组件。这就是 DESIGN 第 2 节 c 条的建议
（插入时拒绝冲突）所针对的差距，也是 checker 在真实插件上看到的撞名问题的根源。

### 差异 e：子 fiber 还没退出，父 fiber 先撤销了更早的效应

最短见证：`insert P, insert Sp, dispose Sp`（Sp 的程序：登记 x5，spawn Ch，登记 x6；Ch 登记 x7）。
Cordis 落定后，这条见证的事件依次是：

```
   ev orch dispose 1
   ev status 1 ACTIVE UNLOADING 0
   ev undo 1 0 6                  Sp 撤销 x6
   ev status 2 ACTIVE UNLOADING 0 Ch 开始卸载
>> ev undo 1 0 5                  Sp 撤销 x5, 而 Ch 还在 UNLOADING, x7 还在
   ev undo 2 0 7
   ev status 2 UNLOADING DISPOSED 0
```

演算按 LIFO 逐项撤销，撤到 `USpawn` 时先请子 fiber 退出，等它被移除后才继续（差异 j），所以 x5 要等 Ch
移除之后才撤。Cordis 按逆序**启动**全部 disposer 但并发执行（`Promise.all`），子 fiber 的 dispose 是异步的，
排在它前面登记的效应在子 fiber 卸载完之前就撤掉了：子 fiber 的清理看到的是被拆了一半的父 fiber。
DESIGN 第 2 节 e 条与 2.1 节记的正是这一点，上游的约定是"互相依赖的效应放进同一个效应迭代器"；
这里给出了不借助任何约定的三步见证，dsh 与上游都复现。

### 变异检查

为确认测试能发现错误，在 Cordis 或测试服务里种三个已知的错误（脚本长度 3，13 310 个用例）：

| 变异 | 内容 | 新出现的分歧 |
|---|---|---|
| `leak` | disposer 不删登记项 | 1 216 个用例，绑定内容不一致 |
| `fifo` | 卸载时按登记顺序启动 disposer | 587 个用例，撤销次序 6 组（如 C2 先撤 x2 再撤 x3，Pw 先撤回 k0 再撤 x8） |
| `noguard` | 依赖者不进提供者的 `dependents` | 338 个用例越过守卫（提供者在依赖者还在时撤回服务或撤销效应） |

三个都被发现，而且都有两三步的见证。

## 范围与局限

- 只有一个服务（登记表），只用 `Register`；没有 `O-React`（运行期反应）、可选依赖、isolate、`ctx.get`
  这些扩展与越界用法。
- 插件只经声明的依赖或自己提供的键操作；沿父链访问祖先的服务（DESIGN 2.1 节 e）不在演算内，没有测。
- 事件之间的中间状态不比较；比较的粒度是事件。restart 按它生效的时刻线性化（见上）。
- 抽取用了 `ExtrOcamlNatInt`（`nat` 映射到 OCaml 的 `int`），这是标准的可信抽取，数值都很小。
- 一处已知的说明性放宽（从未加载过的 fiber 被 dispose 时的 UNLOADING），见"比较什么"。

## 下一步

1. 沿切片链证明精化：从最小切片开始，证明每段 Cordis 代码对应演算的一步；上面的映射表就是精化关系的草稿。
2. 扩大组件库：运行期反应（`O-React`）、可选依赖（`theories/Ext/`）。
3. 把 checker 在真实插件上记下的调用序列接进来，用同一个 replay 判定。
