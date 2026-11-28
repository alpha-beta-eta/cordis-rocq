# viz：执行可视化

把演算的执行一步一步画出来，让人看到一次执行怎样展开，以及定理为什么成立（或者，在反例里，为什么不成立）。

有两种形式：

- **S-表达式（主要的）。** 写在 Rocq 里的函数，执行的输出就是 `Eval vm_compute in ...` 的结果，
  不经过抽取，也没有驱动程序。见下面的第 A 节。
- **网页。** 抽取到 OCaml、输出 JSON、由 `viewer.html` 回放。见第 1–6 节。以后网页可以改为读 S-表达式。

## A. S-表达式

`Text.v` 对演算的参数（键、服务、组件）是通用的，调用者给出键、组件、服务状态、操作的打印函数，
以及要显示的键和组件。输出是 S-表达式的序列，Racket 的 `read` 可以直接读（符号、数、字符串、`#t` / `#f`），
便于继续处理。`TextExamples.v` 是登记表实例上的例子；`sh viz/text.sh` 把它们写到 `viz/text/*.sexp`，
`racket viz/check.rkt viz/text/*.sexp` 读回并检查（见下）。

**一个状态是项的集合。** 每个 fiber 一项，每个被绑定的键一项，变体另有自己的项：

```
(fiber 1 consumer (life Unloading) (view (tools 2)) (target none) (acc (op tools 2 (register 7 42))))
(fiber 0 provider (life Unloading) disposed held (view) (target none) (acc (prov tools 2)))
(bind tools (pid 2) (owner 0) (entries (7 42)))
(queue (2 provider))          ; Queue.v：(票 组件)，队头在前
(fview 1 (tools 2))           ; ViewFail.v：fiber 1 上次卸载时的视图
```

fiber 项依次是：名字、组件，`(life 状态 [错误])`，`(parent p)`（子 fiber），`disposed`，`held`（Unloading 且守卫成立），
已提交的视图 `(view (键 pid) ...)`，目标 `(target (键 pid) ...)`（`(target none)` 是 ⊥，`(target)` 是空视图），
Loading 时的下一条指令 `(next ...)`，累加器 `(acc 项 ...)`（头在前，是下一个要撤销的；`(op 键 pid 操作)`、`(prov 键 pid)`、`(spawn m)`）。

**一次执行是一串表达式。**

```
(run "#358 early (astep)")
(init 项 ... (enabled 标签 ...))
(step 14 (LStep 4)
  (del (fiber 4 provider (life Loading) (view) (target) (next (provide tools)) (acc)))
  (add (fiber 4 provider (life Unloading EConflict) (view) (target) (acc)))
  (enabled (LUndo 1) (LUnloaded 4)))
(step 21 (LBegin 1) refused)
(final 项 ... (quiet #t))
```

因为每项带着一个 fiber 或一个绑定的全部事实，一步就是它删去的项（`del`）与加上的项（`add`），
再加这一步之后能走的生命周期步（`enabled`，为空即 quiet）。step 拒绝的标签（返回 `None`）写成 `refused`，状态不变。
从 `init` 出发逐步删去 `del`、加上 `add`，就得到每一步之后的状态；`check.rkt` 检查这样重放到最后正好是 `final`。

**两次执行并排。** `compare_text` 给出两次执行的标签列、在重命名意义下的终态、以及不同之处：

```
(compare "early (astep)" "late (astep)")
(labels a (OInsert provider) ... (refused (LBegin 1)) (refused (LBegin 4)))
(labels b (OInsert provider) ...)
(final a (comp provider (Inactive EConflict)) (comp consumer (Inactive)) (key tools unbound) (quiet #t))
(final b (comp provider (Active)) (comp consumer (Active)) (key tools (by provider) (entries (7 42))) (quiet #t))
(differ (comp provider) (comp consumer) (key tools))
(same #f)
```

终态按组件对应（`(comp c 生命周期 ...)` 依名字次序列出组件 c 的各个 fiber），绑定按键对应、记提供者的组件而不是名字：
名字与 pid 从同一个计数器取，调度不同就不同。

执行的 step 函数是参数：核心的 `step`、`Admit.v` 的 `astep`、`Queue.v` 的 `qstep`、`ViewFail.v` 的 `vstep` 都用同一个 `run_text`，
只需给出读核心状态的函数、变体自己的项、以及变体自己的生命周期标签（`(QAdmit)`、`(VClear n)`）。
标签序列尽量直接用原文件里的名字（`Admit.drain`、`ViewFail.schedA`、`ViewFail.schedB`）。

| 文件（`viz/text/`） | 内容 | 对应 |
|---|---|---|
| `basic.sexp`、`divert.sexp` | Basic 的完整生命周期，两处被拒；加载中提供者被 dispose | `consumer_waits`、`provider_blocked`、`diverted_obs` |
| `interleave.sexp` | 同样两个输入，第二个早来或晚来，终态一致 | 合流（示意） |
| `early.sexp`、`late.sexp`、`early_late.sexp` | #358 在 `astep` 下的两种静止结局 | `early_obs`、`early_stuck`、`late_obs` |
| `core358.sexp` | 核心拒绝这次插入，旧 fiber 移除后重试 | `core_refuses` |
| `queue358.sexp`、`early_queue.sexp` | 接纳队列下只有一种结局 | `q358_blocked`、`q358_obs` |
| `vfA.sexp`、`vfB.sexp`、`vf_core.sexp` | 核心中失败比原因活得更久，A、B 终态不同 | `core_diverges`、`core_stuck` |
| `vfA_view.sexp`、`vf_view.sexp` | 失败按视图记录，`VClear` 之后 A 与 B 一致 | `view_agrees` |

**Racket 原型（L6）。** `viz/l6.rkt` 对 `layers/L6.rkt` 做同样的事：同样的项、同样的执行与对比格式、同样的排版。
它 `require` L6，不改 L6 的任何定义。唯一要补的是累加器里 `UOp` 项的操作：L6 的 `UOp` 只记逆，
所以像 `Calculus.v` 的 ghost 记录 `oplog` 一样，在每次 `L-Step` 落地一个操作时按令牌记下它，只用于打印。

`racket viz/l6.rkt` 取 `viz/text/` 中用核心 `step` 的那些执行（`basic`、`divert`、`core358`、`vfA`、`vfB`、`interleave`、`vf_core`），
读出它们的标签序列（被拒的也算），在 L6 上重放，输出写到 `viz/text/l6/`，再逐个表达式与 Rocq 的输出比较。
现在七个文件全部相同（连排版也逐字相同）：在这些执行上，原型与演算每一步的状态、被拒的步、能走的步、终态的对比都一致。
这是一种差分测试，与 `difftest/`（Cordis 对演算）同一个想法，对象换成了原型。
`astep`、`qstep`、`vstep` 是 `errors/` 的变体，L6 没有，那几个文件不比较。

以下是网页一种。

## 1. 轨迹从哪里来

候选有三个：

| 来源 | 优点 | 问题 |
|---|---|---|
| 从 Rocq 抽取的 `step`（`difftest/calc/calculus.ml` 已有核心演算） | 状态就是演算的状态，没有第二份实现；改了规则重新抽取即可 | 已有的抽取只含核心，不含 `errors/` 的变体 |
| `layers/` 中可运行的 Racket 层（L0–L6） | 能跑，有交互 | 是另一份实现，与 `Calculus.v` 的对应要靠人保证；没有 `errors/` 的规则 |
| 真实 Cordis 的记录（`difftest/cordis/run.mjs`、`checker/`） | 看到的是实现本身 | 只有事件和快照，没有累加器、视图、目标这些演算内部的量；也画不出 Cordis 没有的规则（队列、`VClear`） |

**选第一种，并扩大抽取范围。** 新的 `viz/Extract.v` 同时抽取四个 step 函数：核心的 `step`、`Admit.v` 的 `astep`（Cordis 的接纳做法：`O-Insert` 不查冲突）、`Queue.v` 的 `qstep`（接纳队列）、`ViewFail.v` 的 `vstep`（失败按视图记录，`VClear`）。
要看的例子都在 `errors/` 里，只有这样才画得出来；而且页面上每个状态都由 Rocq 里定义的函数算出，与证明讨论的是同一个对象。
驱动 `calc/trace.ml` 只解析场景、调 step、读状态，自己不做任何判断。
Cordis 的记录以后可以作为第二种输入（见第 5 节）。

实例与 `Examples/Basic.v` 相同：键、名字、值都是自然数，唯一的服务是登记表（`Services/Registry.v`），组件以编号命名。

## 2. 画什么

每个状态画成三块：

- **fiber 树。** 每个 fiber 一张卡片，子 fiber 缩进在父 fiber 下（`parent`）。卡片上有：名字与组件名；生命周期状态（Inactive / Loading / Active / Unloading，四种颜色）；错误标记（`EUser`、`EOp`、`EUnresolved`、`EConflict`）；`disposed`；Unloading 时守卫 `held` 是否成立。
  再往下是已提交的**视图**与当前的**目标**（`target`，⊥ 表示不该运行），两者不同时标出来，因为 `L-Divert`、`L-Leave` 正是由这个差别触发的；Loading 时列出程序余下的指令（下一条高亮）；累加器从头到尾列出撤销项（`reg` 登记、`prov` 提供、`spawn` 子 fiber，头是下一个要撤的）。view 模式下另有"失败视图"（`fview`，`L-Unloaded` 记下的视图）。
- **绑定。** 每个键：pid、提供者、登记表内容。
- **此刻能走的生命周期步**（对每个名字试 `lifecycle_labels`，queue 模式加 `QAdmit`，view 模式加 `VClear`）。为空时标"静止"，这就是 `quiet`。

还有组件表本身（依赖、提供、程序）和接纳队列（queue 模式）。

## 3. 怎样逐步回放

一个调度是一串标签。页面上每栏一个调度：

- 步骤条列出全部标签，编排输入（`O-*`、`QIns`）与生命周期步用不同颜色，两个调度共有的前缀用虚线框；点任一标签跳到它之后的状态，也可用按钮或方向键。
- step 拒绝的标签（返回 `None`）照样记在轨迹里，划掉并标红，状态不变。这让"守卫挡住了这一步"（`provider_blocked`）、"核心拒绝这次插入"（`core_refuses`）、"终态再也走不动"（`early_stuck`）都能在轨迹里看到，而不只是断言。
- 当前状态中，上一步改变的部分（生命周期状态、视图、目标、程序、累加器、绑定、队列）以黄底标出；新插入的 fiber 整张卡片标出，被移除的 fiber 以虚线卡片留一步；上一步所针对的 fiber 加一圈边框。

## 4. 两个调度并排

合流说的是：同样的编排输入，不同的生命周期步交错，quiet 时终态一致（含 spawn 时在重命名意义下一致）。所以并排对比的对象是**同一组输入的两个调度**：

- 两栏各自回放，互不牵制（两个调度的长度一般不同）。
- 页面底部是**终态对比**：fiber 按组件对应（同一组件的第几个实例），绑定按键对应，比较生命周期状态、错误标记、提供者的组件与登记表内容；名字与 pid 只作参考，不参与比较，因为它们从同一个计数器取，调度不同就不同。不一致的格子标红。
- 同时检查两边的编排输入是否按顺序相同（`QIns c` 记作 `OInsert c`），只有相同时才说"结局取决于调度"。

对比的意思由场景决定：`basic-confluence` 与 `viewfail` 的 A+ / B+ 是合流成立的样子；`c358` 的 early / late 与 `viewfail` 的 A / B 是合流在某个设计下失败的见证；early / queue 并排，说明队列怎样把两种结局收成一种。

## 5. 结构与使用

| 文件 | 内容 |
|---|---|
| `Extract.v` | 实例与读状态的函数；抽取四个 step 到 `calc/calculus.ml` |
| `calc/calculus.ml`、`calc/calculus.mli` | 抽取结果，已提交 |
| `calc/trace.ml` | 驱动：读场景文件，输出 JSON 轨迹 |
| `scenarios.txt` | 场景：组件表与调度，格式见 `trace.ml` 开头的注释 |
| `build.sh` | 在 WSL 中编译驱动，生成 `traces.json` 与 `traces.js` |
| `viewer.html` | 页面：读 `traces.js`（`window.CORDIS_TRACES`），也可载入任意 `traces.json` |
| `Text.v`、`TextExamples.v`、`text.sh`、`check.rkt`、`text/` | S-表达式（第 A 节） |
| `l6.rkt`、`text/l6/` | 同样的输出，来自 Racket 原型 L6，并与 Rocq 的输出比较（第 A 节） |

改了 `theories/` 或 `errors/theories/` 之后，在仓库根目录重新抽取（Windows 或 WSL 均可）：

```sh
coqc -Q theories Cordis -Q errors/theories CordisErr viz/Extract.v
```

生成轨迹（WSL，需要 opam 的 `ocamlopt`；参数可换成别的场景文件）：

```sh
sh viz/build.sh
```

`viewer.html` 与 `traces.js` 放在同一目录，用浏览器打开即可（`file://` 下也能读 `<script src>`）。

JSON 的形状：场景数组，每个场景有 `id`、`title`、`source`、`notes`、`keys`、`comps`、`schedules`、`compare`；
每个调度有 `name`、`mode`（`core` / `admit` / `queue` / `view`）、`prefix`（共同前缀的长度）、`steps`（`label`、`ok`、`kind`、`subject`）、`states`（比 `steps` 多一个，首项是初始状态）；
每个状态有 `next`、`fibers`、`binds`、`enabled`、`quiet`，queue 模式另有 `queue`。

### 场景

| 场景 | 来源 | 看什么 |
|---|---|---|
| `basic` | `theories/Examples/Basic.v` | 一次完整的生命周期，`consumer_waits` 与 `provider_blocked` 两处被拒；`divert` 调度 |
| `basic-confluence` | 示意 | 同样两个输入，第二个早来或晚来，终态在重命名意义下一致 |
| `c358` | `errors/theories/Admit.v`、`Queue.v` | cordiverse/cordis#358：early / late 两种静止结局（`early_obs`、`early_stuck`、`late_obs`）；核心拒绝（`core_refuses`）；队列下只有一种结局（`q358_blocked`、`q358_obs`） |
| `viewfail` | `errors/theories/ViewFail.v` | 比原因活得更久的失败：核心中 A / B 不同（`core_diverges`、`core_stuck`），失败按视图记录后一致（`view_agrees`） |

各场景的终态与 Rocq 中算出的 `Example` 逐一对过。

## 6. 下一步

1. **在页面里探索。** 用 js_of_ocaml 把抽取出的 step 编译到页面里，点"此刻能走的步"就走一步，从任一状态分叉出新的调度。届时轨迹不必预先算好，并排对比也可以从同一状态出发。
2. **菱形。** 合流证明的核心是局部交换：两个都能走的步，先走哪个都能汇合。可以在某个状态上取两个能走的步，画出两条路径与汇合点，对应 `Confluence.v` 的各个情形。
3. **自动找分歧。** 对一组输入枚举调度（有界），把终态归类，挑出终态不同的最短一对，直接作为并排对比的两栏。
4. **接入 Cordis 记录。** `difftest/calc/replay.ml` 已经把 Cordis 事件映射成标签，让它也输出本页的 JSON，就能把真实 Cordis 的执行与演算的状态叠在一起看。
5. **更多场景。** spawn 与 `LRetireChild`（差异 e 的三步见证）、`O-React`、外部资源（`Resource.v`），以及 `keys/DESIGN.md` 的实例化键落地之后的键作用域。
