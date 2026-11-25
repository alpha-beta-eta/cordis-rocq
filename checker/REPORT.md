# dsh 热门插件的生命周期问题：cordis-check 第一轮报告

2026-11-24

## 摘要

我们做了一个检查工具 cordis-check，把 npm 上下载量最高的 26 个第三方 dsh 插件放在真实的 Cordis 上运行，自动找出违反汇总定理的最短调用序列。第一轮在 14 个插件上找到 25 个可重放的见证，并在真实的 dsh 宿主上复现了其中最严重的一类。

主要发现：

- **一次路由撞名，插件就再也装不回去。** dshmarket、dsh-remote、dsh-whale-widget、dsh-connect-workbuddy、dsh-qqbot 都是先登记一批路由，最后才统一登记撤销。中途一次登记失败，前面的路由就泄漏了：插件卸载后，它们仍由旧实例应答；之后再装，插件会撞在自己留下的路由上，直到宿主重启。这 5 个插件在真实宿主上全部复现。
- **dsh-windows-mcp 正常卸载就泄漏。** 它丢弃了 6 个路由登记的返回值。停用后，路由仍由旧实例应答；再启用后，新实例一条路由也登记不上。真实宿主上复现。
- **dsh-free-search 把设置写入接口让给了别的插件。** 撞名时它吞掉错误并"复用"已有登记，于是 `/mutate` 由占住这条路径的插件应答，它自己毫无察觉。真实宿主上复现。
- **7 个插件卸载后留下进程级状态**：dns 解析序、`globalThis` 上的槽、计时器、`process` 监听器。
- **两个插件争同一个服务名 `dshRemote`**，输的一方只打一条警告就继续运行。真实宿主上复现了冲突，但 checker 预测的"结果依赖安装次序"在真实宿主上没有出现：异步延迟让同一方总是赢。
- **服务重启一次，功能就静默消失。** webServer 重启后 dsh-token-diet 的 RPC 路由不再登记，skills 重启后 dsh-remote 的远端 skill provider 不再登记；两者全部 fiber 仍是 ACTIVE，不报错，只有重启插件才恢复。真实宿主上复现 (2026-11-25 补做)。checker 报的第三处 (dsh-im) 在真实宿主上判为误报。
- **补记：connection 桩补上 `rpc` 与 `fetch`。** dsh-im 的两个误报来自 connection 桩缺 `fetch`。补上后重跑，这两个误报消失，dsh-im 在 checker 里全部 ACTIVE。下文保留第一轮的数字。
- **补记：新增"提供者重启"场景 (第二轮，2026-11-25)。** 插件装上后，每个宿主服务分别撤走再提供。新得到 8 个见证，在真实宿主上确认了其中最重要的几个：dsh-free-search 在 systemPrompt 重启一次后整个插件只剩一个空壳 fiber (15 个缩成 1 个)，设置接口与工具全部消失；dshmarket 每次 webServer 重启多留一个 fiber，持续累积；token-diet 的 webServer 重启同上。dsh-image-gen 的监听器翻倍在真实宿主上被掩盖，没有复现。现在共 31 个见证，全部重放复现。见 C 类的"提供者重启"一节。
- **补记：级联重启 (第三轮，2026-11-25)。** 宿主桩现在按真实宿主的服务依赖图声明 inject。依赖图由驱动插件从 dsh 0.2.2-rc.5 读出，共 106 个服务。这样撤走一个服务时，Cordis 会像真实宿主一样，连带卸载依赖它的宿主服务和插件。结果有三点：
  - dsh-image-gen 的误报消失了。image-gen inject 了 `tools`，而 `tools` inject 了 `systemPrompt`，所以 system-prompt 重启时整个插件跟着重来。真实宿主上读 fiber 的 epoch 确认了这一点。
  - 新增两个 webStartup 重启的见证：dshmarket 多一个 fiber，free-search 多一个 PENDING fiber。两者在真实宿主上原样复现。
  - 这次全量重跑中 dsh-ops 全部激活，顺带多出一个故障注入见证。
  
  现在共 33 个见证，除去一个已知受时序影响的见证，全部重放复现。
- **补记：CJS 的 `require` 桩 (第四轮，2026-11-25)。** checker 原来只接管 ESM 的 `import`，dsh-mobile-plugin 用 `require('ws')` 因而装不上。现在 `require` 也做同样的映射与换桩，dsh-mobile-plugin 内外两层全部 ACTIVE，得到 5 个见证：它正常卸载就残留 286 条路由和 2 条升级路由。外壳把共享的 `webServer.register` 换成自己的包装，给每个路径挂一个稳定分派器，卸载时却从不撤销这些分派器，卸载后它们继续把请求转给旧代的处理器 (A′ 类)。真实宿主上原样复现：停用后 fiber 已是 DISPOSED，286 条路由和 2 条升级路由仍挂着停用前的处理器，插件的路径照旧回它自己的 401，而宿主对不存在的路径回 404；再启用后新实例的分派器全部撞名，没有任何报错，请求继续由已卸载实例转发。checker 另报的"webServer 重启后多一个 fiber"在真实宿主上没有复现，判为误报。顺带，dsh-plugin-wallpaper-engine 从启动自检失败变为 ACTIVE，没有新问题。现在共 38 个见证。重放时 37 个复现；没复现的是 dsh-ops 的那个，原因是它在这台机器上停在 LOADING (换回旧代码也一样)。
- **补记：dsh-ops 的故障注入见证在真实宿主上确认 (2026-11-25)。** 驱动先占住 dsh-ops 要登记的提示段名 `dsh-ops:repository-tooling:mode-ptc`，真实的 `systemPrompt.section` 因重名抛错，一个子 fiber 失败。撤掉占位再启用后，段名从 `mode-ptc`、`mode-ptc:2` 变成 `mode-ptc:3`、`mode-ptc:4`，与见证一字不差；之后每正常重启一次再涨 2 (`:5`、`:6`)，不会回落。按 `ctx.root` 共享的序号只在整族 row 清空时归零，而失败那次 apply 的 row 永远留着。至此全部类别的见证都在真实宿主上检查过。
- **补记：B 类在真实宿主上确认 (2026-11-25)。** 驱动在宿主进程里读进程级状态，与空宿主对照。8 个插件中 7 个复现 (dns 解析序、`globalThis` 槽、`process` 监听器)，dsh-prime-memory 的 `beforeExit` 监听器在真实宿主上同样随重启累积；dsh-pet 的计时器不复现。见 B 类一节。
- **补记：落定等到走出 LOADING (第五轮，2026-11-25)。** 原来快照前只等几轮事件循环，apply 里稍慢的异步加载就会被判成 LOADING，结果随机器负载变化。现在每步最多等 2 秒，超时的 fiber 记为卡住、不再等。dsh-agent-compare、dsh-ops、dsh-prime-memory、ds-harness-remote 都全部 ACTIVE，dsh-ops 的见证重新复现，另多出 12 个见证：dsh-prime-memory 的 11 个都是已知的 `beforeExit` 监听器在重装或重启后累积；ds-harness-remote 在 apply 时只读一次 `webServer`，webServer 晚到时一个 fiber 以 `without inject` 失败，13 个工具和 `dshRemote` 服务都不登记，重启后丢前缀路由 (与 token-diet 同类)。这两处在真实宿主上原样复现，都静默，只有重启插件才恢复。现在共 50 个见证，重放全部复现。

代码与全部见证在本目录 (`checker/`)，一次完整检查约 4 分钟。逐插件的细节见 [FINDINGS.md](FINDINGS.md)。

## 背景

dsh (DeepSeek Harness) 的插件运行在 Cordis 之上。cordis-rocq 在 Rocq 中形式化了 Cordis 的生命周期演算，并证明了一个汇总定理 (`theories/Summary.v`)：只要服务与插件满足相应的前提，就有下面四层保证。

| 层 | 保证 | 插件侧的前提 (节选) |
| --- | --- | --- |
| 0 安全 | 良构，提供者比依赖者活得久 | 不猴补服务、不动进程全局、不挂到别人的 ctx 上 (S1–S3) |
| 1 活性 | 生命周期步终止，静止即稳定 | 启动程序有界，依赖无环 (L1–L2) |
| 2 恢复 | 卸载后的状态与从未安装不可区分 | 每个效应都登记在 fiber 上，中途抛错也不例外；登记名不撞 (R1–R4) |
| 3 合流 | 干净终态与调度无关，并等于静态组装 | 启动分支不依赖调度，逆与状态无关 (C1–C5) |

此前我们对这 26 个插件做过一轮人工审计 ([../docs/PLUGIN-AUDIT.md](../docs/PLUGIN-AUDIT.md))，只读源码，逐条判定每个前提。审计给出的是判定，而不是能拿给插件作者看的反例。这一轮的目标是：对每个问题，给出一条具体的、可重放的调用序列。

## 方法

cordis-check 做具体执行加有界枚举，属于欠近似：报出的问题 (相对于宿主桩) 一定真实存在，没报的不等于没有。它与 Rocq 侧的证明互补：证明说满足前提就有保证，checker 找出不满足前提的真实插件会在哪里出事。

```mermaid
flowchart LR
  A["插件 + 宿主桩<br/>真实 Cordis 4.1.0<br/>owned / bare 登记"] --> B["枚举调用序列<br/>卸载再装、第 k 次抛错<br/>服务晚到、两种次序"]
  B --> C["定理判据<br/>第 2 层：卸载即复原<br/>第 3 层：与调度无关"]
  C --> D["稳定性门槛<br/>再判定两次<br/>LOADING 判无结论"]
  D --> E["见证<br/>最短序列，可重放<br/>25 个 / 14 个插件"]
  E --> F["真实 dsh 宿主<br/>驱动插件，真实撞名<br/>只有回环网络"]
```

通过稳定性门槛的候选成为见证；其中有代表性的，再在真实的 dsh 宿主上用真实的触发方式复现。

**运行环境。** 用 dsh 自己 vendored 的 Cordis (4.1.0)。宿主服务用桩代替，只模拟登记语义，照 dsh 源码写。最要紧的是区分两种登记方式：

- **owned**：宿主经调用者的 `ctx.effect` 登记，卸载时自动撤销，如 `tools.register`。
- **bare**：宿主只返回一个裸 disposer，不归任何 fiber，如 `webServer.register`。插件不自己登记它的逆，就会泄漏。

**动作与演算规则。** 每条调用序列都由演算中的动作组成：

| 动作 | 演算规则 |
| --- | --- |
| `install(p)` / `dispose(p)` | O-Insert / O-Dispose |
| 服务出现 / 撤走 | 提供者的 O-Insert / O-Dispose |
| 第 k 次宿主调用抛错 | apply 在第 k 个 L-Step 处 L-Fail |

**四种场景与判据。**

1. 装上、卸载、再装：卸载后应与从未安装相同，再装应与第一次装上相同 (第 2 层)。
2. 故障注入：插件在 apply 中调用的每个宿主方法、每个 k，让第 k 次调用抛错，再卸载、再装 (R1)。
3. 服务晚到：每个宿主服务分别在插件之后才出现，落定状态应与服务先到时相同 (C2)。
4. 安装次序：两个插件两种安装次序，落定状态应相同 (合流、R3)。

比较的是一份规范化的快照：宿主桩上的登记表、Cordis 的服务归属与监听器次序、fiber 状态、进程级状态。令牌与 fiber 编号不进快照，对应 `Observe.v` 中的 ≃。

**防误报。** 每个候选见证再判定两次，三次差异一致才保留；有 fiber 停在 LOADING 时，依赖时序的比较判无结论；再装时用新的安装编号，把旧实例留下的东西和新实例的登记分开。每条序列在单独的进程里跑，网络、子进程、`process.kill` 一律拦下。

**真实宿主复现。** 用 npm 发布版 dsh 0.2.2-rc.5，把插件和一个驱动插件装进全新的 profile。驱动插件通过 loader 停用、启用插件，发真实的 HTTP 请求，并按处理器函数的身份区分新旧实例。它不打补丁：需要故障时，先占住插件要用的一条路由。宿主跑在只有回环接口的网络命名空间里。工具见 [real/](real/)。

## 结果总览

26 个插件中，24 个能在 checker 里装上，共得到 25 个见证，涉及 14 个插件。每个见证都重放复现。另外 2 个插件无结论：dsh-mobile-plugin 用 CJS 的 `require` 加载缺失的包 (第四轮已覆盖)，dsh-archive-manager 在 dsh 的存储校验上失败。

| 类别 | 层 | 插件 | 真实宿主 |
| --- | --- | --- | --- |
| A. 分批登记的路由中途抛错后泄漏，插件装不回去 | 2 (R1) | dsh-whale-widget、dshmarket、dsh-remote、dsh-connect-workbuddy、dsh-qqbot、dsh-windows-mcp、dsh-free-search | 6 个复现；free-search 不泄漏，但会让出路由 (R3) |
| A′. 不注入故障，正常卸载就残留路由 | 2 (R1) | dsh-windows-mcp；dsh-mobile-plugin (第四轮) | 两者都复现 |
| B. 卸载后进程级状态未恢复 | 0 (S3) / 2 (R2、R4) | dsh-whale-widget、dsh-session-superagent、dsh-cost-meter、ds-harness-remote、dsh-pet、dsh-prime-memory、dsh-im | 7 个复现；dsh-pet 的计时器不复现 |
| C. 结果依赖次序或时机 | 3 (C2、R3) | ds-harness-remote + dsh-remote、dsh-token-diet、dsh-remote、dsh-im (低置信) | `dshRemote` 冲突复现，次序依赖未复现；token-diet、dsh-remote 的服务晚到复现；dsh-im 不复现 (误报) |

完整的逐插件报告与见证 JSON 在 [reports/](reports/) 与 [witnesses/](witnesses/)，每个见证可用 `sh check.sh replay` 重放。

## A 类：一次路由撞名，插件就再也装不回去

dsh 的 `webServer.register` 只返回一个裸 disposer，撞名时抛错。这些插件的共同写法是：先按顺序登记一批路由，把返回值收进数组，最后才用一个 `ctx.effect` 登记"全部撤销"。第 k 条一旦抛错，前 k−1 条就没有人负责撤销了。

checker 的最短序列只有四步：

1. 第 k 次 `webServer.register` 抛错 (L-Fail)
2. `install(p)` (O-Insert)：内层 fiber 失败，前 k−1 条路由已登记
3. `dispose(p)` (O-Dispose)：这 k−1 条路由仍在，由旧实例的处理器应答
4. 再 `install(p)`：第一条路由就撞名，直到宿主重启都装不回去

| 插件 | 登记方式 (源码位置) | checker：有残留的故障点 / 最多残留 | 真实宿主 |
| --- | --- | --- | --- |
| dshmarket 1.80.0 | 63 条写在一个数组字面量里 (`lib/routes.js:3271`) | 62/63，62 条 | 复现 |
| dsh-remote 1.3.1 | `guarded.map(route => …register(route))` (`lib/http-transport.js:171`) | 43/44，43 条 | 复现 |
| dsh-whale-widget 0.4.2 | `disposers.push(registerRoute(…))` ×26 (`lib/index.js:895`) | 25/26，25 条 | 复现 |
| dsh-connect-workbuddy 5.31.0 | 一个 `ctx.effect` 的效应体内逐条登记 (`lib/index.js:13226`) | 15/16，15 条 | 复现 |
| dsh-free-search 0.9.82 | `.map(route => registerOnce(…))` (`lib/index.js:2476`) | 9/10，9 条 | 不泄漏，但让出路由 |
| dsh-windows-mcp 0.2.11 | 6 条登记的返回值直接丢弃 (`lib/index.js:1409`) | 5/6，且正常卸载就残留 6 条 | 复现 |
| dsh-qqbot 0.5.5 | 5 条写在一个数组字面量里 (`lib/setup/bind-routes.js:65`) | 4/5，4 条 | 复现 |

**真实宿主上的记录 (dsh-whale-widget)。** 驱动插件先占住它的第 2 条路由 `/dsh-whale/rua.gif`，相当于另一个插件或旧版本占了同一路径：

| 步骤 | 插件状态 | `/dsh-whale/image.png` |
| --- | --- | --- |
| 正常停用 | DISPOSED | 未登记 (正常停用是干净的) |
| 路径被占时启用 | 内层 FAILED：`duplicate exact route "/dsh-whale/rua.gif"` | 已登记，handler#2 |
| 再停用 | DISPOSED | 仍登记 handler#2，HTTP 401 (不是 404) |
| 撤掉占位后再启用 | 内层 FAILED：`duplicate exact route "/dsh-whale/image.png"` | 仍是 handler#2 |

dshmarket、dsh-remote、dsh-connect-workbuddy、dsh-qqbot 的记录与此同构。停用后旧处理器的应答分别是 401、401、200 (`{"status":"signed-out",…}`) 和 200 (`{"phase":"failed",…}`)。

**dsh-windows-mcp 不需要任何故障。** 停用后 fiber 已是 DISPOSED，`/dsh-windows-mcp/state` 仍返回 200 和状态 JSON；对照的不存在路由返回 404。再启用后，路由上挂的仍是停用前那个处理器函数，新实例的 6 次登记全部撞名，被插件吞成了警告。

**dsh-free-search 是例外。** 它的 `registerOnce` (`lib/index.js:1552`) 吞掉撞名错误，并"复用"已有的登记，所以撞名不会泄漏。但路径被占时，它全部 fiber 都是 ACTIVE，`/api/dsh-free-search-settings/mutate` 却由占位者应答 (HTTP 418)。它的设置写入接口就这样让给了别的插件，这是 R3 (相遇受控) 被违反。R1 泄漏仍在，只是要撞名以外的失败才触发。

**这在实际使用中发生过。** dsh-connect-workbuddy 的源码注释提到了 issue #86：热重载时因重复注册同一路径而抛错，后面的路由全部注册不上。它的修法是把登记放进一个 `ctx.effect`，但效应体在中途抛错，没来得及返回清理函数，问题依旧。

**修法。** 每登记一条，就立即登记它的逆，也就是演算里 `L-Step` 压入撤销项的方式：

```js
for (const route of routes) ctx.effect(() => ctx.webServer.register(route))
```

checker 的自测插件 `fixtures/tidy.mjs` 就是这样写的，所有故障点都判为干净。

## B 类：卸载后进程级状态未恢复

7 个插件卸载后留下了 Cordis 管不到的进程级状态。它们都是单步见证：装上再卸载，状态就不同于从未安装。

| 插件 | 卸载后残留 | 归类 |
| --- | --- | --- |
| dsh-whale-widget | 模块加载时 `dns.setDefaultResultOrder('ipv4first')`，影响整个宿主进程 | R4 |
| dsh-session-superagent | `globalThis` 上 3 个 Symbol 槽 (activeRoutes、inFlight、timers) | S3 |
| dsh-cost-meter | `globalThis` 上 `Symbol(dsh-cost-meter.billion-context.peers.v1)` | S3 |
| ds-harness-remote | `globalThis` 上 `Symbol(ds-harness-remote.hmr-safe-settings-pump)` | S3 |
| dsh-pet | 一个计时器 | R2 |
| dsh-prime-memory | `process.on('beforeExit')` 监听器 | R2 |
| dsh-im | `process.on('exit')` 监听器 | R2 |

**真实宿主上的确认 (2026-11-25)。** 驱动在宿主进程里读同一组进程级状态，与只装驱动的空宿主对照，再逐个停用、启用插件。上表除 dsh-pet 外全部复现：dns 解析序在空宿主里是 `verbatim`，装上 whale 后变成 `ipv4first`，停用后不变；各个 `globalThis` 槽停用后都还在 (dsh-cost-meter 停用时撤掉了另外两个槽，留下的正好是 checker 报的那一个)；dsh-prime-memory 的 `beforeExit` 监听器停用后还在，再启用变成 2 个；dsh-im 的 `exit` 监听器是模块加载时登记的，停用后还在，但不累积。dsh-mobile-plugin 卸载后留下的 3 个全局槽 (第四轮) 也复现。dsh-pet 停用时撤掉了它的监听器和计时器，再启用不累积，不复现。ds-harness-remote 打包的 zod 写的 `__zod_global*`，空宿主里本来就有，不算它的残留。

这些不单独是大 bug，但会随热重载累积，并把一个插件的选择强加给整个宿主 (如 dns 解析序)。它们对应审计中"越出模型"的那一类：模型只保证登记在 fiber 上的效应，这些效应从一开始就没有登记。

## C 类：次序与时机

第 3 层要求结果与调度无关。checker 找到了 4 处违反，但真实宿主的结果提醒我们：这一层的见证对宿主桩的异步时序很敏感。

**`dshRemote` 冲突 (R3)。** ds-harness-remote 与 dsh-remote 都 `ctx.provide('dshRemote')`。输的一方收到 `SERVICE_PROVIDE_CONFLICT`，只打一条警告就继续运行。

- checker：服务归先装的一方，两种次序结果相反。
- 真实宿主：两种次序下服务都归 dsh-remote。ds-harness-remote 的 `provide` 排在一段异步激活之后，总是晚到。checker 的通用桩让这段激活提前完成了。

结论：两个插件同装时，ds-harness-remote 的远程服务**总是**拿不到 `dshRemote`，而且只留一条警告。从模型的角度看这仍是 R3 被违反，只是"调度"由 I/O 延迟决定，而不是由安装次序决定。

**服务晚到 (C2)。** checker 报了三处，真实宿主上复现了两处 (2026-11-25 补做)。真实宿主里让服务晚到不需要打补丁：停用提供服务的 loader 条目，期间启用插件，再启用提供者。另外也试了更常见的"提供者重启，插件不动"。

| 插件与服务 | checker | 真实宿主 |
| --- | --- | --- |
| dsh-remote，`skills` | 某个事件上少一个监听器 | **复现**：skills 晚到或重启后，dsh-remote 的远端 skill provider 都没有重新登记，插件全部 ACTIVE、不报错；重启插件才恢复 |
| dsh-token-diet，`webServer` | `/token-diet` 路由永远不登记 | **复现，而且更严重**：webServer 正常重启一次，`/token-diet` 就没了，客户端从此连不上它的 RPC；重启插件才恢复 |
| dsh-im，`sessionController` / `workspaceController` | 晚到时反而激活成功 | **不复现，判为误报**：插件用 `ctx.inject` 等这两个服务，缺席时内层 fiber 停在 PENDING，出现后激活，与先到时相同。checker 里"先到时失败"是因为 connection 桩缺 `fetch`，14 个通道全部激活失败。桩补上后 checker 也不再报 |

dsh-remote 的根源与 checker 的判断一致：`registerRemoteSkills` (`lib/remote-skills.js:299`) 在 apply 时 `ctx.get('skills')` 读一次，不在就不登记。

token-diet 的根源完全在插件侧。它先试 `connection.rpc.handle`，但这个方法在效应体内读 `owner.webServer` (`client/connection/src/rpc-host.ts:273`)，要求调用者 inject 了 webServer；token-diet 没有，于是抛出 `cannot get property "webServer" without inject`，插件退到自己登记的 `/token-diet` 路由 (`lib/host/rpc.js:318`)。这条退路只在 apply 时读一次 webServer，此后不再响应它的出现。真实宿主上对 `/token-diet` 发 GET 得到 405，是退路自己的方法检查 (走 connection 时是 401)，可以印证这一点。

> **更正 (2026-11-25)。** 上一版本节说 token-diet 走的是 `connection.rpc.handle`，并推测凡经它登记、又不 inject webServer 的插件都会在 webServer 重启时丢通道，"一半是宿主的问题"。这不对：不 inject webServer 根本过不了 `rpc.handle`；inject 了的调用者会随 webServer 重启并重新登记。宿主自己的包都不用 `rpc.handle` (gateway 用 `/api` 上的 `rpc.intercept`，而 `/api` 由 connection 在 `ctx.inject(['webServer'])` 内挂载，会随 webServer 重新挂载)。26 个插件中用 `rpc.handle` 的有 4 个：ds-harness-remote、dsh-mnemon、dsh-prime-memory、dsh-token-diet；dsh-prime-memory 在源码注释里写明了要为此 inject webServer。checker 同样在没有 inject 时抛错，所以 checker 里的 token-diet 也走退路，与真实宿主一致。

逐步记录见 [FINDINGS.md](FINDINGS.md) 的"在真实宿主上的复现"一节，场景在 `real/scenarios/` 下。

**提供者重启 (C2，第二轮)。** 上面的真实宿主实验说明，"提供者重启"比"服务晚到"更常见，后果也更重，所以 checker 加了这种场景：插件装上后，每个宿主服务分别撤走再提供 (提供者的 O-Dispose、O-Insert)，落定状态应与重启前相同。为此桩的服务实例被卸载时会清空它名下的登记表，与真实宿主里新实例从空表开始一致。

| 插件与服务 | checker | 真实宿主 |
| --- | --- | --- |
| dsh-free-search，`systemPrompt` / `tools` / `settings` / `web` | 重启任一个，插件的全部工具、提示段、设置接口、14 个子 fiber 都消失 | **复现**：system-prompt 重启一次，插件从 15 个 fiber 缩成 1 个 ACTIVE 的空壳，`/api/dsh-free-search-settings/*` 不再登记 |
| dsh-token-diet，`webServer` | `/token-diet` 消失 | **复现** (见上一节) |
| dshmarket，`webServer` | 多出一个 ACTIVE fiber | **复现，且累积**：webServer 每重启一次多一个，4、5、6、7 |
| dsh-image-gen，`systemPrompt` | 两个 credentials 事件上的监听器各翻一倍，多一个 fiber (第三轮级联后不再报) | **不复现**：重启两次，监听器仍各 1 个；原因见下 |
| dsh-free-search，`webServer` / `webStartup` | 多一个停在 PENDING 的 fiber | **复现** (第三轮)：web-startup 重启后多一个 PENDING fiber，路由重新登记 |
| dshmarket，`webStartup` | 多出一个 ACTIVE fiber (第三轮) | **复现**：web-startup 重启后 4 个变 5 个 (它连带 webServer 重启) |

dsh-free-search 的原因是 apply 开头的重入保护 (`lib/index.js:1546`)：它用一个 `WeakSet` 记下跑过 apply 的 ctx，同一个 ctx 再来就直接返回。注释说这是为了挡住 rc.2 启动时"未 dispose 的重入"。可 Cordis 在被 inject 的服务 (`web`、`settings`、`tools`、`systemPrompt`) 重新提供时，正是先撤销 fiber 的全部效应，再在**同一个** ctx 上重跑 apply，于是插件撤得干干净净，又什么都不登记。宿主里任何一个这样的服务因配置变更或热重载重启一次，免费搜索就整个消失，fiber 仍是 ACTIVE，用户看不到任何报错。

dsh-image-gen 的问题在源码里确实存在：`ctx.inject(["systemPrompt"], (promptCtx) => { ctx.inject(["credentials"], …) })` 在回调里用了外层的 `ctx`，内层 fiber 不随 systemPrompt 的 fiber 撤销，每重启一次就多挂一份。真实宿主上没有复现，原因是级联重启：

- 插件顶层 inject 了 `tools`、`attachments`、`credentials`；
- 宿主的 `tools` 服务自己 inject 了 `systemPrompt`。

所以 system-prompt 重启时 `tools` 跟着重启，插件整棵 fiber 一起重来，外层 `ctx` 上多挂的那份也随之撤销。真实宿主上，插件根 fiber 的 epoch 在重启后从 `0:41:14:26` 变为 `0:118:14:26`，变的正是 `tools` 的实例编号。第二轮的 checker 一次只重启一个服务，没有这种连带，所以把这个潜在问题暴露了出来。它是真实的写法错误，只是在 dsh 当前的服务依赖下不会触发。

dshmarket 多出的 fiber 来源还没在源码里定位到。

**级联重启 (第三轮)。** 真实宿主里，一个服务的提供者本身也 inject 别的服务：`tools` inject 了 `systemPrompt`，`webServer` inject 了 `webStartup`，`connection` inject 了 `credentials` 与 `webStartup`。所以重启一个服务会沿依赖图连带重启别的服务。

为此驱动插件新增 `graph` 步骤：从真实宿主的服务表读出每个服务的提供者，以及提供者 fiber 链上每层的 inject。`real/make-graph.mjs` 把结果整理成 `lib/host-graph.json`。checker 的宿主桩按这张图的传递闭包 inject，只取场景里会出现的服务，于是 Cordis 自己完成级联。

闭包要穿过 checker 没有的中间服务。例如 `subagents` 依赖 `workingDirectory`，`workingDirectory` 又依赖 `systemPrompt`，而 checker 的宿主里没有 `workingDirectory`。

全量重跑的结果：

- 第二轮的 dsh-image-gen 误报消失。
- 新增的 webStartup 见证在真实宿主上原样复现 (`real/scenarios/cascade.json`)：
  - dshmarket 4 个 fiber 变 5 个；
  - free-search 多一个 PENDING fiber。
- 其余第二轮见证都还在。

这一类对应审计中 C2 的主体：插件在启动时读一次未注入的服务，按它在不在决定登记什么，之后不再响应它的出现。模型中的可选依赖扩展 (`theories/Ext/Optional.v`) 正是为这种需求设计的。

## 与人工审计的对照

checker 复现了审计的主要判定，补出了审计漏记的同类问题，也有 3 处走不到。

| | 内容 |
| --- | --- |
| 复现 | whale-widget 的 R1 与 dns；windows-mcp 的路由泄漏；session-superagent 的 `globalThis`；`dshRemote` 撞名；token-diet 的 C2；dshmarket"缺口只在中途抛错" |
| 补充 | 每个 R1 问题的具体故障点与残留条数；"从此装不回去"这一后果；dsh-remote、free-search、connect-workbuddy、qqbot 的同类 R1；free-search 让出路由；cost-meter、ds-harness-remote 的 `globalThis` 槽；pet、prime-memory、dsh-im 的进程级残留 |
| 走不到 | dsh-im 与 dsh-qqbot 的 `approval/request` 中间件次序 (要等 IM 通道真正连上)；cost-meter 对 `ChildProcess.prototype.spawn` 的常驻补丁 (排在一次失败的 typert 注册之后)；whale-widget 的 index-inject 行 (只在桌面端宿主上出现) |

审计与 checker 的分工很自然：审计读源码，能看到所有分支；checker 只看到实际跑到的分支，但给出的是可以拿给插件作者重放的序列。

## 有效性与局限

- **结论相对于桩。** 有专门桩的只有 7 个宿主服务，其余 40 多个用通用桩代替。通用桩会改变插件走的分支和异步时序：`dshRemote` 一例就是这样。所以第 3 层的见证要在真实宿主上确认后再下结论。
- **依赖图来自一个版本。** 级联重启用的服务依赖图是从发布版 0.2.2-rc.5 读出的 (`lib/host-graph.json`)。宿主升级后应重新生成。checker 只按服务重启，不模拟一个 loader 条目同时提供几个服务的情形。
- **落定有上限。** 每步最多等 2 秒让 fiber 走出 LOADING，更慢的仍判无结论。dsh-mobile-plugin 在满载的并行池里结果抖动，它的见证以单独运行为准；它的两个提供者重启见证只差计时器与 TCP 句柄的计数，单独运行时也时稳时不稳。
- **有一个见证受时序影响。** `pair-ds-harness-remote-dsh-remote` 在 checker 里约五次有一次不复现，级联前后都是这样。ds-harness-remote 的 `provide` 排在一段文件 I/O 之后，与另一个插件的装载赛跑。
- **欠近似。** 没有见证不等于没有问题。故障点按调用次数穷举，服务晚到只试单个服务，安装次序只试两两。
- **覆盖缺口。** 24 个能装上的插件中，有 5 个没有任何 ACTIVE 的 fiber (缺服务、配置校验、启动自检等)，另有 5 个只部分激活。connection 桩补全后，其中 deep-view 与 dsh-im 已全部 ACTIVE，没有 ACTIVE 的降为 3 个。第三轮重跑时 dsh-agent-compare 与 dsh-ops 也全部 ACTIVE；它们单独运行时一直如此，第一轮的 LOADING 出现在并行池满载的那次运行里。对它们，checker 只覆盖了走得到的那一段。
- **真实宿主的版本。** checker 用的是 dsh 源码 `fcc0ad46` (2026-11-04)，真实宿主用的是发布版 0.2.2-rc.5 (2026-11-18)。本报告涉及的宿主语义 (裸 disposer、撞名抛错) 在两者中一致。
- **只看宿主端。** 浏览器客户端部分未覆盖。
- **网络。** windows-mcp 与 whale 两次真实宿主运行是在加上网络隔离之前做的，其余都在只有回环接口的命名空间里运行。

## 建议与下一步

**给插件作者。** A 类的修法是统一的：每登记一条就立即登记它的逆。可以给 6 个插件分别提 issue，附上真实宿主上的复现步骤。free-search 还应该在撞名时拒绝启动，而不是"复用"别人的路由。这是对外的动作，需要先确认。

**给宿主与 Cordis。** 两个改动能从源头消除 A 类：

- `webServer.register` 等登记接口改为经调用者的 `ctx.effect` 登记 (与 `tools.register` 一致)，卸载时自动撤销。
- 一个效应体中途抛错时，已经进入它的登记也应被撤销。这正是演算里 L-Fail 的语义。

`dshRemote` 一例则支持审计中的建议：服务名冲突应在插入时拒绝，而不是由插件吞错后继续运行。

服务晚到与提供者重启这两类的修法都在插件侧：

- dsh-remote 用 `ctx.inject(['skills'], …)` 代替 apply 时的一次 `ctx.get`；
- token-diet 声明 inject `webServer` (或把退路放进 `ctx.inject(['webServer'], …)`)，这样 `rpc.handle` 能用，退路也会随 webServer 重新登记；
- dsh-free-search 去掉 apply 的重入保护，或者至少不按 ctx 判断"已经跑过"。Cordis 在被 inject 的服务重新提供时，会先撤销 fiber 上的全部效应，再在同一个 ctx 上重跑 apply，这不是需要防的重入。

宿主侧可以考虑的是：fiber 因依赖重启而重跑 apply 时给一个新的 ctx，或者在文档里写明会复用 ctx。dshmarket 源码注释里就假定了"新的 ctx"，与实际行为不符。

**checker 本身。**

- 给 typert 与 IM 通道写专门的桩，走到 cost-meter 的原型补丁与 `approval/request` 的次序问题。
- ~~支持 CJS 的 `require` 桩，覆盖 dsh-mobile-plugin。~~ 已完成 (2026-11-25，第四轮)：dsh-mobile-plugin 全部 ACTIVE，5 个见证。
- ~~落定改为等到没有 LOADING 的 fiber (设上限)。~~ 已完成 (第五轮)。
- ~~在真实宿主上确认 dsh-mobile-plugin 的卸载残留。~~ 已完成 (2026-11-25)：卸载残留复现，重启累积不复现；ds-harness-remote 的两个 C2 也复现。
- ~~把 C 类其余见证放到真实宿主上确认。~~ 已完成 (2026-11-25)：两处复现，一处误报。
- ~~connection 桩补上 `rpc`，让 checker 走真实宿主走的那条路径。~~ 已完成 (2026-11-25)，连同 `fetch`：dsh-im 的两个误报消失。
- ~~增加"提供者重启"场景。~~ 已完成 (2026-11-25)。
- ~~按真实的依赖图做级联重启。~~ 已完成 (2026-11-25，第三轮)：dsh-image-gen 的误报消失，webStartup 的两个新见证在真实宿主上复现。
- 增加自由搜索与最短化，覆盖三种固定场景以外的序列。

**论文。** 这一轮的结果可以作为论文实证部分的骨架：定理给出前提与保证，人工审计给出前提在真实插件中的分布，checker 给出违反前提的具体后果，真实宿主复现给出端到端的证据。通用桩改变异步时序一事，也值得在"威胁有效性"一节讨论。
