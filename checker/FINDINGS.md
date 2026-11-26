# cordis-check 第一轮结果：26 个热门 dsh 插件

对象与 [../docs/PLUGIN-AUDIT.md](../docs/PLUGIN-AUDIT.md) 相同：npm 上月下载量最高的 26 个第三方 dsh 插件，用 2026-11-23 解压的版本。运行环境：

- dsh 提交 `fcc0ad46` (2026-11-04)；
- Cordis 用 dsh vendored 的 4.1.0；
- 宿主服务 50 个，其中 7 个有专门的桩：webServer、tools、systemPrompt、settings、credentials、connection、loader。

方法见 [README.md](README.md)。每个插件的完整报告在 [reports/](reports/)，见证 (可重放的调用序列) 在 [witnesses/](witnesses/)。

## 总览

- 26 个插件中 24 个能在 checker 中装上，另外 2 个无结论：
  - dsh-mobile-plugin 用 CJS 的 `require('ws')`，桩只接管 ESM 的 import (第四轮已覆盖，见下)；
  - dsh-archive-manager 在 dsh 的 storage domain 校验上失败。
- 共 **25 个见证，涉及 14 个插件**。
  - 每个见证在写入前都另判定两次，三次的差异集合相同才保留；
  - 写入后再统一重放一遍，25 个全部复现。
  - 补记 (2026-11-25)：connection 桩补上 `rpc` 与 `fetch` 之后重跑，dsh-im 的两个服务晚到见证消失 (真实宿主上也判为误报)，其余 23 个照旧，重放全部复现。下文保留第一轮的数字，变化处另行注明。
  - 补记 (第二轮)：新增"提供者重启"场景，多出 8 个见证，共 31 个。
  - 补记 (第三轮)：宿主桩按真实宿主的服务依赖图声明 inject，重启沿依赖级联。dsh-image-gen 的重启见证消失 (真实宿主上本就不复现)，多出 webStartup 重启的两个见证和 dsh-ops 的一个故障注入见证，共 33 个。
  - 补记 (第四轮，CJS 的 `require` 桩)：dsh-mobile-plugin 能装上了，内外两层 fiber 全部 ACTIVE，多出 5 个见证，共 38 个，见 A′ 一节。dsh-plugin-wallpaper-engine 的子包现在解析得到 (换成桩)，从启动自检失败变为 ACTIVE，9 条路由的全部故障点都干净；ds-harness-remote 多走到 13 次 `tools.register`，也都干净。
  - 补记 (第五轮，落定等到走出 LOADING)：原来落定只等几轮事件循环，apply 里稍慢的异步加载 (例如动态 import `@deepseek-ai/dsh-tools`，约 0.3 秒) 就会被判成 LOADING。现在每步最多等 2 秒。dsh-agent-compare、dsh-ops、dsh-prime-memory、ds-harness-remote 都全部 ACTIVE，多出 12 个见证，共 50 个，重放全部复现。新见证中 dsh-prime-memory 的 11 个同出一源 (B 类的 `beforeExit` 监听器每次 apply 加一个)，ds-harness-remote 多出两个 C2 问题，见 C 节。
- 一次完整运行 (26 个插件的检查、普查、两个 pair) 约 4 分钟，并行 16 路。加上 dsh-mobile-plugin 后约 10 分钟：它 apply 时登记 288 条路由，故障点多，且在满载的并行池里大多判为不稳定 (第四轮的见证来自单独运行)。

| 类别 | 层 | 插件 |
|---|---|---|
| A. 分批登记的路由中途抛错后泄漏，插件从此装不回去 | 2 (R1) | dsh-whale-widget、dshmarket、dsh-remote、dsh-connect-workbuddy、dsh-free-search、@tencent-connect/dsh-qqbot、dsh-windows-mcp |
| A′. 不注入故障，正常卸载就残留路由 | 2 (R1) | dsh-windows-mcp、dsh-mobile-plugin (第四轮) |
| B. 卸载后进程级状态未恢复 | 0 (S3) / 2 (R4) | dsh-whale-widget、dsh-session-superagent、dsh-cost-meter、ds-harness-remote、dsh-pet、dsh-prime-memory、@xmanrui/dsh-im |
| C. 结果依赖安装次序或服务出现的时机 | 3 (C2、R3) | ds-harness-remote + dsh-remote、dsh-token-diet、dsh-remote、@xmanrui/dsh-im (低置信，真实宿主上判为误报) |

在真实的 dsh 宿主上 (见"在真实宿主上的复现"一节)：

- A 类 7 个插件中，有 6 个用真实的路由撞名完全复现；
- dsh-free-search 的撞名不泄漏，但会把自己的设置写入接口悄悄让给占位的插件；
- A′ 复现；
- C 类的 `dshRemote` 冲突复现，但它对安装次序的依赖没有复现。

## A. 分批登记的路由：一次中途抛错，插件就再也装不回去

dsh 的 `webServer.register` 只返回一个裸 disposer，不归任何 fiber 管
(`packages/host/webserver/src/index.ts`)，撞名时抛错。

这类插件的共同写法是：先把一批 `register` 的返回值收进数组，或者用 `.map` 一次性登记，最后才用一个 `ctx.effect` 登记"全部撤销"。第 k 次登记一旦抛错，前 k−1 条路由就没有任何人负责撤销。

checker 的最短序列有三步：

```
1. 第 k 次 webServer.register 抛错         L-Fail
2. install(p)                             O-Insert
3. dispose(p)                             O-Dispose
```

结果：前 k−1 条路由在卸载后仍留在宿主里。之后再装同一个插件 (第 4 步)，第一条路由就会撞名，新实例的 fiber 进入 FAILED。在重启宿主之前，这个插件装不回去，旧实例的处理器还继续接请求。

| 插件 | 登记方式 (源码位置) | 有残留的故障点 | 最多残留 |
|---|---|---|---|
| dsh-whale-widget 0.4.2 | `disposers.push(registerRoute(…))` ×26，末尾一个 `ctx.effect` (`lib/index.js:895`, `:4919`) | 25/26 | 25 条，tapIndex 抛错时 26 条 |
| dshmarket 1.80.0 | 63 条 `registerRoute(…)` 写在一个数组字面量里 (`lib/routes.js:3271`) | 62/63 | 62 条 |
| dsh-remote 1.3.1 | `guarded.map(route => …register(route))` (`lib/http-transport.js:171`) | 43/44 | 43 条 |
| dsh-connect-workbuddy 5.31.0 | 一个 `ctx.effect` 的效应体内逐条 `disposers.push(register(…))` (`lib/index.js:13226`) | 15/16 | 15 条 |
| dsh-free-search 0.9.82 | `.map(route => registerOnce(() => …register(route)))` (`lib/index.js:2476`) | 9/10 | 9 条 |
| @tencent-connect/dsh-qqbot 0.5.5 | 5 条 `webServer.register(…)` 写在一个数组字面量里 (`lib/setup/bind-routes.js:65`) | 4/5 | 4 条 |
| dsh-windows-mcp 0.2.11 | 6 条 `scoped.webServer.register(…)` 的返回值直接丢弃 (`lib/index.js:1409`) | 5/6；见 A′ | 6 条 |

dsh-connect-workbuddy 的写法值得单独说。它已经把登记放进了 `ctx.effect`，但效应体是在中途抛错的，还没来得及返回清理函数，Cordis 无从知道前面已经登记过什么。它的源码注释提到 issue #86：热重载时因重复注册同一路径而抛错，"后面的路由全部注册不上"。这正是这一类问题在真实使用中出现过的证据。

正确的写法是演算里 `L-Step` 的做法：每登记一条就立即登记它的逆。例如每条都写成 `ctx.effect(() => ctx.webServer.register(r))`。checker 的 `fixtures/tidy.mjs` 就是这种写法，所有故障点都判为干净。

**A′. dsh-windows-mcp 不注入故障也会泄漏。** 它丢弃了 6 个 `register` 的返回值，正常卸载后 6 条路由全部残留。再装时，6 条路由都还属于已经卸载的旧实例，新实例一条也没登记上，而撞名错误被插件自己 catch 成了一条警告 (见证 `dsh-windows-mcp-unload`)。

**A′. dsh-mobile-plugin 正常卸载就残留 286 条路由和 2 条升级路由 (第四轮)。** 它的外壳做蓝绿换代：把共享的 `webServer.register` 换成自己的包装 (`lib/index.js:156`，审计记为猴补服务)，装载"一代实现"期间登记的路由都记进分发表，每个路径用原始的 `register` 挂一个稳定分派器 (`lib/shell/runtime.js:112`)，分派器的裸 disposer 存在 `httpDispatchers`/`upDispatchers` 里。换代与回滚时会撤掉多余的分派器，但卸载走的 `detach()` (`runtime.js:599`) 只卸掉当前代的 fiber，既不撤分派器，也不清空 `liveHttp`，所以卸载后这些路径仍由分派器转给旧代的处理器。再装时新实例的分派器全部撞名 (见证 `dsh-mobile-plugin-unload`)。另有 A 类的中途抛错：外壳自己的两条 `/api/relay/host-half*` 路由逐条登记，第 2 条失败时第 1 条残留；最多一次残留 287 条 (第 3 次 `register` 失败)。卸载后还留下 `globalThis` 上的 3 个槽 (B 类)，checker 还报了 webServer 或 webStartup 重启一次就多出一个 ACTIVE 的 fiber、一个 TCP 监听句柄和两个计时器 (C2)，但这两个见证在 checker 里就时稳时不稳。真实宿主上卸载残留原样复现，重启累积没有复现，见"在真实宿主上的复现"末尾。

## B. 卸载后进程级状态未恢复

真实宿主上的确认见"在真实宿主上的复现"末尾：除 dsh-pet 的计时器外全部复现；ds-harness-remote 的 zod 槽在真实宿主里本来就有。

| 插件 | 卸载后残留 | 归类 |
|---|---|---|
| dsh-whale-widget | `dns.setDefaultResultOrder('ipv4first')`，在模块加载时设置，影响整个宿主进程 | R4，与审计一致 |
| dsh-session-superagent | `globalThis` 上 3 个 Symbol 槽 (activeRoutes、inFlight、timers)；故障后再装还会多出 routeGeneration | S3，与审计一致 |
| dsh-cost-meter | `globalThis` 上 `Symbol(dsh-cost-meter.billion-context.peers.v1)` | S3 |
| ds-harness-remote | `globalThis` 上 `Symbol(ds-harness-remote.hmr-safe-settings-pump)`；另有它打包的 zod 写的 `__zod_global*` | S3 |
| dsh-pet | 一个计时器 (Timeout 句柄) | R2 |
| dsh-prime-memory | `process.on('beforeExit')` 监听器 (`dist/util/filelog.js:71`，每次 apply 一个 `process.once`，从不移除)。第五轮全部 ACTIVE 后，凡是重装或服务重启的场景都看到它累积：3 个故障注入、7 个服务重启，共 11 个见证 | R2 |
| @xmanrui/dsh-im | `process.on('exit')` 监听器 | R2 |

## C. 依赖次序与时机 (第 3 层)

- **ds-harness-remote 与 dsh-remote 同装 (R3)**：两者都 `ctx.provide('dshRemote')`。服务归先装的一方，后装的一方收到 `SERVICE_PROVIDE_CONFLICT`，只打一条警告就继续运行。见证 `pair-ds-harness-remote-dsh-remote`，两种安装次序下服务的归属正好相反。ds-harness-remote 有异步加载没有走完，所以这一对只比较了服务归属。**真实宿主上次序依赖没有复现**：两种次序下服务都归 dsh-remote，见下一节。
- **dsh-token-diet (C2)**：`webServer` 晚于插件出现时，`/token-diet` 前缀路由永远不会登记。插件在 apply 时读一次 `webServer`，之后不再响应它的出现。插件走的是自己的退路 (`lib/host/rpc.js:318`)：它没有 inject webServer，过不了 `connection.rpc.handle`。真实宿主上同样复现，而且 webServer 正常重启一次就丢路由，见下一节。
- **dsh-remote (C2)**：`skills` 晚于插件出现时，某个事件上少一个监听器。根源是 `registerRemoteSkills` (`lib/remote-skills.js:299`) 在 apply 时 `ctx.get('skills')` 读一次，不在就不登记远端 skill provider。真实宿主上复现。
- **ds-harness-remote (C2，第五轮)**：apply 时 `ctx.get('webServer')` 读一次 (`dist/index.js:112830`)，没有 inject。`webServer` 晚到时，`activateWhenCarrierReady` 以 `cannot get property "webServer" without inject` 失败，13 个 remote_* 工具、`dshRemote` 服务与前缀路由都不登记；webServer 重启一次，`/ds-harness-remote` 前缀路由就不再登记。与 dsh-token-diet 同类。两者在真实宿主上都原样复现，见下一节末尾。
- **@xmanrui/dsh-im (C2，低置信)**：`sessionController` 或 `workspaceController` 晚到时，插件激活成功并提供 `dshIm`；先到时反而激活失败。失败的原因 ("failed to activate every channel") 出在桩上：**真实宿主上没有复现**，插件用 `ctx.inject` 等这两个服务，行为正确，见下一节。确切地说，是 connection 桩缺 `fetch`：插件按 `connection.fetch` 在不在决定是否装上投递与设置的 RPC，缺了它，各通道都激活失败。桩补上 `fetch` 之后，插件在 checker 里全部 ACTIVE，这两个见证消失。

## 在真实宿主上的复现

用 npm 发布版的 dsh 0.2.2-rc.5 (Node 24.22.3) 起真实的 web 宿主，插件从 npm 装，版本与审计时相同。
由一个驱动插件执行场景，方法见 [real/README.md](real/README.md)。

宿主跑在只有回环接口的网络命名空间里。windows-mcp 与 whale 这两次是在加上隔离之前跑的：那时宿主有网络，这两个插件启动时可能做过版本检查，但不会主动上传什么。ds-harness-remote 默认会连 `https://dsh.r2049.cn` 并注册设备，所以 pair 那两次是隔离之后跑的，日志里它的连接都以 `network_error` 失败。

**A′ dsh-windows-mcp：复现。**

```
fibers   装上后            dsh-windows-mcp ACTIVE (×5)
route    装上后            已登记, handler#1
get      装上后            HTTP 200 {"enabled":null,"scope":"session",…
get      对照: 不存在的路由   HTTP 404
disable  windows-mcp-plugin
fibers   停用后            dsh-windows-mcp DISPOSED
route    停用后            已登记, handler#1
get      停用后            HTTP 200 {"enabled":null,"scope":"session",…
enable   windows-mcp-plugin
fibers   再启用后           dsh-windows-mcp ACTIVE (×5)
route    再启用后           已登记, handler#1
```

插件停用后，路由仍挂着旧实例的处理器，并且照常应答；被正确撤掉的路由应该像对照那样返回 404。再启用后挂的仍是同一个处理器函数，新实例的登记全部撞名，被插件吞成了警告。

**A dsh-whale-widget：复现。** 驱动先占住 whale 的第 2 条路由 `/dsh-whale/rua.gif`：

```
route    停用后            未登记                       (正常停用是干净的)
squat    /dsh-whale/rua.gif
enable   dsh-whale-widget
fibers   撞名后启用          … FAILED: webserver: duplicate exact route "/dsh-whale/rua.gif"
route    撞名后启用          /dsh-whale/image.png 已登记, handler#2
disable  dsh-whale-widget
fibers   再停用后           whale-balance-widget DISPOSED
route    再停用后           /dsh-whale/image.png 已登记, handler#2
get      再停用后           HTTP 401                     (旧实例的处理器在应答, 不是 404)
unsquat  /dsh-whale/rua.gif
enable   dsh-whale-widget
fibers   撤掉占位再启用      … FAILED: webserver: duplicate exact route "/dsh-whale/image.png"
```

这和 checker 的见证 `dsh-whale-widget-fault-webServer.register-2` 一一对应：一次撞名之后，第一条路由泄漏；占位撤掉之后插件仍然装不回去，这次是撞在它自己留下的那条路由上，要等宿主重启才能恢复。

**A 类其余 5 个插件**：用同一个场景 (`make-collision.mjs` 生成)，先占住插件的第 2 条路由，再启用，然后停用，撤掉占位，再启用。这 5 次都在网络隔离下运行。

| 插件 | 占住的路由 | 撞名后启用 | 停用后第 1 条路由 | 撤掉占位再启用 | 结论 |
|---|---|---|---|---|---|
| dshmarket 1.80.0 | `/dsh-market/telemetry` | 内层 fiber FAILED | 仍登记，旧处理器应答 HTTP 401 | FAILED，撞在自己留下的 `/dsh-market/telemetry/opened` 上 | 复现 |
| dsh-remote 1.3.1 | `/dsh-remote/status` | 内层 fiber FAILED | 仍登记，HTTP 401 | FAILED，撞在 `/dsh-remote/workspace-context` 上 | 复现 |
| dsh-connect-workbuddy 5.31.0 | `…/account-credits` | 内层 fiber FAILED | 仍登记，HTTP 200 (`{"status":"signed-out",…}`) | FAILED，撞在 `…/usage` 上 | 复现 |
| @tencent-connect/dsh-qqbot 0.5.5 | `/qqbot/im-qqbot/bind/refresh` | 内层 fiber FAILED | 仍登记，HTTP 200 (`{"phase":"failed",…}`) | FAILED，撞在 `/qqbot/im-qqbot/bind` 上 | 复现 |
| dsh-free-search 0.9.82 | `…/mutate` | 全部 ACTIVE | 已撤掉 | 正常 | 泄漏不复现，见下 |

所以 A 类的 7 个插件中，有 6 个在真实宿主上完全复现：一次撞名之后泄漏路由，从此装不回去。

dsh-free-search 不同。它的 `registerOnce` (`lib/index.js:1552`) 会吞掉撞名错误，并"复用"已有的登记，只有别的错误才重新抛出。checker 注入的故障不是撞名错误，所以在 checker 里泄漏了；真实的撞名则不会泄漏。但这暴露了另一个问题：占位期间 free-search 所有 fiber 都是 ACTIVE，自以为复用了自己的 `/mutate`，实际请求由占位者的处理器应答 (HTTP 418，`scenarios/free-search-reuse.json`)。它的设置写入接口就这样悄悄交给了另一个插件，这是 R3 (相遇受控) 被违反。它的 R1 泄漏仍然存在，只是需要一个撞名以外的登记失败才会触发。

**C `dshRemote`：冲突复现，次序依赖没有复现。**

两种安装次序下，`dshRemote` 都归 dsh-remote；ds-harness-remote 两次都报 `SERVICE_PROVIDE_CONFLICT`，然后照常运行。原因是 ds-harness-remote 的 `provide` 排在一段异步激活 (`activateWhenCarrierReady`) 之后，在真实宿主里这段等待总比 dsh-remote 同步的 `provide` 慢。checker 的通用桩让这段激活提前完成了，于是在 checker 里表现为"谁先装归谁"。

所以结论修正为：

- 两个插件同装时，ds-harness-remote 的远程服务**总是**拿不到 `dshRemote`，而且只留一条警告；
- 次序依赖在这个宿主版本、这个环境下被异步延迟固定住了，没有表现出来。

从模型的角度看，这仍然是 R3 (相遇受控) 被违反。只是"调度"在这里由 I/O 延迟决定，而不是由安装次序决定。

**C 服务晚到 (C2)：dsh-remote、dsh-token-diet 复现，dsh-im 不复现。**

真实宿主里让服务晚到，不需要打补丁：停用提供服务的 loader 条目，再启用，就是这个服务的 O-Dispose 与 O-Insert。每个场景跑两种形式，再加一个对照 (2026-11-25，网络隔离)：

- **提供者重启**：插件不动，提供者停用再启用。这是配置变更、热重载时会发生的事。
- **服务晚到**：提供者停用期间启用插件，再启用提供者。这与 checker 的见证 (`install(p)`，再 `provide(s)`) 一一对应。
- **对照**：服务在场时重启插件。

为此驱动不再 inject `webServer`，每次用到时再读，这样停用 webServer 时驱动自己不会被一起卸载。驱动还新增了 `entries`、`provider`、`skillProviders` 三个观察。

dsh-remote 与 `skills` (`scenarios/remote-late-skills.json`)：

```
skillProviders 装上后            dsh-office, dsh-remote
skillProviders skills 停用时     (没有 skills 服务)
skillProviders skills 重启后     dsh-office                    (dsh-remote 的 provider 没回来)
fibers         skills 晚到       dsh-remote ACTIVE (×6)
skillProviders skills 晚到       dsh-office                    (同上)
skillProviders 插件重启后         dsh-office, dsh-remote        (对照: 重启插件才恢复)
```

插件所有 fiber 一直是 ACTIVE，不报任何错，但远端工作区的项目 skill (issue #120 的功能) 再也发现不了，直到插件重启。dsh-office 用的是能响应服务出现的写法，所以 skills 重启后它自己回来了。

dsh-token-diet 与 `webServer` (`scenarios/token-diet-late-webserver.json`)：

```
provider  webServer -> webserver;  connection -> connection
route     装上后            /token-diet 已登记, handler#1
route     webServer 重启后   未登记
route     webServer 晚到    未登记
route     插件重启后         已登记, handler#2
```

这比 checker 的见证更严重：不只是"webServer 晚到"，webServer 正常重启一次，token-diet 的 RPC 就没了，客户端从此连不上它，而插件全部 fiber 仍是 ACTIVE。这条路由是 token-diet 自己的退路 (`installWebRoute`，`lib/host/rpc.js:318`)：它先试 `connection.rpc.handle`，但那个方法读 `owner.webServer`，要求调用者 inject webServer，token-diet 没有，于是抛 `without inject`，插件退回自己登记路由。退路只在 apply 时读一次 webServer。对 `/token-diet/x` 发 GET 得到 405 (退路自己的方法检查；走 connection 时是 401)，印证了这一点 (`scenarios/webserver-restarts.json`)。

> 更正：上一版本节说 token-diet 走的是 `connection.rpc.handle`，并推测凡经它登记又不 inject webServer 的插件都会丢通道。不对。不 inject 根本过不了 `rpc.handle`，inject 了的调用者会随 webServer 重启并重新登记。宿主自己的包不用 `rpc.handle`；26 个插件中用它的是 ds-harness-remote、dsh-mnemon、dsh-prime-memory、dsh-token-diet。checker 同样在没有 inject 时抛错，所以 checker 里的 token-diet 也走退路。

@xmanrui/dsh-im 与 `sessionController`、`workspaceController` (`scenarios/im-late-controllers.json`)：

```
fibers    装上后                          dsh-im-host ACTIVE / … 全部 ACTIVE
fibers    session-controller 缺席时启用     dsh-im-host ACTIVE / $ PENDING / dsh-im-host ACTIVE
fibers    session-controller 晚到          全部 ACTIVE, 与装上后相同
fibers    workspace-controller 缺席时启用   dsh-im-host ACTIVE / $ PENDING / dsh-im-host ACTIVE
fibers    workspace-controller 晚到        全部 ACTIVE, 与装上后相同
services  (每一步)                         dshIm -> dsh-im-host
```

插件用 `G.inject(["sessionController","workspaceController"], …)` 等这两个服务：服务缺席时内层 fiber 停在 PENDING，服务一出现就激活，结果与服务先到时相同。checker 里"服务先到时激活失败"是桩造成的：14 个通道在桩上全部激活失败，插件因此抛出 `dsh-im failed to activate every channel`。所以这两个见证是误报。connection 桩补上 `rpc` 与 `fetch` 之后，checker 里也不再报。

**C 提供者重启 (C2，第二轮)：dsh-free-search、dshmarket 复现，dsh-image-gen 不复现。**

checker 新增"提供者重启"场景后得到 8 个见证 (`witnesses/*-restart-*.json`)。真实宿主上用 `scenarios/restart-providers.json` 依次重启 system-prompt (两次)、webserver、settings，每次之后观察三个插件；用 `scenarios/webserver-restarts.json` 连续重启 webserver 三次。

```
fibers    装上后                web-search-free ACTIVE ×14, PENDING ×1
route     装上后                /api/dsh-free-search-settings/describe 已登记
fibers    systemPrompt 重启 1 次  web-search-free ACTIVE                  (只剩一个)
route     systemPrompt 重启 1 次  未登记
fibers    装上后 / webServer 重启 1、2、3 次   dsh-market ×4 / ×5 / ×6 / ×7
listeners 装上后 / systemPrompt 重启 2 次     credentials/reference-updated: image-gen×1 / image-gen×1
```

- **dsh-free-search**：apply 开头的重入保护 (`lib/index.js:1546`) 用 `WeakSet` 记下跑过的 ctx。Cordis 在被 inject 的服务重新提供时，先撤销 fiber 的全部效应，再在同一个 ctx 上重跑 apply，重入保护把这次重跑挡掉了。checker 里 `web`、`settings`、`tools`、`systemPrompt` 任一个重启都触发；真实宿主上确认了 systemPrompt。
- **dshmarket**：webServer 每重启一次多留一个 ACTIVE 的 fiber，持续累积。来源尚未在源码中定位。
- **dsh-image-gen**：`ctx.inject(["systemPrompt"], (promptCtx) => { ctx.inject(["credentials"], …) })` 在回调里用了外层的 `ctx` (`lib/index.js:32603`)，checker 里 systemPrompt 每重启一次就多挂一份 credentials 监听器。真实宿主上重启两次监听器仍各 1 个，原因是级联：插件 inject 了 `tools`，`tools` 又 inject 了 `systemPrompt`，插件整棵重来。写法错误是真的，只是在 dsh 当前的服务依赖下不触发。见下一节。
- **dsh-token-diet**：webServer 重启丢路由，见上一节。

**C 级联重启 (C2，第三轮)：image-gen 的不复现得到解释，webStartup 的两个新见证复现。**

真实宿主里服务的提供者本身也 inject 别的服务。驱动的 `graph` 步骤读出了 dsh 0.2.2-rc.5 的 106 个服务，以及每个服务的提供者 fiber 链上的 inject。`real/make-graph.mjs` 把它整理成 `lib/host-graph.json`。

与 checker 的宿主相关的边有这些：

- `tools` → `systemPrompt`；
- `webServer` → `webStartup`；
- `connection` → `credentials`、`webStartup`；
- `agents` → `sessionProjections`；
- `subagents` 与 `fileReferences` 经 `workingDirectory` 依赖 `systemPrompt`；
- 另有若干 session 类服务之间的边。

宿主桩按依赖的传递闭包 inject，只取场景中出现的服务，于是撤走一个服务时，由 Cordis 自己连带卸载下游的服务与插件。

真实宿主上用 `scenarios/cascade.json` 验证：先重启 web-startup，再重启 system-prompt，每次之后读 image-gen 根 fiber 的 epoch (修订号加上它 inject 的服务实例编号)。

```
epoch     装上后               image-gen 0:41:14:26   inject=[tools,attachments,credentials]
epoch     webStartup 重启后     image-gen 0:41:14:26   (不受影响)
epoch     systemPrompt 重启后   image-gen 0:118:14:26  (tools 换了实例: 整个插件重来)
fibers    装上后 / webStartup 重启后   dsh-market ×4 / ×5
fibers    装上后 / webStartup 重启后   web-search-free ACTIVE ×14 + PENDING ×1 / ACTIVE ×14 + PENDING ×2
route     webStartup 重启后          /api/dsh-free-search-settings/describe 已登记, 新的处理器
```

逐条看：

- **dsh-image-gen**：级联后 checker 也不再报，与真实宿主一致。
- **dshmarket，`webStartup`**：新见证。web-startup 重启连带 webServer 重启，于是多一个 fiber，与 webServer 重启的见证同源。
- **dsh-free-search，`webStartup`**：新见证。重启后多一个停在 PENDING 的 fiber，与 checker 的判定完全相同。路由随新处理器重新登记。上一轮"未单独确认"的那一行由此确认。
- **dsh-ops，故障注入 `systemPrompt.section` 第 2 次**：这次全量重跑中 dsh-ops 全部 ACTIVE (见"覆盖面")，于是多出这个见证。中途抛错后再装，提示段的名字从 `…:mode-ptc`、`…:mode-ptc:2` 变成 `…:mode-ptc:3`、`…:mode-ptc:4`。序号来自 `publication/ownership.js` 里按 `ctx.root` 共享的状态，只增不减。与级联无关。真实宿主上用真实的段名撞名复现，而且一次失败后序号随每次重启继续增长，见"在真实宿主上的复现"末尾。

另外，`pair-ds-harness-remote-dsh-remote` 在 checker 里约五次有一次不复现，级联前后都是这样。原因是 ds-harness-remote 的 `provide` 排在一段文件 I/O 之后 (`activateWhenCarrierReady`)，与另一个插件的装载赛跑。真实宿主上它总是输，见上文。

**级联的覆盖面 (2026-11-26)。** 真实插件有多依赖这种连带重启？做法是：在 checker 里把能装上的 25 个插件各装一次 (默认宿主)，读出每个插件 fiber 上的 inject，再沿 `lib/host-graph.json` 求闭包。这次只用了一个临时探针，没有进仓库：它在 `exec.mjs` 的快照里多记每个 fiber 的 inject 和它在插件内的深度。

插件自己的嵌套普遍，但不深：

- 17 个插件有嵌套的 inject (apply 里再 `ctx.inject`，或开子插件)，例如 dsh-context 18 个、dsh-free-search 14 个、dsh-ops 11 个；
- 最深 3 层，只有 ds-harness-remote、dsh-ops、dsh-im；
- 没有嵌套的 8 个：deep-view、dsh-mnemon、dsh-mobile-plugin、dsh-onebot-qq、dsh-pet、dsh-plugin-wallpaper-engine、dsh-session-superagent、dsh-skills-manager。

宿主侧的依赖则让插件被许多它没有声明的服务连带重启。一个服务重启时波及的插件数如下 (直接 inject，或经闭包间接依赖)：

| 重启的服务 | 波及 | 其中只经级联 | 经过的边 |
|---|---|---|---|
| `webStartup` | 21 | 20 | `webServer`、`connection` → `webStartup` |
| `systemPrompt` | 17 | 8 | `tools` → `systemPrompt` |
| `sessionProjections` | 13 | 9 | `agents` → `sessionProjections` |
| `credentials` | 12 | 8 | `connection` → `credentials` |
| `webServer` / `tools` / `connection` | 16 / 15 / 12 | 0 | 没有宿主服务依赖它们 |

systemPrompt 只经级联波及的 8 个是 deep-view、ds-harness-remote、dsh-agent-compare、dsh-connect-workbuddy、dsh-mnemon、dsh-session-superagent、dsh-windows-mcp、dsh-skills-manager，都是因为用了 `tools`。闭包里的 `cmdlineArgs`、`profileContext`、`configEditor` 大概只在启动时提供，上表没有列。dsh-im 与 deep-view 经闭包分别多出 21 个与 22 个隐含依赖，基本是整个 session 子系统。

结论取决于级联的只有 3 个插件：第二轮 (不级联) 与第三轮 (级联) 的见证只在 dsh-image-gen、dshmarket、dsh-free-search 上不同。

- dsh-image-gen：级联**掩盖**了外层 `ctx` 的写法错误，这是唯一一个正确性靠级联兜底的插件，而且是碰巧。
- dshmarket、dsh-free-search：级联多出 webStartup 这条触发路径，根源与 webServer 重启相同。

其余见证有没有级联都一样，问题都出在插件直接 inject 的服务上。

所以，级联本身不违反任何前提：它只是 O-Dispose 沿依赖传播，满足前提的插件被连带重启多少次都没关系。但它放大了违反前提的代价：复用 ctx、用外层 `ctx` 这类写法，会被比插件作者以为的多得多的服务重启触发。它也会掩盖违反：宿主的依赖图一变 (例如 `tools` 不再依赖 `systemPrompt`)，image-gen 的问题就会出现。审计与 checker 都应该按服务单独重启来判，不能指望级联兜底。

局限：数字来自一次装载，只覆盖走到的分支。dsh-cost-meter 只部分激活，dsh-mnemon 配置校验失败，它们的嵌套 inject 可能少算了。webStartup 等服务在实际使用中多久重启一次，没有数据。

### 第四、五轮的新见证 (2026-11-25)

驱动新增两个探测：`routes` 按前缀统计路由与升级路由的条数和处理器编号，`tools` 查一组工具是否登记在全局层。

**dsh-mobile-plugin 的卸载残留：原样复现。** `scenarios/mobile-unload.json`，停用再启用 `dsh-mobile` 条目：

| 时刻 | fiber | `/api/mobile/*` | `/api/relay/*` | `/api/cloudflare/*` | 升级路由 | `/api/mobile/v1/commands` | 不属于插件的路径 |
|---|---|---|---|---|---|---|---|
| 装上后 | ACTIVE ×2 | 214 | 72 | 2 | 3 | handler#33，HTTP 401 | 404 |
| 停用后 | DISPOSED | 214 | 70 | 2 | 2 | handler#33，HTTP 401 | 404 |
| 再启用后 | ACTIVE ×2 | 214 | 72 | 2 | 3 | handler#33，HTTP 401 | 404 |

停用后少掉的只有外壳自己的两条 `/api/relay/host-half*`，其余 286 条路由和 2 条升级路由仍在，与 checker 的数字完全相同。插件已经 DISPOSED，它的路径仍然回插件自己格式的 401 (`{"ok":false,"error":{"code":"unauthorized",…}}`)，宿主对不存在的路径回 404。再启用后，除了 `host-half` 换成了新处理器 (handler#293)，其余路由上挂的全是停用前的那批分派器 (同一函数对象)：新实例的分派器撞名没挂上，宿主日志里没有任何报错，fiber 却都显示 ACTIVE。请求就这样由已卸载实例的分派器转给旧代的处理器，直到宿主重启。

**dsh-mobile-plugin 的提供者重启：没有复现。** `scenarios/mobile-restart.json`，连续两次停用再启用 `webserver`：每次插件仍是 2 个 ACTIVE 的 fiber，288 条路由与 3 条升级路由全部换成新处理器重新登记，没有累积。checker 报的多一个 fiber、TCP 监听与计时器，在它自己的稳定性门槛下就时有时无，判为桩造成的误报；两个见证 (`dsh-mobile-plugin-restart-*`) 保留备查。驱动看不到句柄数，TCP 监听与计时器没有在真实宿主上单独检查。

**ds-harness-remote 的两个 C2：原样复现。** `scenarios/remote-harness-webserver.json`：

| 时刻 | fiber | `/ds-harness-remote` 前缀路由 | remote_* 工具 | `dshRemote` |
|---|---|---|---|---|
| 装上后 | 5 个 ACTIVE | 1 条 (handler#1) | 13/13 | 有 |
| webServer 重启后 | 5 个 ACTIVE | **0 条** | 13/13 | 有 |
| webServer 缺席时启用 | `activateWhenCarrierReady` FAILED: `cannot get property "webServer" without inject` | (无 webServer) | **0/13** | **无** |
| webServer 晚到 | 同上，不恢复 | **0 条** | **0/13** | **无** |
| 插件重启后 | 5 个 ACTIVE | 1 条 (handler#2) | 13/13 | 有 |

两处都与 checker 的见证一致，而且都是静默的：重启后全部 fiber 仍是 ACTIVE，只有重启插件才恢复。

### B 类：进程级状态 (2026-11-25)

驱动新增 `proc` 探测，与 checker 的 `probes.mjs` 看同一组状态：`globalThis` 的自有键、`process` 监听器数、dns 解析序、长命句柄数。驱动与宿主同一个进程，看到的就是宿主的状态。宿主插件在启动时就装好，拿不到"装之前"，所以分两次运行：只装驱动的空宿主作对照 (`scenarios/process-baseline.json`)；装上 8 个插件，逐个停用再启用，每步记一次 (`scenarios/process-state.json`)。dsh-im 的 `exit` 监听器在合装时分不清归属，另外单独装一次 (`scenarios/process-im.json`)。

| 插件 | checker 报的残留 | 真实宿主 | 结论 |
|---|---|---|---|
| dsh-whale-widget | dns 解析序 `verbatim` → `ipv4first` | 空宿主 `verbatim`，装上后 `ipv4first`，停用后不变 | 复现 (模块加载时设置，见源码) |
| dsh-session-superagent | `globalThis` 上 3 个 Symbol 槽 | 3 个槽都在，停用后仍在 | 复现 |
| dsh-cost-meter | `Symbol(…billion-context.peers.v1)` | 停用时撤掉了 `…auto.v1` 与 `…v1`，`…peers.v1` 留下 | 复现，与 checker 完全一致 |
| ds-harness-remote | `Symbol(…hmr-safe-settings-pump)`；zod 的 `__zod_global*` | pump 槽停用后仍在；zod 的两个槽空宿主里本来就有 (dsh 自己用 zod) | pump 复现；zod 槽在真实宿主上不算插件的残留 |
| dsh-pet | 一个计时器 | 停用时撤掉 `exit` 监听器，计时器 10 → 6；再启用回到 10，不累积 | 不复现 (桩上的偏差) |
| dsh-prime-memory | `process.on('beforeExit')` 监听器 | 空宿主 0 个，装上后 1 个，停用后仍 1 个，再启用变 2 个 | 复现，且随重启累积 (第五轮的 11 个见证同源) |
| @xmanrui/dsh-im | `process.on('exit')` 监听器 | 单独装：2 → 3，停用后仍 3，再启用不再增加 | 复现 (模块加载时登记，所以不累积) |
| dsh-mobile-plugin | `globalThis` 上 2 个 Symbol 槽与 `__dshZeroNewsCurrent` | 3 个都在，停用后仍在；它的 TCP 监听、子进程与管道停用时都撤掉了 | 复现 |

8 个插件中 7 个复现，dsh-pet 不复现。计时器数在真实宿主上有噪声 (宿主自己的计时器也在变)，所以 dsh-pet 的判断只看"再启用后没有比停用前多"。

### dsh-ops 的提示段序号 (2026-11-25)

checker 的见证 `dsh-ops-fault-systemPrompt.section-2`：第 2 次 `systemPrompt.section` 抛错后卸载再装，提示段 `…:mode-ptc`、`…:mode-ptc:2` 变成 `…:mode-ptc:3`、`…:mode-ptc:4`。真实宿主上用真实的撞名触发：dsh 的 `systemPrompt.section` 遇到重名就抛错，驱动先占住第 2 次调用要登记的段名 `dsh-ops:repository-tooling:mode-ptc` (新增的 `squatSection` 操作)，再启用 dsh-ops (`scenarios/ops-section.json`，`sections` 操作列出 systemPrompt 全局层上的段名)：

| 步骤 | `consumer-ptc` | `repository-tooling:mode-ptc*` 段 |
|---|---|---|
| 装上后 | ACTIVE | `mode-ptc`、`mode-ptc:2` |
| 正常停用，再启用 (对照) | ACTIVE | `mode-ptc`、`mode-ptc:2` |
| 段名被占时启用 | 一个 FAILED：`prompt section "…:mode-ptc" is already registered` | (占位者的 `mode-ptc`)、`mode-ptc:2` |
| 停用，撤掉占位，再启用 | ACTIVE | **`mode-ptc:3`、`mode-ptc:4`** |
| 再正常停用、启用一次 | ACTIVE | **`mode-ptc:5`、`mode-ptc:6`** |

复现，而且比见证更进一步：一次失败之后，每次重启序号都再涨 2，不会回落。原因在 `publication/ownership.js`：按 `ctx.root` 共享的 `sequence` 只在这一族的 `rows` 清空时才随整族删除，而 `publication/ptc.js` 先登记提示段 (`:374`)，再在下一个 `ctx.effect` 里登记 `ownership?.dispose()` (`:375`)。登记提示段一抛错，移除 row 的撤销就没有机会登记，这一行永远留在 `rows` 里。这正是 A 类的同一个模式：先做效应，后登记逆。没有失败过时，正常重启会清空 `rows`，序号归零，所以对照组不变。段名带上的序号会进到提示的组装里；更要紧的是那个死掉的 row 一直在 `rows` 里，每次 `notify` 都还会调它的 `changed`。

## 与审计的对照

- **checker 复现了审计的判定**：
  - dsh-whale-widget 的 R1 ✗ 与 dns；
  - dsh-windows-mcp 的路由泄漏；
  - dsh-session-superagent 的 `globalThis`；
  - `dshRemote` 撞名；
  - dsh-token-diet 的 C2；
  - dshmarket"缺口只在中途抛错"。
- **checker 补充了审计**：
  - 给出了每个 R1 问题的具体故障点和残留条数；
  - 发现了"从此装不回去"这一后果；
  - 补出了 dsh-remote、dsh-free-search、dsh-connect-workbuddy、dsh-qqbot 的同类问题；
  - 补出了 dsh-cost-meter、ds-harness-remote 的 `globalThis` 槽，以及 dsh-pet、dsh-prime-memory、dsh-im 的进程级残留。
- **审计说有、checker 没有复现的**：
  - **`approval/request` 中间件的次序 (dsh-im 与 dsh-qqbot)**：两者都要等 IM 通道真正连上之后才登记这条中间件。checker 禁网，又没有真实账户，走不到这条路径。
  - **dsh-cost-meter 对 `ChildProcess.prototype.spawn` 的常驻补丁**：模块加载时它会临时打一个，apply 结束就按引用计数释放；常驻的那个排在一次 typert 注册之后，而这次注册在通用桩上失败了。
  - **dsh-whale-widget 的 index-inject 行**：checker 看到卸载后监听器已经撤销，宿主每次 emit 都新建表。审计说的是桌面端宿主只收集一次的情形，不在桩的语义里。

## 覆盖面与没走到的部分

装上后的 fiber 状态 (ACTIVE/全部)，见 [reports/sweep.md](reports/sweep.md)：

- **全部 ACTIVE**：dsh-connect-workbuddy、dsh-context、dsh-genui、dsh-image-gen、dsh-onebot-qq、dsh-pet、dsh-remote、dsh-session-superagent、dsh-token-diet、dsh-whale-widget、dsh-windows-mcp、dshmarket、dsh-skills-manager、dsh-qqbot。
- **部分 ACTIVE**：
  - dsh-cost-meter 3/4，一个 fiber 失败在 typert 的通用桩上；
  - dsh-free-search 14/15，等 `connection.authentication`；
  - dsh-prime-memory 3/4，一个停在 LOADING；
  - dsh-ops 9/18，9 个停在 LOADING (第三轮重跑时 18/18)；
  - ds-harness-remote 3/4，一个停在 LOADING。
- **没有 ACTIVE 的 fiber**：dsh-agent-compare (LOADING；第三轮重跑时 3/3)、dsh-mnemon (配置校验失败)、dsh-plugin-wallpaper-engine (启动自检要求的 loader 条目不存在)、deep-view (读一个没有桩的服务时拿到 undefined)、dsh-im (通道激活失败)。
- 补记 (2026-11-25)：connection 桩补上 `rpc` 与 `fetch` 之后，deep-view (1/1) 与 dsh-im (7/7) 都全部 ACTIVE。deep-view 原先读不到的正是 `connection.fetch`。两者在扩大的覆盖面上都没有新的 ✗。
- 补记 (第三轮)：dsh-agent-compare 与 dsh-ops 单独运行时一直全部 ACTIVE，第一轮的 LOADING 出现在并行池满载的那次运行里。第三轮全量重跑时两者全部 ACTIVE，dsh-ops 因此多出一个见证。
- 补记 (第四轮)：dsh-mobile-plugin 2/2、dsh-plugin-wallpaper-engine 1/1 全部 ACTIVE。另一方面，这一轮 (WSL 重启之后) dsh-agent-compare 与 dsh-ops 单独运行也停在 LOADING，换回第三轮的代码同样如此，所以与 require 桩无关：agent-compare 的 apply 要动态 import `@deepseek-ai/dsh-tools`，这里约 0.3 秒，落定等不了这么久。第五轮改了落定，两者恢复全部 ACTIVE。
- 补记 (第五轮)：dsh-prime-memory 6/6、ds-harness-remote 5/5 全部 ACTIVE；它们原先各有一个停在 LOADING 的 fiber，也只是加载慢。

所以，"没有见证"不等于"没有问题"。对后两类插件，checker 只覆盖了它们走得到的那一段。

## 本轮排除掉的假阳性

记下来，是因为它们说明了判据必须注意的地方：

1. **跨进程比较对象编号**：原型属性的身份编号只在进程内有意义。现在每次运行先和自己的基线比，跨运行只比"相对基线的改动"。
2. **宿主自己的库**：schemastery 首次加载会写 `globalThis.__schemastery_*`。现在在基线之前就预先加载。
3. **新旧实例分不开**：卸载后再装若用同一个安装编号，残留的旧路由和新路由在快照里无法区分。现在再装用 `p2`，比较前再统一改名。
4. **异步加载没走完**：装上后有 fiber 停在 LOADING 时，"再装"与"服务晚到"的比较是在拿"没装完"和"装完了"作比较，dsh-ops 因此一度报了 23 处 ✗。现在这两类比较在没落定时判无结论。
5. **时序抖动**：ds-harness-remote 的 25 个"服务晚到"候选重放时时有时无。现在用稳定性门槛排除。
6. **短命句柄**：`FSReqPromise`、`MessagePort` 之类不计入资源。

## 下一步

- 真实宿主上已复现 A 类 7 个插件中的 6 个，以及 `dshRemote` 冲突 (见上)。
- checker 的通用桩会改变异步时序 (`dshRemote` 一例)。凡是依赖时序的第 3 层见证，都应在真实宿主上确认之后再下结论。
- 给 typert、IM 通道写专门的桩，让 dsh-cost-meter 的原型补丁和 `approval/request` 的次序问题能被走到。
- ~~支持 CJS 的 `require` 桩，覆盖 dsh-mobile-plugin。~~ 已完成 (第四轮)。
- ~~落定改为等到没有 LOADING 的 fiber (设上限)。~~ 已完成 (第五轮)。
- ~~在真实宿主上确认 dsh-mobile-plugin 的卸载残留。~~ 已完成：卸载残留复现，重启累积不复现。
- 给上游的报告或 PR：A 类的修法是统一的 (每登记一条立即登记它的逆)，可以给 7 个插件分别提。这是对外的动作，需要先确认。
