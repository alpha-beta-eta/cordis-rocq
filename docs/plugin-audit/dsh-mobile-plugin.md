# dsh-mobile-plugin 0.5.97

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：**是**，另附一个独立的无头宿主程序。插件入口 `lib/index.js` 是「稳定外壳」：`inject = ['webServer']`（`lib/index.js:38` ✔）。外壳在运行期 `ctx.plugin({inject, apply})` 装载可替换的「代」，随包的那一代是 `lib/impl.js`（`inject = ['webServer']`，旧运行时上再加 `apiProxy`，`lib/impl.js:110` ✔）。外壳 provide `dshMobilePluginRuntime`（`lib/index.js:187` ✔），以及 `dshMobileSidecarHost`、`dshMobileTransportFrp`、`dshMobileTransportControl`、`dshMobileTransportMux`、`dshMobileTransportTailcat`、`dshMobileTransportP2P`（`lib/shell/transport-host.js:38-145` ✔）。代先 `ctx.isolate('apiProxy')`，再 provide `apiProxy`（`lib/impl.js:192,249` ✔）。`host.js`（bin）是一个独立的无头 dsh 宿主，自己拼 patch 层、boot Cordis，不属于组件。客户端 `lib/client.js`，`inject: ['slots','locale']`（`lib/client.js:3186`）。
- 一句话功能：让手机远程控制 dsh。宿主端提供 `/api/mobile/v1` 和 `/api/relay/*` 路由，管理 sidecar、frpc、cloudflared、tailcat、p2p 等隧道子进程，做会话镜像推送和推送通知，在手机上管理插件市场，并支持自更新和热换代。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 外壳读取未注入的服务：`ctx.get(key)`（`lib/index.js:67-69` ✔，用于 `dshMobileTailcatCtl` 等）和 `ctx.logger`。代读取外壳 provide 的 `dshMobileTransport*` 和 `dshMobileSidecarHost`（`lib/impl.js:313,320,337,376,526,692` ✔）。这些键由祖先 provide，按 Cordis 的继承语义能读到，但没有声明。代还读宿主的 `apiProxy`（`impl.js:239-241` ✔）和 `connection`。客户端读了未注入的 `ctx.get('layout')`、`ctx.get('pluginNavigation')`。都是有意的可选依赖。 |
| 0 | S2 | △ | 键名都是字面量，并带 `dshMobile` 前缀。`apiProxy` 是宿主旧运行时的服务名；代先 `isolate` 再 provide，以此避开与宿主冲突（`impl.js:192,249` ✔）。这依赖 isolate 约定，算 △。 |
| 0 | S3 | ✗ | **猴补丁服务实例**：替换 `webServer.register`/`registerUpgrade`，改走自己的蓝绿分发（`lib/index.js:156-180` ✔，还原条件是「仍等于我的包装」）。**自编排**：外壳 runtime 运行期 `ctx.plugin` 新代，换代或回滚时直接 `oldFiber.dispose()`/`brokenFiber.dispose()`（`lib/shell/runtime.js:304,453,465,605` ✔），并自己 import 磁盘上的新代代码。**编排其他插件**：手机端可以触发 `pluginManager.installBundle`/`updateBundle`（`lib/mobile/plugin-market.js:395,458` ✔）。**globalThis**：`zeronews/wiring.cjs:145`、`mobile/inbox-clean.js:295`、`session-cleanup.cjs:399` ✔。`approval/request` 和 `user-questions/request` 用 `{prepend:true, global:true}` 抢占全局处理（`mobile/approvals.js:788`、`mobile/questions.js:349` ✔）。 |
| 1 | L1 | △ | 外壳 apply 同步返回。`runtime.start(ctx)` 不在 apply 里 await，代是在 apply 返回**之后**才 spawn 的（`lib/index.js:223` ✔）。装载有 `ACTIVATE_TIMEOUT_MS` 超时，`drain` 有截止时间（`runtime.js:304-307,590-595` ✔），因此有界。2 分钟一次的自更新 `setInterval` 放在 Active 之后（`index.js:229` ✔）。 |
| 1 | L2 | ✓ | 外壳 provide `dshMobileTransport*`，代（外壳的子 fiber）去读，方向是后代读祖先。代没有 inject 只有自己后代才会提供的服务。没有成环。 |
| 2 | R1 | ✗ | 外壳里有两个没登记的 `setTimeout` kick，会在 5 秒或 10 秒后执行 `applyUpdate`/`check`（`lib/index.js:243-253` ✔）。自更新的 `setInterval` 在一个 Promise 回调里才登记 effect（`239` ✔），如果外壳在那之前已 dispose，就漏掉了。代里每一块装配都包在 `mount` 里吞掉异常（`impl.js:231-236` ✔），中途失败时已经做完的部分会留下来，这是有意的「部分装配」设计。`inviteLanTimer` 没有在 dispose 时清除（`impl.js:278-285` ✔）。 |
| 2 | R2 | △ | 隧道子进程**有意由外壳持有，跨代存活**。代只把配置推给外壳的 sidecar，`sidecarLifecycle.start()` 不登记在代的 fiber 上（`impl.js:428-436` ✔）。运行期由手机发起的插件安装和隧道启停不经过子 fiber。 |
| 2 | R3 | △ | 路由 `/api/mobile/v1/*`、`/api/relay/*`（含 `/api/relay/internal/*`）带前缀。`apiProxy` 同名但靠 isolate 避开。`approval/request` 用 prepend+global，依赖它在处理链里排第一。 |
| 2 | R4 | △ | 持久状态：`relay.json`、凭据库（`dsh-mobile-credentials`）、历史密钥、回退代目录和 OTA 包、自更新落盘、宿主插件的安装和升级。临时资源泄漏：上面的 kick 定时器、`inviteLanTimer`、globalThis 上的单例。进程级改动：`host-guard.cjs` 的 `process.on('uncaughtException')` 只由无头宿主 `host.js` 安装，插件路径里只读（`impl.js:80` ✔，`installProcessGuard` 在插件内的调用者**未确认**）。 |
| 3 | C1 | ✓ | 外壳的 provide 都在 apply 里同步、无条件执行。代的 `apiProxy` 也是无条件 provide（失败只被 `mount` 吞掉）。 |
| 3 | C2 | ✗ | 代启动时按 `runtimeProvidesApiProxy()` 分支。旧宿主上要等 `API_PROXY_GRACE_MS` 到时，再看宿主的 `apiProxy` 有没有出现，才决定装不装帧桥（`impl.js:254-268` ✔），这是**真依赖时机**。此外还看外壳的传输宿主是否存在（`ctx.get('dshMobileTransport*')`），以及 relay.json 和凭据库的内容（对固定环境合流）。外壳装哪一代取决于磁盘上的安装状态。 |
| 3 | C3 | ✗ | `webServer.register` 补丁的逆是「仍等于我的才还原」，依赖状态（`index.js:175-177` ✔）。settings 和 relay.json 写入也依赖状态。 |
| 3 | C4 | ✗ | 外壳直接 dispose 自己 `ctx.plugin` 出来的代 fiber（`runtime.js:453,465,605` ✔），正中差异 q。 |
| 3 | C5 | ✓ | 启动期没有读取 emit/waterfall/bail 的结果。 |

**最高层**：不在模型内，0 层也不满足。它猴补丁 `webServer.register`，自己编排代的装载和卸载，还替手机编排其他插件的安装和升级。
**升级路径**：外壳和代的热换代本质上是编排者行为，要单独当编排者看待，不能按组件来审。只看「代」(`impl.js`) 的话：(1) 未注入的 `ctx.get` 改成可选 inject。(2) 删掉 grace 定时器分支，改为 `ctx.inject(['apiProxy'],…)`。(3) 插件市场功能拆出去交给编排者。(4) `inviteLanTimer` 和 globalThis 单例登记到 fiber 上。做完这些，代本身可以到第 1 至 2 层（R2 受「隧道跨代存活」这个设计约束）。外壳只有在放弃猴补丁和自管代、改由宿主提供路由分发和换代机制时，才能进入模型。
