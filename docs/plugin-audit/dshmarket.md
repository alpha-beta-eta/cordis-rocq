# dshmarket 1.80.0

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是，而且是**编排者**。宿主 `lib/index.js` (tsc 输出，可读) 导出 `name='dsh-market'`、`Config`、`apply` (`:18`、`:244` ✔)，无顶层 `inject`；`apply` 开两个静态子 fiber：`ctx.inject(['webServer','loader'])` (`:245` ✔，内部按宿主类型三选一分支，Desktop 分支再嵌套 `hostCtx.inject(['desktopPnpm'])`，`:392`) 与 `ctx.inject(['commands'])` (`:457`，1.80 新增 `/find-plugin`)。无 provide (只登记 settings 命名空间 `dsh-market`)。客户端 `client/client.js`，`inject = ['slots','locale','theme']`。
- 一句话功能：DSH 内的可视化插件市场：浏览/搜索/一键安装、更新、禁用插件，改 profile 与 loader 条目，热挂载插件，必要时重启宿主或热替换自身。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✗ | 未注入读取 9 个名字：`profileContext` ×7 (`lib/index.js:236,256,304,361,401,402`，`lib/routes.js:3268`)、`desktopProfiles` (`index.js:250` ✔)、`connection` ×2 (`:168,203`)、`agents` (`:135`)、`pluginManager` (`:293`)、`llm`、`agentDefaultModel` (`:443-445`，1.80 新增)、`hmr` (`routes.js:3267`，新增)。`desktopProfiles`/`profileContext` 决定启动分支 (见 C2)，有意为之；其余可改为可选依赖。 |
| 0 | S2 | ✓ | 无 provide。 |
| 0 | S3 | ✗ (编排者) | 元层钩子 `host.on('internal/plugin', …)` 把用户禁用的插件重新压下 (`routes.js:937` ✔)；改别的插件的 loader 条目 `entry.update({ disabled })` (`lib/themes.js:188`、`lib/hot.js:953`)；在处理器中 `ctx.plugin(HotTree, { path })` 热挂载其他插件 (`hot.js:1111` ✔)，挂载文件写在 profile 下；调用 `dsh plugin …`/pnpm 子进程装卸插件 (`lib/dsh-cli.js:449-454`)；重启助手给自己进程发 SIGTERM (`lib/restart.js:686`)；经宿主 `hmr.reconcileProfile()` 热替换自身 (`lib/self-reload.js:183`，新增)。本质是编排者，需要编排者义务而不是组件义务。 |
| 1 | L1 | △ | `apply` 同步有界。但 `mountMarketRoutes` (在 `host.effect` 内) 里 `void replayBootDisables()` (`routes.js:933`) 异步挂载 client-only 垫片并逐个重放禁用 (改 loader 条目)，属启动期的编排；官方 Desktop 分支 8 秒后自动重装中断的更新 (`index.js:323`)。都有界 (遍历有限列表)，但发生在启动之后、未登记为反应。遥测心跳每 6 小时一次 (`lib/telemetry.js:112`)，属 Active 期间反应。 |
| 1 | L2 | ✓ | 只 inject 宿主服务 (`webServer`、`loader`、`desktopPnpm`、`commands`、`settings`)；热挂载的 `HotTree` 是运行期 spawn，不在启动依赖图中。 |
| 2 | R1 | △ | 路由 63 条全部收进 `disposers` 数组并由 `host.effect` 返回的 disposer 统一撤销 (`routes.js:3271` ✔、`:9628-9647` ✔)，计时器、心跳、更新通知、实例声明也在其中。缺口：(1) 数组字面量里某条 `webServer.register` 抛 duplicate 时，effect 本身失败，前面已登记的路由泄漏；(2) `setHostPackageManager` (`index.js:350`)、`setModelAccess` (`:442`) 在 effect 外写模块级状态，不恢复；(3) `installMarketSettings(ctx, …)`/`installDesktopMarketSettings(ctx)` 在 `hostCtx` 回调里用外层 `ctx` 开 `inject(['settings'])` (`index.js:317,375` ✔，`lib/settings.js:111,148`)，子 fiber 挂在插件根上而非 `hostCtx` 上：`webServer`/`loader` 重挂时会再登记一次同名命名空间 (按 Cordis 的 fiber 归属推断，未实测)。 |
| 2 | R2 | ✗ | 路由处理器里的效应：`dsh`/pnpm 子进程、写 profile 清单/patch/hot 文件、`entry.update`、`ctx.plugin(HotTree)` (可单独撤销，但挂在长寿的 `hostCtx` 上，并由插件自己的 Map 管理，`hot.js` `listHotMounts`/`hotUnmount`)；SIGTERM 重启与 HMR 自替换不可能由 fiber 撤销。 |
| 2 | R3 | ✗ | 路由在 `/dsh-market/` 前缀下 ✓；命令名 `find-plugin` (`lib/find-plugin.js:596`) 是通用名，可能撞名。`internal/plugin` 监听与 `entry.update` 直接读写别的插件的 loader 条目，和 dsh 自身 patch overlay 互相覆盖 (注释自述 "re-update entries … wipe the runtime disabled flag")。 |
| 2 | R4 | ✗ | 持久状态 (保证不覆盖)：profile 清单与 `cordis.patch.yml`、市场状态文件、日志、快照/备份、`$DSH_HOME/dsh-market/telemetry.json` (`telemetry.js:23`)、WebDAV/Gist 同步凭据。进程级全局改动：模块加载时把 `Symbol.for('undici.globalDispatcher.2')` 清为 `undefined` (`lib/net.js:63` ✔，为修复自己 undici 导入的副作用)；`globalThis` 槽：重启标记与进行中操作 (`lib/official-desktop.js:446-475`)、服务实例声明 (`self-reload.js:73`，新增)、启动修复报告 (`lib/startup-repair-report.js:5,33`，新增)，有意跨重载存活。外发网络：默认开启的匿名遥测 POST 到 `t.dshmarket.com` (`telemetry.js:19`，新增；`DO_NOT_TRACK=1` 或设置可关)。临时资源泄漏：R1 所述。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | ✗ | 启动分支取决于未注入服务**当时**是否存在：`ctx.get('desktopProfiles')` 一次性决定走第三方 Desktop / 官方 Desktop / Web CLI 三支之一 (`index.js:250` ✔)，`profileContext` 决定 profile 名与目录，注释承认 launcher 可能在市场挂载之后才提供 `profileContext` (`:227`)——真的依赖时机，不只是"对固定环境合流"。`replayBootDisables` 读磁盘上的禁用列表决定要改哪些 loader 条目。 |
| 3 | C3 | ✗ | `entry.update({ disabled })`、profile 文件改写、settings 中 `allowRestart` 的"卸载时恢复为组合值" (`settings.js:156-159`) 都是状态相关的逆。 |
| 3 | C4 | ✓ | 未见直接 dispose 启动时 spawn 的子 fiber (热挂载的 `HotTree` 是运行期 spawn，由 `hotUnmount` 撤销)。 |
| 3 | C5 | △ | 启动期不 emit；但 `internal/plugin` 监听器的效果依赖它相对 dsh patch overlay 的执行顺序 (注释称作 "self-healing guard")。 |

客户端：`inject ['slots','locale','theme']`，`slots.register` 都在 `slots.inject` 回调里返回，`locale.register`、更新快照、更新指示器都包在 `ctx.effect` 中；7 处 `setInterval` 都有 `clearInterval` 清理。客户端本身可到第 2 层以上。

**最高层**：不在模型内 (作为组件)。它是编排者：`internal/plugin` 元层钩子、改别的插件的 loader 条目、热挂载、子进程装卸、自我重启/热替换，这些应按编排标签 (`O-Insert`/`O-Dispose`) 的义务审查，不能用组件义务 C 衡量。
**升级路径**：作为组件无法通过小改动进入模型。可拆分：把"市场浏览/搜索/路由/设置/命令"拆成普通组件 (修 R1 的三处后可到第 2 层：逐条注册后立即登记 disposer、模块级 setter 放进 effect、settings inject 改用 `hostCtx`)，把装卸/禁用/重启/HMR 收进一个显式的编排者模块，由宿主提供受控的编排原语 (替代 `internal/plugin` 与直接 `entry.update`)。
**与上一轮审计的差异** (1.73.18 → 1.80.0)：
- 未变：仍无顶层 inject；`desktopProfiles`/`profileContext` 决定启动分支；`internal/plugin` 监听 (`routes.js:776` → `:937`)；`ctx.plugin(HotTree)` 热挂载；`entry.update` 改别人的条目；SIGTERM 重启；`globalThis` 槽；`installMarketSettings(ctx)` 挂在外层 ctx 上 (`index.js:314,366` → `:317,375`)；`void mountClientOnlyDeps` (现包在 `replayBootDisables` 里并捕获异常，修了 #1277 的未处理拒绝)。
- 核对纠正：上一轮说路由处理器"在长寿的 inject 上下文上 `ctx.plugin`"仍成立；但路由本身在 1.73.18 已经收进 `disposers` 并经 `host.effect` 撤销 (旧 `routes.js:2451`)，上一轮 (d) 中"路由不登记"不适用于 dshmarket，缺口只在中途抛错与模块级 setter。
- 新增 (1.80)：`ctx.inject(['commands'])` 登记 `/find-plugin` 命令 (登记在子 fiber 的 `effect` 中 ✓，名字通用)；未注入读取 `llm`、`agentDefaultModel`、`hmr`；经 `hmr.reconcileProfile()` 的自我热替换 (`self-reload.js`) 及其 `globalThis` 实例槽；默认开启的匿名遥测心跳 (`telemetry.js`，计时器在 disposer 中停止 ✓)；`startup-repair-report.js` 的 `globalThis` 报告表；新增 17 个 lib 文件 (catalogs、discovery-cache、offline、policy、release-*、update-notifications 等)，未逐一审查，只按关键词扫过。
- `net.js` 的 undici 全局 dispatcher 修补在 1.73.18 已存在 (`net.js:57`)，上一轮未记，本轮补记为进程级全局改动。

**复核 (2026-11-24)**：自更新 `reloadSelf` (`lib/self-reload.js:158-183`) 只请宿主 `hmr.reconcileProfile()` 把条目换成磁盘上的新版本，自己不写文件；宿主随即由 loader 按 profile 补丁停止并重建条目 (deepseek-harness `packages/boot/hmr/src/index.ts:930`)。这部分属经 loader 的编排，在编排者扩展的模型内。`internal/plugin` 钩子、SIGTERM、子进程装卸仍在模型外。
