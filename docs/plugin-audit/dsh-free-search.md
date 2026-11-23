# dsh-free-search 0.9.82

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主 `lib/index.js` (`main`)，函数插件 `apply` (`lib/index.js:1543` ✔)，`name = "web-search-free"`，`inject = ["web","settings","tools","systemPrompt"]` (`lib/index.js:1184-1188` ✔)；静态子 fiber：`webStartup`、`settings`×2、`["webServer","settings"]`、其中再嵌 `connection.authentication`、`tools`×8 (含 `research.js`/`domain_engines.js` 里的)、`systemPrompt`。无 provide (不 provide 服务；向 `web` 登记 provider)。客户端 `lib/client.js`，`inject = ["slots","commandUi"]` (`lib/client.js:3982` ✔)。另有独立 stdio MCP 服务器 `bin/mcp.js` 与 `bin/restore.js` CLI，不属于插件生命周期，未打分。
- 一句话功能：给 dsh 的 `web` 服务登记搜索 provider `ddg` 与抓取 provider `fs-quality-fetch` (42 个搜索引擎的路由/回退)，并登记 9 个工具、系统提示段、设置页 bridge 路由；启动时**改写 `web` 条目的配置**把默认 provider 接管成自己。

## 宿主

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | `ctx.get("credentials")` 未注入，运行期每次调用时取 (`lib/index.js:1638` ✔，注释说明是因跨 bundle 顺序有意晚取)；bridge 里 `connectionContext.get("connection")`，而注入的是 `connection.authentication` (`lib/index.js:2450-2474` ✔)。均可改为可选依赖。 |
| 0 | S2 | ✓ | 无 provide。 |
| 0 | S3 | ✗ | (1) **改别的插件的 loader 条目配置**：启动时在 `ctx.inject(["settings"])` 子 fiber 里 `sctx.settings.mutate("web", ops)` 把 `web.searchProvider`/`fetchProvider` 改成 `ddg`/`fs-quality-fetch` (`lib/index.js:2554-2631` ✔)，运行期设置事件里再次改写 (`lib/index.js:2353-2382,2388-2405` ✔)；注释自认"provider 写入会重建 web 服务并重新 apply 本插件" (`lib/index.js:2421` 附近)。(2) 旧宿主分支直接写服务实例属性 `web.searchProviderId = id` (`lib/index.js:2516-2517` ✔)，属猴补丁。(3) bridge 路由 `updatePlugin` 执行 `exec("pnpm add dsh-free-search@latest")` 自升级 (`lib/index.js:803` ✔)。(4) 模块级 `appliedContexts` WeakSet 重入保护 (`lib/index.js:220,1546` ✔)，承认 Cordis 会在同一 ctx 上重复 apply。→ 它对 `web` 条目承担的是**编排者**行为。 |
| 1 | L1 | △ | apply 同步部分有界；出口探测 `resolveAutoDefaultProvider()` fire-and-forget (`lib/index.js:1631` ✔)。但存在"写 web 配置 → web 重建 → 本插件重新 apply → 再判定是否写"的回路，靠"已经是自己的 id 就不写"(`lib/index.js:2366`、`2391` ✔) 和 `reclaimAttempted` 收敛；有界性依赖这一幂等约定，写锁超时时注释说"下一轮 apply 再来" (`lib/index.js:2620-2628`)。 |
| 1 | L2 | ✓ | 只 inject 宿主核心服务，无 provide，无环。 |
| 2 | R1 | ✓ | `registerSearchProvider`/`registerFetchProvider` 在 apply 顶层调用 (`lib/index.js:2520,2549` ✔)，返回值被丢弃，但 dsh 文档说明登记随调用 fiber 撤销 (`D:\deepseek-harness\packages\extensions\tool-cordis\src\api-catalog.ts:4306`)；工具、bridge 路由、提示段都在 `sctx.effect` 里。 |
| 2 | R2 | △ | 运行期在处理器里重登记而不建子 fiber：`localizedEffect` 在 `settings/document-updated` 里撤旧工具再 `register` 新的 (`lib/prompt_i18n.js:354-391` ✔)；`refreshPrompt` 从设置事件和出口探测的 promise 里重建 `systemPrompt.section` (`lib/index.js:3747-3763` ✔)——`refreshPrompt` 是外层闭包，`systemPrompt` 子 fiber 撤销后探测 promise 仍可能调用它，往已撤销的 `sctx` 上登记。都用闭包 disposer 在 fiber 撤销时清理，属可重构。 |
| 2 | R3 | ✗ | 搜索 provider id 用通用名 `"ddg"` (`lib/index.js:2042` ✔)；`registerOnce` 遇 `WEB_DUPLICATE_PROVIDER` 时**吞掉错误并"复用"别人的同名登记** (`lib/index.js:1552-1563` ✔)，随后仍把 `web.searchProvider` 指向 `ddg`——相遇结果依赖别的插件登记的条目。工具名 `weather`、`research`、`multi_search`、`advanced_search`、`video_search` 等不带前缀 (`lib/index.js:3156-3641`、`lib/research.js:825,1377` ✔)，易与其他插件撞名。接管判定读的是 `web` 条目当前值 (是否为出厂默认)，依赖别的插件/用户是否已写过。 |
| 2 | R4 | △ | 持久状态 (保证不覆盖)：`web` 条目的 provider 选择 (有意不在 dispose 时还原，`lib/index.js:739-741` ✔，改为设置页手动 `restoreOfficialProvider`)；本条目 config (旧 settings.yaml 迁移，`lib/index.js:1669-1686`)；`$DSH_HOME/free-search-cooldowns.json` (`lib/index.js:253`、`lib/cooldown.js:126-128` ✔)；`~/.cache/dsh-free-search/research.db` (`lib/cache.js:15-17` ✔，模块 import 时打开，从不关闭)；自升级改动 profile 的 node_modules。临时资源：浏览器抓取 `spawn` (`lib/fetch_provider.js:90`，有 taskkill)、`execFile` 调外部 CLI (`lib/agy.js:159`、`lib/platform_engines.js:443`，带 timeout)，都是请求内的，未登记到 fiber。进程级：模块级可变全局 (`autoDefaultProvider`、`bridgeTrust`、`setActiveBlockedDomains`/`setActiveAcceptLanguage`，`lib/index.js:171,634`)，跨重载保留。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | ✗ | 启动时是否改写 `web` 配置取决于 `web` 当前选中的 provider (`lib/index.js:2557-2596` ✔)；系统提示段内容取决于出口地区网络探测 (`cloudflare.com/cdn-cgi/trace`，`lib/index.js:167` ✔) 何时返回；`registerOnce` 成败取决于别的插件是否先登记了 `ddg`。 |
| 3 | C3 | ✗ | 对 `web` 条目的 `settings.mutate` 是"设为 v"型写入，逆依赖旧值，且根本没登记逆。 |
| 3 | C4 | ✓ | 不直接 dispose 子 fiber。 |
| 3 | C5 | ✓ | 启动期不读取分发结果。 |

## 客户端

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 未注入 `ctx.get("layout")` (`lib/client.js:4198` ✔)；`locale` 经 `ctx.inject(["locale"])` 子 fiber 取，✓。 |
| 2 | R1/R2 | △ | slot 登记都在 `ctx.slots.inject` 里；但侧栏入口在 bridge fetch 的 promise 回调里用**外层** `ctx.slots.register` 登记 (`lib/client.js:4022-4070` ✔)，靠闭包在 slot 撤销时清理。模块级 `localeFace`、`sidebarEntryController` 可变状态。 |
| 3 | C2 | △ | 侧栏入口是否登记取决于 bridge 返回的配置 (网络往返)；对固定配置合流。 |

**最高层**：不在模型内 (照现状)。决定性的是 S3：启动和运行期都改写 `web` 插件的配置条目、触发它重建并重新 apply 自己，还有服务实例属性写入与自升级，这些是编排者行为；R3 的 `ddg` 撞名吞错也直接破坏相遇受控。
**升级路径**：(1) 去掉启动/运行期对 `web` 条目的 `settings.mutate` 与 `web.searchProviderId` 写入，改由 bundle patch 或设置页的显式操作 (已有 `restoreOfficialProvider` 的对称物) 完成；`updatePlugin` 移出插件 (或标为编排者动作)——到第 0 层。(2) provider id 改为带前缀的 `free-search` 类名字、重名时报错而不复用；工具名加前缀；`credentials` 改可选依赖——到第 2 层 (R2 的重登记再挪进子 fiber 更干净)。(3) 出口探测只影响搜索路由、不影响登记内容 (或把提示段作为反应期效应)，即可视为对固定环境合流，到第 3 层。
