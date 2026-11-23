# dsh-connect-workbuddy 5.31.0

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主 `lib/index.js` (`main`，tsdown 打包，16949 行；部分代码在 `lib/host-heartbeat-AVovVGqY.js`)，函数插件 `apply(ctx, config)` (`lib/index.js:14462` ✔)，`name = "dsh-connect-workbuddy"`，`inject = ["llm","settings"]` (`lib/index.js:13894-13896` ✔)；动态子 fiber：`tools`×3、`commands`、`sessionProjections`、`webServer`、`settings`。无 provide。客户端 `lib/client.js`，`inject = ["slots","locale"]` (`lib/client.js` 末尾 ✔)。另有 `lib/bin.js` CLI 与 `native/turing-sdk/worker.cjs` 子进程脚本，未打分。
- 一句话功能：复用本机 WorkBuddy/CodeBuddy 桌面端的登录凭据，把 WorkBuddy 国内版/国际版模型作为 LLM provider 接入 dsh (经本地 loopback 中转 shim)，附带账号池换号、积分/签到、图片/视频生成工具和 `codebuddy` CLI 桥。

## 向 llm / 模型目录登记了什么 (重点)

全部在 `shim.ready` 之后的异步回调里 (`lib/index.js:16810-16910` ✔)：
- `ctx.llm.registerAdapter(["workbuddy"], …)` 与 `ctx.llm.registerAdapter(["workbuddy-global"], …)` (`lib/index.js:16861-16862` ✔；常量 `lib/index.js:1750,1752` ✔)。
- `ctx.llm.registerConfigurableProviders([{provider:"workbuddy",…},{provider:"workbuddy-global",…}])`，`settingsNs` 为本插件 loader 条目 id，`declared:false` (`lib/index.js:16863-16875` ✔)。
- `ctx.llm.registerModelDiscovery(settingsNs, …)` (`lib/index.js:16895` ✔)，返回值被丢弃 (dsh 文档：随 fiber 撤销)。
- 之后 `syncRegionRegistration` 用句柄的 `replace` 按区开关增删上面的 provider (`lib/index.js:15103-15112` ✔)，并在每次 `loader/volatile-update` 时重跑。
- 撞名：provider id 是裸的 `workbuddy` / `workbuddy-global`，不带插件前缀。dsh 的 `registerAdapter`/`registerConfigurableProviders` 遇已有同名 provider 抛 `DUPLICATE_ADAPTER`，全有或全无 (`D:\deepseek-harness\packages\extensions\tool-cordis\src\api-catalog.ts:1926,1938`)；插件在 `finally` 里回滚已成功的半边，再 `catch` 记日志后**静默停在"已激活但无 provider"**状态 (`lib/index.js:16876-16917` ✔)。本地语料中未见其他插件登记这两个名字；`dsh-cost-meter` 只把 `workbuddy` 当已知 provider id 读取 (`dsh-cost-meter/lib/index.js:1068,1692`)，不登记——但它的计费按此名字归类，二者是按名字的隐式耦合。用户自定义 provider 是否会取同名，未确认。

## 宿主

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 未注入读取：`ctx.get("agents")` (`lib/index.js:14798` ✔)、`ctx.get("tokenMeter"/"compaction"/"agents")` (`lib/index.js:16813-16817` ✔)、`ctx.get("attachments")` (`lib/index.js:16829` ✔)，都是请求期的可选能力，可改可选依赖。`settingsNamespaceOf` 读 `ctx.fiber.entry.options.id` (`lib/index.js:13920-13923` ✔)，是元层读取 (只读自己的条目)。 |
| 0 | S2 | ✓ | 无 provide。 |
| 0 | S3 | △ | 无 `internal/*`、无猴补丁、不改别的插件条目。边界情况：`ctx.inject(["settings"], sctx => ctx.effect(() => settings.configure({auto:true}, ctx.fiber)))` 用**外层** `ctx.effect` 承载子 fiber 里拿到的服务 (`lib/index.js:16756-16759` ✔)；监听 loader 级事件 `loader/volatile-update` (`lib/index.js:16787` ✔)；执行 WorkBuddy 桌面端可执行文件 `-e` 脚本读取其本地存储密钥 (`lib/host-heartbeat-AVovVGqY.js:840` ✔)——这是读外部应用状态，不越 Cordis 边界。 |
| 1 | L1 | ✓ | apply 同步部分只构造对象、登记监听与子 fiber；按区 `for` 有界。provider 登记、目录拉取、旧账号归属判断都在 promise 里 (`lib/index.js:16794-16801,16810` ✔)；签到/增长用可清理的单次 `setTimeout` 重排 (`lib/index.js:16589,16725` 附近)。 |
| 1 | L2 | ✓ | inject `llm`,`settings`，子 fiber 只等宿主服务，无 provide，无环。 |
| 2 | R1 | △ | 每区的 shim 在 apply 早期就启动 loopback HTTP 服务器 (构造时即 `createServer` + `listen`，`lib/index.js:6506-6521`，调用点 `14619` ✔)，但关闭它的 `ctx.effect` 到 `lib/index.js:16804` 才登记；中间任何同步抛错都会泄漏监听端口。其余 (turing 定时刷新、增长计时器、渠道续写监听) 各有 effect (`lib/index.js:14520,16753,14805` ✔)。 |
| 2 | R2 | ✗ | 核心服务操作 (adapter、目录、模型发现的登记) 不在启动程序里，而在 `shim.ready` 的 promise 回调中做，且在回调里调用 `ctx.effect` 登记撤销 (`lib/index.js:16884` ✔)——运行期效应直接挂在主 fiber 上，不是子 fiber。`loader/volatile-update` 处理器里按配置 `replace` provider 列表、增删图片/视频工具与 CLI 工具/命令 (`lib/index.js:15113-15137,15197-15215` ✔)，靠闭包 disposer 管理。启动后的异步目录拉取会写回本条目配置 (`repairRegionCatalog`/`healRegionsFieldIfCorrupt`，`lib/index.js:14837,14876`，经 `settings.mutate`，`lib/index.js:1467` ✔)。 |
| 2 | R3 | △ | provider id `workbuddy`/`workbuddy-global` 不带前缀 (见上节)，撞名时插件静默失效。路由都在 `/plugins/dsh-connect-workbuddy/` 前缀下 (`lib/index.js:740-920,13552` ✔)；工具 `workbuddy_draw_image`/`workbuddy_draw_video` 带前缀 (`lib/index.js:6925,7691` ✔)，但 `codebuddy_ask` 工具与 `codebuddy` 命令 (`lib/index.js:9610,9712` ✔) 用的是另一产品名，若有 CodeBuddy 自己的插件会撞名。 |
| 2 | R4 | △ | 持久状态 (保证不覆盖)：本条目配置 (`regions` 目录、开关；`lib/index.js:1467,14784` ✔)；`$DSH_HOME/.workbuddy-host-heartbeat.json` (`lib/host-heartbeat-AVovVGqY.js:11627,11641` ✔，dispose 时清理)；账号池、每日签到、首见名单、设备档案等本地存储；读取 WorkBuddy 桌面端的凭据文件。临时资源：loopback 服务器 (有 close)、turing SDK 子进程 (`lib/host-heartbeat-AVovVGqY.js:10736`)、`codebuddy` CLI 子进程 (`lib/index.js:8806`，带 taskkill)，都未登记到 fiber 而由闭包管理。无进程级全局改动 (`process.env` 只读)。 |
| 3 | C1 | ✓ | 无 provide (空真)。 |
| 3 | C2 | ✗ | apply 返回时 provider 尚未登记；何时 (以及是否) 登记取决于 loopback 端口何时就绪、同名 provider 是否已被占用 (`lib/index.js:16810-16917` ✔)。登记的模型目录内容随后由网络拉取 (`client.fetchModels`) 替换并写回配置 (`lib/index.js:16921-16943` ✔)。这是对时机的真实依赖，不只是固定环境。 |
| 3 | C3 | △ | `registerAdapter`/`registerConfigurableProviders` 按名字登记，逆与状态无关；但随后立即用 `replace` 按当前配置改写 (`lib/index.js:16894`)，`replace` 的逆依赖旧列表；本条目配置写入是状态相关的 (持久，按 R4 不计)。 |
| 3 | C4 | ✓ | 未见直接 dispose 子 fiber。 |
| 3 | C5 | ✓ | 启动期不读分发结果。 |

## 客户端

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | `softGet = name => ctx.get(name)` 读未注入服务 (如 `layout`，`lib/client.js:16964` ✔)。 |
| 2 | R1/R3 | ✓ | `locale.register` 在 `ctx.effect` 中；slot 登记都在 `ctx.slots.inject` 内 (`lib/client.js:17020,17105` 附近 ✔)。未见 `window` 全局写入或加载器包装。 |

**最高层**：1 (△ 视为加标注/小重构后可达)。第 2 层卡在 R2：核心 provider 登记推迟到启动后的 promise 回调里、在回调中往主 fiber 上挂效应，配置变化时又在处理器里 `replace`/增删工具。第 3 层另卡在 C2 (登记时机依赖 loopback 就绪与撞名结果)。
**升级路径**：(1) 把 "等 shim 就绪 → 登记 adapter/目录/发现" 放进一个 `ctx.plugin` 子 fiber (或让 apply 成为 async 启动程序、await `shim.ready` 后同步登记)，loopback 服务器的 close 在创建时立刻登记——到第 2 层；配置驱动的 `replace`/工具增删改为按配置重建子 fiber 更干净。(2) provider id 改为带插件前缀或撞名时显式报错 (标注与 `dsh-cost-meter` 按名耦合的约定)。(3) 目录的网络刷新只作为 Active 期反应、不影响首次登记的键集合，可视为对固定环境合流，到第 3 层 (C3 的 `replace` 仍需说明)。
