# dsh-prime-memory 0.26.72

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主入口 `dist/index.js` (`main`，`dsh.plugin.json` 的 `components.host`)，经 `cordis.patch.yml` 插入为条目 `dsh-memory`；宿主 inject = `llm, tools, systemPrompt, connection, webServer` (`dist/index.js:111` ✔)；不 provide。`dsh.pluginDependencies = ["dsh-reference-session-collector"]`。客户端 `dist/client.js` (`__ModuleLoader__` 包装)，inject = `["slots"]` (`dist/client.js:52247` ✔)，`layout` 走 `ctx.inject` 可选子 fiber 并兜底 `ctx.get`/`ctx.reflect.get` (`:52278-52305`)。
- 一句话功能：L0~L3 分层蒸馏记忆：捕获对话→抽取原子记忆→场景/画像，每步前自动召回注入；本地 SQLite + 本地/远程嵌入 (子进程/Worker)，外部记忆驱动推拉同步，约 30 个 `memory_*` 工具与 `/dsh-memory/rpc` 管理接口。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✗ | 未注入的 get：`settings` (`dist/settings.js:200`，另有 `ctx.inject(['settings'])` 并存 `:122,174`)、`agents` (`dist/hooks/recall.js:751`，`dist/pipeline/runner.js:929` 附近)、`agentDefaultModel` (`dist/llm.js:72`，`dist/stats.js:1844,2868`)、`webStartup`/`webRuntime` (直接读属性并 try/catch，`dist/index.js:82-98` ✔)。注释明确说是"宽容路径"，有意的可选依赖。另外绕过服务模型读别的插件：动态 `import("dsh-reference-session-collector")` 并自开其投影库只读句柄 (`dist/clients/drsc-inproc.js:22-37` ✔)。客户端未注入：`layout`、`locale` (`dist/client.js:52292,40220`)。 |
| 0 | S2 | ✓ | 不 provide。 |
| 0 | S3 | ✗ | `internal/*` 钩子两处：`ctx.on('internal/service', …)` 监视 `settings` 服务上下线后重挂设置 (`dist/settings.js:251` ✔)，监视 `webServer` 实例替换后重挂路由 (`dist/stats.js:400` ✔)。`settings.configure({ auto: false }, ctx.fiber)` 关掉宿主为本插件自动生成的设置表单 (`dist/settings.js:121-127`，经 `sctx.effect` 登记，可接受)。客户端：`MutationObserver` 改侧栏图标，从不 disconnect，靠 `body[data-mem-icon-bodywatch]` 防重复 (`dist/client.js:40291-40297`)；模块级 `window.addEventListener(OPEN_EXPLORER_EVENT)` 不移除 (`:52259-52265`)。 |
| 1 | L1 | △ | 启动是一长串 `await` (建目录、扫孤儿 tmp、开库、各 store init、嵌入源解析、`createMemoryBackend` 起 Worker，`dist/index.js:118-570`)，对固定数据目录有界，但耗时随数据量增长。启动尾部 fire-and-forget 后台重嵌 `void (async …)` (`:414`)、图谱预热 (`:848`) 不在 effect 里，只用 `disposed` 标志取消。周期任务 (`setInterval` 补齐/闲置/有效期回填/外部拉取) 都在 effect 或紧随其后登记 (`:502-510,778-779`，`dist/pipeline/runner.js:433-440`)。 |
| 1 | L2 | ✓ | inject 只有宿主服务；对 collector 的依赖不经服务键，不会造成 PENDING 环。 |
| 2 | R1 | ✗ | 主要资源 (`embedManager`、`downloader`、`stores.backend` 的 Worker、`extAssembly`、`flushL0`、`graphStore`) 只由 `apply` 末尾的一个 `ctx.effect` 统一释放 (`dist/index.js:865-886` ✔)；在它之前有十余处 `await` (`:563,568,571,590,…`)，任何一处抛错都会让已建的 Worker/子进程/计时器泄漏。`ctx.inject(['commands'])` 子 fiber 里惰性打开的只读 `DatabaseSync` 从不关闭 (`:207-219` ✔)。`db.close` 有单独登记 (`:202`) ✓。 |
| 2 | R2 | △ | 处理器侧的外部驱动子进程 (`dist/ext-memory/proc.js:59`)、npm 安装运行时 (`dist/store/runtime-installer.js:56`，10 分钟超时)、本地嵌入 fork/Worker (`dist/store/local-embedding.js:55,167`) 都有超时或 dispose，但经插件对象手工回收，不是子 fiber。模块级状态跨重载：collector 只读句柄 `storeHandle` (`dist/clients/drsc-inproc.js:37`) 从不关闭；`initTraceStore` 设置的模块单例 dispose 时不 `resetTraceStore` (`dist/store/trace.js:133-139`)。 |
| 2 | R3 | △ | 工具名 `memory_search`/`memory_add`/`memory_write`/`conversation_search` 等是通用名，与其他记忆插件撞名的可能性高；RPC 前缀 `/dsh-memory/rpc` (`dist/stats.js:169,347`) 不带包名。读 collector 的数据依赖另一插件的内部存储格式。 |
| 2 | R4 | △ | 持久状态 (保证不覆盖)：`$DSH_HOME/memory` 下 `memory.db`、场景/画像/slot/skills JSON、追踪 JSONL、`memory.log`、嵌入模型与运行时缓存 (`runtime/`)，凭据经 DPAPI (`dist/ext-memory/secrets.js:44` 起 PowerShell)，外部记忆服务上的推送。临时资源泄漏：见 R1/R2。未发现写 `process.env` 或全局 dispatcher。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | ✗ | 启动分支依赖文件系统 (`storageOk` 决定是否注册捕获钩子，`dist/index.js:611-613`；嵌入源状态文件优先于配置，`:180-185`) 与网络/模型可用性，属于"对固定环境合流"；但设置挂接看 `settings` 服务此刻是否在、是哪一代 API (`dist/settings.js:199-247`)，路由看 `webServer` 此刻实例 (`dist/stats.js:315`)，并靠 `internal/service` 事件补挂——依赖时机。 |
| 3 | C3 | △ | 登记类操作 (tools、监听器、路由) 逆与状态无关 ✓；启动期对数据库的迁移/标记 (`db.init`、`markEmbeddingSynced`、`cleanupOrphanTmp`) 无逆，但属持久状态。 |
| 3 | C4 | ✓ | 不直接 dispose 子 fiber。 |
| 3 | C5 | ✓ 未确认 | 未见启动期读取 emit/waterfall 结果。 |

**最高层**：不在模型内。两处 `internal/service` 钩子 + 绕过服务键直接 import 另一插件并打开其数据库，S3 不成立。去掉这些后也只到第 1 层：启动中途抛错会泄漏 Worker/子进程 (R1 ✗)。
**升级路径**：(1) 把 `settings`、`agents`、`agentDefaultModel` 写成 `ctx.inject([...], cb)` 可选子 fiber (已有先例 `:207`、`projection/*.js`)，删除两处 `internal/service` 监听——`webServer` 已在 inject 中，路由直接 `ctx.effect(() => webServer.register(...))` 即可；(2) collector 改为通过它提供的服务读取，或把 `storeHandle` 登记到 fiber；→ 第 1 层。(3) 每建一个资源紧接着 `ctx.effect` 登记其释放 (而不是末尾统一释放)，`commands` 子 fiber 关闭只读连接，启动期后台重嵌改放进 `ctx.effect`；→ 第 2 层 (工具名需加前缀以满足 R3)。(4) 设置/路由不再按服务"当前是否存在"分支后，C2 剩下的只是对固定数据目录合流，可到第 3 层。
