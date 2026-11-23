# deep-view 0.1.2

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主入口 `index.js` (`main`)：`name='deep-view'`，`inject=['tools','connection','sessionController','sessions']`，`apply` 只调 `install(ctx, config)` (`index.js:6-11` ✔)；无 provide。客户端 `client.js` (经 `window.__ModuleLoader__.load`，`client.js:2`)：`inject=['slots','uiConversation','locale']` (`client.js:2744` ✔)；清单 `dsh.client` 无 inject。bundle patch 插一行 `deep-view`。
- 一句话功能：注册 `show_view` 工具，让 agent 在聊天里画图表/表格/表单；交互式视图把待答记录存盘，用户在卡片上作答后经 `/api/deep-view` 路由作为下一条用户消息送回会话。

文中路径相对包根。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✗ | 1 处未注入：工具执行时 `ctx.get('agents')` (`src/host/install.js:36` ✔)，有意的可选读取 (缺失时放行)，可直接改为可选依赖。客户端无未注入读取 (`ctx.locale?.register` 只是防御写法，`locale` 已注入)。 |
| 0 | S2 | ✓ | 不 provide。 |
| 0 | S3 | ✓ | 宿主与客户端都没有 `internal/*`、猴补丁、`ctx.plugin`。客户端往 `document.head` 加一个 style，拆除时移除 (`client.js:2753-2765`)。 |
| 1 | L1 | ✓ | `install` 同步、无循环；唯一的重试是作答时 Windows 上 `rename` 至多 6 次 (`src/host/files.js:6-24`)，在运行期。 |
| 1 | L2 | ✓ | 只 inject 4 个宿主服务，无 provide、无 spawn。 |
| 2 | R1 | ✓ | `ctx.tools.register` 由宿主自动挂到调用者 fiber (`D:\deepseek-harness\packages\core\tools\src\index.ts:148` `layers.effect(this.ctx, …)` ✔)；`ctx.on('session/event')` 由 Cordis 登记；路由 `connection.fetch.register` 包在 `ctx.effect` 里 (`src/host/install.js:136-146` ✔)。注册抛错被吞掉时没有残留 (抛在插入之前)。 |
| 2 | R2 | ✓ | 处理器只做三件事：读写 `pending.json`、`agent.followup(createUserMessage(...))` 加 `sessions.flush` (`install.js:116-119`)、按 user/message 丢弃待答记录。前者是有意持久，后者是向会话投递用户消息，即插件的功能，本来不该撤销。没有挂在长寿上下文上的计时器或监听器。 |
| 2 | R3 | ✗ | 工具名 `show_view` 是通用名，README 与注释都写明旧版 DS Bot 也在全局注册同名工具 (`install.js:75-82` ✔，`README.md:5,19`)：撞名时本插件的工具静默不登记。路由 `/api/deep-view`、slot id `deep-view-views`、key `deep-view-reply`、事件定义 kind `deep-view-views`/`deep-view-reply` (`client.js:2378,2647`) 带前缀。客户端事件定义按工具名 `show_view` 匹配 (`client.js:2381`)，以 `presentationMeta.owner` 区分归属 (`install.js:20`)。 |
| 2 | R4 | — | 持久状态 (保证不覆盖)：`$DSH_HOME/deep-view/pending.json` (或 `config.home`)，按会话存待答视图，有意跨重启 (`src/host/pending.js:1-2,22-31`)。进程级：只读 `process.env.DSH_HOME`，无改动。临时资源泄漏：写临时文件成功而 `rename` 失败时留下 `pending-<pid>-<ts>.tmp` (`pending.js:25-27`)，小问题。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | ✗ | `ctx.tools.register` 包在 try/catch 里 (`install.js:78-82` ✔)：别的插件先登记了全局 `show_view` 时，本插件照常激活但不登记工具，启动结果取决于激活顺序。客户端每一步都包在 `step` 的 try/catch 里 (`client.js:2746-2752`)，失败只打日志，部分登记 (△)。 |
| 3 | C3 | ✓ | 工具、监听器、路由、slot、事件定义都按名字/句柄撤销，与状态无关。 |
| 3 | C4 | ✓ | 不 spawn 子 fiber。 |
| 3 | C5 | ✓ | 启动期不分发、不读分发结果。 |

**最高层**：2 (前提是把 `agents` 标为可选依赖；严格按现写法 S1 ✗)。登记都在 fiber 上，运行期效应要么是有意持久的文件，要么是功能本身的消息投递。第 3 层被"撞名则静默不登记"挡住。
**升级路径**：(1) inject 增加可选依赖 `agents` → S1 ✓，第 0–2 层成立 (R3 的撞名仍记为 △/✗，取决于是否同时装旧版 DS Bot)。(2) 给工具换一个带前缀的名字 (或改为由宿主仲裁的作用域工具)，并去掉 `tools.register` 外的 try/catch，客户端去掉 `step` 吞错，则启动结果与激活顺序无关、无失败，可到第 3 层。
