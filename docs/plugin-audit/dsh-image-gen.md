# dsh-image-gen 0.11.4

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主 `lib/index.js` (打包单文件，33802 行，内含 vendored 的 dsh-llm/dsh-tools/dsh-sandbox/dsh-credentials 等库代码)，`inject = ["tools", "attachments", "credentials"]`(`lib/index.js:32263` ✔)，`apply` 在 `:32390`；`connection`、`webServer`(两处)、`systemPrompt`、`settings` 走 `ctx.inject` 子 fiber；无 provide。客户端 `lib/client.js` (134503 行)，`inject = ["slots","connection","remote","locale"]`(`lib/client.js:132072` ✔)，`apply` 在 `:132091`。
- 一句话功能：给 DSH 加图像生成/编辑工具 (Gemini、OpenAI 兼容、Seedream、DashScope、ComfyUI、订阅 OAuth 通道等)，外加画廊、无限画布工作台、灵感库与一组宿主 HTTP 路由。

宿主端：

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✓ | 插件自身代码无 `ctx.get`；可选服务都用 `ctx.inject` (`:32448`、`:32455`、`:32603`、`:32629`、`:33789` ✔)。bundle 中的 `this.ctx.get("approval"/"ptcRuntime"/…)`(`:1762`、`:4662` 等) 属 vendored dsh 库代码，未见被本插件实例化为服务。另：绕过服务直接读 DSH 自己的存储文件 `~/.dsh/storages/workspace.json`(`:8355-8370` ✔)，不经过任何键。 |
| 0 | S2 | ✓ | 无 provide。 |
| 0 | S3 | △ | settings 子 fiber 里把**根** `ctx` 交给 `settings.installSection(ctx, …)`(`:33794` ✔)，登记落在根 fiber 而不是 settingsCtx 上；systemPrompt 子 fiber 里又在**根** `ctx` 上 `ctx.inject(["credentials"], …)`(`:32605` ✔，见 R1)。无元层钩子、无猴补丁。 |
| 1 | L1 | ✓ | 启动同步、无循环；缓存清理是 30s 一次性 + 每日 `setInterval`，在 `ctx.effect` 中并 `unref` (`:32437-32446` ✔)。 |
| 1 | L2 | ✓ | 无 provide/spawn，无环。 |
| 2 | R1 | △ | 路由都在 `webCtx.effect` 里 (`:32458` 起 ✔)，`systemPrompt.context` 在 `promptCtx.effect` 里 (`:32613-32622` ✔)，`tools.register` 直接调用 (`:7094`、`:32815` 等，依赖 dsh 自动挂 fiber)。缺陷：`:32605` 的嵌套 `ctx.inject(["credentials"])` 挂在根 fiber 上，systemPrompt 每重载一次就多一个 credentials 子 fiber 和两份 `credentials/*` 监听器，systemPrompt 离开时不回收；`credentials` 本已在根 inject 中，这层 inject 多余。`installSection(ctx…)` 同理，settings 离开时登记不随之撤销 (未确认 installSection 内部是否另行处理)。 |
| 2 | R2 | ✗ | 订阅登录 `beginLogin` 在 HTTP 处理器里起 OAuth 回调服务器，固定端口 `server.listen(port)`，最长 10 分钟超时 (`:11548-11594` ✔、`:12456` ✔)，未登记到任何 fiber，插件卸载后仍监听。ZIP 导出任务表是模块级状态 (`ensureJob`/`cancelZipJob`，`:9389`、`:9425`)。生成请求的心跳 `setInterval` 在 `finally` 中清除 (`:32040-32053` ✔)。 |
| 2 | R3 | △ | 工具名 `generate_image`、`generate_images`、`edit_image`、`canvas_state`、`view_canvas`、`find_inspiration`(`:7095`、`:7142`、`:32816`、`:32895`、`:33137`、`:33397` ✔) 无前缀，与其他图像插件可能撞名；路由全部在 `/plugins/dsh-image-gen/` 下 (`:5702-5747` ✔)；systemPrompt 段名带前缀。 |
| 2 | R4 | △ | 持久 (保证不覆盖)：凭据库中的 API key 与订阅 OAuth token (`:12474-12479` ✔)、原图 vault、请求图片缓存、保存进工作区的图片、settings。delete 路由会删工作区内文件 (`:32539` ✔)。进程级：未见改 `process.env`、全局 fetch/agent。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | ✓ | 根 fiber 的登记集合固定；可选服务全部经 `ctx.inject` 静态子 fiber。`refreshImageToolContext()` 的异步结果只影响提示文本 (惰性 `text` 函数)，不影响登记。 |
| 3 | C3 | 未确认 | 工具/路由/提示段/监听器都是按名字登记；`settings.installSection` 的逆是否状态相关看不到 (在宿主 settings 服务里)。 |
| 3 | C4 | ✓ | 不直接 dispose 启动子 fiber。 |
| 3 | C5 | ✓ | 启动期不读分发结果。 |

客户端：

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 未注入读取 `configForms`、`settingsScope`(`lib/client.js:132092-132093` ✔)、`remote.credentials`(`:132186` ✔)；`locale`/`remote`/`connection` 已注入。`sessions`、`uiSession`、`uiConversation`、`sidebarRightTabs`、`remote.credentials` 另有 `ctx.inject` 子 fiber。 |
| 2 | R1 | ✓ | 样式、监听、slot 登记在 effect/`slots.inject` 中；`indexedDB.deleteDatabase("dsh_image_gen_canvas")`(`:132119` ✔) 是启动期一次性清旧库，属持久外部状态。 |
| 3 | C2 | ✗ | 启动时按 `configForms` 是否存在决定用哪套设置作用域 (`:132092-132094` ✔)，`credentialsRef` 初值也看未注入服务是否已在；`uiConversation` 子 fiber 置 `promotion.enabled = true` 后不复位 (`:132127` ✔)。 |

**最高层**：宿主 1；客户端 1 (S1 △ 需标注)。宿主卡在 R2 (OAuth 回调服务器不登记) 与 R1 (嵌套 inject 挂错 ctx)。
**升级路径**：(1) `:32605` 改为 `promptCtx.inject` 或直接删掉 (credentials 已注入)；`installSection` 传 `settingsCtx` → R1 ✓；(2) OAuth 回调服务器的 `close` 用 `ctx.effect` 登记 (或接一个随 fiber abort 的 signal) → R2 ✓，宿主到 2；(3) 工具名加前缀 → R3 ✓。若 `installSection` 的逆与状态无关，宿主可到 3。客户端把 `configForms`/`settingsScope` 的二选一改成两个静态 `ctx.inject` 子 fiber，可去掉 C2 ✗。
