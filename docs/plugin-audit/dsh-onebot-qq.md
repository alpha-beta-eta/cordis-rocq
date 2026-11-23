# dsh-onebot-qq 0.11.0

- 是否 Cordis 插件：是，两个宿主条目 + 一个客户端 (`cordis.patch.yml` insert `dsh-onebot` 与 `onebot-settings-remote`)。
  - 主条目 `lib/index.js`：`name='dsh-onebot'`，`inject = [tools, systemPrompt, agents, sessions, agentDefaultModel, agentPresets, sessionPersistence, workspaceRegistry, commands, llm]` (`lib/index.js:55` ✔)，无 provide。启动体是 `apply` + 一个 async `ctx.effect` (`lib/index.js:357`, `:592-624` ✔)。
  - 设置条目 `lib/settings-remote.js`：`TypertRemoteService` 子类，`static inject = ['configEditor','profileContext']`，provide `onebotSettings` (`lib/settings-remote.js:569-575` ✔；协议包缺失时降级为同名普通服务 `:600-603`)。
  - 客户端 `lib/client.js`：`inject = ['slots','locale','remote']`，注册设置面板与侧栏入口 (`lib/client.js:2320-2367` ✔)。
- 一句话功能：经 OneBot 11 (NapCat) 正向/反向 WebSocket 把 QQ 私聊/群聊桥接到 dsh，每个 QQ 会话一个 agent，按 agent scope 注入平台提示词与 `qq_*` 工具；外加可从设置页改写自身 loader 配置的 Remote。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 未注入读取均为有意的可选依赖且 try/catch 归一为 undefined：`sessionTitle` (`lib/index.js:61-70` ✔)、`userQuestions` (`lib/ask-tool.js:18-27` ✔，在 agent scope 上读)、`loader` (`lib/index.js:474` ✔，只 `await loader.await()`)、设置条目里 `workspaceRegistry` (`lib/settings-remote.js:345` ✔)。客户端 `ctx.get('remote.onebotSettings')` 读自己刚 `$mount` 的动态服务 (`lib/client.js:2338-2339` ✔)。均可改为可选 inject (`inject: { optional: [...] }`)，语义不变。 |
| 0 | S2 | ✓ | 只有 `onebotSettings` 一个 provide，字面量 (`lib/settings-remote.js:50`, `:572` ✔)；主条目不 provide。命名空间带插件前缀，未见冲突。 |
| 0 | S3 | △ | 无 `internal/*`、无猴补丁。两点越界：(1) `qq_*` 工具、`channel:dsh-onebot` 提示词段、`user-questions/request` 监听器登记在宿主 agents 服务创建的 `agentCtx` 上 (`lib/bridge.js:1449-1473` ✔)，由宿主的 setup 回调契约许可，寿命随 agent handle 而非本插件 fiber；(2) 设置 Remote 的 `updateSettings` 经 `configEditor.edit` 改写 `dsh-onebot` 的 loader 条目配置并要求重启 (`lib/settings-remote.js:52`, `:500-535` ✔)——这部分是编排者行为 (改 loader 条目)，属编排者义务，由用户请求触发，不在启动期。 |
| 1 | L1 | ✓ | 启动体有界：`bridge.start()` 只挂监听、把映射加载作为未 await 的 promise (`lib/bridge.js:268-303` ✔)；`connection.start()` 明确"不阻塞"，反向模式开端口、正向模式 `void connectForwardOnce()` (`lib/connection.js:152-164` ✔)；重连 (`reconnectMaxAttempts` 可为 0=无限，`lib/index.js:99`)、心跳、自愈、inject 轮询都是定时器驱动，属 Active 期反应。 |
| 1 | L2 | ✓ | inject 全是宿主服务；主条目不 provide；设置条目 provide `onebotSettings` 只被客户端消费，无环、不依赖后代。 |
| 2 | R1 | ✓ | 启动期副作用集中在一个 async `ctx.effect`，返回 disposer 依次停 inject 通道/bridge/connection；启动中途抛错时手动回滚已启动部分再重抛 (`lib/index.js:592-624` ✔)。`ctx.on('session/event'|'session/flush')` 本身被 fiber 收集，且 `stop()` 再显式 off (`lib/bridge.js:276-281`, `:306-315` ✔)。 |
| 2 | R2 | △ | 运行期效应不走子 fiber，而是手工簿记：每个 QQ 会话 `agents.create/resume` 得到的 handle 放进 registry Map，`bridge.stop()→registry.stop()` 统一 dispose (`lib/registry.js:220`, `:329-343`, `:591` ✔)；打字指示 `setInterval` 挂在 chat 对象上、`.unref()` (`lib/bridge.js:1513` ✔)，撤回/合并/防抖定时器同样手工清理。功能上可回收，但单个会话不能经 Cordis 单独撤销；`ask_user_question` 注册失败时返回 undefined (被宿主同名工具抢先) (`lib/ask-tool.js:180-189` ✔)。改为每会话 `ctx.plugin`/`ctx.effect` 即可满足。 |
| 2 | R3 | △ | 工具名 `qq_send_*`/`qq_napcat_api`/`qq_group_history` 带前缀，登记在 agent scope，冲突面小；`ask_user_question` 故意与宿主工具同名，靠"已存在则跳过"处理 (`lib/ask-tool.js:186-188` ✔)，结果取决于 preset 与本插件谁先登记——相遇不受控。反向模式监听端口 8643 (`lib/index.js:93`) 是进程外共享资源，可能与其他实例撞端口 (有 EADDRINUSE 重试)。 |
| 2 | R4 | △ | 持久状态 (保证不覆盖)：媒体目录 `$DSH_HOME/media/onebot` (`lib/index.js:73-79`)、会话映射/退役/可切换会话 JSON (`lib/registry.js:698`, `:855`, `:917`)、deferred 投递持久化 (`lib/deferred.js:382`)、上下文尾巴 (`lib/chat-tails.js:140`)、trace/inbound 记录、诊断包导出 (`lib/health.js:216`)、loader 配置改写。临时资源：STT 子进程按调用 `spawn` 并有超时 (`lib/stt.js:83-87`)；`/version` 命令同步 `execFileSync('git', ...)` (`lib/commands.js:1336`)；均为运行期短命资源，未见泄漏。进程级/模块级：`setFaceStyle`、`configureSendSegments` 在 `apply` 时写模块级变量 (`lib/index.js:362-365` ✔)，跨重载残留但每次 apply 覆盖；`process.env` 只读 (`DSH_HOME`/`PATH`/`HOME`)。 |
| 3 | C1 | ✓ | 主条目无 provide。设置条目构造即 provide，无条件 (协议在位与否只换基类，名字相同)。 |
| 3 | C2 | △ | 宿主端：启动分支只依赖配置 (mode、traceEnabled、recordInbound、injectEnabled)，`installChannelScope` 在 agent 创建时执行，不在启动期；`sessionTitle`/`userQuestions` 按调用惰性读取，未进入启动分支。但映射/退役会话从磁盘加载决定恢复哪些 agent (`lib/bridge.js:287-299`)——对固定环境合流。客户端 ✗：侧栏两个 slot 是否注册取决于启动时 `remote.getSettings()` 的网络结果 (`lib/client.js:2350-2366` ✔)。 |
| 3 | C3 | ✓ (宿主组件部分) | 所用服务操作是按名登记 (tools、systemPrompt section、`ctx.on`)，逆与状态无关。设置 Remote 的 `configEditor.edit` 是"改值"型状态相关逆，但它在请求处理器里，不属启动程序。 |
| 3 | C4 | ✓ | 不 dispose 启动时 spawn 的子 fiber；不调用 `ctx.plugin`。 |
| 3 | C5 | ✓ | 启动期不读 emit/waterfall/bail 结果；`user-questions/request` 中间件只在运行期参与。 |

**最高层**：1 (宿主主条目接近 2；设置条目因改写 loader 条目带编排者义务)。主条目启动/卸载闭合、有界有秩，但运行期 agent/定时器靠手工簿记而非子 fiber，`ask_user_question` 撞名不受控；客户端启动依赖网络结果。
**升级路径**：(1) 把 `sessionTitle`/`userQuestions`/`loader`/`workspaceRegistry` 改为可选 inject，S1 → ✓；(2) 每个 QQ 会话的 agent handle 与其定时器包进 `ctx.effect` (或 `ctx.plugin` 子 fiber)，并给 QQ 专用的 ask 工具改名 (如 `qq_ask_user_question`)，R2/R3 → ✓，主条目到第 2 层；(3) 第 3 层还需客户端无条件注册侧栏 slot (在组件内按快照隐藏)，并把设置 Remote 的配置改写视作编排者操作排除在组件之外。
