# dsh-context 0.87.1

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主 `lib/index.js` (tsdown 压缩 bundle，行号只到压缩行) 导出 `name='dsh-context'`、`inject=['sessionProjections']`、`apply=Tf` (`lib/index.js:32` ✔ 末尾 `export{…}`)。静态子 fiber：3 个 `ctx.inject` (`['sessionQuery','sessionProjectionCache','sessionPersistence','sessions']`、`['systemPrompt']`、`['sessionProjectionCache','storageDomain']`) 加 15 条路由各经 `X({deps,…})` → `ctx.inject(deps, …)` (`:25` ✔)。无 provide。客户端 `lib/client.js`，`inject: ['slots','locale']`。
- 一句话功能：上下文洞察面板与命令：按会话折叠事件成"上下文时间线/头部/活动"投影，提供概览、明细、增量、余额等 HTTP 接口，并在系统提示前后插入可配置的段落。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✗ | 宿主约 14 个名字未注入地读取 (未逐处区分是否位于带 deps 的子 fiber 内)：`sessionPersistence` ×7 (所有路由 deps 都不含它)、`tools` (`ctx.get('tools', false)`，`:26`)、`llm`、`settings`、`credentials`、`deepseekAccount` (0.87 新增，`:26`)、`appReady` (新增，`:32`)、`agents`、`agentPresets`、`skills`、`workspaceRegistry`、`attachments`、`dshHomePath` (`:32` `Sf`)；`fleet` 路由 deps 只有 `connection` 却读 `sessions`/`sessionPersistence`。都带空值兜底，属有意的可选读取。客户端另有约 8 个 (`sessions`、`sidebarRight`、`connection`、`uiWorkspace`、`uiConversation`、`pluginNavigation`、`inputTriggers`…)。 |
| 0 | S2 | ✓ | 无 provide。 |
| 0 | S3 | ✗ | 猴补丁：替换 `tools` 服务实例上的 `register` 为归因包装 (`c.register=l`，`lib/index.js:26` ✔ 函数 `qo`)，并监听元层事件 `internal/get` 观察谁读了 `tools` (`:26` ✔)；卸载时仅在 `c.register===l` 时还原。另用 `{prepend:true}` 的 `agent/pre-step` waterfall 监听器改写消息 id (`Fd`，`:32`)，是普通监听，不越界。 |
| 1 | L1 | ✓ | `apply` 同步、有界。后台工作 (启动回填 `Oc` 的遍历、5 分钟级缓存清扫、worker 池) 都在 effect/inject 回调里启动，属 Active 期间的反应；回填失败重试至多 10 次、指数退避 (`:32` `C()`)。`cf` 的行压缩 `lf` 遍历有限表。 |
| 1 | L2 | ✓ | 顶层只 inject 宿主提供的 `sessionProjections`；子 fiber 的 deps 均为宿主服务；无 provide/spawn 环。 |
| 2 | R1 | △ | 启动期登记大多自动收集：路由经 `ctx.effect(() => connection.route(…))` (`oo`，`:25` ✔)；`sessionProjections.register`、`systemPrompt.section` 都经宿主 layers.effect 挂到调用者 fiber (dsh `session-projection/src/index.ts:338`、`system-prompt/src/index.ts:484`)；worker 池、回填、计时器都有 `ctx.effect` 清理。缺口：猴补丁的还原条件式 (若之后别人也包装了 `register`，则不还原)。 |
| 2 | R2 | △ | 处理器只改局部 Map / 计时器，或返回 waterfall 结果。`cf`→`lf` (`:32`) 在 inject 回调里启动不可取消的异步循环，把持久化的 `contextTimeline` 行从 ver 36 改写为 37 (卸载不停止，写的是持久行)。 |
| 2 | R3 | △ | 路由都在 `/api/dsh-context/` 前缀下；系统提示段名 `dsh-context:prompt-prefix/suffix`。投影键 `contextTimeline`、`contextHeaders`、`contextActivity` 等是共享注册表中的通用名，理论上可能撞名。`tools` 归因依赖别的插件登记的工具及其登记时机。 |
| 2 | R4 | △ | 持久状态：投影缓存表 (`storageDomain` 的 `session_projcache`)、overview 磁盘缓存、`dsh-context-version-probe` 路径下的模块解析 (只读)。临时资源：worker 线程由空闲超时与 effect 终止 ✓。未见 `process.env` 写入、`globalThis` 槽或全局 agent。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | ✗ | 启动分支依赖环境探测：`Sf` 用 `import.meta.resolve`/`createRequire` 探测宿主 dsh 版本 (`:32`)，不兼容时只登记 3 个兜底投影就 `return` (`Tf`，`:32` ✔)——对固定安装合流。启动回填是否等 `appReady` 取决于未注入的 `appReady` 是否存在 (`:32`)，影响的是后台工作的时机，不是登记集合。归因 `qo` 读启动时已登记的全局工具集合作为 `<unknown-plugin>` 的判据，结果依赖激活顺序。 |
| 3 | C3 | ✗ | 猴补丁的逆"若仍是我的包装则改回原函数"与状态相关；其余 (投影、段、路由、监听) 按名字登记，逆与状态无关。 |
| 3 | C4 | ✓ | 未直接 dispose 启动时的子 fiber (回填的 `D()` 调用的是自己 inject 返回的 disposer `E`，仅在被外部显式停止时用，未见在启动路径调用；未完全确认)。 |
| 3 | C5 | ✓ | 启动期不 emit、不读分发结果。 |

客户端：`inject ['slots','locale']`，约 8 处未注入 `get`；React hook 里的 `setInterval` 有 `clearInterval` 清理；`localStorage` 为有意持久。

**最高层**：0 (且 S1、S3 为 ✗：大量未注入读取，加上替换 `tools.register` 与 `internal/get` 元层钩子)。若把可选读取视为可接受，猴补丁仍使它不在模型内。
**升级路径**：(1) 去掉对 `tools.register` 的替换与 `internal/get` 监听，改由宿主提供"工具所有者"查询 (或接受归因缺失)，可回到模型内；(2) 把 `sessionPersistence` 等加入相应路由的 deps，其余声明为可选依赖；(3) 让 `lf` 行压缩在 dispose 时可中止。完成 (1)(2) 后可到第 2 层 (登记已基本全部挂 fiber)；第 3 层还需版本探测分支被视为"对固定环境合流"。
**与上一轮审计的差异** (0.83.1 → 0.87.1)：
- 未变：猴补丁 `tools.register` 与 `internal/get` 监听仍在；版本探测的兜底分支仍在；路由结构与 deps 基本相同；客户端未注入读取的集合不变。
- 新增：`/api/dsh-context/delta`、`/api/dsh-context/history` 两条路由 (`/history` deps 只有 `connection`)；启动即自动回填 (`autoStart:true`，0.83 的 `hs(...)` 无此项)，在 effect 中启动并可经 `AbortController` 中止，等待未注入的 `appReady`；新增未注入读取 `deepseekAccount`、`appReady`；新增 `session/created` 监听。
- 本轮按新四层框架判定，上一轮的 (c) △ 改为 L1 ✓ (后台循环都在 effect 里、重试有上限)；上一轮 (d) ✗ 中的"恢复已登记"现可确认：路由、投影、提示段、worker、计时器都挂 fiber，剩下的缺口只是猴补丁还原的条件式与 `lf` 循环。
- 说明：源码克隆 `D:\dsh-plugins\src\dsh-context` 停在 0.83.1 (`3ff6859`)，本轮只依据发布包的压缩 bundle，行号为压缩行。
