# dsh-pet 0.4.9

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主入口 `lib/index.js` (源码随包发布，`src/host/index.ts`，与 bundle 逐处对应，如 `lib/index.js:10338` inject、`:2463` provide)；`name='pet'`，`inject=['webServer','agentDefaultModel','credentials','llm','commands','connection']` (`src/host/index.ts:37-39` ✔)；provide `petApi7340` (`src/host/plugin/setup.ts:203` ✔)。客户端 `lib/client.js` (源码 `src/client/app.ts`)：`inject=['slots','locale','connection','remote','remote.commands','commandUi']` (`src/client/app.ts:72` ✔)，在页面容器里也 provide `petApi7340` (`:86`)。清单 `dsh.client.inject` 写的是包名 `@deepseek-ai/dsh-client-connection`，与代码里的服务名列表不是一回事。另有 `bin` 独立模式 (伪 ctx)，不在本次范围。
- 一句话功能：桌宠。宿主侧提供 `/dsh-pet-7340` 前缀路由、`/balance` `/pet` `/chat` 命令、余额/碎碎念/待办轮询、会话事件 → 工作状态与通知，并拉起 Electron 桌面 Helper 子进程；客户端画 overlay、设置页、侧栏对话。

文中路径相对包根；`src/...` 即随包源码。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✗ | 宿主 5 个未注入名字，全经软读 `get(name,false)`，有意为之、都有缺省分支，可直接改为可选依赖：`standaloneAi`/`speechToText`/`attachments`/`shutdownApp` 经 `optionalService` (`src/host/plugin/setup.ts:130-134` ✔)，`deepseekAccount` (`src/host/plugin/balance-poll.ts:100` ✔)。客户端 5 个：`uiWorkspace`、`sessions` (`src/client/app.ts:106,110` ✔)、`shortcuts` (`src/client/app-shortcut.ts:115`)、`sidebarRight`/`sidebarRightTabs` (`src/client/chat/register.ts:65,82`)；另 `get` 作为函数传出，名字运行时决定 (`src/client/baifan.ts:66` ✔)。 |
| 0 | S2 | △ | `petApi7340` 字面量、无条件，后缀防撞名；但清单无 provide 元数据，p 只能从代码推出。宿主与客户端同名 provide，分属两个容器 (注释 `setup.ts:200`)。 |
| 0 | S3 | 宿主 ✓ / 客户端 ✗ | 宿主：无 `internal/*`、无猴补丁、无 `ctx.plugin`；`ctx.emit(ctx.webServer,'webserver/entry-url',…)` 收集入口 (`src/host/plugin/desktop/site-url.ts:26` ✔) 是普通分发。客户端：猴补丁 `commandUi.candidates` (`src/client/command-faces.ts:32,58-61` ✔，`lib/client.js:15951`)，有恢复但假设之后无人再包装；设置页导航图标经 `MutationObserver` 改 DOM (`src/client/nav-icon.ts:142`)，在模型外。 |
| 1 | L1 | △ | `apply` 同步有界。但启动末尾 `startHelper()` (`src/host/index.ts:231` ✔) 在效应之外起了：500ms 端口等待重试循环 (`src/host/plugin/desktop/spawn.ts:95-100` ✔，无上限，只打日志)、最长 10 分钟的 Electron 下载 (`spawn.ts:197`，`src/host/helper/electron.ts:225`)、Helper 崩溃重启循环 (`src/host/helper/child.ts:360`)。应当作 Active 期间的反应。其余轮询都在 `ctx.effect` 内 (`src/host/plugin/loops.ts:60,102,240`，`todo-reminders.ts:142`)。 |
| 1 | L2 | ✓ | 只 inject 6 个宿主服务，provide 1 个，无 spawn；无环，不等待后代。 |
| 2 | R1 | ✗ | 已登记：路由 (`src/host/plugin/http-route.ts:73` ✔)、3 个命令 (`command-*.ts:24-28`)、会话监听 (`session-watch.ts:154,265` ✔)、轮询、日志文件 (`setup.ts:114`)、卸载清理 (`lifecycle.ts:31-43` ✔，停 Helper、清计时器与等待者)。Helper 的启动在效应外，但其撤销已先登记在 lifecycle 效应里，算 △。未登记 (0.4.9 新增为主)：`setCityProvider(...)` 改模块级回调 (`src/host/index.ts:86` ✔，`environment.ts:38`)；`setDefaultLogger(log)` 模块级默认 logger，卸载后指向已 dispose 的 logger (`setup.ts:110`)；4 个内置语音实现 `ensure*Provider` 写进模块级注册表，不留 disposer (`src/host/index.ts:114-127` ✔，`voice/registry.ts:18`、`voice/speech-registry.ts:11`)，且 `ensure` 见已有就跳过 (`voice/builtin-edge.ts:40-42` ✔)：若模块实例跨重载保留，闭包里捕获的是第一次激活的 `ctx.credentials` 与 `optionalService`。 |
| 2 | R2 | △ | 会话监听里的计时器按会话存 Map，在效应拆除时清 (`session-watch.ts:255-258,303-307` ✔)；轮询以 `disposed` 标志加 `clearTimeout` 收尾。都由效应承载，但不是逐次反应的子 fiber。`petApi7340.*.register` 只返回裸 disposer，第三方的登记不会自动挂到调用者 fiber 上 (`src/host/balance/registry.ts:30-43`，`voice/registry.ts:28-35`)，与旧 `webServer.register` 同类。客户端拆除时向宿主路由发 `DELETE` (上一轮结论，未重新确认)。 |
| 2 | R3 | △ | 路由前缀 `/dsh-pet-7340`、服务名 `petApi7340` 已防撞。命令名 `/chat`、`/balance`、`/pet` 是通用名，可能与其他插件撞名；客户端 slot id `pet`/`baifan`/`pet-config` 同理。余额/语音/识别/记忆注册表按 id 互斥，重复则抛 (`balance/registry.ts:36`)。 |
| 2 | R4 | — | 持久状态 (保证不覆盖)：`$DSH_HOME/dsh-pet/` 下的 `main-config.jsonc`、`pet/`、`logs.txt`、待办、对话记忆、语音缓存；启动时把 `main-config.json` 一次性改名为 `.jsonc` (`src/host/config/read.ts:20-24` ✔)；Electron 下载到 `$DSH_HOME`。进程级：应用模式下写 `process.env.DSH_PET_PETS` 并调用 `globalThis.__dshPetRebuildUi` (`src/host/plugin/desktop/sync.ts:41-42` ✔，仅 `DSH_PET_IN_PROCESS=1`，DSH 插件模式不走)。临时资源泄漏：上述模块级注册表与回调；卸载不能中止 Electron 下载 (只有超时，下载完后因 `disposed` 不再拉起)。 |
| 3 | C1 | ✓ | `petApi7340` 在 `createHostSetup` 中无条件 provide (`setup.ts:203`)，在任何可失败分支之前。 |
| 3 | C2 | ✗ | `startHelper` 的分支取决于配置文件 (有无桌面宠物)、`DISPLAY`/`WAYLAND_DISPLAY`、Electron 文件是否存在、`webServer.port` 是否已就绪 (时机，`spawn.ts:81-103`)，以及 `connection.authenticatedUrl` 是否存在 (`site-url.ts:22`)。`ensure*Provider` 是否登记取决于注册表里是否已有同 id (先前激活或第三方先到)，与激活顺序有关。文件/显示环境部分是"对固定环境合流"，端口与注册表部分依赖时机。 |
| 3 | C3 | △ | 路由、命令、监听都按名字/句柄撤销，与状态无关。`setCityProvider`、`setDefaultLogger` 是"设为 v"型且没有逆；补逆只能是"恢复旧值"，与状态相关。宜改为按 ctx 持有而非模块级。 |
| 3 | C4 | ✓ | 不 spawn 子 fiber。 |
| 3 | C5 | △ | 启动时若端口已就绪且 Electron 已在，`launchHelper` 同步 `ctx.emit` 并读取收集到的 entries (`site-url.ts:25-27` ✔)；结果只进 Helper 的环境变量，不决定登记内容。 |

**最高层**：宿主 1 (前提是把 5 个软读标为可选依赖；严格按现写法 S1 ✗)；客户端不在模型内 (猴补丁 `commandUi.candidates`)。第 2 层被模块级注册表/回调未登记挡住，第 3 层被 Helper 启动分支依赖环境与时机挡住。
**升级路径**：(1) 宿主 inject 增加可选依赖 `standaloneAi`、`speechToText`、`attachments`、`shutdownApp`、`deepseekAccount` → S1 ✓。(2) `ensure*Provider` 改为 `ctx.effect(() => registerVoiceProvider(...))` 并把注册表挂在每次激活上，`setCityProvider`/`setDefaultLogger` 改为按 ctx 传参；把 `startHelper()` 与端口重试放进一个 `ctx.effect` → R1 ✓，宿主可到 2。(3) 第 3 层需把 Helper 视为 Active 期间对环境的反应而非启动登记，并给 `petApi7340` 的 `register` 自动挂到调用者 fiber；命令改用带前缀的名字。客户端需去掉 `candidates` 猴补丁 (等宿主提供命令面孔入口) 才能进入模型。
**与上一轮审计的差异** (0.4.7 → 0.4.9)：
- 新增越界：0.4.9 在 apply 中加了 `setCityProvider`、4 个内置语音 `ensure*Provider` (模块级注册表、无 disposer、闭包捕获首个 ctx)，R1 退步；新增 `site-url.ts` 在启动路径上同步 `emit` 读收集结果 (C5 △)。
- 未变：宿主 inject 列表、`petApi7340`、5 个软读、Helper 在效应外启动、lifecycle 拆除顺序、Electron 下载不可中止。路由、命令、轮询全部经 `ctx.effect` 登记 (本版核对；与 0.4.7 源码相同)。
- 上一轮未提而本轮发现：客户端猴补丁 `commandUi.candidates` (0.4.7 源码已有，`D:\dsh-plugins\src\dsh-pet\dsh-pet\src\client\command-faces.ts`)；`petApi7340.register` 返回裸 disposer。
