# dsh-windows-mcp 0.2.11

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主 `lib/index.js` 导出 `{ name, apply }` (`:1465` ✔)，无顶层 `inject`；`apply` 里 5 个静态 `ctx.inject` 子 fiber (`tools` ×3、`webServer` ×1，经 `registerDoctor/StateRoute/ToolGate/RevealTool`)。无 provide。另有 `cordis.patch.yml` 在 loader 中插入两行 (`windows-mcp-plugin` 与官方 `@deepseek-ai/dsh-mcp-client` 的 `windows-mcp-bridge`，后者默认 `disabled: true`)。客户端 `lib/client.js`，`inject = ["slots"]` (`:62`)。
- 一句话功能：把官方 MCP 客户端桥接到 Windows-MCP，宿主半边只提供诊断工具 `windows_mcp_doctor`、按需揭示工具 `windows_desktop`、按会话的 Computer Use 开关 (restrict + guard) 和安装/更新/设置路由。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✗ | 宿主未注入的读取：`sessions` (`lib/index.js:322` ✔，0.2.11 新增，用于子代理继承授权)、`tools` 兜底 (`:455` ✔)、`agents` (`:546` ✔)、`connection` (`:1013` ✔)；另读别的 fiber 的 `agent.ctx.get("tools")` (`:515` ✔)。都是有意的可选读取 (缺失时退化为"拒绝")，可改为可选依赖；读 agent 的 tools 不行，见 S3。客户端 `ctx.get("locale")` (`lib/client.js:705`)，有注释说明是可选。 |
| 0 | S2 | ✓ | 无 provide。 |
| 0 | S3 | ✗ | 在每个 agent 的上下文上 `scoped.restrict({ deny })` (`:515-524` ✔)，效应挂在 agent 的 fiber 上，自己用私有 Map `applied` 回收 (`:489-495`)。另有编排成分：安装器在用户操作时改写 profile 的 `cordis.patch.yml` 中 bridge 行 (`lib/dependency.js:658` ✔，下次启动生效)；包自带 patch 插入 loader 行。无 `internal/*`、无猴补丁。 |
| 1 | L1 | ✓ | `apply` (`:1428-1462` ✔) 同步、有界：读设置文件、`which` 扫 PATH、5 次 inject。后台 `updater.check` 是 `void` 的异步任务 (`:1455`)，不阻塞启动。 |
| 1 | L2 | ✓ | 只 inject `tools`/`webServer`，均由宿主提供；无 provide/spawn 环。 |
| 2 | R1 | ✗ | 6 个 `webServer.register` 的返回值被丢弃 (`:1409-1414` ✔)：卸载后路由仍在，重载时因 duplicate 抛错 (dsh `webserver/src/index.ts:445` 仍只返回裸 disposer)，被 catch 成警告，且后续路由不再登记。`tools.register`/`tools.guard`/`ctx.on` 经 Cordis effect 自动收集 ✓。 |
| 2 | R2 | ✗ | 处理器 (`agent/created`、`agent/pre-step`、`tools/change`) 在 agent 上下文上 `restrict`，本插件卸载时没有释放 `applied` 中的句柄 (无 dispose 钩子；只有 `agent/disposed` 时释放，`:566`)。路由处理器启动 `uv tool install` 子进程 (`lib/dependency.js:257`) 与 PowerShell 进程扫描 (`lib/processes.js`)，只受超时/取消路由约束，不挂 fiber。 |
| 2 | R3 | △ | 登记名：工具 `windows_mcp_doctor`、`windows_desktop`，路由 `/dsh-windows-mcp/*`，带前缀，撞名可能性小。但开关逻辑依赖别的插件 (MCP bridge) 登记的 `mcp__windows__*` 工具，并对其做 deny；对同一 agent 的工具视图与其他插件的 restrict 交叠。 |
| 2 | R4 | △ | 持久状态：`$DSH_HOME` 下设置文件 (`lib/settings.js:164-167`)、版本清单 (`lib/installs.js`)、profile patch 层与 `.bak-*` 备份、`~/.windows-mcp`、uv 工具目录。临时资源泄漏：上述路由、restrict 句柄、子进程。模块级状态 `sessionGrants`/`settings`/`updater` (`:102-111`) 跨插件重载存活。未见改 `process.env` 或全局 agent。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | △ | 登记集合与环境无关 (4 个 register 无条件)；`settings` 文件只影响后台更新检查与 gate 的判定，属"对固定环境合流"。 |
| 3 | C3 | △ | 自身 fiber 上的登记 (工具、guard、监听) 按名字，逆与状态无关；但 restrict 的计算依赖当时已登记的工具集合 (`denyFor`，`:459-485`)，且挂在别人 fiber 上，越出本层。 |
| 3 | C4 | ✓ | 未直接 dispose 子 fiber。 |
| 3 | C5 | ✓ | 启动期不 emit、不读分发结果 (`agent/pre-step` waterfall 只在运行期被调用并原样 `next()`)。 |

客户端：只 inject `slots`，所有 `slots.register` 都在 `slots.inject` 回调里返回 (`lib/client.js:1827-1964`)，`setInterval`/事件监听都在 React effect 中返回清理 (`:334-343`、`:741-744`)；`localStorage` 为有意持久。客户端本身可到第 2 层以上。

**最高层**：0 (安全层也只是 △/✗：S1 有 4 处可选读取，S3 有跨 fiber 的 restrict)。照现写法，路由泄漏使第 2 层不成立。
**升级路径**：(1) 把 6 个 `webServer.register` 的 disposer 交给 `scoped.on("dispose", …)` 或 `ctx.effect`，修 R1；(2) 增加本插件 dispose 时释放 `applied` 中全部 restrict 句柄，并把 uv 安装子进程挂到 `ctx.effect`/dispose 上；(3) 把 `sessions`/`agents`/`connection` 声明为可选依赖 (模型扩充后)。完成 (1)(2) 后，除"对他人 fiber 的 restrict"这一交集生命周期效应外，可到第 2 层；若模型补上交集效应原语，可达第 2 层，第 3 层仍受 restrict 依赖当前工具集合限制。
**与上一轮审计的差异** (0.2.8 → 0.2.11)：
- 未修：6 个路由 disposer 仍被丢弃 (原 `:1259-1264` → 现 `:1409-1414`)；agent 上下文上的 `restrict` 仍无卸载回收；uv 子进程仍不挂 fiber。
- 改进：Computer Use 开关不再持久化到 `dsh-windows-mcp.state.json` (0.2.8 启动时读该文件，`package/lib/index.js:81,1281`)，改为内存中按会话的 `sessionGrants`；少了一处启动期读取外部文件决定行为的分支，也少了一个持久文件。
- 新增：未注入读取 `ctx.get("sessions")` (`:322`)；模块级 `sessionGrants` Map (有上限 256) 跨插件重载存活；新增 `lib/processes.js`，安装前在路由处理器中起一个有 5 秒超时的 PowerShell 进程扫描。
- 上一轮的 (a) △ 现在按 S1 记 ✗ (未注入读取从 3 处增到 4 处，再加跨 fiber 读取)。

**复核 (2026-11-24)**：`writeBridgeOverride` (`lib/dependency.js:617-675`) 直接改写 profile 的 `cordis.patch.yml`，即 loader 组合条目所读的补丁文件，返回 `restartRequired`，由下次启动 (或下次 `reconcileProfile`) 执行；算经 loader 的配置编排。它用 `writeFileSync`，绕过了 plugin-manager 的文件锁。
