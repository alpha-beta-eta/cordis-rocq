# dsh-remote 1.3.1

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：**是**。入口 `lib/boot.js` 在模块顶层 `await importWithSelfHeal(import('./main.js'))`（`lib/boot.js:5` ✔），主体在 `lib/main.js`。`inject = ['tools','systemPrompt']`（`lib/main.js:155` ✔），`apply` 是 async（`lib/main.js:482` ✔）。provide `dshRemote`（`lib/main.js:4657` ✔）。客户端 `lib/client.js`，`inject = ['slots','locale']`（`lib/client.js:7444` ✔）。
- 一句话功能：SSH 远程工作区。管理多台机器、本地镜像同步、`rw_*` 系列远程工具、终端、端口转发、Web 面板路由，另有自更新和自修复。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✗ | 未注入的 `ctx.get`：`agents`（`main.js:3367` ✔）、`commands`（`3494` ✔）、`logger`（`573` ✔ 等）、`jobs`（`1187` ✔）、`llm`（`1409`）、`sessions`（`1662`）、`sandboxPolicy`（`1957` ✔）、`directoryPicker`（`3678`）、`workspaceRegistry`（`3726`）、`connection`（`http-transport.js:170` ✔），以及直接读属性 `ctx.loader`（`4560,4617` ✔）。注释表明都是有意的可选依赖，可以改成可选 inject。TUI 层用 `ctx.get(name,false)` 做软探测（`tui/index.js:34` ✔）。客户端读了未注入的 `ctx.get('betterSidebar')`（`client.js:4771,6246`）。 |
| 0 | S2 | ✗ | 键名是字面量，但 **`dshRemote` 与 ds-harness-remote 0.6.7 冲突**（对方在 `dist/index.js:113013` ✔）。两边都把 provide 包在 try/catch 里吞掉错误，谁拿到这个键取决于激活顺序。 |
| 0 | S3 | ✗ | **编排者行为**：`reloadSelf` 找到自己的 loader 条目，清模块缓存，`entry.fiber.dispose()`，改写 `entry.options.disabled`，再 `tree.commit` 或 `tree.write`，最后 `entry.init()`（`update.js:642-682` ✔）。它由自更新的 `scheduleSelfReload(ctx.loader)` 触发（`main.js:4617` ✔）。**`internal/service` 钩子**：`tui/index.js:99` ✔（差异 o）。**在别人的 ctx 上产生效应**：对每个 agent 执行 `agent.ctx.get('tools').restrict({deny})`，再用私有 Map 手工回收（`main.js:3337-3375` ✔），与上一轮 dsh-windows-mcp 是同一种模式。模块加载期的自修复可能**下载 npm tarball 并重写本包文件**（`boot.js:5`、`self-heal.js:58,174` ✔）。客户端猴补丁 `sidebarRight.openTab`/`openTabIn`（`client.js:6543-6575` ✔，有 effect 还原）。 |
| 1 | L1 | ✓ | apply 体内没有顶层 await，没有循环（只遍历静态 `tools` 数组）。周期任务（心跳、自更新检查、auto-push 的 watcher）都放在 effect 里。模块加载期的 self-heal 需要网络，但它属于 loader 阶段，不在 apply 内。 |
| 1 | L2 | ✓ | inject 的 `tools`、`systemPrompt` 是外部服务，provide 的 `dshRemote` 本插件不依赖。没有成环。 |
| 2 | R1 | △ | 大部分都登记了：`ctx.tools.register`（`main.js:3257` ✔，由服务自动收集），`commands.register`（自动收集，宿主 `interaction/commands/src/index.ts:285` ✔），路由在 `inner.effect` 里统一回收（`http-transport.js:171-194` ✔），连接池、web-attach、auto-push、终端都放在 `ctx.effect` 的 Map 里统一清理（`main.js:924,1299,1367,1391` ✔）。没登记的有两处：`setTimeout(publish,2000)`（`main.js:4585` ✔），以及 `import('./tui/index.js').then(installTui(ctx…))` 在 apply 返回**之后**才往主 ctx 上登记效应（`main.js:4679-4685` ✔）。 |
| 2 | R2 | △ | 运行期效应（新机器的连接池、web-attach、auto-push watcher、各个 agent 上的 restrict）放在长寿 ctx 的私有 Map 里，靠一个总的 effect 统一回收，不是子 fiber，没法单独撤销。agent 销毁时靠 `agent/disposed` 事件手工撤销 restrict。 |
| 2 | R3 | △ | 命令名 `remote` 比较通用（`main.js:3497`）。`dshRemote` 撞名（见 S2）。工具名用 `rw_*` 前缀，路由用 `/dsh-remote/*` 前缀，这两项没问题。 |
| 2 | R4 | △ | 持久状态：机器注册表、凭据（钥匙串或文件）、审计日志、本地镜像目录、`update-mode` 文件、更新标记、自更新后的包文件，以及启动时 `migrateLegacyData()` 的迁移（`main.js:490` ✔）。临时资源泄漏：终端 askpass 用的 bearer token 文件 `term-secret.json`，只在下次启动时删除，dispose 时不删（`main.js:514-520` ✔）；上面提到的 `setTimeout`。进程级改动：未发现写 `process.env` 或 globalThis。 |
| 3 | C1 | △ | `dshRemote` 在 `createHostApi` 成功、并且 `ctx.provide` 存在时才 provide，失败只打警告（`main.js:4628-4667` ✔）。实际上几乎总会提供，但写法是条件 provide。 |
| 3 | C2 | ✗ | 启动登记取决于未注入服务是否存在：有 `commands` 才注册 `/remote` 命令，有 `agents` 才给当前已有的 agent 装 restrict（`main.js:3367-3370,3494` ✔）。机器注册表和 `~/.ssh/config` 来自文件，这部分算对固定环境合流。 |
| 3 | C3 | ✓ | 用到的服务操作都是按名字登记或注册监听器（tools、commands、路由、`ctx.on`），逆与状态无关。restrict 的逆也是按句柄撤销。 |
| 3 | C4 | ✗ | `reloadSelf` 直接 dispose 自己 loader 条目的 fiber（`update.js:669` ✔）。它不是子 fiber，但这一步越过了编排边界，已在 S3 记过。 |
| 3 | C5 | ✓ | 启动期没有读取有序分发的结果。`system-prompt/assemble` 和 `tools/pre-execute` 都是运行期的 waterfall 处理器。 |

**最高层**：不在模型内，0 层也不满足。它对自己的 loader 条目做热重载编排，用了 `internal/service`，在 agent 的 ctx 上 restrict，并和 ds-harness-remote 抢 `dshRemote`。
**升级路径**：(1) 自更新只落盘并提示重启，删掉 `reloadSelf`，或交给编排者去做。(2) TUI 层改用 `ctx.inject([...])` 等服务，代替 `internal/service`。(3) agent 级的 restrict 改用宿主提供的「本插件、本 agent 交集」API；如果宿主没有，就标成模型外的已知例外。(4) `dshRemote` 改名或协调所有权。(5) 未注入的 `ctx.get` 都改成可选 inject。做完 (1)、(2)、(4)、(5) 可以到第 1 层；再把 `setTimeout` 和异步的 TUI 安装登记到 fiber 上，term-secret 文件在 dispose 时删除，就能到第 2 层。C2 依赖 `commands`/`agents` 是否存在，改成 `ctx.inject(['commands'],…)` 的子 fiber 后可以消除，C1 改成无条件 provide 也容易。之后 C3、C4、C5 都满足，第 3 层可期。
