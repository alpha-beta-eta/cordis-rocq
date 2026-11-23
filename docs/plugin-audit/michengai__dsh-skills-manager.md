# @michengai/dsh-skills-manager 1.5.0

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主入口 `lib/index.js` (`main`，经 `cordis.patch.yml` 插入为 loader 条目 `skills-manager`)；宿主 inject = `connection, skills, tools, sessions` (`lib/index.js:42` ✔)；不 provide。客户端 `lib/client.js` (`__ModuleLoader__` 包装)，inject = `slots, locale` (`lib/client.js:88` ✔)，另用 `r.inject(["uiWorkspace"])`、`r.inject(["layout"])` 作为可选依赖子 fiber (`lib/client.js:88,47`)。
- 一句话功能：管理本机各 agent 工具 (DSH/Claude/Codex/Cursor 等) 的 skill 目录：浏览、导入、删除/回收站、从 Git 仓库或在线目录安装；向 `skills` 注册外部 skill provider，注册 `create_skill` 工具和一组 `/api/michengai/dsh-skills-manager/*` 路由。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 未注入的 get：`workspaceRegistry` (`lib/index.js:161` ✔)、`agents` (`:255` ✔)、`agentPresets` (`:213`)、`sandboxPolicy`/`sessionProjections` (`:276,281`，经 `safeGetService`，在宿主 ctx 与 agent ctx 上都试)。都判空降级，有意为之 (缺这些服务时仍能工作)，应改为可选依赖。客户端无未注入 get，只读 `globalThis.__DSH_DIRECTORY_PICKER__` (`lib/client.js:88`)。 |
| 0 | S2 | ✓ | 不 provide。 |
| 0 | S3 | △ | 无 `internal/*`、无猴补丁、不改 loader (patch 只插入自身条目)。但对每个 agent 在**agent 的 ctx** 上 `agentCtx.get("skills").registerProvider(...)`，用私有 Map 在 `agent/disposed` 或本插件卸载时回收 (`lib/index.js:233-269` ✔)——与上一轮 dsh-ops 同类的"两 fiber 交集"效应。运行期还代发 `agent-preset/selected` 事件去触发别的插件的缓存失效 (`lib/index.js:148-155`)。客户端 `MutationObserver` 监视 `document.body` 改设置导航图标 (`lib/client.js:40`，有 disposer)。 |
| 1 | L1 | ✓ | 启动只做同步登记；`agents.list()` 有限遍历 (`lib/index.js:256`)。Git 的 `setInterval` 看门狗与超时只在请求处理里 (`lib/repository-git.js:235,257`)。 |
| 1 | L2 | ✓ | 只 inject 宿主内置服务，无 provide/spawn。 |
| 2 | R1 | ✓ | 启动期登记全部经 `ctx.effect`：`agent-preset/selected` 监听、全局 skill provider、per-agent provider 管理器、`create_skill` 工具、`tools/pre-execute` 钩子、全部路由 (`lib/index.js:327-384,828-850` ✔)。 |
| 2 | R2 | ✗ | 路由处理器里 `spawn("git", ...)` (`lib/repository-git.js:188`) 的子进程、`setInterval`/`setTimeout` 只按超时 (默认 900 s) 或配额回收，不随 fiber 撤销；卸载时进行中的 clone/fetch 继续跑并继续写磁盘。per-agent provider 挂在 agent ctx 上 (见 S3)，手工回收而非子 fiber。 |
| 2 | R3 | △ | 路由带包名前缀 ✓，provider 名 `dsh-skills-manager-external` ✓；工具名 `create_skill` 是通用名，可能与其他插件撞名，`tools/pre-execute` 钩子也只按名字 `create_skill` 匹配 (`lib/index.js:368-370`)。 |
| 2 | R4 | △ | 持久状态 (保证不覆盖)：`$DSH_HOME/skills`、`~/.agents` 及十几个其他工具的 skill 目录 (`lib/core.js:145-548`，按用户操作写入/删除)，管理器状态 `repositories.json`、回收站、日志 (`lib/repositories.js:107,177-186`，`lib/index.js:46-60`)。临时资源泄漏：R2 的 Git 子进程与暂存目录。只读 `process.env.*_HOME`，不写全局。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | △ | 启动时按未注入的 `agents` 是否存在、当时有哪些 agent 决定登记哪些 per-agent provider (`lib/index.js:255-258`)；有 `agent/created` 监听补齐，对"最终 agent 集合"合流，但中间形态依赖时机。其余分支 (`ctx.tools`、`ctx.connection?.fetch`) 都基于已注入服务，恒真。 |
| 3 | C3 | ✓ | 只用按名字/句柄的登记 (provider、tool、监听器、路由)，逆与状态无关。 |
| 3 | C4 | ✓ | 不 spawn 子 fiber。 |
| 3 | C5 | ✓ | 启动期无 emit；`commands/change`、`agent-preset/selected` 只在写操作后发出 (`lib/index.js:138-157`)。 |

**最高层**：1。0、1 层成立 (S1/S3 需标注可选依赖与跨 agent ctx 的 provider)；第 2 层卡在路由处理器启动的 Git 子进程不随卸载回收。
**升级路径**：(1) Git 调用带上本插件 fiber 的 AbortSignal (或在 `ctx.effect` 里维护活动子进程集合，dispose 时 `killProcessTree`)，即可到第 2 层；(2) `agents`/`workspaceRegistry`/`agentPresets` 等改为显式可选依赖，per-agent provider 改为 `ctx.inject(["agents"])` 子 fiber 内登记，并给工具改名 (如 `skills_manager_create_skill`)，C2 消除时机依赖后可到第 3 层 (跨 agent ctx 的登记仍需模型的"交集生命周期"构造)。
