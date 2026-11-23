# dsh-agent-compare 3.3.0

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主入口 `lib/host/index.js` (tsc 产物，未打包)；`inject = ['tools', 'agents']` (`lib/host/index.js:35` ✔)；无 provide；`commands`、`webServer`+`connection` 走静态 `ctx.inject` 子 fiber (`:489`、`:853` ✔)。客户端 `lib/client.js` (压缩单行，1000 行)，`inject = ["slots","remote","remote.commands"]`，入口 `function xo` (`lib/client.js:995` ✔)。
- 一句话功能：在主对话里让 2–4 个候选 agent (隔离会话 + git worktree/副本) 并行实现同一需求，跑预览与检查，盲选或公开对比后把改动采用进项目。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 宿主未注入读取约 10 处，均为有意的可选依赖 (代码全用 `?.` 处理缺席)：`subagents`(`lib/host/index.js:352` ✔)、`sandbox`/`commands`/`sessionController`(`:369-371` ✔)、`profileContext`(`:397` ✔)、`workingDirectory`(`:438`，另在 `agent.ctx` 上读)、`llm`(`:673`)、`sessionController`(`:580`、`:666`)；在**别的 agent 的 ctx** 上读 `agentPresets`(`:201` ✔)、`approval`(`:218` ✔)。客户端 `Ve.get("sessions")` 未在 inject 中 (`lib/client.js:994` ✔)。可全部改成可选依赖标注 (差异 m)。 |
| 0 | S2 | ✓ | 无 provide。 |
| 0 | S3 | △ | 无 `internal/*`、无猴补丁。但候选会话的 `setup` 回调在子 agent 的 ctx 上做 `systemPrompt.context(...)`、`presets.composeFrom(childCtx, …)`、`session.append(...)`(`lib/host/index.js:216-228` ✔)：效应挂在由 `agents.create` 建、本插件 `handle.dispose()` 回收(`:277` ✔)的 ctx 上，生命期是"本插件运行 ∩ 该候选会话"。客户端绕过事件 API 直接 `Ve.events.dispatch("emit", ["command/executed", …])` 并手工调用监听器 (`lib/client.js:994` ✔)，等于替宿主伪造一次分发。不是编排者。 |
| 1 | L1 | ✓ | 启动同步部分有界；`apply` 是 async，`await comparer.recover()`(`lib/host/index.js:434` ✔) 只遍历运行记录目录 (`lib/core/orchestrator.js:1591-1630` ✔)，有限。轮询 `settled()`(`lib/host/index.js:175`) 与进度 `setInterval`(`:246`) 都在运行期，`finally` 中清除。 |
| 1 | L2 | ✓ | inject 只有宿主服务，无 provide、无 spawn 插件，无环。 |
| 2 | R1 | ✓ | 两个 `ctx.on` 中间件、两个 `tools.register`、`comparer.dispose` 均包在 `ctx.effect` (`:375`、`:394`、`:433`、`:451`、`:479` ✔)；`commands.register`、`webServer.register` 在子 fiber 的 `effect` 里 (`:491`、`:853` ✔)。`comparer.dispose` 在 `await recover()` 之前登记，recover 抛错时已登记部分可回收。 |
| 2 | R2 | △ | 运行期效应 (候选会话、worktree、预览子进程、安装进程) 由插件私有的 `Comparer` 对象管理：每个 run 有 `AbortController`，卸载时 `dispose()` 统一 abort 并停预览 (`lib/core/orchestrator.js:1674-1700` ✔)。可撤销但不是子 fiber；预览进程在非 Windows 上 `detached: true`(`lib/core/proc.js:119`、`:377`)，靠 dispose 与下次启动的 recover 收尾。候选会话 `handle.dispose()` 在 `finally` 中 (`lib/host/index.js:277` ✔)。 |
| 2 | R3 | △ | 工具名 `agent_compare_start`/`agent_compare_status`、路由前缀 `/agent-compare/api`、slot id `agent-compare*` 带前缀；但命令名 `ab`(`lib/host/index.js:492` ✔) 与 commandview key `ab` 很短，可能撞名。`system-prompt/assemble`、`agent/pre-step` 是带 `next` 的中间件链 (`:375`、`:394`)，与其他插件的相对次序取决于激活顺序。 |
| 2 | R4 | △ | 持久状态 (保证不覆盖)：`~/.dsh/agent-compare` 运行记录与偏好 (`lib/core/run-store.js:12` ✔)、用户仓库下的 owned git worktree (`lib/core/git.js:186`)、示例仓库、采用时写入用户项目的文件。临时资源：预览/安装子进程、warm-deps 目录，登记在 Comparer 内，非 fiber；启动 recover 会删上次残留的 warm 目录 (`orchestrator.js:1593-1597` ✔)。未见改 `process.env` 或其他进程级全局。 |
| 3 | C1 | ✓ | 无 provide (空真)。 |
| 3 | C2 | △ | 登记集合固定，不随探测变化；但 runner 选择看 `agents.create` 是否存在、未注入的 `subagents` 是否存在 (`lib/host/index.js:354-361` ✔)，两者都没有时抛错。启动 `await recover()` 读写文件系统，若 recover 在取得归属后抛错 (`orchestrator.js:1617-1618`)，启动在已登记 ctx.on/effect 之后失败 ("无失败"前提 △)。对固定环境合流。 |
| 3 | C3 | ✓ | 所用的逆都是按名字的登记/监听器注销；recover 改写的是持久记录，不是要撤销的效应。 |
| 3 | C4 | ✓ | 不直接 dispose 启动时的子 fiber。 |
| 3 | C5 | ✓ | 启动期不读分发结果；中间件只在运行期调用 `next`。 |

**最高层**：2 (前提：把 S1 的未注入读取标注为可选依赖，并接受 S3 里"在自建子 agent 的 ctx 上登记"这一交集生命期)。不标注则停在"不在模型内"。
**升级路径**：(1) 未注入的 `ctx.get` 改为 `ctx.inject` 子 fiber 或显式可选依赖 → S1 ✓；(2) 把 `await comparer.recover()` 移到 `ctx.effect` 内后台执行 (或在任何登记之前完成)，消除启动失败与启动期 FS 写 → C2 ✓，可到 3 (R2 仍是 Comparer 统一回收而非子 fiber，第 3 层对它没有额外要求)；(3) 客户端改用宿主提供的命令执行通知而不是 `events.dispatch("emit")`。
