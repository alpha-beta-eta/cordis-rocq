# dsh-session-superagent 0.10.12

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：**是**。入口 `lib/index.js`，`inject = ['tools','agents','webServer']`（`lib/index.js:59` ✔），`apply` 是同步函数（`lib/index.js:1735` ✔），没有 provide。客户端 `client.js` 返回 `{inject:['slots'], apply}`（`client.js:4527` ✔）。`bin/check.mjs`（`dsh-zhuli`）是自检 CLI，不参与生命周期。
- 一句话功能：盯 GitHub 或 Gitee 仓库，有新 issue 或 PR 时唤醒绑定的会话（`agent.followup`/`steer`）。提供 `watch_*`、`github`、`repo_here` 工具和面板路由 `/session-superagent/*`，也能自更新（`dsh plugin add`）。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 未注入的读取：`ctx.get('goals')`（`index.js:544,2685` ✔）和 `ctx.get('gate')`（`1930` ✔），都是有意的可选依赖（有回退），可以改成可选 inject。`agents` 已经声明。 |
| 0 | S2 | ✓ | 没有 provide。 |
| 0 | S3 | ✗ | **跨重载的 globalThis 状态，并清理别的实例的资源**：`sharedTimers`、`sharedInFlight`、`activeRoutes` 挂在 `globalThis[Symbol.for(...)]` 上（`index.js:233-244` ✔）。新实例启动时会 dispose **旧实例**的全部路由、清掉旧实例的定时器（`1937-1946` ✔），等于对另一个 fiber 的效应动手。路由代号 `globalThis[ROUTE_GEN_KEY]`（`2713-2714` ✔）。自更新会调用 CLI `dsh plugin --profile <p> add dsh-session-superagent@<v>` 改 profile（`update.js:54,297` ✔），这是编排行为，只在面板 POST 时由人触发。 |
| 1 | L1 | ✓ | 启动只遍历状态文件里的 watcher（有限），给每个 watcher 开 `setInterval`，首轮用 `setTimeout` 错开（`1823-1834,2784-2787` ✔），之后的轮询都在 Active 期间。失败有退避（`1810-1815` ✔）。 |
| 1 | L2 | ✓ | 只 inject 宿主服务，没有 provide 也没有 spawn。 |
| 2 | R1 | ✗ | 工具用 `ctx.tools.register`，由服务自动收集（`2789` 等 ✔）。但路由、watcher 定时器和 5 秒扫描的 `setInterval` 都由手写的 `teardown` 收尾，这个 `teardown` 只在 `registerRoutes` 走到尾部时才 `ctx.effect` 登记（`2731-2746` ✔）。如果 `webServer.register` 不存在，提前 return（`1938` ✔），`sweepHandle` 和 watcher 定时器就不会登记。（`setInterval(...).unref?.()` 存进 Map（`1823` ✔）没有问题：Node 的 `unref()` 返回 Timeout 本身。） |
| 2 | R2 | ✗ | 运行期的 `watch_start` 工具和面板路由新开的 watcher 定时器存在**全局** Map 里，不在子 fiber 上。唤醒会把消息写进别的会话的 inbox（`wake`，`962-987` ✔），这是有意的、不可撤销的外部效应。 |
| 2 | R3 | △ | 工具名 `github`、`repo_here` 太通用，可能和其他插件撞名（`3172,3202` ✔）。`watch_*` 和路由前缀 `/session-superagent` 没问题。撞名时它会换一个前缀 `/session-superagent/r<N>` 重放（`2711-2720` ✔），等于把相遇处理写成了启动期的分支。 |
| 2 | R4 | △ | 持久状态：`state.json`（含 `.bak`）、`secrets.json`（权限 0600，Windows 上用 `icacls` 改 ACL，`index.js:435,1023` ✔）、各 watcher 的水位，以及仓库上的 ack 标签和评论（外部系统）。临时资源泄漏：见 R1。进程级改动：只读 `process.env.DSH_SUPERAGENT_*` 开关，`spawn` 子进程时把 `process.env` 原样传下去，没有改它。 |
| 3 | C1 | ✓ | 没有 provide。 |
| 3 | C2 | ✗ | 启动登记取决于全局注册表的状态：如果旧实例的路由还在，就换前缀重放，并改写全局代号（`2711-2720` ✔）。启动哪些 watcher 由 `state.json` 决定（对固定环境合流）。 |
| 3 | C3 | △ | tools 和路由都是按名字登记，逆与状态无关。但 `teardown` 会把 `activeRoutes.length = 0`，清掉全局表（`2733-2735` ✔），这个逆依赖全局状态。 |
| 3 | C4 | ✓ | 没有 spawn，也没有 dispose 任何 fiber。 |
| 3 | C5 | ✓ | 启动期没有读取有序分发的结果。 |

**最高层**：不在模型内，0 层也不满足，但差得不远。唯一的硬伤是用 globalThis 跨实例共享定时器和路由表，并在启动时清理旧实例的资源。
**升级路径**：(1) 删掉 `sharedTimers`、`activeRoutes` 和 `ROUTE_GEN_KEY` 这些 globalThis 结构，改用模块内或闭包内的 Map；每条路由 `ctx.effect(() => webServer.register(...))`，每个 watcher 的定时器用 `ctx.effect` 或在子 fiber 里登记。(2) `goals`、`gate` 改成可选 inject。做完这两步可以到第 1 层，R1 和 R2 也一起解决：每个 watcher 做成一个 `ctx.plugin` 子 fiber，`watch_stop` 时 dispose 它，这对应 `O-React`；如果只是登记 effect 而不是子 fiber，就不用担心 C4。做完后可到第 2 层。再把撞名时换前缀的逻辑去掉（重复路由直接报错），C2 的全局状态依赖就消失了，C3 也变成 ✓，可以到**第 3 层**（watcher 集合按固定的 `state.json` 合流）。自更新只给 UI 发提示即可，不影响分层。
