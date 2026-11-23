# dsh-token-diet 0.1.0

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主 `lib/index.js` (`main`)，函数插件 `apply(ctx, config)`，`inject = []` (`lib/index.js:39` ✔)，另有静态子 fiber `ctx.inject(['connection'], …)` (`lib/index.js:157` ✔)；无 provide。客户端 `lib/client.js` (`window.__ModuleLoader__.load`)，`inject = ['slots','locale']` (`lib/client.js:3176` ✔)，package.json 里 `dsh.client.inject` 另声明 `@deepseek-ai/dsh-client-ui-conversation`。
- 一句话功能：汇总所有会话/子智能体的 token 用量与成本 (价格取 models.dev，汇率在线取)，按会话树设预算，在 `agent/pre-step` 上拦截超预算的模型请求并挂起等待用户决定。

## 宿主

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 4 个未注入读取，都是有意的"软依赖"：`ctx.get('sessionPersistence')`、`ctx.get('agents')` (`lib/index.js:107-108` ✔，在 apply 时读一次并存进 index)；`ctx.get('connection')`/`ctx.connection` (`lib/host/rpc.js:290,296` ✔)；`ctx.get('webServer')`/`ctx[name]` (`lib/host/rpc.js:319,394` ✔)。均 try/catch 容忍缺失，可改成可选依赖 (静态 `ctx.inject([...])` 子 fiber)。 |
| 0 | S2 | ✓ | 无 provide。 |
| 0 | S3 | ✓ | 未见 `internal/*`、猴补丁、改 loader。`ctx.inject(['connection'])` 子 fiber 回调里调用的 `install()` 用的是**外层** ctx (`lib/index.js:150-160` ✔)，即子 fiber 的登记由外层 effect 持有——仍在本插件内部，不算挂到别人 ctx 上，但见 R2。 |
| 1 | L1 | ✓ | apply 同步部分只构造对象并登记监听器。初始化放在 `ctx.effect` 里 fire-and-forget (`lib/index.js:116-126` ✔)；`scan` 分批 + `setImmediate` 让步；`resolveRoot` 的 `for(;;)` 有 visited 集合，有界 (`lib/host/index-store.js:654` ✔)。 |
| 1 | L2 | ✓ | 顶层 inject 为空，子 fiber 只等 `connection`，无 provide，无环。 |
| 2 | R1 | ✓ | 监听器 (`session/event`、`session/created`、`agent/pre-step`) 都包在 `ctx.effect(() => ctx.on(...))` 中 (`lib/index.js:172-218` ✔)；RPC 通道/路由的 disposer 由 `ctx.effect` 收集 (`lib/index.js:162-168` ✔)。`installRpc` 失败时返回空 disposer，无半途残留。 |
| 2 | R2 | △ | (1) `connection` 子 fiber 的回调不返回 disposer：connection 离开时子 fiber 撤销，但 `disposeChannel` 仍指向已失效的 connection 句柄，也不会回退到 webServer 路由 (`lib/index.js:157-161` ✔)。(2) 服务 effect 的 disposer 只置 `disposed` 标志，已启动的 `index.scan`、价格/汇率 fetch 不取消 (`lib/index.js:116-126` ✔)。(3) `index` 的 `liveSaveTimer` (`lib/host/index-store.js:553` ✔，已 `unref`) 与 `budgets.waitForDecision` 的挂起计时器 (`lib/host/budget.js:448`) 在 dispose 时不清理，最长 5 分钟后仍写缓存/结算。 |
| 2 | R3 | △ | 登记名都带插件前缀：RPC 通道与 webServer prefix 路由 `/token-diet` (`lib/host/rpc.js:33` ✔)。但 `agent/pre-step` 是带 `next` 的中间件式分发：超预算时返回 `{kind:'reject'}` 而不调 `next()` (`lib/index.js:203-216` ✔)，会截断排在它后面的监听器，且挂起最长 `budgetHoldMs`(默认 300 s)——与其他 pre-step 插件的相遇依赖监听器顺序。 |
| 2 | R4 | △ | 持久状态 (保证不覆盖)：`$DSH_HOME/token-diet/{index.v1.json,prices.v1.json,rate.v1.json}` 及预算文件 (`lib/host/index-store.js:90`、`pricing.js:178`、`rates.js:74`、`budget.js:186` ✔)；网络 `https://models.dev/api.json` 与汇率源。临时资源泄漏：见 R2 的计时器与未取消的扫描。无进程级全局改动 (`process.env.DSH_HOME` 只读，`lib/index.js:53`)。 |
| 3 | C1 | ✓ | 无 provide (空真)。 |
| 3 | C2 | ✗ | 启动登记什么取决于 apply 时未注入服务是否已在：`connection` 在就登记 connection RPC，否则登记 webServer 路由 (`lib/host/rpc.js:256-272` ✔)；`sessionPersistence` 在 apply 时缺席则 index 永远不扫描 (`lib/host/index-store.js:212`)。这是对激活顺序的依赖，不是对固定环境的依赖。 |
| 3 | C3 | ✓ | 所用服务操作是按名字登记的监听器/路由/RPC handler，逆与状态无关。预算/缓存文件写入属 R4 持久状态，不走服务。 |
| 3 | C4 | ✓ | 不直接 dispose 子 fiber。 |
| 3 | C5 | ✓ | 启动期不读取分发结果。 |

## 客户端

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 渲染期 `ctx.get('connection')` 未注入 (`lib/client.js:124` ✔)，有意为之的可选依赖。 |
| 0/2 | S3/R1/R3 | ✓ | `locale.register`、样式表都在 `ctx.effect` 中 (`lib/client.js:3103-3112` ✔)；5 个 `slots.inject/register`，id 均带 `token-diet` 前缀 (`lib/client.js:3115-3170` ✔)；`setInterval` 都在 React effect 内并清理。`TD.ctx = ctx` 存进模块对象 (`lib/client.js:3098` ✔)，只供本模块使用。 |
| 3 | C2 | ✓ | 启动登记固定，不依赖探测。 |

**最高层**：2 (△ 视为加标注/小重构后可达)。宿主第 3 层卡在 C2：传输方式和是否扫描历史取决于 `connection`/`sessionPersistence` 是否先于本插件激活。客户端单独看可到 3。
**升级路径**：(1) 把 `sessionPersistence`/`agents`/`connection`/`webServer` 改为可选依赖，index 构造放进 `ctx.inject(['sessionPersistence'])` 子 fiber，RPC 分别在 `ctx.inject(['connection'])`、`ctx.inject(['webServer'])` 子 fiber 内用子 ctx 登记并返回 disposer (S1、C2、R2(1) 一并解决)；(2) 服务 effect 的 disposer 里清 `liveSaveTimer`、settle 全部挂起的预算等待、中止扫描 (R2)。做完 (1) 即可到第 3 层 (R3 的 pre-step 顺序依赖仍需作为约定标注)。
