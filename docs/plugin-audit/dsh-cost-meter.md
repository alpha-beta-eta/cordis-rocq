# dsh-cost-meter 1.9.85

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主入口 `lib/bootstrap.js` (`main`，压缩产物，内嵌 Acorn)，只导出 `apply` 与 `name = "cost-meter"`，**不导出 inject** (`lib/bootstrap.js:41` ✔)；它在模块求值时做全局安装，再 `await import('./index.js')`，`apply` 转调 `index.js` 的 `apply` (`lib/index.js:4077` ✔)。动态子 fiber：`sessionProjections`、`typert`、`web` (`lib/index.js:4264,4274`，`lib/native-search-billing.js:445` ✔)。provide `costMeter` (`lib/index.js:4269` ✔)。另导出 `./typert` RPC 清单。客户端 `lib/client.js` + 16 个按需加载的 `client.*.js` 分块，`inject = ["remote"]`，`apply` 是 async (`lib/client.js` 末尾 `Tr`/`Or` ✔)。
- 一句话功能：在 `llm/stream` 瀑布上全局记账每次模型调用的 usage，维护本地账本、价格目录、汇率、各家 Coding Plan 额度与余额查询，提供 `costMeter` RPC 服务和大量 UI；另外对外部工具 `billion-context` 的子进程做源码改写注入以计量其请求。

## 宿主

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✗ | 顶层 inject 为空，却直接用 `ctx.llm` (`lib/billing-stream.js:4-62`、`lib/index.js:631`) 并有大量未注入读取：`ctx.get('credentials')` (`lib/index.js:945,1070,1103`、`lib/custom-balance.js:72`)、`ctx.get('loader')` (`lib/codex-subscription-compat.js:132` ✔)、`ctx.get('pluginManager'/'sessions'/'tokenMeter'/'sessionProjections')` (`lib/context-costs.js:18,99,114`)、`ctx.get('sessions')` (`lib/session-storage-compat.js:68`)、`ctx.registry` (`lib/native-search-billing.js:435` ✔)、`ctx.fiber.entry` (`lib/index.js:4279` ✔)。`credentials`/`sessions` 可改可选依赖；`loader`/`registry`/`fiber.entry` 是元层读取，改不成依赖。 |
| 0 | S2 | ✓ | 只 provide 字面量 `costMeter`，未见别的插件用此名。 |
| 0 | S3 | ✗ | (1) **进程级猴补丁**：模块求值时替换 `child_process.ChildProcess.prototype.spawn`，给启动 `billion-context` 的 node 子进程加 `--import` 预加载并注入环境变量，再订阅 `undici:request:*` diagnostics_channel 观察进程内全部 HTTP 请求，状态存 `globalThis[Symbol.for('dsh-cost-meter.billion-context.*')]` (`lib/bootstrap.js:41` ✔，源 `lib/billion-context-auto.js:64-144` ✔)。(2) **猴补丁别的插件的服务实例**：把 `web` 服务的 `search`/`fetch` 方法 `Object.defineProperty` 换成包装 (`lib/native-search-billing.js:396-422` ✔)，并把还原 effect 挂在 `webCtx`——其中经 `ctx.registry` 遍历得到的是**别的插件的 provision.ctx** (`lib/native-search-billing.js:435-443` ✔)。(3) `internal/service` 全局元层钩子 (`lib/native-search-billing.js:432` ✔，差异 o)。(4) 读 loader 条目判断别的插件 (`codex-subscription`) 是否激活 (`lib/codex-subscription-compat.js:130-140` ✔)；以别的包名 `dsh-cost-meter-codex-compat` 向 `typert` 注册清单，并查 `registry.local` (`lib/index.js:4285-4292` ✔)。(5) 客户端绕过 `window.__ModuleLoader__` 上别人装的 load 包装 (见客户端)。 |
| 1 | L1 | ✓ | apply 同步部分做账本打开、价格表修补、本地检测，均有界；回填延迟 3 s 用计时器触发 (`lib/index.js:4202-4208` ✔)，汇率/OpenRouter 刷新是 `setInterval` (`lib/index.js:4094,4219`)，billion 每 3 s 轮询 (`lib/billion-context-billing.js:319` ✔)——都是 Active 期的反应，不在启动里循环。 |
| 1 | L2 | ✓ | 无静态 inject，子 fiber 只等宿主服务，provide `costMeter` 不被自己等待，无环。 |
| 2 | R1 | △ | 计时器、账本关闭、价格请求都有 `ctx.effect` 撤销 (`lib/index.js:4096,4098,4129-4136,4218,4221` ✔)；监听器经 `ctx.on` 登记。但 bootstrap 的全局安装发生在 `import` 时而非 apply 内，靠引用计数 + `setTimeout(release,0)` 回收 (`lib/bootstrap.js:41` ✔)，不在 fiber 上。 |
| 2 | R2 | ✗ | `enableBridge()` 在 3 s 轮询和 `plugin-manager/changed` 处理器里按配置**再次** `installBillionAuto()` 打进程级补丁并写 `globalThis` (`lib/billion-context-billing.js:300-318` ✔)，不建子 fiber；`internal/service` 处理器里对新出现的 `web` 实例做猴补丁并把还原挂到该实例的 ctx 上。 |
| 2 | R3 | ✗ | `llm/stream`、`session/event`、`internal/service` 都是 `{ global: true }` 监听 (`lib/index.js:4259`、`lib/billion-context-billing.js:345`、`lib/native-search-billing.js:434` ✔)，观察所有服务作用域；`llm/stream` 包装注释自认依赖"本插件是链尾监听者" (`lib/index.js:4224` ✔)。对 `web` 方法的替换与其他同样包装 `web` 的插件相遇时，还原逻辑只在"当前值仍是自己的包装"时才还原 (`lib/native-search-billing.js:415-419`)，结果依赖顺序。 |
| 2 | R4 | △ | 持久状态 (保证不覆盖)：`$DSH_HOME/storages/cost-meter/ledger.json` 及 journal/归档、`billion-context-bridge.json` (`lib/billion-context-billing.js:310`)；启动期把明文密钥迁入凭据库 (`runSecretMigration`/`migrateCustomBalanceHeaderSecrets`，`lib/index.js:4168,4174`)。进程级全局改动 (不该存在)：`ChildProcess.prototype.spawn`、diagnostics_channel 订阅、`globalThis` 符号键、对 `web` 服务实例的方法替换。临时资源：账本写入 `worker_threads` Worker (`lib/ledger-writer.js:13`，未确认是否随 close 终止)。 |
| 3 | C1 | ✓ | 成功路径上无条件 `ctx.provide('costMeter', …)` (`lib/index.js:4269` ✔)。 |
| 3 | C2 | ✗ | 启动行为取决于：别的插件在 loader 中是否激活 (`codexRuntimeEnabled`，`lib/index.js:4107` ✔)；文件系统里是否装了订阅包 (`detectCodexSubscription`/`detectChatgptSubscription`，`lib/index.js:4106-4111`)；`typert` 注册表里是否已有本包、`ctx.fiber.entry` 是否已挂 (`lib/index.js:4276-4291` ✔)。这些依赖激活顺序，不只是固定环境。 |
| 3 | C3 | ✗ | 对 `web` 方法的替换，其逆"若当前仍是我的包装则恢复原描述符"是状态相关的；`ensureCodexCompatPlan` 等写账本配置 (持久，非服务)。 |
| 3 | C4 | ✓ | 未见直接 dispose 子 fiber。 |
| 3 | C5 | ✓ | 启动期不读分发结果 (顺序依赖只在运行期的 `llm/stream`，见 R3)。 |

## 客户端

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✗ | `inject = ["remote"]`，另未注入 `get("remote.costMeter")`、`get("slots")`、`get("connection")`、`get("locale")`、`get("modelDirectories")` (`lib/client.js`、`lib/client.openrouter.js`、`lib/client.statistics.js` 中多处 ✔)。 |
| 0 | S3 | ✗ | 每个分块开头读取 `window.__ModuleLoader__[Symbol.for("@dsh-plugin/dsh-loader:load-wrap")]`，若当前 `load` 是该包装就改用其 `original` 加载自己 (`lib/client.js:2` ✔，17 个 `client*.js` 均同)——绕过另一插件安装的模块加载器包装，属元层。另有 `window.cmPeakAlertPreview`、`window.__cmPeakAlertLive` 等全局。 |
| 3 | C2 | ✗ | `apply` 是 async，`await remote.$mount(...)` 之后才登记 (`lib/client.js` 末尾 `Tr` ✔)；slot 集合按远端状态快照动态增删 (`ds()` 订阅)，启动结果取决于远端返回时机。 |

**最高层**：不在模型内。决定性证据是 S3：进程级猴补丁 `ChildProcess.prototype.spawn` + 全局 HTTP 观察、对 `web` 服务实例的方法替换且把还原挂在别的插件 ctx 上、`internal/service` 元层钩子、读 loader 条目；客户端还绕过别人的模块加载包装。
**升级路径**：(1) 把 billion-context 计量整体拆出插件 (或作为显式的编排者/宿主扩展)，去掉 `spawn` 补丁与 diagnostics_channel 订阅；(2) `web` 搜索计费改为订阅 `web` 发出的事件而非替换方法，删去 `internal/service` 与 `ctx.registry` 遍历；(3) 去掉 loader 条目探测和 typert 补注册 (交给宿主)；(4) 声明 `llm`、`credentials`、`sessions` 等为 (可选) 依赖。做完 (1)–(3) 才进入第 0 层，(4) 后约可到第 2 层 (`llm/stream` 的链尾顺序依赖需标注)；C2 的文件系统探测若视为固定环境，可望第 3 层。
