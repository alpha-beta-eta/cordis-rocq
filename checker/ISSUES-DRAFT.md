# 待提的上游 issue (草稿，未提交)

来源：[FINDINGS.md](FINDINGS.md)、[REPORT.md](REPORT.md)。只收问题极其明确、改法机械的几条，共 8 个，按优先级排列。核对源码仓库后，dsh-qqbot 那条已在源码里修掉，实际要提的是 7 个。

共同的复现环境 (写进每个 issue 的"环境"一段)：

- dsh 发布版 0.2.2-rc.5，Node 24，web 宿主，全新 profile；
- 插件版本见各条，均为 2026-11-23 npm 上的版本；
- "停用 / 启用"指通过 loader 停用、启用插件条目 (与设置页里的开关、热重载走同一条路径)。

语言：作者的源码注释多为中文，下面用中文写。dsh-windows-mcp、dshmarket、dsh-remote 的注释是英文，必要时改写成英文。

## 源码仓库核对 (2026-11-26)

8 个插件都有公开的 GitHub 仓库，都没有归档，都开着 issue。按默认分支 (main) 的 HEAD 逐个核对了问题代码是否还在，也按关键词搜过已有 issue，没有找到重复的。

| # | 插件 | 仓库 | 审计版本 → HEAD 版本 | HEAD 上的位置 | 问题还在吗 |
|---|---|---|---|---|---|
| 1 | dsh-windows-mcp | [helloHub1212/dsh-windows-mcp](https://github.com/helloHub1212/dsh-windows-mcp) | 0.2.11 → 0.2.12 | `lib/index.js:1691-1696` | 在 |
| 2 | dsh-prime-memory | [drscrewdriver/dsh-prime-memory](https://github.com/drscrewdriver/dsh-prime-memory) | 0.26.72 → 0.29.0 | `src/util/filelog.ts:74`、`:76`；调用处 `src/index.ts:119` | 在 (没有 `close`，没有 `clearInterval`) |
| 3 | dshmarket | [dsh-market/dsh-market](https://github.com/dsh-market/dsh-market) | 1.80.0 → 1.82.0 | `src/routes.ts:3485` (`registerRoute`)、`:3519` (数组)、`:9975` (撤销) | 在 |
| 4 | dsh-remote | [flymysql/dsh-remote](https://github.com/flymysql/dsh-remote) | 1.3.1 → 1.5.0 | `lib/http-transport.js:171` | 在，一字未改 |
| 5 | dsh-whale-widget | [MeteorNOX/DeepSeek-Balance-Whale-Widget](https://github.com/MeteorNOX/DeepSeek-Balance-Whale-Widget) | 0.4.2 → 0.4.2 | `lib/index.js:884` (`registerRoute`)、`:4903` (`tapIndex`)、`:4920` (撤销) | 在 (仓库自 2026-10-11 未更新) |
| 6 | @tencent-connect/dsh-qqbot | [tencent-connect/dsh-qqbot](https://github.com/tencent-connect/dsh-qqbot) | 0.5.5 → 0.5.5 | — | **源码里已修掉，不提** |
| 7 | dsh-connect-workbuddy | [dingminhua/dsh-connect-workbuddy](https://github.com/dingminhua/dsh-connect-workbuddy) | 5.31.0 → 5.31.8 | 移到了 `src/web-status.ts:1882-1891`、`:2796` | 在 |
| 8 | dsh-image-gen | [shanliuling/dsh-image-gen](https://github.com/shanliuling/dsh-image-gen) | 0.11.4 → 0.12.3 | `src/index.ts:457-459` | 在 |

几处说明：

- **dsh-qqbot**：2026-11-22 的提交 `feat(settings): split config RPC endpoint…` 把绑定页从 `webServer.register` 的 5 条路由改成了经 `connection.fetch.register` 的 RPC (`src/rpc-carrier.ts`)。后者是 owned 登记，宿主按 fiber 记账、卸载时自动撤销。HEAD 的 `src/` 里已经没有任何 `webServer.register`。但这次改动在 0.5.5 的 tag (2026-10-30) 之后，`package.json` 仍是 0.5.5，npm 上的 0.5.5 仍带着问题，只是等下一次发布。下面第 6 节保留备查，不提。
- **dsh-connect-workbuddy**：#86 已关闭，标题是"批量操作报「HTTP 405」…真实原因是宿主进程在跑旧代码"。所以应新开一个 issue 引用 #86，不在 #86 下回复。
- **dshmarket**：`registerRoute` 用的 `host` 类型是 `MarketHost` (`src/routes.ts:185`)，只有 `webServer`、`loader`、`plugin`、`on`、`get`、`logger`，没有 `effect`。所以只能用 `try/catch` 那种最小修法，第 3 节已改。
- **dsh-windows-mcp**、**dsh-remote**、**dsh-whale-widget** 的仓库里直接提交的就是 `lib/*.js`，没有另外的 TS 源码，行号以 HEAD 为准。

---

## 1. dsh-windows-mcp：停用插件后 6 条路由仍然挂着，再启用时全部撞名

**仓库**：https://github.com/helloHub1212/dsh-windows-mcp/issues

**已提交** (2026-11-26)：https://github.com/helloHub1212/dsh-windows-mcp/issues/19

**标题**：停用插件后 webServer 路由不撤销，旧实例继续应答；再启用时新路由全部注册失败

### 现象

停用 dsh-windows-mcp 后，插件的 fiber 已经是 DISPOSED，但 `/dsh-windows-mcp/state` 等 6 条路由仍然登记在宿主上，并由已经卸载的旧实例应答 (HTTP 200，返回状态 JSON)；不存在的路由返回 404 作对照。再启用后，路由上挂的仍是停用前的那个处理器函数：新实例的 6 次 `register` 全部因重复路径抛错，被插件的 `catch` 吞成一条 `could not register the Computer Use state route` 警告。这种状态一直持续到宿主重启。

### 复现

1. 装上 dsh-windows-mcp，确认 `GET /dsh-windows-mcp/state` 返回 200；
2. 停用插件；
3. 再请求 `/dsh-windows-mcp/state`：仍返回 200 (预期 404)；
4. 启用插件，宿主日志里出现 `could not register the Computer Use state route: … duplicate …`，请求仍由旧处理器应答。

### 原因

`lib/index.js:1691-1696` (HEAD；0.2.11 的发布产物里是 `:1409-1414`)：

```js
scoped.webServer.register({ kind: "exact", path: STATE_ROUTE, handler: guarded(handler) });
scoped.webServer.register({ kind: "exact", path: PREPARE_ROUTE, handler: guarded(prepareHandler) });
// … 共 6 条
```

dsh 的 `webServer.register` 返回一个裸 disposer，不归调用者的 fiber 管 (`packages/host/webserver/src/index.ts`)。这里把返回值丢掉了，卸载时没有任何东西撤销这些路由。

### 建议修法

每条都经 `scoped.effect` 登记，让 Cordis 在卸载时撤销：

```js
scoped.effect(() => scoped.webServer.register({ kind: "exact", path: STATE_ROUTE, handler: guarded(handler) }));
scoped.effect(() => scoped.webServer.register({ kind: "exact", path: PREPARE_ROUTE, handler: guarded(prepareHandler) }));
// … 其余 4 条同样
```

这样即使第 k 条抛错，前 k−1 条也已经登记了撤销，外面的 `try/catch` 可以保持不变。

---

## 2. dsh-prime-memory：每次 apply 都多加一个 `beforeExit` 监听器和一个 500ms 计时器，从不移除

**仓库**：https://github.com/drscrewdriver/dsh-prime-memory/issues

**已提交** (2026-11-26)：https://github.com/drscrewdriver/dsh-prime-memory/issues/51

**位置** (HEAD 0.29.0)：`src/util/filelog.ts:74` 的 `setInterval`、`:76` 的 `process.once('beforeExit')`；调用处 `src/index.ts:119`。下文的实测用的是 0.26.72 的发布产物 (`dist/util/filelog.js:71`、`dist/index.js:127`)。

**标题**：`withFileLog` 的 `process.once('beforeExit')` 与 `setInterval` 在插件卸载/重跑时不清理，随重启累积

### 现象

插件每次 apply 都调用一次 `withFileLog` (`dist/index.js:127`)，后者：

- `setInterval(flushNow, 500)` (`dist/util/filelog.js` 第 69 行附近，`unref` 了但从不 `clearInterval`)；
- `process.once('beforeExit', …)` (`dist/util/filelog.js:71`，从不移除)。

插件停用后两者都留着；插件重新 apply 时再加一份。插件 inject 了 `webServer`、`tools` 等服务，这些服务任何一个重启都会让 apply 重跑，所以累积的不只是手动重装。

真实宿主上的计数 (`process.listenerCount('beforeExit')`)：

| 时刻 | 监听器数 |
|---|---|
| 空宿主 | 0 |
| 装上后 | 1 |
| 停用后 | 1 |
| 再启用后 | 2 |
| 从装上开始，webServer 重启 1、2、3 次 | 2、3、4 |
| 接着 tools 重启 1、2、3 次 | 5、6、7 |

每份残留都持有一份旧的 `buffer` 和 `logPath` 闭包，旧计时器也继续每 500ms 跑一次 `flushNow`。

### 复现

1. 空宿主上读 `process.listenerCount('beforeExit')`；
2. 装上 dsh-prime-memory，停用，再启用；
3. 或者：保持插件启用，在设置里停用再启用 webServer 条目若干次；
4. 每次之后读监听器数，单调增加。

### 原因

`withFileLog` 没有提供关闭的手段，`apply` 也没有在 fiber 上登记它的逆。

### 建议修法

让 `withFileLog` 返回一个 `close`，在 apply 里登记：

```ts
// util/filelog.ts
const timer = setInterval(flushNow, FLUSH_INTERVAL_MS)
timer.unref?.()
const onBeforeExit = () => { /* 原来的同步刷盘 */ }
process.once('beforeExit', onBeforeExit)
return {
  // … debug/info/warn/error 不变
  close: () => {
    clearInterval(timer)
    process.off('beforeExit', onBeforeExit)
    flushNow()
  },
}

// index.ts，apply 里
const fileLogger = withFileLog(dataDir, logger)
ctx.effect(() => () => fileLogger.close(), 'prime-memory: file log')
```

---

## 3–7. 路由批量登记：中途一条失败，前面的路由就泄漏，插件从此装不回去

五个插件是同一个写法，各提一个 issue。下面先写通用的正文，再分别列出每个插件的位置、实测和改法。

### 通用正文 (每个 issue 都放)

dsh 的 `webServer.register` 返回一个裸 disposer，不归任何 fiber 管，撞名时抛错。插件先把一批 `register` 的返回值收进数组，最后才统一撤销。第 k 条一旦抛错 (最常见的是路径已被占用，例如另一个插件、同一插件的旧实例，或热重载期间)，apply 就在这里中断：数组还没交给撤销逻辑，前 k−1 条路由没有任何人负责撤销。后果：

1. 插件停用后，这 k−1 条路由仍登记在宿主上，由已卸载的旧实例应答 (不是 404)；
2. 再启用时，第一条路由就撞在自己留下的那条上，插件再次失败；
3. 即使最初占用路径的一方已经离开，插件也装不回去，直到宿主重启。

我们用一个生命周期检查工具枚举了"第 k 次 `register` 抛错 → 装上 → 卸载 → 再装"，几乎每个 k 都有残留；然后在真实宿主上用真实的撞名复现：先由另一个插件占住本插件的第 2 条路由，再启用本插件，然后停用、撤掉占位、再启用。

**通用修法**：每登记一条，立即把它的撤销登记到 fiber 上。最省事的是改登记的辅助函数：

```js
const registerRoute = (route) => ctx.effect(() => ctx.webServer.register(route))
```

`ctx.effect` 返回的 disposer 可以重复调用 (Cordis 内部有 `disposing` 保护)，所以原来"收进数组、最后统一调用"的代码可以原样保留，不会重复撤销。

如果不想动登记方式，最小修法是在批量登记外面包一层：

```js
const disposers = []
try {
  // … 原来的逐条 disposers.push(register(...))
} catch (error) {
  for (const dispose of disposers.splice(0)) dispose()
  throw error
}
```

### 3. dshmarket 1.80.0

**仓库**：https://github.com/dsh-market/dsh-market/issues

**已提交** (2026-11-26)：https://github.com/dsh-market/dsh-market/issues/1309 (按仓库的 bug_report 模板分节，标签 bug)

- **位置** (HEAD 1.82.0)：`src/routes.ts:3519`，`const disposers = [registerRoute(…), …]`，所有路由写在一个数组字面量里 (1.80.0 时是 63 条)；撤销在 `:9975` 的清理函数里。登记辅助函数在 `:3485`，调用 `host.webServer.register`。
- **实测** (真实宿主，占住 `/dsh-market/telemetry`)：
  - 撞名后启用，内层 fiber FAILED；
  - 停用后第 1 条路由仍登记，旧处理器应答 HTTP 401；
  - 撤掉占位再启用，FAILED，撞在自己留下的 `/dsh-market/telemetry/opened` 上。
- **改法**：`mountMarketRoutes` 收到的 `host` 是 `MarketHost` (`src/routes.ts:185`)，没有 `effect`，所以用最小修法：把 `const disposers = [ … ]` 改成先建空数组、逐条 `disposers.push(registerRoute(…))`，外面包 `try/catch`，失败时撤销已登记的再抛出。另一种做法是给 `MarketHost` 加上 `effect`，由调用方传入 ctx，改动更大，留给作者选。

### 4. dsh-remote 1.3.1

**仓库**：https://github.com/flymysql/dsh-remote/issues

**已提交** (2026-11-26)：https://github.com/flymysql/dsh-remote/issues/227 (按仓库的 bug 模板分节，标签 bug)

- **位置**：`lib/http-transport.js:171-172` (1.3.1 与 HEAD 1.5.0 相同)：

  ```js
  const disposers = guarded.map((route) => inner.get('webServer').register(route))
  inner.effect(() => () => disposers.forEach((dispose) => dispose()), 'dsh-remote.web-routes')
  ```

- **实测** (真实宿主，占住 `/dsh-remote/status`)：
  - 撞名后启用，内层 fiber FAILED；
  - 停用后第 1 条路由仍登记，旧处理器应答 HTTP 401；
  - 撤掉占位再启用，FAILED，撞在 `/dsh-remote/workspace-context` 上。
- **改法**：

  ```js
  for (const route of guarded) {
    inner.effect(() => inner.get('webServer').register(route), 'dsh-remote.web-route')
  }
  ```

- **补充**：同一文件紧接着的 `connection.fetch` 分支 (`:174` 起) 已经按"逐条登记、单条失败不中断也不泄漏"的写法处理，注释也讲了原因。`webServer` 分支照着改即可。

### 5. dsh-whale-widget 0.4.2

**仓库**：https://github.com/MeteorNOX/DeepSeek-Balance-Whale-Widget/issues

**已提交** (2026-11-26)：https://github.com/MeteorNOX/DeepSeek-Balance-Whale-Widget/issues/358

- **位置** (HEAD，版本仍是 0.4.2)：`lib/index.js:884` 的 `registerRoute` 直接 `return ctx.webServer.register(wrapped)`；26 处 `disposers.push(registerRoute(…))`；`:4920` 附近的 `ctx.effect` 才统一撤销。`:4903` 的 `ctx.webServer.tapIndex` 返回值同样经这个数组撤销。
- **实测** (真实宿主，占住 `/dsh-whale/rua.gif`)：
  - 撞名后启用，内层 FAILED：`duplicate exact route "/dsh-whale/rua.gif"`；
  - 停用后 `/dsh-whale/image.png` 仍登记，旧处理器应答 HTTP 401；
  - 撤掉占位再启用，FAILED：`duplicate exact route "/dsh-whale/image.png"`，撞在自己留下的路由上。
- **改法**：`registerRoute` 最后一行改成 `return ctx.effect(() => ctx.webServer.register(wrapped))`；`tapIndex` 同样包一层 `ctx.effect`。`disposers.push(...)` 可以不动。

### 6. @tencent-connect/dsh-qqbot 0.5.5 (不提：源码已修)

**仓库**：https://github.com/tencent-connect/dsh-qqbot/issues

> HEAD 已改为经 `connection.fetch.register` 的 RPC，`src/` 里不再有 `webServer.register`，问题随之消失，只是还没发布新版本。下面是对 npm 上 0.5.5 的记录，保留备查。

- **位置**：`lib/setup/bind-routes.js:65` 起，`registerBindRoutes` 里 `const disposers = [webServer.register(…), …]`，5 条写在数组字面量里，返回一个统一撤销的函数；调用方在 `lib/setup/index.js:55`、`:81`。
- **实测** (真实宿主，占住 `/qqbot/im-qqbot/bind/refresh`)：
  - 撞名后启用，内层 fiber FAILED；
  - 停用后第 1 条路由仍登记，旧处理器应答 HTTP 200 (`{"phase":"failed",…}`)；
  - 撤掉占位再启用，FAILED，撞在 `/qqbot/im-qqbot/bind` 上。
- **改法**：`registerBindRoutes` 只拿到 `webServer`，没有 ctx，用上面的最小修法最直接：

  ```js
  const disposers = []
  try {
    disposers.push(webServer.register({ … BIND_STATE_PATH … }))
    disposers.push(webServer.register({ … BIND_REFRESH_PATH … }))
    // … 其余 3 条
  } catch (error) {
    for (const dispose of disposers) dispose()
    throw error
  }
  ```

### 7. dsh-connect-workbuddy 5.31.0

**仓库**：https://github.com/dingminhua/dsh-connect-workbuddy/issues (新开一个，引用已关闭的 #86)

**已提交** (2026-11-26)：https://github.com/dingminhua/dsh-connect-workbuddy/issues/323 (修法改成只动 `route` 一行：`disposers.push(ctx.effect(() => ctx.webServer.register(entry)))`；原写"外层效应体抛错时 Cordis 会撤销已收集的内层 effect"，机制说错了，见下面的回访)

- **位置** (HEAD 5.31.8)：`src/web-status.ts:1882` 起，`registerWorkBuddyStatusRoute` 在一个 `ctx.effect` 的效应体内用 `route(entry)` 逐条 `disposers.push(ctx.webServer.register(entry))` (`:1889-1891`)，到 `:2796` 才 `return () => { for (const dispose of disposers) dispose() }`。5.31.0 的发布产物里对应 `lib/index.js:13226`、`:13886`。
- **实测** (真实宿主，占住 `…/account-credits`)：
  - 撞名后启用，内层 fiber FAILED；
  - 停用后第 1 条路由仍登记，旧处理器应答 HTTP 200 (`{"status":"signed-out",…}`)；
  - 撤掉占位再启用，FAILED，撞在 `…/usage` 上。
- **与 #86 的关系**：源码注释说，#86 是热重载时因重复注册同一路径而抛错，后面的路由全部注册不上；修法是把 disposer 收进数组。这防住了"新加路由忘了加卸载"，但没防住"中途抛错"：效应体在第 k 条抛错时还没执行到最后的 `return`，Cordis 拿不到清理函数，前 k−1 条照样泄漏。
- **改法**：`route` 改成 `const route = (entry) => { ctx.effect(() => ctx.webServer.register(entry)) }`，外层 `ctx.effect` 返回的清理函数里去掉对 `disposers` 的循环 (其余清理保留)。或者用最小修法，在效应体里包 `try/catch`。

---

## 8. dsh-image-gen：`systemPrompt` 的 inject 回调里用了外层 `ctx`

**仓库**：https://github.com/shanliuling/dsh-image-gen/issues

**已提交** (2026-11-26)：https://github.com/shanliuling/dsh-image-gen/issues/169

**标题**：`ctx.inject(["systemPrompt"], (promptCtx) => { ctx.inject(["credentials"], …) })` 应该用 `promptCtx`

**优先级低**：在当前的 dsh 宿主上不触发，属于潜在问题。

### 问题

`src/index.ts:457-459` (HEAD 0.12.3；0.11.4 的发布产物里是 `lib/index.js:32603-32605`)：

```ts
ctx.inject(['systemPrompt'], (promptCtx: Context) => {
  void refreshImageToolContext()
  ctx.inject(['credentials'], credentialCtx => {   // ← 外层 ctx
    credentialCtx.on('credentials/reference-updated', () => { void refreshImageToolContext() })
    credentialCtx.on('credentials/record-updated', () => { void refreshImageToolContext() })
  })
  promptCtx.effect(() => promptCtx.systemPrompt.context({ … }))   // 同一回调里其余地方都用的是 promptCtx
  …
})
```

内层的 `ctx.inject` 把 credentials 的子 fiber 挂在插件根上，而不是 systemPrompt 的子 fiber 上。systemPrompt 每重新提供一次，外层回调就重跑一次，但上一次挂在根上的 credentials 子 fiber 不会被撤销，于是 `credentials/*` 监听器每次多一份，`refreshImageToolContext` 被重复调用。

### 为什么现在看不到

插件 inject 了 `tools`，而 dsh 的 `tools` 服务本身 inject 了 `systemPrompt`。所以 systemPrompt 重启时 tools 跟着重启，整个插件连带重来，多出的那份也一起撤掉了。真实宿主上 systemPrompt 重启两次，监听器仍各 1 个。宿主一旦调整服务依赖 (例如 `tools` 不再依赖 `systemPrompt`)，问题就会出现。我们在不级联重启的环境里确实观察到 systemPrompt 每重启一次，credentials 监听器就多一份。

### 建议修法

一个词：

```js
promptCtx.inject(["credentials"], (credentialCtx) => { … })
```

## 回访 (2026-11-28)

| # | issue | 状态 | 修复 | 已发布吗 |
|---|---|---|---|---|
| 1 | [dsh-windows-mcp#19](https://github.com/helloHub1212/dsh-windows-mcp/issues/19) | 已关闭 | `a9435c7`，6 条路由各经 `scoped.effect` 登记 (`lib/index.js:1698-1700`) | 0.2.13 (npm latest) |
| 2 | [dsh-prime-memory#51](https://github.com/drscrewdriver/dsh-prime-memory/issues/51) | **仍开着** | `f3b4cb8`，`withFileLog` 返回 `close()`，`beforeExit` 处理器具名后 `process.off`，apply 里 `ctx.effect` 登记 | 0.29.5 (npm latest，发布包里有 `process.off('beforeExit'`) |
| 3 | [dsh-market#1309](https://github.com/dsh-market/dsh-market/issues/1309) | 已关闭 | PR #1311 (合进 `nightly1014`)：`registerRoute` 把每个 disposer 记进 `settledRoutes`，登记失败时撤销前面的 | 1.85.0 (npm latest，发布包里有 `settledRoutes`) |
| 4 | [dsh-remote#227](https://github.com/flymysql/dsh-remote/issues/227) | 已关闭 | PR #232：逐条 `try/catch`，一个 `inner.effect` 撤销实际登记了的 (`lib/http-transport.js:222-236`) | **未发布**：npm 1.5.0 的 `:171` 仍是 `guarded.map` |
| 5 | [Whale-Widget#358](https://github.com/MeteorNOX/DeepSeek-Balance-Whale-Widget/issues/358) | 开着，无回复 | 无，`lib/index.js:884` 未变 | — |
| 7 | [dsh-connect-workbuddy#323](https://github.com/dingminhua/dsh-connect-workbuddy/issues/323) | 已关闭 | `0e750b6`，`disposers.push(ctx.effect(() => ctx.webServer.register(entry)))` (`src/web-status.ts:1951`) | 5.32.0 起 (npm latest 5.34.0) |
| 8 | [dsh-image-gen#169](https://github.com/shanliuling/dsh-image-gen/issues/169) | 开着，作者回"收到" | 无，`src/index.ts:459` 仍是外层 `ctx.inject` | — |
| 9 | [dsh-mobile-plugin#47](https://github.com/WNLUO/dsh-mobile-plugin/issues/47) | 刚提 | — | — |
| 10 | [dsh-free-search#173](https://github.com/DDDMUC/dsh-free-search/issues/173) | 刚提 | — | — |

**更正：嵌套 `ctx.effect` 不由外层 effect 收集。** workbuddy 的作者在 #323 里指出，我们说的"外层效应体抛错时 Cordis 撤销已收集的内层 effect"不对。核对 `.vendor/cordis/fiber.ts:424-567`，作者是对的：

- `effect()` 一开始就把自己的 wrapper 推进 **fiber** 的 `_disposables` (`:526`)；外层 effect 的 `collect` 只收效应体**返回**的 disposer (`:372-374`)，效应体里另调的 `ctx.effect` 不会成为它的子项；
- 外层效应体抛错时 (`:529-542`)，只撤销外层自己收到的 disposer。内层 effect 仍挂在 fiber 上。apply 抛错只让 fiber 进入 FAILED (`:693-700`，只记 `_error`)，不会跑 `_disposables`；要等 fiber 卸载 (`_unload`，`:720`) 时才撤销。

所以"每条都经 `ctx.effect` 登记"的修法结论不变 (不再泄漏)，但撤销发生在停用插件时：失败之后、停用之前，已登记的几条仍然挂着；停用后不残留，再启用也不会撞到它们。第一批 3–7 号的通用正文与 9 号 (#47) "顺带两点"里的同一说法都要按这个理解。#47 需要补一条更正评论。

**#47 的复查 (2026-11-28)。** 主问题与修法在 HEAD 上成立：`shell/runtime.js` 与 0.5.97 相比只改了参数透传和分派器带上 `auth` 等字段，`detach()`、分发表、`index.js` 外壳的 effect、`shell/half-route.js` 都没变。正文里有三处要更正：

- "再启用后日志里没有报错"不准确：新实例每条路由撞名时由 `lib/impl.js:565-568` 的 `mountRoute` 兜住，各记一条 warn (`路由 … 没挂上：…`)。fiber 全部 ACTIVE 这一点不变；
- "顺带两点"之一的机制错了，见上一段。`installHostHalf` (`shell/half-route.js:35`) 两条写在数组字面量里，在 `index.js:212` 的 effect 体里调用，第 2 条抛错时第 1 条确实没人撤销，这个结论不变；
- "顺带两点"之二应撤回：`__dshZeroNewsCurrent` 在 HEAD 上已经没有了 (0.5.97 里来自 `lib/zeronews/wiring.cjs`)，剩下的 `Symbol.for('dsh-mobile-plugin.inbox-cleared-once')` (`lib/mobile/inbox-clean.js:281`) 是有意的每进程一次的标记。

---

# 第二批 (2026-11-28 核对；9、10 已提交，11 暂不提)

来源：FINDINGS.md 里在真实宿主上复现、第一批没有收的第一档 4 条。四个仓库都没有归档，都开着 issue。按默认分支的 HEAD 核对问题代码，并按关键词搜过已有 issue。

| 插件 | 仓库 | 审计版本 → HEAD | 问题还在吗 | 重复 issue |
|---|---|---|---|---|
| dsh-mobile-plugin | [WNLUO/dsh-mobile-plugin](https://github.com/WNLUO/dsh-mobile-plugin) | 0.5.97 → 0.5.134 | 在：`lib/shell/runtime.js:621` 的 `detach()` 仍不撤分派器 | 无。#24 (已关闭) 是就地换代留下重复路由，相关但不同 |
| dsh-free-search | [DDDMUC/dsh-free-search](https://github.com/DDDMUC/dsh-free-search) | 0.9.82 → 0.9.88 | 在：重入保护 `lib/index.js:1885-1889`，`registerOnce` `:1891` | 无。#82 (已关闭) 是这个保护的来由 |
| dsh-token-diet | [ybh618618/dsh-token-diet](https://github.com/ybh618618/dsh-token-diet) | 0.1.0 → 0.1.0 | 在：`lib` 与 0.1.0 逐字相同 | 无。仓库自 2026-10-24 未更新，#1 (别人提的) 20 天无回应 |
| ds-harness-remote | [liguobao/ds-harness-remote](https://github.com/liguobao/ds-harness-remote) | 0.6.7 → 0.6.9 | **已修掉，不提** | — |

- **ds-harness-remote**：#542 (2026-11-21) 加了 `mountControlRoute` (`packages/plugin/src/index.ts:606`)，前缀路由经 `ctx.inject(['webServer'], …)` 登记，webServer 重启或晚到时换挂；`activate` 开头那次没有 inject 的 `ctx.get('webServer')` 也去掉了。v0.6.8 的 tag 里已经有，0.6.7 没有，所以已经发布。剩下的 `globalThis` 上的 `hmr-safe-settings-pump` 槽从名字看是有意跨热重载保留的，不单独提。`dshRemote` 冲突另有 #347 (已关闭)，属第二档，到时再看。
- 路径都是仓库里的源码。dsh-mobile-plugin、dsh-free-search、dsh-token-diet 都直接提交 `lib/*.js`，行号以 HEAD 为准。

## 9. dsh-mobile-plugin：停用后 286 条路由和 2 条升级路由仍由旧实例应答

**仓库**：https://github.com/WNLUO/dsh-mobile-plugin/issues (引用 #24)

**已提交** (2026-11-28)：https://github.com/WNLUO/dsh-mobile-plugin/issues/47 (标签 bug)

**标题**：停用插件后分派器路由不撤销：286 条路由和 2 条升级路由仍转给已卸载的实现，再启用时新分派器全部撞名

### 现象

停用 dsh-mobile-plugin 后，插件 fiber 已是 DISPOSED，但 `/api/mobile/*`、`/api/relay/*`、`/api/cloudflare/*` 下的路由只少了外壳自己的两条 `/api/relay/host-half*`，其余 286 条路由和 2 条升级路由仍登记在宿主上。请求照常返回插件格式的 401 (`{"ok":false,"error":{"code":"unauthorized",…}}`)，宿主对不存在的路径返回 404 作对照。

再启用后，除了 `host-half`，路由上挂的仍是停用前那批分派器 (同一函数对象)。新实例的分派器撞名没挂上，日志里没有报错，fiber 全部 ACTIVE。请求由旧实例的分派器转给旧代的处理器，直到宿主重启。

| 时刻 | fiber | `/api/mobile/*` | `/api/relay/*` | `/api/cloudflare/*` | 升级路由 | `/api/mobile/v1/commands` |
|---|---|---|---|---|---|---|
| 装上后 | ACTIVE ×2 | 214 | 72 | 2 | 3 | handler#33，HTTP 401 |
| 停用后 | DISPOSED | 214 | 70 | 2 | 2 | handler#33，HTTP 401 |
| 再启用后 | ACTIVE ×2 | 214 | 72 | 2 | 3 | handler#33，HTTP 401 |

环境：dsh 0.2.2-rc.5，插件 0.5.97；"停用/启用"是经 loader 停用、启用 `dsh-mobile` 条目。

### 原因

蓝绿换代的设计本身没问题：每个路径用原始的 `register` 挂一个稳定分派器 (`lib/shell/runtime.js:118` 的 `ensureHttpDispatcher`、`:141` 的 `ensureUpDispatcher`)，裸 disposer 存在 `httpDispatchers`、`upDispatchers` (`:88-89`)。换代与回滚时会撤掉多余的分派器 (`:186-244`)。

但卸载走的 `detach()` (`:621`) 只卸掉当前代的 fiber：

```js
async function detach() {
  detached = true
  clearBacklogRetry()
  const oldFiber = fiber
  fiber = null
  current = null
  if (oldFiber) await oldFiber.dispose()
}
```

既不撤 `httpDispatchers`/`upDispatchers`，也不清空 `liveHttp`/`liveUp`。`lib/index.js:183-206` 的 `ctx.effect` 在撤销时还原 `server.register` 后调用的就是它。所以分派器连同 `liveHttp` 里旧代的处理器一起留在宿主上。

### 建议修法

`detach()` 末尾撤掉全部分派器，并清空分发表：

```js
async function detach() {
  detached = true
  clearBacklogRetry()
  const oldFiber = fiber
  fiber = null
  current = null
  try {
    if (oldFiber) await oldFiber.dispose()
  } finally {
    for (const unregister of httpDispatchers.values()) { try { unregister() } catch { /* ignore */ } }
    for (const unregister of upDispatchers.values()) { try { unregister() } catch { /* ignore */ } }
    httpDispatchers.clear()
    upDispatchers.clear()
    liveHttp = new Map()
    liveUp = new Map()
  }
}
```

### 顺带 (可选写进同一个 issue)

- 外壳自己的两条 `/api/relay/host-half*` 是逐条登记的，第 2 条登记失败时第 1 条残留，没有人撤销。每条都经 `ctx.effect(() => …register(…))` 登记即可。
- 停用后 `globalThis` 上仍留着 2 个 Symbol 槽与 `__dshZeroNewsCurrent`。

## 10. dsh-free-search：被 inject 的服务重启一次，插件就只剩空壳；撞名时会"复用"别人的设置接口；设置桥的嵌套 inject 用了外层 ctx

**仓库**：https://github.com/DDDMUC/dsh-free-search/issues (引用 #82)

**已提交** (2026-11-28)：https://github.com/DDDMUC/dsh-free-search/issues/173 (标签 bug；三个问题合在一个 issue 里)

**标题**：apply 的重入保护挡掉了 Cordis 的正常重跑：systemPrompt 重启后设置接口与工具全部消失

### 现象一：服务重启后插件只剩一个 fiber

真实宿主上停用再启用 system-prompt 条目一次：

```
fibers    装上后                web-search-free ACTIVE ×14, PENDING ×1
route     装上后                /api/dsh-free-search-settings/describe 已登记
fibers    systemPrompt 重启 1 次  web-search-free ACTIVE                  (只剩一个)
route     systemPrompt 重启 1 次  未登记
```

插件的唯一 fiber 仍是 ACTIVE，日志里只有一条 `apply() already ran on this context — skipping the re-entry`，设置页与全部工具消失，直到重启插件。checker 里 `web`、`settings`、`tools`、`systemPrompt` 任一个重启都会触发；dsh 的 `tools` 依赖 `systemPrompt`，`webServer`、`connection` 依赖 `webStartup`，所以实际会触发它的服务比 inject 列表里写的更多。

### 原因一

`lib/index.js:1885-1889`：

```js
if (appliedContexts.has(ctx)) {
  ctx.logger?.warn?.("free-search: apply() already ran on this context — skipping the re-entry");
  return;
}
appliedContexts.add(ctx);
```

Cordis 在插件 inject 的服务 (`:1518`，`web`、`settings`、`tools`、`systemPrompt`) 重新提供时，先撤销这个 fiber 的全部效应，然后**在同一个 ctx 上**再调一次 apply。这是正常的重跑，但 `WeakSet` 按 ctx 记，分不出它和异常的重入，把它也挡掉了。

**与 #82 的关系。** 这个保护是 0.9.4 作为"防御性修复"加的，防的是"未 dispose 的重入"，当时说明了还没确认上游原因。后来 #82 里追到的链路是：HMR/loader 重建 EntryGroup → `entry.update()` 重写 web 的配置 → web 服务重建 → 正常重跑 apply → 接管 provider 时写配置，撞上 `package.json.lock` 的写锁超时 → 下一轮。这一路上都是正常的 dispose 加重跑，没有出现过没 dispose 的重入；循环最后是 0.9.5 起的日志去重与幂等检查止住的。所以这个保护防的情况没有被证实，挡掉的却是每一次正常的服务重启。

### 建议修法一

让保护在效应撤销时解除。这样正常重跑能通过；万一真有没撤销就重入的情况，仍然会被挡住：

```js
if (appliedContexts.has(ctx)) { /* 原样 */ return; }
appliedContexts.add(ctx);
if (typeof ctx.effect === "function") ctx.effect(() => () => appliedContexts.delete(ctx));
```

放开重跑不会让 #82 的循环回来：HEAD 的接管 (`:2976` 起) 只在当前 provider 不是自己时才写配置 (`fetchSelection.current !== fetchProvider.id`，search 同理)。接管写一次、web 重建、apply 重跑，第二次看到的已经是自己，不会再写。

### 现象二：撞名时把 `/mutate` 让给了别人

`registerOnce` (`:1891`) 遇到 `already registered|duplicate` 就返回空 disposer，并记一条 "reusing it"。设置桥的路由也经它登记 (`:2898`)。真实宿主上先由另一个插件占住 `/api/dsh-free-search-settings/mutate`，再启用 free-search：所有 fiber 都是 ACTIVE，但对 `/mutate` 的请求由占位者的处理器应答 (占位者返回 HTTP 418)。free-search 以为在复用自己的路由，实际上设置写入请求交给了另一个插件。

### 建议修法二

对 provider，"已存在就复用"也许是有意的 (#82 的场景)。但 webServer 路由撞名时，占着路径的那一方不一定是自己，不应当吞掉。设置桥的路由 (`:2898`) 改为直接 `register`，撞名就抛错让这个 fiber 失败，用户能在插件列表里看到。另外最好逐条经 `sctx.effect(() => sctx.get("webServer").register(route))` 登记，这样中途失败时已经登记的几条也会撤销 (现在是 `.map` 收进数组、最后统一撤销，与第一批 3–7 号 issue 同一类问题)。

### 现象三：设置桥每重跑一次，根上就多一个等 `connection.authentication` 的 fiber

真实宿主上重启 web-startup 一次 (它连带重启 webServer)：

```
fibers    装上后               web-search-free ACTIVE ×14, PENDING ×1
fibers    webStartup 重启后     web-search-free ACTIVE ×14, PENDING ×2
```

### 原因三

`lib/index.js:2858` 起：

```js
ctx.inject(["webServer", "settings"], (sctx) => {
  let connectionContext = sctx;
  ctx.inject(["connection.authentication"], (actx) => {   // ← 外层 ctx
    connectionContext = actx;
    …
  });
  sctx.effect(() => { /* 设置桥路由 */ });
});
```

内层的 `ctx.inject` 把等 `connection.authentication` 的子 fiber 挂在插件根上，而不是 `sctx` 下面。webServer 或 settings 每重新提供一次，外层回调重跑一次，就多挂一个，旧的那个不随 `sctx` 撤销，一直留到插件卸载。0.2.2-rc.5 上没有 `connection.authentication`，所以多出来的 fiber 停在 PENDING；在有这个服务的 DSH 上，它们会是 ACTIVE 并持续累积，各自持有一份旧 `sctx` 的闭包。

**归因已验证 (2026-11-28，checker)**：0.9.82 里等 `connection.authentication` 的 inject 只有这一处 (`lib/index.js:2450`)。把它改成 `sctx.inject` 之后重跑全套检查：webServer、webStartup 重启的两个见证消失，其余结果 (含现象一的 4 个重启见证、A 类故障注入) 与原版逐字相同，装上后仍是 ACTIVE ×14 + PENDING ×1。真实宿主上没有用改过的包重跑。

### 建议修法三

一个词：

```js
sctx.inject(["connection.authentication"], (actx) => { … });
```

## 11. dsh-token-diet：webServer 重启一次，`/token-diet` RPC 就再也不登记

**仓库**：https://github.com/ybh618618/dsh-token-diet/issues

**标题**：`installWebRoute` 只在 apply 时读一次 webServer；webServer 重启后 `/token-diet` 路由消失，插件仍是 ACTIVE

**说明**：仓库自 2026-10-24 没有更新，#1 也没有回应，提了可能没人处理。

### 现象

真实宿主上停用再启用 webserver 条目：

```
route     装上后            /token-diet 已登记, handler#1
route     webServer 重启后   未登记
route     webServer 晚到    未登记
route     插件重启后         已登记, handler#2
```

插件全部 fiber 一直 ACTIVE，不报错，客户端的预算显示从此连不上，直到重启插件。

### 原因

插件的 `inject` 是空数组 (`lib/index.js:39`)，`installRpc` 用的是插件根 ctx：

1. 先试 `connection.rpc.handle` (`lib/host/rpc.js:258`)。这个方法要求调用者 inject 了 `webServer`，根 ctx 没有，于是抛 `cannot get property "webServer" without inject`，被 catch 成一条 warn；
2. 退回 `installWebRoute` (`:318`)，用 `softService(ctx, 'webServer')` 读一次 webServer，登记前缀路由，返回裸 disposer。

webServer 重启时，旧实例上的路由随旧实例消失，插件没有 inject webServer，不会重跑，也就不会重新登记。`ctx.inject(['connection'], …)` (`lib/index.js:157`) 只在 connection 出现时重装，不管 webServer。

对 `/token-diet/x` 发 GET 得到 405 (退路自己的方法检查)，走 connection 时应是 401，可以印证现在实际走的是退路。

### 建议修法

把通道的安装放进 `ctx.inject(['webServer'], …)`，用这个子 ctx 去登记。这样 `rpc.handle` 能用了 (调用者 inject 了 webServer)，webServer 重启或晚到时也会重新登记：

```js
ctx.inject(['webServer'], (webCtx) => {
  webCtx.effect(() => installRpc({ ctx: webCtx, services: rpcServices }), 'token-diet: RPC carrier')
})
```

原来 `install()`、`disposeChannel` 与 `lib/index.js:157` 的 connection 重装逻辑可以放进这个回调里，或者改成 `ctx.inject(['webServer', 'connection'], …)` 再保留一个只等 webServer 的退路，留给作者选。
