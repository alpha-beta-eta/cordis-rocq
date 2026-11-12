# 第三方 dsh 插件的生命周期审计

排查对象:npm 上月下载量最高的 6 个第三方 dsh 插件(2026-11-12 统计,排除目录与数据包)。目的是
看真实插件的生命周期骨架能否按插件义务 C(RULES.md 第 1 节)自动检查,以及模型缺什么。

| 插件 | 版本 | 月下载量 | 源码 |
|---|---|---|---|
| dshmarket | 1.73.18 | ~121 万 | `github.com/dsh-market/dsh-market` |
| dsh-windows-mcp | 0.2.8 | ~75 万 | `github.com/helloHub1212/dsh-windows-mcp` |
| dsh-pet | 0.4.7 | ~55 万 | `github.com/PC2005-cloud/dsh-pet` |
| dsh-context | 0.83.1 | ~46 万 | `github.com/bowenliang123/dsh-context` |
| dsh-whale-widget | 0.4.2 | ~45 万 | npm 包(GitHub 仓库未能克隆) |
| dsh-ops | 0.5.4 | ~20 万 | `github.com/T-Auto/dsh-ops` |

方法:只读代码,不安装、不运行。源码克隆到 `D:\dsh-plugins\src`,发布包解压到
`D:\dsh-plugins\<名字>\package`,两者对照确认入口一致。下文的位置都相对于各插件的源码根目录
(dsh-pet 为 `dsh-pet/src`,dsh-ops 为 `src`,whale-widget 为发布包)。人工核对过的位置标 ✔。

检查的五项:

- (a) 每个服务访问的键 k ∈ d ∪ p(d 为 `inject`,p 为自己 provide 的键);
- (b) 每个 provide 的键 k ∈ p,且名字静态;
- (c) 启动程序有界;
- (d) 所有副作用都登记在 fiber 的 disposer 列表上(恢复精确性的前提);
- (e) 运行期事件处理器产生的效应以子 fiber 承载(`O-React`)。

## 结论

| 插件 | (a) | (b) | (c) | (d) | (e) |
|---|---|---|---|---|---|
| dshmarket | ✗ | ✓ | △ | ✗ | ✗ |
| dsh-windows-mcp | △ | ✓ | ✓ | ✗ | ✗ |
| dsh-pet | ✗ | △ | ✓ | ✗ | △ |
| dsh-context | ✗ | ✓ | △ | ✗ | ✓ |
| dsh-whale-widget | △ | ✓ | ✓ | △ | △ |
| dsh-ops | ✗ | △ | △ | ✗ | ✗ |

✓ 可语法检查;△ 需要标注或小重构;✗ 照现在的写法在模型之外。

1. **空间部分基本可查。** 4 个插件不提供任何服务,另外 2 个各一个字面量 provide(dsh-pet 的
   `petApi7340`,dsh-ops 的 `opsSettings`),都没有 `provide` 元数据,p 只能从代码推出。inject 的
   键全是字面量;启动程序几乎都是同步的,循环只遍历静态数组或有限的配置。
2. **未声明的 `ctx.get` 普遍存在,而且多数是有意的。** 6 个插件都有(从 dsh-windows-mcp 的少数几处
   到 dsh-context 的约 30 处)。注释说明了原因:想用某个服务,又不想在缺少它的宿主上停在 PENDING,
   于是在请求时惰性读取。这是模型缺少**可选依赖**,不只是插件不规范(差异 m)。
3. **恢复精确性对每个插件都不成立,原因分两类。**
   - 应登记而未登记的临时资源:路由、计时器、子进程、模块级状态。这类是 bug,可以重构。其中一部分
     来自 dsh 的 API:`webServer.register` 只返回裸 disposer,不像 `tools.register`、`slots.inject`
     那样自动挂到调用者的 fiber 上(dsh `packages/host/webserver/src/index.ts:445` ✔)。
   - 有意持久的外部状态:配置文件、profile、凭据、缓存、日志。它们本来就不该撤销。
4. **生命周期是两个 fiber 交集的效应很常见,模型没有对应构造。** dsh-ops 在 `agent/created` 中
   `agent.ctx.plugin(...)`,把子 fiber 挂在别人的上下文上,再用私有 Map 手工回收(5 处,例如
   `publication/native.ts:112` ✔);dsh-windows-mcp 在每个 agent 的上下文上 `tools.restrict`。
   这类效应应在"本插件卸载"或"该 agent 销毁"任一发生时撤销;`O-React` 只能把子 fiber 挂在自己下面。
5. **dshmarket 是编排者。** 它改 loader 条目、热挂载 `Include` 子树、调用 CLI 安装插件后重启进程。
   这些在模型里是外部编排标签(`O-Insert`、`O-Dispose`),它需要的是编排者的义务,而不是组件义务 C。

## 各插件要点

### dshmarket

- 宿主入口 `src/index.ts`:函数插件,没有顶层 `inject`;依赖全部经动态 `ctx.inject` 子 fiber
  (`['webServer','loader']`,`:290`)。客户端 `inject = ['slots','locale','theme']`。
- (a) 10 处未注入的 `get`:`profileContext` ×6、`connection` ×2、`agents`、`desktopProfiles`、
  `pluginManager`。`ctx.get('desktopProfiles')` 一次性决定走官方 Desktop、Web CLI、第三方 Desktop
  三条分支中的哪一条,之后不再观察(`:295` ✔)。
- (c) `void mountClientOnlyDeps(...)` 在效应之外异步遍历 profile 中的包(`routes.ts:893`)。
- (d) 子进程(`dsh … plugin add|remove|install|update`、`npm install -g pnpm`)、约 33 处文件写入
  (profile 清单、patch 行、日志、快照)、自我 SIGTERM 的重启助手(`restart.ts:513-721`)、一个有意
  跨重载存活的 `globalThis` 槽(`official-desktop.ts:450`)。
- (e) HTTP 与 `internal/plugin` 处理器在长寿的 inject 上下文上 `ctx.plugin`(`hot.ts:1003`),并通过
  `loader.entries()[i].update({disabled})` 改别的条目。

### dsh-windows-mcp

- 宿主入口 `lib/index.js:1316`:`{ name, apply }`,没有 `inject`;四个静态 `ctx.inject` 子 fiber。
- (a) `ctx.get('tools')`、`ctx.get('agents')`、`scope.get('connection')`,以及读别的 fiber 的
  `agent.ctx.get('tools')`(`:415`)。
- (d) 6 个 `webServer.register` 的返回值被丢弃(`lib/index.js:1259-1264` ✔):卸载后路由仍在,重载时
  因重复注册抛错,被 catch 后只打警告。`uv tool install` 子进程只在超时或取消路由时被杀。改写 profile
  的 `cordis.patch.yml`。
- (e) 在每个 agent 的上下文上 `tools.restrict({deny})`(`:425`),本插件卸载时没有释放。

### dsh-pet

- 宿主 `host/index.ts`:`inject` 为 6 个必需服务,`apply` 同步;唯一的 provide 是 `petApi7340`
  (`setup.ts:194`)。客户端另有 inject 列表,与清单的 `dsh.client.inject` 不一致。
- (a) 宿主 5 个、客户端 5 个未声明的名字,经 `optionalService` → `ctx.get(name, false)`;另有一处把
  `get` 作为函数传出,名字在运行时决定(`client/baifan.ts:66`)。
- (c) apply 有界;三个自我重新挂起的 `setTimeout` 轮询、500ms 端口等待重试、helper 崩溃重启循环都是
  有意无界的,应建模为 Active 期间的反应。
- (d) `startHelper()` 在任何效应之外启动 Electron helper 子进程(`host/index.ts:182` ✔),只在
  lifecycle 效应中停止;Electron 下载最长 10 分钟,卸载不能中止;模块级的提供者注册表与缓存跨卸载存活。
- 拆除:lifecycle 效应内部有注释写明的顺序要求;客户端拆除时向宿主自己的路由发 `DELETE`。

### dsh-context

- 宿主 `inject ['sessionProjections']`;约 15 个 `watch*Channel` 各开一个静态 `ctx.inject`。
- (a) 宿主约 17 处、客户端约 13 处未注入的 `get`(`tools`、`llm`、`settings`、`credentials`、
  `sessionQuery`、`agents` 等)。
- (d) 替换 `tools` 服务实例上的 `register`,并监听 `internal/get` 观察谁读了 `tools`
  (`host/attribution.ts:102-151`),恢复已登记,但假设之后没人再包装它;`sweep.ts:37-60` 启动不可取消
  的异步循环,写持久行。
- (e) 处理器只改局部 Map 或返回 waterfall 结果,可查。

### dsh-whale-widget

- 宿主 `lib/index.js:723`:没有 `inject`(注释说明是有意移除);一个静态
  `root.inject(['webServer','credentials','connection'])`,内部约 30 个路由。客户端是不经 Cordis 的
  浏览器脚本,经 `tapIndex` 注入。
- (a) 两处可选读取:`deepseekAccount`、`sessionTitle`。
- (d) 路由的 disposer 先收集到数组,最后才由一个 `ctx.effect` 登记(`:4919`):注册中途抛错(例如路由
  重复)会泄漏之前注册的全部路由。模块加载时 `dns.setDefaultResultOrder('ipv4first')`,改变整个进程。
  `ctx.credentials.set` 改宿主凭据;多处写 `$DSH_HOME/.dshw-*`。

### dsh-ops

- 宿主 `index.ts`:没有 `inject`、`provide`;`await host.plugin` 依次挂上 runtime-settings(唯一的
  provide `opsSettings`)、4 个模式、按配置的预设,再条件挂上至多 3 个组件。以 `{config}` 形式挂载时
  `mount` 重新包装模块,丢掉了它的 `inject`,于是 tui 无保护地 `ctx.get('tuiPanels')`。
- (a) `agents` 11 处,`fs`、`approval`、`shellEnv`、`ptcRuntime`、`workingDirectory`、`settings`、
  `sessionProjections` 各若干处未注入;`sandboxPolicy`、`sandbox` 只在兄弟 inject 中注入,却从外层
  上下文读取。`service()` 包装吞掉错误,缺失的服务读成 `undefined`。
- (d) 大量模块级状态与引用计数的共享运行时;启动时的清扫 `setTimeout` 不清除;Windows 上原生
  `child_process.spawn` 改 ACL 并写回执;部分文件清理推迟到下次进程启动。
- (e) 见结论 4;另有带 `{global: true, prepend: true}` 的 `internal/dispatch` 监听器观察所有分发。
- 拆除:disposer 多为异步;拆除时读 `tools`;预设拆除恢复默认预设,下一次激活要先
  `settlePendingRestore`,即拆除与下次启动之间有显式顺序依赖。

## 越界的写法是否绕开了 Cordis 与 dsh 的设计

大多不是。它们越出的是本模型的纪律,而 Cordis 与 dsh 比模型宽松得多。分三层:

1. **按设计使用。**
   - 嵌套 `ctx.inject`:Cordis 说明它是 `ctx.plugin({ inject, apply })` 的简写(`registry.ts:165-175`),
     按功能拆出带依赖的子 fiber 正是本意。
   - 向注册表登记条目(`tools.register`、`slots.inject` 等):dsh 的扩展方式本来如此,插件之间
     几乎不互相 provide。
   - 把有顺序要求的拆除放进同一个效应:上游 Cordis 注释中的约定(DESIGN.md 2.1 节,差异 e)。
2. **允许、宿主自己也这样做,但保证不覆盖。**
   - 未注入的 `ctx.get`:Cordis 有意提供(`reflect.ts:247`),dsh 非测试代码中有 368 处(差异 m)。
   - 不挂到 fiber 上的资源:`webServer.register` 是 dsh 自己的 API,只返回裸 disposer。
   - 模块级状态、`ctx.root` 上的共享状态、Active 期间的后台循环:Cordis 都不禁止。

   这一层的问题是:Cordis 的清理与依赖顺序保证只在一套纪律下成立,而这套纪律既没有写成义务,
   也没有检查。代码允许,保证却不再覆盖。
3. **确实绕开设计。** 集中在少数几处:
   - 猴补丁(dsh-context 替换 `tools.register`);
   - 拦截运行时自身的扩展点(`internal/get`;带 `{global: true, prepend: true}` 的
     `internal/dispatch`),属于差异 o 的元层;
   - 把子 fiber 挂到别的插件的上下文上再自行回收(dsh-ops 的 `agent.ctx.plugin(...)`);
   - 刻意跨重载存活的 `globalThis` 槽、给自己进程发 SIGTERM 的重启(dshmarket)。

所以差距主要在"Cordis 允许什么"与"Cordis 保证什么"之间。本形式化把隐含的纪律写成显式的义务 C,
用它衡量,大部分写法越界;按 Cordis 自己的标准,它们多数合法。改进的方向是把纪律表达出来并强制
执行,而不是归咎于插件:宿主的注册接口自动挂到调用者的 fiber 上、提供可选依赖、用 lint 检查义务 C,
只为第 3 层的元层操作提供受控的原语。这样"按 Cordis 的方式写"与"满足模型"才是同一件事。

## 对形式化的影响

1. **现阶段逐个插件的精化证明证不出东西**:要证的性质对这些插件本身就不成立(路由泄漏、效应之外的
   子进程、挂在别人 fiber 上无人回收的效应)。检查器的首要用途是找 bug。
2. **模型要扩充三样东西**,都由真实插件归纳而来:
   - 可选依赖:有无影响行为,但不阻止激活;要规定它出现或消失时是否触发重载,否则合流取决于时机;
   - 交集生命周期的效应:挂在另一个 fiber 上,任一方结束即撤销;
   - 外部持久世界:文件、凭据、配置不属于上下文,恢复精确性只对上下文陈述。
3. **编排者单独对待**:dshmarket 这类插件的义务是关于它发出的编排标签,而不是组件义务 C。

## 对 dsh 与 Cordis 的建议

- `webServer.register` 像 `tools.register` 一样经 `ctx.effect` 挂到调用者的 fiber 上,一处修改消除
  一类泄漏(dsh-windows-mcp、dsh-whale-widget)。
- 提供正式的可选依赖,并对读取未注入的服务给出警告(差异 m 的建议,这次有了数据支持)。
- 给"挂在另一个 fiber 上的效应"一个原语,取代 dsh-ops 等插件的私有 Map 手工回收。
