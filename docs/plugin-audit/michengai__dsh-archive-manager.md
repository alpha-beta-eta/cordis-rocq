# @michengai/dsh-archive-manager 1.4.1

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主入口 `lib/index.js` (`main`)，经 `cordis.patch.yml` 插入为 loader 条目 `ui-workspace-archive-manager`；宿主 inject = `webServer` + `workspaceRegistry, sessionPersistence, typert` (`lib/index.js:6` ✔，`lib/host-install.js:2` ✔)；不 provide (另导出 `ArchiveWorkspaceRegistry extends WorkspaceRegistry`，`lib/workspace.js:429`，但 patch 未用它替换官方 workspace)。客户端 `lib/client.js` (`__ModuleLoader__` 包装的 bundle)，inject = `slots, sessions, workspaces, locale, remote, typert` (`lib/client.js:27` ✔)。
- 一句话功能：给会话侧栏加归档/恢复/收藏/永久删除/移动工作区/缓存诊断；做法是把自己的方法**覆盖到官方 `workspaceRegistry` 实例上**，并注册 3 条设置路由。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✗ | 宿主自身的 `ctx.get("workspaceRegistry")` (`lib/index.js:189`) 已在 inject 中，无问题。但被覆盖到 registry 上的方法以 `this.ctx` 运行，即**官方 workspace 插件的 ctx**，在那里读 `sessions`、`sessionProjectionCache`、`spillStore`、`agents`、`storageDomain` (`lib/workspace.js:454,606,1073,1193,499` ✔)——借别人的上下文访问，S1 无从检查。客户端未注入的 get：`remote.workspaceRegistry`(6 处)、`layout`(3)、`uiWorkspace`、`contextMenus` (均 `lib/client.js:27`，contextMenus 另见 `:19`)；都带 `?.`/判空，是有意的可选依赖。 |
| 0 | S2 | ✓ | 不 provide。 |
| 0 | S3 | ✗ | (1) 猴补丁服务实例：`installArchiveWorkspace` 把 `ArchiveWorkspaceRegistry.prototype` 的全部方法拷到官方 registry 实例上，重写 `unarchiveSession`，并改写其**原型**上的 typert remote-methods 描述符、设置 `typertRemote` (`lib/workspace.js:1203-1281` ✔)。(2) 穿过服务代理 (`symbols.original`) 直接删 webServer 内部表 `exact`/`prefixes` 里同路径的路由，并在 server 对象上挂 `Symbol.for` 袋 (`lib/index.js:41-62,90-93` ✔)。(3) 覆盖方法里 `this.ctx.effect(() => domain.close())` 把效应挂在 workspace 插件的 fiber 上 (`lib/workspace.js:499-500` ✔)。(4) `cordis.patch.yml` 改 loader：强制 `ui-workspace` 启用并插入自身条目——这是安装期配置，不是运行时编排。客户端另有 DOM 级补丁：`MutationObserver` 监视 `document.body`，往宿主渲染的侧栏行里插按钮、改设置导航图标 (`lib/client.js:25,27`)，React 挂在 `globalThis.__dshArchive*` 上从不清除 (`lib/client.js:4-7`)。 |
| 1 | L1 | ✓ | 启动同步、无循环；有界重试 `confirmColdCacheWrite` (100×20ms) 只在运行期调用 (`lib/cache-rebuild.js`)。客户端重试计数 `et=20` 有上界 (`lib/client.js:25`)。 |
| 1 | L2 | ✓ | 只 inject 宿主内置服务，无 provide/spawn。 |
| 2 | R1 | △ | 3 条 `webServer.register` 的裸 disposer 手工汇总进 `apply` 的返回值 (`lib/index.js:205-241` ✔)，Cordis 会收集返回的函数。但 `registerSettingsRoutes` 若在第 2/3 次 register 时抛错，外层 `try/catch` 吞掉错误，`disposeSettingsRoutes` 仍是空函数，已注册的路由泄漏 (`lib/index.js:223-227` ✔)。猴补丁有逆 (恢复原方法、描述符)。 |
| 2 | R2 | ✗ | 收藏存储域的关闭登记在 workspace 插件 fiber 上 (`lib/workspace.js:499-500`)，本插件卸载时不关；`favoriteDomainPromise` 缓存在 registry 实例上。路由处理器里 `spawn(explorer.exe/open/xdg-open, {detached}).unref()` 不登记 (`lib/native-explorer.js:55-73`，用户触发、一次性，可接受)。客户端 `slots.inject`、MutationObserver、监听器大多经 `r.effect` 回收 ✔。 |
| 2 | R3 | ✗ | 路由路径带包名前缀 `/api/michengai/dsh-archive-manager/...` ✓；但 `releaseManagedRoute` 不论归属删掉同路径的已有路由，且覆盖的是**共享的** `workspaceRegistry` 实例方法——与任何同样修补该实例的插件相遇时谁覆盖谁取决于顺序，卸载时按快照"恢复"会冲掉后来者的修改。 |
| 2 | R4 | △ | 持久状态 (保证不覆盖)：`$DSH_HOME/archive-manager/settings.json` (`lib/plugin-settings.js:95-186`)；storage domain 里的收藏；永久删除会话目录与 spill 目录 `rm -rf` (`lib/workspace.js:990,1075`)，都是用户操作。临时资源泄漏：上面 R1 的半注册路由、R2 的 domain 句柄、客户端 `globalThis.__dshArchive*`。读 `process.env.DSH_HOME`，不写。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | ✗ | 启动分支依赖共享状态/先前实例：`overlay[workspaceOverlay] === true` 则跳过 (`lib/workspace.js:1236`)，`raw.typertRemote` 已存在则跳过 (`:1225`)，typert `register` 报 "already registered" 时吞掉并返回空逆 (`:409-414`)——后者使逆依赖于谁先注册。 |
| 3 | C3 | ✗ | 猴补丁的逆是"恢复安装时的快照" (`lib/workspace.js:1218-1221,1266-1277`)，与状态相关。 |
| 3 | C4 | ✓ | 不 spawn 子 fiber。 |
| 3 | C5 | ✓ | 启动期无 emit/waterfall；`waterfall("workspace/session-activity")` 只在运行期 (`lib/workspace.js:645`)。 |

**最高层**：不在模型内。核心机制是修补另一插件提供的服务实例 (含原型) 并直接改 webServer 内部路由表，S3 不成立。
**升级路径**：(1) 不再覆盖 `workspaceRegistry`，改为自己 provide 一个字面量服务 (如 `archiveManager`) 并用自己的 typert remote 暴露，内部只经公开 API 调 `workspaceRegistry`；需要的 `sessions`/`sessionProjectionCache`/`spillStore` 写进自己的 inject (或标注为可选依赖)；(2) 删掉 `releaseManagedRoute` 对内部表的操作，每条路由用 `ctx.effect(() => ctx.webServer.register(...))` 登记；(3) storage domain 在本插件 ctx 上打开并 `ctx.effect` 关闭。做完 (1)(2)(3) 可到第 2 层 (持久文件/删除记为保证不覆盖)；若再去掉 "already registered" 吞错分支，C2/C3 也可满足，到第 3 层。客户端的 DOM 注入要么换成宿主提供的 slot/contextMenus API，要么只能按"模型外但有 disposer"标注。
