# 第三方 dsh 插件的生命周期审计

**排查对象**：npm 上月下载量最高的 26 个第三方 dsh 插件，2026-11-23 统计，用 `api.npmjs.org` 的 last-month 数据。

- 排除目录与数据包：`dsh-plugin-catalog`、`dsh-plugin-updates`。
- 排除不是 Cordis 插件的包：`cc-safety-net` 是给多个 agent CLI 共用的钩子程序。
- 其中 6 个是上一轮 (2026-11-12) 审计过的，本轮按最新版本重审；另外 20 个是新加的。

**目的**：按汇总定理 (`theories/Summary.v`，笔记的 thm-summary) 的四层保证，逐个判断真实插件落在哪一层、卡在哪条前提上。

**方法**：只读发布包，不安装、不运行、不克隆。包解压在 `D:\dsh-plugins\<名字>\<版本>\package`。每个插件的逐条证据在 [plugin-audit/](plugin-audit/) 下，每个插件一个文件，文件中位置都相对于包根，人工核对过的标 ✔。

## 四层与检查项

| 层 | 汇总定理给的保证 | 插件侧要检查的前提 |
|---|---|---|
| 0 安全 | 良构、提供者比依赖者活得久 (演算本身无假设) | 插件的行为落在模型内：S1 只访问 inject ∪ 自己 provide 的键；S2 provide 的键静态、不冲突；S3 无 `internal/*` 钩子、无猴补丁、不挂到别人的 ctx 上、不自行编排别的插件 |
| 1 活性 | 生命周期步终止，静止即稳定 | L1 启动程序有界；L2 inject/provide/spawn 无环 |
| 2 恢复 | 卸载后存储 ≃ 略去它全部操作的影子 | R1 启动期效应都登记在 fiber 上 (含中途抛错)；R2 运行期效应由子 fiber/`ctx.effect` 承载；R3 相遇受控 (登记名不与别的插件撞)；R4 区分应登记的临时资源与有意持久的外部状态 |
| 3 合流 | 干净终态在重命名意义下与调度无关，并等于静态组装 | C1 完整提供；C2 启动分支不依赖调度 (未注入服务在不在、分发结果、环境探测)；C3 所用服务的逆与状态无关；C4 不直接 dispose 启动时 spawn 的子 fiber；C5 启动期不读有序分发的结果 |

**判定**：✓ 满足；△ 需要标注、小重构或依赖一个约定；✗ 照现写法不满足。

- 一层算"可达"，要求该层与以下各层都没有 ✗。
- S1 中读未注入的服务一律记 △，前提是把它标成可选依赖，因为模型缺这个机制 (差异 m)，不全是插件的错。
- S3 有 ✗ 的记为**不在模型内**：这时连第 0 层的保证都不覆盖它。
- R3 是对整套安装的要求，不是单个插件的性质。表中的 ✗ 指已经找到与某个热门插件实际撞名。

## 结论

| 插件 | 版本 | 月下载 (万) | 安全 | 活性 | 恢复 | 合流 | 最高层 |
|---|---|---|---|---|---|---|---|
| dshmarket | 1.80.0 | 133 | ✗ | △ | ✗ | ✗ | 不在模型内 (编排者) |
| dsh-windows-mcp | 0.2.11 | 93 | ✗ | ✓ | ✗ | △ | 不在模型内 |
| dsh-pet | 0.4.9 | 59 | ✗ | △ | ✗ | ✗ | 宿主 1；客户端不在模型内 |
| dsh-context | 0.87.1 | 58 | ✗ | ✓ | △ | ✗ | 不在模型内 |
| dsh-whale-widget | 0.4.2 | 40 | △ | ✓ | ✗ | △ | 1 |
| dsh-agent-compare | 3.3.0 | 27 | △ | ✓ | △ | △ | 2 |
| dsh-ops | 0.5.5 | 26 | ✗ | △ | ✗ | ✗ | 不在模型内 |
| dsh-mobile-plugin | 0.5.97 | 26 | ✗ | △ | ✗ | ✗ | 不在模型内 (编排者) |
| dsh-remote | 1.3.1 | 24 | ✗ | ✓ | △ | ✗ | 不在模型内 |
| dsh-cost-meter | 1.9.85 | 18 | ✗ | ✓ | ✗ | ✗ | 不在模型内 |
| @michengai/dsh-skills-manager | 1.5.0 | 17 | △ | ✓ | ✗ | △ | 1 |
| dsh-free-search | 0.9.82 | 17 | ✗ | △ | ✗ | ✗ | 不在模型内 (编排者) |
| dsh-mnemon | 0.5.53 | 16 | ✗ | △ | △ | ✗ | 不在模型内 (编排者) |
| dsh-plugin-wallpaper-engine | 1.4.3 | 16 | △ | ✓ | △ | ✗ | 2 |
| dsh-connect-workbuddy | 5.31.0 | 15 | △ | ✓ | ✗ | ✗ | 1 |
| @xmanrui/dsh-im | 5.10.0 | 14 | △ | ✓ | △ | ✗ | 1 |
| @michengai/dsh-archive-manager | 1.4.1 | 14 | ✗ | ✓ | ✗ | ✗ | 不在模型内 |
| dsh-genui | 0.3.4 | 13 | ✓ | ✓ | △ | ✗ | 宿主 2；客户端 ≤ 1 |
| dsh-session-superagent | 0.10.12 | 10 | ✗ | ✓ | ✗ | ✗ | 不在模型内 |
| dsh-image-gen | 0.11.4 | 10 | △ | ✓ | ✗ | △ | 1 |
| ds-harness-remote | 0.6.7 | 10 | ✗ | △ | ✗ | ✗ | 不在模型内 |
| dsh-prime-memory | 0.26.72 | 10 | ✗ | △ | ✗ | ✗ | 不在模型内 |
| dsh-token-diet | 0.1.0 | 10 | △ | ✓ | △ | ✗ | 2 |
| @tencent-connect/dsh-qqbot | 0.5.5 | 10 | ✗ | △ | ✗ | ✗ | 不在模型内 |
| dsh-onebot-qq | 0.11.0 | 9 | △ | ✓ | △ | △ | 1 |
| deep-view | 0.1.2 | 9 | △ | ✓ | ✗ | ✗ | 2 (不与旧版 DS Bot 同装时) |

表中按宿主端打分。有客户端且客户端更差的，在"最高层"一列分开写。各列取该层检查项中最差的一项。

**分布**：

| 最高层 | 个数 | 插件 |
|---|---|---|
| 3 | 0 | — |
| 2 | 5 | agent-compare、wallpaper-engine、genui (宿主)、token-diet、deep-view |
| 1 | 7 | whale-widget、skills-manager、connect-workbuddy、dsh-im、image-gen、onebot-qq、pet (宿主) |
| 不在模型内 | 14 | 其余 |

下载量最高的 4 个都不在模型内或只到第 1 层。

### 1. 不在模型内的原因可以归成五类

一个插件常常同时占几类。

| 越界方式 | 插件 |
|---|---|
| 编排别的插件或自己：改 loader 条目、装卸插件、自更新、自我重启 | dshmarket、dsh-mobile-plugin、dsh-free-search、dsh-mnemon、ds-harness-remote、dsh-remote (自热重载)、dsh-ops 客户端 |
| 猴补丁服务实例或进程全局 | dsh-context (`tools.register`)、dsh-qqbot (`userQuestions.ask`，`uninstall()` 从未被调用 ✔)、dsh-archive-manager (`workspaceRegistry` 及其原型、webServer 内部路由表)、dsh-mobile-plugin (`webServer.register`)、dsh-cost-meter (`ChildProcess.prototype.spawn` ✔、`web` 服务的方法)、dsh-pet 客户端 (`commandUi.candidates`) |
| `internal/*` 元层钩子 | dshmarket (`internal/plugin` ✔)、dsh-ops (`internal/dispatch`)、dsh-context (`internal/get`)、dsh-prime-memory、dsh-remote、dsh-cost-meter (`internal/service`)、dsh-mnemon (`internal/config`) |
| 把效应挂到别人的 ctx 上 | dsh-ops (`agent.ctx.plugin`)、dsh-windows-mcp 与 dsh-remote (`tools.restrict`)、dsh-cost-meter 与 dsh-archive-manager (还原效应挂在被补丁插件的 ctx 上) |
| `globalThis` 上跨实例共享、新实例清理旧实例 | dsh-session-superagent (✔)、ds-harness-remote |

这些写法多数不是绕开 Cordis 的设计，而是越出了本模型的纪律：Cordis 允许 `ctx.get`、裸 disposer、模块级状态，dsh 自己也这样写。差距主要在"Cordis 允许什么"与"Cordis 保证什么"之间。真正绕开设计的是猴补丁、`internal/*` 钩子和 `globalThis` 跨实例这三类。

其中**编排者**占 6 到 7 个，比上一轮的估计多得多。插件市场、自更新、"装配一组子插件"的 bundle 是真实需求。它们需要的是编排者义务，即关于自己发出的 `O-Insert`/`O-Dispose` 的义务，而不是组件义务。

### 2. 第 2 层主要卡在两处

- **登记推迟或中途抛错泄漏**：
  - dsh-whale-widget 先收集路由的 disposer，最后才登记。
  - dsh-prime-memory 的 Worker/子进程要等 `apply` 末尾的统一 `ctx.effect` 才登记，中间有十余处 `await`。
  - dsh-archive-manager 第 2、3 条路由注册失败时吞错。
  - dsh-connect-workbuddy 在 promise 回调里往主 fiber 上挂效应。

  正确写法是"每做一件事立即登记它的逆"，这正是演算的 `L-Step` 压入撤销项的方式。
- **运行期资源不归任何 fiber**：
  - dsh-image-gen 的 OAuth 回调服务器。
  - dsh-skills-manager 在路由处理器里起的 git 子进程。
  - dsh-windows-mcp 丢弃了 6 个 `webServer.register` 的返回值。
  - dsh-im、dsh-onebot-qq 的按会话 runtime 和定时器都靠手工簿记。

  这些都应由 `O-React` 式的子 fiber 承载。

### 3. 第 3 层几乎都卡在 C2，根源同样是缺可选依赖

能到第 2 层的 5 个插件，有 4 个的第 3 层卡在 C2：

- dsh-token-diet：用哪种传输，取决于 `connection`、`sessionPersistence` 是否先于本插件激活。
- dsh-agent-compare：启动期 `recover()` 读写文件系统。
- dsh-plugin-wallpaper-engine：启动时跨 profile 做文件系统自检。
- deep-view：撞名时静默不登记。

另一个原因是 C3，即状态相关的逆。dsh-genui 写入的提示档位撤销时不恢复，dsh-context 也有同类情形。这正是 `Tiers.v` 中变量存储的情形：可撤销，但不可合流。

C2 的主体是"读未注入的服务，按它在不在决定登记什么"，与 S1 同源。插件作者这样写，是为了不在缺少该服务的宿主上停在 PENDING。模型若有可选依赖，并规定该依赖出现或消失时是否重载，这类插件多数能直接升到第 3 层。

### 4. 相遇受控在真实安装中已被违反

以下撞名都是在本轮的 26 个插件之间、或与宿主之间实际找到的：

- `dshRemote`：ds-harness-remote (`dist/index.js:113013` ✔) 与 dsh-remote (`lib/main.js:4657` ✔) 都 `ctx.provide`，两边都把冲突错误吞掉只打警告，谁拿到这个键取决于激活顺序。
- `approval/request` 中间件：dsh-im (`plugin-src/host/modern-harness-api.mjs:295` ✔) 与 dsh-qqbot 都以 `{ global: true, prepend: true }` 注册，谁先处理审批取决于激活顺序。
- 工具名：
  - deep-view 的 `show_view` 与旧版 DS Bot 撞名，且吞错。
  - dsh-onebot-qq 的 `ask_user_question` 与宿主工具撞名。
  - 通用名容易与同类插件冲突：dsh-prime-memory 的 `memory_*`、dsh-skills-manager 的 `create_skill`、dsh-free-search 的 `weather`/`research`。
- 其他登记名：dsh-free-search 的搜索 provider id `ddg`，撞名时复用别人的登记；dsh-connect-workbuddy 的 provider id `workbuddy` 不带前缀，dsh-cost-meter 又按这个名字隐式耦合计费。

这对应汇总定理里的 `Covers G`：注册表只在 G 关联不同名字时可撤销。插件侧的"相遇受控"读作**登记名带插件前缀**。冲突应在插入时拒绝 (差异 c 的建议)，而不是吞错后继续运行。

### 5. 与上一轮相比 (6 个插件)

- **dshmarket** 1.73.18 → 1.80.0：
  - 纠正上一轮：1.73.18 的路由其实已经经 `host.effect` 登记，缺口只在中途抛错和两个模块级 setter。
  - 补记上一轮漏掉的一处：`net.js` 清掉 undici 的 `globalDispatcher`。
  - 新增：经 `hmr.reconcileProfile()` 热替换自身；`llm`、`agentDefaultModel`、`hmr` 三个未注入读取；默认开启的匿名遥测心跳；一个新的 `globalThis` 槽。
- **dsh-windows-mcp** 0.2.8 → 0.2.11：
  - Computer Use 开关不再写 `state.json`，改为模块级的按会话 Map，跨插件重载存活。
  - 新增未注入读取 `sessions`。
  - 路由泄漏仍在 (`lib/index.js:1409-1414`)。
- **dsh-pet** 0.4.7 → 0.4.9：
  - 退步：新增 `setCityProvider`，并把 4 个内置语音实现写进模块级注册表，没有 disposer。
  - 客户端猴补丁 `commandUi.candidates` 在 0.4.7 就已存在，上一轮漏记。
- **dsh-context** 0.83.1 → 0.87.1：
  - 仍猴补丁 `tools.register`、监听 `internal/get`。
  - 新增：启动即自动回填 (可中止)、两条路由、两个可选读取。
  - 除此之外，路由、投影、提示段、worker、计时器都已挂到 fiber 上。
- **dsh-whale-widget** 0.4.2：发布包未变。补记它往宿主的 `webserver/index-inject` 表里 push 的一行没有逆。
- **dsh-ops** 0.5.4 → 0.5.5：
  - 改进：去掉了 `forceDefaultOpsPtc`，拆除不再恢复默认预设，所以拆除与下次启动之间的顺序依赖 (`settlePendingRestore`) 和状态相关的逆都消失了。
  - `internal/dispatch` 与 5 处 `agent.ctx.plugin` 仍在。

## 有潜力纳入模型的插件

下面按"要做什么才能进模型"分组，依据是各插件审计文件中的升级路径。

先说明一点：S1/C2 里的大部分"可选依赖"**现在的模型就能表达**。写成静态的 `ctx.inject([...], cb)` 子 fiber，就是一个依赖为 d 的 Spawn。服务不在时，子 fiber 停在 Inactive，target 为 ⊥，状态仍然稳定。只有当父 fiber 自己的行为按"服务在不在"分支时，才需要扩展模型。

### A. 只改插件就能进模型，并可到第 3 层 (8 个)

| 插件 | 现在 | 要改的地方 |
|---|---|---|
| deep-view | 2 | 工具名加前缀，去掉 `tools.register` 外的吞错 |
| dsh-agent-compare | 2 | 未注入读取改为 `ctx.inject` 子 fiber；`recover()` 移进 `ctx.effect` |
| dsh-plugin-wallpaper-engine | 2 | 跨 profile 的自检移出 `apply`，或只告警不抛错 |
| dsh-token-diet | 2 | 按服务分出 `ctx.inject` 子 fiber，在各自的子 ctx 上登记 |
| dsh-genui (宿主) | 2 | 登记一个固定名字的提示段，按当前档位惰性求值 |
| dsh-session-superagent | 不在模型内 | 去掉 `globalThis` 共享表；每个 watcher 做成子 fiber；路由撞名直接报错 |
| dsh-remote | 不在模型内 | 自更新只落盘提示；`internal/service` 改为 inject；`dshRemote` 改名；未注入读取改为子 fiber。agent 级 `restrict` 需要 B 类的交集生命期，或标为已知例外 |
| @michengai/dsh-archive-manager | 不在模型内 | 不再覆盖 `workspaceRegistry`，改为自己 provide 一个服务；路由逐条 `ctx.effect` 登记；去掉吞错分支 |

### B. 只改插件可到第 2 层；第 3 层要么需要模型扩展，要么受限于外部环境 (10 个)

| 插件 | 现在 | 到第 2 层要改的地方 | 第 3 层卡在 |
|---|---|---|---|
| dsh-whale-widget | 1 | 路由逐条登记；去掉模块级 `dns` 设置 | 定时器分支依赖配置文件 (外部世界) |
| dsh-image-gen | 1 | OAuth 回调服务器登记到 fiber；嵌套 inject 挂对 ctx；工具名加前缀 | `installSection` 的逆是否与状态无关，未确认 |
| dsh-connect-workbuddy | 1 | 登记移进子 fiber，不再在 promise 回调里挂效应；provider id 加前缀 | 目录刷新依赖网络 (外部世界) |
| dsh-onebot-qq | 1 | 会话 agent 与定时器用 `ctx.effect`；ask 工具改名 | 设置条目改写 loader 条目 (编排者) |
| @xmanrui/dsh-im | 1 | 每个通道或 bot 做成子 fiber；中间件去掉 `prepend` 或约定唯一拦截者 | 自更新 (编排者)；父 fiber `await` 子 fiber 的结果 |
| @michengai/dsh-skills-manager | 1 | git 子进程接 fiber 的 AbortSignal | 在每个 agent 的 ctx 上登记 provider (交集生命期) |
| dsh-pet (宿主) | 1 | 语音和城市 provider 用 `ctx.effect` 登记；Helper 启动移进效应 | Helper 依赖环境与端口时机 (外部世界)。客户端要等宿主提供命令面孔入口，才能去掉猴补丁 |
| @tencent-connect/dsh-qqbot | 不在模型内 | 删掉 `userQuestions.ask` 补丁，改挂 `user-questions/request` 中间件 (onebot-qq 就是这么做的)；会话 agent 用 `ctx.effect` 承载 | 凭据写入 `cordis.patch.yml` (编排者)；`approval/request` 用了 `prepend` |
| dsh-prime-memory | 不在模型内 | 删掉 `internal/service`，改为 inject；collector 经服务读取；每建一个资源立即登记其释放 | 数据目录 (外部世界) |
| dsh-context | 不在模型内 | 去掉对 `tools.register` 的替换和 `internal/get` 监听，需要宿主提供"工具所有者"查询，否则放弃归因功能 | 版本探测分支 (外部世界) |

### C. 必须等模型扩展或宿主提供新原语 (8 个)

| 插件 | 需要的扩展 | 扩展后可达 |
|---|---|---|
| dsh-ops | 交集生命期 (`agent.ctx.plugin`)；宿主提供 `tools/change` 事件以替代 `internal/dispatch` | 2 |
| dsh-windows-mcp | 交集生命期 (对 agent 的 `restrict`)；另需修路由登记 | 2 |
| dshmarket | 编排者义务：拆出市场浏览组件 (可到 2)，装卸、禁用、HMR 收进编排者模块 | 组件部分 2 |
| dsh-mnemon | 编排者义务 (bundle、starter)；交集生命期 (per-agent 效应) | 本体 2 |
| dsh-mobile-plugin | 编排者义务；还需宿主提供路由分发与换代机制，以取代对 `webServer.register` 的猴补丁 | 代 (`impl.js`) 1 到 2 |
| dsh-free-search | 编排者义务 (改写 `web` 条目、自升级)；provider id 与工具名加前缀 | 2，对固定环境可到 3 |
| ds-harness-remote | 编排者义务 (禁用旧条目、自更新)；`dshRemote` 改名 | 2 (换服务器要 dispose 子 fiber，违反 C4) |
| dsh-cost-meter | 计量拆成宿主扩展；宿主提供 `web` 的计费事件，取代方法替换 | 2 |

### 汇总

- 只改插件、不动模型，就有 8 个能到第 3 层，10 个能到第 2 层。
- 剩下 8 个要等三项扩展：编排者义务、交集生命期、外部持久世界 (对固定环境合流)，有几个还需要宿主新增原语。
- B 类第 3 层的障碍大多是"外部世界"。这一项若作为"对固定环境合流"写进模型，B 类有一半左右可以再升一层。

真正没有前景的只有各插件中少数几项功能本身：dsh-genui 客户端的自定义元素、dsh-context 的归因、dsh-cost-meter 的子进程计量。它们要么由宿主接管，要么标为"保证不覆盖"。

## 按已形式化的扩展重新分层

三项扩展已经在 Rocq 中证明 (`theories/Ext/`，汇总在 `Ext/ExtSummary.v`，说明见 [EXTENSIONS.md](EXTENSIONS.md) 4.3 节)。本节按扩展汇总定理逐个插件重看：哪项扩展适用，要满足什么前提，在上一节的升级路径都做完之后能到哪一层。依据是各插件审计文件的逐条证据，另行逐一抽取核对过。

### 三项扩展各自要求什么

| 扩展 | 插件要做的 | 运行时或宿主要提供的 | 换来的层 |
|---|---|---|---|
| 可选依赖 (`xsum_*`) | 把"按服务在不在分支"的启动写成按在场集选变体；每个变体都完整提供 (`XTotal`)；秩沿可选依赖边也递增 | 声明式可选依赖，并在依赖出现或消失时重载 fiber。Cordis 现在没有，这是对它的建议 (差异 m) | 0–3。第 3 层要求子组件 (被 spawn 的、处理器) 不声明可选依赖 |
| 编排者 (`orch_*`、`osum_confluence`) | 只经 loader 条目编排 (写条目，由 loader 协调)；输入有限；存活组件只由配置决定 (O3)；不在自己的启动程序里自我重启 | loader 的条目接口 (已有)；包的安装与下载属于外部世界，不在模型内 | 0–3。第 3 层只要求存活组件相同，顺序可以不同 |
| 交集生命期 (`isum_*`) | 挂在 agent 上的效应写成插件的反应子 fiber，依赖该 agent 的条目键 | 每个 agent 的上下文暴露成一个键 ("条目即键")；`agent/created` 这类事件带上 agent id，能按载荷运行处理器 | 0–2，另有包含性质：效应在插件与 agent 两者的生命期之内，agent 卸载被守卫停住直到效应撤销。合流与核心一样不含运行期反应 |

几个判别要点：

- **可选依赖只解决"时机"**。分支若取决于文件、网络、环境变量、端口就绪时刻，重载帮不上，仍记为外部世界。
- **编排是否在模型内，看走哪条路**。经 loader 条目 (`entry.update`、`configEditor.edit`、写 `cordis.patch.yml` 后由 loader 协调)，或经宿主的 `pluginManager.installBundle`/`updateBundle`、`hmr.reconcileProfile()`，在模型内。后两者先装包 (外部世界)，再由 loader 按 profile 补丁重组条目：停止、替换、启动 (`packages/boot/hmr/src/index.ts:930`)。下列做法在模型外：`internal/*` 钩子、给自己进程发 SIGTERM、清模块缓存热替换自己、直接 dispose 启动时 spawn 的子 fiber。
- **"自更新"拆成两半**。下载新版本属于外部世界；让新版本生效应当是 loader 对条目的重启 (`IRestart`) 或替换 (`IDis` 加 `IIns`)。
- **由插件自己创建的 agent 不算交集生命期**。dsh-agent-compare、dsh-onebot-qq、dsh-qqbot 的 agent 都是插件自己建的，效应的生命期就是插件的，核心的子 fiber 已经够用。

### 逐个插件

"上一节"指"有潜力纳入模型的插件"给出的可达层。"现在"指在上一节的升级路径之外再用上表中的扩展，能到的层。带"启动部分"的第 3 层指：合流对不含运行期反应的执行成立，与核心相同。

| 插件 | 用到的扩展 | 前提与剩余障碍 | 上一节 | 现在 |
|---|---|---|---|---|
| dsh-token-diet | 可选依赖 | 有 `connection` 走 RPC、否则走 webServer 路由，两者互斥 (rpc.js:256-272)；`sessionPersistence` 晚到时索引不扫描 (index-store.js:212)。拆成两个 inject 子 fiber 会在两者都在时都登记，改变行为；可选依赖正好表达这个二选一，并在 `connection` 晚到时重载 | 3 | 3，且不改行为 |
| dsh-agent-compare | 可选依赖 | runner 在 `apply` 里选一次 (lib/host/index.js:352-361)，是按 `agents`/`subagents` 在不在的启动分支，用可选依赖：先有 `subagents` 后来才有 `agents` 时，重载换成隔离的 runner。两者都不在时现在抛错；失败的 fiber 不会因依赖出现而重载，所以要改成什么也不登记的变体，否则结果仍取决于时机 | 3 | 3，前提是两者都不在时不抛错 |
| dsh-remote | 三项都用到 | `/remote` 命令只在 `commands` 在时登记 (main.js:3494)，用可选依赖；对每个 agent 的 `tools.restrict` (3337-3375) 用交集生命期；`reloadSelf` 清模块缓存、直接 dispose 再 init (update.js:642-682) 必须改为经 loader 重启条目 | 3，restrict 记为例外 | 第 3 层只覆盖启动部分；restrict 在第 0–2 层之内 |
| @michengai/dsh-skills-manager | 交集生命期、可选依赖 | 每个 agent 上的 `registerProvider` (233-269) 改为依赖 agent 条目键的反应子 fiber；启动时按 `agents` 在不在补挂 (255-258)，用可选依赖；git 子进程接 fiber 的 AbortSignal | 2，第 3 层卡在交集生命期 | 2，第 3 层只覆盖启动部分 |
| dsh-onebot-qq | 编排者 | 设置 Remote 用 `configEditor.edit` 改写自己的条目并请求重启 (settings-remote.js:500-535)，经 loader 条目、由用户触发，满足 O1–O3；仍需会话 agent 与定时器改用 `ctx.effect`、ask 工具改名 | 2，第 3 层卡在编排者 | **3** |
| @tencent-connect/dsh-qqbot | 编排者、可选依赖 | 写 `cordis.patch.yml` 由 loader 热重载 (setup/persist.js:23-70)，经 loader 条目；`tools`/`llm`/`attachments`/`userQuestions` 不在时跳过对应功能 (send-file-tool.js:31-35 等)，用可选依赖；解绑时 `delete process.env.QQBOT_*`、凭据来自配置与环境变量，属外部世界；`approval/request` 的 `prepend` 与 dsh-im 冲突 (相遇受控) | 2，第 3 层卡在编排者与 prepend | 对固定环境 3，前提是约定唯一的审批拦截者 |
| @xmanrui/dsh-im | 编排者 | `update.install` 用 pnpm 子进程装新版本 (update-runtime.mjs:236-239)，改为"下载 (外部世界) 加经 loader 重启条目"；按 `connection.fetch` 在不在的分支 (index.mjs:216) 检查的是必需依赖 `connection` (35-39) 的接口形状，不是存在性，不需要可选依赖；父 fiber `await` 子 fiber 的结果 (index.mjs:165-168) 仍须去掉；各通道按本地文件尽力启动 (index.mjs:246-259)，属外部世界 | 2，第 3 层卡在编排者 | 对固定环境 3，前提是去掉对子 fiber 的 `await` |
| dshmarket | 编排者、可选依赖 | 在模型内的：`entry.update({disabled})` (themes.js:188、hot.js:953)。热挂载其他插件 `ctx.plugin(HotTree)` (hot.js:1111) 在处理器中进行，即反应子 fiber，也在第 0–2 层之内。按 `desktopProfiles`/`profileContext` 选三条启动分支 (index.js:250，注释承认 `profileContext` 可能晚到) 用可选依赖。自更新经宿主的 `hmr.reconcileProfile()` 换成磁盘上的新版本 (self-reload.js:158-183)，由 loader 停止并重建自己的条目，也在模型内。须去掉的：`internal/plugin` 钩子 (routes.js:937)、给自己进程发 SIGTERM (restart.js:686)、pnpm/dsh 子进程装卸 (改为宿主的 `pluginManager.installBundle`)、启动 8 秒后的自动重装 | 组件部分 2 | **整体 2** |
| dsh-mnemon | 编排者、交集生命期 | bundle 经 loader 的 `group` 与 `group.update(entries)` (bundle.js:69-77)，运行时 `entry.update` (19431,19481)，都在模型内；`entry.parent.unlink(sibling)` (bundle.js:57) 只把已禁用的重复策略行从父组的配置数组移到自己的组 (`EntryGroup.unlink` 只删数组项，不 dispose fiber；loader 自己的 `tree.update(id, …, parent)` 也这样移动条目)，不涉及运行中的 fiber，在模型内，但应改用公开的 `update` 接口；每个 agent 上的钩子与效应 (9437-14711) 用交集生命期；须去掉 `internal/config` 钩子 (7915) 与 dsh CLI 子进程安装 | 本体 2 | **整体 2** (含 bundle 与 starter) |
| dsh-free-search | 编排者 | `settings.mutate("web")` 经 loader 条目 (2554-2631)，但必须只在值不同时写，否则 loader 重建 `web` 后再次触发，违反"输入有限" (即审计中的 L1 循环)；`web.searchProviderId = id` (2516) 是改别人的服务实例，须去掉；pnpm 自升级 (803) 改为下载加 loader 重启 | 2，固定环境可到 3 | 2，固定环境可到 3；编排部分已在模型内 |
| ds-harness-remote | 编排者、可选依赖 | `disableLegacyLoaderEntries` 经 loader 条目 (113193-113201)；自更新 `pluginManager.updateBundle(self)` (112266) 经宿主重组 profile，也在模型内；按 `connection`/`subprocess`/`schedule`/`webApp` 分支用可选依赖。但 `dshRemoteClient` 只在有 `connection` 时 provide (112870-112898)，违反"每个变体完整提供" (`XTotal`)，要改为无条件 provide 或放进 inject 子 fiber；换服务器时 dispose 启动期效应 (112804) 仍违反 C4 | 2 | 2 |
| dsh-ops | 交集生命期 | 五处 `agent.ctx.plugin` 与每个 agent 的 `tools.restrict` 改为依赖 agent 条目键的反应子 fiber；仍需宿主提供 `tools/change` 事件取代 `internal/dispatch`。客户端的 `installBundle('dsh-win-pwsh7')` 经宿主重组 profile，在模型内 | 2 | 2，扩展部分已证 |
| dsh-windows-mcp | 交集生命期 | 每个 agent 的 `restrict` (515-524) 现在只在 `agent/disposed` 时释放，插件卸载时泄漏 (566)；改为反应子 fiber 后两个方向都撤销。deny 集合随当时的工具集变 (459-485)，是状态相关的逆，但合流本来就不覆盖反应。另需修 6 处丢弃的路由 disposer。安装器直接改写 `cordis.patch.yml` (dependency.js:617-675) 是配置改动，由 loader 在下次启动 (或下次 `reconcileProfile`) 执行，在模型内；但它绕过 plugin-manager 的文件锁 | 2 | 2，扩展部分已证 |
| dsh-mobile-plugin | 可选依赖 (只到第 2 层) | 唯一真正依赖时机的分支在被 spawn 的"代"里 (impl.js:254-268)，子组件不能声明可选依赖，第 3 层要改成静态 inject 子 fiber；外壳换代时 dispose 自己 spawn 的子 fiber (runtime.js:304,453,465,605) 仍违反 C4；仍需宿主的路由分发原语取代对 `webServer.register` 的猴补丁。手机端触发的 `installBundle`/`updateBundle` 经宿主重组 profile，在模型内 | 1 到 2 | 1 到 2，不变 |
| dsh-prime-memory | 可选依赖 | `settings` 挂载取决于它此刻在不在、是哪一代接口 (settings.js:199-247)，可选依赖的重载正好取代现在靠 `internal/service` 补救的做法；数据目录仍属外部世界 | 2 | 2，但不再需要 `internal/service` |
| dsh-image-gen | 可选依赖 (客户端) | 客户端按 `configForms` 在不在选设置作用域 (client.js:132092-132094)，用可选依赖或两个静态 inject 子 fiber；宿主不需要 | 2 | 2 |
| dsh-whale-widget、dsh-plugin-wallpaper-engine | 可选依赖 (可选) | 为了不在旧宿主上停在 PENDING 而软读 (`deepseekAccount`、客户端的 `locale`/`theme` 等)，声明成可选依赖即可让 S1 成为 ✓；第 3 层的障碍 (配置文件、跨 profile 自检) 属外部世界 | 2 / 3 | 不变 |
| dsh-context、dsh-cost-meter、@michengai/dsh-archive-manager、dsh-session-superagent、dsh-pet、dsh-genui、deep-view、dsh-connect-workbuddy | 无 | 障碍是猴补丁、`globalThis`、`internal/*`、泄漏、撞名或外部世界，三项扩展都不涉及。dsh-cost-meter 把还原效应挂在被补丁插件的 ctx 上 (native-search-billing.js:435-443)，形状像交集生命期，但前提是猴补丁，不适用；dsh-connect-workbuddy 运行时用 `settings.mutate` 写回自己的条目，属经 loader 条目的编排，但它第 3 层的障碍是网络与端口时机 | 同上一节 | 不变 |

### 汇总

与上一节比，三项扩展形式化之后：

- **第 3 层多了 3 个**：dsh-onebot-qq 无条件；dsh-qqbot 要先约定唯一的审批拦截者，dsh-im 要先去掉对子 fiber 的 `await`，两者都只对固定环境 (凭据、本地文件) 合流。它们原来都卡在"编排者"，而它们的编排都经 loader 条目，正是编排者扩展覆盖的形状。
- **原 C 类里有 6 个现在可到第 2 层，扩展部分都已证明**：
  - dshmarket、dsh-mnemon、dsh-free-search、ds-harness-remote 靠编排者扩展，前两者从"组件部分""本体"扩大到整个插件；
  - dsh-ops、dsh-windows-mcp 靠交集生命期，dsh-ops 仍需宿主的 `tools/change` 事件。
- **可选依赖**让 dsh-token-diet 不必改行为就到第 3 层，让 dsh-prime-memory 不再需要 `internal/service`。它对多数插件的作用是把"为兼容旧宿主而软读"变成正式声明。
- **仍要宿主提供新原语的**：dsh-mobile-plugin (路由分发与换代)、dsh-cost-meter (计费事件)、dsh-ops (`tools/change`)、dsh-context (工具所有者查询)。交集生命期另需宿主把 agent 上下文暴露成键、事件带上 agent id。
- **还没有形式化的**：外部持久世界 ("对固定环境合流")。B 类大部分第 3 层的障碍仍是它。

### 复核

审计文件里有五处没写清。下面按插件发布包与宿主源码 (deepseek-harness) 逐一复核过：

- **dsh-agent-compare 的 runner 何时选**：在 `apply` 里选一次 (lib/host/index.js:352-361)，是启动分支，需要可选依赖。两者都不在时抛错的写法要改，见上表。
- **`pluginManager.installBundle`/`updateBundle` 写不写 loader 条目**：先用 pnpm 装包，再调 `reload()`。有 HMR 时即 `hmr.reconcileProfile()`：重读 profile 的补丁、由 loader 重组条目 (`packages/boot/plugin-manager/src/index.ts:872`、`:1247`；`packages/boot/hmr/src/index.ts:930`)。没有 HMR 时改动留到下次启动。所以它是"外部世界的下载加经 loader 的编排"，在模型内。这同时改变了一处判断：dshmarket 的自更新 `reloadSelf` 只请宿主 `hmr.reconcileProfile()` (self-reload.js:158-183)，自己不写文件，也在模型内。dsh-remote 的 `reloadSelf` 自己清模块缓存、直接 dispose 再 init，仍在模型外。
- **dsh-mnemon 的 `entry.parent.unlink`**：`EntryGroup.unlink` 只从父组的配置数组删掉这一项 (`vendor/loader/src/config/group.ts:31`)，loader 移动条目时也这样用 (`tree.ts:155`)。mnemon 只对 `disabled: true` 的重复策略行这样做 (bundle.js:15-24、57)，把它们移进自己的组，不涉及运行中的 fiber，算配置层面的条目移动。
- **dsh-windows-mcp 改写 `cordis.patch.yml`**：`writeBridgeOverride` (dependency.js:617-675) 改的正是 loader 组合条目所读的补丁文件，返回 `restartRequired`，不触发重组，由下次启动或下次 `reconcileProfile` 执行。算经 loader 的配置编排；但它直接 `writeFileSync`，绕过了 plugin-manager 的文件锁 (`withFileLock`)，与同时进行的 profile 改动可能互相覆盖。
- **dsh-im 的 `connection.fetch`**：`connection` 是必需依赖 (plugin-src/host/index.mjs:35-39)，`ctx?.connection?.fetch` (216) 检查的是接口形状，不是存在性；`tools`/`systemPrompt` 的登记已在静态 inject 子 fiber 里 (199-207)。都不需要可选依赖。

复核后各插件的可达层不变，只有 dsh-agent-compare 的第 3 层多了一个前提 (两者都不在时不抛错)。dshmarket、ds-harness-remote、dsh-mobile-plugin、dsh-ops 各有一部分编排从"模型外"改判为"模型内"，但它们的可达层由其他障碍决定。

## 对形式化的影响

1. **汇总定理的分层与实际情况吻合**。
   - 安全和活性的义务 (有界、有秩) 几乎所有插件都满足：活性一列没有 ✗，只有几处 △ (启动后的轮询应建模为反应)。
   - 差距集中在恢复与合流，又集中在少数几种可以机械检查的写法上。
   - 逐个插件的精化证明现在仍然证不出东西；检查器的首要用途是找 bug，并告诉作者差哪一层。
2. **模型要补的东西**，按影响的插件数排序 (前三项已在 `theories/Ext/` 中形式化，见上一节与 [EXTENSIONS.md](EXTENSIONS.md))：
   - **可选依赖**：同时影响 S1 与 C2，涉及过半插件。必须规定依赖出现或消失时是否重载，否则合流取决于时机。
   - **编排者义务**：6 到 7 个插件本质上是编排者。
   - **交集生命期的效应**：挂在另一个 fiber 上，任一方结束即撤销。
   - **外部持久世界**：配置、凭据、缓存、日志不属于上下文，恢复精确性只对上下文陈述。
3. **相遇受控应当可以静态检查**：登记名多为字面量，可以从发布包中抽出所有工具名、provider id、provide 键，做跨插件的冲突检查。

## 对 dsh 与 Cordis 的建议

- 让 `webServer.register` 等登记接口像 `tools.register` 一样自动挂到调用者的 fiber 上，消除"延后登记"和"丢弃 disposer"两类泄漏。
- 提供正式的可选依赖，并对读取未注入的服务给出警告 (差异 m)。
- 键冲突、工具名冲突在插入时拒绝；文档约定登记名带插件前缀。
- 给"挂在另一个 fiber 上的效应"一个原语，取代私有 Map 手工回收；给编排者一组受控原语 (安装、启停、自更新)，取代改 loader 条目、`internal/*` 钩子和自我 SIGTERM。
- 插件市场上架时跑一遍按层的 lint，把"最高层"作为插件的一个标签展示。
