# dsh-whale-widget 0.4.2

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主 `lib/index.js` 默认导出 `{ name: 'whale-balance-widget', apply }` (`:723` ✔)，有意不写对象级 `inject` (`:725` 注释)；`apply` 先在 root 上监听 `webserver/index-inject` (`:735`)，再开一个静态 `root.inject(['webServer','credentials','connection'])` (`:749` ✔)，内部登记约 30 个路由与一个 `tapIndex`。无 provide。客户端 `assets/whale-widget.js` 是不经 Cordis 的浏览器脚本，经 `tapIndex` (`:4903`) 或桌面端内联注入行加载，不在模型内。
- 一句话功能：DSH Web 右下角的 DeepSeek 余额/用量小鲸鱼挂件，带自定义角色、音效、泡泡和多厂商余额查询。

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 两处有意的可选读取：`sessionTitle` (`lib/index.js:1007`)、`deepseekAccount` (`:1189` ✔，注释说明不能进 inject，否则老宿主上永远 PENDING)。`connection` 已注入。可改为可选依赖。 |
| 0 | S2 | ✓ | 无 provide。 |
| 0 | S3 | △ | 无 `internal/*`、无猴补丁、不挂别人的 ctx。但向宿主的 `webserver/index-inject` 表直接 `push` 一行 (`:735-746`)：表由宿主启动时一次性收集、无刷新路径，插件卸载后该行仍在 (注释自述，改成"路由不在就静默失败"来兜底)。这是借宿主共享可变对象登记的条目，逆不登记。 |
| 1 | L1 | ✓ | `apply` 同步有界；启动期重试至多一次 (`:1301`、`:1329`)；5 分钟 `setInterval` 只在配置了 Codex 时挂上 (`:2124`)，属 Active 期间的反应。 |
| 1 | L2 | ✓ | inject 的三个服务均由宿主提供；无 provide/spawn。 |
| 2 | R1 | ✗ | 26 处路由与 `tapIndex`、计时器的 disposer 先收集到局部数组 `disposers` (`:895`)，直到回调末尾才由一个 `ctx.effect` 登记 (`:4919` ✔)：中途抛错 (例如重复路由触发 `webServer.register` 的 duplicate 异常) 会泄漏此前已登记的全部路由。`ctx.on` 本身由 Cordis 收集 ✓。index-inject 行无逆 (见 S3)。 |
| 2 | R2 | △ | 路由处理器里的效应：`exec('npm view …')` 子进程 (`:3911`，有超时)、`credentials.set` (`:2946`)、大量文件写入；Codex 预热计时器由处理器重挂 (`codexInvalidate` → `codexRearmPrewarm`，`:2027`)，但统一由同一个 disposer 摘除 (`:2134`) ✓。子进程不挂 fiber，只靠超时。 |
| 2 | R3 | ✓ | 路由路径都在 `/dsh-whale/` 前缀下；index-inject 只对自己旧版本的行去重 (`:738-743`)，不依赖其他插件的条目。 |
| 2 | R4 | △ | 持久状态：`$DSH_HOME/.dshw-*` 配置、账本、用量归档、角色/音频/泡泡图片目录、`.dshw-codex.json` (`:1777`)、宿主凭据 `credentials.set` (`:2946`)——保证不覆盖。进程级全局改动：模块加载时 `dns.setDefaultResultOrder('ipv4first')` (`:16` ✔)，影响整个宿主进程，卸载不恢复。临时资源泄漏：R1 所述的中途抛错路径；index-inject 行。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | △ | 启动是否挂 Codex 定时器取决于读配置文件 (`codexRearmPrewarm(false)`，`:2133`)，属"对固定环境合流"。登记的路由集合固定 (26 处 `disposers.push(registerRoute(…))` 都无条件)。 |
| 3 | C3 | △ | 路由、监听按名字登记，逆与状态无关 ✓；但运行期 `credentials.set` 与文件写入是状态相关且不撤销的 (列为持久)。index-inject 行的"逆"不存在。 |
| 3 | C4 | ✓ | 未直接 dispose 子 fiber。 |
| 3 | C5 | ✓ | 启动期不 emit、不读分发结果；`webserver/index-inject` 监听器只在宿主分发时追加一行。 |

**最高层**：1。安全层只有可选读取与 index-inject 行两处 △，活性满足；恢复层被 R1 (disposer 延后登记) 与模块级 `dns` 全局改动挡住。
**升级路径**：(1) `registerRoute` 内部直接 `ctx.effect(() => ctx.webServer.register(wrapped))` 或每次注册后立即 `ctx.on('dispose', d)`，修 R1；(2) 去掉模块级 `dns.setDefaultResultOrder`，改为对需要的请求传 `family: 4`/自建 agent；(3) `deepseekAccount`/`sessionTitle` 改为可选依赖。做完 (1)(2) 可到第 2 层 (持久文件与凭据记为保证不覆盖；index-inject 行需宿主提供可撤销的登记接口)。第 3 层还需要 Codex 定时器的启动分支不依赖配置文件，或接受"对固定环境合流"。
**与上一轮审计的差异**：版本未变 (0.4.2)，发布包与上一轮逐文件相同 (`diff -rq` 无差异)。结论一致；本轮补充一点：上一轮未提的 `webserver/index-inject` 行 (`:735`) 是直接改宿主共享表、无逆的登记，卸载后仍留在桌面端注入表里。
