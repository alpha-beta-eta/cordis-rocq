# dsh-plugin-wallpaper-engine 1.4.3

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主 `lib/index.js` (未打包，多文件)，`inject = ['webServer']`(`lib/index.js:175` ✔)，provide `wallpaperEngineHost`(`lib/index.js:200` → `lib/subpackage-boot.js:680` ✔)。`cordis.patch.yml` 一次插入 9 行：主包 1 行 + 8 行子包/组件 (`…-about-notice`、`…-mascot-avatar`、`…-media-bridge`、`…-pet-link`、`…-fx`、`…-parallax`、`…-fonts`、`…-glass`)，子包本身不在本发布包内，它们 `inject: ['wallpaperEngineHost']` 并经服务回调主包的 `applyComponent`(`lib/index.js:468`)。本审计只覆盖主包。客户端 `lib/client.js` (2MB，`window.__ModuleLoader__` 格式)，`inject = ["slots"]`(`lib/client.js:29927` ✔)，`dsh.client.immediately: true`。
- 一句话功能：扫描本机 Wallpaper Engine 库，通过宿主 HTTP 路由下发媒体/清单，在 DSH Web GUI 背后渲染 Scene/Video/Web 壁纸，附带液态玻璃外观、字体、预设等设置。

宿主端 (主包)：

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | 未注入读取 `ctx.loader`：枚举 loader 条目判断 `dsh-better-sidebar` 是否启用 (`lib/shim-seed.js:128-141` ✔，经 `GET /settings` 调用，`lib/routes/settings.js:190`)，是元层只读访问，有意为之，可改为对侧栏服务的可选依赖。`ctx.logger` 外无其他 `ctx.get`。 |
| 0 | S2 | ✓ | `HOST_SERVICE_NAME = 'wallpaperEngineHost'` 字面量 (`lib/subpackage-boot.js:629` ✔)，名字专属。真宿主上总走 `ctx.provide`，只在无 `provide` 的测试夹具上退化为挂属性 (`:678-685` ✔)。 |
| 0 | S3 | △ | 无 `internal/*`、不改 loader。但：(1) 宿主内核 `hostKernel` 是模块级单例 (`lib/host-boot.js:40` ✔)，多行共享，靠模块级 `WeakMap` 引用计数租约决定何时 dispose (`lib/kernel/host-kernel.js:141-162` ✔)——跨 fiber 的模块级状态；(2) `tolerantWebServer` 用 Proxy 包住 `webServer`，吞掉本命名空间内的"duplicate route"错误 (`lib/host-boot.js:231-293` ✔)，是本地包装不是猴补丁，但它的存在说明旧版卸载漏登记的路由会跨重载残留；(3) 子包经服务拿到主包 per-apply 实例面 (`applyView`)，各行共享同一 `mediaMap`。不是编排者。 |
| 1 | L1 | ✓ | 启动同步；循环只遍历 patch 行与 `~/.dsh/profiles` 下的目录 (`lib/subpackage-boot.js:503-530`)，有限。缓存清扫推迟为一次性 3s `setTimeout`，disposer 已登记 (`lib/startup-sweep.js:46`、`lib/kernel/host-session.js:193` ✔)。 |
| 1 | L2 | ✓ | 只 inject `webServer`；provide 的 `wallpaperEngineHost` 由兄弟行 inject，不是自己的后代，无环。 |
| 2 | R1 | ✓ | 所有路由的 `webServer.register` 裸 disposer 推进会话的 `disposers` 数组 (例 `lib/routes/diag.js:149-150` ✔)，整体 teardown 在任何路由注册之前经 `handOffTeardown` 交给 `ctx.effect`(`lib/index.js:273` ✔、`lib/host-boot.js:201-209` ✔)，所以中途抛错已注册部分也会回滚；`createHostSession` 装配失败时退还内核租约 (`lib/kernel/host-session.js:101-108` ✔)。小缺口：装配中途失败时已建的 3s 清扫计时器不会清除 (未确认 `createMediaOrigin` 能否抛错)。 |
| 2 | R2 | △ | 运行期资源：按需起的媒体源 HTTP 服务器 (`lib/media-origin.js:140-184`，close 推进 disposers ✔)、在途流 (`activeStreams`，teardown 逐个 destroy)、ffmpeg 子进程 (可能 `detached: true`，`lib/media/transcode.js:324`，由模块级 `transcodeKit.dispose()` 在租约归零时杀)。都可回收，但集中在会话/内核对象里，不是子 fiber，不能单独撤销。 |
| 2 | R3 | △ | 路由大多在 `/wallpaper-engine` 前缀下 (`lib/host-boot.js:34`)，但注册了根路径 `/diag`(`lib/routes/diag.js:149` ✔)，子包另注册 `/api/local-assets`，都可能与其他插件撞名。Proxy 对命名空间内重复路由"跳过并告警"，撞名时静默保留先到者。`isBetterSidebarLoaded` 依赖别的插件的 loader 条目。 |
| 2 | R4 | △ | 持久 (保证不覆盖)：`~/.dsh-wallpaper-engine/config.json` 设置、字体集、玻璃预设、上传、转码/faststart/预览缓存、诊断日志；每次启动写 `build-stamp.json`(`lib/kernel/host-session.js:139-146` ✔)。临时资源泄漏：模块级内核跨热重载存活 (租约设计正是为此)。未见改 `process.env` 等进程级全局 (只读 env)。 |
| 3 | C1 | △ | 成功路径都先 provide (`lib/index.js:200`)；但 provide 之后启动仍可能抛错 (见 C2)，"无失败"不满足。 |
| 3 | C2 | ✗ | 启动根据文件系统探测决定成败：解析每个 patch 子包行 (`lib/index.js:217` ✔)，并扫描 `~/.dsh/profiles` 下**所有**装了本包的 profile，在其中任一解析不到就抛 (`lib/subpackage-boot.js:588-615` ✔)；受 `DSH_WE_SKIP_HOST_CHECK`、`DSH_PROFILE_DIR` 环境变量控制。属于"对固定环境合流"，但会受其他 profile 的安装状态影响。 |
| 3 | C3 | ✓ | 路由按路径登记；设置写入是持久状态，不作为逆。 |
| 3 | C4 | ✓ | 不 spawn 子 fiber。 |
| 3 | C5 | ✓ | 宿主不调用 emit/waterfall/bail。 |

客户端：

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | △ | inject 只有 `slots`，但轮询 `ctx.get` 读 `locale`(`lib/client.js:1657` ✔)、`theme`(`:8678` ✔)、`shortcuts`(`:4985`)、`sidebarRightTabs`/`sidebarRight`(`:4922-4923` ✔)；注释明说是避免低版本宿主卡在 PENDING 的可选依赖。 |
| 0 | S3 | △ | 同一 bundle 里定义多个模块，与子包客户端经模块级登记表 (`weSetLayerAttacher`、`glassStatusRegister` 等) 交换函数；与其他皮肤插件通过 `data-dsh-skin` DOM 属性协调让位 (`installSkinInterop`，`lib/client.js:24958` ✔)——模型外的相遇通道。 |
| 2 | R1 | ✓ | DOM 层、监听器、React 根都在 `ctx.effect` 内并返回清理 (`lib/client.js:30039-30510` ✔)；settings 段走 `slots.inject`。 |
| 2 | R2 | △ | `apply` 末尾的启动链 (`loadPersisted → loadInventory → …`，`:30553` ✔) 不在 effect 内，结果写入模块级 store；轮播/防抖计时器多数在 effect 清理中清除，未逐一核对。 |

**最高层**：2 (前提：S1 的 `ctx.loader`/客户端轮询读取标注为可选依赖，模块级内核视为本包共享资源)。卡在第 3 层的是 C2 (启动期跨 profile 的文件系统自检会抛错)。
**升级路径**：把两条子包可解析性自检从 `apply` 移到安装/诊断路径 (或只告警不抛) → C1/C2 ✓；`/diag` 根路径改到前缀下；`isBetterSidebarLoaded` 改为可选注入侧栏服务。之后宿主可到 3 (R2 仍为会话级统一回收)。
