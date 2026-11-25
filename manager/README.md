# 渐进的插件管理器

这里用 Racket 一步一步实现 Cordis 这个插件管理器，共 13 层（M0–M12），都已写完，目的是理解 Cordis 本身，而不是它的形式化（形式化的分层见 [layers/](../layers/)）。

**每一层都是一个能用的插件管理器**，带 `install!`、`show` 和一组演示场景（`settle!` 从 M2 起才需要），比上一层多一个用户看得见的功能。分层依据的是"用户在上一层会碰到什么问题"。

## 做法

- 每层是一个完整的独立文件，不 `require` 前一层；相邻两层的差别放在 `diffs/`，同 `layers/`。
- 例子插件从头到尾是同一套：core、shell、git、bad、toolkit、bus、ping、watcher，每层多上场几个。各层的 `main` 尽量保持同样的场景，读者能看到同一幕在新的一层里有什么不同。
- M0–M5 是同步的：一个插件的加载一下子完成。M6 才改成逐步执行；M6 的运行时与 [programs/cordis.rkt](../programs/cordis.rkt) 只差消息措辞和注释。
- M9 起插件写成拿到 ctx 的 apply，运行时用定界续延把它变回前几层的程序；M9 的演示输出与 M8 逐字相同。
- 编排者（插件市场、自更新、热重载）不加机制，作为 M3、M6 的演示场景出现，不单独成层。

## 运行

```sh
racket M6.rkt        # 演示: 一幕一幕地装, 移除, 重启, 打印每一步和状态
raco test M6.rkt     # 本层的全部检查
sh build.sh          # 测试全部各层, 重新生成 diffs/
```

## 分层

| 层 | 新功能 | 用户在上一层碰到的问题 | 引入的机制 | 对应的 Cordis |
|---|---|---|---|---|
| **M0 注册** | `install!`：插件的 body 往共享注册表里登记条目 | —— | 插件 = 名字 + body；body 是一串操作 | `ctx.plugin` |
| **M1 卸载** | `dispose!`；加载失败时自动回滚 | 装上去就卸不掉；加载到一半失败，留下半截状态 | 操作交出逆，实例的撤销栈按 LIFO 弹出；令牌让同一个处理器登记两次也能各撤各的 | disposer、`fiber.dispose` |
| **M2 服务与依赖** | 插件提供服务、声明依赖；安装次序随意 | 插件之间只能共用全局状态；装的次序一错就坏 | `provides`/`deps`、provision；依赖不可用时停在 inactive；提供冲突时报错。义务：依赖不成环（成环的插件永远等待，运行时不检查） | `ctx.provide`、`inject` |
| **M3 依赖变化** | `restart!`；卸掉提供者时依赖者跟着下线，提供者回来后重新上线；`reset!` 重试失败的插件 | 卸掉 core 之后，shell 还拿着一个已经不存在的服务 | provision 编号 + 视图；卸载守卫 held：先卸依赖者，再卸提供者 | `impl.uid`、`dependents`、`restart` |
| **M4 子插件** | 插件在加载中装别的插件 | 想打包几个小插件，生命期要跟着自己 | parent、`undo-spawn`：撤到这一项时先请子插件退出 | 在 `apply` 里调 `ctx.plugin` |
| **M5 运行时反应** | `react!`：上线后每响应一个事件产生一些效应，可以单独撤销 | 加载完之后做的事不在撤销栈里，卸载时漏掉 | 一次反应 = 一个子实例，复用 M4 | `ctx.effect`、事件处理器里动态创建的子 fiber |
| **M6 异步加载** | 加载一步一步走，其间别的事可以插进来；调度顺序可换 | 真实插件的加载是异步的，加载到一半依赖可能变了 | `remaining` 程序、`step!`；中途改道；守卫 held 在这里才真正要紧（使用者的卸载要走好几步）；测试中用随机调度检查结果一致 | 异步 `apply`、epoch |
| **M7 可选依赖** | 有就用，没有不等；出现或消失时重载 | 为了在缺少某个服务的宿主上不卡住，插件改用 `ctx.get` 偷看 | optional 声明；开始加载时的在场集进入视图；在场集一变就重载。取舍：为合流付的代价是两条义务（不可选依赖自己提供的服务，沿依赖边不成环），违反时活锁，测试中有反例 | （Cordis 没有；见 [EXTENSIONS.md](../docs/EXTENSIONS.md) 第1节） |
| **M8 交集生命期** | 效应挂在"插件 × agent"上，任一方结束就撤销 | 按 agent 的效应要靠手工簿记 | 带载荷的反应。取舍：效应实例不随 agent 结束而移除，代价是编排者义务（agent 编号不复用），测试中有反例 | （见 EXTENSIONS.md 第3节、[cordis3.rkt](../programs/cordis3.rkt)） |
| **M9 ctx 与 apply** | 插件写成"拿到 ctx 的一段代码"：`ctx-use`、`ctx-provide`、`ctx-plugin`、`ctx-on`（返回令牌）、`ctx-has?` | 程序 IR 不是用户写插件的样子 | ctx 对象；用定界续延把 apply 变回程序 IR，每次 ctx 调用是一个 await 点 | `apply(ctx)`、`ctx.plugin`、`ctx.on` |
| **M10 配置** | 插件带 config；`#:schema`；`update!` 换配置后重新加载；`replace!` 原地换插件 | 改一个参数只能卸了重装 | config；换配置就是卸载后重新加载。不建模 `internal/update` 拦下重启 | `apply(ctx, config)`、`fiber.update`、`registry.replace` |
| **M11 作用域与事件** | 沿父链查找服务；`isolate`；带顺序和选项的 emit | 子插件要用父插件的服务；两个插件抢同一个事件 | 作用域链；按键改名的隔离；`#:prepend`、`emit`、`bail` | `locate`、`isolate`、`ctx.emit`、`ctx.bail`（`intercept` 与其余 emit 方式没有做） |
| **M12 去掉纪律** | 允许 `ctx.get`、迟登记的 disposer、并发撤销 | —— | 不加机制，而是放开限制（`ctx-get`、`ctx-mutate!`、`ctx-on-dispose`、`#:undo-order 'any`），每一处失效配一个反例 | 真实的 Cordis；接到 [checker/](../checker/) 和 [PLUGIN-AUDIT.md](../docs/PLUGIN-AUDIT.md) |

M12 是整个系列的结尾。前面各层讲 Cordis 能保证什么；最后一层讲真实的 Cordis 允许什么，以及这两者之间的落差。

## 与真实 Cordis 的其余差别

有些地方是 Cordis 与我们有意不同，不打算在哪一层"追上"，只在相应层的注释里说明（细节见 [DESIGN.md](../docs/DESIGN.md) 第2节）：

- 状态：六态 vs 四态加错误标记；
- 提供冲突：运行时抛错 vs 安装时拒绝；
- disposer：并发 vs 串行 LIFO；
- provision 的 `check` 谓词：我们没有；
- 依赖成环：Cordis 和我们都不检测（M2 的义务）；
- disposer 失败：Cordis 吞掉。
