# 插件形态与 Rust 生态

主要回答 R6(插件的加载与卸载),对照 F3(target 驱动)与 F10(热重载),顺带涉及 F2(守卫 `¬held`)、
F6(父子 fiber)、F7(divert)。规则名见 [docs/RULES.md](../../docs/RULES.md),设计点见
[docs/DESIGN.md](../../docs/DESIGN.md),插件问题的分类见 [docs/PLUGIN-AUDIT.md](../../docs/PLUGIN-AUDIT.md)。
文中当作已有定理引用的 Rocq 名字都在 `theories/` 下检索确认过;候选课题里的新名字是提议。

关于 Rust 生态现状的事实(库名、API、版本、WASI 状态)都在 2026-11-25 前后检索核对过,版本号取自 crates.io
与 docs.rs 当天的数据。核实不了或只有二手材料的,在正文和第 5 节中标出。

## 1. 领域概览

### 1.1 原生动态库

**加载。** Rust 中加载动态库的事实标准是 `libloading`(当前 0.9.1,2026-11-13 发布)。`Library::close` 卸载库,
文档说它"视打开标志、库本身或平台细节,可能什么也不做";`Drop` 也会关闭库并忽略错误;`Library::new` 的安全条件
要求调用者保证库的终止例程可以安全执行 [libloading]。

**卸载的已知问题。** dlclose 一类的卸载在 Rust 中不可靠,原因有四类:

1. **线程局部变量的析构函数。** 在 Linux 类系统上,std 通过 `__cxa_thread_atexit_impl` 注册 TLS 析构函数,
   用的是 `&__dso_handle`。库被 dlclose 之后,线程退出时仍会调用已卸载代码里的析构函数,导致段错误
   [rust#88737];[rust#91979] 报告了 C 程序加载 Rust 模块、dlclose 后线程退出即崩溃,Node 的 worker 线程中加载
   Rust 原生模块同样中招,常用的变通是让模块永不卸载。[rust#147342] 在讨论给用户态 TLS 析构函数一个确定的运行
   时点,仍未定。libloading 自己的 issue 中也有 macOS 上 TLS 析构未运行导致崩溃的老报告。
2. **残留的线程与回调。** 库里起的线程、注册到别处(运行时、日志、tracing)的函数指针,在卸载后仍可能被调用。
   `hot-lib-reloader` 的文档记录了一个实例:被重载的库里用 `tracing` 会因重复注册 callsite 而崩溃 [hlr]。
3. **静态变量。** Rust 不在库卸载时对静态变量运行 `Drop`(Rust 内部论坛有专门讨论,见 [irlo-static])。
   `stabby` 在 Rust 1.78 以后把 trait 对象的 vtable 放进一个全局集合并且有意泄漏 [stabby],这意味着卸载库之后
   该集合中留有指向已卸载代码的指针。
4. **平台。** macOS 上一般不应指望 `dlclose` 真正卸载代码。Apple DTS 工程师 Quinn 在开发者论坛中说,
   Objective-C/Swift 运行时登记和 C++ ODR 等构造都会让卸载不发生,而且"很难判断你是否用到了这些构造"
   [apple-dlclose]。thread_local 会阻止 macOS 卸载 dylib 的说法只见于论坛与评论,**未找到官方陈述**。

**ABI 不稳定。** Rust Reference 写明默认的 `"Rust"` ABI"不提供任何稳定性保证" [ref-abi]。跨动态库传 Rust 类型
有三条路:

- **`abi_stable`**(0.11.3,最后发布于 2023-10):Rust 到 Rust 的 FFI,加载时检查类型布局;用例中明确写着
  "插件系统(不支持卸载)" [abi_stable]。
- **`stabby`**(72.1.16,2026-07):给结构体、带 niche 的和类型、trait 对象提供稳定布局;`#[stabby::export]`
  生成带类型报告的符号,`#[stabby::import]` 在使用前比对报告,可加"金丝雀"符号检查 rustc 版本 [stabby]。
  文档没有讨论卸载。
- **crABI**:`extern "crabi"` 的跟踪 issue [rust#111423] 自 2023-05 开启至今未关,四个步骤一个都没有勾上,
  没有 RFC;MCP 说明稳定前需要一份包含 ABI 规格的完整 RFC。

**共享全局状态。** `rubicon`(3.4.9)让多个 cdylib 共用一份 thread-local 和静态变量,前提是模块永不卸载、
所有模块用同一 rustc 版本和同一组 Cargo feature [rubicon]。

### 1.2 Rust 热重载工具

- **`hot-lib-reloader`**(0.8.2,2025-08):监视库文件,变化时重新加载;已知限制包括函数签名变化会崩溃、
  共享结构体布局不能改、函数不能泛型、全局状态要在重载后重新初始化(`TypeId` 也可能变),建议把状态留在
  可执行文件里、传给可重载函数 [hlr]。
- **Dioxus 的 subsecond**:不改写内存,而是让函数调用经过一张跳转表,重载时只更新表中的地址;应用把可热补丁的
  入口包在 `subsecond::call()` 里,补丁到来时把栈回卷到最近的热点再重新调用;静态变量被跟踪但不析构,
  结构体布局变化可能崩溃,仍标为实验性 [subsecond]。Bevy 0.17 起有基于 subsecond 的可选集成,限于 ECS 系统
  [bevy-0.17];Bevy 的设计笔记把插件或系统的卸载列在 MVP 范围之外。

两者的共同点:**旧代码通常不卸载**(subsecond 只追加新代码,hot-lib-reloader 依赖每次复制出新文件),状态的
连续性靠"状态留在宿主一侧"或"回卷后重新执行"。它们都是开发期工具,不处理效应的撤销。

### 1.3 WASM 组件模型

**组件与 WIT。** 组件用 WIT 描述导入与导出。资源(resource)是"指向组件之外某个实体的句柄",只通过方法暴露
行为;句柄分 `own`(唯一所有权,`resource.drop` 时销毁)和 `borrow`(调用期间的临时借用) [cm-wit]。
组件模型规范说明:句柄是指向**每个组件实例自己的**句柄表的 `i32` 下标,该表由运行时维护,模块不能直接访问;
被调用者必须在调用结束前放下全部借来的句柄,这由陷入强制 [cm-explainer]。组件之间不共享内存
(shared-nothing 链接) [cm-explainer]。

**wasmtime。** 当前 51.0.0(2026-11-20)。实例一旦在 `Store` 中创建,直到 `Store` 被丢弃才会释放;
因此文档建议让 `Store` 的生命期大致跟随一个"主实例",不适合在一个 `Store` 里无限创建实例 [wt-store]。
宿主侧资源放在 `ResourceTable` 中,它支持父子关系:`push_child` 记录父项,有子项存活时删除父项会失败,
报 `HasChildren` [wt-table]。v51 的说明提到对组件间调用的重入与 `may_leave` 条件做了更严格的检查 [wt-rel]。

**WASI 现状。** WASI 0.3.0 于 2026-06-11 发布,把 WASI 改建在组件模型的异步原语上:`async func`、`stream<T>`、
`future<T>` 进入规范 ABI,0.2 中 `wasi:io` 的 pollable 与流资源改由它们承担;wasmtime 46 起默认开启组件模型
异步 [bca-wasi03][cm-faq]。WASI 发布页显示 0.3 系列最新为 0.3.2(10-13),0.2 系列最新为 0.2.12(06-02);
0.3 运行时可以在宿主边界把 0.2 的导入映射到 0.3 原语 [wasi-rel][cm-faq]。下一个里程碑是组件模型 1.0,
WASI 1.0 依赖它先完成;官方博文没有给出日期,协作式线程会在之后的 0.3.x 小版本中提供 [bca-cm1]。
"WASI 1.0 定在 2026 年底或 2027 年初"的说法只见于二手综述,**未核实**。

**取消。** 组件模型的并发说明中,调用者用 `subtask.cancel` 提出取消请求,这只是请求,不是强行终止:
子任务可以照常 `task.return` 返回结果,也可以调用 `task.cancel` 确认取消;终态分"已返回""开始前取消"
"返回前取消"三种,后两种保证借出的句柄都已归还 [cm-conc]。目前只有使用 callback ABI 且已回到事件循环的线程
可以被取消。

### 1.4 用 WASM 做插件系统的项目

| 项目 | 做法 | 生命周期 |
|---|---|---|
| Zed 扩展 [zed] | WASM 组件,WIT 定义接口(含资源 `worktree`),宿主用 wasmtime 和 `bindgen!`;按扩展编译时的 API 版本选宿主接口;能力有限,没有任意 HTTP 或文件系统 | `extensions_updated` 删除已卸载的、重载已安装的、加入新的;加载时编译组件、建 `Store`、实例化、调 `init-extension`;每个扩展一个任务从通道取调用。卸载细节博文未写 |
| Extism [extism] | 核心 WASM 模块(不是组件),宿主函数提供能力;维护者在 issue 中表示等组件模型更成熟再采用(该 issue 日期与现状**未核实**) | `Plugin::reset` 使全部已分配内存失效;`cancel_handle` 可从别的线程取消正在运行的插件 |
| Lapce [lapce] | WASI 模块,依赖 wasmtime 14;插件通常负责启动 LSP 服务器并转发消息(PSP 协议) | 加载与卸载流程**未核实** |
| Envoy proxy-wasm [envoy][pw-abi] | 主线程加载主实例,插件接受配置后克隆到各 worker,worker 之间不共享实例与内存;`vm_id` 控制共享 | ABI v0.2.1:`proxy_on_context_create(context_id, parent_context_id)`;`proxy_on_done` 返回 false 可推迟删除,之后由模块调 `proxy_done`;最后 `proxy_on_delete`。`proxy_on_vm_start` 返回 false 中止启动 |

### 1.5 脚本宿主:在 Rust 中继续运行 dsh 的 JS 插件

- **`deno_core`**(0.413.0,2026-10):V8 加 Tokio;`JsRuntime` 是一个 JS 执行上下文,宿主经 `#[op2]` 暴露
  Rust 函数,`extension` 打包一组 op,模块加载器可替换 [deno_core]。Node 兼容层在单独的 `deno_node`
  (0.198.0)中 [deno_node]。
- **`rquickjs`**(0.14.0,2026-09):QuickJS 绑定;`Runtime` 是解释器状态,`Context` 是一个全局环境,同一
  `Runtime` 下的 `Context` 可以共享对象,隔离程度文档没有说清 [rquickjs]。
- **`boa_engine`**(0.22.0,2026-08):纯 Rust 的 JS 引擎,自述"支持语言的一部分" [boa]。
- **Hardened JavaScript(SES)**:`lockdown()` 冻结内建对象,`Compartment` 是只拥有显式传入能力的隔离全局环境;
  MetaMask 等用它隔离第三方插件 [ses]。
- **JS 编译成组件**:ComponentizeJS 内嵌 SpiderMonkey(基于 StarlingMonkey),经 `jco componentize` 把 ES 模块
  编译成组件;jco 的内置 world 默认 WASI 0.3,StarlingMonkey 核心仍以 WASI 0.2 为目标 [componentize-js]。

审计中的插件都以打包后的 JS 发布(`dist/index.js`、`lib/main.js` 等),运行时不涉及 TS 转译。真正的障碍是
它们依赖 Node API(子进程、文件系统、HTTP 服务器)和 npm 依赖,这只有 `deno_node` 一类完整兼容层能承接。

### 1.6 已有 Rust 框架中的相关部件

- **Bevy 的 `Plugin` 与 `App`**(0.20.1):`Plugin` 有 `build`、`ready`、`finish`、`cleanup`、`name`、`is_unique`;
  没有卸载,也没有依赖声明 [bevy-plugin]。`is_unique` 为真的插件重复加入时报 `DuplicatePlugin`;`finish` 或
  `cleanup` 之后再加插件会 panic;`insert_resource` "覆盖同类型的已有资源" [bevy-app]。资源是按类型索引的
  全局单例。
- **actor 框架。**
  - `ractor`(0.16.6):`pre_start` 构造状态,失败时 `spawn` 返回错误;`post_stop` 在 `Signal::Kill` 或自身
    panic 时不调用;`handle_supervisor_evt` 默认在任一子 actor 退出时让监督者也退出 [ractor]。
  - `kameo`(0.22.2):`on_start`、`on_panic`、`on_link_died`(默认在链接的 actor 非正常死亡时自己也停止)、
    `on_stop` [kameo]。
  - `actix`(0.13.6):`Supervised::restarting` 在监督者重启失败的 actor 时调用,用新的执行上下文 [actix]。
  - `bastion`:最后发布 0.4.5,2022-01,已不活跃 [bastion]。
- **tower**(0.5.3):`Service` 只有 `poll_ready` 和 `call`;`poll_ready` 可以预留资源供随后的 `call` 消耗,
  未就绪就调用 `call` 时实现可以 panic;没有显式的关闭方法,清理靠 drop [tower]。`Layer` 把中间件静态地
  套在服务外面。
- **依赖注入**:`shaku`(0.6.3,2026-08)是编译期 DI,`module!` 宏声明一组组件与提供者,`HasComponent` 让依赖
  在编译期检查;没有启动、停止、卸载 [shaku]。
- **systemd(对照)**:`Requires=`/`Wants=` 不影响启停顺序,顺序由 `After=`/`Before=` 单独给出,停止时按启动顺序
  的逆序;`BindsTo=` 比 `Requires=` 强,被依赖单元意外停止时本单元也停止;`PartOf=` 只传递停止与重启 [systemd]。

## 2. 对照表

"关系"一列:**精确**、**近似**、**仅形似**。

### 2.1 加载与卸载机制

| 生态中的概念 | 演算中的对应 | 关系 | 说明 |
|---|---|---|---|
| wasmtime `Store` 丢弃即回收全部实例内存 | `L-Unloaded` 后 `L-Remove` 删除 fiber 条目 | 近似 | 回收的是插件私有内存。演算里私有状态不在存储中(D1:跨组件共享的可变状态都是服务的状态),所以私有内存的回收与 `recovery_exact` 无关;它保证的是"私有状态不泄漏",这一层演算没有陈述 |
| 实例私有的线性内存、shared-nothing 链接 | 不设 `Amb`(RULES §0,差异 m) | 精确 | 组件之间没有共享内存,跨插件共享的状态只能经宿主导入,正是"所有共享状态都是服务的状态"的宿主层实现 |
| WIT world 中静态列出的导入 | 组件义务"`Op k` 满足 `k ∈ d ∪ p`"(RULES §1)、审计 S1 | 近似 | 导入的粒度是接口,不是键;按条目即键(差异 r)动态出现的键要靠运行时交出的句柄 |
| `own`/`borrow` 句柄,每实例一张句柄表 | 承诺视图 ω、能力不可伪造 | 近似 | 句柄只能由宿主或别的组件交出,不能凭名字取得,所以"读未注入的服务"写不出来。ω 记的是 pid,句柄对应"已解析的 provision" |
| `borrow` 必须在调用结束前放下 | effects-coeffects 报告 4.3 节"加载期能力不得逃进运行期回调" | 近似 | 组件模型在一次调用的粒度上强制,演算需要的是"整个加载期"的粒度 |
| `ResourceTable` 有子项时拒绝删除父项 | `L-Undo` 撤 `USpawn m` 要求 `m ∉ dom F`;`parent_waits_child` | 近似 | 只是拒绝,不会像 `L-RetireChild` 那样先请子项退出,也没有 LIFO |
| `subtask.cancel` 只是请求,子任务可照常返回或 `task.cancel` 确认 | `L-Divert` 与 target 变化后的 `L-Step`(落地,差异 h) | 近似 | 很贴近:取消后仍可落地,或在检查点放弃。差别在于组件模型的取消针对一次调用,演算针对整个加载;"返回前取消"保证借出句柄归还,对应放弃后不留下半个操作(D6 的"放弃") |
| proxy-wasm `proxy_on_done` 返回 false 推迟删除,`proxy_done` 后才 `proxy_on_delete` | 卸载可等待(R3):`Unloading` 期间逐项 `L-Undo`,完毕才 `L-Unloaded` | 近似 | 只有"自己没清理完就别删我",没有"别人还依赖我就别动"(`¬held`) |
| `context_id`/`parent_context_id` | 父指针 π(RULES §2) | 仅形似 | 只用于路由回调,父上下文结束不等子上下文 |
| Envoy 主实例先验证配置再克隆到 worker | `O-Insert` 前提检查后 `L-Begin` | 仅形似 | 没有依赖关系 |
| Zed `extensions_updated`:删除、重载、新增 | 编排者经 loader 条目协调(`Ext/Orchestrator.v`,`osum_confluence`) | 近似 | 期望状态是已安装扩展的集合,宿主收敛到它;扩展之间没有依赖,所以不需要守卫,也谈不上合流 |
| Extism `Plugin::reset` | `O-Restart` | 仅形似 | reset 只丢插件内存,不撤销插件经宿主函数做过的事 |
| libloading `Library::close` / dlclose | 无 | — | 演算没有"代码"的生命期。见 3.1 |
| `abi_stable`/`stabby` 加载时比对类型布局或类型报告 | `O-Insert` 的前提(插入时拒绝不相容的组件,差异 c) | 近似 | 都在插入时检查,不等运行时失败;检查的对象不同:ABI 相容性对提供集合不相交 |
| subsecond 跳转表,回卷到热点后重新调用 | `O-Restart` | 仅形似 | 回卷不撤销效应,状态原样保留;这正是演算刻意不做的(恢复精确性要求先撤销再重载) |
| hot-lib-reloader"状态留在宿主,传给可重载函数" | 程序看不到状态,只经操作结果决定下一步(D1) | 近似 | 同一原则:代码可换,状态归宿主。hot-lib-reloader 没有撤销 |

### 2.2 框架部件

| 生态中的概念 | 演算中的对应 | 关系 | 说明 |
|---|---|---|---|
| Bevy `build`/`ready`/`finish`/`cleanup` | `L-Begin`、`L-Step`、`Done` | 仅形似 | 只有一次性的启动阶段,没有卸载,也没有 target 驱动的重载 |
| Bevy `is_unique` 与 `DuplicatePlugin` | `O-Insert` 要求 `p` 两两不相交 | 近似 | 按插件名去重,不是按提供的键;但同样在加入时拒绝,不等运行时 |
| Bevy 资源(按类型索引的全局单例) | 绑定 `B : K ⇀ Binding`,键为类型 | 近似 | 没有 owner 与 pid;`insert_resource` 覆盖已有资源,而 `Provide` 在键已绑定时失败。覆盖会让依赖者在不知情时换了 provision,这正是差异 b 用 pid 排除的情形 |
| Bevy 插件按加入顺序构建,`finish` 后不能再加 | `static_assembly` 的"按插入顺序静态组装" | 近似 | Bevy 只有静态组装这一种执行;演算证明任意动态执行的终态等于它 |
| shaku 编译期 DI(`module!`、`HasComponent`) | 组件声明 `d`/`p`、静态组装 | 近似 | shaku 直接算出静态组装,编译期检查依赖齐全,相当于把 research 第一梯队课题 1(提供状态的静态判断)做到类型里;没有运行期出现、消失、替换 |
| kameo `on_link_died` 默认随之停止 | 提供者离开 Active 后依赖者 target 变为 ⊥,`L-Leave`/`L-Divert` | 近似 | 演算还会在提供者回来后自动重新加载(`L-Begin`);kameo 默认只停不起 |
| ractor 监督者默认在子 actor 退出时退出 | 无 | — | 演算中子 fiber 失败不传给父 fiber(concurrency.md:相当于 SupervisorJob) |
| actix `Supervised::restarting`,ractor/kameo 的重启 | `O-Reset`、`O-Restart` | 近似 | actor 框架由监督者自动重启;演算把重试交给外部(差异 i),research 第二梯队课题 7 把监督者作为编排扩展 |
| ractor `post_stop` 在 Kill 或 panic 时不调用 | R1:`mem::forget` 安全,析构不保证运行 | 精确 | 同一个问题:清理代码可能不运行。演算的回答是逆由服务给出、由运行时调度(见 3.1),而不是写在会被跳过的析构里 |
| tower `poll_ready` 预留、`call` 消耗 | D6 的 `prepare`/`commit` | 仅形似 | 都是两段;但 `poll_ready` 是背压,不是"可以 await、不碰状态"的准备阶段 |
| tower `Layer` 的静态套叠 | 有序中间件链;`EventBus.v` 的有序分发,`bus_no_commute` | 近似 | 套叠顺序决定行为,所以动态登记的中间件在 `HCom` 下不可交换。审计中 dsh-im 与 dsh-qqbot 都以 `prepend` 登记 `approval/request`,谁先处理取决于激活顺序,就是这个问题 |
| systemd `Requires=` + `After=`,停止按逆序 | `begin_requires_deps`、`provider_outlives`、`unload_waits` | 近似 | 演算把"需要"和"顺序"合成一个 `d`;systemd 分开写。逆序停止对应依赖者先卸载;`unload_waits` 更强,提供者在依赖者离开前不撤销任何一项 |
| systemd `BindsTo=` | 提供者离开 → 依赖者 target 变化 → 离开 | 近似 | 演算还有自动的重新加载;systemd 要另配重启策略 |
| systemd `PartOf=`(重启传递) | 提供者 `O-Restart` 后 pid 改变,依赖者重新加载(差异 b) | 近似 | 演算中重启的传递不是声明的,是 ω 记 pid 的推论 |

## 3. 差异

### 3.1 卸载不可靠时,`recovery_exact` 还在什么层面成立

`recovery_exact`(`Recovery.v`)说的是:选定 fiber `n`,从 `n` 没有待撤销项到再次没有待撤销项,每个绑定上的服务状态
≃ 影子执行中略去 `n` 全部操作的状态。它的对象是**存储**(`binds`),不涉及代码。由此:

1. **代码段不在定理内。** 动态库的代码、静态变量、TLS、残留线程都属于演算没有的 `Amb`(差异 m)。
   dlclose 失败或不做,不影响存储层面的结论。
2. **但定理依赖一个隐含前提:逆可以运行。** 演算里撤销项 `UOp k pid tok g` 的 `g` 来自服务操作 `run`
   (`Prov` 不变式:每个撤销项的逆都来自组件程序中某个操作的结果)。在实现中,若 `g` 是插件动态库里的闭包,
   那么撤销时这段代码必须还在。所以对动态库,正确的顺序是:先走完 `Unloading` 直到 `L-Unloaded`,再到
   `L-Remove`,最后才可以考虑卸载代码。更好的做法是让逆由宿主一侧的服务给出,插件代码里不留逆
   (这正是演算的形状:插件只发出 `Op`,逆由 `Σ` 产生)。
3. **什么时候可以卸载代码。** 演算中逆来自 `Σ`,不来自组件程序,所以组件 `c` 的最后一个 fiber 被移除之后,
   将来的任何步骤都不再需要 `c` 的程序(除非再次 `O-Insert c`)。这给出了一个"代码可回收"的判据,
   见课题 P3。对 WASM 它决定何时丢弃 `Store`;对动态库,它只是必要条件,TLS 析构、残留线程、vtable 指针
   这些演算外的引用仍可能让卸载不安全。
4. **实际结论:原生动态库采用"加载一次,永不卸载"。** 重载 = 撤销全部效应(恢复精确性照常成立)+ 加载新
   版本的代码到新地址;旧代码泄漏。泄漏量以版本数为界。这与 `abi_stable` 的"不支持卸载"、`rubicon` 的
   "模块永不卸载"、subsecond 的"只追加"一致。代价是长时间运行、频繁热更新的进程内存单调增长。

所以在动态库形态下,`recovery_exact` 在**服务状态**层面完整成立;在**进程**层面不成立,也不打算成立。
WASM 形态下,私有内存随 `Store` 丢弃而回收,宿主侧资源放在 `ResourceTable` 里;`Store` 丢弃时这些宿主资源
是否随之释放,文档没有直接说明(`Store<T>` 拥有 `T`,按 Rust 的所有权推断会被 drop,**未核实**),
所以进程层面也接近成立。

### 3.2 能力隔离让 S3 写不出来,但不是全部

审计 S3 的四类写法在 WASM 组件中的情况:

| 写法 | 组件中 | 原因 |
|---|---|---|
| 猴补丁服务实例或原型 | 写不出 | 服务对象在宿主或提供者实例的内存里,插件只拿到句柄和导入函数 |
| `globalThis` 跨实例共享 | 写不出 | 每个实例有自己的线性内存;只要宿主给每个 fiber 一个独立实例,就没有可共享的全局 |
| `internal/*` 元层钩子 | 写不出,除非宿主导出 | 导入在 world 中静态列出,宿主不提供就不存在 |
| 把效应挂到别人的 ctx 上 | 写不出,除非宿主允许转交 | 句柄表按实例分开;插件只能用别人交给它的句柄。宿主不把一个 fiber 的能力交给另一个 fiber 即可 |
| 编排别的插件 | 仍可写,但只能经宿主接口 | 这是编排者义务(`Ext/Orchestrator.v`),宿主只导出 loader 条目接口,就把编排限定在 `osum_confluence` 覆盖的形状内 |

能力隔离**不**解决的:

- **R1 登记推迟、中途抛错泄漏**:如果宿主的服务接口是"注册,返回一个 disposer 让插件自己保管",插件照样可以
  丢掉它。必须把接口做成"操作原子地产生逆,逆进宿主的累加器",也就是演算的 `L-Step`。这要求宿主不提供
  返回 disposer 的接口。
- **R3 相遇受控**:两个插件在同一注册表登记同名条目,能力隔离不管。宿主可以按 fiber 给登记名加前缀,
  把注册表的 `Covers G` 变成构造性质(课题 P2)。
- **C2 依赖外部世界的分支**:插件仍可经 WASI 读文件、网络、时钟。要得到合流,宿主必须不给这些导入,
  或把它们放进 D6 的 `prepare` 阶段并承认合流只对固定环境成立。
- **提供者插件的服务义务**:插件 provide 的服务,其状态在提供者实例的内存里,操作与逆是提供者的代码。
  这时 `Revertible`、`ConfHyps` 是插件作者的义务,宿主检查不了。

### 3.3 插件形态推荐,以及汇总定理前提的分配

下表把 `Summary.v` 的前提逐条分给宿主或插件。"宿主"指运行时能检查或由构造保证;"插件"指仍是插件作者的义务;
"服务"指服务作者的义务(宿主自带的服务由宿主团队负责,另行验证,见 [assurance.md](assurance.md))。

| 前提 | 静态链接的 Rust crate | 原生动态库 | WASM 组件 | 嵌入 JS(每插件一个隔离环境) |
|---|---|---|---|---|
| 第 0 层的隐含前提 S1(只访问 `d ∪ p`) | 宿主:类型系统,每个依赖作为参数传入 | 插件:可以绕过(全进程地址空间,`unsafe`) | 宿主:导入静态、句柄不可伪造 | 宿主,"诚实但出错的作者"级:只给能力对象;反射等手段仍可能绕过 |
| S2(provide 的键静态、不冲突) | 宿主:清单检查于 `O-Insert` | 宿主:清单检查 | 宿主:清单检查 | 宿主:清单检查 |
| S3(无猴补丁、全局共享、元层钩子、借用别人的 ctx) | 宿主,前提是禁 `static mut` 与 `unsafe`(可用 lint 强制) | 插件 | 宿主(3.2) | 部分由宿主:SES 式冻结加每插件 `Compartment`;Node API 要么不给,要么成为新的越界口子 |
| `Obligations`:`Bounded Kb` | 插件 | 插件 | 宿主可以强制:按操作计数,超过 `Kb` 即 `Fail`(课题 P2);fuel/epoch 只限制计算量 | 宿主可强制操作计数 |
| `Obligations`:秩沿 `Above` 递增、有上界 | 宿主:插入时对清单做无环检查 | 同左 | 同左 | 同左 |
| `Revertible G`(操作良好、撤销独立) | 服务 | 服务 | 宿主自带服务:服务作者;插件提供的服务:插件 | 同 WASM |
| `Covers G`(`CoPair ⊆ G`) | 插件(相遇受控) | 插件 | 注册表类服务可由宿主强制命名空间,其余仍是插件 | 同 WASM |
| `ConfHyps Σ G` | 服务 | 服务 | 同 `Revertible` | 同 `Revertible` |
| `TotalProv` | 插件,或由宿主包装(课题 P2) | 同左 | 宿主包装:`Done` 时未提供全部 `p` 即 `Fail` | 同左 |
| D6 原子性(每个操作是一个原子步) | 宿主:服务操作是同步函数 | 宿主,但插件可在操作中途经别的路径改状态 | 宿主:导入函数同步执行即原子;异步导入取 `prepare`/`commit` 形状;组件模型限制重入 | 宿主:op 在 Rust 一侧同步执行 |
| `Prov`(逆都来自程序中的操作) | 宿主:不提供裸 disposer 接口 | 宿主同样可以不提供,但插件能自带析构逻辑 | 宿主:插件无法向宿主累加器写入任意代码 | 宿主:不暴露 `ctx.effect` 式的裸 disposer,或把它算作越界 |
| C4(不直接 dispose 启动时 spawn 的子 fiber) | 宿主:不导出该操作 | 同左 | 同左 | 同左 |
| C2(启动分支不依赖调度与外部世界) | 插件 | 插件 | 宿主可收紧:不给 WASI 文件、网络、时钟 | 宿主可收紧:不给 Node API,但这样大部分现有插件跑不起来 |
| 代码与私有状态的回收 | 不需要 | 不可靠,采用"永不卸载" | 宿主:丢弃 `Store` | 宿主:丢弃 isolate/context |

**推荐。**

1. **第三方插件用 WASM 组件。** 它是唯一一种让第 0 层的隐含前提(S1、S3)和 `Prov`、D6 原子性都由宿主保证的
   形态,也是唯一一种能真正回收插件私有状态的形态。设计要点:每个 fiber 一个实例(反应子 fiber 可以共享父
   fiber 的 `Store`,但共享 `Store` 意味着要等父 fiber 移除才能回收,见 [wt-store]);服务操作是宿主导入,
   逆由宿主产生并压进宿主维护的累加器;插件不接触 disposer;spawn 只能引用清单中声明的组件。代价:
   要为 dsh 的服务重写 WIT 接口;依赖 WASI 0.3 的异步,而组件模型的取消目前只覆盖 callback ABI。
2. **宿主自带的服务和第一方插件用静态链接的 Rust crate。** 服务义务(`Revertible`、`ConfHyps`)集中在这里,
   用 [assurance.md](assurance.md) 中的工具验证。插件形态的好处是类型系统直接给出 S1。
3. **现有的 dsh JS 插件用嵌入 JS 作为过渡。** 用 `deno_core` 加 `deno_node`,每个插件一个隔离环境,只经 op
   接触服务。保证只到"诚实但出错的作者"级。审计中能到第 2、3 层的插件(PLUGIN-AUDIT 的 A 类)最可能在这一层
   直接运行。ComponentizeJS 把 JS 编译成组件是第二条路,但 Node API 与 npm 依赖同样是障碍。
4. **原生动态库只用于可信的第一方扩展,且永不卸载。** 不推荐给第三方:S1、S3 都回到插件义务,ABI 要靠
   `stabby` 一类库加金丝雀检查,而 crABI 至今没有 RFC。

## 4. 候选课题

### P1. 演算的 WIT 映射与最小宿主原型(中到大)

- **目标**:给出一份 WIT 包,让组件的启动程序恰好是 `Prog` 的一次解释,宿主恰好是 `step` 的实现,并据此逐条
  核对 3.3 节表中"宿主"一栏的前提确实由宿主保证。
- **做法**:
  1. 写 WIT:服务操作是宿主导入 `op(key, arg) -> result<out, err>`(同步);`provide(key, init)`;`spawn(component-id)`,
     `component-id` 只能取清单中的值;启动程序是导出 `apply()`,正常返回即 `Done`,返回错误或陷入即 `Fail`。
     依赖的解析结果以 `own` 句柄交给组件,对应 ω。
  2. 用 wasmtime 写一个只含注册表与监听器两个服务的宿主,实现 `O-Insert`、`O-Dispose`、`O-Restart` 与全部生命周期
     规则,每个 fiber 一个 `Store`。
  3. 用演算抽取出的 `step`(research 第二梯队课题 6)做差分测试:同一输入序列下,宿主每到达一个落定状态,
     与 `step` 给出的状态比较。
  4. 对照审计的 S3 证据写反例组件:试图访问未声明的键、保留加载期句柄到运行期、转交句柄,都应被拒绝。
- **预期产出**:WIT 文件;原型宿主;差分测试;一份"每条前提由谁保证"的表,取代 3.3 节中的推测。
- **风险**:dsh 服务接口多且以对象为中心,WIT 化的工作量可能远大于原型本身;wasmtime 的组件模型异步仍在
  收紧规范(v51 的说明中还在修重入与取消的行为);异步导入下"操作原子"要靠 `prepare`/`commit` 形状保证。
- **工作量**:原型中,接近 dsh 实际服务面时大。

### P2. 宿主包装把插件义务变成定理(小到中)

- **目标**:证明三种宿主侧的包装把汇总定理的三项插件义务变成构造性质,让 `Summary.v` 的前提在 WASM 或 JS 宿主
  下变少。
- **做法**(在 `theories/` 下新建一个文件,不改现有文件):
  1. **操作预算**:`budget Kb P` 在程序上数 `Op`/`Provide`/`Spawn`,超出 `Kb` 时变成 `Fail`。证明
     `budget_bounded : Bounded Kb (budget Kb P)`,且 `Bounded Kb P` 时 `budget Kb P = P`。
  2. **完整提供**:`totalize ps P` 沿路径记录已提供的键,在 `Done` 处若未提供全部 `ps` 则 `Fail EUnresolved`。
     证明 `totalize_total : AllDoneProv` 对 `ps` 中每个键成立,且对已满足 `TotalProv` 的程序不改变。
     这样 `summary_confluence` 的 `TotalProv` 前提可以对包装后的组件表去掉;代价是原来"漏提供"的执行变成失败,
     被 `NoFailed` 排除,这与差异 c"冲突在插入时拒绝而不是运行时吞掉"是同一方向。
  3. **注册表命名空间**:把注册表操作的名字与 fiber 所属组件配对,证明不同组件的注册从不同名,从而注册操作
     落在 `RegistryConf.v` 的 `reg_meet` 内,`Covers G` 对注册表成立。
- **预期产出**:三条引理和一个推论版的汇总定理(前提少三项,组件表换成包装后的表)。
- **风险**:第 3 项要处理"同一组件多个 fiber"(不提供键的组件,RULES §6′)的情形,前缀要用 fiber 名而不是
  组件名,这会碰到合流在重命名意义下成立的细节;`totalize` 需要程序是语法对象,`Prog` 正好是。
- **工作量**:1、2 小,3 小到中。

### P3. 代码回收时机引理(小)

- **目标**:给出"何时可以丢弃组件 `c` 的代码"(丢弃 WASM `Store`,或在可行时 dlclose)的判据,并证明丢弃后
  将来的执行不受影响,对应 3.1 节第 3 条。
- **做法**:定义 `NoFiberOf c γ`(没有现存 fiber 的组件是 `c`);证明从这样的状态出发,不含 `O-Insert c` 的任意
  执行与"把 `prog c` 换成任意组件"的执行逐步相同(`step` 不读 `prog c`)。再证明撤销项不引用组件程序:
  `UOp` 中的逆来自服务,`USpawn` 只含名字。
- **预期产出**:一条引理和一段对 Rust 宿主的设计说明:每个组件的代码引用计数等于其现存 fiber 数,降到零即可回收;
  反应子 fiber 共享父 fiber 的 `Store` 时,回收点是父 fiber 的 `L-Remove`。
- **风险**:结论在演算里几乎是显然的,价值主要在于把"逆归服务而不归插件"这条设计原则写成可引用的陈述;
  对动态库它只是必要条件。
- **工作量**:小。

### P4. 审计插件在嵌入 JS 宿主中的可运行性实验(中)

- **目标**:回答"Rust 版 Cordis 能否继续运行现有 dsh 插件,以什么保证"。
- **做法**:用 `deno_core` 加 `deno_node` 搭一个最小宿主,每个插件一个隔离环境,只经 op 暴露 `ctx` 的受控子集;
  选审计中 A 类的几个插件(deep-view、dsh-agent-compare、dsh-token-diet 等)运行,记录哪些写法在隔离下失败、
  哪些需要宿主新原语。与 effects-coeffects.md 课题 B(能力化的 EDSL 运行时)共享反例集。
- **预期产出**:一张"插件 × 失败原因"表;对 Node API 的最小需求清单。
- **风险**:`deno_node` 与 Node 的兼容程度、在嵌入场景下的可用性本次没有核实;dsh 宿主自身的服务都是 TS,
  实验需要先把它们桥接过来。
- **工作量**:中。

**排序。** P2、P3 小,只动 Rocq,能直接减少 `Summary.v` 的前提或补上一条设计原则,先做。P1 是 Rust 重写的
核心设计验证,应在 P2 之后做,用 P2 的包装作为宿主的检查项。P4 只在决定保留 JS 插件兼容时做。

**不建议做**:把原生动态库的卸载做成可靠机制(TLS 析构、残留线程、macOS 行为都在 Rust 与平台的控制之外);
给插件开放返回 disposer 的服务接口(会把 R1 类泄漏带回来,破坏 `Prov`)。

## 5. 参考文献

核实方式:2026-11-25 前后逐条访问官方文档、docs.rs、crates.io API、GitHub 页面。版本号取自当天的 crates.io/docs.rs。

**Rust 语言与动态库**

- **[ref-abi]** The Rust Reference, "External blocks", ABI 一节。doc.rust-lang.org/reference/items/external-blocks.html。
  已读:"The Rust ABI offers no stability guarantees."
- **[libloading]** `libloading` 0.9.1(2026-11-13),`Library` 文档。docs.rs/libloading。已读。
- **[rust#88737]** rust-lang/rust issue #88737(TLS 析构经 `__cxa_thread_atexit_impl` 注册,dlclose 后仍被调用)。
  依据检索摘要,未逐条读完讨论。
- **[rust#91979]** rust-lang/rust issue #91979(dlclose Rust 模块后线程退出段错误)。依据检索摘要。
- **[rust#147342]** rust-lang/rust issue #147342(用户态 TLS 析构注册表的讨论)。依据检索摘要。
- **[irlo-static]** Rust 内部论坛帖 "When a DLL built with Rust is unloaded, it seems that Rust does not automatically
  call drop on static global variables defined in the DLL"。internals.rust-lang.org。只核实了标题与存在,**内容未读**。
- **[apple-dlclose]** Apple Developer Forums thread 122591,"dlclose will not unload library when using macOS Frameworks",
  DTS 工程师 Quinn 的回复。已读。
- **[rust#111423]** rust-lang/rust issue #111423,"Tracking Issue for the experimental crabi ABI",2023-05-10 开启,
  至今开启,无 RFC。已读。
- **[abi_stable]** `abi_stable` 0.11.3(2023-10-12)。docs.rs/abi_stable。已读。
- **[stabby]** `stabby` 72.1.16(2026-07-20),github.com/ZettaScaleLabs/stabby README。已读。
- **[rubicon]** `rubicon` 3.4.9(2024-09-17),bearcove/rubicon。docs.rs。已读。

**热重载**

- **[hlr]** `hot-lib-reloader` 0.8.2(2025-08-11),github.com/rksm/hot-lib-reloader-rs README。已读。
- **[subsecond]** `subsecond`(Dioxus),docs.rs/subsecond 0.7.x 文档与 Dioxus 0.7 发布说明。机制已读;
  速度数字只见于第三方,本文未引用。
- **[bevy-0.17]** Bevy 0.17 发布说明,bevy.org/news/bevy-0-17/,hotpatching 一节。依据检索摘要;"MVP 不含卸载"
  出自 Bevy 的设计笔记(hackmd),是提案,与实际发布可能不同。

**WASM 组件模型与 WASI**

- **[cm-wit]** The WebAssembly Component Model 文档,"WIT" 一节。component-model.bytecodealliance.org/design/wit.html。已读。
- **[cm-explainer]** WebAssembly/component-model, `design/mvp/Explainer.md`。已读资源、句柄表、`own`/`borrow`、
  shared-nothing 部分。
- **[cm-conc]** WebAssembly/component-model, `design/mvp/Concurrency.md`,取消一节。已读。
- **[cm-faq]** Component Model 文档 FAQ。已读。
- **[bca-wasi03]** Bailey Hayes, Yosh Wuyts. "WASI 0.3 Launched". Bytecode Alliance 博客,2026-06-11。已读。
- **[bca-cm1]** Eric Gregory. "The Road to Component Model 1.0". Bytecode Alliance 博客,2026-06-08。已读。
- **[wasi-rel]** github.com/WebAssembly/WASI/releases。已读;页面多数只显示月日,年份按 RC 标签推断。
- **[wt-store]** wasmtime `Store` 文档,docs.rs/wasmtime。已读。
- **[wt-table]** wasmtime `component::ResourceTable` 文档。已读。`Store` 丢弃时宿主资源的去向文档未说明。
- **[wt-rel]** github.com/bytecodealliance/wasmtime/releases,v51.0.0(2026-11-20)。已读。

**WASM 插件系统**

- **[zed]** Thorsten Ball, Max Brunsfeld, Marshall Bowers. "How Zed Extensions Work"(Zed Decoded)。zed.dev 博客,
  2024-10-21。已读;卸载细节博文未写。
- **[extism]** Extism 文档 "Plug-in" 概念页;`extism` 1.41.0 的 `Plugin` 文档;GitHub issue extism/extism#666。
  前两者已读;#666 只见检索摘要,日期与当前立场**未核实**。
- **[lapce]** `lapce-plugin` 0.1.2(2023-10-24);lapce/lapce 仓库 `lapce-proxy/Cargo.toml`(wasmtime 14)。
  依赖已读;插件的加载、卸载流程**未核实**。
- **[envoy]** Envoy 文档 "Wasm" 架构概览,envoyproxy.io。已读。
- **[pw-abi]** proxy-wasm/spec, `abi-versions/v0.2.1/README.md`。依据检索摘要与 `proxy-sdk` 文档,未通读规格。

**脚本宿主**

- **[deno_core]** `deno_core` 0.413.0(2026-10-21),docs.rs。已读。
- **[deno_node]** `deno_node` 0.198.0(2026-10-21),crates.io。只核实存在与描述("Node compatibility for Deno"),
  嵌入场景的可用性**未核实**。
- **[rquickjs]** `rquickjs` 0.14.0(2026-09-18),docs.rs。已读;上下文间的隔离程度文档未说明。
- **[boa]** `boa_engine` 0.22.0(2026-08-28),crates.io。已读描述。
- **[ses]** endojs/endo, `packages/ses/README.md`(Hardened JavaScript)。依据检索摘要。
- **[componentize-js]** bytecodealliance/ComponentizeJS 与 jco README。依据检索摘要;ComponentizeJS 对 WASI 0.3 的
  完整程度**未核实**。

**框架**

- **[bevy-plugin]** Bevy 0.20.1,`bevy::app::Plugin` 文档。已读。
- **[bevy-app]** Bevy 0.20.1,`bevy_app/src/app.rs`(`insert_resource`、`add_plugins`、`DuplicatePlugin`)。已读源码。
- **[ractor]** `ractor` 0.16.6,`Actor` trait 文档。已读。
- **[kameo]** `kameo` 0.22.2,`Actor` trait 文档。已读。
- **[actix]** `actix` 0.13.6,`Supervised` 文档。已读。
- **[bastion]** `bastion` 0.4.5(2022-01-07),crates.io。已读。
- **[tower]** `tower` 0.5.3 / `tower-service` 0.3.3,`Service` 文档。已读。
- **[shaku]** `shaku` 0.6.3(2026-08-02),docs.rs。已读;"缺依赖是编译错误"文档没有明说,是按 `HasComponent` 的设计推断。
- **[systemd]** systemd.unit(5),freedesktop.org。已读 `Requires=`、`Wants=`、`BindsTo=`、`PartOf=`、`After=`。

**未核实或只部分核实的条目**,共 7 条:

1. thread_local 会阻止 macOS 卸载 dylib(只见论坛与评论);
2. WASI 1.0 的目标时间(只见二手综述);
3. wasmtime `Store` 丢弃时 `ResourceTable` 中宿主资源随之释放(按所有权推断);
4. Extism 对组件模型的当前立场(issue #666 的日期);
5. Lapce 插件的加载与卸载流程;
6. `deno_node` 在嵌入场景下的可用性;
7. ComponentizeJS 对 WASI 0.3 的支持程度。

另有 [irlo-static] 只核实了标题,[rust#88737]、[rust#91979]、[rust#147342]、[pw-abi]、[ses]、[bevy-0.17] 依据检索摘要。
