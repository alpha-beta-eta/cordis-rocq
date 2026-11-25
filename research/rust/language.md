# Rust 语言机制如何承载演算

本文回答 [PLAN.md](PLAN.md) 的 R1–R5 与 R7:演算的撤销日志、共享服务、守卫与等待、取消与落地、组件声明、
fiber 身份,分别能落到 Rust 的哪些语言机制上,哪些会和语言冲突。结构沿用 [../PLAN.md](../PLAN.md) 第 3 节的五段。

**核对日期。** 本文的 Rust 现状按 2026-11-25 核对。当时 doc.rust-lang.org 上的稳定版文档是 1.100.0(构建于 2026-11-09),
tokio 是 1.54.1,tokio-util 是 0.7.20。变化快的事实(async drop、`Forget` trait、`adt_const_params`、非毒化锁)在正文中
都写明了核对时的状态和出处,开工前应再查一次。

**结论先行。**

1. **撤销日志 `acc` 必须是显式的数据结构,由运行时按 LIFO 逐项执行,不能交给 `Drop`。** 原因有四:`Drop` 不能 `await`,
   而 `L-Undo` 的 `USpawn` 情形和守卫 `¬held` 都要等别的 fiber;守卫是跨 fiber 的全局条件,`Drop` 只看得到自己;
   `Vec` 不保证元素的析构顺序,连 LIFO 都要自己写;`mem::forget` 是安全函数,析构不保证运行。`Drop` 只适合做兜底。
   好在演算本来就把 `acc` 放在运行时一侧(DESIGN D6:"累加器归 fiber 独占"),插件代码碰不到撤销项,
   所以 leakpocalypse 那一类问题在这里不涉及内存安全,只涉及"运行时自己有没有把日志执行完"。
2. **Cordis 的结构化是"注册表驱动"的,不是"词法作用域驱动"的,所以 Rust 的作用域任务难题(scoped task trilemma)
   不挡路。** fiber 都是 `'static` 的任务,由运行时持有;父子关系、依赖关系记在注册表 `F` 与绑定 `B` 里,
   等待由运行时的卸载循环完成(`parent_waits_child`、`unload_waits`)。这等于放弃了三难中的"借用",换来并发与并行,
   而结构由运行时的不变量保证,不靠析构。async drop(2026-11 仍是 nightly 实验特性)对这个设计不是必需的。
3. **async 取消(drop future)正好对应 D6 的"放弃",前提是"提交服务操作"与"压入撤销项"在同一个同步片段内完成。**
   这样 future 在任何 `.await` 处被 drop,对演算都是"这一步还没走"或"这一步已经走完",没有半步。
   tokio 对 cancel safety 的定义("drop 后重新创建是 no-op")正是 `prepare` 阶段需要满足的条件。
4. **插件局部的义务(`Op k` 满足 `k ∈ d ∪ p`、提供状态检查 `ProvOK`)可以放进 Rust 类型系统;全局义务
   (`p` 两两不相交、`Above` 无环、`Bounded`)不行,仍是插入时或链接时的检查。** 线性类型的缺失对差异 q 影响不大:
   需要的是"启动时 spawn 的子 fiber 不暴露 dispose",这是仿射、甚至是"不给句柄",Rust 现有的所有权就能表达。
5. **fiber、pid、令牌都用单调递增、从不复用的 `u64`。** 演算的若干不变量(`wf_names`、`wf_pids`、`Inv2` 的 pid 互异、
   `Prov` 的令牌互异)依赖新鲜性;代际索引(slotmap 的版本号 2^31 次后回绕)和指针身份(`Arc::ptr_eq`)都可能出现 ABA。

## 1. 领域概览

### 1.1 R1:`Drop`、RAII 与泄漏

**析构顺序。** Rust 参考手册规定:一个作用域内的变量按声明的**逆序**析构;结构体字段按**声明顺序**析构;
数组与拥有的切片从第一个元素到最后一个析构。标准库对 `Vec` 另有说明:当前**不保证**元素的析构顺序,
"这个顺序过去改过,将来还可能改"(`Vec` 文档 Guarantees 一节)。所以"把撤销项压进 `Vec`,靠 `Vec` 的析构撤销"
连 LIFO 都得不到保证,更不用说其他条件。

**析构不保证运行。** Rust 1.0 之前,`thread::scoped` 返回一个 `JoinGuard`,它的析构阻塞父线程直到子线程结束,
子线程因此可以安全地借用父线程栈上的数据。Rust issue #24292 指出,用 `Rc` 环可以让 guard 永不析构,
于是父线程释放数据时子线程仍在用,出现释放后使用。Beingessner 2015 年的文章 *Pre-Pooping Your Pants With Rust*
讨论了这件事,社区称之为 leakpocalypse。结局是 RFC 1066:`mem::forget` 改为安全函数,明确"析构不一定运行",
`thread::scoped` 从标准库移除。参考手册现在写明:unsafe 代码不能依赖析构运行来保证安全;`process::exit`、
`process::abort` 以及 `panic = abort` 时析构都不运行。Rustonomicon 的 Leaking 一节把应对办法称为
"泄漏放大"(leak amplification):让泄漏只导致更多泄漏,而不是不安全,例子是 `vec::Drain` 一开始就把长度置零。
作用域线程后来以闭包的形式回到标准库(RFC 3151,Rust 1.63 稳定的 `std::thread::scope`):
`scope` 在返回前 join 所有子线程,不依赖任何 guard 的析构。

**`Drop` 不能失败,也不能 async。** `Drop::drop(&mut self)` 没有返回值。文档说实现应避免 panic:`drop` 可能在
panic 展开时被调用,此时再 panic("双重 panic")很可能中止进程。rustc 的测试与 RFC 3288 的描述一致:展开过程中
从析构里逃出的 panic 会中止进程(输出 "panic in a destructor during cleanup")。`Drop` 也不能 `await`。
async 版本 `std::future::AsyncDrop`(签名 `async fn drop(self: Pin<&mut Self>)`)在 2026-11 仍是 nightly 实验 API,
特性门 `async_drop`,追踪 issue #126482;该 issue 仍开着,`dyn Trait` 的情形尚未完成,2026 年 10 月还有人报告
async drop glue 的 `Send` 推断等问题(#164706、#164842)。

**线性与"保证析构"的路线。** Matsakis 2023 年的 *Must move types* 提出 `?Drop` 约束:这类值离开作用域前必须被移走
或解构。Wuyts 同年的 *Linear Types One-Pager* 把线性重新表述为"析构保证运行",提出不安全的自动 trait `Leak`
(也叫 `Forget`),默认加在所有约束上,`?Leak` 放宽。boats 2024 年的 *Asynchronous clean-up* 认为 async 析构
"不会是铁的保证",建议先做 `poll_cancel` 与 `do … final` 块。Rust 2026 年的项目目标 *Immobile types and guaranteed
destructors*(rust-lang/goals#635)把 `Move` 与 `Forget` 两个 trait 列为 2026–2027 的工作;`Forget` 的追踪 issue
#165370 于 2026-11-02 开出,页面写明"还没有实现",beta 文档中已有 `pub unsafe auto trait Forget`(特性门
`forget_trait`),说明 `?Forget` 类型的析构"保证运行"。所以直到本文核对时,稳定 Rust 里没有线性类型,
也没有保证运行的析构。

### 1.2 R2:共享服务状态

- `Arc<T>` 共享所有权,`Weak<T>` 不让值存活,`upgrade` 在值已被析构后返回 `None`。
- `Arc::strong_count` 文档的原话是:别的线程随时可能改变强引用计数,包括在调用之后、依据结果行动之前。
  `Arc::into_inner`(1.70 稳定)保证对所有克隆各调用一次时恰好有一次拿到内部值。
- 内部可变性:`Mutex`、`RwLock`(标准库的版本会在持锁线程 panic 时"毒化");不毒化的 `std::sync::nonpoison::Mutex`
  仍是 nightly(特性门 `nonpoison_mutex`,追踪 issue #134645,2026-10-13 的 libs 会议仍在讨论)。
- `arc-swap`(1.9.5):原子地替换一个 `Arc`,读者不加锁,适合读多写少、偶尔整体替换的数据。
- 代际索引:Catherine West 在 RustConf 2018 的闭幕演讲中推广了"generational index":槽位复用,代数加一,
  旧索引不会匹配新实体。`slotmap` 是现在的主流实现:键是(索引,版本),版本匹配才有效;同一槽位删除插入
  2^31 次后版本回绕,旧键理论上可能匹配新元素。`generational-arena` 已被 RUSTSEC-2024-0014 标为不再维护,
  公告建议改用 slotmap。

### 1.3 R3/R4:async 取消、cancel safety 与结构化并发

**取消就是 drop。** Rust 的 future 是惰性的,不再 poll、把它 drop 掉就是取消;取消只能发生在 `.await` 处,
两个 `.await` 之间的代码不会被打断(Wuyts, *Async Cancellation I*)。tokio 的任务模块文档:`abort` 之后任务在下一个
让出点停下,所有局部变量的析构都会运行;任务可能在 abort 生效前正常完成。`JoinHandle` 被 drop 时任务被**分离**
而不是取消;`spawn_blocking` 的任务不能 abort。

**cancel safety。** tokio `select!` 文档的定义:一个尚未完成的 future,drop 掉再重新创建必须是 no-op。
`mpsc::Receiver::recv`、`TcpListener::accept`、`AsyncReadExt::read` 等是 cancel safe 的;`read_exact`、`write_all`
会丢数据;`tokio::sync::Mutex::lock`、`RwLock::read/write`、`Semaphore::acquire`、`Notify::notified` 因为公平队列,
drop 后会丢掉排队位置。Oxide 的 RFD 400(Rain Paharia,*Dealing with cancel safety in async Rust*)建议:尽量写成
cancel safe;不 abort 任务,改用显式的协作式取消;把复杂操作拆成 cancel safe 的一步加不可取消的一步
(例如先 reserve 再 send)。

**作用域任务的不健全。** Mandry 2023 年的 *A formulation for scoped tasks in Rust* 指出,async 版的 `thread::scope`
做不到:future 可以在任意 `.await` 处被 drop,也可以被 forget,作用域无法保证子任务先于被借用的数据结束。
boats 同年的 *The Scoped Task trilemma* 把它归结为三选二:并发(子任务与父任务同时推进)、可并行、无同步地借用父任务的数据。
`thread::scope` 放弃并发(父线程阻塞),`tokio::spawn` 放弃借用(`'static`),`select!`/`FuturesUnordered` 放弃并行。

**现有的结构化工具。**

| 工具 | 行为 | 与演算有关的点 |
|---|---|---|
| `tokio::task::JoinSet` | drop 时**立即 abort** 全部任务;`shutdown` = `abort_all` 后逐个 `join_next`;`join_next` 是 cancel safe 的 | abort 不是"请求退出后等待" |
| `tokio_util::task::TaskTracker` | `close` 后 `wait` 等全部任务结束;drop 不 abort;不保存返回值 | 只等不取消,适合"等子 fiber 被移除" |
| `tokio_util::sync::CancellationToken` | `child_token`:父取消则子取消,子取消不影响父;`cancelled()` 是 cancel safe 的;`drop_guard` | 取消请求沿父子树传播,对应 `τ` 标记 |
| `moro`(0.4.0) | 仿 Trio nursery 的 `async_scope!`,子任务可借用栈上数据;只并发不并行;0.4 支持 `terminate` | 三难中放弃并行的一支 |
| `async-scoped`(0.9.0) | `scope_and_block` 安全但阻塞线程;`scope_and_collect`、`scope` 是 `unsafe`,因为返回的 future 可能被 forget | leakpocalypse 在 async 中的重现 |

Rust 2026 年的 async 路线图(*Just add async*)没有给 async drop、作用域任务或取消单独立项,只说保证析构的目标
是为了"安全的作用域 spawn",结构化并发列为"更难的问题"。

### 1.4 R5:类型状态、类型级集合与宏

- **类型状态模式**(Biffle, *The Typestate Pattern in Rust*,2019):把对象的运行期状态编码进类型,操作消耗 `self`
  返回新状态的值,误用不能通过编译。Embedded Rust Book 指出 builder 就是类型状态。
- **类型级集合**:稳定 Rust 的 const 泛型只支持整数、`bool`、`char`。用结构体、字符串做 const 参数要
  `adt_const_params`(追踪 issue #95174)或拆出的 `min_adt_const_params`(#154042),2026-11 仍未稳定;
  2026 年的 *Full Const Generics* 目标把"稳定 `adt_const_params`"列为工作项。所以键集合只能用**类型**表示:
  每个服务键一个标记类型,集合是类型级列表(HList)。frunk 的 `Plucker`/`Sculptor` 用幻影索引类型 `Here`/`There<T>`
  做"按类型取出元素",索引由类型推断求出,这正是"键 ∈ 集合"的证据。
- **过程宏**可以从 `#[plugin(inject(A, B), provide(C))]` 这类声明生成标记类型和约束,但宏只看到一个 crate 的语法,
  看不到别的插件,所以做不了跨插件的检查。
- **`#[must_use]`** 由 `unused_must_use` lint 检查,默认级别是 warn;`let _ = x;` 就能消掉,`mem::forget` 也不受影响。
  它是"别忘了用",不是线性。

### 1.5 R7:身份与 ABA

ABA:一个位置的值从 A 变成 B 又变回 A,观察者以为没变。在身份层面,就是"旧的名字指向了新的对象"。
复用槽位的代际索引靠版本号缓解,版本回绕后理论上仍可能发生(slotmap 文档称"极不可能");
按地址比较身份(`Arc::ptr_eq`、`*const T`)时,旧对象释放、新对象分配在同一地址,同样是 ABA。
单调递增、从不复用的 `u64` 计数器在实践中没有这个问题(每纳秒分配一个也要几百年才回绕)。

## 2. 对照表

"关系"一列:**精确** = 语义一致,可以直接承载;**近似** = 能承载,但有可说明的差别;**形似** = 名字或形状相近,
不能直接用;**冲突** = 语言机制与演算的要求相反,必须绕开。

### 2.1 R1:撤销日志

| Rust 机制 | 演算 | 关系 | 说明 |
|---|---|---|---|
| 局部变量逆序析构 | 单个 fiber 内 `acc` 的 LIFO(`L-Undo` 从表头开始;差异 e) | 形似 | 方向一致,但只对词法作用域内的变量成立;`acc` 是跨多次 `L-Step` 动态增长的,变量放不下 |
| `Vec<T>` 的析构 | `acc : list Undo` 整体撤销 | 冲突 | `Vec` 不保证元素析构顺序;要 LIFO 必须显式 `while let Some(u) = acc.pop()` |
| `Drop::drop(&mut self)` 不能失败 | 逆是全函数(差异 f) | 近似 | 签名上一致;但 panic 仍可能发生,展开中再 panic 就中止。运行时应 `catch_unwind` 每个逆,失败记日志后继续,与 Cordis 相同,越出保证范围 |
| `Drop` 不能 `await` | `L-Undo` 的 `USpawn m` 要求 `m ∉ dom F`(`parent_waits_child`);守卫 `¬held`(`unload_waits`、`unload_blocked`) | 冲突 | 这两处都是"等别的 fiber",只能在 async 的卸载循环里做 |
| `Drop` 只看到自己 | `held n acc` 读的是全体已安装 fiber 的 ω | 冲突 | 守卫是全局条件,必须由持有 `F` 与 `B` 的一方判断 |
| `mem::forget` 安全,析构不保证运行(RFC 1066) | `recovery_exact`、`effect_exact` 要求每个撤销项最终都被执行 | 近似 | 只要撤销项不交给插件代码,forget 只可能是运行时自己的 bug;插件拿到的资源句柄(D6 的 `prepare` 里起的进程、文件)不在 `acc` 中,本来就越出保证 |
| `thread::scope`:返回前 join,不靠 guard | `L-RetireChild` 后等子 fiber 移除 | 近似 | 都是"结构由控制者保证,不由析构保证";`scope` 是词法的,Cordis 是注册表驱动的 |
| 泄漏放大(`Drain` 先把长度置零) | `L-Undo` 遇到绑定已不存在的 `UOp` 时不做任何事(RULES 第 8 节第 2 条) | 形似 | 都是"出意外时退化为无害的状态",但后者按不变量不会发生 |
| panic 展开时运行析构 | `Fail ξ`:`L-Step` 进入 `Unloading acc ω (Some ξ)` | 近似 | 插件体 panic 应被 `catch_unwind` 转成 `Fail`,然后**由卸载循环**按 LIFO 撤销,而不是在展开中撤销 |

### 2.2 R2:共享服务与依赖者的引用

| Rust 机制 | 演算 | 关系 | 说明 |
|---|---|---|---|
| `Arc<Mutex<S>>` / 单线程执行器上的 `RefCell<S>` | Binding `⟨pid, owner, s⟩` 中被提供者与依赖者共同读写的 `s` | 近似 | 逻辑原子性(D6)要求操作的提交在一个临界区内完成且不跨 `.await`;标准库 `MutexGuard` 不是 `Send`,在多线程 tokio 上跨 `.await` 持有它的 future 不能 `tokio::spawn`,编译器顺带挡住了一部分违例 |
| `tokio::sync::Mutex` 跨 `await` 持锁 | 无 | 冲突 | D6 已说明:跨 `await` 持有的锁可能与 `held`、`USpawn` 两处等待形成演算看不到的死锁;而且它的 `lock` 不是 cancel safe 的 |
| `ArcSwap<S>` 整体替换 | 服务操作 `run a tok s = Some (s', g, o)` 写回 `s'` | 近似 | 读多写少时合适;但"读-改-写"要用比较交换循环,逆 `g` 也要作用在当时的状态上,多个写者时仍需串行化提交 |
| `Weak<S>`,`upgrade` 可能为 `None` | 依赖者的 ω(k) = pid;`provider_outlives` | 形似 | 演算保证依赖者已安装期间 pid 对应的绑定一直存在,`upgrade` 的 `None` 分支是死代码;`Weak` 也不能阻止撤回,守卫要另做 |
| `Arc::strong_count == 1` 作为"没人用了" | `¬held`:没有 `m ≠ n` 满足 `resolves m pid` | 冲突 | 计数包含临时克隆(操作执行中的、日志中的),不区分"已安装的依赖者";计数随时变化,判断与行动之间有竞态。`resolves` 是关于 ω 的谓词,应维护显式的反向索引 |
| 反向索引 `dependents: pid → 集合` | `resolves m pid := installed m ∧ ∃ k ∈ d. ωₘ k = pid` | 精确(需证) | Cordis 的做法(DESIGN 差异 g);在 `L-Begin` 加入、`L-Unloaded` 移除,不变量"索引 = resolves"可以在 Rocq 里证,见课题 L3 |
| `Arc::into_inner` 恰有一次成功 | `withdraw_waits`:撤回时没有其他已安装 fiber 解析它 | 近似 | 可作调试断言:撤回 provide 时运行时持有的应是最后一个强引用 |
| 控制层单一所有者(一个 actor 或一把锁保护 `F`、`B`) | DESIGN D6:每条控制规则在一个同步片段内完成 | 精确 | 在 Rust 中表现为"控制状态只被一个任务持有,规则是对它的 `&mut` 方法" |

### 2.3 R3/R4:等待、取消与落地

| Rust 机制 | 演算 | 关系 | 说明 |
|---|---|---|---|
| drop 一个 future(取消只在 `.await` 处) | `L-Divert`:Loading → Unloading;D6"放弃" | 精确(有前提) | 前提:服务操作的提交与 `acc.push(undo)` 在两个 `.await` 之间完成。于是 drop 时要么这一步没走,要么已走完并留下撤销项 |
| 被 drop 前已提交的操作 | `L-Step` 在 target 变化后仍可走(落地);`step_coherent`、`divert_when_changed` | 精确 | 运行时选择继续 poll 到下一个提交点再 drop,就是"落地";立即 drop 就是"放弃"。两种都在演算之内 |
| tokio 的 cancel safety 定义 | D6 `prepare`:可以 `await`,不碰 `S` | 近似 | cancel safe 是"drop 后重建是 no-op",`prepare` 要求的是"对服务状态 `S` 没有效果";对外部世界的副作用两者都不管(D6"得不到的"第 3 条) |
| RFD 400 的"拆成 cancel safe 一步加不可取消一步" | D6 的 `prepare`/`commit` 两段 | 精确 | 同一个设计;`commit` 是同步纯函数,天然不可取消 |
| `JoinSet` drop 时 abort | `L-RetireChild` 置 `τₘ` 后等待 | 形似 | abort 是强行在下一个 `.await` 停下,不运行子 fiber 的卸载;演算要求子 fiber 自己走完 `Unloading` |
| `CancellationToken::child_token` | `τ`(已请求移除)沿父子传播 | 近似 | 演算中父卸载时逐个置子的 `τ`(`L-RetireChild`),不是一次广播;且子的 target 变 ⊥ 后自己走卸载 |
| `TaskTracker::close` + `wait` | `USpawn m` 等 `m ∉ dom F` | 近似 | 只等不取消,与"先请求再等待"的后半段相同 |
| `thread::scope`、Trio nursery、`moro` | `wf_parent` + `parent_waits_child`(concurrency.md 判为精确) | 近似 | Cordis 的"作用域"是 `acc` 中 `USpawn m` 以上的后缀,由运行时的注册表维护,不是词法块 |
| scoped task trilemma | — | 不适用 | fiber 不借用父 fiber 的栈数据,只经服务交互;放弃"借用"一项,三难不成立 |
| `AsyncDrop`(nightly) | 可等待的撤销 | 形似 | 即使稳定也不保证运行(forget、同步上下文中析构);而且仍是局部的,不能判断守卫 |
| `abort` 后局部变量析构运行 | `Unloading` 没有出口回到 Loading/Active(concurrency.md:清理不可取消) | 冲突 | 若卸载循环本身被 abort,撤销做到一半就停了。卸载循环必须不可被外部取消:放在运行时自有任务里,不放进可被 `select!` 掉的分支 |

### 2.4 R5:声明与类型

| Rust 机制 | 演算 | 关系 | 说明 |
|---|---|---|---|
| 关联类型 `type Deps: KeySet; type Provides: KeySet;` | 组件的 `d`、`p` | 精确 | 静态声明,与 DESIGN 差异 c"组件静态声明 p"一致 |
| `ctx.op::<K>()` 要求 `K: In<Deps ∪ Provided>` | 组件义务:`Op k` 满足 `k ∈ d ∪ p` | 精确 | RULES 第 1 节的静态义务;Rocq 中依赖键的解析由 `wf_view`、`wf_view_keys` 保证 |
| 类型状态 `Ctx<S>`,`provide::<K>(self) -> Ctx<Cons<K, S>>`,要求 `K: In<Provides>`、`K: NotIn<S>` | `ProvOK d p S`(session-types 课题 B,README 第一梯队课题 1) | 近似,可做成精确 | 排除 `EConflict`(重复 provide 或 provide 不在 `p` 中的键) |
| 对自己的键操作要求 `K: In<S>` | `Op k` 对自己的键要求 owner 为 `n`,否则 `EUnresolved` | 精确 | 同上 |
| 收尾 `ctx.done()` 要求 `Provides ⊆ S` | `AllDoneProv`、`Confluence.Total`、`Summary.TotalProv` | 近似 | Rust 的 `if`/`match` 两支必须同类型,所以分支汇合处的 `S` 必须一致,比 `ProvOK` 对每个 `o` 分别量化更保守;循环体里不能改变类型,provide 不能出现在循环中(本来每个键至多一次,`wf_uprov_unique`) |
| `Fail` 路径(`?`、提前 `return Err`) | `PFail` 总成立 | 精确 | 错误路径不需要满足 `Provides ⊆ S` |
| 过程宏生成键标记类型 | 键 `K` 相等可判定 | 近似 | 标记类型的身份由路径决定;同名不同 crate 的键要靠路径区分,对应 `Derived.scoped` 的键重命名 |
| 跨插件的 `p` 不相交 | `O-Insert` 的前提;`wf_disjoint` | 冲突(类型层做不到) | 插件独立编译、运行期加载,只能在插入时检查(DESIGN 差异 c 的建议) |
| `Above` 无环、`Bounded` | `progress`、`termination` 的假设 | 冲突(类型层做不到) | 全局性质,宜做成插件清单的链接期检查(README 第一梯队课题 5) |
| 启动时 `spawn` 不返回句柄或返回无 `dispose` 的令牌 | `SLInv`;差异 q;session-types 课题 C | 精确 | Rust 不需要线性:不给句柄就没人能 dispose;TS 版做不到真正强制,Rust 可以 |
| 反应中创建的子 fiber 返回 `ChildHandle`,`dispose(self)` | `O-React` + `O-Dispose m`;`effect_exact` | 近似 | 仿射句柄够用:忘了 dispose,父卸载时 `USpawn` 仍会回收 |
| `#[must_use]` | 无 | 形似 | 只是 warn,不能表达"必须 dispose";演算也不需要 |
| `Forget` trait(nightly 特性门,尚无实现) | 若要求"句柄必须 dispose" | 形似 | 本设计不依赖它 |

### 2.5 R7:身份

| Rust 机制 | 演算 | 关系 | 说明 |
|---|---|---|---|
| 单调 `u64` 计数器 | `next`;`O-Insert`、`Spawn`、`Provide`、`Op` 都取 `next` 并加一 | 精确 | 名字、pid、令牌共用一个计数器,与 `Calculus.v` 一致 |
| `HashMap<u64, Fiber>` / `BTreeMap` | `F : N ⇀ Fiber`,`B : K ⇀ Binding` | 精确 | 删除即 `L-Remove`;键从不复用 |
| slotmap 的(索引,版本)键 | 名字的新鲜性:`wf_names`(名字 < `next`)、`Inv2`(pid 互异) | 近似 | 版本回绕(2^31)后可能 ABA;若用 slotmap 做存储,应另存单调 id 并在访问时比对 |
| `Arc::ptr_eq` 作为钩子身份 | `Tok`:"事件钩子这类生成出来的身份(JS 中由对象身份充当)"(RULES 第 0 节) | 冲突 | 地址可复用;按身份注销(差异 p 的上游修复)在 Rust 中应以令牌 `u64` 为身份 |
| 依赖者持有 `pid: u64` | ω : d → pid;差异 b | 精确 | 提供者撤掉再重新提供时 pid 变,依赖者重新加载,不会拿着过期的 pid 继续运行 |

## 3. 差异

### 3.1 演算要求而 Rust 不直接提供的

1. **可等待、全局受控的撤销。** Rust 的资源纪律是 RAII:每个资源自己负责清理,清理同步、局部、无序可言
   (字段顺序、逆序变量是语言规定,但跨对象没有协调)。演算的撤销是一个**调度问题**:一个 fiber 的撤销项按 LIFO
   串行,其中某些项要等别的 fiber(`USpawn`),整体要等依赖者(`held`)。这只能由运行时的事件循环来做。
   设计草图(只示意结构):

   ```rust
   enum Undo { Op { pid: Pid, tok: Tok, inv: Box<dyn FnOnce(&mut S) + Send> },
               Prov { key: Key, pid: Pid },
               Spawn { child: FiberId } }

   // 运行时持有全部 Fiber;卸载是控制者的一个循环,不是析构
   async fn unload(rt: &Runtime, n: FiberId) {
       rt.wait_until(|st| !st.held(n)).await;           // 守卫:等依赖者离开
       while let Some(u) = rt.with(|st| st.acc_mut(n).pop()) {
           match u {
               Undo::Spawn { child } => { rt.retire(child); rt.wait_removed(child).await; }
               u => rt.with(|st| st.apply_undo(u)),      // 同步、原子
           }
       }
   }
   ```

   `held` 在整个卸载期间一直为假:提供者一进入 Unloading,它的服务就对新解析不可见(`visible` 只计 Active),
   已有依赖者只会减少,`acc` 中的 `UProv` 也只会减少。所以只在开头等一次即可。这是规则的推论,
   仓库里还没有对应的引理(规则在每次 `L-Undo` 都检查 `¬held`),可作为课题 L3 的附带引理 `held_stable` 一并证明。

2. **清理不可取消。** async Rust 中任何 future 都可能被 drop。卸载循环一旦被 drop,撤销就停在中间,
   而演算里 `Unloading` 只能走到 `Inactive`。所以卸载循环要放在运行时自己 spawn 的任务里,外部只能通过
   `τ`/target 请求,不能 abort 它。这一点在 Rust 里要靠约定和 API 形状保证(不暴露卸载 future),类型系统帮不上。

3. **全局义务。** `p` 不相交、`Above` 无环、程序有界,都不是单个插件的类型能表达的。

### 3.2 Rust 有而演算没有的

1. **真并行。** 演算是交错语义;DESIGN D6 已说明若服务跨线程共享,"操作是原子步"就是"服务操作可线性化"。
   Rust 的 `Send`/`Sync` 能在编译期挡住一部分数据竞争,但挡不住逻辑上的非原子(先读、`await`、再按旧值写回)。
   后者仍需 D6 的 `prepare`/`commit` 形状。
2. **panic。** 演算只有 `Fail ξ`。Rust 插件体与服务操作都可能 panic。建议:插件体的 panic 经 `catch_unwind`
   转为 `Fail`(`L-Step` 的 `Fail` 情形,进入 `Unloading acc ω (Some ξ)`);`commit` 中 panic 时服务状态可能已被部分修改,
   违反逻辑原子性,应视为服务作者违约,运行时至少要毒化这个绑定;逆中 panic 越出保证(差异 f),记日志后继续,
   不能让它在展开中再 panic 导致整个进程中止。
3. **析构本身。** 插件在 `prepare` 中持有的 Rust 资源(文件、连接)会由自己的 `Drop` 回收,这是演算之外但
   对"外部世界的恢复"(D6"得不到的"第 3 条)有帮助的部分。它和 `acc` 是两套机制:前者回收内存与 OS 资源,
   后者撤销共享服务上的效应。

### 3.3 一个容易误判的地方:leakpocalypse 与本设计的关系

leakpocalypse 的问题是**安全性依赖析构**:guard 被 forget 后出现释放后使用。本设计里,撤销日志不保护内存安全,
只保护功能正确性(`recovery_exact`)。只要 (a) 撤销项只存在于运行时持有的 `acc` 里,(b) 插件只拿到不含撤销责任的句柄,
forget 就无从发生。需要警惕的是相反的设计:把"provide 的撤回"做成 `ProvideGuard` 交给插件,在 `Drop` 中撤回。
那样插件 forget 掉 guard,服务就永远不撤;guard 的析构顺序由插件的变量布局决定,不再是 LIFO;
而且撤回要等依赖者,`Drop` 等不了。这正是 async-scoped 把 `scope_and_collect` 标为 `unsafe` 的同一个原因。

### 3.4 线性类型缺失的实际影响

session-types 课题 C 认为启动时 spawn 的子 fiber 句柄应是"线性能力",TS 无法强制。细看 `SLInv` 要排除的是
"第三方 dispose 启动时的子 fiber",需要的是**不能被 dispose**,而不是**必须被使用**。前者在 Rust 中用
"不返回句柄"或"返回不带 `dispose` 方法、不可 `Clone` 的令牌"就能做到,不需要线性类型。线性类型(必须消费)
只在想要"插件必须显式 dispose 某个句柄"时才有用,而演算由 `USpawn` 兜底,不需要这个要求。
所以 `Forget` trait 是否稳定,对本设计没有影响。

## 4. 候选课题

### L1 Rust 类型状态版的提供状态检查(中)

- **目标。** 把 `ProvOK`(session-types 课题 B、README 第一梯队课题 1)落到 Rust:插件体中重复 provide、
  provide 不在 `p` 中的键、provide 之前操作自己的键、某条到 `Done` 的路径没提供全部 `p`,都不能通过编译。
- **做法。**
  1. 先完成 Rocq 侧的 `ProvOK` 与 `provok_total`、`provok_no_self_fail`(课题 B 原计划)。
  2. 定义 Rust 草图:键是标记类型;`KeySet` 用 HList;成员证据用 frunk 式的幻影索引(`Here`/`There<I>`);
     `Ctx<S>` 的 `provide`、`op`、`done` 带约束。过程宏从 `#[plugin(inject(..), provide(..))]` 生成 `Deps`、`Provides`。
  3. 写一份"Rust 可接受 ⊆ ProvOK"的论证:Rust 的分支汇合要求同一类型,所以接受的程序满足一个更强的判断
     `ProvOK₌`(分支后的已提供集合相同);在 Rocq 中定义 `ProvOK₌` 并证明 `ProvOK₌ → ProvOK`。
  4. 用 dsh 中若干真实插件的启动逻辑手工翻译,检查表达力:有没有"分支中各自 provide 不同键、汇合后再统一"的写法被拒。
- **预期产出。** Rocq 中的 `ProvOK₌` 与蕴涵引理;一份 Rust 草图(几十行,只验证能否编译通过,不是实现);
  对表达力限制的记录。
- **风险。** 类型级集合的错误信息很差,可用性可能不如运行期检查;async 插件体中把 `Ctx<S>` 当值传递,
  遇到 `select!` 等组合子时类型会很难写。若表达力不够,退回"宏做语法检查 + 运行期 `debug_assert`"。
- **工作量。** 中(Rocq 部分小,Rust 草图与表达力评估占大头)。

### L2 取消即放弃:提交与压栈原子时,任意 drop 点都是演算的执行(中)

- **目标。** 把 2.3 节"drop future = `L-Divert`"的对应写成一个可检查的陈述:只要提交服务操作与压入撤销项在
  同一个原子片段中,运行时在任意 `.await` 处 drop 插件体,所得执行都对应演算的一个执行。它是 concurrency 课题 C3
  在 Rust 取消语义下的具体化。
- **做法。**
  1. 在 Rocq 中给一个细粒度语义:fiber 处于"等待 prepare"的中间态时,运行时可以选择"继续"或"丢弃"(drop);
     提交是一步,同时写 `B` 与 `acc`。另加一个**反例**语义:提交与压栈分成两步,中间可以被丢弃。
  2. 证明前者的每个执行对应演算的执行(中间态映射为"这一步还没走");对后者构造反例:
     丢在两步之间时,服务状态已改、撤销项未记录,`recovery_exact` 的结论不成立。
  3. 在文档中给出对应的 Rust 规则:`commit` 为同步函数;运行时在同一个 `with(|st| ..)` 闭包中执行 `commit` 与 `push`;
     插件体只能在 `prepare` 中 `await`。
- **预期产出。** `theories/Ext/Cancel.v`(名字待定):模拟定理与反例;D6"在途操作"一节可以引用它说明
  Rust 的取消模型与演算一致。
- **风险。** 与 C3 重叠,宜合并做;若 C3 已完成,本课题只剩反例与 Rust 规则的说明。
- **工作量。** 中;与 C3 合并后增量为小。

### L3 守卫的可计算形式:反向索引与 `resolves` 一致(小)

- **目标。** 证明运行时维护的反向索引 `dependents : pid → list N`(`L-Begin` 时加入,`L-Unloaded` 时移除)
  在可达状态上恰好等于 `{m | resolves m pid}`,于是 `held` 可以用索引是否为空来判断,不用扫描全体 fiber,
  也不用 `Arc::strong_count`。顺带证明 `held_stable`:Unloading 的 fiber 一旦 `¬held`,此后直到卸载完毕一直 `¬held`,
  于是卸载循环只需在开头等待一次(3.1 节第 1 条)。
- **做法。** 在状态上加一个鬼字段(或在 `Ext/` 中给扩展状态),给出更新规则;不变量 `DepIdx γ := ∀ pid m,
  In m (dependents γ pid) ↔ (m ≠ owner ∧ resolves γ m pid)`;证明它被每条规则保持(依赖 `Ordering.fiber_step`:
  已安装期间 ω 不变,以及 `WF` 的 `wf_view`)。然后证 `held_fast n acc ↔ held n acc`。
- **预期产出。** 一个小文件与两条引理;Rust 运行时设计中 `held` 的实现依据。Cordis 的 `dependents` 集合
  (DESIGN 差异 g)也由此得到形式依据。
- **风险。** 低。Loading 的 fiber 也算已安装(`installed` 只排除 Inactive),索引要在 `L-Begin` 时就加入,
  而不是 `Done` 时,容易写错,正是该证的地方。
- **工作量。** 小。

### L4 启动子 fiber 与反应子 fiber 的句柄 API(小)

- **目标。** 用 Rust 的所有权把差异 q 与 session-types 课题 C 的约定变成 API 形状:启动程序中的 `spawn` 不返回可 dispose 的句柄;
  反应(`O-React`)中创建的子 fiber 返回仿射的 `ChildHandle`,`dispose(self)` 消费它。
- **做法。**
  1. 写出两种上下文类型的草图:`BootCtx` 的 `spawn` 返回 `()`(或一个只能用于查询的 `ChildId`);
     `ReactCtx` 的 `spawn` 返回 `ChildHandle`,不实现 `Clone`。
  2. 在 Rocq 一侧,把"编排者只 dispose 根 fiber 或 `O-React` 生成的子 fiber"写成编排输入的谓词,
     对照 `Dynamic.sl_dispose` 的前提,说明 `SLInv` 在这种输入下保持(只有根上的 dispose 与反应子 fiber 上的 dispose)。
     注意合流定理本身不含 `O-React`,所以这一条落在恢复精确性(`effect_exact`)与 `SLInv` 的保持上,不扩大合流的范围。
  3. 列出 dsh 中直接 dispose 子 fiber 的典型写法(差异 q 的例子),判定它们在新 API 下属于哪一类。
- **预期产出。** API 草图;一条说明性引理或对已有引理前提的整理;迁移指南的要点。
- **风险。** 低。若 dsh 有"启动时 spawn、之后单独回收"的写法,需要改成反应或 `ctx.effect`,这是迁移成本,不是技术风险。
- **工作量。** 小。

### L5 身份层的新鲜性清单(小)

- **目标。** 列出演算中所有依赖"名字、pid、令牌从不复用"的定理与不变量,作为 Rust 实现选择 id 方案的依据,
  并判断能否放宽为"代际索引在回绕前有效"。
- **做法。** 在 `theories/` 中检索用到 `wf_names`、`wf_pids`、`Inv2` 的 pid 互异、`Prov` 的令牌互异、
  `new_fiber`(新 fiber 的名字为当时的计数器)的证明;对每一处写明复用会破坏什么(例如令牌复用使 `RevertIndep`
  的"令牌不同"前提失效,`recovery_exact` 不再适用)。结论写成一段设计说明:Rust 实现用单调 `u64`,
  slotmap 只作存储并比对单调 id。
- **预期产出。** 一张表与一段说明,放在 Rust 版设计文档里;不需要新的证明。
- **风险。** 低。价值在于防止实现时出于性能改用复用 id。
- **工作量。** 小。

### 不建议做

- **用 `Drop`/RAII guard 承载撤销日志。** 见 3.3。可以保留一个兜底的 `Drop`:运行时整体关闭时若某个 fiber 的 `acc`
  非空,只记录"未撤销"并报警,不尝试在析构中撤销(那里不能等待,也判断不了守卫)。
- **等 async drop 或 `Forget` 稳定再设计。** 两者在 2026-11 都没有稳定的时间表,本设计也不依赖它们。
- **用 `Arc::strong_count` 实现守卫。** 见 2.2。

## 5. 参考文献

核对日期均为 2026-11-25。"已核实"指在原始页面上核对了标题、作者或维护者、日期或版本;"部分核实"注明缺哪一项。

**语言与标准库文档**

1. The Rust Reference, Destructors 一章(析构顺序;`mem::forget` 与 `ManuallyDrop`;不能依赖析构保证安全)。
   doc.rust-lang.org/reference/destructors.html。已核实。
2. Rust 标准库文档 `std::ops::Drop`(双重 panic"很可能中止")、`std::vec::Vec`(Guarantees:不保证元素析构顺序)、
   `std::sync::Arc`(`strong_count` 的竞态警告;`into_inner` 自 1.70.0)。文档版本 1.100.0(2026-11-09)。已核实。
3. Rust 标准库文档 `std::future::AsyncDrop`(nightly,特性门 `async_drop`);追踪 issue rust-lang/rust#126482
   "Tracking Issue for async drop codegen"(2024-06-14 开出,2026-11 仍开着)。已核实。
4. Rust beta 文档 `std::marker::Forget`(nightly,特性门 `forget_trait`);追踪 issue rust-lang/rust#165370
   (2026-11-02 开出,写明尚无实现)。已核实。
5. Rust 标准库文档 `std::sync::nonpoison`(nightly,特性门 `nonpoison_mutex`,追踪 issue #134645)。已核实;
   2026-10-13 libs 会议纪要只部分核实(来自检索摘要)。
6. The Rustonomicon, Leaking 一节(`Drain`、`Rc`、`thread::scoped`;泄漏放大)。doc.rust-lang.org/nomicon/leaking.html。已核实。
7. Rust 1.63.0 发布公告(`std::thread::scope` 稳定),blog.rust-lang.org,2022-08-11。已核实。
8. Rust Reference, Panic 一章(`-C panic`,`unwind`/`abort`)。已核实。展开中析构 panic 即中止:由 rustc 测试
   `tests/ui/panics/panic-in-cleanup.rs` 与 RFC 3288 的讨论佐证;RFC 3288(rust-lang/rfcs#3288,提议无条件中止)
   的最终结局**未核实**。

**RFC 与项目目标**

9. RFC 1066, Safe `mem::forget`。rust-lang.github.io/rfcs/1066-safe-mem-forget.html;实现 PR rust-lang/rust#25187(2015 年 5 月合并)。已核实。
10. RFC 3151, Scoped threads。rust-lang.github.io/rfcs/3151-scoped-threads.html(正文提到 leakpocalypse)。已核实。
11. Rust Project Goals 2026, *Immobile types and guaranteed destructors*(rust-lang/goals#635;goals.rust-lang.org/2026/move-trait.html),
    2026-09-03 的进展更新。已核实。
12. Rust Project Goals 2026, *Full Const Generics*(goals.rust-lang.org/2026/const-generics.html);Unstable Book 的
    `adt_const_params`(#95174)与 `min_adt_const_params`(#154042)。部分核实:未稳定这一点来自目标页面与 Unstable Book,
    没有逐条查看追踪 issue 的最新评论。
13. Rust Project Goals 2026 路线图 *Just add async*(goals.rust-lang.org/2026/roadmap-just-add-async.html)。已核实。

**文章**

14. Alexis Beingessner. *Pre-Pooping Your Pants With Rust*. 2015-04-27. cglab.ca/~abeinges/blah/everyone-poops。已核实(经检索摘要与 RFC 3151 交叉确认)。
15. Niko Matsakis. *Must move types*. Baby Steps,2023-03-16。已核实。
16. Yoshua Wuyts. *Linear Types One-Pager*. 2023-03-28(2023-05 更新)。已核实。
17. Yoshua Wuyts. *Async Cancellation I*. blog.yoshuawuyts.com/async-cancellation-1/。部分核实:只核对了标题与"取消只在 `.await` 处"的内容,未核对日期。
18. Tyler Mandry. *A formulation for scoped tasks in Rust*. 2023-03-01. tmandry.gitlab.io。已核实。
19. withoutboats. *The Scoped Task trilemma*. 2023-04-08. without.boats。已核实。
20. withoutboats. *Asynchronous clean-up*. 2024-02-24. without.boats。已核实。
21. Cliff Biffle. *The Typestate Pattern in Rust*. 2019-06-05. cliffle.com。部分核实:标题与日期来自索引页和镜像,未打开原文。
22. Catherine West. *My RustConf 2018 Closing Keynote*. 2018-09-14. kyren.github.io(generational index 一节)。已核实。
23. Rain Paharia. *Dealing with cancel safety in async Rust*. Oxide RFD 400。部分核实:标题、作者、状态(Published)已核对,**日期未核实**。

**库**

24. tokio 1.54.1:`select!` 的 Cancellation safety 一节;`task` 模块(abort 在下一个让出点生效,局部变量析构运行);
    `JoinHandle`(drop 即分离;`spawn_blocking` 不能 abort);`JoinSet`(drop 即 abort;`shutdown`)。docs.rs。已核实。
25. tokio-util 0.7.20:`sync::CancellationToken`、`task::TaskTracker`。docs.rs。已核实。
26. moro 0.4.0(Niko Matsakis)。docs.rs。已核实(经 docs.rs 源码页摘要)。
27. async-scoped 0.9.0。docs.rs。已核实。
28. arc-swap 1.9.5。docs.rs。已核实。
29. slotmap(版本号 2^31 次后回绕;`SlotMap`、`DenseSlotMap`、`SecondaryMap`)。docs.rs。部分核实:**未记录版本号**。
30. RUSTSEC-2024-0014:generational-arena 不再维护(2024-02-11)。rustsec.org。已核实。
31. frunk / frunk_core 的 `Plucker`、`Sculptor`、`Here`/`There`。docs.rs。部分核实:在旧版本文档上核对,**当前版本号未核实**。

**未核实条目共 4 处**:RFC 3288 的结局(第 8 条)、RFD 400 的日期(第 23 条)、slotmap 当前版本(第 29 条)、
frunk 当前版本(第 31 条)。另有 4 条部分核实(第 5、12、17、21 条),缺项已在条目中注明。
