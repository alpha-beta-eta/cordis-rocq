# 调研:Rust 版 Cordis

计划见 [PLAN.md](PLAN.md)。三份报告:

- [language.md](language.md):语言机制,即 Rust 的语言特性怎样承载演算;
- [plugins.md](plugins.md):插件形态与 Rust 生态;
- [assurance.md](assurance.md):让 Rust 实现与 Rocq 演算保持一致的手段。

快速变化的事实(版本号、WASI 状态、async drop 是否稳定)都按 2026-11-25 核对,开工前应再查一次。

## 设计结论

1. **撤销日志 `acc` 做成运行时持有的显式数据结构,不交给 `Drop`。** 理由有四:
   - `Drop` 里不能 `await`,而 `L-Undo` 的 `USpawn` 情形和守卫 `¬held` 都要等别的 fiber;
   - 守卫是跨 fiber 的全局条件,`Drop` 只看得到自己;
   - `Vec` 不保证元素的析构顺序;
   - `mem::forget` 是安全函数,析构不一定会运行。

   演算本来就把 `acc` 放在运行时一侧(DESIGN D6),插件碰不到撤销项,所以 leakpocalypse 一类问题在这里不涉及内存安全。
   `Drop` 只用来兜底。([language.md](language.md) 结论 1)

2. **结构由注册表维持,不靠词法作用域。** fiber 是由运行时持有的 `'static` 任务,父子关系和依赖关系记在 `F`、`B` 里。
   所以作用域任务的三难不挡路,也用不着 async drop。async drop 截至 2026-11 仍是 nightly 特性,追踪 issue 是 #126482。
   ([language.md](language.md) 结论 2)

3. **取消一个 future 就是 `L-Divert` 的放弃,前提是"提交服务操作"和"压入撤销项"在同一个同步片段里完成。**
   这样 future 不论在哪个 `.await` 处被 drop,对演算来说都没有"半步"。
   tokio 对 cancel safety 的定义,正是 D6 中 `prepare` 阶段要满足的条件。([language.md](language.md) 结论 3)

4. **身份都用单调递增、永不复用的 `u64`。** 涉及 fiber、pid 和令牌。
   代际索引的版本号会回绕,`Arc::ptr_eq` 也可能出现 ABA 问题。
   演算的 `wf_names`、`wf_pids`、`Inv2`、`Prov` 都依赖新鲜性。([language.md](language.md) 结论 5)

5. **插件按信任程度分四种形态。**

   | 插件 | 形态 | 说明 |
   |---|---|---|
   | 第三方 | WASM 组件(wasmtime,WASI 0.3) | 唯一一种由宿主保证 S1、S3、`Prov` 和 D6 原子性的形态;丢弃 `Store` 就能回收插件的私有状态 |
   | 宿主服务与第一方插件 | 静态链接的 crate | 服务义务集中在这里,由类型系统给出 S1 |
   | 现有的 dsh JS 插件 | 嵌入 JS(`deno_core` 加 `deno_node`) | 过渡方案,保证只到"诚实但出错的作者"级 |
   | 可信的第一方扩展 | 原生动态库 | 加载一次,永不卸载 |

   动态库卸载不可靠,原因包括 TLS 析构、残留线程、静态变量,以及 macOS 上本来就不真正卸载。
   但 `recovery_exact` 讲的是存储,不是代码,所以它在服务状态层面照样成立。
   `Summary.v` 每条前提由谁负责,见 [plugins.md](plugins.md) 3.3 节的分配表。

6. **能力隔离让 S3 类写法写不出来,但不是全部问题都能消除。**
   宿主不能提供"注册之后返回一个 disposer 让插件自己保管"的接口,逆必须由宿主产生、压进宿主的累加器,也就是演算的 `L-Step`。
   能力隔离管不到的有三类:
   - 注册表撞名;
   - 依赖外部世界的启动分支;
   - 插件自己提供的服务的服务义务。

   ([plugins.md](plugins.md) 3.2)

7. **2026 年能做证明的 Rust 工具都不支持 async,Kani 也不支持并发。** 这里说的工具包括 Verus、Aeneas、hax、RefinedRust、Creusot。
   出路是把控制层写成同步、一阶、不含 IO 的纯 step 状态机,外面套单个 actor 的异步外壳。
   这样工具只需证明一个顺序函数等于 `ctl_step`,交错相关的定理仍留在 Rocq 里。
   Rocq 自带的抽取没有 Rust 后端。第三方的 rocq-rust-extraction 0.2.1 支持 Rocq 9.1,但用区域分配管理内存,适合当测试 oracle,不适合当生产核。
   ([assurance.md](assurance.md) 结论)

结论 7 对 Rust 版的架构影响最大:**纯 step 核加异步外壳**这个形状,同时满足以下几方:
- 验证工具,只面对纯核;
- 差分测试,纯核对抽取出的 oracle;
- 结论 3 的取消语义,外壳 drop 时纯核还没被调用;
- 结论 1 的显式撤销日志,日志是纯核状态的一部分。

建议从第一天起就按这个形状组织代码。

## 课题

排序标准同 [../README.md](../README.md):与现有成果的贴合度、收益、工作量。下面的新名字都是报告提议的,仓库里还没有。

### 先做:Rocq 一侧的准备,现在就能做,不依赖 Rust 代码

| # | 课题 | 来源 | 工作量 |
|---|---|---|---|
| 1 | 可计算的精化版 `step`(有限映射、二进制数,去掉鬼字段)与可判定的 `WF` | assurance V1 | 小到中 |
| 2 | 控制投影 `ctl_step`:把服务状态和插件程序从 `step` 中剥出去,作为 Rust 纯核的精确接口 | assurance V2 | 中 |
| 3 | 守卫的可计算形式:用反向索引实现 `¬held`,并证明它与 `resolves` 一致 | language L3 | 小 |
| 4 | 宿主包装把插件义务变成定理:操作预算给出 `Bounded`,`totalize` 给出 `TotalProv`,注册表命名空间给出 `Covers G` | plugins P2 | 小到中 |
| 5 | 代码回收时机:组件最后一个 fiber 移除后,`step` 不再读它的程序 | plugins P3 | 小 |

第 4 项和总调研第一梯队的课题 1(提供状态的静态判断)是同一个目标的两种做法:一个在运行时包装,一个做静态检查。可以一起做。

### 写 Rust 时做

| # | 课题 | 来源 | 工作量 |
|---|---|---|---|
| 6 | Rust 纯核对 oracle 做 lockstep 差分测试(proptest-state-machine、cargo-fuzz);外壳用 shuttle 测交错 | assurance V3 | 中 |
| 7 | 取消即放弃:证明提交与压栈原子时,任何 drop 点都是演算的一次执行,并给出一个反例 | language L2 | 中 |
| 8 | 用 Rust 类型状态实现提供状态检查(`ProvOK`),评估表达力 | language L1 | 中 |
| 9 | 启动时 spawn 的子 fiber 不给 dispose 句柄,反应子 fiber 给仿射句柄 | language L4 | 小 |
| 10 | 用 Kani 有界检查纯核的不变式保持 | assurance V5 | 小 |

### 之后做

- 用 Aeneas 把纯核翻回 Rocq,证明它精化 `ctl_step`(assurance V4,中到大)。Aeneas 的 Coq 后端不够用时,退到它的 Lean 后端或 Verus。
- 演算的 WIT 映射加最小 wasmtime 宿主,和抽取出的 `step` 做差分测试(plugins P1,中到大)。
- 审计过的插件在嵌入 JS 宿主中能否运行的实验(plugins P4,中)。

## 可靠性说明

- **未核实条目。** 三份报告标为未核实的分别有 4、7、13 条。assurance 的 13 条多数是工具特性表中的空格,例如某工具是否支持内部可变性,不是文献书目。各条都已在报告中注明。
- **抽查结果。** 我另外抽查了两项:WASI 0.3.0 于 2026-06-11 发布;rocq-rust-extraction 0.2.1 依赖 Rocq 9.1 范围。两项都属实。
- **定理名。** 报告里被当作已有定理引用的 Rocq 名字都在仓库中。查不到的名字要么是 Rust API(如 `strong_count`、`join_next`),要么是提议的新名字(如 `ctl_step`、`step_fm`、`held_stable`)。
