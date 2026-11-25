# 调研计划:Cordis 演算与 PL 技术的结合点

## 1. 目的

本仓库已经把 Cordis 的生命周期形式化为一个演算([docs/RULES.md](../docs/RULES.md)),并证明了保持性、顺序、
恢复精确性、进展、终止、合流。这次调研要回答的问题是:

> 哪些 PL 领域的现成技术,能 (a) 给这个演算一个理论定位,借用已有的元理论;
> (b) 给 Cordis 或 dsh 插件提供新的静态保证或工具;(c) 反过来,Cordis 的哪些特征是那些领域还没处理好的。

调研的产出不是综述本身,而是**可以动手的课题**:每个课题写明对应演算里的哪条规则或哪个定理、要做什么、
预期得到什么、风险在哪里。

## 2. 演算中值得对照的特征

调研时以这些特征为锚,逐一看各领域有没有对应物:

| 编号 | 特征 | 演算中的位置 |
|---|---|---|
| F1 | LIFO 撤销日志 `acc`,每个操作带逆 | `L-Step` 的 `Op`,`L-Undo`;`Recovery.v` |
| F2 | 守卫 `¬held`:别人仍依赖我的 provision 时,我不撤销任何一项 | §4.2 守卫;`Ordering.unload_waits` |
| F3 | target 驱动:声明期望状态,生命周期规则逐步收敛 | `target`,`quiet`;`Progress.v`、`Termination.v` |
| F4 | 依赖 `d(c)` 是对上下文的需求,提供 `p(c)` 静态声明 | 余效应上下文;`O-Insert` 的前提 |
| F5 | 共享服务:一个 provision 被多个依赖者同时解析、读写 | Binding `⟨pid, o, s⟩`;`resolves` |
| F6 | 父子 fiber,父卸载时先请子退出再等待 | `L-RetireChild`;`parent_waits_child` |
| F7 | 加载中途可放弃(divert)、可落地,失败带错误停住,外部重置 | `L-Divert`、`Fail`、`O-Reset` |
| F8 | 运行期效应:事件反应是子 fiber,可单独撤销 | `O-React`;`Runtime.effect_exact` |
| F9 | 合流:任意调度的终态与静态组装一致(服务状态在 ≃ 意义下) | `Confluence.v` … `Dynamic.v` |
| F10 | 热重载:restart、配置更换、依赖替换引起的重新加载 | `O-Restart`;设计点 l |

## 3. 调研方向

每个方向一个文件,放在本目录。

| 文件 | 方向 | 主要对照的特征 |
|---|---|---|
| [reversibility.md](reversibility.md) | 可逆计算与补偿:RCCS、因果一致可逆性、可逆 π、saga 与补偿事务 | F1 F2 F7 F8 |
| [effects-coeffects.md](effects-coeffects.md) | 效应系统、余效应、分级类型、代数效应与处理器 | F1 F4 F8 |
| [session-types.md](session-types.md) | 会话类型、共享会话、优先级与无死锁、取消、类型状态 | F2 F5 F6 F7 |
| [components-dsu.md](components-dsu.md) | 动态组件模型与动态软件更新:OSGi、Fractal、依赖注入、DSU、Erlang 热加载 | F3 F4 F10 |
| [incremental.md](incremental.md) | 增量计算与声明式协调:自调整计算、FRP、React、Kubernetes 控制器、构建系统 | F3 F9 F10 |
| [concurrency.md](concurrency.md) | 结构化并发、取消、Erlang/OTP 监督树 | F6 F7 |
| [verification.md](verification.md) | 验证与测试:Iris/分离逻辑 refinement、模型检测、状态机性质测试 | F9;`checker/` |

每个文件的结构:

1. **领域概览**:核心概念和代表工作,只写与本演算有关的部分。
2. **对照表**:领域概念 ↔ 演算中的规则、定义或定理,注明是精确对应、近似对应还是只有形似。
3. **差异**:演算有而该领域没有的,或反过来。
4. **候选课题**:每个课题写目标、做法、预期产出、风险、工作量粗估(小/中/大)。
5. **参考文献**:每条都核对过作者、题目、会议或期刊、年份;核对不了的标注"未核实"。

## 4. 方法

- 先读 [docs/RULES.md](../docs/RULES.md) 和 [docs/DESIGN.md](../docs/DESIGN.md),定位上面的十个特征。
- 每个方向检索经典工作和近五年的工作,优先读原论文的摘要和相关章节,不凭记忆写引用。
- 对照时落到具体规则和 Rocq 定理名,不停在类比层面。
- 七个方向互相独立,并行调研;最后由一个人统一核对引用、去重、排序。

## 5. 产出

- 七个方向文件。
- [README.md](README.md):索引、总体结论、课题排序(按与现有成果的贴合度、预期收益、工作量)。

## 6. 不做的事

- 不改动演算、证明和其他目录。
- 不追求文献完整;一个方向找到能支撑课题判断的代表工作即可。
- 插件业务逻辑的验证不在范围内,与整个仓库一致。
