# keys：键的卫生

设计与进度见 [DESIGN.md](DESIGN.md)。构建：先构建核心，再运行 `sh keys/build.sh`。

插件提供的服务默认只给自己的子树用（私有键按实例区分），要给别的插件用必须显式导出；导出名有多个提供者时，
冲突是一个确定的值（与贡献键相同），不让任何 fiber 失败。

与现有形式化隔离：代码将放在 `keys/theories/`，逻辑名 `CordisKeys`，核心不 import 它；每个模块给出对核心的
保守性定理。

| 文件 | 内容 |
|---|---|
| `theories/Scoped.v` | 作用域、名字解析、导出名选择、`kstep`；归约到核心（`kstep_core`）、保持 `WF`、作用域不同则不冲突、无导出依赖时保守 |
| `theories/ScopedSafety.v` | 作用域唯一的不变式；插入、spawn、反应永不冲突；自己作用域上的绑定属于自己 |
| `theories/ScopedTerm.v` | 终止：扩展的生命周期步单独不能无限进行，含改绑带来的重新加载 |
| `theories/ScopedProgress.v` | 没有死锁：quiet 的状态都 settled；Inactive fiber 等待的原因只有没有候选、并列、键不可见 |
| `theories/ScopedConf.v` | 控制层合流（组件不 spawn）：同样的 fiber 与活跃性、同样的键所有者、同样的候选与解析、同样的选择 |
| `theories/ScopedSpawn.v` | 带 spawn 与服务状态的合流（子 fiber 继承父 fiber 的选择）：按规范名对应，组件、活跃性、键所有者、服务状态、解析与并列都一致 |
| `theories/ScopedDynamic.v` | 与编排交错的合流：同样的存活组件次序 ⇒ 终态按标签对应、解析与并列一致；静态组装 |
| `theories/ScopedCons.v` | 对核心的保守性（K6）：所有名字导出、没有私有依赖时，扩展与基组件表上的核心走同样的步，只在三处分开（核心报冲突处、实例 id 重用、选择过时的 fiber 的惰性一步）；`sim_back`/`back_run`、`sim_fwd`/`fwd_run` |
| `theories/Examples.v` | 两个实例、导出名并列、更高优先级者胜出、改绑、同一处理器并发触发，均为计算验证 |
