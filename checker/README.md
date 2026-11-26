# cordis-check

在真实的 Cordis 上跑真实的 dsh 插件，枚举生命周期调用序列，以汇总定理 (`theories/Summary.v`) 的各层为判据，
找出违反性质的**最短调用序列** (见证)。与 [../docs/PLUGIN-AUDIT.md](../docs/PLUGIN-AUDIT.md) 的人工审计互补：
审计读源码给出判定，checker 给出能重放的反例。

它是具体执行加有界枚举，属于欠近似：报出的问题 (相对于宿主桩的语义) 一定真实存在，没报的不等于没有。

## 运行

在 WSL 中运行，需要 node 22。`setup.sh` 会从 npm 下载 typescript@5.9.3 到 `.tools/` 并校验 sha1，只用来转译 dsh 的 TS 源码，因为发行版的 Node 不带类型剥离：

```sh
sh check.sh check dsh-whale-widget                 # 单个插件: 卸载再装, 故障注入, 服务晚到, 提供者重启
sh check.sh check --all                            # 全部插件, 共用一个并行池 (约 5 分钟)
sh check.sh pair ds-harness-remote dsh-remote      # 两个插件: 两种安装次序
sh check.sh sweep                                  # 全部插件各装上卸载一次 (覆盖面普查)
sh check.sh replay witnesses/*.json                # 重放见证 (全部复现时退出码为 1)
```

并行度默认是 CPU 数的一半，可以用 `CHECK_JOBS` 改。`CHECK_CONTRIB=1` 打开贡献模式 ([../docs/CONTRIB.md](../docs/CONTRIB.md) 的 E6e)：所有登记都经调用者的 fiber，撞名不抛错而按多重集记下。`CHECK_OUT=<目录>` 把见证与报告写到别处，不碰 `witnesses/` 与 `reports/`。转译结果和 dsh 包索引缓存在 `.cache/` 下，删掉即可重建。

第一轮的报告见 [REPORT.md](REPORT.md)，逐插件的细节见 [FINDINGS.md](FINDINGS.md)。在真实的 dsh 宿主上复现见证的工具在 [real/](real/)。

首次运行时 `setup.sh` 把 dsh vendored 的 cordis、cosmokit、schemastery 源码复制到 `.vendor/`，并在
`.vendor/SOURCE` 中记下 dsh 的提交。插件从 `PLUGINS_ROOT` (默认 `/mnt/d/dsh-plugins/<名字>/<版本>/package`)
加载，其余 `@deepseek-ai/*` 包从 `DSH_ROOT/packages` (默认 `/mnt/d/deepseek-harness`) 只读加载。

输出：`reports/<插件>.md` 是报告，`witnesses/*.json` 是见证 (场景加期望的差异)。

## 结构

| 文件 | 内容 |
|---|---|
| `lib/exec.mjs` | 在一个新进程里执行一条调用序列，输出各个观察点的快照 |
| `lib/world.mjs` | 账本：宿主桩上的全部登记、调用计数、故障计划 |
| `lib/host.mjs` | dsh 宿主服务的桩：webServer、tools、systemPrompt、settings、credentials、connection、loader，其余服务用通用桩 |
| `lib/host-graph.json` | 真实宿主的服务依赖图 (由 `real/make-graph.mjs` 生成)；桩按它的传递闭包 inject，重启沿依赖级联 |
| `lib/probes.mjs` | 进程级探针 (原型、globalThis、dns、process 监听器、长命句柄、环境变量)；沙箱 (禁网络、子进程、kill、exit) |
| `lib/oracle.mjs` | 判据：恢复 (第 2 层) 与合流 (第 3 层) |
| `lib/scenarios.mjs` | 调用序列的生成，动作与演算规则的对应 |
| `lib/run.mjs` | 并行执行 |
| `hooks.mjs` | 模块解析钩子：dsh 包映射、找不到的包换成吸收型桩、TS 转译 |
| `require-hooks.mjs` | 对 CJS 的 `require` 做同样的事：补丁 `Module._resolveFilename`，桩是 `.cache/require-stubs/` 下的真实文件；dsh 包经一层薄壳给出 tsdown CJS 构建的形状 (只有 default 导出时是 default 本身) |
| `fixtures/` | 自测用的小插件：leaky (故障注入下泄漏)、stale (提供者重启后丢登记) 应被抓到，tidy 应判干净 |

## 动作与观察

| 动作 | 演算规则 |
|---|---|
| `install(p)` | O-Insert |
| `dispose(p)` | O-Dispose |
| `provide(s)` / `withdraw(s)` | 提供者的 O-Insert / O-Dispose |
| `fault(site, k)` | 插件第 k 次调用 site 时抛错，即 apply 在第 k 个 L-Step 处 L-Fail |
| `emit(e)` | 一次分发 |

每个观察点 (`snap`) 记下：

- 宿主桩的登记表 (键、值、属于哪个安装)；
- Cordis 自己的状态 (谁提供了哪个服务、每个事件上监听器的次序、全部 fiber 的状态)；
- 进程级状态；
- 临时 HOME 下的文件。

令牌、fiber 编号不进快照，安装编号是场景里给定的固定名字，所以比较是"重命名意义下"的，对应 `Observe.v` 的 ≃。

## 判据

- **恢复 (第 2 层)**：`dispose` 之后与安装之前比较。分三类：
  - 登记表有残留，记 ✗ (R1/R2)；
  - 进程级改动未恢复，记 ✗ (越出模型的效应或未恢复的全局状态，S3/R4)；
  - credentials、settings 的写入与 HOME 下的文件，只报告 (R4 中有意持久的外部状态)。
- **再装**：卸载后再装一次，与第一次装上比较。
- **故障注入 (R1)**：对插件在 apply 期间调用的每个宿主方法、每个 k，让第 k 次调用抛错，然后卸载，再装一次。
  再装与正常装上不同，说明残留已经影响到下一次加载。
- **服务晚到 (C2)**：每个宿主服务分别在插件之后才出现，落定状态与服务先到时比较。
- **提供者重启 (C2)**：插件装上后，每个宿主服务分别撤走再提供，落定状态与重启前比较。桩的服务实例被卸载时清空它名下的登记表，与真实宿主里新实例从空表开始一致。桩按真实宿主的服务依赖图 (`lib/host-graph.json`) inject，所以撤走一个服务时，依赖它的宿主服务与插件由 Cordis 连带卸载，与真实宿主一致 (例如 `tools` 依赖 `systemPrompt`)。
- **安装次序 (合流)**：两个插件的两种安装次序，落定状态比较 (含服务归属与监听器次序)。

三条防止误报的规则：

- **稳定性**：每个候选见证写入前再判定两次，差异集合三次都相同才保留；不稳定的留在 `.out/unstable/` 备查。
- **落定**：每步之后先走几轮事件循环，再等插件的 fiber 走出 LOADING，每次最多等 2 秒 (`CHECK_SETTLE_MS`)；超时仍在 LOADING 的 fiber 记为卡住，之后不再等它。仍有 fiber 停在 LOADING 时，"再装"与"服务晚到"两类比较判无结论；
  pair 在这种情况下只比较服务归属，因为 `ctx.provide` 先到先得，不依赖异步加载走没走完。
- **新旧实例**：卸载后再装用安装编号 `p2`，比较前把旧实例改名为 `p(旧)`、把 `p2` 改名为 `p`，
  这样旧实例卸载后还占着的东西 (残留路由、仍在监听的事件) 能和新实例的登记分开。

## 宿主桩的保真度

桩只模拟登记语义，照 dsh 源码写，注释给出出处。最要紧的区分是：

- **owned**：宿主经调用者的 `ctx.effect` 登记，卸载调用者时自动撤销。例：`tools.register`、`systemPrompt.section`。
- **bare**：宿主只返回一个裸 disposer，插件不自己登记它的逆就会泄漏。例：`webServer.register`、`webServer.tapIndex`、`settings.configure`。

`connection.rpc.handle` 是 owned，在效应体内用 `owner.webServer.register` 把通道登成一条 webServer 路由。读 `owner.webServer` 要求调用者 inject 了 webServer，否则 Cordis 抛 `without inject`；inject 了的调用者会随 webServer 重启，通道随之重新登记。`connection.fetch.register`、`connection.rpc.intercept` 是普通的 owned。插件常按 `connection.fetch` 在不在选择分支，所以 connection 的桩必须带上 `rpc` 与 `fetch`；第一轮缺了它们，造成 dsh-im 的两个误报。

另外三点照真实 dsh 做：

- 插件装在一个提供 `loader` 的宿主 fiber 下面，因为祖先 fiber 提供的服务不经 inject 也能访问；
- 默认配置为 `{}`；
- 宿主自己的 schemastery 在基线之前就已加载。

没有桩的服务由通用桩顶替：方法调用记为"没有桩的调用"，返回吸收型值。吸收型值的任何取属性、调用、`new` 都返回另一个吸收型值，迭代为空。找不到的第三方包也换成吸收型模块。报告会列出两者。通用桩有一个已知的偏差：它"什么方法都有"，所以按方法是否存在做鸭子类型判断的插件会走到别的分支 (ds-harness-remote 的 settings 就是这样，因此给 settings 写了专门的桩)。

## 沙箱

插件的代码真的会执行，所以每条序列都在单独的进程里跑，且：

- HOME/DSH_HOME 指向临时目录；
- 网络 (fetch、http、https、net、tls) 一律拒绝；
- 子进程 (spawn、exec、execFile、fork 及其同步版本) 不执行，返回一个立即以 ENOENT 失败的伪 ChildProcess；
- `process.kill` 与 `process.exit` 被拦下。

被拦下的调用都记入轨迹。插件若起 worker 线程，线程内不受这些拦截。

## 已知的局限

- 结论相对于桩：凡是只在真实网关、真实账户、真实网络下才走到的路径 (例如 IM 插件在通道连上之后才登记的 `approval/request` 中间件)，checker 走不到。
- `require('x/package.json')` 找不到时照常抛错，不给桩：这几乎总是在探测包在不在。
- 落定的上限是 2 秒：比这更慢的异步加载仍判无结论。dsh-mobile-plugin 在满载的并行池里结果抖动 (内层装载受时序影响)，它的见证以单独运行为准。
- 有界：故障点按调用次数穷举 (默认上限 64)，服务晚到只试单个服务，安装次序只试两两。还没有自由搜索 (`explore`) 和最短化，现有的三种场景形状本身已经是最短的。
- 只看宿主端，不看浏览器客户端。
