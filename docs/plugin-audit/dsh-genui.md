# dsh-genui 0.3.4

- 是否 Cordis 插件 / 入口 / 宿主 inject / provide / 客户端：是。宿主 `lib/index.js` (打包单文件，6548 行)，`inject = ["systemPrompt", "webServer"]`(`lib/index.js:6413` ✔)，`settings` 走 `ctx.inject` 子 fiber (`:6492` ✔)；无 provide。客户端 `lib/client.js`，`inject = ["slots", "locale"]`(`lib/client.js:1414` ✔)。`lib/genui-runtime.js` (6.3MB) 是由宿主路由下发给浏览器的 Vue/OpenTiny 运行时，不是插件入口。
- 一句话功能：向系统提示注入 GenUI 卡片写作说明 (off/mini/standard/plus 四档)，浏览器端把助手回复中的 schemaJson 渲染成交互卡片。

宿主端：

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✓ | 宿主代码无 `ctx.get`；`systemPrompt`/`webServer` 已注入，`settings` 在注入子 fiber 内使用 (`lib/index.js:6492-6528` ✔)。`settings.describe()` 读其他条目只在旧宿主回退分支 (`:6197` ✔)。 |
| 0 | S2 | ✓ | 无 provide。 |
| 0 | S3 | ✓ | 无元层钩子、无猴补丁、不碰别的插件 ctx。 |
| 1 | L1 | ✓ | 启动同步、无循环。 |
| 1 | L2 | ✓ | 无 provide/spawn，无环。 |
| 2 | R1 | ✓ | 三条路由各包 `ctx.effect` (`:6531-6545` ✔)；提示段由 `ctx.effect` 设为 standard，逆为 `set("off")`(`:6488-6491` ✔)；`settings.register` 与持久化控制在 `settingsCtx.effect` 内 (`:6505`)。 |
| 2 | R2 | △ | 运行期 POST `/api/dsh-genui/prompt` 会调用 `systemPrompt.section(...)` 换段 (`:6249-6268`、`:6296` ✔)。段的 disposer 保存在闭包中，卸载时 `set("off")` 释放，可回收；但它挂在根 fiber 上而不是子 fiber，只能整体撤销。 |
| 2 | R3 | ✓ | 路由 `/api/dsh-genui/prompt`、`/dsh-genui/runtime.js(.map)`(`:6365-6371` ✔) 带前缀；提示段名来自配置 `genui:cards`(`cordis.patch.yml`)，settings 命名空间 `dsh-genui`。 |
| 2 | R4 | △ | 持久：settings 中的提示档位与按钮显隐 (`:6213-6241`)。无进程级全局改动；运行时 JS 只读下发。 |
| 3 | C1 | ✓ | 无 provide。 |
| 3 | C2 | ✓ | 登记集合固定；只按注入服务的接口形状选分支 (`openPromptSettings`)。 |
| 3 | C3 | ✗ | 提示档位是状态相关的逆："设为 standard / 卸载设 off" (`:6488-6491`)，settings 子 fiber 启动时再 `control.set(持久值)`(`:6214` ✔)，其撤销只恢复 `currentControl` 指针、不恢复档位 (`:6522-6526` ✔)。于是 settings 先离开再回来、或从未出现，终态档位不同；HTTP 也能在运行期改档位。 |
| 3 | C4 | ✓ | 不直接 dispose 启动子 fiber。 |
| 3 | C5 | ✓ | 不读分发结果。 |

客户端 (分开评)：

| 层 | 前提 | 判定 | 证据 |
|---|---|---|---|
| 0 | S1 | ✓ | 只用 `slots`、`locale`。 |
| 0 | S3 | △ | 以 `priority: -1` 遮蔽聊天自带的 `conversation.chat.node`/`assistant-step` 条目，再读 `slots.entries(...)` 抓取内置组件 (`lib/client.js:121-130`、`:1497-1511` ✔)，并在注册后直接改自己条目对象的 `children`，借用内置条目声明的 reasoning-body 槽 (`:76-90`、`:1512-1516`)——改写注册表内部记录。 |
| 2 | R1 | △ | slot/locale 登记都随 fiber；但 `apply` 里 `ensureGenuiRuntimeStyles()`、`prefetchGenuiRuntime()` 不在 effect 中 (`:1422-1423` ✔)。 |
| 2 | R3 | ✗ | 依赖别的插件 (chat) 登记的 `assistant-step` 条目和它的 children 表；遮蔽同一 key 与其他也想遮蔽它的插件 (例如 cot 翻译插件替换 reasoning body，`:62`) 相遇时结果取决于 priority 与次序。 |
| 2 | R4 | ✗ | 运行时脚本以 `<script type=module>` 注入 `document.head`(`:238`)，定义全局自定义元素 `dsh-genui-card`(`lib/genui-runtime.js`) 并写 `globalThis.__dshGenuiCss`(`lib/client.js:183`、`:196`)，样式标签不随 fiber 删除。自定义元素无法注销：属于进程级不可撤销的改动。 |

**最高层**：宿主 2；客户端 0 (S3 △，R3/R4 ✗)。宿主 C3 ✗ 是卡在第 2 层的唯一原因。
**升级路径**：宿主改成启动时登记一个固定名字的提示段，`text` 写成读当前档位的函数 (档位 off 时返回空串)，档位只是普通状态、不再通过增删段来表达 → C3 ✓，宿主到 3。客户端：运行时预取与样式注入放进 `ctx.effect` 并在撤销时删样式标签，可到 R1 ✓；自定义元素与对 chat 条目的遮蔽是设计上的，无法在模型内撤销，只能标注为"保证不覆盖"。
