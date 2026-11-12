# dsh 事件分发调用排查

排查对象:`D:\deepseek-harness\packages` 中非测试代码的 Cordis 分发调用(`emit`、`parallel`、`serial`、`bail`、`waterfall`)。目的是确认合流定理的前提"启动程序不读取分发结果"(RULES.md 第 7 节)在 dsh 中是否成立。

方法:先按调用模式用 grep 收集,共 200 处;再对每处列出它外层的函数与回调,判断它运行在插件激活期间(插件函数体、`[Service.init]`、构造函数、`ctx.effect`、`ctx.inject` 回调的同步部分)还是运行期(事件处理器、工具执行、请求处理、定时器、方法调用)。少数关键位置人工核对过。

## 结论

1. **读取结果的分发都在运行期。** 共 38 处:`waterfall` 31、`bail` 5、`serial` 2,全部位于以下几类代码中,没有一处在插件激活期间:
   - 工具执行管线(`core/tools/src/pipeline.ts`、各 `fs/*-intent`);
   - agent 循环(`core/agent-loop/src/agent.ts`);
   - 用户输入与命令(`client/ui-commands`、`client/ui-input-trigger`);
   - HTTP 请求处理(`client/connection`);
   - 提示词组装、LLM 请求头、审批与提问、会话遥测等。

   因此"启动程序不读取分发结果"在 dsh 中成立,监听器顺序不影响启动结果。
2. **不读结果的分发(`emit` 153、`parallel` 9)大多在运行期**,例如 `fs/observed` 18 处、插件管理器的进度事件、会话与 agent 状态事件。
3. **例外:注册时发出的变更通知。** 有一类分发会在启动期间发生,但不读结果:服务在有人向它注册时发出通知,例如:
   - `tools/change`(`core/tools/src/index.ts:106`)、`system-prompt/change`(`core/system-prompt/src/index.ts:448`):注册层发生变化时发出;
   - `slots/changed`(`client/ui-renderer/src/client/registry.ts:161`);
   - `subagent/provider-added`(`subagent/subagent/src/index.ts:566`,在 `registerProvider` 的效应中发出)。

   `typert/registry` 中的 `changes.emit` 用的是它自己的 `ChangeSource`,不是 Cordis 事件总线。
4. **这些通知的监听器按"监听加当前状态"的写法编写,与激活顺序无关。** 典型是 `subagent/tool-subagent/src/index.ts:347`:先注册 `provider-added`/`provider-removed` 监听器,再检查提供者是否已存在,两种情况走同一个 `mount`。源码注释明确说明这是为了应对激活顺序和热替换。其他监听器(`refreshBlockedMasks`、forge 的 `sync`、模型目录的 `refresh`)都从当前状态重新计算。
5. **注册时监听器可以否决注册。** `registerProvider` 中监听器抛出异常会撤销这次注册(注释称为 fail-loud)。这样一来,结果取决于监听器与注册谁先发生,但两种顺序下都是某个 fiber 失败,已被合流定理的"没有失败 fiber"排除。

## 对形式化的影响

- 第 7 节的前提在 dsh 中成立:启动期间没有依赖顺序的分发。
- 第 3、4 条描述的是一种未建模的依赖:插件依赖另一个服务内部的某个条目(例如名为 X 的子 agent 提供者),而不是依赖一个键。dsh 用"事件加检查"手工实现了它。模型目前只支持对键的依赖(`deps`、视图)。可选的后续方向:
  - 在模型中把这种"对条目的依赖"表示为对键的依赖,由 L-Begin 与 target 自动处理;
  - 或者把"监听加当前状态"作为运行期反应建模(与 DESIGN.md 差异 k 相关)。
- 本次排查依赖文本与缩进启发式,不是穷尽证明。插件函数调用的辅助函数里若有分发,只能从调用位置追踪;第 3 条中的通知正是这样找到的。
