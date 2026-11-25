# dsh-connect-workbuddy@5.31.0

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-connect-workbuddy#0 ACTIVE; p/dsh-connect-workbuddy#1 ACTIVE; p/dsh-connect-workbuddy#2 ACTIVE; p/dsh-connect-workbuddy#3 ACTIVE; p/dsh-connect-workbuddy#4 ACTIVE; p/dsh-connect-workbuddy#5 ACTIVE; p/dsh-connect-workbuddy#6 ACTIVE; p/dsh-connect-workbuddy#7 ACTIVE
- 登记: settings.presentations ×1, webServer.routes ×16, cordis.listeners ×2
- 没有桩的调用: llm.registerAdapter, llm.registerConfigurableProviders, llm.registerModelDiscovery
- 换成桩的模块: @earendil-works/pi-ai (from ../dsh-plugins/dsh-connect-workbuddy/5.31.0/package/lib/index.js), @earendil-works/pi-ai/api/openai-completions.lazy (from ../dsh-plugins/dsh-connect-workbuddy/5.31.0/package/lib/index.js), @earendil-works/pi-ai/providers/all (from packages/llm/llm-pi-ai/src/catalog.ts), @earendil-works/pi-ai/api/anthropic-messages.lazy (from packages/llm/llm-pi-ai/src/provider.ts), @earendil-works/pi-ai/api/openai-completions.lazy (from packages/llm/llm-pi-ai/src/provider.ts), @earendil-works/pi-ai/api/openai-responses.lazy (from packages/llm/llm-pi-ai/src/provider.ts), @earendil-works/pi-ai/providers/all (from packages/llm/llm-pi-ai/src/models.ts), @earendil-works/pi-ai/utils/overflow (from packages/llm/llm-pi-ai/src/stream.ts)

## 第 2 层: 装上再卸载

- ○ 持久状态 (R4, 只报告): + fs .workbuddy-device.json

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: webServer.register ×16, settings.configure ×1, settings.describe ×1

- ✗ webServer.register: 15/16 个故障点卸载后有残留; 15/16 个故障点之后再装与正常装上不同.
  最小的 k = 2:
  - 卸载后残留 + webServer.routes exact /plugins/dsh-connect-workbuddy/usage (exact) @p
  - 再装: + webServer.routes exact /plugins/dsh-connect-workbuddy/usage (exact) @p(旧)
  - 再装: - webServer.routes exact /plugins/dsh-connect-workbuddy/__save (exact) @p
  - 再装: - webServer.routes exact /plugins/dsh-connect-workbuddy/account-credits (exact) @p
  - 再装: - webServer.routes exact /plugins/dsh-connect-workbuddy/accounts/refresh (exact) @p
  - 再装: - webServer.routes exact /plugins/dsh-connect-workbuddy/benefit/claim (exact) @p
  - 再装: - webServer.routes exact /plugins/dsh-connect-workbuddy/checkin (exact) @p
  残留最多的是 k = 16: 15 条.
- ✓ settings.configure: k = 1..1 都恢复干净, 再装与正常装上相同.
- ✓ settings.describe: k = 1..1 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

### dsh-connect-workbuddy-fault-webServer.register-2 (第 2 层)

```
1. webServer.register call #2 by p throws                           L-Fail at the k-th call
2. install(dsh-connect-workbuddy) as p                              O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-connect-workbuddy) as p2                             O-Insert
```

- + webServer.routes exact /plugins/dsh-connect-workbuddy/usage (exact) @p
- reload: + webServer.routes exact /plugins/dsh-connect-workbuddy/usage (exact) @p(旧)
- reload: - webServer.routes exact /plugins/dsh-connect-workbuddy/__save (exact) @p
- reload: - webServer.routes exact /plugins/dsh-connect-workbuddy/account-credits (exact) @p
- reload: - webServer.routes exact /plugins/dsh-connect-workbuddy/accounts/refresh (exact) @p
- reload: - webServer.routes exact /plugins/dsh-connect-workbuddy/benefit/claim (exact) @p
- reload: - webServer.routes exact /plugins/dsh-connect-workbuddy/checkin (exact) @p
- reload: - webServer.routes exact /plugins/dsh-connect-workbuddy/cli-live (exact) @p
- reload: - webServer.routes exact /plugins/dsh-connect-workbuddy/device-profile (exact) @p
- reload: - webServer.routes exact /plugins/dsh-connect-workbuddy/device-sdk (exact) @p

重放: `sh check.sh replay witnesses/dsh-connect-workbuddy-fault-webServer.register-2.json`

(共 119 次运行, 399.5 秒)
