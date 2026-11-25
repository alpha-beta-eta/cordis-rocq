# dsh-token-diet@0.1.0

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/token-diet#0 ACTIVE; p/token-diet#1 ACTIVE
- 登记: webServer.routes ×1, cordis.listeners ×3
- 没有桩的调用: sessionPersistence.list

## 第 2 层: 装上再卸载

✓ 卸载后与从未安装相同, 再装与第一次装上相同.

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: connection.rpc.handle ×2, webServer.register ×2

- ✓ connection.rpc.handle: k = 1..2 都恢复干净, 再装与正常装上相同.
- ✓ webServer.register: k = 1..2 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✗ webServer 在插件之后出现时, 落定状态不同:
  - - webServer.routes prefix /token-diet (prefix) @p
- ✓ 其余 49 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✗ webServer 的提供者重启后, 落定状态不同:
  - - webServer.routes prefix /token-diet (prefix) @p
- ✓ 其余 49 个服务重启后与重启前相同.

## 见证

### dsh-token-diet-late-webServer (第 3 层)

```
1. install(dsh-token-diet) as p                                     O-Insert
2. provide(webServer)                                               O-Insert (provider)
```

- - webServer.routes prefix /token-diet (prefix) @p

重放: `sh check.sh replay witnesses/dsh-token-diet-late-webServer.json`

### dsh-token-diet-restart-webServer (第 3 层)

```
1. install(dsh-token-diet) as p                                     O-Insert
2. withdraw(webServer)                                              O-Dispose (provider)
3. provide(webServer)                                               O-Insert (provider)
```

- - webServer.routes prefix /token-diet (prefix) @p

重放: `sh check.sh replay witnesses/dsh-token-diet-restart-webServer.json`

(共 105 次运行, 372.8 秒)
