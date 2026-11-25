# dsh-pet@0.4.9

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/pet#0 ACTIVE
- 登记: webServer.routes ×1, cordis.services ×1, cordis.listeners ×2
- 没有桩的调用: commands.register, agentDefaultModel.currentSelection
- 换成桩的模块: @electron/get (from ../dsh-plugins/dsh-pet/0.4.9/package/lib/index.js)

## 第 2 层: 装上再卸载

- ✗ 进程级改动未恢复: handle Timeout: 0 → 1
- ○ 持久状态 (R4, 只报告): + fs dsh-pet/logs.txt

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: webServer.register ×1

- ✓ webServer.register: k = 1..1 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

### dsh-pet-unload (第 2 层)

```
1. install(dsh-pet) as p                                            O-Insert
2. dispose(p)                                                       O-Dispose
3. install(dsh-pet) as p2                                           O-Insert
```

- handle Timeout: 0 → 1

重放: `sh check.sh replay witnesses/dsh-pet-unload.json`

(共 102 次运行, 330.4 秒)
