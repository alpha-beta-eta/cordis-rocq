# dsh-session-superagent@0.10.12

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-session-superagent#0 ACTIVE
- 登记: tools ×8, webServer.routes ×13, cordis.listeners ×1
- 换成桩的模块: @mycf711/dsh-gate (from ../dsh-plugins/dsh-session-superagent/0.10.12/package/lib/index.js)

## 第 2 层: 装上再卸载

- ✗ 进程级改动未恢复: global globalThis.Symbol(dsh-session-superagent.activeRoutes): (absent) → set
- ✗ 进程级改动未恢复: global globalThis.Symbol(dsh-session-superagent.inFlight): (absent) → set
- ✗ 进程级改动未恢复: global globalThis.Symbol(dsh-session-superagent.timers): (absent) → set
- ○ 持久状态 (R4, 只报告): + fs .dsh/state/session-superagent/watchers.json
- ○ 持久状态 (R4, 只报告): + fs .dsh/state/session-superagent/watchers.json.bak

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: webServer.register ×13, tools.register ×8

- ✗ webServer.register: 0/13 个故障点卸载后有残留; 13/13 个故障点之后再装与正常装上不同.
  最小的 k = 1:
  - 再装: + global globalThis.Symbol(dsh-session-superagent.routeGeneration) added
- ✓ tools.register: k = 1..8 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

### dsh-session-superagent-unload (第 2 层)

```
1. install(dsh-session-superagent) as p                             O-Insert
2. dispose(p)                                                       O-Dispose
3. install(dsh-session-superagent) as p2                            O-Insert
```

- global globalThis.Symbol(dsh-session-superagent.activeRoutes): (absent) → set
- global globalThis.Symbol(dsh-session-superagent.inFlight): (absent) → set
- global globalThis.Symbol(dsh-session-superagent.timers): (absent) → set

重放: `sh check.sh replay witnesses/dsh-session-superagent-unload.json`

### dsh-session-superagent-fault-webServer.register-1 (第 2 层)

```
1. webServer.register call #1 by p throws                           L-Fail at the k-th call
2. install(dsh-session-superagent) as p                             O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-session-superagent) as p2                            O-Insert
```

- global globalThis.Symbol(dsh-session-superagent.activeRoutes): (absent) → set
- global globalThis.Symbol(dsh-session-superagent.inFlight): (absent) → set
- global globalThis.Symbol(dsh-session-superagent.routeGeneration): (absent) → set
- global globalThis.Symbol(dsh-session-superagent.timers): (absent) → set
- reload: + global globalThis.Symbol(dsh-session-superagent.routeGeneration) added

重放: `sh check.sh replay witnesses/dsh-session-superagent-fault-webServer.register-1.json`

(共 122 次运行, 396.5 秒)
