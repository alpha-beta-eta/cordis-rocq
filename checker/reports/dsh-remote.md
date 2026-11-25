# dsh-remote@1.3.1

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-remote#0 ACTIVE; p/dsh-remote#1 ACTIVE; p/dsh-remote#2 ACTIVE; p/dsh-remote#3 ACTIVE; p/dsh-remote#4 ACTIVE; p/dsh-remote#5 ACTIVE
- 登记: connection.fetchRoutes ×44, systemPrompt.sections ×1, tools ×21, webServer.routes ×44, cordis.services ×1, cordis.listeners ×5
- 没有桩的调用: skills.registerProvider, agents.list, commands.register
- 换成桩的模块: iconv-lite (from ../dsh-plugins/dsh-remote/1.3.1/package/lib/main.js), yaml (from ../dsh-plugins/dsh-remote/1.3.1/package/lib/remote-skills.js)

## 第 2 层: 装上再卸载

- ○ 持久状态 (R4, 只报告): + fs remote-terminal/remote ssh
- ○ 持久状态 (R4, 只报告): + fs remote-terminal/term-askpass
- ○ 持久状态 (R4, 只报告): + fs remote-terminal/term-askpass.cjs
- ○ 持久状态 (R4, 只报告): + fs remote-terminal/term-secret.json

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: tools.register ×21, systemPrompt.section ×1, webServer.register ×44, connection.fetch.register ×44

- ✓ tools.register: k = 1..21 都恢复干净, 再装与正常装上相同.
- ✓ systemPrompt.section: k = 1..1 都恢复干净, 再装与正常装上相同.
- ✗ webServer.register: 43/44 个故障点卸载后有残留; 43/44 个故障点之后再装与正常装上不同.
  最小的 k = 2:
  - 卸载后残留 + webServer.routes exact /dsh-remote/workspace-context (exact) @p
  - 再装: + webServer.routes exact /dsh-remote/workspace-context (exact) @p(旧)
  - 再装: - webServer.routes exact /dsh-remote/audit (exact) @p
  - 再装: - webServer.routes exact /dsh-remote/bindings (exact) @p
  - 再装: - webServer.routes exact /dsh-remote/connect (exact) @p
  - 再装: - webServer.routes exact /dsh-remote/current (exact) @p
  - 再装: - webServer.routes exact /dsh-remote/explorer-auto-open (exact) @p
  残留最多的是 k = 44: 43 条.
- ✓ connection.fetch.register: k = 1..44 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✗ skills 在插件之后出现时, 落定状态不同:
  - cordis.listeners: [p | p | p | p | p > p] → [p | p | p | p | p]
- ✓ 其余 49 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

### dsh-remote-fault-webServer.register-2 (第 2 层)

```
1. webServer.register call #2 by p throws                           L-Fail at the k-th call
2. install(dsh-remote) as p                                         O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-remote) as p2                                        O-Insert
```

- + webServer.routes exact /dsh-remote/workspace-context (exact) @p
- reload: + webServer.routes exact /dsh-remote/workspace-context (exact) @p(旧)
- reload: - webServer.routes exact /dsh-remote/audit (exact) @p
- reload: - webServer.routes exact /dsh-remote/bindings (exact) @p
- reload: - webServer.routes exact /dsh-remote/connect (exact) @p
- reload: - webServer.routes exact /dsh-remote/current (exact) @p
- reload: - webServer.routes exact /dsh-remote/explorer-auto-open (exact) @p
- reload: - webServer.routes exact /dsh-remote/forget-key (exact) @p
- reload: - webServer.routes exact /dsh-remote/forwards (exact) @p
- reload: - webServer.routes exact /dsh-remote/fs (exact) @p

重放: `sh check.sh replay witnesses/dsh-remote-fault-webServer.register-2.json`

### dsh-remote-late-skills (第 3 层)

```
1. install(dsh-remote) as p                                         O-Insert
2. provide(skills)                                                  O-Insert (provider)
```

- cordis.listeners: [p | p | p | p | p > p] → [p | p | p | p | p]

重放: `sh check.sh replay witnesses/dsh-remote-late-skills.json`

(共 211 次运行, 415.6 秒)
