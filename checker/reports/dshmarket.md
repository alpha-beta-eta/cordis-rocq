# dshmarket@1.80.0

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-market#0 ACTIVE; p/dsh-market#1 ACTIVE; p/dsh-market#2 ACTIVE; p/dsh-market#3 ACTIVE
- 登记: webServer.routes ×63, cordis.listeners ×3
- 没有桩的调用: loader.entries, commands.register
- 换成桩的模块: js-yaml (from ../dsh-plugins/dshmarket/1.80.0/package/lib/check.js), js-yaml (from ../dsh-plugins/dshmarket/1.80.0/package/lib/profile.js), js-yaml (from ../dsh-plugins/dshmarket/1.80.0/package/lib/updates.js), undici (from ../dsh-plugins/dshmarket/1.80.0/package/lib/net.js), js-yaml (from ../dsh-plugins/dshmarket/1.80.0/package/lib/routes.js)

## 第 2 层: 装上再卸载

- ○ 持久状态 (R4, 只报告): + fs profiles/web/.dsh-market/log.ndjson
- ○ 持久状态 (R4, 只报告): + fs profiles/web/.dsh-market/state.json

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: webServer.register ×63

- ✗ webServer.register: 62/63 个故障点卸载后有残留; 62/63 个故障点之后再装与正常装上不同.
  最小的 k = 2:
  - 卸载后残留 + webServer.routes exact /dsh-market/telemetry/opened (exact) @p
  - 再装: + webServer.routes exact /dsh-market/telemetry/opened (exact) @p(旧)
  - 再装: - webServer.routes exact /dsh-market/ai-recommend (exact) @p
  - 再装: - webServer.routes exact /dsh-market/ai-search (exact) @p
  - 再装: - webServer.routes exact /dsh-market/ai-use-my-plugins (exact) @p
  - 再装: - webServer.routes exact /dsh-market/api/v1/capabilities (exact) @p
  - 再装: - webServer.routes exact /dsh-market/api/v1/operations (exact) @p
  - 再装: - global globalThis.Symbol(dsh-market.serving-instance) added
  残留最多的是 k = 63: 62 条.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✗ webServer 的提供者重启后, 落定状态不同:
  - + cordis.fibers p/dsh-market#4 (ACTIVE) @p
- ✗ webStartup 的提供者重启后, 落定状态不同:
  - + cordis.fibers p/dsh-market#4 (ACTIVE) @p
- ✓ 其余 48 个服务重启后与重启前相同.

## 见证

### dshmarket-fault-webServer.register-2 (第 2 层)

```
1. webServer.register call #2 by p throws                           L-Fail at the k-th call
2. install(dshmarket) as p                                          O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dshmarket) as p2                                         O-Insert
```

- + webServer.routes exact /dsh-market/telemetry/opened (exact) @p
- reload: + webServer.routes exact /dsh-market/telemetry/opened (exact) @p(旧)
- reload: - webServer.routes exact /dsh-market/ai-recommend (exact) @p
- reload: - webServer.routes exact /dsh-market/ai-search (exact) @p
- reload: - webServer.routes exact /dsh-market/ai-use-my-plugins (exact) @p
- reload: - webServer.routes exact /dsh-market/api/v1/capabilities (exact) @p
- reload: - webServer.routes exact /dsh-market/api/v1/operations (exact) @p
- reload: - webServer.routes exact /dsh-market/api/v1/restart (exact) @p
- reload: - webServer.routes exact /dsh-market/api/v1/rollback (exact) @p
- reload: - webServer.routes exact /dsh-market/api/v1/updates (exact) @p

重放: `sh check.sh replay witnesses/dshmarket-fault-webServer.register-2.json`

### dshmarket-restart-webServer (第 3 层)

```
1. install(dshmarket) as p                                          O-Insert
2. withdraw(webServer)                                              O-Dispose (provider)
3. provide(webServer)                                               O-Insert (provider)
```

- + cordis.fibers p/dsh-market#4 (ACTIVE) @p

重放: `sh check.sh replay witnesses/dshmarket-restart-webServer.json`

### dshmarket-restart-webStartup (第 3 层)

```
1. install(dshmarket) as p                                          O-Insert
2. withdraw(webStartup)                                             O-Dispose (provider)
3. provide(webStartup)                                              O-Insert (provider)
```

- + cordis.fibers p/dsh-market#4 (ACTIVE) @p

重放: `sh check.sh replay witnesses/dshmarket-restart-webStartup.json`

(共 164 次运行, 412.1 秒)
