# dsh-free-search@0.9.82

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/web-search-free#0 ACTIVE; p/web-search-free#1 ACTIVE; p/web-search-free#10 ACTIVE; p/web-search-free#11 ACTIVE; p/web-search-free#12 ACTIVE; p/web-search-free#13 ACTIVE; p/web-search-free#14 PENDING (waiting: connection.authentication); p/web-search-free#2 ACTIVE; p/web-search-free#3 ACTIVE; p/web-search-free#4 ACTIVE; p/web-search-free#5 ACTIVE; p/web-search-free#6 ACTIVE; p/web-search-free#7 ACTIVE; p/web-search-free#8 ACTIVE; p/web-search-free#9 ACTIVE
- 登记: settings.presentations ×1, systemPrompt.sections ×1, tools ×9, webServer.routes ×10, cordis.listeners ×1
- 没有桩的调用: web.registerSearchProvider, web.registerFetchProvider
- 换成桩的模块: yaml (from packages/settings/settings/src/index.ts), @deepseek-ai/cordis-plugin-loader (from packages/settings/settings/src/index.ts)

## 第 2 层: 装上再卸载

- ○ 持久状态 (R4, 只报告): + fs .cache/dsh-free-search/research.db

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: settings.configure ×1, webServer.register ×10, tools.register ×9, systemPrompt.section ×2

- ✓ settings.configure: k = 1..1 都恢复干净, 再装与正常装上相同.
- ✗ webServer.register: 9/10 个故障点卸载后有残留; 9/10 个故障点之后再装与正常装上不同.
  最小的 k = 2:
  - 卸载后残留 + webServer.routes exact /api/dsh-free-search-settings/describe (exact) @p
  - 再装: + webServer.routes exact /api/dsh-free-search-settings/describe (exact) @p(旧)
  - 再装: - webServer.routes exact /api/dsh-free-search-settings/describe (exact) @p
  残留最多的是 k = 10: 9 条.
- ✓ tools.register: k = 1..9 都恢复干净, 再装与正常装上相同.
- ✓ systemPrompt.section: k = 1..2 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✗ settings 的提供者重启后, 落定状态不同:
  - - settings.presentations web-search-free ({"auto":false}) @p
  - - systemPrompt.sections free-search:engines (section) @p
  - - tools advanced_search (tool) @p
  - - tools cache_search (tool) @p
  - - tools domain_search (tool) @p
  - - tools free_search_test (tool) @p
  - - tools multi_search (tool) @p
  - - tools platform_search (tool) @p
- ✗ webServer 的提供者重启后, 落定状态不同:
  - + cordis.fibers p/web-search-free#15 (PENDING (waiting: connection.authentication)) @p
- ✗ tools 的提供者重启后, 落定状态不同:
  - - settings.presentations web-search-free ({"auto":false}) @p
  - - systemPrompt.sections free-search:engines (section) @p
  - - tools advanced_search (tool) @p
  - - tools cache_search (tool) @p
  - - tools domain_search (tool) @p
  - - tools free_search_test (tool) @p
  - - tools multi_search (tool) @p
  - - tools platform_search (tool) @p
- ✗ systemPrompt 的提供者重启后, 落定状态不同:
  - - settings.presentations web-search-free ({"auto":false}) @p
  - - systemPrompt.sections free-search:engines (section) @p
  - - tools advanced_search (tool) @p
  - - tools cache_search (tool) @p
  - - tools domain_search (tool) @p
  - - tools free_search_test (tool) @p
  - - tools multi_search (tool) @p
  - - tools platform_search (tool) @p
- ✗ webStartup 的提供者重启后, 落定状态不同:
  - + cordis.fibers p/web-search-free#15 (PENDING (waiting: connection.authentication)) @p
- ✗ web 的提供者重启后, 落定状态不同:
  - - settings.presentations web-search-free ({"auto":false}) @p
  - - systemPrompt.sections free-search:engines (section) @p
  - - tools advanced_search (tool) @p
  - - tools cache_search (tool) @p
  - - tools domain_search (tool) @p
  - - tools free_search_test (tool) @p
  - - tools multi_search (tool) @p
  - - tools platform_search (tool) @p
- ✓ 其余 44 个服务重启后与重启前相同.

## 见证

### dsh-free-search-fault-webServer.register-2 (第 2 层)

```
1. webServer.register call #2 by p throws                           L-Fail at the k-th call
2. install(dsh-free-search) as p                                    O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-free-search) as p2                                   O-Insert
```

- + webServer.routes exact /api/dsh-free-search-settings/describe (exact) @p
- reload: + webServer.routes exact /api/dsh-free-search-settings/describe (exact) @p(旧)
- reload: - webServer.routes exact /api/dsh-free-search-settings/describe (exact) @p

重放: `sh check.sh replay witnesses/dsh-free-search-fault-webServer.register-2.json`

### dsh-free-search-restart-settings (第 3 层)

```
1. install(dsh-free-search) as p                                    O-Insert
2. withdraw(settings)                                               O-Dispose (provider)
3. provide(settings)                                                O-Insert (provider)
```

- - settings.presentations web-search-free ({"auto":false}) @p
- - systemPrompt.sections free-search:engines (section) @p
- - tools advanced_search (tool) @p
- - tools cache_search (tool) @p
- - tools domain_search (tool) @p
- - tools free_search_test (tool) @p
- - tools multi_search (tool) @p
- - tools platform_search (tool) @p
- - tools research (tool) @p
- - tools video_search (tool) @p

重放: `sh check.sh replay witnesses/dsh-free-search-restart-settings.json`

### dsh-free-search-restart-webServer (第 3 层)

```
1. install(dsh-free-search) as p                                    O-Insert
2. withdraw(webServer)                                              O-Dispose (provider)
3. provide(webServer)                                               O-Insert (provider)
```

- + cordis.fibers p/web-search-free#15 (PENDING (waiting: connection.authentication)) @p

重放: `sh check.sh replay witnesses/dsh-free-search-restart-webServer.json`

### dsh-free-search-restart-tools (第 3 层)

```
1. install(dsh-free-search) as p                                    O-Insert
2. withdraw(tools)                                                  O-Dispose (provider)
3. provide(tools)                                                   O-Insert (provider)
```

- - settings.presentations web-search-free ({"auto":false}) @p
- - systemPrompt.sections free-search:engines (section) @p
- - tools advanced_search (tool) @p
- - tools cache_search (tool) @p
- - tools domain_search (tool) @p
- - tools free_search_test (tool) @p
- - tools multi_search (tool) @p
- - tools platform_search (tool) @p
- - tools research (tool) @p
- - tools video_search (tool) @p

重放: `sh check.sh replay witnesses/dsh-free-search-restart-tools.json`

### dsh-free-search-restart-systemPrompt (第 3 层)

```
1. install(dsh-free-search) as p                                    O-Insert
2. withdraw(systemPrompt)                                           O-Dispose (provider)
3. provide(systemPrompt)                                            O-Insert (provider)
```

- - settings.presentations web-search-free ({"auto":false}) @p
- - systemPrompt.sections free-search:engines (section) @p
- - tools advanced_search (tool) @p
- - tools cache_search (tool) @p
- - tools domain_search (tool) @p
- - tools free_search_test (tool) @p
- - tools multi_search (tool) @p
- - tools platform_search (tool) @p
- - tools research (tool) @p
- - tools video_search (tool) @p

重放: `sh check.sh replay witnesses/dsh-free-search-restart-systemPrompt.json`

### dsh-free-search-restart-webStartup (第 3 层)

```
1. install(dsh-free-search) as p                                    O-Insert
2. withdraw(webStartup)                                             O-Dispose (provider)
3. provide(webStartup)                                              O-Insert (provider)
```

- + cordis.fibers p/web-search-free#15 (PENDING (waiting: connection.authentication)) @p

重放: `sh check.sh replay witnesses/dsh-free-search-restart-webStartup.json`

### dsh-free-search-restart-web (第 3 层)

```
1. install(dsh-free-search) as p                                    O-Insert
2. withdraw(web)                                                    O-Dispose (provider)
3. provide(web)                                                     O-Insert (provider)
```

- - settings.presentations web-search-free ({"auto":false}) @p
- - systemPrompt.sections free-search:engines (section) @p
- - tools advanced_search (tool) @p
- - tools cache_search (tool) @p
- - tools domain_search (tool) @p
- - tools free_search_test (tool) @p
- - tools multi_search (tool) @p
- - tools platform_search (tool) @p
- - tools research (tool) @p
- - tools video_search (tool) @p

重放: `sh check.sh replay witnesses/dsh-free-search-restart-web.json`

(共 123 次运行, 402.4 秒)
