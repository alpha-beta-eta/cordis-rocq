# dsh-whale-widget@0.4.2

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/whale-balance-widget#0 ACTIVE; p/whale-balance-widget#1 ACTIVE
- 登记: webServer.indexTaps[] ×1, webServer.routes ×26, cordis.listeners ×5

## 第 2 层: 装上再卸载

- ✗ 进程级改动未恢复: dns dns.defaultResultOrder: verbatim → ipv4first

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: webServer.register ×26, webServer.tapIndex ×1

- ✗ webServer.register: 25/26 个故障点卸载后有残留; 25/26 个故障点之后再装与正常装上不同.
  最小的 k = 2:
  - 卸载后残留 + webServer.routes exact /dsh-whale/image.png (exact) @p
  - 再装: webServer.indexTaps[]: [tap] → []
  - 再装: + webServer.routes exact /dsh-whale/image.png (exact) @p(旧)
  - 再装: - webServer.routes exact /dsh-whale/about.json (exact) @p
  - 再装: - webServer.routes exact /dsh-whale/api-models.json (exact) @p
  - 再装: - webServer.routes exact /dsh-whale/audio-fragment (exact) @p
  - 再装: - webServer.routes exact /dsh-whale/audio-fragment.wav (exact) @p
  残留最多的是 k = 26: 25 条.
- ✗ webServer.tapIndex: 1/1 个故障点卸载后有残留; 1/1 个故障点之后再装与正常装上不同.
  最小的 k = 1:
  - 卸载后残留 + webServer.routes exact /dsh-whale/about.json (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-whale/api-models.json (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-whale/audio-fragment (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-whale/audio-fragment.wav (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-whale/audio.json (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-whale/balance-adjustments.json (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-whale/balance.json (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-whale/bubble-img-upload.json (exact) @p
  - … 共 26 条
  - 再装: webServer.indexTaps[]: [tap] → []
  - 再装: + webServer.routes exact /dsh-whale/about.json (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-whale/api-models.json (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-whale/audio-fragment (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-whale/audio-fragment.wav (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-whale/audio.json (exact) @p(旧)

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

### dsh-whale-widget-unload (第 2 层)

```
1. install(dsh-whale-widget) as p                                   O-Insert
2. dispose(p)                                                       O-Dispose
3. install(dsh-whale-widget) as p2                                  O-Insert
```

- dns dns.defaultResultOrder: verbatim → ipv4first

重放: `sh check.sh replay witnesses/dsh-whale-widget-unload.json`

### dsh-whale-widget-fault-webServer.register-2 (第 2 层)

```
1. webServer.register call #2 by p throws                           L-Fail at the k-th call
2. install(dsh-whale-widget) as p                                   O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-whale-widget) as p2                                  O-Insert
```

- + webServer.routes exact /dsh-whale/image.png (exact) @p
- dns dns.defaultResultOrder: verbatim → ipv4first
- reload: webServer.indexTaps[]: [tap] → []
- reload: + webServer.routes exact /dsh-whale/image.png (exact) @p(旧)
- reload: - webServer.routes exact /dsh-whale/about.json (exact) @p
- reload: - webServer.routes exact /dsh-whale/api-models.json (exact) @p
- reload: - webServer.routes exact /dsh-whale/audio-fragment (exact) @p
- reload: - webServer.routes exact /dsh-whale/audio-fragment.wav (exact) @p
- reload: - webServer.routes exact /dsh-whale/audio.json (exact) @p
- reload: - webServer.routes exact /dsh-whale/balance-adjustments.json (exact) @p

重放: `sh check.sh replay witnesses/dsh-whale-widget-fault-webServer.register-2.json`

### dsh-whale-widget-fault-webServer.tapIndex-1 (第 2 层)

```
1. webServer.tapIndex call #1 by p throws                           L-Fail at the k-th call
2. install(dsh-whale-widget) as p                                   O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-whale-widget) as p2                                  O-Insert
```

- + webServer.routes exact /dsh-whale/about.json (exact) @p
- + webServer.routes exact /dsh-whale/api-models.json (exact) @p
- + webServer.routes exact /dsh-whale/audio-fragment (exact) @p
- + webServer.routes exact /dsh-whale/audio-fragment.wav (exact) @p
- + webServer.routes exact /dsh-whale/audio.json (exact) @p
- + webServer.routes exact /dsh-whale/balance-adjustments.json (exact) @p
- + webServer.routes exact /dsh-whale/balance.json (exact) @p
- + webServer.routes exact /dsh-whale/bubble-img-upload.json (exact) @p
- + webServer.routes exact /dsh-whale/bubble-img.png (exact) @p
- + webServer.routes exact /dsh-whale/bubble-imgs.json (exact) @p

重放: `sh check.sh replay witnesses/dsh-whale-widget-fault-webServer.tapIndex-1.json`

(共 128 次运行, 397.2 秒)
