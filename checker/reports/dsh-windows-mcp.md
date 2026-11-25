# dsh-windows-mcp@0.2.11

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-windows-mcp#0 ACTIVE; p/dsh-windows-mcp#1 ACTIVE; p/dsh-windows-mcp#2 ACTIVE; p/dsh-windows-mcp#3 ACTIVE; p/dsh-windows-mcp#4 ACTIVE
- 登记: tools ×2, tools.guards[] ×1, webServer.routes ×6, cordis.listeners ×5

## 第 2 层: 装上再卸载

- ✗ 残留登记: + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p
- ✗ 残留登记: + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p
- ✗ 残留登记: + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p
- ✗ 残留登记: + webServer.routes exact /dsh-windows-mcp/settings (exact) @p
- ✗ 残留登记: + webServer.routes exact /dsh-windows-mcp/state (exact) @p
- ✗ 残留登记: + webServer.routes exact /dsh-windows-mcp/update (exact) @p
- ✗ 再装与第一次装上不同: + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p(旧)
- ✗ 再装与第一次装上不同: + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p(旧)
- ✗ 再装与第一次装上不同: + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p(旧)
- ✗ 再装与第一次装上不同: + webServer.routes exact /dsh-windows-mcp/settings (exact) @p(旧)
- ✗ 再装与第一次装上不同: + webServer.routes exact /dsh-windows-mcp/state (exact) @p(旧)
- ✗ 再装与第一次装上不同: + webServer.routes exact /dsh-windows-mcp/update (exact) @p(旧)
- ✗ 再装与第一次装上不同: - webServer.routes exact /dsh-windows-mcp/bridge (exact) @p
- ✗ 再装与第一次装上不同: - webServer.routes exact /dsh-windows-mcp/prepare (exact) @p
- ✗ 再装与第一次装上不同: - webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p
- ✗ 再装与第一次装上不同: - webServer.routes exact /dsh-windows-mcp/settings (exact) @p
- ✗ 再装与第一次装上不同: - webServer.routes exact /dsh-windows-mcp/state (exact) @p
- ✗ 再装与第一次装上不同: - webServer.routes exact /dsh-windows-mcp/update (exact) @p
- ○ 持久状态 (R4, 只报告): + fs dsh-windows-mcp.versions.json

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: tools.register ×2, webServer.register ×6, tools.guard ×1

- ✗ tools.register: 2/2 个故障点卸载后有残留; 2/2 个故障点之后再装与正常装上不同.
  最小的 k = 1:
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/settings (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/state (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/update (exact) @p
  - 再装: + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-windows-mcp/settings (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-windows-mcp/state (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-windows-mcp/update (exact) @p(旧)
- ✗ webServer.register: 5/6 个故障点卸载后有残留; 5/6 个故障点之后再装与正常装上不同.
  最小的 k = 2:
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/state (exact) @p
  - 再装: + webServer.routes exact /dsh-windows-mcp/state (exact) @p(旧)
  - 再装: - webServer.routes exact /dsh-windows-mcp/bridge (exact) @p
  - 再装: - webServer.routes exact /dsh-windows-mcp/prepare (exact) @p
  - 再装: - webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p
  - 再装: - webServer.routes exact /dsh-windows-mcp/settings (exact) @p
  - 再装: - webServer.routes exact /dsh-windows-mcp/state (exact) @p
  残留最多的是 k = 6: 5 条.
- ✗ tools.guard: 1/1 个故障点卸载后有残留; 1/1 个故障点之后再装与正常装上不同.
  最小的 k = 1:
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/settings (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/state (exact) @p
  - 卸载后残留 + webServer.routes exact /dsh-windows-mcp/update (exact) @p
  - 再装: + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-windows-mcp/settings (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-windows-mcp/state (exact) @p(旧)
  - 再装: + webServer.routes exact /dsh-windows-mcp/update (exact) @p(旧)

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

### dsh-windows-mcp-unload (第 2 层)

```
1. install(dsh-windows-mcp) as p                                    O-Insert
2. dispose(p)                                                       O-Dispose
3. install(dsh-windows-mcp) as p2                                   O-Insert
```

- + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p
- + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p
- + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p
- + webServer.routes exact /dsh-windows-mcp/settings (exact) @p
- + webServer.routes exact /dsh-windows-mcp/state (exact) @p
- + webServer.routes exact /dsh-windows-mcp/update (exact) @p
- reload: + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p(旧)
- reload: + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p(旧)
- reload: + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p(旧)
- reload: + webServer.routes exact /dsh-windows-mcp/settings (exact) @p(旧)

重放: `sh check.sh replay witnesses/dsh-windows-mcp-unload.json`

### dsh-windows-mcp-fault-tools.register-1 (第 2 层)

```
1. tools.register call #1 by p throws                               L-Fail at the k-th call
2. install(dsh-windows-mcp) as p                                    O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-windows-mcp) as p2                                   O-Insert
```

- + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p
- + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p
- + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p
- + webServer.routes exact /dsh-windows-mcp/settings (exact) @p
- + webServer.routes exact /dsh-windows-mcp/state (exact) @p
- + webServer.routes exact /dsh-windows-mcp/update (exact) @p
- reload: + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p(旧)
- reload: + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p(旧)
- reload: + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p(旧)
- reload: + webServer.routes exact /dsh-windows-mcp/settings (exact) @p(旧)

重放: `sh check.sh replay witnesses/dsh-windows-mcp-fault-tools.register-1.json`

### dsh-windows-mcp-fault-webServer.register-2 (第 2 层)

```
1. webServer.register call #2 by p throws                           L-Fail at the k-th call
2. install(dsh-windows-mcp) as p                                    O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-windows-mcp) as p2                                   O-Insert
```

- + webServer.routes exact /dsh-windows-mcp/state (exact) @p
- reload: + webServer.routes exact /dsh-windows-mcp/state (exact) @p(旧)
- reload: - webServer.routes exact /dsh-windows-mcp/bridge (exact) @p
- reload: - webServer.routes exact /dsh-windows-mcp/prepare (exact) @p
- reload: - webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p
- reload: - webServer.routes exact /dsh-windows-mcp/settings (exact) @p
- reload: - webServer.routes exact /dsh-windows-mcp/state (exact) @p
- reload: - webServer.routes exact /dsh-windows-mcp/update (exact) @p

重放: `sh check.sh replay witnesses/dsh-windows-mcp-fault-webServer.register-2.json`

### dsh-windows-mcp-fault-tools.guard-1 (第 2 层)

```
1. tools.guard call #1 by p throws                                  L-Fail at the k-th call
2. install(dsh-windows-mcp) as p                                    O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-windows-mcp) as p2                                   O-Insert
```

- + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p
- + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p
- + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p
- + webServer.routes exact /dsh-windows-mcp/settings (exact) @p
- + webServer.routes exact /dsh-windows-mcp/state (exact) @p
- + webServer.routes exact /dsh-windows-mcp/update (exact) @p
- reload: + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p(旧)
- reload: + webServer.routes exact /dsh-windows-mcp/prepare (exact) @p(旧)
- reload: + webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p(旧)
- reload: + webServer.routes exact /dsh-windows-mcp/settings (exact) @p(旧)

重放: `sh check.sh replay witnesses/dsh-windows-mcp-fault-tools.guard-1.json`

(共 110 次运行, 400.7 秒)
