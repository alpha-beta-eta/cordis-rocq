# dsh-cost-meter@1.9.85

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/cost-meter#0 ACTIVE; p/cost-meter#1 ACTIVE; p/cost-meter#2 ACTIVE; p/cost-meter#3 FAILED: registry.local.get is not a function
- 登记: cordis.services ×1, cordis.listeners ×11
- 没有桩的调用: loader.entries, locale.getSnapshot, llm.listConfigurableProviders, sessionProjections.register, typert.getPackage
- 换成桩的模块: acorn (from ../dsh-plugins/dsh-cost-meter/1.9.85/package/lib/billion-context-patch.js), zod (from ../dsh-plugins/dsh-cost-meter/1.9.85/package/lib/index.js), zod (from ../dsh-plugins/dsh-cost-meter/1.9.85/package/lib/typert.host.js)
- 注意: 不注入故障时就有 fiber 失败或停在 PENDING, 多半是桩不够真; 以下结论只对能跑到的部分成立.

## 第 2 层: 装上再卸载

- ✗ 进程级改动未恢复: global globalThis.Symbol(dsh-cost-meter.billion-context.peers.v1): (absent) → set
- ✗ 再装与第一次装上不同: - handle Timeout = 1
- ○ 持久状态 (R4, 只报告): + fs storages/cost-meter/billion-context-bridge.json
- ○ 持久状态 (R4, 只报告): + fs storages/cost-meter/ledger.json
- ○ 持久状态 (R4, 只报告): + fs storages/cost-meter/ledger.json.config-bak
- ○ 持久状态 (R4, 只报告): + fs storages/cost-meter/ledger.json.native-search-coverage.json

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: settings.describe ×2

- ✗ settings.describe: 0/2 个故障点卸载后有残留; 2/2 个故障点之后再装与正常装上不同.
  最小的 k = 1:
  - 再装: - handle Timeout = 1

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

### dsh-cost-meter-unload (第 2 层)

```
1. install(dsh-cost-meter) as p                                     O-Insert
2. dispose(p)                                                       O-Dispose
3. install(dsh-cost-meter) as p2                                    O-Insert
```

- global globalThis.Symbol(dsh-cost-meter.billion-context.peers.v1): (absent) → set
- reload: - handle Timeout = 1

重放: `sh check.sh replay witnesses/dsh-cost-meter-unload.json`

### dsh-cost-meter-fault-settings.describe-1 (第 2 层)

```
1. settings.describe call #1 by p throws                            L-Fail at the k-th call
2. install(dsh-cost-meter) as p                                     O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-cost-meter) as p2                                    O-Insert
```

- global globalThis.Symbol(dsh-cost-meter.billion-context.peers.v1): (absent) → set
- reload: - handle Timeout = 1

重放: `sh check.sh replay witnesses/dsh-cost-meter-fault-settings.describe-1.json`

(共 103 次运行, 414.5 秒)
