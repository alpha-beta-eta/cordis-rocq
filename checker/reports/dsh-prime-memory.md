# dsh-prime-memory@0.26.72

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-memory-plugin#0 ACTIVE; p/dsh-memory-plugin#1 ACTIVE; p/dsh-memory-plugin#2 ACTIVE; p/dsh-memory-plugin#3 ACTIVE; p/dsh-memory-plugin#4 ACTIVE; p/dsh-memory-plugin#5 ACTIVE
- 登记: settings.presentations ×1, tools ×16, webServer.routes ×1, cordis.listeners ×6
- 没有桩的调用: commands.register, agentDefaultModel.currentSelection, agents.list, sessionProjections.register
- 换成桩的模块: undici (from ../dsh-plugins/dsh-prime-memory/0.26.72/package/dist/store/download-queue.js), @node-rs/jieba (require, from ../dsh-plugins/dsh-prime-memory/0.26.72/package/dist/util/tokenizer.js), @node-rs/jieba/dict (require, from ../dsh-plugins/dsh-prime-memory/0.26.72/package/dist/util/tokenizer.js)

## 第 2 层: 装上再卸载

- ✗ 进程级改动未恢复: listener process.on(beforeExit): 0 → 1
- ✗ 再装与第一次装上不同: + listener process.on(beforeExit) = 2
- ✗ 再装与第一次装上不同: - listener process.on(beforeExit) = 1
- ○ 持久状态 (R4, 只报告): + fs memory/memory.db
- ○ 持久状态 (R4, 只报告): + fs memory/memory.log

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: settings.configure ×1, tools.register ×16, webServer.register ×1

- ✗ settings.configure: 0/1 个故障点卸载后有残留; 1/1 个故障点之后再装与正常装上不同.
  最小的 k = 1:
  - 再装: + listener process.on(beforeExit) = 2
  - 再装: - listener process.on(beforeExit) = 1
- ✗ tools.register: 0/16 个故障点卸载后有残留; 16/16 个故障点之后再装与正常装上不同.
  最小的 k = 1:
  - 再装: + listener process.on(beforeExit) = 2
  - 再装: - listener process.on(beforeExit) = 1
- ✗ webServer.register: 0/1 个故障点卸载后有残留; 1/1 个故障点之后再装与正常装上不同.
  最小的 k = 1:
  - 再装: + listener process.on(beforeExit) = 2
  - 再装: - listener process.on(beforeExit) = 1

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✗ webServer 的提供者重启后, 落定状态不同:
  - + listener process.on(beforeExit) = 2
  - - listener process.on(beforeExit) = 1
- ✗ tools 的提供者重启后, 落定状态不同:
  - + listener process.on(beforeExit) = 2
  - - listener process.on(beforeExit) = 1
- ✗ systemPrompt 的提供者重启后, 落定状态不同:
  - + listener process.on(beforeExit) = 2
  - - listener process.on(beforeExit) = 1
- ✗ credentials 的提供者重启后, 落定状态不同:
  - + listener process.on(beforeExit) = 2
  - - listener process.on(beforeExit) = 1
- ✗ connection 的提供者重启后, 落定状态不同:
  - + listener process.on(beforeExit) = 2
  - - listener process.on(beforeExit) = 1
- ✗ webStartup 的提供者重启后, 落定状态不同:
  - + listener process.on(beforeExit) = 2
  - - listener process.on(beforeExit) = 1
- ✗ llm 的提供者重启后, 落定状态不同:
  - + listener process.on(beforeExit) = 2
  - - listener process.on(beforeExit) = 1
- ✓ 其余 43 个服务重启后与重启前相同.

## 见证

### dsh-prime-memory-unload (第 2 层)

```
1. install(dsh-prime-memory) as p                                   O-Insert
2. dispose(p)                                                       O-Dispose
3. install(dsh-prime-memory) as p2                                  O-Insert
```

- listener process.on(beforeExit): 0 → 1
- reload: + listener process.on(beforeExit) = 2
- reload: - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-unload.json`

### dsh-prime-memory-fault-settings.configure-1 (第 2 层)

```
1. settings.configure call #1 by p throws                           L-Fail at the k-th call
2. install(dsh-prime-memory) as p                                   O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-prime-memory) as p2                                  O-Insert
```

- listener process.on(beforeExit): 0 → 1
- reload: + listener process.on(beforeExit) = 2
- reload: - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-fault-settings.configure-1.json`

### dsh-prime-memory-fault-tools.register-1 (第 2 层)

```
1. tools.register call #1 by p throws                               L-Fail at the k-th call
2. install(dsh-prime-memory) as p                                   O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-prime-memory) as p2                                  O-Insert
```

- listener process.on(beforeExit): 0 → 1
- reload: + listener process.on(beforeExit) = 2
- reload: - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-fault-tools.register-1.json`

### dsh-prime-memory-fault-webServer.register-1 (第 2 层)

```
1. webServer.register call #1 by p throws                           L-Fail at the k-th call
2. install(dsh-prime-memory) as p                                   O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-prime-memory) as p2                                  O-Insert
```

- listener process.on(beforeExit): 0 → 1
- reload: + listener process.on(beforeExit) = 2
- reload: - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-fault-webServer.register-1.json`

### dsh-prime-memory-restart-webServer (第 3 层)

```
1. install(dsh-prime-memory) as p                                   O-Insert
2. withdraw(webServer)                                              O-Dispose (provider)
3. provide(webServer)                                               O-Insert (provider)
```

- + listener process.on(beforeExit) = 2
- - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-restart-webServer.json`

### dsh-prime-memory-restart-tools (第 3 层)

```
1. install(dsh-prime-memory) as p                                   O-Insert
2. withdraw(tools)                                                  O-Dispose (provider)
3. provide(tools)                                                   O-Insert (provider)
```

- + listener process.on(beforeExit) = 2
- - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-restart-tools.json`

### dsh-prime-memory-restart-systemPrompt (第 3 层)

```
1. install(dsh-prime-memory) as p                                   O-Insert
2. withdraw(systemPrompt)                                           O-Dispose (provider)
3. provide(systemPrompt)                                            O-Insert (provider)
```

- + listener process.on(beforeExit) = 2
- - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-restart-systemPrompt.json`

### dsh-prime-memory-restart-credentials (第 3 层)

```
1. install(dsh-prime-memory) as p                                   O-Insert
2. withdraw(credentials)                                            O-Dispose (provider)
3. provide(credentials)                                             O-Insert (provider)
```

- + listener process.on(beforeExit) = 2
- - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-restart-credentials.json`

### dsh-prime-memory-restart-connection (第 3 层)

```
1. install(dsh-prime-memory) as p                                   O-Insert
2. withdraw(connection)                                             O-Dispose (provider)
3. provide(connection)                                              O-Insert (provider)
```

- + listener process.on(beforeExit) = 2
- - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-restart-connection.json`

### dsh-prime-memory-restart-webStartup (第 3 层)

```
1. install(dsh-prime-memory) as p                                   O-Insert
2. withdraw(webStartup)                                             O-Dispose (provider)
3. provide(webStartup)                                              O-Insert (provider)
```

- + listener process.on(beforeExit) = 2
- - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-restart-webStartup.json`

### dsh-prime-memory-restart-llm (第 3 层)

```
1. install(dsh-prime-memory) as p                                   O-Insert
2. withdraw(llm)                                                    O-Dispose (provider)
3. provide(llm)                                                     O-Insert (provider)
```

- + listener process.on(beforeExit) = 2
- - listener process.on(beforeExit) = 1

重放: `sh check.sh replay witnesses/dsh-prime-memory-restart-llm.json`

(共 119 次运行, 620.4 秒)
