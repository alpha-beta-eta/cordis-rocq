# ds-harness-remote@0.6.7

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/activateWhenCarrierReady#0 ACTIVE; p/activateWhenCarrierReady#1 ACTIVE; p/ds-harness-remote#0 ACTIVE; p/ds-harness-remote#1 ACTIVE; p/scope#0 ACTIVE
- 登记: settings.presentations ×1, tools ×13, webServer.routes ×1, cordis.services ×1
- 没有桩的调用: loader.locate, loader.entries
- 换成桩的模块: zod (from packages/client/connection/src/rpc-schema.ts), bufferutil (require, from ../dsh-plugins/ds-harness-remote/0.6.7/package/dist/index.js)

## 第 2 层: 装上再卸载

- ✗ 进程级改动未恢复: global globalThis.Symbol(ds-harness-remote.hmr-safe-settings-pump): (absent) → set
- ✗ 进程级改动未恢复: global globalThis.__zod_globalConfig: (absent) → set
- ✗ 进程级改动未恢复: global globalThis.__zod_globalRegistry: (absent) → set
- ○ 持久状态 (R4, 只报告): + fs .ds-harness-remote-migration/credential-refresh-gate
- ○ 持久状态 (R4, 只报告): + fs ds-harness-remote/device.json
- ○ 持久状态 (R4, 只报告): + fs ds-harness-remote/device.key
- ○ 持久状态 (R4, 只报告): + fs ds-harness-remote/trusted-peers.json
- ○ 持久状态 (R4, 只报告): + fs logs/ds-harness-remote/host.log

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: settings.configure ×1, webServer.register ×1, tools.register ×13

- ✓ settings.configure: k = 1..1 都恢复干净, 再装与正常装上相同.
- ✓ webServer.register: k = 1..1 都恢复干净, 再装与正常装上相同.
- ✓ tools.register: k = 1..13 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✗ webServer 在插件之后出现时, 落定状态不同:
  - - tools remote_create_session (tool) @p
  - - tools remote_download_file (tool) @p
  - - tools remote_get_operation (tool) @p
  - - tools remote_interrupt_session (tool) @p
  - - tools remote_list_hosts (tool) @p
  - - tools remote_list_presets (tool) @p
  - - tools remote_list_sessions (tool) @p
  - - tools remote_list_workspaces (tool) @p
- ✓ 其余 49 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✗ webServer 的提供者重启后, 落定状态不同:
  - - webServer.routes prefix /ds-harness-remote (prefix) @p
- ✓ 其余 49 个服务重启后与重启前相同.

## 见证

### ds-harness-remote-unload (第 2 层)

```
1. install(ds-harness-remote) as p                                  O-Insert
2. dispose(p)                                                       O-Dispose
3. install(ds-harness-remote) as p2                                 O-Insert
```

- global globalThis.Symbol(ds-harness-remote.hmr-safe-settings-pump): (absent) → set
- global globalThis.__zod_globalConfig: (absent) → set
- global globalThis.__zod_globalRegistry: (absent) → set

重放: `sh check.sh replay witnesses/ds-harness-remote-unload.json`

### ds-harness-remote-late-webServer (第 3 层)

```
1. install(ds-harness-remote) as p                                  O-Insert
2. provide(webServer)                                               O-Insert (provider)
```

- - tools remote_create_session (tool) @p
- - tools remote_download_file (tool) @p
- - tools remote_get_operation (tool) @p
- - tools remote_interrupt_session (tool) @p
- - tools remote_list_hosts (tool) @p
- - tools remote_list_presets (tool) @p
- - tools remote_list_sessions (tool) @p
- - tools remote_list_workspaces (tool) @p
- - tools remote_read_session (tool) @p
- - tools remote_select_preset (tool) @p

重放: `sh check.sh replay witnesses/ds-harness-remote-late-webServer.json`

### ds-harness-remote-restart-webServer (第 3 层)

```
1. install(ds-harness-remote) as p                                  O-Insert
2. withdraw(webServer)                                              O-Dispose (provider)
3. provide(webServer)                                               O-Insert (provider)
```

- - webServer.routes prefix /ds-harness-remote (prefix) @p

重放: `sh check.sh replay witnesses/ds-harness-remote-restart-webServer.json`

(共 116 次运行, 309.4 秒)
