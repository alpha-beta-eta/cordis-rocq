# @xmanrui/dsh-im@5.10.0

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/$#0 ACTIVE; p/$#1 ACTIVE; p/$#2 ACTIVE; p/a#0 ACTIVE; p/dsh-im-host#0 ACTIVE; p/dsh-im-host#1 ACTIVE; p/q#0 ACTIVE
- 登记: connection.fetchRoutes ×19, systemPrompt.contexts ×3, tools ×3, webServer.routes ×1, cordis.services ×1, cordis.listeners ×12
- 没有桩的调用: sessions.list, agentPresets.list, typertGateway.invoke
- 换成桩的模块: qrcode (from ../dsh-plugins/xmanrui__dsh-im/5.10.0/package/lib/index.js), @tencent-connect/qqbot-nodejs (from ../dsh-plugins/xmanrui__dsh-im/5.10.0/package/lib/index.js), @tencent-connect/qqbot-connector (from ../dsh-plugins/xmanrui__dsh-im/5.10.0/package/lib/index.js), undici (from ../dsh-plugins/xmanrui__dsh-im/5.10.0/package/lib/index.js), @wecom/aibot-node-sdk (from ../dsh-plugins/xmanrui__dsh-im/5.10.0/package/lib/index.js), imapflow (from ../dsh-plugins/xmanrui__dsh-im/5.10.0/package/lib/index.js), mailparser (from ../dsh-plugins/xmanrui__dsh-im/5.10.0/package/lib/index.js), nodemailer (from ../dsh-plugins/xmanrui__dsh-im/5.10.0/package/lib/index.js), supports-color (require, from ../dsh-plugins/xmanrui__dsh-im/5.10.0/package/lib/index.js), bufferutil (require, from ../dsh-plugins/xmanrui__dsh-im/5.10.0/package/lib/index.js)

## 第 2 层: 装上再卸载

- ✗ 进程级改动未恢复: listener process.on(exit): 0 → 1
- ○ 持久状态 (R4, 只报告): + fs integrations/dsh-im/group-history.sqlite

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: settings.describe ×2, connection.fetch.register ×19, tools.register ×3, systemPrompt.context ×3, webServer.register ×1

- ✓ settings.describe: k = 1..2 都恢复干净, 再装与正常装上相同.
- ✓ connection.fetch.register: k = 1..19 都恢复干净, 再装与正常装上相同.
- ✓ tools.register: k = 1..3 都恢复干净, 再装与正常装上相同.
- ✓ systemPrompt.context: k = 1..3 都恢复干净, 再装与正常装上相同.
- ✓ webServer.register: k = 1..1 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

### xmanrui__dsh-im-unload (第 2 层)

```
1. install(xmanrui__dsh-im) as p                                    O-Insert
2. dispose(p)                                                       O-Dispose
3. install(xmanrui__dsh-im) as p2                                   O-Insert
```

- listener process.on(exit): 0 → 1

重放: `sh check.sh replay witnesses/xmanrui__dsh-im-unload.json`

(共 129 次运行, 401.9 秒)
