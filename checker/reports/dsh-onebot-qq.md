# dsh-onebot-qq@0.11.0

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-onebot#0 ACTIVE
- 登记: cordis.listeners ×2
- 没有桩的调用: loader.await
- 换成桩的模块: ws (from ../dsh-plugins/dsh-onebot-qq/0.11.0/package/lib/connection.js), @napi-rs/canvas (from ../dsh-plugins/dsh-onebot-qq/0.11.0/package/lib/t2i/canvas.js), @napi-rs/canvas (from ../dsh-plugins/dsh-onebot-qq/0.11.0/package/lib/t2i/fonts.js), @napi-rs/canvas (from ../dsh-plugins/dsh-onebot-qq/0.11.0/package/lib/image-shrink.js), zod (from packages/core/agent/src/projection.ts), zod (from packages/core/agent/src/model-selection.ts)

## 第 2 层: 装上再卸载

- ○ 持久状态 (R4, 只报告): + fs media/onebot/chat-sessions.json

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: (无)


## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

(共 101 次运行, 132.0 秒)
