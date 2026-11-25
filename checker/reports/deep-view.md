# deep-view@0.1.2

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/deep-view#0 ACTIVE
- 登记: connection.fetchRoutes ×1, tools ×1, cordis.listeners ×1

## 第 2 层: 装上再卸载

✓ 卸载后与从未安装相同, 再装与第一次装上相同.

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: tools.register ×1, connection.fetch.register ×1

- ✓ tools.register: k = 1..1 都恢复干净, 再装与正常装上相同.
- ✓ connection.fetch.register: k = 1..1 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

(共 103 次运行, 211.0 秒)
