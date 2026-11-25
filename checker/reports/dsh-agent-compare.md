# dsh-agent-compare@3.3.0

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/agent-compare#0 ACTIVE; p/agent-compare#1 ACTIVE; p/agent-compare#2 ACTIVE
- 登记: tools ×2, webServer.routes ×1, cordis.listeners ×2
- 没有桩的调用: commands.register

## 第 2 层: 装上再卸载

✓ 卸载后与从未安装相同, 再装与第一次装上相同.

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: tools.register ×2, webServer.register ×1

- ✓ tools.register: k = 1..2 都恢复干净, 再装与正常装上相同.
- ✓ webServer.register: k = 1..1 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

(共 104 次运行, 292.1 秒)
