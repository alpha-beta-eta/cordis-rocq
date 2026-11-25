# dsh-image-gen@0.11.4

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-image-gen#0 ACTIVE; p/dsh-image-gen#1 ACTIVE; p/dsh-image-gen#2 ACTIVE; p/dsh-image-gen#3 ACTIVE; p/dsh-image-gen#4 ACTIVE; p/dsh-image-gen#5 ACTIVE; p/dsh-image-gen#6 ACTIVE
- 登记: systemPrompt.contexts ×2, tools ×6, webServer.routes ×21, cordis.listeners ×2

## 第 2 层: 装上再卸载

✓ 卸载后与从未安装相同, 再装与第一次装上相同.

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: tools.register ×6, webServer.register ×21, systemPrompt.context ×2

- ✓ tools.register: k = 1..6 都恢复干净, 再装与正常装上相同.
- ✓ webServer.register: k = 1..21 都恢复干净, 再装与正常装上相同.
- ✓ systemPrompt.context: k = 1..2 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

(共 130 次运行, 152.0 秒)
