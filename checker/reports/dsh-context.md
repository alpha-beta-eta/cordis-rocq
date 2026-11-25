# dsh-context@0.87.1

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-context#0 ACTIVE; p/dsh-context#1 ACTIVE; p/dsh-context#10 ACTIVE; p/dsh-context#11 ACTIVE; p/dsh-context#12 ACTIVE; p/dsh-context#13 ACTIVE; p/dsh-context#14 ACTIVE; p/dsh-context#15 ACTIVE; p/dsh-context#16 ACTIVE; p/dsh-context#17 ACTIVE; p/dsh-context#18 ACTIVE; p/dsh-context#2 ACTIVE; p/dsh-context#3 ACTIVE; p/dsh-context#4 ACTIVE; p/dsh-context#5 ACTIVE; p/dsh-context#6 ACTIVE; p/dsh-context#7 ACTIVE; p/dsh-context#8 ACTIVE; p/dsh-context#9 ACTIVE
- 登记: connection.fetchRoutes ×15, systemPrompt.sections ×2, cordis.listeners ×4
- 没有桩的调用: sessionProjections.register, storageDomain.get, sessionQuery.listSessions
- 换成桩的模块: zod (from ../dsh-plugins/dsh-context/0.87.1/package/lib/index.js)

## 第 2 层: 装上再卸载

✓ 卸载后与从未安装相同, 再装与第一次装上相同.

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: connection.fetch.register ×15, systemPrompt.section ×2

- ✓ connection.fetch.register: k = 1..15 都恢复干净, 再装与正常装上相同.
- ✓ systemPrompt.section: k = 1..2 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

(共 118 次运行, 194.7 秒)
