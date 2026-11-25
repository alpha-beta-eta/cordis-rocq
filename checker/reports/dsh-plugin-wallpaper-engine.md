# dsh-plugin-wallpaper-engine@1.4.3

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/host:loader#0 ACTIVE
- 登记: webServer.routes ×9, cordis.services ×1
- 换成桩的模块: dsh-plugin-wallpaper-engine-about-notice (from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js), dsh-plugin-wallpaper-engine-mascot-avatar (from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js), dsh-plugin-wallpaper-engine-media-bridge (from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js), dsh-plugin-wallpaper-engine-about-notice (require, from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js), dsh-plugin-wallpaper-engine-mascot-avatar (require, from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js), dsh-plugin-wallpaper-engine-media-bridge (require, from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js), dsh-plugin-wallpaper-engine-pet-link (require, from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js), dsh-plugin-wallpaper-engine-fx (require, from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js), dsh-plugin-wallpaper-engine-parallax (require, from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js), dsh-plugin-wallpaper-engine-fonts (require, from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js), dsh-plugin-wallpaper-engine-glass (require, from ../dsh-plugins/dsh-plugin-wallpaper-engine/1.4.3/package/lib/index.js)

## 第 2 层: 装上再卸载

✓ 卸载后与从未安装相同, 再装与第一次装上相同.

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: webServer.register ×9

- ✓ webServer.register: k = 1..9 都恢复干净, 再装与正常装上相同.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

(共 110 次运行, 258.8 秒)
