# dsh-mnemon@0.5.53

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-mnemon#0 FAILED: invalid config:
  - dsh-mnemon: Runtime MEMORY.md limit must be an integer within 1..[stub dsh-mnemon-source-runtime/con
- 登记: (无)
- 换成桩的模块: dsh-mnemon-source-memory-spaces (from ../dsh-plugins/dsh-mnemon/0.5.53/package/lib/index.js), dsh-mnemon-source-memory-spaces/contracts (from ../dsh-plugins/dsh-mnemon/0.5.53/package/lib/index.js), dsh-mnemon-source-runtime/contracts (from ../dsh-plugins/dsh-mnemon/0.5.53/package/lib/index.js), yaml (from ../dsh-plugins/dsh-mnemon/0.5.53/package/lib/index.js), fflate (from ../dsh-plugins/dsh-mnemon/0.5.53/package/lib/index.js), dsh-mnemon-source-documents/contracts (from ../dsh-plugins/dsh-mnemon/0.5.53/package/lib/index.js), dsh-mnemon-source-memory-spaces/space-identity (from ../dsh-plugins/dsh-mnemon/0.5.53/package/lib/index.js), dsh-mnemon-source-memory-spaces/native-cli (from ../dsh-plugins/dsh-mnemon/0.5.53/package/lib/index.js), dsh-mnemon-source-skills/contracts (from ../dsh-plugins/dsh-mnemon/0.5.53/package/lib/index.js), zod (from ../dsh-plugins/dsh-mnemon/0.5.53/package/lib/index.js)
- 注意: 不注入故障时就有 fiber 失败或停在 PENDING, 多半是桩不够真; 以下结论只对能跑到的部分成立.

## 第 2 层: 装上再卸载

✓ 卸载后与从未安装相同, 再装与第一次装上相同.

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: (无)


## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

(共 101 次运行, 107.0 秒)
