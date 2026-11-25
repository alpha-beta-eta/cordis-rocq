# dsh-ops@0.5.5

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/dsh-ops#0 ACTIVE; p/dsh-ops#1 ACTIVE; p/dsh-ops/consumer-cordis#0 ACTIVE; p/dsh-ops/consumer-cordis#1 ACTIVE; p/dsh-ops/consumer-cordis#2 ACTIVE; p/dsh-ops/consumer-cordis#3 ACTIVE; p/dsh-ops/consumer-minimal#0 ACTIVE; p/dsh-ops/consumer-minimal#1 ACTIVE; p/dsh-ops/consumer-ops-ptc#0 ACTIVE; p/dsh-ops/consumer-ops-ptc#1 ACTIVE; p/dsh-ops/consumer-ptc#0 ACTIVE; p/dsh-ops/consumer-ptc#1 ACTIVE; p/dsh-ops/consumer-standard#0 ACTIVE; p/dsh-ops/consumer-standard#1 ACTIVE; p/dsh-ops/consumer-standard#2 ACTIVE; p/dsh-ops/consumer-standard#3 ACTIVE; p/dsh-ops/runtime-settings#0 ACTIVE; p/dsh-ops/runtime-settings#1 ACTIVE
- 登记: systemPrompt.sections ×7, cordis.services ×1, cordis.listeners ×7
- 没有桩的调用: typert.register, agents.list
- 换成桩的模块: js-yaml (from packages/boot/app-boot/src/index.ts), @deepseek-ai/cordis-plugin-loader (from packages/boot/app-boot/src/index.ts), @deepseek-ai/cordis-plugin-include (from packages/boot/app-boot/src/index.ts), @deepseek-ai/cordis-plugin-group (from packages/boot/app-boot/src/index.ts), @deepseek-ai/cordis-plugin-include (from packages/boot/app-boot/src/profile.ts), semver (from packages/boot/app-boot/src/plugin-compatibility.ts), semver (from packages/boot/app-boot/src/profile-compatibility.ts), @deepseek-ai/cordis-plugin-include (from packages/boot/app-boot/src/compatibility-preflight.ts), js-yaml (from packages/boot/app-boot/src/compatibility-preflight.ts), @deepseek-ai/cordis-plugin-loader (from packages/boot/app-boot/src/package-meta.ts), resolve.exports (from packages/boot/app-boot/src/profile-resolution/resolver.ts), js-yaml (from packages/boot/app-boot/src/config-schema/collect.ts), @deepseek-ai/cordis-plugin-loader (from packages/boot/app-boot/src/config-schema/collect.ts), @deepseek-ai/cordis-plugin-group (from packages/boot/app-boot/src/config-schema/collect.ts), @deepseek-ai/cordis-plugin-include (from packages/boot/app-boot/src/config-schema/collect.ts)

## 第 2 层: 装上再卸载

✓ 卸载后与从未安装相同, 再装与第一次装上相同.

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: systemPrompt.section ×7

- ✗ systemPrompt.section: 0/7 个故障点卸载后有残留; 5/7 个故障点之后再装与正常装上不同.
  最小的 k = 2:
  - 再装: + systemPrompt.sections dsh-ops:repository-tooling:mode-ptc:3 (section) @p
  - 再装: + systemPrompt.sections dsh-ops:repository-tooling:mode-ptc:4 (section) @p
  - 再装: - systemPrompt.sections dsh-ops:repository-tooling:mode-ptc (section) @p
  - 再装: - systemPrompt.sections dsh-ops:repository-tooling:mode-ptc:2 (section) @p

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

### dsh-ops-fault-systemPrompt.section-2 (第 2 层)

```
1. systemPrompt.section call #2 by p throws                         L-Fail at the k-th call
2. install(dsh-ops) as p                                            O-Insert
3. dispose(p)                                                       O-Dispose
4. install(dsh-ops) as p2                                           O-Insert
```

- reload: + systemPrompt.sections dsh-ops:repository-tooling:mode-ptc:3 (section) @p
- reload: + systemPrompt.sections dsh-ops:repository-tooling:mode-ptc:4 (section) @p
- reload: - systemPrompt.sections dsh-ops:repository-tooling:mode-ptc (section) @p
- reload: - systemPrompt.sections dsh-ops:repository-tooling:mode-ptc:2 (section) @p

重放: `sh check.sh replay witnesses/dsh-ops-fault-systemPrompt.section-2.json`

(共 108 次运行, 419.4 秒)
