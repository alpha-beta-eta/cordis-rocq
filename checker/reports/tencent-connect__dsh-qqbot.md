# @tencent-connect/dsh-qqbot@0.5.5

宿主服务: settings, webServer, tools, systemPrompt, credentials, connection, subprocess, sandboxPolicy, layout, typert, sessions, sessionProjections, jobs, uiConversation, sidebarRight, pluginNavigation, slots, settingsScope, locale, commands, theme, agentPresets, fileUpload, fileViewer, typertGateway, uiWorkspace, sidebarRightTabs, sandbox, inputTriggers, desktopPnpm, betterSidebar, workspaceRegistry, workspaceController, webTerminals, webStartup, web, uiSession, terminalController, sessionQuery, agents, sessionController, llm, sessionProjectionCache, storageDomain, sessionPersistence, attachments, subagents, agentDefaultModel, fileReferences, skills

## 装上后

- fiber: p/im-qqbot#0 ACTIVE; p/im-qqbot#1 ACTIVE
- 登记: webServer.routes ×5
- 换成桩的模块: @tencent-connect/qqbot-nodejs (from ../dsh-plugins/tencent-connect__dsh-qqbot/0.5.5/package/lib/gateway/middleware-setup.js), @tencent-connect/qqbot-nodejs (from ../dsh-plugins/tencent-connect__dsh-qqbot/0.5.5/package/lib/features/history-store.js), @tencent-connect/qqbot-nodejs (from ../dsh-plugins/tencent-connect__dsh-qqbot/0.5.5/package/lib/gateway/bootstrap.js), js-yaml (from ../dsh-plugins/tencent-connect__dsh-qqbot/0.5.5/package/lib/model/settings-reader.js), @tencent-connect/qqbot-nodejs (from ../dsh-plugins/tencent-connect__dsh-qqbot/0.5.5/package/lib/transport/reply-target.js), yaml (from ../dsh-plugins/tencent-connect__dsh-qqbot/0.5.5/package/lib/media/vision-tool.js), @tencent-connect/qqbot-connector (from ../dsh-plugins/tencent-connect__dsh-qqbot/0.5.5/package/lib/setup/binding-service.js), yaml (from ../dsh-plugins/tencent-connect__dsh-qqbot/0.5.5/package/lib/setup/persist.js)

## 第 2 层: 装上再卸载

✓ 卸载后与从未安装相同, 再装与第一次装上相同.

## 第 2 层: 中途抛错 (R1)

插件在 apply 期间调用的宿主方法: webServer.register ×5

- ✗ webServer.register: 4/5 个故障点卸载后有残留; 4/5 个故障点之后再装与正常装上不同.
  最小的 k = 2:
  - 卸载后残留 + webServer.routes exact /qqbot/im-qqbot/bind (exact) @p
  - 再装: + webServer.routes exact /qqbot/im-qqbot/bind (exact) @p(旧)
  - 再装: - webServer.routes exact /qqbot/im-qqbot/bind (exact) @p
  - 再装: - webServer.routes exact /qqbot/im-qqbot/bind/manual (exact) @p
  - 再装: - webServer.routes exact /qqbot/im-qqbot/bind/refresh (exact) @p
  - 再装: - webServer.routes exact /qqbot/im-qqbot/bind/unbind (exact) @p
  - 再装: - webServer.routes exact /qqbot/im-qqbot/config (exact) @p
  残留最多的是 k = 5: 4 条.

## 第 3 层: 服务晚到 (C2)

- ✓ 其余 50 个服务晚到时与先到相同.

## 第 3 层: 提供者重启 (C2)

- ✓ 其余 50 个服务重启后与重启前相同.

## 见证

### tencent-connect__dsh-qqbot-fault-webServer.register-2 (第 2 层)

```
1. webServer.register call #2 by p throws                           L-Fail at the k-th call
2. install(tencent-connect__dsh-qqbot) as p                         O-Insert
3. dispose(p)                                                       O-Dispose
4. install(tencent-connect__dsh-qqbot) as p2                        O-Insert
```

- + webServer.routes exact /qqbot/im-qqbot/bind (exact) @p
- reload: + webServer.routes exact /qqbot/im-qqbot/bind (exact) @p(旧)
- reload: - webServer.routes exact /qqbot/im-qqbot/bind (exact) @p
- reload: - webServer.routes exact /qqbot/im-qqbot/bind/manual (exact) @p
- reload: - webServer.routes exact /qqbot/im-qqbot/bind/refresh (exact) @p
- reload: - webServer.routes exact /qqbot/im-qqbot/bind/unbind (exact) @p
- reload: - webServer.routes exact /qqbot/im-qqbot/config (exact) @p
- reload: + cordis.fibers p/im-qqbot#1 (FAILED: duplicate webServer.routes "exact /qqbot/im-qqbot/bind") @p
- reload: - cordis.fibers p/im-qqbot#1 (ACTIVE) @p

重放: `sh check.sh replay witnesses/tencent-connect__dsh-qqbot-fault-webServer.register-2.json`

(共 106 次运行, 414.6 秒)
