# 加载与卸载普查

宿主服务: 50 个 (默认); 插件: 26 个

| 插件 | 加载 | fiber (ACTIVE/全部) | 装上后的登记 | 卸载后残留 | 进程级改动 | 没有桩的调用 | 换成桩的模块 |
|---|---|---|---|---|---|---|---|
| deep-view | ✓ | 1/1 | connection.fetchRoutes×1 tools×1 cordis.listeners×1 | — | — | 0 | 0 |
| ds-harness-remote | ✓ | 3/4 (未激活: LOADING) | settings.presentations×1 webServer.routes×1 cordis.services×1 | — | global globalThis.Symbol(ds-harness-remote.hmr-safe-settings-pump): (absent) → set<br>global globalThis.__zod_globalConfig: (absent) → set<br>global globalThis.__zod_globalRegistry: (absent) → set | 2 | 1 |
| dsh-agent-compare | ✓ | 3/3 | tools×2 webServer.routes×1 cordis.listeners×2 | — | — | 1 | 15 |
| dsh-connect-workbuddy | ✓ | 8/8 | settings.presentations×1 webServer.routes×16 cordis.listeners×2 | — | — | 3 | 8 |
| dsh-context | ✓ | 19/19 | connection.fetchRoutes×15 systemPrompt.sections×2 cordis.listeners×4 | — | — | 3 | 1 |
| dsh-cost-meter | ✓ | 3/4 (未激活: FAILED: registry.local.get is not a function) | cordis.services×1 cordis.listeners×11 | — | global globalThis.Symbol(dsh-cost-meter.billion-context.peers.v1): (absent) → set | 5 | 3 |
| dsh-free-search | ✓ | 14/15 (未激活: PENDING (waiting: connection.authentication)) | settings.presentations×1 systemPrompt.sections×1 tools×9 webServer.routes×10 cordis.listeners×1 | — | — | 2 | 2 |
| dsh-genui | ✓ | 2/2 | systemPrompt.sections×1 webServer.routes×3 | — | — | 0 | 0 |
| dsh-image-gen | ✓ | 7/7 | systemPrompt.contexts×2 tools×6 webServer.routes×21 cordis.listeners×2 | — | — | 0 | 0 |
| dsh-mnemon | ✓ | 0/1 (未激活: FAILED: invalid config:) |  | — | — | 0 | 10 |
| dsh-mobile-plugin | ✗ 无法安装 dsh-mobile-plugin: Cannot find module 'ws'
Require stack:
- /mnt/d/dsh-plugins/dsh-mobile-plugin/0.5.97/package/lib | | | | | | |
| dsh-onebot-qq | ✓ | 1/1 | cordis.listeners×2 | — | — | 1 | 6 |
| dsh-ops | ✓ | 18/18 | systemPrompt.sections×7 cordis.services×1 cordis.listeners×7 | — | — | 2 | 0 |
| dsh-pet | ✓ | 1/1 | webServer.routes×1 cordis.services×1 cordis.listeners×2 | — | handle Timeout: 0 → 1 | 2 | 1 |
| dsh-plugin-wallpaper-engine | ✓ | 0/1 (未激活: FAILED: [wallpaper-engine] 子包启动自检失败：8 个子包行解析不到 —— dsh-plugin-wallpaper-engine-about-notice) |  | — | — | 0 | 3 |
| dsh-prime-memory | ✓ | 3/4 (未激活: LOADING) | settings.presentations×1 cordis.listeners×2 | — | listener process.on(beforeExit): 0 → 1 | 2 | 1 |
| dsh-remote | ✓ | 6/6 | connection.fetchRoutes×44 systemPrompt.sections×1 tools×21 webServer.routes×44 cordis.services×1 cordis.listeners×5 | — | — | 3 | 2 |
| dsh-session-superagent | ✓ | 1/1 | tools×8 webServer.routes×13 cordis.listeners×1 | — | global globalThis.Symbol(dsh-session-superagent.activeRoutes): (absent) → set<br>global globalThis.Symbol(dsh-session-superagent.inFlight): (absent) → set<br>global globalThis.Symbol(dsh-session-superagent.timers): (absent) → set | 0 | 1 |
| dsh-token-diet | ✓ | 2/2 | webServer.routes×1 cordis.listeners×3 | — | — | 1 | 0 |
| dsh-whale-widget | ✓ | 2/2 | webServer.indexTaps[]×1 webServer.routes×26 cordis.listeners×5 | — | dns dns.defaultResultOrder: verbatim → ipv4first | 0 | 0 |
| dsh-windows-mcp | ✓ | 5/5 | tools×2 tools.guards[]×1 webServer.routes×6 cordis.listeners×5 | + webServer.routes exact /dsh-windows-mcp/bridge (exact) @p<br>+ webServer.routes exact /dsh-windows-mcp/prepare (exact) @p<br>+ webServer.routes exact /dsh-windows-mcp/prepare/cancel (exact) @p<br>+ webServer.routes exact /dsh-windows-mcp/settings (exact) @p<br>+ webServer.routes exact /dsh-windows-mcp/state (exact) @p<br>+ webServer.routes exact /dsh-windows-mcp/update (exact) @p | — | 0 | 0 |
| dshmarket | ✓ | 4/4 | webServer.routes×63 cordis.listeners×3 | — | — | 2 | 5 |
| michengai__dsh-archive-manager | ✗ 无法安装 michengai__dsh-archive-manager: domain 'workspace' global schema must not accept null: null is the medium's "never  | | | | | | |
| michengai__dsh-skills-manager | ✓ | 1/1 | connection.fetchRoutes×48 tools×1 cordis.listeners×4 | — | — | 2 | 1 |
| tencent-connect__dsh-qqbot | ✓ | 2/2 | webServer.routes×5 | — | — | 0 | 8 |
| xmanrui__dsh-im | ✓ | 7/7 | connection.fetchRoutes×19 systemPrompt.contexts×3 tools×3 webServer.routes×1 cordis.services×1 cordis.listeners×12 | — | listener process.on(exit): 0 → 1 | 3 | 8 |
