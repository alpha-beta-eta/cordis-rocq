# 在真实的 dsh 宿主上复现见证

checker 的结论是相对于宿主桩而言的。这里用 npm 发布版的 dsh (`@deepseek-ai/dsh@0.2.2-rc.5`，2026-11-18) 起一个真实的 web 宿主，把要检查的插件和一个**驱动插件**装进一个全新的 profile，由驱动插件执行场景。

在 WSL 中：

```sh
sh setup.sh                                                    # 只需一次: Node 24.22.3 (校验 SHA-256), dsh, pnpm
sh run.sh wmcp  scenarios/windows-mcp.json dsh-windows-mcp@0.2.11
sh run.sh whale scenarios/whale.json       dsh-whale-widget@0.4.2
sh run.sh pair-ab scenarios/remote-pair.json ds-harness-remote@0.6.7 dsh-remote@1.3.1
sh run.sh pair-ba scenarios/remote-pair.json dsh-remote@1.3.1 ds-harness-remote@0.6.7

# A 类其余插件: 占住第 2 条路由 (场景由 make-collision.mjs 生成)
node make-collision.mjs dsh-market /dsh-market/telemetry/opened /dsh-market/telemetry > scenarios/dshmarket.json
sh run.sh dshmarket scenarios/dshmarket.json dshmarket@1.80.0
sh run.sh free-search-reuse scenarios/free-search-reuse.json dsh-free-search@0.9.82

# C 类服务晚到: 停用提供服务的条目, 期间启用插件, 再启用提供者; 另试"提供者重启"与"插件重启"对照
sh run.sh remote-late-skills scenarios/remote-late-skills.json dsh-remote@1.3.1
sh run.sh token-diet-late-webserver scenarios/token-diet-late-webserver.json dsh-token-diet@0.1.0
sh run.sh im-late-controllers scenarios/im-late-controllers.json @xmanrui/dsh-im@5.10.0

# 提供者重启: 依次重启 system-prompt (两次), webserver, settings; 再单独连续重启 webserver 三次
sh run.sh restart-providers scenarios/restart-providers.json dshmarket@1.80.0 dsh-image-gen@0.11.4 dsh-free-search@0.9.82
sh run.sh webserver-restarts scenarios/webserver-restarts.json dsh-token-diet@0.1.0 dshmarket@1.80.0

# 级联重启: 重启 web-startup, 再重启 system-prompt; 读 image-gen 根 fiber 的 epoch 看它是否被连带重启
sh run.sh cascade scenarios/cascade.json dshmarket@1.80.0 dsh-image-gen@0.11.4 dsh-free-search@0.9.82

# 第四、五轮: dsh-mobile-plugin 的卸载残留与 webServer 重启; ds-harness-remote 的 webServer 晚到与重启
sh run.sh mobile-unload scenarios/mobile-unload.json dsh-mobile-plugin@0.5.97
sh run.sh mobile-restart scenarios/mobile-restart.json dsh-mobile-plugin@0.5.97
sh run.sh harness-ws scenarios/remote-harness-webserver.json ds-harness-remote@0.6.7

# B 类进程级状态: 空宿主作对照, 再装上 8 个插件逐个停用, 启用; dsh-im 单独一次
sh run.sh proc-base scenarios/process-baseline.json
sh run.sh proc-state scenarios/process-state.json dsh-whale-widget@0.4.2 dsh-session-superagent@0.10.12 dsh-cost-meter@1.9.85 ds-harness-remote@0.6.7 dsh-pet@0.4.9 dsh-prime-memory@0.26.72 @xmanrui/dsh-im@5.10.0 dsh-mobile-plugin@0.5.97
sh run.sh proc-im scenarios/process-im.json @xmanrui/dsh-im@5.10.0

# dsh-ops 的故障注入见证: 占住它第 2 次要登记的提示段名, 让真实的 systemPrompt.section 因重名抛错
sh run.sh ops-section scenarios/ops-section.json dsh-ops@0.5.5

# E6f (../../docs/CONTRIB.md): 贡献键宿主. 硬链接复制一份宿主, 只改 webserver 一个文件 (owned 登记, 撞名按多重集);
# 之后任一场景加 DSH_HOST=dsh-host-contrib 即在它上面跑, 名字后加 -contrib 以免覆盖基线的 /tmp 目录
node contrib-host.mjs ~/.cache/cordis-check
DSH_HOST=dsh-host-contrib sh run.sh whale-contrib scenarios/whale.json dsh-whale-widget@0.4.2

# 服务依赖图: 读出每个服务的提供者及其 fiber 链上的 inject, 生成 checker 的 lib/host-graph.json
sh run.sh graph scenarios/graph.json dsh-image-gen@0.11.4 dshmarket@1.80.0 dsh-free-search@0.9.82
node make-graph.mjs /tmp/cordis-real-graph/out.json 0.2.2-rc.5 > ../lib/host-graph.json
```

`run.sh` 依次做这几件事：

1. 在 `/tmp/cordis-real-<名字>` 下建全新的 `DSH_HOME` 与 `HOME`，不碰你自己的 dsh；
2. 用 `dsh plugin --profile web add --ignore-scripts` 按给定次序从 npm 装插件，最后装驱动；
3. 在**只有回环接口的网络命名空间**里启动宿主 (`unshare -n`，需要 root，WSL 默认就是)，插件连不上任何外部地址；
4. 等驱动写出 `done`，杀掉整棵进程树，打印驱动的记录和宿主日志的结尾。

## 驱动插件

[driver/](driver/) 是一个编排者：

- 通过 loader 的条目停用、启用别的插件 (O-Dispose / O-Insert)；
- 发真实的 HTTP 请求；
- 读宿主 webServer 内部的路由表，给每条路由上的处理器函数编号，同一个函数对象编号相同，以此区分新旧实例；
- 读 Cordis 的服务表，看服务归哪个插件。

它不打补丁，也不注入故障。需要故障时，用真实世界里会发生的方式触发：先由驱动占住插件要用的一条路径，相当于另一个插件或同一插件的旧版本占了它。需要服务晚到时，停用再启用提供这个服务的 loader 条目，相当于提供者因配置变更或热重载而重启。驱动自己不 inject 任何服务，每次用到 webServer 时再读，所以停用 webServer 时驱动不会被一起卸载。场景的步骤见 `driver/index.mjs` 开头的注释。
