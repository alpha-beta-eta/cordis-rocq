# ds-harness-remote@0.6.7 + dsh-remote@1.3.1

- A = ds-harness-remote: activateWhenCarrierReady#0 ACTIVE; activateWhenCarrierReady#1 ACTIVE; ds-harness-remote#0 ACTIVE; ds-harness-remote#1 ACTIVE; scope#0 ACTIVE
- B = dsh-remote: dsh-remote#0 ACTIVE; dsh-remote#1 ACTIVE; dsh-remote#2 ACTIVE; dsh-remote#3 ACTIVE; dsh-remote#4 ACTIVE; dsh-remote#5 ACTIVE
- 没有桩的调用: loader.locate, loader.entries, skills.registerProvider, agents.list, commands.register
- 换成桩的模块: zod (from packages/client/connection/src/rpc-schema.ts), iconv-lite (from ../dsh-plugins/dsh-remote/1.3.1/package/lib/main.js), yaml (from ../dsh-plugins/dsh-remote/1.3.1/package/lib/remote-skills.js)

注意: 有 fiber 停在 LOADING, 只比较 cordis.services.

✗ 两种安装次序的落定状态不同 (A = 第一个参数, B = 第二个):

- + cordis.services dshRemote (service) @B
- - cordis.services dshRemote (service) @A

```
A 先:
1. install(ds-harness-remote) as A                                  O-Insert
2. install(dsh-remote) as B                                         O-Insert

B 先:
1. install(dsh-remote) as B                                         O-Insert
2. install(ds-harness-remote) as A                                  O-Insert
```

重放: `sh check.sh replay witnesses/pair-ds-harness-remote-dsh-remote.json`

插件的告警输出:

- `[warn] [ds-harness-remote] Codex Remote domain unavailable {"code":"CODEX_START_FAILED"}`
- `[warn] [ds-harness-remote] Codex App Server restart scheduled {"attempt":1,"delayMs":1000}`
- `[warn] [ds-harness-remote] client remote mode is unavailable {"serverConfigured":false,"remoteGatewayAvailable":true,"connectionAvailable":true}`
- `[warn] [ds-harness-remote] Codex App Server restart failed {"attempt":1,"code":"CODEX_START_FAILED"}`
- `[warn] [ds-harness-remote] Codex App Server restart scheduled {"attempt":2,"delayMs":2000}`
- `[warn] [ds-harness-remote] failed to provide remote service {"service":"dshRemote","code":"SERVICE_PROVIDE_CONFLICT"}`
