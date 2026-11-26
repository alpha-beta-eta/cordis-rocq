// 模板之外的调用序列: 读插件源码与定理前提提出假设, 在 checker 上执行, 用 checker 自己的判据判定.
// 五种固定场景 (lib/scenarios.mjs) 之外的组合: 服务交接, 故障后重启, 连续重启, 事件分发, 非默认配置.
// 每条判三次, 一致才算. 结果写到 reports/beyond.json; 真实宿主上的对应场景见 real/README.md.
// 用法 (WSL): node --no-warnings --import ./register.mjs beyond.mjs [名字前缀, 如 P2]
import { runScenario } from './lib/run.mjs'
import { recovery, confluence, fmtRow, fmtProc } from './lib/oracle.mjs'
import { DEFAULT_HOST as H } from './lib/scenarios.mjs'
import fs from 'node:fs'

const snap = label => ({ op: 'snap', label })
const install = (plugin, id = 'p', config) => ({ op: 'install', plugin, id, ...(config ? { config } : {}) })
const dispose = id => ({ op: 'dispose', id })
const restart = s => [{ op: 'withdraw', service: s }, { op: 'provide', service: s }]
const fault = (site, nth, who = 'p') => ({ op: 'fault', site, nth, who })
const sc = (...actions) => ({ host: H, actions: actions.flat() })

// 每个假设: 一条序列 x, 一个对照 y (或恢复判据), 以及读源码得出的预测.
const H_ = []
const hyp = h => H_.push(h)

// P1. dshRemote 交接 (R3 + C2). 两个插件的 provide 都 try/catch 吞错, 之后不再重试
// (ds-harness-remote 只在 replaceServer 时重试; dsh-remote 不重试). 预测: 赢家卸载后,
// 仍在运行的输家不会接手, dshRemote 空着; 与"只装输家"不同.
for (const [a, b] of [['ds-harness-remote', 'dsh-remote'], ['dsh-remote', 'ds-harness-remote']]) {
  hyp({
    name: `P1 handover: ${a} 先装, 卸载后 ${b} 接手 dshRemote?`,
    x: sc(install(a, 'W'), install(b, 'L'), dispose('W'), snap('s')),
    y: sc(install(b, 'L'), snap('s')),
    only: ['cordis.services'],
    predict: '不同: 输家不接手',
  })
}

// P2. 故障后重启服务 (R1 与 C2 的组合). whale-widget 的路由登记在 root.inject(['webServer',...]) 的回调里,
// 第 2 次 register 抛错时内层 fiber FAILED, 留下 1 条裸路由. 重启 webServer 会清空旧表;
// 若 Cordis 在依赖重新出现时重跑这个 FAILED 的 inject fiber, 状态就"自愈"成正常装上.
for (const p of ['dsh-whale-widget', 'dshmarket', 'dsh-remote', 'dsh-connect-workbuddy', 'tencent-connect__dsh-qqbot']) {
  hyp({
    name: `P2 heal: ${p} 第 2 次 register 抛错后重启 webServer, 是否等于正常装上?`,
    x: sc(fault('webServer.register', 2), install(p), restart('webServer'), snap('s')),
    y: sc(install(p), snap('s')),
    predict: '未知: 取决于 FAILED 的 fiber 是否随依赖重跑',
  })
}

// P3. 反复重启 (累积). 报告在真实宿主上看到 dshmarket 每重启 webServer 一次多一个 fiber (4,5,6,7);
// checker 的模板只重启一次. prime-memory 的 beforeExit 监听器在 apply 里登记 (filelog.js:71),
// 它 inject 了 webServer, 重启会重跑 apply. 预测: 重启 3 次与 1 次不同 (累积).
for (const [p, s] of [['dshmarket', 'webServer'], ['dsh-prime-memory', 'webServer'], ['dsh-prime-memory', 'tools'], ['dsh-session-superagent', 'webServer']]) {
  hyp({
    name: `P3 accumulate: ${p} 重启 ${s} 3 次 vs 1 次`,
    x: sc(install(p), restart(s), restart(s), restart(s), snap('s')),
    y: sc(install(p), restart(s), snap('s')),
    predict: '不同: 累积',
  })
}

// P4. 事件分发 (模板里没有 emit). whale-widget 用 root.on 登记 index-inject 行 (owned), 不依赖任何服务.
// 预测: 卸载后再分发, 表里没有它的行; webServer 不在时分发, 行照样出现 (插件注释的设计意图).
hyp({
  name: 'P4 emit: whale-widget 卸载后 index-inject 不再推行',
  emits: true,
  x: { host: H, actions: [install('dsh-whale-widget'), { op: 'emit', event: 'webserver/index-inject', args: ['$table'] }, dispose('p'), { op: 'emit', event: 'webserver/index-inject', args: ['$table'] }] },
  predict: '第 1 次 1 行, 第 2 次 0 行',
})
hyp({
  name: 'P4 emit: whale-widget 在 webServer 缺席时也推行',
  emits: true,
  x: { host: H.filter(h => h !== 'webServer'), actions: [install('dsh-whale-widget'), { op: 'emit', event: 'webserver/index-inject', args: ['$table'] }] },
  predict: '1 行',
})

// P5. 非默认配置 (模板总传 {}). prime-memory 的 live.toolLegacy / toolGraphAdmin / skillsEnabled 默认关,
// 打开后经 reg() 多登记几组工具 (tools/index.js:60). 预测: 卸载后干净 (tools 是 owned),
// 但 beforeExit 残留照旧.
const PM_CFG = { live: { toolLegacy: true, toolGraphAdmin: true, skillsEnabled: true } }
hyp({
  name: 'P5 config: prime-memory 打开封印组后装上再卸载',
  recovery: true,
  x: sc(snap('before'), install('dsh-prime-memory', 'p', PM_CFG), snap('loaded'), dispose('p'), snap('after')),
  predict: '只有 beforeExit 残留',
})
hyp({
  name: 'P5 config: 打开封印组后工具数是否变多 (覆盖面)',
  x: sc(install('dsh-prime-memory', 'p', PM_CFG), snap('s')),
  y: sc(install('dsh-prime-memory'), snap('s')),
  only: ['tools'],
  predict: '不同: 多出 legacy / graphAdmin / skills 组',
})

const filter = process.argv[2]
const settled = s => !(s.world['cordis.fibers'] ?? []).some(f => f.view === 'LOADING')
const proj = (s, t) => t ? { ...s, procDelta: [], world: Object.fromEntries(t.map(k => [k, s.world[k] ?? []])) } : s

async function judge(h) {
  const rx = await runScenario(h.x)
  if (rx.crashed) return { verdict: 'crash', detail: [rx.stderr?.slice(-400)] }
  const errs = rx.steps.filter(s => s.error && !s.injected).map(s => `${s.op} ${s.plugin ?? s.service ?? ''}: ${s.error}`)
  if (h.emits) {
    const rows = rx.steps.filter(s => s.op === 'emit').map(s => (s.result ?? []).length)
    return { verdict: `emit rows ${rows.join(', ')}`, detail: errs }
  }
  if (h.recovery) {
    const r = recovery(rx.snaps.before, rx.snaps.after)
    return { verdict: r.ok ? 'clean' : 'leak', detail: [...r.leaks.map(fmtRow), ...r.process.map(fmtProc), ...errs] }
  }
  const ry = await runScenario(h.y)
  const a = rx.snaps.s, b = ry.snaps.s
  if (!settled(a) || !settled(b)) return { verdict: 'inconclusive (LOADING)', detail: errs }
  const c = confluence(proj(b, h.only), proj(a, h.only))
  return { verdict: c.ok ? 'same' : 'differ', detail: [...c.world.map(fmtRow), ...c.process.map(fmtProc), ...errs] }
}

const out = []
for (const h of H_.filter(h => !filter || h.name.startsWith(filter))) {
  // 稳定性: 判三次, 一致才算.
  const rs = await Promise.all([judge(h), judge(h), judge(h)])
  const vs = rs.map(r => r.verdict + '|' + r.detail.join('\n'))
  const stable = vs.every(v => v === vs[0])
  out.push({ name: h.name, predict: h.predict, stable, verdict: rs[0].verdict, detail: rs[0].detail.slice(0, 30), others: stable ? undefined : rs.map(r => r.verdict) })
  console.log(`${stable ? '' : '[不稳定] '}${h.name}\n  预测: ${h.predict}\n  结果: ${rs[0].verdict}${stable ? '' : '  (' + rs.map(r => r.verdict).join(' / ') + ')'}\n${rs[0].detail.slice(0, 12).map(d => '    ' + d).join('\n')}\n`)
}
// 只跑一部分时不覆盖完整的结果.
if (!filter) fs.writeFileSync(new URL('./reports/beyond.json', import.meta.url), JSON.stringify(out, null, 1))
