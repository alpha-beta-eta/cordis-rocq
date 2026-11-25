// cordis-check: 在真实的 Cordis (dsh vendored) 上跑插件, 枚举生命周期调用序列, 以汇总定理的各层为判据.
//
//   node cli.mjs check <plugin>... | --all [--host a,b,c] [--max-k N]   恢复 (含故障注入), 服务晚到与提供者重启 (C2); 多个插件共用并行池
//   node cli.mjs pair <a> <b> [--host ...]                    两个插件: 两种安装次序的落定状态是否相同
//   node cli.mjs replay <witness.json>...                     重放见证 (多个时并行)
//   node cli.mjs sweep                                        全部插件各装上卸载一次 (覆盖面普查)
//
// 见证写到 witnesses/, 报告写到 reports/.

import fs from 'node:fs'
import path from 'node:path'
import { fileURLToPath } from 'node:url'
import { runScenario, runAll, JOBS } from './lib/run.mjs'
import { recovery, confluence, fmtRow, fmtProc, diffWorld } from './lib/oracle.mjs'
import * as S from './lib/scenarios.mjs'
import { resolvePlugin, PLUGINS_ROOT } from './lib/plugins.mjs'

const here = path.dirname(fileURLToPath(import.meta.url))
const [cmd, ...rest] = process.argv.slice(2)
const opts = {}
const args = []
for (let i = 0; i < rest.length; i++) {
  if (rest[i].startsWith('--')) opts[rest[i].slice(2)] = rest[++i]
  else args.push(rest[i])
}
const host = opts.host ? opts.host.split(',') : S.DEFAULT_HOST
const maxK = Number(opts['max-k'] ?? 64)
let quiet = false // 一次处理多个插件或见证时, 每个只打印一行

const slug = s => s.replace(/^\.\//, '').replace(/[^A-Za-z0-9_.-]+/g, '_')

function saveWitness(name, w) {
  fs.mkdirSync(path.join(here, 'witnesses'), { recursive: true })
  const file = path.join(here, 'witnesses', `${name}.json`)
  fs.writeFileSync(file, JSON.stringify(w, null, 2) + '\n')
  return path.relative(here, file)
}

function explain(scenario) {
  return scenario.actions.filter(a => a.op !== 'snap').map((a, i) => {
    const what = a.op === 'install' ? `install(${a.plugin}) as ${a.id}`
      : a.op === 'dispose' ? `dispose(${a.id})`
      : a.op === 'fault' ? `${a.site} call #${a.nth} by ${a.who ?? "anyone"} throws`
      : a.op === 'provide' || a.op === 'withdraw' ? `${a.op}(${a.service})`
      : a.op === 'emit' ? `emit(${a.event})` : a.op
    return `${i + 1}. ${what.padEnd(64)} ${S.RULE[a.op] ?? ''}`
  }).join('\n')
}

// 一次运行能否下结论: 进程崩溃, 或某个 install 步骤本身出错 (模块加载失败等), 都不能.
function bad(result) {
  if (result.crashed) return `run crashed (${result.code ?? result.signal}): ${result.stderr?.split('\n').slice(-3).join(' ')}`
  const failed = result.steps.find(s => s.op === 'install' && s.error)
  if (failed) return `无法安装 ${failed.plugin}: ${failed.error}`
}

// 快照是否落定: 有 fiber 停在 LOADING (异步加载没走完) 时, 拿它与别的快照比较没有意义.
// 卸载后的残留不受影响 (dispose 是等到底的), 受影响的是"再装"与"服务晚到"两类比较.
const settled = snap => !(snap.world['cordis.fibers'] ?? []).some(f => f.view === 'LOADING')
const SKIP = { world: [], process: [], ok: true, skipped: true }
// 只看部分表 (例如服务归属), 进程级状态不比.
const project = (snap, tables) => ({ ...snap, procDelta: [], world: Object.fromEntries(tables.map(t => [t, snap.world[t] ?? []])) })
const compareSettled = (x, y) => settled(x) && settled(y) ? confluence(x, y) : SKIP

// 一个见证的判定: 重新执行它的场景, 返回差异列表 (空表示未复现). replay 与稳定性确认共用.
async function evaluate(w) {
  if (w.check.startsWith('recovery')) {
    const r = await runScenario(w.scenario)
    if (bad(r)) return [`无结论: ${bad(r)}`]
    const rr = recovery(r.snaps[w.compare[0]], r.snaps[w.compare[1]])
    const diffs = [...rr.leaks.map(fmtRow), ...rr.process.map(fmtProc)]
    if (r.snaps.reloaded) {
      // 故障场景的第一次安装是坏的, 再装要与另跑的正常安装比; 不注入故障时与本次的第一次安装比.
      const ref = w.scenario.actions.some(a => a.op === 'fault')
        ? (await runScenario(S.plain(w.scenario.actions.find(a => a.op === 'install').plugin, w.scenario.host))).snaps.loaded
        : r.snaps.loaded
      const c = compareSettled(ref, S.reloadView(r.snaps.reloaded))
      diffs.push(...c.world.map(d => `reload: ${fmtRow(d)}`), ...c.process.map(d => `reload: ${fmtProc(d)}`))
    }
    return diffs
  }
  const [x, y] = await runAll([w.against, w.scenario])
  if (bad(x) || bad(y)) return [`无结论: ${bad(x) ?? bad(y)}`]
  const c = w.only
    ? confluence(project(x.snaps[w.againstSnap], w.only), project(y.snaps[w.snap], w.only))
    : compareSettled(x.snaps[w.againstSnap], y.snaps[w.snap])
  if (c.skipped) return ['无结论: 有 fiber 停在 LOADING']
  return [...c.world.map(fmtRow), ...c.process.map(fmtProc)]
}

// 稳定性: 再判定两次, 差异集合三次都相同才算稳定. 异步活动没落定的插件 (fiber 停在 LOADING)
// 快照取决于时序, 这样的候选不作为见证.
async function stable(w) {
  const runs = await Promise.all([evaluate(w), evaluate(w)])
  const key = d => [...new Set(d)].sort().join('\n')
  const ok = runs.every(d => key(d) === key(w.summary))
  if (!ok) {
    // 不稳定的候选留在 .out/unstable/ 里备查, 不进 witnesses/.
    fs.mkdirSync(path.join(here, '.out/unstable'), { recursive: true })
    fs.writeFileSync(path.join(here, '.out/unstable', `${w.name}.json`), JSON.stringify({ ...w, reruns: runs }, null, 2))
  }
  return ok
}

async function check(plugin) {
  const label = resolvePlugin(plugin).label
  const lines = [`# ${label}`, '', `宿主服务: ${host.join(', ')}`, '']
  const witnesses = []
  const t0 = Date.now()

  // 1. 不注入故障: 装上, 卸载.
  const base = await runScenario(S.plain(plugin, host))
  if (bad(base)) { console.log(`${plugin}: 无结论: ${bad(base)}`); process.exitCode = 2; return }
  const fibers = base.snaps.loaded.world['cordis.fibers'] ?? []
  lines.push('## 装上后', '')
  lines.push(`- fiber: ${fibers.map(f => `${f.key} ${f.view}`).join('; ') || '(无)'}`)
  const loadedTables = Object.entries(base.snaps.loaded.world).filter(([t]) => t !== 'cordis.fibers')
  lines.push(`- 登记: ${loadedTables.map(([t, rows]) => `${t} ×${rows.length}`).join(', ') || '(无)'}`)
  if (base.unmodeled.length) lines.push(`- 没有桩的调用: ${base.unmodeled.join(', ')}`)
  if (base.stubbed.length) lines.push(`- 换成桩的模块: ${base.stubbed.join(', ')}`)
  if (base.steps.some(s => s.error)) lines.push(`- 步骤出错: ${base.steps.filter(s => s.error).map(s => `${s.op}: ${s.error}`).join('; ')}`)
  const harness = fibers.some(f => f.view.startsWith('FAILED') || f.view === 'PENDING')
  if (harness) lines.push('- 注意: 不注入故障时就有 fiber 失败或停在 PENDING, 多半是桩不够真; 以下结论只对能跑到的部分成立.')
  lines.push('')

  const rec = recovery(base.snaps.before, base.snaps.after)
  const again = compareSettled(base.snaps.loaded, S.reloadView(base.snaps.reloaded))
  if (!settled(base.snaps.loaded)) lines.push('- 注意: 装上后有 fiber 停在 LOADING (异步加载没走完), "再装"与"服务晚到"两类比较无结论.', '')
  lines.push('## 第 2 层: 装上再卸载', '')
  if (rec.ok && again.ok && !rec.persistent.length) lines.push('✓ 卸载后与从未安装相同, 再装与第一次装上相同.')
  for (const d of rec.leaks) lines.push(`- ✗ 残留登记: ${fmtRow(d)}`)
  for (const d of rec.process) lines.push(`- ✗ 进程级改动未恢复: ${fmtProc(d)}`)
  for (const d of again.world) lines.push(`- ✗ 再装与第一次装上不同: ${fmtRow(d)}`)
  for (const d of again.process) lines.push(`- ✗ 再装与第一次装上不同: ${fmtProc(d)}`)
  for (const d of rec.persistent) lines.push(`- ○ 持久状态 (R4, 只报告): ${fmtRow(d)}`)
  if (!rec.ok || !again.ok) {
    witnesses.push({ name: `${slug(plugin)}-unload`, tier: 2, check: 'recovery', compare: ['before', 'after'], scenario: S.plain(plugin, host),
      summary: [...rec.leaks.map(fmtRow), ...rec.process.map(fmtProc), ...again.world.map(d => `reload: ${fmtRow(d)}`), ...again.process.map(d => `reload: ${fmtProc(d)}`)] })
  }
  lines.push('')

  // 2. 故障注入: 插件自己的每个宿主调用点, 每个 k.
  const sites = new Map()
  for (const t of base.trace) if (t.who === 'p' && !t.fault) sites.set(t.site, Math.max(sites.get(t.site) ?? 0, t.n))
  const faultScenarios = []
  for (const [site, count] of sites) for (let k = 1; k <= Math.min(count, maxK); k++) faultScenarios.push(S.fault(plugin, host, site, k))
  const results = await runAll(faultScenarios)
  lines.push('## 第 2 层: 中途抛错 (R1)', '')
  lines.push(`插件在 apply 期间调用的宿主方法: ${[...sites].map(([s, c]) => `${s} ×${c}`).join(', ') || '(无)'}`, '')
  const bySite = new Map()
  for (const r of results) {
    if (bad(r)) { lines.push(`- 运行失败: ${bad(r)}`); continue }
    const f = r.scenario.actions.find(a => a.op === 'fault')
    const rr = recovery(r.snaps.before, r.snaps.after)
    const reload = compareSettled(base.snaps.loaded, S.reloadView(r.snaps.reloaded))
    const list = bySite.get(f.site) ?? []
    list.push({ k: f.nth, rr, reload, r })
    bySite.set(f.site, list)
  }
  for (const [site, list] of bySite) {
    const leaking = list.filter(x => x.rr.leaks.length)
    const broken = list.filter(x => !x.reload.ok)
    if (!leaking.length && !broken.length) { lines.push(`- ✓ ${site}: k = 1..${list.length} 都恢复干净, 再装与正常装上相同.`); continue }
    lines.push(`- ✗ ${site}: ${leaking.length}/${list.length} 个故障点卸载后有残留; ${broken.length}/${list.length} 个故障点之后再装与正常装上不同.`)
    const first = leaking[0] ?? broken[0]
    lines.push(`  最小的 k = ${first.k}:`)
    for (const d of first.rr.leaks.slice(0, 8)) lines.push(`  - 卸载后残留 ${fmtRow(d)}`)
    if (first.rr.leaks.length > 8) lines.push(`  - … 共 ${first.rr.leaks.length} 条`)
    for (const d of first.reload.world.slice(0, 6)) lines.push(`  - 再装: ${fmtRow(d)}`)
    for (const d of first.reload.process.slice(0, 3)) lines.push(`  - 再装: ${fmtProc(d)}`)
    const worst = leaking.reduce((m, x) => (x.rr.leaks.length > (m?.rr.leaks.length ?? -1) ? x : m), undefined)
    if (worst && worst !== first) lines.push(`  残留最多的是 k = ${worst.k}: ${worst.rr.leaks.length} 条.`)
    witnesses.push({ name: `${slug(plugin)}-fault-${slug(site)}-${first.k}`, tier: 2, check: 'recovery+reload', compare: ['before', 'after'],
      scenario: first.r.scenario,
      summary: [...first.rr.leaks.map(fmtRow), ...first.rr.process.map(fmtProc), ...first.reload.world.map(d => `reload: ${fmtRow(d)}`), ...first.reload.process.map(d => `reload: ${fmtProc(d)}`)] })
  }
  lines.push('')

  // 3. 服务晚到 (C2): 每个宿主服务分别在插件之后出现.
  const lateResults = await runAll(host.map(h => S.late(plugin, host, h)))
  lines.push('## 第 3 层: 服务晚到 (C2)', '')
  let lateOk = 0, lateSkipped = 0
  for (const r of lateResults) {
    if (bad(r)) { lines.push(`- 运行失败: ${bad(r)}`); continue }
    const svc = r.scenario.actions.find(a => a.op === 'provide').service
    const c = compareSettled(base.snaps.loaded, r.snaps.final)
    if (c.skipped) { lateSkipped++; continue }
    if (c.ok) { lateOk++; continue }
    lines.push(`- ✗ ${svc} 在插件之后出现时, 落定状态不同:`)
    for (const d of c.world.slice(0, 8)) lines.push(`  - ${fmtRow(d)}`)
    for (const d of c.process.slice(0, 4)) lines.push(`  - ${fmtProc(d)}`)
    witnesses.push({ name: `${slug(plugin)}-late-${slug(svc)}`, tier: 3, check: 'confluence',
      against: S.plain(plugin, host), againstSnap: 'loaded', scenario: r.scenario, snap: 'final',
      summary: [...c.world.map(fmtRow), ...c.process.map(fmtProc)] })
  }
  lines.push(`- ✓ 其余 ${lateOk} 个服务晚到时与先到相同.`)
  if (lateSkipped) lines.push(`- ${lateSkipped} 个服务晚到的比较无结论 (有 fiber 停在 LOADING).`)
  lines.push('')

  // 4. 提供者重启 (C2): 插件装上之后, 每个宿主服务分别撤走再提供.
  const restartResults = await runAll(host.map(h => S.restart(plugin, host, h)))
  lines.push('## 第 3 层: 提供者重启 (C2)', '')
  let restartOk = 0, restartSkipped = 0
  for (const r of restartResults) {
    if (bad(r)) { lines.push(`- 运行失败: ${bad(r)}`); continue }
    const svc = r.scenario.actions.find(a => a.op === 'withdraw').service
    const c = compareSettled(base.snaps.loaded, r.snaps.final)
    if (c.skipped) { restartSkipped++; continue }
    if (c.ok) { restartOk++; continue }
    lines.push(`- ✗ ${svc} 的提供者重启后, 落定状态不同:`)
    for (const d of c.world.slice(0, 8)) lines.push(`  - ${fmtRow(d)}`)
    for (const d of c.process.slice(0, 4)) lines.push(`  - ${fmtProc(d)}`)
    witnesses.push({ name: `${slug(plugin)}-restart-${slug(svc)}`, tier: 3, check: 'confluence',
      against: S.plain(plugin, host), againstSnap: 'loaded', scenario: r.scenario, snap: 'final',
      summary: [...c.world.map(fmtRow), ...c.process.map(fmtProc)] })
  }
  lines.push(`- ✓ 其余 ${restartOk} 个服务重启后与重启前相同.`)
  if (restartSkipped) lines.push(`- ${restartSkipped} 个服务重启的比较无结论 (有 fiber 停在 LOADING).`)
  lines.push('')

  lines.push('## 见证', '')
  const verdicts = await Promise.all(witnesses.map(stable))
  for (const [i, w] of witnesses.entries()) {
    if (!verdicts[i]) {
      lines.push(`### ${w.name} (第 ${w.tier} 层): 不稳定, 无结论`, '', '再判定两次, 差异不总相同 (多半是有异步活动没有落定), 不作为见证.', '')
      continue
    }
    const file = saveWitness(w.name, w)
    lines.push(`### ${w.name} (第 ${w.tier} 层)`, '', '```', explain(w.scenario), '```', '', ...w.summary.slice(0, 10).map(s => `- ${s}`), '', `重放: \`sh check.sh replay ${file}\``, '')
  }
  lines.push(`(共 ${1 + faultScenarios.length + 2 * host.length} 次运行, ${((Date.now() - t0) / 1000).toFixed(1)} 秒)`)
  writeReport(slug(plugin), lines)
}

async function pair(a, b) {
  const [ab, ba] = await runAll([S.pair(a, b, host, 'ab'), S.pair(a, b, host, 'ba')])
  const lines = [`# ${resolvePlugin(a).label} + ${resolvePlugin(b).label}`, '']
  for (const r of [ab, ba]) if (bad(r)) { console.log(`无结论: ${bad(r)}`); process.exitCode = 2; return }
  for (const [id, p] of [['A', a], ['B', b]]) {
    const fs_ = (ab.snaps.final.world['cordis.fibers'] ?? []).filter(f => f.owner === id)
    lines.push(`- ${id} = ${p}: ${fs_.map(f => `${f.key.split('/').slice(1).join('/')} ${f.view.split('\n')[0]}`).join('; ') || '(没有 fiber)'}`)
  }
  for (const [id, p] of [['A', a], ['B', b]]) {
    const active = (ab.snaps.final.world['cordis.fibers'] ?? []).some(f => f.owner === id && f.view === 'ACTIVE')
    if (!active) {
      console.log(lines.join('\n'))
      console.log(`\n无结论: ${p} 没有任何 ACTIVE 的 fiber (多半是桩不够, 或缺服务), 比较没有意义.`)
      process.exitCode = 2
      return
    }
  }
  const stubbed = [...new Set([...ab.stubbed, ...ba.stubbed])]
  const unmodeled = [...new Set([...ab.unmodeled, ...ba.unmodeled])]
  if (unmodeled.length) lines.push(`- 没有桩的调用: ${unmodeled.join(', ')}`)
  if (stubbed.length) lines.push(`- 换成桩的模块: ${stubbed.join(', ')}`)
  lines.push('')
  // 有一方没落定 (fiber 停在 LOADING) 时整体比较没有意义, 只比服务归属: ctx.provide 先到先得,
  // 不依赖异步加载走没走完.
  const only = settled(ab.snaps.final) && settled(ba.snaps.final) ? undefined : ['cordis.services']
  if (only) lines.push(`注意: 有 fiber 停在 LOADING, 只比较 ${only.join(', ')}.`, '')
  const c = only ? confluence(project(ab.snaps.final, only), project(ba.snaps.final, only)) : confluence(ab.snaps.final, ba.snaps.final)
  if (c.ok) lines.push('✓ 两种安装次序的落定状态相同.')
  else {
    lines.push('✗ 两种安装次序的落定状态不同 (A = 第一个参数, B = 第二个):', '')
    for (const d of c.world) lines.push(`- ${fmtRow(d)}`)
    for (const d of c.process) lines.push(`- ${fmtProc(d)}`)
    const w = { name: `pair-${slug(a)}-${slug(b)}`, tier: 3, check: 'confluence', against: ab.scenario, againstSnap: 'final', scenario: ba.scenario, snap: 'final', only,
      summary: [...c.world.map(fmtRow), ...c.process.map(fmtProc)] }
    if (await stable(w)) {
      const file = saveWitness(w.name, w)
      lines.push('', '```', 'A 先:', explain(ab.scenario), '', 'B 先:', explain(ba.scenario), '```', '', `重放: \`sh check.sh replay ${file}\``)
    } else lines.push('', '再判定两次, 差异不总相同, 不稳定, 无结论.')
  }
  const warns = [...ab.log, ...ba.log].filter(l => l.startsWith('[warn]') || l.startsWith('[error]'))
  if (warns.length) lines.push('', '插件的告警输出:', '', ...[...new Set(warns)].slice(0, 10).map(l => `- \`${l.slice(0, 300).replace(/\n.*/s, '')}\``))
  writeReport(`pair-${slug(a)}-${slug(b)}`, lines)
}

// 重放见证. 一个文件时打印全部差异; 多个文件时并行重放, 每个见证一行.
// 退出码: 全部复现为 1 (与单个见证的约定一致), 有未复现的为 0.
async function replay(files) {
  const results = await Promise.all(files.map(async file => {
    const w = JSON.parse(fs.readFileSync(path.resolve(file), 'utf8'))
    return { file, w, diffs: await evaluate(w) }
  }))
  for (const { file, w, diffs } of results) {
    if (quiet) console.log(`${diffs.length ? '✗ 复现' : '✓ 未复现'}  ${file}`)
    else {
      console.log(`${w.name} (第 ${w.tier} 层, ${w.check})\n\n${explain(w.scenario)}\n`)
      console.log(diffs.length ? `✗ 复现:\n${diffs.map(d => `- ${d}`).join('\n')}` : '✓ 未复现')
    }
  }
  process.exitCode = results.every(r => r.diffs.length) ? 1 : 0
}

// 全部插件 (排除非插件目录与只有客户端的包).
function allPlugins() {
  return fs.readdirSync(PLUGINS_ROOT).filter(n => n !== 'src' && n !== 'cc-safety-net' && n !== 'michengai__dsh-codex-ui')
    .filter(n => { try { resolvePlugin(n); return true } catch { return false } }).sort()
}

// 对插件目录下全部插件各跑一次"装上再卸载": 能否加载, fiber 状态, 卸载后的残留.
async function sweep() {
  const names = allPlugins()
  const results = await runAll(names.map(n => S.plain(n, host)))
  const lines = ['# 加载与卸载普查', '', `宿主服务: ${host.length} 个 (${S.DEFAULT_HOST === host ? '默认' : '自定'}); 插件: ${names.length} 个`, '',
    '| 插件 | 加载 | fiber (ACTIVE/全部) | 装上后的登记 | 卸载后残留 | 进程级改动 | 没有桩的调用 | 换成桩的模块 |', '|---|---|---|---|---|---|---|---|']
  for (const [i, r] of results.entries()) {
    const n = names[i]
    const why = bad(r)
    if (why) { lines.push(`| ${n} | ✗ ${why.replace(/\|/g, '/').slice(0, 120)} | | | | | | |`); continue }
    const fibers = r.snaps.loaded.world['cordis.fibers'] ?? []
    const active = fibers.filter(f => f.view === 'ACTIVE').length
    const failed = fibers.filter(f => f.view !== 'ACTIVE').map(f => f.view.split('\n')[0].slice(0, 90))
    const reg = Object.entries(r.snaps.loaded.world).filter(([t]) => t !== 'cordis.fibers').map(([t, rows]) => `${t}×${rows.length}`).join(' ')
    const rec = recovery(r.snaps.before, r.snaps.after)
    lines.push(`| ${n} | ✓ | ${active}/${fibers.length}${failed.length ? ` (未激活: ${failed.join('; ').replace(/\|/g, '/')})` : ''} | ${reg} | ${rec.leaks.map(fmtRow).join('<br>') || '—'} | ${rec.process.map(fmtProc).join('<br>') || '—'} | ${r.unmodeled.length} | ${r.stubbed.length} |`)
  }
  writeReport('sweep', lines)
}

function writeReport(name, lines) {
  fs.mkdirSync(path.join(here, 'reports'), { recursive: true })
  const file = path.join(here, 'reports', `${name}.md`)
  fs.writeFileSync(file, lines.join('\n') + '\n')
  if (quiet) {
    const n = lines.filter(l => l.includes('✗')).length
    const ws = lines.filter(l => l.startsWith('### ') && !l.includes('不稳定')).length
    const unstable = lines.filter(l => l.startsWith('### ') && l.includes('不稳定')).length
    console.log(`${name}: ✗ ${n} 处, 见证 ${ws} 个${unstable ? `, 不稳定 ${unstable} 个` : ''} -> ${path.relative(here, file)}`)
  } else {
    console.log(lines.join('\n'))
    console.log(`\n报告: ${path.relative(here, file)}`)
  }
}

const t0 = Date.now()
if (cmd === 'check') {
  const names = 'all' in opts || args[0] === '--all' ? allPlugins() : args
  quiet = names.length > 1
  await Promise.all(names.map(check))
  if (quiet) console.log(`(${names.length} 个插件, 并行池 ${JOBS}, ${((Date.now() - t0) / 1000).toFixed(1)} 秒)`)
}
else if (cmd === 'pair') await pair(args[0], args[1])
else if (cmd === 'replay') { quiet = args.length > 1; await replay(args) }
else if (cmd === 'sweep') await sweep()
else console.log('usage: sh check.sh check <plugin>... | check --all | pair <a> <b> | replay <witness.json>... | sweep')
