// 判据: 两份快照之间的差异, 按审计的检查项分类.
//
// 快照的 world 部分是 表名 -> 行列表, 行 = { key, view, owner }.
// 比较时 owner 也算: 名字归谁是可观察的 (调用会落到不同的实现上).
// 安装编号是场景里给定的固定名字, 不随调度变化, 所以带 owner 比较仍是"重命名意义下"的比较.

import { processDiff } from './probes.mjs'

const rowKey = r => `${r.key ?? ''}\u0000${r.view ?? ''}\u0000${r.owner ?? ''}`

export function diffWorld(a = {}, b = {}, { skip = [] } = {}) {
  const out = []
  for (const table of new Set([...Object.keys(a), ...Object.keys(b)])) {
    if (skip.some(s => table.startsWith(s))) continue
    const ra = a[table] ?? [], rb = b[table] ?? []
    if (table.endsWith('[]') || table === 'cordis.listeners') {
      // 有序表: 整体比较次序.
      const sa = ra.map(rowKey).join('\n'), sb = rb.map(rowKey).join('\n')
      if (sa !== sb) out.push({ table, change: '~', from: ra, to: rb })
      continue
    }
    const ka = new Map(ra.map(r => [rowKey(r), r])), kb = new Map(rb.map(r => [rowKey(r), r]))
    for (const [k, r] of kb) if (!ka.has(k)) out.push({ table, change: '+', ...r })
    for (const [k, r] of ka) if (!kb.has(k)) out.push({ table, change: '-', ...r })
  }
  return out
}

// 恢复 (第 2 层): 卸载后的状态与影子 (从未安装) 比较.
//   leaks:      宿主登记表里残留的条目 (R1/R2) —— ✗
//   process:    进程级改动 (原型, globalThis, dns, 监听器, 句柄) —— 越出模型 (S3) 或未恢复的全局状态 (R4)
//   persistent: credentials 与临时 HOME 下的文件 —— 有意持久的外部状态, 只报告 (R4)
export function recovery(before, after) {
  const leaks = diffWorld(before.world, after.world, { skip: ['persistent:', 'cordis.fibers'] })
  const proc = processDiff(before.process, after.process)
  const persistent = [
    ...diffWorld(before.world, after.world).filter(d => d.table.startsWith('persistent:')),
    ...after.fs.filter(f => !before.fs.includes(f)).map(f => ({ table: 'fs', change: '+', key: f })),
  ]
  return { leaks, process: proc, persistent, ok: !leaks.length && !proc.length }
}

// 合流 (第 3 层): 两个落定状态是否相同. 进程级状态也比 (如 dns 设置谁最后写).
export function confluence(x, y) {
  const world = diffWorld(x.world, y.world)
  const dx = new Set(x.procDelta), dy = new Set(y.procDelta)
  const proc = [
    ...[...dy].filter(d => !dx.has(d)).map(d => ({ kind: '+', where: d, from: '', to: '' })),
    ...[...dx].filter(d => !dy.has(d)).map(d => ({ kind: '-', where: d, from: '', to: '' })),
  ]
  return { world, process: proc, ok: !world.length && !proc.length }
}

export function fmtRow(d) {
  if (d.change === '~') {
    const f = r => r.map(x => x.view ?? x.key).join(' | ')
    return `${d.table}: [${f(d.from)}] → [${f(d.to)}]`
  }
  return `${d.change} ${d.table} ${d.key ?? ''}${d.view && d.view !== d.key ? ` (${d.view})` : ''}${d.owner ? ` @${d.owner}` : ''}`
}

export function fmtProc(d) {
  if (d.kind === '+' || d.kind === '-') return `${d.kind} ${d.where}`
  return `${d.kind} ${d.where}: ${d.from} → ${d.to}`
}
