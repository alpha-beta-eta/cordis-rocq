// 汇总 replay 的结果: 按分歧的种类归组, 每组给出最短的见证 (脚本和到分歧为止的事件).
// 用法: node summarize.mjs witnesses <results.txt> <cases.json> > witnesses.json   (每组最短见证的用例)
//       node summarize.mjs report <results.txt> <cases.json> <witnesses-trace.txt>  (报告)

import fs from 'node:fs'
import readline from 'node:readline'
import { describe } from './gen.mjs'

const [mode, resultsFile, casesFile, ...traceFiles] = process.argv.slice(2)
const input = JSON.parse(fs.readFileSync(casesFile, 'utf8'))
const cases = new Map(input.cases.map(tc => [tc.id, tc]))

const groups = new Map()
let ok = 0, total = 0
for (const line of fs.readFileSync(resultsFile, 'utf8').split('\n')) {
  if (!line.trim()) continue
  total++
  const m = line.match(/^(\S+) diverge (\d+) (\S+) (.*)$/)
  if (!m) { ok++; continue }
  const [, id, ev, kind, detail] = m
  // 组键: 去掉 fiber 编号, 保留键 (k), 名字 (x), 组件 (c) 和登记的值
  const key = `${kind}: ${detail.replace(/USpawn\(\d+\)/g, 'USpawn(#)').replace(/(?<![kxc=(,/:\d])\b\d+\b(?!:=|\d)/g, '#')}`
  const tc = cases.get(id)
  // 长度相同时优先不带加载中途动作的脚本
  const len = tc.script.length + tc.script.filter(a => a.at).length / 2
  const w = { id, ev: Number(ev), kind, detail, len, script: describe(tc.script) }
  const g = groups.get(key) ?? { key, kind, count: 0, best: w }
  g.count++
  if (w.len < g.best.len || (w.len === g.best.len && w.ev < g.best.ev)) g.best = w
  groups.set(key, g)
}

if (mode === 'witnesses') {
  const ids = new Set([...groups.values()].map(g => g.best.id))
  process.stdout.write(JSON.stringify({ lib: input.lib, cases: input.cases.filter(tc => ids.has(tc.id)) }))
  process.exit(0)
}

// 只取见证的事件行 (与 replay 计数一致: case/comp/keys/names 之后的每一行算一个事件)
const wanted = new Set([...groups.values()].map(g => g.best.id))
const events = new Map()
for (const file of traceFiles) {
  let cur = null
  for await (const line of readline.createInterface({ input: fs.createReadStream(file) })) {
    if (line.startsWith('case ')) {
      cur = wanted.has(line.slice(5)) ? [] : null
      if (cur) events.set(line.slice(5), cur)
      continue
    }
    if (!cur || /^(comp|keys|names|end)\b/.test(line)) continue
    cur.push(line)
  }
}

const out = []
out.push('# 差分测试结果', '', `${total} 个用例, ${ok} 个与演算一致, ${total - ok} 个有分歧, 归为 ${groups.size} 组.`, '')
const sorted = [...groups.values()].sort((a, b) => a.kind.localeCompare(b.kind) || b.count - a.count)
out.push('| 种类 | 分歧 | 用例数 | 最短见证 |', '|---|---|---|---|')
for (const g of sorted) out.push(`| ${g.kind} | ${g.key.slice(g.kind.length + 2)} | ${g.count} | \`${g.best.id}\`: ${g.best.script} |`)
out.push('')
for (const g of sorted) {
  const w = g.best
  out.push(`## ${g.key}`, '', `${g.count} 个用例. 最短见证 \`${w.id}\`: ${w.script}`, '', '```')
  const evs = events.get(w.id) ?? []
  evs.slice(0, w.ev).forEach((e, i) => out.push(`${i + 1 === w.ev ? '>>' : '  '} ${e}`))
  out.push('```', `分歧: ${w.detail}`, '')
}
process.stdout.write(out.join('\n') + '\n')
