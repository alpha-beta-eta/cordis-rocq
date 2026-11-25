// 把驱动 graph 步骤的输出整理成 checker 用的服务依赖图 (lib/host-graph.json).
// 用法: node make-graph.mjs <out.json> <dsh 版本> > ../lib/host-graph.json
//
// 每个服务的依赖 = 它的提供者 fiber 链上每层 inject 的并集, 去掉 loader (宿主根上的编排服务, 从不重启).
// 同名服务有多个提供者 (同一条目下的几个 fiber) 时取并集.
import fs from 'node:fs'

const [file, version] = process.argv.slice(2)
const log = JSON.parse(fs.readFileSync(file, 'utf8'))
const step = log.find(e => e.op === 'graph')
if (!step) throw new Error(`no graph step in ${file}`)

const deps = {}
const entries = {}
for (const s of step.services) {
  const set = new Set(deps[s.name] ?? [])
  for (const layer of s.chain) for (const name of layer.inject) if (name !== 'loader' && name !== s.name) set.add(name)
  deps[s.name] = set
  if (s.entry) entries[s.name] = s.entry
}

const out = {
  source: `driver graph step on @deepseek-ai/dsh@${version ?? '?'} (checker/real/scenarios/graph.json)`,
  entries: Object.fromEntries(Object.keys(deps).sort().filter(n => entries[n]).map(n => [n, entries[n]])),
  deps: Object.fromEntries(Object.keys(deps).sort().map(n => [n, [...deps[n]].sort()])),
}
console.log(JSON.stringify(out, null, 1))
