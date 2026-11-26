// 把驱动的结果打印成一行一步. 用法: node show.mjs <out.json>
import fs from 'node:fs'
for (const e of JSON.parse(fs.readFileSync(process.argv[2], 'utf8'))) {
  const bits = [e.op.padEnd(8), (e.label ?? e.id ?? '').padEnd(14)]
  if (e.status !== undefined) bits.push(`HTTP ${e.status} ${e.body.slice(0, 48)}`)
  if (e.registered !== undefined) bits.push(e.registered ? `已登记, ${e.handler}` : '未登记')
  if (e.owners) bits.push(`${e.name} -> ${e.owners.join(', ') || '(无)'}`)
  if (e.entries) bits.push(e.entries.map(x => `${x.id}=${x.name}${x.disabled ? '(off)' : ''}:${x.state}`).join(' '))
  if (e.providers) bits.push(`${e.name} -> ${e.providers.map(p => `${p.entry ?? '?'} [${p.fiber}]`).join(', ') || '(无)'}`)
  if (e.op === 'skillProviders') bits.push(e.names ? e.names.join(', ') || '(空)' : '(没有 skills 服务)')
  if (e.counts) bits.push(`${e.event}: ${Object.entries(e.counts).map(([k, n]) => `${k}×${n}`).join(', ') || '(无)'}`)
  if (e.op === 'routes' && !e.note) bits.push(`${e.prefix}* 路由 ${e.http} 条 (处理器 ${e.httpHandlers} 个), 升级 ${e.upgrades} 条${e.sample.length ? `; 例: ${e.sample.join(', ')}` : ''}`)
  if (e.op === 'tools') bits.push(`工具 ${e.present}/${e.of}${e.missing.length ? `, 缺 ${e.missing.length} 个` : ''}`)
  if (e.op === 'proc') bits.push(`globalThis ${e.globals.length} 个键, dns ${e.dns}, exit×${e.listeners.exit} beforeExit×${e.listeners.beforeExit}, Timeout×${e.handles.Timeout ?? 0} (对照用 out.json)`)
  if (e.op === 'sections') bits.push(e.names.join(', ') || '(无)')
  if (e.op === 'squatSection' || e.op === 'unsquatSection') bits.push(e.name)
  if (e.op === 'indexInject') bits.push(`index-inject 行 ${e.rows} (表共 ${e.total} 行, 经 ${e.via})`)
  if (e.op === 'config') bits.push(JSON.stringify(e.merge))
  if (e.note) bits.push(e.note)
  if (e.op === 'epoch') bits.push(`${e.id} epoch=${e.epoch} inject=[${(e.inject ?? []).join(',')}]`)
  if (e.services) bits.push(`${e.services.length} 个服务 (完整数据见 out.json)`)
  if (e.fibers) bits.push(e.fibers.map(f => f.trim()).join(' / '))
  if (e.error) bits.push(`ERROR ${e.error.split('\n')[0]}`)
  console.log(bits.join(' '))
}
