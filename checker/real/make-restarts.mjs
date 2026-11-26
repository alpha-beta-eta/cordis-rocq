// 生成"连续重启一个服务提供者 n 次"的场景 (checker 外的 P3 序列: 累积).
// 用法: node make-restarts.mjs <插件条目 id> <n> <提供者条目 id>... > scenarios/<名字>.json
// 每次重启后记下插件的 fiber 与进程级状态 (process 监听器, globalThis).
const [id, n, ...providers] = process.argv.slice(2)
const look = label => [{ op: 'fibers', id, label }, { op: 'proc', label }]
const steps = [{ op: 'settle' }, { op: 'wait', ms: 3000 }, ...look('装上后')]
for (const p of providers) {
  for (let i = 1; i <= Number(n); i++) {
    steps.push({ op: 'disable', id: p }, { op: 'settle' }, { op: 'enable', id: p }, { op: 'settle' }, { op: 'wait', ms: 3000 })
    steps.push(...look(`${p} 重启 ${i} 次`))
  }
}
steps.push({ op: 'done' })
console.log(JSON.stringify(steps, null, 1))
