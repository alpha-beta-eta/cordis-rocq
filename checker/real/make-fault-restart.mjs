// 生成"占住第 2 条路由, 再重启 webServer"的场景 (checker 外的 P2 序列: R1 故障后提供者重启).
// 用法: node make-fault-restart.mjs <条目 id> <路由前缀> <第 1 条路由> <第 2 条路由> > scenarios/<名字>.json
// checker 的预测: 重启清掉泄漏的路由, 但失败的内层 fiber 不随 webServer 重跑, 插件一条路由都不剩;
// 之后重启插件本身才恢复.
const [id, prefix, r1, r2] = process.argv.slice(2)
const look = label => [
  { op: 'fibers', id, label },
  { op: 'routes', prefix, label },
  { op: 'route', path: r1, label },
]
const steps = [
  { op: 'settle' },
  ...look('装上后'),
  { op: 'disable', id },
  { op: 'settle' },
  { op: 'squat', path: r2 },
  { op: 'enable', id },
  { op: 'settle' },
  ...look('撞名后启用'),
  { op: 'disable', id: 'webserver' },
  { op: 'settle' },
  { op: 'enable', id: 'webserver' },
  { op: 'settle' },
  { op: 'wait', ms: 3000 },
  ...look('重启 webServer 后'),
  { op: 'get', path: r1, label: '重启 webServer 后' },
  { op: 'disable', id },
  { op: 'settle' },
  { op: 'enable', id },
  { op: 'settle' },
  { op: 'wait', ms: 3000 },
  ...look('再重启插件后'),
  { op: 'done' },
]
console.log(JSON.stringify(steps, null, 1))
