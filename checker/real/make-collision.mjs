// 生成"占住第 2 条路由"的场景 (whale 场景的通用版).
// 用法: node make-collision.mjs <条目 id> <第 1 条路由> <第 2 条路由> > scenarios/<名字>.json
const [id, r1, r2] = process.argv.slice(2)
const steps = [
  { op: 'settle' },
  { op: 'fibers', id, label: '装上后' },
  { op: 'route', path: r1, label: '装上后' },
  { op: 'disable', id },
  { op: 'settle' },
  { op: 'route', path: r1, label: '停用后' },
  { op: 'squat', path: r2 },
  { op: 'enable', id },
  { op: 'settle' },
  { op: 'fibers', id, label: '撞名后启用' },
  { op: 'route', path: r1, label: '撞名后启用' },
  { op: 'disable', id },
  { op: 'settle' },
  { op: 'fibers', id, label: '再停用后' },
  { op: 'route', path: r1, label: '再停用后' },
  { op: 'get', path: r1, label: '再停用后' },
  { op: 'unsquat', path: r2 },
  { op: 'enable', id },
  { op: 'settle' },
  { op: 'fibers', id, label: '撤掉占位再启用' },
  { op: 'route', path: r1, label: '撤掉占位再启用' },
  { op: 'route', path: r2, label: '撤掉占位再启用' },
  { op: 'done' },
]
console.log(JSON.stringify(steps, null, 1))
