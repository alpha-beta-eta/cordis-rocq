// 账本: 宿主桩上所有登记的唯一来源.
//
// 每个登记表是 键 -> 条目 的映射. 条目记下谁登记的 (顶层插件的安装编号, 由 owner() 求出)
// 和是哪种登记 (owned: 经调用者 ctx.effect, 随 fiber 撤销; bare: 只返回裸 disposer).
// 快照只比较表的内容 (键与值的可比部分), 不比较 owner, 这是 Observe.v 中 ≃ 的具体化:
// 令牌, fiber 编号, 安装编号都不进快照.

export class InjectedFault extends Error {
  constructor(site, nth) {
    super(`checker: injected fault at ${site} (call #${nth})`)
    this.site = site
    this.nth = nth
  }
}

export class World {
  constructor() {
    this.tables = new Map()
    this.counts = new Map()
    this.faults = []
    this.trace = []
    this.unmodeled = []
    this.owners = new Map() // 顶层 fiber 的 uid -> 安装编号 (ctx.fiber 经过代理, 不能比对象身份)
  }

  // 求一个 ctx 属于哪个顶层安装. 沿 fiber 的 parent 链向上找.
  owner(ctx) {
    let fiber = ctx?.fiber
    const seen = new Set()
    while (fiber && !seen.has(fiber)) {
      seen.add(fiber)
      if (fiber.uid != null && this.owners.has(fiber.uid)) return this.owners.get(fiber.uid)
      fiber = fiber.parent?.fiber
    }
    return 'host'
  }

  table(name) {
    let t = this.tables.get(name)
    if (!t) this.tables.set(name, t = new Map())
    return t
  }

  // 每次宿主调用都经过这里: 计数, 按故障计划抛错, 记入轨迹.
  hit(site, ctx, detail) {
    const who = this.owner(ctx)
    // 计数按 (site, 调用者) 分开: 故障计划说的"第 k 次"是该插件自己的第 k 次调用.
    const n = (this.counts.get(`${site}|${who}`) ?? 0) + 1
    this.counts.set(`${site}|${who}`, n)
    this.trace.push({ site, n, who, detail })
    for (const f of this.faults) {
      if (f.site === site && f.nth === n && (f.who === undefined || f.who === who)) {
        this.trace.push({ site, n, who, fault: true })
        throw new InjectedFault(site, n)
      }
    }
    return who
  }

  // 登记一个名字. dup: 'throw' 照 dsh 的 NamedEntries/WebServer 撞名即抛错.
  // 返回的 undo 是幂等的, 只撤掉这一次登记.
  insert(tableName, key, entry, { dup = 'throw' } = {}) {
    const t = this.table(tableName)
    if (t.has(key)) {
      if (dup === 'throw') throw new Error(`duplicate ${tableName} "${key}"`)
    }
    const cell = { ...entry }
    t.set(key, cell)
    let active = true
    return () => {
      if (!active) return
      active = false
      if (t.get(key) === cell) t.delete(key)
    }
  }

  // 追加到有序列表 (如中间件, tapIndex). 键可重复, 次序有意义.
  append(tableName, entry, { prepend = false } = {}) {
    const t = this.table(tableName)
    const list = t.get('*') ?? []
    const cell = { ...entry }
    if (prepend) list.unshift(cell); else list.push(cell)
    t.set('*', list)
    let active = true
    return () => {
      if (!active) return
      active = false
      const at = list.indexOf(cell)
      if (at !== -1) list.splice(at, 1)
      // 表可能已被 reset 换成了新列表 (服务重启), 那时旧列表的 undo 不碰新列表.
      if (!list.length && t.get('*') === list) t.delete('*')
    }
  }

  // 一个宿主服务的实例被卸载: 它名下的登记表随实例消失 (真实宿主里这些表是实例的字段).
  // 之后旧登记的 undo 按条目身份撤销, 不会碰到新实例上的同名登记.
  reset(prefixes) {
    for (const [name, t] of this.tables) {
      if (!name.startsWith('persistent:') && prefixes.some(p => name === p || name.startsWith(`${p}.`))) t.clear()
    }
  }

  // 规范化的快照: 只留表名, 键, 值的可比部分 (view), 以及 (可选) owner.
  snapshot({ owners = false } = {}) {
    const out = {}
    for (const [name, t] of [...this.tables].sort(([a], [b]) => a < b ? -1 : 1)) {
      if (!t.size) continue
      const rows = []
      for (const [key, cell] of t) {
        const cells = key === '*' ? cell : [cell]
        for (const c of cells) {
          const row = { key: key === '*' ? undefined : key, view: c.view }
          if (owners) row.owner = c.owner
          rows.push(row)
        }
      }
      if (name.endsWith('[]')) out[name] = rows // 有序表保持次序
      else out[name] = rows.sort((a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0))
    }
    return out
  }
}
