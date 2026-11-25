// 在真实的 Cordis 上跑测试用例, 记下每个生命周期事件和事件发生时的状态快照, 写成 replay 读的文本格式.
// 用法 (WSL): node --import ../../checker/register.mjs run.mjs <cases.json> <out.txt> [i/N]
// 给出 i/N 时只跑编号模 N 余 i 的用例 (并行用).
//
// cases.json 是 { lib: [组件], cases: [用例] }, 用例里没有 comps 时用 lib. 用例:
//   { id, comps: [{ deps: [k], provs: [k], body: [instr] }], script: [action] }
//   instr:  ['op', k, x, v]  在键 k 的登记表上登记 x ↦ v (演算的 POp k (Register x v))
//           ['provide', k]   提供键 k, 初值是空登记表 (PProvide k ∅)
//           ['spawn', c]     在加载中装上组件 c (PSpawn c)
//           ['fail']         加载失败 (PFail)
//   action: { op: 'insert', c } | { op: 'dispose' | 'restart' | 'reset', i }   (i: 第 i 次 insert 的 fiber)
//           加上 at: [c, j] 时, 这个动作在组件 c 的 fiber 第一次走到第 j 条指令之前同步执行 (加载中途),
//           否则按顺序执行, 每个动作之后等 Cordis 落定.
//
// 组件 c 生成一个 Cordis 插件: inject 声明的依赖 (服务名 s<k>), apply 是 async 函数,
// 每条指令之前 await 一次 (让出事件循环, 别的 fiber 和编排动作可以插进来).
// 键 k 的服务值是 Reg: 一张登记表, register 在名字已占用时抛错, 返回的 disposer 删掉这一项.

import fs from 'node:fs'
import { Context, Fiber, DisposableList } from '@deepseek-ai/cordis'

// 变异 (检查测试本身): DIFFTEST_MUTANT 给出时, 往 Cordis 或测试服务里种一个已知的错误,
// 用来确认 replay 能发现它. 正常运行时不设.
//   leak     服务的 disposer 不删登记项
//   fifo     卸载时按登记顺序 (而不是逆序) 启动 disposer
//   noguard  依赖者不登记到提供者的 dependents 里, 提供者卸载时不等依赖者
const MUTANT = process.env.DIFFTEST_MUTANT
const STYLE = process.env.DIFFTEST_STYLE ?? 'fn'
if (!['fn', 'gen'].includes(STYLE)) throw new Error(`unknown style ${STYLE}`)
if (MUTANT === 'fifo') {
  DisposableList.prototype.clear = function () {
    const values = [...this.map.values()]
    this.map.clear()
    return values
  }
} else if (MUTANT === 'noguard') {
  const reload = Fiber.prototype._reload
  Fiber.prototype._reload = function () {
    const task = reload.call(this)
    for (const impl of Object.values(this.committed ?? {})) impl.dependents.delete(this)
    return task
  }
} else if (MUTANT && MUTANT !== 'leak') {
  throw new Error(`unknown mutant ${MUTANT}`)
}

const STATES = ['PENDING', 'LOADING', 'ACTIVE', 'FAILED', 'DISPOSED', 'UNLOADING']
const [casesFile, outFile, shard] = process.argv.slice(2)
const [si, sn] = (shard ?? '0/1').split('/').map(Number)
const { lib, cases: all } = JSON.parse(fs.readFileSync(casesFile, 'utf8'))
const cases = all.filter((_, i) => i % sn === si).map(tc => ({ comps: lib, ...tc }))
const out = []

// Cordis 把插件的错误打到 logger; 测试里不要这些输出.
for (const level of ['log', 'info', 'warn', 'error', 'debug']) console[level] = () => {}

const turn = () => new Promise(r => setImmediate(r))

async function runCase(tc) {
  const root = new Context()
  const lines = []
  const ids = new WeakMap() // fiber -> 编号 (按创建顺序, 卸载后 uid 变 null, 所以不用 uid)
  const fibers = []         // 编号 -> fiber
  const inserted = []       // 第 i 次 insert 的 fiber (wrapped)
  const armed = (tc.script ?? []).filter(a => a.at)
  const keys = [...new Set(tc.comps.flatMap(c => [...c.deps, ...c.provs]))].sort((a, b) => a - b)
  const names = [...new Set(tc.comps.flatMap(c => c.body.filter(i => i[0] === 'op').map(i => i[2])))].sort((a, b) => a - b)
  const idOf = (fiber) => ids.get(fiber) ?? '?'

  class Reg {
    constructor(k) { this.k = k; this.map = new Map() }
    register(caller, x, v) {
      if (this.map.has(x)) {
        log(`op ${caller} ${this.k} ${x} ${v} 0`)
        throw new Error(`name ${x} taken`)
      }
      this.map.set(x, v)
      log(`op ${caller} ${this.k} ${x} ${v} 1`)
      return () => {
        if (MUTANT !== 'leak') this.map.delete(x)
        log(`undo ${caller} ${this.k} ${x}`)
      }
    }
  }

  function snapshot() {
    const f = fibers.map((fiber, id) => `${id}=${STATES[fiber.state] ?? fiber.state}${fiber.uid === null ? '!' : ''}`)
    const b = []
    const store = root.reflect.store
    for (const sym of Reflect.ownKeys(store)) {
      const impl = store[sym]
      if (!(impl?.value instanceof Reg)) continue
      const vals = names.map(x => impl.value.map.has(x) ? impl.value.map.get(x) : '-')
      b.push(`${impl.value.k}=${idOf(impl.ctx.fiber)}:${vals.join('/') || '.'}`)
    }
    return `| F ${f.join(' ')} | B ${b.join(' ')}`
  }
  function log(ev) { lines.push(`ev ${ev} ${snapshot()}`) }

  // 撤回: provide 的 disposer 从 store 里删掉 impl. 用 Proxy 接住删除.
  const reflect = root.reflect
  const rawStore = reflect.store
  reflect.store = new Proxy(rawStore, {
    deleteProperty(target, key) {
      const impl = target[key]
      delete target[key]
      if (impl?.value instanceof Reg) log(`withdraw ${idOf(impl.ctx.fiber)} ${impl.value.k}`)
      return true
    },
  })

  const defs = []
  const compOf = new Map() // apply -> 组件编号
  const fired = new Set()
  async function gate(c, j) {
    for (const a of armed) {
      if (fired.has(a) || a.at[0] !== c || a.at[1] !== j) continue
      fired.add(a)
      act(a)
    }
    await turn()
  }
  tc.comps.forEach((comp, c) => {
    // 两种写法 (DIFFTEST_STYLE):
    //   fn   apply 是 async 函数, 操作经 ctx.effect 登记逆. Cordis 让整个函数跑完 (差异 h 的"落地").
    //   gen  apply 返回 async 生成器, 每个操作 yield 它的逆. Cordis 在两次迭代之间检查 epoch,
    //        变了就停 (放弃剩下的操作), 这是 EDSL 的写法 (docs/EDSL.md).
    const instr = (ctx, me, [kind, ...args]) => {
      if (kind === 'op') {
        const [k, x, v] = args
        return ctx[`s${k}`].register(me, x, v)
      } else if (kind === 'provide') {
        const [k] = args
        ctx.provide(`s${k}`, new Reg(k))
        log(`provide ${me} ${k}`)
      } else if (kind === 'spawn') {
        ctx.plugin(defs[args[0]])
      } else if (kind === 'fail') {
        throw new Error('PFail')
      }
    }
    const apply = STYLE === 'gen'
      ? (ctx) => { // 箭头函数: 普通 function 会被 Cordis 当成类 (isConstructor) 用 new 调用
        const me = idOf(ctx.fiber)
        return (async function* () {
          for (let j = 0; j < comp.body.length; j++) {
            await gate(c, j)
            const undo = instr(ctx, me, comp.body[j])
            if (undo) yield undo
          }
          await gate(c, comp.body.length)
        })()
      }
      : async function (ctx) {
        const me = idOf(ctx.fiber)
        for (let j = 0; j < comp.body.length; j++) {
          await gate(c, j)
          if (comp.body[j][0] === 'op') ctx.effect(() => instr(ctx, me, comp.body[j]), 'op')
          else instr(ctx, me, comp.body[j])
        }
        await gate(c, comp.body.length)
      }
    compOf.set(apply, c)
    defs.push({ name: `c${c}`, inject: comp.deps.map(k => `s${k}`), apply })
  })

  root.on('internal/plugin', (fiber) => {
    if (ids.has(fiber)) return // 卸载时也发这个事件
    const c = compOf.get(fiber.runtime?.callback)
    if (c === undefined) return
    ids.set(fiber, fibers.length)
    fibers.push(fiber)
    const parent = fiber.parent.fiber
    const p = ids.has(parent) ? ids.get(parent) : '-'
    log(`create ${ids.get(fiber)} ${c} ${p}`)
  })
  root.on('internal/status', (fiber, old) => {
    if (!ids.has(fiber)) return
    log(`status ${ids.get(fiber)} ${STATES[old]} ${STATES[fiber.state]} ${fiber._error ? 1 : 0}`)
  })

  function act(a) {
    try {
      if (a.op === 'insert') {
        inserted.push(root.plugin(defs[a.c]))
      } else {
        const fiber = inserted[a.i]
        if (!fiber) return
        log(`orch ${a.op} ${idOf(fiber.ctx.fiber)}`)
        let r
        if (a.op === 'dispose') r = fiber.dispose()
        else if (a.op === 'restart') r = fiber.restart()
        else if (a.op === 'reset') r = fiber.update(fiber.config)
        Promise.resolve(r).catch(() => {})
      }
    } catch (e) {
      lines.push(`throw ${a.op} ${a.op === 'insert' ? '-' : idOf(inserted[a.i]?.ctx.fiber)} ${String(e?.message ?? e).replace(/\s+/g, '_')}`)
    }
  }

  async function settle() {
    for (let round = 0; round < 200; round++) {
      for (let i = 0; i < 10; i++) await turn()
      if (fibers.every(f => !f.inertia)) {
        lines.push('settled')
        return true
      }
    }
    lines.push('stuck')
    return false
  }

  for (const a of tc.script ?? []) {
    if (a.at) continue
    act(a)
    if (!await settle()) break
  }
  if (!(tc.script ?? []).some(a => !a.at)) await settle()

  const comps = tc.comps.map((comp, c) => {
    const body = comp.body.map(([k, ...xs]) => [k, ...xs].join('.')).join(';') || '-'
    return `comp ${c} ${comp.deps.join(',') || '-'} ${comp.provs.join(',') || '-'} ${body}`
  })
  out.push(`case ${tc.id}`, ...comps, `keys ${keys.join(',') || '-'}`, `names ${names.join(',') || '-'}`, ...lines, 'end')
}

for (const tc of cases) await runCase(tc)
fs.writeFileSync(outFile, out.join('\n') + '\n')
process.exit(0)
