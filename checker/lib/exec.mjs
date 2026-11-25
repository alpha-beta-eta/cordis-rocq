// 在一个新进程里执行一条调用序列, 把观察结果写成 JSON.
// 用法: node --import ./register.mjs lib/exec.mjs <scenario.json> <out.json>
//
// 每条序列一个进程: 插件的模块级状态 (如 dns 设置, globalThis 槽) 不会串到下一条序列.

import fs from 'node:fs'
const realExit = process.exit.bind(process)
import os from 'node:os'
import path from 'node:path'
import { pathToFileURL } from 'node:url'
import { Context } from '@deepseek-ai/cordis'
import { World, InjectedFault } from './world.mjs'
import { makeHost } from './host.mjs'
import { blockNetwork, processSnapshot, processDelta, fsSnapshot } from './probes.mjs'
import { resolvePlugin } from './plugins.mjs'

const [scenarioFile, outFile] = process.argv.slice(2).map(p => path.resolve(p))
const scenario = JSON.parse(fs.readFileSync(scenarioFile, 'utf8'))

// 隔离持久状态: HOME 与 DSH_HOME 指向临时目录.
const home = fs.mkdtempSync(path.join(os.tmpdir(), 'cordis-check-'))
for (const k of ['HOME', 'USERPROFILE', 'DSH_HOME']) process.env[k] = home
process.env.XDG_CONFIG_HOME = path.join(home, '.config')
process.env.XDG_DATA_HOME = path.join(home, '.local/share')
process.chdir(home)

const world = new World()
blockNetwork(world)

// 插件和 Cordis 的输出都收进 log, 不打到终端.
const log = []
for (const level of ['log', 'info', 'warn', 'error', 'debug']) {
  console[level] = (...args) => log.push(`[${level}] ${args.map(a => a instanceof Error ? a.stack : typeof a === 'string' ? a : safeJson(a)).join(' ')}`.slice(0, 2000))
}
const errors = []
process.on('unhandledRejection', (e) => errors.push({ kind: 'unhandledRejection', message: String(e?.message ?? e), injected: e instanceof InjectedFault }))
process.on('uncaughtException', (e) => errors.push({ kind: 'uncaughtException', message: String(e?.message ?? e), injected: e instanceof InjectedFault }))

function safeJson(v) { try { return JSON.stringify(v) } catch { return String(v) } }

const STATES = ['PENDING', 'LOADING', 'ACTIVE', 'FAILED', 'DISPOSED', 'UNLOADING']

// 落定: 先走几轮事件循环, 再等插件的 fiber 走出 LOADING. apply 里的异步加载 (例如动态 import
// @deepseek-ai/dsh-tools, 约 0.3 秒) 比几轮事件循环长, 只等固定的几轮, 快照就会停在 LOADING,
// 结果随机器负载变化. 每次最多等 SETTLE_MS; 超时还在 LOADING 的 fiber 记为卡住 (例如在等一个
// 永远不来的东西), 之后不再等它, 免得每一步都白等一遍.
const SETTLE_MS = Number(process.env.CHECK_SETTLE_MS ?? 2000)
const stuck = new WeakSet()
const loadingFibers = () => {
  const out = []
  for (const runtime of root.registry.values()) {
    for (const f of runtime.fibers ?? []) {
      if (f.state === 1 && !stuck.has(f) && world.owner(f.ctx) !== 'host') out.push(f)
    }
  }
  return out
}

async function settle() {
  const turns = async () => { for (let i = 0; i < 20; i++) await new Promise(r => setImmediate(r)) }
  await turns()
  await new Promise(r => setTimeout(r, 5))
  await turns()
  const deadline = Date.now() + SETTLE_MS
  let loading = loadingFibers()
  while (loading.length && Date.now() < deadline) {
    await new Promise(r => setTimeout(r, 20))
    await turns()
    loading = loadingFibers()
  }
  for (const f of loading) stuck.add(f)
}

// 宿主自己的库在插件之前就已加载 (schemastery 首次加载时会写 globalThis.__schemastery_*), 不算插件的效应.
await import('@deepseek-ai/schemastery')
const baseline = processSnapshot()
const root = new Context()
const host = makeHost(world)
const services = new Map() // 服务名 -> fiber
const installs = new Map() // 安装编号 -> fiber
const modules = new Map()

// 场景里会出现的宿主服务 (一开始就有的, 和后来 provide 的). 桩只 inject 其中的服务.
const universe = new Set([...(scenario.host ?? []), ...(scenario.actions ?? []).filter(a => a.op === 'provide').map(a => a.service)])

function provide(name) {
  if (services.has(name)) return
  services.set(name, root.plugin(host.plugin(name, universe)))
}

for (const name of scenario.host ?? []) provide(name)

// 真实 dsh 里插件由 loader 装载, 挂在 loader 的 fiber 子树下; 祖先 fiber 提供的服务 (如 loader 自己)
// 不经 inject 也能访问 (reflect.ts 的 get 沿 parent 链查 provisions). 这里照样把插件装在一个
// 提供 loader 的宿主 fiber 下. loader 的方法 (装卸别的插件, 即编排) 只记录, 不执行.
let loaderCtx
root.plugin({ name: 'host:loader', apply(ctx) { loaderCtx = ctx; host.loader(ctx) } })
await settle()

// Cordis 自己的状态: 谁提供了哪个服务, 每个事件上监听器的次序 (不含 internal/* 和宿主桩).
function cordisSnapshot() {
  const out = {}
  const services = []
  const store = root.reflect.store
  for (const key of Reflect.ownKeys(store)) {
    const impl = store[key]
    const owner = world.owner(impl.ctx)
    if (owner === 'host') continue
    services.push({ key: impl.name, view: 'service', owner })
  }
  if (services.length) out['cordis.services'] = services.sort((a, b) => a.key < b.key ? -1 : 1)
  const listeners = []
  const hooks = root.events._hooks
  for (const name of Reflect.ownKeys(hooks)) {
    if (typeof name === 'string' && name.startsWith('internal/')) continue
    const owners = (hooks[name] ?? []).map(h => world.owner(h.ctx))
    if (owners.every(o => o === 'host')) continue
    listeners.push({ key: String(name), view: owners.join(' > '), owner: [...new Set(owners)].join(',') })
  }
  if (listeners.length) out['cordis.listeners'] = listeners.sort((a, b) => a.key < b.key ? -1 : 1)
  // 所有 fiber (含 inject 子 fiber) 的状态, 按顶层安装归组.
  // uid 随调度变化, 不进快照: 同一安装下同名的 fiber 按 uid 排序后编号.
  const raw = []
  for (const runtime of root.registry.values()) {
    for (const f of runtime.fibers ?? []) {
      const owner = world.owner(f.ctx)
      if (owner === 'host') continue
      const provided = new Set(Reflect.ownKeys(root.reflect.store).map(k => root.reflect.store[k].name))
      const waiting = f.state === 0 ? Object.keys(f.inject ?? {}).filter(n => f.inject[n]?.required !== false && !provided.has(n)) : []
      const err = waiting.length ? ` (waiting: ${waiting.join(',')})` : f._error ? `: ${String(f._error?.message ?? f._error).slice(0, 120)}${process.env.CHECK_DEBUG ? `
${f._error?.stack}` : ''}` : ''
      raw.push({ owner, name: f.name, uid: f.uid ?? Infinity, view: `${STATES[f.state] ?? f.state}${err}` })
    }
  }
  raw.sort((a, b) => a.uid - b.uid)
  const seen = new Map()
  const fibers = raw.map(({ owner, name, view }) => {
    const base = `${owner}/${name}`
    const i = seen.get(base) ?? 0
    seen.set(base, i + 1)
    return { key: `${base}#${i}`, view, owner }
  })
  if (fibers.length) out['cordis.fibers'] = fibers.sort((a, b) => a.key < b.key ? -1 : 1)
  return out
}

const snaps = {}
const steps = []

for (const action of scenario.actions) {
  const step = { ...action }
  try {
    switch (action.op) {
      case 'fault':
        world.faults.push({ site: action.site, nth: action.nth, who: action.who })
        break
      case 'install': {
        const id = action.id ?? action.plugin
        let mod = modules.get(action.plugin)
        if (!mod) {
          const entry = resolvePlugin(action.plugin)
          step.entry = entry.label
          mod = await import(pathToFileURL(entry.main).href)
          modules.set(action.plugin, mod)
        }
        const def = action.export ? mod[action.export] : (mod.default ?? mod)
        const fiber = loaderCtx.plugin(def, action.config ?? {}) // dsh 的 loader 至少传一个空对象
        world.owners.set(fiber.uid, id)
        installs.set(id, fiber)
        break
      }
      case 'dispose': {
        const fiber = installs.get(action.id)
        await fiber.dispose()
        break
      }
      case 'provide':
        provide(action.service)
        break
      case 'withdraw': {
        const fiber = services.get(action.service)
        services.delete(action.service)
        await fiber?.dispose()
        break
      }
      case 'emit': {
        // 照 webServer.collectIndexInjections: 每次新建表 (host/webserver/src/index.ts:722).
        const args = (action.args ?? []).map(a => a === '$table' ? [] : a)
        root.emit(action.event, ...args)
        step.result = args.find(Array.isArray)
        break
      }
      case 'snap': {
        await settle()
        snaps[action.label] = {
          world: { ...world.snapshot({ owners: true }), ...cordisSnapshot() },
          process: processSnapshot(),
          procDelta: processDelta(baseline, processSnapshot()),
          fs: fsSnapshot(home),
          fibers: Object.fromEntries([...installs].map(([id, f]) => [id, STATES[f.state] ?? f.state])),
        }
        break
      }
      default:
        throw new Error(`unknown op ${action.op}`)
    }
  } catch (e) {
    step.error = String(e?.message ?? e)
    step.injected = e instanceof InjectedFault
  }
  await settle()
  steps.push(step)
}

fs.writeFileSync(outFile, JSON.stringify({
  baseline,
  snaps,
  steps,
  trace: world.trace,
  unmodeled: [...new Set(world.unmodeled)],
  stubbed: [...new Set(process[Symbol.for('cordis-check.stubs')] ?? [])],
  errors,
  log: log.slice(0, 200),
}, null, 1))
fs.rmSync(home, { recursive: true, force: true })
realExit(0)
