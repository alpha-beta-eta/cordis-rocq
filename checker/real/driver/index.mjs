// cordis-check 的真实宿主驱动插件.
//
// 装进一个真实的 dsh profile, 按 CHECK_REAL_SCENARIO 指向的场景文件逐步执行, 结果写到 CHECK_REAL_OUT.
// 它是一个编排者: 通过 ctx.loader 停用, 启用别的条目 (O-Dispose / O-Insert), 用真实的 HTTP 请求
// 探测路由, 读 Cordis 的服务表看服务归谁. 不打补丁, 不注入故障: 故障由真实的撞名触发.
//
// 场景是一个步骤数组, 每步一个对象:
//   { op: 'wait', ms }                    等待
//   { op: 'settle' }                      等 loader 的任务都完成, 再等 500 ms
//   { op: 'disable', id } / { op: 'enable', id }   停用 / 启用一个 loader 条目
//   { op: 'squat', path } / { op: 'unsquat', path } 驱动自己登记 / 撤销一条路由, 用来占住别的插件要用的路径
//   { op: 'get', path, label }            GET 一条路由, 记下状态码与响应体开头
//   { op: 'route', path, label }          读 webServer 内部路由表, 给该路径上的处理器函数编号 (同一函数对象同一编号)
//   { op: 'routes', prefix, label }       路径以 prefix 开头的全部路由与升级路由: 条数与处理器编号
//   { op: 'tools', names, label }         这些名字的工具在全局层上登记了没有
//   { op: 'proc', label }                 进程级状态: globalThis 的键, process 监听器数, dns 解析序, 句柄数
//   { op: 'squatSection', name } / { op: 'unsquatSection', name }  驱动登记 / 撤销一个提示段, 占住别的插件要用的段名
//   { op: 'sections', prefix, label }     systemPrompt 全局层上以 prefix 开头的段名
//   { op: 'services', name, label }       记下服务 name 由哪个插件提供
//   { op: 'fibers', id, label }           记下条目 id 下所有 fiber 的状态
//   { op: 'entries', match, label }       列出 loader 条目 (id, 插件名, 是否停用); match 是对 id 或插件名的子串过滤
//   { op: 'provider', name, label }       记下服务 name 由哪个 loader 条目提供 (提供者 fiber 往上找到的第一个条目)
//   { op: 'skillProviders', label }       记下 skills 服务全局层上登记的 provider 名
//   { op: 'listeners', event, label }     记下事件 event 上的监听器数, 按所属 loader 条目分组
//   { op: 'graph', label }          记下每个服务的提供者条目, 以及提供者 fiber 链上每层的 inject (服务依赖图)
//   { op: 'epoch', id, label }      记下条目根 fiber 的 epoch (inject 的服务实例 uid); 前后不同即被连带重启过
//   { op: 'indexInject', match, label }   收集一次 webserver/index-inject 表, 记下含 match 的行数
//   { op: 'config', id, merge }     改条目配置 (与现有配置按顶层键浅合并); 只改 volatile 节时热更新
//   { op: 'done' }                        写出结果
//
// 驱动不 inject 任何服务, 每次用到 webServer 时再读: 这样场景可以停用 webServer 的提供者 (服务晚到),
// 而驱动自己不被一起卸载.

import fs from 'node:fs'

export const name = 'cordis-check-driver'
export const inject = []

const STATES = ['PENDING', 'LOADING', 'ACTIVE', 'FAILED', 'DISPOSED', 'UNLOADING']

export function apply(ctx) {
  const scenarioFile = process.env.CHECK_REAL_SCENARIO
  const outFile = process.env.CHECK_REAL_OUT
  if (!scenarioFile || !outFile) return
  const steps = JSON.parse(fs.readFileSync(scenarioFile, 'utf8'))
  const log = []
  const squats = new Map()
  const record = (entry) => {
    log.push({ t: Date.now(), ...entry })
    fs.writeFileSync(outFile, JSON.stringify(log, null, 1))
  }
  const loader = ctx.get('loader')
  const webServer = () => {
    const ws = ctx.get('webServer')
    if (!ws) throw new Error('webServer is not available')
    return ws
  }
  const origin = () => webServer().getOrigin()
  // 服务表中名为 name 的项 (含提供者的 ctx).
  const serviceItems = (name) => {
    const store = ctx.root.reflect.store
    return Reflect.ownKeys(store).map(k => store[k]).filter(i => i.name === name)
  }
  // fiber 所属的 loader 条目: 条目记着自己的 fiber, 沿 parent 往上找.
  const entryOfFiber = (fiber) => {
    const byFiber = new Map([...loader.entries()].filter(e => e.fiber).map(e => [e.fiber.uid, e]))
    for (let f = fiber, n = 0; f && n < 64; f = f.parent?.fiber, n++) {
      const e = byFiber.get(f.uid)
      if (e) return e
    }
    return undefined
  }

  const handlerIds = new WeakMap()
  let nextHandler = 0
  const handlerId = (fn) => {
    if (!fn) return null
    if (!handlerIds.has(fn)) handlerIds.set(fn, `handler#${++nextHandler}`)
    return handlerIds.get(fn)
  }

  const findEntry = (id) => {
    const entry = [...loader.entries()].find(e => e.options.id === id)
    if (!entry) throw new Error(`no loader entry ${id}`)
    return entry
  }

  // 条目 id 对应的 fiber 子树. loader 的条目记着自己的 fiber.
  const entryFibers = (id) => {
    const entry = [...loader.entries()].find(e => e.options.id === id)
    if (!entry?.fiber) return { entry: entry ? 'no fiber' : 'no entry', disabled: entry?.options.disabled }
    const out = []
    const seen = new Set()
    const walk = (fiber, depth) => {
      if (!fiber || seen.has(fiber) || depth > 6) return
      seen.add(fiber)
      out.push(`${'  '.repeat(depth)}${fiber.name} ${STATES[fiber.state] ?? fiber.state}${fiber._error ? `: ${String(fiber._error.message ?? fiber._error).slice(0, 160)}` : ''}`)
      for (const runtime of ctx.root.registry.values()) {
        for (const child of runtime.fibers ?? []) if (child.uid != null && child.parent?.fiber?.uid === fiber.uid) walk(child, depth + 1)
      }
    }
    walk(entry.fiber, 0)
    return { disabled: entry.options.disabled ?? false, fibers: out }
  }

  const run = async () => {
    for (const step of steps) {
      try {
        switch (step.op) {
          case 'wait': await new Promise(r => setTimeout(r, step.ms)); break
          case 'settle':
            await loader.await?.()
            await new Promise(r => setTimeout(r, 500))
            break
          // bundle 组合出的树按嵌套路径寻址, loader.update(id) 找不到; 直接对条目对象 update,
          // 与 loader.update 走同一条 dispose / init 路径, 只是不写回配置文件.
          case 'disable': await findEntry(step.id).update({ disabled: true }); record({ op: 'disable', id: step.id }); break
          case 'enable': await findEntry(step.id).update({ disabled: null }); record({ op: 'enable', id: step.id }); break
          case 'squat': {
            const dispose = webServer().register({ kind: 'exact', path: step.path, handler: (req, res) => { res.writeHead(418); res.end('cordis-check-driver squat') } })
            squats.set(step.path, dispose)
            record({ op: 'squat', path: step.path })
            break
          }
          case 'unsquat': squats.get(step.path)?.(); squats.delete(step.path); record({ op: 'unsquat', path: step.path }); break
          case 'get': {
            const res = await fetch(origin() + step.path)
            const body = (await res.text()).slice(0, 120)
            record({ op: 'get', label: step.label, path: step.path, status: res.status, body })
            break
          }
          case 'route': {
            // WebServer 的 exact / prefixes 是 TS 的 private 字段, 运行时可读 (host/webserver/src/index.ts).
            const ws = serviceItems('webServer')[0]?.value
            if (!ws) { record({ op: 'route', label: step.label, path: step.path, registered: false, handler: null, note: 'no webServer' }); break }
            const route = ws.exact?.get(step.path) ?? ws.prefixes?.get(step.path)
            record({ op: 'route', label: step.label, path: step.path, registered: !!route, handler: handlerId(route?.handler) })
            break
          }
          case 'routes': {
            // 路径以 prefix 开头的全部 exact/prefix 路由与升级路由: 条数, 以及处理器函数的编号集合.
            const ws = serviceItems('webServer')[0]?.value
            if (!ws) { record({ op: 'routes', label: step.label, prefix: step.prefix, note: 'no webServer' }); break }
            const pick = (table) => [...(table?.entries() ?? [])].filter(([p]) => p.startsWith(step.prefix))
            const http = [...pick(ws.exact), ...pick(ws.prefixes)]
            const up = pick(ws.upgrades)
            const ids = (list) => [...new Set(list.map(([, r]) => handlerId(r?.handler)))]
            record({ op: 'routes', label: step.label, prefix: step.prefix, http: http.length, upgrades: up.length, httpHandlers: ids(http).length, upgradeHandlers: ids(up), sample: http.slice(0, 3).map(([p, r]) => `${p} ${handlerId(r?.handler)}`) })
            break
          }
          case 'tools': {
            // 全局层上这些名字的工具登记了没有 (tools.get(name) 不带 scope 即全局层).
            const tools = serviceItems('tools')[0]?.value
            const present = tools ? step.names.filter(n => tools.get(n)) : []
            record({ op: 'tools', label: step.label, present: present.length, of: step.names.length, missing: step.names.filter(n => !present.includes(n)) })
            break
          }
          case 'squatSection': {
            // 驱动自己登记一个提示段, 占住别的插件要用的段名; 重名时 systemPrompt.section 抛错.
            const dispose = ctx.get('systemPrompt').section({ name: step.name, order: 0, interpolate: false, text: '' })
            squats.set(`section:${step.name}`, dispose)
            record({ op: 'squatSection', name: step.name })
            break
          }
          case 'unsquatSection': squats.get(`section:${step.name}`)?.(); squats.delete(`section:${step.name}`); record({ op: 'unsquatSection', name: step.name }); break
          case 'sections': {
            // systemPrompt 全局层上名字以 prefix 开头的段 (layers 是 TS 的 private 字段, 运行时可读).
            const sp = serviceItems('systemPrompt')[0]?.value
            const names = sp ? [...sp.layers.global.sections.entries()].map(([n]) => n).filter(n => n.startsWith(step.prefix)) : []
            record({ op: 'sections', label: step.label, prefix: step.prefix, names })
            break
          }
          case 'proc': {
            // 进程级状态 (与 checker 的 probes.mjs 同一组观察): globalThis 的自有键, process 监听器数,
            // dns 解析序, 长命句柄数. 驱动与宿主同一个进程, 所以看到的就是宿主的状态.
            const globals = Reflect.ownKeys(globalThis).map(k => typeof k === 'symbol' ? `Symbol(${k.description})` : k).sort()
            const listeners = Object.fromEntries(['exit', 'beforeExit', 'uncaughtException', 'unhandledRejection', 'warning', 'SIGINT', 'SIGTERM'].map(e => [e, process.listenerCount(e)]))
            const handles = {}
            for (const r of process.getActiveResourcesInfo()) handles[r] = (handles[r] ?? 0) + 1
            record({ op: 'proc', label: step.label, globals, listeners, dns: (await import('node:dns')).getDefaultResultOrder(), handles })
            break
          }
          case 'services': {
            const owners = serviceItems(step.name).filter(i => i.value != null).map(i => i.ctx.fiber.name)
            record({ op: 'services', label: step.label, name: step.name, owners })
            break
          }
          case 'entries': {
            const list = [...loader.entries()]
              .map(e => ({ id: e.options.id, name: e.options.name, disabled: e.options.disabled ?? false, state: e.fiber ? STATES[e.fiber.state] : null }))
              .filter(e => !step.match || String(e.id).includes(step.match) || String(e.name).includes(step.match))
            record({ op: 'entries', label: step.label, entries: list })
            break
          }
          case 'provider': {
            const items = serviceItems(step.name).filter(i => i.value != null)
            const providers = items.map(i => {
              const e = entryOfFiber(i.ctx.fiber)
              return { fiber: i.ctx.fiber.name, entry: e?.options.id ?? null, plugin: e?.options.name ?? null }
            })
            record({ op: 'provider', label: step.label, name: step.name, providers })
            break
          }
          case 'listeners': {
            // 事件 event 上的监听器, 按所属 loader 条目计数.
            const hooks = ctx.root.events._hooks?.[step.event] ?? []
            const counts = {}
            for (const h of hooks) {
              const e = h.ctx?.fiber ? entryOfFiber(h.ctx.fiber) : undefined
              const k = e?.options.id ?? '?'
              counts[k] = (counts[k] ?? 0) + 1
            }
            record({ op: 'listeners', label: step.label, event: step.event, counts })
            break
          }
          case 'skillProviders': {
            const skills = serviceItems('skills').find(i => i.value != null)?.value
            // SkillRegistry 的 layers 与 NamedEntries 的 data 是 TS 的 private 字段, 运行时可读
            // (skill/skill/src/index.ts, core/scope/src/store.ts).
            const names = skills ? [...(skills.layers?.global?.providers?.data?.keys() ?? [])] : null
            record({ op: 'skillProviders', label: step.label, names })
            break
          }
          case 'graph': {
            // 服务依赖图: 每个服务的提供者 fiber 沿 parent 往上到根, 记下每一层 fiber 的 inject.
            // 链上任何一层 inject 的服务被撤走, 提供者都会被卸载 (Fiber._refresh 把 epoch 置为 INACTIVE).
            const store = ctx.root.reflect.store
            const services = []
            for (const k of Reflect.ownKeys(store)) {
              const item = store[k]
              if (item?.value == null || !item.ctx?.fiber) continue
              const chain = []
              for (let f = item.ctx.fiber, n = 0; f && f.runtime && n < 64; f = f.parent?.fiber, n++) {
                chain.push({ fiber: f.name, inject: Object.keys(f.inject ?? {}) })
              }
              const e = entryOfFiber(item.ctx.fiber)
              services.push({ name: item.name, entry: e?.options.id ?? null, plugin: e?.options.name ?? null, chain })
            }
            record({ op: 'graph', label: step.label, services })
            break
          }
          case 'epoch': {
            // 条目根 fiber 的 epoch: 修订号加上每个 inject 的服务实例 uid (Fiber._refresh).
            // 前后不同说明它 inject 的某个服务换了实例, 即它被连带重启过.
            const entry = findEntry(step.id)
            record({ op: 'epoch', label: step.label, id: step.id, epoch: entry.fiber?._runner?.epoch ?? null, inject: Object.keys(entry.fiber?.inject ?? {}) })
            break
          }
          case 'indexInject': {
            // 收集一次 index-inject 表, 记下含 match 的行. webServer 在时走它自己的 collectIndexInjections
            // (host/webserver/src/index.ts:725, 即 emit 一次再返回表); 不在时照同一写法直接 emit.
            // peer 取宿主所有者自己的页面 (remoteAccess 的监听器要读 peer.principal.kind).
            const peer = { principal: { kind: 'owner' } }
            const ws = serviceItems('webServer')[0]?.value
            let table = [], via = 'emit'
            if (typeof ws?.collectIndexInjections === 'function') { table = ws.collectIndexInjections(peer); via = 'webServer' }
            else ctx.root.emit('webserver/index-inject', table, peer)
            const rows = table.filter(r => JSON.stringify(r).includes(step.match ?? ''))
            record({ op: 'indexInject', label: step.label, via, rows: rows.length, total: table.length })
            break
          }
          case 'config': {
            // 改条目的配置: merge 的每个顶层键与现有配置浅合并一层. 只改 volatile 节时 loader 热更新, 不重挂.
            const entry = findEntry(step.id)
            const config = { ...(entry.options.config ?? {}) }
            for (const [k, v] of Object.entries(step.merge)) {
              config[k] = v && typeof v === 'object' && !Array.isArray(v) ? { ...(config[k] ?? {}), ...v } : v
            }
            await entry.update({ config })
            record({ op: 'config', id: step.id, merge: step.merge })
            break
          }
          case 'fibers': record({ op: 'fibers', label: step.label, id: step.id, ...entryFibers(step.id) }); break
          case 'done': record({ op: 'done' }); break
        }
      } catch (e) {
        record({ op: step.op, error: String(e?.stack ?? e).slice(0, 400) })
      }
    }
  }
  // 不阻塞自己的 apply; 驱动的步骤在宿主启动之后跑.
  const timer = setTimeout(() => { run() }, 0)
  ctx.effect(() => () => clearTimeout(timer))
}
