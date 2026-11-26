// dsh 宿主服务的桩. 只模拟登记语义, 不模拟业务.
//
// 每个桩方法的语义照 deepseek-harness 源码 (见 .vendor/SOURCE 的提交) 写, 注释里给出出处.
// 两种登记方式要分清, 因为它决定了插件中途抛错或卸载时登记会不会自动撤销:
//   owned: 宿主经调用者的 ctx.effect 登记 (ScopedLayers.effect, core/scope/src/store.ts),
//          卸载调用者的 fiber 时自动撤销. 例: tools.register, systemPrompt.section.
//   bare:  宿主只返回一个裸 disposer, 不归任何 fiber (host/webserver/src/index.ts).
//          插件不自己登记它的逆, 就会泄漏. 例: webServer.register, webServer.tapIndex.
// 没有桩的服务由 GenericService 顶替: 调用被记为 unmodeled, 返回 undefined.

import fs from 'node:fs'
import { Service } from '@deepseek-ai/cordis'

// 真实宿主的服务依赖图 (real/make-graph.mjs 从驱动的 graph 步骤生成): 服务 -> 它的提供者 fiber 链上 inject 的服务.
// 桩照它声明 inject, 于是撤走一个服务时, Cordis 像在真实宿主里一样连带卸载依赖它的宿主服务,
// 再连带卸载 inject 了这些服务的插件 (级联重启).
export const GRAPH = JSON.parse(fs.readFileSync(new URL('./host-graph.json', import.meta.url), 'utf8'))

// name 经依赖图可达的所有服务 (传递闭包). 中间服务不在宿主里时也要穿过它:
// 例如 subagents -> workingDirectory -> systemPrompt, 而 checker 的宿主没有 workingDirectory.
export function closure(name) {
  const seen = new Set()
  const walk = n => { for (const d of GRAPH.deps[n] ?? []) if (!seen.has(d)) { seen.add(d); walk(d) } }
  walk(name)
  seen.delete(name)
  return seen
}

// 经调用者 ctx.effect 登记: 照 ScopedLayers.effect, 先登记 fiber 效应, 效应体内做插入.
function owned(world, ctx, site, table, key, view) {
  const who = world.hit(site, ctx, key)
  return ctx.effect(function* () {
    const undo = world.insert(table, key, { owner: who, view })
    yield () => undo()
  }, site)
}

// 贡献模式 (CHECK_CONTRIB=1, docs/CONTRIB.md 的 E6e): 宿主满足 H1, 所有登记都经调用者的 fiber (owned);
// 撞名不抛错, 由 world 按多重集记下 (H2). 用来检验"宿主改成贡献键之后, 哪些见证会消失".
export const CONTRIB = process.env.CHECK_CONTRIB === '1'

// 只返回裸 disposer.
function bare(world, ctx, site, table, key, view) {
  if (CONTRIB) return owned(world, ctx, site, table, key, view)
  const who = world.hit(site, ctx, key)
  return world.insert(table, key, { owner: who, view })
}

function bareAppend(world, ctx, site, table, view, opts) {
  const who = world.hit(site, ctx, view)
  if (CONTRIB) {
    return ctx.effect(function* () {
      const undo = world.append(table, { owner: who, view }, opts)
      yield () => undo()
    }, site)
  }
  return world.append(table, { owner: who, view }, opts)
}

export function makeHost(world) {
  // 服务实例的登记表随实例消失: 提供者被卸载 (重启, 撤走) 时清空它名下的表.
  // 真实宿主里这些表是服务实例的字段, 新实例从空表开始.
  const instance = (ctx, prefix) => ctx.effect(() => () => world.reset([prefix]), `host:${prefix} instance`)

  // host/webserver/src/index.ts: register/registerUpgrade/registerFallback/tapIndex 都返回裸 disposer,
  // (kind, path) 撞名抛错.
  class WebServer extends Service {
    constructor(ctx) { super(ctx, 'webServer'); instance(ctx, 'webServer') }
    get protocol() { return 'http:' }
    get host() { return '127.0.0.1' }
    get port() { return 3080 }
    getOrigin() { return 'http://127.0.0.1:3080' }
    register(route) {
      return bare(world, this.ctx, 'webServer.register', `webServer.routes`, `${route.kind} ${route.path}`, route.kind)
    }
    registerUpgrade(route) {
      return bare(world, this.ctx, 'webServer.registerUpgrade', 'webServer.upgrades', route.path, 'upgrade')
    }
    registerFallback() {
      return bare(world, this.ctx, 'webServer.registerFallback', 'webServer.fallback', 'fallback', 'fallback')
    }
    tapIndex() {
      return bareAppend(world, this.ctx, 'webServer.tapIndex', 'webServer.indexTaps[]', 'tap')
    }
    applyIndexTaps(html) { return html }
    // collectIndexInjections: 每次新建表, emit 给订阅者 (index.ts:722).
    collectIndexInjections(peer) {
      const table = []
      this.ctx.emit('webserver/index-inject', table, peer)
      return table
    }
  }

  // core/tools/src/index.ts: register/restrict/guard 都经 ScopedLayers.effect (owned),
  // 同层撞名抛错 (NamedEntries.insert).
  class Tools extends Service {
    constructor(ctx) { super(ctx, 'tools'); instance(ctx, 'tools') }
    register(def) {
      return owned(world, this.ctx, 'tools.register', 'tools', def?.name, 'tool')
    }
    restrict(filter) {
      const who = world.hit('tools.restrict', this.ctx, filter)
      return this.ctx.effect(function* () {
        const undo = world.append('tools.restrictions[]', { owner: who, view: JSON.stringify(filter) })
        yield () => undo()
      }, 'tools.restrict')
    }
    guard() {
      const who = world.hit('tools.guard', this.ctx)
      return this.ctx.effect(function* () {
        const undo = world.append('tools.guards[]', { owner: who, view: 'guard' })
        yield () => undo()
      }, 'tools.guard')
    }
    get() { return undefined }
    definitions() { return [] }
  }

  // core/system-prompt/src/index.ts: section/context/variable/tools 都是 owned, 按名字撞名抛错.
  class SystemPrompt extends Service {
    constructor(ctx) { super(ctx, 'systemPrompt'); instance(ctx, 'systemPrompt') }
    section(s) { return owned(world, this.ctx, 'systemPrompt.section', 'systemPrompt.sections', s?.name, 'section') }
    context(c) { return owned(world, this.ctx, 'systemPrompt.context', 'systemPrompt.contexts', c?.name, 'context') }
    variable(name) { return owned(world, this.ctx, 'systemPrompt.variable', 'systemPrompt.variables', name, 'variable') }
    tools() {
      const who = world.hit('systemPrompt.tools', this.ctx)
      return this.ctx.effect(function* () {
        const undo = world.append('systemPrompt.toolProviders[]', { owner: who, view: 'provider' })
        yield () => undo()
      }, 'systemPrompt.tools')
    }
    suppressRuntimeContext() {
      const who = world.hit('systemPrompt.suppressRuntimeContext', this.ctx)
      return this.ctx.effect(function* () {
        const undo = world.append('systemPrompt.suppressors[]', { owner: who, view: 'suppress' })
        yield () => undo()
      }, 'systemPrompt.suppressRuntimeContext')
    }
    getSectionOrder() { return 0 }
    getContextOrder() { return 0 }
  }

  // credentials/credentials: 持久存储. set 是有意持久的外部状态 (R4), 进 persistent 表.
  class Credentials extends Service {
    constructor(ctx) { super(ctx, 'credentials') }
    get(key) { world.hit('credentials.get', this.ctx, key); return undefined }
    has(key) { world.hit('credentials.has', this.ctx, key); return false }
    set(key, value) {
      const who = world.hit('credentials.set', this.ctx, key)
      world.table('persistent:credentials').set(key, { owner: who, view: 'set' })
    }
    delete(key) {
      world.hit('credentials.delete', this.ctx, key)
      world.table('persistent:credentials').delete(key)
    }
  }

  // client/connection/src/rpc-host.ts. requestRejection 返回 undefined 表示放行.
  // rpc 与 fetch 是 getter, 以读到服务的那个 ctx (调用者) 为 owner, 三种登记都经 owner.effect (owned):
  //   rpc.handle(channel, h): 在效应体内用 owner.webServer.register 登记一条 prefix 路由 (rpc-host.ts:253).
  //     读 owner.webServer 要求调用者 inject 了 webServer (否则 Cordis 抛 "without inject"),
  //     而 inject 了的调用者会随 webServer 重启, 所以通道能随 webServer 重新登记.
  //     不 inject 的调用者在这里就失败 (真实宿主上的 token-diet 因此退到自己登记的路由).
  //   rpc.intercept(channel, ...): 只接受 '/api', 每个通道一个拦截器, 重复抛错 (rpc-host.ts:279).
  //   fetch.register(route): /api 下的精确路由, 同一路径重复抛错 (rpc-host.ts:234).
  const CHANNEL_PATTERN = /^\/[A-Za-z0-9._~-]+$/
  class Connection extends Service {
    constructor(ctx) { super(ctx, 'connection'); instance(ctx, 'connection') }
    requestRejection() { return undefined }
    get rpc() {
      const owner = this.ctx
      return {
        handle(channel, handler) {
          world.hit('connection.rpc.handle', owner, channel)
          // assertChannel (rpc-host.ts:396)
          if (!CHANNEL_PATTERN.test(channel) || channel === '/api') throw new Error(`connection: invalid RPC channel ${JSON.stringify(channel)}`)
          return owner.effect(() => owner.webServer.register({ kind: 'prefix', path: channel, handler }), `client-connection: ${channel} rpc channel`)
        },
        intercept(channel) {
          if (channel !== '/api') {
            world.hit('connection.rpc.intercept', owner, channel)
            throw new Error(`connection: invalid shared RPC channel ${JSON.stringify(channel)}`)
          }
          return owned(world, owner, 'connection.rpc.intercept', 'connection.interceptors', channel, 'interceptor')
        },
      }
    }
    get fetch() {
      const owner = this.ctx
      return {
        register(route) { return owned(world, owner, 'connection.fetch.register', 'connection.fetchRoutes', route?.path, 'fetch') },
      }
    }
  }

  // settings/settings/src/index.ts: 当前接口没有 register (插件把有 register 的当作旧版 provider).
  // configure 返回裸 disposer, 同一 fiber 重复 configure 抛错; update/replace/mutate 写配置文件 (持久).
  class Settings extends Service {
    constructor(ctx) { super(ctx, 'settings'); instance(ctx, 'settings') }
    get writable() { return true }
    get documentPath() { return 'cordis.patch.yml' }
    configure(presentation, owner) {
      const fiberCtx = owner?.ctx ?? this.ctx
      // 键只用 fiber 名字; 属于哪个安装记在 owner 里 (键里带安装编号会让新旧实例比不起来).
      const key = fiberCtx.fiber?.name ?? "?"
      return bare(world, this.ctx, 'settings.configure', 'settings.presentations', key, JSON.stringify(presentation))
    }
    describe() { world.hit('settings.describe', this.ctx); return [] }
    prepareDocument() { return Promise.resolve(this.documentPath) }
    async update(ns) { const who = world.hit('settings.update', this.ctx, ns); world.table('persistent:settings').set(ns, { owner: who, view: 'update' }) }
    async replace(ns) { const who = world.hit('settings.replace', this.ctx, ns); world.table('persistent:settings').set(ns, { owner: who, view: 'replace' }) }
    async mutate(ns) { const who = world.hit('settings.mutate', this.ctx, ns); world.table('persistent:settings').set(ns, { owner: who, view: 'mutate' }) }
  }

  const stubs = {
    settings: Settings,
    webServer: WebServer,
    tools: Tools,
    systemPrompt: SystemPrompt,
    credentials: Credentials,
    connection: Connection,
  }

  // 吸收型值: 任何取属性, 调用, new 都返回另一个吸收型值. 没有桩的服务的方法返回它,
  // 这样插件能继续往下跑 (返回 undefined 会让 x.register(...).get 之类的写法直接崩).
  function absorb(p) {
    return new Proxy(function () {}, {
      get(t, k) {
        if (k === Symbol.toPrimitive) return () => `[stub ${p}]`
        if (k === Symbol.iterator) return function* () {}
        if (k === Symbol.asyncIterator) return async function* () {}
        if (k === 'then' || typeof k === 'symbol') return undefined
        if (k === 'length' || k === 'size') return 0
        if (k === 'prototype') return t.prototype
        return absorb(`${p}.${String(k)}`)
      },
      apply() { return absorb(`${p}()`) },
      construct() { return absorb(`new ${p}`) },
    })
  }

  // 没有桩的服务: 任何方法调用都记为 unmodeled, 返回吸收型值.
  function generic(name) {
    return function (ctx) {
      const target = new Proxy({}, {
        get(_, prop) {
          if (typeof prop === 'symbol' || prop === 'then' || prop === 'toJSON' || prop === 'constructor') return undefined
          return (...args) => {
            world.unmodeled.push(`${name}.${String(prop)}`)
            return absorb(`${name}.${String(prop)}()`)
          }
        },
      })
      ctx.provide(name, target)
    }
  }

  // 把每个宿主服务作为一个独立的插件提供, 这样它有自己的 fiber, 可以被撤走 (withdraw).
  // universe 是这个场景里会出现的宿主服务; 桩 inject 依赖闭包与它的交集
  // (不在场景里的服务不能 inject, 否则桩永远起不来).
  function plugin(name, universe) {
    const inject = universe ? [...closure(name)].filter(n => universe.has(n)).sort() : []
    // 服务类本身就是 Cordis 插件 (构造即 provide), 与 dsh 的 ctx.plugin(WebServer) 一致.
    if (stubs[name]) {
      if (!inject.length) return stubs[name]
      const cls = class extends stubs[name] { static inject = inject }
      Object.defineProperty(cls, 'name', { value: stubs[name].name })
      return cls
    }
    return { name: `host:${name}`, inject, apply: generic(name) }
  }

  // loader: 编排接口. 插件调用它就是在发出 O-Insert/O-Dispose (编排者), 记入 trace.
  function loader(ctx) {
    const target = new Proxy({}, {
      get(_, prop) {
        if (typeof prop === 'symbol' || prop === 'then' || prop === 'toJSON' || prop === 'constructor') return undefined
        return (...args) => {
          world.trace.push({ site: `loader.${String(prop)}`, who: '?', orchestration: true })
          world.unmodeled.push(`loader.${String(prop)}`)
          return absorb(`loader.${String(prop)}()`)
        }
      },
    })
    ctx.provide('loader', target)
  }

  return { plugin, loader, modeled: Object.keys(stubs) }
}
