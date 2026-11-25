// 进程级探针: 插件越出 Cordis 的那部分效应 (第 0 层 S3, 第 2 层 R4) 落在这里.
//
// 快照比较的是: 指定原型上的属性身份, globalThis 的键, dns 默认解析序, process 上的监听器数,
// 活跃句柄的种类计数, 环境变量. 网络一律禁用: 插件发起的连接被拒并记入 world.trace.

import dns from 'node:dns'
import http from 'node:http'
import https from 'node:https'
import net from 'node:net'
import tls from 'node:tls'
import events from 'node:events'
import stream from 'node:stream'
import child_process from 'node:child_process'
import fs from 'node:fs'
import path from 'node:path'
import { syncBuiltinESMExports } from 'node:module'

const PROTOS = {
  'Object.prototype': Object.prototype,
  'Function.prototype': Function.prototype,
  'Array.prototype': Array.prototype,
  'Promise.prototype': Promise.prototype,
  'EventEmitter.prototype': events.EventEmitter.prototype,
  'ChildProcess.prototype': child_process.ChildProcess.prototype,
  'http.Server.prototype': http.Server.prototype,
  'http.IncomingMessage.prototype': http.IncomingMessage.prototype,
  'http.ServerResponse.prototype': http.ServerResponse.prototype,
  'net.Socket.prototype': net.Socket.prototype,
  'stream.Readable.prototype': stream.Readable.prototype,
}
const MODULES = { child_process, http, https, net, dns, fs }
const PROCESS_EVENTS = ['exit', 'beforeExit', 'uncaughtException', 'unhandledRejection', 'warning', 'SIGINT', 'SIGTERM']

const ids = new WeakMap()
let nextId = 0
function idOf(v) {
  if ((typeof v !== 'object' && typeof v !== 'function') || v === null) return JSON.stringify(v)
  if (!ids.has(v)) ids.set(v, `#${++nextId}`)
  return ids.get(v)
}

function descriptorIds(obj) {
  const out = {}
  for (const key of Reflect.ownKeys(obj)) {
    const d = Object.getOwnPropertyDescriptor(obj, key)
    out[String(key)] = d.get || d.set ? `${idOf(d.get)}/${idOf(d.set)}` : idOf(d.value)
  }
  return out
}

export function blockNetwork(world) {
  const deny = (what) => function () {
    world.trace.push({ site: `net.${what}`, who: '?', blocked: true })
    throw new Error(`checker: network disabled (${what})`)
  }
  globalThis.fetch = async () => {
    world.trace.push({ site: 'net.fetch', who: '?', blocked: true })
    throw new TypeError('checker: network disabled (fetch)')
  }
  for (const m of [http, https]) { m.request = deny('request'); m.get = deny('get') }
  net.connect = net.createConnection = deny('connect')
  tls.connect = deny('tls.connect')
  // 子进程也一律不执行: 插件可能去找并启动本机的 codex, claude 之类的程序.
  // 异步的 spawn/exec/execFile/fork 返回一个立即以 ENOENT 失败的 ChildProcess, 同步的直接抛错.
  for (const what of ['spawn', 'exec', 'execFile', 'fork']) {
    child_process[what] = function (cmd) {
      world.trace.push({ site: `proc.${what}`, who: '?', blocked: true, detail: String(cmd).slice(0, 120) })
      const cp = new child_process.ChildProcess()
      // 构造函数会建一个未初始化的 Process 句柄 (pid 0); 不置空的话 cp.kill() 就是 kill(0, sig), 杀掉整个进程组.
      cp._handle = null
      const err = Object.assign(new Error(`checker: subprocess disabled (${what} ${cmd})`), { code: 'ENOENT' })
      process.nextTick(() => { cp.emit('error', err); cp.emit('close', -2) })
      const cb = [...arguments].find(a => typeof a === 'function')
      if (cb) process.nextTick(() => cb(err, '', ''))
      return cp
    }
  }
  for (const what of ['spawnSync', 'execSync', 'execFileSync']) {
    child_process[what] = function (cmd) {
      world.trace.push({ site: `proc.${what}`, who: '?', blocked: true, detail: String(cmd).slice(0, 120) })
      throw Object.assign(new Error(`checker: subprocess disabled (${what} ${cmd})`), { code: 'ENOENT' })
    }
  }
  // 不许插件发信号或退出进程: 子进程是伪造的, 没有 pid, process.kill(-pid) 之类会落到整个进程组上.
  process.kill = function (pid, signal) {
    world.trace.push({ site: 'proc.kill', who: '?', blocked: true, detail: `${pid} ${signal ?? ''}` })
    if (pid === process.pid && signal === 0) return true
    throw Object.assign(new Error('checker: process.kill disabled'), { code: 'ESRCH' })
  }
  process.exit = function (code) {
    world.trace.push({ site: 'proc.exit', who: '?', blocked: true, detail: String(code) })
    throw new Error('checker: process.exit disabled')
  }
  // 插件以 ESM 具名导入内置模块 (import { exec } from 'node:child_process') 时, 改模块对象
  // 不会自动同步到具名绑定.
  syncBuiltinESMExports()
}

// 长命的句柄才算插件留下的资源; FSReqPromise, MessagePort 之类随时序抖动, 不比.
const LASTING = new Set(['Timeout', 'TCPServerWrap', 'TCPSocketWrap', 'TCPWrap', 'ProcessWrap', 'FSEventWrap',
  'StatWatcher', 'UDPWrap', 'PipeServerWrap', 'SignalWrap', 'Immediate'])

// 进程快照. 原型与模块对象记属性身份; 其余记值或计数.
export function processSnapshot() {
  const protos = {}
  for (const [name, p] of Object.entries(PROTOS)) protos[name] = descriptorIds(p)
  for (const [name, m] of Object.entries(MODULES)) protos[`module:${name}`] = descriptorIds(m)
  const handles = {}
  for (const r of process.getActiveResourcesInfo()) if (LASTING.has(r)) handles[r] = (handles[r] ?? 0) + 1
  const listeners = {}
  for (const e of PROCESS_EVENTS) listeners[e] = process.listenerCount(e)
  return {
    protos,
    globals: Reflect.ownKeys(globalThis).map(String).sort(),
    dnsOrder: dns.getDefaultResultOrder?.(),
    listeners,
    handles,
    env: Object.keys(process.env).sort().map(k => `${k}=${String(process.env[k]).split(process.env.HOME).join('$HOME')}`),
  }
}

// 两份进程快照的差异, 逐项列出.
export function processDiff(a, b) {
  const out = []
  for (const name of Object.keys(a.protos)) {
    const x = a.protos[name], y = b.protos[name]
    for (const k of new Set([...Object.keys(x), ...Object.keys(y)])) {
      if (x[k] !== y[k]) out.push({ kind: 'proto', where: `${name}.${k}`, from: x[k] ?? '(absent)', to: y[k] ?? '(absent)' })
    }
  }
  const ga = new Set(a.globals), gb = new Set(b.globals)
  for (const k of gb) if (!ga.has(k)) out.push({ kind: 'global', where: `globalThis.${k}`, from: '(absent)', to: 'set' })
  for (const k of ga) if (!gb.has(k)) out.push({ kind: 'global', where: `globalThis.${k}`, from: 'set', to: '(absent)' })
  if (a.dnsOrder !== b.dnsOrder) out.push({ kind: 'dns', where: 'dns.defaultResultOrder', from: a.dnsOrder, to: b.dnsOrder })
  for (const e of Object.keys(a.listeners)) {
    if (a.listeners[e] !== b.listeners[e]) out.push({ kind: 'listener', where: `process.on(${e})`, from: a.listeners[e], to: b.listeners[e] })
  }
  for (const h of new Set([...Object.keys(a.handles), ...Object.keys(b.handles)])) {
    if ((a.handles[h] ?? 0) !== (b.handles[h] ?? 0)) out.push({ kind: 'handle', where: h, from: a.handles[h] ?? 0, to: b.handles[h] ?? 0 })
  }
  const ea = new Set(a.env), eb = new Set(b.env)
  for (const k of eb) if (!ea.has(k)) out.push({ kind: 'env', where: k.split('=')[0], from: '?', to: k })
  return out
}

// 临时 HOME 下的文件列表 (持久状态, R4).
export function fsSnapshot(root) {
  const out = []
  const walk = (dir) => {
    let entries
    try { entries = fs.readdirSync(dir, { withFileTypes: true }) } catch { return }
    for (const e of entries) {
      const p = path.join(dir, e.name)
      if (e.isDirectory()) walk(p); else out.push(path.relative(root, p))
    }
  }
  walk(root)
  return out.sort()
}

// 相对本进程基线的改动, 规范化成可以跨进程比较的形式 (对象编号只在进程内有意义).
export function processDelta(baseline, now) {
  return processDiff(baseline, now).map(d =>
    d.kind === 'proto' || d.kind === 'global' ? `${d.kind} ${d.where} ${d.to === '(absent)' ? 'deleted' : d.from === '(absent)' ? 'added' : 'replaced'}`
    : d.kind === 'env' ? `env ${d.to}`
    : `${d.kind} ${d.where} = ${d.to}`).sort()
}
