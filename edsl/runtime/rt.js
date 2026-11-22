"use strict";
// rt.js — 演算语义的 JS 运行时(垫片)。生成的插件只调用这里的指令构造子 I.*。
//
// 与 Cordis 的差别正是 docs/EDSL.md 第 2 节的表:
//   - 撤销栈按 LIFO 串行执行(不是 Promise.all);
//   - Put 按令牌撤回(不是按回调身份);
//   - 插件体是生成器,每个 yield 是一个原子操作,两次 yield 之间都可以放弃加载;
//   - 只能访问声明过的键。
//
// 服务只有贡献模型一种形状(docs/OPLIB.md):冻结部分 F + 贡献多重集 C。
// 运行时扩展了两样演算里还没有的东西(EDSL.md 6.2):可选依赖、资源。
// 与外部世界的边界(EDSL.md 5.2):载荷闭包惰性构造(I.lazy),贡献出去的闭包随撤销作废(seal)。

const path = require("path");

// ---------------------------------------------------------------- 指令
const I = {
  read: (key) => ({ op: "read", key }),
  readOpt: (key) => ({ op: "readOpt", key }),
  put: (key, value) => ({ op: "put", key, value }),
  provide: (key, value) => ({ op: "provide", key, value }),
  spawn: (plugin) => ({ op: "spawn", plugin }),
  on: (event, handler) => ({ op: "on", event, handler }),
  resource: (mod, args) => ({ op: "resource", mod, args }),
  fail: (why) => ({ op: "fail", why }),
  // 载荷闭包:加载时不运行任何载荷代码(连 require 也不做),宿主第一次调用时才构造。
  // 所以加载过程中载荷的效应为零,外部世界影响不了控制流;对它做条件判断只能得到常量
  // (函数恒为真,=== 恒为假)。
  lazy: (p, args) => {
    let f = null;
    return (...a) => (f ??= payload(p)(...args))(...a);
  },
};

// 载荷:相对 edsl/ 目录解析。载荷只拿到参数,拿不到运行时。
const root = path.resolve(__dirname, "..");
const payload = (p) => require(path.resolve(root, p));

// ---------------------------------------------------------------- 工具
function freeze(x) {
  if (x && typeof x === "object" && !Object.isFrozen(x)) {
    Object.freeze(x);
    for (const v of Object.values(x)) freeze(v);
  }
  return x;
}
// 把值里的函数换成可撤销的包装。撤销对应的 put/provide 时作废,之后再调用就抛错,
// 所以宿主缓存的闭包在插件卸载后也调不到。已经包过的函数再包一层:任一层作废即作废。
function seal(x, cell) {
  if (typeof x === "function") {
    const f = x;
    return function (...a) {
      if (cell.revoked) throw new Error(`revoked: ${cell.who}`);
      return f.apply(this, a);
    };
  }
  if (x && typeof x === "object") {
    const y = Array.isArray(x) ? [] : {};
    for (const [k, v] of Object.entries(x)) y[k] = seal(v, cell);
    return freeze(y);
  }
  return x;
}
const sameView =(a, b) => {
  if (a === null || b === null) return a === b;
  const ka = Object.keys(a), kb = Object.keys(b);
  return ka.length === kb.length && ka.every((k) => a[k] === b[k]);
};
function mulberry32(seed) {
  return function () {
    seed |= 0; seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// ---------------------------------------------------------------- 管理器
class Manager {
  constructor() {
    this.next = 0;
    this.fibers = new Map();   // id -> fiber
    this.bindings = new Map(); // key -> { pid, owner, F, C: [{token, value}] }
    this.log = [];
  }
  fresh() { return this.next++; }

  // O-Insert
  install(plugin, parent = null) {
    for (const f of this.fibers.values())
      for (const k of plugin.provide)
        if (f.plugin.provide.includes(k))
          throw new Error(`${plugin.name} 与 ${f.plugin.name} 都提供 ${k}`);
    return this._add(plugin, parent);
  }
  _add(plugin, parent) {
    const id = this.fresh();
    this.fibers.set(id, {
      id, plugin, parent, phase: "inactive", gen: null, last: undefined,
      acc: [], view: null, error: null, disposed: false,
    });
    return id;
  }
  dispose(id) { const f = this.fibers.get(id); if (f) f.disposed = true; }
  reset(id) { const f = this.fibers.get(id); if (f && f.phase === "inactive") f.error = null; }

  // O-React:对每个 Active 且挂了 event 处理器的 fiber,插入一个反应子 fiber
  emit(event, arg) {
    for (const f of [...this.fibers.values()]) {
      if (f.phase !== "active" || f.disposed) continue;
      for (const u of [...f.acc]) {
        if (u.kind !== "on" || u.event !== event) continue;
        const p = f.plugin;
        const child = {
          name: `${p.name}/on:${event}`, inject: p.inject, optional: p.optional,
          provide: [], body: () => u.handler(freeze(arg)),
        };
        const m = this._add(child, f.id);
        f.acc.unshift({ kind: "spawn", child: m });
      }
    }
  }

  visible(key) {
    const b = this.bindings.get(key);
    if (!b) return null;
    const o = this.fibers.get(b.owner);
    return o && o.phase === "active" ? b.pid : null;
  }
  target(f) {
    if (f.disposed) return null;
    const w = {};
    for (const k of f.plugin.inject) {
      const p = this.visible(k);
      if (p === null) return null;
      w[k] = p;
    }
    for (const k of f.plugin.optional) w["?" + k] = this.visible(k); // 可能为 null
    return w;
  }
  installed(f) { return f.phase !== "inactive"; }
  resolvedBy(pid, except) {
    for (const f of this.fibers.values())
      if (f.id !== except && this.installed(f) && f.view &&
          Object.values(f.view).includes(pid)) return true;
    return false;
  }
  hasChildren(id) {
    for (const f of this.fibers.values()) if (f.parent === id) return true;
    return false;
  }

  // 单步;返回描述,不可走时返回 null
  step(id) {
    const f = this.fibers.get(id);
    const t = this.target(f);
    switch (f.phase) {
      case "inactive":
        if (f.disposed && !this.hasChildren(id)) { this.fibers.delete(id); return "remove"; }
        if (!f.disposed && f.error === null && t !== null) {
          f.phase = "loading"; f.view = t; f.acc = []; f.last = undefined;
          f.gen = f.plugin.body();
          return "begin";
        }
        return null;
      case "loading":
        if (!sameView(t, f.view)) { this._abandon(f); f.phase = "unloading"; return "divert"; }
        return this._run(f);
      case "active":
        if (!sameView(t, f.view)) { f.phase = "unloading"; return "leave"; }
        return null;
      case "unloading":
        return this._undo(f);
    }
  }
  _abandon(f) { if (f.gen) { try { f.gen.return(); } catch (_) {} f.gen = null; } }
  _fail(f, why) { this._abandon(f); f.error = why; f.phase = "unloading"; return `fail: ${why}`; }

  _resolve(f, key) {
    // 依赖查视图;自己提供的键查绑定(owner 必须是自己)
    const b = this.bindings.get(key);
    if (f.plugin.inject.includes(key) || f.plugin.optional.includes(key)) {
      const want = f.view[key] ?? f.view["?" + key];
      return b && want !== null && want !== undefined && b.pid === want ? b : null;
    }
    if (f.plugin.provide.includes(key)) return b && b.owner === f.id ? b : null;
    return undefined; // 未声明
  }

  _run(f) {
    let r;
    try { r = f.gen.next(f.last); } catch (e) { return this._fail(f, `exception: ${e.message}`); }
    if (r.done) { f.gen = null; f.phase = "active"; return "active"; }
    const ins = r.value;
    switch (ins.op) {
      case "read": case "readOpt": {
        const b = this._resolve(f, ins.key);
        if (b === undefined) return this._fail(f, `undeclared key ${ins.key}`);
        if (b === null) {
          if (ins.op === "readOpt") { f.last = null; return `readOpt ${ins.key} = null`; }
          return this._fail(f, `cannot resolve ${ins.key}`);
        }
        f.last = b.F; // 恒等逆,不入栈
        return `read ${ins.key}`;
      }
      case "put": {
        const b = this._resolve(f, ins.key);
        if (!b) return this._fail(f, `cannot resolve ${ins.key}`);
        const token = this.fresh();
        const cell = { revoked: false, who: `${f.plugin.name} put ${ins.key}#${token}` };
        b.C.push({ token, value: seal(ins.value, cell) });
        f.acc.unshift({ kind: "put", key: ins.key, pid: b.pid, token, cell });
        f.last = undefined;
        return `put ${ins.key}#${token}`;
      }
      case "provide": {
        if (!f.plugin.provide.includes(ins.key) || this.bindings.has(ins.key))
          return this._fail(f, `EConflict ${ins.key}`);
        const pid = this.fresh();
        const cell = { revoked: false, who: `${f.plugin.name} provide ${ins.key}@${pid}` };
        this.bindings.set(ins.key, { pid, owner: f.id, F: seal(ins.value, cell), C: [] });
        f.acc.unshift({ kind: "provide", key: ins.key, pid, cell });
        f.last = undefined;
        return `provide ${ins.key}@${pid}`;
      }
      case "spawn": {
        for (const g of this.fibers.values())
          for (const k of ins.plugin.provide)
            if (g.plugin.provide.includes(k)) return this._fail(f, `EConflict spawn ${k}`);
        const m = this._add(ins.plugin, f.id);
        f.acc.unshift({ kind: "spawn", child: m });
        f.last = undefined;
        return `spawn ${ins.plugin.name}#${m}`;
      }
      case "on": {
        f.acc.unshift({ kind: "on", event: ins.event, handler: ins.handler });
        f.last = undefined;
        return `on ${ins.event}`;
      }
      case "resource": {
        let h;
        try { h = ins.mod.acquire(...ins.args); } catch (e) { return this._fail(f, `acquire: ${e.message}`); }
        f.acc.unshift({ kind: "resource", mod: ins.mod, handle: h });
        f.last = undefined;
        return "resource";
      }
      case "fail":
        return this._fail(f, ins.why);
      default:
        return this._fail(f, `bad instruction ${ins.op}`);
    }
  }

  _undo(f) {
    if (f.acc.length === 0) { f.phase = "inactive"; f.view = null; return "unloaded"; }
    const u = f.acc[0];
    switch (u.kind) {
      case "put": {
        const b = this.bindings.get(u.key);
        if (b && b.pid === u.pid) b.C = b.C.filter((c) => c.token !== u.token);
        u.cell.revoked = true;
        break;
      }
      case "provide":
        if (this.resolvedBy(u.pid, f.id)) return null; // 守卫:等依赖者卸载
        this.bindings.delete(u.key);
        u.cell.revoked = true;
        break;
      case "spawn": {
        const c = this.fibers.get(u.child);
        if (c) {
          if (!c.disposed) { c.disposed = true; return `retire #${u.child}`; }
          return null; // 等子 fiber 被移除
        }
        break;
      }
      case "on": break;
      case "resource":
        try { u.mod.release(u.handle); } catch (_) {}
        break;
    }
    f.acc.shift();
    return `undo ${u.kind}`;
  }

  // 调度:random 为 null 时按编号顺序;否则用给定种子随机挑可走的 fiber
  settle({ seed = null, limit = 20000 } = {}) {
    const rnd = seed === null ? null : mulberry32(seed);
    for (let n = 0; n < limit; n++) {
      const ids = [...this.fibers.keys()].sort((a, b) => a - b);
      if (rnd) {
        for (let i = ids.length - 1; i > 0; i--) {
          const j = Math.floor(rnd() * (i + 1)); [ids[i], ids[j]] = [ids[j], ids[i]];
        }
      }
      let moved = false;
      for (const id of ids) {
        const msg = this.step(id);
        if (msg) { this.log.push(`#${id} ${msg}`); moved = true; break; }
      }
      if (!moved) return n;
    }
    throw new Error("settle: no quiescence");
  }

  // 观察:每个键的 F 与贡献多重集(去掉令牌,排序),以及失败的 fiber
  contributions(key) {
    const b = this.bindings.get(key);
    return b ? b.C.map((c) => c.value) : null;
  }
  snapshot() {
    const ser = (v) => JSON.stringify(v, (_, x) => (typeof x === "function" ? "<fn>" : x));
    const keys = [...this.bindings.keys()].sort();
    const out = {};
    for (const k of keys) {
      const b = this.bindings.get(k);
      out[k] = { F: ser(b.F), C: b.C.map((c) => ser(c.value)).sort() };
    }
    const fibers = [...this.fibers.values()]
      .map((f) => `${f.plugin.name}:${f.phase}${f.error ? "!" : ""}`).sort();
    return JSON.stringify({ bindings: out, fibers });
  }
}

module.exports = { I, payload, Manager, freeze };
