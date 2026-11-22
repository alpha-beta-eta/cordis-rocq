"use strict";
// 用法: node test/run.js out/racket/examples.js
// 在 runtime/rt.js 上运行生成的插件, 检查 dsh2 中的生命周期性质在生成代码上成立.

const path = require("path");
const assert = require("assert");
const { Manager } = require("../runtime/rt.js");
const timer = require("../payload/timer.js");
const echo = require("../payload/echo.js");

const P = require(path.resolve(process.argv[2]));
const roots = ["tools_host", "config", "shell", "alias", "pet", "shell_plus"];

// 宿主一侧的 view: 与贡献的先后无关
function toolsView(m) {
  const C = m.contributions("tools");
  if (C === null) return null;
  const plain = new Set(C.filter((c) => c.name && !c.when).map((c) => c.name));
  const show = (c) => (c.exec ? c.exec("x") : `alias ${c.alias}`);
  const best = {};
  for (const c of C) {
    if (!c.name || (c.when && !plain.has(c.when))) continue;
    const b = best[c.name];
    if (!b || c.prio > b.prio || (c.prio === b.prio && show(c) < show(b))) best[c.name] = c;
  }
  return {
    tools: Object.keys(best).sort().map((n) => `${n} -> ${show(best[n])}`),
    restrict: C.filter((c) => c.restrict).map((c) => `${c.restrict} deny ${c.deny}`).sort(),
  };
}

function assemble(names, { seed = null } = {}) {
  const m = new Manager();
  const ids = {};
  for (const n of names) ids[n] = m.install(P[n]);
  m.settle({ seed });
  return { m, ids };
}

let checks = 0;
function check(name, f) { f(); checks++; console.log(`ok - ${name}`); }

// 1. 静态组装
const { m: m0, ids: ids0 } = assemble(roots);
const S0 = m0.snapshot();
check("加载期间没有运行载荷代码", () => assert.strictEqual(echo.made, 0));
check("静态组装: view 符合预期", () => {
  assert.deepStrictEqual(toolsView(m0), {
    tools: ["cat -> cat x", "dir -> alias ls", "ls -> ls --color x", "pet -> pet x", "pet-help -> pet-help x"],
    restrict: [],
  });
  assert.strictEqual(timer.live(), 1);
});

// 2. 合流: 随机的安装顺序, 安装之间随机走若干步, 随机调度
check("合流: 200 个随机调度到达同一终态", () => {
  const made = echo.made;
  for (let seed = 1; seed <= 200; seed++) {
    let s = seed;
    const rnd = () => ((s = (s * 1103515245 + 12345) % 2147483648) / 2147483648);
    const order = [...roots].sort(() => rnd() - 0.5);
    const m = new Manager();
    for (const n of order) {
      m.install(P[n]);
      const k = Math.floor(rnd() * 6);
      for (let i = 0; i < k; i++) {
        const ids = [...m.fibers.keys()];
        if (ids.length) m.step(ids[Math.floor(rnd() * ids.length)]);
      }
    }
    m.settle({ seed });
    assert.strictEqual(m.snapshot(), S0, `seed ${seed}`);
    for (const id of [...m.fibers.keys()]) if (m.fibers.get(id).parent === null) m.dispose(id);
    m.settle({ seed });
  }
  assert.strictEqual(timer.live(), 1); // 只剩 m0 中的那一个
  assert.strictEqual(echo.made, made); // 200 次装卸都没有运行载荷
});

// 3. 恢复精确性: 卸载 pet 等于从来没有装过 pet
check("恢复: 卸载 pet 后与不装 pet 的终态相同, 资源已释放", () => {
  const { m, ids } = assemble(roots);
  assert.strictEqual(timer.live(), 2);
  m.dispose(ids.pet);
  m.settle({ seed: 7 });
  const { m: m2 } = assemble(roots.filter((n) => n !== "pet"));
  assert.strictEqual(m.snapshot(), m2.snapshot());
  assert.strictEqual(timer.live(), 1);
  m.dispose(ids.shell); m.dispose(ids.shell_plus);
  m.settle({ seed: 8 });
  assert.deepStrictEqual(toolsView(m).tools, []); // dir 的条件不再满足
});

// 4. 可选依赖: config 出现与消失时 pet 重新加载
check("可选依赖: config 出现/消失时 pet 重新加载", () => {
  const { m } = assemble(["tools_host", "pet"]);
  assert.deepStrictEqual(toolsView(m).tools, ["pet-help -> pet-help x"]);
  const c = m.install(P.config);
  m.settle({ seed: 3 });
  assert.deepStrictEqual(toolsView(m).tools, ["pet -> pet x", "pet-help -> pet-help x"]);
  m.dispose(c);
  m.settle({ seed: 4 });
  assert.deepStrictEqual(toolsView(m).tools, ["pet-help -> pet-help x"]);
  assert.strictEqual(timer.live(), 2); // m0 一个, 这里一个 (释放后重新获取)
  for (const id of [...m.fibers.keys()]) m.dispose(id);
  m.settle();
  assert.strictEqual(timer.live(), 1);
});

// 5. 运行期反应: 子 fiber 承载, 随 pet 一起撤销
check("反应: agent/created 的效应随 pet 卸载而撤销", () => {
  const { m, ids } = assemble(roots);
  m.emit("agent/created", { agent: "a1" });
  m.emit("agent/created", { agent: "a2" });
  m.settle({ seed: 5 });
  assert.deepStrictEqual(toolsView(m).restrict, ["a1 deny rm", "a2 deny rm"]);
  m.dispose(ids.pet);
  m.settle({ seed: 6 });
  assert.deepStrictEqual(toolsView(m).restrict, []);
  assert.ok(![...m.fibers.values()].some((f) => f.plugin.name.startsWith("pet")));
  for (const id of [...m.fibers.keys()]) m.dispose(id);
  m.settle();
});

// 6. 撤走提供者: 依赖者先卸载, 提供最后撤掉
check("撤走 tools-host: 依赖者级联卸载, 绑定消失, 资源释放", () => {
  const { m, ids } = assemble(roots);
  m.dispose(ids.tools_host);
  m.settle({ seed: 9 });
  assert.strictEqual(m.contributions("tools"), null);
  assert.strictEqual(timer.live(), 1);
  const phases = [...m.fibers.values()].filter((f) => f.parent === null)
    .map((f) => `${f.plugin.name}:${f.phase}`).sort();
  assert.deepStrictEqual(phases, ["alias:inactive", "config:active", "pet:inactive",
                                  "shell-plus:inactive", "shell:inactive"]);
});

// 7. 宿主缓存的闭包在卸载后作废
check("卸载后宿主缓存的 exec 调用即抛错, 重新加载得到新的闭包", () => {
  const { m, ids } = assemble(roots);
  const petExec = () => m.contributions("tools").find((c) => c.name === "pet").exec;
  const cached = petExec();
  assert.strictEqual(cached("x"), "pet x");
  m.dispose(ids.config); // pet 因可选依赖消失而重新加载
  m.settle({ seed: 10 });
  assert.throws(() => cached("x"), /revoked: pet put tools/);
  m.install(P.config);
  m.settle({ seed: 11 });
  assert.strictEqual(petExec()("y"), "pet y");
  assert.throws(() => cached("x"), /revoked/); // 旧闭包不会复活
  for (const id of [...m.fibers.keys()]) m.dispose(id);
  m.settle();
});

// 收尾
for (const id of Object.values(ids0)) m0.dispose(id);
m0.settle();
check("全部卸载后没有泄漏的资源", () => assert.strictEqual(timer.live(), 0));
console.log(`${checks} checks passed`);
