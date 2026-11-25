// 生成差分测试的用例: 一个固定的组件库, 加上有界枚举的编排脚本.
// 用法: node gen.mjs [最大脚本长度, 默认 3] > cases.json   (输出 { lib, cases: [{ id, script }] })
//
// 组件库里每个组件针对演算的一条规则或 Cordis 的一处已知差异 (见 README.md 的表).
// 每个用例都带着整个组件库, 所以组件编号在所有用例里一致.

export const LIB = [
  /* 0 P   */ { deps: [], provs: [0], body: [['provide', 0]] },
  /* 1 C   */ { deps: [0], provs: [], body: [['op', 0, 1, 1]] },
  /* 2 C2  */ { deps: [0], provs: [], body: [['op', 0, 2, 2], ['op', 0, 3, 3]] },
  /* 3 Cx  */ { deps: [0], provs: [], body: [['op', 0, 1, 7]] },              // 与 C 撞名
  /* 4 F   */ { deps: [0], provs: [], body: [['op', 0, 4, 4], ['fail']] },
  /* 5 Sp  */ { deps: [0], provs: [], body: [['op', 0, 5, 5], ['spawn', 6], ['op', 0, 6, 6]] },
  /* 6 Ch  */ { deps: [0], provs: [], body: [['op', 0, 7, 7]] },              // 只由 Sp 装
  /* 7 Pw  */ { deps: [], provs: [0], body: [['provide', 0], ['op', 0, 8, 8]] }, // 与 P 争 k0
  /* 8 Q   */ { deps: [0], provs: [1], body: [['op', 0, 9, 9], ['provide', 1]] },
  /* 9 R   */ { deps: [1], provs: [], body: [['op', 1, 1, 1]] },
  /* 10 PF */ { deps: [], provs: [0], body: [['provide', 0], ['fail']] },
  /* 11 C3 */ { deps: [0], provs: [], body: [['op', 0, 10, 10], ['op', 0, 11, 11], ['op', 0, 12, 12]] }, // 中途放弃 (差异 h)
]
export const NAMES = ['P', 'C', 'C2', 'Cx', 'F', 'Sp', 'Ch', 'Pw', 'Q', 'R', 'PF', 'C3']
const INSERTABLE = LIB.map((_, c) => c).filter(c => c !== 6)

// 插入冲突 (差异 c: Cordis 接受与在场 fiber 提供同一个键的组件, 演算的 O-Insert 拒绝) 是已知的分歧,
// 而 replay 在第一个分歧处停下, 它会遮住之后的一切. 所以长度不超过 CONFLICT_LEN 的脚本才允许冲突
// (作为差异 c 的见证); 更长的脚本只在先前的提供者已被 dispose 后才插入同一个键的提供者.
const CONFLICT_LEN = 2
const overlaps = (c1, c2) => LIB[c1].provs.some(k => LIB[c2].provs.includes(k))
const clashes = (c, live) => live.some(c2 => overlaps(c, c2))

// 长度为 len 的顶层脚本 (按顺序执行, 每步之后落定). live: 插入后没有被 dispose 的组件 (按插入序号)
function* scripts(len, prefix = [], inserts = [], live = []) {
  if (prefix.length === len) { yield { script: prefix, inserts, live }; return }
  for (const c of INSERTABLE) {
    if (len > CONFLICT_LEN && clashes(c, live.filter(x => x !== null))) continue
    yield* scripts(len, [...prefix, { op: 'insert', c }], [...inserts, c], [...live, c])
  }
  for (let i = 0; i < inserts.length; i++) {
    for (const op of ['dispose', 'restart', 'reset']) {
      yield* scripts(len, [...prefix, { op, i }], inserts, op === 'dispose' ? live.map((x, j) => j === i ? null : x) : live)
    }
  }
}

// 加载中途的动作: 在某个会加载的组件的第 j 条指令之前执行
function* armedFor(inserts, live, len) {
  const loaders = new Set(inserts)
  if (loaders.has(5)) loaders.add(6)
  for (const c of loaders) {
    for (let j = 0; j <= LIB[c].body.length; j++) {
      for (const c2 of INSERTABLE) {
        if (len + 1 > CONFLICT_LEN && clashes(c2, live.filter(x => x !== null))) continue
        yield { op: 'insert', c: c2, at: [c, j] }
      }
      for (let i = 0; i < inserts.length; i++) {
        for (const op of ['dispose', 'restart']) yield { op, i, at: [c, j] }
      }
    }
  }
}

export function* cases(maxLen = 3, maxArmedLen = Math.min(maxLen - 1, 3)) {
  let n = 0
  for (let len = 1; len <= maxLen; len++) {
    for (const { script, inserts, live } of scripts(len)) {
      if (!script.some(a => a.op === 'insert')) continue
      yield { id: `s${n++}`, script }
      if (len > maxArmedLen) continue
      for (const a of armedFor(inserts, live, len)) yield { id: `s${n++}`, script: [...script, a] }
    }
  }
}

export function describe(script) {
  return script.map(a => {
    const what = a.op === 'insert' ? `insert ${NAMES[a.c]}` : `${a.op} #${a.i}`
    return a.at ? `${what} @${NAMES[a.at[0]]}:${a.at[1]}` : what
  }).join(', ')
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const maxLen = Number(process.argv[2] ?? 3)
  process.stdout.write(JSON.stringify({ lib: LIB, cases: [...cases(maxLen)] }))
}
