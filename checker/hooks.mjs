// Node 模块钩子. 插件在真实宿主里能 import 到宿主自己的包, 这里照样给它们:
// 1. dsh vendored 的包 (cordis, cosmokit, schemastery) 映射到 .vendor/ 下的 TS 源码;
// 2. 其余 @deepseek-ai/* 映射到 DSH_ROOT/packages 下同名包的 src/ (只读引用, 不复制);
// 3. 仍然找不到的裸包名 (dsh 源码依赖的第三方包没装) 换成"吸收型"桩模块:
//    导出的名字照 import 语句生成, 任何取属性, 调用, new 都返回另一个桩. 用到的桩记在
//    process[Symbol.for('cordis-check.stubs')] 里, 报告会列出来.
// 4. .ts 用 .tools/typescript 转译 (发行版 Node 不带类型剥离), 结果缓存在 .cache/ts/.
// 这些只管 import. require 走 CJS 自己的加载器, 由 require-hooks.mjs 另行接管, 共用这里的映射与转译.
import { pathToFileURL, fileURLToPath } from 'node:url'
import { createRequire } from 'node:module'
import { readFileSync, existsSync, readdirSync, statSync, mkdirSync, writeFileSync, renameSync } from 'node:fs'
import { createHash } from 'node:crypto'
import { readFile } from 'node:fs/promises'
import path from 'node:path'

const here = path.dirname(fileURLToPath(import.meta.url))

// 转译缓存. 每条序列一个新进程, 不缓存的话每个进程都要加载 TS 编译器 (约 0.3 s) 再转译一遍
// (cordis 等 17 个文件约 0.3 s). 键是 源文件路径, 修改时间, 大小, 编译器路径与选项 的哈希;
// 未命中时才加载编译器. 并发的进程可能同时写同一项, 先写临时文件再 rename, 内容相同, 谁赢都行.
const TS_PATH = path.join(here, '.tools/typescript/lib/typescript.js')
const CACHE = path.join(here, '.cache/ts')
const OPTIONS = {
  module: 'ESNext', target: 'ES2022', useDefineForClassFields: true,
  verbatimModuleSyntax: false, isolatedModules: true, inlineSourceMap: true,
}
const OPTIONS_KEY = JSON.stringify(OPTIONS) + statSync(TS_PATH).mtimeMs
let ts
function cacheKey(file) {
  const st = statSync(file)
  return path.join(CACHE, `${createHash('sha1').update(`${file}\0${st.mtimeMs}\0${st.size}\0${OPTIONS_KEY}`).digest('hex')}.js`)
}
function compile(file, text, cached) {
  ts ??= createRequire(import.meta.url)(TS_PATH)
  const { outputText } = ts.transpileModule(text, {
    fileName: file,
    compilerOptions: { ...OPTIONS, module: ts.ModuleKind.ESNext, target: ts.ScriptTarget.ES2022 },
  })
  try {
    mkdirSync(CACHE, { recursive: true })
    const tmp = `${cached}.${process.pid}.${Math.random().toString(36).slice(2)}`
    writeFileSync(tmp, outputText)
    renameSync(tmp, cached)
  } catch {}
  return outputText
}
async function transpile(file) {
  const cached = cacheKey(file)
  try { return await readFile(cached, 'utf8') } catch {}
  return compile(file, await readFile(file, 'utf8'), cached)
}
// require 钩子 (require-hooks.mjs) 是同步的, 用这个版本. 两者共用缓存, 输出相同.
export function transpileSync(file) {
  const cached = cacheKey(file)
  try { return readFileSync(cached, 'utf8') } catch {}
  return compile(file, readFileSync(file, 'utf8'), cached)
}

export const DSH_ROOT = process.env.DSH_ROOT ?? '/mnt/d/deepseek-harness'
export const vendored = {
  '@deepseek-ai/cordis': path.join(here, '.vendor/cordis/index.ts'),
  'cordis': path.join(here, '.vendor/cordis/index.ts'),
  '@deepseek-ai/cosmokit': path.join(here, '.vendor/cosmokit/index.ts'),
  '@deepseek-ai/schemastery': path.join(here, '.vendor/schemastery/index.ts'),
}
// CORDIS_ENTRY 换用另一份 Cordis 源码 (如上游的 packages/core/src/index.ts, difftest 用);
// 它 import 的裸包 cosmokit 映射到 vendored 的 cosmokit.
if (process.env.CORDIS_ENTRY) {
  vendored['@deepseek-ai/cordis'] = vendored.cordis = path.resolve(process.env.CORDIS_ENTRY)
  vendored.cosmokit = vendored['@deepseek-ai/cosmokit']
}

// dsh 包名 -> 目录 的索引. 经 /mnt/d 遍历 packages/ (约 1300 个目录) 要 4 s, 所以缓存到磁盘,
// 键是 dsh 仓库的 HEAD 提交. 工作区里未提交的新包不会进缓存; 删掉 .cache/ 即可重建.
function dshHead() {
  try {
    const head = readFileSync(path.join(DSH_ROOT, '.git/HEAD'), 'utf8').trim()
    if (!head.startsWith('ref: ')) return head
    const ref = head.slice(5)
    try { return readFileSync(path.join(DSH_ROOT, '.git', ref), 'utf8').trim() } catch {}
    const packed = readFileSync(path.join(DSH_ROOT, '.git/packed-refs'), 'utf8')
    return packed.split('\n').find(l => l.endsWith(` ${ref}`))?.split(' ')[0]
  } catch {}
}

let index
function dshPackages() {
  if (index) return index
  const head = dshHead()
  const cacheFile = head && path.join(here, '.cache', `dsh-index-${createHash('sha1').update(`${DSH_ROOT}\0${head}`).digest('hex')}.json`)
  if (cacheFile) {
    try { return index = new Map(JSON.parse(readFileSync(cacheFile, 'utf8'))) } catch {}
  }
  index = new Map()
  try { buildIndex() } finally {
    if (cacheFile) {
      try {
        mkdirSync(path.dirname(cacheFile), { recursive: true })
        const tmp = `${cacheFile}.${process.pid}`
        writeFileSync(tmp, JSON.stringify([...index]))
        renameSync(tmp, cacheFile)
      } catch {}
    }
  }
  return index
}

function buildIndex() {
  const walk = (dir, depth) => {
    if (depth > 4) return
    let entries
    try { entries = readdirSync(dir, { withFileTypes: true }) } catch { return }
    if (entries.some(e => e.name === 'package.json')) {
      try {
        const pkg = JSON.parse(readFileSync(path.join(dir, 'package.json'), 'utf8'))
        if (pkg.name?.startsWith('@deepseek-ai/')) index.set(pkg.name, { dir, pkg })
      } catch {}
    }
    for (const e of entries) {
      if (e.isDirectory() && e.name !== 'node_modules' && !e.name.startsWith('.') && e.name !== 'tests') walk(path.join(dir, e.name), depth + 1)
    }
  }
  walk(path.join(DSH_ROOT, 'packages'), 0)
}

export function dshEntry(specifier) {
  const m = specifier.match(/^(@deepseek-ai\/[^/]+)(\/.*)?$/)
  if (!m) return
  const found = dshPackages().get(m[1])
  if (!found) return
  const sub = m[2] ? '.' + m[2] : '.'
  const exp = found.pkg.exports?.[sub]
  let target = typeof exp === 'string' ? exp : exp?.source ?? exp?.import ?? exp?.default
  const candidates = []
  if (target) candidates.push(target.replace(/^\.\/lib\//, './src/').replace(/\.js$/, '.ts'), target)
  candidates.push(sub === '.' ? './src/index.ts' : `./src/${m[2].slice(1)}.ts`)
  for (const c of candidates) {
    const p = path.join(found.dir, c)
    if (existsSync(p) && statSync(p).isFile()) return p
  }
}

function importedNames(parentURL, specifier) {
  const names = new Set()
  let hasDefault = false
  try {
    const src = readFileSync(fileURLToPath(parentURL), 'utf8')
    const esc = specifier.replace(/[.*+?^${}()|[\]\\/]/g, '\\$&')
    // 压缩过的包写成 import{a as b}from"x", 中间可以没有空白.
    const re = new RegExp(`import\\s*(type\\s+)?([^'";()]*?)\\s*from\\s*['"]${esc}['"]`, 'g')
    for (const m of src.matchAll(re)) {
      if (m[1]) continue
      const clause = m[2]
      const braces = clause.match(/\{([^}]*)\}/)
      if (braces) for (const part of braces[1].split(',')) {
        const p = part.trim().replace(/^type\s+/, '')
        if (!p || part.trim().startsWith('type ')) continue
        names.add(p.split(/\s+as\s+/)[0].trim())
      }
      const head = clause.replace(/\{[^}]*\}/, '').replace(/\*\s+as\s+\w+/, '').replace(/,/g, ' ').trim()
      if (head) hasDefault = true
    }
    const re2 = new RegExp(`export\\s*\\{([^}]*)\\}\\s*from\\s*['"]${esc}['"]`, 'g')
    for (const m of src.matchAll(re2)) for (const part of m[1].split(',')) {
      const p = part.trim(); if (p) names.add(p.split(/\s+as\s+/)[0].trim())
    }
  } catch {}
  return { names: [...names].filter(n => /^[A-Za-z_$][\w$]*$/.test(n) && n !== 'default'), hasDefault }
}

// 吸收型桩的公共部分: 记下用到的桩 (label 为 null 时不记, 由调用方自己记), 定义 make.
// ESM 桩与 require 桩 (require-hooks.mjs) 共用.
export const stubPrelude = (label) => `
const tag = Symbol.for('cordis-check.stubs')
;${label == null ? '' : `(process[tag] ??= []).push(${JSON.stringify(label)})`}
const make = (p) => new Proxy(function () {}, {
  get(t, k) {
    if (k === Symbol.toPrimitive) return () => '[stub ' + p + ']'
    if (k === Symbol.iterator) return function* () {}
    if (k === Symbol.asyncIterator) return async function* () {}
    if (k === 'then' || k === '__esModule' || typeof k === 'symbol') return undefined
    if (k === 'length' || k === 'size') return 0
    if (k === 'prototype') return t.prototype
    return make(p + '.' + String(k))
  },
  apply() { return make(p + '()') },
  construct() { return make('new ' + p) },
})
`

export async function resolve(specifier, context, next) {
  if (specifier in vendored) return { url: pathToFileURL(vendored[specifier]).href, shortCircuit: true }
  const dsh = dshEntry(specifier)
  if (dsh) return { url: pathToFileURL(dsh).href, shortCircuit: true }
  try {
    return await next(specifier, context)
  } catch (e) {
    if (e?.code !== 'ERR_MODULE_NOT_FOUND' && e?.code !== 'ERR_PACKAGE_PATH_NOT_EXPORTED') throw e
    // TS 源码里写 ./x.js 指 ./x.ts.
    if (specifier.startsWith('.') && specifier.endsWith('.js') && context.parentURL) {
      const alt = new URL(specifier.replace(/\.js$/, '.ts'), context.parentURL)
      if (existsSync(fileURLToPath(alt))) return { url: alt.href, shortCircuit: true }
    }
    if (specifier.startsWith('.') || specifier.startsWith('/') || specifier.startsWith('node:')) throw e
    const { names, hasDefault } = importedNames(context.parentURL, specifier)
    const q = new URLSearchParams({ names: names.join(','), d: hasDefault ? '1' : '0', from: context.parentURL ?? '' })
    return { url: `cordis-check-stub:${specifier}?${q}`, shortCircuit: true }
  }
}

export async function load(url, context, next) {
  if (url.startsWith('cordis-check-stub:')) {
    const [spec, query] = url.slice('cordis-check-stub:'.length).split('?')
    const q = new URLSearchParams(query)
    const names = (q.get('names') || '').split(',').filter(Boolean)
    const from = q.get('from') ? path.relative(DSH_ROOT, fileURLToPath(q.get('from'))) : '?'
    const source = `
${stubPrelude(`${spec} (from ${from})`)}
export default make(${JSON.stringify(spec)})
${names.map(n => `export const ${n} = make(${JSON.stringify(`${spec}.${n}`)})`).join('\n')}
`
    return { format: 'module', source, shortCircuit: true }
  }
  if (!url.startsWith('file:') || !url.endsWith('.ts')) return next(url, context)
  return { format: 'module', source: await transpile(fileURLToPath(url)), shortCircuit: true }
}
