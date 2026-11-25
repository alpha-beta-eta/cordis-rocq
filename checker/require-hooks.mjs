// require 的钩子 (在主线程里运行). hooks.mjs 的异步钩子只接管 import; 插件用 createRequire
// 或 .cjs 文件 require 的包走 CJS 自己的加载器, 绕过了它们 (dsh-mobile-plugin 就这样
// require('ws') 而装不上). 这里对 require 做同样的三件事:
// 1. dsh vendored 的包与其余 @deepseek-ai/* 映射到同一个 TS 源文件. require(esm) 与 import 共用
//    同一个模块缓存, 所以插件 require 到的 schemastery 与宿主桩 import 到的是同一个实例.
//    require 拿到的值照 dsh 的 CJS 构建 (tsdown) 的形状: 只有 default 导出时是 default 本身
//    (例如 schemastery 的 lib/index.cjs 是 module.exports = Schema), 否则是命名空间. 这由一层
//    薄壳 (.cache/require-shims/) 的 'module.exports' 导出名给出;
// 2. 找不到的裸包名换成吸收型桩 (module.exports 是一个桩), 照样记进
//    process[Symbol.for('cordis-check.stubs')];
// 3. 被 require 的 .ts 同步转译 (与异步钩子共用缓存).
//
// 解析用的是给 Module._resolveFilename 打补丁, 而不是 registerHooks 的 resolve: ESM 加载器
// 装载 CJS 文件时给它的 require 只调 Module._resolveFilename, 不经过 registerHooks. 桩因此
// 是磁盘上的真实文件 (.cache/require-stubs/), 不用自定义 URL.
import Module, { registerHooks } from 'node:module'
import { fileURLToPath, pathToFileURL } from 'node:url'
import { readFileSync, existsSync, mkdirSync, writeFileSync, renameSync } from 'node:fs'
import { createHash } from 'node:crypto'
import path from 'node:path'
import { vendored, dshEntry, transpileSync, stubPrelude, DSH_ROOT } from './hooks.mjs'

const here = path.dirname(fileURLToPath(import.meta.url))
const STUBS = path.join(here, '.cache/require-stubs')
const SHIMS = path.join(here, '.cache/require-shims')
const tag = Symbol.for('cordis-check.stubs')
const seen = new Set()

// 按内容生成的小文件. 并发的进程可能同时写同一个, 先写临时文件再 rename, 内容相同, 谁赢都行.
function generated(dir, key, ext, content) {
  const file = path.join(dir, `${createHash('sha1').update(key).digest('hex').slice(0, 16)}${ext}`)
  if (!existsSync(file)) {
    mkdirSync(dir, { recursive: true })
    const tmp = `${file}.${process.pid}.${Math.random().toString(36).slice(2)}`
    writeFileSync(tmp, content)
    renameSync(tmp, file)
  }
  return file
}

const stubFile = spec => generated(STUBS, spec, '.cjs', `${stubPrelude(null)}\nmodule.exports = make(${JSON.stringify(spec)})\n`)

function shimFile(target) {
  const url = JSON.stringify(pathToFileURL(target).href)
  return generated(SHIMS, target, '.mjs', `import * as ns from ${url}
export * from ${url}
const keys = Object.keys(ns)
const value = keys.length === 1 && keys[0] === 'default' ? ns.default : ns
export { value as 'module.exports' }
`)
}

const original = Module._resolveFilename
Module._resolveFilename = function (request, parent, ...rest) {
  const target = request in vendored ? vendored[request] : dshEntry(request)
  if (target) return shimFile(target)
  try {
    return original.call(this, request, parent, ...rest)
  } catch (e) {
    if (e?.code !== 'MODULE_NOT_FOUND' && e?.code !== 'ERR_PACKAGE_PATH_NOT_EXPORTED') throw e
    if (request.startsWith('.') || path.isAbsolute(request) || request.startsWith('node:')) throw e
    // require('x/package.json') 几乎总是在探测包在不在 (或读版本), 给桩会让插件以为它装着.
    if (request.endsWith('/package.json')) throw e
    const from = parent?.filename ? path.relative(DSH_ROOT, parent.filename) : '?'
    const label = `${request} (require, from ${from})`
    if (!seen.has(label)) { seen.add(label); (process[tag] ??= []).push(label) }
    return stubFile(request)
  }
}

registerHooks({
  load(url, context, next) {
    if (url.startsWith('file:') && url.endsWith('.ts')) {
      return { format: 'module', source: transpileSync(fileURLToPath(url)), shortCircuit: true }
    }
    try {
      return next(url, context)
    } catch (e) {
      // Node 22 的毛病: 注册了同步 load 钩子以后, import 一个 CJS 文件时默认 load 不给源码
      // (留给 CJS 加载器自己读), 却又被同步钩子链的校验拒掉. 这时自己把源码读出来交回去.
      // 这样装载的 CJS 文件, 它的 require 走上面的 Module._resolveFilename.
      if (e?.code !== 'ERR_INVALID_RETURN_PROPERTY_VALUE' || !url.startsWith('file:')) throw e
      return { format: context.format ?? 'commonjs', source: readFileSync(fileURLToPath(url)), shortCircuit: true }
    }
  },
})
