// 找到插件的入口文件.
// 名字是 D:\dsh-plugins 下的目录名 (如 dsh-whale-widget, xmanrui__dsh-im), 每个目录下只有一个版本;
// 以 ./ 或 / 开头的名字是本地的测试插件.

import fs from 'node:fs'
import path from 'node:path'
import { fileURLToPath } from 'node:url'

const here = path.dirname(fileURLToPath(import.meta.url))
export const PLUGINS_ROOT = process.env.PLUGINS_ROOT ?? '/mnt/d/dsh-plugins'

export function resolvePlugin(name) {
  if (name.startsWith('./') || name.startsWith('/')) {
    const main = path.resolve(here, '..', name)
    return { main, label: name, version: 'local' }
  }
  const dir = path.join(PLUGINS_ROOT, name)
  // 只认版本号目录; 有的插件目录下还留着上一轮审计解压的 package/.
  const versions = fs.readdirSync(dir).filter(v => /^\d+\.\d+\.\d+/.test(v))
  if (versions.length !== 1) throw new Error(`${name}: expected one version under ${dir}, found ${versions.join(', ')}`)
  const pkgDir = path.join(dir, versions[0], 'package')
  const pkg = JSON.parse(fs.readFileSync(path.join(pkgDir, 'package.json'), 'utf8'))
  let main = pkg.exports?.['.']?.import ?? pkg.exports?.['.']?.default ?? (typeof pkg.exports?.['.'] === 'string' ? pkg.exports['.'] : undefined) ?? pkg.main ?? 'index.js'
  main = path.join(pkgDir, main)
  return { main, label: `${pkg.name}@${pkg.version}`, version: pkg.version }
}
