import { register } from 'node:module'
register('./hooks.mjs', import.meta.url)
// require 走 CJS 的加载器, 异步钩子管不到, 另用同步钩子接管.
await import('./require-hooks.mjs')
