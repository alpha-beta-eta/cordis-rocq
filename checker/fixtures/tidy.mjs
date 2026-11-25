// 自测用: 每做一件事立即登记它的逆.
export default {
  name: 'tidy',
  inject: ['webServer', 'tools'],
  apply(ctx) {
    for (const p of ['a', 'b', 'c']) ctx.effect(() => ctx.webServer.register({ kind: 'exact', path: `/tidy/${p}` }))
    ctx.tools.register({ name: 'tidy_tool' })
  },
}
