// 自测用: 先收集裸 disposer, 最后才登记 (dsh-whale-widget 的写法).
export default {
  name: 'leaky',
  inject: ['webServer', 'tools'],
  apply(ctx) {
    const disposers = []
    for (const p of ['a', 'b', 'c']) disposers.push(ctx.webServer.register({ kind: 'exact', path: `/leaky/${p}` }))
    ctx.tools.register({ name: 'leaky_tool' })
    ctx.effect(() => () => { for (const d of disposers) d() })
  },
}
