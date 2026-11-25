// 自测用: apply 时用 ctx.get 读一次没有 inject 的服务 (dsh-remote 读 skills 的写法).
// 登记本身随 fiber 撤销, 卸载是干净的; 但服务晚到或提供者重启之后, 新实例上没有它的登记.
export default {
  name: 'stale',
  apply(ctx) {
    const webServer = ctx.get('webServer')
    if (webServer) ctx.effect(() => webServer.register({ kind: 'exact', path: '/stale/a' }))
  },
}
