// 调用序列的生成. 每个场景都是 exec.mjs 能执行的 { host, actions }.
//
// 动作与演算规则的对应 (见 docs/RULES.md):
//   install  -> O-Insert        dispose  -> O-Dispose
//   provide  -> 提供者的 O-Insert   withdraw -> 提供者的 O-Dispose
//   fault    -> 让第 k 次宿主调用抛错, 即 apply 在第 k 个 L-Step 处 L-Fail
//   emit     -> 一次分发 (O-React 的触发)

import { makeHost } from './host.mjs'

// 默认宿主: 有桩的服务, 加上审计的 26 个插件 inject 最多的若干服务 (无桩, 调用只记录).
export const DEFAULT_HOST = [...new Set([
  ...makeHost({}).modeled,
  'settings', 'subprocess', 'sandboxPolicy', 'layout', 'typert', 'sessions', 'sessionProjections',
  'jobs', 'uiConversation', 'sidebarRight', 'pluginNavigation', 'slots', 'settingsScope', 'locale',
  'commands', 'theme', 'agentPresets', 'fileUpload', 'fileViewer', 'typertGateway', 'uiWorkspace',
  'sidebarRightTabs', 'sandbox', 'inputTriggers', 'desktopPnpm', 'betterSidebar', 'workspaceRegistry',
  'workspaceController', 'webTerminals', 'webStartup', 'web', 'uiSession', 'terminalController', 'sessionQuery', 'agents',
  'sessionController', 'llm', 'sessionProjectionCache', 'storageDomain', 'sessionPersistence', 'attachments',
  'subagents', 'agentDefaultModel', 'fileReferences', 'skills',
])]

export const RULE = {
  install: 'O-Insert', dispose: 'O-Dispose', provide: 'O-Insert (provider)', withdraw: 'O-Dispose (provider)',
  fault: 'L-Fail at the k-th call', emit: 'dispatch', snap: 'observe',
}

export function plain(plugin, host) {
  return {
    host,
    actions: [
      { op: 'snap', label: 'before' },
      { op: 'install', plugin, id: 'p' },
      { op: 'snap', label: 'loaded' },
      { op: 'dispose', id: 'p' },
      { op: 'snap', label: 'after' },
      { op: 'install', plugin, id: 'p2' },
      { op: 'snap', label: 'reloaded' },
    ],
  }
}

// 再装用编号 p2; 比较前用 reloadView 改名: 旧实例 p -> p(旧), 新实例 p2 -> p.
// 这样旧实例卸载后还占着的东西 (残留路由, 仍在监听的事件) 与新实例的登记分得开.
export function reloadView(snap) {
  const ren = o => o === 'p' ? 'p(旧)' : o === 'p2' ? 'p' : o
  const world = {}
  for (const [t, rows] of Object.entries(snap.world)) {
    world[t] = rows.map(r => ({ ...r, owner: r.owner?.split(',').map(ren).join(','), key: t === 'cordis.fibers' ? r.key.replace(/^[^/]+/, ren) : r.key,
      view: t === 'cordis.listeners' ? r.view.split(' > ').map(ren).join(' > ') : r.view }))
  }
  return { ...snap, world }
}

// 第 k 次 site 调用抛错; 卸载; 再装一次 (不再注入故障).
export function fault(plugin, host, site, k) {
  return {
    host,
    actions: [
      { op: 'snap', label: 'before' },
      { op: 'fault', site, nth: k, who: 'p' },
      { op: 'install', plugin, id: 'p' },
      { op: 'snap', label: 'loaded' },
      { op: 'dispose', id: 'p' },
      { op: 'snap', label: 'after' },
      { op: 'install', plugin, id: 'p2' },
      { op: 'snap', label: 'reloaded' },
    ],
  }
}

// 服务 s 在插件之后才出现. 与 plain 的 loaded 比较 (C2: 启动分支不依赖调度).
export function late(plugin, host, service) {
  return {
    host: host.filter(h => h !== service),
    actions: [
      { op: 'install', plugin, id: 'p' },
      { op: 'provide', service },
      { op: 'snap', label: 'final' },
    ],
  }
}

// 服务 s 的提供者在插件装上之后重启: 撤走再提供 (提供者的 O-Dispose, O-Insert).
// 与 plain 的 loaded 比较. 真实宿主里配置变更, 热重载都会这样; 插件若只在 apply 时读一次 s,
// 新实例上就没有它的登记 (真实宿主上的 token-diet 与 webServer, dsh-remote 与 skills).
export function restart(plugin, host, service) {
  return {
    host,
    actions: [
      { op: 'install', plugin, id: 'p' },
      { op: 'withdraw', service },
      { op: 'provide', service },
      { op: 'snap', label: 'final' },
    ],
  }
}

// 两个插件按给定次序安装.
export function pair(a, b, host, order) {
  const [x, y] = order === 'ab' ? [a, b] : [b, a]
  return {
    host,
    actions: [
      { op: 'install', plugin: x, id: x === a ? 'A' : 'B' },
      { op: 'install', plugin: y, id: y === a ? 'A' : 'B' },
      { op: 'snap', label: 'final' },
    ],
  }
}
