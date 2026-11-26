// E6f (docs/CONTRIB.md): 造一份实现了贡献键 H1、H2 的真实 dsh 宿主, 不碰基线.
//
//   node contrib-host.mjs <TOOLS 目录>
//
// 把 <TOOLS>/dsh-host 硬链接复制成 <TOOLS>/dsh-host-contrib (不占额外空间), 再只改其中
// @deepseek-ai/dsh-host-webserver/lib/index.js 一个文件 (写新文件, 断开它的硬链接):
//   H1  register / registerUpgrade / tapIndex 经调用者的 ctx.effect 登记 (与 tools.register 一样 owned),
//       调用者的 fiber 卸载或中途失败时自动撤销; 返回值仍可调用, 用来提前撤销.
//   H2  同一 (kind, path) 的登记不再抛错, 按多重集全部留下: 恰好一个时照常应答;
//       多于一个时那条路径回 409 (升级路由则断开), 谁都不生效, 与登记次序无关.
// registerFallback 不改. 用法: DSH_HOST=dsh-host-contrib sh run.sh ...
import fs from 'node:fs'
import path from 'node:path'
import { execFileSync } from 'node:child_process'

const tools = process.argv[2]
if (!tools) { console.error('usage: node contrib-host.mjs <TOOLS dir>'); process.exit(2) }
const src = path.join(tools, 'dsh-host')
const dst = path.join(tools, 'dsh-host-contrib')
if (!fs.existsSync(dst)) execFileSync('cp', ['-al', src, dst])
const file = path.join(dst, 'node_modules/@deepseek-ai/dsh-host-webserver/lib/index.js')
const orig = fs.readFileSync(path.join(src, 'node_modules/@deepseek-ai/dsh-host-webserver/lib/index.js'), 'utf8')

const swap = (text, from, to) => {
  if (!text.includes(from)) throw new Error(`patch anchor not found:\n${from}`)
  return text.replace(from, to)
}

let s = orig
s = swap(s, '\tupgrades = /* @__PURE__ */ new Map();\n',
  '\tupgrades = /* @__PURE__ */ new Map();\n\tcontribs = /* @__PURE__ */ new Map();\n')

s = swap(s, `	register(route) {
		const table = route.kind === "exact" ? this.exact : this.prefixes;
		if (table.has(route.path)) throw new Error(\`webserver: duplicate \${route.kind} route "\${route.path}"\`);
		table.set(route.path, route);
		return () => {
			table.delete(route.path);
		};
	}`, `	register(route) {
		const table = route.kind === "exact" ? this.exact : this.prefixes;
		return this.contribute(table, \`\${route.kind} \${route.path}\`, route.path, route, (n) => ({
			kind: route.kind,
			path: route.path,
			contributors: n,
			handler: (req, res) => {
				res.writeHead(409, { "content-type": "application/json" });
				res.end(JSON.stringify({ error: "route conflict", path: route.path, contributors: n }));
			}
		}), "webServer.register");
	}
	/** E6f: 贡献键. 经调用者的 fiber 登记 (H1); 同一个键的贡献按多重集保存, 发布的值只取决于多重集 (H2). */
	contribute(table, key, path, entry, conflict, label) {
		const self = this;
		return this.ctx.effect(function* () {
			const list = self.contribs.get(key) ?? [];
			list.push(entry);
			self.contribs.set(key, list);
			self.publish(table, path, list, conflict);
			yield () => {
				const at = list.indexOf(entry);
				if (at !== -1) list.splice(at, 1);
				if (!list.length && self.contribs.get(key) === list) self.contribs.delete(key);
				self.publish(table, path, list, conflict);
			};
		}, label);
	}
	publish(table, path, list, conflict) {
		if (list.length === 0) table.delete(path);
		else if (list.length === 1) table.set(path, list[0]);
		else table.set(path, conflict(list.length));
	}`)

s = swap(s, `	registerUpgrade(route) {
		if (this.upgrades.has(route.path)) throw new Error(\`webserver: duplicate upgrade route "\${route.path}"\`);
		this.upgrades.set(route.path, route);
		return () => {
			this.upgrades.delete(route.path);
		};
	}`, `	registerUpgrade(route) {
		return this.contribute(this.upgrades, \`upgrade \${route.path}\`, route.path, route, (n) => ({
			path: route.path,
			contributors: n,
			handler: (req, socket) => { socket.destroy(); }
		}), "webServer.registerUpgrade");
	}`)

s = swap(s, `	tapIndex(transform) {
		this.indexTaps.push(transform);
		return () => {
			const at = this.indexTaps.indexOf(transform);
			if (at !== -1) this.indexTaps.splice(at, 1);
		};
	}`, `	tapIndex(transform) {
		const self = this;
		return this.ctx.effect(function* () {
			self.indexTaps.push(transform);
			yield () => {
				const at = self.indexTaps.indexOf(transform);
				if (at !== -1) self.indexTaps.splice(at, 1);
			};
		}, "webServer.tapIndex");
	}`)

fs.rmSync(file)            // 断开硬链接, 不改基线里的同一个 inode
fs.writeFileSync(file, s)
console.log(`patched ${path.relative(tools, file)} (${orig.length} -> ${s.length} bytes)`)
