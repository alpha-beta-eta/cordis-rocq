// 并行执行调用序列, 每条序列一个子进程 (见 exec.mjs).
// 全进程共用一个并行池: 不论来自哪个插件的检查, 哪个阶段, 稳定性复核, 同时在跑的子进程
// 不超过 JOBS 个 (默认 CPU 数的一半, 环境变量 CHECK_JOBS 可改).

import { spawn } from 'node:child_process'
import fs from 'node:fs'
import os from 'node:os'
import path from 'node:path'
import { fileURLToPath } from 'node:url'

const here = path.dirname(fileURLToPath(import.meta.url))
const root = path.resolve(here, '..')
const work = fs.mkdtempSync(path.join(os.tmpdir(), 'cordis-check-run-'))
let counter = 0

export const JOBS = Number(process.env.CHECK_JOBS) || Math.max(2, Math.floor(os.cpus().length / 2))
let active = 0
const waiting = []
async function acquire() {
  if (active < JOBS) { active++; return }
  await new Promise(resolve => waiting.push(resolve))
}
function release() {
  const next = waiting.shift()
  if (next) next(); else active--
}

export async function runScenario(scenario, opts) {
  await acquire()
  try { return await runOne(scenario, opts) } finally { release() }
}

function runOne(scenario, { timeoutMs = 60000 } = {}) {
  const n = ++counter
  const inFile = path.join(work, `s${n}.json`)
  const outFile = path.join(work, `r${n}.json`)
  fs.writeFileSync(inFile, JSON.stringify(scenario))
  return new Promise((resolve) => {
    const child = spawn(process.execPath, [
      '--no-warnings', '--import', path.join(root, 'register.mjs'),
      path.join(here, 'exec.mjs'), inFile, outFile,
    ], { cwd: root, stdio: ['ignore', 'ignore', 'pipe'] })
    let stderr = ''
    child.stderr.on('data', d => { stderr += d })
    const timer = setTimeout(() => child.kill('SIGKILL'), timeoutMs)
    child.on('exit', (code, signal) => {
      clearTimeout(timer)
      let result
      try { result = JSON.parse(fs.readFileSync(outFile, 'utf8')) } catch {
        result = { crashed: true, code, signal, stderr: stderr.slice(-4000) }
      }
      result.scenario = scenario
      resolve(result)
    })
  })
}

export async function runAll(scenarios, { onDone } = {}) {
  return Promise.all(scenarios.map(async (sc, i) => {
    const r = await runScenario(sc)
    onDone?.(i, r)
    return r
  }))
}
