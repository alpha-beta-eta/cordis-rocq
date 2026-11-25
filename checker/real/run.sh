#!/bin/sh
# 在真实的 dsh 宿主上跑一个场景 (在 WSL 中运行).
# 用法: sh run.sh <名字> <场景.json> <插件>...
#   插件写成 npm 规格 (如 dsh-windows-mcp@0.2.11), 按给定次序装进一个全新的 web profile;
#   驱动插件最后装. 宿主的 DSH_HOME 与 HOME 都在 /tmp/cordis-real-<名字> 下, 不碰你自己的 dsh.
# 需要: ~/.cache/cordis-check 下的 Node 24, pnpm (corepack) 与 npm 装好的 @deepseek-ai/dsh (见 README).
set -e
NAME=$1; SCENARIO=$(cd "$(dirname "$2")" && pwd)/$(basename "$2"); shift 2
HERE=$(cd "$(dirname "$0")" && pwd)
TOOLS=$HOME/.cache/cordis-check
export PATH=$TOOLS/bin:$TOOLS/node-v24.22.3-linux-x64/bin:$PATH
ROOT=/tmp/cordis-real-$NAME
rm -rf "$ROOT"; mkdir -p "$ROOT/home" "$ROOT/dsh"
export DSH_HOME=$ROOT/dsh HOME=$ROOT/home XDG_DATA_HOME=$TOOLS/xdg   # pnpm 的包存储跨运行共用
cd "$TOOLS/dsh-host"
npx dsh web --help > /dev/null                      # 生成 profile
for p in "$@"; do npx dsh plugin --profile web add --ignore-scripts "$p" > "$ROOT/add.log" 2>&1 || { cat "$ROOT/add.log"; exit 1; }; done
cp -r "$HERE/driver" "$ROOT/driver"
npx dsh plugin --profile web add --ignore-scripts "link:$ROOT/driver" > "$ROOT/add.log" 2>&1 || { cat "$ROOT/add.log"; exit 1; }
export CHECK_REAL_SCENARIO=$SCENARIO CHECK_REAL_OUT=$ROOT/out.json
# 宿主跑在只有回环接口的网络命名空间里 (需要 root, WSL 默认就是): 插件连不上任何外部地址,
# 驱动经 127.0.0.1 访问宿主不受影响. 插件的安装在这之前, 在命名空间外完成.
if [ "$(id -u)" = 0 ] && command -v unshare > /dev/null; then
  unshare -n sh -c 'ip link set lo up && exec npx dsh web --no-open --port 0' > "$ROOT/host.log" 2>&1 &
  echo "== host network: loopback only"
else
  npx dsh web --no-open --port 0 > "$ROOT/host.log" 2>&1 &
  echo "== host network: NOT isolated (needs root for unshare -n)"
fi
PID=$!
i=0
while [ $i -lt 240 ]; do
  sleep 1; i=$((i+1))
  if grep -q '"op": "done"' "$ROOT/out.json" 2>/dev/null; then break; fi
  if ! kill -0 $PID 2>/dev/null; then echo "host exited early"; break; fi
done
# 宿主进程树: unshare -> sh -> npx -> node; 整棵杀掉.
kill_tree() { for c in $(pgrep -P "$1"); do kill_tree "$c"; done; kill -"$2" "$1" 2>/dev/null || true; }
kill_tree $PID TERM; sleep 2; kill_tree $PID KILL
echo "== bundles: $(node -e "console.log(require('$DSH_HOME/profiles/web/package.json').dsh.profile.bundles.join(' > '))")"
echo "== driver log ($ROOT/out.json)"; node "$HERE/show.mjs" "$ROOT/out.json" 2>/dev/null || echo "(none)"
echo "== host log tail ($ROOT/host.log)"; tail -25 "$ROOT/host.log"
