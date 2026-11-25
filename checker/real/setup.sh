#!/bin/sh
# 准备真实宿主 (在 WSL 中运行, 只需一次): Node 24, npm 发布版 dsh, pnpm. 都放在 ~/.cache/cordis-check/ 下,
# 不放在 /mnt/d 上 (npm 的安装在 /mnt/d 上又慢, 对符号链接的支持也差).
set -e
TOOLS=$HOME/.cache/cordis-check
NODE=node-v24.22.3-linux-x64
mkdir -p "$TOOLS/bin" "$TOOLS/dsh-host"
if [ ! -x "$TOOLS/$NODE/bin/node" ]; then
  cd "$TOOLS"
  curl -sSfLO "https://nodejs.org/dist/v24.22.3/$NODE.tar.xz"
  curl -sSfL https://nodejs.org/dist/v24.22.3/SHASUMS256.txt | grep " $NODE.tar.xz\$" | sha256sum -c -
  tar xJf "$NODE.tar.xz" && rm "$NODE.tar.xz"
fi
export PATH=$TOOLS/bin:$TOOLS/$NODE/bin:$PATH
cd "$TOOLS/dsh-host"
[ -f package.json ] || echo '{"private":true}' > package.json
# 不执行依赖包的安装脚本.
[ -x node_modules/.bin/dsh ] || npm install --ignore-scripts --no-audit --no-fund @deepseek-ai/dsh@0.2.2-rc.5
COREPACK_ENABLE_DOWNLOAD_PROMPT=0 corepack enable --install-directory "$TOOLS/bin" pnpm
COREPACK_ENABLE_DOWNLOAD_PROMPT=0 corepack prepare pnpm@11.28.5 --activate > /dev/null
echo "node $(node --version), pnpm $(pnpm --version), dsh $(npx dsh --version)"
