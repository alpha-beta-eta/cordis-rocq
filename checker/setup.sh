#!/bin/sh
# 把 dsh 自带的 cordis, cosmokit, schemastery 源码复制到 .vendor/，记下来源提交；缺 TypeScript 时下载。
# 用法: sh setup.sh [dsh 仓库路径]，默认 /mnt/d/deepseek-harness。
# 其余 @deepseek-ai/* 包由 hooks.mjs 在运行时从 DSH_ROOT/packages 读取 (只读)。
set -e
DSH=${1:-/mnt/d/deepseek-harness}
HERE=$(cd "$(dirname "$0")" && pwd)
rm -rf "$HERE/.vendor"
mkdir -p "$HERE/.vendor"
for p in cordis cosmokit schemastery; do
  cp -r "$DSH/vendor/$p/src" "$HERE/.vendor/$p"
done
# TypeScript (只用它的 transpileModule): 缺失时从 npm 下载并校验 sha1.
if [ ! -f "$HERE/.tools/typescript/lib/typescript.js" ]; then
  mkdir -p "$HERE/.tools"
  curl -sSfL -o "$HERE/.tools/typescript-5.9.3.tgz" https://registry.npmjs.org/typescript/-/typescript-5.9.3.tgz
  echo "5b4f59e15310ab17a216f5d6cf53ee476ede670f  $HERE/.tools/typescript-5.9.3.tgz" | sha1sum -c -
  tar xzf "$HERE/.tools/typescript-5.9.3.tgz" -C "$HERE/.tools" && mv "$HERE/.tools/package" "$HERE/.tools/typescript"
fi
git -C "$DSH" log -1 --format='deepseek-harness %H %cd' > "$HERE/.vendor/SOURCE"
cat "$HERE/.vendor/SOURCE"
