#!/bin/sh
# 在 WSL 中运行: 编译 replay (抽取出的演算 + 重放驱动) 到 $BUILD (默认 ~/.cache/cordis-difftest).
# /mnt 上的文件系统不支持 dune 需要的 socket, 所以直接调 ocamlopt, 在临时目录里编译.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
BUILD=${BUILD:-$HOME/.cache/cordis-difftest}
eval "$(opam env 2>/dev/null)" || true
mkdir -p "$BUILD"
cp "$HERE"/calculus.ml "$HERE"/calculus.mli "$HERE"/replay.ml "$BUILD"/
cd "$BUILD"
ocamlopt -w -a -c calculus.mli calculus.ml
ocamlopt -w +a-4-9-26-27-32..42-44-45-48-70 calculus.cmx replay.ml -o replay
echo "$BUILD/replay"
