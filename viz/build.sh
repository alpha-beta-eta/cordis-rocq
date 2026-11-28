#!/bin/sh
# 在 WSL 中运行（需要 opam 的 ocamlopt）：编译 trace（抽取出的演算 + 驱动），
# 在 scenarios.txt 上运行，写出 traces.json 与 traces.js（viewer.html 读后者）。
# 改了演算或 errors/ 之后，先在仓库根目录重新抽取：
#   coqc -Q theories Cordis -Q errors/theories CordisErr viz/Extract.v
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
BUILD=${BUILD:-$HOME/.cache/cordis-viz}
eval "$(opam env 2>/dev/null)" || true
mkdir -p "$BUILD"
cp "$HERE"/calc/calculus.ml "$HERE"/calc/calculus.mli "$HERE"/calc/trace.ml "$BUILD"/
cd "$BUILD"
ocamlopt -w -a -c calculus.mli calculus.ml
ocamlopt -w +a-4-9-26-27-32..42-44-45-48-70 calculus.cmx trace.ml -o trace
SCEN=${1:-$HERE/scenarios.txt}
./trace "$SCEN" > "$HERE/traces.json"
./trace -js "$SCEN" > "$HERE/traces.js"
echo "wrote $HERE/traces.json and $HERE/traces.js"
