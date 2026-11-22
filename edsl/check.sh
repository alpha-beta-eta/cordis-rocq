#!/bin/sh
# 在 WSL 中运行: sh check.sh
# 两版 EDSL 分别生成代码, 比较输出逐字相同, 跑反例, 再在 runtime/rt.js 上跑生命周期测试.
set -e
cd "$(dirname "$0")"
export DUNE_BUILD_DIR=${DUNE_BUILD_DIR:-/tmp/edsl-ocaml-build}   # /mnt 上 dune 无法建 socket

echo "### Racket"
( cd racket && raco make examples.rkt gen.rkt && racket gen.rkt examples.rkt >/dev/null )
for f in key escape react; do
  if (cd racket && raco make "bad/$f.rkt" 2>/tmp/err); then echo "bad/$f.rkt 不应通过"; exit 1; fi
  echo "rejected bad/$f.rkt: $(head -1 /tmp/err)"
done
for f in partial cycle; do
  if (cd racket && raco make "bad/$f.rkt" && racket gen.rkt "bad/$f.rkt" >/dev/null 2>&1); then
    echo "bad/$f.rkt 不应通过"; exit 1; fi
  rm -f "out/racket/$f.analysis" "out/racket/$f.ast"
  echo "rejected bad/$f.rkt by analysis"
done

echo "### OCaml"
( cd ocaml && dune build ./gen.exe && mkdir -p ../out/ocaml && "$DUNE_BUILD_DIR/default/gen.exe" examples ../out/ocaml >/dev/null )
sh ocaml/check-bad.sh >/dev/null 2>&1 || true

echo "### 两版输出比较"
for ext in ast js analysis; do
  cmp "out/racket/examples.$ext" "out/ocaml/examples.$ext" && echo "examples.$ext identical"
done

echo "### 生命周期测试"
node test/run.js out/racket/examples.js
node test/run.js out/ocaml/examples.js
