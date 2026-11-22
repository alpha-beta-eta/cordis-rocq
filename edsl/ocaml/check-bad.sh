#!/bin/sh
# 反例: 前三个应当在类型检查时被拒绝 (escape 除外, 见文件注释); 后两个由分析器拒绝.
cd "$(dirname "$0")"
T=$(mktemp -d)
cp sym.ml keys.ml interp.ml bad/*.ml "$T"
( cd "$T"
  ocamlc -c sym.ml keys.ml interp.ml
  for f in key react escape; do
    echo "== bad/$f.ml"
    ocamlc -c "$f.ml" 2>&1 | grep -v '^ *[0-9]* |' | grep -v '^ *\^' | head -8
  done
  echo "== bad/escape.ml (run)"
  ocamlc -o esc sym.cmo keys.cmo interp.cmo escape.cmo && ./esc 2>&1 | head -2 )
for s in partial cycle; do
  echo "== $s"
  "${DUNE_BUILD_DIR:-_build}/default/gen.exe" "$s" "$T"; echo "exit=$?"
done
rm -rf "$T"
