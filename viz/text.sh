#!/bin/sh
# 把 TextExamples.v 中的 S-表达式写到 viz/text/<名字>.sexp。
# 在仓库根目录运行（Windows 的 Git Bash 或 WSL，只需要 coqc）；先构建核心与 errors/。
set -e
cd "$(dirname "$0")/.."
FLAGS="-Q theories Cordis -Q errors/theories CordisErr -Q viz CordisViz"
coqc $FLAGS viz/Text.v
coqc $FLAGS viz/TextExamples.v
mkdir -p viz/text
for name in basic divert interleave early late core358 queue358 early_late early_queue \
            vfA vfB vfA_view vf_core vf_view; do
  tmp=viz/_text_$name.v
  printf 'From Stdlib Require Import String.\nFrom CordisViz Require Import TextExamples.\nOpen Scope string_scope.\nEval vm_compute in %s_text.\n' "$name" > "$tmp"
  # Rocq prints  = "<text>"  : string  with each quote doubled; keep <text>, undouble the quotes.
  coqc $FLAGS "$tmp" | sed -e '1s/^ *= "//' -e '/^ *: string$/d' -e 's/"$//' -e 's/""/"/g' > "viz/text/$name.sexp"
  rm -f "$tmp" viz/_text_$name.vo viz/_text_$name.vok viz/_text_$name.vos viz/_text_$name.glob viz/._text_$name.aux
  echo "viz/text/$name.sexp"
done
