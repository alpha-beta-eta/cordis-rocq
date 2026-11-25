#!/usr/bin/env sh
# 运行各层的测试, 并重新生成相邻两层的差别 diffs/L<n>-L<n+1>.diff.
set -e
cd "$(dirname "$0")"
for f in L?.rkt; do raco test "$f"; done
mkdir -p diffs
prev=
for f in L?.rkt; do
  if [ -n "$prev" ]; then
    diff -u "$prev" "$f" > "diffs/${prev%.rkt}-${f%.rkt}.diff" || true
  fi
  prev=$f
done
