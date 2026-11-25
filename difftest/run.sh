#!/bin/sh
# 差分测试 (在 WSL 中运行): sh run.sh [最大脚本长度, 默认 3]
# 1. 编译 replay (calc/calculus.ml 由 Extract.v 抽取, 见 README.md);
# 2. 生成用例, 分片并行在真实的 Cordis 上跑, 轨迹直接交给 replay 在演算上重放;
# 3. 汇总分歧; 只把每组最短见证重跑一遍, 取它的轨迹 (运行是确定的).
# 结果写到 .out/summary-$NAME.md 与 .out/results-$NAME.txt.
# 默认测 dsh vendored 的 Cordis (NAME=dsh), 插件写成 async 函数; DIFFTEST_STYLE=gen 写成 async 生成器.
# 测上游: CORDIS_ENTRY=/mnt/d/cordis/packages/core/src/index.ts NAME=upstream sh run.sh 4
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
LEN=${1:-3}
NAME=${NAME:-dsh}
JOBS=${JOBS:-$(( $(nproc) / 4 > 0 ? $(nproc) / 4 : 1 ))}
WORK=${WORK:-$HOME/.cache/cordis-difftest/$NAME}
rm -rf "$WORK"
mkdir -p "$WORK" "$HERE/.out"
REPLAY=$(sh "$HERE/calc/build.sh")
[ -d "$HERE/../checker/.vendor" ] || sh "$HERE/../checker/setup.sh"
cd "$HERE/cordis"
RUN="node --no-warnings --import ../../checker/register.mjs run.mjs"
node gen.mjs "$LEN" > "$WORK/cases.json"
i=0
while [ $i -lt "$JOBS" ]; do
  ( $RUN "$WORK/cases.json" /dev/stdout "$i/$JOBS" | "$REPLAY" /dev/stdin > "$WORK/results.$i.txt" ) &
  i=$((i + 1))
done
wait
cat "$WORK"/results.*.txt | sort -V > "$HERE/.out/results-$NAME.txt"
node summarize.mjs witnesses "$HERE/.out/results-$NAME.txt" "$WORK/cases.json" > "$WORK/witnesses.json"
$RUN "$WORK/witnesses.json" "$WORK/witnesses.txt"
node summarize.mjs report "$HERE/.out/results-$NAME.txt" "$WORK/cases.json" "$WORK/witnesses.txt" > "$HERE/.out/summary-$NAME.md"
rm -rf "$WORK"
cat "$HERE/.out/summary-$NAME.md"
