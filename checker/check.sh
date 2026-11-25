#!/bin/sh
# 在 WSL 中运行: sh check.sh check <plugin> | pair <a> <b> | replay <witness.json>
HERE=$(cd "$(dirname "$0")" && pwd)
[ -d "$HERE/.vendor" ] || sh "$HERE/setup.sh"
exec node --no-warnings --import "$HERE/register.mjs" "$HERE/cli.mjs" "$@"
