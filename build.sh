#!/usr/bin/env sh
# Compile every file listed in _CoqProject, in order.
set -e
cd "$(dirname "$0")"
for f in $(grep '^theories/.*\.v$' _CoqProject); do
  echo "coqc $f"
  coqc -Q theories Cordis "$f"
done
