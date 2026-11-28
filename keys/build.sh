#!/usr/bin/env sh
# Compile the hygienic-keys extension. The core (../theories) must be built
# first: run ../build.sh. Nothing in ../theories imports these files.
set -e
cd "$(dirname "$0")"
for f in $(grep '^theories/.*\.v$' _CoqProject); do
  echo "coqc $f"
  coqc -Q ../theories Cordis -Q theories CordisKeys "$f"
done
