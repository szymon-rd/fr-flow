#!/bin/sh
# Compiles FrFlow's thread library and Ox's proof with Rocq, each file after those it imports.
# Run from the repository root: sh examples/ox/rocq/check.sh
set -e
lib=modules/proof/rocq/FrFlow
ox=examples/ox/rocq/Ox
for f in Prog Jdk Sem Logic Lang; do
  rocq compile -q -Q "$lib" FrFlow "$lib/Threads/$f.v"
done
for f in ${OX_FILES:-Code Ghost Facts Specs Frame Updates Steps Inner HerdProofs ScopeProofs}; do
  rocq compile -q -Q "$lib" FrFlow -Q "$ox" Ox "$ox/$f.v"
done
echo "checked"
