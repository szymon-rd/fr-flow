#!/usr/bin/env bash
# Measures examples/scale for each N given (default: 20 60): a cold check, then one code change,
# one claim change and one definition change, each checked, and status. Prints one table row per N.
#
#   bench/measure.sh 20 60
set -euo pipefail
cd "$(dirname "$0")/.."
src=examples/scale/src/main/scala/scale
cp=$(sbt --client "export scale/Runtime/fullClasspath" 2>/dev/null | grep -v '^\[' | grep -E '\.jar|classes' | tail -1)
run() { java -Xss8m -cp "$cp" scale.scaleCli "$@" > /dev/null 2>&1 || true; }
timed() { local s=$(date +%s.%N); "$@"; printf '%.1f' "$(echo "$(date +%s.%N) - $s" | bc)"; }
compile() { sbt --client "scale/compile" > /dev/null 2>&1; }

echo "| nodes | cold \`check\` | one code change | one claim change | one definition change | \`status\` |"
echo "|---|---|---|---|---|---|"
[ $# -gt 0 ] || set -- 20 60
for n in "$@"; do
  nodes=$(python3 bench/generate.py "$n" | sed -E 's/.*: ([0-9]+) nodes.*/\1/')
  rm -rf examples/scale/lean/.lake/build examples/scale/lean/FrFlowGen examples/scale/.frflow
  compile
  cold=$(timed run check)
  # Code: service 3's code, written another way.
  sed -i 's/xs.filter(x => x >= f) }/xs.filter(x => f <= x) }/' $src/Service3.scala; compile
  code=$(timed run check)
  # Claim: FromRequest3 also says what it shows is visible (its contract proves that too).
  sed -i 's/forall(x => xs.contains(x)))).under(service3)/forall(x => xs.contains(x) \&\& visible(x, f)))).under(service3)/' $src/Service3.scala; compile
  claim=$(timed run check)
  # Definition: the limit every bounded service keeps.
  sed -i 's/limit := BigInt(1000)/limit := BigInt(2000)/' $src/Vocabulary.scala; compile
  definition=$(timed run check)
  status=$(timed run status)
  echo "| $nodes | $cold s | $code s | $claim s | $definition s | $status s |"
done
