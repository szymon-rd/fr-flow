#!/usr/bin/env bash
# Compiles FrFlow and the examples with a plain Scala 3 distribution, without sbt
# or access to Maven repositories. Tests are not built here (they need munit).
#
#   SCALA_HOME=/path/to/scala3-3.10.0 scripts/build-offline.sh
#   scripts/frflow-offline.sh check     # runs the authz example CLI
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SCALA_HOME="${SCALA_HOME:?set SCALA_HOME to an unpacked Scala 3 distribution}"
OUT="$ROOT/target/offline"

rm -rf "$OUT" && mkdir -p "$OUT/classes"
mapfile -t SOURCES < <(find "$ROOT/modules/core/src/main/scala" "$ROOT/examples" -path '*/src/main/scala/*' -name '*.scala' | sort)
"$SCALA_HOME/bin/scalac" -deprecation -feature -Werror -d "$OUT/classes" "${SOURCES[@]}"
echo "compiled ${#SOURCES[@]} files to $OUT/classes"
