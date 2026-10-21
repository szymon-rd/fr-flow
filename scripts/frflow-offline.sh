#!/usr/bin/env bash
# Runs the authz example CLI from classes built by build-offline.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SCALA_HOME="${SCALA_HOME:?set SCALA_HOME to an unpacked Scala 3 distribution}"
cd "$ROOT"
exec java -cp "$ROOT/target/offline/classes:$SCALA_HOME/lib/scala.jar" frflow.examples.authz.authz "$@"
