#!/bin/sh
# Stands in for a knowledge base's CLI in tests: writes a fixed snapshot.
set -- $1
mkdir -p .frflow
if [ -n "$FAKE_FAIL" ]; then echo "[error] -- Error: model.scala:3: Not found: foo"; exit 1; fi
case "$1" in
  render|check|accept|scaffold)
    cp kb.template.json .frflow/kb.json
    [ -f .frflow/ledger.json ] || cp ledger.template.json .frflow/ledger.json ;;
esac
echo "Picked up JAVA_TOOL_OPTIONS: x"
echo "[info] welcome to sbt 1.10.7"
echo "[info] ran $*"
