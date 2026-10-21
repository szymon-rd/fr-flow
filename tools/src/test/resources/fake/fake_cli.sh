#!/bin/sh
# Stands in for a knowledge base's CLI in tests: writes a fixed snapshot and an event.
set -- $1
mkdir -p .frflow
if [ -n "$FAKE_FAIL" ]; then echo "[error] -- Error: model.scala:3: Not found: foo"; exit 1; fi
case "$1" in
  render|check|accept|scaffold)
    cp kb.template.json .frflow/kb.json
    actor=""; [ -n "$FRFLOW_ACTOR" ] && actor=",\"actor\":\"$FRFLOW_ACTOR\""
    printf '{"at":"2026-01-01T00:00:00Z","action":"%s","node":"%s"%s}\n' "$1" "${2:-Root}" "$actor" >> .frflow/events.jsonl ;;
esac
echo "Picked up JAVA_TOOL_OPTIONS: x"
echo "[info] welcome to sbt 1.10.7"
echo "[info] ran $*"
