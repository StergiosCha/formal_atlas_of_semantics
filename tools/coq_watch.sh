#!/bin/bash
# coq_watch.sh — compile bridge between a sandboxed Claude session and the
# Mac's Coq 8.20.1 toolchain, over the shared repo folder.
#
# Run ONCE from anywhere:   bash ~/Dropbox/revisiting-formal-semantics/tools/coq_watch.sh
# Stop with Ctrl-C (or:     touch .build/STOP   in the repo root).
#
# Protocol: the sandbox writes .build/REQUEST (line 1: nonce, line 2: command
# key). The watcher runs the whitelisted command, streams stdout+stderr to
# .build/OUT.log, appends "==EXIT:<code>==", and copies REQUEST to .build/DONE.
# Only the fixed commands below are ever executed — nothing from the file is
# eval'd.

set -u
REPO="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO" || exit 1
mkdir -p .build
rm -f .build/STOP
echo "watcher started in $REPO (pid $$) — Ctrl-C to stop"

COQFLAGS=(-R shallow "" -R deep "" -R extras "" -R ttr_mtt "" -R atlas "")
last=""
while true; do
  date +%s > .build/heartbeat
  [ -f .build/STOP ] && { echo "STOP file seen; exiting"; exit 0; }
  if [ -f .build/REQUEST ]; then
    req="$(cat .build/REQUEST 2>/dev/null)"
    if [ -n "$req" ] && [ "$req" != "$last" ]; then
      last="$req"
      cmd="$(sed -n '2p' .build/REQUEST)"
      echo "[$(date +%H:%M:%S)] running: $cmd"
      : > .build/OUT.log
      case "$cmd" in
        coqc_inqb)
          coqc "${COQFLAGS[@]}" atlas/inquisitive/InqB.v >> .build/OUT.log 2>&1 ;;
        coqc_dpl)
          coqc "${COQFLAGS[@]}" atlas/dynamic/DPL.v >> .build/OUT.log 2>&1 ;;
        coq_makefile)
          coq_makefile -f _CoqProject -o Makefile >> .build/OUT.log 2>&1 ;;
        make)
          make -k -j8 >> .build/OUT.log 2>&1 ;;
        coq_version)
          coqc --version >> .build/OUT.log 2>&1 ;;
        ps_dpl)
          ps aux | grep run_dpl | grep -v grep >> .build/OUT.log 2>&1
          echo "(end of ps output)" >> .build/OUT.log ;;
        stat_dpl)
          stat -f %m atlas/dynamic/DPL.v >> .build/OUT.log 2>&1 ;;
        *)
          echo "unknown command key: $cmd" >> .build/OUT.log ;;
      esac
      echo "==EXIT:$?==" >> .build/OUT.log
      cp .build/REQUEST .build/DONE
      echo "[$(date +%H:%M:%S)] done: $cmd"
    fi
  fi
  sleep 2
done
