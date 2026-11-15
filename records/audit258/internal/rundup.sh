#!/bin/bash
source /home/claude/leanwork/leanpath.sh
export LEAN_PATH=$LEAN_PATH:/home/claude/out/audit_internal/lean
cd /home/claude/leanwork/pagpkg
t0=$(date +%s)
lean /home/claude/out/audit258/internal/Dup262.lean > /home/claude/out/audit258/internal/Dup262.out 2>&1
echo "rc=$? $(( $(date +%s)-t0 ))s" >> /home/claude/out/audit258/internal/Dup262.out
