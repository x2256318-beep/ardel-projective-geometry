#!/bin/bash
source /home/claude/leanwork/leanpath.sh
export LEAN_PATH=$LEAN_PATH:/home/claude/out/audit_internal/lean
cd /home/claude/leanwork/pagpkg
j=$1
t0=$(date +%s)
lean -R /home/claude/out/audit_internal/lean /home/claude/out/audit_internal/lean/Run$j.lean > /home/claude/out/audit_internal/lean/Run$j.out 2>&1
echo "Run$j rc=$? $(( $(date +%s)-t0 ))s" >> /home/claude/out/audit_internal/lean/run_checks.log
