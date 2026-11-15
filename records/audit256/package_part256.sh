#!/bin/bash
# Part 256 の納品物をまとめる
set -e
D=/home/claude/out/deliver256
rm -rf "$D"
mkdir -p "$D"
cp /home/claude/leanwork/pagpkg/PAG260.lean "$D/"
cp /home/claude/leanwork/pagpkg/PAG260.out "$D/"
cp /home/claude/out185/step279.py "$D/"
cp /home/claude/out185/step279.log "$D/"
cp /home/claude/out185/pag2_part256_gluing_cross_term.md "$D/"
cp /home/claude/out185/pag2_part256_independent_audit.md "$D/"
cp /home/claude/out185/pag2_part256_preregistration.md "$D/"
cp /home/claude/leanwork/pagpkg/PAG260.lean /home/claude/leanwork/pagpkg/PAG260.out /home/claude/out/audit256/ 2>/dev/null || true
cp /home/claude/out185/pag2_terwilliger_dictionary.md "$D/"
cp /home/claude/out/final75/lean_verification_status.xlsx "$D/"
cp /home/claude/out/final75/PAG2_handoff_part256.md "$D/"
cd /home/claude/out
rm -f "$D/audit256.zip"
zip -qr "$D/audit256.zip" audit256 -x "audit256/__pycache__/*"
ls -la "$D"
