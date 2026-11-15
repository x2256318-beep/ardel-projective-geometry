#!/usr/bin/env python3
"""Part 256 の行を xlsx に足す（final74 → final75）。集計の式の範囲と、検証手順の行・式、環境の行を更新する。"""
import sys, copy, os, re
sys.path.insert(0, '/home/claude/out/audit256')
import importlib
import xlsx_rows_part256 as R
importlib.reload(R)
from openpyxl import load_workbook

# 行の名前が PAG260.lean の定理と同じ順か確かめる
lean = open('/home/claude/leanwork/pagpkg/PAG260.lean', encoding='utf-8').read()
names = re.findall(r"^theorem (\S+)", lean, flags=re.M)
assert [r[0] for r in R.ROWS] == names, ([r[0] for r in R.ROWS], names)

SRC = '/home/claude/out/final74/lean_verification_status.xlsx'
DST = '/home/claude/out/final75/lean_verification_status.xlsx'
os.makedirs(os.path.dirname(DST), exist_ok=True)
wb = load_workbook(SRC)
ws = wb['定理と証明']
last = 3530
assert ws.cell(last, 2).value == 'exists_between_one', ws.cell(last, 2).value
assert ws.cell(last + 1, 1).value is None
n = len(R.ROWS)
ws.insert_rows(last + 1, amount=n)
style_row = last
for i, (name, claim, proof, lemmas) in enumerate(R.ROWS):
    r = last + 1 + i
    vals = [R.HEAD, name, claim, proof, lemmas, '検証完了（axioms 確認済み）']
    for c, v in enumerate(vals, start=1):
        cell = ws.cell(r, c)
        cell.value = v
        src = ws.cell(style_row, c)
        cell.font = copy.copy(src.font)
        cell.alignment = copy.copy(src.alignment)
        cell.border = copy.copy(src.border)
        cell.fill = copy.copy(src.fill)
        cell.number_format = src.number_format
new_last = last + n
fixed = 0
for r in range(new_last + 1, ws.max_row + 1):
    v = ws.cell(r, 2).value
    if isinstance(v, str) and v.startswith(f'=COUNTIF($F$2:$F${last}'):
        ws.cell(r, 2).value = f'=COUNTIF($F$2:$F${new_last},A{r})'
        fixed += 1
assert fixed == 4, fixed
done = False
for r in range(new_last + 1, ws.max_row + 1):
    v = ws.cell(r, 1).value
    if isinstance(v, str) and v.startswith('メモ：'):
        a = 'PAG259 は 2026-11-13 に同じ環境でコンパイル（追加のビルドなし）。'
        assert a in v
        v = v.replace(a, a + 'PAG260 は 2026-11-13 に同じ環境でコンパイル（追加のビルドなし）。')
        b = '、PAG259.lean）'
        assert v.count(b) == 1 and 'Part 256（行' not in v
        v = v.replace(b, b + f'、Part 256（行 3531〜{new_last}、PAG260.lean）')
        ws.cell(r, 1).value = v
        done = True
assert done
ws2 = wb['検証手順']
assert str(ws2.cell(276, 1).value) == '275'
ws2.insert_rows(277, amount=1)
step = [276, R.STEP_TEXT, '完了', R.STEP_NOTE]
for c, v in enumerate(step, start=1):
    cell = ws2.cell(277, c)
    cell.value = v
    src = ws2.cell(276, c)
    cell.font = copy.copy(src.font)
    cell.alignment = copy.copy(src.alignment)
    cell.border = copy.copy(src.border)
    cell.fill = copy.copy(src.fill)
fixed2 = 0
for r in range(278, ws2.max_row + 1):
    v = ws2.cell(r, 2).value
    if isinstance(v, str) and v.startswith('=COUNTIF($C$2:$C$276'):
        ws2.cell(r, 2).value = v.replace('$C$276', '$C$277').replace('$A$276', '$A$277')
        fixed2 += 1
assert fixed2 == 1, fixed2
ws3 = wb['環境']
r3 = ws3.max_row + 1
assert ws3.cell(r3 - 1, 1).value.startswith('Mathlib の追加ビルド（2026-11-13、Part 255）')
for c, v in enumerate([R.ENV_KEY, R.ENV_TEXT], start=1):
    cell = ws3.cell(r3, c)
    cell.value = v
    src = ws3.cell(r3 - 1, c)
    cell.font = copy.copy(src.font)
    cell.alignment = copy.copy(src.alignment)
    cell.border = copy.copy(src.border)
    cell.fill = copy.copy(src.fill)
wb.save(DST)
print('saved', DST, 'rows', last + 1, '..', new_last, 'items', new_last - 1)
