#!/usr/bin/env python3
"""直しの照合 F の指摘を受けた xlsx の 2 回目の直し（final77 の中で直す。1 回目の状態は round1_state に保存）。"""
import re
from openpyxl import load_workbook
P = '/home/claude/out/final77/lean_verification_status.xlsx'
wb = load_workbook(P)
ws = wb['定理と証明']
rows = {}
for r in range(2, ws.max_row + 1):
    m = re.match(r'PAG2\.0-(249|25[0-6]) ', str(ws.cell(r, 1).value or ''))
    if m: rows.setdefault(m.group(1), []).append(r)
def cell_of(part, name, col):
    rs = [r for r in rows[part] if ws.cell(r, 2).value == name]
    assert len(rs) == 1, (part, name, rs)
    return ws.cell(rs[0], col)
def rep(cell, a, b):
    v = cell.value; assert v.count(a) == 1, (cell.coordinate, a[:40])
    cell.value = v.replace(a, b)
# もとからある文のファイル番号の取り違え（Part 番号 = ファイル番号 − 4）
rep(cell_of('252', 'normSq_rootNum', 4), 'Part 16 の |τ(χ)|² = N', 'Part 12（PAG16）の |τ(χ)|² = N')
rep(cell_of('253', 'ip_charU', 4), 'Part 218 の単数の上の指標の和', 'Part 214（PAG218）の単数の上の指標の和')
c3295 = [ws.cell(r, 4) for r in rows['249'] if isinstance(ws.cell(r, 4).value, str) and 'Part 218 の dil_one' in ws.cell(r, 4).value]
assert len(c3295) == 1
rep(c3295[0], 'Part 218 の dil_one', 'Part 214（PAG218）の dil_one')
# Lean で確かめた C（標本）
rep(cell_of('252', 'hartley_one', 4), '付録 A の Part 3 の hartley_char（命題 2.8）から数行。照合者の判定）', '付録 A の Part 3 の hartley_char（命題 2.8）から数行。照合者の判定、Lean で確認）')
rep(cell_of('252', 'casKer_eq', 4), '付録 A の Part 3 の casK_even_part・casK_odd_part から数行。照合者の判定）', '付録 A の Part 3 の casK_even_part・casK_odd_part から数行。照合者の判定、Lean で確認）')
# 境目と関係の注記
rep(cell_of('256', 'rootNum_prodChar', 4), '中身は Part 189 の gaussSum_mul_coprime に偶奇の因子のずれを足したもの。照合者の判定は数行と新しいの境目）',
    '中身は Part 189 の z_mul_coprime・gaussSum_mul_coprime に偶奇の因子のずれを足したもの。照合者の判定は D（C との境目）。Lean ではつないでいない）')
rep(cell_of('256', 'cross_eq_sign_of_rootNum_one', 4), '実原始指標では 3 つの仮定は Part 194 の gauss_sign_real から成り立ち、結論は Part 194 の real_reciprocity と同じ式。相互法則そのものは Part 194 で仮定なしに示してある）',
    '実原始指標では 3 つの仮定は Part 194 の gauss_sign_real から成り立ち、結論は Part 194 の real_reciprocity の式と同値（crossSign と rs が同じ値）。数学として。Lean ではつないでいない。相互法則そのものは Part 194 で、W = 1 の仮定を使わずに（互いに素・原始・実の指標のもとで）示してある）')
# 見出し
def rep_head(part, a, b):
    h = ws.cell(rows[part][0], 1).value
    assert h.count(a) == 1, (part, a[:40])
    for r in rows[part]: ws.cell(r, 1).value = h.replace(a, b)
rep_head('252', '。内部照合（2026-11-14）：Hartley の部分は付録 A の Part 3（PAG3.lean、命題 2.8）とほぼ重なる。casKer は Part 3 の casK、rootNum は Part 192 の zN ÷ Part 194 の gs と同じ値',
         '。内部照合（2026-11-14）：照合者の判定では、Hartley の部分の中心の 7 件は付録 A の Part 3（PAG3.lean、命題 2.8 hartley_char）などから数行で出る（2 件を Lean で確認、5 件は確信度 低）。casKer は付録 A の Part 3 の casK、rootNum は Part 192 の zN ÷ Part 194 の gs と同じ値（Lean で確認）')
rep_head('253', '。内部照合（2026-11-14）：charU は Part 1 の PAG.charFun（toUnitHom を通したもの）、ip は Part 249 の ipG と同じ対象',
         '。内部照合（2026-11-14）：charU は Part 1 の PAG.charFun に toUnitHom を通したものと同じ関数、ip は Part 249 の ipG と同じ定義（Lean で確認）')
rep_head('256', 'は Part 189・190・195・232 の示し直し。crossSign は Part 194 の rs と同じ値。相互法則は Part 194 の real_reciprocity',
         'は Part 189・190・195・232 の示し直し（Lean で確認）。crossSign は Part 194 の rs と同じ値。相互法則は Part 194 の real_reciprocity で、W = 1 の仮定を使わずに示してある')
# メモ
memo = [ws.cell(r, 1) for r in range(3554, ws.max_row + 1) if isinstance(ws.cell(r, 1).value, str) and ws.cell(r, 1).value.startswith('メモ：')]
assert len(memo) == 1
rep(memo[0], 'PAG255〜PAG258・PAG260 の docstring と冒頭の説明に注記を足し', 'PAG256〜PAG258・PAG260 の docstring と、PAG255〜PAG258・PAG260 の冒頭の説明に注記を足し')
rep(memo[0], 'Part 251〜256 の行の「証明の方針」と、Part 252・253・256 の見出しに注記を足した（行は足していない）。',
    'Part 251〜254・256 の行の「証明の方針」と、Part 252・253・256 の見出しに注記を足した（行は足していない）。直しの照合（照合者 F）の指摘で、注記の強さと、もとからある文のファイル番号の取り違え 3 か所（Part 249・252・253 の行）を直した。')
# 手順 278
ws2 = wb['検証手順']
assert str(ws2.cell(279, 1).value) == '278'
rep(ws2.cell(279, 2), '一方を他方にそのまま当てる確認を約 1 万 3 千組', '一方を他方にそのまま当てる確認を約 1 万 3 千回（組ごとに両向き）')
rep(ws2.cell(279, 4), '照合者の判定で前の鎖から数行で出るもの（C）は 20（4 件を Lean で確認、すべて当たり）。Part 249・250・255 は前の鎖に重複なし。',
    '照合者の判定で前の鎖から数行で出るもの（C）は 20（6 件を Lean で確認、すべて当たり）。Part 249・250・255 は前の鎖との重複が見つからなかった（網羅ではない）。直しの照合（照合者 F）の指摘 24 件を受けて、注記の強さなどを直した。')
wb.save(P)
print('saved')
