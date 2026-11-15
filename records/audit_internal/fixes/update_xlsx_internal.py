#!/usr/bin/env python3
"""内部照合（2026-11-14）による xlsx の直し（final76 → final77）。Part 251〜256 の行の「証明の方針」に注記を足し、
Part 252・253・256 の見出しに 1 文を足す。行は足さない。検証手順に 1 行（手順 278）を足し、メモを更新する。"""
import copy, re
from openpyxl import load_workbook
SRC = '/home/claude/out/final76/lean_verification_status.xlsx'
DST = '/home/claude/out/final77/lean_verification_status.xlsx'
wb = load_workbook(SRC)
ws = wb['定理と証明']
T = '（内部照合 2026-11-14：'
NOTES = {
 '251': {'units_eq_of_coprime_parts': 'Part 192 の crt_unique から数行。照合者の判定、Lean で確認）'},
 '252': {
  'inv_apply_neg_one': 'Part 5 の inv_apply_neg_one、Part 21 の chi_inv_neg_one、Part 77 の inv_neg_one と同じ文。Lean で確認）',
  'neg_one_mul_self': "Part 5 の chi_neg_one_sq、Part 25 の chi_neg_one_sq' と同じ文。Lean で確認）",
  'isPrimitive_of_prime_of_ne_one': 'Part 167 の primitive_of_ne_one と同じ文。Lean で確認）',
  'inv_apply_units_inv': '付録 A の Part 3 の apply_inv_eq_inv_apply から 1 行。Lean で確認）',
  'sum_mul_stdAddChar_neg': '付録 A の Part 3 の sum_neg_twist（x = 1）。Lean で確認）',
  'hartley_one': '付録 A の Part 3 の hartley_char（命題 2.8）から数行。照合者の判定）',
  'hartley_eq_of_isPrimitive': '付録 A の Part 3 の hartley_char から数行。照合者の判定、確信度 低）',
  'hartley_eq_zero_of_not_isUnit': '付録 A の Part 3 の hartley_char から数行。照合者の判定、確信度 低）',
  'hartley_units_inv': '付録 A の Part 3 の hartley_char から数行。照合者の判定、確信度 低）',
  'JH_eq_rootNum_mul': '付録 A の Part 3 の hartley_char から数行。照合者の判定、確信度 低）',
  'JH_eq_rootNum_mul_any': '付録 A の Part 3 の hartley_char から数行。照合者の判定、確信度 低）',
  'casKer_eq': '付録 A の Part 3 の casK_even_part・casK_odd_part から数行。照合者の判定）',
  'normSq_rootNum': 'Part 12 の normSq_gaussSum から数行。照合者の判定、Lean で確認）',
  'exists_primitive_odd_three': 'Part 115・163・167 の補題から数行。照合者の判定、Lean で確認）',
  'exists_primitive_even_five': 'Part 115・163・167 の補題から数行。照合者の判定）',
  'rootNum_eq': '付録 A の Part 2 の parity_weight から数行。照合者の判定）',
  'parFac_of_even': '付録 A の Part 2 の parity_weight（r = 1）から [NeZero N] を外した形。照合者の判定）',
  'parFac_of_odd': '付録 A の Part 2 の parity_weight（r = 1）から [NeZero N] を外した形。照合者の判定）',
 },
 '253': {
  'eq_one_of_two': 'Part 194 の level_two_trivial から直ちに出る。Lean で確認）',
  'not_isPrimitive_one_of_two_le': 'Part 191 の ne_one_of_isPrimitive の対偶。Lean で確認）',
  'charU_one_mem_Vimprim': 'Part 191 の ne_one_of_isPrimitive から 1 行。Lean で確認）',
  'not_isPrimitive_one_prime': 'Part 28 の prim_level_p_iff から 1 行。Lean で確認）',
  'Vprim_two': 'Part 26 の no_prim_mod_two から出る。Lean で確認）',
  'ip_charU': 'Part 214 の sum_units_char と付録 A の Part 3 の conj_apply_eq_inv から数行。照合者の判定）',
  'Vprim_ne_bot_prime': 'Part 115 の Lc_ne_one と Part 167 の primitive_of_ne_one から数行。照合者の判定、確信度 低）',
 },
 '254': {
  'gaussSum_inv': 'Part 5 の conj_gaussSum と chi_neg_one_sq から 1 行。Lean で確認）',
  'rootNum_one_of_eq_one': 'Part 192 の zN_level_one から数行。照合者の判定、Lean で確認）',
  'phaseA1_one': 'Part 192 の zN_level_one から数行。照合者の判定、確信度 低）',
 },
 '256': {
  'crtMap_bijective': 'Part 189 の param_bijective と同じ文。Lean で確認）',
  'stdAddChar_crtMap': 'Part 189 の stdAddChar_param と同じ文。Lean で確認）',
  'gaussSum_prodChar': 'Part 189 の gaussSum_mul_coprime と同じ文。Lean で確認。この Part はそれを使わずに示し直していた）',
  'prodChar_apply': 'Part 189 の mul_changeLevel_apply、Part 195 の cmul_apply、Part 232 の charMul_apply と同じ文。Lean で確認）',
  'isPrimitive_prodChar': 'Part 190 の isPrimitive_mul、Part 232 の isPrimitive_charMul と同じ文。Lean で確認）',
  'cast_crtMap_fst': 'Part 189 の param_cast₁ から直ちに出る。Lean で確認）',
  'cast_crtMap_snd': 'Part 189 の param_cast₂ から直ちに出る。Lean で確認）',
  'charU_prodChar': 'Part 232 の charMul_apply_unit から直ちに出る。Lean で確認）',
  'prodChar_neg_one': 'Part 200 の changeLevel_neg_one を 2 回使うだけ。Lean で確認）',
  'norm_char_unit': 'Part 198 の normSq_chi_unit から数行。照合者の判定）',
  'norm_cross': 'Part 195 の normSq_chi_natCast から数行。照合者の判定）',
  'parFac_prodChar': 'Part 200 の changeLevel_neg_one と Part 194 の neg_one_sq_eq から数行。Part 194 の gs_combine と同じ形。照合者の判定）',
  'rootNum_prodChar': '中身は Part 189 の gaussSum_mul_coprime に偶奇の因子のずれを足したもの。照合者の判定は数行と新しいの境目）',
  'cross_eq_sign_of_rootNum_one': '実原始指標では 3 つの仮定は Part 194 の gauss_sign_real から成り立ち、結論は Part 194 の real_reciprocity と同じ式。相互法則そのものは Part 194 で仮定なしに示してある）',
 },
}
HEADS = {
 '252': '。内部照合（2026-11-14）：Hartley の部分は付録 A の Part 3（PAG3.lean、命題 2.8）とほぼ重なる。casKer は Part 3 の casK、rootNum は Part 192 の zN ÷ Part 194 の gs と同じ値',
 '253': '。内部照合（2026-11-14）：charU は Part 1 の PAG.charFun（toUnitHom を通したもの）、ip は Part 249 の ipG と同じ対象',
 '256': '。内部照合（2026-11-14）：前半（中国剰余の分解 crtMap ＝ Part 189 の param、積の指標 prodChar ＝ Part 195 の cmul ＝ Part 232 の charMul、ガウス和の乗法性、原始性）は Part 189・190・195・232 の示し直し。crossSign は Part 194 の rs と同じ値。相互法則は Part 194 の real_reciprocity',
}
rows = {}
for r in range(2, ws.max_row + 1):
    m = re.match(r'PAG2\.0-(25[1-6]) ', str(ws.cell(r, 1).value or ''))
    if m: rows.setdefault(m.group(1), []).append(r)
count = 0
for p, d in NOTES.items():
    for name, note in d.items():
        rs = [r for r in rows[p] if ws.cell(r, 2).value == name]
        assert len(rs) == 1, (p, name, rs)
        v = ws.cell(rs[0], 4).value or ''
        if T in v: continue
        ws.cell(rs[0], 4).value = v + T + note
        count += 1
for p, add in HEADS.items():
    h = ws.cell(rows[p][0], 1).value
    assert all(ws.cell(r, 1).value == h for r in rows[p])
    if '内部照合（2026-11-14）' in h: continue
    for r in rows[p]:
        ws.cell(r, 1).value = h + add
done = False
for r in range(3554, ws.max_row + 1):
    v = ws.cell(r, 1).value
    if isinstance(v, str) and v.startswith('メモ：') and '内部照合' not in v:
        ws.cell(r, 1).value = v + '2026-11-14、内部照合（Part 249〜256 の宣言を前の鎖と突き合わせた監査）のあと、PAG255〜PAG258・PAG260 の docstring と冒頭の説明に注記を足し、PAG255〜PAG260 を同じ環境で組み立て直した（形式文は変えていない）。Part 251〜256 の行の「証明の方針」と、Part 252・253・256 の見出しに注記を足した（行は足していない）。'
        done = True
assert done
ws2 = wb['検証手順']
assert str(ws2.cell(278, 1).value) == '277', ws2.cell(278, 1).value
ws2.insert_rows(279, amount=1)
vals = [278, '内部照合の監査（2026-11-14、著者の判断）：Part 249〜256（PAG253〜PAG260）の宣言 334 件を、前の鎖（PAG.lean〜PAG252.lean と PAG3・PAG5・PAG6）と突き合わせた。Lean のメタプログラムで全宣言の定数を書き出し（4279 件）、候補を機械的に選び、一方を他方にそのまま当てる確認を約 1 万 3 千組。独立の照合者 5 人（R1〜R5）に形式文の全文を渡して判定させ、A・B の判定を Lean で確かめた。重複を docstring・冒頭・ノート・表に書き足し、PAG255〜PAG260 を組み立て直した', '完了',
        '前の鎖と同じ文・同じ対象（A）と直ちに出るもの（B）を Lean で確認：Part 252 に 7、Part 253 に 6（範囲の中の ip を含めず）、Part 254 に 1、Part 256 に 12（定義 3 を含む）、計 26。照合者の判定で前の鎖から数行で出るもの（C）は 20（4 件を Lean で確認、すべて当たり）。Part 249・250・255 は前の鎖に重複なし。照合者は Grep が使えず、全宣言の文の 1〜3 割しか読めていない。記録は pag2_internal_audit_249_256.md']
for c, v in enumerate(vals, start=1):
    cell = ws2.cell(279, c); cell.value = v
    src = ws2.cell(278, c)
    cell.font = copy.copy(src.font); cell.alignment = copy.copy(src.alignment); cell.border = copy.copy(src.border); cell.fill = copy.copy(src.fill)
fixed2 = 0
for r in range(280, ws2.max_row + 1):
    v = ws2.cell(r, 2).value
    if isinstance(v, str) and v.startswith('=COUNTIF($C$2:$C$278'):
        ws2.cell(r, 2).value = v.replace('$C$278', '$C$279').replace('$A$278', '$A$279')
        fixed2 += 1
assert fixed2 == 1, fixed2
wb.save(DST)
print('saved', DST, 'row notes', count)
