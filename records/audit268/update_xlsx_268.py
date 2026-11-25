"""Part 264（PAG268）の行を検証表に足す（2026-11-25）。行 3758 から 14 行。"""
import openpyxl, copy, shutil, os
R = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
os.makedirs('/home/claude/out/final86', exist_ok=True)
p = '/home/claude/out/final86/lean_verification_status.xlsx'
shutil.copy(R, p)
wb = openpyxl.load_workbook(p); ws = wb['定理と証明']
LABEL = ('PAG2.0-264（PAG268、短期層の小さいノート）P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致'
 '（推薦案 pag2_p1_lift_preregistration.md、著者の指示「お勧めで進めてください」2026-11-25 19:13。索引 2.4 の留保と Part 263 の候補 C2）：'
 'χ(a)·χ⁻¹(b) は P¹ の上で well-defined で、赤道では χ、W で χ⁻¹、トーラスで χ(u) 倍。原始指標の関数の引き戻し extChi は赤道で χ、引き戻しとトーラスと両立。'
 '法 N の式をそのまま使うと原始的でない χ では両立しない。素数冪の法で殻 0 の南ケット（Part 25（PAG29））は χ(a)χ̄(b) の引き戻しの |S_0|^(−1/2) 倍（1 ≤ c）。'
 'U_∞ の持ち上げの非一意性とトーラス等変な延長の一意性は Lean の外。ラベル（見込み、閉鎖で確定）は［再導出（小さい）］、新規候補なし')
R_ = [
 ('mul_inv_apply_unit', '単数 u で χ(u)·χ⁻¹(u) = 1', 'χ·χ⁻¹ = 1', 'MulChar.one_apply_coe'),
 ('chiPt_mk', 'chiPt χ [a:b] = χ(a)·χ⁻¹(b)', '定義', 'Quotient.lift'),
 ('chiPt_eqPt', '赤道 [x:1] で chiPt χ = χ(x)', 'χ⁻¹(1) = 1', 'map_one'),
 ('chiPt_Wproj', 'chiPt χ ∘ W = chiPt χ⁻¹', '積の交換', 'inv_inv'),
 ('torus_eqPt', 'トーラス u·[x:1] = [u x : 1]', 'rfl', 'Units.val_mul'),
 ('chiPt_torus', 'chiPt χ (u·q) = χ(u)·chiPt χ q', '乗法性', 'map_mul'),
 ('chiPt_red_congr', '法が等しく整数での値が等しい指標は、還元の後で同じ chiPt', 'subst と MulChar.ext', 'ZMod.intCast_surjective'),
 ('extChi_eqPt', 'extChi χ の赤道での値は χ(x)', '還元は赤道を保つ、指標の引き戻し', 'PAG.Part258.pullL_charU, changeLevel_primitiveCharacter'),
 ('extChi_changeLevel', 'N ∣ M のとき extChi(changeLevel χ) = extChi χ ∘ 還元', '導手と原始指標の不変性', 'conductor_changeLevel, primitiveCharacter_changeLevel_apply'),
 ('extChi_torus', 'extChi χ (u·q) = χ(u)·extChi χ q', '還元とトーラスの可換', 'chiPt_torus'),
 ('pullP_extChi', '段の言葉で：pullP (extChi χ) = extChi (changeLevel χ)', 'extChi_changeLevel', 'extChi_changeLevel'),
 ('resE_extChi', 'resE (extChi χ) = charU χ（Part 257（PAG261））', 'extChi_eqPt', 'extChi_eqPt'),
 ('chiPt_not_compat', '法 2 の自明な指標（導手 1）で、法 2 の式は点 0 で 0、法 1 の式の引き戻しは 1（法 N の式は原始的でない χ で両立しない）', '値の計算', 'MulChar.map_nonunit'),
 ('ketS_proj_zero_eq', 'p 素数、1 ≤ c ≤ K：殻 0 の南ケット ketS_proj K 0 c（Part 25（PAG29））= |S_0|^(−1/2)·（法 p^c の chiPt χ の引き戻し）（c = 0 では破れる：Lean の外、手計算）', '南北の成分の比較', 'PAG.Part24.ket0_apply, PAG.Part24.chi_cast_inv, PAG.Part29.projFun_ketS'),
]
start = 3758
ws.insert_rows(start, len(R_))
for k, (name, claim, proof, ml) in enumerate(R_):
    r = start + k
    for c, v in enumerate([LABEL, name, claim, proof, ml, '検証完了（axioms 確認済み）'], 1):
        cell = ws.cell(r, c); cell.value = v; s = ws.cell(3757, c)
        if s.has_style:
            cell.font = copy.copy(s.font); cell.alignment = copy.copy(s.alignment); cell.border = copy.copy(s.border); cell.fill = copy.copy(s.fill)
last = start + len(R_) - 1
for r in range(last + 1, ws.max_row + 1):
    v = ws.cell(r, 1).value
    if isinstance(ws.cell(r, 2).value, str) and ws.cell(r, 2).value.startswith('=COUNTIF'):
        ws.cell(r, 2).value = f'=COUNTIF($F$2:$F${last},A{r})'
    if isinstance(v, str) and v.startswith('メモ'):
        old = 'Part 263（行 3724〜3757、PAG267.lean、短期層）'; assert old in v
        v = v.replace(old, f'Part 263（行 3724〜3757、PAG267.lean、短期層）、Part 264（行 3758〜{last}、PAG268.lean、短期層）', 1)
        v = v.rstrip() + (f' 2026-11-25 夜、Part 264（PAG268.lean、短期層、P¹ の上の指標の関数と等変延長、殻 0 のケットとの一致）をコンパイルし、行 3758〜{last} を足した（定理 14 個）。'
         '内部照合で Part 254（PAG258）の pullL_charU、Part 20（PAG24）の ket0_apply、Part 25（PAG29）の projFun_ketS などを使った。')
        ws.cell(r, 1).value = v
ws2 = wb['検証手順']
ws2.insert_rows(287, 1)
for c in range(1, 5):
    s = ws2.cell(286, c); d = ws2.cell(287, c)
    if s.has_style:
        d.font = copy.copy(s.font); d.alignment = copy.copy(s.alignment); d.border = copy.copy(s.border); d.fill = copy.copy(s.fill)
ws2.cell(287, 1).value = 286
ws2.cell(287, 2).value = 'PAG 2.0 Part 264（短期層）: PAG268.lean（P¹(ℤ/N) の上の指標の関数 χ(a)χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致）をコンパイル'
ws2.cell(287, 3).value = '完了'
ws2.cell(287, 4).value = ('2026-11-25 夜、推薦案 pag2_p1_lift_preregistration.md（著者の指示「お勧めで進めてください」19:13）。定理 14 個、sorry 0、警告 0、#print axioms 10 行は標準の公理の範囲。'
 '内部照合（機械的な照合は全宣言 4409 件、対象 18 件、256 回で一致なし）。独立照合の記録は records/audit268/outputs/。')
for row in ws2.iter_rows(min_row=288):
    for c in row:
        if isinstance(c.value, str) and 'COUNTIF($C$2:$C$286' in c.value:
            c.value = c.value.replace('$C$286', '$C$287').replace('$A$286', '$A$287')
wb.save(p); shutil.copy(p, R); print('last', last)
