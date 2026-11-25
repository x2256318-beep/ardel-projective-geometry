"""Part 263（PAG267）の行を検証表に足す（2026-11-25）。行 3724 から 34 行。"""
import openpyxl, copy, shutil, os
R = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
os.makedirs('/home/claude/out/final85', exist_ok=True)
p = '/home/claude/out/final85/lean_verification_status.xlsx'
shutil.copy(R, p)
wb = openpyxl.load_workbook(p); ws = wb['定理と証明']
LABEL = ('PAG2.0-263（PAG267、短期層の小さいノート）P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限、赤道への制限と赤道からの 0 延長'
 '（推薦案 pag2_p1_tower_preregistration.md、著者の採用 2026-11-25 18:27。基礎文書の索引の「射影」の空間の水準の問い）：'
 '還元 P¹(ℤ/M) → P¹(ℤ/N) は恒等・合成の法則を満たし、反転と可換で、M ≠ 0 なら全射。0 と ∞ は W で入れ替わり、N ≠ 1 なら異なる。'
 'P¹ の上の関数の引き戻しは整除の順序の上の帰納系で、極限の上の反転は対合。赤道 [x:1] への制限は引き戻しと両立し、Part 254 の Lim への全射を誘導し、反転を逆元に移す。'
 '赤道からの 0 延長が引き戻しと可換 ⇔ 上の段の法の素因数がすべて下の段の法を割る。証人 (1, 2)。0 延長は極限に降りない。'
 'ラベル（見込み、閉鎖で確定）は 1〜3 が［既知］、4・5 が［再導出（小さい）］、新規候補なし')
R_ = [
 ('red_mk', 'red h [v] = [v mod N]', '定義', 'Quotient.lift'),
 ('red_self', 'N ∣ N の還元は恒等', 'castHom の恒等', 'ZMod.cast_id\''),
 ('red_comp', 'N ∣ M ∣ L なら還元の合成は L → N の還元', 'castHom の合成', 'ZMod.castHom_comp'),
 ('red_Wproj', '還元は反転 W と可換', '代表で rfl', 'PAG.Part27.Wproj'),
 ('Wproj_zeroPt', 'W[0:1] = [1:0]', 'rfl', 'PAG.Part27.Wproj'),
 ('Wproj_infPt', 'W[1:0] = [0:1]', 'rfl', 'PAG.Part27.Wproj'),
 ('red_zeroPt', '還元は [0:1] を [0:1] に送る', 'map_zero・map_one', 'ZMod.castHom'),
 ('red_infPt', '還元は [1:0] を [1:0] に送る', 'map_zero・map_one', 'ZMod.castHom'),
 ('zeroPt_ne_infPt', 'N ≠ 1 なら [0:1] ≠ [1:0]（N = 1 では等しい）', '1 = u·0 から N ∣ 1', 'ZMod.natCast_eq_zero_iff'),
 ('exists_redU', 'M ≠ 0、N ∣ M なら、法 N の単模の組は法 M の単模の組の還元と射影的に同値', 'a = 単数 × N の約数 d と書き、(d, b の持ち上げ) の単模性を核の補題で直す', 'ZMod.eq_unit_mul_divisor, PAG.Part262.mem_ker_iff'),
 ('red_surjective', 'M ≠ 0 なら還元 P¹(ℤ/M) → P¹(ℤ/N) は全射（M ≠ 0 は外しても成り立つ見込み）', 'exists_redU', 'exists_redU'),
 ('eqPt_injective', 'x ↦ [x:1]（x は単数）は単射', 'スカラー倍は 1', 'Units.ext'),
 ('red_eqPt', '還元は [x:1] を [x mod N : 1] に送る', '代表の計算', 'ZMod.unitsMap'),
 ('isUnit_of_castHom', 'M の素因数がすべて N を割るなら、法 N で単数に落ちる元は法 M でも単数', '互いに素性の素因数による判定', 'Nat.coprime_of_dvd, ZMod.isUnit_iff_coprime'),
 ('exists_eqPt_of_red', '同じ条件で、還元が赤道の点なら元の点も赤道の点', 'isUnit_of_castHom を両座標に', 'isUnit_of_castHom'),
 ('pullP_injective', 'P¹ の上の関数の引き戻しは単射', '還元の全射性', 'red_surjective'),
 ('ofP_injective', '各段から極限 LimP への写像は単射', 'pullP_injective', 'Module.DirectLimit.exists_eq_of_of_eq'),
 ('Wfun_comp_pullP', '反転の関数の写像（Part 24 の Wpull）は引き戻しと可換', 'red_Wproj', 'red_Wproj'),
 ('WL_ofP', '極限の上の反転 W_∞ は各段で Wfun', 'DirectLimit.map の値', 'Module.DirectLimit.map_apply_of'),
 ('WL_WL', 'W_∞ は対合', 'Wpull_Wpull', 'PAG.Part28.Wpull_Wpull'),
 ('resE_comp_pullP', '赤道への制限は引き戻しと両立（制限してから単数の還元で引き戻す = 引き戻してから制限）', 'red_eqPt', 'red_eqPt'),
 ('resL_ofP', '制限が誘導する resL : LimP → Lim（Part 254）は各段で resE', 'DirectLimit.map の値', 'Module.DirectLimit.map_apply_of'),
 ('invG_comp_pullSys', '単数の逆元による引き戻しは pullSys と可換', 'unitsMap は逆元を保つ', 'map_inv'),
 ('invL_ofL', '逆元の引き戻しが誘導する invL : Lim → Lim は各段で invG', 'DirectLimit.map の値', 'Module.DirectLimit.map_apply_of'),
 ('Wproj_eqPt', 'W[x:1] = [x⁻¹:1]（Part 24 の mk_inv_eq と同じ内容）', 'スカラー倍 x⁻¹', 'PAG.Part27.mk_eq_mk'),
 ('resL_WL', 'resL ∘ W_∞ = invL ∘ resL（独立照合の指摘で追加）', '各段で Wproj_eqPt', 'Wproj_eqPt'),
 ('extE_eqPt', '0 延長は赤道の点で元の値', 'eqPt_injective', 'eqPt_injective'),
 ('extE_off', '0 延長は赤道の外で 0（合成数の法では赤道の外は 0・∞ だけではない）', '定義', 'dite'),
 ('resE_extE', '制限 ∘ 0 延長 = 恒等', 'extE_eqPt', 'extE_eqPt'),
 ('resL_surjective', 'resL は全射', '各段の 0 延長で持ち上げる', 'resE_extE'),
 ('extE_compat_iff', 'a ∣ b のとき、0 延長がすべての関数で引き戻しと可換 ⇔ b の素因数はすべて a を割る', '⇒：p ∣ b、p ∤ a なら [p:1] は赤道の外で還元は赤道。⇐：exists_eqPt_of_red', 'exists_eqPt_of_red'),
 ('lv1_le_lv2', '1 ∣ 2', 'one_dvd', 'one_dvd'),
 ('extE_not_compat', '証人 (1, 2)：0 延長は引き戻しと可換でない', 'extE_compat_iff で p = 2', 'extE_compat_iff'),
 ('not_exists_extL', '各段で 0 延長と一致する ℂ 線形写像 Lim → LimP はない（resL の線形な切断は否定しない）', 'of_f と ofP_injective と証人', 'Module.DirectLimit.of_f, ofP_injective'),
]
start = 3724
ws.insert_rows(start, len(R_))
for k, (name, claim, proof, ml) in enumerate(R_):
    r = start + k
    for c, v in enumerate([LABEL, name, claim, proof, ml, '検証完了（axioms 確認済み）'], 1):
        cell = ws.cell(r, c); cell.value = v; s = ws.cell(3723, c)
        if s.has_style:
            cell.font = copy.copy(s.font); cell.alignment = copy.copy(s.alignment); cell.border = copy.copy(s.border); cell.fill = copy.copy(s.fill)
last = start + len(R_) - 1
for r in range(last + 1, ws.max_row + 1):
    v = ws.cell(r, 1).value
    if isinstance(ws.cell(r, 2).value, str) and ws.cell(r, 2).value.startswith('=COUNTIF'):
        ws.cell(r, 2).value = f'=COUNTIF($F$2:$F${last},A{r})'
    if isinstance(v, str) and v.startswith('メモ'):
        old = 'Part 262（行 3719〜3723、PAG266.lean、短期層）'; assert old in v, v[-400:]
        v = v.replace(old, f'Part 262（行 3719〜3723、PAG266.lean、短期層）、Part 263（行 3724〜{last}、PAG267.lean、短期層）', 1)
        v = v.rstrip() + (f' 2026-11-25 夜、Part 263（PAG267.lean、短期層、P¹(ℤ/N) の還元の逆系と赤道への制限・0 延長）をコンパイルし、行 3724〜{last} を足した（定理 34 個）。'
         '内部照合で Part 258（PAG262）の mem_ker_iff と Part 24（PAG28）の Wpull・Wpull_Wpull を使った（言葉の検索）。'
         '独立照合を受け、その指摘で Wproj_eqPt・invG_comp_pullSys・invL_ofL・resL_WL を足した。この直しは尾の台帳の L13 で、閉じるときの統合照合の対象。')
        ws.cell(r, 1).value = v
ws2 = wb['検証手順']
ws2.insert_rows(286, 1)
for c in range(1, 5):
    s = ws2.cell(285, c); d = ws2.cell(286, c)
    if s.has_style:
        d.font = copy.copy(s.font); d.alignment = copy.copy(s.alignment); d.border = copy.copy(s.border); d.fill = copy.copy(s.fill)
ws2.cell(286, 1).value = 285
ws2.cell(286, 2).value = 'PAG 2.0 Part 263（短期層）: PAG267.lean（P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限と反転、赤道への制限と Lim への全射、赤道からの 0 延長の両立の判定と極限に降りないこと）をコンパイル'
ws2.cell(286, 3).value = '完了'
ws2.cell(286, 4).value = ('2026-11-25 夜、推薦案 pag2_p1_tower_preregistration.md（著者の採用 18:27）。定理 34 個、sorry 0、警告 0、#print axioms 11 行は標準の公理の範囲。'
 '内部照合（言葉の検索で PAG262 の mem_ker_iff と PAG28 の Wpull を使った。機械的な照合は全宣言 4391 件、対象 55 件、712 回で一致なし）。独立照合（records/audit267/outputs/）。独立照合の後の直しは尾の台帳の L13。')
for row in ws2.iter_rows(min_row=287):
    for c in row:
        if isinstance(c.value, str) and 'COUNTIF($C$2:$C$285' in c.value:
            c.value = c.value.replace('$C$285', '$C$286').replace('$A$285', '$A$286')
wb.save(p); shutil.copy(p, R); print('last', last)
