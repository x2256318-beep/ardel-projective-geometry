import openpyxl, copy, shutil, os
src = '/home/claude/out/final83/lean_verification_status.xlsx'
os.makedirs('/home/claude/out/final84', exist_ok=True)
p = '/home/claude/out/final84/lean_verification_status.xlsx'
shutil.copy(src, p)
wb = openpyxl.load_workbook(p); ws = wb['定理と証明']
LABEL = ('PAG2.0-262（PAG266、短期層の小さいノート）舞台 P¹ の赤道の絡み合いを、貼り合わせの位相 𝔀 で書く（推薦案 pag2_p1_gluing_preregistration.md、著者の採用 2026-11-20 06:55。'
 '基礎文書の索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める材料）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、'
 'conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は χ₁ か χ₂ が偶なら 1、両方とも奇なら −1）、conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²、'
 '赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと射影直線の上）。ラベルは 1〜3 が［既知］、4・5 が［再導出（小さい）］')
R = [
 ('conj_Jhat_eq_gauss', 'χ₁・χ₂・χ₁χ₂ が法 N = p^(n+1) の原始指標なら conj(Ĵ(χ₁, χ₂)) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))（Ĵ = J/√N、τ = gaussSum χ stdAddChar）',
  'J·conj J = N と、ガウス和の比はヤコビ和', 'PAG.Part15.gauss_ratio_eq_jacobi'),
 ('conj_Jhat_eq_rootNum', '同じ仮定で conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（𝔀 = rootNum = τ/(i^a √N)。s は χ₁ か χ₂ が偶なら 1、両方とも奇なら −1）',
  '1 と rootNum の定義、偶奇の 4 通りの場合分け（積の偶奇は χ(−1) の積）', 'MulChar.mul_apply'),
 ('conj_Jhat_sq_eq_rootNum', '同じ仮定で conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²（符号は 2 乗で消える）', '2 の 2 乗', 'conj_Jhat_eq_rootNum'),
 ('equator_intertwine_rootNum', 'n + 1 ≤ K のとき、P¹(ℤ/p^K) の 2 チャートのモデルの赤道のケット |0, χ⟩ について B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)',
  'Part 21 の equator_intertwine_hat と 3', 'PAG.Part25.equator_intertwine_hat'),
 ('equator_intertwine_proj_rootNum', '同じ式を、射影直線 P¹(ℤ/p^K)（ProjLine）の上の関数としての南北の畳み込みと赤道のケットについて（1 ≤ K）',
  'Part 25 の equator_intertwine_proj と 3', 'PAG.Part29.equator_intertwine_proj'),
]
start = 3719
ws.insert_rows(start, len(R))
for k, (name, claim, proof, ml) in enumerate(R):
    r = start + k
    for c, v in enumerate([LABEL, name, claim, proof, ml, '検証完了（axioms 確認済み）'], 1):
        cell = ws.cell(r, c); cell.value = v; s = ws.cell(3718, c)
        if s.has_style:
            cell.font = copy.copy(s.font); cell.alignment = copy.copy(s.alignment); cell.border = copy.copy(s.border); cell.fill = copy.copy(s.fill)
last = start + len(R) - 1
for r in range(last + 1, ws.max_row + 1):
    v = ws.cell(r, 1).value
    if isinstance(ws.cell(r, 2).value, str) and ws.cell(r, 2).value.startswith('=COUNTIF'):
        ws.cell(r, 2).value = f'=COUNTIF($F$2:$F${last},A{r})'
    if isinstance(v, str) and v.startswith('メモ'):
        old = 'Part 261（行 3709〜3718、PAG265.lean、短期層）'; assert old in v, v[-400:]
        v = v.replace(old, f'Part 261（行 3709〜3718、PAG265.lean、短期層）、Part 262（行 3719〜{last}、PAG266.lean、短期層）', 1)
        v = v.rstrip() + (f' 2026-11-20 朝、Part 262（PAG266.lean、短期層、舞台 P¹ の赤道の絡み合いを 𝔀 で書く）をコンパイルし、行 3719〜{last} を足した（定理 5 個）。'
         '内部照合で、Part 21（PAG25）の equator_intertwine_hat と Part 25（PAG29）の equator_intertwine_proj を使った（言葉の検索）。')
        ws.cell(r, 1).value = v
ws2 = wb['検証手順']
ws2.insert_rows(285, 1)
for c in range(1, 5):
    s = ws2.cell(284, c); d = ws2.cell(285, c)
    if s.has_style:
        d.font = copy.copy(s.font); d.alignment = copy.copy(s.alignment); d.border = copy.copy(s.border); d.fill = copy.copy(s.fill)
ws2.cell(285, 1).value = 284
ws2.cell(285, 2).value = 'PAG 2.0 Part 262（短期層）: PAG266.lean（舞台 P¹ の赤道の絡み合いを貼り合わせの位相 𝔀 で書く：ヤコビ和の共役のガウス和と 𝔀 による形、符号つきの 1 乗と 2 乗の形、2 チャートのモデルと射影直線の上の作用素の形）をコンパイル'
ws2.cell(285, 3).value = '完了'
ws2.cell(285, 4).value = ('2026-11-20 朝、推薦案 pag2_p1_gluing_preregistration.md（著者の採用 06:55）。定理 5 個、sorry 0、警告 0、#print axioms 5 行は標準の公理の範囲。'
 '内部照合（言葉の検索で Part 21 の equator_intertwine_hat と Part 25 の equator_intertwine_proj を使った。機械的な照合は全宣言 4490 件、対象 5 件、200 回で一致なし）。記録は records/audit266/。')
for row in ws2.iter_rows(min_row=286):
    for c in row:
        if isinstance(c.value, str) and 'COUNTIF($C$2:$C$284' in c.value:
            c.value = c.value.replace('$C$284', '$C$285').replace('$A$284', '$A$285')
wb.save(p); print('last', last)
