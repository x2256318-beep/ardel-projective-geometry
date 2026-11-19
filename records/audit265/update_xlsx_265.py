import openpyxl, copy, shutil
src='/home/claude/out/final82/lean_verification_status.xlsx'
p='/home/claude/out/final83/lean_verification_status.xlsx'
shutil.copy(src,p)
wb=openpyxl.load_workbook(p); ws=wb['定理と証明']
LABEL=('PAG2.0-261（PAG265、短期層の小さいノート）角の写像の帰納系と、その極限の非単位的な代数（方向 γ の立て直しの推薦案の R-d の残り。著者の採用 2026-11-19 12:51。基礎文書の第5章の材料）：'
 '正の整数の整除の順序（Part 254 の Lvl、有向）の上で、Part 260 の角の写像 φ は帰納系をなし（恒等と合成の法則、DirectedSystem のインスタンス）、Mathlib の一般の DirectLimit による極限 CornerLim は非単位的な環の構造と ℂ のスカラー倍を持つ。'
 '各 A_N は非単位的な ℂ 代数準同型 ofCorner で単射に入り、極限は局所的な単位元を持つ（有限集合ごとに共通のべき等元）が、左単位元を持たない。ラベルは［再導出（小さい）］')
R=[
('cornerSys_self','恒等の法則：φ_{a,a} = id（cornerSys は def：a ≤ b なら Part 260 の cornerHom）','Part 260 の cornerOp_self','PAG.Part264.cornerOp_self'),
('cornerSys_comp','合成の法則：φ_{b,c} ∘ φ_{a,b} = φ_{a,c}（この 2 法則で DirectedSystem のインスタンス）','Part 260 の cornerOp_comp','PAG.Part264.cornerOp_comp'),
('ofCorner_apply','標準の写像 ofCorner（def：A_a → 極限 CornerLim（abbrev、Mathlib の一般の DirectLimit）、非単位的な ℂ 代数準同型）の値は商の元 ⟦⟨a, S⟩⟧','rfl','DirectLimit.NonUnitalAlgebra.of'),
('ofCorner_cornerSys','標準の写像は系の写像と両立する：ofCorner_b ∘ φ_{a,b} = ofCorner_a','商の定義','DirectLimit.eq_of_le'),
('ofCorner_injective','各 A_a は極限に単射で入る','遷移写像の単射性（Part 260 の cornerHom_injective）','DirectLimit.mk_injective'),
('exists_local_unit','局所的な単位元：極限のどの元 x にも、ある a があって e_a = ofCorner_a(1) が e_a x = x = x e_a を満たす','x を ofCorner_a(S) と書き、A_a の中で 1·S = S = S·1','DirectLimit.exists_eq_mk'),
('ofCorner_one_mul_self','e_a = ofCorner_a(1) はべき等（2 回目の独立照合の指摘で追加）','A_a の中で 1·1 = 1','map_mul'),
('ofCorner_one_le','a ≤ b なら e_b e_a = e_a = e_a e_b（同上）','e_a = ofCorner_b(φ_{a,b}(1))','ofCorner_cornerSys'),
('exists_local_unit_finset','局所的な単位元（有限集合ごと）：極限の有限部分集合 F ごとに、ある a があってべき等元 e_a が F のどの元も両側から固定する（F ⊆ e_a·極限·e_a。局所的な単位元を持つ環の定義の形。同上）','有限集合の帰納法と添字の有向性、上の 2 つ','Finset.induction_on'),
('not_exists_left_one','大域の単位元はない：極限には左単位元がない','u = ofCorner_c(U) なら d = 2c で φ_{c,d}(U) = 1、Part 260 の cornerOp_one_mul と cornerOp_one_ne_one に反する','PAG.Part264.cornerOp_one_ne_one'),
]
start=3709
ws.insert_rows(start,len(R))
for k,(name,claim,proof,ml) in enumerate(R):
    r=start+k
    for c,v in enumerate([LABEL,name,claim,proof,ml,'検証完了（axioms 確認済み）'],1):
        cell=ws.cell(r,c); cell.value=v; s=ws.cell(3708,c)
        if s.has_style:
            cell.font=copy.copy(s.font); cell.alignment=copy.copy(s.alignment); cell.border=copy.copy(s.border); cell.fill=copy.copy(s.fill)
last=start+len(R)-1
for r in range(last+1, ws.max_row+1):
    v=ws.cell(r,1).value
    if isinstance(ws.cell(r,2).value,str) and ws.cell(r,2).value.startswith('=COUNTIF'):
        ws.cell(r,2).value=f'=COUNTIF($F$2:$F${last},A{r})'
    if isinstance(v,str) and v.startswith('メモ'):
        old='Part 260（行 3669〜3708、PAG264.lean、短期層）'; assert old in v, v[-400:]
        v=v.replace(old,f'Part 260（行 3669〜3708、PAG264.lean、短期層）、Part 261（行 3709〜{last}、PAG265.lean、短期層）',1)
        v=v.rstrip()+(f' 2026-11-19 午後、Part 261（PAG265.lean、短期層、角の写像の帰納系と極限）をコンパイルし、行 3709〜{last} を足した（定理 10 個）。'
         '索引の型は Part 254 の Lvl を使った（内部照合）。下書きの cornerSys_apply（Part 260 の cornerHom_coe と同じ文）を消した。')
        ws.cell(r,1).value=v
ws2=wb['検証手順']
ws2.insert_rows(284,1)
for c in range(1,5):
    s=ws2.cell(283,c); d=ws2.cell(284,c)
    if s.has_style:
        d.font=copy.copy(s.font); d.alignment=copy.copy(s.alignment); d.border=copy.copy(s.border); d.fill=copy.copy(s.fill)
ws2.cell(284,1).value=283
ws2.cell(284,2).value='PAG 2.0 Part 261（短期層）: PAG265.lean（角の写像の帰納系：正の整数の整除の順序 Lvl の上の DirectedSystem、Mathlib の一般の DirectLimit による非単位的な代数の極限 CornerLim、各段の単射性、局所的な単位元、左単位元がないこと）をコンパイル'
ws2.cell(284,3).value='完了'
ws2.cell(284,4).value=('2026-11-19 午後、方向 γ の立て直しの推薦案の R-d の残り（著者の採用 12:51）。定理 10 個、sorry 0、警告 0、#print axioms 10 行は標準の公理の範囲。'
 '内部照合（言葉の検索で Part 254 の Lvl を使った。機械的な照合は全宣言 4483 件、対象 11 件、380 回）。1 回目の独立照合の指摘（Mathlib の一般の DirectLimit に非単位的な代数の構造がある）を受けて組み直し、2 回目の独立照合の指摘（局所的な単位元の標準の定義）を受けて 3 定理を足し、再照合を行った。記録は records/audit265/。')
for row in ws2.iter_rows(min_row=285):
    for c in row:
        if isinstance(c.value,str) and 'COUNTIF($C$2:$C$283' in c.value:
            c.value=c.value.replace('$C$283','$C$284').replace('$A$283','$A$284')
wb.save(p); print('last',last)
