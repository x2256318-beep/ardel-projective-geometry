import openpyxl, copy, shutil
src='/home/claude/out/final81/lean_verification_status.xlsx'
p='/home/claude/out/final82/lean_verification_status.xlsx'
shutil.copy(src,p)
wb=openpyxl.load_workbook(p); ws=wb['定理と証明']
LABEL=('PAG2.0-260（PAG264、短期層の小さいノート）角の写像 A_N → A_M（方向 γ の立て直しの推薦案。著者の採用 2026-11-19 09:37。基礎文書の第5章・第6章 6.3 の材料）：'
 'N ∣ M のとき φ(S) = (N/M)·π^* ∘ S ∘ π_*（読みでは ι S ι^†）は A_N を A_M に送る非単位的な代数準同型（gcd(N, M/N) によらない。N < M なら φ(1) ≠ 1）。φ(E_s) = E_{(M/N)s}、φ(1) = Σ_{s∣M, (M/N)∣s} E_s、'
 '引き戻しと両立、一意性（(a) 引き戻しとの両立と (b) φ(1) の値の 2 条件で）、合成（恒等の法則と極限は Lean の外）。D 側は殻の span に入らない（(2,4) の証人）。ラベル：E 側の像は［既知］（商スキームのべき等元による角）、他は［再導出（小さい）］。像が角全体であることは Lean の外')
R=[
('fsum_add','繊維の和 fsum（def：π_* g(x) = Σ_{π y = x} g(y)、π : ℤ/M → ℤ/N）は和を保つ','和の分配','Finset.sum_add_distrib'),
('fsum_smul','fsum はスカラー倍を保つ','和の分配','Finset.mul_sum'),
('card_fiber','π のどの繊維もちょうど M/N 個の元を持つ','核の平行移動と Part 197 の card_ker_cast','PAG.Part201.card_ker_cast, Finset.card_map'),
('fsum_pull','π_*(π^* f) = (M/N)·f','card_fiber','Finset.sum_const'),
('cornerOp_apply','角の写像 cornerOp（def：φ(S) = (N/M)·π^* ∘ S ∘ π_*。pullLin・fsumLin は def）の値','rfl（機械的な照合で Part 197 の pull_smul と一致と出たが、どちらも定義の展開で等しい式）','—'),
('scal_cancel','(N/M)(M/N) = 1（補助）','field_simp','—'),
('cornerOp_pull','引き戻しと両立：φ(S) π^* = π^* S（S ∈ End(ℂ^{ℤ/N}) 全体）','fsum_pull','—'),
('cornerOp_mul','φ は積を保つ','fsum_pull','—'),
('cornerOp_add','φ は和を保つ','各点で','—'),
('cornerOp_smul','φ はスカラー倍を保つ','各点で','smul_comm'),
('cornerOp_zero','φ(0) = 0','cornerOp_smul','—'),
('cornerOp_one_mul','φ(1)φ(S) = φ(S)（像は φ(1) の角に入る）','cornerOp_mul','—'),
('cornerOp_mul_one','φ(S)φ(1) = φ(S)','cornerOp_mul','—'),
('cornerOp_injective','φ は単射','引き戻しの単射性（Part 259 の pull_injective\'。内部照合で使う形に直した）','PAG.Part263.pull_injective\''),
('fsum_single','1 点の関数の繊維の和','和の中の 1 点','Finset.sum_pi_single\''),
('cornerOp_one_single','φ(1)(δ₀)(0) = N/M','fsum_single','—'),
('cornerOp_one_ne_one','N < M なら φ(1) ≠ 1（非単位的）','cornerOp_one_single','Nat.cast_injective'),
('pull_fsum','M = Nt で π^*(π_* g) = t·P g（P は Part 202 の旧部分への射影 oldP）','x − y への並べ替え、N ∣ (x − z).val ⇔ π z = π x','Fintype.sum_equiv, ZMod.natCast_eq_zero_iff'),
('cornerOp_one_apply','M = Nt で φ(1) = P','pull_fsum','—'),
('conv_geps_oldP','ε_{ts} ⋆ P g = ε_{ts} ⋆ g（M = Nt）','フーリエ側：dind_{ts} の台は t の倍数の上','PAG.Part206.dft_oldP, PAG.Part205.dft_geps'),
('cornerOp_geps_mul','M = Nt で φ(E_s) = E_{ts}','Part 202 の geps_conv_pull と pull_fsum','PAG.Part206.geps_conv_pull'),
('cornerOp_one','φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s（一般の N ∣ M）','M = Nt に書き、Part 202 の oldP_eq_sum','PAG.Part206.oldP_eq_sum'),
('cornerOp_geps','φ(E_s) = E_{(M/N)s}（一般の N ∣ M）','M = Nt に書く','—'),
('pull_dind','π^* 1_{D_s} = Σ_{u ∣ M, gcd(u, N) = s} 1_{D_u}','gcd(N, y mod N) = gcd(gcd(M, y), N)','Nat.gcd_rec, Nat.gcd_assoc, ZMod.val_natCast'),
('mulLeft_sum','掛け算の作用素は有限和を保つ（補助）','各点で','Finset.sum_mul'),
('mulLeft_pull_dind_mem','π^* 1_{D_s} の掛け算は A_M に入る','pull_dind と Part 228 の mulLeft_dind_mem','PAG.Part232.mulLeft_dind_mem'),
('cornerOp_dind','φ(D_s) = (π^* 1_{D_s} の掛け算)·φ(1)','各点で','—'),
('cornerOp_one_mem','φ(1) ∈ A_M','cornerOp_one と Part 228 の convL_geps_mem','PAG.Part232.convL_geps_mem'),
('cornerOp_mem','φ は A_N を A_M に送る（gcd(N, M/N) は仮定にない）','生成元についての帰納法','Algebra.adjoin_induction'),
('cornerHom_coe','角の写像 cornerHom（def：A_N →ₙₐ[ℂ] A_M、非単位的な代数準同型。型は単位元の保存を課さない）の値','rfl','—'),
('existsUnique_corner','一意性：(a) 引き戻しと両立し、(b) φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s を満たす非単位的な代数準同型 A_N → A_M は（→ₙₐ の中で）ちょうど 1 つ（(b) を外すと、(a) を外すと、積を保つことを外すと一意でない：独立照合の手計算の反例、Lean にしていない）','φ(S) = φ(S)φ(1) と (a)(b)','NonUnitalAlgHom.ext'),
('fsum_trans','繊維の和の合成：π_{L→N *} = π_{M→N *} ∘ π_{L→M *}','繊維ごとの和','Finset.sum_fiberwise_of_maps_to, ZMod.castHom_comp'),
('cornerOp_comp','合成：N ∣ M ∣ L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}（恒等の法則 φ_{N,N} = id は Lean の外）','Part 259 の pull_pull（内部照合で下書きの pull_trans を消した）と fsum_trans','PAG.Part263.pull_pull'),
('cornerHom_comp','合成（非単位的な代数準同型として）','cornerOp_comp','NonUnitalAlgHom.ext'),
('cornerHom_injective','cornerHom は単射','cornerOp_injective','—'),
('cornerHom_one_ne_one','N < M なら cornerHom(1) ≠ 1','cornerOp_one_ne_one','—'),
('cornerOp_dind_not_mem_span','(N, M) = (2, 4)：φ(D_2) は D_t の線形結合でない（Part 258 の強い読みの D 側を満たさない。N ∣ M、N < M ならすべての s ∣ N で起きる：数値 81 組、(1,2)・(2,6) は手計算。Lean にあるのは (2,4)・s = 2 だけ）','δ₀ を当てて点 2 の値 1/2（Part 258 の exists_mulLeft_of_mem_span を使う形。内部照合で補助の補題を消した）','PAG.Part262.exists_mulLeft_of_mem_span'),
]
assert len(R)==37
start=3669
ws.insert_rows(start,len(R))
for k,(name,claim,proof,ml) in enumerate(R):
    r=start+k
    for c,v in enumerate([LABEL,name,claim,proof,ml,'検証完了（axioms 確認済み）'],1):
        cell=ws.cell(r,c); cell.value=v; s=ws.cell(3668,c)
        if s.has_style:
            cell.font=copy.copy(s.font); cell.alignment=copy.copy(s.alignment); cell.border=copy.copy(s.border); cell.fill=copy.copy(s.fill)
last=start+len(R)-1
for r in range(last+1, ws.max_row+1):
    v=ws.cell(r,1).value
    if isinstance(ws.cell(r,2).value,str) and ws.cell(r,2).value.startswith('=COUNTIF'):
        ws.cell(r,2).value=f'=COUNTIF($F$2:$F${last},A{r})'
    if isinstance(v,str) and v.startswith('メモ'):
        old='Part 259（行 3602〜3668、PAG263.lean）'; assert old in v, v[-600:]
        v=v.replace(old,f'Part 259（行 3602〜3668、PAG263.lean）、Part 260（行 3669〜{last}、PAG264.lean、短期層）',1)
        v=v.rstrip()+(f' 2026-11-19、Part 260（PAG264.lean、短期層の小さいノート、方向 γ の立て直しの推薦案を著者が採用）を同じ環境でコンパイルし、行 3669〜{last} を足した（定理 37 個）。'
         '閉じる前の内部照合で、下書きの pull_trans（Part 259 の pull_pull と向きが逆の同じ文）と apply_single_two_of_mem_span（Part 258 の exists_mulLeft_of_mem_span から直ちに出る）を消し、単射を Part 259 の pull_injective\' から出す形に直した。')
        ws.cell(r,1).value=v
ws2=wb['検証手順']
ws2.insert_rows(283,1)
for c in range(1,5):
    s=ws2.cell(282,c); d=ws2.cell(283,c)
    if s.has_style:
        d.font=copy.copy(s.font); d.alignment=copy.copy(s.alignment); d.border=copy.copy(s.border); d.fill=copy.copy(s.fill)
ws2.cell(283,1).value=282
ws2.cell(283,2).value='PAG 2.0 Part 260（短期層）: PAG264.lean（角の写像 A_N → A_M：φ(S) = (N/M)·π^* ∘ S ∘ π_* は非単位的な代数準同型、φ(E_s) = E_{(M/N)s}、φ(1) = Σ E_t、引き戻しと両立、一意性、合成、D 側の (2,4) の証人）をコンパイル'
ws2.cell(283,3).value='完了'
ws2.cell(283,4).value=('2026-11-19、方向 γ の立て直しの推薦案（著者の採用 09:37）。数値は records/gamma_corner/（M ≤ 30 の 111 組、鎖 276 本、Lean の各文の照合 111 組）。定理 37 個、sorry 0、警告 0、#print axioms 37 行は標準の公理の範囲。'
 '着手前と閉じる前の内部照合（全宣言 4470 件、1740 回と 4468 件、1660 回、言葉の検索）。独立照合（形式文と定義だけ）で偽・空虚な文なし、除去テストの反例を文面に反映し、直した文面を再照合した（7 点の指摘を直した。その後の直しは尾）。')
for row in ws2.iter_rows(min_row=284):
    for c in row:
        if isinstance(c.value,str) and 'COUNTIF($C$2:$C$282' in c.value:
            c.value=c.value.replace('$C$282','$C$283').replace('$A$282','$A$283')
wb.save(p); print('last',last)
