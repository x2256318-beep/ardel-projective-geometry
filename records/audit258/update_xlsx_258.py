import openpyxl, copy
p='/home/claude/out/final79/lean_verification_status.xlsx'
wb=openpyxl.load_workbook(p); ws=wb['定理と証明']
LABEL=('PAG2.0-258 N ∣ M のとき、(i) φ(S)π^* = π^*S、(ii) φ(D_s)・φ(E_s) が D_t・E_t の線形結合、を満たす単位的な代数準同型 A_N → A_M（A_N は Part 214 の shellAlg、'
 'Terwilliger 代数 T(0) にあたる）がある ⇔ gcd(N, M/N) = 1（登録の言葉では方向βの前提の判定。著者側の補足7 の決定。登録の受容条件を (1) 単位元を保つ代数準同型、'
 '(2) φ(S)π^* = π^*S、(3) φ(D_s)・φ(E_s) は D・E の線形結合（強い読み）と読んだ。存在の側のテンソル積は既知（Hanaki–Kim–Maekawa Theorem 3.1、鎖の Part 228。作用素は Part 236 の locHom の k = 0 と同じ式）。'
 '不存在の側は盲検で文献が見つからなかった（確信度 中）。ラベルは著者の判断事項）')
R=[
('shellLift_apply','互いに素な a, b で φ = shellLift（def：S ↦ Θ(S ⊗ 1)、Θ は Part 228 の shellAlgTensorEquiv）の値（補助）','定義から rfl',''),
('crtConj_shellLift','CRT の共役で φ(S) は L(S)（第 1 座標への作用）に移る','Part 228 の crtConj_shellAlgTensorEquiv_tmul の T = 1 の場合（内部照合：そこから直ちに出る、B）と Part 247 の rightOp_one\'','PAG.Part232.crtConj_shellAlgTensorEquiv_tmul, PAG.Part251.rightOp_one\''),
('castHom_crt_symm','CRT の逆の点の法 a への還元は第 1 成分（補助）','Part 236 の crt_fst_eq_castHom から直ちに出る（内部照合）','PAG.Part240.crt_fst_eq_castHom'),
('crtLin_pull','ℤ/ab → ℤ/a の引き戻しを CRT の座標で見ると第 1 座標だけの関数（補助）','castHom_crt_symm','PAG.Part232.crtLin_apply'),
('shellLift_pull','条件 2（射影と両立）：φ(S)(π^* f) = π^*(S f)','crtLin で移して L(S) の値を計算','PAG.Part232.crtConj_apply, PAG.Part232.leftOp_apply'),
('shellLift_dind','条件 3（D）：s ∣ a で φ(D_s) = Σ_{u ∣ b} D_{su}','A_b の 1 = Σ D_u と Part 228 の shellAlgTensorEquiv_dind','PAG.Part232.sum_mulLeft_dind, TensorProduct.tmul_sum'),
('shellLift_geps','条件 3（E）：s ∣ a で φ(E_s) = Σ_{u ∣ b} E_{su}','A_b の 1 = Σ E_u と Part 228 の shellAlgTensorEquiv_geps','PAG.Part232.sum_convL_geps, TensorProduct.tmul_sum'),
('shellLift_injective','φ は単射','L の単射性（Part 228 の leftHom_injective）','PAG.Part232.leftHom_injective'),
('exists_compatible_hom','存在：gcd(a, b) = 1 なら、条件 (1)〜(3)（(3) は span{D_t}・span{E_t} への所属）を満たす代数準同型 A_a → A_{ab} がある','shellLift と上の 3 つ。s ∤ a の生成元は 0','Submodule.subset_span, Submodule.sum_mem'),
('conv_single','g ⋆ δ₀ = g（補助）','Part 107 の conv_single_gen と Part 15 の conv_comm','PAG.Part111.conv_single_gen, PAG.Part15.conv_comm'),
('dTop_eTop_dTop','A_N の関係：D_N E_N D_N = (1/N) D_N（D_N = {0} の指示関数の掛け算 dTop（def）、E_N = 定数 1/N の畳み込み eTop（def））。Part 247 の E_N D_N E_N = (1/N) E_N と対の式','点 0 で場合分け。ε_N = 1/N は Part 239 の geps_self','PAG.Part251.dind_self_apply, PAG.Part243.geps_self'),
('eTop_mul_self','E_N はべき等','Part 89 の結合法則と Part 201 の geps_conv_geps','PAG.Part89.conv_assoc\', PAG.Part205.geps_conv_geps'),
('exists_mulLeft_of_mem_span','D_t の線形結合は掛け算の作用素（補助）','span ⊆ LinearMap.mul の像','Submodule.span_le'),
('exists_convL_of_mem_span','E_t の線形結合は ε の線形結合 g の畳み込み（補助）','span の像 = 像の span','Submodule.span_image'),
('dft_const_on_shells','ε の線形結合のフーリエ変換は双対殻の上で定数（gcd(M, ξ) だけで決まる）','span の帰納法と dft_geps','Submodule.span_induction, PAG.Part205.dft_geps'),
('mem_ker_iff','核 ker(ℤ/M → ℤ/N) の元は N の倍数（補助）','cast と val','ZMod.natCast_eq_zero_iff'),
('sum_ker_stdAddChar','核 H の上の指標の和：Σ_{y∈H} e(ay/M) = [aN = 0]·|H|','a·N = 0 なら各項 1。そうでなければ y ↦ y + N で和が e(aN/M) 倍になる','ZMod.injective_stdAddChar, Finset.sum_equiv'),
('p_dvd_div_p','p ∣ N、p ∣ M/N なら p ∣ M/p（補助）','p² ∣ M','Nat.dvd_div_of_mul_dvd'),
('sq_x_eq_zero','x = M/p（ℤ/M の中）で x² = 0（補助）','p ∣ M/p','ZMod.natCast_eq_zero_iff'),
('x_mul_N','x·N = 0（p ∣ N）（補助）','M/p·N = M·(N/p)','ZMod.natCast_eq_zero_iff'),
('mul_x_ne_zero','(ξ − 1)·N = 0 なら ξ·x ≠ 0（p ∤ ξ）（補助）','整数に上げて p ∣ ξ と p ∣ ξ − 1 から矛盾','ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.dvd_of_mul_dvd_mul_left'),
('no_compatible_hom','不存在：素数 p が N と M/N の両方を割るなら、条件 (1)〜(3) を満たす代数準同型 A_N → A_M はない','φ(D_N) は核の指示関数、φ(E_N) の 𝓕 は双対殻で定数かつ 0・1 値。関係から ξ ≡ 1 (mod M/N) の剰余類に点がちょうど 1 つ。単数 1 + M/p で 2 つになり矛盾','PAG.Part207.gcd_val_unit_mul, PAG.Part201.card_ker_cast, ZMod.invDFT_apply'),
('exists_compatible_hom_iff','二分法：N ∣ M のとき、条件 (1)〜(3) を満たす代数準同型 A_N → A_M がある ⇔ gcd(N, M/N) = 1','no_compatible_hom と exists_compatible_hom','Nat.exists_prime_and_dvd'),
]
assert len(R)==23
start=3579
ws.insert_rows(start,len(R))
for k,(name,claim,proof,ml) in enumerate(R):
    r=start+k
    for c,v in enumerate([LABEL,name,claim,proof,ml,'検証完了（axioms 確認済み）'],1):
        cell=ws.cell(r,c); cell.value=v; s=ws.cell(3578,c)
        if s.has_style:
            cell.font=copy.copy(s.font); cell.alignment=copy.copy(s.alignment); cell.border=copy.copy(s.border); cell.fill=copy.copy(s.fill)
last=start+len(R)-1  # 3602
for r in range(last+1, ws.max_row+1):
    v=ws.cell(r,1).value
    if isinstance(ws.cell(r,2).value,str) and ws.cell(r,2).value.startswith('=COUNTIF'):
        ws.cell(r,2).value=f'=COUNTIF($F$2:$F${last},A{r})'
    if isinstance(v,str) and v.startswith('メモ'):
        old='Part 257（行 3554〜3578、PAG261.lean）。'; assert old in v
        v=v.replace(old,f'Part 257（行 3554〜3578、PAG261.lean）、Part 258（行 3579〜{last}、PAG262.lean）。')
        v=v.rstrip()+(f' 2026-11-14 夜〜11-15、Part 258（PAG262.lean、著者側の補足7 の決定）を同じ環境でコンパイルし、行 3579〜{last} を足した。閉じる前の内部照合で下書きの 3 つの宣言（dind_self_apply・rightOp_one・geps_self）が前の鎖と同じ内容だったので消した。独立照合 B の後に pull_one を消した（定理 23 個）。'
         '閉鎖条件の照合（R1〜R4、F3）の直しで、PAG256・257・260・261 の docstring と冒頭の説明、Part 252・253 の行の「最初の形式化の Part n（PAGn.lean）」をそろえた（形式文は変えていない）。')
        ws.cell(r,1).value=v
ws2=wb['検証手順']
ws2.insert_rows(281,1)
for c in range(1,5):
    s=ws2.cell(280,c); d=ws2.cell(281,c)
    if s.has_style:
        d.font=copy.copy(s.font); d.alignment=copy.copy(s.alignment); d.border=copy.copy(s.border); d.fill=copy.copy(s.fill)
ws2.cell(281,1).value=280
ws2.cell(281,2).value='PAG 2.0 Part 258: PAG262.lean（方向βの前提：N ∣ M で、引き戻しと両立し殻を混ぜない代数準同型 A_N → A_M の存在（gcd(N, M/N) = 1）、不存在（素数 p が N と M/N を割る）、二分法）をコンパイル'
ws2.cell(281,3).value='完了'
ws2.cell(281,4).value=('2026-11-14 夜〜11-15、Part 258（著者側の補足7 の決定）。段階 1 の盲検（gcd = 1 のときに限り存在、文献なし）、段階 2 の数値 step281（13 組、二分法と一致）、段階 3 の Lean。'
 '定理 23 個、sorry 0、警告 0、#print axioms 23 行は標準の公理の範囲。閉じる前の内部照合（全宣言 4339 件、1140 回と、言葉の検索）で 3 つの宣言を消し、2 回目（1060 回）は記録した B の 1 組だけ。'
 '閉鎖条件の 4 件（S18〜S50 の逆翻訳 A、記録 §9、重複注記の F2 の後の直し、Part 257 の照合後の直し）を照合して閉じた。')
for row in ws2.iter_rows(min_row=282):
    for c in row:
        if isinstance(c.value,str) and 'COUNTIF($C$2:$C$280' in c.value:
            c.value=c.value.replace('$C$280','$C$281').replace('$A$280','$A$281')
wb.save(p); print('last',last)
