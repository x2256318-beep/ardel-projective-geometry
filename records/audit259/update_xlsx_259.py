import openpyxl, copy, re
p='/home/claude/out/final80/lean_verification_status.xlsx'
wb=openpyxl.load_workbook(p); ws=wb['定理と証明']
LABEL=('PAG2.0-259 互いに素な段の写像の一意性と帰納系の添字（基礎文書の骨格の第5章、方向ラウンド (b) の R1。著者の指示 2026-11-15「Lean」）：'
 'N ∣ M のとき、Part 258 の (i)(ii) に (iii) フーリエとの両立を足した条件を満たす代数準同型 A_N → A_M がちょうど 1 つある ⇔ gcd(N, M/N) = 1（それは shellLift）。'
 '(iii) を外すと a = 2 で一意でない（a が奇数では数値の上で一意）。標準の写像は合成と両立するが、互いに素な段の順序は有向でない（p と p²）。無平方数の段は帰納系をなす。ラベルは［再導出（小さい）］の見込み、文献照合は未了')
R=[
('udvd_refl','互いに素な段の順序 UDvd（def：N ∣ M かつ gcd(N, M/N) = 1。古典的なユニタリ約数 N ∥ M、Cohen 1960）は反射的（N > 0）','N/N = 1','Nat.div_self'),
('udvd_trans','UDvd は推移的','M = Na、L = Nab と書き、gcd(N, ab) = 1','Nat.Coprime.mul_right, Nat.Coprime.coprime_dvd_left'),
('udvd_iff_inLayer','UDvd N M ⇔ Part 216 の層 InLayer N N M（N > 0。内部照合で見つけた同じ概念）','定義を開く','Nat.mul_div_cancel_left'),
('not_udvd_and_udvd_sq','素数 p で UDvd p M と UDvd p² M は同時に成り立たない','M = p²k なら M/p = pk で gcd(p, pk) = p','Nat.Coprime.eq_one_of_dvd'),
('not_directed_udvd','有向でない：p と p² の両方の上に来る互いに素な段はない','上の補題','—'),
('not_isDirected_udvd','有向でない：ℕ の上の UDvd は有向でない（照合 B の指摘で追加）','p = 2 の場合','IsDirected.directed'),
('shellAlg_hom_ext','生成元 D_s・E_s で一致する A_N からの代数準同型は等しい','等化子の部分代数が生成元を含む','AlgHom.equalizer, Algebra.adjoin_le'),
('pull_pull','引き戻しの合成：π_{M→L}^* π_{N→M}^* = π_{N→L}^*','Part 192 の castHom_castHom（内部照合）','PAG.Part196.castHom_castHom'),
('pull_self','N → N の引き戻しは恒等（補助）','castHom_self','ZMod.castHom_self'),
('pull_one','定数 1 の引き戻しは 1（補助）','rfl','—'),
('compat_dind_unique','(i) と (ii) の D の側から φ(D_s) は一意に決まる（文は N ∣ M だけを仮定。gcd(N, M/N) ≠ 1 で前提を満たす写像があるかは未確認）','φ(D_s) は掛け算の作用素 g・、(i) を定数 1 に当てると g = π^*(D_s 1)','PAG.Part262.exists_mulLeft_of_mem_span'),
('fC_coe','fC（def：Part 242 の fourierConj を A_N に制限した代数同型）の値（補助）','rfl','AlgEquiv.subalgebraMap'),
('fC_dind','fC(D_s) = E_s','Part 242 の fourierConj_mulLeft_dind','PAG.Part246.fourierConj_mulLeft_dind'),
('fC_geps','fC(E_s) = D_s','Part 242 の fourierConj_convL_geps','PAG.Part246.fourierConj_convL_geps'),
('compatF_unique','一意性：(i)(ii)(iii)（CompatF、def。Compat は Part 258 の (i)(ii)、def）を満たす代数準同型は高々 1 つ（φ(D_s) の一意性を (iii) で運ぶだけの、ほぼ即座の帰結）','D の側は compat_dind_unique、E_s = fC(D_s) と (iii)、生成元で一致','shellAlg_hom_ext'),
('fourierConj_mem_spanE','フーリエ共役は D_t の張る空間を E_t の張る空間に移す（補助）','span の像','Submodule.map_span'),
('compatF_of_dind','(ii) の E の側は余分：(i)、(ii) の D の側、(iii) から CompatF が出る（照合 B の指摘で追加）','φ(E_s) = fC(φ(D_s))','fourierConj_mem_spanE'),
('dsub_eq_zero','s ∤ N なら D_s = 0（補助）','Part 228 の dind_eq_zero_of_not_dvd','PAG.Part232.dind_eq_zero_of_not_dvd'),
('esub_eq_zero','s ∤ N なら E_s = 0（補助）','Part 228 の geps_eq_zero_of_not_dvd','PAG.Part232.geps_eq_zero_of_not_dvd'),
('shellLift_fC','shellLift（Part 258）はフーリエと両立する','生成元で：fourierConj が Σ D_{su} と Σ E_{su} を入れ替える','PAG.Part262.shellLift_dind, PAG.Part262.shellLift_geps'),
('compatF_shellLift','shellLift は (i)(ii)(iii) を満たす','Part 258 の shellLift_pull と上','PAG.Part262.shellLift_pull'),
('compatF_iff_eq_shellLift','gcd(a, b) = 1 なら、(i)(ii)(iii) を満たす A_a → A_{ab} は shellLift だけ','一意性と上','—'),
('existsUnique_compatF_iff','一意な存在の二分法：N ∣ M のとき、(i)(ii)(iii) を満たす代数準同型がちょうど 1 つ ⇔ gcd(N, M/N) = 1（互いに素でないときは (i)(ii) を満たすものが 1 つもない）','⇒ は Part 258 の二分法、⇐ は shellLift と一意性','PAG.Part262.exists_compatible_hom_iff'),
('map_mem_spanD','D の生成元を D の張る空間に送る準同型は、その空間の元も送る（補助）','span の像','Submodule.map_span'),
('map_mem_spanE','E について同じ（補助）','span の像','Submodule.map_span'),
('compatF_comp','合成：(i)(ii)(iii) は合成で保たれる','引き戻しの合成と span の補題','pull_pull'),
('compatF_id','恒等写像は (i)(ii)(iii) を満たす','pull_self','—'),
('compatF_canon','互いに素な段の標準の写像 canon（def：一意な存在から選んだもの）は (i)(ii)(iii) を満たす','選択の性質','Exists.choose_spec'),
('canon_eq_shellLift','canon は shellLift に等しい','一意性','—'),
('canon_self','φ_{N,N} = id','一意性','—'),
('canon_comp','帰納系：互いに素な段 N → M → L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}','合成と一意性','udvd_trans'),
('esub_mul_esub','E_s E_t = [s = t] E_s（A_N の中で、補助）','Part 85（PAG89）の結合法則と Part 201 の geps_conv_geps','PAG.Part205.geps_conv_geps'),
('conv_geps_self_const','E_N は定数関数を保つ（補助）','Part 239 の geps_self','PAG.Part243.geps_self'),
('chi2_mul_self','χ(x) = (−1)^x（chi2、def、ℤ/2 上）で χ² = 1（補助）','場合分け','—'),
('chiConj_apply','χ による共役 chiConj（def、chiMul は χ を掛ける線形同型、def）の値（補助）','rfl','LinearEquiv.conjAlgEquiv'),
('chiConj_mulLeft','χ の共役は掛け算の作用素を固定する','可換性と χ² = 1','—'),
('chiConj_chiConj','χ の共役は対合','χ² = 1','—'),
('convL_geps_two_one','E_1 = 1 − E_2（N = 2）','Part 228 の sum_convL_geps','PAG.Part232.sum_convL_geps'),
('sum_zmod2','ℤ/2 上の和は 2 項（補助）','Fin.sum_univ_two','Fin.sum_univ_two'),
('chiConj_geps_two','χ E_2 χ⁻¹ = E_1','ℤ/2 の 2 点で計算（E_2 は定数 1/2 の畳み込み）','PAG.Part243.geps_self'),
('chiConj_geps_one','χ E_1 χ⁻¹ = E_2','共役は対合','—'),
('map_chiConj_le','χ の共役は A_2 を保つ（補助）','生成元の像','AlgHom.map_adjoin'),
('twist2_coe','A_2 の自己準同型 ψ = twist2（def）の値（補助）','rfl','AlgHom.codRestrict'),
('twist2_twist2','ψ は対合（照合 B の指摘で追加）','chiConj_chiConj','—'),
('twist2_bijective','ψ は全単射（A_2 の自己同型）','対合','Function.Involutive.bijective'),
('twist2_dind','ψ(D_s) = D_s','chiConj_mulLeft','—'),
('twist2_geps_one','ψ(E_1) = E_2','chiConj_geps_one','—'),
('twist2_geps_two','ψ(E_2) = E_1','chiConj_geps_two','—'),
('eTop_const','E_b（Part 258 の eTop）は定数を保つ（補助）','conv_geps_self_const','—'),
('one_sub_eTop_const','1 − E_b は定数を 0 に送る（補助）','上','—'),
('one_sub_eTop_eq','1 − E_b = 1 + (−1)·E_b（A_b の中で、補助）','係数への移行','—'),
('twTensLin_apply','線形写像 S ↦ S ⊗ E_b + ψ(S) ⊗ (1 − E_b)（twTensLin、def）の値（補助）','rfl','TensorProduct.mk'),
('twTens_apply','代数準同型 twTens（def）の値（補助）','rfl','AlgHom.ofLinearMap'),
('twLift_apply','捩れた写像 twLift（def：φ\'(S) = Θ(S ⊗ E_b + ψ(S) ⊗ (1 − E_b))、Θ は Part 228）の値（補助）','rfl','—'),
('twLift_pull','φ\' は (i) を満たす','CRT の座標で：E_b は定数を保ち 1 − E_b は消す','PAG.Part232.crtConj_shellAlgTensorEquiv, PAG.Part262.crtLin_pull'),
('twLift_dind','φ\'(D_s) = shellLift(D_s)','ψ(D_s) = D_s','—'),
('twist2_geps','ψ(E_s) はある E_t（補助）','s = 1, 2 とそれ以外（E_s = 0）','—'),
('tensor_eTop_mem_spanE','Θ(E_t ⊗ E_b) は E の張る空間に入る（補助）','Part 228 の shellAlgTensorEquiv_geps','PAG.Part232.shellAlgTensorEquiv_geps'),
('compat_twLift','φ\' は Part 258 の (i)(ii) を満たす','φ\'(E_s) = Θ(E_s ⊗ E_b) + shellLift(E_t) − Θ(E_t ⊗ E_b)','—'),
('convL_geps_one_ne_zero','E_1 ≠ 0（補助）','フーリエ共役で D_1、点 1 で値 1','PAG.Part246.fourierConj_convL_geps'),
('twLift_ne_shellLift','1 < b なら φ\' ≠ shellLift','E_1 ⊗ E_1 を右から掛けると φ\'(E_1) 側は 0、shellLift(E_1) 側は E_1^{(2b)} ≠ 0','esub_mul_esub'),
('not_existsUnique_compat','(iii) を外すと一意でない場合がある（a = 2 の例）：gcd(2, b) = 1、1 < b のとき、(i)(ii) を満たす A_2 → A_{2b} は一意でない（数値では a が奇数なら (i)(ii) だけで一意、Lean にしていない）','shellLift と φ\'','—'),
('pull_injective\'','引き戻しは単射（N ∣ M）','Part 202 の pull_injective（内部照合）','PAG.Part206.pull_injective'),
('compat_injective','(i)(ii)（Compat）を満たす写像は単射（証明は (i) だけを使う）','引き戻しの単射性','—'),
('primeProd_pos','素数の有限集合の積 N_S（primeProd、def）は正（補助）','Finset.prod_pos','Finset.prod_pos'),
('primeProd_udvd','S ⊆ T なら N_S → N_T は互いに素な段','N_T = N_{T∖S}·N_S、異なる素数は互いに素','Finset.prod_sdiff, Nat.coprime_primes'),
('sqLim_of_injective','無平方数の段の帰納極限 sqLim（abbrev、ℂ 加群。標準の写像 sqMap（def）による帰納系、DirectedSystem のインスタンス）に各 A_{N_S} は単射で入る','compat_injective','Module.DirectLimit.exists_eq_of_of_eq'),
]
print(len(R))
start=3602
ws.insert_rows(start,len(R))
for k,(name,claim,proof,ml) in enumerate(R):
    r=start+k
    for c,v in enumerate([LABEL,name,claim,proof,ml,'検証完了（axioms 確認済み）'],1):
        cell=ws.cell(r,c); cell.value=v; s=ws.cell(3601,c)
        if s.has_style:
            cell.font=copy.copy(s.font); cell.alignment=copy.copy(s.alignment); cell.border=copy.copy(s.border); cell.fill=copy.copy(s.fill)
last=start+len(R)-1
for r in range(last+1, ws.max_row+1):
    v=ws.cell(r,1).value
    if isinstance(ws.cell(r,2).value,str) and ws.cell(r,2).value.startswith('=COUNTIF'):
        ws.cell(r,2).value=f'=COUNTIF($F$2:$F${last},A{r})'
    if isinstance(v,str) and v.startswith('メモ'):
        old='Part 258（行 3579〜3601、PAG262.lean）。'; assert old in v, v[-500:]
        v=v.replace(old,f'Part 258（行 3579〜3601、PAG262.lean）、Part 259（行 3602〜{last}、PAG263.lean）。')
        v=v.rstrip()+(f' 2026-11-15、Part 259（PAG263.lean、著者の指示「Lean」）を同じ環境でコンパイルし、行 3602〜{last} を足した（定理 67 個）。'
         '閉じる前の内部照合で、pull_injective\' を Part 202 の pull_injective から、pull_pull を Part 192 の castHom_castHom から出す形に直し、UDvd と Part 216 の InLayer の一致（udvd_iff_inLayer）を足した。')
        ws.cell(r,1).value=v
ws2=wb['検証手順']
ws2.insert_rows(282,1)
for c in range(1,5):
    s=ws2.cell(281,c); d=ws2.cell(282,c)
    if s.has_style:
        d.font=copy.copy(s.font); d.alignment=copy.copy(s.alignment); d.border=copy.copy(s.border); d.fill=copy.copy(s.fill)
ws2.cell(282,1).value=281
ws2.cell(282,2).value='PAG 2.0 Part 259: PAG263.lean（互いに素な段の写像：(iii) フーリエとの両立を足すと一意（shellLift）、外すと a = 2 で一意でない、合成との両立、順序が有向でないこと、無平方数の段の帰納系）をコンパイル'
ws2.cell(282,3).value='完了'
ws2.cell(282,4).value=('2026-11-15、Part 259（R1 の査定の数値 uniq.py・aut.py・fourier.py の主張を Lean に）。定理 67 個、sorry 0、警告 0、#print axioms 67 行は標準の公理の範囲。'
 '着手前と閉じる前の内部照合（全宣言 4424 件、3440 回と、言葉の検索）。独立照合 B の後に 6 つの定理（有向でないこと、(ii) の E の側が余分なこと、ψ が対合で全単射なこと）を足し、ヘッダの言い過ぎを直した。')
for row in ws2.iter_rows(min_row=283):
    for c in row:
        if isinstance(c.value,str) and 'COUNTIF($C$2:$C$281' in c.value:
            c.value=c.value.replace('$C$281','$C$282').replace('$A$281','$A$282')
wb.save(p); print('last',last)
