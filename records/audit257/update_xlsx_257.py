import openpyxl, copy
p='/home/claude/out/final78/lean_verification_status.xlsx'
wb=openpyxl.load_workbook(p); ws=wb['定理と証明']
LABEL=('PAG2.0-257 互いに素な法の並びの指標の積での、ガウス和と W の分解（成分の τ・W の積と、交差項・符号。読みの問い：∞ を含む各点の局所因子の積に分かれるか）'
 '（著者が 2026-11-14 20:59 に候補 P1 を選んだ。開始条件 2（方向βの登録ファイルとの突き合わせ）は著者の判断で保留のまま。'
 '既知の事実の Lean 化：互いに素な法でのガウス和の乗法性の繰り返しと、Tate の局所定数の積公式の GL(1)/ℚ の場合（原始・素数冪の成分・ω の正規化・Tate の規約のもとでの同定は盲検と手計算、確信度 中〜高）。'
 '局所定数は Lean にしていない）')
R=[
('lvl_cons','法の並びの積 lvl（def：先頭 × 残りの積）の展開 lvl (a::l) = N_a·lvl l（補助）','定義から rfl',''),
('lvl_eq_prod','lvl l = (l.map N).prod','リストの帰納法','List.map_cons, List.prod_cons'),
('coprime_lvl','N_a が l のすべての N_j と互いに素なら、N_a と lvl l も互いに素（補助）','リストの帰納法','Nat.Coprime.mul_right'),
('gaussSum_listChar','互いに素な法の並びの指標の積 listChar χ l（def：先頭と残りを Part 256 の prodChar でつなぐ、法 lvl l）のガウス和：τ(listChar χ l) = cross χ l·∏_i τ(χ_i)。交差項 cross（def）は漸化式 cross (a::l) = χ_a(lvl l)·listChar l (N_a)·cross l。原始性は要らない','リストの帰納法で Part 189（PAG193）の gaussSum_mul_coprime を繰り返す。法 1 は Part 199（PAG203）の gaussSum_level_one','PAG.Part193.gaussSum_mul_coprime, PAG.Part203.gaussSum_level_one'),
('listChar_natCast','listChar χ l の自然数 n での値は ∏_j χ_j(n)（単数でない n も含む）','帰納法で Part 189 の mul_changeLevel_apply','PAG.Part193.mul_changeLevel_apply, ZMod.cast_natCast'),
('listChar_neg_one','listChar χ l (−1) = ∏_j χ_j(−1)','帰納法で Part 256 の prodChar_neg_one','PAG.Part260.prodChar_neg_one'),
('cross_eq_formI','交差項の形 (I)：並びに重複がなければ cross χ l = ∏_i χ_i(∏_{j≠i} N_j)','帰納法。先頭以外の成分では (a::l).erase i = a :: l.erase i','List.erase_cons_tail, List.prod_map_mul, map_mul'),
('cross_eq_formII','交差項の形 (II)：並びに重複がなければ cross χ l = ∏_i ∏_{j≠i} χ_j(N_i)（成分 i の因子を、ほかの成分を N_i で読んだ値で書く）','帰納法。χ_a(∏ N_i) = ∏ χ_a(N_i)','List.erase_cons_tail, Nat.cast_list_prod, map_list_prod'),
('sqrt_lvl','√(lvl l) = ∏_i √N_i（ℂ で。補助）','帰納法','Real.sqrt_mul, Complex.ofReal_mul'),
('prod_map_div\'','∏_i f_i/g_i = (∏ f_i)/(∏ g_i)（ℂ のリストで。補助）','帰納法','div_mul_div_comm'),
('rootNum_listChar_formII','W の形 (II)：互いに素で重複なしなら W(listChar χ l) = ε_∞·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)。ε_∞ = parFac(listChar χ l)（偶で 1、奇で −i）。原始指標の素数冪の成分では、形 (II) の因子が Tate の局所定数（ω_q(q) = χ(q)、ψ_∞ = e^{−2πix} の規約）と一致する、は盲検と手計算で、Lean の外（原始でない成分では言えない）','Part 252 の rootNum_eq と gaussSum_listChar・cross_eq_formII・sqrt_lvl','PAG.Part256.rootNum_eq'),
('rootNum_listChar_formI','W の形 (I)：互いに素で重複なしなら W(listChar χ l) = ε_∞·∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)/√N_i','rootNum_eq と gaussSum_listChar・cross_eq_formI・sqrt_lvl','PAG.Part256.rootNum_eq'),
('listChar_neg_one_pow','listChar χ l (−1) = (−1)^k（k は奇の成分の数 oddCount（def））','listChar_neg_one と偶奇の場合分け','DirichletCharacter.even_or_odd, DirichletCharacter.Even.not_odd'),
('tri_succ','(1+k)·k/2 = k(k−1)/2 + k（自然数。補助）','k = 0 と k = m+1 に分ける','Nat.add_mul_div_right'),
('parFac_listChar','∞ の因子の符号：ε_∞(listChar χ l) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数）。Part 256 の符号 s の一般化','帰納法で Part 256 の parFac_prodChar・crossSign と listChar_neg_one_pow、tri_succ','PAG.Part260.parFac_prodChar, neg_one_pow_eq_neg_one_iff_odd'),
('rootNum_listChar','W の分解（符号つき）：互いに素なら W(listChar χ l) = (−1)^{k(k−1)/2}·cross χ l·∏_i W(χ_i)（成分 2 つでは、法 N_a·(N_b·1) の上で Part 256 の rootNum_prodChar と同じ式。Lean ではつないでいない）','rootNum_eq・gaussSum_listChar・parFac_listChar・sqrt_lvl','PAG.Part256.rootNum_eq'),
('isPrimitive_listChar_iff','互いに素なら、listChar χ l が原始 ⇔ l のすべての χ_i が原始','帰納法で Part 190（PAG194）の isPrimitive_iff・comp₁_mul・comp₂_mul','PAG.Part194.isPrimitive_iff, DirichletCharacter.isPrimitive_one_level_one'),
('phaseA1_listChar','互いに素で成分がすべて原始なら、phaseA1(listChar χ l) = (−1)^{k(k−1)/2}·cross χ l·∏_i phaseA1(χ_i)（読み：U の固有値も同じ式で分かれる）','Part 254（PAG258）の phaseA1_of_isPrimitive と rootNum_listChar','PAG.Part258.phaseA1_of_isPrimitive'),
('listChar_congr','l の各成分で χ_i = χ\'_i なら listChar χ l = listChar χ\' l（補助）','帰納法',''),
('exists_listChar','分解の存在：互いに素で重複なしなら、法 lvl l の指標はどれも listChar χ l の形に書ける','帰納法で Part 190 の decomp。先頭の成分は Function.update で入れる','PAG.Part194.decomp, Function.update_self, Function.update_of_ne'),
('listChar_injective','分解の一意性：互いに素なら、listChar χ l = listChar χ\' l のとき l の各成分で χ_i = χ\'_i','帰納法で Part 232（PAG236）の charMul_injective（Part 256 の prodChar は Part 232 の charMul と同じ定義）','PAG.Part236.charMul_injective'),
('gaussSum_listChar_singleton','退化例（成分 1 つ）：τ(listChar χ [a]) = τ(χ_a)','gaussSum_listChar と、交差項が 1',''),
('pairwise_primeFactors','n の素因数の並び（重複なし）で、p^{v_p(n)} どうしは互いに素（補助）','異なる素数の冪は互いに素','Nat.coprime_primes, Nat.Coprime.pow, List.Pairwise.imp_of_mem'),
('lvl_primeFactors','n ≠ 0 なら、素因数の並びでの lvl（p ↦ p^{v_p(n)}）は n','素因数分解の積の公式','Nat.prod_factorization_pow_eq_self, Finset.prod_map_toList'),
('gaussSum_primeFactors','すべての素数への分解：法 n の指標 Ψ には素数冪の法 p^{v_p(n)} の成分 χ_p があり、自然数 x で Ψ(x) = ∏_p χ_p(x)、τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)})（形 (II)。成分の存在の文で、一意性は listChar_injective の形でだけ言う）','lvl = n を subst で受け渡し、exists_listChar・listChar_natCast・gaussSum_listChar・cross_eq_formII。p^{v_p(n)} ≠ 0 は Part 236（PAG240）の instance neZero_ordProj','PAG.Part240.neZero_ordProj, Nat.prod_factorization_pow_eq_self'),
]
assert len(R)==25
start=3554
ws.insert_rows(start, len(R))
src=3553
for k,(name,claim,proof,mlem) in enumerate(R):
    r=start+k
    vals=[LABEL,name,claim,proof,mlem,'検証完了（axioms 確認済み）']
    for c,v in enumerate(vals,1):
        cell=ws.cell(r,c); cell.value=v
        s=ws.cell(src,c)
        if s.has_style:
            cell.font=copy.copy(s.font); cell.alignment=copy.copy(s.alignment); cell.border=copy.copy(s.border); cell.fill=copy.copy(s.fill); cell.number_format=s.number_format
last=start+len(R)-1
# fix summary formulas
for row in ws.iter_rows(min_row=last+1, max_row=ws.max_row):
    for c in row:
        if isinstance(c.value,str) and c.value.startswith('=COUNTIF($F$2:$F$3553'):
            c.value=c.value.replace('$F$3553',f'$F${last}')
        if isinstance(c.value,str) and c.value.startswith('メモ：'):
            memo_cell=c
memo=memo_cell.value
add=f'、PAG 2.0 Part 257（行 3554〜{last}、PAG261.lean。2026-11-14 夜、著者が候補 P1 を選んだ。開始条件 2 は保留のまま）'
import re
print(memo[-300:])
wb.save(p); print('last',last)
