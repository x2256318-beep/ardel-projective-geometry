p = '/home/claude/leanwork/pagpkg/PAG258.lean'
s = open(p, encoding='utf-8').read()
REP = [
 ('''5. 原始的でない部分では U_N ≠ T：素数 p の自明な指標で U(1) = 1、T(1) = W(1)·1、|W(1)|² = 1/p（`UA1_ne_TopL_prime`）。''',
  '''5. 原始的でない部分では U_N ≠ T：素数 p では自明な指標は V_imprim に入り、U_p(1) ≠ T_p(1)（`UA1_ne_TopL_prime`）。
   値（U(1) = 1、T(1) = W(1)·1、|W(1)|² = 1/p）は `phaseA1_one`・`UA1_charU` と Part 253 の `TopL_charU`・
   `normSq_rootNum_one_prime` から。'''),
 ('''   正定値（`ipLim_self_nonneg`・`eq_zero_of_ipLim_self`）。U_∞ はこれを保つ（`ipLim_Uinf`）。''',
  '''   正値（`ipLim_self_nonneg`）と定値性（`eq_zero_of_ipLim_self`：⟨z, z⟩ = 0 なら z = 0）。U_∞ はこれを保つ（`ipLim_Uinf`）。'''),
 ('''   独立（`iSupIndep_condPart`）。つまり単数の上の関数の空間は ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和。U_M は各部分を
   保ち（`UA1_mem_condPart`）、その上で π∘T_q（`UA1_pullL_of_mem_Vprim`：g ∈ V_prim(q) なら U_M(π g) = π(T_q g)）。
   極限でも、導手の違う原始部分の像は直交する（`ipLim_ofL_Vprim`）。''',
  '''   独立（`iSupIndep_condPart`）。添字は q ∈ ℕ 全体で、q ∤ M の部分が 0 であることは文にしていない。合わせると
   ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和になるが、1 つの定理にはしていない。U_M は各部分を保ち（`UA1_mem_condPart`）、
   原始部分の引き戻しの上で π∘T_q（`UA1_pullL_of_mem_Vprim`：q ∣ M、g ∈ V_prim(q) なら U_M(π g) = π(T_q g)）。
   極限では、導手の違う原始部分の像は直交する（`ipLim_ofL_Vprim`。前ヒルベルト空間での直交。極限での独立性と、
   U_∞ が各部分を保つことは文にしていない）。'''),
 ('''していない。
-/''',
  '''していない。10 について：q ∤ M の部分が 0 であること、直和を 1 つの文（DirectSum.IsInternal）にすること、極限での
独立性、U_∞ が各部分を保つことは Lean にしていない。
-/'''),
 ('/-- **指標ごとの式**（直和の文の指標ごとの形。直和そのものは §8）：',
  '/-- **指標ごとの式**（直和の文の指標ごとの形。直和の部品は冒頭の説明の 10）：'),
 ('/-- 素数 p の自明な指標の W は −1/√p（実数で負）。法 p の T の極分解のユニタリ因子なら、この指標での固有値は −1\n（U_p の固有値は 1）。 -/',
  '/-- 素数 p の自明な指標の W は −1/√p（実数で負）。法 p の T の極分解のユニタリ因子なら、この指標での固有値は −1\n（U_p の固有値は 1）。極分解そのものは Lean にしていない。 -/'),
 ('/-- 極限の内積の正定値性：⟨z, z⟩ = 0 なら z = 0。 -/',
  '/-- 極限の内積の定値性：⟨z, z⟩ = 0 なら z = 0（正値は `ipLim_self_nonneg`）。 -/'),
 ('/-- 新しい部分の上の U_N：q ∣ M、g ∈ V_prim(q) なら U_M(π g) = π(T_q g)。 -/',
  '/-- 新しい部分の上の U_M：q ∣ M、g ∈ V_prim(q) なら U_M(π g) = π(T_q g)（左辺の U は法 M、右辺の T は法 q）。 -/'),
 ('/-- 導手ごとの部分は独立（直和）。 -/',
  '/-- 導手ごとの部分は独立（内部直和の独立性。添字は q ∈ ℕ 全体）。 -/'),
]
for a, b in REP:
    assert s.count(a) == 1, (s.count(a), a[:60])
    s = s.replace(a, b)
open(p, 'w', encoding='utf-8').write(s)
print('ok')
