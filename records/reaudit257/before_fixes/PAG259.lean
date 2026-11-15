/-
アーデル射影幾何 — Part 255（PAG 2.0）：§1 の命題 3（解像度と有効な姿）の L1 の読み — 測る素点と、極限の取り方

問いの出所：Part 255 の着手前の文書（`pag2_part255_preregistration.md`）の候補 L1 を、著者が §1 の命題 3 の読みとして
採った（2026-11-13 08:38「L1 で Part 255 を始める」）。L1 は Claude の案で、著者の定義の文面そのものではない。
著者の定義（2026-11-13 08:41、原文）：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。
連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。」

L1：基礎は正の有理数の群（または有限個の素数の集合 S が生成する部分群 ⟨S⟩）。解像度は測る素点の集合。
測った座標は (log q（∞ を測るとき）, (v_p(q))_{測る素数 p})。有限素点の座標は離散な ℤ。
このファイルが示すのは数学の事実だけ（どの位相で像が離散で、どこで閉包が連続な成分を含むか）。「解像度が落ちる」は
著者の定義で、ここでは示していない。

内容（すべて既知の事実の Lean 化。新しいのは置き方だけ）：
1. すべての素点の付値の組：単射（`eq_of_padicValRat_eq`、素因数分解の一意性）、異なる正の有理数はある素数の座標で
   1 以上離れる（`exists_prime_one_le_abs`。sup 距離の意味。位相の文は節 4）。∏_{s∈S} s^{k_s} の付値
   （`padicValRat_prod_zpow`）、付値の組への全射（`exists_padicValRat_eq`）、⟨S⟩ の元の表示（`eq_prod_of_support`）、
   積公式 log q = Σ v_s(q) log s（`log_eq_sum_of_support`：∞ の座標は有限素点の座標から決まる）。
2. ∞ だけを測る：log ℚ_{>0} の閉包は ℝ 全体（`closure_logSet`、Part 250 の `dense_logSet` から）。異なる 2 つの素数の
   対数が生成する群は稠密（`dense_closure_log_primes`・`exists_zpow_near`。Part 250 の 2 と 3 の一般化）。log r / log p は
   無理数（`irrational_log_div_log`）。
3. 有限の基礎 ⟨S⟩ での閾値（T ⊆ S、∞ と T の素数を測る。像 `imgST S T` ⊆ ℝ × ℤ^T）：
   - 閉包がある水平な直線 ℝ × {k} 全体を含む ⇔ T の外に S の異なる素数が 2 つある（`threshold_iff`）。
   - 二分法：その条件のもとで像は稠密（`dense_imgST_iff`）。条件が成り立たない（測らない素数が高々 1 つ）なら像は閉かつ
     離散（`isClosed_discrete_imgST`。T の座標が同じ点は一定の間隔 c > 0 で離れる `fiber_sep` から）。
   - 部品：測らない素数 p ≠ r があれば、ほかの座標を保ったまま log を任意の x に近づけられる
     （`exists_near_of_two_unmeasured`・`exists_near_measured`・`exists_near_in_subgroup`）。p 以外の付値が一致する 2 元は
     q' = q·p^k で、等しいか log p 以上離れる（`eq_mul_zpow_of_agree`・`log_sep_of_agree`・`log_sep_one_unmeasured`）。
     ℚ_{>0} を基礎にしたこれらの文は、測った座標が同じ点の集まり（ファイバー）の中の距離の文で、有限の解像度の文ではない
     （ℚ_{>0} では、有限の解像度の外に素数が無限個ある）。S の素数をすべて測れば離散
     （`exists_mem_one_le_abs_of_support`）、∞ を測らなければ整数の座標で離散（`sep_of_inf_unmeasured`。ほぼ同語反復）。
4. 極限の取り方：すべての素点の座標 ρ(q) = (log q, (v_p(q))_p)。集合は同じで、位相が 2 通り。
   - 直積の位相（`Nat.Primes → ℤ` の既定の位相。各近傍は有限個の素点しか測らない）：像は稠密（`dense_rho_image`）、
     ℝ × {0} の直線が閉包に入る（`mem_closure_line_prod`）、ρ(1) は孤立点でない（`rho_one_mem_closure_ne_one`）、閉包の点
     (1, 0) は積公式の形 x = Σ k_p log p を満たさず像にない（`closure_rho_not_image`）。
   - すべての素点を同時に測る位相（`BoxCoord`：離散位相。ℤ 値では箱・一様の位相と同じ）：像は閉かつ離散
     （`isClosed_discrete_rhoBox_image`）。sup 距離で 1 以上離れる（`rho_sep`）。
   - 離散になるかどうかは位相の選び方で決まり、有限台では決まらない（付値の組は有限台 `finite_support_padicValRat`、
     各元は台の段 ⟨T⟩ の元 `eq_prod_support` だが、`rho_one_mem_closure_ne_one` の近似点も有限台）。
5. 対照群：値が c·ℤ（c > 0）に入れば離散（`sep_of_mem_zmultiples`。F_q(t) では c = log q）。対数が通約的な
   一般化素数（`mem_zmultiples_of_commensurable`・`sep_of_commensurable`）。
6. 順序版（大きさの順序 = 無限素点の絶対値）：⟨p⟩ では 1 より大きい最小の元は p（`zpow_ge_of_one_lt`）。
   ⟨p, r⟩（p ≠ r）では最小の元がない（`exists_between_one`）。
7. 退化例：すべての付値が 0 の正の有理数は 1（`eq_one_of_padicValRat_eq_zero`。S = ∅ で ⟨S⟩ = {1}）。
一般の補題：T1 空間で、どの点にも集合と高々 1 点でしか交わらない近傍があれば、その集合は閉かつ離散
（`isClosed_and_discrete_of_subsingleton`）。

独立照合の後に足したもの：A・C の後に `imgST`（def）・`fiber_sep`・`threshold_iff`・`irrational_log_div_log`・
`closure_rho_not_image`、`exists_mem_one_le_abs_of_support` の結論に「証人は素数」。B の後に `BoxCoord`・`rhoBox`（def）・
`isClosed_discrete_rhoBox_image`・`dense_imgST_iff`・`isClosed_discrete_imgST`・`isClosed_and_discrete_of_subsingleton`。

Lean にしていないこと：直和 ⊕ℤ の直極限の位相（有限の段 ℤ^T の直極限。離散）そのものと、それと `BoxCoord` の位相の
同一視（標準の事実）。S ∪ {∞} から 1 つ落としても格子であること（S 単数定理の形。数値 step278 の (9)）。⟨S⟩ の大きさの
順序の Dedekind 完備化が ℝ であること。F_q(t) そのもの（付値と積公式。数値 (15)）。測らない生成元が無限個の一般化素数の
反例（数値 (17)）。
ℝ は log の値域として定義に明示的に置かれていて、隠れた注入ではない。それを完備化と読み、著者の定義の「解像度が落ちる」に
あたると読むのは読み（数学の文ではない）。
-/
import PAG258
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace PAG.Part259

/-! ### 1. すべての素点の付値の組（単射、sup 距離で 1 以上、積公式） -/

/-- 異なる素数 s ≠ p：v_s(p) = 0。 -/
theorem padicValRat_prime_ne {s p : ℕ} (hs : s.Prime) (hp : p.Prime) (hne : s ≠ p) :
    padicValRat s (p : ℚ) = 0 := by
  have := Fact.mk hs
  have := Fact.mk hp
  rw [padicValRat.of_nat, padicValNat_primes hne]
  simp

/-- v_s(p^k) は s = p なら k、そうでなければ 0。 -/
theorem padicValRat_prime_zpow {s p : ℕ} (hs : s.Prime) (hp : p.Prime) (k : ℤ) :
    padicValRat s ((p : ℚ) ^ k) = if s = p then k else 0 := by
  have := Fact.mk hs
  rw [padicValRat.zpow]
  split_ifs with h
  · subst h
    rw [padicValRat.self hs.one_lt, mul_one]
  · rw [padicValRat_prime_ne hs hp h, mul_zero]

/-- **1a.** ∏_{s∈S} s^{k_s} の付値：t ∈ S なら k_t、t ∉ S なら 0。 -/
theorem padicValRat_prod_zpow (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (k : ℕ → ℤ) {t : ℕ}
    (ht : t.Prime) :
    padicValRat t (∏ s ∈ S, (s : ℚ) ^ (k s)) = if t ∈ S then k t else 0 := by
  have := Fact.mk ht
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hS' : ∀ s ∈ S, s.Prime := fun s hs => hS s (Finset.mem_insert_of_mem hs)
    have hapr : a.Prime := hS a (Finset.mem_insert_self a S)
    rw [Finset.prod_insert ha]
    have h1 : ((a : ℚ) ^ (k a)) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hapr.ne_zero)
    have h2 : (∏ s ∈ S, (s : ℚ) ^ (k s)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun s hs => zpow_ne_zero _ (by exact_mod_cast (hS' s hs).ne_zero))
    rw [padicValRat.mul h1 h2, padicValRat_prime_zpow ht hapr, ih hS']
    by_cases hta : t = a
    · subst hta
      simp [ha]
    · simp [hta, Finset.mem_insert]

/-- **1b. 全解像度の単射**（素因数分解の一意性）：すべての素数で付値が一致する正の有理数は等しい。 -/
theorem eq_of_padicValRat_eq {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (h : ∀ p : ℕ, p.Prime → padicValRat p q = padicValRat p r) : q = r := by
  have hqn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq.ne'
  have hrn : r.num ≠ 0 := Rat.num_ne_zero.mpr hr.ne'
  have key : q.num.natAbs * r.den = r.num.natAbs * q.den := by
    rw [Nat.eq_iff_prime_padicValNat_eq _ _ (mul_ne_zero (Int.natAbs_ne_zero.mpr hqn) r.den_nz)
      (mul_ne_zero (Int.natAbs_ne_zero.mpr hrn) q.den_nz)]
    intro p hp
    have := Fact.mk hp
    have hpq := h p hp
    rw [padicValRat_def, padicValRat_def] at hpq
    simp only [padicValInt] at hpq
    rw [padicValNat.mul (Int.natAbs_ne_zero.mpr hqn) r.den_nz,
      padicValNat.mul (Int.natAbs_ne_zero.mpr hrn) q.den_nz]
    omega
  have hqn' : 0 < q.num := Rat.num_pos.mpr hq
  have hrn' : 0 < r.num := Rat.num_pos.mpr hr
  rw [Rat.eq_iff_mul_eq_mul]
  have := congrArg (fun n : ℕ => (n : ℤ)) key
  push_cast at this
  rwa [abs_of_pos hqn', abs_of_pos hrn'] at this

/-- **7. 退化例**：すべての付値が 0 の正の有理数は 1（S = ∅ で ⟨S⟩ = {1}）。 -/
theorem eq_one_of_padicValRat_eq_zero {q : ℚ} (hq : 0 < q)
    (h : ∀ p : ℕ, p.Prime → padicValRat p q = 0) : q = 1 :=
  eq_of_padicValRat_eq hq one_pos (fun p hp => by rw [h p hp, padicValRat.one])

/-- 異なる整数は、実数として 1 以上離れる（整数の座標の離散性）。 -/
theorem one_le_abs_intCast_sub {a b : ℤ} (hne : a ≠ b) : (1 : ℝ) ≤ |((a - b : ℤ) : ℝ)| := by
  have h : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h1 : (1 : ℤ) ≤ |a - b| := Int.one_le_abs h
  exact_mod_cast h1

/-- **1c.** 異なる正の有理数は、ある素数の座標で 1 以上離れる（sup 距離の意味。位相の文は `isClosed_discrete_rhoBox_image`）。 -/
theorem exists_prime_one_le_abs {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (hne : q ≠ r) :
    ∃ p : ℕ, p.Prime ∧ (1 : ℝ) ≤ |((padicValRat p q - padicValRat p r : ℤ) : ℝ)| := by
  by_contra hcon
  apply hne
  apply eq_of_padicValRat_eq hq hr
  intro p hp
  by_contra hne'
  exact hcon ⟨p, hp, one_le_abs_intCast_sub hne'⟩

/-- **1d.** 台が S に入る正の有理数（⟨S⟩ の元）は q = ∏_{s∈S} s^{v_s(q)}。 -/
theorem eq_prod_of_support (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) {q : ℚ} (hq : 0 < q)
    (hsupp : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) :
    q = ∏ s ∈ S, (s : ℚ) ^ (padicValRat s q) := by
  apply eq_of_padicValRat_eq hq
    (Finset.prod_pos (fun s hs => zpow_pos (by exact_mod_cast (hS s hs).pos) _))
  intro t ht
  rw [padicValRat_prod_zpow S hS _ ht]
  split_ifs with htS
  · rfl
  · exact hsupp t ht htS

/-- **1e. 積公式**：⟨S⟩ の元では log q = Σ_{s∈S} v_s(q)·log s（全解像度では ∞ の座標は有限素点の座標から決まる）。 -/
theorem log_eq_sum_of_support (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) {q : ℚ} (hq : 0 < q)
    (hsupp : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) :
    Real.log q = ∑ s ∈ S, (padicValRat s q : ℝ) * Real.log s := by
  conv_lhs => rw [eq_prod_of_support S hS hq hsupp]
  push_cast
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro s _
    rw [Real.log_zpow]
  · intro s hs
    exact zpow_ne_zero _ (by exact_mod_cast (hS s hs).ne_zero)

/-- **1f. 付値の組への全射**：S の上の任意の整数の組 k に対し、v_s = k_s（s ∈ S）で S の外では付値 0 の正の有理数がある。 -/
theorem exists_padicValRat_eq (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (k : ℕ → ℤ) :
    ∃ q : ℚ, 0 < q ∧ (∀ s ∈ S, padicValRat s q = k s) ∧
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) := by
  refine ⟨∏ s ∈ S, (s : ℚ) ^ (k s),
    Finset.prod_pos (fun s hs => zpow_pos (by exact_mod_cast (hS s hs).pos) _), ?_, ?_⟩
  · intro s hs
    simp [padicValRat_prod_zpow S hS k (hS s hs), hs]
  · intro t ht htS
    simp [padicValRat_prod_zpow S hS k ht, htS]

/-! ### 2. ∞ だけを測る（log ℚ_{>0} の閉包は ℝ、異なる 2 素数の対数の群は稠密） -/

/-- **2a.** ∞ だけを測って完備化すると ℝ 全体（Part 250 の `dense_logSet` から）。 -/
theorem closure_logSet : closure PAG.Part254.logSet = Set.univ :=
  PAG.Part254.dense_logSet.closure_eq

/-- **2b.** 異なる 2 つの素数 p, r の対数が生成する加法群は ℝ で稠密（最小の正の元があれば p^K = r^M となり矛盾）。Part 250 の 2 と 3 の一般化。 -/
theorem dense_closure_log_primes {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) :
    Dense ((AddSubgroup.closure ({Real.log p, Real.log r} : Set ℝ) : AddSubgroup ℝ) : Set ℝ) := by
  set S : AddSubgroup ℝ := AddSubgroup.closure ({Real.log p, Real.log r} : Set ℝ) with hS
  have h2S : Real.log p ∈ S := AddSubgroup.subset_closure (by simp)
  have h3S : Real.log r ∈ S := AddSubgroup.subset_closure (by simp)
  have hl2 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hl3 : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
  have hbot : S ≠ ⊥ := by
    intro h
    rw [h, AddSubgroup.mem_bot] at h2S
    exact hl2.ne' h2S
  refine AddSubgroup.dense_of_no_min S hbot ?_
  rintro ⟨a, ⟨haS, ha0⟩, hmin⟩
  have key : ∀ g, g ∈ S → ∃ k : ℤ, g = k * a := by
    intro g hg
    refine ⟨⌊g / a⌋, ?_⟩
    have hrem : g - (⌊g / a⌋ : ℝ) * a ∈ S := by
      have := S.sub_mem hg (S.zsmul_mem haS ⌊g / a⌋)
      rwa [zsmul_eq_mul] at this
    have h1 : (⌊g / a⌋ : ℝ) ≤ g / a := Int.floor_le _
    have h2 : g / a < ⌊g / a⌋ + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ ha0] at h1
    rw [div_lt_iff₀ ha0] at h2
    by_contra hne
    have hpos : 0 < g - (⌊g / a⌋ : ℝ) * a := by
      rcases lt_or_eq_of_le (sub_nonneg.mpr h1) with h | h
      · exact h
      · exact absurd (by linarith) hne
    have := hmin ⟨hrem, hpos⟩
    linarith
  obtain ⟨m, hm⟩ := key _ h2S
  obtain ⟨n, hn⟩ := key _ h3S
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := by
      by_contra hcon
      have : (m : ℝ) * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) ha0.le
      linarith
    exact_mod_cast this
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by
      by_contra hcon
      have : (n : ℝ) * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) ha0.le
      linarith
    exact_mod_cast this
  obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hm0.le
  obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hn0.le
  have hK : 0 < K := by exact_mod_cast hn0
  have heq : (K : ℝ) * Real.log p = (M : ℝ) * Real.log r := by
    rw [hm, hn]
    push_cast
    ring
  have hpow : ((p : ℝ) ^ K) = (r : ℝ) ^ M := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by have := hp.pos; positivity))
      (Set.mem_Ioi.mpr (by have := hr.pos; positivity))
    rw [Real.log_pow, Real.log_pow]
    exact heq
  have hnat : p ^ K = r ^ M := by exact_mod_cast hpow
  have hdvd : p ∣ r ^ M := by
    rw [← hnat]
    exact dvd_pow_self p hK.ne'
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hdvd))

/-- **2c.** どの x と ε > 0 に対しても、|a·log p + b·log r − x| < ε となる整数 a, b がある。 -/
theorem exists_zpow_near {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ a b : ℤ, |(a : ℝ) * Real.log p + (b : ℝ) * Real.log r - x| < ε := by
  obtain ⟨y, hy, hyS⟩ := Metric.dense_iff.mp (dense_closure_log_primes hp hr hne) x ε hε
  obtain ⟨a, b, hab⟩ := AddSubgroup.mem_closure_pair.mp hyS
  refine ⟨a, b, ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at hy
  rw [← hab, zsmul_eq_mul, zsmul_eq_mul] at hy
  exact hy

/-- 異なる素数 p, r で log r / log p は無理数（通約できない。対照群の通約的な場合との違い）。 -/
theorem irrational_log_div_log {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) :
    Irrational (Real.log r / Real.log p) := by
  rw [irrational_iff_ne_rational]
  intro a b hb h
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlr : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have key : (b : ℝ) * Real.log r = a * Real.log p := by
    rw [div_eq_div_iff hlp.ne' hb'] at h
    linarith
  have habs : (b.natAbs : ℝ) * Real.log r = (a.natAbs : ℝ) * Real.log p := by
    have h1 : |(b : ℝ) * Real.log r| = |(a : ℝ) * Real.log p| := by rw [key]
    rw [abs_mul, abs_mul, abs_of_pos hlr, abs_of_pos hlp] at h1
    simp only [Nat.cast_natAbs, Int.cast_abs]
    exact h1
  have hK : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow : ((r : ℝ) ^ b.natAbs) = (p : ℝ) ^ a.natAbs := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos hr0 _)) (Set.mem_Ioi.mpr (pow_pos hp0 _))
    rw [Real.log_pow, Real.log_pow]
    exact habs
  have hnat : r ^ b.natAbs = p ^ a.natAbs := by exact_mod_cast hpow
  have hdvd : r ∣ p ^ a.natAbs := by
    rw [← hnat]
    exact dvd_pow_self r hK.ne'
  exact hne ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hdvd)).symm

/-! ### 3. ファイバーの中の距離（p・r の付値だけが違いうる点、p の付値だけが違いうる点） -/

/-- q₀·p^a·r^b の付値。 -/
theorem padicValRat_mul_zpow_zpow {p r t : ℕ} (hp : p.Prime) (hr : r.Prime) (ht : t.Prime)
    {q₀ : ℚ} (hq₀ : q₀ ≠ 0) (a b : ℤ) :
    padicValRat t (q₀ * (p : ℚ) ^ a * (r : ℚ) ^ b) =
      padicValRat t q₀ + (if t = p then a else 0) + (if t = r then b else 0) := by
  have := Fact.mk ht
  have hpa : ((p : ℚ) ^ a) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hrb : ((r : ℚ) ^ b) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hr.ne_zero)
  rw [padicValRat.mul (mul_ne_zero hq₀ hpa) hrb, padicValRat.mul hq₀ hpa,
    padicValRat_prime_zpow ht hp, padicValRat_prime_zpow ht hr]

/-- q₀·p^a·r^b の log。 -/
theorem log_mul_zpow_zpow {p r : ℕ} (hp : p.Prime) (hr : r.Prime) {q₀ : ℚ} (hq₀ : 0 < q₀)
    (a b : ℤ) :
    Real.log ((q₀ * (p : ℚ) ^ a * (r : ℚ) ^ b : ℚ) : ℝ) =
      Real.log q₀ + (a : ℝ) * Real.log p + (b : ℝ) * Real.log r := by
  have hq₀' : (q₀ : ℝ) ≠ 0 := by exact_mod_cast hq₀.ne'
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
  push_cast
  rw [Real.log_mul (mul_ne_zero hq₀' (zpow_ne_zero _ hp')) (zpow_ne_zero _ hr'),
    Real.log_mul hq₀' (zpow_ne_zero _ hp'), Real.log_zpow, Real.log_zpow]

/-- p ≠ r 以外のすべての付値を q₀ と同じに保ったまま（p・r の付値だけが違いうるファイバーの中で）、log を任意の x に近づけられる。 -/
theorem exists_near_of_two_unmeasured {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r)
    {q₀ : ℚ} (hq₀ : 0 < q₀) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ≠ p → t ≠ r → padicValRat t q = padicValRat t q₀) ∧
      |Real.log q - x| < ε := by
  obtain ⟨a, b, hab⟩ := exists_zpow_near hp hr hne (x - Real.log q₀) hε
  refine ⟨q₀ * (p : ℚ) ^ a * (r : ℚ) ^ b, ?_, ?_, ?_⟩
  · have := hp.pos
    have := hr.pos
    positivity
  · intro t ht htp htr
    rw [padicValRat_mul_zpow_zpow hp hr ht hq₀.ne' a b]
    simp [htp, htr]
  · rw [log_mul_zpow_zpow hp hr hq₀ a b]
    have : Real.log q₀ + a * Real.log p + b * Real.log r - x =
        a * Real.log p + b * Real.log r - (x - Real.log q₀) := by ring
    rw [this]
    exact hab

/-- 有限の解像度 M（∞ と M の素数を測る）：測らない素数 p ≠ r があれば、(x, (v_s(q₀))_{s∈M}) は像の閉包に入る。 -/
theorem exists_near_measured {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r)
    (M : Finset ℕ) (hpM : p ∉ M) (hrM : r ∉ M) {q₀ : ℚ} (hq₀ : 0 < q₀) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ s ∈ M, s.Prime → padicValRat s q = padicValRat s q₀) ∧
      |Real.log q - x| < ε := by
  obtain ⟨q, hq, hv, hlog⟩ := exists_near_of_two_unmeasured hp hr hne hq₀ x hε
  refine ⟨q, hq, fun s hs hsp => hv s hsp ?_ ?_, hlog⟩
  · rintro rfl
    exact hpM hs
  · rintro rfl
    exact hrM hs

/-- p 以外のすべての付値が一致すれば q' = q·p^k（k = v_p q' − v_p q）。 -/
theorem eq_mul_zpow_of_agree {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q) (hq' : 0 < q')
    (h : ∀ t : ℕ, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q * (p : ℚ) ^ (padicValRat p q' - padicValRat p q) := by
  have hpk : ((p : ℚ) ^ (padicValRat p q' - padicValRat p q)) ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  apply eq_of_padicValRat_eq hq'
    (mul_pos hq (zpow_pos (by exact_mod_cast hp.pos) _))
  intro t ht
  have := Fact.mk ht
  rw [padicValRat.mul hq.ne' hpk, padicValRat_prime_zpow ht hp]
  by_cases htp : t = p
  · subst htp
    simp
  · simp [htp, h t ht htp]

/-- p 以外のすべての付値が一致する 2 元（p の付値だけが違いうるファイバー）は、等しいか、∞ の座標で log p 以上離れる。 -/
theorem log_sep_of_agree {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q) (hq' : 0 < q')
    (h : ∀ t : ℕ, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q ∨ Real.log p ≤ |Real.log q' - Real.log q| := by
  set k := padicValRat p q' - padicValRat p q with hk
  have heq := eq_mul_zpow_of_agree hp hq hq' h
  by_cases hk0 : k = 0
  · left
    rw [heq, ← hk, hk0, zpow_zero, mul_one]
  · right
    have hlog : Real.log q' - Real.log q = (k : ℝ) * Real.log p := by
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [heq, ← hk]
      push_cast
      rw [Real.log_mul hq0 (zpow_ne_zero _ hp0), Real.log_zpow]
      ring
    rw [hlog, abs_mul]
    have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      exact_mod_cast this
    rw [abs_of_pos hl]
    nlinarith

/-! ### 3b. 有限の基礎 ⟨S⟩ での閾値（T ⊆ S、∞ と T の素数を測る） -/

/-- ⟨S⟩ の全解像度：S の素数をすべて測れば、異なる元は S のある素数の座標で 1 以上離れる。 -/
theorem exists_mem_one_le_abs_of_support (S : Finset ℕ) {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (hqS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
    (hrS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t r = 0) (hne : q ≠ r) :
    ∃ p ∈ S, p.Prime ∧ (1 : ℝ) ≤ |((padicValRat p q - padicValRat p r : ℤ) : ℝ)| := by
  obtain ⟨p, hp, h⟩ := exists_prime_one_le_abs hq hr hne
  by_cases hpS : p ∈ S
  · exact ⟨p, hpS, hp, h⟩
  · rw [hqS p hp hpS, hrS p hp hpS] at h
    norm_num at h

/-- ∞ を測らないとき：有限素点の座標は整数なので、異なる像は 1 以上離れる。 -/
theorem sep_of_inf_unmeasured (M : Finset ℕ) {q r : ℚ}
    (hne : ∃ s ∈ M, padicValRat s q ≠ padicValRat s r) :
    ∃ s ∈ M, (1 : ℝ) ≤ |((padicValRat s q - padicValRat s r : ℤ) : ℝ)| := by
  obtain ⟨s, hs, h⟩ := hne
  exact ⟨s, hs, one_le_abs_intCast_sub h⟩

/-- ⟨S⟩ で S の素数 p だけを測らないとき：p 以外の S の座標が一致する 2 元は、等しいか、∞ の座標で log p 以上離れる。 -/
theorem log_sep_one_unmeasured (S : Finset ℕ) {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q)
    (hq' : 0 < q') (hqS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
    (hq'S : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q' = 0)
    (h : ∀ t ∈ S, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q ∨ Real.log p ≤ |Real.log q' - Real.log q| := by
  apply log_sep_of_agree hp hq hq'
  intro t ht htp
  by_cases htS : t ∈ S
  · exact h t htS ht htp
  · rw [hqS t ht htS, hq'S t ht htS]

/-- ⟨S⟩ で S の素数 p ≠ r を測らないとき：⟨S⟩ の中にとどまり、T の座標を q₀ と同じに保ったまま、log を任意の x に
近づけられる（閉包は ℝ × ℤ^T を含む）。 -/
theorem exists_near_in_subgroup (S : Finset ℕ) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hne : p ≠ r) (hpS : p ∈ S) (hrS : r ∈ S) (T : Finset ℕ) (hpT : p ∉ T) (hrT : r ∉ T)
    {q₀ : ℚ} (hq₀ : 0 < q₀) (hq₀S : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q₀ = 0) (x : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) ∧
      (∀ s ∈ T, s.Prime → padicValRat s q = padicValRat s q₀) ∧ |Real.log q - x| < ε := by
  obtain ⟨q, hq, hv, hlog⟩ := exists_near_of_two_unmeasured hp hr hne hq₀ x hε
  refine ⟨q, hq, fun t ht htS => ?_, fun s hs hsp => ?_, hlog⟩
  · have htp : t ≠ p := by
      rintro rfl
      exact htS hpS
    have htr : t ≠ r := by
      rintro rfl
      exact htS hrS
    rw [hv t ht htp htr, hq₀S t ht htS]
  · have hsp' : s ≠ p := by
      rintro rfl
      exact hpT hs
    have hsr : s ≠ r := by
      rintro rfl
      exact hrT hs
    exact hv s hsp hsp' hsr

/-- 基礎 ⟨S⟩（S は素数の有限集合）で、∞ と T の素数を測るときの像 {(log q, (v_t(q))_{t∈T}) | q ∈ ⟨S⟩}。
T の座標は ℤ^T（T は有限なので離散）。 -/
def imgST (S T : Finset ℕ) : Set (ℝ × (T → ℤ)) :=
  {z | ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) ∧
    z = (Real.log q, fun t : T => padicValRat (t : ℕ) q)}

/-- 測らない素数（S ∖ T の元）が高々 1 つなら、T の座標が同じ ⟨S⟩ の 2 元は、等しいか、∞ の座標で一定の c > 0 以上離れる。 -/
theorem fiber_sep (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime)
    (h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r) :
    ∃ c : ℝ, 0 < c ∧ ∀ q q' : ℚ, 0 < q → 0 < q' →
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) →
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q' = 0) →
      (∀ t ∈ T, padicValRat t q' = padicValRat t q) →
      q' = q ∨ c ≤ |Real.log q' - Real.log q| := by
  by_cases hex : ∃ p ∈ S, p ∉ T
  · obtain ⟨p, hpS, hpT⟩ := hex
    have hp := hS p hpS
    refine ⟨Real.log p, Real.log_pos (by exact_mod_cast hp.one_lt), ?_⟩
    intro q q' hq hq' hqS hq'S hT
    apply log_sep_of_agree hp hq hq'
    intro t ht htp
    by_cases htT : t ∈ T
    · exact hT t htT
    · by_cases htS : t ∈ S
      · exact absurd (h1 t p htS hpS htT hpT) htp
      · rw [hqS t ht htS, hq'S t ht htS]
  · refine ⟨1, one_pos, ?_⟩
    intro q q' hq hq' hqS hq'S hT
    left
    apply eq_of_padicValRat_eq hq' hq
    intro t ht
    by_cases htS : t ∈ S
    · have htT : t ∈ T := by
        by_contra htT
        exact hex ⟨t, htS, htT⟩
      exact hT t htT
    · rw [hqS t ht htS, hq'S t ht htS]

/-- **閾値の定理**（基礎 ⟨S⟩、T ⊆ S、∞ と T の素数を測る）：像の閉包がある水平な直線 ℝ × {k} 全体を含む
⇔ T の外に S の異なる素数が 2 つある（測らない素数が 2 つ以上）。 -/
theorem threshold_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    (∃ k : T → ℤ, ∀ x : ℝ, (x, k) ∈ closure (imgST S T)) ↔
      ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T := by
  constructor
  · rintro ⟨k, hk⟩
    by_contra hno
    have h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r := by
      intro p r hp hr hpT hrT
      by_contra hne
      exact hno ⟨p, r, hne, hp, hr, hpT, hrT⟩
    obtain ⟨c, hc, hsep⟩ := fiber_sep S T hS h1
    have hmem : ∀ x : ℝ, ∀ δ : ℝ, 0 < δ → ∃ q : ℚ, 0 < q ∧
        (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) ∧
        (fun t : T => padicValRat (t : ℕ) q) = k ∧ |Real.log q - x| < δ := by
      intro x δ hδ
      have hx := hk x
      rw [mem_closure_iff_nhds] at hx
      have hU : (Metric.ball x δ ×ˢ ({k} : Set (T → ℤ))) ∈ nhds (x, k) :=
        prod_mem_nhds (Metric.ball_mem_nhds x hδ) ((isOpen_discrete _).mem_nhds rfl)
      obtain ⟨z, hzU, hzA⟩ := hx _ hU
      obtain ⟨q, hq, hqS, rfl⟩ := hzA
      refine ⟨q, hq, hqS, hzU.2, ?_⟩
      have := hzU.1
      rwa [Metric.mem_ball, Real.dist_eq] at this
    obtain ⟨q₀, hq₀, hq₀S, hk₀, -⟩ := hmem 0 1 one_pos
    obtain ⟨q, hq, hqS, hkq, hlog⟩ := hmem (Real.log q₀ + c / 2) (c / 4) (by linarith)
    have hagree : ∀ t ∈ T, padicValRat t q = padicValRat t q₀ := by
      intro t ht
      have e1 := congrFun hkq ⟨t, ht⟩
      have e2 := congrFun hk₀ ⟨t, ht⟩
      simp only at e1 e2
      rw [e1, e2]
    have hl := abs_lt.mp hlog
    rcases hsep q₀ q hq₀ hq hq₀S hqS hagree with heq | hle
    · rw [heq] at hl
      linarith [hl.1, hl.2]
    · have h3 : |Real.log q - Real.log q₀| < c := by
        rw [abs_lt]
        constructor <;> linarith [hl.1, hl.2]
      linarith
  · rintro ⟨p, r, hne, hpS, hrS, hpT, hrT⟩
    refine ⟨fun _ => 0, fun x => ?_⟩
    rw [mem_closure_iff_nhds]
    intro t ht
    rw [nhds_prod_eq, Filter.mem_prod_iff] at ht
    obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := ht
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht₁
    obtain ⟨q, hq, hqS, hqT, hlog⟩ := exists_near_in_subgroup S (hS p hpS) (hS r hrS) hne hpS hrS T
      hpT hrT one_pos (fun t _ _ => padicValRat.one) x hε
    refine ⟨(Real.log q, fun t : T => padicValRat (t : ℕ) q), hsub ⟨?_, ?_⟩, q, hq, hqS, rfl⟩
    · apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      exact hlog
    · have hz : (fun t : T => padicValRat (t : ℕ) q) = fun _ => 0 := by
        funext t
        rw [hqT t t.prop (hS t (hTS t.prop)), padicValRat.one]
      rw [hz]
      exact mem_of_mem_nhds ht₂


/-- 一般の補題：T1 空間で、どの点にも集合 A と高々 1 点でしか交わらない近傍があれば、A は閉かつ（部分空間として）離散。 -/
theorem isClosed_and_discrete_of_subsingleton {X : Type*} [TopologicalSpace X] [T1Space X]
    {A : Set X} (h : ∀ z : X, ∃ U ∈ nhds z, (U ∩ A).Subsingleton) :
    IsClosed A ∧ DiscreteTopology A := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨U, hU, hsub⟩ := h z
    by_cases hne : (U ∩ A).Nonempty
    · obtain ⟨w, hwU, hwA⟩ := hne
      have hwz : z ≠ w := fun h' => hz (h' ▸ hwA)
      filter_upwards [hU, isOpen_compl_singleton.mem_nhds hwz] with y hyU hyw hyA
      exact hyw (hsub ⟨hyU, hyA⟩ ⟨hwU, hwA⟩)
    · filter_upwards [hU] with y hyU hyA
      exact hne ⟨y, hyU, hyA⟩
  · rw [discreteTopology_iff_isOpen_singleton]
    rintro ⟨a, ha⟩
    obtain ⟨U, hU, hsub⟩ := h a
    obtain ⟨V, hVU, hVo, haV⟩ := mem_nhds_iff.mp hU
    have hset : ({⟨a, ha⟩} : Set A) = Subtype.val ⁻¹' V := by
      ext ⟨b, hb⟩
      simp only [Set.mem_singleton_iff, Set.mem_preimage, Subtype.mk.injEq]
      constructor
      · rintro rfl
        exact haV
      · intro hbV
        exact hsub ⟨hVU hbV, hb⟩ ⟨hVU haV, ha⟩
    rw [hset]
    exact hVo.preimage continuous_subtype_val

/-- **閾値の二分法（片側）**：像 `imgST S T` が ℝ × ℤ^T で稠密 ⇔ T の外に S の異なる素数が 2 つある。 -/
theorem dense_imgST_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    Dense (imgST S T) ↔ ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T := by
  constructor
  · intro hd
    rw [← threshold_iff S T hS hTS]
    exact ⟨fun _ => 0, fun x => hd (x, fun _ => 0)⟩
  · rintro ⟨p, r, hne, hpS, hrS, hpT, hrT⟩
    rintro ⟨x, k⟩
    rw [mem_closure_iff_nhds]
    intro t ht
    rw [nhds_prod_eq, Filter.mem_prod_iff] at ht
    obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := ht
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht₁
    let kk : ℕ → ℤ := fun s => if hs : s ∈ T then k ⟨s, hs⟩ else 0
    obtain ⟨q₀, hq₀, hv₀, hsupp₀⟩ := exists_padicValRat_eq T (fun s hs => hS s (hTS hs)) kk
    have hq₀S : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q₀ = 0 :=
      fun t ht htS => hsupp₀ t ht (fun htT => htS (hTS htT))
    obtain ⟨q, hq, hqS, hqT, hlog⟩ := exists_near_in_subgroup S (hS p hpS) (hS r hrS) hne hpS
      hrS T hpT hrT hq₀ hq₀S x hε
    refine ⟨(Real.log q, fun t : T => padicValRat (t : ℕ) q), hsub ⟨?_, ?_⟩, q, hq, hqS, rfl⟩
    · apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      exact hlog
    · have hz : (fun t : T => padicValRat (t : ℕ) q) = k := by
        funext t
        rw [hqT t t.prop (hS t (hTS t.prop)), hv₀ t t.prop]
        simp only [kk]
        split_ifs with h
        · rfl
        · exact absurd t.prop h
      rw [hz]
      exact mem_of_mem_nhds ht₂

/-- **閾値の二分法（もう片側）**：T の外に S の異なる素数が 2 つないとき（測らない素数が高々 1 つ）、像 `imgST S T` は
ℝ × ℤ^T の中で閉かつ離散。 -/
theorem isClosed_discrete_imgST (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime)
    (h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r) :
    IsClosed (imgST S T) ∧ DiscreteTopology (imgST S T) := by
  obtain ⟨c, hc, hsep⟩ := fiber_sep S T hS h1
  apply isClosed_and_discrete_of_subsingleton
  rintro ⟨x, k⟩
  refine ⟨Metric.ball x (c / 2) ×ˢ {k},
    prod_mem_nhds (Metric.ball_mem_nhds x (half_pos hc)) ((isOpen_discrete _).mem_nhds rfl), ?_⟩
  rintro w₁ ⟨⟨hw₁b, hw₁k⟩, q₁, hq₁, hq₁S, rfl⟩ w₂ ⟨⟨hw₂b, hw₂k⟩, q₂, hq₂, hq₂S, rfl⟩
  have e1 : (fun t : T => padicValRat (t : ℕ) q₁) = k := hw₁k
  have e2 : (fun t : T => padicValRat (t : ℕ) q₂) = k := hw₂k
  have hagree : ∀ t ∈ T, padicValRat t q₂ = padicValRat t q₁ := by
    intro t ht
    have f1 := congrFun e1 ⟨t, ht⟩
    have f2 := congrFun e2 ⟨t, ht⟩
    simp only at f1 f2
    rw [f1, f2]
  simp only [Metric.mem_ball, Real.dist_eq] at hw₁b hw₂b
  rcases hsep q₁ q₂ hq₁ hq₂ hq₁S hq₂S hagree with heq | hle
  · rw [heq]
  · exfalso
    have a1 := abs_lt.mp hw₁b
    have a2 := abs_lt.mp hw₂b
    have h3 : |Real.log q₂ - Real.log q₁| < c := by
      rw [abs_lt]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    linarith

/-! ### 4. 極限の取り方：直積の位相と、すべての素点を同時に測る位相 -/

/-- すべての素点の座標 ρ(q) = (log q, (v_p(q))_p)。有限素点の座標は ℤ（離散）。`Nat.Primes → ℤ` には直積の位相が入る。 -/
noncomputable def rho (q : ℚ) : ℝ × (Nat.Primes → ℤ) := (Real.log q, fun p => padicValRat p q)

/-- ρ(1) = (0, 0)。 -/
theorem rho_one : rho 1 = (0, 0) := by
  simp [rho]
  rfl

/-- 有限個の素数の集合の外に、異なる素数が 2 つある。 -/
theorem exists_two_primes_not_mem (I : Set Nat.Primes) (hI : I.Finite) :
    ∃ p r : Nat.Primes, p ∉ I ∧ r ∉ I ∧ (p : ℕ) ≠ (r : ℕ) := by
  obtain ⟨p, hpI⟩ := hI.infinite_compl.nonempty
  obtain ⟨r, hrI⟩ := (hI.insert p).infinite_compl.nonempty
  refine ⟨p, r, hpI, fun h => hrI (Set.mem_insert_of_mem p h), fun h => hrI ?_⟩
  have : r = p := (Subtype.ext h).symm
  rw [this]
  exact Set.mem_insert p I

/-- I の元と I の外の元は、自然数として異なる。 -/
theorem val_ne_of_mem_of_not_mem {I : Set Nat.Primes} {i p : Nat.Primes} (hi : i ∈ I)
    (hp : p ∉ I) : (i : ℕ) ≠ p := by
  intro h
  have : i = p := Subtype.ext h
  exact hp (this ▸ hi)

/-- **直積の位相では、像は稠密**：ℝ × (素数 → ℤ) のどの点 (x, k) の近傍（∞ の座標の ε 近傍と、有限個の素数の座標の
指定）にも、正の有理数の像がある。各近傍は有限個の素点しか見ない。これを著者の言葉の「完備化（極限）」にあたると読むのは読み。 -/
theorem dense_rho_image : Dense (rho '' {q : ℚ | 0 < q}) := by
  rintro ⟨x, k⟩
  rw [mem_closure_iff_nhds]
  intro t ht
  rw [nhds_prod_eq, Filter.mem_prod_iff] at ht
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := ht
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht₁
  rw [nhds_pi, Filter.mem_pi] at ht₂
  obtain ⟨I, hI, u, hu, hIu⟩ := ht₂
  set F : Finset ℕ := hI.toFinset.image (fun i : Nat.Primes => (i : ℕ)) with hFdef
  have hF : ∀ s ∈ F, s.Prime := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact i.prop
  let kk : ℕ → ℤ := fun s => if hs : s.Prime then k ⟨s, hs⟩ else 0
  obtain ⟨q₀, hq₀, hv₀, -⟩ := exists_padicValRat_eq F hF kk
  obtain ⟨p, r, hpI, hrI, hne⟩ := exists_two_primes_not_mem I hI
  obtain ⟨q, hq, hv, hlog⟩ := exists_near_of_two_unmeasured p.prop r.prop hne hq₀ x hε
  refine ⟨rho q, hsub ⟨?_, hIu ?_⟩, q, hq, rfl⟩
  · apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    exact hlog
  · intro i hi
    show padicValRat (i : ℕ) q ∈ u i
    have hiF : (i : ℕ) ∈ F := Finset.mem_image_of_mem _ (hI.mem_toFinset.mpr hi)
    rw [hv i i.prop (val_ne_of_mem_of_not_mem hi hpI) (val_ne_of_mem_of_not_mem hi hrI),
      hv₀ i hiF]
    have hk : kk i = k i := by
      simp only [kk]
      split_ifs with h
      · rfl
      · exact absurd i.prop h
    rw [hk]
    exact mem_of_mem_nhds (hu i)

/-- 系：直積の位相では、ℝ × {0} の直線全体が像の閉包に入る（連続体に滑り落ちる）。 -/
theorem mem_closure_line_prod (x : ℝ) :
    (x, (0 : Nat.Primes → ℤ)) ∈ closure (rho '' {q : ℚ | 0 < q}) :=
  dense_rho_image (x, 0)

/-- 直積の位相の閉包には、積公式を満たさない点が入る：(1, 0) は閉包に入るが、どの正の有理数の像でもない
（付値がすべて 0 なら q = 1 で log q = 0）。 -/
theorem closure_rho_not_image :
    ((1 : ℝ), (0 : Nat.Primes → ℤ)) ∈ closure (rho '' {q : ℚ | 0 < q}) ∧
      ((1 : ℝ), (0 : Nat.Primes → ℤ)) ∉ rho '' {q : ℚ | 0 < q} := by
  refine ⟨mem_closure_line_prod 1, ?_⟩
  rintro ⟨q, hq, hρ⟩
  have h2 : ∀ p : ℕ, p.Prime → padicValRat p q = 0 := by
    intro p hp
    exact congrFun (congrArg Prod.snd hρ) ⟨p, hp⟩
  have hq1 : q = 1 := eq_one_of_padicValRat_eq_zero hq h2
  have h1 := congrArg Prod.fst hρ
  simp [rho, hq1] at h1

/-- 直積の位相では ρ(1) は孤立点でない：1 と異なる正の有理数の像が、ρ(1) のどの近傍にもある。 -/
theorem rho_one_mem_closure_ne_one :
    rho 1 ∈ closure (rho '' {q : ℚ | 0 < q ∧ q ≠ 1}) := by
  rw [rho_one, mem_closure_iff_nhds]
  intro t ht
  rw [nhds_prod_eq, Filter.mem_prod_iff] at ht
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := ht
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht₁
  rw [nhds_pi, Filter.mem_pi] at ht₂
  obtain ⟨I, hI, u, hu, hIu⟩ := ht₂
  obtain ⟨p, r, hpI, hrI, hne⟩ := exists_two_primes_not_mem I hI
  obtain ⟨q, hq, hv, hlog⟩ :=
    exists_near_of_two_unmeasured p.prop r.prop hne one_pos (ε / 2) (half_pos hε)
  have h1 := (abs_lt.mp hlog).1
  have h2 := (abs_lt.mp hlog).2
  have hlogpos : 0 < Real.log q := by linarith
  have hq1 : q ≠ 1 := by
    rintro rfl
    simp at hlogpos
  refine ⟨rho q, hsub ⟨?_, hIu ?_⟩, q, ⟨hq, hq1⟩, rfl⟩
  · apply hball
    show Real.log q ∈ Metric.ball (0 : ℝ) ε
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hlogpos]
    linarith
  · intro i hi
    show padicValRat (i : ℕ) q ∈ u i
    rw [hv i i.prop (val_ne_of_mem_of_not_mem hi hpI) (val_ne_of_mem_of_not_mem hi hrI),
      padicValRat.one]
    exact mem_of_mem_nhds (hu i)

/-- 異なる正の有理数の像は、ある素数の座標で 1 以上離れる（sup 距離で 1 以上。`exists_prime_one_le_abs` の言い換え。
位相の文は `isClosed_discrete_rhoBox_image`）。 -/
theorem rho_sep {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (hne : q ≠ r) :
    ∃ p : Nat.Primes, (1 : ℝ) ≤ |(((rho q).2 p - (rho r).2 p : ℤ) : ℝ)| := by
  obtain ⟨p, hp, h⟩ := exists_prime_one_le_abs hq hr hne
  exact ⟨⟨p, hp⟩, h⟩

/-- すべての素点の座標の組に、すべての素点を同時に測る位相を入れた型：離散位相（ℤ 値では箱の位相・一様の位相と同じ）。
`Nat.Primes → ℤ` の直積の位相（各近傍は有限個の素点しか測らない）と、集合としては同じで位相だけが違う。 -/
def BoxCoord : Type := Nat.Primes → ℤ

instance : TopologicalSpace BoxCoord := ⊥

instance : DiscreteTopology BoxCoord := ⟨rfl⟩

/-- ρ と同じ写像を、値域の有限素点の座標に離散位相（すべての素点を同時に測る）を入れて考える。 -/
noncomputable def rhoBox (q : ℚ) : ℝ × BoxCoord := (Real.log q, fun p => padicValRat p q)

/-- **すべての素点を同時に測る位相では、像は閉かつ離散**（独立照合 B の指摘で追加）。同じ集合が直積の位相では稠密
（`dense_rho_image`）で、離散になるかどうかは有限台ではなく位相の選び方で決まる（`rho_one_mem_closure_ne_one` の近似点も
正の有理数なので有限台）。 -/
theorem isClosed_discrete_rhoBox_image :
    IsClosed (rhoBox '' {q : ℚ | 0 < q}) ∧ DiscreteTopology (rhoBox '' {q : ℚ | 0 < q}) := by
  apply isClosed_and_discrete_of_subsingleton
  rintro ⟨x, k⟩
  refine ⟨Set.univ ×ˢ {k}, prod_mem_nhds Filter.univ_mem ((isOpen_discrete _).mem_nhds rfl), ?_⟩
  rintro w₁ ⟨⟨-, hw₁k⟩, q₁, hq₁, rfl⟩ w₂ ⟨⟨-, hw₂k⟩, q₂, hq₂, rfl⟩
  have e1 : (rhoBox q₁).2 = k := hw₁k
  have e2 : (rhoBox q₂).2 = k := hw₂k
  have h : ∀ p : ℕ, p.Prime → padicValRat p q₁ = padicValRat p q₂ := by
    intro p hp
    exact congrFun (e1.trans e2.symm) ⟨p, hp⟩
  rw [eq_of_padicValRat_eq hq₁ hq₂ h]

/-- 付値の組は有限台：付値が 0 でない素数は有限個（各正の有理数は、有限個の素数が生成する段 ⟨T⟩ に住む）。有限台だけでは離散にならない（`rho_one_mem_closure_ne_one`）。 -/
theorem finite_support_padicValRat {q : ℚ} (hq : 0 < q) :
    {p : ℕ | p.Prime ∧ padicValRat p q ≠ 0}.Finite := by
  have hn : q.num.natAbs * q.den ≠ 0 :=
    mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq.ne')) q.den_nz
  apply (Nat.divisors (q.num.natAbs * q.den)).finite_toSet.subset
  rintro p ⟨hp, hv⟩
  have := Fact.mk hp
  rw [Finset.mem_coe, Nat.mem_divisors]
  refine ⟨?_, hn⟩
  rw [padicValRat_def] at hv
  simp only [padicValInt] at hv
  by_cases h1 : padicValNat p q.num.natAbs = 0
  · have h2 : padicValNat p q.den ≠ 0 := by
      intro h2
      apply hv
      rw [h1, h2]
      simp
    exact Dvd.dvd.mul_left (dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr h2)) _
  · exact Dvd.dvd.mul_right (dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr h1)) _

/-- 各正の有理数は、その台 T の段 ⟨T⟩ の元：q = ∏_{s∈T} s^{v_s(q)}。 -/
theorem eq_prod_support {q : ℚ} (hq : 0 < q) :
    q = ∏ s ∈ (finite_support_padicValRat hq).toFinset, (s : ℚ) ^ (padicValRat s q) := by
  apply eq_prod_of_support _ (fun s hs => ((finite_support_padicValRat hq).mem_toFinset.mp hs).1) hq
  intro t ht htS
  by_contra h
  exact htS ((finite_support_padicValRat hq).mem_toFinset.mpr ⟨ht, h⟩)


/-! ### 5. 対照群 -/

/-- 値が c·ℤ（c > 0）に入れば、異なる値は c 以上離れる（F_q(t)：c = log q、通約的な一般化素数）。 -/
theorem sep_of_mem_zmultiples {c x y : ℝ} (hc : 0 < c) (hx : ∃ m : ℤ, x = m * c)
    (hy : ∃ n : ℤ, y = n * c) (hne : x ≠ y) : c ≤ |x - y| := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  have hmn : m ≠ n := by
    rintro rfl
    exact hne rfl
  have h1 : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := one_le_abs_intCast_sub hmn
  have : (m : ℝ) * c - n * c = ((m - n : ℤ) : ℝ) * c := by push_cast; ring
  rw [this, abs_mul, abs_of_pos hc]
  nlinarith

/-- 通約的な対数：n·L₂ = m·L₁（n > 0）なら a·L₁ + b·L₂ = (a n + b m)·(L₁/n)。 -/
theorem mem_zmultiples_of_commensurable {L₁ L₂ : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) * L₂ = m * L₁) (a b : ℤ) :
    (a : ℝ) * L₁ + b * L₂ = ((a * n + b * m : ℤ) : ℝ) * (L₁ / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hL₂ : L₂ = m * L₁ / n := by
    field_simp
    linarith
  rw [hL₂]
  push_cast
  field_simp

/-- 対照群のまとめ：通約的な 2 つの対数の整数結合は、異なれば L₁/n 以上離れる（連続体は現れない）。 -/
theorem sep_of_commensurable {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) * L₂ = m * L₁) (a b a' b' : ℤ)
    (hne : (a : ℝ) * L₁ + b * L₂ ≠ a' * L₁ + b' * L₂) :
    L₁ / n ≤ |((a : ℝ) * L₁ + b * L₂) - (a' * L₁ + b' * L₂)| := by
  have hc : 0 < L₁ / n := div_pos hL₁ (by exact_mod_cast hn)
  exact sep_of_mem_zmultiples hc ⟨_, mem_zmultiples_of_commensurable hn h a b⟩
    ⟨_, mem_zmultiples_of_commensurable hn h a' b'⟩ hne

/-! ### 6. 順序版 -/

/-- ⟨p⟩ の大きさの順序は離散：1 < p^k なら p ≤ p^k（1 より大きい最小の元は p）。 -/
theorem zpow_ge_of_one_lt {p : ℕ} (hp : p.Prime) {k : ℤ} (hk : 1 < (p : ℝ) ^ k) :
    (p : ℝ) ≤ (p : ℝ) ^ k := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hk0 : 0 < k := by
    by_contra hcon
    have : (p : ℝ) ^ k ≤ 1 := zpow_le_one_of_nonpos₀ hp1.le (not_lt.mp hcon)
    linarith
  calc (p : ℝ) = (p : ℝ) ^ (1 : ℤ) := (zpow_one _).symm
    _ ≤ (p : ℝ) ^ k := zpow_le_zpow_right₀ hp1.le (by omega)

/-- ⟨p, r⟩（p ≠ r）の大きさの順序には 1 より大きい最小の元がない：どの y > 1 に対しても 1 < p^a r^b < y。 -/
theorem exists_between_one {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) {y : ℝ}
    (hy : 1 < y) :
    ∃ a b : ℤ, 1 < (p : ℝ) ^ a * (r : ℝ) ^ b ∧ (p : ℝ) ^ a * (r : ℝ) ^ b < y := by
  have hly : 0 < Real.log y := Real.log_pos hy
  obtain ⟨a, b, hab⟩ := exists_zpow_near hp hr hne (Real.log y / 2) (half_pos hly)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hz : 0 < (p : ℝ) ^ a * (r : ℝ) ^ b := mul_pos (zpow_pos hp0 a) (zpow_pos hr0 b)
  have hlog : Real.log ((p : ℝ) ^ a * (r : ℝ) ^ b) = a * Real.log p + b * Real.log r := by
    rw [Real.log_mul (zpow_ne_zero _ hp0.ne') (zpow_ne_zero _ hr0.ne'), Real.log_zpow,
      Real.log_zpow]
  have h1 := (abs_lt.mp hab).1
  have h2 := (abs_lt.mp hab).2
  refine ⟨a, b, ?_, ?_⟩
  · apply (Real.log_lt_log_iff one_pos hz).mp
    rw [Real.log_one, hlog]
    linarith
  · apply (Real.log_lt_log_iff hz (by linarith)).mp
    rw [hlog]
    linarith

end PAG.Part259

#print axioms PAG.Part259.padicValRat_prime_ne
#print axioms PAG.Part259.padicValRat_prime_zpow
#print axioms PAG.Part259.padicValRat_prod_zpow
#print axioms PAG.Part259.eq_of_padicValRat_eq
#print axioms PAG.Part259.eq_one_of_padicValRat_eq_zero
#print axioms PAG.Part259.one_le_abs_intCast_sub
#print axioms PAG.Part259.exists_prime_one_le_abs
#print axioms PAG.Part259.eq_prod_of_support
#print axioms PAG.Part259.log_eq_sum_of_support
#print axioms PAG.Part259.exists_padicValRat_eq
#print axioms PAG.Part259.closure_logSet
#print axioms PAG.Part259.dense_closure_log_primes
#print axioms PAG.Part259.exists_zpow_near
#print axioms PAG.Part259.irrational_log_div_log
#print axioms PAG.Part259.padicValRat_mul_zpow_zpow
#print axioms PAG.Part259.log_mul_zpow_zpow
#print axioms PAG.Part259.exists_near_of_two_unmeasured
#print axioms PAG.Part259.exists_near_measured
#print axioms PAG.Part259.eq_mul_zpow_of_agree
#print axioms PAG.Part259.log_sep_of_agree
#print axioms PAG.Part259.exists_mem_one_le_abs_of_support
#print axioms PAG.Part259.sep_of_inf_unmeasured
#print axioms PAG.Part259.log_sep_one_unmeasured
#print axioms PAG.Part259.exists_near_in_subgroup
#print axioms PAG.Part259.fiber_sep
#print axioms PAG.Part259.threshold_iff
#print axioms PAG.Part259.isClosed_and_discrete_of_subsingleton
#print axioms PAG.Part259.dense_imgST_iff
#print axioms PAG.Part259.isClosed_discrete_imgST
#print axioms PAG.Part259.rho_one
#print axioms PAG.Part259.exists_two_primes_not_mem
#print axioms PAG.Part259.val_ne_of_mem_of_not_mem
#print axioms PAG.Part259.dense_rho_image
#print axioms PAG.Part259.mem_closure_line_prod
#print axioms PAG.Part259.closure_rho_not_image
#print axioms PAG.Part259.rho_one_mem_closure_ne_one
#print axioms PAG.Part259.rho_sep
#print axioms PAG.Part259.isClosed_discrete_rhoBox_image
#print axioms PAG.Part259.finite_support_padicValRat
#print axioms PAG.Part259.eq_prod_support
#print axioms PAG.Part259.sep_of_mem_zmultiples
#print axioms PAG.Part259.mem_zmultiples_of_commensurable
#print axioms PAG.Part259.sep_of_commensurable
#print axioms PAG.Part259.zpow_ge_of_one_lt
#print axioms PAG.Part259.exists_between_one
