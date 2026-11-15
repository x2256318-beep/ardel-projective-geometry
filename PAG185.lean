/-
  PAG 2.0 Part 181（2026-10-22）— 位数 n ≥ 3 の指標では z = τ(χ)/√p は 1 の冪根でない
  p は素数、χ は法 p の乗法的指標で n = ord χ、ψ は原始的な加法的指標、z = τ(χ)/√p、k = (p − 1)/n。
  1. べき和：0 < e < 2(p − 1) で Σ_x x^e = (e = p − 1 なら −1、それ以外は 0)
  2. 冪の指標 x ↦ x^u のヤコビ和 Σ_x x^u (1 − x)^v：u + v < p − 1 なら 0、u + v ≥ p − 1 なら
     −(−1)^{p−1−u} C(v, p−1−u) ≠ 0（Stickelberger 型の合同）
  3. 評価：μ = χ(生成元) とし、ℤ[μ] → 𝔽_p の環準同型 ev で ev ∘ χ = (x ↦ x^k)
  4. gauss_not_root：n ≥ 3 なら z^N ≠ 1（N > 0）。jacobi_not_root：J(χ, χ)/√p も同様
  5. gauss_root_iff：z が 1 の冪根 ⇔ ord χ = 2（法 p の指標についての完全な判定）
  6. 鎖の記号での形：zOf_not_root_chain、zOf_root_iff_chain（PAG184 の zOf）
-/
import PAG184
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

namespace PAG.Part185

open Complex Finset Polynomial
open ZMod (stdAddChar)

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### 1. べき和 -/

/-- **1a.** 0 ≤ e < p − 1 なら Σ_x x^e = 0。 -/
theorem sum_pow_lt (e : ℕ) (he : e < p - 1) : ∑ x : ZMod p, x ^ e = 0 := by
  apply FiniteField.sum_pow_lt_card_sub_one
  rwa [ZMod.card]

/-- **1b.** Σ_x x^{p−1} = −1。 -/
theorem sum_pow_card_sub_one : ∑ x : ZMod p, x ^ (p - 1) = -1 := by
  classical
  have h2 := hp.out.two_le
  have h : ∀ x : ZMod p, x ^ (p - 1) = 1 - if x = 0 then 1 else 0 := by
    intro x
    by_cases hx : x = 0
    · rw [ite_eq_left hx, hx, zero_pow (by omega), sub_self]
    · rw [ite_eq_right hx, ZMod.pow_card_sub_one_eq_one hx, sub_zero]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ZMod.natCast_self, zero_sub]

/-- **1c.** 0 < e < 2(p − 1) なら Σ_x x^e = (e = p − 1 なら −1、それ以外は 0)。 -/
theorem sum_pow_eq (e : ℕ) (he0 : 0 < e) (he : e < 2 * (p - 1)) :
    ∑ x : ZMod p, x ^ e = if e = p - 1 then -1 else 0 := by
  rcases lt_trichotomy e (p - 1) with h | h | h
  · rw [ite_eq_right (show ¬e = p - 1 by omega), sum_pow_lt e h]
  · rw [ite_eq_left h, h, sum_pow_card_sub_one]
  · rw [ite_eq_right (show ¬e = p - 1 by omega)]
    have hx : ∀ x : ZMod p, x ^ e = x ^ (e - (p - 1)) := by
      intro x
      by_cases hx : x = 0
      · rw [hx, zero_pow (by omega), zero_pow (by omega)]
      · conv_lhs => rw [show e = (e - (p - 1)) + (p - 1) by omega, pow_add,
          ZMod.pow_card_sub_one_eq_one hx, mul_one]
    simp only [hx]
    exact sum_pow_lt _ (by omega)

/-! ### 2. 冪の指標とそのヤコビ和 -/

/-- **2a.** x ↦ x^k を単数の上の準同型として乗法的指標にしたもの（0 では 0）。 -/
noncomputable def powChar (k : ℕ) : MulChar (ZMod p) (ZMod p) :=
  MulChar.ofUnitHom (powMonoidHom k)

theorem powChar_apply (k : ℕ) (hk : 0 < k) (x : ZMod p) : powChar k x = x ^ k := by
  by_cases hx : x = 0
  · rw [hx, MulChar.map_zero, zero_pow hk.ne']
  · have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [← hu.unit_spec, powChar, MulChar.ofUnitHom_coe, powMonoidHom_apply, Units.val_pow_eq_pow_val]

theorem powChar_pow (k m : ℕ) : powChar (p := p) k ^ m = powChar (k * m) := by
  refine MulChar.ext (fun u => ?_)
  simp only [MulChar.pow_apply_coe, powChar, MulChar.ofUnitHom_coe, powMonoidHom_apply,
    Units.val_pow_eq_pow_val, ← pow_mul]

theorem jacobi_powChar (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    jacobiSum (powChar (p := p) u) (powChar v) = ∑ x : ZMod p, x ^ u * (1 - x) ^ v := by
  simp only [jacobiSum, powChar_apply u hu, powChar_apply v hv]

/-- **2b.** 二項展開：Σ_x x^u (1 − x)^v = Σ_m (−1)^m C(v, m) Σ_x x^{u+m}。 -/
theorem sum_mul_one_sub_pow (u v : ℕ) :
    ∑ x : ZMod p, x ^ u * (1 - x) ^ v =
      ∑ m ∈ range (v + 1), (-1) ^ m * (v.choose m : ZMod p) * ∑ x : ZMod p, x ^ (u + m) := by
  have h : ∀ x : ZMod p, x ^ u * (1 - x) ^ v =
      ∑ m ∈ range (v + 1), (-1) ^ m * (v.choose m : ZMod p) * x ^ (u + m) := by
    intro x
    rw [show (1 : ZMod p) - x = -x + 1 by ring, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [one_pow, mul_one, neg_pow, pow_add]
    ring
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum]

/-- **2c. 消える側**：u + v < p − 1 なら J(x^u, x^v) = 0。 -/
theorem jacobi_powChar_eq_zero (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (huv : u + v < p - 1) :
    jacobiSum (powChar (p := p) u) (powChar v) = 0 := by
  rw [jacobi_powChar u v hu hv, sum_mul_one_sub_pow]
  refine Finset.sum_eq_zero (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  rw [sum_pow_lt (u + m) (by omega), mul_zero]

theorem choose_ne_zero_mod (v j : ℕ) (hv : v < p) (hj : j ≤ v) : (v.choose j : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have h1 := Nat.choose_mul_factorial_mul_factorial hj
  have h2 : p ∣ v.factorial := h1 ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_right hdvd _) _
  have hfact : ∀ w, w < p → ¬ p ∣ w.factorial := by
    intro w
    induction w with
    | zero =>
      intro _ h
      rw [Nat.factorial_zero, Nat.dvd_one] at h
      exact hp.out.one_lt.ne' h
    | succ w ih =>
      intro hw h
      rw [Nat.factorial_succ] at h
      rcases (Nat.Prime.dvd_mul hp.out).mp h with h1 | h1
      · exact absurd (Nat.le_of_dvd (Nat.succ_pos w) h1) (by omega)
      · exact ih (by omega) h1
  exact hfact v hv h2

/-- **2d. 値の公式**：u, v < p − 1 ≤ u + v なら J(x^u, x^v) = −(−1)^{p−1−u} C(v, p−1−u)。 -/
theorem jacobi_powChar_eq (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hu' : u < p - 1) (hv' : v < p - 1)
    (huv : p - 1 ≤ u + v) :
    jacobiSum (powChar (p := p) u) (powChar v)
      = -((-1) ^ (p - 1 - u) * (v.choose (p - 1 - u) : ZMod p)) := by
  rw [jacobi_powChar u v hu hv, sum_mul_one_sub_pow]
  have key : ∀ m ∈ range (v + 1), (-1) ^ m * (v.choose m : ZMod p) * ∑ x : ZMod p, x ^ (u + m)
      = if m = p - 1 - u then -((-1) ^ m * (v.choose m : ZMod p)) else 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [sum_pow_eq (u + m) (by omega) (by omega)]
    by_cases h : m = p - 1 - u
    · rw [ite_eq_left (show u + m = p - 1 by omega), ite_eq_left h]; ring
    · rw [ite_eq_right (show ¬u + m = p - 1 by omega), ite_eq_right h, mul_zero]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq',
    ite_eq_left (show p - 1 - u ∈ range (v + 1) by rw [Finset.mem_range]; omega)]

/-- **2e. 消えない側**。 -/
theorem jacobi_powChar_ne_zero (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hu' : u < p - 1) (hv' : v < p - 1)
    (huv : p - 1 ≤ u + v) :
    jacobiSum (powChar (p := p) u) (powChar v) ≠ 0 := by
  rw [jacobi_powChar_eq u v hu hv hu' hv' huv, neg_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (choose_ne_zero_mod v _ (by omega) (by omega))

/-! ### 3. ℤ[μ] から 𝔽_p への評価 -/

/-- 𝔽_p^× の生成元 a：すべての単数は a の自然数冪。 -/
theorem exists_gen : ∃ a : (ZMod p)ˣ, ∀ x : (ZMod p)ˣ, ∃ j : ℕ, a ^ j = x := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  exact ⟨a, fun x => (Submonoid.mem_powers_iff x a).mp (mem_powers_iff_mem_zpowers.mpr (ha x))⟩

theorem orderOf_gen (a : (ZMod p)ˣ) (ha : ∀ x : (ZMod p)ˣ, ∃ j : ℕ, a ^ j = x) :
    orderOf a = p - 1 := by
  have hall : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers a := fun x => by
    obtain ⟨j, rfl⟩ := ha x
    exact Subgroup.npow_mem_zpowers a j
  rw [orderOf_eq_card_of_forall_mem_zpowers hall, Nat.card_eq_fintype_card, ZMod.card_units]

/-- **3a.** μ = χ(a) は 1 の原始 ord χ 乗根。 -/
theorem isPrimitiveRoot_gen (χ : MulChar (ZMod p) ℂ) (a : (ZMod p)ˣ)
    (ha : ∀ x : (ZMod p)ˣ, ∃ j : ℕ, a ^ j = x) : IsPrimitiveRoot (χ a) (orderOf χ) := by
  refine ⟨?_, fun l hl => ?_⟩
  · rw [← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
  · apply orderOf_dvd_of_pow_eq_one
    rw [MulChar.eq_one_iff]
    intro x
    obtain ⟨j, rfl⟩ := ha x
    rw [MulChar.pow_apply_coe, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, mul_comm, pow_mul, hl,
      one_pow]

theorem orderOf_dvd_sub_one (χ : MulChar (ZMod p) ℂ) : orderOf χ ∣ p - 1 := by
  obtain ⟨a, ha⟩ := exists_gen (p := p)
  apply (isPrimitiveRoot_gen χ a ha).dvd_of_pow_eq_one
  rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one,
    map_one]

theorem orderOf_pos_chi (χ : MulChar (ZMod p) ℂ) : 0 < orderOf χ :=
  Nat.pos_of_dvd_of_pos (orderOf_dvd_sub_one χ) (by have := hp.out.two_le; omega)

/-- χ の値を ℤ[μ] ⊆ ℂ に制限した指標。 -/
noncomputable def chiA (χ : MulChar (ZMod p) ℂ) {μ : ℂ} (hμ : IsPrimitiveRoot μ (orderOf χ)) :
    MulChar (ZMod p) (Algebra.adjoin ℤ ({μ} : Set ℂ)) where
  toFun x := ⟨χ x, by
    have : NeZero (orderOf χ) := ⟨(orderOf_pos_chi χ).ne'⟩
    exact MulChar.apply_mem_algebraAdjoin_of_pow_eq_one (pow_orderOf_eq_one χ) hμ x⟩
  map_one' := Subtype.ext (map_one χ)
  map_mul' x y := Subtype.ext (map_mul χ x y)
  map_nonunit' x hx := Subtype.ext (χ.map_nonunit hx)

@[simp] theorem chiA_apply (χ : MulChar (ZMod p) ℂ) {μ : ℂ} (hμ : IsPrimitiveRoot μ (orderOf χ))
    (x : ZMod p) : ((chiA χ hμ x : Algebra.adjoin ℤ ({μ} : Set ℂ)) : ℂ) = χ x := rfl

/-- **3b. 評価の存在**：部分環 A = ℤ[μ] ⊆ ℂ、A に値をもつ χ_A、環準同型 ev : A → 𝔽_p があって、
  χ_A を ℂ に戻すと χ、ev で 𝔽_p に送ると x ↦ x^k（k = (p − 1)/ord χ）。 -/
theorem exists_eval (χ : MulChar (ZMod p) ℂ) :
    ∃ (A : Subalgebra ℤ ℂ) (χA : MulChar (ZMod p) A) (ev : A →+* ZMod p),
      A ≤ integralClosure ℤ ℂ ∧ χA.ringHomComp A.val.toRingHom = χ ∧
        χA.ringHomComp ev = powChar ((p - 1) / orderOf χ) := by
  obtain ⟨a, ha⟩ := exists_gen (p := p)
  have hμ := isPrimitiveRoot_gen χ a ha
  have hnpos : 0 < orderOf χ := orderOf_pos_chi χ
  have hdvd : orderOf χ ∣ p - 1 := orderOf_dvd_sub_one χ
  have h2 := hp.out.two_le
  have hkn : (p - 1) / orderOf χ * orderOf χ = p - 1 := Nat.div_mul_cancel hdvd
  have hkpos : 0 < (p - 1) / orderOf χ := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hnpos
  -- g = a^k は 𝔽_p の 1 の原始 n 乗根
  have hga : IsPrimitiveRoot ((a : ZMod p)) (p - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, ← orderOf_gen a ha]; exact IsPrimitiveRoot.orderOf a
  have hg : IsPrimitiveRoot ((a : ZMod p) ^ ((p - 1) / orderOf χ)) (orderOf χ) := by
    have := hga.pow_of_dvd hkpos.ne' (Dvd.intro _ hkn)
    rwa [Nat.div_div_self hdvd (by omega)] at this
  -- ℤ[μ] の冪基底と最小多項式 Φ_n
  have hint : IsIntegral ℤ (χ a) := hμ.isIntegral hnpos
  obtain ⟨pb, hgen⟩ : ∃ pb : PowerBasis ℤ (Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ)),
      pb.gen = ⟨χ a, Algebra.subset_adjoin (Set.mem_singleton _)⟩ :=
    ⟨Algebra.adjoin.powerBasis' hint, Algebra.adjoin.powerBasis'_gen hint⟩
  have hmin : minpoly ℤ pb.gen = cyclotomic (orderOf χ) ℤ := by
    rw [hgen, ← minpoly.algHom_eq (Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ)).val Subtype.val_injective]
    exact (cyclotomic_eq_minpoly hμ hnpos).symm
  have : NeZero ((orderOf χ : ℕ) : ZMod p) := ⟨by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
    have := Nat.le_of_dvd hnpos h; have := Nat.le_of_dvd (by omega) hdvd; omega⟩
  have hroot : aeval ((a : ZMod p) ^ ((p - 1) / orderOf χ)) (minpoly ℤ pb.gen) = 0 := by
    rw [hmin, aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact isRoot_cyclotomic_iff.mpr hg
  obtain ⟨ev, hevg⟩ : ∃ ev : Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ) →ₐ[ℤ] ZMod p,
      ev pb.gen = (a : ZMod p) ^ ((p - 1) / orderOf χ) := ⟨pb.lift _ hroot, pb.lift_gen _ hroot⟩
  have hev : ∀ y : ZMod p, ev (chiA χ hμ y) = y ^ ((p - 1) / orderOf χ) := by
    intro y
    by_cases hy : y = 0
    · rw [hy, MulChar.map_zero, map_zero, zero_pow hkpos.ne']
    · obtain ⟨j, hj⟩ := ha (Units.mk0 y hy)
      have hy' : y = ((a : ZMod p)) ^ j := by rw [← Units.val_pow_eq_pow_val, hj, Units.val_mk0]
      have hc : chiA χ hμ y = pb.gen ^ j := by
        rw [hgen]
        apply Subtype.ext
        rw [chiA_apply, SubmonoidClass.coe_pow, hy', map_pow]
      rw [hc, map_pow, hevg, hy', ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨_, chiA χ hμ, ev.toRingHom, adjoin_le_integralClosure hint, MulChar.ext' (fun x => rfl),
    MulChar.ext' (fun y => ?_)⟩
  rw [MulChar.ringHomComp_apply, powChar_apply _ hkpos]
  exact hev y

/-- **3c.** ヤコビ和は A から ℂ に戻せる。 -/
theorem jacobi_val {A : Subalgebra ℤ ℂ} {χA : MulChar (ZMod p) A} {χ : MulChar (ZMod p) ℂ}
    (hval : χA.ringHomComp A.val.toRingHom = χ) (s t : ℕ) :
    jacobiSum (χ ^ s) (χ ^ t) = ((jacobiSum (χA ^ s) (χA ^ t) : A) : ℂ) := by
  rw [← hval, MulChar.ringHomComp_pow, MulChar.ringHomComp_pow, jacobiSum_ringHomComp]
  all_goals rfl

/-- **3d.** ヤコビ和の評価：ev J(χ_A^s, χ_A^t) = J(x^{ks}, x^{kt})。 -/
theorem jacobi_ev {A : Subalgebra ℤ ℂ} {χA : MulChar (ZMod p) A} {ev : A →+* ZMod p} {k : ℕ}
    (hev : χA.ringHomComp ev = powChar k) (s t : ℕ) :
    ev (jacobiSum (χA ^ s) (χA ^ t)) = jacobiSum (powChar (k * s)) (powChar (k * t)) := by
  rw [← jacobiSum_ringHomComp, ← MulChar.ringHomComp_pow, ← MulChar.ringHomComp_pow, hev, powChar_pow,
    powChar_pow]

/-! ### 4. ガウス和の n 乗とヤコビ和の積 P, P̄ -/

theorem sqrt_ne_zero : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)
  exact_mod_cast this.ne'

omit hp in
theorem sqrt_sq_cast : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
  rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
  simp

/-- (x/√p)^N = 1 なら x^{2N} = p^N。 -/
theorem pow_two_mul_of_root (x : ℂ) (N : ℕ) (h : (x / ((Real.sqrt p : ℝ) : ℂ)) ^ N = 1) :
    x ^ (2 * N) = (p : ℂ) ^ N := by
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ sqrt_ne_zero)] at h
  rw [mul_comm, pow_mul, h, ← pow_mul, mul_comm, pow_mul, sqrt_sq_cast]

theorem ringChar_ne : ringChar ℂ ≠ ringChar (ZMod p) := by
  rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact hp.out.ne_zero.symm

/-- P(χ) = ∏_{i=1}^{n−2} J(χ, χ^i)（n = ord χ）。 -/
noncomputable def Pj (χ : MulChar (ZMod p) ℂ) : ℂ :=
  ∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum χ (χ ^ i)

/-- P̄(χ) = ∏_{i=1}^{n−2} J(χ^{n−1}, χ^{n−i})（逆の指標どうしのヤコビ和の積）。 -/
noncomputable def Pjbar (χ : MulChar (ZMod p) ℂ) : ℂ :=
  ∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum (χ ^ (orderOf χ - 1)) (χ ^ (orderOf χ - i))

omit hp in
theorem inv_pow_eq (χ : MulChar (ZMod p) ℂ) (i : ℕ) (hi : i ≤ orderOf χ) :
    (χ ^ i)⁻¹ = χ ^ (orderOf χ - i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, Nat.add_sub_cancel' hi, pow_orderOf_eq_one]

/-- **4a.** τ^n = χ(−1)·p·P（Mathlib の gaussSum_pow_eq_prod_jacobiSum）。 -/
theorem gauss_pow_order (χ : MulChar (ZMod p) ℂ) (hn : 2 ≤ orderOf χ) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) : gaussSum χ ψ ^ orderOf χ = χ (-1) * p * Pj χ := by
  have := gaussSum_pow_eq_prod_jacobiSum hn hψ
  rwa [ZMod.card] at this

/-- **4b.** P·P̄ = p^{n−2}（n ≥ 3）。 -/
theorem Pj_mul_Pjbar (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ) :
    Pj χ * Pjbar χ = (p : ℂ) ^ (orderOf χ - 2) := by
  have hpow : ∀ i, 0 < i → i < orderOf χ → χ ^ i ≠ 1 :=
    fun i hi hin => pow_ne_one_of_lt_orderOf hi.ne' hin
  have hχ1 : χ ≠ 1 := by simpa using hpow 1 (by omega) (by omega)
  have hpair : ∀ i ∈ Ico 1 (orderOf χ - 1),
      jacobiSum χ (χ ^ i) * jacobiSum (χ ^ (orderOf χ - 1)) (χ ^ (orderOf χ - i)) = (p : ℂ) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have := jacobiSum_mul_jacobiSum_inv ringChar_ne hχ1 (hpow i (by omega) (by omega))
      (by rw [← pow_succ']; exact hpow (i + 1) (by omega) (by omega))
    have h1 := inv_pow_eq χ 1 (by omega)
    rw [pow_one] at h1
    rwa [h1, inv_pow_eq χ i (by omega), ZMod.card] at this
  rw [Pj, Pjbar, ← Finset.prod_mul_distrib, Finset.prod_congr rfl hpair, Finset.prod_const,
    Nat.card_Ico, show orderOf χ - 1 - 1 = orderOf χ - 2 by omega]

/-- **4c.** z^{2n}·P̄ = P（つまり z^{2n} = P/P̄）。 -/
theorem z_pow_mul_Pjbar (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) :
    (gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * orderOf χ) * Pjbar χ = Pj χ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hm1 : χ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have hT := gauss_pow_order χ (by omega) hψ
  have hPP := Pj_mul_Pjbar χ hn
  rw [div_pow, mul_comm 2 (orderOf χ), pow_mul, hT, pow_mul', sqrt_sq_cast, div_mul_eq_mul_div,
    div_eq_iff (pow_ne_zero _ hp0)]
  calc (χ (-1) * p * Pj χ) ^ 2 * Pjbar χ = χ (-1) ^ 2 * ((p : ℂ) ^ 2 * (Pj χ * (Pj χ * Pjbar χ))) := by
        ring
    _ = Pj χ * (p : ℂ) ^ (2 + (orderOf χ - 2)) := by rw [hm1, hPP]; ring
    _ = Pj χ * (p : ℂ) ^ orderOf χ := by rw [Nat.add_sub_cancel' (by omega : 2 ≤ orderOf χ)]

/-- **4d.** z^N = 1 なら P^N = P̄^N。 -/
theorem Pj_pow_eq_of_root (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) (N : ℕ) (h : (gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ N = 1) :
    Pj χ ^ N = Pjbar χ ^ N := by
  have hz := z_pow_mul_Pjbar χ hn hψ
  have h1 : ((gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * orderOf χ)) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h, one_pow]
  rw [← hz, mul_pow, h1, one_mul]

/-- 不等式の補助：k > 0、1 ≤ i、i + 2 ≤ n のとき u = k(n − 1)、v = k(n − i) が
  2e の条件をみたす（p − 1 = kn）。 -/
theorem aux_ineq (k n i : ℕ) (hk : 0 < k) (hi1 : 1 ≤ i) (hin : i + 2 ≤ n) :
    0 < k * (n - 1) ∧ 0 < k * (n - i) ∧ k * (n - 1) < k * n ∧ k * (n - i) < k * n ∧
      k * n ≤ k * (n - 1) + k * (n - i) := by
  obtain ⟨b, rfl⟩ : ∃ b, n = i + 2 + b := ⟨n - (i + 2), by omega⟩
  rw [show i + 2 + b - 1 = i + 1 + b by omega, show i + 2 + b - i = 2 + b by omega]
  refine ⟨Nat.mul_pos hk (by omega), Nat.mul_pos hk (by omega), by nlinarith, by nlinarith, by nlinarith⟩

/-- **4e. 評価で P と P̄ を区別する**：ℤ[μ] ⊆ ℂ の元 x, y（x = P、y = P̄）と
  環準同型 ev : ℤ[μ] → 𝔽_p があって、ev x = 0、ev y ≠ 0。 -/
theorem exists_eval_Pj (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ) :
    ∃ (A : Subalgebra ℤ ℂ) (ev : A →+* ZMod p) (x y : A), A ≤ integralClosure ℤ ℂ ∧
      (x : ℂ) = Pj χ ∧ (y : ℂ) = Pjbar χ ∧ ev x = 0 ∧ ev y ≠ 0 := by
  obtain ⟨A, χA, ev, hA, hval, hev⟩ := exists_eval χ
  have hdvd := orderOf_dvd_sub_one χ
  have h2 := hp.out.two_le
  have hkn : (p - 1) / orderOf χ * orderOf χ = p - 1 := Nat.div_mul_cancel hdvd
  have hk : 0 < (p - 1) / orderOf χ := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
  set k := (p - 1) / orderOf χ with hk_def
  refine ⟨A, ev, ∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum (χA ^ 1) (χA ^ i),
    ∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum (χA ^ (orderOf χ - 1)) (χA ^ (orderOf χ - i)), hA,
    ?_, ?_, ?_, ?_⟩
  · rw [SubmonoidClass.coe_finsetProd, Pj]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← jacobi_val hval 1 i, pow_one]
  · rw [SubmonoidClass.coe_finsetProd, Pjbar]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← jacobi_val hval]
  · rw [map_prod]
    apply Finset.prod_eq_zero (show (1 : ℕ) ∈ Ico 1 (orderOf χ - 1) by rw [Finset.mem_Ico]; omega)
    rw [jacobi_ev hev, mul_one]
    exact jacobi_powChar_eq_zero _ _ hk hk (by rw [← hkn]; nlinarith)
  · rw [map_prod, Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [jacobi_ev hev]
    obtain ⟨h1, h2, h3, h4, h5⟩ := aux_ineq _ (orderOf χ) i hk hi.1 (by omega)
    exact jacobi_powChar_ne_zero _ _ h1 h2 (hkn ▸ h3) (hkn ▸ h4) (hkn ▸ h5)

/-! ### 5. 主定理 -/

/-- **5a. 主定理**：ord χ ≥ 3 なら z = τ(χ)/√p は 1 の冪根でない。 -/
theorem gauss_not_root (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) (N : ℕ) (hN : 0 < N) :
    (gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ N ≠ 1 := by
  intro h
  obtain ⟨A, ev, x, y, -, hx, hy, hx0, hy0⟩ := exists_eval_Pj χ hn
  have hPN := Pj_pow_eq_of_root χ hn hψ N h
  have hxy : x ^ N = y ^ N := by
    apply Subtype.val_injective
    simp only [SubmonoidClass.coe_pow]
    rw [hx, hy, hPN]
  have := congrArg ev hxy
  rw [map_pow, map_pow, hx0, zero_pow hN.ne'] at this
  exact hy0 (pow_eq_zero_iff hN.ne' |>.mp this.symm)

/-- **5b.** 同じ評価で、ヤコビ和の位相 J(χ, χ)/√p も ord χ ≥ 3 なら 1 の冪根でない。 -/
theorem jacobi_not_root (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ) (N : ℕ) (hN : 0 < N) :
    (jacobiSum χ χ / ((Real.sqrt p : ℝ) : ℂ)) ^ N ≠ 1 := by
  intro h
  obtain ⟨A, χA, ev, -, hval, hev⟩ := exists_eval χ
  have hdvd := orderOf_dvd_sub_one χ
  set n := orderOf χ with hn_def
  set k := (p - 1) / n with hk_def
  have h2 := hp.out.two_le
  have hkn : k * n = p - 1 := Nat.div_mul_cancel hdvd
  have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpow : ∀ i, 0 < i → i < n → χ ^ i ≠ 1 := fun i hi hin => pow_ne_one_of_lt_orderOf hi.ne' hin
  have hχ1 : χ ≠ 1 := by simpa using hpow 1 (by omega) (by omega)
  have hinv : χ⁻¹ = χ ^ (n - 1) := by
    have h1 := inv_pow_eq χ 1 (by omega)
    rwa [pow_one] at h1
  have hpair : jacobiSum χ χ * jacobiSum (χ ^ (n - 1)) (χ ^ (n - 1)) = (p : ℂ) := by
    have := jacobiSum_mul_jacobiSum_inv ringChar_ne hχ1 hχ1
      (by rw [← sq]; exact hpow 2 (by omega) (by omega))
    rwa [hinv, ZMod.card] at this
  have h2N := pow_two_mul_of_root _ N h
  have hJne : jacobiSum χ χ ≠ 0 := left_ne_zero_of_mul (by rw [hpair]; exact hp0)
  have hJN : jacobiSum χ χ ^ N = jacobiSum (χ ^ (n - 1)) (χ ^ (n - 1)) ^ N := by
    have e3 : jacobiSum χ χ ^ N * jacobiSum χ χ ^ N
        = jacobiSum χ χ ^ N * jacobiSum (χ ^ (n - 1)) (χ ^ (n - 1)) ^ N := by
      rw [← pow_add, ← two_mul, h2N, ← mul_pow, hpair]
    exact mul_left_cancel₀ (pow_ne_zero _ hJne) e3
  have hA : jacobiSum (χA ^ 1) (χA ^ 1) ^ N = jacobiSum (χA ^ (n - 1)) (χA ^ (n - 1)) ^ N := by
    apply Subtype.val_injective
    simp only [SubmonoidClass.coe_pow]
    rw [← jacobi_val hval, ← jacobi_val hval, pow_one, hJN]
  have hevA := congrArg ev hA
  rw [map_pow, map_pow, jacobi_ev hev, jacobi_ev hev, mul_one,
    jacobi_powChar_eq_zero k k hk hk (by rw [← hkn]; nlinarith), zero_pow hN.ne'] at hevA
  have hu : 0 < k * (n - 1) := Nat.mul_pos hk (by omega)
  have hu' : k * (n - 1) < k * n := Nat.mul_lt_mul_of_pos_left (by omega) hk
  have huv : k * n ≤ k * (n - 1) + k * (n - 1) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left k (by omega)
  exact jacobi_powChar_ne_zero _ _ hu hu (hkn ▸ hu') (hkn ▸ hu') (hkn ▸ huv)
    (pow_eq_zero_iff hN.ne' |>.mp hevA.symm)

/-! ### 6. 完全な判定 -/

/-- **6. z が 1 の冪根 ⇔ ord χ = 2**（自明な指標では z = −1/√p で |z| < 1、2 次では z⁴ = 1）。 -/
theorem gauss_root_iff (χ : MulChar (ZMod p) ℂ) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    (∃ N : ℕ, 0 < N ∧ (gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ N = 1) ↔ orderOf χ = 2 := by
  have hψ1 : ψ ≠ 1 := by
    intro h1; apply hψ (one_ne_zero (α := ZMod p)); rw [AddChar.mulShift_one, h1]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · rintro ⟨N, hN, h⟩
    by_contra h2
    have hpos : 0 < orderOf χ := orderOf_pos_chi χ
    rcases (show orderOf χ = 1 ∨ 3 ≤ orderOf χ by omega) with h1 | h3
    · rw [orderOf_eq_one_iff] at h1
      rw [h1, gaussSum_one_left hψ1] at h
      have hs : (1 : ℝ) < Real.sqrt p := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast hp.out.one_lt)
      have hlt : ‖(-1 : ℂ) / ((Real.sqrt p : ℝ) : ℂ)‖ < 1 := by
        rw [norm_div, norm_neg, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith), div_lt_one (by linarith)]
        exact hs
      have := congrArg norm h
      rw [norm_pow, norm_one] at this
      exact (pow_lt_one₀ (norm_nonneg _) hlt hN.ne').ne this
    · exact gauss_not_root χ h3 hψ N hN h
  · intro h2
    refine ⟨4, by norm_num, ?_⟩
    have hχ1 : χ ≠ 1 := by intro h1; rw [h1, orderOf_one] at h2; norm_num at h2
    have hq : χ.IsQuadratic :=
      MulChar.isQuadratic_iff_sq_eq_one.mpr (by rw [← h2]; exact pow_orderOf_eq_one χ)
    have hsq := gaussSum_sq hχ1 hq hψ
    rw [ZMod.card] at hsq
    have hm1 : χ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
    rw [div_pow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, hsq, sqrt_sq_cast, mul_pow, hm1,
      one_mul, div_self (pow_ne_zero 2 hp0)]

/-! ### 7. ディリクレ指標と標準の加法的指標での形 -/

theorem zOf_not_root (χ : DirichletCharacter ℂ p) (hn : 3 ≤ orderOf χ) (N : ℕ) (hN : 0 < N) :
    (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ N ≠ 1 :=
  gauss_not_root χ hn (ZMod.isPrimitive_stdAddChar p) N hN

theorem zOf_root_iff (χ : DirichletCharacter ℂ p) :
    (∃ N : ℕ, 0 < N ∧ (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ N = 1) ↔ orderOf χ = 2 :=
  gauss_root_iff χ (ZMod.isPrimitive_stdAddChar p)

/-- ζ = z^{ord χ} は無限位数（ord χ ≥ 3）。 -/
theorem zeta_infinite (χ : DirichletCharacter ℂ p) (hn : 3 ≤ orderOf χ) :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ orderOf χ) = 0 := by
  rw [orderOf_eq_zero_iff']
  intro M hM
  rw [← pow_mul]
  exact zOf_not_root χ hn _ (Nat.mul_pos (by omega) hM)

/-- 引き継ぎメモの「第一候補」：位数 5 の場合。 -/
theorem quintic_not_root (χ : DirichletCharacter ℂ p) (h5 : orderOf χ = 5) (N : ℕ) (hN : 0 < N) :
    (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ N ≠ 1 :=
  zOf_not_root χ (by rw [h5]; norm_num) N hN

/-! ### 8. 鎖の記号（PAG184 の zOf）での形 -/

/-- PAG184 の `zOf` での主定理（`zOf χ = τ(χ)/√p` は定義から同じ）。 -/
theorem zOf_not_root_chain (χ : DirichletCharacter ℂ p) (hn : 3 ≤ orderOf χ) (N : ℕ) (hN : 0 < N) :
    PAG.Part184.zOf χ ^ N ≠ 1 :=
  zOf_not_root χ hn N hN

theorem zOf_root_iff_chain (χ : DirichletCharacter ℂ p) :
    (∃ N : ℕ, 0 < N ∧ PAG.Part184.zOf χ ^ N = 1) ↔ orderOf χ = 2 :=
  zOf_root_iff χ

end PAG.Part185

#print axioms PAG.Part185.sum_pow_lt
#print axioms PAG.Part185.sum_pow_card_sub_one
#print axioms PAG.Part185.sum_pow_eq
#print axioms PAG.Part185.powChar_apply
#print axioms PAG.Part185.powChar_pow
#print axioms PAG.Part185.jacobi_powChar
#print axioms PAG.Part185.sum_mul_one_sub_pow
#print axioms PAG.Part185.jacobi_powChar_eq_zero
#print axioms PAG.Part185.choose_ne_zero_mod
#print axioms PAG.Part185.jacobi_powChar_eq
#print axioms PAG.Part185.jacobi_powChar_ne_zero
#print axioms PAG.Part185.exists_gen
#print axioms PAG.Part185.orderOf_gen
#print axioms PAG.Part185.isPrimitiveRoot_gen
#print axioms PAG.Part185.orderOf_dvd_sub_one
#print axioms PAG.Part185.orderOf_pos_chi
#print axioms PAG.Part185.chiA_apply
#print axioms PAG.Part185.exists_eval
#print axioms PAG.Part185.jacobi_val
#print axioms PAG.Part185.jacobi_ev
#print axioms PAG.Part185.sqrt_ne_zero
#print axioms PAG.Part185.sqrt_sq_cast
#print axioms PAG.Part185.pow_two_mul_of_root
#print axioms PAG.Part185.ringChar_ne
#print axioms PAG.Part185.inv_pow_eq
#print axioms PAG.Part185.gauss_pow_order
#print axioms PAG.Part185.Pj_mul_Pjbar
#print axioms PAG.Part185.z_pow_mul_Pjbar
#print axioms PAG.Part185.Pj_pow_eq_of_root
#print axioms PAG.Part185.aux_ineq
#print axioms PAG.Part185.exists_eval_Pj
#print axioms PAG.Part185.gauss_not_root
#print axioms PAG.Part185.jacobi_not_root
#print axioms PAG.Part185.gauss_root_iff
#print axioms PAG.Part185.zOf_not_root
#print axioms PAG.Part185.zOf_root_iff
#print axioms PAG.Part185.zeta_infinite
#print axioms PAG.Part185.quintic_not_root
#print axioms PAG.Part185.zOf_not_root_chain
#print axioms PAG.Part185.zOf_root_iff_chain
