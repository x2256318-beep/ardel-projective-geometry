/-
  PAG 2.0 Part 10（2026-10-18）
  1. 馴分位数の同定 ord(χ^(p^n)) = tameOrder χ と、χ^(p^n) の導手の二分法
  2. 殻遷移と導手降下の統合定理（PAG9 の D と PAG13 の導手公式）
  3. 球平均の吸収律からの直交べき等元（フーリエ変換を使わない）と望遠鏡和
  4. 定常位相の 1 項抽出（加法指標の直交性）と持ち上げ不変性
-/
import PAG13

namespace PAG.Part14

open PAG.Part9 PAG.Part13 Finset

/-! ## 1. 馴分位数の同定 -/

section Tame

variable {p n : ℕ} [hp : Fact p.Prime]

/-- **ord(χ^(p^n)) = tameOrder χ**（Part 9 の限定の解除）。 -/
theorem orderOf_pow_pn_eq_tameOrder (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : orderOf (χ ^ (p ^ n)) = tameOrder χ := by
  rw [orderOf_pow' χ (pow_ne_zero n hp.out.ne_zero),
    Nat.gcd_eq_right (pow_dvd_orderOf hodd χ hχ)]
  rfl

theorem tameOrder_pos (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : 0 < tameOrder χ := by
  rcases Nat.eq_zero_or_pos (tameOrder χ) with h | h
  · exfalso; apply orderOf_ne_zero χ; rw [orderOf_eq hodd χ hχ, h, mul_zero]
  · exact h

/-- χ^(p^n) の導手は p を割る。 -/
theorem conductor_pow_pn_dvd_p (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    (χ ^ (p ^ n)).conductor ∣ p := by
  have := PAG.Part12.conductor_pow_pr_dvd_p hodd (r := n) le_rfl 1 χ
  rwa [mul_one] at this

/-- tameOrder χ = 1 ⇔ χ^(p^n) = 1。 -/
theorem tameOrder_eq_one_iff (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : tameOrder χ = 1 ↔ χ ^ (p ^ n) = 1 := by
  rw [← orderOf_pow_pn_eq_tameOrder hodd χ hχ, orderOf_eq_one_iff]

/-- tameOrder χ = 1 ⇔ cond(χ^(p^n)) = 1。 -/
theorem tameOrder_eq_one_iff_conductor (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : tameOrder χ = 1 ↔ (χ ^ (p ^ n)).conductor = 1 := by
  rw [tameOrder_eq_one_iff hodd χ hχ, DirichletCharacter.eq_one_iff_conductor_eq_one]

/-- 1 < tameOrder χ ⇔ cond(χ^(p^n)) = p。 -/
theorem one_lt_tameOrder_iff (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : 1 < tameOrder χ ↔ (χ ^ (p ^ n)).conductor = p := by
  have hpos := tameOrder_pos hodd χ hχ
  have h1 := tameOrder_eq_one_iff_conductor hodd χ hχ
  rcases (Nat.dvd_prime hp.out).mp (conductor_pow_pn_dvd_p hodd χ) with hc | hc
  · constructor
    · intro h; exact absurd (h1.mpr hc) (by omega)
    · intro h; rw [hc] at h; exact absurd h hp.out.one_lt.ne
  · constructor
    · intro _; exact hc
    · intro _
      by_contra hle
      have : tameOrder χ = 1 := by omega
      rw [h1.mp this] at hc; exact hp.out.one_lt.ne hc

end Tame

/-! ## 2. 殻遷移と導手降下の統合 -/

section Synthesis

variable {p n : ℕ} [hp : Fact p.Prime]

/-- **野生残留（r < c − 1）**: 導手 p^(c−r)、殻 v ↦ v + r、許容範囲 [r, K − (c − r)]。 -/
theorem cascade_wild (hodd : Odd p) (hn : 1 ≤ n) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) {r m : ℕ} (hcop : Nat.Coprime m p) (hr : r < n)
    {K v : ℤ} (hv0 : 0 ≤ v) (hvK : v + (n + 1) ≤ K) :
    (χ ^ (p ^ r * m)).conductor = p ^ (n + 1 - r) ∧
      D K ((n + 1 - r : ℕ) : ℤ) (D K ((n + 1 : ℕ) : ℤ) v) = v + r ∧
      (r : ℤ) ≤ D K ((n + 1 - r : ℕ) : ℤ) (D K ((n + 1 : ℕ) : ℤ) v) ∧
      D K ((n + 1 - r : ℕ) : ℤ) (D K ((n + 1 : ℕ) : ℤ) v) ≤ K - ((n + 1 - r : ℕ) : ℤ) := by
  refine ⟨conductor_wild hodd hn χ hχ hcop hr, ?_, ?_, ?_⟩ <;>
  · rw [D_comp]; push_cast [show r ≤ n + 1 by omega]; omega

/-- **馴残留（r ≥ c − 1, d ∤ m）**: 導手 p、殻 v ↦ v + c − 1、許容範囲 [c − 1, K − 1]。 -/
theorem cascade_tame (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) {r m : ℕ} (hcop : Nat.Coprime m p) (hr : n ≤ r) (hd : ¬ tameOrder χ ∣ m)
    {K v : ℤ} (hv0 : 0 ≤ v) (hvK : v + (n + 1) ≤ K) :
    (χ ^ (p ^ r * m)).conductor = p ∧
      D K 1 (D K ((n + 1 : ℕ) : ℤ) v) = v + n ∧
      (n : ℤ) ≤ D K 1 (D K ((n + 1 : ℕ) : ℤ) v) ∧ D K 1 (D K ((n + 1 : ℕ) : ℤ) v) ≤ K - 1 := by
  refine ⟨conductor_tame_one hodd χ hχ hcop hr hd, ?_, ?_, ?_⟩ <;>
  · rw [D_comp]; push_cast; omega

/-- **動径落下（r ≥ c − 1, d ∣ m）**: χ^(p^r m) = 1（導手 1）、中間双対殻 w₀ ∈ [0, K − c]、
そして双対べき等元は正規化畳み込みの反復で射線として不変（PAG10.cvpow_dual）。 -/
theorem cascade_radial (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) {r m : ℕ} (hcop : Nat.Coprime m p) (hr : n ≤ r) (hd : tameOrder χ ∣ m)
    {K v : ℤ} (hv0 : 0 ≤ v) (hvK : v + (n + 1) ≤ K)
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (F : A ≃ₗ[R] A) (α : R) (e : A) (c : R)
    (he : e * e = c • e) :
    χ ^ (p ^ r * m) = 1 ∧ (χ ^ (p ^ r * m)).conductor = 1 ∧
      0 ≤ D K ((n + 1 : ℕ) : ℤ) v ∧ D K ((n + 1 : ℕ) : ℤ) v ≤ K - ((n + 1 : ℕ) : ℤ) ∧
      ∀ k : ℕ, PAG.Part10.cvpow F α (F.symm e) k = (α * c) ^ k • F.symm e := by
  refine ⟨(pow_eq_one_iff hodd χ hχ hcop).mpr ⟨hr, hd⟩, conductor_tame_zero hodd χ hχ hcop hr hd,
    ?_, ?_, PAG.Part10.cvpow_dual F α e c he⟩ <;>
  · unfold D; push_cast; omega

end Synthesis

/-! ## 3. 球平均の吸収律からの直交べき等元（フーリエ変換なし） -/

section Ball

variable {R : Type*} [CommRing R]

/-- ε_w = P_w − P_(w+1)（w < K）、ε_K = P_K。 -/
def epsBall (P : ℕ → R) (K w : ℕ) : R := if w < K then P w - P (w + 1) else P K

/-- **望遠鏡和**: Σ_{w ≤ K} ε_w = P_0。 -/
theorem sum_epsBall (P : ℕ → R) (K : ℕ) : ∑ w ∈ range (K + 1), epsBall P K w = P 0 := by
  rw [sum_range_succ]
  have h : ∑ w ∈ range K, epsBall P K w = ∑ w ∈ range K, (P w - P (w + 1)) :=
    sum_congr rfl (fun w hw => by simp [epsBall, mem_range.mp hw])
  rw [h, sum_range_sub', epsBall, ite_eq_right_of_eq_false _ _ (eq_false ((lt_irrefl K)))]
  ring

/-- **吸収律からの直交べき等性**: a ≤ b ≤ K で P_a P_b = P_b なら ε_a ε_b = δ_ab ε_a（a, b ≤ K）。 -/
theorem epsBall_mul (P : ℕ → R) (K : ℕ) (habs : ∀ a b, a ≤ b → b ≤ K → P a * P b = P b)
    {a b : ℕ} (ha : a ≤ K) (hb : b ≤ K) :
    epsBall P K a * epsBall P K b = if a = b then epsBall P K a else 0 := by
  have hsq : ∀ a, a ≤ K → P a * P a = P a := fun a ha => habs a a le_rfl ha
  have hcomm : ∀ a b, a ≤ b → b ≤ K → P b * P a = P b := fun a b h hb => by
    rw [mul_comm]; exact habs a b h hb
  unfold epsBall
  rcases lt_trichotomy a b with h | h | h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (h.ne))]
    have haK : a < K := lt_of_lt_of_le h hb
    rw [ite_eq_left_of_eq_true _ _ (eq_true (haK))]
    by_cases hbK : b < K
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (hbK))]
      have e1 := habs a b h.le hb; have e2 := habs a (b + 1) (by omega) (by omega)
      have e3 := habs (a + 1) b (by omega) hb; have e4 := habs (a + 1) (b + 1) (by omega) (by omega)
      linear_combination e1 - e2 - e3 + e4
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (hbK))]
      have e1 := habs a K (by omega) le_rfl; have e2 := habs (a + 1) K (by omega) le_rfl
      linear_combination e1 - e2
  · subst h
    rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl))]
    by_cases haK : a < K
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (haK))]
      have e1 := hsq a ha; have e2 := habs a (a + 1) (by omega) (by omega)
      have e3 := hsq (a + 1) (by omega)
      linear_combination e1 - 2 * e2 + e3
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (haK))]; exact hsq K le_rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (h.ne'))]
    have hbK : b < K := lt_of_lt_of_le h ha
    rw [ite_eq_left_of_eq_true _ _ (eq_true (hbK))]
    by_cases haK : a < K
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (haK))]
      have e1 := hcomm b a h.le ha; have e2 := hcomm (b + 1) a (by omega) ha
      have e3 := hcomm b (a + 1) (by omega) (by omega); have e4 := hcomm (b + 1) (a + 1) (by omega) (by omega)
      linear_combination e1 - e2 - e3 + e4
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (haK))]
      have e1 := hcomm b K (by omega) le_rfl; have e2 := hcomm (b + 1) K (by omega) le_rfl
      linear_combination e1 - e2

/-- 系: P_0 が単位元なら Σ ε_w は単位元（δ₀）。 -/
theorem sum_epsBall_eq_one (P : ℕ → R) (K : ℕ) (h0 : P 0 = 1) :
    ∑ w ∈ range (K + 1), epsBall P K w = 1 := by
  rw [sum_epsBall, h0]

end Ball

/-! ## 4. 定常位相の 1 項抽出 -/

section Phase

variable {M : ℕ} [NeZero M]

/-- **定常位相の核**: Σ_t ψ(−A t) ψ(y t) = M（y = A）/ 0（y ≠ A）、ψ = ZMod.stdAddChar。 -/
theorem stationary_phase (A y : ZMod M) :
    ∑ t : ZMod M, ZMod.stdAddChar (-A * t) * ZMod.stdAddChar (y * t)
      = if y = A then (M : ℂ) else 0 := by
  have h : ∀ t : ZMod M, ZMod.stdAddChar (-A * t) * ZMod.stdAddChar (y * t)
      = ZMod.stdAddChar (t * (y - A)) := fun t => by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  simp_rw [h]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar M), ZMod.card]
  simp [sub_eq_zero]

/-- **持ち上げ不変性**: A が単数なら ψ(−A·(r A⁻¹)) ψ(r) = 1。 -/
theorem lift_invariance (A : (ZMod M)ˣ) (r : ZMod M) :
    ZMod.stdAddChar (-(A : ZMod M) * (r * ((A⁻¹ : (ZMod M)ˣ) : ZMod M))) * ZMod.stdAddChar r = 1 := by
  rw [← AddChar.map_add_eq_mul]
  have : -(A : ZMod M) * (r * ((A⁻¹ : (ZMod M)ˣ) : ZMod M)) + r = 0 := by
    have hA : (A : ZMod M) * ((A⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    linear_combination (-r) * hA
  rw [this, AddChar.map_zero_eq_one]

end Phase

end PAG.Part14

#print axioms PAG.Part14.orderOf_pow_pn_eq_tameOrder
#print axioms PAG.Part14.tameOrder_pos
#print axioms PAG.Part14.conductor_pow_pn_dvd_p
#print axioms PAG.Part14.tameOrder_eq_one_iff
#print axioms PAG.Part14.tameOrder_eq_one_iff_conductor
#print axioms PAG.Part14.one_lt_tameOrder_iff
#print axioms PAG.Part14.cascade_wild
#print axioms PAG.Part14.cascade_tame
#print axioms PAG.Part14.cascade_radial
#print axioms PAG.Part14.sum_epsBall
#print axioms PAG.Part14.epsBall_mul
#print axioms PAG.Part14.sum_epsBall_eq_one
#print axioms PAG.Part14.stationary_phase
#print axioms PAG.Part14.lift_invariance
