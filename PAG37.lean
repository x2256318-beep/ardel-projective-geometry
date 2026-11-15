/-
  PAG 2.0 Part 33（2026-10-19）— p = 2 の単数群の構造と、導手の閉じた式
  1. 5^(2^k) = 1 + 2^(k+2)·u（u 奇数）、5 の位数は法 2^m（m ≥ 2）で 2^(m−2)
  2. (Z/2^c)^× = {±1} × ⟨5⟩（c ≥ 3）: 全単射 Fin 2 × Fin 2^(c−2) → (Z/2^c)^×
  3. 法 2^c → 2^m（2 ≤ m ≤ c）の単数の核 = ⟨5^(2^(m−2))⟩
  4. 経由の判定: ψ が法 2^m を経由 ⇔ ψ(5)^(2^(m−2)) = 1、ψ = 1 ⇔ ψ(−1) = ψ(5) = 1
  5. 原始性: ψ 原始的 ⇔ ψ(5)^(2^(c−3)) ≠ 1、導手 = 2^m ⇔ ψ(5) の位数がちょうど 2^(m−2)（3 ≤ m ≤ c）
  （以下、法を 2^(d+3)（d ≥ 0）と書く）
-/
import PAG36

namespace PAG.Part37

open ZMod Finset

/-! ## 1. 5 の冪 -/

/-- 5^(2^k) = 1 + 2^(k+2)·u（u 奇数）。 -/
theorem five_pow_two_pow (k : ℕ) : ∃ u : ℕ, Odd u ∧ 5 ^ (2 ^ k) = 1 + 2 ^ (k + 2) * u := by
  induction k with
  | zero => exact ⟨1, odd_one, by norm_num⟩
  | succ k ih =>
    obtain ⟨u, hu, he⟩ := ih
    refine ⟨u + 2 ^ (k + 1) * u ^ 2, ?_, ?_⟩
    · exact hu.add_even ⟨2 ^ k * u ^ 2, by ring⟩
    · rw [pow_succ, pow_mul, he]; ring

/-- 5 を法 2^m の単数として。 -/
def five (m : ℕ) : (ZMod (2 ^ m))ˣ := ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right m (by norm_num))

theorem five_val (m : ℕ) : ((five m : (ZMod (2 ^ m))ˣ) : ZMod (2 ^ m)) = 5 := by
  rw [five, ZMod.coe_unitOfCoprime]; norm_num

theorem unitsMap_five {m c : ℕ} (h : m ≤ c) :
    ZMod.unitsMap (pow_dvd_pow 2 h) (five c) = five m := by
  have : NeZero (2 ^ c) := ⟨pow_ne_zero _ two_ne_zero⟩
  ext
  rw [ZMod.unitsMap_val, five_val, five_val, show (5 : ZMod (2 ^ c)) = ((5 : ℕ) : ZMod (2 ^ c)) by norm_num,
    ZMod.cast_natCast (pow_dvd_pow 2 h)]
  norm_num

/-- five^(2^k) の値（ZMod で）。 -/
theorem five_pow_val (m k : ℕ) :
    ∃ u : ℕ, Odd u ∧ (((five m) ^ (2 ^ k) : (ZMod (2 ^ m))ˣ) : ZMod (2 ^ m)) = ((1 + 2 ^ (k + 2) * u : ℕ) : ZMod _) := by
  obtain ⟨u, hu, he⟩ := five_pow_two_pow k
  refine ⟨u, hu, ?_⟩
  rw [Units.val_pow_eq_pow_val, five_val, ← he]; push_cast; ring

/-- 法 2^m（m ≥ 3）で 5 の位数は 2^(m−2)。 -/
theorem orderOf_five_ge3 {m : ℕ} (hm : 3 ≤ m) : orderOf (five m) = 2 ^ (m - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  rw [show n + 3 - 2 = n + 1 by omega]
  apply orderOf_eq_prime_pow
  · intro h
    obtain ⟨u, hu, he⟩ := five_pow_val (n + 3) n
    rw [h, Units.val_one] at he
    have h0 : ((2 ^ (n + 2) * u : ℕ) : ZMod (2 ^ (n + 3))) = 0 := by
      have := congrArg (fun z => z - 1) he
      simp only [sub_self, Nat.cast_add, Nat.cast_one, add_sub_cancel_left] at this
      exact this.symm
    rw [ZMod.natCast_eq_zero_iff, pow_succ, Nat.mul_dvd_mul_iff_left (by positivity)] at h0
    exact (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h0)
  · ext
    obtain ⟨u, _, he⟩ := five_pow_val (n + 3) (n + 1)
    rw [he, Units.val_one, Nat.cast_add, Nat.cast_one, add_eq_left,
      show n + 1 + 2 = n + 3 by omega, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_right _ _

theorem five_two : five 2 = 1 := by
  ext; rw [five_val, Units.val_one]; decide

/-- 法 2^m（m ≥ 2）で 5 の位数は 2^(m−2)。 -/
theorem orderOf_five {m : ℕ} (hm : 2 ≤ m) : orderOf (five m) = 2 ^ (m - 2) := by
  rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | h3
  · rw [five_two, orderOf_one]; rfl
  · exact orderOf_five_ge3 h3

theorem unitsMap_neg_one {m n : ℕ} (h : m ∣ n) : ZMod.unitsMap h (-1) = -1 := by
  rw [ZMod.unitsMap_def]; exact Units.map_neg_one _

/-! ## 2. 単数群 = {±1} × ⟨5⟩ -/

section Units

variable {d : ℕ}

/-- (Z/2^c)^× → (Z/4)^×。 -/
noncomputable def toFour (d : ℕ) : (ZMod (2 ^ (d + 3)))ˣ →* (ZMod (2 ^ 2))ˣ :=
  ZMod.unitsMap (pow_dvd_pow 2 (show 2 ≤ d + 3 by omega))

theorem toFour_five : toFour d (five (d + 3)) = 1 := by
  rw [toFour, unitsMap_five (show 2 ≤ d + 3 by omega), five_two]

theorem neg_one_ne_one_four : (-1 : (ZMod (2 ^ 2))ˣ) ≠ 1 := by
  intro h; have := congrArg Units.val h; revert this; decide

theorem toFour_neg_one : toFour d (-1) = -1 := unitsMap_neg_one _

/-- 写像 (a, b) ↦ (−1)^a · 5^b。 -/
def pm5 (d : ℕ) (x : Fin 2 × Fin (2 ^ (d + 1))) : (ZMod (2 ^ (d + 3)))ˣ :=
  (-1) ^ (x.1 : ℕ) * (five (d + 3)) ^ (x.2 : ℕ)

theorem pm5_injective : Function.Injective (pm5 d) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have ha : a = a' := by
    have := congrArg (toFour d) h
    simp only [pm5, map_mul, map_pow, toFour_five, one_pow, mul_one, toFour_neg_one] at this
    fin_cases a <;> fin_cases a'
    · rfl
    · exfalso; simp at this; exact neg_one_ne_one_four this.symm
    · exfalso; simp at this; exact neg_one_ne_one_four this
    · rfl
  subst ha
  have hb : (five (d + 3)) ^ (b : ℕ) = (five (d + 3)) ^ (b' : ℕ) := mul_left_cancel h
  rw [pow_inj_mod, orderOf_five (by omega), show d + 3 - 2 = d + 1 by omega,
    Nat.mod_eq_of_lt b.2, Nat.mod_eq_of_lt b'.2] at hb
  exact Prod.ext rfl (Fin.ext hb)

/-- **(Z/2^(d+3))^× = {±1} × ⟨5⟩**（全単射）。 -/
theorem pm5_bijective : Function.Bijective (pm5 d) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨pm5_injective, ?_⟩
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega)]
  rw [show d + 3 - 1 = d + 1 + 1 by omega, pow_succ]; ring

theorem units_pm5 (u : (ZMod (2 ^ (d + 3)))ˣ) : ∃ a b : ℕ, u = (-1) ^ a * (five (d + 3)) ^ b := by
  obtain ⟨⟨a, b⟩, h⟩ := pm5_bijective.2 u
  exact ⟨a, b, h.symm⟩

/-- **核 = ⟨5^(2^(m−2))⟩**（2 ≤ m ≤ d+3）。 -/
theorem ker_five {m : ℕ} (hm2 : 2 ≤ m) (hm : m ≤ d + 3) (u : (ZMod (2 ^ (d + 3)))ˣ)
    (hu : u ∈ (ZMod.unitsMap (pow_dvd_pow 2 hm)).ker) :
    ∃ t : ℕ, u = (five (d + 3)) ^ (2 ^ (m - 2) * t) := by
  obtain ⟨a, b, rfl⟩ := units_pm5 u
  rw [MonoidHom.mem_ker, map_mul, map_pow, map_pow, unitsMap_five hm, unitsMap_neg_one] at hu
  -- 法 4 へ落として a を偶数に
  have h4 := congrArg (ZMod.unitsMap (pow_dvd_pow 2 hm2)) hu
  rw [map_mul, map_pow, map_pow, unitsMap_five hm2, five_two, one_pow, mul_one, map_one, unitsMap_neg_one] at h4
  have hb : (five m) ^ b = 1 := by
    rcases Nat.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [← two_mul, pow_mul, neg_one_sq, one_pow, one_mul] at hu; exact hu
    · exfalso
      rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one] at h4
      exact neg_one_ne_one_four h4
  have hdvd := orderOf_dvd_of_pow_eq_one hb
  rw [orderOf_five hm2] at hdvd
  obtain ⟨t, rfl⟩ := hdvd
  refine ⟨t, ?_⟩
  rcases Nat.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  · exfalso
    rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one] at h4
    exact neg_one_ne_one_four h4

end Units

/-! ## 3. 導手の閉じた式 -/

section Cond

variable {d : ℕ}

instance (k : ℕ) : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩

/-- **経由の判定**: ψ が法 2^m を経由 ⇔ ψ(5)^(2^(m−2)) = 1（2 ≤ m ≤ d+3）。 -/
theorem factors_iff_five {m : ℕ} (hm2 : 2 ≤ m) (hm : m ≤ d + 3) (ψ : DirichletCharacter ℂ (2 ^ (d + 3))) :
    ψ.FactorsThrough (2 ^ m) ↔ ψ 5 ^ (2 ^ (m - 2)) = 1 := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (pow_dvd_pow 2 hm)]
  have h5 : (5 : ZMod (2 ^ (d + 3))) = ((five (d + 3) : (ZMod (2 ^ (d + 3)))ˣ) : ZMod _) := (five_val _).symm
  constructor
  · intro h
    have hmem : (five (d + 3)) ^ (2 ^ (m - 2)) ∈ (ZMod.unitsMap (pow_dvd_pow 2 hm)).ker := by
      rw [MonoidHom.mem_ker, map_pow, unitsMap_five hm, ← orderOf_five hm2, pow_orderOf_eq_one]
    have := congrArg Units.val (h hmem)
    rw [MulChar.coe_toUnitHom, Units.val_one, Units.val_pow_eq_pow_val, map_pow] at this
    rw [h5]; exact this
  · intro h u hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    obtain ⟨t, rfl⟩ := ker_five hm2 hm u hu
    rw [Units.val_pow_eq_pow_val, map_pow, pow_mul, ← h5, h, one_pow]

/-- ψ = 1 ⇔ ψ(−1) = 1 かつ ψ(5) = 1。 -/
theorem eq_one_iff_five (ψ : DirichletCharacter ℂ (2 ^ (d + 3))) : ψ = 1 ↔ ψ (-1) = 1 ∧ ψ 5 = 1 := by
  constructor
  · rintro rfl
    exact ⟨MulChar.one_apply (isUnit_one.neg), MulChar.one_apply (by rw [← five_val]; exact Units.isUnit _)⟩
  · rintro ⟨h1, h5⟩
    apply MulChar.ext
    intro u
    obtain ⟨a, b, rfl⟩ := units_pm5 u
    rw [MulChar.one_apply_coe, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul,
      map_pow, map_pow, Units.val_neg, Units.val_one, h1, five_val, h5, one_pow, one_pow, one_mul]

/-- **原始性**: ψ 原始的 ⇔ ψ(5)^(2^d) ≠ 1（法 2^(d+3)）。 -/
theorem prim_iff_five (ψ : DirichletCharacter ℂ (2 ^ (d + 3))) : ψ.IsPrimitive ↔ ψ 5 ^ (2 ^ d) ≠ 1 := by
  have h := PAG.Part32.not_prim_iff_factors (p := 2) (c := d + 2) (by omega) ψ
  rw [factors_iff_five (by omega) (by omega), show d + 2 - 2 = d by omega] at h
  rw [ne_eq, ← h, not_not]

/-- **導手の閉じた式**: 導手 = 2^m ⇔ ψ(5)^(2^(m−2)) = 1 かつ ψ(5)^(2^(m−3)) ≠ 1（3 ≤ m ≤ d+3）、
すなわち ψ(5) の位数がちょうど 2^(m−2)。 -/
theorem conductor_eq_iff_five {m : ℕ} (hm3 : 3 ≤ m) (hm : m ≤ d + 3) (ψ : DirichletCharacter ℂ (2 ^ (d + 3))) :
    ψ.conductor = 2 ^ m ↔ ψ 5 ^ (2 ^ (m - 2)) = 1 ∧ ψ 5 ^ (2 ^ (m - 3)) ≠ 1 := by
  rw [PAG.Part33.conductor_eq_iff (p := 2) (c := d + 2) (by omega) hm, factors_iff_five (by omega) hm,
    factors_iff_five (by omega) (by omega), show m - 1 - 2 = m - 3 by omega]

/-- 導手 = 4 ⇔ ψ(5) = 1 かつ ψ(−1) ≠ 1。 -/
theorem conductor_eq_four_iff (ψ : DirichletCharacter ℂ (2 ^ (d + 3))) :
    ψ.conductor = 2 ^ 2 ↔ ψ 5 = 1 ∧ ψ (-1) ≠ 1 := by
  rw [PAG.Part33.conductor_eq_iff (p := 2) (c := d + 2) (m := 2) (by omega) (by omega), factors_iff_five le_rfl (by omega),
    show 2 - 2 = 0 by rfl, pow_zero, pow_one]
  have h2 : ψ.FactorsThrough (2 ^ (2 - 1)) ↔ ψ = 1 := by
    rw [show 2 - 1 = 1 by rfl, pow_one]
    constructor
    · intro hf
      have hdvd := DirichletCharacter.conductor_dvd_of_mem_conductorSet ψ ((DirichletCharacter.mem_conductorSet_iff _).mpr hf)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1
      · exact absurd h1 (PAG.Part31.conductor_ne_two ψ)
    · rintro rfl
      exact DirichletCharacter.FactorsThrough.mono (1 : DirichletCharacter ℂ (2 ^ (d + 3)))
        ((DirichletCharacter.factorsThrough_one_iff _).mpr rfl) (one_dvd 2) (dvd_pow_self 2 (by omega : d + 3 ≠ 0))
  rw [h2, eq_one_iff_five]
  tauto

/-- 積の導手（3 ≤ m）: (χ₁χ₂)(5) = χ₁(5)χ₂(5) の位数で決まる。 -/
theorem mul_conductor_eq_iff_five {m : ℕ} (hm3 : 3 ≤ m) (hm : m ≤ d + 3) (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (d + 3))) :
    (χ₁ * χ₂).conductor = 2 ^ m ↔
      (χ₁ 5 * χ₂ 5) ^ (2 ^ (m - 2)) = 1 ∧ (χ₁ 5 * χ₂ 5) ^ (2 ^ (m - 3)) ≠ 1 := by
  rw [conductor_eq_iff_five hm3 hm, MulChar.coeToFun_mul, Pi.mul_apply]

end Cond

end PAG.Part37

#print axioms PAG.Part37.five_pow_two_pow
#print axioms PAG.Part37.five
#print axioms PAG.Part37.five_val
#print axioms PAG.Part37.unitsMap_five
#print axioms PAG.Part37.five_pow_val
#print axioms PAG.Part37.orderOf_five_ge3
#print axioms PAG.Part37.five_two
#print axioms PAG.Part37.orderOf_five
#print axioms PAG.Part37.unitsMap_neg_one
#print axioms PAG.Part37.toFour
#print axioms PAG.Part37.toFour_five
#print axioms PAG.Part37.neg_one_ne_one_four
#print axioms PAG.Part37.toFour_neg_one
#print axioms PAG.Part37.pm5
#print axioms PAG.Part37.pm5_injective
#print axioms PAG.Part37.pm5_bijective
#print axioms PAG.Part37.units_pm5
#print axioms PAG.Part37.ker_five
#print axioms PAG.Part37.factors_iff_five
#print axioms PAG.Part37.eq_one_iff_five
#print axioms PAG.Part37.prim_iff_five
#print axioms PAG.Part37.conductor_eq_iff_five
#print axioms PAG.Part37.conductor_eq_four_iff
#print axioms PAG.Part37.mul_conductor_eq_iff_five
