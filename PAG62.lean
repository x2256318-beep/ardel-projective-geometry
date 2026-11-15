/-
  PAG 2.0 Part 58（2026-10-19）— 奇素数での導手の ν_p 公式
  p 奇素数、n = c+1、ω は PAG61 の忠実な指標。
  1. 簡約 (Z/p^n)ˣ → (Z/p^m)ˣ の核 K_m の位数は φ(p^n)/φ(p^m)（m ≥ 1 なら p^(n−m)）
  2. ω^j が法 p^m を経由 ⇔ |K_m| ∣ j（ω の忠実性と、巡回群 K_m の指数 = 位数）
  3. 導手: m ≥ 2 で cond(ω^j) = p^m ⇔ p^(n−m) ∣ j ∧ ¬ p^(n−m+1) ∣ j
           cond(ω^j) = p ⇔ p^(n−1) ∣ j ∧ ¬ φ ∣ j
-/
import PAG61

namespace PAG.Part62

open ZMod Finset PAG.Part61

variable {p : ℕ} [hp : Fact p.Prime] (c : ℕ) (hp2 : p ≠ 2)

/-- 簡約の核の位数 × φ(p^m) = φ(p^n)。 -/
theorem card_ker_mul (m : ℕ) (hm : m ≤ c + 1) :
    Nat.card (ZMod.unitsMap (pow_dvd_pow p hm)).ker * (p ^ m).totient = (p ^ (c + 1)).totient := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have h1 := Subgroup.card_mul_index (ZMod.unitsMap (pow_dvd_pow p hm)).ker
  rw [Subgroup.index_ker, (MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective (pow_dvd_pow p hm))),
    Subgroup.card_top, Nat.card_eq_fintype_card (α := (ZMod (p ^ m))ˣ),
    Nat.card_eq_fintype_card (α := (ZMod (p ^ (c + 1)))ˣ), ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient] at h1
  exact h1

/-- m ≥ 1 なら |K_m| = p^(n−m)。 -/
theorem card_ker (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ c + 1) :
    Nat.card (ZMod.unitsMap (pow_dvd_pow p hm)).ker = p ^ (c + 1 - m) := by
  have h := card_ker_mul (p := p) c m hm
  rw [Nat.totient_prime_pow hp.out (by omega), Nat.totient_prime_pow hp.out (by omega)] at h
  have hpos : 0 < p ^ (m - 1) * (p - 1) := Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
  have e : p ^ (c + 1 - 1) * (p - 1) = p ^ (c + 1 - m) * (p ^ (m - 1) * (p - 1)) := by
    rw [← mul_assoc, ← pow_add]; congr 2; omega
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_right hpos h

/-- m = 0 なら |K_0| = φ。 -/
theorem card_ker_zero : Nat.card (ZMod.unitsMap (pow_dvd_pow p (Nat.zero_le (c + 1)))).ker = phi (p := p) c := by
  have h := card_ker_mul (p := p) c 0 (Nat.zero_le _)
  rw [show (p ^ 0).totient = 1 by simp, mul_one] at h
  rw [h, phi, ZMod.card_units_eq_totient]

include hp2

/-- **経由の判定**: ω^j が法 p^m を経由 ⇔ |K_m| ∣ j。 -/
theorem omega_pow_factors_iff (m : ℕ) (hm : m ≤ c + 1) (j : ℕ) :
    (omega c hp2 ^ j).FactorsThrough (p ^ m) ↔ Nat.card (ZMod.unitsMap (pow_dvd_pow p hm)).ker ∣ j := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have := isCyclic_units c hp2
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (pow_dvd_pow p hm),
    ← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  constructor
  · intro h u
    have hu := h u.2
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.pow_apply_coe,
      ← map_pow, ← Units.val_pow_eq_pow_val] at hu
    exact Subtype.ext (omega_faithful c hp2 _ hu)
  · intro h u hu
    have e := h ⟨u, hu⟩
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.pow_apply_coe,
      ← map_pow, ← Units.val_pow_eq_pow_val]
    have : u ^ j = 1 := congrArg Subtype.val e
    rw [this, Units.val_one, map_one]

/-- 経由の判定（m ≥ 1）: ω^j が法 p^m を経由 ⇔ p^(n−m) ∣ j。 -/
theorem omega_pow_factors_iff' (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ c + 1) (j : ℕ) :
    (omega c hp2 ^ j).FactorsThrough (p ^ m) ↔ p ^ (c + 1 - m) ∣ j := by
  rw [omega_pow_factors_iff c hp2 m hm, card_ker c m hm1 hm]

/-- 経由の判定（m = 0）: ω^j が自明 ⇔ φ ∣ j。 -/
theorem omega_pow_factors_zero (j : ℕ) :
    (omega c hp2 ^ j).FactorsThrough (p ^ 0) ↔ phi (p := p) c ∣ j := by
  rw [omega_pow_factors_iff c hp2 0 (Nat.zero_le _), card_ker_zero]

/-- **導手の ν_p 公式（m ≥ 2）**: cond(ω^j) = p^m ⇔ p^(n−m) ∣ j ∧ ¬ p^(n−m+1) ∣ j。 -/
theorem omega_pow_conductor_iff (m : ℕ) (hm2 : 2 ≤ m) (hm : m ≤ c + 1) (j : ℕ) :
    (omega c hp2 ^ j).conductor = p ^ m ↔ p ^ (c + 1 - m) ∣ j ∧ ¬ p ^ (c + 1 - m + 1) ∣ j := by
  rw [PAG.Part33.conductor_eq_iff (by omega) hm, omega_pow_factors_iff' c hp2 m (by omega) hm,
    omega_pow_factors_iff' c hp2 (m - 1) (by omega) (by omega), show c + 1 - (m - 1) = c + 1 - m + 1 by omega]

/-- **導手 p**: cond(ω^j) = p ⇔ p^(n−1) ∣ j ∧ ¬ φ ∣ j。 -/
theorem omega_pow_conductor_p_iff (j : ℕ) :
    (omega c hp2 ^ j).conductor = p ^ 1 ↔ p ^ c ∣ j ∧ ¬ phi (p := p) c ∣ j := by
  rw [PAG.Part33.conductor_eq_iff le_rfl (by omega), omega_pow_factors_iff' c hp2 1 le_rfl (by omega),
    Nat.sub_self, omega_pow_factors_zero c hp2, show c + 1 - 1 = c by omega]

/-- 積の導手（m ≥ 2）: cond(ω^j ω^j') = p^m ⇔ p^(n−m) ∣ j+j' ∧ ¬ p^(n−m+1) ∣ j+j'。 -/
theorem omega_mul_conductor_iff (m : ℕ) (hm2 : 2 ≤ m) (hm : m ≤ c + 1) (j j' : ℕ) :
    (omega c hp2 ^ j * omega c hp2 ^ j').conductor = p ^ m ↔
      p ^ (c + 1 - m) ∣ (j + j') ∧ ¬ p ^ (c + 1 - m + 1) ∣ (j + j') := by
  rw [← pow_add, omega_pow_conductor_iff c hp2 m hm2 hm]

end PAG.Part62

#print axioms PAG.Part62.card_ker_mul
#print axioms PAG.Part62.card_ker
#print axioms PAG.Part62.card_ker_zero
#print axioms PAG.Part62.omega_pow_factors_iff
#print axioms PAG.Part62.omega_pow_factors_iff'
#print axioms PAG.Part62.omega_pow_factors_zero
#print axioms PAG.Part62.omega_pow_conductor_iff
#print axioms PAG.Part62.omega_pow_conductor_p_iff
#print axioms PAG.Part62.omega_mul_conductor_iff
