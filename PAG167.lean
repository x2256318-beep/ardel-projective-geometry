/-
  PAG 2.0 Part 163（2026-10-22）— ガウスの符号決定（その 3）：組み立て
  1. g = aeval ζ P、Π = aeval ζ Q
  2. g² = Π²、したがって g = ±Π
  3. gauss_eq: g = (−1)^m χ(2) i^m √p（Part 162 の係数比較で符号を決める）
  4. epsG_one / epsG_three: ε = τ(L)/√p = 1（p ≡ 1）、i（p ≡ 3）
  5. zeta_order_one_odd_iff': p ≡ 1・ord χ 奇数で ord ζ = p ⇔ L(−δ/2) = 1
-/
import PAG166
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

namespace PAG.Part167

open Complex Finset Polynomial Real PAG.Part165 PAG.Part166
open ZMod (stdAddChar)

variable (p : ℕ) [hp : Fact p.Prime]

theorem std_eq_pow (a : ℕ) : (stdAddChar (a : ZMod p) : ℂ) = zp p ^ a := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold zp
  rw [← Complex.exp_nat_mul]
  congr 1; ring

/-- **1. g = aeval ζ P**。 -/
theorem gauss_eq_aeval : gaussSum (PAG.Part119.Lc p) stdAddChar = aeval (zp p) (Pz p) := by
  unfold gaussSum Pz
  rw [← sum_range_zmod p, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, aeval_C, map_pow, aeval_X, std_eq_pow, PAG.Part119.Lc_apply]
  simp

theorem zp_pow_sub (a : ℕ) (ha : a ≤ p) : zp p ^ (p - a) = (zp p ^ a)⁻¹ := by
  have h1 : zp p ^ (p - a) * zp p ^ a = 1 := by rw [← pow_add, Nat.sub_add_cancel ha, (zp_prim p).pow_eq_one]
  exact eq_inv_of_mul_eq_one_left h1

/-- **1'. Π = aeval ζ Q**。 -/
theorem Pi_eq_aeval (m : ℕ) (hpm : p = 2 * m + 1) : Pi p m = aeval (zp p) (Qz p m) := by
  unfold Pi Qz
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro a ha
  simp only [Finset.mem_Ico] at ha
  rw [map_sub, map_pow, map_pow, aeval_X, zp_pow_sub p a (by omega)]
  rfl

theorem Lc_neg_one_pow (m : ℕ) (hpm : p = 2 * m + 1) : (PAG.Part119.Lc p (-1) : ℂ) = (-1) ^ m := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [PAG.Part129.Lc_neg_one_of_one (by omega), hk, ← two_mul, pow_mul]; norm_num
  · rw [PAG.Part129.Lc_neg_one_of_three (by omega), hk, pow_succ, pow_mul]; norm_num

/-- **2. g² = Π²**。 -/
theorem gauss_sq_eq (m : ℕ) (hpm : p = 2 * m + 1) :
    gaussSum (PAG.Part119.Lc p) stdAddChar ^ 2 = Pi p m ^ 2 := by
  have hp2 : p ≠ 2 := by omega
  have hsq := gaussSum_sq (χ := PAG.Part119.Lc p) (PAG.Part119.Lc_ne_one hp2) PAG.Part119.Lc_isQuadratic
    (ZMod.isPrimitive_stdAddChar p)
  rw [ZMod.card] at hsq
  rw [hsq, Pi_sq p m hpm, Lc_neg_one_pow p m hpm]

theorem int_eq_of_cast (hp2 : p ≠ 2) (a b : ℤ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (h : (a : ZMod p) = b) : a = b := by
  have h2 := PAG.Part119.two_ne_zero' hp2
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exfalso; apply h2; push_cast at h; linear_combination h
  · exfalso; apply h2; push_cast at h; linear_combination -h
  · rfl

/-- **3. g = (−1)^m χ(2) i^m √p**。 -/
theorem gauss_eq (m : ℕ) (hpm : p = 2 * m + 1) :
    gaussSum (PAG.Part119.Lc p) stdAddChar
      = ((((-1) ^ m * quadraticChar (ZMod p) 2 : ℤ)) : ℂ) * (I ^ m * (Real.sqrt p : ℂ)) := by
  have hp2 : p ≠ 2 := by omega
  have hsq := gauss_sq_eq p m hpm
  have hpm' : gaussSum (PAG.Part119.Lc p) stdAddChar = Pi p m ∨ gaussSum (PAG.Part119.Lc p) stdAddChar = -Pi p m := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  obtain ⟨ε, hε, hgε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ gaussSum (PAG.Part119.Lc p) stdAddChar = (ε : ℂ) * Pi p m := by
    rcases hpm' with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩
  have h0 : aeval (zp p) (Pz p - C ε * Qz p m) = 0 := by
    rw [map_sub, map_mul, aeval_C, ← gauss_eq_aeval, ← Pi_eq_aeval p m hpm, hgε]
    simp
  have hdvd : cyclotomic p ℤ ∣ Pz p - C ε * Qz p m := by
    rw [cyclotomic_eq_minpoly (zp_prim p) hp.out.pos]
    exact minpoly.isIntegrallyClosed_dvd ((zp_prim p).isIntegral hp.out.pos) h0
  have hsign := sign_from_poly p m hpm ε hdvd
  have h2 : quadraticChar (ZMod p) 2 = 1 ∨ quadraticChar (ZMod p) 2 = -1 :=
    quadraticChar_dichotomy (PAG.Part119.two_ne_zero' hp2)
  have hr : (-1) ^ m * quadraticChar (ZMod p) 2 = 1 ∨ (-1) ^ m * quadraticChar (ZMod p) 2 = -1 := by
    rcases neg_one_pow_eq_or ℤ m with h | h <;> rcases h2 with h' | h' <;> rw [h, h'] <;> simp
  have heq := int_eq_of_cast p hp2 ε _ hε hr (by rw [hsign]; push_cast; rfl)
  rw [hgε, heq, Pi_eq p m hpm]

theorem I_pow_four_mul (j : ℕ) : I ^ (4 * j) = 1 := by rw [pow_mul, show I ^ 4 = 1 by norm_num, one_pow]

/-- **4a. p ≡ 1 (mod 4) なら ε = 1**。 -/
theorem epsG_one (h4 : p % 4 = 1) : PAG.Part160.epsG p = 1 := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  set m := (p - 1) / 2
  have hpm : p = 2 * m + 1 := by omega
  have hs : (Real.sqrt p : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)
    exact_mod_cast this.ne'
  unfold PAG.Part160.epsG
  rw [gauss_eq p m hpm, mul_div_assoc, mul_div_assoc, div_self hs, mul_one]
  rw [quadraticChar_two (PAG.Part119.ringChar_ne_two hp2), ZMod.card, ZMod.χ₈_nat_eq_if_mod_eight]
  have hev : ∀ j : ℕ, (-1 : ℂ) ^ (4 * j) = 1 := fun j => (show Even (4 * j) from ⟨2 * j, by ring⟩).neg_one_pow
  rcases (show p % 8 = 1 ∨ p % 8 = 5 by omega) with h8 | h8
  · obtain ⟨j, hj⟩ : ∃ j, m = 4 * j := ⟨m / 4, by omega⟩
    simp only [show ¬ (p % 2 = 0) by omega, show (p % 8 = 1 ∨ p % 8 = 7) by omega, ↓reduceIte]
    rw [hj, I_pow_four_mul]; push_cast; rw [hev]; norm_num
  · obtain ⟨j, hj⟩ : ∃ j, m = 4 * j + 2 := ⟨m / 4, by omega⟩
    simp only [show ¬ (p % 2 = 0) by omega, show ¬ (p % 8 = 1 ∨ p % 8 = 7) by omega, ↓reduceIte]
    rw [hj, pow_add I, I_pow_four_mul]; push_cast; rw [pow_add, hev]; norm_num

/-- **4b. p ≡ 3 (mod 4) なら ε = i**。 -/
theorem epsG_three (h4 : p % 4 = 3) : PAG.Part160.epsG p = I := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  set m := (p - 1) / 2
  have hpm : p = 2 * m + 1 := by omega
  have hs : (Real.sqrt p : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)
    exact_mod_cast this.ne'
  unfold PAG.Part160.epsG
  rw [gauss_eq p m hpm, mul_div_assoc, mul_div_assoc, div_self hs, mul_one]
  rw [quadraticChar_two (PAG.Part119.ringChar_ne_two hp2), ZMod.card, ZMod.χ₈_nat_eq_if_mod_eight]
  have hev : ∀ j : ℕ, (-1 : ℂ) ^ (4 * j) = 1 := fun j => (show Even (4 * j) from ⟨2 * j, by ring⟩).neg_one_pow
  rcases (show p % 8 = 3 ∨ p % 8 = 7 by omega) with h8 | h8
  · obtain ⟨j, hj⟩ : ∃ j, m = 4 * j + 1 := ⟨m / 4, by omega⟩
    simp only [show ¬ (p % 2 = 0) by omega, show ¬ (p % 8 = 1 ∨ p % 8 = 7) by omega, ↓reduceIte]
    rw [hj, pow_add I, I_pow_four_mul]; push_cast; rw [pow_add, hev]; norm_num
  · obtain ⟨j, hj⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    simp only [show ¬ (p % 2 = 0) by omega, show (p % 8 = 1 ∨ p % 8 = 7) by omega, ↓reduceIte]
    rw [hj, pow_add I, I_pow_four_mul]; push_cast; rw [pow_add, hev]
    rw [show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]; norm_num

/-- **5. p ≡ 1・ord χ 奇数：ord ζ = p ⇔ L(−δ/2) = 1**（Part 156 の ε に値を入れた形）。 -/
theorem zeta_order_one_odd_iff' (h4 : p % 4 = 1) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (δ : ZMod (p ^ (n + 1)))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ (n + 1))) ^ (m + 1) * y) = stdAddChar ((p : ZMod (p ^ (n + 1))) ^ (m + 1) * δ * y))
    (hodd : ¬ 2 ∣ orderOf χ) :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = p ↔
      PAG.Part119.Lc p (((-δ : ZMod (p ^ (n + 1))).cast : ZMod p) * 2⁻¹) = 1 := by
  rw [PAG.Part160.zeta_order_one_odd_iff h4 n m hnm hm χ hχ δ hδ hodd, epsG_one p h4]

end PAG.Part167

#print axioms PAG.Part167.std_eq_pow
#print axioms PAG.Part167.gauss_eq_aeval
#print axioms PAG.Part167.zp_pow_sub
#print axioms PAG.Part167.Pi_eq_aeval
#print axioms PAG.Part167.Lc_neg_one_pow
#print axioms PAG.Part167.gauss_sq_eq
#print axioms PAG.Part167.int_eq_of_cast
#print axioms PAG.Part167.gauss_eq
#print axioms PAG.Part167.I_pow_four_mul
#print axioms PAG.Part167.epsG_one
#print axioms PAG.Part167.epsG_three
#print axioms PAG.Part167.zeta_order_one_odd_iff'
