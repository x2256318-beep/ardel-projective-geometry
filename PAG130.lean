/-
  PAG 2.0 Part 126（2026-10-21）— p = 2 のガウス和の位相の位数
  N = 2^c、χ 原始、z = τ(χ)/√(2^c) について
  1. 偶数の c ≥ 2: ord z = 2^c
  2. 奇数の c ≥ 5: ord z = 2^c
  （c = 3 は例外: 位数 1 と 4 が現れる — 数値）
-/
import PAG129

namespace PAG.Part130

open ZMod Finset PAG.Part118 PAG.Part120 PAG.Part127 PAG.Part128

theorem chi_pow_two_pow (c : ℕ) (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (2 ^ c)) (u : ZMod (2 ^ c))
    (hu : IsUnit u) : χ u ^ (2 ^ (c - 1)) = 1 := by
  have h := chi_pow_totient χ u hu
  rwa [Nat.totient_prime_pow Nat.prime_two (by omega), show 2 - 1 = 1 from rfl, mul_one] at h

/-- **1. 偶数の c**: ord z = 2^c。 -/
theorem orderOf_gauss_two_even (c m : ℕ) (hc : c = 2 * m) (hm : 1 ≤ m) (χ : DirichletCharacter ℂ (2 ^ c))
    (hχ : χ.IsPrimitive) :
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((2 : ℝ) ^ c) : ℝ) : ℂ)) = 2 ^ c := by
  obtain ⟨u₀, hu, ho⟩ := orderOf_gauss_even (p := 2) hc hm χ hχ
  have h := ho
  push_cast at h
  rw [h]
  apply Nat.lcm_eq_right
  exact (orderOf_dvd_of_pow_eq_one (chi_pow_two_pow c (by omega) χ u₀ hu)).trans
    (pow_dvd_pow 2 (by omega))

/-- **2. 奇数の c ≥ 5**: ord z = 2^c。 -/
theorem orderOf_gauss_two_odd (c m : ℕ) (hc : c = 2 * m + 1) (hm : 2 ≤ m) (χ : DirichletCharacter ℂ (2 ^ c))
    (hχ : χ.IsPrimitive) :
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((2 : ℝ) ^ c) : ℝ) : ℂ)) = 2 ^ c := by
  obtain ⟨u₀, hu, q, hq, hz⟩ := gauss_odd_phase (p := 2) hc (by omega) χ hχ
  have hz' : gaussSum χ stdAddChar / ((Real.sqrt ((2 : ℝ) ^ c) : ℝ) : ℂ) = χ u₀ * stdAddChar u₀ * q := by
    have := hz; push_cast at this; exact this
  rw [hz', show χ u₀ * stdAddChar u₀ * q = (χ u₀ * q) * stdAddChar u₀ by ring]
  have hx := stdAddChar_pow_eq_one_iff (p := 2) u₀ hu
  have h8 : 8 ∣ 2 ^ (c - 1) := ⟨2 ^ (c - 4), by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega⟩
  have hy : (χ u₀ * q) ^ (2 ^ (c - 1) * 1) = 1 := by
    obtain ⟨k, hk⟩ := h8
    rw [mul_one, mul_pow, chi_pow_two_pow c (by omega) χ u₀ hu, one_mul, hk, pow_mul,
      show q ^ 8 = 1 by norm_num at hq; exact hq, one_pow]
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    have key : ∀ x : ℂ, x ^ (2 ^ (c - 1) * 1) = 1 → x ^ (2 ^ c) = 1 := fun x hx1 => by
      rw [show 2 ^ c = 2 ^ (c - 1) * 1 * 2 by rw [mul_one, ← pow_succ]; congr 1; omega, pow_mul, hx1, one_pow]
    rw [mul_pow, (hx _).mpr dvd_rfl, mul_one]
    exact key _ hy
  · exact pdvd_of_mul_gen (p := 2) c (by omega) _ _ hx 1 (by norm_num) hy _
      (pow_orderOf_eq_one _)

end PAG.Part130

#print axioms PAG.Part130.chi_pow_two_pow
#print axioms PAG.Part130.orderOf_gauss_two_even
#print axioms PAG.Part130.orderOf_gauss_two_odd
