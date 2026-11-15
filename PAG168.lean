/-
  PAG 2.0 Part 164（2026-10-22）— 単独のケットの ζ の位数の完全に明示的な公式
  導手 p^{2m+1}（p 奇素数）、ord χ = p^n s'、ε = τ(L)/√p（= 1 または i、Part 163）
  1. Lc_neg_half: L(−x/2) = L(−1) L(2x)
  2. eps_pow_three: p ≡ 3、n+1 奇数なら ε^{p^{n+1}} = −i
  3. zeta_p_explicit: ζ^p = (ε · L(2δ))^{s'}
  4. orderOf_zeta_explicit: ord ζ = p · ord((ε · L(2δ))^{s'})
-/
import PAG167

namespace PAG.Part168

open Complex Finset PAG.Part119 PAG.Part160 PAG.Part167
open ZMod (stdAddChar)

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. L(−x/2) = L(−1) L(2x)**。 -/
theorem Lc_neg_half (hp2 : p ≠ 2) (x : ZMod p) : Lc p (-x * 2⁻¹) = Lc p (-1) * Lc p (2 * x) := by
  have h2 := two_ne_zero' hp2
  have e : -x * 2⁻¹ = (-1) * (2 * x) * (2⁻¹) ^ 2 := by field_simp
  rw [e, map_mul, map_mul, map_pow, Lc_sq _ (inv_ne_zero h2), mul_one]

/-- **2. p ≡ 3、n + 1 = 2m + 1 なら ε^{p^{n+1}} = −i**。 -/
theorem eps_pow_three (h4 : p % 4 = 3) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) : epsG p ^ (p ^ (n + 1)) = -I := by
  rw [epsG_three p h4]
  have hmod : p ^ (n + 1) % 4 = 3 := by
    rw [Nat.pow_mod, h4, hnm, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  rw [← Nat.div_add_mod (p ^ (n + 1)) 4, hmod, pow_add, pow_mul, show I ^ 4 = 1 by norm_num, one_pow, one_mul,
    pow_succ, I_sq]; ring

/-- **3. ζ^p = (ε · L(2δ))^{s'}**。 -/
theorem zeta_p_explicit (hp2 : p ≠ 2) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (δ : ZMod (p ^ (n + 1)))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ (n + 1))) ^ (m + 1) * y) = stdAddChar ((p : ZMod (p ^ (n + 1))) ^ (m + 1) * δ * y))
    (s' : ℕ) (hs : orderOf χ = p ^ n * s') :
    ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ^ p
      = (epsG p * Lc p (2 * (δ.cast : ZMod p))) ^ s' := by
  rw [PAG.Part161.zeta_p_formula hp2 n m hnm hm χ hχ δ hδ s' hs]
  congr 1
  rw [ZMod.cast_neg (dvd_pow_self p (by omega)), Lc_neg_half hp2]
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by
    have := hp.out.eq_one_or_self_of_dvd 2; have h := hp.out.odd_of_ne_two hp2; omega) with h4 | h4
  · rw [PAG.Part129.Lc_neg_one_of_one h4, epsG_one p h4, one_pow]; ring
  · rw [PAG.Part129.Lc_neg_one_of_three h4, eps_pow_three h4 n m hnm, epsG_three p h4]; ring

/-- **4. ord ζ = p · ord((ε · L(2δ))^{s'})**。 -/
theorem orderOf_zeta_explicit (hp2 : p ≠ 2) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (δ : ZMod (p ^ (n + 1)))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ (n + 1))) ^ (m + 1) * y) = stdAddChar ((p : ZMod (p ^ (n + 1))) ^ (m + 1) * δ * y))
    (s' : ℕ) (hs : orderOf χ = p ^ n * s') :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ)
      = p * orderOf ((epsG p * Lc p (2 * (δ.cast : ZMod p))) ^ s') := by
  obtain ⟨-, hpd, -⟩ := PAG.Part157.zeta_order_odd hp2 n m hnm hm χ hχ
  rw [← zeta_p_explicit hp2 n m hnm hm χ hχ δ hδ s' hs, orderOf_pow' _ hp.out.ne_zero,
    Nat.gcd_eq_right hpd, Nat.mul_div_cancel' hpd]

end PAG.Part168

#print axioms PAG.Part168.Lc_neg_half
#print axioms PAG.Part168.eps_pow_three
#print axioms PAG.Part168.zeta_p_explicit
#print axioms PAG.Part168.orderOf_zeta_explicit
