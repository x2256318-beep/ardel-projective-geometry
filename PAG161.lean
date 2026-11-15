/-
  PAG 2.0 Part 157（2026-10-22）— 単独のケットの ζ の位数の統一公式（p 奇素数、導手 p^{2m+1}）
  1. zeta_p_formula: ζ^p = (L(−δ/2) ε^{p^{n+1}})^{s'}
  2. orderOf_zeta_formula: ord ζ = p · ord((L(−δ/2) ε^{p^{n+1}})^{s'})
-/
import PAG160

namespace PAG.Part161

open ZMod Finset PAG.Part119 PAG.Part160

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. ζ^p = (L(−δ/2) ε^{p^{n+1}})^{s'}**。 -/
theorem zeta_p_formula (hp2 : p ≠ 2) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (δ : ZMod (p ^ (n + 1)))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ (n + 1))) ^ (m + 1) * y) = stdAddChar ((p : ZMod (p ^ (n + 1))) ^ (m + 1) * δ * y))
    (s' : ℕ) (hs : orderOf χ = p ^ n * s') :
    ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ^ p
      = (Lc p (((-δ : ZMod (p ^ (n + 1))).cast : ZMod p) * 2⁻¹) * epsG p ^ (p ^ (n + 1))) ^ s' := by
  have hn : 1 ≤ n := by omega
  obtain ⟨u₀, hu, hS₀⟩ := PAG.Part139.exists_unit_SP (p := p) (k := m + 1) (by omega) χ hχ
  obtain ⟨κ, hz⟩ := phase_explicit hnm hm hp2 χ hχ u₀ hu hS₀
  have hcast := PAG.Part142.stationary_cast (p := p) (k := m + 1) (by omega) χ δ hδ u₀ hS₀
  have hdvd : p ∣ p ^ (n + 1) := dvd_pow_self p (by omega)
  have hu0 : ((u₀.cast : ZMod p)) ≠ 0 := by
    have := (hu.map (ZMod.castHom hdvd (ZMod p))).ne_zero
    simpa [ZMod.castHom_apply] using this
  have hA : (u₀.cast : ZMod p) * 2⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero (PAG.Part119.two_ne_zero' hp2))
  rw [hz, zeta_pow_p n χ u₀ hu _ s' hs,
    show ∀ x : ℂ, x ^ (p ^ (n + 1)) = (x ^ (p ^ n)) ^ p from fun x => by rw [pow_succ, pow_mul],
    Q_explicit hp2 n hn κ _ hA, mul_pow, pow_odd_of_sq_one _ (Lc_sq _ hA) _ (hp.out.odd_of_ne_two hp2),
    ← pow_mul, ← pow_succ, hcast]

/-- **2. ord ζ = p · ord((L(−δ/2) ε^{p^{n+1}})^{s'})**。 -/
theorem orderOf_zeta_formula (hp2 : p ≠ 2) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (δ : ZMod (p ^ (n + 1)))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ (n + 1))) ^ (m + 1) * y) = stdAddChar ((p : ZMod (p ^ (n + 1))) ^ (m + 1) * δ * y))
    (s' : ℕ) (hs : orderOf χ = p ^ n * s') :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ)
      = p * orderOf ((Lc p (((-δ : ZMod (p ^ (n + 1))).cast : ZMod p) * 2⁻¹) * epsG p ^ (p ^ (n + 1))) ^ s') := by
  obtain ⟨-, hpd, -⟩ := PAG.Part157.zeta_order_odd hp2 n m hnm hm χ hχ
  rw [← zeta_p_formula hp2 n m hnm hm χ hχ δ hδ s' hs, orderOf_pow' _ hp.out.ne_zero,
    Nat.gcd_eq_right hpd, Nat.mul_div_cancel' hpd]

end PAG.Part161

#print axioms PAG.Part161.zeta_p_formula
#print axioms PAG.Part161.orderOf_zeta_formula
