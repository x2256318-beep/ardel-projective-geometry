/-
  PAG 2.0 Part 154（2026-10-22）— p ≡ 3 (mod 4)、導手 p^{2m+1}: 単独のケットの ζ の位数は偶数
  1. 4 ∤ ord χ（ord χ = p^n s′、s′ ∣ p − 1、v₂(p − 1) = 1）
  2. 2 ∣ ord ζ（4 ∣ ord z と合わせて）
  3. 系: ord ζ ∈ {2p, 4p}（2p ∣ ord ζ ∣ 4p）
-/
import PAG157

namespace PAG.Part158

open ZMod Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. p ≡ 3 (mod 4) なら 4 ∤ ord χ**。 -/
theorem four_not_dvd_ord_chi (h4 : p % 4 = 3) (n : ℕ) (hn : 1 ≤ n) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : ¬ 4 ∣ orderOf χ := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  obtain ⟨s', hs, -, hs1⟩ := PAG.Part157.order_chi_split hp2 n hn χ hχ
  rw [hs]
  intro h
  have hcop : Nat.Coprime 4 (p ^ n) := by
    apply Nat.Coprime.pow_right
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2)
  have h1 : 4 ∣ s' := hcop.dvd_of_dvd_mul_left h
  have h2 : 4 ∣ p - 1 := h1.trans hs1
  omega

/-- **2・3. ord ζ は偶数、ord ζ ∈ {2p, 4p}**。 -/
theorem zeta_order_three_mod_four (h4 : p % 4 = 3) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    2 ∣ orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ∧
    2 * p ∣ orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ∧
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ∣ 4 * p := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  have hn : 1 ≤ n := by omega
  have hz4 := PAG.Part129.four_dvd_orderOf_gauss_odd (p := p) hnm hm h4 χ hχ
  have h2 : 2 ∣ orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) := by
    rw [orderOf_pow' _ (orderOf_pos χ).ne']
    exact PAG.Part132.p_dvd_div_gcd 2 Nat.prime_two 2 _ _ (by simpa using hz4)
      (by simpa using four_not_dvd_ord_chi h4 n hn χ hχ)
  obtain ⟨h4p, hpd, -⟩ := PAG.Part157.zeta_order_odd hp2 n m hnm hm χ hχ
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2)
  exact ⟨h2, hcop.mul_dvd_of_dvd_of_dvd h2 hpd, orderOf_dvd_of_pow_eq_one h4p⟩

end PAG.Part158

#print axioms PAG.Part158.four_not_dvd_ord_chi
#print axioms PAG.Part158.zeta_order_three_mod_four
