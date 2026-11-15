/-
  PAG 2.0 Part 155（2026-10-22）— p ≡ 3 (mod 4)、導手 p^{2m+1}: ord ζ = 2p か 4p かの判定
  1. 2 次の因子 Q = q^{p^n} は Q² = −1
  2. ord χ が偶数 ⇒ ord ζ = 2p、ord χ が奇数 ⇒ ord ζ = 4p
  3. p ≡ 1 では Q² = 1
  4. p ≡ 1、ord χ 偶数 ⇒ ord ζ = p
-/
import PAG158

namespace PAG.Part159

open ZMod Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. Q² = −1**（p ≡ 3、n ≥ 1）。 -/
theorem Q_sq (h4 : p % 4 = 3) (n : ℕ) (hn : 1 ≤ n) (q : ℂ) (hq : q ^ (2 * p) = PAG.Part119.Lc p (-1)) :
    (q ^ (p ^ n)) ^ 2 = -1 := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  rw [PAG.Part129.Lc_neg_one_of_three h4] at hq
  rw [← pow_mul, show p ^ n * 2 = 2 * p * p ^ (n - 1) by
    rw [show p ^ n = p * p ^ (n - 1) by rw [← pow_succ']; congr 1; omega]; ring, pow_mul, hq]
  exact (Odd.pow (hp.out.odd_of_ne_two hp2)).neg_one_pow

/-- **2. ord ζ = 2p（ord χ 偶数）、4p（ord χ 奇数）**。 -/
theorem zeta_order_parity (h4 : p % 4 = 3) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    (2 ∣ orderOf χ → orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = 2 * p) ∧
    (¬ 2 ∣ orderOf χ → orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = 4 * p) := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  have hn : 1 ≤ n := by omega
  obtain ⟨h2, h2p, h4p⟩ := PAG.Part158.zeta_order_three_mod_four h4 n m hnm hm χ hχ
  set z := gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)
  constructor
  · intro hev
    apply Nat.dvd_antisymm _ h2p
    apply orderOf_dvd_of_pow_eq_one
    -- ζ^{2p} = 1
    obtain ⟨δ, hδ⟩ := PAG.Part141.exists_delta_gen (p := p) (c := n + 1) (k := m + 1) (by omega) (by omega) χ
    obtain ⟨q, hq2, hord⟩ := PAG.Part156.orderOf_gauss_odd_freq hnm hm hp2 χ hχ δ hδ
    rw [show n + 1 - 1 = n by omega] at hord
    obtain ⟨s', hs, -, -⟩ := PAG.Part157.order_chi_split hp2 n hn χ hχ
    have hδu : IsUnit (-δ) :=
      ((PAG.Part142.primitive_iff_freq (p := p) (k := m + 1) (by omega) (by omega) χ δ hδ).mp hχ).neg
    have hx : (χ (-δ) ^ (p ^ n)) ^ s' = 1 := by
      rw [← pow_mul, ← hs, ← MulChar.pow_apply' _ (orderOf_pos χ).ne', pow_orderOf_eq_one, MulChar.one_apply hδu]
    have hs2 : 2 ∣ s' := by
      have hcop : Nat.Coprime 2 (p ^ n) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
      rw [hs] at hev; exact hcop.dvd_of_dvd_mul_left hev
    obtain ⟨t, ht⟩ := hs2
    have hQ := Q_sq h4 n hn q hq2
    have hy : (χ (-δ) ^ (p ^ n) * q ^ (p ^ n)) ^ (2 * s') = 1 := by
      rw [mul_pow, pow_mul', hx, one_pow, one_mul, pow_mul, hQ, ht]
      exact Even.neg_one_pow ⟨t, by ring⟩
    rw [← pow_mul, mul_comm (orderOf χ)]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hord, hs]
    obtain ⟨r, hr⟩ := orderOf_dvd_of_pow_eq_one hy
    refine ⟨r, ?_⟩
    calc 2 * p * (p ^ n * s') = p ^ (n + 1) * (2 * s') := by ring
      _ = _ := by rw [hr]; ring
  · intro hodd
    apply Nat.dvd_antisymm h4p
    -- 4 ∣ ord ζ
    have hz4 := PAG.Part129.four_dvd_orderOf_gauss_odd (p := p) hnm hm h4 χ hχ
    have h4z : 4 ∣ orderOf (z ^ orderOf χ) := by
      rw [orderOf_pow' _ (orderOf_pos χ).ne']
      have hg : Nat.Coprime 4 (Nat.gcd (orderOf z) (orderOf χ)) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        apply Nat.Coprime.pow_left
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
        exact fun h => hodd (h.trans (Nat.gcd_dvd_right _ _))
      have hsplit : orderOf z = Nat.gcd (orderOf z) (orderOf χ) * (orderOf z / Nat.gcd (orderOf z) (orderOf χ)) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
      exact hg.dvd_of_dvd_mul_left (hsplit ▸ hz4)
    have hcop : Nat.Coprime 4 p := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
    exact hcop.mul_dvd_of_dvd_of_dvd h4z ((Nat.dvd_mul_left p 2).trans h2p)

/-- **3. Q² = 1**（p ≡ 1、n ≥ 1）。 -/
theorem Q_sq_one (h4 : p % 4 = 1) (n : ℕ) (hn : 1 ≤ n) (q : ℂ) (hq : q ^ (2 * p) = PAG.Part119.Lc p (-1)) :
    (q ^ (p ^ n)) ^ 2 = 1 := by
  rw [PAG.Part129.Lc_neg_one_of_one h4] at hq
  rw [← pow_mul, show p ^ n * 2 = 2 * p * p ^ (n - 1) by
    rw [show p ^ n = p * p ^ (n - 1) by rw [← pow_succ']; congr 1; omega]; ring, pow_mul, hq, one_pow]

/-- **4. p ≡ 1、導手 p^{2m+1}、ord χ 偶数 ⇒ ord ζ = p**（偶数の導手と同じ）。 -/
theorem zeta_order_one_even (h4 : p % 4 = 1) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (hev : 2 ∣ orderOf χ) :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = p := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  have hn : 1 ≤ n := by omega
  obtain ⟨-, hpd, -⟩ := PAG.Part157.zeta_order_odd hp2 n m hnm hm χ hχ
  apply Nat.dvd_antisymm _ hpd
  apply orderOf_dvd_of_pow_eq_one
  obtain ⟨δ, hδ⟩ := PAG.Part141.exists_delta_gen (p := p) (c := n + 1) (k := m + 1) (by omega) (by omega) χ
  obtain ⟨q, hq2, hord⟩ := PAG.Part156.orderOf_gauss_odd_freq hnm hm hp2 χ hχ δ hδ
  rw [show n + 1 - 1 = n by omega] at hord
  obtain ⟨s', hs, -, -⟩ := PAG.Part157.order_chi_split hp2 n hn χ hχ
  have hδu : IsUnit (-δ) :=
    ((PAG.Part142.primitive_iff_freq (p := p) (k := m + 1) (by omega) (by omega) χ δ hδ).mp hχ).neg
  have hx : (χ (-δ) ^ (p ^ n)) ^ s' = 1 := by
    rw [← pow_mul, ← hs, ← MulChar.pow_apply' _ (orderOf_pos χ).ne', pow_orderOf_eq_one, MulChar.one_apply hδu]
  have hs2 : 2 ∣ s' := by
    have hcop : Nat.Coprime 2 (p ^ n) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
    rw [hs] at hev; exact hcop.dvd_of_dvd_mul_left hev
  obtain ⟨t, ht⟩ := hs2
  have hQ := Q_sq_one h4 n hn q hq2
  have hy : (χ (-δ) ^ (p ^ n) * q ^ (p ^ n)) ^ s' = 1 := by
    rw [mul_pow, hx, one_mul, ht, pow_mul, hQ, one_pow]
  rw [← pow_mul, mul_comm (orderOf χ)]
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hord, hs]
  obtain ⟨r, hr⟩ := orderOf_dvd_of_pow_eq_one hy
  refine ⟨r, ?_⟩
  calc p * (p ^ n * s') = p ^ (n + 1) * s' := by ring
    _ = _ := by rw [hr]; ring

end PAG.Part159

#print axioms PAG.Part159.Q_sq
#print axioms PAG.Part159.zeta_order_parity
#print axioms PAG.Part159.Q_sq_one
#print axioms PAG.Part159.zeta_order_one_even
