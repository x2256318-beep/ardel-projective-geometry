/-
  PAG 2.0 Part 153（2026-10-22）— 単独のケットの ζ の位数の完全な決定（p 奇素数）
  導手 p^{n+1}（n ≥ 1）、χ 原始、z = τ/√(p^{n+1})、ζ = z^{ord χ}
  1. ord χ = p^n · s'、p ∤ s'、s' ∣ p − 1
  2. n + 1 が偶数: ord ζ = p ちょうど
  3. n + 1 が奇数: ζ^{4p} = 1、p ∣ ord ζ、p ≡ 1 (mod 4) なら ζ^{2p} = 1
-/
import PAG156

namespace PAG.Part157

open ZMod Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. ord χ = p^n · s'、p ∤ s'、s' ∣ p − 1**。 -/
theorem order_chi_split (hp2 : p ≠ 2) (n : ℕ) (hn : 1 ≤ n) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : ∃ s' : ℕ, orderOf χ = p ^ n * s' ∧ ¬ p ∣ s' ∧ s' ∣ p - 1 := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨s', hs'⟩ := PAG.Part133.pc_dvd_orderOf (p := p) n hn (hp.out.odd_of_ne_two hp2) χ hχ
  have hφ := PAG.Part134.orderOf_dvd_totient χ
  rw [Nat.totient_prime_pow hp.out (by omega), show n + 1 - 1 = n by omega, hs'] at hφ
  have h1 : s' ∣ p - 1 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos n) hφ
  refine ⟨s', hs', fun h => ?_, h1⟩
  have := Nat.le_of_dvd (by have := hp.out.two_le; omega) (h.trans h1)
  have := hp.out.two_le; omega

/-- **2. 導手 p^{2m}: ord ζ = p**。 -/
theorem zeta_order_even (hp2 : p ≠ 2) (n m : ℕ) (hnm : n + 1 = 2 * m) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = p := by
  have hn : 1 ≤ n := by omega
  obtain ⟨δ, hδ⟩ := PAG.Part141.exists_delta_gen (p := p) (c := n + 1) (k := m) (by omega) (by omega) χ
  have hord := PAG.Part154.orderOf_gauss_freq hnm hm χ hχ δ hδ
  rw [show n + 1 - 1 = n by omega] at hord
  obtain ⟨s', hs, hps, -⟩ := order_chi_split hp2 n hn χ hχ
  set z := gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)
  set t := orderOf (χ (-δ) ^ (p ^ n))
  have ht : t ∣ s' := by
    apply orderOf_dvd_of_pow_eq_one
    have hδu : IsUnit (-δ) :=
      ((PAG.Part142.primitive_iff_freq (p := p) (k := m) (by omega) (by omega) χ δ hδ).mp hχ).neg
    rw [← pow_mul, ← hs, ← MulChar.pow_apply' _ (orderOf_pos χ).ne', pow_orderOf_eq_one,
      MulChar.one_apply hδu]
  apply orderOf_eq_prime
  · rw [← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hord, hs, pow_succ]
    obtain ⟨r, hr⟩ := ht
    exact ⟨r, by rw [hr]; ring⟩
  · intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord, hs, pow_succ, mul_assoc] at h2
    have h3 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos n) h2
    exact hps ((dvd_mul_right p t).trans h3)

/-- **3. 導手 p^{2m+1}: ζ^{4p} = 1、p ∣ ord ζ、p ≡ 1 (mod 4) なら ζ^{2p} = 1**。 -/
theorem zeta_order_odd (hp2 : p ≠ 2) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ^ (4 * p) = 1 ∧
    p ∣ orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ∧
    (p % 4 = 1 → ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ^ (2 * p) = 1) := by
  have hn : 1 ≤ n := by omega
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨δ, hδ⟩ := PAG.Part141.exists_delta_gen (p := p) (c := n + 1) (k := m + 1) (by omega) (by omega) χ
  obtain ⟨q, hq2, hord⟩ := PAG.Part156.orderOf_gauss_odd_freq hnm hm hp2 χ hχ δ hδ
  rw [show n + 1 - 1 = n by omega] at hord
  obtain ⟨s', hs, hps, -⟩ := order_chi_split hp2 n hn χ hχ
  obtain ⟨hQ4, hQ2⟩ := PAG.Part155.quad_factor (p := p) (n + 1) (by omega) q hq2
  rw [show n + 1 - 1 = n by omega] at hQ4 hQ2
  set z := gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)
  have hδu : IsUnit (-δ) :=
    ((PAG.Part142.primitive_iff_freq (p := p) (k := m + 1) (by omega) (by omega) χ δ hδ).mp hχ).neg
  have hx : (χ (-δ) ^ (p ^ n)) ^ s' = 1 := by
    rw [← pow_mul, ← hs, ← MulChar.pow_apply' _ (orderOf_pos χ).ne', pow_orderOf_eq_one, MulChar.one_apply hδu]
  set y := χ (-δ) ^ (p ^ n) * q ^ (p ^ n)
  have hy4 : y ^ (4 * s') = 1 := by
    simp only [y]
    rw [mul_pow, show 4 * s' = s' * 4 by ring, pow_mul (χ (-δ) ^ (p ^ n)) s' 4, hx, one_pow, one_mul,
      pow_mul' (q ^ (p ^ n)) s' 4, hQ4, one_pow]
  have hzord : orderOf z ∣ 4 * p * orderOf χ := by
    rw [hord, hs, pow_succ]
    obtain ⟨r, hr⟩ := orderOf_dvd_of_pow_eq_one hy4
    exact ⟨r, by rw [show 4 * p * (p ^ n * s') = p ^ n * p * (4 * s') by ring, hr]; ring⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm (orderOf χ)]; exact orderOf_dvd_iff_pow_eq_one.mp hzord
  · rw [orderOf_pow' _ (orderOf_pos χ).ne']
    apply PAG.Part132.p_dvd_div_gcd p hp.out (n + 1)
    · rw [hord]; exact dvd_mul_right _ _
    · rw [hs]; intro h
      rw [pow_succ] at h
      exact hps (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos n) h)
  · intro h1
    have hy2 : y ^ (2 * s') = 1 := by
      simp only [y]
      rw [mul_pow, show 2 * s' = s' * 2 by ring, pow_mul (χ (-δ) ^ (p ^ n)) s' 2, hx, one_pow, one_mul,
        pow_mul' (q ^ (p ^ n)) s' 2, hQ2 h1, one_pow]
    rw [← pow_mul, mul_comm (orderOf χ)]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hord, hs, pow_succ]
    obtain ⟨r, hr⟩ := orderOf_dvd_of_pow_eq_one hy2
    exact ⟨r, by rw [show 2 * p * (p ^ n * s') = p ^ n * p * (2 * s') by ring, hr]; ring⟩

end PAG.Part157

#print axioms PAG.Part157.order_chi_split
#print axioms PAG.Part157.zeta_order_even
#print axioms PAG.Part157.zeta_order_odd
