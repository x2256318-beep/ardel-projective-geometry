/-
  PAG 2.0 Part 151（2026-10-22）— 導手 p^{2m+1} の位数の明示（p 奇素数）
  1. lcm_tame の一般化: x^{p^{c−1} r} = 1、p ∤ r ⇒ lcm(ord x, p^c) = p^c · ord(x^{p^{c−1}})
  2. y^{p^{c−1} r} = 1、p ∤ r、u₀ 単元 ⇒ ord(y e(u₀)) = lcm(ord y, p^c)
  3. 位数の公式: ord z = p^c · ord(χ(u₀)^{p^{c−1}} · q^{p^{c−1}})、q^{2p} = L(−1)
  4. 2 次の因子 Q = q^{p^{c−1}}: Q^4 = 1、p ≡ 1 (mod 4) なら Q^2 = 1
-/
import PAG154

namespace PAG.Part155

open ZMod Finset PAG.Part127 PAG.Part128 PAG.Part119

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. lcm_tame の一般化**。 -/
theorem lcm_tame_gen (c : ℕ) (hc1 : 1 ≤ c) (x : ℂ) (r : ℕ) (hr0 : ¬ p ∣ r) (hx : x ^ (p ^ (c - 1) * r) = 1) :
    Nat.lcm (orderOf x) (p ^ c) = p ^ c * orderOf (x ^ (p ^ (c - 1))) := by
  have hr1 : r ≠ 0 := fun h0 => hr0 (h0 ▸ dvd_zero p)
  have hpos : 0 < p ^ (c - 1) * r := Nat.mul_pos (pow_pos hp.out.pos _) (Nat.pos_of_ne_zero hr1)
  have ho0 : orderOf x ≠ 0 := (orderOf_pos_iff.mpr ((isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hpos, hx⟩))).ne'
  obtain ⟨j, r', hr, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho0 p hp.out.ne_one
  have hdvd : orderOf x ∣ p ^ (c - 1) * r := orderOf_dvd_of_pow_eq_one hx
  have hcopr : Nat.Coprime r' p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hr))
  have hcop1 : Nat.Coprime (p ^ j) r := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]; exact hr0
  have hj : j ≤ c - 1 := by
    have h1 : p ^ j ∣ p ^ (c - 1) * r := (Dvd.intro _ hor.symm).trans hdvd
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp (hcop1.dvd_of_dvd_mul_right h1)
  -- ord(x^{p^{c−1}}) = r'
  have hord : orderOf (x ^ (p ^ (c - 1))) = r' := by
    rw [orderOf_pow' _ (pow_ne_zero _ hp.out.ne_zero), hor]
    have hg : Nat.gcd (p ^ j * r') (p ^ (c - 1)) = p ^ j := by
      rw [Nat.Coprime.gcd_mul_right_cancel _ (Nat.Coprime.pow_right _ hcopr)]
      exact Nat.gcd_eq_left (pow_dvd_pow p hj)
    rw [hg, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos j)]
  rw [hord, hor]
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · exact Nat.mul_dvd_mul (pow_dvd_pow p (by omega)) dvd_rfl
    · exact dvd_mul_right _ _
  · have hcop : Nat.Coprime (p ^ c) r' := Nat.Coprime.pow_left c (Nat.coprime_comm.mp hcopr)
    exact hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_right _ _) ((dvd_mul_left r' (p ^ j)).trans (Nat.dvd_lcm_left _ _))


/-- **2. ord(y e(u₀)) = lcm(ord y, p^c)**。 -/
theorem ord_mul_e (c : ℕ) (hc1 : 1 ≤ c) (y : ℂ) (r : ℕ) (hr0 : ¬ p ∣ r) (hy : y ^ (p ^ (c - 1) * r) = 1)
    (u₀ : ZMod (p ^ c)) (hu : IsUnit u₀) :
    orderOf (y * stdAddChar u₀) = Nat.lcm (orderOf y) (p ^ c) := by
  have hx := stdAddChar_pow_eq_one_iff (p := p) u₀ hu
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [mul_pow, (hx _).mpr (Nat.dvd_lcm_right _ _), mul_one]
    obtain ⟨a, ha⟩ := Nat.dvd_lcm_left (orderOf y) (p ^ c)
    rw [ha, pow_mul, pow_orderOf_eq_one, one_pow]
  · have hz1 := pow_orderOf_eq_one (y * stdAddChar u₀)
    have hpd := pdvd_of_mul_gen c hc1 _ _ hx r hr0 hy _ hz1
    have he : stdAddChar u₀ ^ orderOf (y * stdAddChar u₀) = 1 := (hx _).mpr hpd
    have hy1 : y ^ orderOf (y * stdAddChar u₀) = 1 := by
      have := hz1; rw [mul_pow, he, mul_one] at this; exact this
    exact Nat.lcm_dvd (orderOf_dvd_of_pow_eq_one hy1) hpd

/-- **3. 導手 p^{2m+1} の位数の公式**（p 奇素数）。 -/
theorem orderOf_gauss_odd_formula {c m : ℕ} (hc : c = 2 * m + 1) (hm : 1 ≤ m) (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧ ∃ q : ℂ, q ^ (2 * p) = Lc p (-1) ∧
      orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ))
        = p ^ c * orderOf (χ u₀ ^ (p ^ (c - 1)) * q ^ (p ^ (c - 1))) := by
  obtain ⟨u₀, hu, q, hq4, hq2, hz⟩ := PAG.Part129.gauss_odd_phase2 hc hm χ hχ
  refine ⟨u₀, hu, q, hq2 hp2, ?_⟩
  have hc1 : 1 ≤ c := by omega
  have hr : ¬ p ∣ 4 * (p - 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · have h4 : p ∣ 2 ^ 2 := by norm_num; exact h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h4))
    · have := hp.out.two_le; have := Nat.le_of_dvd (by omega) h; omega
  have hy : (χ u₀ * q) ^ (p ^ (c - 1) * (4 * (p - 1))) = 1 := by
    have h1 : χ u₀ ^ (p ^ (c - 1) * (p - 1)) = 1 := by
      rw [← Nat.totient_prime_pow hp.out (by omega : 0 < c)]; exact chi_pow_totient χ u₀ hu
    have h2 : 4 * p ∣ p ^ (c - 1) * (4 * (p - 1)) := by
      obtain ⟨k, hk⟩ : p ∣ p ^ (c - 1) := dvd_pow_self p (by omega)
      exact ⟨k * (p - 1), by rw [hk]; ring⟩
    obtain ⟨k, hk⟩ := h2
    rw [mul_pow, show p ^ (c - 1) * (4 * (p - 1)) = p ^ (c - 1) * (p - 1) * 4 by ring, pow_mul, h1, one_pow,
      one_mul, show p ^ (c - 1) * (p - 1) * 4 = p ^ (c - 1) * (4 * (p - 1)) by ring, hk, pow_mul, hq4, one_pow]
  rw [hz, show χ u₀ * stdAddChar u₀ * q = (χ u₀ * q) * stdAddChar u₀ by ring,
    ord_mul_e c hc1 _ _ hr hy u₀ hu, lcm_tame_gen c hc1 _ _ hr hy, mul_pow]

/-- **4. 2 次の因子 Q = q^{p^{c−1}}**: Q^4 = 1、p ≡ 1 (mod 4) なら Q^2 = 1（c ≥ 2）。 -/
theorem quad_factor (c : ℕ) (hc : 2 ≤ c) (q : ℂ) (hq : q ^ (2 * p) = Lc p (-1)) :
    (q ^ (p ^ (c - 1))) ^ 4 = 1 ∧ (p % 4 = 1 → (q ^ (p ^ (c - 1))) ^ 2 = 1) := by
  obtain ⟨k, hk⟩ : p ∣ p ^ (c - 1) := dvd_pow_self p (by omega)
  have hL2 : Lc p (-1) ^ 2 = 1 := Lc_sq (-1) (neg_ne_zero.mpr one_ne_zero)
  constructor
  · rw [← pow_mul, hk, show p * k * 4 = 2 * p * (2 * k) by ring, pow_mul, hq, pow_mul, hL2, one_pow]
  · intro h1
    rw [← pow_mul, hk, show p * k * 2 = 2 * p * k by ring, pow_mul, hq, PAG.Part129.Lc_neg_one_of_one h1, one_pow]

end PAG.Part155

#print axioms PAG.Part155.lcm_tame_gen
#print axioms PAG.Part155.ord_mul_e
#print axioms PAG.Part155.orderOf_gauss_odd_formula
#print axioms PAG.Part155.quad_factor
