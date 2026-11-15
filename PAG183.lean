/-
  PAG 2.0 Part 179（2026-10-22）— 3 次・4 次・6 次の因子の積の完全な判定
  1. root_mul_iff: C^M = 1（M > 0）なら CY が 1 の冪根 ⇔ Y が 1 の冪根
  2. sextic_zpow: z(ψL)^b = c^b · z(ψ)^{−2b}（c = ψ(4)⁻¹ ε、c¹² = 1）
  3. full_root_iff: 相異なる素数の 3 次 ψ_i（冪 a_i）と 6 次 ψ_i L（冪 b_i）、相異なる素数の 4 次 φ_j（冪 l_j）の積が
     1 の冪根 ⇔ すべての i で a_i = 2b_i、すべての j で l_j = 0
-/
import PAG182

namespace PAG.Part183

open Complex Finset PAG.Part119 PAG.Part160 PAG.Part171 PAG.Part180 PAG.Part181 PAG.Part182
open ZMod (stdAddChar)

/-- **1. 1 の冪根を掛けても判定は変わらない**。 -/
theorem root_mul_iff (C Y : ℂ) (M : ℕ) (hM : 0 < M) (hC : C ^ M = 1) :
    (∃ N : ℕ, 0 < N ∧ (C * Y) ^ N = 1) ↔ (∃ N : ℕ, 0 < N ∧ Y ^ N = 1) := by
  constructor
  · rintro ⟨N, hN, h⟩
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have := congrArg (· ^ M) h
    simp only [one_pow, mul_pow, ← pow_mul] at this
    rwa [mul_comm N M, pow_mul C M N, hC, one_pow, one_mul] at this
  · rintro ⟨N, hN, h⟩
    refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
    rw [mul_pow, pow_mul Y, h, one_pow, mul_one, mul_comm, pow_mul, hC, one_pow]

variable {p : ℕ} [hp : Fact p.Prime]

theorem c12 (h3p : p % 3 = 1) (ψ : DirichletCharacter ℂ p) (h3 : orderOf ψ = 3) :
    ((ψ 4)⁻¹ * epsG p) ^ 12 = 1 := by
  have hp2 : p ≠ 2 := by intro h; rw [h] at h3p; norm_num at h3p
  have hψ3 : ψ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one ψ
  have h4 : (4 : ZMod p) ≠ 0 := by
    have h2 := two_ne_zero' (p := p) hp2
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hc3 : (ψ 4) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' ψ (by norm_num), hψ3, MulChar.one_apply (Ne.isUnit h4)]
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hε4 : epsG p ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, epsG_sq hp2,
      PAG.Part167.Lc_neg_one_pow p ((p - 1) / 2) (by omega), ← pow_mul]
    exact (show Even ((p - 1) / 2 * 2) from ⟨(p - 1) / 2, by ring⟩).neg_one_pow
  rw [mul_pow, inv_pow, show (12 : ℕ) = 3 * 4 by rfl, pow_mul, hc3, one_pow, inv_one, one_mul,
    show (3 * 4 : ℕ) = 4 * 3 by rfl, pow_mul, hε4, one_pow]

/-- **2. z(ψL)^b = c^b · z(ψ)^{−2b}**。 -/
theorem sextic_zpow (h3p : p % 3 = 1) (ψ : DirichletCharacter ℂ p) (h3 : orderOf ψ = 3) (b : ℤ) :
    (gaussSum (ψ * Lc p) stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ b
      = ((ψ 4)⁻¹ * epsG p) ^ b * (gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ (-2 * b) := by
  have hne : ψ ≠ 1 := by intro h; rw [h, orderOf_one] at h3; norm_num at h3
  have hz0 : gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
    apply div_ne_zero (PAG.Part16.gaussSum_ne_zero (primitive_of_ne_one _ hne))
    have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)
    exact_mod_cast this.ne'
  have hrel := sextic_relation h3p ψ h3
  have hzL : gaussSum (ψ * Lc p) stdAddChar / ((Real.sqrt p : ℝ) : ℂ)
      = ((ψ 4)⁻¹ * epsG p) * ((gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 2)⁻¹ := by
    rw [← hrel, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hz0), mul_one]
  rw [hzL, mul_zpow, inv_zpow', ← zpow_natCast, ← zpow_mul]
  congr 2; push_cast; ring

variable {nc nq : ℕ} (pc : Fin nc → ℕ) [hpc : ∀ i, Fact (pc i).Prime] (pq : Fin nq → ℕ) [hpq : ∀ j, Fact (pq j).Prime]

/-- **3. 3 次・4 次・6 次の因子の積の完全な判定**。 -/
theorem full_root_iff (hinjc : Function.Injective pc) (h3p : ∀ i, pc i % 3 = 1)
    (ψ : ∀ i, DirichletCharacter ℂ (pc i)) (h3 : ∀ i, orderOf (ψ i) = 3) (a b : Fin nc → ℤ)
    (hinjq : Function.Injective pq) (φ : ∀ j, DirichletCharacter ℂ (pq j)) (h4 : ∀ j, orderOf (φ j) = 4)
    (l : Fin nq → ℤ) :
    (∃ N : ℕ, 0 < N ∧ ((∏ i, (gaussSum (ψ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ a i
          * (gaussSum (ψ i * Lc (pc i)) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ b i)
        * (∏ j, (gaussSum (φ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ)) ^ l j)) ^ N = 1)
      ↔ (∀ i, a i = 2 * b i) ∧ (∀ j, l j = 0) := by
  set C := ∏ i, ((ψ i 4)⁻¹ * epsG (pc i)) ^ b i
  have hC : C ^ 12 = 1 := by
    simp only [C]; rw [← Finset.prod_pow]
    apply Finset.prod_eq_one; intro i _
    rw [← zpow_natCast, ← zpow_mul, mul_comm (b i), zpow_mul, zpow_natCast, c12 (h3p i) (ψ i) (h3 i), one_zpow]
  have hsplit : (∏ i, (gaussSum (ψ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ a i
        * (gaussSum (ψ i * Lc (pc i)) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ b i)
      = C * ∏ i, (gaussSum (ψ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ (a i - 2 * b i) := by
    simp only [C]; rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro i _
    have hne : ψ i ≠ 1 := by intro h; have := h3 i; rw [h, orderOf_one] at this; norm_num at this
    have hz0 : gaussSum (ψ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ) ≠ 0 := by
      apply div_ne_zero (PAG.Part16.gaussSum_ne_zero (primitive_of_ne_one _ hne))
      have : (0 : ℝ) < Real.sqrt (pc i) := Real.sqrt_pos.mpr (by exact_mod_cast (hpc i).out.pos)
      exact_mod_cast this.ne'
    rw [sextic_zpow (h3p i) (ψ i) (h3 i), show a i - 2 * b i = a i + (-2 * b i) by ring, zpow_add₀ hz0]
    ring
  rw [hsplit, mul_assoc, root_mul_iff C _ 12 (by norm_num) hC,
    mixed_zpow_root_iff pc pq hinjc h3p ψ h3 (fun i => a i - 2 * b i) hinjq φ h4 l]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i => by have := h1 i; omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun i => by rw [h1 i]; ring, h2⟩

end PAG.Part183

#print axioms PAG.Part183.root_mul_iff
#print axioms PAG.Part183.c12
#print axioms PAG.Part183.sextic_zpow
#print axioms PAG.Part183.full_root_iff
