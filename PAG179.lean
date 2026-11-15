/-
  PAG 2.0 Part 175（2026-10-22）— 導手 p の 3 次・4 次の因子の一般の積
  1. 単独の因子: z⁶ ∈ ℚ(ω)、z⁴ ∈ ℚ(i)、共役 = 逆元
  2. key_lemma: u ∈ ℚ(ω)、v ∈ ℚ(i)、ū = u⁻¹、v̄ = v⁻¹ で u^{2N} v^{3N} = 1 なら u^{4N} = 1 かつ v^{6N} = 1
  3. mixed_not_root_c: 3 次の因子（相異なる素数、1 個以上）× 4 次の因子（任意）は 1 の冪根でない
  4. mixed_not_root_q: 4 次の因子（相異なる素数、1 個以上）× 3 次の因子（任意）も同様
-/
import PAG178

namespace PAG.Part179

open Complex Finset PAG.Part171 PAG.Part172 PAG.Part174 PAG.Part175 PAG.Part176 PAG.Part177 PAG.Part178
open ZMod (stdAddChar)

theorem InQω_one : InQω 1 := ⟨1, 0, by simp⟩
theorem InQi_one : InQi 1 := ⟨1, 0, by simp⟩

theorem InQω_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, InQω (f i)) : InQω (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InQω_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact InQω_mul (h j (by simp)) (ih (fun i hi => h i (by simp [hi])))

theorem InQi_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, InQi (f i)) : InQi (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InQi_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact InQi_mul (h j (by simp)) (ih (fun i hi => h i (by simp [hi])))

theorem InQω_conj {y : ℂ} (h : InQω y) : InQω ((starRingEnd ℂ) y) := by
  obtain ⟨A, B, rfl⟩ := h
  exact ⟨A - B, -B, by rw [map_add, map_mul, conj_ω, map_ratCast, map_ratCast]; push_cast; ring⟩

theorem InQi_conj {y : ℂ} (h : InQi y) : InQi ((starRingEnd ℂ) y) := by
  obtain ⟨A, B, rfl⟩ := h
  exact ⟨A, -B, by rw [map_add, map_mul, conj_I, map_ratCast, map_ratCast]; push_cast; ring⟩

theorem conj_prod_inv {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, (starRingEnd ℂ) (f i) = (f i)⁻¹) :
    (starRingEnd ℂ) (∏ i ∈ s, f i) = (∏ i ∈ s, f i)⁻¹ := by
  rw [map_prod, ← Finset.prod_inv_distrib]; exact Finset.prod_congr rfl h

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1a. 3 次の因子: z⁶ ∈ ℚ(ω)、共役 = 逆元**。 -/
theorem z6_facts (χ : DirichletCharacter ℂ p) (h3 : orderOf χ = 3) :
    InQω ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 6) ∧
      (starRingEnd ℂ) ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 6)
        = ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 6)⁻¹ := by
  obtain ⟨a, b, hJ, hJc, hab⟩ := jacobi_data χ h3
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hnJ := jacobi_norm χ h3
  have hJ0 : jacobiSum χ χ ≠ 0 := by intro h; rw [h, zero_mul] at hnJ; exact hp0 hnJ.symm
  rw [z6_eq χ h3]
  refine ⟨?_, ?_⟩
  · rw [hJ]
    exact ⟨(a ^ 2 - b ^ 2 : ℚ) / p, (2 * a * b - b ^ 2 : ℚ) / p, by
      push_cast; field_simp; linear_combination ((b : ℂ) ^ 2) * ω_sq⟩
  · have hJbar : (starRingEnd ℂ) (jacobiSum χ χ) = p / jacobiSum χ χ := by
      rw [eq_div_iff hJ0, mul_comm]; exact hnJ
    rw [map_div₀, map_pow, hJbar, map_natCast]; field_simp

/-- **1b. 4 次の因子: z⁴ ∈ ℚ(i)、共役 = 逆元**。 -/
theorem z4_facts (ψ : DirichletCharacter ℂ p) (h4 : orderOf ψ = 4) :
    InQi ((gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 4) ∧
      (starRingEnd ℂ) ((gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 4)
        = ((gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 4)⁻¹ := by
  obtain ⟨c, d, hK, hKc, hcd⟩ := jacobi_data4 ψ h4
  obtain ⟨σ, hσ, hsσ⟩ := sign_int ψ
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hnK := jacobi_norm4 ψ h4
  have hK0 : jacobiSum ψ ψ ≠ 0 := by intro h; rw [h, zero_mul] at hnK; exact hp0 hnK.symm
  have hσ2 : (σ : ℂ) ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσ0 : (σ : ℂ) ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  rw [z4_eq ψ h4, hsσ]
  refine ⟨?_, ?_⟩
  · rw [hK]
    exact ⟨σ * (c ^ 2 - d ^ 2 : ℚ) / p, σ * (2 * c * d : ℚ) / p, by
      push_cast; field_simp; linear_combination ((d : ℂ) ^ 2) * I_sq⟩
  · have hKbar : (starRingEnd ℂ) (jacobiSum ψ ψ) = p / jacobiSum ψ ψ := by
      rw [eq_div_iff hK0, mul_comm]; exact hnK
    rw [map_div₀, map_mul, map_pow, hKbar, map_natCast, map_intCast]; field_simp
    linear_combination hσ2

/-- **2. 鍵の補題**。 -/
theorem key_lemma (u v : ℂ) (hu : InQω u) (hv : InQi v) (hu' : (starRingEnd ℂ) u = u⁻¹)
    (hv' : (starRingEnd ℂ) v = v⁻¹) (N : ℕ) (hN : 0 < N) (h : u ^ (2 * N) * v ^ (3 * N) = 1) :
    u ^ (4 * N) = 1 ∧ v ^ (6 * N) = 1 := by
  have heq : u ^ (2 * N) = (v⁻¹) ^ (3 * N) := by rw [inv_pow]; exact eq_inv_of_mul_eq_one_left h
  have hvi : InQi (v⁻¹) := hv' ▸ InQi_conj hv
  obtain ⟨r, hr⟩ := inter_rat (InQω_pow hu _) (heq ▸ InQi_pow hvi _)
  have hc := congrArg (starRingEnd ℂ) hr
  rw [map_pow, hu', map_ratCast, inv_pow, hr] at hc
  have hu0 : u ≠ 0 := by
    rintro rfl; rw [zero_pow (by omega), zero_mul] at h; exact zero_ne_one h
  have hr0 : (r : ℂ) ≠ 0 := by rw [← hr]; exact pow_ne_zero _ hu0
  have hrr : (r : ℂ) * r = 1 := by
    calc (r : ℂ) * r = r * (r : ℂ)⁻¹ := by rw [hc]
      _ = 1 := mul_inv_cancel₀ hr0
  have h1 : u ^ (4 * N) = 1 := by rw [show 4 * N = 2 * N * 2 by ring, pow_mul, hr, sq]; exact hrr
  refine ⟨h1, ?_⟩
  have h2 : (v ^ (3 * N)) ^ 2 = 1 := by
    have : v ^ (3 * N) = (u ^ (2 * N))⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_pow, ← pow_mul, show 2 * N * 2 = 4 * N by ring, h1, inv_one]
  rw [show 6 * N = 3 * N * 2 by ring, pow_mul, h2]

variable {nc nq : ℕ} (pc : Fin nc → ℕ) [hpc : ∀ i, Fact (pc i).Prime] (pq : Fin nq → ℕ) [hpq : ∀ j, Fact (pq j).Prime]

theorem split_pow (Zc Zq : ℂ) (N : ℕ) (hX : (Zc * Zq) ^ N = 1) : (Zc ^ 6) ^ (2 * N) * (Zq ^ 4) ^ (3 * N) = 1 := by
  rw [← pow_mul, ← pow_mul, show 6 * (2 * N) = 12 * N by ring, show 4 * (3 * N) = 12 * N by ring, ← mul_pow,
    mul_comm 12 N, pow_mul, hX, one_pow]

/-- **3. 3 次（相異なる素数、1 個以上）× 4 次（任意）の積は 1 の冪根でない**。 -/
theorem mixed_not_root_c (hnc : 0 < nc) (hinjc : Function.Injective pc) (h3p : ∀ i, pc i % 3 = 1)
    (χ : ∀ i, DirichletCharacter ℂ (pc i)) (h3 : ∀ i, orderOf (χ i) = 3)
    (ψ : ∀ j, DirichletCharacter ℂ (pq j)) (h4 : ∀ j, orderOf (ψ j) = 4) :
    ∀ N : ℕ, 0 < N → ((∏ i, gaussSum (χ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ))
      * (∏ j, gaussSum (ψ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ))) ^ N ≠ 1 := by
  intro N hN hX
  set Zc := ∏ i, gaussSum (χ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)
  set Zq := ∏ j, gaussSum (ψ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ)
  have hu : InQω (Zc ^ 6) := by
    simp only [Zc]; rw [← Finset.prod_pow]
    exact InQω_prod _ _ (fun i _ => (z6_facts (χ i) (h3 i)).1)
  have hu' : (starRingEnd ℂ) (Zc ^ 6) = (Zc ^ 6)⁻¹ := by
    simp only [Zc]; rw [← Finset.prod_pow]
    exact conj_prod_inv _ _ (fun i _ => (z6_facts (χ i) (h3 i)).2)
  have hv : InQi (Zq ^ 4) := by
    simp only [Zq]; rw [← Finset.prod_pow]
    exact InQi_prod _ _ (fun j _ => (z4_facts (ψ j) (h4 j)).1)
  have hv' : (starRingEnd ℂ) (Zq ^ 4) = (Zq ^ 4)⁻¹ := by
    simp only [Zq]; rw [← Finset.prod_pow]
    exact conj_prod_inv _ _ (fun j _ => (z4_facts (ψ j) (h4 j)).2)
  have := (key_lemma _ _ hu hv hu' hv' N hN (split_pow Zc Zq N hX)).1
  rw [← pow_mul] at this
  exact cubic_multi_not_root pc hnc hinjc h3p χ h3 (6 * (4 * N)) (by omega) this

/-- **4. 4 次（相異なる素数、1 個以上）× 3 次（任意）の積も 1 の冪根でない**。 -/
theorem mixed_not_root_q (hnq : 0 < nq) (hinjq : Function.Injective pq)
    (χ : ∀ i, DirichletCharacter ℂ (pc i)) (h3 : ∀ i, orderOf (χ i) = 3)
    (ψ : ∀ j, DirichletCharacter ℂ (pq j)) (h4 : ∀ j, orderOf (ψ j) = 4) :
    ∀ N : ℕ, 0 < N → ((∏ i, gaussSum (χ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ))
      * (∏ j, gaussSum (ψ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ))) ^ N ≠ 1 := by
  intro N hN hX
  set Zc := ∏ i, gaussSum (χ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)
  set Zq := ∏ j, gaussSum (ψ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ)
  have hu : InQω (Zc ^ 6) := by
    simp only [Zc]; rw [← Finset.prod_pow]
    exact InQω_prod _ _ (fun i _ => (z6_facts (χ i) (h3 i)).1)
  have hu' : (starRingEnd ℂ) (Zc ^ 6) = (Zc ^ 6)⁻¹ := by
    simp only [Zc]; rw [← Finset.prod_pow]
    exact conj_prod_inv _ _ (fun i _ => (z6_facts (χ i) (h3 i)).2)
  have hv : InQi (Zq ^ 4) := by
    simp only [Zq]; rw [← Finset.prod_pow]
    exact InQi_prod _ _ (fun j _ => (z4_facts (ψ j) (h4 j)).1)
  have hv' : (starRingEnd ℂ) (Zq ^ 4) = (Zq ^ 4)⁻¹ := by
    simp only [Zq]; rw [← Finset.prod_pow]
    exact conj_prod_inv _ _ (fun j _ => (z4_facts (ψ j) (h4 j)).2)
  have := (key_lemma _ _ hu hv hu' hv' N hN (split_pow Zc Zq N hX)).2
  rw [← pow_mul] at this
  exact quartic_multi_not_root pq hnq hinjq ψ h4 (4 * (6 * N)) (by omega) this

end PAG.Part179

#print axioms PAG.Part179.InQω_prod
#print axioms PAG.Part179.InQi_prod
#print axioms PAG.Part179.InQω_conj
#print axioms PAG.Part179.InQi_conj
#print axioms PAG.Part179.conj_prod_inv
#print axioms PAG.Part179.z6_facts
#print axioms PAG.Part179.z4_facts
#print axioms PAG.Part179.key_lemma
#print axioms PAG.Part179.split_pow
#print axioms PAG.Part179.mixed_not_root_c
#print axioms PAG.Part179.mixed_not_root_q
