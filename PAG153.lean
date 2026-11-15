/-
  PAG 2.0 Part 149（2026-10-22）— 導手 4, 8 の因子を含む積のケットの ζ の 2 部分
  1. z² = −1 ⇒ ord z = 4
  2. 導手 2^{c+1}（c = 1, 2）で χ(−1) = −1 なら ord z = 4、ord χ = 2
  3. 積のケット: q_i = 2、導手 4 または（導手 8 かつ χ_i(−1) = −1）、
     4 ∤ ∏_{j≠i} ord z_j、∀ j ≠ i: 4 ∤ ord χ_j ⇒ ζ の 2 部分はちょうど 2
-/
import PAG152

namespace PAG.Part153

open ZMod Finset

/-- **1. z² = −1 ⇒ ord z = 4**。 -/
theorem orderOf_of_sq_neg_one (z : ℂ) (h : z ^ 2 = -1) : orderOf z = 4 := by
  have h4 : z ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, h]; norm_num
  have hd := orderOf_dvd_of_pow_eq_one h4
  have h2' : ¬ orderOf z ∣ 2 := by
    intro hd2; have := orderOf_dvd_iff_pow_eq_one.mp hd2; rw [h] at this; norm_num at this
  rcases (Nat.dvd_prime_pow (show Nat.Prime 2 from Nat.prime_two)).mp (show orderOf z ∣ 2 ^ 2 by simpa using hd)
    with ⟨j, hj, hjo⟩
  interval_cases j
  · exact absurd (by rw [hjo]; norm_num) h2'
  · exact absurd (by rw [hjo]; norm_num) h2'
  · rw [hjo]; norm_num

/-- **2. 導手 4, 8 の奇指標**: ord z = 4、ord χ = 2。 -/
theorem small_two_facts {p : ℕ} [hp : Fact p.Prime] (hp2 : p = 2) (c : ℕ) (hc : c = 1 ∨ c = 2)
    (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive) (hodd : χ (-1) = -1) :
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (c + 1)) : ℝ) : ℂ)) = 4 ∧ orderOf χ = 2 := by
  subst hp2
  rcases hc with rfl | rfl
  · have h := PAG.Part151.real_phase_sq (N := 4) χ hχ (PAG.Part151.sq_eq_one_mod4 χ)
    have hne : χ ≠ 1 := by
      intro h1; rw [h1, MulChar.one_apply (isUnit_one.neg)] at hodd; norm_num at hodd
    refine ⟨?_, orderOf_eq_prime (PAG.Part151.sq_eq_one_mod4 χ) hne⟩
    apply orderOf_of_sq_neg_one
    rw [hodd] at h
    convert h using 4
    norm_num
  · have h := PAG.Part151.real_phase_sq (N := 8) χ hχ (PAG.Part151.sq_eq_one_mod8 χ)
    have hne : χ ≠ 1 := by
      intro h1; rw [h1, MulChar.one_apply (isUnit_one.neg)] at hodd; norm_num at hodd
    refine ⟨?_, orderOf_eq_prime (PAG.Part151.sq_eq_one_mod8 χ) hne⟩
    apply orderOf_of_sq_neg_one
    rw [hodd] at h
    convert h using 4
    norm_num

section Ket

open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117 PAG.Part125 PAG.Part126 PAG.Part132 PAG.Part136

variable {n : ℕ} (q : Fin n → ℕ) [hq : ∀ i, Fact (q i).Prime] (K w c : Fin n → ℕ)

/-- **3. 導手 4, 8（奇）の因子: ζ の 2 部分はちょうど 2**。 -/
theorem zeta_prod_small_two (hc : ∀ i, 1 ≤ c i) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (q i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (q i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := q i) (K i) (K i - (c i + 1) - w i)) (i : Fin n)
    (hqi : q i = 2) (hci : c i = 1 ∨ c i = 2) (hodd : χ i (-1) = -1)
    (hcond : ¬ 2 ^ 2 ∣ ∏ j ∈ univ.erase i,
      orderOf (gaussSum (χ j) stdAddChar / ((Real.sqrt ((q j : ℝ) ^ (c j + 1)) : ℝ) : ℂ)))
    (hχj : ∀ j, j ≠ i → ¬ 2 ^ 2 ∣ orderOf (χ j)) :
    2 ∣ orderOf ((∏ i, cnorm (q i) (K i) (K i - (c i + 1) - w i)
        * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i))) ∧
    ¬ 4 ∣ orderOf ((∏ i, cnorm (q i) (K i) (K i - (c i + 1) - w i)
        * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i))) := by
  rw [zeta_prod_eq_pow q K w c h χ hχ t ht]
  set z : Fin n → ℂ := fun j => gaussSum (χ j) stdAddChar / ((Real.sqrt ((q j : ℝ) ^ (c j + 1)) : ℝ) : ℂ)
  obtain ⟨hz, ho⟩ := small_two_facts (p := q i) hqi (c i) hci (χ i) (hχ i) hodd
  have hL0 : lcmF n (fun i => orderOf (χ i)) ≠ 0 := lcmF_ne_zero n _ (fun i => (orderOf_pos (χ i)).ne')
  have hLF : 2 ^ 1 ∣ lcmF n (fun i => orderOf (χ i)) := by
    rw [pow_one, ← ho]; exact dvd_lcmF n (fun i => orderOf (χ i)) i
  have hLF' : ¬ 2 ^ (1 + 1) ∣ lcmF n (fun i => orderOf (χ i)) := by
    intro h2
    rw [lcmF_eq] at h2
    obtain ⟨j, -, hj⟩ := PAG.Part134.pow_dvd_finset_lcm Nat.prime_two (by omega) univ (fun j => orderOf (χ j))
      (fun j _ => (orderOf_pos (χ j)).ne') h2
    by_cases hji : j = i
    · subst hji; rw [ho] at hj; norm_num at hj
    · exact hχj j hji hj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := ppart_prod_pow (p := 2) z (fun j => orderOf_gauss_ne_zero (c j) (hc j) (χ j) (hχ j)) i
    2 1 _ hL0 (by rw [show z i = _ from rfl, hz]; norm_num)
    (by rw [show z i = _ from rfl, hz]; norm_num)
    hcond hLF hLF' (by omega)
  exact ⟨by simpa using key.1, by simpa using key.2⟩

end Ket

end PAG.Part153

#print axioms PAG.Part153.orderOf_of_sq_neg_one
#print axioms PAG.Part153.small_two_facts
#print axioms PAG.Part153.zeta_prod_small_two
