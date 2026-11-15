/-
  PAG 2.0 Part 147（2026-10-22）— 実指標のガウス和と、例外的な導手 4, 8
  1. χ 原始、χ² = 1 ⇒ τ(χ)² = χ(−1) N、z² = χ(−1)
  2. 単独のケット（導手 p^{c+1}）で χ² = 1、χ ≠ 1 ⇒ ζ = χ(−1)
  3. 法 4: すべての指標で χ² = 1、原始なら χ(−1) = −1、z² = −1、ord z = 4、ζ = −1
  4. 法 8: すべての指標で χ² = 1、原始なら ζ = χ(−1)
-/
import PAG150

namespace PAG.Part151

open ZMod Finset

/-- **1a. 実指標の τ² = χ(−1) N**。 -/
theorem real_gauss_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h2 : χ ^ 2 = 1) :
    gaussSum χ stdAddChar ^ 2 = χ (-1) * N := by
  have hinv : χ⁻¹ = χ := by
    rw [inv_eq_iff_mul_eq_one, ← sq, h2]
  have := PAG.Part16.gauss_mul_gauss_inv_eq hχ
  rw [hinv] at this
  rw [sq]; exact this

/-- **1b. z² = χ(−1)**。 -/
theorem real_phase_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h2 : χ ^ 2 = 1) :
    (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ 2 = χ (-1) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hs : ((Real.sqrt (N : ℝ) : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hN.le]; push_cast; rfl
  have hs0 : ((Real.sqrt (N : ℝ) : ℝ) : ℂ) ^ 2 ≠ 0 := by rw [hs]; exact_mod_cast hN.ne'
  rw [div_pow, real_gauss_sq χ hχ h2, hs, mul_div_assoc, div_self (by exact_mod_cast hN.ne'), mul_one]

section Single

open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117

variable {p : ℕ} [hp : Fact p.Prime]

/-- **2. 単独のケットで χ² = 1、χ ≠ 1 なら ζ = χ(−1)**。 -/
theorem zeta_real (K w c : ℕ) (h : w + (c + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (c + 1)))
    (hχ : χ.IsPrimitive) (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) (t₀ : ZMod (p ^ K))
    (ht₀ : t₀ ∈ Tset (p := p) K (K - (c + 1) - w)) :
    (cnorm p K (K - (c + 1) - w) * 𝓕 (ket K w (c + 1) h χ) t₀) ^ orderOf χ = χ (-1) := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have ho : orderOf χ = 2 := orderOf_eq_prime h2 h1
  rw [zeta_eq_gauss K w c h χ hχ t₀ ht₀, ho]
  have := real_phase_sq χ hχ h2
  push_cast at this ⊢
  exact this

end Single

/-! ## 3. 法 4 -/

theorem sq_eq_one_mod4 (χ : DirichletCharacter ℂ 4) : χ ^ 2 = 1 := by
  apply MulChar.ext
  intro a
  have ha : a ^ 2 = 1 := by revert a; decide
  rw [MulChar.pow_apply' _ (by norm_num), ← map_pow, ← Units.val_pow_eq_pow_val, ha, Units.val_one, map_one,
    MulChar.one_apply a.isUnit]

theorem neg_one_mod4 (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) : χ (-1) = -1 := by
  have hne : χ ≠ 1 := by
    intro h1
    rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hχ
    norm_num at hχ
  have hv : χ (-1) ^ 2 = 1 := by
    rw [← map_pow]; norm_num
  by_contra hn
  have h1 : χ (-1) = 1 := by
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by ring_nf; rw [hv]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (eq_neg_of_add_eq_zero_left h) hn
  apply hne
  apply MulChar.ext
  intro a
  have ha : (a : ZMod 4) = 1 ∨ (a : ZMod 4) = -1 := by revert a; decide
  rcases ha with ha | ha
  · rw [ha, map_one, MulChar.one_apply isUnit_one]
  · rw [ha, h1, MulChar.one_apply (by rw [← ha]; exact a.isUnit)]

/-- **3. 法 4: z² = −1、ord z = 4、ζ = −1**。 -/
theorem phase_mod4 (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) :
    (gaussSum χ stdAddChar / ((Real.sqrt (4 : ℕ) : ℝ) : ℂ)) ^ 2 = -1 ∧
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt (4 : ℕ) : ℝ) : ℂ)) = 4 := by
  have h := real_phase_sq χ hχ (sq_eq_one_mod4 χ)
  rw [neg_one_mod4 χ hχ] at h
  refine ⟨h, ?_⟩
  set z := gaussSum χ stdAddChar / ((Real.sqrt (4 : ℕ) : ℝ) : ℂ)
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

/-! ## 4. 法 8 -/

theorem sq_eq_one_mod8 (χ : DirichletCharacter ℂ 8) : χ ^ 2 = 1 := by
  apply MulChar.ext
  intro a
  have ha : a ^ 2 = 1 := by revert a; decide
  rw [MulChar.pow_apply' _ (by norm_num), ← map_pow, ← Units.val_pow_eq_pow_val, ha, Units.val_one, map_one,
    MulChar.one_apply a.isUnit]

/-- **4. 法 8: z² = χ(−1)**。 -/
theorem phase_mod8 (χ : DirichletCharacter ℂ 8) (hχ : χ.IsPrimitive) :
    (gaussSum χ stdAddChar / ((Real.sqrt (8 : ℕ) : ℝ) : ℂ)) ^ 2 = χ (-1) :=
  real_phase_sq χ hχ (sq_eq_one_mod8 χ)

end PAG.Part151

#print axioms PAG.Part151.real_gauss_sq
#print axioms PAG.Part151.real_phase_sq
#print axioms PAG.Part151.zeta_real
#print axioms PAG.Part151.sq_eq_one_mod4
#print axioms PAG.Part151.neg_one_mod4
#print axioms PAG.Part151.phase_mod4
#print axioms PAG.Part151.sq_eq_one_mod8
#print axioms PAG.Part151.phase_mod8
