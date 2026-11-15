/-
  PAG 2.0 Part 167（2026-10-22）— 導手 p の場合：3 次の指標のガウス和の位相は 1 の冪根ではない
  p ≡ 1 (mod 3)、χ は位数 3 の指標、z = τ(χ)/√p、ω = (−1 + √3 i)/2、J = J(χ, χ)
  1. not_root_of_trace: x + 1/x が整数でない有理数なら x は 1 の冪根でない
  2. J = a + bω（a, b ∈ ℤ）、a² − ab + b² = p
  3. J = τ³/p、z⁶ = J²/p、z⁶ + z⁻⁶ = ((2a − b)² − 2p)/p
  4. gauss_cubic_not_root: z^N ≠ 1（N > 0）。とくに ζ = z³ の位数は 0（無限位数）
-/
import PAG170

namespace PAG.Part171

open Complex Finset Polynomial
open ZMod (stdAddChar)

/-- **1. x + 1/x が整数でない有理数なら、x は 1 の冪根ではない**。 -/
theorem not_root_of_trace (x : ℂ) (r : ℚ) (hr : x + x⁻¹ = (r : ℂ)) (hnot : ∀ n : ℤ, r ≠ n) :
    ∀ N : ℕ, 0 < N → x ^ N ≠ 1 := by
  intro N hN hxN
  have hint : IsIntegral ℤ x := ⟨X ^ N - 1, monic_X_pow_sub_C 1 hN.ne', by simp [hxN]⟩
  have hinv : x⁻¹ = x ^ (N - 1) :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', Nat.sub_add_cancel hN, hxN])
  have hint2 : IsIntegral ℤ (x + x⁻¹) := hint.add (hinv ▸ hint.pow _)
  rw [hr] at hint2
  have hq : IsIntegral ℤ r := by
    have h := (isIntegral_algHom_iff ((Algebra.ofId ℚ ℂ).restrictScalars ℤ) (algebraMap ℚ ℂ).injective (x := r)).mp
    exact h (by simpa using hint2)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  exact hnot y (by rw [← hy]; simp)

/-- ω = (−1 + √3 i)/2。 -/
noncomputable def ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2

theorem ω_sq : ω ^ 2 = -1 - ω := by
  unfold ω
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  linear_combination (-1 / 4 : ℂ) * h3 + (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * I_sq

theorem conj_ω : (starRingEnd ℂ) ω = -1 - ω := by
  unfold ω
  rw [map_div₀, map_add, map_neg, map_one, map_mul, conj_ofReal, conj_I]
  simp only [map_ofNat]; ring

theorem cube_eq_one (u : ℂ) (hu : u ^ 3 = 1) : u = 1 ∨ u = ω ∨ u = -1 - ω := by
  have h : (u - 1) * (u - ω) * (u - (-1 - ω)) = 0 := by
    linear_combination hu - (u - 1) * ω_sq
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · left; linear_combination h
    · right; left; linear_combination h
  · right; right; linear_combination h

/-- ℤ[ω] の元。 -/
def InZω (y : ℂ) : Prop := ∃ a b : ℤ, y = a + b * ω

theorem InZω_add {y y' : ℂ} (h : InZω y) (h' : InZω y') : InZω (y + y') := by
  obtain ⟨a, b, rfl⟩ := h; obtain ⟨a', b', rfl⟩ := h'
  exact ⟨a + a', b + b', by push_cast; ring⟩

variable {p : ℕ} [hp : Fact p.Prime]

/-- **2a. J(χ, χ) ∈ ℤ[ω]**（χ³ = 1）。 -/
theorem jacobi_InZω (χ : MulChar (ZMod p) ℂ) (h3 : χ ^ 3 = 1) : InZω (jacobiSum χ χ) := by
  unfold jacobiSum
  apply Finset.sum_induction _ InZω (fun _ _ => InZω_add) ⟨0, 0, by simp⟩
  intro x _
  rw [← map_mul]
  by_cases h0 : x * (1 - x) = 0
  · rw [h0, MulChar.map_zero]; exact ⟨0, 0, by simp⟩
  · have hu : (χ (x * (1 - x))) ^ 3 = 1 := by
      rw [← MulChar.pow_apply' χ (by norm_num), h3, MulChar.one_apply (Ne.isUnit h0)]
    rcases cube_eq_one _ hu with h | h | h
    · exact ⟨1, 0, by rw [h]; simp⟩
    · exact ⟨0, 1, by rw [h]; simp⟩
    · exact ⟨-1, -1, by rw [h]; push_cast; ring⟩

/-- **2b. conj J(χ, χ) = J(χ⁻¹, χ⁻¹)**。 -/
theorem conj_jacobi (χ : MulChar (ZMod p) ℂ) : (starRingEnd ℂ) (jacobiSum χ χ) = jacobiSum χ⁻¹ χ⁻¹ := by
  unfold jacobiSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul]
  exact congrArg₂ (· * ·) (MulChar.star_apply' χ x) (MulChar.star_apply' χ (1 - x))

/-- **2c. J · conj J = p**（χ は位数 3）。 -/
theorem jacobi_norm (χ : MulChar (ZMod p) ℂ) (h3 : orderOf χ = 3) :
    jacobiSum χ χ * (starRingEnd ℂ) (jacobiSum χ χ) = p := by
  have hne : χ ≠ 1 := by intro h; rw [h, orderOf_one] at h3; norm_num at h3
  have hne2 : χ * χ ≠ 1 := by
    intro h
    have : orderOf χ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [h3] at this; norm_num at this
  have hch : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact hp.out.ne_zero.symm
  rw [conj_jacobi, jacobiSum_mul_jacobiSum_inv hch hne hne hne2, ZMod.card]

/-- **3a. 位数 3 の指標で χ(−1) = 1**。 -/
theorem chi_neg_one (χ : MulChar (ZMod p) ℂ) (h3 : orderOf χ = 3) : χ (-1) = 1 := by
  have hχ3 : χ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one χ
  have a : χ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have b : χ (-1) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' χ (by norm_num), hχ3, MulChar.one_apply isUnit_one.neg]
  linear_combination b - χ (-1) * a

/-- **3b. 法 p の非自明な指標は原始的**。 -/
theorem primitive_of_ne_one (χ : DirichletCharacter ℂ p) (hne : χ ≠ 1) : χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hd := DirichletCharacter.conductor_dvd_level χ
  rcases (Nat.dvd_prime hp.out).mp hd with h | h
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) hne
  · exact h

/-- **3c. J(χ, χ) = τ(χ)³ / p**。 -/
theorem jacobi_eq_gauss_cube (χ : DirichletCharacter ℂ p) (h3 : orderOf χ = 3) :
    jacobiSum χ χ = gaussSum χ stdAddChar ^ 3 / p := by
  have hne : χ ≠ 1 := by intro h; rw [h, orderOf_one] at h3; norm_num at h3
  have hχ3 : χ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one χ
  have hinv : χ * χ = χ⁻¹ := by
    symm; apply inv_eq_of_mul_eq_one_right; rw [← mul_assoc, ← sq, ← pow_succ]; exact hχ3
  have hne2 : χ * χ ≠ 1 := by
    rw [hinv]; exact inv_ne_one.mpr hne
  have hpr := primitive_of_ne_one χ hne
  have hgi := PAG.Part16.gauss_mul_gauss_inv_eq hpr
  rw [chi_neg_one χ h3, one_mul] at hgi
  have hτ : gaussSum χ stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero hpr
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum (by rw [ZMod.card]; exact hp0) hne2
    (ZMod.isPrimitive_stdAddChar p), hinv]
  have : gaussSum χ⁻¹ stdAddChar = p / gaussSum χ stdAddChar := by
    rw [eq_div_iff hτ, mul_comm, hgi]
  rw [this]; field_simp

/-- **4. 3 次の指標のガウス和の位相は 1 の冪根ではない**（p ≡ 1 (mod 3)）。 -/
theorem gauss_cubic_not_root (h3p : p % 3 = 1) (χ : DirichletCharacter ℂ p) (h3 : orderOf χ = 3) :
    ∀ N : ℕ, 0 < N → (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ N ≠ 1 := by
  have hχ3 : χ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one χ
  obtain ⟨a, b, hJ⟩ := jacobi_InZω χ hχ3
  have hnorm := jacobi_norm χ h3
  set J := jacobiSum χ χ
  have hJc : (starRingEnd ℂ) J = a + b * (-1 - ω) := by
    rw [hJ, map_add, map_mul, conj_ω, map_intCast, map_intCast]
  have hω2 := ω_sq
  -- a² − ab + b² = p
  have hab : (a ^ 2 - a * b + b ^ 2 : ℤ) = p := by
    have h : ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℂ) = p := by
      rw [← hnorm, hJc, hJ]; push_cast; linear_combination ((b : ℂ) ^ 2) * hω2
    exact_mod_cast h
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hJ0 : J ≠ 0 := by intro h; rw [h, zero_mul] at hnorm; exact hp0 hnorm.symm
  set z := gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)
  have hs : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = p := by
    rw [← ofReal_pow, Real.sq_sqrt (by exact_mod_cast hp.out.pos.le)]; push_cast; ring
  have hz6 : z ^ 6 = J ^ 2 / p := by
    have hJg : J = gaussSum χ stdAddChar ^ 3 / p := jacobi_eq_gauss_cube χ h3
    simp only [z]
    rw [hJg, div_pow, show (((Real.sqrt p : ℝ) : ℂ)) ^ 6 = ((((Real.sqrt p : ℝ) : ℂ)) ^ 2) ^ 3 by ring, hs]
    field_simp
  set r : ℚ := ((2 * a - b) ^ 2 - 2 * p) / p
  have hr : z ^ 6 + (z ^ 6)⁻¹ = (r : ℂ) := by
    rw [hz6]
    have hJbar : (starRingEnd ℂ) J = p / J := by rw [eq_div_iff hJ0, mul_comm]; exact hnorm
    have hJinv : (J ^ 2 / p)⁻¹ = ((starRingEnd ℂ) J) ^ 2 / p := by
      rw [inv_div, hJbar]; field_simp
    rw [hJinv]
    simp only [r]; push_cast
    rw [← add_div, div_left_inj' hp0, hJc, hJ]
    have hpZ : ((p : ℤ) : ℂ) = (p : ℂ) := by norm_cast
    have hab' : ((a : ℂ) ^ 2 - a * b + b ^ 2) = p := by exact_mod_cast hab
    linear_combination (2 * (b : ℂ) ^ 2) * hω2 - 2 * hab' + 0 * hpZ
  have hnot : ∀ n : ℤ, r ≠ n := by
    intro n hn
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h1 : ((2 * a - b) ^ 2 : ℚ) = (n + 2) * p := by
      simp only [r] at hn; field_simp at hn; linear_combination hn
    have h2 : (2 * a - b) ^ 2 = (n + 2) * (p : ℤ) := by exact_mod_cast h1
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    have hdvd : (p : ℤ) ∣ 2 * a - b := hpi.dvd_of_dvd_pow (n := 2) ⟨n + 2, by rw [h2]; ring⟩
    obtain ⟨k, hk⟩ := hdvd
    have h4 : (2 * a - b) ^ 2 + 3 * b ^ 2 = 4 * (p : ℤ) := by rw [← hab]; ring
    rw [hk] at h4
    have hp7 : (7 : ℤ) ≤ p := by
      have h2' := hp.out.two_le
      have : p ≠ 4 := by intro h; subst h; exact absurd hp.out (by decide)
      have : p ≠ 1 := by omega
      have : 7 ≤ p := by omega
      exact_mod_cast this
    by_cases hk0 : k = 0
    · subst hk0
      have : 3 * b ^ 2 = 4 * (p : ℤ) := by linarith
      generalize b ^ 2 = B at this
      omega
    · have hk1 : 1 ≤ k ^ 2 := by
        have := sq_pos_of_ne_zero hk0
        omega
      have e : ((p : ℤ) * k) ^ 2 = (p : ℤ) ^ 2 * k ^ 2 := by ring
      rw [e] at h4
      have hm : (p : ℤ) ^ 2 * 1 ≤ (p : ℤ) ^ 2 * k ^ 2 := mul_le_mul_of_nonneg_left hk1 (sq_nonneg _)
      nlinarith [sq_nonneg b, hp7]
  intro N hN hzN
  apply not_root_of_trace (z ^ 6) r hr hnot N hN
  rw [← pow_mul, mul_comm, pow_mul, hzN, one_pow]

/-- **4'. したがって ζ = z^{ord χ} は無限位数**。 -/
theorem zeta_cubic_infinite (h3p : p % 3 = 1) (χ : DirichletCharacter ℂ p) (h3 : orderOf χ = 3) :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ orderOf χ) = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn h
  rw [← pow_mul] at h
  exact gauss_cubic_not_root h3p χ h3 _ (Nat.mul_pos (orderOf_pos χ) hn) h

/-- **5. p ≡ 1 (mod 3) なら位数 3 の指標が存在する**。 -/
theorem exists_cubic (h3p : p % 3 = 1) : ∃ χ : DirichletCharacter ℂ p, orderOf χ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Fintype.card (DirichletCharacter ℂ p) = p - 1 := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity,
      Nat.totient_prime hp.out]
  exact exists_prime_orderOf_dvd_card 3 (by rw [hcard]; omega)

end PAG.Part171

#print axioms PAG.Part171.not_root_of_trace
#print axioms PAG.Part171.ω_sq
#print axioms PAG.Part171.conj_ω
#print axioms PAG.Part171.cube_eq_one
#print axioms PAG.Part171.jacobi_InZω
#print axioms PAG.Part171.conj_jacobi
#print axioms PAG.Part171.jacobi_norm
#print axioms PAG.Part171.chi_neg_one
#print axioms PAG.Part171.primitive_of_ne_one
#print axioms PAG.Part171.jacobi_eq_gauss_cube
#print axioms PAG.Part171.gauss_cubic_not_root
#print axioms PAG.Part171.zeta_cubic_infinite
#print axioms PAG.Part171.exists_cubic
