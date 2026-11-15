/-
  PAG 2.0 Part 148（2026-10-22）— 法 4, 8 のガウス和の符号の決定
  1. 法 4 の原始指標: τ = 2i、z = i
  2. 法 8 の原始指標: χ(5) = −1、τ = 2√2（χ(−1) = 1）、τ = 2√2 i（χ(−1) = −1）
-/
import PAG151

namespace PAG.Part152

open ZMod Finset Complex Real

/-! ## 1. 法 4 -/

theorem e4_one : stdAddChar (1 : ZMod 4) = I := by
  have h := ZMod.stdAddChar_coe (N := 4) 1
  push_cast at h
  rw [h, show 2 * (π : ℂ) * I * 1 / 4 = (π / 2 : ℝ) * I by push_cast; ring]
  push_cast
  exact exp_pi_div_two_mul_I

theorem e4_pow (k : ℕ) : stdAddChar ((k : ZMod 4)) = I ^ k := by
  rw [← nsmul_one, AddChar.map_nsmul_eq_pow, e4_one]

/-- **1. 法 4: τ = 2i**。 -/
theorem gauss_mod4 (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) : gaussSum χ stdAddChar = 2 * I := by
  have : Fact (1 < 4) := ⟨by norm_num⟩
  have hm1 := PAG.Part151.neg_one_mod4 χ hχ
  have h3 : χ 3 = -1 := by rw [show (3 : ZMod 4) = -1 from rfl]; exact hm1
  have h2 : χ 2 = 0 := MulChar.map_nonunit χ (by
    rw [show (2 : ZMod 4) = ((2 : ℕ) : ZMod 4) from rfl, ZMod.isUnit_iff_coprime]; decide)
  unfold gaussSum
  rw [show (univ : Finset (ZMod 4)) = {0, 1, 2, 3} from by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [MulChar.map_zero, MulChar.map_one, h2, h3, e4_one,
    show (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) from rfl, e4_pow]
  ring_nf
  have : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  rw [this]; ring

/-- 系: z = i。 -/
theorem phase_mod4_eq (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar / ((Real.sqrt (4 : ℕ) : ℝ) : ℂ) = I := by
  rw [gauss_mod4 χ hχ, show Real.sqrt ((4 : ℕ) : ℝ) = 2 by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  push_cast; ring

/-! ## 2. 法 8 -/

theorem e8_one : stdAddChar (1 : ZMod 8) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + I) := by
  have h := ZMod.stdAddChar_coe (N := 8) 1
  push_cast at h
  rw [h, show 2 * (π : ℂ) * I * 1 / 8 = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

theorem e8_pow (k : ℕ) : stdAddChar ((k : ZMod 8)) = stdAddChar (1 : ZMod 8) ^ k := by
  rw [← nsmul_one, AddChar.map_nsmul_eq_pow]

theorem e8_sq : stdAddChar (1 : ZMod 8) ^ 2 = I := by
  rw [e8_one, mul_pow, ← ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]
  have : (1 + I) ^ 2 = 2 * I := by ring_nf; rw [I_sq]; ring
  rw [this]; push_cast; ring

/-- 法 8 の原始指標は χ(5) = −1。 -/
theorem five_mod8 (χ : DirichletCharacter ℂ 8) (hχ : χ.IsPrimitive) : χ 5 = -1 := by
  have : Fact (1 < 8) := ⟨by norm_num⟩
  have hs : χ 5 ^ 2 = 1 := by
    rw [← map_pow, show (5 : ZMod 8) ^ 2 = 1 from by decide, map_one]
  by_contra hn
  have h1 : χ 5 = 1 := by
    have : (χ 5 - 1) * (χ 5 + 1) = 0 := by ring_nf; rw [hs]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (eq_neg_of_add_eq_zero_left h) hn
  have hδ : ∀ y : ZMod (2 ^ 3), (χ : DirichletCharacter ℂ (2 ^ 3)) (1 + ((2 : ℕ) : ZMod (2 ^ 3)) ^ 2 * y)
      = stdAddChar (((2 : ℕ) : ZMod (2 ^ 3)) ^ 2 * 0 * y) := by
    intro y
    rw [mul_zero, zero_mul, AddChar.map_zero_eq_one]
    have hy : (1 + ((2 : ℕ) : ZMod 8) ^ 2 * y = 1) ∨ (1 + ((2 : ℕ) : ZMod 8) ^ 2 * y = 5) := by
      revert y; decide
    rcases hy with hy | hy
    · exact (congrArg χ hy).trans (map_one χ)
    · exact (congrArg χ hy).trans h1
  have := (PAG.Part142.primitive_iff_freq (p := 2) (c := 3) (k := 2) (by norm_num) (by norm_num)
    (χ : DirichletCharacter ℂ (2 ^ 3)) 0 hδ).mp hχ
  exact not_isUnit_zero this

/-- **2. 法 8: τ = 2√2（χ(−1) = 1）、τ = 2√2 i（χ(−1) = −1）**。 -/
theorem gauss_mod8 (χ : DirichletCharacter ℂ 8) (hχ : χ.IsPrimitive) :
    (χ (-1) = 1 → gaussSum χ stdAddChar = 2 * ((Real.sqrt 2 : ℝ) : ℂ)) ∧
    (χ (-1) = -1 → gaussSum χ stdAddChar = 2 * ((Real.sqrt 2 : ℝ) : ℂ) * I) := by
  have : Fact (1 < 8) := ⟨by norm_num⟩
  have h5 := five_mod8 χ hχ
  have h7 : χ 7 = χ 3 * χ 5 := by rw [← map_mul]; rfl
  have hm : χ (-1) = χ 7 := rfl
  have hnu : ∀ n : ℕ, n ∈ ({0, 2, 4, 6} : Finset ℕ) → χ (n : ZMod 8) = 0 := by
    intro n hn
    apply MulChar.map_nonunit
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rw [ZMod.isUnit_iff_coprime]
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  set τ := stdAddChar (1 : ZMod 8)
  have hτ2 := e8_sq
  have hsum : gaussSum χ stdAddChar = 2 * τ + 2 * χ 3 * τ ^ 3 := by
    unfold gaussSum
    rw [show (univ : Finset (ZMod 8)) = {0, 1, 2, 3, 4, 5, 6, 7} from by decide]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    rw [show (0 : ZMod 8) = ((0 : ℕ) : ZMod 8) from rfl, show (2 : ZMod 8) = ((2 : ℕ) : ZMod 8) from rfl,
      show (4 : ZMod 8) = ((4 : ℕ) : ZMod 8) from rfl, show (6 : ZMod 8) = ((6 : ℕ) : ZMod 8) from rfl,
      hnu 0 (by simp), hnu 2 (by simp), hnu 4 (by simp), hnu 6 (by simp)]
    rw [show ((0 : ℕ) : ZMod 8) = 0 from rfl, show ((2 : ℕ) : ZMod 8) = 2 from rfl,
      show ((4 : ℕ) : ZMod 8) = 4 from rfl, show ((6 : ℕ) : ZMod 8) = 6 from rfl]
    rw [show (3 : ZMod 8) = ((3 : ℕ) : ZMod 8) from rfl, show (5 : ZMod 8) = ((5 : ℕ) : ZMod 8) from rfl,
      show (7 : ZMod 8) = ((7 : ℕ) : ZMod 8) from rfl, e8_pow 3, e8_pow 5, e8_pow 7]
    rw [show ((3 : ℕ) : ZMod 8) = 3 from rfl, show ((5 : ℕ) : ZMod 8) = 5 from rfl,
      show ((7 : ℕ) : ZMod 8) = 7 from rfl, h7, h5, MulChar.map_one]
    have h4 : τ ^ 4 = -1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hτ2, I_sq]
    linear_combination (- τ - χ 3 * τ ^ 3) * h4
  have hτ3 : τ ^ 3 = I * τ := by rw [pow_succ, hτ2, mul_comm]
  have hτv : τ = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + I) := e8_one
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  constructor
  · intro h1
    have h3 : χ 3 = -1 := by
      rw [hm, h7, h5] at h1; linear_combination -h1
    rw [hsum, h3, hτ3, hτv]
    push_cast
    linear_combination (-(Real.sqrt 2 : ℂ)) * I_sq
  · intro h1
    have h3 : χ 3 = 1 := by
      rw [hm, h7, h5] at h1; linear_combination -h1
    rw [hsum, h3, hτ3, hτv]
    push_cast
    linear_combination (Real.sqrt 2 : ℂ) * I_sq

end PAG.Part152

#print axioms PAG.Part152.gauss_mod4
#print axioms PAG.Part152.phase_mod4_eq
#print axioms PAG.Part152.e8_one
#print axioms PAG.Part152.e8_sq
#print axioms PAG.Part152.five_mod8
#print axioms PAG.Part152.gauss_mod8
