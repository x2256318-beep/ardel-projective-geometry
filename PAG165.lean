/-
  PAG 2.0 Part 161（2026-10-22）— ガウスの符号決定（その 1）：正弦の積 Π
  ζ = exp(2πi/p)、m = (p−1)/2、Π = ∏_{a=1}^{m} (ζ^a − ζ^{−a})
  1. prod_X_sub: ∏_{b<n} (X − ω^b) = X^n − 1（ω は 1 の原始 n 乗根）
  2. prod_one_sub: ∏_{b=1}^{n−1} (1 − ω^b) = n
  3. Pi_sq: Π² = (−1)^m p
  4. Pi_eq: Π = i^m √p（正弦の正値性から）
-/
import PAG164

namespace PAG.Part165

open Complex Finset Polynomial Real

/-- **1. ∏_{b<n} (X − ω^b) = X^n − 1**。 -/
theorem prod_X_sub (n : ℕ) (hn : 0 < n) (ω : ℂ) (hω : IsPrimitiveRoot ω n) :
    ∏ b ∈ range n, (X - C (ω ^ b)) = (X ^ n - 1 : ℂ[X]) := by
  classical
  rw [X_pow_sub_one_eq_prod hn hω]
  have hinj : Set.InjOn (fun b => ω ^ b) (range n : Set ℕ) := by
    intro i hi j hj h
    exact hω.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  have himg : (range n).image (fun b => ω ^ b) = nthRootsFinset n (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx
      rw [mem_nthRootsFinset hn, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    · rw [hω.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [← himg, Finset.prod_image hinj]

/-- **2. ∏_{b=1}^{n−1} (1 − ω^b) = n**。 -/
theorem prod_one_sub (n : ℕ) (hn : 0 < n) (ω : ℂ) (hω : IsPrimitiveRoot ω n) :
    ∏ b ∈ Ico 1 n, (1 - ω ^ b) = n := by
  have h := prod_X_sub n hn ω hω
  rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot hn, pow_zero, ← geom_sum_mul,
    show (X - C (1 : ℂ)) = (X - 1 : ℂ[X]) by simp, mul_comm] at h
  have h' := mul_left_cancel₀ (X_sub_C_ne_zero (1 : ℂ)) (by simpa using h)
  have := congrArg (eval 1) h'
  simp only [eval_prod, eval_sub, eval_X, eval_C, eval_pow, eval_geom_sum, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one] at this
  exact this

variable (p : ℕ) [hp : Fact p.Prime]

/-- ζ = exp(2πi/p)。 -/
noncomputable def zp : ℂ := Complex.exp (2 * π * I / p)

theorem zp_prim : IsPrimitiveRoot (zp p) p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero

omit hp in
theorem zp_ne_zero : zp p ≠ 0 := Complex.exp_ne_zero _

/-- g(b) = ζ^b − ζ^{−b}。 -/
noncomputable def gb (b : ℕ) : ℂ := zp p ^ b - (zp p ^ b)⁻¹

/-- Π = ∏_{a=1}^{m} (ζ^a − ζ^{−a})。 -/
noncomputable def Pi (m : ℕ) : ℂ := ∏ a ∈ Ico 1 (m + 1), gb p a

theorem gb_reflect (a : ℕ) (ha : a ≤ p) : gb p (p - a) = - gb p a := by
  have hpow : zp p ^ (p - a) = (zp p ^ a)⁻¹ := by
    have h1 : zp p ^ (p - a) * zp p ^ a = 1 := by rw [← pow_add, Nat.sub_add_cancel ha, (zp_prim p).pow_eq_one]
    exact eq_inv_of_mul_eq_one_left h1
  unfold gb; rw [hpow, inv_inv]; ring

/-- **3. ∏_{b=1}^{p−1} (ζ^b − ζ^{−b}) = p**（p 奇素数）。 -/
theorem prod_gb (hp2 : p ≠ 2) : ∏ b ∈ Ico 1 p, gb p b = p := by
  have hz := zp_ne_zero p
  have e1 : ∀ b, gb p b = ((zp p ^ b)⁻¹) * -(1 - (zp p ^ 2) ^ b) := by
    intro b; unfold gb
    have : zp p ^ b ≠ 0 := pow_ne_zero _ hz
    field_simp; ring
  rw [Finset.prod_congr rfl (fun b _ => e1 b), Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_neg, prod_one_sub p hp.out.pos _
      ((zp_prim p).pow_of_coprime 2 ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2).symm)]
  have hsum : ∑ b ∈ Ico 1 p, b = p * ((p - 1) / 2) := by
    have h := Finset.sum_range_id_mul_two p
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.out.pos] at h
    have hodd := hp.out.odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := hodd
    subst hk
    simp only [zero_add] at h
    rw [show (2 * k + 1 - 1) / 2 = k by omega]
    have : (∑ b ∈ Ico 1 (2 * k + 1), b) * 2 = (2 * k + 1) * k * 2 := by rw [h]; rw [show 2 * k + 1 - 1 = 2 * k by omega]; ring
    omega
  have hcard : (Ico 1 p).card = p - 1 := by simp
  have hev : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2; exact ⟨k, by omega⟩
  rw [hsum, pow_mul, (zp_prim p).pow_eq_one, one_pow, inv_one, one_mul, hcard, hev.neg_one_pow, one_mul]

/-- **3'. Π² = (−1)^m p**（p = 2m + 1）。 -/
theorem Pi_sq (m : ℕ) (hpm : p = 2 * m + 1) : Pi p m ^ 2 = (-1) ^ m * p := by
  have hp2 : p ≠ 2 := by omega
  have hsplit : ∏ b ∈ Ico 1 p, gb p b = (∏ a ∈ Ico 1 (m + 1), gb p a) * ∏ a ∈ Ico 1 (m + 1), gb p (p - a) := by
    rw [← Finset.prod_Ico_consecutive _ (show 1 ≤ m + 1 by omega) (show m + 1 ≤ p by omega)]
    congr 1
    rw [Finset.prod_Ico_reflect (gb p) 1 (show m + 1 ≤ p + 1 by omega),
      show p + 1 - (m + 1) = m + 1 by omega, show p + 1 - 1 = p by omega]
  have hrefl : ∏ a ∈ Ico 1 (m + 1), gb p (p - a) = (-1) ^ m * ∏ a ∈ Ico 1 (m + 1), gb p a := by
    rw [Finset.prod_congr rfl (fun a ha => gb_reflect p a (by simp at ha; omega)), Finset.prod_neg]
    simp
  have h := prod_gb p hp2
  rw [hsplit, hrefl] at h
  unfold Pi
  have hm1 : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  calc (∏ a ∈ Ico 1 (m + 1), gb p a) ^ 2
      = (-1) ^ m * ((∏ a ∈ Ico 1 (m + 1), gb p a) * ((-1) ^ m * ∏ a ∈ Ico 1 (m + 1), gb p a)) := by
        linear_combination (-(∏ a ∈ Ico 1 (m + 1), gb p a) ^ 2) * hm1
    _ = (-1) ^ m * p := by rw [h]

omit hp in
/-- g(a) = 2i sin(2πa/p)。 -/
theorem gb_sin (b : ℕ) : gb p b = 2 * I * (Real.sin (2 * π * b / p) : ℂ) := by
  unfold gb zp
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
  have e : (b : ℂ) * (2 * π * I / p) = ((2 * π * b / p : ℝ) : ℂ) * I := by push_cast; ring
  rw [e, show -(((2 * π * b / p : ℝ) : ℂ) * I) = ((-(2 * π * b / p) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast; ring

/-- **4. Π = i^m √p**。 -/
theorem Pi_eq (m : ℕ) (hpm : p = 2 * m + 1) : Pi p m = I ^ m * (Real.sqrt p : ℂ) := by
  set R : ℝ := 2 ^ m * ∏ a ∈ Ico 1 (m + 1), Real.sin (2 * π * a / p)
  have hpos : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hR : 0 < R := by
    apply mul_pos (by positivity)
    apply Finset.prod_pos
    intro a ha
    simp only [Finset.mem_Ico] at ha
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
      positivity
    · rw [div_lt_iff₀ hpos]
      have : (2 : ℝ) * a < p := by exact_mod_cast (show 2 * a < p by omega)
      nlinarith [Real.pi_pos]
  have hPi : Pi p m = I ^ m * (R : ℂ) := by
    unfold Pi
    rw [Finset.prod_congr rfl (fun b _ => gb_sin p b), Finset.prod_mul_distrib, Finset.prod_const]
    simp only [R, Nat.card_Ico, Nat.add_sub_cancel]
    push_cast
    rw [mul_pow]; ring
  have hsq := Pi_sq p m hpm
  rw [hPi, mul_pow, ← pow_mul, mul_comm m 2, pow_mul, I_sq] at hsq
  have hR2 : (R : ℂ) ^ 2 = p := by
    have h1 : ((-1 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact mul_left_cancel₀ h1 hsq
  have hR2' : R ^ 2 = p := by exact_mod_cast hR2
  have hRs : R = Real.sqrt p := by rw [← hR2', Real.sqrt_sq hR.le]
  rw [hPi, hRs]

end PAG.Part165

#print axioms PAG.Part165.prod_X_sub
#print axioms PAG.Part165.prod_one_sub
#print axioms PAG.Part165.gb_reflect
#print axioms PAG.Part165.prod_gb
#print axioms PAG.Part165.Pi_sq
#print axioms PAG.Part165.gb_sin
#print axioms PAG.Part165.Pi_eq
