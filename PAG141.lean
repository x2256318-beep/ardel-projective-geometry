/-
  PAG 2.0 Part 137（2026-10-22）— 野性的なひねりの一般形（偶奇を問わない）
  P = p^k（k < c ≤ 2k）、S_P(χ) = {u : ∀ y, χ(1 + P y) e(P u y) = 1}
  1. どの ψ にも ψ(1 + P y) = e(P δ y) となる δ がある
  2. u ∈ S_P(χψ) ↔ u + δ ∈ S_P(χ)
  3. 平行移動の公式: τ(χψ) = Σ_{v ∈ S_P(χ)} (χψ)(v − δ) e(v − δ)
  4. u₀ ∈ S_P(χ) で u₀ − δ が単元でなければ τ(χψ) = 0
  5. 系: χψ が原始なら u₀ − δ は単元（δ ≢ u₀ mod p）
  6. 原始性の判定: χψ 原始 ↔ u₀ − δ 単元
-/
import PAG140

namespace PAG.Part141

open ZMod Finset PAG.Part120

variable {p : ℕ} [hp : Fact p.Prime]

section Gen

variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)

include hkc h2k in
/-- **1. δ の存在**。 -/
theorem exists_delta_gen (ψ : DirichletCharacter ℂ (p ^ c)) :
    ∃ δ : ZMod (p ^ c), ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y) := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set P := (p : ZMod (p ^ c)) ^ k
  have hP : P * P = 0 := by
    simp only [P]; rw [← pow_add]
    exact pow_eq_zero_of_le (show c ≤ k + k by omega) (by rw [← Nat.cast_pow, ZMod.natCast_self])
  set f : ZMod (p ^ c) → ℂ := fun y => ψ (1 + P * y)
  have hadd : ∀ y z, f (y + z) = f y * f z := by
    intro y z; simp only [f]; rw [← map_mul]; congr 1; linear_combination (-(y * z)) * hP
  have hnat : ∀ n : ℕ, f n = f 1 ^ n := by
    intro n; induction n with
    | zero => simp [f]
    | succ n ih => rw [Nat.cast_succ, hadd, ih, pow_succ]
  have hf1 : f 1 ^ (p ^ c) = 1 := by
    rw [← hnat, ZMod.natCast_self]; simp [f]
  have hprim := PAG.Part140.stdAddChar_one_primitive (p := p) c
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hf1
  have hsplit : p ^ (c - k) * p ^ k = p ^ c := by rw [← pow_add]; congr 1; omega
  have hf2 : f 1 ^ (p ^ (c - k)) = 1 := by
    rw [← hnat]; simp only [f]
    rw [show P * ((p ^ (c - k) : ℕ) : ZMod (p ^ c)) = 0 by
      simp only [P]; push_cast; rw [← pow_add, show k + (c - k) = c by omega, ← Nat.cast_pow, ZMod.natCast_self],
      add_zero, map_one]
  rw [← hj, ← pow_mul] at hf2
  have h3 := (hprim.pow_eq_one_iff_dvd _).mp hf2
  rw [← hsplit, mul_comm j] at h3
  obtain ⟨d, hd⟩ := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos (c - k)) h3
  refine ⟨d, fun y => ?_⟩
  change f y = _
  rw [← ZMod.natCast_zmod_val y, hnat, ← hj, ← pow_mul, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hd]
  congr 1
  simp only [P]; push_cast; ring

/-- **2. 停留集合の平行移動**。 -/
theorem mem_SP_twist (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hψ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y)) (u : ZMod (p ^ c)) :
    (∀ y, phiP (χ * ψ) ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * u * y) = 1) ↔
      (∀ y, phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * (u + δ) * y) = 1) := by
  have key : ∀ y, phiP (χ * ψ) ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * u * y)
      = phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * (u + δ) * y) := by
    intro y
    simp only [phiP, MulChar.mul_apply, hψ]
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2; ring
  simp only [key]

include h2k in
/-- **3. 平行移動の公式**。 -/
theorem gauss_twist_shift (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hψ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y)) :
    gaussSum (χ * ψ) stdAddChar = ∑ v ∈ univ.filter (fun v : ZMod (p ^ c) =>
      ∀ y, phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * v * y) = 1),
        (χ * ψ) (v - δ) * stdAddChar (v - δ) := by
  classical
  have hP : (p : ZMod (p ^ c)) ^ k * (p : ZMod (p ^ c)) ^ k = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (show c ≤ k + k by omega) (by rw [← Nat.cast_pow, ZMod.natCast_self])
  rw [gauss_eq_sum_SP (χ * ψ) _ hP]
  apply Finset.sum_nbij' (fun u => u + δ) (fun v => v - δ)
  · intro u hu
    exact Finset.mem_filter.mpr ⟨mem_univ _, (mem_SP_twist χ ψ δ hψ u).mp (Finset.mem_filter.mp hu).2⟩
  · intro v hv
    refine Finset.mem_filter.mpr ⟨mem_univ _, (mem_SP_twist χ ψ δ hψ (v - δ)).mpr ?_⟩
    rw [sub_add_cancel]; exact (Finset.mem_filter.mp hv).2
  · intro u _; simp
  · intro v _; simp
  · intro u _; simp

include hkc h2k in
/-- **4. 停留点が非単元に落ちれば τ(χψ) = 0**。 -/
theorem gauss_twist_zero_gen (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hψ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y))
    (u₀ : ZMod (p ^ c)) (hu₀' : ¬ IsUnit (u₀ - δ))
    (hS₀ : ∀ y, phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * u₀ * y) = 1) :
    gaussSum (χ * ψ) stdAddChar = 0 := by
  classical
  have hpc : p ∣ p ^ c := dvd_pow_self p (by omega)
  rw [gauss_twist_shift h2k χ ψ δ hψ]
  apply Finset.sum_eq_zero
  intro v hv
  have hS := (Finset.mem_filter.mp hv).2
  have hPv : (p : ZMod (p ^ c)) ^ k * v = (p : ZMod (p ^ c)) ^ k * u₀ := by
    have h1 := hS 1; have h2 := hS₀ 1
    rw [mul_one] at h1 h2
    have hφ : phiP χ ((p : ZMod (p ^ c)) ^ k) 1 ≠ 0 := by intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
    exact ZMod.injective_stdAddChar (mul_left_cancel₀ hφ (h1.trans h2.symm))
  have hcast := PAG.Part139.cast_eq_of_P (p := p) hkc v u₀ hPv
  have hnu : ¬ IsUnit (v - δ) := by
    rw [PAG.Part140.isUnit_iff_cast_ne_zero c (by omega)]
    rw [PAG.Part140.isUnit_iff_cast_ne_zero c (by omega), ZMod.cast_sub hpc, not_not] at hu₀'
    rw [ZMod.cast_sub hpc, hcast]
    intro h; exact h hu₀'
  rw [MulChar.map_nonunit _ hnu, zero_mul]

include hkc h2k in
/-- **5. 系: χψ が原始なら u₀ − δ は単元**。 -/
theorem unit_of_primitive (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hψ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y))
    (hχψ : (χ * ψ).IsPrimitive) (u₀ : ZMod (p ^ c))
    (hS₀ : ∀ y, phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * u₀ * y) = 1) :
    IsUnit (u₀ - δ) := by
  by_contra h
  exact PAG.Part16.gaussSum_ne_zero hχψ (gauss_twist_zero_gen hkc h2k χ ψ δ hψ u₀ h hS₀)

include hkc h2k in
/-- **6. 原始性の判定**: χψ 原始 ↔ u₀ − δ 単元。 -/
theorem primitive_iff_unit (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hψ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y))
    (u₀ : ZMod (p ^ c))
    (hS₀ : ∀ y, phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * u₀ * y) = 1) :
    (χ * ψ).IsPrimitive ↔ IsUnit (u₀ - δ) := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  refine ⟨fun h => unit_of_primitive hkc h2k χ ψ δ hψ h u₀ hS₀, fun hu => ?_⟩
  by_contra hnp
  have hdvd : p ^ (c - 1) ∣ p ^ c := pow_dvd_pow p (by omega)
  -- 導手は p^{c−1} を割る
  have hcond : (χ * ψ).conductor ∣ p ^ (c - 1) := by
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp.out).mp (DirichletCharacter.conductor_dvd_level (χ * ψ))
    have hjne : j ≠ c := fun he => hnp (by rw [DirichletCharacter.isPrimitive_def, hjc, he])
    rw [hjc]; exact pow_dvd_pow p (by omega)
  have hft := ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd (χ * ψ) hdvd).mpr hcond)
  have hker := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd).mp hft
  -- u₁ = u₀ − δ ∈ S_P(χψ)
  have hS1 := (mem_SP_twist χ ψ δ hψ (u₀ - δ)).mpr (by rw [sub_add_cancel]; exact hS₀)
  set w : ZMod (p ^ c) := 1 + (p : ZMod (p ^ c)) ^ (c - 1)
  have hw2 : (p : ZMod (p ^ c)) ^ (c - 1) * (p : ZMod (p ^ c)) ^ (c - 1) = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (show c ≤ c - 1 + (c - 1) by omega) (by rw [← Nat.cast_pow, ZMod.natCast_self])
  have hwu : IsUnit w := isUnit_iff_exists_inv.mpr ⟨1 - (p : ZMod (p ^ c)) ^ (c - 1), by
    simp only [w]; linear_combination (-1 : ZMod (p ^ c)) * hw2⟩
  have hw1 : (χ * ψ) w = 1 := by
    have hk : ZMod.unitsMap hdvd hwu.unit = 1 := by
      apply Units.ext
      rw [ZMod.unitsMap_val, IsUnit.unit_spec, Units.val_one]
      simp only [w]
      rw [ZMod.cast_add hdvd, ZMod.cast_one hdvd, ZMod.cast_pow hdvd, ZMod.cast_natCast hdvd,
        ← Nat.cast_pow, ZMod.natCast_self, add_zero]
    have := hker hk
    rw [MonoidHom.mem_ker] at this
    have e := congrArg Units.val this
    rw [MulChar.coe_toUnitHom, IsUnit.unit_spec, Units.val_one] at e
    exact e
  -- y = p^{c−1−k} で P y = p^{c−1}
  have hy := hS1 ((p : ZMod (p ^ c)) ^ (c - 1 - k))
  have hPy : (p : ZMod (p ^ c)) ^ k * (p : ZMod (p ^ c)) ^ (c - 1 - k) = (p : ZMod (p ^ c)) ^ (c - 1) := by
    rw [← pow_add]; congr 1; omega
  have hphi1 : phiP (χ * ψ) ((p : ZMod (p ^ c)) ^ k) ((p : ZMod (p ^ c)) ^ (c - 1 - k)) = 1 := by
    simp only [phiP]; rw [hPy]; exact hw1
  rw [hphi1, one_mul, mul_assoc, mul_comm (u₀ - δ), ← mul_assoc, hPy] at hy
  have h0 : (p : ZMod (p ^ c)) ^ (c - 1) * (u₀ - δ) = (p : ZMod (p ^ c)) ^ (c - 1) * 0 := by
    rw [mul_zero]
    exact ZMod.injective_stdAddChar (hy.trans (AddChar.map_zero_eq_one _).symm)
  have hc0 := PAG.Part139.cast_eq_of_P (p := p) (k := c - 1) (by omega) (u₀ - δ) 0 h0
  rw [ZMod.cast_zero] at hc0
  exact (PAG.Part140.isUnit_iff_cast_ne_zero c (by omega) (u₀ - δ)).mp hu hc0

end Gen

end PAG.Part141

#print axioms PAG.Part141.exists_delta_gen
#print axioms PAG.Part141.mem_SP_twist
#print axioms PAG.Part141.gauss_twist_shift
#print axioms PAG.Part141.gauss_twist_zero_gen
#print axioms PAG.Part141.unit_of_primitive
#print axioms PAG.Part141.primitive_iff_unit
