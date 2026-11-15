/-
  Projective Adelic Geometry 2.0, Part 4 — formalization（PAG8.lean）
  非単数ファイバーの消滅と、PAG7 の仮定 hnon の除去。
    1. 安定化部分群の補題: u·s = s を満たす単数 u について F(s) = (χ₁χ₂)(u)·F(s)
    2. F(0) = 0（χ₁χ₂ ≠ 1、任意の N）
    3. 素数べき法 N = p^(n+1) で χ₁χ₂ が原始的なら、すべての非単数 s に
       u ≡ 1 (mod p^n)、u·s = s、(χ₁χ₂)(u) ≠ 1 となる単数 u が存在する
    4. 無条件の定理: χ₁χ₂ が原始的なら τ(χ₁)τ(χ₂) = J(χ₁,χ₂)·τ(χ₁χ₂)
-/
import PAG7

open Complex Finset

namespace PAG.Part8

open PAG.Part7

section General

variable {N : ℕ} [NeZero N]

/-- **安定化部分群の補題**: u·s = s なら F(s) = (χ₁χ₂)(u)·F(s)（x ↦ u x の置換）。 -/
theorem fiber_eq_mul_of_stabilizer (χ₁ χ₂ : MulChar (ZMod N) ℂ) (s : ZMod N) (u : (ZMod N)ˣ)
    (hu : (u : ZMod N) * s = s) :
    fiber χ₁ χ₂ s = (χ₁ * χ₂) u * fiber χ₁ χ₂ s := by
  unfold fiber
  rw [mul_sum]
  conv_lhs => rw [← Equiv.sum_comp (Units.mulLeft u)]
  refine sum_congr rfl fun x _ => ?_
  simp only [Units.mulLeft_apply]
  rw [show s - (u : ZMod N) * x = u * (s - x) by rw [mul_sub, hu], map_mul, map_mul,
    MulChar.coeToFun_mul, Pi.mul_apply]
  ring

/-- u·s = s かつ (χ₁χ₂)(u) ≠ 1 なら F(s) = 0。 -/
theorem fiber_eq_zero_of_stabilizer (χ₁ χ₂ : MulChar (ZMod N) ℂ) (s : ZMod N) (u : (ZMod N)ˣ)
    (hu : (u : ZMod N) * s = s) (hne : (χ₁ * χ₂) u ≠ 1) :
    fiber χ₁ χ₂ s = 0 := by
  have h := fiber_eq_mul_of_stabilizer χ₁ χ₂ s u hu
  have h' : (1 - (χ₁ * χ₂) u) * fiber χ₁ χ₂ s = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1).symm hne
  · exact h1

/-- **F(0) = 0**（χ₁χ₂ ≠ 1、任意の法 N）。u·0 = 0 なので、どの単数でも安定化する。 -/
theorem fiber_zero_of_ne_one (χ₁ χ₂ : MulChar (ZMod N) ℂ) (h : χ₁ * χ₂ ≠ 1) :
    fiber χ₁ χ₂ 0 = 0 := by
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp h
  exact fiber_eq_zero_of_stabilizer χ₁ χ₂ 0 u (mul_zero _) hu

/-- 一般形: すべての非単数 s に安定化単数 u（(χ₁χ₂)(u) ≠ 1）があれば τ₁τ₂ = J τ(χ₁χ₂)。 -/
theorem gauss_mul_gauss_eq_jacobi_mul_of_stab (χ₁ χ₂ : MulChar (ZMod N) ℂ)
    (ψ : AddChar (ZMod N) ℂ)
    (hstab : ∀ s : ZMod N, ¬ IsUnit s → ∃ u : (ZMod N)ˣ, (u : ZMod N) * s = s ∧ (χ₁ * χ₂) u ≠ 1) :
    gaussSum χ₁ ψ * gaussSum χ₂ ψ = J χ₁ χ₂ * gaussSum (χ₁ * χ₂) ψ := by
  refine gauss_mul_gauss_eq_jacobi_mul χ₁ χ₂ ψ fun s hs => ?_
  obtain ⟨u, hu, hne⟩ := hstab s hs
  exact fiber_eq_zero_of_stabilizer χ₁ χ₂ s u hu hne

end General

section PrimePower

variable {p n : ℕ} [hp : Fact p.Prime]

instance neZero_pow : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- 非単数 s ∈ Z/p^(n+1) は p ∣ s.val。 -/
theorem p_dvd_val_of_not_isUnit (s : ZMod (p ^ (n + 1))) (hs : ¬ IsUnit s) : p ∣ s.val := by
  rw [← ZMod.natCast_zmod_val s, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (Nat.succ_pos n)] at hs
  exact (Nat.Prime.dvd_iff_not_coprime hp.out).mpr (fun h => hs (Nat.Coprime.symm h))

/-- u ≡ 1 (mod p^n)（Z/p^n への像が 1）なら、非単数 s について u·s = s。 -/
theorem unit_mul_eq_of_ker (u : (ZMod (p ^ (n + 1)))ˣ)
    (hu : ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ n)) u = 1)
    (s : ZMod (p ^ (n + 1))) (hs : ¬ IsUnit s) : (u : ZMod (p ^ (n + 1))) * s = s := by
  -- (u − 1) の像は 0、すなわち p^n ∣ (u − 1).val
  have hd : p ^ n ∣ p ^ (n + 1) := pow_dvd_pow p (Nat.le_succ n)
  have hc : ZMod.castHom hd (ZMod (p ^ n)) ((u : ZMod (p ^ (n + 1))) - 1) = 0 := by
    rw [map_sub, map_one, ZMod.castHom_apply, ← ZMod.unitsMap_val hd, hu, Units.val_one, sub_self]
  have h1' : ((((u : ZMod (p ^ (n + 1))) - 1).val : ℕ) : ZMod (p ^ n)) = 0 := by
    rw [← hc, ZMod.castHom_apply (h := hd), ZMod.cast_eq_val]
  have h1 : p ^ n ∣ ((u : ZMod (p ^ (n + 1))) - 1).val := (ZMod.natCast_eq_zero_iff _ _).mp h1'
  have h2 := p_dvd_val_of_not_isUnit s hs
  have h3 : p ^ (n + 1) ∣ (((u : ZMod (p ^ (n + 1))) - 1).val * s.val) :=
    Nat.dvd_trans (dvd_of_eq (pow_succ p n)) (Nat.mul_dvd_mul h1 h2)
  have h4 : ((u : ZMod (p ^ (n + 1))) - 1) * s = 0 := by
    rw [← ZMod.natCast_zmod_val ((u : ZMod (p ^ (n + 1))) - 1), ← ZMod.natCast_zmod_val s,
      ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact h3
  rw [sub_mul, one_mul, sub_eq_zero] at h4
  exact h4

/-- 原始的な指標は、核 ker(Z/p^(n+1) → Z/p^n) の上で自明でない。 -/
theorem exists_ker_ne_one_of_primitive (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) :
    ∃ u : (ZMod (p ^ (n + 1)))ˣ,
      ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ n)) u = 1 ∧ χ u ≠ 1 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hft : χ.FactorsThrough (p ^ n) := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ) (pow_dvd_pow p (Nat.le_succ n))]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    ext
    rw [MulChar.coe_toUnitHom, Units.val_one]
    exact hcon u hu
  have hle : χ.conductor ≤ p ^ n := Nat.sInf_le hft
  rw [DirichletCharacter.isPrimitive_def] at hχ
  rw [hχ] at hle
  have : p ^ n < p ^ (n + 1) := Nat.pow_lt_pow_right hp.out.one_lt (Nat.lt_succ_self n)
  omega

/-- **無条件の定理**（素数べき法）: χ₁χ₂ が原始的なら τ(χ₁)τ(χ₂) = J(χ₁,χ₂)·τ(χ₁χ₂)。 -/
theorem gauss_mul_gauss_eq_jacobi_mul_primitive (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hprim : (χ₁ * χ₂).IsPrimitive) (ψ : AddChar (ZMod (p ^ (n + 1))) ℂ) :
    gaussSum χ₁ ψ * gaussSum χ₂ ψ = J χ₁ χ₂ * gaussSum (χ₁ * χ₂) ψ := by
  refine gauss_mul_gauss_eq_jacobi_mul_of_stab χ₁ χ₂ ψ fun s hs => ?_
  obtain ⟨u, hker, hne⟩ := exists_ker_ne_one_of_primitive (χ₁ * χ₂) hprim
  exact ⟨u, unit_mul_eq_of_ker u hker s hs, hne⟩

/-- 系: χ² が原始的なら τ(χ)² = J(χ,χ)·τ(χ²)。 -/
theorem gauss_sq_primitive (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hprim : (χ * χ).IsPrimitive)
    (ψ : AddChar (ZMod (p ^ (n + 1))) ℂ) :
    gaussSum χ ψ ^ 2 = J χ χ * gaussSum (χ * χ) ψ := by
  rw [sq]; exact gauss_mul_gauss_eq_jacobi_mul_primitive χ χ hprim ψ

end PrimePower

end PAG.Part8

#print axioms PAG.Part8.fiber_eq_mul_of_stabilizer
#print axioms PAG.Part8.fiber_eq_zero_of_stabilizer
#print axioms PAG.Part8.fiber_zero_of_ne_one
#print axioms PAG.Part8.gauss_mul_gauss_eq_jacobi_mul_of_stab
#print axioms PAG.Part8.p_dvd_val_of_not_isUnit
#print axioms PAG.Part8.unit_mul_eq_of_ker
#print axioms PAG.Part8.exists_ker_ne_one_of_primitive
#print axioms PAG.Part8.gauss_mul_gauss_eq_jacobi_mul_primitive
#print axioms PAG.Part8.gauss_sq_primitive
