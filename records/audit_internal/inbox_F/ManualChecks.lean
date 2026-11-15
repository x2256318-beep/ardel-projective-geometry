import PAG260
import PAG3
import PAG6
/-! 内部照合の監査（2026-11-14）：照合者が A・B と判定し、直接の当てはめでは確かめられなかった組を、
前の鎖の宣言から短く示して確かめる。鎖の外のファイルで、鎖の定理は変えない。 -/
open Complex DirichletCharacter

namespace PAG.Audit257

section
variable {N : ℕ} [NeZero N]

/-- A（定義）：Part 252 の `casKer` は PAG3 の `casK` と同じ値。 -/
theorem casKer_eq_casK (t : ZMod N) : PAG.Part256.casKer t = PAG.Part3.casK t := by
  have h1 := PAG.Part3.casK_even_part t
  have h2 := PAG.Part3.casK_odd_part t
  rw [PAG.Part256.casKer_eq]
  linear_combination (-(1:ℂ)/2) * h1 + (-(1:ℂ)/2) * h2

/-- B（定義）：Part 252 の `rootNum` は Part 192 の `zN` を Part 194 の `gs` で割ったもの。 -/
theorem rootNum_eq_zN_div_gs (χ : DirichletCharacter ℂ N) :
    PAG.Part256.rootNum χ = PAG.Part196.zN χ / PAG.Part198.gs χ := by
  unfold PAG.Part256.rootNum PAG.Part196.zN PAG.Part198.gs
  rw [div_div, mul_comm]
  rfl

/-- B：Part 252 の `inv_apply_units_inv` は PAG3 の `apply_inv_eq_inv_apply` から 1 行。 -/
theorem inv_apply_units_inv_of_PAG3 (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ⁻¹ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u := by
  rw [← ZMod.inv_coe_unit, PAG.Part3.apply_inv_eq_inv_apply χ⁻¹ u.isUnit, inv_inv]

/-- B：Part 252 の `sum_mul_stdAddChar_neg` は PAG3 の `sum_neg_twist`（x = 1）。 -/
theorem sum_mul_stdAddChar_neg_of_PAG3 (χ : DirichletCharacter ℂ N) :
    ∑ x : ZMod N, χ x * ZMod.stdAddChar (-x) = χ (-1) * gaussSum χ ZMod.stdAddChar := by
  have h := PAG.Part3.sum_neg_twist χ 1
  simp only [one_mul] at h
  unfold gaussSum
  simpa only [mul_comm (χ _)] using h

/-- A（定義）：Part 253 の `charU` は基本ファイルの `PAG.charFun` に `toUnitHom` を通したもの。 -/
theorem charU_eq_charFun (χ : DirichletCharacter ℂ N) :
    PAG.Part257.charU χ = PAG.charFun (MulChar.toUnitHom χ) := by
  funext u
  simp [PAG.Part257.charU, PAG.charFun]

/-- A（定義）：Part 253 の `ip` は Part 249 の `ipG` の G = (ZMod N)ˣ の場合（範囲の中）。 -/
theorem ip_eq_ipG (f g : (ZMod N)ˣ → ℂ) : PAG.Part257.ip f g = PAG.Part253.ipG f g := rfl

/-- B：Part 253 の `not_isPrimitive_one_of_two_le` は Part 191 の `ne_one_of_isPrimitive` の対偶。 -/
theorem not_isPrimitive_one_of_two_le_of_PAG195 (hN : 2 ≤ N) :
    ¬(1 : DirichletCharacter ℂ N).IsPrimitive :=
  fun h => PAG.Part195.ne_one_of_isPrimitive hN 1 h rfl

/-- B：Part 253 の `charU_one_mem_Vimprim` も同じ定理から 1 行。 -/
theorem charU_one_mem_Vimprim_of_PAG195 (hN : 2 ≤ N) :
    PAG.Part257.charU (1 : DirichletCharacter ℂ N) ∈ PAG.Part257.Vimprim N :=
  Submodule.subset_span ⟨⟨1, fun h => PAG.Part195.ne_one_of_isPrimitive hN 1 h rfl⟩, rfl⟩

/-- B：Part 254 の `gaussSum_inv` は Part 5 の `conj_gaussSum` と `chi_neg_one_sq` から 1 行。 -/
theorem gaussSum_inv_of_PAG9 (χ : DirichletCharacter ℂ N) :
    gaussSum χ⁻¹ (ZMod.stdAddChar (N := N)) = χ (-1) * (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) := by
  rw [PAG.Part9.conj_gaussSum, ← mul_assoc, PAG.Part9.chi_neg_one_sq, one_mul]

end

/-- B：Part 253 の `not_isPrimitive_one_prime` は Part 28 の `prim_level_p_iff` から 1 行。 -/
theorem not_isPrimitive_one_prime_of_PAG32 (p : ℕ) [Fact p.Prime] :
    ¬(1 : DirichletCharacter ℂ p).IsPrimitive :=
  fun h => (PAG.Part32.prim_level_p_iff 1).mp h rfl

/-- B：Part 253 の `Vprim_two` は Part 26 の `no_prim_mod_two` から（張る集合が空）。 -/
theorem Vprim_two_of_PAG30 : PAG.Part257.Vprim 2 = ⊥ := by
  rw [PAG.Part257.Vprim, Submodule.span_eq_bot]
  rintro _ ⟨χ, rfl⟩
  exact absurd χ.2 (PAG.Part30.no_prim_mod_two χ.1)

/-- A（定義）：Part 256 の `crtMap` は Part 189 の `param` と同じ式。 -/
theorem crtMap_eq_param {M N : ℕ} [NeZero M] [NeZero N] (x : ZMod M × ZMod N) :
    PAG.Part260.crtMap M N x = PAG.Part193.param M N x := rfl

/-- A（値）：Part 256 の `crossSign` は Part 194 の `rs` と同じ値（χ(−1) = ±1 による）。 -/
theorem crossSign_eq_rs {M N : ℕ} [NeZero M] [NeZero N]
    (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part260.crossSign χ₁ χ₂ = PAG.Part198.rs χ₁ χ₂ := by
  unfold PAG.Part260.crossSign PAG.Part198.rs
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  rcases χ₁.even_or_odd with h1 | h1 <;> rcases χ₂.even_or_odd with h2 | h2 <;>
    simp only [DirichletCharacter.Even, DirichletCharacter.Odd] at h1 h2 <;>
    simp [DirichletCharacter.Odd, h1, h2, hne, hne.symm]

/-- B：Part 256 の `prodChar_neg_one` は Part 200 の `changeLevel_neg_one` を 2 回使うだけ。 -/
theorem prodChar_neg_one_of_PAG204 {M N : ℕ} [NeZero M] [NeZero N]
    (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part260.prodChar χ₁ χ₂ (-1) = χ₁ (-1) * χ₂ (-1) := by
  simp only [PAG.Part260.prodChar, MulChar.coeToFun_mul, Pi.mul_apply,
    PAG.Part204.changeLevel_neg_one]

end PAG.Audit257

#print axioms PAG.Audit257.casKer_eq_casK
#print axioms PAG.Audit257.rootNum_eq_zN_div_gs
#print axioms PAG.Audit257.crossSign_eq_rs
