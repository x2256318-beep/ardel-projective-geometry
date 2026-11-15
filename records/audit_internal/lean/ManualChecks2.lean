import PAG260
import PAG3
import PAG6
/-! 内部照合の監査（2026-11-14、直しの照合 F の指摘 #3・#13 を受けた版）：照合者が A・B と判定し、直接の当てはめでは
確かめられなかった組を、前の鎖の宣言だけから示す。定理の対象は `type_of%` で対象の型そのものを述べる（仮定を足さない）。
定義の一致は、両辺が型を持つのに要る仮定だけで述べる。鎖の外のファイルで、鎖は変えない。 -/
open Complex DirichletCharacter

namespace PAG.Audit257

/-! ### 定義の一致（値として） -/

/-- A（値）：Part 252 の `casKer` は付録 A の Part 3 の `casK` と同じ値（定義から直接。Part 252 の補題は使わない）。 -/
theorem casKer_eq_casK {N : ℕ} [NeZero N] (t : ZMod N) : PAG.Part256.casKer t = PAG.Part3.casK t := by
  unfold PAG.Part256.casKer PAG.Part3.casK PAG.Kloosterman.cas
  have h1 : (ZMod.stdAddChar t : ℂ) = Complex.exp (((2 * Real.pi * t.val / N : ℝ) : ℂ) * I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    push_cast
    ring
  rw [h1, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- B（値）：Part 252 の `rootNum` は Part 192 の `zN` を Part 194 の `gs` で割ったもの。 -/
theorem rootNum_eq_zN_div_gs {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    PAG.Part256.rootNum χ = PAG.Part196.zN χ / PAG.Part198.gs χ := by
  unfold PAG.Part256.rootNum PAG.Part196.zN PAG.Part198.gs
  rw [div_div, mul_comm]
  rfl

/-- A（値）：Part 253 の `charU` は Part 1 の `PAG.charFun` に `MulChar.toUnitHom` を通したもの（NeZero は仮定しない）。 -/
theorem charU_eq_charFun {N : ℕ} (χ : DirichletCharacter ℂ N) :
    PAG.Part257.charU χ = PAG.charFun (MulChar.toUnitHom χ) := by
  funext u
  simp [PAG.Part257.charU, PAG.charFun]

/-- A（定義、範囲の中）：Part 253 の `ip` は Part 249 の `ipG` の G = (ZMod N)ˣ の場合。 -/
theorem ip_eq_ipG {N : ℕ} [NeZero N] (f g : (ZMod N)ˣ → ℂ) : PAG.Part257.ip f g = PAG.Part253.ipG f g := rfl

/-- A（定義）：Part 256 の `crtMap` は Part 189 の `param` と同じ式。 -/
theorem crtMap_eq_param {M N : ℕ} [NeZero M] [NeZero N] (x : ZMod M × ZMod N) :
    PAG.Part260.crtMap M N x = PAG.Part193.param M N x := rfl

/-- A（値）：Part 256 の `crossSign` は Part 194 の `rs` と同じ値（χ(−1) = ±1 による。NeZero は仮定しない）。 -/
theorem crossSign_eq_rs {M N : ℕ} (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part260.crossSign χ₁ χ₂ = PAG.Part198.rs χ₁ χ₂ := by
  unfold PAG.Part260.crossSign PAG.Part198.rs
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  rcases χ₁.even_or_odd with h1 | h1 <;> rcases χ₂.even_or_odd with h2 | h2 <;>
    simp only [DirichletCharacter.Even, DirichletCharacter.Odd] at h1 h2 <;>
    simp [DirichletCharacter.Odd, h1, h2, hne, hne.symm]

/-! ### 定理（対象の型そのもの） -/

/-- B：Part 252 の `inv_apply_units_inv`（NeZero なし）は付録 A の Part 3 の `apply_inv_eq_inv_apply` から 1 行。 -/
theorem inv_apply_units_inv_of_PAG3 : type_of% @PAG.Part256.inv_apply_units_inv := by
  intro N χ u
  rw [← ZMod.inv_coe_unit, PAG.Part3.apply_inv_eq_inv_apply χ⁻¹ u.isUnit, inv_inv]

/-- B：Part 252 の `sum_mul_stdAddChar_neg` は付録 A の Part 3 の `sum_neg_twist`（x = 1）。 -/
theorem sum_mul_stdAddChar_neg_of_PAG3 : type_of% @PAG.Part256.sum_mul_stdAddChar_neg := by
  intro N _ χ
  have h := PAG.Part3.sum_neg_twist χ 1
  simp only [one_mul] at h
  unfold gaussSum
  simpa only [mul_comm (χ _)] using h

/-- B：Part 253 の `not_isPrimitive_one_of_two_le` は Part 191 の `ne_one_of_isPrimitive` の対偶。 -/
theorem not_isPrimitive_one_of_two_le_of_PAG195 : type_of% @PAG.Part257.not_isPrimitive_one_of_two_le := by
  intro N _ hN h
  exact PAG.Part195.ne_one_of_isPrimitive hN 1 h rfl

/-- B：Part 253 の `charU_one_mem_Vimprim` も同じ定理から 1 行。 -/
theorem charU_one_mem_Vimprim_of_PAG195 : type_of% @PAG.Part257.charU_one_mem_Vimprim := by
  intro N _ hN
  exact Submodule.subset_span ⟨⟨1, fun h => PAG.Part195.ne_one_of_isPrimitive hN 1 h rfl⟩, rfl⟩

/-- B：Part 254 の `gaussSum_inv` は Part 5 の `conj_gaussSum` と `chi_neg_one_sq` から 1 行。 -/
theorem gaussSum_inv_of_PAG9 : type_of% @PAG.Part258.gaussSum_inv := by
  intro N _ χ
  rw [PAG.Part9.conj_gaussSum, ← mul_assoc, PAG.Part9.chi_neg_one_sq, one_mul]

/-- B：Part 253 の `not_isPrimitive_one_prime` は Part 28 の `prim_level_p_iff` から 1 行。 -/
theorem not_isPrimitive_one_prime_of_PAG32 : type_of% @PAG.Part257.not_isPrimitive_one_prime := by
  intro p _ h
  exact (PAG.Part32.prim_level_p_iff 1).mp h rfl

/-- B：Part 253 の `Vprim_two` は Part 26 の `no_prim_mod_two` から（張る集合が空）。 -/
theorem Vprim_two_of_PAG30 : type_of% @PAG.Part257.Vprim_two := by
  rw [PAG.Part257.Vprim, Submodule.span_eq_bot]
  rintro _ ⟨χ, rfl⟩
  exact absurd χ.2 (PAG.Part30.no_prim_mod_two χ.1)

/-- B：Part 256 の `prodChar_neg_one` は Part 200 の `changeLevel_neg_one` を 2 回使うだけ。 -/
theorem prodChar_neg_one_of_PAG204 : type_of% @PAG.Part260.prodChar_neg_one := by
  intro M N _ _ χ₁ χ₂
  simp only [PAG.Part260.prodChar, MulChar.coeToFun_mul, Pi.mul_apply, PAG.Part204.changeLevel_neg_one]

end PAG.Audit257

#print axioms PAG.Audit257.casKer_eq_casK
#print axioms PAG.Audit257.rootNum_eq_zN_div_gs
#print axioms PAG.Audit257.charU_eq_charFun
#print axioms PAG.Audit257.ip_eq_ipG
#print axioms PAG.Audit257.crtMap_eq_param
#print axioms PAG.Audit257.crossSign_eq_rs
#print axioms PAG.Audit257.inv_apply_units_inv_of_PAG3
#print axioms PAG.Audit257.sum_mul_stdAddChar_neg_of_PAG3
#print axioms PAG.Audit257.not_isPrimitive_one_of_two_le_of_PAG195
#print axioms PAG.Audit257.charU_one_mem_Vimprim_of_PAG195
#print axioms PAG.Audit257.gaussSum_inv_of_PAG9
#print axioms PAG.Audit257.not_isPrimitive_one_prime_of_PAG32
#print axioms PAG.Audit257.Vprim_two_of_PAG30
#print axioms PAG.Audit257.prodChar_neg_one_of_PAG204
