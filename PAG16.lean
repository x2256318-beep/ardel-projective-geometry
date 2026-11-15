/-
  PAG 2.0 Part 12（2026-10-18）— 定理 A・B の頂上殻（K = c, v = 0）での完全な関数空間版
  1. 原始指標のガウス和: τ(χ) ≠ 0、τ(χ)τ(χ⁻¹) = χ(−1) N、|τ(χ)|² = N
  2. ZMod N 上の離散フーリエ変換 𝓕（Mathlib `ZMod.dft`）の畳み込み定理 𝓕(f ⋆ g) = 𝓕f · 𝓕g
  3. 定理 A（積が原始的）: χ₁ ⋆ χ₂ = J(χ₁, χ₂) · χ₁χ₂（PAG15.Bcv_shift の仮定をすべて具体的に満たす）
  4. 定理 B（χ₂ = χ₁⁻¹）: χ ⋆ χ⁻¹ = χ(−1) · c_N（ラマヌジャン和）
-/
import PAG15
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

namespace PAG.Part16

open ZMod Finset

variable {N : ℕ} [NeZero N]

/-! ## 1. 原始指標のガウス和 -/

omit [NeZero N] in
theorem isPrimitive_inv {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ

/-- **τ(χ) ≠ 0**（χ 原始的）: 𝓕χ = τ·χ⁻¹(−·) なので τ = 0 なら χ = 0 となり χ(1) = 1 に反する。 -/
theorem gaussSum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar ≠ 0 := by
  intro h
  have hF : 𝓕 (χ : ZMod N → ℂ) = 0 := by
    funext k; rw [hχ.fourierTransform_eq_inv_mul_gaussSum, h, mul_zero]; rfl
  have h0 : (χ : ZMod N → ℂ) = 0 := by
    rw [← (dft (N := N) (E := ℂ)).symm_apply_apply χ, hF, map_zero]
  have := congrFun h0 1
  simp at this

/-- τ(χ)τ(χ⁻¹) = χ(−1) N（χ 原始的）。 -/
theorem gauss_mul_gauss_inv_eq {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = χ (-1) * N := by
  have hdd := congrFun (dft_dft (N := N) (E := ℂ) χ) 1
  have hF : 𝓕 (χ : ZMod N → ℂ) = fun k => gaussSum χ stdAddChar * (χ⁻¹ : DirichletCharacter ℂ N) (-k) := by
    funext k; rw [hχ.fourierTransform_eq_inv_mul_gaussSum, mul_comm]
  have hF' : 𝓕 (fun k => (χ⁻¹ : DirichletCharacter ℂ N) (-k)) = fun j =>
      gaussSum χ⁻¹ stdAddChar * χ j := by
    rw [dft_comp_neg]
    funext j
    rw [(isPrimitive_inv hχ).fourierTransform_eq_inv_mul_gaussSum, inv_inv, neg_neg, mul_comm]
  rw [hF, show (fun k => gaussSum χ stdAddChar * (χ⁻¹ : DirichletCharacter ℂ N) (-k))
      = gaussSum χ stdAddChar • (fun k => (χ⁻¹ : DirichletCharacter ℂ N) (-k)) from rfl,
    _root_.map_smul, Pi.smul_apply, hF', smul_eq_mul] at hdd
  simp only [MulChar.map_one, mul_one, smul_eq_mul] at hdd
  linear_combination hdd

/-- **|τ(χ)|² = N**（χ 原始的）。法 p^c なら |τ|² = p^c。 -/
theorem normSq_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ stdAddChar) = N := by
  have h1 := gauss_mul_gauss_inv_eq hχ
  have h2 := PAG.Part9.gauss_mul_gauss_inv (N := N) χ
  have hm : χ (-1) ≠ 0 := by
    intro h; have := PAG.Part9.chi_neg_one_sq χ; rw [h, zero_mul] at this; exact zero_ne_one this
  rw [h2] at h1
  have := mul_left_cancel₀ hm h1
  exact_mod_cast this

/-! ## 2. 畳み込み定理 -/

/-- **𝓕(f ⋆ g) = 𝓕f · 𝓕g**（PAG15.conv、G = ZMod N）。 -/
theorem dft_conv (f g : ZMod N → ℂ) : 𝓕 (PAG.Part15.conv f g) = 𝓕 f * 𝓕 g := by
  funext k
  simp only [dft_apply, PAG.Part15.conv, smul_eq_mul, Pi.mul_apply]
  rw [Finset.sum_mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun y _ => ?_)
  exact (Fintype.sum_equiv (Equiv.addRight y) _ _ (fun z => by
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [show -((z + y) * k) = -(y * k) + -(z * k) by ring, AddChar.map_add_eq_mul]
    ring)).symm

/-- 畳み込みは PAG10.Bcv の 𝓕, α = 1 の場合。 -/
theorem conv_eq_Bcv (f g : ZMod N → ℂ) : PAG.Part15.conv f g = PAG.Part10.Bcv 𝓕 1 f g := by
  unfold PAG.Part10.Bcv
  rw [one_smul, ← dft_conv, LinearEquiv.symm_apply_apply]

/-! ## 3. 定理 A（頂上殻、積が原始的） -/

variable {p n : ℕ} [hp : Fact p.Prime]

/-- **定理 A（頂上殻）**: χ₁, χ₂, χ₁χ₂ が法 p^(n+1) で原始的なら χ₁ ⋆ χ₂ = J(χ₁, χ₂) · χ₁χ₂。
PAG15.Bcv_shift_jacobi の仮定（𝓕f_i = τ_i g_i、g₁g₂ = g₁₂、τ₁₂ ≠ 0）をすべて具体的に満たして得る。 -/
theorem conv_chars_eq_jacobi (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    PAG.Part15.conv (χ₁ : ZMod (p ^ (n + 1)) → ℂ) χ₂ = PAG.Part7.J χ₁ χ₂ • ((χ₁ * χ₂ : DirichletCharacter ℂ _) : ZMod (p ^ (n + 1)) → ℂ) := by
  set g : DirichletCharacter ℂ (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ℂ := fun χ k => χ⁻¹ (-k) with hg
  have hF : ∀ χ : DirichletCharacter ℂ (p ^ (n + 1)), χ.IsPrimitive →
      𝓕 (χ : ZMod (p ^ (n + 1)) → ℂ) = gaussSum χ stdAddChar • g χ := by
    intro χ hχ; funext k; rw [hχ.fourierTransform_eq_inv_mul_gaussSum, mul_comm]; rfl
  have hgg : g χ₁ * g χ₂ = (1 : ℂ) • g (χ₁ * χ₂) := by
    funext k; simp only [hg, Pi.mul_apply, one_smul, mul_inv, MulChar.coeToFun_mul, Pi.mul_apply]
  rw [conv_eq_Bcv, PAG.Part15.Bcv_shift_jacobi (A := ZMod (p ^ (n + 1)) → ℂ) χ₁ χ₂ h₁₂ stdAddChar
    (gaussSum_ne_zero h₁₂) 𝓕 1 1 (χ₁ : ZMod (p ^ (n + 1)) → ℂ) (χ₂ : ZMod (p ^ (n + 1)) → ℂ)
    ((χ₁ * χ₂ : DirichletCharacter ℂ _) : ZMod (p ^ (n + 1)) → ℂ) (g χ₁) (g χ₂) (g (χ₁ * χ₂))
    (hF χ₁ h₁) (hF χ₂ h₂) hgg (hF _ h₁₂), one_mul, one_mul]

/-! ## 4. 定理 B（頂上殻、χ₂ = χ⁻¹） -/

omit hp in
/-- **定理 B（頂上殻）**: χ 原始的なら (χ ⋆ χ⁻¹)(x) = χ(−1) Σ_{k 単数} ψ(kx)（ラマヌジャン和）。 -/
theorem conv_char_inv (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (x : ZMod N) :
    PAG.Part15.conv (χ : ZMod N → ℂ) (χ⁻¹ : DirichletCharacter ℂ N) x
      = χ (-1) * ∑ k : ZMod N, stdAddChar (k * x) * (1 : DirichletCharacter ℂ N) (-k) := by
  have hF1 : 𝓕 (χ : ZMod N → ℂ) = fun k => gaussSum χ stdAddChar * χ⁻¹ (-k) := by
    funext k; rw [hχ.fourierTransform_eq_inv_mul_gaussSum, mul_comm]
  have hF2 : 𝓕 ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) = fun k => gaussSum χ⁻¹ stdAddChar * χ (-k) := by
    funext k; rw [(isPrimitive_inv hχ).fourierTransform_eq_inv_mul_gaussSum, inv_inv, mul_comm]
  have hprod : 𝓕 (χ : ZMod N → ℂ) * 𝓕 ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ)
      = (χ (-1) * N) • fun k => (1 : DirichletCharacter ℂ N) (-k) := by
    rw [hF1, hF2, ← gauss_mul_gauss_inv_eq hχ]
    funext k
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [← inv_mul_cancel χ, MulChar.coeToFun_mul, Pi.mul_apply]
    ring
  rw [conv_eq_Bcv]
  unfold PAG.Part10.Bcv
  rw [one_smul, hprod, _root_.map_smul, Pi.smul_apply, invDFT_apply, smul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_assoc (χ (-1)), mul_inv_cancel₀ (NeZero.ne' (N : ℂ)).symm, mul_one]

end PAG.Part16

#print axioms PAG.Part16.isPrimitive_inv
#print axioms PAG.Part16.gaussSum_ne_zero
#print axioms PAG.Part16.gauss_mul_gauss_inv_eq
#print axioms PAG.Part16.normSq_gaussSum
#print axioms PAG.Part16.dft_conv
#print axioms PAG.Part16.conv_eq_Bcv
#print axioms PAG.Part16.conv_chars_eq_jacobi
#print axioms PAG.Part16.conv_char_inv
