/-
  PAG 2.0 Part 32（2026-10-19）
  1. 鏡像定理 B を「定理 B + (Z/2)² 同変性」から再導出（W ε^S = ε^N、係数 cB は実）
  2. B と内積の随伴関係: ⟨Φ, B_S(Ψ₁, Ψ₂)⟩ = ⟨B_S(Φ, ~Ψ₂), Ψ₁⟩、B_N も同様
-/
import PAG35

namespace PAG.Part36

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part23 PAG.Part25 PAG.Part26 PAG.Part27 PAG.Part28 PAG.Part29 PAG.Part30
  PAG.Part31 PAG.Part32 PAG.Part34 PAG.Part35

open Classical

variable {p : ℕ} [hp : Fact p.Prime] (K : ℕ) (hK : 1 ≤ K)

instance : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-! ## 1. 鏡像定理 B の再導出 -/

/-- W ε^S = ε^N（射影直線上）。 -/
theorem Wpull_epsS (a : ℕ) : Wpull (epsS_proj (p := p) K hK a) = epsN_proj (p := p) K hK a := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  rw [projFun_Wpull, projFun_epsS, projFun_epsN, W_extS]

omit hp in
/-- 係数 cB は実数（共役で不変）。 -/
theorem conj_cB (w n : ℕ) (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    starRingEnd ℂ (cB K w n χ) = cB K w n χ := by
  rw [cB, map_mul, star_chi_neg_one, map_div₀, map_pow, Complex.conj_natCast, Complex.conj_natCast]

/-- **鏡像定理 B は定理 B と (Z/2)² 同変性から従う**（PAG29 の直接証明とは独立な導出）。 -/
theorem mirror_thmB_via_sym (w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    BNproj K hK (ketN_proj K hK w (n + 1) h χ) (ketN_proj K hK w (n + 1) h χ⁻¹)
      = cB K w n χ • epsN_proj K hK (K - (n + 1) - w) := by
  have hE := B_equivariant K hK false true true (ketS_proj K hK w (n + 1) h χ) (ketS_proj K hK w (n + 1) h χ⁻¹)
  simp only [Bb, Bool.false_xor, ↓reduceIte, Bool.false_eq_true] at hE
  rw [thmB_BSproj K hK w n h χ hχ, sym_tt_smul, (sym_ketS K hK w (n + 1) h χ).2.2.2,
    (sym_ketS K hK w (n + 1) h χ⁻¹).2.2.2, BNproj_smul, conj_cB] at hE
  have hsym : sym true true (epsS_proj (p := p) K hK (K - (n + 1) - w)) = epsN_proj K hK (K - (n + 1) - w) := by
    simp only [sym, ↓reduceIte, tildePull_epsS, Wpull_epsS]
  rw [hsym, chi_inv_neg_one, PAG.Part9.chi_neg_one_sq, one_smul] at hE
  exact hE

/-! ## 2. 随伴関係 -/

omit hp in
/-- チャート上の随伴: Σ conj φ · (f ⋆ g) = Σ conj (φ ⋆ g~) · f。 -/
theorem conv_adjoint {N : ℕ} [NeZero N] (φ f g : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (φ x) * conv f g x = ∑ x, starRingEnd ℂ (conv φ (tilde g) x) * f x := by
  simp only [conv, tilde, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
  rw [neg_sub]
  ring

/-- BSproj は北の内部点で 0。 -/
theorem BSproj_north_interior (Φ Ψ : ProjLine (p ^ K) → ℂ) (y : {y : ZMod (p ^ K) // ¬ IsUnit y}) :
    BSproj K hK Φ Ψ (toProj K (Sum.inr y)) = 0 := by
  show BSproj K hK Φ Ψ (mk ⟨(1, y.1), 1, 0, by simp⟩) = 0
  have e := projFun_north K hK (BSproj K hK Φ Ψ) y.1
  rw [← e, projFun_BSproj]
  show (extS _).2 y.1 = 0
  simp [extS, y.2]

/-- **B_S^proj の随伴**: ⟨Φ, B_S(Ψ₁, Ψ₂)⟩ = ⟨B_S(Φ, ~Ψ₂), Ψ₁⟩。 -/
theorem inner_BSproj (Φ Ψ₁ Ψ₂ : ProjLine (p ^ K) → ℂ) :
    PAG.Part35.inner K Φ (BSproj K hK Ψ₁ Ψ₂) = PAG.Part35.inner K (BSproj K hK Φ (tildePull Ψ₂)) Ψ₁ := by
  unfold PAG.Part35.inner
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [BSproj_north_interior, mul_zero, map_zero, zero_mul, Finset.sum_const_zero, add_zero]
  show ∑ x, starRingEnd ℂ (Φ (mk ⟨(x, 1), 0, 1, by simp⟩)) * BSproj K hK Ψ₁ Ψ₂ (mk ⟨(x, 1), 0, 1, by simp⟩)
    = ∑ x, starRingEnd ℂ (BSproj K hK Φ (tildePull Ψ₂) (mk ⟨(x, 1), 0, 1, by simp⟩)) * Ψ₁ (mk ⟨(x, 1), 0, 1, by simp⟩)
  simp only [BSproj_south]
  exact conv_adjoint _ _ _

/-- **B_N^proj の随伴**: ⟨Φ, B_N(Ψ₁, Ψ₂)⟩ = ⟨B_N(Φ, ~Ψ₂), Ψ₁⟩（W で南から移す）。 -/
theorem inner_BNproj (Φ Ψ₁ Ψ₂ : ProjLine (p ^ K) → ℂ) :
    PAG.Part35.inner K Φ (BNproj K hK Ψ₁ Ψ₂) = PAG.Part35.inner K (BNproj K hK Φ (tildePull Ψ₂)) Ψ₁ := by
  have h1 : PAG.Part35.inner K Φ (BNproj K hK Ψ₁ Ψ₂) = PAG.Part35.inner K (Wpull Φ) (BSproj K hK (Wpull Ψ₁) (Wpull Ψ₂)) := by
    rw [BNproj_eq, ← inner_Wpull K (Wpull Φ), Wpull_Wpull]
  rw [h1, inner_BSproj, tildePull_Wpull K hK, BSproj_W, inner_Wpull]

end PAG.Part36

#print axioms PAG.Part36.Wpull_epsS
#print axioms PAG.Part36.conj_cB
#print axioms PAG.Part36.mirror_thmB_via_sym
#print axioms PAG.Part36.conv_adjoint
#print axioms PAG.Part36.BSproj_north_interior
#print axioms PAG.Part36.inner_BSproj
#print axioms PAG.Part36.inner_BNproj
