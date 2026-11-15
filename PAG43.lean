/-
  PAG 2.0 Part 39（2026-10-19）— 混合定理 A の射影直線版と鏡像
  1. 南: B_S^proj(|w,χ₁⟩_S, |w+v,χ₂⟩_S) = C·|w,ψ⟩_S
  2. 北（鏡像、(Z/2)² 同変性から）: B_N^proj(|−w,χ₁⟩_N, |−(w+v),χ₂⟩_N) = conj C·|−w,ψ⟩_N
-/
import PAG42

namespace PAG.Part43

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part23 PAG.Part25 PAG.Part28 PAG.Part29 PAG.Part32
  PAG.Part34 PAG.Part35 PAG.Part42

open Classical

variable {p : ℕ} [hp : Fact p.Prime] (K : ℕ) (hK1 : 1 ≤ K)

/-- 混合定理 A の係数 C。 -/
noncomputable def Cmix (K w n v : ℕ) (χ₁ : DirichletCharacter ℂ (p ^ (n + 1)))
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (ψ : DirichletCharacter ℂ (p ^ (n + 1))) : ℂ :=
  (((Real.sqrt (sz p K (w + v)))⁻¹ : ℝ) * (((p ^ (K - w - (n + 1)) : ℕ) : ℂ) *
    (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar)) : ℂ)

/-- **混合定理 A（射影直線上、南）**。 -/
theorem mixed_BSproj (w n v : ℕ) (hv : v ≤ n) (h : w + (n + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, ψ x = χ₁ x * χ₂ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    BSproj K hK1 (ketS_proj K hK1 w (n + 1) h χ₁) (ketS_proj K hK1 (w + v) (n + 1 - v) (by omega) χ₂)
      = Cmix K w n v χ₁ χ₂ ψ • ketS_proj K hK1 w (n + 1) h ψ := by
  apply (projFunEquiv K hK1).injective
  apply Subtype.ext
  simp only [LinearEquiv.map_smul, Submodule.coe_smul, projFun_BSproj, projFun_ketS]
  unfold BS kS
  show extS (conv (ket K w (n + 1) h χ₁) (ket K (w + v) (n + 1 - v) (by omega) χ₂)) = _
  rw [conv_ket_mixed K w n v hv h χ₁ h₁ χ₂ h₂ ψ hψ hprod, extS_smul]
  rfl

omit hp in
/-- ψ(−1) = χ₁(−1)χ₂(−1)。 -/
theorem psi_neg_one_mixed {n v : ℕ} (χ₁ : DirichletCharacter ℂ (p ^ (n + 1)))
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (ψ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hprod : ∀ x, ψ x = χ₁ x * χ₂ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    ψ (-1) = χ₁ (-1) * χ₂ (-1) := by
  have hπ : ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) (ZMod (p ^ (n + 1 - v))) (-1) = -1 := by
    rw [map_neg, map_one]
  rw [hprod, hπ]

/-- **混合定理 A の鏡像（北）**: (Z/2)² 同変性から。 -/
theorem mixed_BNproj (w n v : ℕ) (hv : v ≤ n) (h : w + (n + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, ψ x = χ₁ x * χ₂ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    BNproj K hK1 (ketN_proj K hK1 w (n + 1) h χ₁) (ketN_proj K hK1 (w + v) (n + 1 - v) (by omega) χ₂)
      = starRingEnd ℂ (Cmix K w n v χ₁ χ₂ ψ) • ketN_proj K hK1 w (n + 1) h ψ := by
  have hA := mixed_BSproj K hK1 w n v hv h χ₁ h₁ χ₂ h₂ ψ hψ hprod
  have hE := B_equivariant K hK1 false true true (ketS_proj K hK1 w (n + 1) h χ₁)
    (ketS_proj K hK1 (w + v) (n + 1 - v) (by omega) χ₂)
  simp only [Bb, Bool.false_xor, ↓reduceIte, Bool.false_eq_true] at hE
  rw [hA, sym_tt_smul, (sym_ketS K hK1 w (n + 1) h χ₁).2.2.2,
    (sym_ketS K hK1 (w + v) (n + 1 - v) (by omega) χ₂).2.2.2,
    (sym_ketS K hK1 w (n + 1) h ψ).2.2.2, BNproj_smul, smul_smul] at hE
  have s1 := PAG.Part9.chi_neg_one_sq χ₁
  have s2 := PAG.Part9.chi_neg_one_sq χ₂
  have e := congrArg (fun F => (χ₁ (-1) * χ₂ (-1)) • F) hE
  simp only [smul_smul] at e
  rw [show χ₁ (-1) * χ₂ (-1) * (χ₁ (-1) * χ₂ (-1)) = 1 by linear_combination (χ₂ (-1) * χ₂ (-1)) * s1 + s2,
    one_smul] at e
  rw [e, psi_neg_one_mixed χ₁ χ₂ ψ hprod]
  congr 1
  linear_combination (starRingEnd ℂ (Cmix K w n v χ₁ χ₂ ψ)) * ((χ₂ (-1) * χ₂ (-1)) * s1 + s2)

end PAG.Part43

#print axioms PAG.Part43.Cmix
#print axioms PAG.Part43.mixed_BSproj
#print axioms PAG.Part43.psi_neg_one_mixed
#print axioms PAG.Part43.mixed_BNproj
