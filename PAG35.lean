/-
  PAG 2.0 Part 31（2026-10-19）
  1. B_S^proj, B_N^proj のスカラー双線形性、~_proj の反線形性
  2. 鏡像定理 A を「定理 A + (Z/2)² 同変性」から再導出（mirror_thmA_via_sym）
  3. 射影直線上の ℓ² 内積（点の数え上げ測度）: W_proj はユニタリ、~_proj は反ユニタリ
-/
import PAG34

namespace PAG.Part35

open ZMod Finset PAG.Part19 PAG.Part23 PAG.Part26 PAG.Part27 PAG.Part28 PAG.Part29 PAG.Part31 PAG.Part32 PAG.Part34

open Classical

/-! ## 1. 双線形性と反線形性 -/

section Lin

variable {p : ℕ} [hp : Fact p.Prime] (K : ℕ) (hK : 1 ≤ K)

instance : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

theorem BS_smul (a b : ℂ) (F G : P1F (p ^ K)) : BS (a • F) (b • G) = (a * b) • BS F G := by
  unfold BS
  rw [Prod.smul_fst, Prod.smul_fst, PAG.Part15.conv_smul_smul, extS_smul]

theorem BN_smul (a b : ℂ) (F G : P1F (p ^ K)) : BN (a • F) (b • G) = (a * b) • BN F G := by
  rw [BN_eq, BN_eq, Prod.smul_snd, Prod.smul_snd, PAG.Part15.conv_smul_smul, extN_smul]

theorem BSproj_smul (a b : ℂ) (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    BSproj K hK (a • Φ) (b • Ψ) = (a * b) • BSproj K hK Φ Ψ := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  simp only [LinearEquiv.map_smul, Submodule.coe_smul, projFun_BSproj]
  exact BS_smul K a b _ _

theorem BNproj_smul (a b : ℂ) (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    BNproj K hK (a • Φ) (b • Ψ) = (a * b) • BNproj K hK Φ Ψ := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  simp only [LinearEquiv.map_smul, Submodule.coe_smul, projFun_BNproj]
  exact BN_smul K a b _ _

omit hp in
theorem tildePull_smul {N : ℕ} (a : ℂ) (Φ : ProjLine N → ℂ) :
    tildePull (a • Φ) = starRingEnd ℂ a • tildePull Φ := by
  funext q; simp [tildePull]

omit hp in
theorem Wpull_smul {N : ℕ} (a : ℂ) (Φ : ProjLine N → ℂ) : Wpull (a • Φ) = a • Wpull Φ := rfl

omit hp in
theorem sym_tt_smul {N : ℕ} (a : ℂ) (Φ : ProjLine N → ℂ) :
    sym true true (a • Φ) = starRingEnd ℂ a • sym true true Φ := by
  simp only [sym, ↓reduceIte, tildePull_smul, Wpull_smul]

end Lin

/-! ## 2. 鏡像定理 A の再導出 -/

section Mirror

variable {p : ℕ} [hp : Fact p.Prime] (K : ℕ) (hK : 1 ≤ K)

omit hp in
/-- 積の関係から ψ(−1) = χ₁(−1)χ₂(−1)。 -/
theorem psi_neg_one {n v : ℕ} (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v)))
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    ψ (-1) = χ₁ (-1) * χ₂ (-1) := by
  have h0 := hprod (-1)
  have hπ : ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) (ZMod (p ^ (n + 1 - v))) (-1) = -1 := by
    rw [map_neg, map_one]
  rw [hπ, MulChar.coeToFun_mul, Pi.mul_apply] at h0
  exact h0.symm

/-- **鏡像定理 A は定理 A と (Z/2)² 同変性から従う**（PAG29 の直接証明とは独立な導出）。 -/
theorem mirror_thmA_via_sym (w n v : ℕ) (hv : v ≤ n) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    BNproj K hK (ketN_proj K hK w (n + 1) h χ₁) (ketN_proj K hK w (n + 1) h χ₂)
      = ((Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) : ℝ) *
          starRingEnd ℂ (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
            (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))) : ℂ) •
        ketN_proj K hK (w + v) (n + 1 - v) (by omega) ψ := by
  -- 定理 A に W~ を当てる
  have hA := thmA_BSproj K hK w n v hv h χ₁ χ₂ h₁ h₂ ψ hψ hprod
  have hE := B_equivariant K hK false true true (ketS_proj K hK w (n + 1) h χ₁) (ketS_proj K hK w (n + 1) h χ₂)
  simp only [Bb, Bool.false_xor, ↓reduceIte, Bool.false_eq_true] at hE
  rw [hA, sym_tt_smul, (sym_ketS K hK w (n + 1) h χ₁).2.2.2, (sym_ketS K hK w (n + 1) h χ₂).2.2.2,
    (sym_ketS K hK (w + v) (n + 1 - v) (by omega) ψ).2.2.2, BNproj_smul, smul_smul] at hE
  -- 両辺に χ₁(−1)χ₂(−1)（= ±1）を掛けて整理
  have s1 := PAG.Part9.chi_neg_one_sq χ₁
  have s2 := PAG.Part9.chi_neg_one_sq χ₂
  have hψ1 := psi_neg_one χ₁ χ₂ ψ hprod
  have e := congrArg (fun F => (χ₁ (-1) * χ₂ (-1)) • F) hE
  simp only [smul_smul] at e
  rw [show χ₁ (-1) * χ₂ (-1) * (χ₁ (-1) * χ₂ (-1)) = 1 by linear_combination (χ₂ (-1) * χ₂ (-1)) * s1 + s2,
    one_smul] at e
  rw [e, hψ1]
  congr 1
  rw [map_mul, Complex.conj_ofReal]
  linear_combination (((Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) : ℝ) : ℂ) *
    starRingEnd ℂ (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
      (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ)))) *
    ((χ₂ (-1) * χ₂ (-1)) * s1 + s2)

end Mirror

/-! ## 3. 等長性 -/

section Iso

variable {p : ℕ} [hp : Fact p.Prime] (K : ℕ)

/-- 点の反転 [x:1] ↦ [−x:1]、[1:y] ↦ [1:−y]。 -/
def negPt {N : ℕ} : Pt N → Pt N
  | Sum.inl x => Sum.inl (-x)
  | Sum.inr y => Sum.inr ⟨-y.1, fun h => y.2 (by simpa using h.neg)⟩

theorem negPt_negPt {N : ℕ} (z : Pt N) : negPt (negPt z) = z := by
  rcases z with x | ⟨y, hy⟩ <;> simp [negPt]

omit hp in
theorem toProj_negPt (z : Pt (p ^ K)) : toProj K (negPt z) = negProj (toProj K z) := by
  rcases z with x | ⟨y, hy⟩
  · rfl
  · exact (negProj_north y).symm

/-- 射影直線上の ℓ² 内積（点の数え上げ測度、点モデルで和をとる）。 -/
noncomputable def inner (Φ Ψ : ProjLine (p ^ K) → ℂ) : ℂ :=
  ∑ z : Pt (p ^ K), starRingEnd ℂ (Φ (toProj K z)) * Ψ (toProj K z)

/-- **W_proj はユニタリ**: ⟨WΦ, WΨ⟩ = ⟨Φ, Ψ⟩。 -/
theorem inner_Wpull (Φ Ψ : ProjLine (p ^ K) → ℂ) : inner K (Wpull Φ) (Wpull Ψ) = inner K Φ Ψ := by
  unfold inner Wpull
  simp only [Function.comp_apply, ← toProj_Wpt]
  exact Fintype.sum_equiv (WptEquiv (p ^ K)) _ _ (fun z => rfl)

/-- **~_proj は反ユニタリ**: ⟨~Φ, ~Ψ⟩ = conj⟨Φ, Ψ⟩。 -/
theorem inner_tildePull (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    inner K (tildePull Φ) (tildePull Ψ) = starRingEnd ℂ (inner K Φ Ψ) := by
  unfold inner tildePull
  rw [map_sum]
  simp only [← toProj_negPt, map_mul, Complex.conj_conj]
  exact Fintype.sum_equiv (Function.Involutive.toPerm _ (fun z => negPt_negPt (N := p ^ K) z)) _ _
    (fun z => rfl)

/-- (Z/2)² の各元は内積を保つか共役をとる: ⟨gΦ, gΨ⟩ = ⟨Φ, Ψ⟩ または conj。 -/
theorem inner_sym (s t : Bool) (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    inner K (sym s t Φ) (sym s t Ψ) = if t then starRingEnd ℂ (inner K Φ Ψ) else inner K Φ Ψ := by
  cases s <;> cases t <;>
    simp only [sym, Bool.false_eq_true, ↓reduceIte, id, inner_Wpull, inner_tildePull]

end Iso

end PAG.Part35

#print axioms PAG.Part35.BS_smul
#print axioms PAG.Part35.BN_smul
#print axioms PAG.Part35.BSproj_smul
#print axioms PAG.Part35.BNproj_smul
#print axioms PAG.Part35.tildePull_smul
#print axioms PAG.Part35.Wpull_smul
#print axioms PAG.Part35.sym_tt_smul
#print axioms PAG.Part35.psi_neg_one
#print axioms PAG.Part35.mirror_thmA_via_sym
#print axioms PAG.Part35.negPt
#print axioms PAG.Part35.negPt_negPt
#print axioms PAG.Part35.toProj_negPt
#print axioms PAG.Part35.inner
#print axioms PAG.Part35.inner_Wpull
#print axioms PAG.Part35.inner_tildePull
#print axioms PAG.Part35.inner_sym
