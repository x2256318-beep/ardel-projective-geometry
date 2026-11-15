/-
  Projective Adelic Geometry — formalization (付録 A)
  対象: 定理 2.6（有限レベル版）, 命題 3.1（グリーン恒等式の代数部分）
  命題 3.1 は EuclideanSpace ℂ (Fin n) ではなく、一般の複素内積空間 E 上で述べる（より一般）。
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap

open Complex

namespace PAG

/-! ## 1. 有限レベル: 可換群 G（例: (ZMod N)ˣ）上の関数空間 -/

section Finite

variable {G : Type*} [CommGroup G]

/-- 正則表現の平行移動 (T_h f)(g) = f (g * h)（M_p の有限レベル版）。 -/
def transl (h : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f g := f (g * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- ファイバー反転 (J f)(g) = f g⁻¹。 -/
def rev : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f g := f g⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 指標を関数として見たもの。 -/
def charFun (χ : G →* ℂˣ) : G → ℂ := fun g => (χ g : ℂ)

/-- 定理 2.6 (a)⇒(b) の前半（有限版）:
すべての平行移動と可換な線形写像は、各指標にスカラー（= U χ の単位元での値）として作用する。 -/
theorem eigen_of_commute (U : (G → ℂ) →ₗ[ℂ] (G → ℂ))
    (hU : ∀ h : G, U ∘ₗ transl h = transl h ∘ₗ U) (χ : G →* ℂˣ) :
    ∃ c : ℂ, U (charFun χ) = c • charFun χ := by
  refine ⟨U (charFun χ) 1, ?_⟩
  have key : ∀ h g : G, U (charFun χ) (g * h) = (χ h : ℂ) * U (charFun χ) g := by
    intro h g
    have e1 : transl h (charFun χ) = (χ h : ℂ) • charFun χ := by
      funext x
      simp [transl, charFun, mul_comm]
    have h2 := congrArg (fun F => F (charFun χ)) (hU h)
    simp only [LinearMap.comp_apply] at h2
    rw [e1, map_smul] at h2
    have h3 := congrFun h2 g
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    exact h3.symm
  funext h
  have h4 := key h 1
  rw [one_mul] at h4
  rw [h4]
  simp [charFun, mul_comm]

/-- 定理 2.6 の実指標についての帰結:
対角形 U χ = c χ で反転条件 c(χ⁻¹) = conj (c χ) が成り立ち、χ⁻¹ = χ なら c χ = ±1。 -/
theorem real_sector_sign (c : (G →* ℂˣ) → ℂ)
    (hc : ∀ χ, ‖c χ‖ = 1)
    (hrev : ∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ))
    (χ : G →* ℂˣ) (hreal : χ⁻¹ = χ) :
    c χ = 1 ∨ c χ = -1 := by
  have h1 := hrev χ
  rw [hreal] at h1
  have him : (c χ).im = 0 := Complex.conj_eq_iff_im.mp h1.symm
  have hz : c χ = ((c χ).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hn := hc χ
  rw [hz, Complex.norm_real, Real.norm_eq_abs] at hn
  rcases (abs_eq zero_le_one).mp hn with h | h
  · left; rw [hz, h]; simp
  · right; rw [hz, h]; simp

end Finite

/-! ## 2. 命題 3.1: 境界三重組のグリーン恒等式（代数部分）
  Mathlib の内積 `inner ℂ x y` は第 1 引数について共役線形。
  本文の ⟨u, v⟩（第 1 引数について線形）は `inner ℂ v u` に対応する。 -/

section BoundaryTriple

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- 1/√2 -/
noncomputable def s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- Γ₀ = (U a − b)/√2（a = γ₊ f, b = γ₋ f）。 -/
noncomputable def Γ₀ (U : E ≃ₗᵢ[ℂ] E) (a b : E) : E := s • (U a - b)

/-- Γ₁ = −i (U a + b)/√2。 -/
noncomputable def Γ₁ (U : E ≃ₗᵢ[ℂ] E) (a b : E) : E := (-I * s) • (U a + b)

lemma conj_s : starRingEnd ℂ s = s := by
  simp [s]

lemma s_mul_s : s * s = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [s, ← mul_inv, h]
  norm_num

lemma s_ne_zero : s ≠ 0 := by
  simp [s]

/-- 命題 3.1 の代数的核心（Mathlib の慣例で書いたもの）:
⟪Γ₀ g, Γ₁ f⟫ − ⟪Γ₁ g, Γ₀ f⟫ = −i (⟪a', a⟫ − ⟪b', b⟫)。 -/
theorem green_boundary (U : E ≃ₗᵢ[ℂ] E) (a b a' b' : E) :
    inner ℂ (Γ₀ U a' b') (Γ₁ U a b) - inner ℂ (Γ₁ U a' b') (Γ₀ U a b)
      = -I * (inner ℂ a' a - inner ℂ b' b) := by
  simp only [Γ₀, Γ₁, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, LinearIsometryEquiv.inner_map_map, map_mul, map_neg,
    Complex.conj_I, conj_s]
  linear_combination (-2 * I * (inner ℂ a' a - inner ℂ b' b)) * s_mul_s

/-- ker Γ₀ = {b = U a}、すなわち D(D_U) の境界条件。 -/
theorem ker_Γ₀ (U : E ≃ₗᵢ[ℂ] E) (a b : E) : Γ₀ U a b = 0 ↔ b = U a := by
  unfold Γ₀
  rw [smul_eq_zero, sub_eq_zero]
  simp only [s_ne_zero, false_or]
  exact eq_comm

end BoundaryTriple

end PAG

#print axioms PAG.eigen_of_commute
#print axioms PAG.real_sector_sign
#print axioms PAG.green_boundary
#print axioms PAG.ker_Γ₀
