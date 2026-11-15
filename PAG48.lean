/-
  PAG 2.0 Part 44（2026-10-19）— 原始ケットの組の畳み込みの分類定理（一つの選言）
  任意の原始ケット |w₁,χ₁⟩（導手 p^(n₁+1)）、|w₂,χ₂⟩（導手 p^(n₂+1)）、双対殻 a, b、λ = p^K/|S_a| について
  次のいずれか（少なくとも一つ。排他性は Lean では述べていない）:
  (i)  a ≠ b かつ conv = 0
  (ii) a = b かつ conv = C·|w,ψ⟩（ψ 原始、|C|² = λ、w は殻の小さい方か w₁ + v）
  (iii) w₁ = w₂、n₁ = n₂ かつ conv = χ₁(−1)·(球の差)（証明の中では χ₁χ₂ = 1 の場合に当たる）
-/
import PAG47

namespace PAG.Part48

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part46 PAG.Part47

variable {p : ℕ} [hp : Fact p.Prime]

/-- 球の差（定理 B の像）。 -/
noncomputable def ballB (K w n : ℕ) : ZMod (p ^ K) → ℂ :=
  PAG.Part22.ball (p := p) K (w + (n + 1))
    - ((p : ℂ) - 1)⁻¹ • (PAG.Part22.ball (p := p) K (w + n) - PAG.Part22.ball (p := p) K (w + (n + 1)))

/-- 混合の場合の一般形（殻・法を変数に一般化して subst）。 -/
theorem mixed_general (K w n v w₂ c₂ : ℕ) (hv1 : 1 ≤ v) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (hw : w + v = w₂) (hc : n + 1 - v = c₂) (h₂ : w₂ + c₂ ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ c₂)) (hχ₂ : χ₂.IsPrimitive) :
    ∃ ψ : DirichletCharacter ℂ (p ^ (n + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
      conv (ket K w (n + 1) hK χ₁) (ket K w₂ c₂ h₂ χ₂) = C • ket K w (n + 1) hK ψ := by
  subst hw; subst hc
  exact conv_ket_mixed_exists K w n v hv1 hv hK χ₁ h₁ χ₂ hχ₂

/-- **分類定理**。 -/
theorem conv_ket_classification (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    (K - (n₁ + 1) - w₁ ≠ K - (n₂ + 1) - w₂ ∧ conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = 0) ∨
    (K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂ ∧
      ∃ w c, ∃ h : w + c ≤ K, 1 ≤ c ∧ ∃ ψ : DirichletCharacter ℂ (p ^ c), ψ.IsPrimitive ∧ ∃ C : ℂ,
        Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℝ) ∧
        conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = C • ket K w c h ψ) ∨
    (w₁ = w₂ ∧ n₁ = n₂ ∧
      conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = χ₁ (-1) • ballB (p := p) K w₁ n₁) := by
  by_cases hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂
  swap
  · exact Or.inl ⟨hab, conv_ket_eq_zero K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab⟩
  rcases lt_trichotomy w₁ w₂ with hw | hw | hw
  · -- w₁ < w₂: 混合（χ₁ の側が大きい導手）
    right; left
    refine ⟨hab, ?_⟩
    obtain ⟨ψ, hψ, C, hC, hconv⟩ := mixed_general K w₁ n₁ (w₂ - w₁) w₂ (n₂ + 1) (by omega) (by omega) h₁
      (by omega) (by omega) h₂ χ₁ hχ₁ χ₂ hχ₂
    exact ⟨w₁, n₁ + 1, h₁, by omega, ψ, hψ, C, hC, hconv⟩
  · -- w₁ = w₂: 同じ殻・同じ導手
    subst hw
    obtain rfl : n₁ = n₂ := by omega
    rcases same_shell_classify K w₁ n₁ h₁ χ₁ χ₂ hχ₁ hχ₂ with ⟨v, hv, ψ, hψ, C, hC, hconv⟩ | ⟨_, hB⟩
    · right; left
      exact ⟨hab, w₁ + v, n₁ + 1 - v, by omega, by omega, ψ, hψ, C, hC, hconv⟩
    · right; right
      exact ⟨rfl, rfl, hB⟩
  · -- w₂ < w₁: 混合（χ₂ の側が大きい導手）、可換性で入れ替え
    right; left
    refine ⟨hab, ?_⟩
    obtain ⟨ψ, hψ, C, hC, hconv⟩ := mixed_general K w₂ n₂ (w₁ - w₂) w₁ (n₁ + 1) (by omega) (by omega) h₂
      (by omega) (by omega) h₁ χ₂ hχ₂ χ₁ hχ₁
    refine ⟨w₂, n₂ + 1, h₂, by omega, ψ, hψ, C, ?_, ?_⟩
    · rw [hab]; exact hC
    · rw [conv_comm]; exact hconv

/-- 系: どの場合も、a = b なら ‖conv‖² = λ、a ≠ b なら 0（ノルムの二択）。 -/
theorem conv_ket_norm_dichotomy (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    ∑ x, Complex.normSq (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) x)
      = if K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂ then (p : ℝ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℝ) else 0 := by
  split_ifs with hab
  · exact norm_conv_ket_same K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab
  · rw [conv_ket_eq_zero K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab]
    simp

end PAG.Part48

#print axioms PAG.Part48.ballB
#print axioms PAG.Part48.mixed_general
#print axioms PAG.Part48.conv_ket_classification
#print axioms PAG.Part48.conv_ket_norm_dichotomy
