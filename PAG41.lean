/-
  PAG 2.0 Part 37（2026-10-19）— 異なる殻のケットの畳み込み: 直交か飽和かの二択
  原始的なケット |w₁,χ₁⟩（導手 p^(n₁+1)）, |w₂,χ₂⟩（導手 p^(n₂+1)）について、双対殻 a = K−c₁−w₁, b = K−c₂−w₂ とすると
  1. |𝓕|w,χ⟩|² = λ_a·𝓕ε_a（λ_a = p^K/|S_a|）: フーリエ側の台は双対殻 a だけで決まる
  2. a ≠ b なら |w₁,χ₁⟩ ⋆ |w₂,χ₂⟩ = 0
  3. a = b なら ‖|w₁,χ₁⟩ ⋆ |w₂,χ₂⟩‖² = λ_a（作用素ノルムを飽和）
-/
import PAG40

namespace PAG.Part41

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part28 PAG.Part29 PAG.Part30 PAG.Part31 PAG.Part38 PAG.Part39

variable {p : ℕ} [hp : Fact p.Prime]

instance (K : ℕ) : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- **|𝓕|w,χ⟩|² = λ_a · 𝓕ε_a**（a = K − c − w）。 -/
theorem normSq_dft_ket_eq (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (k : ZMod (p ^ K)) :
    (Complex.normSq (𝓕 (ket K w (n + 1) hK χ) k) : ℂ)
      = ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ)) *
          𝓕 (PAG.Part14.epsBall (Pavg (p := p) K) K (K - (n + 1) - w)) k := by
  rw [← dft_auto_eq_normSq, auto_eps K w n hK χ hχ, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul]

/-- 異なる双対殻のべき等元はフーリエ側で直交: 𝓕ε_a · 𝓕ε_b = 0（a ≠ b）。 -/
theorem dft_eps_mul_eq_zero (K a b : ℕ) (ha : a ≤ K) (hb : b ≤ K) (hab : a ≠ b) (k : ZMod (p ^ K)) :
    𝓕 (PAG.Part14.epsBall (Pavg (p := p) K) K a) k * 𝓕 (PAG.Part14.epsBall (Pavg (p := p) K) K b) k = 0 := by
  rw [← Pi.mul_apply, ← PAG.Part16.dft_conv, eps_conv K a b ha hb, ite_eq_right_of_eq_false _ _ (eq_false hab), map_zero, Pi.zero_apply]

/-- **異なる双対殻なら畳み込みは 0**。 -/
theorem conv_ket_eq_zero (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (hab : K - (n₁ + 1) - w₁ ≠ K - (n₂ + 1) - w₂) :
    conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = 0 := by
  apply (ZMod.dft (N := p ^ K) (E := ℂ)).injective
  rw [map_zero]
  funext k
  rw [PAG.Part16.dft_conv, Pi.mul_apply, Pi.zero_apply]
  have e1 := normSq_dft_ket_eq K w₁ n₁ h₁ χ₁ hχ₁ k
  have e2 := normSq_dft_ket_eq K w₂ n₂ h₂ χ₂ hχ₂ k
  have h0 := dft_eps_mul_eq_zero (p := p) K _ _ (by omega) (by omega) hab k
  have hn : (Complex.normSq (𝓕 (ket K w₁ (n₁ + 1) h₁ χ₁) k * 𝓕 (ket K w₂ (n₂ + 1) h₂ χ₂) k) : ℂ) = 0 := by
    rw [Complex.normSq_mul]; push_cast; rw [e1, e2]
    linear_combination (((p : ℂ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℂ)) *
      ((p : ℂ) ^ K / (sz p K (K - (n₂ + 1) - w₂) : ℂ))) * h0
  exact Complex.normSq_eq_zero.mp (by exact_mod_cast hn)

/-- **同じ双対殻なら作用素ノルムを飽和**: ‖|w₁,χ₁⟩ ⋆ |w₂,χ₂⟩‖² = λ_a。 -/
theorem norm_conv_ket_same (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂) :
    ∑ x, Complex.normSq (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) x)
      = (p : ℝ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℝ) := by
  have hN : ((p ^ K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  set lam := (p : ℝ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℝ)
  have h1 := plancherel_normSq (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂))
  have h2 := plancherel_normSq (ket K w₁ (n₁ + 1) h₁ χ₁)
  rw [norm_ket K w₁ n₁ h₁ χ₁ hχ₁, mul_one] at h2
  have hsq : ∀ k, Complex.normSq (𝓕 (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂)) k)
      = lam * Complex.normSq (𝓕 (ket K w₁ (n₁ + 1) h₁ χ₁) k) := by
    intro k
    rw [PAG.Part16.dft_conv, Pi.mul_apply, Complex.normSq_mul]
    have e1 := normSq_dft_ket_eq K w₁ n₁ h₁ χ₁ hχ₁ k
    have e2 := normSq_dft_ket_eq K w₂ n₂ h₂ χ₂ hχ₂ k
    rw [← hab] at e2
    have hz := dft_eps_zero_or_one (p := p) K (K - (n₁ + 1) - w₁) (by omega) k
    have : ((Complex.normSq (𝓕 (ket K w₁ (n₁ + 1) h₁ χ₁) k) * Complex.normSq (𝓕 (ket K w₂ (n₂ + 1) h₂ χ₂) k) : ℝ) : ℂ)
        = ((lam * Complex.normSq (𝓕 (ket K w₁ (n₁ + 1) h₁ χ₁) k) : ℝ) : ℂ) := by
      push_cast; rw [e1, e2]
      simp only [lam]; push_cast
      rcases hz with hz | hz <;> rw [hz] <;> ring
    exact_mod_cast this
  simp_rw [hsq] at h1
  rw [← Finset.mul_sum, h2] at h1
  have e : ((p ^ K : ℕ) : ℝ) * ∑ x, Complex.normSq (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) x)
      = ((p ^ K : ℕ) : ℝ) * lam := by rw [← h1]; ring
  exact mul_left_cancel₀ hN e

end PAG.Part41

#print axioms PAG.Part41.normSq_dft_ket_eq
#print axioms PAG.Part41.dft_eps_mul_eq_zero
#print axioms PAG.Part41.conv_ket_eq_zero
#print axioms PAG.Part41.norm_conv_ket_same
