/-
  PAG 2.0 Part 78（2026-10-19）— 三つの同値の一本化
  任意の素数・同じ殻・同じ導手の原始ケット: (k₁ ⋆ k₂)(0) ≠ 0 ↔ χ₂ = χ₁⁻¹
  奇素数（塔）:  φ ∣ j₁ + j₂ ↔ (k₁ ⋆ k₂)(0) ≠ 0 ↔ ω^{j₂} = (ω^{j₁})⁻¹
  p = 2（χ_{s,j}）: (2^(d+1) ∣ j + j' ∧ s + s' 偶) ↔ (k₁ ⋆ k₂)(0) ≠ 0 ↔ χ_{s',j'} = χ_{s,j}⁻¹
  （左辺は乗積表の (B)/(B2)、すなわち像が ballB の定数倍になる場合）
-/
import PAG81

namespace PAG.Part82

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part48 PAG.Part49 PAG.Part61 PAG.Part67 PAG.Part68
  PAG.Part69 PAG.Part73 PAG.Part81

variable {p : ℕ} [hp : Fact p.Prime]

/-- **原点での値が 0 でない ↔ 逆指標**（任意の素数・同じ殻・同じ導手）。 -/
theorem conv_zero_ne_iff (K w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    conv (ket K w (n + 1) h χ₁) (ket K w (n + 1) h χ₂) 0 ≠ 0 ↔ χ₂ = χ₁⁻¹ := by
  classical
  rw [conv_zero_same K w n h χ₁ χ₂ hχ₁ hχ₂]
  by_cases hc : χ₂ = χ₁⁻¹
  · simp only [hc, ite_true, iff_true]; exact PAG.Part75.chi_neg_one_ne_zero _
  · simp only [hc, ite_false, ne_eq, not_true_eq_false]

section Odd
variable (hp2 : p ≠ 2) (c : ℕ)
include hp2

/-- **奇素数: (B) ↔ 原点での値 ≠ 0**。 -/
theorem odd_B_iff_conv_zero (K w c₁ : ℕ) (hc₁ : 1 ≤ c₁) (h₁ : c₁ ≤ c) (hK : w + (c₁ + 1) ≤ K) (j₁ j₂ : ℕ)
    (hj₁ : ¬ p ∣ j₁) (hj₂ : ¬ p ∣ j₂) :
    phi (p := p) c₁ ∣ j₁ + j₂ ↔
      conv (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
        (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₂ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ)) 0
        ≠ 0 := by
  have hT := odd_same_shell_table hp2 c K w c₁ hc₁ h₁ hK j₁ j₂ hj₁ hj₂
  simp only at hT
  rcases hT with ⟨hD, h, C, -, e⟩ | ⟨hL, hφ, h, C, -, e⟩ | ⟨hB, e⟩
  · rw [e, Pi.smul_apply, ket_apply_zero K _ _ (by omega) h _, smul_zero]
    refine ⟨fun hB => absurd ⟨hD, hB⟩ (PAG.Part74.odd_cases_exactly_one (p := p) c₁ j₁ j₂ hc₁ hj₁).2.2.1,
      fun h0 => absurd rfl h0⟩
  · rw [e, Pi.smul_apply, ket_apply_zero K _ _ (by omega) h _, smul_zero]
    exact ⟨fun hB => absurd hB hφ, fun h0 => absurd rfl h0⟩
  · rw [e, Pi.smul_apply, ballB_apply_zero, smul_eq_mul, mul_one]
    exact ⟨fun _ => PAG.Part75.chi_neg_one_ne_zero _, fun _ => hB⟩

/-- **奇素数・三つの同値**: (B) ↔ 原点での値 ≠ 0 ↔ ω^{j₂} = (ω^{j₁})⁻¹。 -/
theorem odd_three_equiv (K w c₁ : ℕ) (hc₁ : 1 ≤ c₁) (h₁ : c₁ ≤ c) (hK : w + (c₁ + 1) ≤ K) (j₁ j₂ : ℕ)
    (hj₁ : ¬ p ∣ j₁) (hj₂ : ¬ p ∣ j₂) :
    (phi (p := p) c₁ ∣ j₁ + j₂ ↔
      conv (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
        (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₂ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ)) 0
        ≠ 0) ∧
    (phi (p := p) c₁ ∣ j₁ + j₂ ↔ omegaLow hp2 c c₁ h₁ ^ j₂ = (omegaLow hp2 c c₁ h₁ ^ j₁)⁻¹) := by
  have h1 := odd_B_iff_conv_zero hp2 c K w c₁ hc₁ h₁ hK j₁ j₂ hj₁ hj₂
  have hf := omegaLow_isFaithful hp2 c c₁ h₁
  have hP₁ : (omegaLow hp2 c c₁ h₁ ^ j₁).IsPrimitive := (faithful_pow_prim_iff hc₁ _ hf j₁).mpr hj₁
  have hP₂ : (omegaLow hp2 c c₁ h₁ ^ j₂).IsPrimitive := (faithful_pow_prim_iff hc₁ _ hf j₂).mpr hj₂
  exact ⟨h1, h1.trans (conv_zero_ne_iff K w c₁ hK _ _ hP₁ hP₂)⟩

end Odd

/-- **p = 2: (B2) ↔ 原点での値 ≠ 0**。 -/
theorem p2_B_iff_conv_zero {d : ℕ} (K w : ℕ) (hK : w + (d + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j') :
    (2 ^ (d + 1) ∣ j + j' ∧ Even (s + s')) ↔
      conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j')) 0 ≠ 0 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := p2_same_shell_table K w hK s j s' j' hj hj'
  simp only at hT
  rcases hT with ⟨hD, h, C, -, e⟩ | ⟨hM, hs, C, -, e⟩ | ⟨hM, hs, e⟩
  · rw [e, Pi.smul_apply, ket_apply_zero (p := 2) K _ _ (by omega) h _, smul_zero]
    exact ⟨fun hB => absurd hB.1 hD, fun h0 => absurd rfl h0⟩
  · rw [e, Pi.smul_apply, ket_apply_zero (p := 2) K _ _ (by omega) _ _, smul_zero]
    exact ⟨fun hB => absurd hB.2 (Nat.not_even_iff_odd.mpr hs), fun h0 => absurd rfl h0⟩
  · rw [e, Pi.smul_apply, ballB_apply_zero, smul_eq_mul, mul_one]
    exact ⟨fun _ => pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero), fun _ => ⟨hM, hs⟩⟩

/-- **p = 2・三つの同値**: (B2) ↔ 原点での値 ≠ 0 ↔ χ_{s',j'} = χ_{s,j}⁻¹。 -/
theorem p2_three_equiv {d : ℕ} (K w : ℕ) (hK : w + (d + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j') :
    ((2 ^ (d + 1) ∣ j + j' ∧ Even (s + s')) ↔
      conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j')) 0 ≠ 0) ∧
    ((2 ^ (d + 1) ∣ j + j' ∧ Even (s + s')) ↔ chiSJ d s' j' = (chiSJ d s j)⁻¹) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := p2_B_iff_conv_zero K w hK s j s' j' hj hj'
  exact ⟨h1, h1.trans (conv_zero_ne_iff (p := 2) K w (d + 2) hK _ _ ((chiSJ_prim_iff s j).mpr hj)
    ((chiSJ_prim_iff s' j').mpr hj'))⟩

end PAG.Part82

#print axioms PAG.Part82.conv_zero_ne_iff
#print axioms PAG.Part82.odd_B_iff_conv_zero
#print axioms PAG.Part82.odd_three_equiv
#print axioms PAG.Part82.p2_B_iff_conv_zero
#print axioms PAG.Part82.p2_three_equiv
