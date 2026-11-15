/-
  PAG 2.0 Part 77（2026-10-19）— 原点での値 (k₁ ⋆ k₂)(0) の判定
  1. χ₁⁻¹(−1)·(k₁ ⋆ k₂)(0) = ⟨|w₁,χ₁⁻¹⟩, |w₂,χ₂⟩⟩
  2. 殻または導手が異なれば (k₁ ⋆ k₂)(0) = 0
  3. 同じ殻・同じ導手なら (k₁ ⋆ k₂)(0) = [χ₂ = χ₁⁻¹]·χ₁(−1)
  4. 系（PAG80 と合わせて）: χ₂ ≠ χ₁⁻¹ なら k₁ ⋆ k₂ の 1_{S_v}・δ₀ 成分はすべて 0
-/
import PAG80

namespace PAG.Part81

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part52 PAG.Part54 PAG.Part55 PAG.Part80

variable {p : ℕ} [hp : Fact p.Prime]

theorem conv_zero_ip (K w₁ c₁ w₂ c₂ : ℕ) (h₁ : w₁ + c₁ ≤ K) (h₂ : w₂ + c₂ ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ c₁)) (χ₂ : DirichletCharacter ℂ (p ^ c₂)) :
    χ₁⁻¹ (-1) * conv (ket K w₁ c₁ h₁ χ₁) (ket K w₂ c₂ h₂ χ₂) 0
      = ip (ket K w₁ c₁ h₁ ((χ₁⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)) (ket K w₂ c₂ h₂ χ₂) := by
  rw [ip_ket K w₁ c₁ w₂ c₂ h₁ h₂ χ₁⁻¹ χ₂, inv_inv, conv_comm]

theorem inv_neg_one {N : ℕ} (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1) := by
  have h1 := PAG.Part9.chi_neg_one_sq χ
  have h2 : χ⁻¹ (-1) * χ (-1) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply isUnit_one.neg]
  calc χ⁻¹ (-1) = χ⁻¹ (-1) * (χ (-1) * χ (-1)) := by rw [h1, mul_one]
    _ = (χ⁻¹ (-1) * χ (-1)) * χ (-1) := by ring
    _ = χ (-1) := by rw [h2, one_mul]

/-- **殻または導手が異なれば原点での値は 0**。 -/
theorem conv_zero_eq_zero_of_ne (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hne : w₁ ≠ w₂ ∨ n₁ ≠ n₂) :
    conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) 0 = 0 := by
  have e := conv_zero_ip K w₁ (n₁ + 1) w₂ (n₂ + 1) h₁ h₂ χ₁ χ₂
  rw [ip_ket_eq_zero_of_ne K w₁ n₁ w₂ n₂ h₁ h₂ _ χ₂ (PAG.Part16.isPrimitive_inv hχ₁) hχ₂ hne] at e
  exact (mul_eq_zero.mp e).resolve_left (PAG.Part75.chi_neg_one_ne_zero _)

open Classical in
/-- **同じ殻・同じ導手での原点での値**: [χ₂ = χ₁⁻¹]·χ₁(−1)。 -/
theorem conv_zero_same (K w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    conv (ket K w (n + 1) h χ₁) (ket K w (n + 1) h χ₂) 0 = if χ₂ = χ₁⁻¹ then χ₁ (-1) else 0 := by
  have e := conv_zero_ip K w (n + 1) w (n + 1) h h χ₁ χ₂
  rw [inv_neg_one] at e
  have hs := PAG.Part9.chi_neg_one_sq χ₁
  split_ifs with hc
  · subst hc
    rw [ip_ket_self K w n h _ (PAG.Part16.isPrimitive_inv hχ₁)] at e
    calc conv (ket K w (n + 1) h χ₁) (ket K w (n + 1) h (χ₁⁻¹ : DirichletCharacter ℂ _)) 0
        = χ₁ (-1) * (χ₁ (-1) * conv (ket K w (n + 1) h χ₁) (ket K w (n + 1) h (χ₁⁻¹ : DirichletCharacter ℂ _)) 0) := by
          rw [← mul_assoc, hs, one_mul]
      _ = χ₁ (-1) := by rw [e, mul_one]
  · rw [ip_ket_eq_zero_of_char_ne K w n h _ χ₂ (PAG.Part16.isPrimitive_inv hχ₁) hχ₂ (Ne.symm hc)] at e
    exact (mul_eq_zero.mp e).resolve_left (PAG.Part75.chi_neg_one_ne_zero _)

open Classical in
/-- **系**: χ₂ ≠ χ₁⁻¹（同じ殻・導手）なら、k₁ ⋆ k₂ の 1_{S_v}・δ₀ 成分はすべて 0。 -/
theorem ind_components_zero_same (K w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (hc : χ₂ ≠ χ₁⁻¹) :
    ip (Pi.single (0 : ZMod (p ^ K)) (1 : ℂ)) (conv (ket K w (n + 1) h χ₁) (ket K w (n + 1) h χ₂)) = 0 ∧
    ∀ v (hv : v < K), ip (shellInd (p := p) K v hv) (conv (ket K w (n + 1) h χ₁) (ket K w (n + 1) h χ₂)) = 0 :=
  ip_ind_conv_zero K w n h χ₁ hχ₁ _ (by rw [conv_zero_same K w n h χ₁ χ₂ hχ₁ hχ₂, ite_eq_right_of_eq_false _ _ (eq_false hc)])

/-- **系**: 殻または導手が異なる組でも、1_{S_v}・δ₀ 成分はすべて 0。 -/
theorem ind_components_zero_ne (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hne : w₁ ≠ w₂ ∨ n₁ ≠ n₂) :
    ip (Pi.single (0 : ZMod (p ^ K)) (1 : ℂ)) (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂)) = 0 ∧
    ∀ v (hv : v < K), ip (shellInd (p := p) K v hv)
      (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂)) = 0 :=
  ip_ind_conv_zero K w₁ n₁ h₁ χ₁ hχ₁ _ (conv_zero_eq_zero_of_ne K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hne)

end PAG.Part81

#print axioms PAG.Part81.conv_zero_ip
#print axioms PAG.Part81.inv_neg_one
#print axioms PAG.Part81.conv_zero_eq_zero_of_ne
#print axioms PAG.Part81.conv_zero_same
#print axioms PAG.Part81.ind_components_zero_same
#print axioms PAG.Part81.ind_components_zero_ne
