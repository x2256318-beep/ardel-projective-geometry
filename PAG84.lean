/-
  PAG 2.0 Part 80（2026-10-19）— χ₄ どうしの積と、法 p のケットの三つの同値
  1. χ₄·χ₄ = 1、χ₄⁻¹ = χ₄
  2. |w, χ₄⟩ ⋆ |w, χ₄⟩ = −ballB(K, w, 1)（定理 B、p = 2・レベル 2）
  3. 奇素数・法 p のケット（ω^j、レベル 1）: φ(p) ∣ j₁+j₂ ↔ (k₁⋆k₂)(0) ≠ 0 ↔ ω^{j₂} = (ω^{j₁})⁻¹
-/
import PAG83

namespace PAG.Part84

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part47 PAG.Part48 PAG.Part49 PAG.Part61 PAG.Part67 PAG.Part68
  PAG.Part69 PAG.Part72 PAG.Part82

theorem chi4_mul_self : chi4 * chi4 = 1 := by
  apply MulChar.ext
  intro u
  rcases units_four u with rfl | rfl
  · simp
  · rw [MulChar.mul_apply, MulChar.one_apply_coe, Units.val_neg, Units.val_one, chi4_neg_one]; norm_num

theorem chi4_inv : chi4⁻¹ = chi4 := (eq_inv_of_mul_eq_one_right chi4_mul_self).symm

/-- **χ₄ どうしの積（定理 B）**。 -/
theorem chi4_conv_self (K w : ℕ) (hK : w + (1 + 1) ≤ K) :
    conv (ket (p := 2) K w (1 + 1) hK chi4) (ket (p := 2) K w (1 + 1) hK chi4) = (-1 : ℂ) • ballB (p := 2) K w 1 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← chi4_neg_one]
  exact thmB_of_mul_eq_one (p := 2) K w 1 hK chi4 chi4 chi4_prim chi4_mul_self

/-- χ₄ どうしの積の原点での値は −1（≠ 0）。 -/
theorem chi4_conv_self_zero (K w : ℕ) (hK : w + (1 + 1) ≤ K) :
    conv (ket (p := 2) K w (1 + 1) hK chi4) (ket (p := 2) K w (1 + 1) hK chi4) 0 = -1 := by
  rw [chi4_conv_self, Pi.smul_apply, ballB_apply_zero, smul_eq_mul, mul_one]

section LevelP
variable {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ)
include hp2

/-- **奇素数・法 p のケットの三つの同値**。 -/
theorem levelp_three_equiv (K w : ℕ) (hK : w + (0 + 1) ≤ K) (j₁ j₂ : ℕ) (hj₁ : ¬ phi (p := p) 0 ∣ j₁)
    (hj₂ : ¬ phi (p := p) 0 ∣ j₂) :
    (phi (p := p) 0 ∣ j₁ + j₂ ↔
      conv (ket K w (0 + 1) hK ((omegaLow hp2 c 0 (Nat.zero_le _) ^ j₁ : DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ))
        (ket K w (0 + 1) hK ((omegaLow hp2 c 0 (Nat.zero_le _) ^ j₂ : DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ))
        0 ≠ 0) ∧
    (phi (p := p) 0 ∣ j₁ + j₂ ↔
      omegaLow hp2 c 0 (Nat.zero_le _) ^ j₂ = (omegaLow hp2 c 0 (Nat.zero_le _) ^ j₁)⁻¹) := by
  have hP₁ := (PAG.Part74.levelp_prim_iff hp2 c j₁).mpr hj₁
  have hP₂ := (PAG.Part74.levelp_prim_iff hp2 c j₂).mpr hj₂
  have h1 : phi (p := p) 0 ∣ j₁ + j₂ ↔
      conv (ket K w (0 + 1) hK ((omegaLow hp2 c 0 (Nat.zero_le _) ^ j₁ : DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ))
        (ket K w (0 + 1) hK ((omegaLow hp2 c 0 (Nat.zero_le _) ^ j₂ : DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ))
        0 ≠ 0 := by
    constructor
    · intro hφ
      rw [PAG.Part74.levelp_B hp2 c K w hK j₁ j₂ hj₁ hφ, Pi.smul_apply, ballB_apply_zero, smul_eq_mul, mul_one]
      exact PAG.Part75.chi_neg_one_ne_zero _
    · intro h0
      by_contra hφ
      obtain ⟨C, -, e⟩ := PAG.Part74.levelp_A hp2 c K w hK j₁ j₂ hj₁ hj₂ hφ
      rw [e, Pi.smul_apply, ket_apply_zero K w (0 + 1) (by omega) hK _, smul_zero] at h0
      exact h0 rfl
  exact ⟨h1, h1.trans (conv_zero_ne_iff K w 0 hK _ _ hP₁ hP₂)⟩

end LevelP

end PAG.Part84

#print axioms PAG.Part84.chi4_mul_self
#print axioms PAG.Part84.chi4_inv
#print axioms PAG.Part84.chi4_conv_self
#print axioms PAG.Part84.chi4_conv_self_zero
#print axioms PAG.Part84.levelp_three_equiv
