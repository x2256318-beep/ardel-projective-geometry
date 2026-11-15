/-
  PAG 2.0 Part 69（2026-10-19）— 乗積表を一つの選言として述べる
  1. 奇素数・同じ殻: (D) ∨ (L) ∨ (B)
  2. 奇素数・全体: (0) ∨ (M) ∨ (M') ∨ (同じ殻・同じレベル)
  3. p = 2・同じ殻: (D2) ∨ (L2) ∨ (B2)
-/
import PAG72

namespace PAG.Part73

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part48 PAG.Part61 PAG.Part67 PAG.Part68
  PAG.Part69 PAG.Part70 PAG.Part71 PAG.Part72

section Odd

variable {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ)
include hp2

/-- **奇素数・同じ殻の乗積表（一つの選言）**。 -/
theorem odd_same_shell_table (K w c₁ : ℕ) (hc₁ : 1 ≤ c₁) (h₁ : c₁ ≤ c) (hK : w + (c₁ + 1) ≤ K) (j₁ j₂ : ℕ)
    (hj₁ : ¬ p ∣ j₁) (hj₂ : ¬ p ∣ j₂) :
    let F := conv (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
      (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₂ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
    let ν := padicValNat p (j₁ + j₂)
    let lam := (p : ℝ) ^ K / (sz p K (K - (c₁ + 1) - w) : ℝ)
    (ν ≤ c₁ - 1 ∧ ∃ h : w + ν + (c₁ - ν + 1) ≤ K, ∃ C : ℂ, Complex.normSq C = lam ∧
      F = C • ket K (w + ν) (c₁ - ν + 1) h
        ((omegaLow hp2 c (c₁ - ν) (by omega) ^ ((j₁ + j₂) / p ^ ν) :
          DirichletCharacter ℂ (p ^ (c₁ - ν + 1))) : ZMod _ → ℂ)) ∨
    (c₁ ≤ ν ∧ ¬ phi (p := p) c₁ ∣ j₁ + j₂ ∧ ∃ h : w + c₁ + (0 + 1) ≤ K, ∃ C : ℂ, Complex.normSq C = lam ∧
      F = C • ket K (w + c₁) (0 + 1) h
        ((omegaLow hp2 c 0 (Nat.zero_le _) ^ ((j₁ + j₂) / p ^ c₁) :
          DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ)) ∨
    (phi (p := p) c₁ ∣ j₁ + j₂ ∧ F = (omegaLow hp2 c c₁ h₁ ^ j₁) (-1) • ballB (p := p) K w c₁) := by
  intro F ν lam
  rcases same_shell_cases (p := p) c₁ j₁ j₂ with hB | hD | ⟨hL, hφ⟩
  · exact Or.inr (Or.inr ⟨hB, table_B hp2 c K w c₁ hc₁ h₁ hK j₁ j₂ hj₁ hB⟩)
  · exact Or.inl ⟨hD, by omega, table_descent hp2 c K w c₁ hc₁ h₁ hK j₁ j₂ hj₁ hj₂ hD (by omega)⟩
  · exact Or.inr (Or.inl ⟨hL, hφ, by omega, table_bottom hp2 c K w c₁ hc₁ h₁ hK j₁ j₂ hj₁ hj₂ hL hφ (by omega)⟩)

/-- **奇素数・全体の乗積表（一つの選言）**: (0) ∨ (M) ∨ (M') ∨ (同じ殻・同じレベル)。 -/
theorem odd_table (K w₁ c₁ w₂ c₂ : ℕ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (h₁ : c₁ ≤ c) (h₂ : c₂ ≤ c)
    (hK₁ : w₁ + (c₁ + 1) ≤ K) (hK₂ : w₂ + (c₂ + 1) ≤ K) (j₁ j₂ : ℕ) (hj₁ : ¬ p ∣ j₁) (hj₂ : ¬ p ∣ j₂) :
    let F := conv (ket K w₁ (c₁ + 1) hK₁ ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
      (ket K w₂ (c₂ + 1) hK₂ ((omegaLow hp2 c c₂ h₂ ^ j₂ : DirichletCharacter ℂ (p ^ (c₂ + 1))) : ZMod _ → ℂ))
    (w₁ + c₁ ≠ w₂ + c₂ ∧ F = 0) ∨
    (w₁ < w₂ ∧ ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (c₁ + 1) - w₁) : ℝ) ∧
      F = C • ket K w₁ (c₁ + 1) hK₁
        ((omegaLow hp2 c c₁ h₁ ^ (j₁ + p ^ (c₁ - c₂) * j₂) : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ)) ∨
    (w₂ < w₁ ∧ ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (c₂ + 1) - w₂) : ℝ) ∧
      F = C • ket K w₂ (c₂ + 1) hK₂
        ((omegaLow hp2 c c₂ h₂ ^ (j₂ + p ^ (c₂ - c₁) * j₁) : DirichletCharacter ℂ (p ^ (c₂ + 1))) : ZMod _ → ℂ)) ∨
    (w₁ = w₂ ∧ c₁ = c₂) := by
  intro F
  by_cases hab : w₁ + c₁ = w₂ + c₂
  swap
  · left
    exact ⟨hab, table_zero hp2 c K w₁ c₁ w₂ c₂ hc₁ hc₂ h₁ h₂ hK₁ hK₂ j₁ j₂ hj₁ hj₂ (by omega)⟩
  rcases lt_trichotomy w₁ w₂ with hw | hw | hw
  · right; left
    refine ⟨hw, ?_⟩
    obtain rfl : w₂ = w₁ + (c₁ - c₂) := by omega
    exact table_mixed hp2 c K w₁ c₁ c₂ hc₁ (by omega) h₁ hK₁ hK₂ j₁ j₂ hj₁
      ((faithful_pow_prim_iff hc₂ _ (omegaLow_isFaithful hp2 c c₂ h₂) j₂).mpr hj₂)
  · right; right; right
    exact ⟨hw, by omega⟩
  · right; right; left
    refine ⟨hw, ?_⟩
    obtain rfl : w₁ = w₂ + (c₂ - c₁) := by omega
    obtain ⟨C, hC, hconv⟩ := table_mixed hp2 c K w₂ c₂ c₁ hc₂ (by omega) h₂ hK₂ hK₁ j₂ j₁ hj₂
      ((faithful_pow_prim_iff hc₁ _ (omegaLow_isFaithful hp2 c c₁ h₁) j₁).mpr hj₁)
    exact ⟨C, hC, by rw [show F = _ from conv_comm _ _]; exact hconv⟩

end Odd

/-- **p = 2・同じ殻の乗積表（一つの選言）**。 -/
theorem p2_same_shell_table {d : ℕ} (K w : ℕ) (hK : w + (d + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j') :
    let F := conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j'))
    let ν := padicValNat 2 (j + j')
    let lam := (2 : ℝ) ^ K / (sz 2 K (K - (d + 3) - w) : ℝ)
    (¬ 2 ^ (d + 1) ∣ j + j' ∧ ∃ h : w + ν + (d - ν + 3) ≤ K, ∃ C : ℂ, Complex.normSq C = lam ∧
      F = C • ket (p := 2) K (w + ν) (d - ν + 3) h (chiSJ (d - ν) (s + s') ((j + j') / 2 ^ ν))) ∨
    (2 ^ (d + 1) ∣ j + j' ∧ Odd (s + s') ∧ ∃ C : ℂ, Complex.normSq C = lam ∧
      F = C • ket (p := 2) K (w + (d + 1)) 2 (by omega) chi4) ∨
    (2 ^ (d + 1) ∣ j + j' ∧ Even (s + s') ∧ F = ((-1 : ℂ) ^ s) • ballB (p := 2) K w (d + 2)) := by
  intro F ν lam
  by_cases hM : 2 ^ (d + 1) ∣ j + j'
  · rcases Nat.even_or_odd (s + s') with hs | hs
    · exact Or.inr (Or.inr ⟨hM, hs, PAG.Part50.p2_caseB K w hK s j s' j' hj hs hM⟩)
    · exact Or.inr (Or.inl ⟨hM, hs, p2_table_bottom K w hK s j s' j' hj hj' hs hM⟩)
  · left
    have hJ : j + j' ≠ 0 := by have := hj.pos; omega
    have hν1 : 1 ≤ ν := by
      rcases Nat.eq_zero_or_pos ν with h0 | h0
      · exfalso
        have := pow_succ_padicValNat_not_dvd (p := 2) hJ
        rw [show padicValNat 2 (j + j') = 0 from h0, zero_add, pow_one] at this
        exact this (even_iff_two_dvd.mp (hj.add_odd hj'))
      · exact h0
    have hνd : ν ≤ d := by
      by_contra hlt
      exact hM (dvd_trans (pow_dvd_pow 2 (by omega)) pow_padicValNat_dvd)
    exact ⟨hM, by omega, p2_table_descent K w d hK s j s' j' hj hj' hν1 hνd (by omega)⟩

end PAG.Part73

#print axioms PAG.Part73.odd_same_shell_table
#print axioms PAG.Part73.odd_table
#print axioms PAG.Part73.p2_same_shell_table
