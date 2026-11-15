/-
  PAG 2.0 Part 70（2026-10-19）— 乗積表の「ちょうど一つ」と、法 p のケットを含む完全版
  1. 奇素数・同じ殻: (D)(L)(B) の条件はちょうど一つ成り立つ
  2. p = 2・同じ殻: (D2)(L2)(B2) の条件はちょうど一つ成り立つ
  3. 法 p のケット（c₁ = 0）同士: φ₀ ∣ j₁+j₂ なら定理 B、そうでなければ |w, 0, j₁+j₂⟩（降下なし）
  4. 混合で低いほうが法 p（c₂ = 0）: φ₀ ∤ j₂ なら PAG69 table_mixed がそのまま使える
-/
import PAG73

namespace PAG.Part74

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part47 PAG.Part48 PAG.Part61 PAG.Part62 PAG.Part67
  PAG.Part68 PAG.Part69 PAG.Part70

/-- **奇素数・同じ殻の条件はちょうど一つ**（p ∤ j₁ のとき）。 -/
theorem odd_cases_exactly_one {p : ℕ} [hp : Fact p.Prime] (c₁ j₁ j₂ : ℕ) (hc₁ : 1 ≤ c₁) (hj₁ : ¬ p ∣ j₁) :
    let ν := padicValNat p (j₁ + j₂)
    let D := ν ≤ c₁ - 1
    let L := c₁ ≤ ν ∧ ¬ phi (p := p) c₁ ∣ j₁ + j₂
    let B := phi (p := p) c₁ ∣ j₁ + j₂
    (D ∨ L ∨ B) ∧ ¬ (D ∧ L) ∧ ¬ (D ∧ B) ∧ ¬ (L ∧ B) := by
  intro ν D L B
  have hJ : j₁ + j₂ ≠ 0 := by intro h0; apply hj₁; rw [show j₁ = 0 by omega]; exact dvd_zero p
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases same_shell_cases (p := p) c₁ j₁ j₂ with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rintro ⟨hD, hL, -⟩; simp only [D, ν] at hD hL; omega
  · rintro ⟨hD, hB⟩
    have h1 : p ^ c₁ ∣ j₁ + j₂ := dvd_trans ⟨phi (p := p) 0, phi_eq c₁⟩ hB
    have h2 : c₁ ≤ ν := (padicValNat_dvd_iff_le hJ).mp h1
    simp only [D, ν] at hD h2; omega
  · rintro ⟨⟨-, hL⟩, hB⟩; exact hL hB

/-- **p = 2・同じ殻の条件はちょうど一つ**。 -/
theorem p2_cases_exactly_one (d s s' j j' : ℕ) :
    let D := ¬ 2 ^ (d + 1) ∣ j + j'
    let L := 2 ^ (d + 1) ∣ j + j' ∧ Odd (s + s')
    let B := 2 ^ (d + 1) ∣ j + j' ∧ Even (s + s')
    (D ∨ L ∨ B) ∧ ¬ (D ∧ L) ∧ ¬ (D ∧ B) ∧ ¬ (L ∧ B) := by
  intro D L B
  refine ⟨?_, fun h => h.1 h.2.1, fun h => h.1 h.2.1,
    fun h => (Nat.not_even_iff_odd.mpr h.1.2) h.2.2⟩
  by_cases hM : 2 ^ (d + 1) ∣ j + j'
  · rcases Nat.even_or_odd (s + s') with hs | hs
    · exact Or.inr (Or.inr ⟨hM, hs⟩)
    · exact Or.inr (Or.inl ⟨hM, hs⟩)
  · exact Or.inl hM

section LevelP

variable {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ)
include hp2

/-- **法 p のケット同士・定理 B**: φ₀ ∣ j₁+j₂ なら球の差。 -/
theorem levelp_B (K w : ℕ) (hK : w + (0 + 1) ≤ K) (j₁ j₂ : ℕ) (hj₁ : ¬ phi (p := p) 0 ∣ j₁)
    (hφ : phi (p := p) 0 ∣ j₁ + j₂) :
    conv (ket K w (0 + 1) hK ((omegaLow hp2 c 0 (Nat.zero_le _) ^ j₁ : DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ))
      (ket K w (0 + 1) hK ((omegaLow hp2 c 0 (Nat.zero_le _) ^ j₂ : DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ))
      = (omegaLow hp2 c 0 (Nat.zero_le _) ^ j₁) (-1) • ballB (p := p) K w 0 := by
  have : NeZero (p ^ (0 + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hf := omegaLow_isFaithful hp2 c 0 (Nat.zero_le _)
  have h1 : omegaLow hp2 c 0 (Nat.zero_le _) ^ j₁ * omegaLow hp2 c 0 (Nat.zero_le _) ^ j₂ = 1 := by
    rw [← pow_add]
    apply PAG.Part63.eq_one_of_factors_one
    have := (faithful_pow_factors_iff hp2 _ hf 0 (by omega) (j₁ + j₂)).mpr (by rw [card_ker_zero]; exact hφ)
    rwa [pow_zero] at this
  exact thmB_of_mul_eq_one K w 0 hK _ _ ((faithful_level_p_prim_iff hp2 _ hf j₁).mpr hj₁) h1

/-- **法 p のケット同士・降下なし**: φ₀ ∤ j₁+j₂ なら = C·|w, 0, j₁+j₂⟩、|C|² = λ。 -/
theorem levelp_A (K w : ℕ) (hK : w + (0 + 1) ≤ K) (j₁ j₂ : ℕ) (hj₁ : ¬ phi (p := p) 0 ∣ j₁)
    (hj₂ : ¬ phi (p := p) 0 ∣ j₂) (hφ : ¬ phi (p := p) 0 ∣ j₁ + j₂) :
    ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (0 + 1) - w) : ℝ) ∧
      conv (ket K w (0 + 1) hK ((omegaLow hp2 c 0 (Nat.zero_le _) ^ j₁ : DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ))
        (ket K w (0 + 1) hK ((omegaLow hp2 c 0 (Nat.zero_le _) ^ j₂ : DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ))
        = C • ket K w (0 + 1) hK
          ((omegaLow hp2 c 0 (Nat.zero_le _) ^ (j₁ + j₂) : DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ) := by
  have hf := omegaLow_isFaithful hp2 c 0 (Nat.zero_le _)
  have hprod : ∀ x, (omegaLow hp2 c 0 (Nat.zero_le _) ^ j₁ * omegaLow hp2 c 0 (Nat.zero_le _) ^ j₂) x
      = (omegaLow hp2 c 0 (Nat.zero_le _) ^ (j₁ + j₂))
          (ZMod.castHom (pow_dvd_pow p (le_refl (0 + 1))) _ x) := by
    intro x
    rw [← pow_add, ZMod.castHom_apply, ZMod.cast_id]
  exact thmA_with_psi K w 0 0 w (0 + 1) le_rfl hK (by omega) rfl hK _ _
    ((faithful_level_p_prim_iff hp2 _ hf j₁).mpr hj₁) ((faithful_level_p_prim_iff hp2 _ hf j₂).mpr hj₂) _
    ((faithful_level_p_prim_iff hp2 _ hf _).mpr hφ) hprod

/-- 混合で低いほうが法 p（c₂ = 0）の場合: 原始性の仮定は φ₀ ∤ j₂ と同値。 -/
theorem levelp_prim_iff (j₂ : ℕ) :
    (omegaLow hp2 c 0 (Nat.zero_le _) ^ j₂).IsPrimitive ↔ ¬ phi (p := p) 0 ∣ j₂ :=
  faithful_level_p_prim_iff hp2 _ (omegaLow_isFaithful hp2 c 0 (Nat.zero_le _)) j₂

end LevelP

end PAG.Part74

#print axioms PAG.Part74.odd_cases_exactly_one
#print axioms PAG.Part74.p2_cases_exactly_one
#print axioms PAG.Part74.levelp_B
#print axioms PAG.Part74.levelp_A
#print axioms PAG.Part74.levelp_prim_iff
