/-
  PAG 2.0 Part 71（2026-10-19）— 乗積表の結論のレベルでの排他性（場合は像そのものから決まる）
  1. ケットの定数倍と球の差の 0 でない定数倍は一致しない（原点での値）
  2. 奇素数・同じ殻: 像 F が C·|u, m, ψ⟩（C ≠ 0、ψ 原始）と書けるなら
       φ ∤ j₁+j₂（(B) ではない）かつ u = w + min(ν, c₁)、m = c₁ + 1 − min(ν, c₁)
     すなわち像の殻とレベルから場合（降下量）が読み取れる
  3. (B) の像はケットの定数倍ではない
-/
import PAG74

namespace PAG.Part75

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part48 PAG.Part49 PAG.Part51 PAG.Part61 PAG.Part67
  PAG.Part68 PAG.Part73

variable {p : ℕ} [hp : Fact p.Prime]

/-- ケットの定数倍は球の差の 0 でない定数倍ではない。 -/
theorem ket_ne_ballB (K u m w n : ℕ) (hm : 1 ≤ m) (h : u + m ≤ K) (ψ : DirichletCharacter ℂ (p ^ m)) (C a : ℂ)
    (ha : a ≠ 0) : C • ket K u m h ψ ≠ a • ballB (p := p) K w n := by
  intro e
  have e0 := congrFun e 0
  rw [Pi.smul_apply, Pi.smul_apply, ket_apply_zero K u m hm h ψ, ballB_apply_zero, smul_eq_mul, smul_eq_mul,
    mul_zero, mul_one] at e0
  exact ha e0.symm

theorem chi_neg_one_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) : χ (-1) ≠ 0 := by
  intro h
  have := PAG.Part9.chi_neg_one_sq χ
  rw [h, mul_zero] at this
  exact zero_ne_one this

variable (hp2 : p ≠ 2) (c : ℕ)
include hp2

/-- **像から場合が決まる（奇素数・同じ殻）**。 -/
theorem odd_outcome_determines (K w c₁ : ℕ) (hc₁ : 1 ≤ c₁) (h₁ : c₁ ≤ c) (hK : w + (c₁ + 1) ≤ K) (j₁ j₂ : ℕ)
    (hj₁ : ¬ p ∣ j₁) (hj₂ : ¬ p ∣ j₂)
    (u m : ℕ) (hm : 1 ≤ m) (hu : u + m ≤ K) (ψ : DirichletCharacter ℂ (p ^ m)) (hψ : ψ.IsPrimitive) (C : ℂ) (hC : C ≠ 0)
    (hF : conv (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
      (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₂ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
      = C • ket K u m hu ψ) :
    ¬ phi (p := p) c₁ ∣ j₁ + j₂ ∧
      u = w + min (padicValNat p (j₁ + j₂)) c₁ ∧ m = c₁ + 1 - min (padicValNat p (j₁ + j₂)) c₁ := by
  have hT := odd_same_shell_table hp2 c K w c₁ hc₁ h₁ hK j₁ j₂ hj₁ hj₂
  simp only at hT
  rcases hT with ⟨hD, h, C', hC', e⟩ | ⟨hL, hφ, h, C', hC', e⟩ | ⟨hB, e⟩
  · rw [hF] at e
    have hψ' := (faithful_pow_prim_iff (c := c₁ - padicValNat p (j₁ + j₂)) (by omega) _
      (omegaLow_isFaithful hp2 c _ (by omega)) ((j₁ + j₂) / p ^ padicValNat p (j₁ + j₂))).mpr (by
        intro hq
        have hJ : j₁ + j₂ ≠ 0 := by intro h0; apply hj₁; rw [show j₁ = 0 by omega]; exact dvd_zero p
        apply pow_succ_padicValNat_not_dvd (p := p) hJ
        have hJq := (Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := j₁ + j₂))).symm
        have key : p ^ (padicValNat p (j₁ + j₂) + 1) ∣
            p ^ padicValNat p (j₁ + j₂) * ((j₁ + j₂) / p ^ padicValNat p (j₁ + j₂)) := by
          rw [pow_succ]; exact Nat.mul_dvd_mul_left _ hq
        exact dvd_trans key (dvd_of_eq hJq.symm))
    obtain ⟨hu', hm', -⟩ := ket_rep_unique K u m _ _ hm (by omega) hu h ψ hψ _ hψ' C C' hC e
    have hφ : ¬ phi (p := p) c₁ ∣ j₁ + j₂ := by
      intro hB
      exact ((PAG.Part74.odd_cases_exactly_one c₁ j₁ j₂ hc₁ hj₁).2.2.1) ⟨hD, hB⟩
    refine ⟨hφ, ?_, ?_⟩
    · rw [hu', min_eq_left (by omega)]
    · rw [hm', min_eq_left (by omega)]; omega
  · rw [hF] at e
    have hψ' := (PAG.Part70.faithful_level_p_prim_iff hp2 _ (omegaLow_isFaithful hp2 c 0 (Nat.zero_le _))
      ((j₁ + j₂) / p ^ c₁)).mpr (by
        intro hq
        apply hφ
        have hdvd : p ^ c₁ ∣ j₁ + j₂ := dvd_trans (pow_dvd_pow p hL) pow_padicValNat_dvd
        rw [PAG.Part70.phi_eq c₁, ← Nat.mul_div_cancel' hdvd]
        exact Nat.mul_dvd_mul_left _ hq)
    obtain ⟨hu', hm', -⟩ := ket_rep_unique K u m _ _ hm (by omega) hu h ψ hψ _ hψ' C C' hC e
    refine ⟨hφ, ?_, ?_⟩
    · rw [hu', min_eq_right hL]
    · rw [hm', min_eq_right hL]; omega
  · exfalso
    rw [hF] at e
    exact ket_ne_ballB K u m w c₁ hm hu ψ C _ (chi_neg_one_ne_zero _) e

/-- **(B) の像はケットの定数倍ではない**。 -/
theorem odd_B_not_ket (K w c₁ : ℕ) (hc₁ : 1 ≤ c₁) (h₁ : c₁ ≤ c) (hK : w + (c₁ + 1) ≤ K) (j₁ j₂ : ℕ)
    (hj₁ : ¬ p ∣ j₁) (hφ : phi (p := p) c₁ ∣ j₁ + j₂)
    (u m : ℕ) (hm : 1 ≤ m) (hu : u + m ≤ K) (ψ : DirichletCharacter ℂ (p ^ m)) (C : ℂ) :
    conv (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
      (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₂ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
      ≠ C • ket K u m hu ψ := by
  rw [PAG.Part69.table_B hp2 c K w c₁ hc₁ h₁ hK j₁ j₂ hj₁ hφ]
  exact fun e => ket_ne_ballB K u m w c₁ hm hu ψ C _ (chi_neg_one_ne_zero _) e.symm

end PAG.Part75

#print axioms PAG.Part75.ket_ne_ballB
#print axioms PAG.Part75.chi_neg_one_ne_zero
#print axioms PAG.Part75.odd_outcome_determines
#print axioms PAG.Part75.odd_B_not_ket
