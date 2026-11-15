/-
  PAG 2.0 Part 66（2026-10-19）— 乗積表の最下段（導手 p への降下）の添字表示
  1. 法 p（c' = 0）の忠実な指標 χ について χ^q 原始 ⇔ φ_0 ∤ q
  2. φ_{c₁} = p^{c₁}·φ_0
  3. (L) 同じ殻・ν_p(j₁+j₂) ≥ c₁・φ_{c₁} ∤ j₁+j₂ なら
        |w,c₁,j₁⟩ ⋆ |w,c₁,j₂⟩ = C·|w+c₁, 0, (j₁+j₂)/p^{c₁}⟩、|C|² = λ
  これで PAG69 と合わせ、塔の上の原始ケットの乗積表が (0)(M)(D)(L)(B) で完結する。
-/
import PAG69

namespace PAG.Part70

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part61 PAG.Part62 PAG.Part67 PAG.Part68 PAG.Part69

variable {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
include hp2

/-- **法 p の忠実な指標**: χ^q 原始 ⇔ φ_0 ∤ q。 -/
theorem faithful_level_p_prim_iff (χ : DirichletCharacter ℂ (p ^ (0 + 1))) (hχ : Faithful χ) (q : ℕ) :
    (χ ^ q).IsPrimitive ↔ ¬ phi (p := p) 0 ∣ q := by
  rw [DirichletCharacter.isPrimitive_def]
  change _ = p ^ 1 ↔ _
  rw [faithful_pow_conductor_p_iff hp2 χ hχ q, pow_zero]
  exact ⟨fun h => h.2, fun h => ⟨one_dvd _, h⟩⟩

omit hp2 in
/-- φ_{c₁} = p^{c₁}·φ_0。 -/
theorem phi_eq (c₁ : ℕ) : phi (p := p) c₁ = p ^ c₁ * phi (p := p) 0 := by
  have h1 := phi_div (p := p) c₁ 0 (Nat.zero_le _)
  have h2 := Nat.div_mul_cancel (phi_dvd (p := p) c₁ 0 (Nat.zero_le _))
  rw [h1, Nat.sub_zero] at h2
  exact h2.symm

/-- (L) **最下段**: ν ≥ c₁、φ_{c₁} ∤ j₁+j₂ なら = C·|w+c₁, 0, (j₁+j₂)/p^{c₁}⟩。 -/
theorem table_bottom (c K w c₁ : ℕ) (hc₁ : 1 ≤ c₁) (h₁ : c₁ ≤ c) (hK : w + (c₁ + 1) ≤ K) (j₁ j₂ : ℕ)
    (hj₁ : ¬ p ∣ j₁) (hj₂ : ¬ p ∣ j₂) (hν : c₁ ≤ padicValNat p (j₁ + j₂)) (hφ : ¬ phi (p := p) c₁ ∣ j₁ + j₂)
    (hK' : w + c₁ + (0 + 1) ≤ K) :
    ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (c₁ + 1) - w) : ℝ) ∧
      conv (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
        (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₂ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
        = C • ket K (w + c₁) (0 + 1) hK'
          ((omegaLow hp2 c 0 (Nat.zero_le _) ^ ((j₁ + j₂) / p ^ c₁) :
            DirichletCharacter ℂ (p ^ (0 + 1))) : ZMod _ → ℂ) := by
  have hdvd : p ^ c₁ ∣ j₁ + j₂ := dvd_trans (pow_dvd_pow p hν) pow_padicValNat_dvd
  set q := (j₁ + j₂) / p ^ c₁ with hqdef
  have hJq : j₁ + j₂ = p ^ c₁ * q := (Nat.mul_div_cancel' hdvd).symm
  have hf := omegaLow_isFaithful hp2 c c₁ h₁
  have hf0 := omegaLow_isFaithful hp2 c 0 (Nat.zero_le _)
  have hψ : (omegaLow hp2 c 0 (Nat.zero_le _) ^ q).IsPrimitive := by
    rw [faithful_level_p_prim_iff hp2 _ hf0]
    intro hq
    apply hφ
    rw [phi_eq c₁, hJq]
    exact Nat.mul_dvd_mul_left _ hq
  have hprod : ∀ x, (omegaLow hp2 c c₁ h₁ ^ j₁ * omegaLow hp2 c c₁ h₁ ^ j₂) x
      = (omegaLow hp2 c 0 (Nat.zero_le _) ^ q)
          (ZMod.castHom (pow_dvd_pow p (by omega : 0 + 1 ≤ c₁ + 1)) _ x) := by
    intro x
    rw [← pow_add (omegaLow hp2 c c₁ h₁) j₁ j₂, hJq, pow_mul]
    have ht := tower_compat hp2 c c₁ 0 (Nat.zero_le _) h₁
    rw [Nat.sub_zero] at ht
    rw [← ht, ← map_pow, PAG.Part47.changeLevel_apply_cast (by omega) (by omega)]
  exact thmA_with_psi K w c₁ c₁ (w + c₁) (0 + 1) le_rfl hK rfl (by omega) hK' _ _
    ((faithful_pow_prim_iff hc₁ _ hf j₁).mpr hj₁) ((faithful_pow_prim_iff hc₁ _ hf j₂).mpr hj₂) _ hψ hprod

omit hp2 in
/-- 同じ殻の場合分けの網羅性: (B)・(D)・(L) のどれかの条件が成り立つ。 -/
theorem same_shell_cases (c₁ j₁ j₂ : ℕ) :
    phi (p := p) c₁ ∣ j₁ + j₂ ∨ padicValNat p (j₁ + j₂) ≤ c₁ - 1 ∨
      (c₁ ≤ padicValNat p (j₁ + j₂) ∧ ¬ phi (p := p) c₁ ∣ j₁ + j₂) := by
  by_cases h : phi (p := p) c₁ ∣ j₁ + j₂
  · exact Or.inl h
  · by_cases h2 : padicValNat p (j₁ + j₂) ≤ c₁ - 1
    · exact Or.inr (Or.inl h2)
    · right; right
      exact ⟨by omega, h⟩

end PAG.Part70

#print axioms PAG.Part70.faithful_level_p_prim_iff
#print axioms PAG.Part70.phi_eq
#print axioms PAG.Part70.table_bottom
#print axioms PAG.Part70.same_shell_cases
