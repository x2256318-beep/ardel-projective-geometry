/-
  PAG 2.0 Part 73（2026-10-19）— 双対殻の保存則と、混合の像からの読み取り
  1. 双対殻の保存則（任意の素数）: 原始ケットの組（双対殻 a が共通）の畳み込みが
     C·|u, m, ψ⟩（ψ 原始、C は任意）と書けるなら、行き先の双対殻も a（K − m − u = a）
  2. 奇素数・混合: w₁ < w₂ なら像の殻・レベルは (w₁, c₁+1)（レベルの高いほう）
-/
import PAG76

namespace PAG.Part77

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part51 PAG.Part59 PAG.Part61 PAG.Part67
  PAG.Part68 PAG.Part69 PAG.Part73

variable {p : ℕ} [hp : Fact p.Prime]

/-- 𝓕ε_a は 1 をとる点をもつ。 -/
theorem exists_dft_eps_one (K a : ℕ) (ha : a ≤ K) :
    ∃ t, 𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) t = 1 := by
  by_contra h
  push Not at h
  apply eps_ne_zero (p := p) K a
  apply (ZMod.dft (N := p ^ K) (E := ℂ)).injective
  rw [map_zero]
  funext t
  rcases PAG.Part31.dft_eps_zero_or_one (p := p) K a ha t with h0 | h1
  · exact h0
  · exact absurd h1 (h t)

theorem lam_ne_zero (K u : ℕ) : ((p : ℂ) ^ K / (sz p K u : ℂ)) ≠ 0 := by
  have h1 : 0 < sz p K u := by
    unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
  exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) (by exact_mod_cast h1.ne')

/-- **双対殻の保存則**。 -/
theorem dual_shell_conservation (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂)
    (u n : ℕ) (hu : u + (n + 1) ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive)
    (C : ℂ)
    (hF : conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = C • ket K u (n + 1) hu ψ) :
    K - (n + 1) - u = K - (n₁ + 1) - w₁ := by
  by_contra hne
  obtain ⟨t, ht⟩ := exists_dft_eps_one (p := p) K (K - (n₁ + 1) - w₁) (by omega)
  have e := congrArg (fun f => Complex.normSq (𝓕 f t)) hF
  rw [PAG.Part16.dft_conv, Pi.mul_apply, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Complex.normSq_mul] at e
  have e1 := normSq_dft_ket_eq K w₁ n₁ h₁ χ₁ hχ₁ t
  have e2 := normSq_dft_ket_eq K w₂ n₂ h₂ χ₂ hχ₂ t
  have e3 := normSq_dft_ket_eq K u n hu ψ hψ t
  rw [ht, mul_one] at e1
  rw [← hab, ht, mul_one] at e2
  have hz := dft_eps_mul_eq_zero (p := p) K _ _ (by omega) (by omega) (Ne.symm hne) t
  rw [ht, one_mul] at hz
  rw [hz, mul_zero] at e3
  have e' : ((Complex.normSq (𝓕 (ket K w₁ (n₁ + 1) h₁ ⇑χ₁) t) *
      Complex.normSq (𝓕 (ket K w₂ (n₂ + 1) h₂ ⇑χ₂) t) : ℝ) : ℂ)
      = ((Complex.normSq C * Complex.normSq (𝓕 (ket K u (n + 1) hu ⇑ψ) t) : ℝ) : ℂ) := by
    exact_mod_cast e
  push_cast at e'
  rw [e1, e2, e3, mul_zero] at e'
  exact mul_ne_zero (lam_ne_zero (p := p) K _) (lam_ne_zero (p := p) K _) e'

variable (hp2 : p ≠ 2) (c : ℕ)
include hp2

/-- **奇素数・混合の像からの読み取り**: w₁ < w₂ なら像の殻・レベルはレベルの高いほう (w₁, c₁)。 -/
theorem odd_mixed_determines (K w₁ c₁ w₂ c₂ : ℕ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (h₁ : c₁ ≤ c) (h₂ : c₂ ≤ c)
    (hK₁ : w₁ + (c₁ + 1) ≤ K) (hK₂ : w₂ + (c₂ + 1) ≤ K) (j₁ j₂ : ℕ) (hj₁ : ¬ p ∣ j₁) (hj₂ : ¬ p ∣ j₂)
    (hw : w₁ < w₂) (hab : w₁ + c₁ = w₂ + c₂)
    (u n : ℕ) (hu : u + (n + 1) ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive) (C : ℂ)
    (hC : C ≠ 0)
    (hF : conv (ket K w₁ (c₁ + 1) hK₁ ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
      (ket K w₂ (c₂ + 1) hK₂ ((omegaLow hp2 c c₂ h₂ ^ j₂ : DirichletCharacter ℂ (p ^ (c₂ + 1))) : ZMod _ → ℂ))
      = C • ket K u (n + 1) hu ψ) :
    u = w₁ ∧ n = c₁ := by
  have hT := odd_table hp2 c K w₁ c₁ w₂ c₂ hc₁ hc₂ h₁ h₂ hK₁ hK₂ j₁ j₂ hj₁ hj₂
  simp only at hT
  rcases hT with ⟨hne, -⟩ | ⟨-, C', -, e⟩ | ⟨hw', -⟩ | ⟨hw', -⟩
  · exact absurd hab hne
  · rw [hF] at e
    have hf := omegaLow_isFaithful hp2 c c₁ h₁
    have hψ' : (omegaLow hp2 c c₁ h₁ ^ (j₁ + p ^ (c₁ - c₂) * j₂)).IsPrimitive := by
      rw [faithful_pow_prim_iff hc₁ _ hf]
      intro h
      apply hj₁
      have hpr : p ∣ p ^ (c₁ - c₂) * j₂ := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
      exact (Nat.dvd_add_right hpr).mp (by rwa [add_comm] at h)
    obtain ⟨hu', hn', -⟩ := ket_rep_unique K u (n + 1) w₁ (c₁ + 1) (by omega) (by omega) hu hK₁ ψ hψ _ hψ' C C' hC e
    exact ⟨hu', by omega⟩
  · omega
  · omega

end PAG.Part77

#print axioms PAG.Part77.exists_dft_eps_one
#print axioms PAG.Part77.lam_ne_zero
#print axioms PAG.Part77.dual_shell_conservation
#print axioms PAG.Part77.odd_mixed_determines
