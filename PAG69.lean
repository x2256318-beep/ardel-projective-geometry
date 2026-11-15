/-
  PAG 2.0 Part 65（2026-10-19）— 生成元指標の塔による乗積表（奇素数）
  最上段 p^(c+1) を固定し、各レベル c' ≤ c の生成元指標 W_{c'} := ω''_{c'}（PAG67・68）で
  ケット |w, c', j⟩ := |w, (W_{c'})^j⟩（導手 p^(c'+1)）を考える。
  (0) 双対殻が異なれば 0
  (M) 混合 w₂ = w₁ + (c₁−c₂)：|w₁,c₁,j₁⟩ ⋆ |w₂,c₂,j₂⟩ = C·|w₁, c₁, j₁ + p^(c₁−c₂) j₂⟩
  (D) 同じ殻・ν = ν_p(j₁+j₂) ≤ c₁−1：= C·|w+ν, c₁−ν, (j₁+j₂)/p^ν⟩
  (B) 同じ殻・φ_{c₁} ∣ j₁+j₂：= W_{c₁}^{j₁}(−1)·ballB
  いずれも |C|² = λ。
-/
import PAG68

namespace PAG.Part69

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part40 PAG.Part47 PAG.Part48 PAG.Part61 PAG.Part62
  PAG.Part67 PAG.Part68

variable {p : ℕ} [hp : Fact p.Prime]

/-- 定理 A の一般形（行き先の ψ・殻・法を変数で）。 -/
theorem thmA_with_psi (K w n v u m : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K) (hu : u = w + v)
    (hm : n + 1 - v = m) (huK : u + m ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ m)) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (by omega : m ≤ n + 1)) _ x)) :
    ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
      conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂) = C • ket K u m huK ψ := by
  subst hu; subst hm
  have hA := thmA_ket K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod
  refine ⟨_, ?_, hA⟩
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact normSq_coef_of _ _ _ _ hA (norm_ket' K (w + v) (n + 1 - v) (by omega) _ ψ hψ)
    (thmA_norm K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod)

variable (hp2 : p ≠ 2) (c : ℕ)
include hp2

/-- (0) 双対殻が異なれば 0。 -/
theorem table_zero (K w₁ c₁ w₂ c₂ : ℕ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (h₁ : c₁ ≤ c) (h₂ : c₂ ≤ c)
    (hK₁ : w₁ + (c₁ + 1) ≤ K) (hK₂ : w₂ + (c₂ + 1) ≤ K) (j₁ j₂ : ℕ) (hj₁ : ¬ p ∣ j₁) (hj₂ : ¬ p ∣ j₂)
    (hab : K - (c₁ + 1) - w₁ ≠ K - (c₂ + 1) - w₂) :
    conv (ket K w₁ (c₁ + 1) hK₁ ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
      (ket K w₂ (c₂ + 1) hK₂ ((omegaLow hp2 c c₂ h₂ ^ j₂ : DirichletCharacter ℂ (p ^ (c₂ + 1))) : ZMod _ → ℂ)) = 0 :=
  PAG.Part41.conv_ket_eq_zero K w₁ c₁ w₂ c₂ hK₁ hK₂ _ _
    ((faithful_pow_prim_iff hc₁ _ (omegaLow_isFaithful hp2 c c₁ h₁) j₁).mpr hj₁)
    ((faithful_pow_prim_iff hc₂ _ (omegaLow_isFaithful hp2 c c₂ h₂) j₂).mpr hj₂) hab

/-- (M) **混合**: |w₁,c₁,j₁⟩ ⋆ |w₁+(c₁−c₂),c₂,j₂⟩ = C·|w₁, c₁, j₁ + p^(c₁−c₂) j₂⟩。 -/
theorem table_mixed (K w₁ c₁ c₂ : ℕ) (hc₁ : 1 ≤ c₁) (hlt : c₂ < c₁) (h₁ : c₁ ≤ c)
    (hK₁ : w₁ + (c₁ + 1) ≤ K) (hK₂ : w₁ + (c₁ - c₂) + (c₂ + 1) ≤ K) (j₁ j₂ : ℕ) (hj₁ : ¬ p ∣ j₁)
    (hψ₂ : (omegaLow hp2 c c₂ (by omega) ^ j₂).IsPrimitive) :
    ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (c₁ + 1) - w₁) : ℝ) ∧
      conv (ket K w₁ (c₁ + 1) hK₁ ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
        (ket K (w₁ + (c₁ - c₂)) (c₂ + 1) hK₂
          ((omegaLow hp2 c c₂ (by omega) ^ j₂ : DirichletCharacter ℂ (p ^ (c₂ + 1))) : ZMod _ → ℂ))
        = C • ket K w₁ (c₁ + 1) hK₁
          ((omegaLow hp2 c c₁ h₁ ^ (j₁ + p ^ (c₁ - c₂) * j₂) : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ) := by
  have hf := omegaLow_isFaithful hp2 c c₁ h₁
  have hχ₁ := (faithful_pow_prim_iff hc₁ _ hf j₁).mpr hj₁
  have hψ : (omegaLow hp2 c c₁ h₁ ^ (j₁ + p ^ (c₁ - c₂) * j₂)).IsPrimitive := by
    rw [faithful_pow_prim_iff hc₁ _ hf]
    intro h
    apply hj₁
    have hpr : p ∣ p ^ (c₁ - c₂) * j₂ := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
    exact (Nat.dvd_add_right hpr).mp (by rwa [add_comm] at h)
  have hprod : ∀ x, (omegaLow hp2 c c₁ h₁ ^ (j₁ + p ^ (c₁ - c₂) * j₂)) x
      = (omegaLow hp2 c c₁ h₁ ^ j₁) x * (omegaLow hp2 c c₂ (by omega) ^ j₂)
          (ZMod.castHom (pow_dvd_pow p (by omega : c₂ + 1 ≤ c₁ + 1)) _ x) := by
    intro x
    rw [pow_add (omegaLow hp2 c c₁ h₁) j₁ (p ^ (c₁ - c₂) * j₂), MulChar.coeToFun_mul, Pi.mul_apply, pow_mul,
      ← tower_compat hp2 c c₁ c₂ hlt.le h₁, ← map_pow, changeLevel_apply_cast (by omega) (by omega)]
  exact PAG.Part65.mixed_general_psi K w₁ c₁ (c₁ - c₂) (w₁ + (c₁ - c₂)) (c₂ + 1) (by omega) hK₁ rfl (by omega) hK₂
    _ hχ₁ _ hψ₂ _ hψ hprod

/-- (D) **同じ殻・降下**: ν = ν_p(j₁+j₂) ≤ c₁−1 なら = C·|w+ν, c₁−ν, (j₁+j₂)/p^ν⟩。 -/
theorem table_descent (K w c₁ : ℕ) (hc₁ : 1 ≤ c₁) (h₁ : c₁ ≤ c) (hK : w + (c₁ + 1) ≤ K) (j₁ j₂ : ℕ)
    (hj₁ : ¬ p ∣ j₁) (hj₂ : ¬ p ∣ j₂) (hν : padicValNat p (j₁ + j₂) ≤ c₁ - 1)
    (hK' : w + padicValNat p (j₁ + j₂) + (c₁ - padicValNat p (j₁ + j₂) + 1) ≤ K) :
    ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (c₁ + 1) - w) : ℝ) ∧
      conv (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
        (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₂ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
        = C • ket K (w + padicValNat p (j₁ + j₂)) (c₁ - padicValNat p (j₁ + j₂) + 1) hK'
          ((omegaLow hp2 c (c₁ - padicValNat p (j₁ + j₂)) (by omega) ^ ((j₁ + j₂) / p ^ padicValNat p (j₁ + j₂)) :
            DirichletCharacter ℂ (p ^ (c₁ - padicValNat p (j₁ + j₂) + 1))) : ZMod _ → ℂ) := by
  set ν := padicValNat p (j₁ + j₂) with hνdef
  have hJ : j₁ + j₂ ≠ 0 := by intro h0; apply hj₁; rw [show j₁ = 0 by omega]; exact dvd_zero p
  have hdvd : p ^ ν ∣ j₁ + j₂ := pow_padicValNat_dvd
  have hndvd : ¬ p ^ (ν + 1) ∣ j₁ + j₂ := pow_succ_padicValNat_not_dvd hJ
  set q := (j₁ + j₂) / p ^ ν with hqdef
  have hJq : j₁ + j₂ = p ^ ν * q := (Nat.mul_div_cancel' hdvd).symm
  have hf := omegaLow_isFaithful hp2 c c₁ h₁
  have hfl := omegaLow_isFaithful hp2 c (c₁ - ν) (by omega)
  have hψ : (omegaLow hp2 c (c₁ - ν) (by omega) ^ q).IsPrimitive := by
    rw [faithful_pow_prim_iff (by omega) _ hfl]
    intro hq
    apply hndvd
    rw [hJq, pow_succ]
    exact Nat.mul_dvd_mul_left _ hq
  have hprod : ∀ x, (omegaLow hp2 c c₁ h₁ ^ j₁ * omegaLow hp2 c c₁ h₁ ^ j₂) x
      = (omegaLow hp2 c (c₁ - ν) (by omega) ^ q)
          (ZMod.castHom (pow_dvd_pow p (by omega : c₁ - ν + 1 ≤ c₁ + 1)) _ x) := by
    intro x
    rw [← pow_add (omegaLow hp2 c c₁ h₁) j₁ j₂, hJq, pow_mul]
    have ht := tower_compat hp2 c c₁ (c₁ - ν) (by omega) h₁
    rw [show c₁ - (c₁ - ν) = ν by omega] at ht
    rw [← ht, ← map_pow, changeLevel_apply_cast (by omega) (by omega)]
  exact thmA_with_psi K w c₁ ν (w + ν) (c₁ - ν + 1) (by omega) hK rfl (by omega) hK' _ _
    ((faithful_pow_prim_iff hc₁ _ hf j₁).mpr hj₁) ((faithful_pow_prim_iff hc₁ _ hf j₂).mpr hj₂) _ hψ hprod

/-- (B) **同じ殻・定理 B**: φ_{c₁} ∣ j₁+j₂ なら = W^{j₁}(−1)·ballB。 -/
theorem table_B (K w c₁ : ℕ) (hc₁ : 1 ≤ c₁) (h₁ : c₁ ≤ c) (hK : w + (c₁ + 1) ≤ K) (j₁ j₂ : ℕ)
    (hj₁ : ¬ p ∣ j₁) (hφ : phi (p := p) c₁ ∣ j₁ + j₂) :
    conv (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
      (ket K w (c₁ + 1) hK ((omegaLow hp2 c c₁ h₁ ^ j₂ : DirichletCharacter ℂ (p ^ (c₁ + 1))) : ZMod _ → ℂ))
      = (omegaLow hp2 c c₁ h₁ ^ j₁) (-1) • ballB (p := p) K w c₁ := by
  have : NeZero (p ^ (c₁ + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hf := omegaLow_isFaithful hp2 c c₁ h₁
  have h1 : omegaLow hp2 c c₁ h₁ ^ j₁ * omegaLow hp2 c c₁ h₁ ^ j₂ = 1 := by
    rw [← pow_add]
    apply PAG.Part63.eq_one_of_factors_one
    have := (faithful_pow_factors_iff hp2 _ hf 0 (by omega) (j₁ + j₂)).mpr (by rw [card_ker_zero]; exact hφ)
    rwa [pow_zero] at this
  exact thmB_of_mul_eq_one K w c₁ hK _ _ ((faithful_pow_prim_iff hc₁ _ hf j₁).mpr hj₁) h1

end PAG.Part69

#print axioms PAG.Part69.thmA_with_psi
#print axioms PAG.Part69.table_zero
#print axioms PAG.Part69.table_mixed
#print axioms PAG.Part69.table_descent
#print axioms PAG.Part69.table_B
