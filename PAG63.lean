/-
  PAG 2.0 Part 59（2026-10-19）— 奇素数版の分類: ω^j ケット積の行き先（一つの選言）
  p 奇素数、n = c+1、p ∤ j, j'、ν = padicValNat p (j+j')、同じ殻 w のとき次のいずれか:
  (a) φ ∣ j+j'：conv = ω^j(−1)·ballB（定理 B）
  (b) ν ≤ c−1：conv = C·|w+ν, ψ⟩、ψ は導手 p^(n−ν) の原始指標、|C|² = λ
  (c) ν ≥ c ∧ φ ∤ j+j'：conv = C·|w+c, ψ⟩、ψ は導手 p の原始指標、|C|² = λ
-/
import PAG62

namespace PAG.Part63

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part48 PAG.Part61 PAG.Part62

variable {p : ℕ} [hp : Fact p.Prime] (c : ℕ) (hp2 : p ≠ 2)

omit hp in
/-- 法 1 を経由する指標は自明。 -/
theorem eq_one_of_factors_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h : χ.FactorsThrough 1) : χ = 1 := by
  rw [DirichletCharacter.eq_one_iff_conductor_eq_one]
  have hle : χ.conductor ≤ 1 := Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr h)
  have hne : χ.conductor ≠ 0 := by
    intro h0
    have := DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mp h0
    exact NeZero.ne N this
  omega

include hp2

/-- **奇素数版の分類**。 -/
theorem odd_classification (hc : 1 ≤ c) (K w : ℕ) (hK : w + (c + 1) ≤ K) (j j' : ℕ)
    (hj : ¬ p ∣ j) (hj' : ¬ p ∣ j') :
    (phi (p := p) c ∣ j + j' ∧
      conv (ket K w (c + 1) hK ((omega c hp2 ^ j : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ))
        (ket K w (c + 1) hK ((omega c hp2 ^ j' : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ))
        = (omega c hp2 ^ j) (-1) • ballB (p := p) K w c) ∨
    (padicValNat p (j + j') ≤ c - 1 ∧
      ∃ u m, ∃ h : u + m ≤ K, u = w + padicValNat p (j + j') ∧ m = c + 1 - padicValNat p (j + j') ∧
        ∃ ψ : DirichletCharacter ℂ (p ^ m), ψ.IsPrimitive ∧ ∃ C : ℂ,
          Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (c + 1) - w) : ℝ) ∧
          conv (ket K w (c + 1) hK ((omega c hp2 ^ j : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ))
            (ket K w (c + 1) hK ((omega c hp2 ^ j' : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ))
            = C • ket K u m h ψ) ∨
    (c ≤ padicValNat p (j + j') ∧ ¬ phi (p := p) c ∣ j + j' ∧
      ∃ ψ : DirichletCharacter ℂ (p ^ 1), ψ.IsPrimitive ∧ ∃ C : ℂ,
        Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (c + 1) - w) : ℝ) ∧
        conv (ket K w (c + 1) hK ((omega c hp2 ^ j : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ))
          (ket K w (c + 1) hK ((omega c hp2 ^ j' : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ))
          = C • ket K (w + c) 1 (by omega) ψ) := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have h₁ := (omega_pow_prim_iff c hp2 hc j).mpr hj
  have h₂ := (omega_pow_prim_iff c hp2 hc j').mpr hj'
  have hJ : j + j' ≠ 0 := by
    intro h0; apply hj; rw [show j = 0 by omega]; exact dvd_zero p
  set ν := padicValNat p (j + j') with hνdef
  have hdvd : p ^ ν ∣ j + j' := pow_padicValNat_dvd
  have hndvd : ¬ p ^ (ν + 1) ∣ j + j' := pow_succ_padicValNat_not_dvd hJ
  by_cases hφ : phi (p := p) c ∣ j + j'
  · left
    refine ⟨hφ, ?_⟩
    have h1 : omega c hp2 ^ j * omega c hp2 ^ j' = 1 := by
      rw [← pow_add]
      exact eq_one_of_factors_one _ (by
        have := (omega_pow_factors_zero c hp2 (j + j')).mpr hφ
        rwa [pow_zero] at this)
    exact PAG.Part47.thmB_of_mul_eq_one K w c hK _ _ h₁ h1
  · right
    by_cases hν : ν ≤ c - 1
    · left
      refine ⟨hν, ?_⟩
      have hcond : (omega c hp2 ^ j * omega c hp2 ^ j').conductor = p ^ (c + 1 - ν) := by
        rw [omega_mul_conductor_iff c hp2 (c + 1 - ν) (by omega) (by omega),
          show c + 1 - (c + 1 - ν) = ν by omega]
        exact ⟨hdvd, hndvd⟩
      obtain ⟨ψ, hψ, C, hC, hconv⟩ := PAG.Part50.thmA_of_conductor (p := p) K w c (w + ν) (c + 1 - ν) hK
        (by omega) (by omega) (by omega) (by omega) _ _ h₁ h₂ hcond
      exact ⟨w + ν, c + 1 - ν, by omega, rfl, rfl, ψ, hψ, C, hC, hconv⟩
    · right
      refine ⟨by omega, hφ, ?_⟩
      have hcond : (omega c hp2 ^ j * omega c hp2 ^ j').conductor = p ^ 1 := by
        rw [← pow_add, omega_pow_conductor_p_iff c hp2]
        exact ⟨dvd_trans (pow_dvd_pow p (by omega)) hdvd, hφ⟩
      exact PAG.Part50.thmA_of_conductor (p := p) K w c (w + c) 1 hK le_rfl (by omega) (by omega) (by omega)
        _ _ h₁ h₂ hcond

end PAG.Part63

#print axioms PAG.Part63.eq_one_of_factors_one
#print axioms PAG.Part63.odd_classification
