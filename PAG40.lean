/-
  PAG 2.0 Part 36（2026-10-19）— 定理 A・B は作用素ノルムを飽和する
  ‖f ⋆ |w,χ₂⟩‖² ≤ λ‖f‖²（PAG39、λ = p^K/|S_{w0}|）に対し、
  1. 定理 A: ‖|w,χ₁⟩ ⋆ |w,χ₂⟩‖² = λ（|J̃| = 1、‖|w+v,ψ⟩‖ = 1）
  2. 定理 B: ‖|w,χ⟩ ⋆ |w,χ̄⟩‖² = λ
  すなわち単位ベクトル |w,χ₁⟩ は畳み込み作用素 · ⋆ |w,χ₂⟩ の最大特異ベクトル。
-/
import PAG39

namespace PAG.Part40

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part29 PAG.Part30 PAG.Part31 PAG.Part38 PAG.Part39

variable {p : ℕ} [hp : Fact p.Prime]

instance (K : ℕ) : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- ‖|w,χ⟩‖² = 1（一般の c ≥ 1、χ 原始的）。 -/
theorem norm_ket' (K w c : ℕ) (hc : 1 ≤ c) (h : w + c ≤ K)
    (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∑ x, Complex.normSq (ket K w c h χ x) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
  exact norm_ket K w n h χ hχ

/-- **定理 A は作用素ノルムを飽和する**: ‖|w,χ₁⟩ ⋆ |w,χ₂⟩‖² = λ。 -/
theorem thmA_norm (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    ∑ x, Complex.normSq (conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂) x)
      = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) := by
  rw [thmA_ket K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [← Finset.mul_sum, norm_ket' K (w + v) (n + 1 - v) (by omega) _ ψ hψ, mul_one,
    PAG.Part20.normSq_Jt n v hv χ₁ χ₂ h₁ h₂ ψ hψ, mul_one, Complex.normSq_ofReal,
    Real.mul_self_sqrt]
  have : (0 : ℝ) < sz p K (K - (n + 1) - w) := by
    unfold sz; exact_mod_cast Nat.mul_pos (pow_pos hp.out.pos _) (by have := hp.out.two_le; omega)
  positivity

/-- **定理 B も作用素ノルムを飽和する**: ‖|w,χ⟩ ⋆ |w,χ̄⟩‖² = λ。 -/
theorem thmB_norm (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    ∑ x, Complex.normSq (conv (ket K w (n + 1) hK χ)
        (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)) x)
      = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) := by
  have hN : ((p ^ K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  set lam := (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)
  have h1 := plancherel_normSq (conv (ket K w (n + 1) hK χ)
    (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
  have h2 := plancherel_normSq (ket K w (n + 1) hK χ)
  rw [norm_ket K w n hK χ hχ, mul_one] at h2
  have hsq : ∀ k, Complex.normSq (𝓕 (conv (ket K w (n + 1) hK χ)
      (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))) k)
      = lam * Complex.normSq (𝓕 (ket K w (n + 1) hK χ) k) := by
    intro k
    rw [H_eq_chi_auto, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
      dft_auto_eq_normSq, Complex.normSq_ofReal]
    have hm : Complex.normSq (χ (-1)) = 1 := by
      have := PAG.Part9.chi_neg_one_sq χ
      have e := congrArg Complex.normSq this
      rw [map_mul, map_one] at e
      nlinarith [Complex.normSq_nonneg (χ (-1))]
    rw [hm, one_mul]
    rcases normSq_dft_ket K w n hK χ hχ k with h | h <;> rw [h]
    · ring
  simp_rw [hsq] at h1
  rw [← Finset.mul_sum, h2] at h1
  have e : ((p ^ K : ℕ) : ℝ) * ∑ x, Complex.normSq (conv (ket K w (n + 1) hK χ)
      (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)) x) = ((p ^ K : ℕ) : ℝ) * lam := by
    rw [← h1]; ring
  exact mul_left_cancel₀ hN e

/-- **飽和の言い換え**: 単位ベクトル |w,χ₁⟩ で上界 ‖f ⋆ |w,χ₂⟩‖² ≤ λ‖f‖² が等号になる。 -/
theorem thmA_saturates (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    ∑ x, Complex.normSq (conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂) x)
      = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) * ∑ x, Complex.normSq (ket K w (n + 1) hK χ₁ x) := by
  rw [thmA_norm K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod, norm_ket K w n hK χ₁ h₁, mul_one]

end PAG.Part40

#print axioms PAG.Part40.norm_ket'
#print axioms PAG.Part40.thmA_norm
#print axioms PAG.Part40.thmB_norm
#print axioms PAG.Part40.thmA_saturates
