/-
  PAG 2.0 Part 35（2026-10-19）— ZMod.dft の Plancherel と、ケットによる畳み込みの作用素ノルム
  1. Σ_k 𝓕h(k) = N·h(0)、Plancherel Σ conj(𝓕f)·𝓕g = N Σ conj f·g、Σ|𝓕f|² = N Σ|f|²
  2. ‖|w,χ⟩‖² = 1
  3. ‖f ⋆ |w,χ⟩‖² ≤ λ‖f‖²、かつ f = |w,χ⟩ で等号（作用素ノルム = √λ、λ = p^K/|S_{w0}|）
-/
import PAG38

namespace PAG.Part39

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part31 PAG.Part38

/-! ## 1. Plancherel -/

section Planch

variable {N : ℕ} [NeZero N]

/-- Σ_k 𝓕h(k) = N·h(0)。 -/
theorem sum_dft (h : ZMod N → ℂ) : ∑ k, 𝓕 h k = (N : ℂ) * h 0 := by
  have := congrFun (dft_dft h) 0
  rw [dft_apply_zero, neg_zero, smul_eq_mul] at this
  exact this

/-- **Plancherel**: Σ conj(𝓕f)·𝓕g = N·Σ conj f·g。 -/
theorem plancherel (f g : ZMod N → ℂ) :
    ∑ k, starRingEnd ℂ (𝓕 f k) * 𝓕 g k = (N : ℂ) * ∑ j, starRingEnd ℂ (f j) * g j := by
  have e : ∀ k, starRingEnd ℂ (𝓕 f k) * 𝓕 g k = 𝓕 (conv (tilde f) g) k := by
    intro k; rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_tilde]
  simp_rw [e]
  rw [sum_dft]
  congr 1
  simp only [conv, tilde, zero_sub]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun y => by simp)

/-- Σ|𝓕f|² = N·Σ|f|²。 -/
theorem plancherel_normSq (f : ZMod N → ℂ) :
    ∑ k, Complex.normSq (𝓕 f k) = (N : ℝ) * ∑ j, Complex.normSq (f j) := by
  have h := plancherel f f
  simp only [← Complex.normSq_eq_conj_mul_self] at h
  exact_mod_cast h

end Planch

/-! ## 2. ケットのノルムと作用素ノルム -/

section Op

variable {p : ℕ} [hp : Fact p.Prime]

instance (K : ℕ) : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- **‖|w,χ⟩‖² = 1**（χ 原始的）。 -/
theorem norm_ket (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    ∑ x, Complex.normSq (ket K w (n + 1) hK χ x) = 1 := by
  have h := auto_zero K w n hK χ hχ
  unfold auto conv tilde at h
  simp only [zero_sub, neg_neg] at h
  have : (∑ x, Complex.normSq (ket K w (n + 1) hK χ x) : ℂ) = 1 := by
    rw [← h]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
  exact_mod_cast this

/-- **作用素ノルムの上界**: ‖f ⋆ |w,χ⟩‖² ≤ λ‖f‖²。 -/
theorem norm_conv_ket_le (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (f : ZMod (p ^ K) → ℂ) :
    ∑ x, Complex.normSq (conv f (ket K w (n + 1) hK χ) x)
      ≤ (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) * ∑ x, Complex.normSq (f x) := by
  have hN : (0 : ℝ) < ((p ^ K : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.out.pos K
  have h1 := plancherel_normSq (conv f (ket K w (n + 1) hK χ))
  have h2 := plancherel_normSq f
  have hle : ∑ k, Complex.normSq (𝓕 (conv f (ket K w (n + 1) hK χ)) k)
      ≤ ∑ k, (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) * Complex.normSq (𝓕 f k) :=
    Finset.sum_le_sum (fun k _ => normSq_dft_conv_ket_le K w n hK χ hχ f k)
  rw [← Finset.mul_sum, h1, h2, mul_left_comm] at hle
  exact le_of_mul_le_mul_left hle hN

/-- **等号の達成**: ‖|w,χ⟩ ⋆ |w,χ⟩‖² = λ（= λ‖|w,χ⟩‖²）。作用素ノルムはちょうど √λ。 -/
theorem norm_conv_ket_self (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    ∑ x, Complex.normSq (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK χ) x)
      = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) := by
  have hN : ((p ^ K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  set lam := (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)
  have h1 := plancherel_normSq (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK χ))
  have h2 := plancherel_normSq (ket K w (n + 1) hK χ)
  rw [norm_ket K w n hK χ hχ, mul_one] at h2
  have hsq : ∀ k, Complex.normSq (𝓕 (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK χ)) k)
      = lam * Complex.normSq (𝓕 (ket K w (n + 1) hK χ) k) := by
    intro k
    rw [PAG.Part16.dft_conv, Pi.mul_apply, Complex.normSq_mul]
    rcases normSq_dft_ket K w n hK χ hχ k with h | h <;> rw [h]
    · ring
  simp_rw [hsq] at h1
  rw [← Finset.mul_sum, h2] at h1
  have e : ((p ^ K : ℕ) : ℝ) * ∑ x, Complex.normSq (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK χ) x)
      = ((p ^ K : ℕ) : ℝ) * lam := by rw [← h1]; ring
  exact mul_left_cancel₀ hN e

end Op

end PAG.Part39

#print axioms PAG.Part39.sum_dft
#print axioms PAG.Part39.plancherel
#print axioms PAG.Part39.plancherel_normSq
#print axioms PAG.Part39.norm_ket
#print axioms PAG.Part39.norm_conv_ket_le
#print axioms PAG.Part39.norm_conv_ket_self
