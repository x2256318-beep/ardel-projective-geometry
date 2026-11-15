/-
  PAG 2.0 Part 34（2026-10-19）— 随伴関係の帰結とフーリエ乗数
  1. 内積の半線形性、ケットを固定した随伴: B_S(·, |w,χ⟩)^† = χ(−1)·B_S(·, |w,χ̄⟩)
  2. 𝓕(f~) = conj 𝓕f、𝓕A = |𝓕 ket|²
  3. ケットのフーリエ振幅: |𝓕|w,χ⟩(k)|² ∈ {0, λ}（λ = p^K/|S_{w0}|）
  4. フーリエ乗数の評価: |𝓕(f ⋆ |w,χ⟩)(k)|² ≤ λ·|𝓕f(k)|²
-/
import PAG37

namespace PAG.Part38

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part25 PAG.Part28 PAG.Part29 PAG.Part30 PAG.Part31
  PAG.Part32 PAG.Part35 PAG.Part36

open Classical

/-! ## 1. 随伴の帰結 -/

section Adj

variable {p : ℕ} [hp : Fact p.Prime] (K : ℕ) (hK : 1 ≤ K)

instance : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

theorem inner_smul_left (a : ℂ) (Φ Ψ : PAG.Part27.ProjLine (p ^ K) → ℂ) :
    PAG.Part35.inner K (a • Φ) Ψ = starRingEnd ℂ a * PAG.Part35.inner K Φ Ψ := by
  unfold PAG.Part35.inner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

theorem inner_smul_right (a : ℂ) (Φ Ψ : PAG.Part27.ProjLine (p ^ K) → ℂ) :
    PAG.Part35.inner K Φ (a • Ψ) = a * PAG.Part35.inner K Φ Ψ := by
  unfold PAG.Part35.inner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- **ケットを固定した随伴**: ⟨Φ, B_S(Ψ, |w,χ⟩)⟩ = χ(−1)·⟨B_S(Φ, |w,χ̄⟩), Ψ⟩。 -/
theorem adjoint_ketS (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c))
    (Φ Ψ : PAG.Part27.ProjLine (p ^ K) → ℂ) :
    PAG.Part35.inner K Φ (BSproj K hK Ψ (ketS_proj K hK w c h χ))
      = χ (-1) * PAG.Part35.inner K (BSproj K hK Φ (ketS_proj K hK w c h χ⁻¹)) Ψ := by
  rw [inner_BSproj, tildePull_ketS, show BSproj K hK Φ (χ (-1) • ketS_proj K hK w c h χ⁻¹)
      = BSproj K hK ((1 : ℂ) • Φ) (χ (-1) • ketS_proj K hK w c h χ⁻¹) by rw [one_smul],
    BSproj_smul, one_mul, inner_smul_left, star_chi_neg_one]

/-- 北の版: ⟨Φ, B_N(Ψ, |−w,χ⟩)⟩ = χ(−1)·⟨B_N(Φ, |−w,χ̄⟩), Ψ⟩。 -/
theorem adjoint_ketN (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c))
    (Φ Ψ : PAG.Part27.ProjLine (p ^ K) → ℂ) :
    PAG.Part35.inner K Φ (BNproj K hK Ψ (ketN_proj K hK w c h χ))
      = χ (-1) * PAG.Part35.inner K (BNproj K hK Φ (ketN_proj K hK w c h χ⁻¹)) Ψ := by
  rw [inner_BNproj, tildePull_ketN, show BNproj K hK Φ (χ (-1) • ketN_proj K hK w c h χ⁻¹)
      = BNproj K hK ((1 : ℂ) • Φ) (χ (-1) • ketN_proj K hK w c h χ⁻¹) by rw [one_smul],
    BNproj_smul, one_mul, inner_smul_left, star_chi_neg_one]

end Adj

/-! ## 2. フーリエ側 -/

section Four

/-- **𝓕(f~) = conj 𝓕f**。 -/
theorem dft_tilde {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (k : ZMod N) :
    𝓕 (tilde f) k = starRingEnd ℂ (𝓕 f k) := by
  rw [dft_apply, dft_apply, map_sum]
  simp only [tilde, smul_eq_mul, map_mul]
  refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => ?_)
  rw [Equiv.neg_apply, ← AddChar.map_neg_eq_conj, neg_mul, neg_neg]

variable {p : ℕ} [hp : Fact p.Prime]

instance (K : ℕ) : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- 𝓕A = |𝓕 ket|²。 -/
theorem dft_auto_eq_normSq (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) (k : ZMod (p ^ K)) :
    𝓕 (auto K w c h χ) k = (Complex.normSq (𝓕 (ket K w c h χ) k) : ℂ) := by
  rw [auto, PAG.Part16.dft_conv, Pi.mul_apply, dft_tilde, Complex.mul_conj]

/-- **ケットのフーリエ振幅**: |𝓕|w,χ⟩(k)|² ∈ {0, λ}（χ 原始的）。 -/
theorem normSq_dft_ket (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (k : ZMod (p ^ K)) :
    Complex.normSq (𝓕 (ket K w (n + 1) hK χ) k) = 0 ∨
      Complex.normSq (𝓕 (ket K w (n + 1) hK χ) k) = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) := by
  have h := dft_auto_nonneg K w n hK χ hχ k
  rw [dft_auto_eq_normSq] at h
  rcases h with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

/-- **フーリエ乗数の評価**: |𝓕(f ⋆ |w,χ⟩)(k)|² ≤ λ·|𝓕f(k)|²。 -/
theorem normSq_dft_conv_ket_le (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (f : ZMod (p ^ K) → ℂ) (k : ZMod (p ^ K)) :
    Complex.normSq (𝓕 (conv f (ket K w (n + 1) hK χ)) k)
      ≤ (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) * Complex.normSq (𝓕 f k) := by
  rw [PAG.Part16.dft_conv, Pi.mul_apply, Complex.normSq_mul, mul_comm]
  have hl := (lam_pos (p := p) K (K - (n + 1) - w)).le
  rcases normSq_dft_ket K w n hK χ hχ k with h | h
  · rw [h, zero_mul]; exact mul_nonneg hl (Complex.normSq_nonneg _)
  · rw [h]

end Four

end PAG.Part38

#print axioms PAG.Part38.inner_smul_left
#print axioms PAG.Part38.inner_smul_right
#print axioms PAG.Part38.adjoint_ketS
#print axioms PAG.Part38.adjoint_ketN
#print axioms PAG.Part38.dft_tilde
#print axioms PAG.Part38.dft_auto_eq_normSq
#print axioms PAG.Part38.normSq_dft_ket
#print axioms PAG.Part38.normSq_dft_conv_ket_le
