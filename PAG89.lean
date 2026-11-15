/-
  PAG 2.0 Part 85（2026-10-19）— 畳み込み作用素 T_k : f ↦ k ⋆ f の構造
  k を原始ケット（双対殻 a）、E_a = ε_a（べき等元）、λ = p^K/|S_a| とする。任意の素数で
  1. T_k* T_k = λ·T_{E_a}:  k̃ ⋆ (k ⋆ f) = λ·(ε_a ⋆ f)
  2. ‖k ⋆ f‖² ≤ λ‖f‖²（作用素ノルムの評価）
  3. ε_a ⋆ f = f なら ‖k ⋆ f‖² = λ‖f‖²（V_a = 像(ε_a) 上で √λ 倍の等長）
  4. ε_a ⋆ f = 0 なら k ⋆ f = 0（V_a の直交補空間で 0）
  すなわち λ^{-1/2} T_k は V_a 上のユニタリと 0 の直和（部分等長）
-/
import PAG88

namespace PAG.Part89

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part41

variable {p : ℕ} [hp : Fact p.Prime]

theorem conv_assoc' {N : ℕ} [NeZero N] (f g h : ZMod N → ℂ) : conv (conv f g) h = conv f (conv g h) := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv, PAG.Part16.dft_conv, PAG.Part16.dft_conv, PAG.Part16.dft_conv]
  ring

/-- **T_k* T_k = λ·T_{ε_a}**。 -/
theorem adjoint_mul (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (f : ZMod (p ^ K) → ℂ) :
    conv (tilde (ket K w (n + 1) hK χ)) (conv (ket K w (n + 1) hK χ) f)
      = ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ)) • conv (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w)) f := by
  rw [← conv_assoc', conv_comm (tilde _), ← auto, auto_eps K w n hK χ hχ, conv_comm, PAG.Part52.conv_smul_right,
    conv_comm]

/-- 各点で |𝓕k(t)|² は 0 か λ。 -/
theorem normSq_dft_ket_cases (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (t : ZMod (p ^ K)) :
    𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w)) t = 0 ∧ Complex.normSq (𝓕 (ket K w (n + 1) hK χ) t) = 0 ∨
    𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w)) t = 1 ∧
      Complex.normSq (𝓕 (ket K w (n + 1) hK χ) t) = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) := by
  have e := normSq_dft_ket_eq K w n hK χ hχ t
  rcases PAG.Part31.dft_eps_zero_or_one (p := p) K (K - (n + 1) - w) (by omega) t with h0 | h1
  · left; refine ⟨h0, ?_⟩
    rw [h0, mul_zero] at e; exact_mod_cast e
  · right; refine ⟨h1, ?_⟩
    rw [h1, mul_one] at e
    apply Complex.ofReal_injective
    rw [e]; push_cast; ring

omit hp in
theorem lam_nonneg (K a : ℕ) : 0 ≤ (p : ℝ) ^ K / (sz p K a : ℝ) := by positivity

/-- **作用素ノルムの評価**: ‖k ⋆ f‖² ≤ λ‖f‖²。 -/
theorem norm_conv_le (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (f : ZMod (p ^ K) → ℂ) :
    ∑ x, Complex.normSq (conv (ket K w (n + 1) hK χ) f x)
      ≤ (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) * ∑ x, Complex.normSq (f x) := by
  have hN : (0 : ℝ) < ((p ^ K : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.out.pos K
  have P1 := PAG.Part39.plancherel_normSq (conv (ket K w (n + 1) hK χ) f)
  have P2 := PAG.Part39.plancherel_normSq f
  have key : ∑ t, Complex.normSq (𝓕 (conv (ket K w (n + 1) hK χ) f) t)
      ≤ (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) * ∑ t, Complex.normSq (𝓕 f t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun t _ => ?_)
    rw [PAG.Part16.dft_conv, Pi.mul_apply, Complex.normSq_mul]
    rcases normSq_dft_ket_cases K w n hK χ hχ t with ⟨-, h0⟩ | ⟨-, h1⟩
    · rw [h0, zero_mul]
      exact mul_nonneg (lam_nonneg K _) (Complex.normSq_nonneg _)
    · rw [h1]
  rw [P1, P2] at key
  have : ((p ^ K : ℕ) : ℝ) * ∑ x, Complex.normSq (conv (ket K w (n + 1) hK χ) f x)
      ≤ ((p ^ K : ℕ) : ℝ) * ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) * ∑ x, Complex.normSq (f x)) := by
    nlinarith [key]
  exact le_of_mul_le_mul_left this hN

/-- **V_a 上の等長性**: ε_a ⋆ f = f なら ‖k ⋆ f‖² = λ‖f‖²。 -/
theorem norm_conv_eq_of_mem (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (f : ZMod (p ^ K) → ℂ) (hf : conv (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w)) f = f) :
    ∑ x, Complex.normSq (conv (ket K w (n + 1) hK χ) f x)
      = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) * ∑ x, Complex.normSq (f x) := by
  have hN : ((p ^ K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  have P1 := PAG.Part39.plancherel_normSq (conv (ket K w (n + 1) hK χ) f)
  have P2 := PAG.Part39.plancherel_normSq f
  have key : ∑ t, Complex.normSq (𝓕 (conv (ket K w (n + 1) hK χ) f) t)
      = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) * ∑ t, Complex.normSq (𝓕 f t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [PAG.Part16.dft_conv, Pi.mul_apply, Complex.normSq_mul]
    rcases normSq_dft_ket_cases K w n hK χ hχ t with ⟨h0e, h0⟩ | ⟨-, h1⟩
    · have hft : 𝓕 f t = 0 := by
        have := congrArg (fun g => 𝓕 g t) hf
        simp only [PAG.Part16.dft_conv, Pi.mul_apply] at this
        rw [h0e, zero_mul] at this
        exact this.symm
      rw [h0, hft, Complex.normSq_zero, mul_zero, mul_zero]
    · rw [h1]
  rw [P1, P2] at key
  apply mul_left_cancel₀ hN
  rw [key]; ring

/-- **V_a の直交補空間で 0**: ε_a ⋆ f = 0 なら k ⋆ f = 0。 -/
theorem conv_eq_zero_of_perp (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (f : ZMod (p ^ K) → ℂ) (hf : conv (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w)) f = 0) :
    conv (ket K w (n + 1) hK χ) f = 0 := by
  rw [← PAG.Part58.ket_conv_eps_self K w n hK χ hχ, conv_assoc', hf]
  funext x
  simp [conv]

end PAG.Part89

#print axioms PAG.Part89.conv_assoc'
#print axioms PAG.Part89.adjoint_mul
#print axioms PAG.Part89.normSq_dft_ket_cases
#print axioms PAG.Part89.lam_nonneg
#print axioms PAG.Part89.norm_conv_le
#print axioms PAG.Part89.norm_conv_eq_of_mem
#print axioms PAG.Part89.conv_eq_zero_of_perp
