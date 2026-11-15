/-
  PAG 2.0 Part 84（2026-10-19）— 積のノルムの一様性と、素数によらない乗積表
  1. ノルムの公式（任意の素数）: 双対殻が共通な原始ケットの組なら ‖k₁ ⋆ k₂‖² = λ = p^K/|S_a|
     （場合 (M)(S)(B) によらない。とくに ‖ballB(K,w,n)‖² = λ も従う）
  2. 双対殻が異なれば ‖k₁ ⋆ k₂‖² = 0
  3. 素数によらない乗積表: p = 2 なら PAG85、p 奇素数なら PAG87
-/
import PAG87

namespace PAG.Part88

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part48

variable {p : ℕ} [hp : Fact p.Prime]

/-- **積のノルム**: 双対殻が共通なら Σ|k₁⋆k₂|² = λ。 -/
theorem norm_conv_ket (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂) :
    ∑ x, Complex.normSq (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) x)
      = (p : ℝ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℝ) := by
  set a := K - (n₁ + 1) - w₁ with ha
  set lam : ℂ := (p : ℂ) ^ K / (sz p K a : ℂ) with hlam
  set e := fun t => 𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) t with he
  have hee : ∀ t, e t * e t = e t := by
    intro t
    rcases PAG.Part31.dft_eps_zero_or_one (p := p) K a (by omega) t with h0 | h1
    · simp only [he, h0, mul_zero]
    · simp only [he, h1, mul_one]
  have hN : ((p ^ K : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  have P1 := PAG.Part39.plancherel_normSq (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂))
  have P2 := PAG.Part39.plancherel_normSq (ket K w₁ (n₁ + 1) h₁ χ₁)
  rw [PAG.Part39.norm_ket K w₁ n₁ h₁ χ₁ hχ₁, mul_one] at P2
  have P1c : ((∑ k, Complex.normSq (𝓕 (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂)) k) : ℝ) : ℂ)
      = ((p ^ K : ℕ) : ℂ) * ((∑ x, Complex.normSq (conv (ket K w₁ (n₁ + 1) h₁ χ₁)
          (ket K w₂ (n₂ + 1) h₂ χ₂) x) : ℝ) : ℂ) := by
    rw [P1]; push_cast; ring
  have P2c : ((∑ k, Complex.normSq (𝓕 (ket K w₁ (n₁ + 1) h₁ χ₁) k) : ℝ) : ℂ) = ((p ^ K : ℕ) : ℂ) := by
    rw [P2]; push_cast; ring
  have key : ((∑ k, Complex.normSq (𝓕 (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂)) k) : ℝ) : ℂ)
      = lam * ((∑ k, Complex.normSq (𝓕 (ket K w₁ (n₁ + 1) h₁ χ₁) k) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [PAG.Part16.dft_conv, Pi.mul_apply, Complex.normSq_mul]
    push_cast
    rw [normSq_dft_ket_eq K w₁ n₁ h₁ χ₁ hχ₁ t, normSq_dft_ket_eq K w₂ n₂ h₂ χ₂ hχ₂ t, ← hab]
    have := hee t
    simp only [he] at this
    calc lam * 𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) t *
          (lam * 𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) t)
        = lam * (lam * (𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) t *
            𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) t)) := by ring
      _ = lam * (lam * 𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) t) := by rw [this]
  rw [P1c, P2c] at key
  have hfin : ((∑ x, Complex.normSq (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) x) : ℝ) : ℂ) = lam := by
    apply mul_left_cancel₀ hN
    rw [key, mul_comm]
  rw [hlam] at hfin
  apply Complex.ofReal_injective
  rw [hfin]; push_cast; ring

/-- 双対殻が異なれば ‖k₁ ⋆ k₂‖² = 0。 -/
theorem norm_conv_ket_ne (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hab : K - (n₁ + 1) - w₁ ≠ K - (n₂ + 1) - w₂) :
    ∑ x, Complex.normSq (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) x) = 0 := by
  rw [conv_ket_eq_zero K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab]
  simp

/-- **系: ‖ballB(K, w, n)‖² = λ**（逆指標の組の像から）。 -/
theorem norm_ballB (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) :
    ∑ x, Complex.normSq (ballB (p := p) K w n x) = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) := by
  have e := norm_conv_ket K w n w n h h χ χ⁻¹ hχ (PAG.Part16.isPrimitive_inv hχ) rfl
  rw [PAG.Part86.inv_pair_ballB K w n h χ χ⁻¹ hχ rfl] at e
  have hs : Complex.normSq (χ (-1)) = 1 := by
    have h1 := PAG.Part9.chi_neg_one_sq χ
    have : Complex.normSq (χ (-1)) * Complex.normSq (χ (-1)) = 1 := by
      rw [← Complex.normSq_mul, h1, Complex.normSq_one]
    nlinarith [Complex.normSq_nonneg (χ (-1))]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, hs, one_mul] at e
  exact e

/-- **素数によらない乗積表**（全原始指標）。 -/
theorem table_all (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    let F := conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂)
    (K - (n₁ + 1) - w₁ ≠ K - (n₂ + 1) - w₂ ∧ F = 0) ∨
    (w₁ < w₂ ∧ ∃ ψ : DirichletCharacter ℂ (p ^ (n₁ + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℝ) ∧ F = C • ket K w₁ (n₁ + 1) h₁ ψ) ∨
    (w₂ < w₁ ∧ ∃ ψ : DirichletCharacter ℂ (p ^ (n₂ + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n₂ + 1) - w₂) : ℝ) ∧ F = C • ket K w₂ (n₂ + 1) h₂ ψ) ∨
    (w₁ = w₂ ∧ n₁ = n₂) := by
  by_cases hp2 : p = 2
  · subst hp2
    exact PAG.Part85.p2_table K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂
  · exact PAG.Part87.odd_table_general hp2 K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂

/-- **素数によらない同じ殻の記述**（全原始指標）。 -/
theorem same_shell_all (K w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    let F := conv (ket K w (n + 1) h χ₁) (ket K w (n + 1) h χ₂)
    (χ₂ = χ₁⁻¹ ∧ F = χ₁ (-1) • ballB (p := p) K w n) ∨
    (χ₂ ≠ χ₁⁻¹ ∧ ∃ u m : ℕ, ∃ hu : u + (m + 1) ≤ K, ∃ ψ : DirichletCharacter ℂ (p ^ (m + 1)), ψ.IsPrimitive ∧
      ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
        F = C • ket K u (m + 1) hu ψ ∧ u + (m + 1) = w + (n + 1)) := by
  by_cases hp2 : p = 2
  · subst hp2
    exact PAG.Part86.p2_same_shell_general K w n h χ₁ χ₂ hχ₁ hχ₂
  · exact PAG.Part87.odd_same_shell_general hp2 K w n h χ₁ χ₂ hχ₁ hχ₂

end PAG.Part88

#print axioms PAG.Part88.norm_conv_ket
#print axioms PAG.Part88.norm_conv_ket_ne
#print axioms PAG.Part88.norm_ballB
#print axioms PAG.Part88.table_all
#print axioms PAG.Part88.same_shell_all
