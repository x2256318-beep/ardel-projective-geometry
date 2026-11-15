/-
  PAG 2.0 Part 48（2026-10-19）— 原始ケットは正規直交系をなす（分類定理からの導出）
  内積 ⟨f, g⟩ = Σ_x conj(f x)·g x とする。
  1. ⟨f, g⟩ = (g ⋆ f̃)(0)、f̃(x) = conj f(−x)
  2. ⟨|w₁,χ₁⟩, |w₂,χ₂⟩⟩ = χ₁(−1)·(|w₂,χ₂⟩ ⋆ |w₁,χ̄₁⟩)(0)
  3. 分類定理を (χ₂, χ̄₁) に適用: (i) 零、(ii) ケットの定数倍（原点で 0）、(iii) 球の差（原点で χ₂(−1)）
     ⇒ ラベル (w, c, χ) が異なれば内積 0、同じなら 1
-/
import PAG51

namespace PAG.Part52

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part31 PAG.Part48 PAG.Part49

variable {p : ℕ} [hp : Fact p.Prime]

/-- 内積。 -/
noncomputable def ip {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x

theorem ip_eq_conv {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) : ip f g = conv g (tilde f) 0 := by
  simp only [ip, conv, tilde, zero_sub, neg_neg]
  exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)

theorem conv_smul_right {N : ℕ} [NeZero N] (a : ℂ) (f g : ZMod N → ℂ) : conv g (a • f) = a • conv g f := by
  have := conv_smul_smul (G := ZMod N) (1 : ℂ) a g f
  rwa [one_smul, one_mul] at this

/-- ⟨|w₁,χ₁⟩, |w₂,χ₂⟩⟩ = χ₁(−1)·(|w₂,χ₂⟩ ⋆ |w₁,χ̄₁⟩)(0)。 -/
theorem ip_ket (K w₁ c₁ w₂ c₂ : ℕ) (h₁ : w₁ + c₁ ≤ K) (h₂ : w₂ + c₂ ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ c₁)) (χ₂ : DirichletCharacter ℂ (p ^ c₂)) :
    ip (ket K w₁ c₁ h₁ χ₁) (ket K w₂ c₂ h₂ χ₂)
      = χ₁ (-1) * conv (ket K w₂ c₂ h₂ χ₂) (ket K w₁ c₁ h₁ ((χ₁⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)) 0 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [ip_eq_conv, tilde_ket, conv_smul_right, Pi.smul_apply, smul_eq_mul]

/-- 共通部: 内積は 0 か、(iii) の場合の χ₁(−1)·χ₂(−1)。 -/
theorem ip_ket_cases (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    ip (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = 0 ∨
      caseIII K w₂ n₂ w₁ n₁ h₂ h₁ χ₂ χ₁⁻¹ := by
  rw [ip_ket]
  rcases classification K w₂ n₂ w₁ n₁ h₂ h₁ χ₂ χ₁⁻¹ hχ₂ (PAG.Part16.isPrimitive_inv hχ₁) with hI | hII | hIII
  · left; rw [hI.2, Pi.zero_apply, mul_zero]
  · left
    obtain ⟨-, w, c, h, hc, ψ, -, C, -, hconv⟩ := hII
    rw [hconv, Pi.smul_apply, PAG.Part49.ket_apply_zero K w c hc h ψ, smul_zero, mul_zero]
  · right; exact hIII

/-- **異なる殻または異なる導手のケットは直交**。 -/
theorem ip_ket_eq_zero_of_ne (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hne : w₁ ≠ w₂ ∨ n₁ ≠ n₂) :
    ip (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = 0 := by
  rcases ip_ket_cases K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ with h | ⟨hw, hn, -⟩
  · exact h
  · rcases hne with hne | hne
    · exact absurd hw.symm hne
    · exact absurd hn.symm hne

/-- **同じ殻・同じ導手で異なる指標のケットは直交**。 -/
theorem ip_ket_eq_zero_of_char_ne (K w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hne : χ₁ ≠ χ₂) :
    ip (ket K w (n + 1) h χ₁) (ket K w (n + 1) h χ₂) = 0 := by
  rcases ip_ket_cases K w n w n h h χ₁ χ₂ hχ₁ hχ₂ with e | hIII
  · exact e
  · exfalso
    have e := (caseIII_iff_inv K w n h χ₂ χ₁⁻¹ hχ₂ (PAG.Part16.isPrimitive_inv hχ₁)).mp hIII
    exact hne (inv_inj.mp e)

/-- **正規性**: ⟨|w,χ⟩, |w,χ⟩⟩ = 1。 -/
theorem ip_ket_self (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : ip (ket K w (n + 1) h χ) (ket K w (n + 1) h χ) = 1 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have e := PAG.Part39.norm_ket K w n h χ hχ
  unfold ip
  have : ∀ x, starRingEnd ℂ (ket K w (n + 1) h χ x) * ket K w (n + 1) h χ x
      = ((Complex.normSq (ket K w (n + 1) h χ x) : ℝ) : ℂ) := by
    intro x; rw [mul_comm, Complex.mul_conj]
  simp_rw [this]
  exact_mod_cast e

open Classical in
/-- **正規直交系**（まとめ）: 原始ケットの内積はラベルが同じなら 1、異なれば 0。 -/
theorem ket_orthonormal (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    (w₁ ≠ w₂ ∨ n₁ ≠ n₂ → ip (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = 0) ∧
    (w₁ = w₂ → ∀ hn : n₁ = n₂, ip (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂)
      = if (hn ▸ χ₁ : DirichletCharacter ℂ (p ^ (n₂ + 1))) = χ₂ then 1 else 0) := by
  refine ⟨ip_ket_eq_zero_of_ne K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂, ?_⟩
  intro hw hn
  subst hw; subst hn
  split_ifs with e
  · subst e; exact ip_ket_self K w₁ n₁ h₁ χ₁ hχ₁
  · exact ip_ket_eq_zero_of_char_ne K w₁ n₁ h₁ χ₁ χ₂ hχ₁ hχ₂ e

end PAG.Part52

#print axioms PAG.Part52.ip
#print axioms PAG.Part52.ip_eq_conv
#print axioms PAG.Part52.conv_smul_right
#print axioms PAG.Part52.ip_ket
#print axioms PAG.Part52.ip_ket_cases
#print axioms PAG.Part52.ip_ket_eq_zero_of_ne
#print axioms PAG.Part52.ip_ket_eq_zero_of_char_ne
#print axioms PAG.Part52.ip_ket_self
#print axioms PAG.Part52.ket_orthonormal
