/-
  PAG 2.0 Part 45（2026-10-19）— 分類定理の排他性
  1. 原始ケットは原点 0 で 0（殻 w < K に台）、球の差 ballB は原点で 1
  2. 分類の 3 つの場合を命題 caseI/II/III として定義し、分類定理を caseI ∨ caseII ∨ caseIII と述べ直す
  3. 3 つの場合は互いに排他的（ちょうど一つが成り立つ）
-/
import PAG48

namespace PAG.Part49

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part48

variable {p : ℕ} [hp : Fact p.Prime]

/-- **原始ケット（導手 ≥ p）は原点で 0**。 -/
theorem ket_apply_zero (K w c : ℕ) (hc : 1 ≤ c) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    ket K w c h χ 0 = 0 := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : Fact (1 < p ^ c) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  unfold ket
  rw [Pi.smul_apply, ← map_zero (shellEmb (p := p) K w (by omega)),
    PAG.Part21.push_apply_emb _ (shellEmb_injective K w (by omega))]
  simp only [Function.comp_apply, map_zero, smul_eq_mul]
  rw [MulChar.map_nonunit χ not_isUnit_zero, mul_zero]

omit hp in
/-- 球は原点で 1。 -/
theorem ball_apply_zero (K j : ℕ) : PAG.Part22.ball (p := p) K j 0 = 1 := by
  simp [PAG.Part22.ball]

omit hp in
/-- **球の差は原点で 1**。 -/
theorem ballB_apply_zero (K w n : ℕ) : ballB (p := p) K w n 0 = 1 := by
  simp only [ballB, Pi.sub_apply, Pi.smul_apply, ball_apply_zero, sub_self, smul_zero, sub_zero]

/-- 分類の場合 (i)。 -/
def caseI (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1))) : Prop :=
  K - (n₁ + 1) - w₁ ≠ K - (n₂ + 1) - w₂ ∧ conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = 0

/-- 分類の場合 (ii)。 -/
def caseII (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1))) : Prop :=
  K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂ ∧
    ∃ w c, ∃ h : w + c ≤ K, 1 ≤ c ∧ ∃ ψ : DirichletCharacter ℂ (p ^ c), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℝ) ∧
      conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = C • ket K w c h ψ

/-- 分類の場合 (iii)。 -/
def caseIII (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1))) : Prop :=
  w₁ = w₂ ∧ n₁ = n₂ ∧ conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = χ₁ (-1) • ballB (p := p) K w₁ n₁

variable (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
  (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))

/-- 分類定理（場合の命題で述べ直したもの）。 -/
theorem classification (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    caseI K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ ∨ caseII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ ∨ caseIII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ :=
  conv_ket_classification K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂

theorem not_I_and_II : ¬ (caseI K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ ∧ caseII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂) :=
  fun ⟨hI, hII⟩ => hI.1 hII.1

theorem not_I_and_III : ¬ (caseI K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ ∧ caseIII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂) := by
  rintro ⟨hI, hw, hn, -⟩
  exact hI.1 (by rw [hw, hn])

/-- (ii) と (iii) は排他的: 原点での値が 0 と χ₁(−1) ≠ 0 で異なる。 -/
theorem not_II_and_III : ¬ (caseII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ ∧ caseIII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂) := by
  rintro ⟨⟨-, w, c, h, hc, ψ, -, C, -, hII⟩, -, -, hIII⟩
  have e := congrFun (hII.symm.trans hIII) 0
  rw [Pi.smul_apply, Pi.smul_apply, ket_apply_zero K w c hc h ψ, ballB_apply_zero, smul_eq_mul, smul_eq_mul,
    mul_zero, mul_one] at e
  have hs := PAG.Part9.chi_neg_one_sq χ₁
  rw [← e, mul_zero] at hs
  exact zero_ne_one hs

/-- **ちょうど一つ**: 分類の 3 つの場合のうち、ちょうど一つが成り立つ。 -/
theorem classification_exactly_one (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    (caseI K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ ∨ caseII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ ∨ caseIII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂) ∧
    ¬ (caseI K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ ∧ caseII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂) ∧
    ¬ (caseI K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ ∧ caseIII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂) ∧
    ¬ (caseII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ ∧ caseIII K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂) :=
  ⟨classification K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂, not_I_and_II K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂,
    not_I_and_III K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂, not_II_and_III K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂⟩

/-- 系: 同じ殻・同じ導手で (iii) が起きるのは χ₂ = χ₁⁻¹ のときに限る。 -/
theorem caseIII_iff_inv (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    caseIII K w n w n h h χ₁ χ₂ ↔ χ₂ = χ₁⁻¹ := by
  constructor
  · intro hIII
    rcases PAG.Part47.same_shell_classify K w n h χ₁ χ₂ hχ₁ hχ₂ with ⟨v, hv, ψ, hψ, C, hC, hconv⟩ | ⟨e, -⟩
    · exfalso
      refine not_II_and_III K w n w n h h χ₁ χ₂ ⟨⟨rfl, w + v, n + 1 - v, by omega, by omega, ψ, hψ, C, hC, hconv⟩, hIII⟩
    · exact e
  · rintro rfl
    exact ⟨rfl, rfl, PAG.Part22.thmB_closed K w n h χ₁ hχ₁⟩

end PAG.Part49

#print axioms PAG.Part49.ket_apply_zero
#print axioms PAG.Part49.ball_apply_zero
#print axioms PAG.Part49.ballB_apply_zero
#print axioms PAG.Part49.caseI
#print axioms PAG.Part49.caseII
#print axioms PAG.Part49.caseIII
#print axioms PAG.Part49.classification
#print axioms PAG.Part49.not_I_and_II
#print axioms PAG.Part49.not_I_and_III
#print axioms PAG.Part49.not_II_and_III
#print axioms PAG.Part49.classification_exactly_one
#print axioms PAG.Part49.caseIII_iff_inv
