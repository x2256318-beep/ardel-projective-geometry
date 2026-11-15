/-
  PAG 2.0 Part 42（2026-10-19）— 原始的なケットの組の畳み込みの分類
  双対殻 a = K−(n₁+1)−w₁, b = K−(n₂+1)−w₂、λ = p^K/|S_a| とする。
  1. conv = 0 ⇔ a ≠ b（零か飽和かの二択、どちらが起きるかは双対殻だけで決まる）
  2. 異なる殻（w₁ < w₂）で a = b なら、ψ = χ₁·changeLevel(χ₂) は原始的で、
     conv = C·|w₁,ψ⟩、|C|² = λ（存在命題として閉じる）
  3. 鏡像（w₂ < w₁）も同じ（conv の可換性）
-/
import PAG45

namespace PAG.Part46

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part42

variable {p : ℕ} [hp : Fact p.Prime]

theorem lam_pos (K u : ℕ) : (0 : ℝ) < (p : ℝ) ^ K / (sz p K u : ℝ) := by
  have h1 : 0 < sz p K u := by
    unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
  have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  positivity

/-- **分類 1**: conv = 0 ⇔ 双対殻が異なる。 -/
theorem conv_ket_eq_zero_iff (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = 0 ↔
      K - (n₁ + 1) - w₁ ≠ K - (n₂ + 1) - w₂ := by
  constructor
  · intro h hab
    have e := norm_conv_ket_same K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab
    rw [h] at e
    simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero] at e
    exact (lam_pos (p := p) K _).ne e
  · exact conv_ket_eq_zero K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂

/-- 混合の場合の積指標 ψ = χ₁·changeLevel(χ₂)。 -/
noncomputable def psiMix {n v : ℕ} (χ₁ : DirichletCharacter ℂ (p ^ (n + 1)))
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) : DirichletCharacter ℂ (p ^ (n + 1)) :=
  χ₁ * DirichletCharacter.changeLevel (pow_dvd_pow p (Nat.sub_le (n + 1) v)) χ₂

theorem psiMix_apply {n v : ℕ} (χ₁ : DirichletCharacter ℂ (p ^ (n + 1)))
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (x : ZMod (p ^ (n + 1))) :
    psiMix χ₁ χ₂ x = χ₁ x * χ₂ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x) := by
  unfold psiMix
  rw [MulChar.coeToFun_mul, Pi.mul_apply]
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.castHom_apply]
  · rw [MulChar.map_nonunit χ₁ hx, zero_mul, zero_mul]

/-- **分類 2（混合、存在命題）**: w < w+v（1 ≤ v ≤ n）、同じ双対殻なら conv = C·|w,ψ⟩、ψ 原始、|C|² = λ。 -/
theorem conv_ket_mixed_exists (K w n v : ℕ) (hv1 : 1 ≤ v) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (h₂ : χ₂.IsPrimitive) :
    ∃ ψ : DirichletCharacter ℂ (p ^ (n + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
      conv (ket K w (n + 1) hK χ₁) (ket K (w + v) (n + 1 - v) (by omega) χ₂) = C • ket K w (n + 1) hK ψ := by
  have hprod := psiMix_apply χ₁ χ₂
  have hψ := mixed_prim n v hv1 hv χ₁ h₁ χ₂ (psiMix χ₁ χ₂) hprod
  exact ⟨psiMix χ₁ χ₂, hψ, _, normSq_mixed_coef K w n v hv hK χ₁ h₁ χ₂ h₂ _ hψ,
    conv_ket_mixed K w n v hv hK χ₁ h₁ χ₂ h₂ _ hψ hprod⟩

/-- **分類 3（鏡像）**: 順序を入れ替えても同じ（conv の可換性）。 -/
theorem conv_ket_mixed_exists' (K w n v : ℕ) (hv1 : 1 ≤ v) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (h₂ : χ₂.IsPrimitive) :
    ∃ ψ : DirichletCharacter ℂ (p ^ (n + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
      conv (ket K (w + v) (n + 1 - v) (by omega) χ₂) (ket K w (n + 1) hK χ₁) = C • ket K w (n + 1) hK ψ := by
  rw [conv_comm]
  exact conv_ket_mixed_exists K w n v hv1 hv hK χ₁ h₁ χ₂ h₂

/-- 混合の積の値 ψ(−1) = χ₁(−1)χ₂(−1)。 -/
theorem psiMix_neg_one {n v : ℕ} (χ₁ : DirichletCharacter ℂ (p ^ (n + 1)))
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) :
    psiMix χ₁ χ₂ (-1) = χ₁ (-1) * χ₂ (-1) :=
  PAG.Part43.psi_neg_one_mixed χ₁ χ₂ _ (psiMix_apply χ₁ χ₂)

end PAG.Part46

#print axioms PAG.Part46.lam_pos
#print axioms PAG.Part46.conv_ket_eq_zero_iff
#print axioms PAG.Part46.psiMix
#print axioms PAG.Part46.psiMix_apply
#print axioms PAG.Part46.conv_ket_mixed_exists
#print axioms PAG.Part46.conv_ket_mixed_exists'
#print axioms PAG.Part46.psiMix_neg_one
