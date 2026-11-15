/-
  PAG 2.0 Part 68（2026-10-19）— 法 4 の原始指標の一意性と、p = 2 の最下段の行き先
  1. (Z/4)ˣ = {1, −1}
  2. 法 4 の原始指標 ψ は ψ(−1) = −1 をみたし、ただ一つ（chi4）
  3. (L2) 同じ殻・M ∣ j+j'・s+s' 奇数なら |w,χ_{s,j}⟩ ⋆ |w,χ_{s',j'}⟩ = C·|w+d+1, chi4⟩、|C|² = λ
-/
import PAG71

namespace PAG.Part72

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part47 PAG.Part50

theorem units_four : ∀ u : (ZMod (2 ^ 2))ˣ, u = 1 ∨ u = -1 := by decide

/-- 法 4 の原始指標は ψ(−1) = −1。 -/
theorem prim4_neg_one (ψ : DirichletCharacter ℂ (2 ^ 2)) (hψ : ψ.IsPrimitive) : ψ (-1) = -1 := by
  have hsq := PAG.Part9.chi_neg_one_sq ψ
  have hne : ψ (-1) ≠ 1 := by
    intro h1
    have : ψ = 1 := by
      apply MulChar.ext
      intro u
      rcases units_four u with rfl | rfl
      · simp
      · rw [MulChar.one_apply_coe, Units.val_neg, Units.val_one, h1]
    have hc := (DirichletCharacter.isPrimitive_def ψ).mp hψ
    rw [this, DirichletCharacter.conductor_one] at hc
    norm_num at hc
  have : (ψ (-1) - 1) * (ψ (-1) + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (by linear_combination h) hne
  · linear_combination h

/-- **法 4 の原始指標の一意性**。 -/
theorem prim4_unique (ψ ψ' : DirichletCharacter ℂ (2 ^ 2)) (hψ : ψ.IsPrimitive) (hψ' : ψ'.IsPrimitive) :
    ψ = ψ' := by
  apply MulChar.ext
  intro u
  rcases units_four u with rfl | rfl
  · simp
  · rw [Units.val_neg, Units.val_one, prim4_neg_one ψ hψ, prim4_neg_one ψ' hψ']

/-- 法 4 の原始指標は存在する（χ_{1,0}（法 8）の原始指標）。 -/
theorem exists_prim4 : ∃ ψ : DirichletCharacter ℂ (2 ^ 2), ψ.IsPrimitive := by
  have hc : (chiSJ 0 1 0).conductor = 2 ^ 2 := by
    rw [chiSJ_conductor_four_iff]; exact ⟨dvd_zero _, odd_one⟩
  obtain ⟨ψ, hψ, -⟩ := exists_prim_of_conductor (chiSJ 0 1 0) hc
  exact ⟨ψ, hψ⟩

/-- 法 4 の原始指標 chi4。 -/
noncomputable def chi4 : DirichletCharacter ℂ (2 ^ 2) := Classical.choose exists_prim4

theorem chi4_prim : chi4.IsPrimitive := Classical.choose_spec exists_prim4

theorem chi4_neg_one : chi4 (-1) = -1 := prim4_neg_one _ chi4_prim

/-- (L2) **p = 2 の最下段の行き先**: = C·|w+d+1, chi4⟩。 -/
theorem p2_table_bottom {d : ℕ} (K w : ℕ) (hK : w + (d + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j')
    (hs : Odd (s + s')) (hM : 2 ^ (d + 1) ∣ j + j') :
    ∃ C : ℂ, Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (d + 3) - w) : ℝ) ∧
      conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j'))
        = C • ket (p := 2) K (w + (d + 1)) 2 (by omega) chi4 := by
  obtain ⟨ψ, hψ, C, hC, hconv⟩ := p2_caseA4 K w hK s j s' j' hj hj' hs hM
  rw [prim4_unique ψ chi4 hψ chi4_prim] at hconv
  exact ⟨C, hC, hconv⟩

end PAG.Part72

#print axioms PAG.Part72.units_four
#print axioms PAG.Part72.prim4_neg_one
#print axioms PAG.Part72.prim4_unique
#print axioms PAG.Part72.exists_prim4
#print axioms PAG.Part72.chi4
#print axioms PAG.Part72.chi4_prim
#print axioms PAG.Part72.chi4_neg_one
#print axioms PAG.Part72.p2_table_bottom
