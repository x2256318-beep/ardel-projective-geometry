/-
  PAG 2.0 Part 81（2026-10-19）— p = 2 の乗積表の完全形（全原始指標、一つの選言）
  任意の原始指標 χ₁（法 2^(n₁+1)）、χ₂（法 2^(n₂+1)）について F = |w₁,χ₁⟩ ⋆ |w₂,χ₂⟩ は
    (0) 双対殻が異なり F = 0
    (M) w₁ < w₂ で F = C·|w₁, ψ⟩（ψ 原始・法 2^(n₁+1)、|C|² = λ）
    (M') w₂ < w₁ で同様（行き先は χ₂ 側）
    (S) w₁ = w₂ ∧ n₁ = n₂（同じ殻・同じレベル。PAG73/PAG84 の表に続く）
  のどれか。補題: 法 2 の原始指標は存在しない
-/
import PAG84

namespace PAG.Part85

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part44 PAG.Part45 PAG.Part66 PAG.Part72
  PAG.Part83

/-- 法 2 の原始指標は存在しない。 -/
theorem no_prim_mod2 (χ : DirichletCharacter ℂ (2 ^ (0 + 1))) : ¬ χ.IsPrimitive := by
  intro hχ
  have : χ = 1 := by
    apply MulChar.ext
    intro u
    have hu : u = 1 := by
      have : ∀ v : (ZMod (2 ^ (0 + 1)))ˣ, v = 1 := by decide
      exact this u
    rw [hu]; simp
  have hc := (DirichletCharacter.isPrimitive_def χ).mp hχ
  rw [this, DirichletCharacter.conductor_one] at hc
  norm_num at hc

/-- **p = 2 の混合（全原始指標）**: w₁ < w₂（双対殻共通）なら F = C·|w₁, ψ⟩。 -/
theorem p2_mixed_general (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (2 ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (2 ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂)
    (hw : w₁ < w₂) :
    ∃ ψ : DirichletCharacter ℂ (2 ^ (n₁ + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (n₁ + 1) - w₁) : ℝ) ∧
      conv (ket (p := 2) K w₁ (n₁ + 1) h₁ χ₁) (ket (p := 2) K w₂ (n₂ + 1) h₂ χ₂)
        = C • ket (p := 2) K w₁ (n₁ + 1) h₁ ψ := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- レベルの大小
  rcases Nat.lt_or_ge n₂ 1 with hn₂ | hn₂
  · obtain rfl : n₂ = 0 := by omega
    exact absurd hχ₂ (no_prim_mod2 χ₂)
  obtain ⟨d, rfl⟩ : ∃ d, n₁ = d + 2 := ⟨n₁ - 2, by omega⟩
  obtain ⟨s, -, j, -, rfl⟩ := chiSJ_surj (d := d) χ₁
  have hj : Odd j := (chiSJ_prim_iff s j).mp hχ₁
  rcases Nat.lt_or_ge n₂ 2 with hn₂' | hn₂'
  · -- レベル 2（χ₄）
    obtain rfl : n₂ = 1 := by omega
    obtain rfl : χ₂ = chi4 := prim4_unique χ₂ chi4 hχ₂ chi4_prim
    obtain rfl : w₂ = w₁ + (d + 1) := by omega
    obtain ⟨C, hC, e⟩ := mixed_ket_chi4 d K w₁ h₁ h₂ s j hj
    exact ⟨_, (chiSJ_prim_iff (s + 1) j).mpr hj, C, hC, e⟩
  · -- レベル 3 以上
    obtain ⟨d', rfl⟩ : ∃ d', n₂ = d' + 2 := ⟨n₂ - 2, by omega⟩
    obtain ⟨s', -, j', -, rfl⟩ := chiSJ_surj (d := d') χ₂
    have hj' : Odd j' := (chiSJ_prim_iff s' j').mp hχ₂
    have hdd : d' < d := by omega
    obtain rfl : w₂ = w₁ + (d - d') := by omega
    obtain ⟨C, hC, e⟩ := mixed_ket_chiSJ d d' hdd K w₁ h₁ h₂ s j s' j' hj hj'
    exact ⟨_, mixed_chiSJ_prim d d' hdd s j s' j' hj, C, hC, e⟩

/-- **p = 2 の乗積表（全原始指標、一つの選言）**。 -/
theorem p2_table (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (2 ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (2 ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    let F := conv (ket (p := 2) K w₁ (n₁ + 1) h₁ χ₁) (ket (p := 2) K w₂ (n₂ + 1) h₂ χ₂)
    (K - (n₁ + 1) - w₁ ≠ K - (n₂ + 1) - w₂ ∧ F = 0) ∨
    (w₁ < w₂ ∧ ∃ ψ : DirichletCharacter ℂ (2 ^ (n₁ + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (n₁ + 1) - w₁) : ℝ) ∧ F = C • ket (p := 2) K w₁ (n₁ + 1) h₁ ψ) ∨
    (w₂ < w₁ ∧ ∃ ψ : DirichletCharacter ℂ (2 ^ (n₂ + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (n₂ + 1) - w₂) : ℝ) ∧ F = C • ket (p := 2) K w₂ (n₂ + 1) h₂ ψ) ∨
    (w₁ = w₂ ∧ n₁ = n₂) := by
  intro F
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂
  swap
  · exact Or.inl ⟨hab, conv_ket_eq_zero (p := 2) K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab⟩
  rcases lt_trichotomy w₁ w₂ with hw | hw | hw
  · exact Or.inr (Or.inl ⟨hw, p2_mixed_general K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab hw⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨hw, by omega⟩))
  · refine Or.inr (Or.inr (Or.inl ⟨hw, ?_⟩))
    obtain ⟨ψ, hψ, C, hC, e⟩ := p2_mixed_general K w₂ n₂ w₁ n₁ h₂ h₁ χ₂ χ₁ hχ₂ hχ₁ hab.symm hw
    exact ⟨ψ, hψ, C, hC, by rw [show F = _ from conv_comm _ _]; exact e⟩

/-- **系（p = 2・混合の読み取り、全原始指標）**: w₁ < w₂ で像が C'·|u,m,ψ'⟩（C' ≠ 0）なら u = w₁、m = n₁+1。 -/
theorem p2_mixed_general_determines (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (2 ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (2 ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂)
    (hw : w₁ < w₂) (u m : ℕ) (hm : 1 ≤ m) (hu : u + m ≤ K) (ψ' : DirichletCharacter ℂ (2 ^ m))
    (hψ' : ψ'.IsPrimitive) (C' : ℂ) (hC' : C' ≠ 0)
    (hF : conv (ket (p := 2) K w₁ (n₁ + 1) h₁ χ₁) (ket (p := 2) K w₂ (n₂ + 1) h₂ χ₂)
      = C' • ket (p := 2) K u m hu ψ') :
    u = w₁ ∧ m = n₁ + 1 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ, C, -, e⟩ := p2_mixed_general K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab hw
  rw [hF] at e
  obtain ⟨hu', hm', -⟩ := PAG.Part51.ket_rep_unique (p := 2) K u m w₁ (n₁ + 1) hm (by omega) hu h₁ ψ' hψ' ψ hψ
    C' C hC' e
  exact ⟨hu', hm'⟩

end PAG.Part85

#print axioms PAG.Part85.no_prim_mod2
#print axioms PAG.Part85.p2_mixed_general
#print axioms PAG.Part85.p2_table
#print axioms PAG.Part85.p2_mixed_general_determines
