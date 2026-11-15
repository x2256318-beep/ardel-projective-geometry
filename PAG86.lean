/-
  PAG 2.0 Part 82（2026-10-19）— 同じ殻・同じレベルの積の、指標の言葉による完全な記述
  1. 任意の素数: χ₂ = χ₁⁻¹ なら F = χ₁(−1)·ballB(K, w, n)（定理 B）
  2. p = 2（全原始指標）: χ₂ ≠ χ₁⁻¹ なら F = C·|u, m, ψ⟩（ψ 原始、|C|² = λ）、しかも u + m = w + (n+1)
  よって p = 2 の乗積表は、PAG85 の (0)(M)(M') と合わせて添字によらない形で完結する
-/
import PAG85

namespace PAG.Part86

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part45 PAG.Part47 PAG.Part48 PAG.Part72
  PAG.Part73 PAG.Part82 PAG.Part84 PAG.Part85

/-- **逆指標の組（任意の素数）**: F = χ₁(−1)·ballB。 -/
theorem inv_pair_ballB {p : ℕ} [hp : Fact p.Prime] (K w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ₁ : χ₁.IsPrimitive) (hinv : χ₂ = χ₁⁻¹) :
    conv (ket K w (n + 1) h χ₁) (ket K w (n + 1) h χ₂) = χ₁ (-1) • ballB (p := p) K w n := by
  subst hinv
  exact thmB_of_mul_eq_one K w n h χ₁ χ₁⁻¹ hχ₁ (mul_inv_cancel χ₁)

/-- **p = 2・同じ殻・同じレベル（全原始指標）**。 -/
theorem p2_same_shell_general (K w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (n + 1))) (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    let F := conv (ket (p := 2) K w (n + 1) h χ₁) (ket (p := 2) K w (n + 1) h χ₂)
    (χ₂ = χ₁⁻¹ ∧ F = χ₁ (-1) • ballB (p := 2) K w n) ∨
    (χ₂ ≠ χ₁⁻¹ ∧ ∃ u m : ℕ, ∃ hu : u + (m + 1) ≤ K, ∃ ψ : DirichletCharacter ℂ (2 ^ (m + 1)), ψ.IsPrimitive ∧
      ∃ C : ℂ, Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (n + 1) - w) : ℝ) ∧
        F = C • ket (p := 2) K u (m + 1) hu ψ ∧ u + (m + 1) = w + (n + 1)) := by
  intro F
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hinv : χ₂ = χ₁⁻¹
  · exact Or.inl ⟨hinv, inv_pair_ballB K w n h χ₁ χ₂ hχ₁ hinv⟩
  refine Or.inr ⟨hinv, ?_⟩
  -- 保存則で u + m を出すための補助
  suffices H : ∃ u m : ℕ, ∃ hu : u + (m + 1) ≤ K, ∃ ψ : DirichletCharacter ℂ (2 ^ (m + 1)), ψ.IsPrimitive ∧
      ∃ C : ℂ, Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (n + 1) - w) : ℝ) ∧
        F = C • ket (p := 2) K u (m + 1) hu ψ by
    obtain ⟨u, m, hu, ψ, hψ, C, hC, e⟩ := H
    exact ⟨u, m, hu, ψ, hψ, C, hC, e,
      PAG.Part78.dual_shell_conservation_add (p := 2) K w n w n h h χ₁ χ₂ hχ₁ hχ₂ rfl u m hu ψ hψ C e⟩
  rcases Nat.lt_or_ge n 1 with hn | hn
  · obtain rfl : n = 0 := by omega
    exact absurd hχ₁ (no_prim_mod2 χ₁)
  rcases Nat.lt_or_ge n 2 with hn' | hn'
  · obtain rfl : n = 1 := by omega
    obtain rfl : χ₁ = chi4 := prim4_unique χ₁ chi4 hχ₁ chi4_prim
    obtain rfl : χ₂ = chi4 := prim4_unique χ₂ chi4 hχ₂ chi4_prim
    exact absurd chi4_inv.symm hinv
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  obtain ⟨s, -, j, -, rfl⟩ := chiSJ_surj (d := d) χ₁
  obtain ⟨s', -, j', -, rfl⟩ := chiSJ_surj (d := d) χ₂
  have hj : Odd j := (chiSJ_prim_iff s j).mp hχ₁
  have hj' : Odd j' := (chiSJ_prim_iff s' j').mp hχ₂
  have hT := p2_same_shell_table K w h s j s' j' hj hj'
  simp only at hT
  rcases hT with ⟨hD, h', C, hC, e⟩ | ⟨hM, hs, C, hC, e⟩ | ⟨hM, hs, -⟩
  · have hJ : j + j' ≠ 0 := by have := hj.pos; omega
    have hq : Odd ((j + j') / 2 ^ padicValNat 2 (j + j')) := by
      rw [Nat.odd_iff]
      by_contra hne
      have h2 : 2 ∣ (j + j') / 2 ^ padicValNat 2 (j + j') := Nat.dvd_of_mod_eq_zero (by omega)
      apply pow_succ_padicValNat_not_dvd (p := 2) hJ
      have hJq := (Nat.mul_div_cancel' (pow_padicValNat_dvd (p := 2) (n := j + j'))).symm
      have key : 2 ^ (padicValNat 2 (j + j') + 1) ∣
          2 ^ padicValNat 2 (j + j') * ((j + j') / 2 ^ padicValNat 2 (j + j')) := by
        rw [pow_succ]; exact Nat.mul_dvd_mul_left _ h2
      exact dvd_trans key (dvd_of_eq hJq.symm)
    exact ⟨_, _, h', _, (chiSJ_prim_iff (d := d - padicValNat 2 (j + j')) (s + s') _).mpr hq, C, hC, e⟩
  · exact ⟨_, 1, by omega, chi4, chi4_prim, C, hC, e⟩
  · exfalso
    exact hinv ((p2_three_equiv K w h s j s' j' hj hj').2.mp ⟨hM, hs⟩)

end PAG.Part86

#print axioms PAG.Part86.inv_pair_ballB
#print axioms PAG.Part86.p2_same_shell_general
