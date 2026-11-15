/-
  PAG 2.0 Part 88（2026-10-19）— T_k は B_a = {双対殻 a の原始ケット} ∪ {ε_a} 上の単項（一般化置換）作用素
  k = |w, χ⟩（双対殻 a）、λ = p^K/|S_a|。任意の素数で
  (a) T_k ε_a = k
  (b) T_k k̄ = χ(−1)·λ·ε_a（k̄ = |w, χ⁻¹⟩）
  (c1) 殻の異なる双対殻 a の原始ケット k'' について T_k k'' = C·|u, ψ⟩、|C|² = λ（ψ 原始、双対殻 a）
  (c2) 同じ殻・同じ導手で χ'' ≠ χ⁻¹ なら T_k k'' = C·|u, ψ⟩、|C|² = λ（u + m = w + c）
  すなわち λ^{-1/2} T_k は B_a の各元を、絶対値 1 の係数つきで B_a の元に移す
-/
import PAG91

namespace PAG.Part92

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part29 PAG.Part88

variable {p : ℕ} [hp : Fact p.Prime]

/-- (b) **T_k k̄ = χ(−1)·λ·ε_a**。 -/
theorem T_conj (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    conv (ket K w (n + 1) h χ) (ket K w (n + 1) h ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))
      = (χ (-1) * ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ))) •
          PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w) :=
  thmB_eps K w n h χ hχ

/-- (c1) **殻の異なる相手**: 双対殻が共通で w ≠ w'' なら T_k k'' は単位係数（|C|² = λ）のケット。 -/
theorem T_other_shell (K w n w'' n'' : ℕ) (h : w + (n + 1) ≤ K) (h'' : w'' + (n'' + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (χ'' : DirichletCharacter ℂ (p ^ (n'' + 1)))
    (hχ : χ.IsPrimitive) (hχ'' : χ''.IsPrimitive) (hab : K - (n + 1) - w = K - (n'' + 1) - w'')
    (hw : w ≠ w'') :
    ∃ u m : ℕ, ∃ hu : u + (m + 1) ≤ K, ∃ ψ : DirichletCharacter ℂ (p ^ (m + 1)), ψ.IsPrimitive ∧
      ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
        conv (ket K w (n + 1) h χ) (ket K w'' (n'' + 1) h'' χ'') = C • ket K u (m + 1) hu ψ := by
  have hT := table_all K w n w'' n'' h h'' χ χ'' hχ hχ''
  simp only at hT
  rcases hT with ⟨hne, -⟩ | ⟨-, ψ, hψ, C, hC, e⟩ | ⟨-, ψ, hψ, C, hC, e⟩ | ⟨hw', -⟩
  · exact absurd hab hne
  · exact ⟨w, n, h, ψ, hψ, C, hC, e⟩
  · exact ⟨w'', n'', h'', ψ, hψ, C, by rw [hab]; exact hC, e⟩
  · exact absurd hw' hw

/-- (c2) **同じ殻・同じ導手で逆指標でない相手**。 -/
theorem T_same_shell (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ χ'' : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (hχ'' : χ''.IsPrimitive) (hne : χ'' ≠ χ⁻¹) :
    ∃ u m : ℕ, ∃ hu : u + (m + 1) ≤ K, ∃ ψ : DirichletCharacter ℂ (p ^ (m + 1)), ψ.IsPrimitive ∧
      ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
        conv (ket K w (n + 1) h χ) (ket K w (n + 1) h χ'') = C • ket K u (m + 1) hu ψ ∧
        u + (m + 1) = w + (n + 1) := by
  have hT := same_shell_all K w n h χ χ'' hχ hχ''
  simp only at hT
  rcases hT with ⟨hinv, -⟩ | ⟨-, H⟩
  · exact absurd hinv hne
  · exact H

end PAG.Part92

#print axioms PAG.Part92.T_conj
#print axioms PAG.Part92.T_other_shell
#print axioms PAG.Part92.T_same_shell
