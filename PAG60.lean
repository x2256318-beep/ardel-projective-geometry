/-
  PAG 2.0 Part 56（2026-10-19）— 原始ケットの固有値の明示
  f = Σ_b g_b ε_b ∈ IndSpan のとき、双対殻 a のケット k について k ⋆ f = g_a·k。
  特に ball_j・1_{S_v}・δ₀ の ε 展開から、PAG58 の固有値が再現される（係数の一致）。
-/
import PAG59

namespace PAG.Part60

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part54 PAG.Part57 PAG.Part58 PAG.Part59

variable {p : ℕ} [hp : Fact p.Prime]

/-- **固有値の明示**: k ⋆ Σ_b g_b ε_b = g_a·k（a = K−(n+1)−w）。 -/
theorem ket_conv_eps_sum (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (g : Fin (K + 1) → ℂ) :
    conv (ket K w (n + 1) hK χ) (∑ b : Fin (K + 1), g b • eps (p := p) K b)
      = g ⟨K - (n + 1) - w, by omega⟩ • ket K w (n + 1) hK χ := by
  rw [conv_sum_right, Finset.sum_eq_single ⟨K - (n + 1) - w, by omega⟩]
  · rw [conv_smul_right']
    congr 1
    exact ket_conv_eps_self K w n hK χ hχ
  · intro b _ hb
    rw [conv_smul_right', ket_conv_eps_ne K w n b hK (by have := b.2; omega)
      (fun h => hb (Fin.ext h)) χ hχ, smul_zero]
  · intro h; exact absurd (mem_univ _) h

/-- 係数の一意性: Σ g_b ε_b = Σ g'_b ε_b ⇒ g = g'。 -/
theorem eps_coeff_unique (K : ℕ) (g g' : Fin (K + 1) → ℂ)
    (h : ∑ b : Fin (K + 1), g b • eps (p := p) K b = ∑ b : Fin (K + 1), g' b • eps (p := p) K b) : g = g' := by
  have := (eps_linearIndependent (p := p) K)
  rw [Fintype.linearIndependent_iff] at this
  funext b
  have e := this (fun b => g b - g' b) (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) b
  exact sub_eq_zero.mp e

/-- 固有値は ε 係数の評価写像: k ⋆ f = (f の ε_a 係数)·k（係数は一意）。 -/
theorem ket_eigenvalue_unique (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (g : Fin (K + 1) → ℂ) (c : ℂ)
    (hc : conv (ket K w (n + 1) hK χ) (∑ b : Fin (K + 1), g b • eps (p := p) K b) = c • ket K w (n + 1) hK χ) :
    c = g ⟨K - (n + 1) - w, by omega⟩ := by
  rw [ket_conv_eps_sum K w n hK χ hχ g] at hc
  have hk := PAG.Part55.ne_zero_of_mem (p := p) K _ (Or.inl ⟨w, n + 1, hK, by omega, χ, hχ, rfl⟩)
  have e : (g ⟨K - (n + 1) - w, by omega⟩ - c) • ket K w (n + 1) hK χ = 0 := by rw [sub_smul, hc, sub_self]
  exact (sub_eq_zero.mp ((smul_eq_zero.mp e).resolve_right hk)).symm

end PAG.Part60

#print axioms PAG.Part60.ket_conv_eps_sum
#print axioms PAG.Part60.eps_coeff_unique
#print axioms PAG.Part60.ket_eigenvalue_unique
