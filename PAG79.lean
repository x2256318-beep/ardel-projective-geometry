/-
  PAG 2.0 Part 75（2026-10-19）— 展開係数の台による双対殻の保存則
  1. 𝓕ε_a(t) = 0 なら 𝓕(ket)(t) = 0（a はケットの双対殻）
  2. 原始ケット k' の双対殻が k₁ の双対殻と異なれば、任意の g について ⟨k', k₁ ⋆ g⟩ = 0（任意の素数）
  3. 系: 族 S による展開で、k₁ ⋆ g の原始ケット成分は k₁ と同じ双対殻のものだけ
-/
import PAG78

namespace PAG.Part79

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part52 PAG.Part54 PAG.Part55 PAG.Part56

variable {p : ℕ} [hp : Fact p.Prime]

/-- 𝓕ε_a(t) = 0 なら 𝓕(ket)(t) = 0。 -/
theorem dft_ket_eq_zero (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (t : ZMod (p ^ K))
    (h0 : 𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w)) t = 0) :
    𝓕 (ket K w (n + 1) hK χ) t = 0 := by
  have e := normSq_dft_ket_eq K w n hK χ hχ t
  rw [h0, mul_zero] at e
  exact Complex.normSq_eq_zero.mp (by exact_mod_cast e)

/-- **台による保存則**: 双対殻が異なる原始ケットとは、k₁ ⋆ g は直交する（g は任意）。 -/
theorem ip_ket_conv_eq_zero (K w' n' : ℕ) (h' : w' + (n' + 1) ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n' + 1)))
    (hψ : ψ.IsPrimitive) (w₁ n₁ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hne : K - (n' + 1) - w' ≠ K - (n₁ + 1) - w₁) (g : ZMod (p ^ K) → ℂ) :
    ip (ket K w' (n' + 1) h' ψ) (conv (ket K w₁ (n₁ + 1) h₁ χ₁) g) = 0 := by
  have hP := PAG.Part39.plancherel (ket K w' (n' + 1) h' ψ) (conv (ket K w₁ (n₁ + 1) h₁ χ₁) g)
  have hz : ∀ t, starRingEnd ℂ (𝓕 (ket K w' (n' + 1) h' ψ) t) * 𝓕 (conv (ket K w₁ (n₁ + 1) h₁ χ₁) g) t = 0 := by
    intro t
    rw [PAG.Part16.dft_conv, Pi.mul_apply]
    rcases PAG.Part31.dft_eps_zero_or_one (p := p) K (K - (n' + 1) - w') (by omega) t with h0 | h1
    · rw [dft_ket_eq_zero K w' n' h' ψ hψ t h0, map_zero, zero_mul]
    · have e := dft_eps_mul_eq_zero (p := p) K _ _ (by omega) (by omega) hne t
      rw [h1, one_mul] at e
      rw [dft_ket_eq_zero K w₁ n₁ h₁ χ₁ hχ₁ t e, zero_mul, mul_zero]
  simp only [hz, Finset.sum_const_zero] at hP
  have hN : ((p ^ K : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  have := (mul_eq_zero.mp hP.symm).resolve_left hN
  exact this

/-- **系（展開係数の台）**: 族 S の基底での k₁ ⋆ g の係数は、双対殻の異なる原始ケットで 0。 -/
theorem repr_conv_eq_zero (K w' n' : ℕ) (h' : w' + (n' + 1) ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n' + 1)))
    (hψ : ψ.IsPrimitive) (w₁ n₁ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hne : K - (n' + 1) - w' ≠ K - (n₁ + 1) - w₁) (g : ZMod (p ^ K) → ℂ)
    (hmem : ket K w' (n' + 1) h' ψ ∈ family (p := p) K) :
    (familyBasis (p := p) K).repr (conv (ket K w₁ (n₁ + 1) h₁ χ₁) g) ⟨_, hmem⟩ = 0 := by
  rw [repr_eq]
  simp only
  rw [ip_ket_conv_eq_zero K w' n' h' ψ hψ w₁ n₁ h₁ χ₁ hχ₁ hne g, zero_div]

/-- 原始ケットは族 S に属する。 -/
theorem ket_mem_family (K w n : ℕ) (h : w + (n + 1) ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hψ : ψ.IsPrimitive) : ket K w (n + 1) h ψ ∈ family (p := p) K :=
  Or.inl ⟨w, n + 1, h, by omega, ψ, hψ, rfl⟩

/-- **系（二つの原始ケットの積）**: k₁ ⋆ k₂ の原始ケット成分の双対殻は、k₁ と k₂ の双対殻のどちらとも等しい。 -/
theorem conv_component_dual (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (w' n' : ℕ) (h' : w' + (n' + 1) ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n' + 1))) (hψ : ψ.IsPrimitive)
    (hnz : ip (ket K w' (n' + 1) h' ψ) (conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂)) ≠ 0) :
    K - (n' + 1) - w' = K - (n₁ + 1) - w₁ ∧ K - (n' + 1) - w' = K - (n₂ + 1) - w₂ := by
  refine ⟨?_, ?_⟩
  · by_contra hne
    exact hnz (ip_ket_conv_eq_zero K w' n' h' ψ hψ w₁ n₁ h₁ χ₁ hχ₁ hne _)
  · by_contra hne
    rw [conv_comm] at hnz
    exact hnz (ip_ket_conv_eq_zero K w' n' h' ψ hψ w₂ n₂ h₂ χ₂ hχ₂ hne _)

end PAG.Part79

#print axioms PAG.Part79.dft_ket_eq_zero
#print axioms PAG.Part79.ip_ket_conv_eq_zero
#print axioms PAG.Part79.repr_conv_eq_zero
#print axioms PAG.Part79.ket_mem_family
#print axioms PAG.Part79.conv_component_dual
