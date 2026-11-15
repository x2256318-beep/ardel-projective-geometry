/-
  PAG 2.0 Part 74（2026-10-19）— p = 2・混合の像からの読み取りと、双対殻の保存則の対称形
  1. p = 2・混合（d' < d、殻 w < w + (d − d')）: 像が C·|u, m, ψ⟩（C ≠ 0、ψ 原始）なら
     u = w、m = d + 3（レベルの高いほうの因子）。左右を入れ替えても同じ（conv_comm）
  2. 保存則の帰結: 双対殻が共通な組の像がケットの定数倍なら、u + m は因子の w + c に等しい（加法形）
-/
import PAG77

namespace PAG.Part78

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part51 PAG.Part66 PAG.Part77

/-- **p = 2・混合の像からの読み取り**。 -/
theorem p2_mixed_determines (d d' : ℕ) (h : d' < d) (K w : ℕ) (hK : w + (d + 3) ≤ K)
    (h₂ : w + (d - d') + (d' + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j')
    (u m : ℕ) (hm : 1 ≤ m) (hu : u + m ≤ K) (ψ : DirichletCharacter ℂ (2 ^ m)) (hψ : ψ.IsPrimitive) (C : ℂ)
    (hC : C ≠ 0)
    (hF : conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j))
      (ket (p := 2) K (w + (d - d')) (d' + 3) h₂ (chiSJ d' s' j')) = C • ket (p := 2) K u m hu ψ) :
    u = w ∧ m = d + 3 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C', -, e⟩ := mixed_ket_chiSJ d d' h K w hK h₂ s j s' j' hj hj'
  rw [hF] at e
  obtain ⟨hu', hm', -⟩ := ket_rep_unique (p := 2) K u m w (d + 3) hm (by omega) hu hK ψ hψ _
    (mixed_chiSJ_prim d d' h s j s' j' hj) C C' hC e
  exact ⟨hu', hm'⟩

/-- 左右を入れ替えた形（レベルの低い因子が左）。 -/
theorem p2_mixed_determines' (d d' : ℕ) (h : d' < d) (K w : ℕ) (hK : w + (d + 3) ≤ K)
    (h₂ : w + (d - d') + (d' + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j')
    (u m : ℕ) (hm : 1 ≤ m) (hu : u + m ≤ K) (ψ : DirichletCharacter ℂ (2 ^ m)) (hψ : ψ.IsPrimitive) (C : ℂ)
    (hC : C ≠ 0)
    (hF : conv (ket (p := 2) K (w + (d - d')) (d' + 3) h₂ (chiSJ d' s' j'))
      (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) = C • ket (p := 2) K u m hu ψ) :
    u = w ∧ m = d + 3 := by
  rw [conv_comm] at hF
  exact p2_mixed_determines d d' h K w hK h₂ s j s' j' hj hj' u m hm hu ψ hψ C hC hF

variable {p : ℕ} [hp : Fact p.Prime]

/-- **保存則の加法形**: u + m = w₁ + c₁（m = n+1, c₁ = n₁+1）。 -/
theorem dual_shell_conservation_add (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂)
    (u n : ℕ) (hu : u + (n + 1) ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive)
    (C : ℂ)
    (hF : conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = C • ket K u (n + 1) hu ψ) :
    u + (n + 1) = w₁ + (n₁ + 1) := by
  have := dual_shell_conservation K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab u n hu ψ hψ C hF
  omega

/-- **双対殻が異なる組の像は、0 でないケットの定数倍にならない**
（像は 0 なので、C·ket = 0 から C = 0）。 -/
theorem diff_dual_not_ket (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hab : K - (n₁ + 1) - w₁ ≠ K - (n₂ + 1) - w₂)
    (u n : ℕ) (hu : u + (n + 1) ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive)
    (C : ℂ)
    (hF : conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = C • ket K u (n + 1) hu ψ) :
    C = 0 := by
  by_contra hC
  -- 像のフーリエ側 |𝓕|² は λ₁λ₂·ε_{a₁}ε_{a₂} = 0、一方右辺は |C|²λ_b ε_b で ε_b(t) = 1 の点がある
  obtain ⟨t, ht⟩ := exists_dft_eps_one (p := p) K (K - (n + 1) - u) (by omega)
  have e := congrArg (fun f => Complex.normSq (𝓕 f t)) hF
  rw [PAG.Part16.dft_conv, Pi.mul_apply, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Complex.normSq_mul] at e
  have e1 := PAG.Part41.normSq_dft_ket_eq K w₁ n₁ h₁ χ₁ hχ₁ t
  have e2 := PAG.Part41.normSq_dft_ket_eq K w₂ n₂ h₂ χ₂ hχ₂ t
  have e3 := PAG.Part41.normSq_dft_ket_eq K u n hu ψ hψ t
  rw [ht, mul_one] at e3
  have hz := PAG.Part41.dft_eps_mul_eq_zero (p := p) K _ _ (by omega) (by omega) hab t
  have e' : ((Complex.normSq (𝓕 (ket K w₁ (n₁ + 1) h₁ ⇑χ₁) t) *
      Complex.normSq (𝓕 (ket K w₂ (n₂ + 1) h₂ ⇑χ₂) t) : ℝ) : ℂ)
      = ((Complex.normSq C * Complex.normSq (𝓕 (ket K u (n + 1) hu ⇑ψ) t) : ℝ) : ℂ) := by
    exact_mod_cast e
  push_cast at e'
  rw [e1, e2, e3] at e'
  have : ((p : ℂ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℂ) * 𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K
      (K - (n₁ + 1) - w₁)) t) * ((p : ℂ) ^ K / (sz p K (K - (n₂ + 1) - w₂) : ℂ) *
      𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n₂ + 1) - w₂)) t) = 0 := by
    rw [mul_mul_mul_comm, hz, mul_zero]
  rw [this] at e'
  have hC' : (Complex.normSq C : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hC).ne'
  exact mul_ne_zero hC' (lam_ne_zero (p := p) K _) e'.symm

end PAG.Part78

#print axioms PAG.Part78.p2_mixed_determines
#print axioms PAG.Part78.p2_mixed_determines'
#print axioms PAG.Part78.dual_shell_conservation_add
#print axioms PAG.Part78.diff_dual_not_ket
