/-
  PAG 2.0 Part 61（2026-10-19）— 混合の場合の添字表示（奇素数）
  p 奇素数、高い法 p^(c+1)、低い法 p^(c'+1)（c' ≤ c）、ω = ω_c、ω' = ω_{c'}（PAG61）。
  1. changeLevel(ω') = ω^r となる r があり、p^(c−c') ∣ r
  2. changeLevel(ω'^j') = ω^(r j')
  3. 混合の積指標 ψ = ω^j·changeLevel(ω'^j') = ω^(j + r j')、p ∤ j かつ c' < c なら原始的
  4. ケット: |w, ω^j⟩ ⋆ |w+(c−c'), ω'^j'⟩ = C·|w, ω^(j + r j')⟩、|C|² = λ
-/
import PAG64

namespace PAG.Part65

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part42 PAG.Part47 PAG.Part61 PAG.Part62

variable {p : ℕ} [hp : Fact p.Prime]

/-- 混合定理 A の一般形（殻・法を変数にし、ψ を保ったまま）。 -/
theorem mixed_general_psi (K w n v w₂ c₂ : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (hw : w + v = w₂) (hc : n + 1 - v = c₂) (h₂ : w₂ + c₂ ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ c₂)) (hχ₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, ψ x = χ₁ x * χ₂ (ZMod.castHom (pow_dvd_pow p (by omega : c₂ ≤ n + 1)) _ x)) :
    ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
      conv (ket K w (n + 1) hK χ₁) (ket K w₂ c₂ h₂ χ₂) = C • ket K w (n + 1) hK ψ := by
  subst hw; subst hc
  exact ⟨_, normSq_mixed_coef K w n v hv hK χ₁ h₁ χ₂ hχ₂ ψ hψ,
    conv_ket_mixed K w n v hv hK χ₁ h₁ χ₂ hχ₂ ψ hψ hprod⟩

variable (hp2 : p ≠ 2)
include hp2

/-- **changeLevel(ω') = ω^r、p^(c−c') ∣ r**。 -/
theorem changeLevel_omega (c c' : ℕ) (hcc : c' ≤ c) :
    ∃ r, p ^ (c - c') ∣ r ∧
      DirichletCharacter.changeLevel (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1)) (omega c' hp2) = omega c hp2 ^ r := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨r, -, hr⟩ := exists_eq_omega_pow c hp2
    (DirichletCharacter.changeLevel (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1)) (omega c' hp2))
  refine ⟨r, ?_, hr⟩
  have hf := DirichletCharacter.changeLevel_factorsThrough (omega c' hp2) (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1))
  rw [hr, omega_pow_factors_iff' c hp2 (c' + 1) (by omega) (by omega)] at hf
  rwa [show c + 1 - (c' + 1) = c - c' by omega] at hf

/-- **changeLevel(ω'^j') = ω^(r j')**。 -/
theorem changeLevel_omega_pow (c c' : ℕ) (hcc : c' ≤ c) (r : ℕ)
    (hr : DirichletCharacter.changeLevel (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1)) (omega c' hp2) = omega c hp2 ^ r)
    (j' : ℕ) :
    DirichletCharacter.changeLevel (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1)) (omega c' hp2 ^ j')
      = omega c hp2 ^ (r * j') := by
  rw [map_pow, hr, ← pow_mul]

/-- **混合の積指標の添字**: ω^j·changeLevel(ω'^j') = ω^(j + r j')、値は ω^j(x)·ω'^j'(π x)。 -/
theorem mixed_index_apply (c c' : ℕ) (hcc : c' ≤ c) (r : ℕ)
    (hr : DirichletCharacter.changeLevel (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1)) (omega c' hp2) = omega c hp2 ^ r)
    (j j' : ℕ) (x : ZMod (p ^ (c + 1))) :
    (omega c hp2 ^ (j + r * j')) x
      = (omega c hp2 ^ j) x * (omega c' hp2 ^ j') (ZMod.castHom (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1)) _ x) := by
  rw [pow_add (omega c hp2) j (r * j'), MulChar.coeToFun_mul, Pi.mul_apply, ← changeLevel_omega_pow hp2 c c' hcc r hr j',
    changeLevel_apply_cast (by omega) (by omega)]

/-- 混合の積指標は原始的（p ∤ j、c' < c）。 -/
theorem mixed_index_prim (c c' : ℕ) (hc : 1 ≤ c) (hcc : c' < c) (r : ℕ) (hr : p ^ (c - c') ∣ r)
    (j j' : ℕ) (hj : ¬ p ∣ j) : (omega c hp2 ^ (j + r * j')).IsPrimitive := by
  rw [omega_pow_prim_iff c hp2 hc]
  intro h
  apply hj
  have hpr : p ∣ r * j' := dvd_mul_of_dvd_left (dvd_trans (dvd_pow_self p (by omega)) hr) _
  exact (Nat.dvd_add_right hpr).mp (by rwa [add_comm] at h)

/-- **混合の場合の添字表示（ケット）**。 -/
theorem mixed_ket_index (c c' : ℕ) (hc : 1 ≤ c) (hcc : c' < c) (K w : ℕ) (hK : w + (c + 1) ≤ K)
    (h₂ : w + (c - c') + (c' + 1) ≤ K) (j j' : ℕ) (hj : ¬ p ∣ j) (hc'1 : (omega c' hp2 ^ j').IsPrimitive) :
    ∃ r, p ^ (c - c') ∣ r ∧ ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (c + 1) - w) : ℝ) ∧
      conv (ket K w (c + 1) hK ((omega c hp2 ^ j : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ))
        (ket K (w + (c - c')) (c' + 1) h₂ ((omega c' hp2 ^ j' : DirichletCharacter ℂ (p ^ (c' + 1))) : ZMod _ → ℂ))
        = C • ket K w (c + 1) hK ((omega c hp2 ^ (j + r * j') : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ) := by
  obtain ⟨r, hrd, hr⟩ := changeLevel_omega hp2 c c' hcc.le
  refine ⟨r, hrd, ?_⟩
  have h₁ := (omega_pow_prim_iff c hp2 hc j).mpr hj
  exact mixed_general_psi K w c (c - c') (w + (c - c')) (c' + 1) (by omega) hK rfl (by omega) h₂
    _ h₁ _ hc'1 _ (mixed_index_prim hp2 c c' hc hcc r hrd j j' hj)
    (fun x => mixed_index_apply hp2 c c' hcc.le r hr j j' x)

end PAG.Part65

#print axioms PAG.Part65.mixed_general_psi
#print axioms PAG.Part65.changeLevel_omega
#print axioms PAG.Part65.changeLevel_omega_pow
#print axioms PAG.Part65.mixed_index_apply
#print axioms PAG.Part65.mixed_index_prim
#print axioms PAG.Part65.mixed_ket_index
