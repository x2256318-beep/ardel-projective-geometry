/-
  PAG 2.0 Part 43（2026-10-19）— 同じ殻の定理 A・B を存在命題として閉じる
  1. 導手 N の指標は法 N の原始指標の changeLevel（N を変数にして subst）
  2. 素数べきの法 p^c（c ≥ 1）では changeLevel ψ (x) = ψ(π x) が非単数でも成り立つ
  3. χ₁χ₂ ≠ 1 なら ∃ v ≤ n, ∃ ψ 原始（法 p^(n+1−v)）, ∃ C, |C|² = λ ∧ conv = C·|w+v,ψ⟩（定理 A の存在形）
  4. χ₁χ₂ = 1 なら conv は定理 B の球の差（χ₂ = χ₁⁻¹）
  5. 同じ殻・同じ導手の二択（3 と 4 を一つの定理に）
-/
import PAG46

namespace PAG.Part47

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part24 PAG.Part40

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- 導手 N の指標は、法 N の原始指標の changeLevel。 -/
theorem exists_prim_of_conductor {M : ℕ} (χ : DirichletCharacter ℂ M) {N : ℕ} (hN : χ.conductor = N) :
    ∃ ψ : DirichletCharacter ℂ N, ψ.IsPrimitive ∧ ∃ h : N ∣ M, DirichletCharacter.changeLevel h ψ = χ := by
  subst hN
  exact ⟨χ.primitiveCharacter, DirichletCharacter.primitiveCharacter_isPrimitive χ,
    DirichletCharacter.conductor_dvd_level χ, DirichletCharacter.changeLevel_primitiveCharacter χ⟩

/-- 法 p^c（c ≥ 1）では changeLevel ψ (x) = ψ(π x)（非単数を含むすべての x）。 -/
theorem changeLevel_apply_cast {K c : ℕ} (hc1 : 1 ≤ c) (hcK : c ≤ K) (ψ : DirichletCharacter ℂ (p ^ c))
    (x : ZMod (p ^ K)) :
    DirichletCharacter.changeLevel (pow_dvd_pow p hcK) ψ x = ψ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.castHom_apply]
  · rw [MulChar.map_nonunit _ hx, chi_cast_nonunit hc1 hcK ψ hx]

/-- 法 p^(n+1) の指標の導手は p^i（i ≤ n+1）。 -/
theorem conductor_eq_pow {n : ℕ} (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    ∃ i ≤ n + 1, χ.conductor = p ^ i :=
  (Nat.dvd_prime_pow hp.out).1 (DirichletCharacter.conductor_dvd_level χ)

/-- 係数の大きさは像のノルムから決まる: conv = C·k、‖k‖² = 1、‖conv‖² = λ ⇒ |C|² = λ。 -/
theorem normSq_coef_of {N : ℕ} [NeZero N] (F k : ZMod N → ℂ) (C : ℂ) (lam : ℝ) (hF : F = C • k)
    (hk : ∑ x, Complex.normSq (k x) = 1) (hn : ∑ x, Complex.normSq (F x) = lam) : Complex.normSq C = lam := by
  rw [hF] at hn
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul] at hn
  rw [← Finset.mul_sum, hk, mul_one] at hn
  exact hn

/-- **定理 A の存在形**: χ₁χ₂ ≠ 1 なら、積の原始指標 ψ（導手 p^(n+1−v)、v ≤ n）がとれて conv = C·|w+v,ψ⟩、|C|² = λ。 -/
theorem thmA_exists (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (hne : χ₁ * χ₂ ≠ 1) :
    ∃ v, ∃ hv : v ≤ n, ∃ ψ : DirichletCharacter ℂ (p ^ (n + 1 - v)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
      conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂) = C • ket K (w + v) (n + 1 - v) (by omega) ψ := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨i, hi, hc⟩ := conductor_eq_pow (χ₁ * χ₂)
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, ← DirichletCharacter.eq_one_iff_conductor_eq_one] at hc
    exact hne hc
  have hv : n + 1 - i ≤ n := by omega
  have hc' : (χ₁ * χ₂).conductor = p ^ (n + 1 - (n + 1 - i)) := by rw [hc]; congr 1; omega
  obtain ⟨ψ, hψ, hdvd, hcl⟩ := exists_prim_of_conductor (χ₁ * χ₂) hc'
  have hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) (n + 1 - i))) _ x) := by
    intro x
    rw [← hcl]
    exact changeLevel_apply_cast (by omega) (Nat.sub_le (n + 1) (n + 1 - i)) ψ x
  have hA := thmA_ket K w n (n + 1 - i) hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod
  refine ⟨n + 1 - i, hv, ψ, hψ, _, ?_, hA⟩
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact normSq_coef_of _ _ _ _ hA (norm_ket' K (w + (n + 1 - i)) (n + 1 - (n + 1 - i)) (by omega) _ ψ hψ)
    (thmA_norm K w n (n + 1 - i) hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod)

/-- **定理 B の場合**: χ₁χ₂ = 1 なら χ₂ = χ₁⁻¹ で、conv は球の差。 -/
theorem thmB_of_mul_eq_one (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h1 : χ₁ * χ₂ = 1) :
    conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂)
      = χ₁ (-1) • (PAG.Part22.ball (p := p) K (w + (n + 1))
          - ((p : ℂ) - 1)⁻¹ • (PAG.Part22.ball (p := p) K (w + n) - PAG.Part22.ball (p := p) K (w + (n + 1)))) := by
  have e : χ₂ = χ₁⁻¹ := eq_inv_of_mul_eq_one_right h1
  subst e
  exact PAG.Part22.thmB_closed K w n hK χ₁ h₁

/-- **同じ殻・同じ導手の二択**: 定理 A（ケットの定数倍、|C|² = λ）か定理 B（球の差）のどちらか一方。 -/
theorem same_shell_classify (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (∃ v, ∃ hv : v ≤ n, ∃ ψ : DirichletCharacter ℂ (p ^ (n + 1 - v)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
      conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂) = C • ket K (w + v) (n + 1 - v) (by omega) ψ) ∨
    (χ₂ = χ₁⁻¹ ∧ conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂)
      = χ₁ (-1) • (PAG.Part22.ball (p := p) K (w + (n + 1))
          - ((p : ℂ) - 1)⁻¹ • (PAG.Part22.ball (p := p) K (w + n) - PAG.Part22.ball (p := p) K (w + (n + 1))))) := by
  by_cases h1 : χ₁ * χ₂ = 1
  · exact Or.inr ⟨eq_inv_of_mul_eq_one_right h1, thmB_of_mul_eq_one K w n hK χ₁ χ₂ h₁ h1⟩
  · exact Or.inl (thmA_exists K w n hK χ₁ χ₂ h₁ h₂ h1)

end PAG.Part47

#print axioms PAG.Part47.exists_prim_of_conductor
#print axioms PAG.Part47.changeLevel_apply_cast
#print axioms PAG.Part47.conductor_eq_pow
#print axioms PAG.Part47.normSq_coef_of
#print axioms PAG.Part47.thmA_exists
#print axioms PAG.Part47.thmB_of_mul_eq_one
#print axioms PAG.Part47.same_shell_classify
