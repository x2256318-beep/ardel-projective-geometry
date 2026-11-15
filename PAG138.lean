/-
  PAG 2.0 Part 134（2026-10-21）— 導手 p^{2m} のガウス和のひねり公式
  N = p^c、c = 2m（m ≥ 1）について
  1. 停留点 u₀: χ 原始なら ∀ y, χ(1 + p^m y) e(p^m u₀ y) = 1 をみたす単元 u₀ がある
  2. ひねり公式: ψ(1 + p^m y) = 1（∀ y）なら τ(χψ) = ψ(u₀) τ(χ)（u₀ は ψ によらない）
  3. ψ が法 p の指標の持ち上げなら 2 の仮定をみたす
  4. 系: z(χψ) = ψ(u₀) z(χ)、z = τ/√(p^c)
-/
import PAG137

namespace PAG.Part138

open ZMod Finset PAG.Part118

variable {p : ℕ} [hp : Fact p.Prime]

section Even

variable {c m : ℕ} (hc : c = 2 * m)

include hc in
/-- **1. 停留点の存在**。 -/
theorem exists_stationary (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧
      ∀ y, phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u₀ * y) = 1 := by
  classical
  have hτ := gauss_eq_sum_S (p := p) hc χ
  have hτ0 := PAG.Part16.gaussSum_ne_zero hχ
  rw [hτ] at hτ0
  obtain ⟨u₀, hu₀S, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ0
  have hχu₀ : χ u₀ ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  exact ⟨u₀, by by_contra hn; exact hχu₀ (MulChar.map_nonunit χ hn), (Finset.mem_filter.mp hu₀S).2⟩

include hc in
/-- **2. ひねり公式**。 -/
theorem gauss_twist (χ ψ : DirichletCharacter ℂ (p ^ c))
    (hψ : ∀ y : ZMod (p ^ c), ψ (1 + (p : ZMod (p ^ c)) ^ m * y) = 1)
    (u₀ : ZMod (p ^ c)) (hu₀ : IsUnit u₀)
    (hS₀ : ∀ y, phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u₀ * y) = 1) :
    gaussSum (χ * ψ) stdAddChar = ψ u₀ * gaussSum χ stdAddChar := by
  classical
  have hphi : ∀ y, phi (m := m) (χ * ψ) y = phi (m := m) χ y := by
    intro y; simp only [phi, MulChar.mul_apply, hψ, mul_one]
  have hS₀' : ∀ y, phi (m := m) (χ * ψ) y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u₀ * y) = 1 := by
    intro y; rw [hphi]; exact hS₀ y
  rw [gauss_eq_sum_S (p := p) hc (χ * ψ), gauss_eq_sum_S (p := p) hc χ]
  simp only [hphi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hS := (Finset.mem_filter.mp hu).2
  have hS' : ∀ y, phi (m := m) (χ * ψ) y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u * y) = 1 := by
    intro y; rw [hphi]; exact hS y
  rw [const_on_S (p := p) hc (χ * ψ) u₀ u hu₀ hS₀' hS', const_on_S (p := p) hc χ u₀ u hu₀ hS₀ hS,
    MulChar.mul_apply]
  ring

omit hc in
/-- **3. 法 p の指標の持ち上げは仮定をみたす**（m ≥ 1）。 -/
theorem lift_trivial (hm : 1 ≤ m) (ψ₀ : DirichletCharacter ℂ p) (hpc : p ∣ p ^ c)
    (y : ZMod (p ^ c)) (hu : IsUnit (1 + (p : ZMod (p ^ c)) ^ m * y)) :
    DirichletCharacter.changeLevel hpc ψ₀ (1 + (p : ZMod (p ^ c)) ^ m * y) = 1 := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ₀ hpc hu.unit
  rw [IsUnit.unit_spec] at this
  rw [this, ZMod.cast_add hpc, ZMod.cast_one hpc, ZMod.cast_mul hpc, ZMod.cast_pow hpc, ZMod.cast_natCast hpc,
    ZMod.natCast_self, zero_pow (by omega), zero_mul, add_zero, map_one]

include hc in
/-- **4. 系: z(χψ) = ψ(u₀) z(χ)**。 -/
theorem phase_twist (χ ψ : DirichletCharacter ℂ (p ^ c))
    (hψ : ∀ y : ZMod (p ^ c), ψ (1 + (p : ZMod (p ^ c)) ^ m * y) = 1)
    (u₀ : ZMod (p ^ c)) (hu₀ : IsUnit u₀)
    (hS₀ : ∀ y, phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u₀ * y) = 1) :
    gaussSum (χ * ψ) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)
      = ψ u₀ * (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) := by
  rw [gauss_twist hc χ ψ hψ u₀ hu₀ hS₀, mul_div_assoc]

end Even

end PAG.Part138

#print axioms PAG.Part138.exists_stationary
#print axioms PAG.Part138.gauss_twist
#print axioms PAG.Part138.lift_trivial
#print axioms PAG.Part138.phase_twist
