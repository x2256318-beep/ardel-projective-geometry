/-
  PAG 2.0 Part 142（2026-10-22）— ひねりの軌道の中での位相・桁の等分配
  χ 原始 mod p^c（c ≥ 2）、ψ₀ は法 p の指標、ψ₀↑ はその持ち上げ、z = τ/√(p^c)
  1. 評価準同型 ψ₀ ↦ ψ₀(a)（a 単元）
  2. z(χ·ψ₀↑) = ψ₀(ū₀) · z(χ)（ū₀ = u₀ mod p）
  3. 等分配: 任意の N について ψ₀ ↦ z(χ·ψ₀↑)^N の値はその像の上で等しい重複度をもつ
-/
import PAG145

namespace PAG.Part146

open ZMod Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. 評価準同型**。 -/
noncomputable def evalHom (a : ZMod p) (ha : IsUnit a) : DirichletCharacter ℂ p →* ℂ where
  toFun ψ := ψ a
  map_one' := MulChar.one_apply ha
  map_mul' ψ ψ' := MulChar.mul_apply ψ ψ' a

/-- 桁の準同型 ψ₀ ↦ ψ₀(a)^N。 -/
noncomputable def digitHom (a : ZMod p) (ha : IsUnit a) (N : ℕ) : DirichletCharacter ℂ p →* ℂ :=
  (powMonoidHom N).comp (evalHom a ha)

/-- **2. 位相のひねり**（持ち上げの値を法 p で）。 -/
theorem phase_twist_cast (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive)
    (hpc : p ∣ p ^ c) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧ ∀ ψ₀ : DirichletCharacter ℂ p,
      gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)
        = ψ₀ (u₀.cast : ZMod p) * (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) := by
  obtain ⟨u₀, hu, h⟩ := PAG.Part139.gauss_twist_all c hc χ hχ hpc
  refine ⟨u₀, hu, fun ψ₀ => ?_⟩
  have e := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ₀ hpc hu.unit
  rw [IsUnit.unit_spec] at e
  rw [h ψ₀, e, mul_div_assoc]

/-- **3. 等分配**: 値ごとの重複度は像の上で一定。 -/
theorem twist_digit_uniform (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive)
    (hpc : p ∣ p ^ c) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧ ∀ (N : ℕ) (x y : ℂ),
      x ∈ Set.range (fun ψ₀ : DirichletCharacter ℂ p =>
        (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N) →
      y ∈ Set.range (fun ψ₀ : DirichletCharacter ℂ p =>
        (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N) →
      #{ψ₀ : DirichletCharacter ℂ p |
          (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N = x}
        = #{ψ₀ : DirichletCharacter ℂ p |
          (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N = y} := by
  classical
  obtain ⟨u₀, hu, h⟩ := phase_twist_cast c hc χ hχ hpc
  refine ⟨u₀, hu, fun N x y hx hy => ?_⟩
  set z := gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)
  have hz0 : z ^ N ≠ 0 := by
    apply pow_ne_zero
    apply div_ne_zero (PAG.Part16.gaussSum_ne_zero hχ)
    have : (0 : ℝ) < Real.sqrt ((p : ℝ) ^ c) := Real.sqrt_pos.mpr (pow_pos (by exact_mod_cast hp.out.pos) _)
    exact_mod_cast this.ne'
  have hpc' : p ∣ p ^ c := hpc
  have hū : IsUnit (u₀.cast : ZMod p) := hu.map (ZMod.castHom hpc (ZMod p))
  set D := digitHom (u₀.cast : ZMod p) hū N
  have hD : ∀ ψ₀, (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar
      / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N = D ψ₀ * z ^ N := by
    intro ψ₀; rw [h ψ₀, mul_pow]; rfl
  have hset : ∀ w : ℂ, #{ψ₀ : DirichletCharacter ℂ p |
      (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N = w}
      = #{ψ₀ : DirichletCharacter ℂ p | D ψ₀ = w / z ^ N} := by
    intro w; congr 1; ext ψ₀; simp only [Finset.mem_filter, mem_univ, true_and, hD]
    constructor
    · intro e; rw [← e, mul_div_cancel_right₀ _ hz0]
    · intro e; rw [e, div_mul_cancel₀ _ hz0]
  rw [hset x, hset y]
  apply MonoidHom.card_fiber_eq_of_mem_range D
  · obtain ⟨ψ₀, hψ⟩ := hx
    exact ⟨ψ₀, by simp only at hψ; rw [← hψ, hD, mul_div_cancel_right₀ _ hz0]⟩
  · obtain ⟨ψ₀, hψ⟩ := hy
    exact ⟨ψ₀, by simp only at hψ; rw [← hψ, hD, mul_div_cancel_right₀ _ hz0]⟩

end PAG.Part146

#print axioms PAG.Part146.evalHom
#print axioms PAG.Part146.digitHom
#print axioms PAG.Part146.phase_twist_cast
#print axioms PAG.Part146.twist_digit_uniform
