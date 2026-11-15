/-
  PAG 2.0 Part 144（2026-10-22）— 桁の像の大きさ ord(ū)/gcd(ord(ū), N)
  1. 値の集合 {ψ(a)} の個数 = ord a（Set.ncard 版）
  2. {ψ(a)^N} の個数 = ord a / gcd(ord a, N)（ψ(a)^N = ψ(a^N) と orderOf_pow）
  3. ひねりの軌道: {z(χ·ψ₀↑)^N} の個数 = ord ū₀ / gcd(ord ū₀, N)
-/
import PAG147

namespace PAG.Part148

open ZMod Finset PAG.Part147

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. 値の個数 = ord a**。 -/
theorem ncard_range_eval (a : (ZMod p)ˣ) :
    (Set.range fun ψ : DirichletCharacter ℂ p => ψ (a : ZMod p)).ncard = orderOf a := by
  rw [← card_range_eval a]
  have h1 : Nat.card (evalUnits (a : ZMod p) a.isUnit).range
      = (Set.range (evalUnits (a : ZMod p) a.isUnit)).ncard := by
    rw [← MonoidHom.coe_range]; exact Nat.card_coe_set_eq _
  have : (Set.range fun ψ : DirichletCharacter ℂ p => ψ (a : ZMod p))
      = Units.val '' Set.range (evalUnits (a : ZMod p) a.isUnit) := by
    rw [← Set.range_comp]; rfl
  rw [h1, this, Set.ncard_image_of_injective _ Units.val_injective]

/-- **2. 桁の値の個数 = ord a / gcd(ord a, N)**。 -/
theorem ncard_range_digit (a : (ZMod p)ˣ) (N : ℕ) :
    (Set.range fun ψ : DirichletCharacter ℂ p => ψ (a : ZMod p) ^ N).ncard = orderOf a / Nat.gcd (orderOf a) N := by
  have : (Set.range fun ψ : DirichletCharacter ℂ p => ψ (a : ZMod p) ^ N)
      = Set.range fun ψ : DirichletCharacter ℂ p => ψ ((a ^ N : (ZMod p)ˣ) : ZMod p) := by
    congr 1; funext ψ; rw [Units.val_pow_eq_pow_val, map_pow]
  rw [this, ncard_range_eval, orderOf_pow]

/-- **3. ひねりの軌道の桁の値の個数**。 -/
theorem ncard_twist_digit (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive)
    (hpc : p ∣ p ^ c) :
    ∃ ū : (ZMod p)ˣ, ∀ N : ℕ,
      (Set.range fun ψ₀ : DirichletCharacter ℂ p =>
        (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar
          / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N).ncard = orderOf ū / Nat.gcd (orderOf ū) N := by
  obtain ⟨u₀, hu, h⟩ := PAG.Part146.phase_twist_cast c hc χ hχ hpc
  have hū : IsUnit (u₀.cast : ZMod p) := hu.map (ZMod.castHom hpc (ZMod p))
  refine ⟨hū.unit, fun N => ?_⟩
  set z := gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)
  have hz0 : z ^ N ≠ 0 := by
    apply pow_ne_zero
    apply div_ne_zero (PAG.Part16.gaussSum_ne_zero hχ)
    have : (0 : ℝ) < Real.sqrt ((p : ℝ) ^ c) := Real.sqrt_pos.mpr (pow_pos (by exact_mod_cast hp.out.pos) _)
    exact_mod_cast this.ne'
  have e : (Set.range fun ψ₀ : DirichletCharacter ℂ p =>
        (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar
          / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N)
      = (fun w => w * z ^ N) '' Set.range fun ψ : DirichletCharacter ℂ p => ψ ((hū.unit : ZMod p)) ^ N := by
    rw [← Set.range_comp]
    congr 1; funext ψ₀
    simp only [Function.comp, IsUnit.unit_spec]
    rw [h ψ₀, mul_pow]
  rw [e, Set.ncard_image_of_injective _ (mul_left_injective₀ hz0), ncard_range_digit]

end PAG.Part148

#print axioms PAG.Part148.ncard_range_eval
#print axioms PAG.Part148.ncard_range_digit
#print axioms PAG.Part148.ncard_twist_digit
