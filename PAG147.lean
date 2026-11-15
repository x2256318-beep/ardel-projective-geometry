/-
  PAG 2.0 Part 143（2026-10-22）— 評価の像の大きさ: 値が原始 ord(a) 乗根になる指標の存在
  a ∈ (ℤ/p)ˣ、d = ord a、ψ ↦ ψ(a) の像（ℂˣ の有限部分群、巡回）
  1. Nat の補題: e ∣ d、d > 0、どの素数 q ∣ d でも e ∤ d/q ⇒ e = d
  2. 像の大きさ = d
  3. ψ(a) が 1 の原始 d 乗根となる ψ が存在する
-/
import PAG146

namespace PAG.Part147

open ZMod Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. Nat の補題**。 -/
theorem eq_of_dvd_not_dvd_div (e d : ℕ) (hd : 0 < d) (he : e ∣ d)
    (h : ∀ q, q.Prime → q ∣ d → ¬ e ∣ d / q) : e = d := by
  obtain ⟨r, hr⟩ := he
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; omega)
  by_contra hne
  have hr1 : r ≠ 1 := by rintro rfl; omega
  obtain ⟨q, hq, hqr⟩ := Nat.exists_prime_and_dvd hr1
  apply h q hq (hr ▸ dvd_mul_of_dvd_right hqr e)
  obtain ⟨s, hs⟩ := hqr
  refine ⟨s, ?_⟩
  rw [hr, hs, show e * (q * s) = q * (e * s) by ring, Nat.mul_div_cancel_left _ hq.pos]

/-- 評価を ℂˣ に値をとる準同型として。 -/
noncomputable def evalUnits (a : ZMod p) (ha : IsUnit a) : DirichletCharacter ℂ p →* ℂˣ :=
  (PAG.Part146.evalHom a ha).toHomUnits

theorem evalUnits_val (a : ZMod p) (ha : IsUnit a) (ψ : DirichletCharacter ℂ p) :
    ((evalUnits a ha ψ : ℂˣ) : ℂ) = ψ a := rfl

/-- **2. 像の大きさ = ord a**。 -/
theorem card_range_eval (a : (ZMod p)ˣ) :
    Nat.card (evalUnits (a : ZMod p) a.isUnit).range = orderOf a := by
  classical
  set f := evalUnits (a : ZMod p) a.isUnit
  rw [← IsCyclic.exponent_eq_card]
  set d := orderOf a
  have hd : 0 < d := orderOf_pos a
  apply eq_of_dvd_not_dvd_div _ d hd
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨x, ψ, rfl⟩
    apply Subtype.ext
    apply Units.ext
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
    rw [evalUnits_val, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  · intro q hq hqd hdiv
    have hlt : d / q < d := Nat.div_lt_self hd hq.one_lt
    have hpos : 0 < d / q := Nat.div_pos (Nat.le_of_dvd hd hqd) hq.pos
    have hne : ((a ^ (d / q) : (ZMod p)ˣ) : ZMod p) ≠ 1 := by
      intro h1
      have := orderOf_le_of_pow_eq_one hpos (Units.ext h1)
      omega
    obtain ⟨ψ, hψ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hne
    apply hψ
    have hx : (⟨f ψ, ψ, rfl⟩ : f.range) ^ (d / q) = 1 := by
      obtain ⟨r, hr⟩ := hdiv
      rw [hr, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
    have hx' := congrArg (fun y : f.range => ((y : ℂˣ) : ℂ)) hx
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one] at hx'
    rw [evalUnits_val] at hx'
    rw [Units.val_pow_eq_pow_val, map_pow, hx']

/-- **3. ψ(a) が 1 の原始 ord(a) 乗根となる ψ が存在する**。 -/
theorem exists_primitive_value (a : (ZMod p)ˣ) :
    ∃ ψ : DirichletCharacter ℂ p, IsPrimitiveRoot (ψ a) (orderOf a) := by
  set f := evalUnits (a : ZMod p) a.isUnit
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := f.range)
  rw [card_range_eval a] at hg
  obtain ⟨ψ, hψ⟩ := g.2
  refine ⟨ψ, ?_⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  rw [← evalUnits_val _ a.isUnit, orderOf_units, show f ψ = (g : ℂˣ) from hψ, ← hg, Subgroup.orderOf_coe]

end PAG.Part147

#print axioms PAG.Part147.eq_of_dvd_not_dvd_div
#print axioms PAG.Part147.evalUnits
#print axioms PAG.Part147.card_range_eval
#print axioms PAG.Part147.exists_primitive_value
