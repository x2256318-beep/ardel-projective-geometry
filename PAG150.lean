/-
  PAG 2.0 Part 146（2026-10-22）— 打ち消しが起こるかどうかの判定
  a ∈ (ℤ/q)ˣ、m = ord a / gcd(ord a, N)
  1. 桁の像 = 1 の m 乗根の全体 {x | x^m = 1}
  2. 打ち消しの個数 K ≠ 0 ↔ (A₀ B)^{N m} = 1
-/
import PAG149

namespace PAG.Part150

open ZMod Finset Polynomial

variable {q : ℕ} [hq : Fact q.Prime]

/-- 1 の m 乗根の個数は m 以下。 -/
theorem ncard_roots_le (m : ℕ) (hm : 0 < m) : ({x : ℂ | x ^ m = 1} : Set ℂ).ncard ≤ m := by
  classical
  have : ({x : ℂ | x ^ m = 1} : Set ℂ) = ↑(nthRootsFinset m (1 : ℂ)) := by
    ext x; simp [mem_nthRootsFinset hm]
  rw [this, Set.ncard_coe_finset, nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots m 1)

/-- **1. 桁の像 = 1 の m 乗根の全体**。 -/
theorem range_digit_eq (a : (ZMod q)ˣ) (N : ℕ) :
    (Set.range fun ψ : DirichletCharacter ℂ q => ψ (a : ZMod q) ^ N)
      = {x : ℂ | x ^ (orderOf a / Nat.gcd (orderOf a) N) = 1} := by
  set m := orderOf a / Nat.gcd (orderOf a) N
  have hm : orderOf (a ^ N) = m := orderOf_pow a
  have hm0 : 0 < m := hm ▸ orderOf_pos _
  have hsub : (Set.range fun ψ : DirichletCharacter ℂ q => ψ (a : ZMod q) ^ N) ⊆ {x : ℂ | x ^ m = 1} := by
    rintro _ ⟨ψ, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rw [← pow_mul, ← map_pow, ← Units.val_pow_eq_pow_val, pow_mul, ← hm, pow_orderOf_eq_one, Units.val_one,
      map_one]
  have hfin : ({x : ℂ | x ^ m = 1} : Set ℂ).Finite := by
    classical
    have : ({x : ℂ | x ^ m = 1} : Set ℂ) = ↑(nthRootsFinset m (1 : ℂ)) := by
      ext x; simp [mem_nthRootsFinset hm0]
    rw [this]; exact Finset.finite_toSet _
  apply Set.eq_of_subset_of_ncard_le hsub _ hfin
  rw [PAG.Part148.ncard_range_digit]
  exact ncard_roots_le m hm0

/-- **2. 打ち消しが起こる ↔ (A₀ B)^{N m} = 1**。 -/
theorem cancel_ne_zero_iff {p : ℕ} [hp : Fact p.Prime] (a : (ZMod q)ˣ) (A₀ B : ℂ) (hAB : A₀ * B ≠ 0)
    (E M' : ℕ) (hE : 1 ≤ E) (hM' : ¬ p ∣ M')
    (hdvd : ∀ ψ : DirichletCharacter ℂ q, orderOf (ψ (a : ZMod q) * A₀ * B) ∣ p ^ E * M') :
    #{ψ : DirichletCharacter ℂ q | ¬ p ^ E ∣ orderOf (ψ (a : ZMod q) * A₀ * B)} ≠ 0 ↔
      (A₀ * B) ^ (p ^ (E - 1) * M' * (orderOf a / Nat.gcd (orderOf a) (p ^ (E - 1) * M'))) = 1 := by
  classical
  set N := p ^ (E - 1) * M'
  set m := orderOf a / Nat.gcd (orderOf a) N
  have hw0 : (A₀ * B) ^ N ≠ 0 := pow_ne_zero _ hAB
  have hK : #{ψ : DirichletCharacter ℂ q | ¬ p ^ E ∣ orderOf (ψ (a : ZMod q) * A₀ * B)}
      = #{ψ : DirichletCharacter ℂ q | ψ (a : ZMod q) ^ N = ((A₀ * B) ^ N)⁻¹} := by
    congr 1; ext ψ
    simp only [Finset.mem_filter, mem_univ, true_and]
    rw [PAG.Part149.criterion_gen _ E M' hE hM' (hdvd ψ), not_not, mul_assoc, mul_pow]
    constructor
    · intro h; exact eq_inv_of_mul_eq_one_left h
    · intro h; rw [h, inv_mul_cancel₀ hw0]
  rw [hK, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨ψ, hψ⟩
    have hmem : ((A₀ * B) ^ N)⁻¹ ∈ Set.range fun ψ : DirichletCharacter ℂ q => ψ (a : ZMod q) ^ N :=
      ⟨ψ, (Finset.mem_filter.mp hψ).2⟩
    rw [range_digit_eq] at hmem
    simp only [Set.mem_ofPred_eq, inv_pow] at hmem
    rw [pow_mul]; exact inv_eq_one.mp hmem
  · intro h
    have hmem : ((A₀ * B) ^ N)⁻¹ ∈ Set.range fun ψ : DirichletCharacter ℂ q => ψ (a : ZMod q) ^ N := by
      rw [range_digit_eq]
      simp only [Set.mem_ofPred_eq, inv_pow]
      rw [← pow_mul, h, inv_one]
    obtain ⟨ψ, hψ⟩ := hmem
    exact ⟨ψ, Finset.mem_filter.mpr ⟨mem_univ _, hψ⟩⟩

end PAG.Part150

#print axioms PAG.Part150.ncard_roots_le
#print axioms PAG.Part150.range_digit_eq
#print axioms PAG.Part150.cancel_ne_zero_iff
