/-
  PAG 2.0 Part 41（2026-10-19）— χ_{s,j} は法 2^(d+3) の指標をちょうど一度ずつ尽くす
  1. 指標は χ(5) と χ(−1) で決まる
  2. 全射: 任意の χ は χ_{s,j}（s < 2, j < M）
  3. 一意性: χ_{s,j} = χ_{s',j'} ⇔ s ≡ s' (mod 2) ∧ j ≡ j' (mod M)
  4. 全単射 Fin 2 × Fin M → 指標
  5. 自明: χ_{s,j} = 1 ⇔ s 偶数 ∧ M ∣ j（導手 1 の場合。導手公式が 3 つの場合すべてで閉じる）
-/
import PAG44

namespace PAG.Part45

open ZMod Finset PAG.Part37 PAG.Part44 Complex

variable {d : ℕ}

/-- 5^M = 1（法 2^(d+3)）。 -/
theorem five_pow_M : (5 : ZMod (2 ^ (d + 3))) ^ (2 ^ (d + 1)) = 1 := by
  have h := pow_orderOf_eq_one (five (d + 3))
  rw [orderOf_five'] at h
  rw [← five_val, ← Units.val_pow_eq_pow_val, h, Units.val_one]

/-- **指標は χ(5) と χ(−1) で決まる**。 -/
theorem char_ext (χ χ' : DirichletCharacter ℂ (2 ^ (d + 3)))
    (h5 : χ 5 = χ' 5) (h1 : χ (-1) = χ' (-1)) : χ = χ' := by
  apply MulChar.ext
  intro u
  rw [rep_spec u]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, five_val, map_mul, map_pow,
    h5, h1]

theorem neg_one_pow_C (s : ℕ) : (-1 : ℂ) ^ s = if s % 2 = 0 then 1 else -1 := by
  rw [neg_one_pow_mod]
  have := Nat.mod_lt s (by norm_num : 0 < 2)
  interval_cases (s % 2) <;> simp

/-- **全射**: 任意の指標は χ_{s,j}（s < 2, j < M）。 -/
theorem chiSJ_surj (χ : DirichletCharacter ℂ (2 ^ (d + 3))) :
    ∃ s < 2, ∃ j < 2 ^ (d + 1), χ = chiSJ d s j := by
  have : NeZero (2 ^ (d + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have h5 : χ 5 ^ (2 ^ (d + 1)) = 1 := by rw [← map_pow, five_pow_M, map_one]
  obtain ⟨j, hj, hjz⟩ := (zeta_prim (d := d)).eq_pow_of_pow_eq_one h5
  have hsq := PAG.Part9.chi_neg_one_sq χ
  have hpm : χ (-1) = 1 ∨ χ (-1) = -1 := by
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hpm with h1 | h1
  · refine ⟨0, by norm_num, j, hj, char_ext _ _ ?_ ?_⟩
    · rw [chiSJ_five, hjz]
    · rw [chiSJ_neg_one, h1, pow_zero]
  · refine ⟨1, by norm_num, j, hj, char_ext _ _ ?_ ?_⟩
    · rw [chiSJ_five, hjz]
    · rw [chiSJ_neg_one, h1, pow_one]

/-- **一意性**: χ_{s,j} = χ_{s',j'} ⇔ s ≡ s' (mod 2) ∧ j ≡ j' (mod M)。 -/
theorem chiSJ_eq_iff (s j s' j' : ℕ) :
    chiSJ d s j = chiSJ d s' j' ↔ s % 2 = s' % 2 ∧ j % 2 ^ (d + 1) = j' % 2 ^ (d + 1) := by
  constructor
  · intro h
    have e5 := congrArg (fun χ : DirichletCharacter ℂ (2 ^ (d + 3)) => χ 5) h
    have e1 := congrArg (fun χ : DirichletCharacter ℂ (2 ^ (d + 3)) => χ (-1)) h
    simp only [chiSJ_five, chiSJ_neg_one] at e5 e1
    rw [zeta_pow_mod j, zeta_pow_mod j'] at e5
    refine ⟨?_, (zeta_prim (d := d)).pow_inj (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity)) e5⟩
    rw [neg_one_pow_C, neg_one_pow_C] at e1
    have hs := Nat.mod_lt s (by norm_num : 0 < 2)
    have hs' := Nat.mod_lt s' (by norm_num : 0 < 2)
    interval_cases (s % 2) <;> interval_cases (s' % 2) <;> first | rfl | norm_num at e1
  · rintro ⟨hs, hj⟩
    apply char_ext
    · rw [chiSJ_five, chiSJ_five, zeta_pow_mod j, zeta_pow_mod j', hj]
    · rw [chiSJ_neg_one, chiSJ_neg_one, neg_one_pow_mod s, neg_one_pow_mod s', hs]

/-- **全単射** Fin 2 × Fin M → 法 2^(d+3) の指標。 -/
theorem chiSJ_bijective :
    Function.Bijective (fun x : Fin 2 × Fin (2 ^ (d + 1)) => chiSJ d (x.1 : ℕ) (x.2 : ℕ)) := by
  constructor
  · rintro ⟨s, j⟩ ⟨s', j'⟩ h
    have e := (chiSJ_eq_iff (d := d) s j s' j').mp h
    rw [Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt s'.isLt, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at e
    exact Prod.ext (Fin.ext e.1) (Fin.ext e.2)
  · intro χ
    obtain ⟨s, hs, j, hj, h⟩ := chiSJ_surj χ
    exact ⟨(⟨s, hs⟩, ⟨j, hj⟩), h.symm⟩

/-- χ_{0,0} = 1。 -/
theorem chiSJ_zero : chiSJ d 0 0 = 1 := by
  apply char_ext
  · rw [chiSJ_five, pow_zero, ← five_val, MulChar.one_apply_coe]
  · rw [chiSJ_neg_one, pow_zero]
    have := MulChar.one_apply_coe (R' := ℂ) (-1 : (ZMod (2 ^ (d + 3)))ˣ)
    simp only [Units.val_neg, Units.val_one] at this
    exact this.symm

/-- **自明 ⇔ s 偶数 ∧ M ∣ j**。 -/
theorem chiSJ_eq_one_iff (s j : ℕ) : chiSJ d s j = 1 ↔ Even s ∧ 2 ^ (d + 1) ∣ j := by
  rw [← chiSJ_zero, chiSJ_eq_iff, Nat.zero_mod, Nat.zero_mod, Nat.even_iff, Nat.dvd_iff_mod_eq_zero]

/-- **導手 1 ⇔ s 偶数 ∧ M ∣ j**（導手公式の第 3 の場合）。 -/
theorem chiSJ_conductor_one_iff (s j : ℕ) : (chiSJ d s j).conductor = 1 ↔ Even s ∧ 2 ^ (d + 1) ∣ j := by
  have : NeZero (2 ^ (d + 3)) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [← DirichletCharacter.eq_one_iff_conductor_eq_one, chiSJ_eq_one_iff]

end PAG.Part45

#print axioms PAG.Part45.five_pow_M
#print axioms PAG.Part45.char_ext
#print axioms PAG.Part45.neg_one_pow_C
#print axioms PAG.Part45.chiSJ_surj
#print axioms PAG.Part45.chiSJ_eq_iff
#print axioms PAG.Part45.chiSJ_bijective
#print axioms PAG.Part45.chiSJ_zero
#print axioms PAG.Part45.chiSJ_eq_one_iff
#print axioms PAG.Part45.chiSJ_conductor_one_iff
