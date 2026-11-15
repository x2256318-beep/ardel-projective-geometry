/-
  PAG 2.0 Part 62（2026-10-19）— p = 2 の混合の場合の添字表示
  法 2^(d'+3) ⊂ 2^(d+3)（d' ≤ d）、χ_{s,j}（PAG44）について
  1. ζ_d^(2^(d−d')) = ζ_{d'}
  2. changeLevel(χ_{s',j'}) = χ_{s', 2^(d−d') j'}（生成元 −1, 5 は法によらず標準的なので r が確定する）
  3. 混合の行き先: |w, χ_{s,j}⟩ ⋆ |w+(d−d'), χ_{s',j'}⟩ = C·|w, χ_{s+s', j + 2^(d−d') j'}⟩、|C|² = λ
     （j 奇数・d' < d なら j + 2^(d−d') j' は奇数で、行き先は原始的）
-/
import PAG65

namespace PAG.Part66

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part45 PAG.Part47 Complex

/-- ζ_d^(2^(d−d')) = ζ_{d'}。 -/
theorem zeta_pow_sub (d d' : ℕ) (h : d' ≤ d) : zeta d ^ (2 ^ (d - d')) = zeta d' := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  have e : ((2 ^ (d + 1) : ℕ) : ℂ) = ((2 ^ (d - d') : ℕ) : ℂ) * ((2 ^ (d' + 1) : ℕ) : ℂ) := by
    rw [← Nat.cast_mul, ← pow_add, show d - d' + (d' + 1) = d + 1 by omega]
  rw [e]
  have h1 : ((2 ^ (d - d') : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero _ two_ne_zero)
  have h2 : ((2 ^ (d' + 1) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero _ two_ne_zero)
  field_simp

/-- **持ち上げの添字**: changeLevel(χ_{s',j'}) = χ_{s', 2^(d−d') j'}。 -/
theorem changeLevel_chiSJ (d d' : ℕ) (h : d' ≤ d) (s' j' : ℕ) :
    DirichletCharacter.changeLevel (pow_dvd_pow 2 (by omega : d' + 3 ≤ d + 3)) (chiSJ d' s' j')
      = chiSJ d s' (2 ^ (d - d') * j') := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply char_ext
  · rw [changeLevel_apply_cast (p := 2) (K := d + 3) (by omega) (by omega), map_ofNat, chiSJ_five, chiSJ_five,
      pow_mul, zeta_pow_sub d d' h]
  · rw [changeLevel_apply_cast (p := 2) (K := d + 3) (by omega) (by omega), map_neg, map_one, chiSJ_neg_one,
      chiSJ_neg_one]

/-- 混合の積指標は χ_{s+s', j + 2^(d−d') j'}。 -/
theorem mixed_chiSJ_apply (d d' : ℕ) (h : d' ≤ d) (s j s' j' : ℕ) (x : ZMod (2 ^ (d + 3))) :
    chiSJ d (s + s') (j + 2 ^ (d - d') * j') x
      = chiSJ d s j x * chiSJ d' s' j' (ZMod.castHom (pow_dvd_pow 2 (by omega : d' + 3 ≤ d + 3)) _ x) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← chiSJ_mul, ← changeLevel_chiSJ d d' h, MulChar.coeToFun_mul, Pi.mul_apply,
    changeLevel_apply_cast (p := 2) (K := d + 3) (by omega) (by omega)]

/-- j 奇数・d' < d なら行き先は原始的。 -/
theorem mixed_chiSJ_prim (d d' : ℕ) (h : d' < d) (s j s' j' : ℕ) (hj : Odd j) :
    (chiSJ d (s + s') (j + 2 ^ (d - d') * j')).IsPrimitive := by
  rw [chiSJ_prim_iff]
  have : Even (2 ^ (d - d') * j') := by
    rw [even_iff_two_dvd]; exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
  exact hj.add_even this

/-- **p = 2 の混合の添字表示（ケット）**。 -/
theorem mixed_ket_chiSJ (d d' : ℕ) (h : d' < d) (K w : ℕ) (hK : w + (d + 3) ≤ K)
    (h₂ : w + (d - d') + (d' + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j') :
    ∃ C : ℂ, Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (d + 3) - w) : ℝ) ∧
      conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K (w + (d - d')) (d' + 3) h₂ (chiSJ d' s' j'))
        = C • ket (p := 2) K w (d + 3) hK (chiSJ d (s + s') (j + 2 ^ (d - d') * j')) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := PAG.Part65.mixed_general_psi (p := 2) K w (d + 2) (d - d') (w + (d - d')) (d' + 3) (by omega) hK rfl
    (by omega) h₂ (chiSJ d s j) ((chiSJ_prim_iff s j).mpr hj) (chiSJ d' s' j') ((chiSJ_prim_iff s' j').mpr hj')
    (chiSJ d (s + s') (j + 2 ^ (d - d') * j')) (mixed_chiSJ_prim d d' h s j s' j' hj)
    (fun x => mixed_chiSJ_apply d d' h.le s j s' j' x)
  exact e

end PAG.Part66

#print axioms PAG.Part66.zeta_pow_sub
#print axioms PAG.Part66.changeLevel_chiSJ
#print axioms PAG.Part66.mixed_chiSJ_apply
#print axioms PAG.Part66.mixed_chiSJ_prim
#print axioms PAG.Part66.mixed_ket_chiSJ
