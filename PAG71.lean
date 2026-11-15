/-
  PAG 2.0 Part 67（2026-10-19）— p = 2 の乗積表（χ_{s,j} の塔）
  |w, d, s, j⟩ := |w, χ_{s,j}⟩（法 2^(d+3)）、j, j' 奇数、ν = ν₂(j+j')。
  (D2) 同じ殻・1 ≤ ν ≤ d：|w,d,s,j⟩ ⋆ |w,d,s',j'⟩ = C·|w+ν, d−ν, s+s', (j+j')/2^ν⟩
  (M2) 混合（PAG66）：|w,d,s,j⟩ ⋆ |w+(d−d'),d',s',j'⟩ = C·|w, d, s+s', j + 2^(d−d') j'⟩
  (B2)(L2) M ∣ j+j' のとき s+s' の偶奇で定理 B（PAG50 p2_caseB）または導手 4（p2_caseA4）
-/
import PAG70

namespace PAG.Part71

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part66 PAG.Part69

/-- (D2) **p = 2 の降下の添字表示**。 -/
theorem p2_table_descent (K w d : ℕ) (hK : w + (d + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j')
    (hν1 : 1 ≤ padicValNat 2 (j + j')) (hνd : padicValNat 2 (j + j') ≤ d)
    (hK' : w + padicValNat 2 (j + j') + (d - padicValNat 2 (j + j') + 3) ≤ K) :
    ∃ C : ℂ, Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (d + 3) - w) : ℝ) ∧
      conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j'))
        = C • ket (p := 2) K (w + padicValNat 2 (j + j')) (d - padicValNat 2 (j + j') + 3) hK'
          (chiSJ (d - padicValNat 2 (j + j')) (s + s') ((j + j') / 2 ^ padicValNat 2 (j + j'))) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ν := padicValNat 2 (j + j') with hνdef
  have hJ : j + j' ≠ 0 := by have := hj.pos; omega
  have hdvd : 2 ^ ν ∣ j + j' := pow_padicValNat_dvd
  have hndvd : ¬ 2 ^ (ν + 1) ∣ j + j' := pow_succ_padicValNat_not_dvd hJ
  set q := (j + j') / 2 ^ ν with hqdef
  have hJq : j + j' = 2 ^ ν * q := (Nat.mul_div_cancel' hdvd).symm
  have hq : Odd q := by
    rw [Nat.odd_iff]
    by_contra h
    have h2 : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
    apply hndvd
    rw [hJq, pow_succ]
    exact Nat.mul_dvd_mul_left _ h2
  have hψ : (chiSJ (d - ν) (s + s') q).IsPrimitive := (chiSJ_prim_iff _ _).mpr hq
  have hprod : ∀ x, (chiSJ d s j * chiSJ d s' j') x
      = chiSJ (d - ν) (s + s') q (ZMod.castHom (pow_dvd_pow 2 (by omega : d - ν + 3 ≤ d + 2 + 1)) _ x) := by
    intro x
    have hc := changeLevel_chiSJ d (d - ν) (by omega) (s + s') q
    rw [show d - (d - ν) = ν by omega, ← hJq] at hc
    rw [chiSJ_mul, ← hc]
    exact PAG.Part47.changeLevel_apply_cast (p := 2) (K := d + 2 + 1) (by omega) (by omega) _ x
  exact thmA_with_psi (p := 2) K w (d + 2) ν (w + ν) (d - ν + 3) (by omega) hK rfl (by omega) hK' _ _
    ((chiSJ_prim_iff s j).mpr hj) ((chiSJ_prim_iff s' j').mpr hj') _ hψ hprod

end PAG.Part71

#print axioms PAG.Part71.p2_table_descent
