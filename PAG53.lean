/-
  PAG 2.0 Part 49（2026-10-19）— p = 2 の χ_{s,j} ケット積の分類（一つの選言、ν = padicValNat 2 (j+j')）
  j, j' 奇数、同じ殻 w のとき、次のちょうど一つ:
  (a) s+s' 偶数 ∧ M ∣ j+j' ∧ conv = (−1)^s·ballB
  (b) M ∤ j+j' ∧ 1 ≤ ν ≤ d ∧ conv = C·|w+ν, ψ⟩、ψ は導手 2^(d+3−ν) の原始指標、|C|² = λ
  (c) M ∣ j+j' ∧ s+s' 奇数 ∧ conv = C·|w+d+1, ψ⟩、ψ は導手 4 の原始指標、|C|² = λ
-/
import PAG52

namespace PAG.Part53

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part48 PAG.Part50

variable {d : ℕ}

/-- **p = 2 の分類（一つの選言）**。 -/
theorem p2_classification (K w : ℕ) (hK : w + (d + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j') :
    (Even (s + s') ∧ 2 ^ (d + 1) ∣ j + j' ∧
      conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j'))
        = ((-1 : ℂ) ^ s) • ballB (p := 2) K w (d + 2)) ∨
    (¬ 2 ^ (d + 1) ∣ j + j' ∧ 1 ≤ padicValNat 2 (j + j') ∧ padicValNat 2 (j + j') ≤ d ∧
      ∃ u c, ∃ h : u + c ≤ K, u = w + padicValNat 2 (j + j') ∧ c = d + 3 - padicValNat 2 (j + j') ∧
        ∃ ψ : DirichletCharacter ℂ (2 ^ c), ψ.IsPrimitive ∧ ∃ C : ℂ,
          Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (d + 3) - w) : ℝ) ∧
          conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j'))
            = C • ket (p := 2) K u c h ψ) ∨
    (2 ^ (d + 1) ∣ j + j' ∧ Odd (s + s') ∧
      ∃ ψ : DirichletCharacter ℂ (2 ^ 2), ψ.IsPrimitive ∧ ∃ C : ℂ,
        Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (d + 3) - w) : ℝ) ∧
        conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j'))
          = C • ket (p := 2) K (w + (d + 1)) 2 (by omega) ψ) := by
  by_cases hM : 2 ^ (d + 1) ∣ j + j'
  · rcases Nat.even_or_odd (s + s') with hs | hs
    · exact Or.inl ⟨hs, hM, p2_caseB K w hK s j s' j' hj hs hM⟩
    · exact Or.inr (Or.inr ⟨hM, hs, p2_caseA4 K w hK s j s' j' hj hj' hs hM⟩)
  · right; left
    set ν := padicValNat 2 (j + j') with hνdef
    have hJ : j + j' ≠ 0 := by have := hj.pos; omega
    have hdvd : 2 ^ ν ∣ j + j' := pow_padicValNat_dvd
    have hndvd : ¬ 2 ^ (ν + 1) ∣ j + j' := pow_succ_padicValNat_not_dvd hJ
    have hν1 : 1 ≤ ν := by
      rcases Nat.eq_zero_or_pos ν with h0 | h0
      · exfalso; rw [h0, zero_add, pow_one] at hndvd; exact hndvd (even_iff_two_dvd.mp (hj.add_odd hj'))
      · exact h0
    have hνd : ν ≤ d := by
      by_contra hlt
      exact hM (dvd_trans (pow_dvd_pow 2 (by omega)) hdvd)
    refine ⟨hM, hν1, hνd, ?_⟩
    have hν : 2 ^ (d + 3 - (d + 3 - ν)) ∣ (j + j') ∧ ¬ 2 ^ (d + 4 - (d + 3 - ν)) ∣ (j + j') := by
      rw [show d + 3 - (d + 3 - ν) = ν by omega, show d + 4 - (d + 3 - ν) = ν + 1 by omega]
      exact ⟨hdvd, hndvd⟩
    obtain ⟨ψ, hψ, C, hC, hconv⟩ := p2_caseA K w hK s j s' j' hj hj' (m := d + 3 - ν) (by omega) (by omega) hν
    exact ⟨w + (d + 3 - (d + 3 - ν)), d + 3 - ν, by omega, by omega, rfl, ψ, hψ, C, hC, hconv⟩

/-- 法 8（d = 0）では (b) は起きない。 -/
theorem p2_mod8_no_b (j j' : ℕ) (hj : Odd j) (hj' : Odd j') :
    ¬ (¬ 2 ^ (0 + 1) ∣ j + j') := by
  rw [not_not, zero_add, pow_one]
  exact even_iff_two_dvd.mp (hj.add_odd hj')

end PAG.Part53

#print axioms PAG.Part53.p2_classification
#print axioms PAG.Part53.p2_mod8_no_b
