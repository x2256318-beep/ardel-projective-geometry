/-
  PAG 2.0 Part 72（2026-10-19）— p = 2 版の結論のレベルでの排他性
  p = 2・同じ殻で像 F が C·|u, m, ψ⟩（C ≠ 0、ψ 原始）と書けるなら
    ¬ (M ∣ J ∧ s+s' 偶数)（(B2) ではない）、かつ
    M ∤ J なら u = w + ν₂(J)、m = d − ν + 3；M ∣ J なら u = w + d + 1、m = 2
-/
import PAG75

namespace PAG.Part76

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part48 PAG.Part51 PAG.Part72 PAG.Part73
  PAG.Part75

/-- **像から場合が決まる（p = 2・同じ殻）**。 -/
theorem p2_outcome_determines {d : ℕ} (K w : ℕ) (hK : w + (d + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j')
    (u m : ℕ) (hm : 1 ≤ m) (hu : u + m ≤ K) (ψ : DirichletCharacter ℂ (2 ^ m)) (hψ : ψ.IsPrimitive) (C : ℂ)
    (hC : C ≠ 0)
    (hF : conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j'))
      = C • ket (p := 2) K u m hu ψ) :
    ¬ (2 ^ (d + 1) ∣ j + j' ∧ Even (s + s')) ∧
    (¬ 2 ^ (d + 1) ∣ j + j' → u = w + padicValNat 2 (j + j') ∧ m = d - padicValNat 2 (j + j') + 3) ∧
    (2 ^ (d + 1) ∣ j + j' → u = w + (d + 1) ∧ m = 2) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := p2_same_shell_table K w hK s j s' j' hj hj'
  simp only at hT
  rcases hT with ⟨hD, h, C', hC', e⟩ | ⟨hM, hs, C', hC', e⟩ | ⟨hM, hs, e⟩
  · rw [hF] at e
    have hJ : j + j' ≠ 0 := by have := hj.pos; omega
    have hq : Odd ((j + j') / 2 ^ padicValNat 2 (j + j')) := by
      rw [Nat.odd_iff]
      by_contra hne
      have h2 : 2 ∣ (j + j') / 2 ^ padicValNat 2 (j + j') := Nat.dvd_of_mod_eq_zero (by omega)
      apply pow_succ_padicValNat_not_dvd (p := 2) hJ
      have hJq := (Nat.mul_div_cancel' (pow_padicValNat_dvd (p := 2) (n := j + j'))).symm
      have key : 2 ^ (padicValNat 2 (j + j') + 1) ∣
          2 ^ padicValNat 2 (j + j') * ((j + j') / 2 ^ padicValNat 2 (j + j')) := by
        rw [pow_succ]; exact Nat.mul_dvd_mul_left _ h2
      exact dvd_trans key (dvd_of_eq hJq.symm)
    have hψ' := (chiSJ_prim_iff (d := d - padicValNat 2 (j + j')) (s + s') _).mpr hq
    obtain ⟨hu', hm', -⟩ := ket_rep_unique (p := 2) K u m _ _ hm (by omega) hu h ψ hψ _ hψ' C C' hC e
    exact ⟨fun h' => hD h'.1, fun _ => ⟨hu', hm'⟩, fun h' => absurd h' hD⟩
  · rw [hF] at e
    obtain ⟨hu', hm', -⟩ := ket_rep_unique (p := 2) K u m _ _ hm (by omega) hu _ ψ hψ _ chi4_prim C C' hC e
    exact ⟨fun h' => (Nat.not_even_iff_odd.mpr hs) h'.2, fun h' => absurd hM h', fun _ => ⟨hu', hm'⟩⟩
  · exfalso
    rw [hF] at e
    exact ket_ne_ballB (p := 2) K u m w (d + 2) hm hu ψ C _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) e

end PAG.Part76

#print axioms PAG.Part76.p2_outcome_determines
