/-
  PAG 2.0 Part 122（2026-10-21）— 反復 lcm と Finset.lcm の一致、積のケットの ζ の冪根性
  1. o_i ∣ lcmF o、共通倍数 m について lcmF o ∣ m、lcmF o = Finset.univ.lcm o
  2. 積のケットの位相 ζ = (∏ λ_i^{-1/2} 𝓕k_i(t_i))^L は、各導手が p_i² 以上なら 1 の冪根
-/
import PAG125

namespace PAG.Part126

open ZMod Finset PAG.Part125

/-- **1a. o_i ∣ lcmF o**。 -/
theorem dvd_lcmF : ∀ (n : ℕ) (o : Fin n → ℕ) (i : Fin n), o i ∣ lcmF n o := by
  intro n
  induction n with
  | zero => intro o i; exact Fin.elim0 i
  | succ n ih =>
    intro o i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.dvd_lcm_left _ _
    · exact (ih (fun j => o j.succ) j).trans (Nat.dvd_lcm_right _ _)

/-- **1b. lcmF は最小の共通倍数**。 -/
theorem lcmF_dvd : ∀ (n : ℕ) (o : Fin n → ℕ) (m : ℕ), (∀ i, o i ∣ m) → lcmF n o ∣ m := by
  intro n
  induction n with
  | zero => intro o m _; exact one_dvd m
  | succ n ih =>
    intro o m h
    exact Nat.lcm_dvd (h 0) (ih (fun j => o j.succ) m (fun j => h j.succ))

/-- **1c. lcmF = Finset.univ.lcm**。 -/
theorem lcmF_eq (n : ℕ) (o : Fin n → ℕ) : lcmF n o = (univ : Finset (Fin n)).lcm o := by
  apply Nat.dvd_antisymm
  · exact lcmF_dvd n o _ (fun i => Finset.dvd_lcm (Finset.mem_univ i))
  · exact Finset.lcm_dvd (fun i _ => dvd_lcmF n o i)

/-! ## 2. 積のケットの ζ -/

section Ket

open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part120

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)

/-- **2. 積のケットの位相は 1 の冪根**（各導手 p_i^{c_i+1}、c_i ≥ 1）。 -/
theorem zeta_root_prod (hc : ∀ i, 1 ≤ c i) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := p i) (K i) (K i - (c i + 1) - w i)) :
    ∃ M : ℕ, 0 < M ∧
      ((∏ i, cnorm (p i) (K i) (K i - (c i + 1) - w i) * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i))
        ^ lcmF n (fun i => orderOf (χ i))) ^ M = 1 := by
  have hN := fun i => zeta_root_ge_two (K i) (w i) (c i) (hc i) (h i) (χ i) (hχ i) (t i) (ht i)
  choose N hNpos hNeq using hN
  refine ⟨∏ i, N i, Finset.prod_pos (fun i _ => hNpos i), ?_⟩
  rw [← pow_mul, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  obtain ⟨q, hq⟩ := dvd_lcmF n (fun i => orderOf (χ i)) i
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
  rw [hq, hr, show orderOf (χ i) * q * (N i * r) = orderOf (χ i) * N i * (q * r) by ring, pow_mul, pow_mul,
    pow_mul _ (orderOf (χ i)) (N i), hNeq i, one_pow, one_pow]

end Ket

end PAG.Part126

#print axioms PAG.Part126.dvd_lcmF
#print axioms PAG.Part126.lcmF_dvd
#print axioms PAG.Part126.lcmF_eq
#print axioms PAG.Part126.zeta_root_prod
