/-
  PAG 2.0 Part 130（2026-10-21）— ζ の p 部分の定理から余分な仮定を除く
  1. 素数冪は lcm を割れば、どれかの因子を割る（2 項と Finset）
  2. ord χ ∣ φ(N)、p^{c+1} ∤ p^c (p−1)
  3. p 奇素数・導手 p^{c+1}: p^{c+2} ∤ ord z（ガウス和の位相）
  4. Part 127 の鋭い条件 ⇒ p_i^{c_i+2} ∤ ord w（Part 129 の第三の仮定は不要）
  5. ∀ j ≠ i, p_i^{c_i+1} ∤ ord χ_j ⇒ p_i^{c_i+1} ∤ L
  6. 積のケットの ζ の p_i 部分はちょうど p_i（二つの条件だけで）
  7. 鋭い条件の下で: q_i ∣ ord ζ ↔ ∀ j ≠ i, q_i^{c_i+1} ∤ ord χ_j
-/
import PAG133

namespace PAG.Part134

open ZMod Finset

/-- **1a. 2 項**。 -/
theorem pow_dvd_lcm_two {p : ℕ} (hp : p.Prime) {e a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : p ^ e ∣ Nat.lcm a b) : p ^ e ∣ a ∨ p ^ e ∣ b := by
  rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha hb), Nat.factorization_lcm ha hb,
    Finsupp.sup_apply] at h
  rcases le_max_iff.mp h with h | h
  · exact Or.inl ((hp.pow_dvd_iff_le_factorization ha).mpr h)
  · exact Or.inr ((hp.pow_dvd_iff_le_factorization hb).mpr h)

/-- **1b. Finset**。 -/
theorem pow_dvd_finset_lcm {ι : Type*} [DecidableEq ι] {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 1 ≤ e)
    (s : Finset ι) (f : ι → ℕ) (hf : ∀ j ∈ s, f j ≠ 0) (h : p ^ e ∣ s.lcm f) : ∃ j ∈ s, p ^ e ∣ f j := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.lcm_empty] at h
    have := Nat.le_of_dvd one_pos h
    have := Nat.one_lt_pow (by omega : e ≠ 0) hp.one_lt
    omega
  | insert a r har ih =>
    rw [Finset.lcm_insert] at h
    have hr0 : r.lcm f ≠ 0 := by
      intro h0
      obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h0
      exact hf x (mem_insert_of_mem hx) hx0
    rcases pow_dvd_lcm_two hp (hf a (mem_insert_self _ _)) hr0 h with h | h
    · exact ⟨a, mem_insert_self _ _, h⟩
    · obtain ⟨j, hj, hj'⟩ := ih (fun j hj => hf j (mem_insert_of_mem hj)) h
      exact ⟨j, mem_insert_of_mem hj, hj'⟩

/-- **2a. ord χ ∣ φ(N)**。 -/
theorem orderOf_dvd_totient {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : orderOf χ ∣ Nat.totient N := by
  apply orderOf_dvd_of_pow_eq_one
  apply MulChar.ext
  intro a
  have hφ : Nat.totient N ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  rw [MulChar.pow_apply' _ hφ, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one,
    map_one, MulChar.one_apply a.isUnit]

/-- **2b. p^{c+1} ∤ p^c (p−1)**。 -/
theorem not_pow_succ_dvd {p : ℕ} (hp : p.Prime) (c : ℕ) : ¬ p ^ (c + 1) ∣ p ^ c * (p - 1) := by
  intro h
  rw [pow_succ] at h
  have h1 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos c) h
  have := Nat.le_of_dvd (by have := hp.two_le; omega) h1
  have := hp.two_le
  omega

/-- **7a. p^e ∣ L、p^{e+1} ∤ a ⇒ p ∤ a / gcd(a, L)**。 -/
theorem not_dvd_div_gcd {p : ℕ} (hp : p.Prime) (e a L : ℕ) (ha0 : a ≠ 0) (hL : p ^ e ∣ L)
    (ha : ¬ p ^ (e + 1) ∣ a) : ¬ p ∣ a / Nat.gcd a L := by
  obtain ⟨j, a', hpa', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha0 p hp.ne_one
  have hj : j ≤ e := by
    by_contra h; exact ha (dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) _)
  have hg : p ^ j ∣ Nat.gcd (p ^ j * a') L := Nat.dvd_gcd (dvd_mul_right _ _) ((pow_dvd_pow p hj).trans hL)
  intro hd
  have h1 := Nat.mul_dvd_mul hg hd
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)] at h1
  exact hpa' (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos j) h1)

variable {p : ℕ} [hp : Fact p.Prime]

/-- **3. p^{c+2} ∤ ord z**（p 奇素数、導手 p^{c+1}、c ≥ 1）。 -/
theorem not_pow_dvd_gauss (hp2 : p ≠ 2) (c : ℕ) (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ (c + 1)))
    (hχ : χ.IsPrimitive) :
    ¬ p ^ (c + 2) ∣ orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (c + 1)) : ℝ) : ℂ)) := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  intro h
  have hb := (PAG.Part128.orderOf_gauss_bounds hp2 (c + 1) (by omega) χ hχ).2
  have ho0 : orderOf χ ≠ 0 := (orderOf_pos χ).ne'
  have hpc0 : p ^ (c + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  rcases pow_dvd_lcm_two hp.out (Nat.lcm_ne_zero ho0 hpc0) (by norm_num) (h.trans hb) with h1 | h1
  · rcases pow_dvd_lcm_two hp.out ho0 hpc0 h1 with h2 | h2
    · have h3 := h2.trans (orderOf_dvd_totient χ)
      rw [Nat.totient_prime_pow hp.out (by omega), show c + 1 - 1 = c by omega] at h3
      exact not_pow_succ_dvd hp.out c ((pow_dvd_pow p (by omega)).trans h3)
    · have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h2; omega
  · have h5 : p ∣ 4 := (dvd_pow_self p (show c + 2 ≠ 0 by omega)).trans h1
    have h4 : p ∣ 2 ^ 2 := by norm_num; exact h5
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h4))

section Ket

open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117 PAG.Part125 PAG.Part126 PAG.Part132

variable {n : ℕ} (q : Fin n → ℕ) [hq : ∀ i, Fact (q i).Prime] (K w c : Fin n → ℕ)

/-- **4. 鋭い条件 ⇒ q_i^{c_i+2} ∤ ord w**。 -/
theorem hw2_of_hcond (hq2 : ∀ i, q i ≠ 2) (hc : ∀ i, 1 ≤ c i)
    (χ : ∀ i, DirichletCharacter ℂ (q i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive) (i : Fin n)
    (hcond : ¬ q i ^ (c i + 1) ∣ ∏ j ∈ univ.erase i,
      orderOf (gaussSum (χ j) stdAddChar / ((Real.sqrt ((q j : ℝ) ^ (c j + 1)) : ℝ) : ℂ))) :
    ¬ q i ^ (c i + 2) ∣ orderOf (∏ j, gaussSum (χ j) stdAddChar / ((Real.sqrt ((q j : ℝ) ^ (c j + 1)) : ℝ) : ℂ)) := by
  set z : Fin n → ℂ := fun j => gaussSum (χ j) stdAddChar / ((Real.sqrt ((q j : ℝ) ^ (c j + 1)) : ℝ) : ℂ)
  have hpos : ∀ j, orderOf (z j) ≠ 0 := by
    intro j h0
    have hb := (PAG.Part128.orderOf_gauss_bounds (hq2 j) (c j + 1) (by have := hc j; omega) (χ j) (hχ j)).2
    change orderOf (z j) ∣ _ at hb
    rw [h0] at hb
    exact Nat.lcm_ne_zero (Nat.lcm_ne_zero (orderOf_pos (χ j)).ne' (pow_ne_zero _ (hq j).out.ne_zero))
      (by norm_num) (Nat.eq_zero_of_zero_dvd hb)
  intro h
  change q i ^ (c i + 2) ∣ orderOf (∏ j, z j) at h
  obtain ⟨j, -, hj⟩ := pow_dvd_finset_lcm (hq i).out (by omega) univ (fun j => orderOf (z j))
    (fun j _ => hpos j) (h.trans (PAG.Part131.orderOf_prod_dvd_lcm z))
  by_cases hji : j = i
  · subst hji
    exact not_pow_dvd_gauss (hq2 j) (c j) (hc j) (χ j) (hχ j) hj
  · apply hcond
    exact ((pow_dvd_pow (q i) (by omega)).trans hj).trans
      (Finset.dvd_prod_of_mem (fun j => orderOf (z j)) (Finset.mem_erase.mpr ⟨hji, mem_univ j⟩))

/-- **5. ∀ j ≠ i, q_i^{c_i+1} ∤ ord χ_j ⇒ q_i^{c_i+1} ∤ L**。 -/
theorem hL_of_chi (χ : ∀ i, DirichletCharacter ℂ (q i ^ (c i + 1))) (i : Fin n)
    (hχj : ∀ j, j ≠ i → ¬ q i ^ (c i + 1) ∣ orderOf (χ j)) :
    ¬ q i ^ (c i + 1) ∣ lcmF n (fun i => orderOf (χ i)) := by
  intro h
  rw [lcmF_eq] at h
  obtain ⟨j, -, hj⟩ := pow_dvd_finset_lcm (hq i).out (by omega) univ (fun j => orderOf (χ j))
    (fun j _ => (orderOf_pos (χ j)).ne') h
  by_cases hji : j = i
  · subst hji
    have : NeZero (q j ^ (c j + 1)) := ⟨pow_ne_zero _ (hq j).out.ne_zero⟩
    have h3 := hj.trans (orderOf_dvd_totient (χ j))
    rw [Nat.totient_prime_pow (hq j).out (by omega), show c j + 1 - 1 = c j by omega] at h3
    exact not_pow_succ_dvd (hq j).out (c j) h3
  · exact hχj j hji hj

/-- **6. ζ の q_i 部分はちょうど q_i**（二つの条件だけで）。 -/
theorem zeta_prod_ppart' (hq2 : ∀ i, q i ≠ 2) (hc : ∀ i, 1 ≤ c i) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (q i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (q i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := q i) (K i) (K i - (c i + 1) - w i)) (i : Fin n)
    (hcond : ¬ q i ^ (c i + 1) ∣ ∏ j ∈ univ.erase i,
      orderOf (gaussSum (χ j) stdAddChar / ((Real.sqrt ((q j : ℝ) ^ (c j + 1)) : ℝ) : ℂ)))
    (hχj : ∀ j, j ≠ i → ¬ q i ^ (c i + 1) ∣ orderOf (χ j)) :
    q i ∣ orderOf ((∏ i, cnorm (q i) (K i) (K i - (c i + 1) - w i)
        * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i))) ∧
    ¬ q i ^ 2 ∣ orderOf ((∏ i, cnorm (q i) (K i) (K i - (c i + 1) - w i)
        * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i))) :=
  PAG.Part133.zeta_prod_ppart q K w c hq2 hc h χ hχ t ht i hcond (hL_of_chi q c χ i hχj)
    (hw2_of_hcond q c hq2 hc χ hχ i hcond)

/-- **7b. 鋭い条件の下で: q_i ∣ ord ζ ↔ ∀ j ≠ i, q_i^{c_i+1} ∤ ord χ_j**。 -/
theorem zeta_ppart_iff (hq2 : ∀ i, q i ≠ 2) (hc : ∀ i, 1 ≤ c i) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (q i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (q i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := q i) (K i) (K i - (c i + 1) - w i)) (i : Fin n)
    (hcond : ¬ q i ^ (c i + 1) ∣ ∏ j ∈ univ.erase i,
      orderOf (gaussSum (χ j) stdAddChar / ((Real.sqrt ((q j : ℝ) ^ (c j + 1)) : ℝ) : ℂ))) :
    q i ∣ orderOf ((∏ i, cnorm (q i) (K i) (K i - (c i + 1) - w i)
        * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i)))
      ↔ ∀ j, j ≠ i → ¬ q i ^ (c i + 1) ∣ orderOf (χ j) := by
  constructor
  · intro hd j hji hj
    set z : Fin n → ℂ := fun j => gaussSum (χ j) stdAddChar / ((Real.sqrt ((q j : ℝ) ^ (c j + 1)) : ℝ) : ℂ)
    have hpos : ∀ j, orderOf (z j) ≠ 0 := by
      intro j h0
      have hb := (PAG.Part128.orderOf_gauss_bounds (hq2 j) (c j + 1) (by have := hc j; omega) (χ j) (hχ j)).2
      change orderOf (z j) ∣ _ at hb
      rw [h0] at hb
      exact Nat.lcm_ne_zero (Nat.lcm_ne_zero (orderOf_pos (χ j)).ne' (pow_ne_zero _ (hq j).out.ne_zero))
        (by norm_num) (Nat.eq_zero_of_zero_dvd hb)
    have hw0 : orderOf (∏ j, z j) ≠ 0 := by
      intro h0
      have hb := PAG.Part131.orderOf_prod_dvd_lcm z
      rw [h0] at hb
      obtain ⟨x, -, hx⟩ := Finset.lcm_eq_zero_iff.mp (Nat.eq_zero_of_zero_dvd hb)
      exact hpos x hx
    rw [orderOf_zeta_prod q K w c h χ hχ t ht] at hd
    exact not_dvd_div_gcd (hq i).out (c i + 1) _ _ hw0
      (hj.trans (dvd_lcmF n (fun i => orderOf (χ i)) j)) (hw2_of_hcond q c hq2 hc χ hχ i hcond) hd
  · intro hχj
    exact (zeta_prod_ppart' q K w c hq2 hc h χ hχ t ht i hcond hχj).1

end Ket

end PAG.Part134

#print axioms PAG.Part134.pow_dvd_lcm_two
#print axioms PAG.Part134.pow_dvd_finset_lcm
#print axioms PAG.Part134.orderOf_dvd_totient
#print axioms PAG.Part134.not_pow_succ_dvd
#print axioms PAG.Part134.not_pow_dvd_gauss
#print axioms PAG.Part134.hw2_of_hcond
#print axioms PAG.Part134.hL_of_chi
#print axioms PAG.Part134.zeta_prod_ppart'
#print axioms PAG.Part134.not_dvd_div_gcd
#print axioms PAG.Part134.zeta_ppart_iff
