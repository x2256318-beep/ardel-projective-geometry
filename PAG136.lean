/-
  PAG 2.0 Part 132（2026-10-21）— p = 2 を含む積のケットの ζ の素数部分
  1. 正確な p 部分の除算: v_p(a) = E、v_p(L) = F ≤ E ⇒ v_p(a / gcd(a, L)) = E − F
  2. 抽象形: z_i の p 部分が p^E ちょうど、p^E ∤ ∏_{j≠i} ord z_j、v_p(L) = F ⇒ ord(w^L) の p 部分は p^{E−F}
  3. ガウス和の位相は有限位数（導手 ≥ p²、すべての素数）
  4. p_i = 2、導手 2^{c_i+1}（c_i ≥ 3）、2^{c_i+1} ∤ ∏_{j≠i} ord z_j、∀ j ≠ i: 2^{c_i} ∤ ord χ_j
     ⇒ 積のケットの ζ の 2 部分はちょうど 4
-/
import PAG135

namespace PAG.Part136

open ZMod Finset

/-- **1. 正確な p 部分の除算**。 -/
theorem ppart_div_gcd {p : ℕ} (hp : p.Prime) (a L E F : ℕ) (ha0 : a ≠ 0) (hL0 : L ≠ 0)
    (haE : p ^ E ∣ a) (haE' : ¬ p ^ (E + 1) ∣ a) (hLF : p ^ F ∣ L) (hLF' : ¬ p ^ (F + 1) ∣ L) (hFE : F ≤ E) :
    p ^ (E - F) ∣ a / Nat.gcd a L ∧ ¬ p ^ (E - F + 1) ∣ a / Nat.gcd a L := by
  have hg0 : Nat.gcd a L ≠ 0 := Nat.gcd_ne_zero_left ha0
  have hq0 : a / Nat.gcd a L ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) (Nat.gcd_dvd_left a L)) (Nat.pos_of_ne_zero hg0)).ne'
  have hfa : a.factorization p = E := by
    have h1 := (hp.pow_dvd_iff_le_factorization ha0).mp haE
    have h2 : ¬ E + 1 ≤ a.factorization p := fun h => haE' ((hp.pow_dvd_iff_le_factorization ha0).mpr h)
    omega
  have hfL : L.factorization p = F := by
    have h1 := (hp.pow_dvd_iff_le_factorization hL0).mp hLF
    have h2 : ¬ F + 1 ≤ L.factorization p := fun h => hLF' ((hp.pow_dvd_iff_le_factorization hL0).mpr h)
    omega
  have hfq : (a / Nat.gcd a L).factorization p = E - F := by
    rw [Nat.factorization_div (Nat.gcd_dvd_left a L), Finsupp.tsub_apply, Nat.factorization_gcd ha0 hL0,
      Finsupp.inf_apply, hfa, hfL]
    omega
  constructor
  · exact (hp.pow_dvd_iff_le_factorization hq0).mpr (by omega)
  · intro h; have := (hp.pow_dvd_iff_le_factorization hq0).mp h; omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **2a. 積の位相の p 部分**: z_i の p 部分が p^E ちょうど、p^E ∤ ∏_{j≠i} ord z_j ⇒ ord(∏ z) の p 部分も p^E ちょうど。 -/
theorem ppart_prod {p : ℕ} [hp : Fact p.Prime] (z : ι → ℂ) (hz0 : ∀ j, orderOf (z j) ≠ 0) (i : ι) (E : ℕ)
    (hE : p ^ E ∣ orderOf (z i)) (hE' : ¬ p ^ (E + 1) ∣ orderOf (z i))
    (hcond : ¬ p ^ E ∣ ∏ j ∈ univ.erase i, orderOf (z j)) :
    p ^ E ∣ orderOf (∏ j, z j) ∧ ¬ p ^ (E + 1) ∣ orderOf (∏ j, z j) := by
  constructor
  · rw [← Finset.prod_erase_mul _ _ (mem_univ i)]
    apply PAG.Part131.pdvd_orderOf_mul p E _ _ hE (∏ j ∈ univ.erase i, orderOf (z j))
      (Finset.prod_ne_zero_iff.mpr (fun j _ => hz0 j)) _ hcond
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro j hj
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun j => orderOf (z j)) hj
    rw [hr, pow_mul, pow_orderOf_eq_one, one_pow]
  · intro h
    obtain ⟨j, -, hj⟩ := PAG.Part134.pow_dvd_finset_lcm hp.out (by omega) univ (fun j => orderOf (z j))
      (fun j _ => hz0 j) (h.trans (PAG.Part131.orderOf_prod_dvd_lcm z))
    by_cases hji : j = i
    · subst hji; exact hE' hj
    · exact hcond (((pow_dvd_pow p (by omega)).trans hj).trans
        (Finset.dvd_prod_of_mem (fun j => orderOf (z j)) (Finset.mem_erase.mpr ⟨hji, mem_univ j⟩)))

/-- **2b. w^L の p 部分は p^{E−F}**。 -/
theorem ppart_prod_pow {p : ℕ} [hp : Fact p.Prime] (z : ι → ℂ) (hz0 : ∀ j, orderOf (z j) ≠ 0) (i : ι) (E F L : ℕ)
    (hL0 : L ≠ 0) (hE : p ^ E ∣ orderOf (z i)) (hE' : ¬ p ^ (E + 1) ∣ orderOf (z i))
    (hcond : ¬ p ^ E ∣ ∏ j ∈ univ.erase i, orderOf (z j))
    (hLF : p ^ F ∣ L) (hLF' : ¬ p ^ (F + 1) ∣ L) (hFE : F ≤ E) :
    p ^ (E - F) ∣ orderOf ((∏ j, z j) ^ L) ∧ ¬ p ^ (E - F + 1) ∣ orderOf ((∏ j, z j) ^ L) := by
  have hw0 : orderOf (∏ j, z j) ≠ 0 := by
    intro h0
    have hb := PAG.Part131.orderOf_prod_dvd_lcm z
    rw [h0] at hb
    obtain ⟨x, -, hx⟩ := Finset.lcm_eq_zero_iff.mp (Nat.eq_zero_of_zero_dvd hb)
    exact hz0 x hx
  obtain ⟨h1, h2⟩ := ppart_prod z hz0 i E hE hE' hcond
  rw [orderOf_pow' _ hL0]
  exact ppart_div_gcd hp.out _ L E F hw0 hL0 h1 h2 hLF hLF' hFE

/-- **3. ガウス和の位相は有限位数**（導手 p^{c+1}、c ≥ 1、すべての素数）。 -/
theorem orderOf_gauss_ne_zero {p : ℕ} [hp : Fact p.Prime] (c : ℕ) (hc : 1 ≤ c)
    (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive) :
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (c + 1)) : ℝ) : ℂ)) ≠ 0 := by
  obtain ⟨M, hM, h⟩ := PAG.Part120.gauss_root_ge_two (c + 1) (by omega) χ hχ
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨M, hM, h⟩).orderOf_pos.ne'

/-- p = 2 の版（p を変数のまま）: ord z = 2^{c+1}、ord χ = 2^{c−1}（c ≥ 3）。 -/
theorem two_facts {p : ℕ} [hp : Fact p.Prime] (hp2 : p = 2) (c : ℕ) (hc : 3 ≤ c)
    (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive) :
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (c + 1)) : ℝ) : ℂ)) = 2 ^ (c + 1) ∧
    orderOf χ = 2 ^ (c - 1) := by
  subst hp2
  refine ⟨?_, PAG.Part135.orderOf_chi_two c (by omega) χ hχ⟩
  rcases Nat.even_or_odd (c + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have := PAG.Part130.orderOf_gauss_two_even (c + 1) m (by omega) (by omega) χ hχ
    push_cast; exact this
  · have := PAG.Part130.orderOf_gauss_two_odd (c + 1) m hm (by omega) χ hχ
    push_cast; exact this

section Ket

open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117 PAG.Part125 PAG.Part126 PAG.Part132

variable {n : ℕ} (q : Fin n → ℕ) [hq : ∀ i, Fact (q i).Prime] (K w c : Fin n → ℕ)

/-- **4. p_i = 2 の因子: ζ の 2 部分はちょうど 4**。 -/
theorem zeta_prod_two_part (hc : ∀ i, 1 ≤ c i) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (q i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (q i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := q i) (K i) (K i - (c i + 1) - w i)) (i : Fin n)
    (hqi : q i = 2) (hci : 3 ≤ c i)
    (hcond : ¬ 2 ^ (c i + 1) ∣ ∏ j ∈ univ.erase i,
      orderOf (gaussSum (χ j) stdAddChar / ((Real.sqrt ((q j : ℝ) ^ (c j + 1)) : ℝ) : ℂ)))
    (hχj : ∀ j, j ≠ i → ¬ 2 ^ (c i) ∣ orderOf (χ j)) :
    4 ∣ orderOf ((∏ i, cnorm (q i) (K i) (K i - (c i + 1) - w i)
        * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i))) ∧
    ¬ 8 ∣ orderOf ((∏ i, cnorm (q i) (K i) (K i - (c i + 1) - w i)
        * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i))) := by
  rw [zeta_prod_eq_pow q K w c h χ hχ t ht]
  set z : Fin n → ℂ := fun j => gaussSum (χ j) stdAddChar / ((Real.sqrt ((q j : ℝ) ^ (c j + 1)) : ℝ) : ℂ)
  obtain ⟨hz, ho⟩ := two_facts (p := q i) hqi (c i) hci (χ i) (hχ i)
  have hL0 : lcmF n (fun i => orderOf (χ i)) ≠ 0 := lcmF_ne_zero n _ (fun i => (orderOf_pos (χ i)).ne')
  have hLF : 2 ^ (c i - 1) ∣ lcmF n (fun i => orderOf (χ i)) := by
    rw [← ho]; exact dvd_lcmF n (fun i => orderOf (χ i)) i
  have hLF' : ¬ 2 ^ (c i - 1 + 1) ∣ lcmF n (fun i => orderOf (χ i)) := by
    intro h2
    rw [lcmF_eq] at h2
    obtain ⟨j, -, hj⟩ := PAG.Part134.pow_dvd_finset_lcm Nat.prime_two (by omega) univ (fun j => orderOf (χ j))
      (fun j _ => (orderOf_pos (χ j)).ne') h2
    by_cases hji : j = i
    · subst hji
      rw [ho, show c j - 1 + 1 = c j by omega] at hj
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hj
      omega
    · exact hχj j hji (by rwa [show c i - 1 + 1 = c i by omega] at hj)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := ppart_prod_pow (p := 2) z (fun j => orderOf_gauss_ne_zero (c j) (hc j) (χ j) (hχ j)) i
    (c i + 1) (c i - 1) _ hL0 (by rw [show z i = _ from rfl, hz])
    (by rw [show z i = _ from rfl, hz]
        intro h3; have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h3; omega)
    hcond hLF hLF' (by omega)
  rw [show c i + 1 - (c i - 1) = 2 by omega] at key
  exact ⟨by simpa using key.1, by simpa using key.2⟩

end Ket

end PAG.Part136

#print axioms PAG.Part136.ppart_div_gcd
#print axioms PAG.Part136.ppart_prod
#print axioms PAG.Part136.ppart_prod_pow
#print axioms PAG.Part136.orderOf_gauss_ne_zero
#print axioms PAG.Part136.two_facts
#print axioms PAG.Part136.zeta_prod_two_part
