/-
  PAG 2.0 Part 127（2026-10-21）— 積の位相の位数: 各素数の p 部分は消えないか
  1. k ∣ ord B、A^M = 1、gcd(k, M) = 1 ⇒ k ∣ ord(A B)
  2. 族 z_i（z_j^{B_j} = 1）で gcd(k_i, ∏_{j≠i} B_j) = 1、k_i ∣ ord z_i ⇒ k_i ∣ ord(∏ z)
  3. ord(∏ z) ∣ lcm(ord z_i)、位数が対ごとに互いに素なら ord(∏ z) = ∏ ord z_i
  4. ガウス和の位相の積 w = ∏ τ(χ_i)/√(p_i^{c_i})（相異なる奇素数、c_i ≥ 2）:
     p_i ∤ ∏_{j≠i} lcm(ord χ_j, p_j^{c_j}, 4) なら ∏ p_i^{c_i} ∣ ord w
  5. 鋭い形: p^c ∣ ord B、A^M = 1、p^c ∤ M ⇒ p^c ∣ ord(A B)
  6. p_i^{c_i} ∤ ∏_{j≠i} ord z_j なら p_i^{c_i} ∣ ord w
-/
import PAG130

namespace PAG.Part131

open Finset ZMod

/-- 互いに素な約数の積は割る（ℕ、Finset）。 -/
theorem prod_dvd_of_coprime_nat {ι : Type*} [DecidableEq ι] (t : Finset ι) (s : ι → ℕ) (n : ℕ)
    (hco : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Nat.Coprime (s i) (s j)) (h : ∀ i ∈ t, s i ∣ n) :
    ∏ i ∈ t, s i ∣ n := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a r har ih =>
    rw [Finset.prod_insert har]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · exact Nat.coprime_prod_right_iff.mpr (fun j hj => hco a (mem_insert_self _ _) j (mem_insert_of_mem hj)
        (fun he => har (he ▸ hj)))
    · exact h a (mem_insert_self _ _)
    · exact ih (fun i hi j hj => hco i (mem_insert_of_mem hi) j (mem_insert_of_mem hj))
        (fun i hi => h i (mem_insert_of_mem hi))

/-- **1. k ∣ ord B、A^M = 1、gcd(k, M) = 1 ⇒ k ∣ ord(A B)**。 -/
theorem dvd_orderOf_mul (A B : ℂ) (k M : ℕ) (hk : k ∣ orderOf B) (hA : A ^ M = 1) (hco : Nat.Coprime k M) :
    k ∣ orderOf (A * B) := by
  have h1 : (A * B) ^ (orderOf (A * B) * M) = 1 := by rw [pow_mul, pow_orderOf_eq_one, one_pow]
  rw [mul_pow, mul_comm (orderOf (A * B)) M, pow_mul A, hA, one_pow, one_mul] at h1
  have h2 : k ∣ M * orderOf (A * B) := hk.trans (orderOf_dvd_of_pow_eq_one h1)
  exact hco.dvd_of_dvd_mul_left h2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **2. 族の場合**。 -/
theorem dvd_orderOf_prod (z : ι → ℂ) (B k : ι → ℕ) (hB : ∀ j, z j ^ B j = 1) (hk : ∀ i, k i ∣ orderOf (z i))
    (hco : ∀ i, Nat.Coprime (k i) (∏ j ∈ univ.erase i, B j)) (i : ι) :
    k i ∣ orderOf (∏ j, z j) := by
  rw [← Finset.prod_erase_mul _ _ (mem_univ i)]
  apply dvd_orderOf_mul _ _ _ _ (hk i) _ (hco i)
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro j hj
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem B hj
  rw [hr, pow_mul, hB j, one_pow]

/-- 互いに素な k_i の積も割る。 -/
theorem prod_dvd_orderOf_prod (z : ι → ℂ) (B k : ι → ℕ) (hB : ∀ j, z j ^ B j = 1)
    (hk : ∀ i, k i ∣ orderOf (z i)) (hco : ∀ i, Nat.Coprime (k i) (∏ j ∈ univ.erase i, B j))
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (k i) (k j)) :
    ∏ i, k i ∣ orderOf (∏ j, z j) :=
  prod_dvd_of_coprime_nat univ k _ (fun i _ j _ hij => hpair i j hij)
    (fun i _ => dvd_orderOf_prod z B k hB hk hco i)

omit [DecidableEq ι] in
/-- **3a. ord(∏ z) ∣ lcm(ord z_i)**。 -/
theorem orderOf_prod_dvd_lcm (z : ι → ℂ) : orderOf (∏ j, z j) ∣ (univ : Finset ι).lcm (fun j => orderOf (z j)) := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro j _
  obtain ⟨r, hr⟩ := Finset.dvd_lcm (f := fun j => orderOf (z j)) (mem_univ j)
  rw [hr, pow_mul, pow_orderOf_eq_one, one_pow]

/-- **3b. 位数が対ごとに互いに素なら ord(∏ z) = ∏ ord z_i**。 -/
theorem orderOf_prod_coprime (z : ι → ℂ) (hpair : ∀ i j, i ≠ j → Nat.Coprime (orderOf (z i)) (orderOf (z j))) :
    orderOf (∏ j, z j) = ∏ j, orderOf (z j) := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro j _
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun j => orderOf (z j)) (mem_univ j)
    rw [hr, pow_mul, pow_orderOf_eq_one, one_pow]
  · apply prod_dvd_orderOf_prod z (fun j => orderOf (z j)) (fun j => orderOf (z j))
      (fun j => pow_orderOf_eq_one _) (fun i => dvd_rfl) _ hpair
    intro i
    exact Nat.coprime_prod_right_iff.mpr (fun j hj => hpair i j (Ne.symm (Finset.ne_of_mem_erase hj)))

/-! ## 4. ガウス和の位相の積 -/

open PAG.Part128 in
/-- **4. 各素数の p 部分が残る十分条件**。 -/
theorem gauss_prod_pdvd (p c : ι → ℕ) [hp : ∀ i, Fact (p i).Prime] (hp2 : ∀ i, p i ≠ 2) (hinj : Function.Injective p)
    (hc : ∀ i, 2 ≤ c i) (χ : ∀ i, DirichletCharacter ℂ (p i ^ c i)) (hχ : ∀ i, (χ i).IsPrimitive)
    (hcond : ∀ i, ¬ p i ∣ ∏ j ∈ univ.erase i, Nat.lcm (Nat.lcm (orderOf (χ j)) (p j ^ c j)) 4) :
    ∏ i, p i ^ c i ∣ orderOf (∏ j, gaussSum (χ j) stdAddChar / ((Real.sqrt ((p j : ℝ) ^ c j) : ℝ) : ℂ)) := by
  apply prod_dvd_orderOf_prod _ (fun j => Nat.lcm (Nat.lcm (orderOf (χ j)) (p j ^ c j)) 4)
  · intro j
    exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_gauss_bounds (hp2 j) (c j) (hc j) (χ j) (hχ j)).2
  · intro i
    exact (orderOf_gauss_bounds (hp2 i) (c i) (hc i) (χ i) (hχ i)).1
  · intro i
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (hp i).out).mpr (hcond i))
  · intro i j hij
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hp i).out (hp j).out).mpr (fun h => hij (hinj h)))

/-- **5. 鋭い形**: p^c ∣ ord B、A^M = 1（M ≠ 0）、p^c ∤ M ⇒ p^c ∣ ord(A B)。 -/
theorem pdvd_orderOf_mul (p : ℕ) [hp : Fact p.Prime] (c : ℕ) (A B : ℂ) (hB : p ^ c ∣ orderOf B)
    (M : ℕ) (hM0 : M ≠ 0) (hA : A ^ M = 1) (hMc : ¬ p ^ c ∣ M) : p ^ c ∣ orderOf (A * B) := by
  obtain ⟨a, M', hM', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM0 p hp.out.ne_one
  have ha : a < c := by
    by_contra h; exact hMc (dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) _)
  set d := orderOf (A * B)
  have hd : (A * B) ^ d = 1 := pow_orderOf_eq_one _
  rcases Nat.eq_zero_or_pos d with h0 | hd0
  · rw [h0]; exact dvd_zero _
  by_contra hnd
  obtain ⟨j, d', hnot, hdj⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0.ne' p hp.out.ne_one
  have hj : j < c := by
    by_contra h; exact hnd (hdj ▸ dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) _)
  have hsplit : p ^ (c - 1) = p ^ j * p ^ (c - 1 - j) := by rw [← pow_add]; congr 1; omega
  have hsplit' : p ^ (c - 1) = p ^ a * p ^ (c - 1 - a) := by rw [← pow_add]; congr 1; omega
  have hE : d * (M' * p ^ (c - 1 - j)) = p ^ (c - 1) * (d' * M') := by rw [hdj, hsplit]; ring
  have hE' : p ^ (c - 1) * (d' * M') = p ^ a * M' * (p ^ (c - 1 - a) * d') := by rw [hsplit']; ring
  have h1 : (A * B) ^ (d * (M' * p ^ (c - 1 - j))) = 1 := by rw [pow_mul, hd, one_pow]
  rw [mul_pow, hE, hE', pow_mul A, hA, one_pow, one_mul, ← hE'] at h1
  have h4 := hB.trans (orderOf_dvd_of_pow_eq_one h1)
  have hnd' : ¬ p ∣ d' * M' := by
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · exact hnot h
    · exact hM' h
  have hcop : Nat.Coprime (p ^ c) (d' * M') :=
    Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd')
  have h6 := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp (hcop.dvd_of_dvd_mul_right h4)
  omega

open PAG.Part128 in
/-- **6. ガウス和の位相の積、鋭い十分条件**: p_i^{c_i} ∤ ∏_{j≠i} ord z_j なら p_i^{c_i} ∣ ord w。 -/
theorem gauss_prod_pdvd_sharp (p c : ι → ℕ) [hp : ∀ i, Fact (p i).Prime] (hp2 : ∀ i, p i ≠ 2)
    (hc : ∀ i, 2 ≤ c i) (χ : ∀ i, DirichletCharacter ℂ (p i ^ c i)) (hχ : ∀ i, (χ i).IsPrimitive) (i : ι)
    (hcond : ¬ p i ^ c i ∣ ∏ j ∈ univ.erase i,
      orderOf (gaussSum (χ j) stdAddChar / ((Real.sqrt ((p j : ℝ) ^ c j) : ℝ) : ℂ))) :
    p i ^ c i ∣ orderOf (∏ j, gaussSum (χ j) stdAddChar / ((Real.sqrt ((p j : ℝ) ^ c j) : ℝ) : ℂ)) := by
  set z : ι → ℂ := fun j => gaussSum (χ j) stdAddChar / ((Real.sqrt ((p j : ℝ) ^ c j) : ℝ) : ℂ)
  have hpos : ∀ j, orderOf (z j) ≠ 0 := by
    intro j h0
    have hb := (orderOf_gauss_bounds (hp2 j) (c j) (hc j) (χ j) (hχ j)).2
    change orderOf (z j) ∣ _ at hb
    rw [h0] at hb
    have := Nat.eq_zero_of_zero_dvd hb
    exact Nat.lcm_ne_zero (Nat.lcm_ne_zero (orderOf_pos (χ j)).ne' (pow_ne_zero _ (hp j).out.ne_zero))
      (by norm_num) this
  change p i ^ c i ∣ orderOf (∏ j, z j)
  rw [← Finset.prod_erase_mul _ _ (mem_univ i)]
  apply pdvd_orderOf_mul (p i) (c i) _ _ (orderOf_gauss_bounds (hp2 i) (c i) (hc i) (χ i) (hχ i)).1
    (∏ j ∈ univ.erase i, orderOf (z j)) (Finset.prod_ne_zero_iff.mpr (fun j _ => hpos j)) _ hcond
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro j hj
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun j => orderOf (z j)) hj
  rw [hr, pow_mul, pow_orderOf_eq_one, one_pow]

end PAG.Part131

#print axioms PAG.Part131.prod_dvd_of_coprime_nat
#print axioms PAG.Part131.dvd_orderOf_mul
#print axioms PAG.Part131.dvd_orderOf_prod
#print axioms PAG.Part131.prod_dvd_orderOf_prod
#print axioms PAG.Part131.orderOf_prod_dvd_lcm
#print axioms PAG.Part131.orderOf_prod_coprime
#print axioms PAG.Part131.gauss_prod_pdvd
#print axioms PAG.Part131.pdvd_orderOf_mul
#print axioms PAG.Part131.gauss_prod_pdvd_sharp
