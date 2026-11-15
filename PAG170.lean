/-
  PAG 2.0 Part 166（2026-10-22）— 積のケットの ζ の位数（素数の重複と p = 2 を許す一般形）
  1. ord_prod_primes': ord_prod_primes の、添字集合の上だけで仮定する版
  2. ord_prod_mixed: ζ_i^{4p_i} = 1（p_i 奇）、ζ_i^4 = 1（p_i = 2）、X = ∏ ζ_i^{e_i}、
     S = {奇素数 p_i}、P = ∏_{q ∈ S} q、U_q = ∏_{p_i = q} (ζ_i^4)^{e_i}
     ⇒ ord X = (∏_{q ∈ S, U_q ≠ 1} q) · ord(X^P)
  3. two_zeta4: 導手 2^{c+1}（c ≥ 1）の単独のケットで ζ^4 = 1
  4. orderOf_zeta_prod_mixed: 積のケット（任意の素数、c_i ≥ 1）の ζ の位数
-/
import PAG169

namespace PAG.Part170

open Finset

/-- **1. ord ∏_{i ∈ s} u_i = ∏_{i ∈ s, u_i ≠ 1} q_i**（仮定は s の上だけ）。 -/
theorem ord_prod_primes' {ι : Type*} [DecidableEq ι] (q : ι → ℕ) (u : ι → ℂ) :
    ∀ s : Finset ι, (∀ i ∈ s, (q i).Prime) → (∀ i ∈ s, u i ^ q i = 1) → Set.InjOn q s →
      orderOf (∏ i ∈ s, u i) = ∏ i ∈ s.filter (fun i => u i ≠ 1), q i := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert i s hi ih =>
    intro hq hu hinj
    have hs : Set.InjOn q s := hinj.mono (by intro x hx; simp [hx])
    have hq' : ∀ j ∈ s, (q j).Prime := fun j hj => hq j (by simp [hj])
    have hu' : ∀ j ∈ s, u j ^ q j = 1 := fun j hj => hu j (by simp [hj])
    rw [Finset.prod_insert hi]
    have hord_i : orderOf (u i) = if u i ≠ 1 then q i else 1 := by
      have := Fact.mk (hq i (by simp))
      split_ifs with h
      · exact orderOf_eq_prime_iff.mpr ⟨hu i (by simp), h⟩
      · rw [ne_eq, not_not] at h; rw [h, orderOf_one]
    have hcop : Nat.Coprime (orderOf (u i)) (orderOf (∏ j ∈ s, u j)) := by
      rw [ih hq' hu' hs, hord_i]
      split_ifs
      · apply Nat.Coprime.prod_right
        intro j hj
        have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
        have hne : q i ≠ q j := by
          intro h
          have := hinj (by simp) (by simp [hjs]) h
          exact hi (this ▸ hjs)
        exact (Nat.coprime_primes (hq i (by simp)) (hq' j hjs)).mpr hne
      · exact Nat.coprime_one_left _
    rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hcop, ih hq' hu' hs, hord_i, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.prod_insert (by simp [hi])]
    · rw [one_mul]

/-- 奇素数の集合 S。 -/
def oddS {n : ℕ} (p : Fin n → ℕ) : Finset ℕ := (univ.filter (fun i => p i ≠ 2)).image p

/-- 素数 q の上の桁 U_q。 -/
noncomputable def Uq {n : ℕ} (p : Fin n → ℕ) (ζ : Fin n → ℂ) (e : Fin n → ℕ) (q : ℕ) : ℂ :=
  ∏ i ∈ univ.filter (fun i => p i = q), (ζ i ^ 4) ^ e i

/-- **2. 積の位数の一般形**。 -/
theorem ord_prod_mixed {n : ℕ} (p : Fin n → ℕ) (hpr : ∀ i, (p i).Prime) (ζ : Fin n → ℂ)
    (h4odd : ∀ i, p i ≠ 2 → ζ i ^ (4 * p i) = 1) (h4two : ∀ i, p i = 2 → ζ i ^ 4 = 1) (e : Fin n → ℕ) :
    orderOf (∏ i, ζ i ^ e i)
      = (∏ q ∈ (oddS p).filter (fun q => Uq p ζ e q ≠ 1), q)
        * orderOf ((∏ i, ζ i ^ e i) ^ (∏ q ∈ oddS p, q)) := by
  set S := oddS p
  set P := ∏ q ∈ S, q
  have hmemS : ∀ i, p i ≠ 2 → p i ∈ S := fun i h =>
    Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨mem_univ _, h⟩, rfl⟩
  have hSprop : ∀ q ∈ S, q.Prime ∧ q ≠ 2 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hpr i, (Finset.mem_filter.mp hi).2⟩
  have hPpos : 0 < P := Finset.prod_pos (fun q hq => (hSprop q hq).1.pos)
  have hcop : Nat.Coprime 4 P := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.prod_right
    intro q hq
    exact (Nat.coprime_primes Nat.prime_two (hSprop q hq).1).mpr (Ne.symm (hSprop q hq).2)
  have hX : (∏ i, ζ i ^ e i) ^ (4 * P) = 1 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro i _
    by_cases h2 : p i = 2
    · rw [← pow_mul, show e i * (4 * P) = 4 * (e i * P) by ring, pow_mul, h4two i h2, one_pow]
    · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun q => q) (hmemS i h2)
      have hr' : P = p i * r := hr
      rw [← pow_mul, show e i * (4 * P) = 4 * p i * (e i * r) by rw [hr']; ring, pow_mul, h4odd i h2, one_pow]
  rw [PAG.Part169.ord_split _ 4 P (by norm_num) hPpos hcop hX]
  congr 1
  -- X^4 = ∏_{q ∈ S} U_q
  have hX4 : (∏ i, ζ i ^ e i) ^ 4 = ∏ q ∈ S, Uq p ζ e q := by
    rw [← Finset.prod_pow]
    have e1 : ∀ i, (ζ i ^ e i) ^ 4 = (ζ i ^ 4) ^ e i := fun i => by rw [← pow_mul, ← pow_mul, mul_comm]
    simp_rw [e1]
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun i => p i ≠ 2)]
    have htwo : ∏ i ∈ univ.filter (fun i => ¬ p i ≠ 2), (ζ i ^ 4) ^ e i = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      rw [Finset.mem_filter, ne_eq, not_not] at hi
      rw [h4two i hi.2, one_pow]
    rw [htwo, mul_one]
    rw [← Finset.prod_fiberwise_of_maps_to (g := p) (t := S) (fun i hi => hmemS i (Finset.mem_filter.mp hi).2)]
    apply Finset.prod_congr rfl
    intro q hq
    unfold Uq
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by rw [h]; exact (hSprop q hq).2, h⟩
  rw [hX4]
  have hU : ∀ q ∈ S, Uq p ζ e q ^ q = 1 := by
    intro q hq
    unfold Uq
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro i hi
    have hpi : p i = q := (Finset.mem_filter.mp hi).2
    rw [← pow_mul, ← pow_mul, ← hpi, show 4 * (e i * p i) = 4 * p i * e i by ring, pow_mul,
      h4odd i (by rw [hpi]; exact (hSprop q hq).2), one_pow]
  exact ord_prod_primes' (fun q => q) (Uq p ζ e) S (fun q hq => (hSprop q hq).1) hU (fun a _ b _ h => h)

open ZMod PAG.Part125 PAG.Part126 PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part120

/-- **3. 導手 2^{c+1}（c ≥ 1）の単独のケットで ζ^4 = 1**。 -/
theorem two_zeta4 (c : ℕ) (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (2 ^ (c + 1))) (hχ : χ.IsPrimitive) :
    ((gaussSum χ stdAddChar / ((Real.sqrt ((2 : ℝ) ^ (c + 1)) : ℝ) : ℂ)) ^ orderOf χ) ^ 4 = 1 := by
  set z := gaussSum χ stdAddChar / ((Real.sqrt ((2 : ℝ) ^ (c + 1)) : ℝ) : ℂ)
  by_cases hc3 : 3 ≤ c
  · have hordz : orderOf z = 2 ^ (c + 1) := by
      rcases Nat.even_or_odd (c + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact PAG.Part130.orderOf_gauss_two_even (c + 1) m (by omega) (by omega) χ hχ
      · exact PAG.Part130.orderOf_gauss_two_odd (c + 1) m (by omega) (by omega) χ hχ
    have hordχ := PAG.Part135.orderOf_chi_two c (by omega) χ hχ
    have hz := pow_orderOf_eq_one z
    rw [hordz] at hz
    rw [← pow_mul, hordχ, show 2 ^ (c - 1) * 4 = 2 ^ (c + 1) by
      rw [show c + 1 = (c - 1) + 2 by omega, pow_add]; norm_num, hz]
  · have : NeZero (2 ^ (c + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
    have h2 : χ ^ 2 = 1 := by
      have hd : orderOf χ ∣ 2 := by
        rcases (show c = 1 ∨ c = 2 by omega) with rfl | rfl
        · have := PAG.Part134.orderOf_dvd_totient χ
          rwa [show Nat.totient (2 ^ (1 + 1)) = 2 by decide] at this
        · have := PAG.Part135.orderOf_chi_two_dvd 2 le_rfl χ
          simpa using this
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have hsq := PAG.Part151.real_phase_sq χ hχ h2
    have hcast : ((2 ^ (c + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (c + 1) := by push_cast; ring
    rw [hcast] at hsq
    have hz4 : z ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, ← map_pow, neg_one_sq, map_one]
    rw [← pow_mul, mul_comm, pow_mul, hz4, one_pow]

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)

/-- **4. 積のケット（任意の素数、各 c_i ≥ 1）の ζ の位数**。 -/
theorem orderOf_zeta_prod_mixed (hc : ∀ i, 1 ≤ c i) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := p i) (K i) (K i - (c i + 1) - w i)) :
    let ζi := fun i => (gaussSum (χ i) stdAddChar / ((Real.sqrt ((p i : ℝ) ^ (c i + 1)) : ℝ) : ℂ)) ^ orderOf (χ i)
    let e := fun i => lcmF n (fun i => orderOf (χ i)) / orderOf (χ i)
    orderOf ((∏ i, cnorm (p i) (K i) (K i - (c i + 1) - w i) * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i))
        ^ lcmF n (fun i => orderOf (χ i)))
      = (∏ q ∈ (oddS p).filter (fun q => Uq p ζi e q ≠ 1), q)
        * orderOf ((∏ i, ζi i ^ e i) ^ (∏ q ∈ oddS p, q)) := by
  intro ζi e
  rw [PAG.Part169.zeta_prod_split p K w c h χ hχ t ht]
  apply ord_prod_mixed p (fun i => (hp i).out) ζi
  · intro i hi
    exact (PAG.Part169.single_facts hi (c i) (hc i) (χ i) (hχ i)).1
  · intro i hi
    have key : ∀ (q : ℕ) [Fact q.Prime] (hq : q = 2) (χ' : DirichletCharacter ℂ (q ^ (c i + 1))),
        χ'.IsPrimitive →
        ((gaussSum χ' stdAddChar / ((Real.sqrt ((q : ℝ) ^ (c i + 1)) : ℝ) : ℂ)) ^ orderOf χ') ^ 4 = 1 := by
      intro q _ hq χ' hχ'
      subst hq
      exact_mod_cast two_zeta4 (c i) (hc i) χ' hχ'
    exact key (p i) hi (χ i) (hχ i)

end PAG.Part170

#print axioms PAG.Part170.ord_prod_primes'
#print axioms PAG.Part170.ord_prod_mixed
#print axioms PAG.Part170.two_zeta4
#print axioms PAG.Part170.orderOf_zeta_prod_mixed
