/-
  PAG 2.0 Part 165（2026-10-22）— 積のケットの ζ の位数（相異なる奇素数）
  1. ord_split: x^{ab} = 1、a ⊥ b ⇒ ord x = ord(x^a) · ord(x^b)
  2. ord_prod_primes: u_i^{q_i} = 1、q_i 相異なる素数 ⇒ ord ∏ u_i = ∏_{u_i ≠ 1} q_i
  3. ord_prod_general: ζ_i^{4p_i} = 1、p_i ∣ ord ζ_i（p_i 相異なる奇素数）、X = ∏ ζ_i^{e_i}、P = ∏ p_i
     ⇒ ord X = (∏_{p_i ∤ e_i} p_i) · ord(∏ (ζ_i^{p_i})^{e_i · P/p_i})
  4. single_facts: 導手 p^{c+1}（c ≥ 1、p 奇素数）の単独のケットで ζ^{4p} = 1、p ∣ ord ζ
  5. zeta_prod_split: 積のケットの ζ = ∏ ζ_i^{L/o_i}
  6. orderOf_zeta_prod_formula: 積のケットの ζ の位数の公式
-/
import PAG168

namespace PAG.Part169

open Finset

/-- **1. ord x = ord(x^a) · ord(x^b)**。 -/
theorem ord_split (x : ℂ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) (hx : x ^ (a * b) = 1) :
    orderOf x = orderOf (x ^ a) * orderOf (x ^ b) := by
  have hd : orderOf x ∣ a * b := orderOf_dvd_of_pow_eq_one hx
  have hg : Nat.gcd (orderOf x) a * Nat.gcd (orderOf x) b = orderOf x := by
    rw [← Nat.Coprime.gcd_mul _ hab, Nat.gcd_eq_left hd]
  have e1 : orderOf x / Nat.gcd (orderOf x) a = Nat.gcd (orderOf x) b :=
    Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_right _ ha) (by rw [mul_comm]; exact hg.symm)
  have e2 : orderOf x / Nat.gcd (orderOf x) b = Nat.gcd (orderOf x) a :=
    Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_right _ hb) hg.symm
  rw [orderOf_pow' _ ha.ne', orderOf_pow' _ hb.ne', e1, e2, mul_comm, hg]

/-- **2. ord ∏ u_i = ∏_{u_i ≠ 1} q_i**。 -/
theorem ord_prod_primes {ι : Type*} [DecidableEq ι] (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (u : ι → ℂ)
    (hu : ∀ i, u i ^ q i = 1) :
    ∀ s : Finset ι, Set.InjOn q s → orderOf (∏ i ∈ s, u i) = ∏ i ∈ s.filter (fun i => u i ≠ 1), q i := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert i s hi ih =>
    intro hinj
    have hs : Set.InjOn q s := hinj.mono (by intro x hx; simp [hx])
    rw [Finset.prod_insert hi]
    have hord_i : orderOf (u i) = if u i ≠ 1 then q i else 1 := by
      have := Fact.mk (hq i)
      split_ifs with h
      · exact orderOf_eq_prime_iff.mpr ⟨hu i, h⟩
      · rw [ne_eq, not_not] at h; rw [h, orderOf_one]
    have hcop : Nat.Coprime (orderOf (u i)) (orderOf (∏ j ∈ s, u j)) := by
      rw [ih hs, hord_i]
      split_ifs
      · apply Nat.Coprime.prod_right
        intro j hj
        have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
        have hne : q i ≠ q j := by
          intro h
          have := hinj (by simp) (by simp [hjs]) h
          exact hi (this ▸ hjs)
        exact (Nat.coprime_primes (hq i) (hq j)).mpr hne
      · exact Nat.coprime_one_left _
    rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hcop, ih hs, hord_i, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.prod_insert (by simp [hi])]
    · rw [one_mul]

/-- **3. 積の位数の一般公式**。 -/
theorem ord_prod_general {n : ℕ} (p : Fin n → ℕ) (hpr : ∀ i, (p i).Prime) (hp2 : ∀ i, p i ≠ 2)
    (hinj : Function.Injective p) (ζ : Fin n → ℂ) (h4 : ∀ i, ζ i ^ (4 * p i) = 1)
    (hpd : ∀ i, p i ∣ orderOf (ζ i)) (e : Fin n → ℕ) :
    orderOf (∏ i, ζ i ^ e i)
      = (∏ i ∈ univ.filter (fun i => ¬ p i ∣ e i), p i)
        * orderOf (∏ i, (ζ i ^ p i) ^ (e i * ((∏ j, p j) / p i))) := by
  set P := ∏ j, p j
  have hPi : ∀ i, P = p i * (P / p i) := fun i =>
    (Nat.mul_div_cancel' (Finset.dvd_prod_of_mem p (mem_univ i))).symm
  have hPpos : 0 < P := Finset.prod_pos (fun i _ => (hpr i).pos)
  have hPodd : Nat.Coprime 4 P := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.prod_right
    intro i _
    exact (Nat.coprime_primes Nat.prime_two (hpr i)).mpr (Ne.symm (hp2 i))
  have hX : (∏ i, ζ i ^ e i) ^ (4 * P) = 1 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro i _
    rw [← pow_mul, hPi i, show e i * (4 * (p i * (P / p i))) = 4 * p i * (e i * (P / p i)) by ring, pow_mul, h4 i,
      one_pow]
  rw [ord_split _ 4 P (by norm_num) hPpos hPodd hX]
  congr 1
  · -- X^4
    rw [← Finset.prod_pow]
    have hu : ∀ i, ((ζ i ^ e i) ^ 4) ^ p i = 1 := by
      intro i; rw [← pow_mul, ← pow_mul, show e i * (4 * p i) = 4 * p i * e i by ring, pow_mul, h4 i, one_pow]
    rw [ord_prod_primes p hpr (fun i => (ζ i ^ e i) ^ 4) hu univ (hinj.injOn)]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- (ζ^e)^4 ≠ 1 ⇔ p ∤ e
    have hord4 : orderOf (ζ i ^ 4) = p i := by
      rw [orderOf_pow' _ (by norm_num)]
      obtain ⟨t, ht⟩ := hpd i
      have hd : orderOf (ζ i) ∣ 4 * p i := orderOf_dvd_of_pow_eq_one (h4 i)
      rw [ht] at hd ⊢
      have ht4 : t ∣ 4 := by
        obtain ⟨r, hr⟩ := hd
        refine ⟨r, ?_⟩
        have h' : p i * 4 = p i * (t * r) := by rw [mul_comm (p i) 4, hr]; ring
        exact Nat.eq_of_mul_eq_mul_left (hpr i).pos h'
      have hcop : Nat.Coprime (p i) 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_right _ ((Nat.coprime_primes (hpr i) Nat.prime_two).mpr (hp2 i))
      rw [Nat.Coprime.gcd_mul_left_cancel t hcop, Nat.gcd_eq_left ht4, Nat.mul_div_cancel _
        (Nat.pos_of_dvd_of_pos ht4 (by norm_num))]
    rw [← pow_mul, mul_comm (e i) 4, pow_mul, Ne, ← orderOf_dvd_iff_pow_eq_one, hord4]
  · -- X^P
    rw [← Finset.prod_pow]
    apply congrArg
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, ← pow_mul, hPi i]
    congr 1
    rw [← hPi i]; nth_rewrite 1 [hPi i]; ring

open ZMod PAG.Part125 PAG.Part126 PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part120

/-- **4. 単独のケット（導手 p^{c+1}、c ≥ 1）：ζ^{4p} = 1、p ∣ ord ζ**。 -/
theorem single_facts {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ) (hc : 1 ≤ c)
    (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive) :
    ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (c + 1)) : ℝ) : ℂ)) ^ orderOf χ) ^ (4 * p) = 1 ∧
      p ∣ orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (c + 1)) : ℝ) : ℂ)) ^ orderOf χ) := by
  rcases Nat.even_or_odd (c + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have h := PAG.Part157.zeta_order_even hp2 c m (by omega) (by omega) χ hχ
    refine ⟨?_, by rw [h]⟩
    have hz := pow_orderOf_eq_one ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (c + 1)) : ℝ) : ℂ)) ^ orderOf χ)
    rw [h] at hz
    rw [mul_comm, pow_mul, hz, one_pow]
  · obtain ⟨h1, h2, -⟩ := PAG.Part157.zeta_order_odd hp2 c m (by omega) (by omega) χ hχ
    exact ⟨h1, h2⟩

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)

/-- **5. 積のケットの ζ = ∏ ζ_i^{L/o_i}**。 -/
theorem zeta_prod_split (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := p i) (K i) (K i - (c i + 1) - w i)) :
    (∏ i, cnorm (p i) (K i) (K i - (c i + 1) - w i) * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i))
        ^ lcmF n (fun i => orderOf (χ i))
      = ∏ i, ((gaussSum (χ i) stdAddChar / ((Real.sqrt ((p i : ℝ) ^ (c i + 1)) : ℝ) : ℂ)) ^ orderOf (χ i))
          ^ (lcmF n (fun i => orderOf (χ i)) / orderOf (χ i)) := by
  rw [PAG.Part132.zeta_prod_eq_pow p K w c h χ hχ t ht, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, Nat.mul_div_cancel' (dvd_lcmF n (fun i => orderOf (χ i)) i)]

/-- **6. 積のケットの ζ の位数（相異なる奇素数、各 c_i ≥ 1）**。 -/
theorem orderOf_zeta_prod_formula (hp2 : ∀ i, p i ≠ 2) (hinj : Function.Injective p) (hc : ∀ i, 1 ≤ c i)
    (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := p i) (K i) (K i - (c i + 1) - w i)) :
    orderOf ((∏ i, cnorm (p i) (K i) (K i - (c i + 1) - w i) * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i))
        ^ lcmF n (fun i => orderOf (χ i)))
      = (∏ i ∈ univ.filter (fun i => ¬ p i ∣ lcmF n (fun i => orderOf (χ i)) / orderOf (χ i)), p i)
        * orderOf (∏ i, (((gaussSum (χ i) stdAddChar / ((Real.sqrt ((p i : ℝ) ^ (c i + 1)) : ℝ) : ℂ))
            ^ orderOf (χ i)) ^ p i)
            ^ ((lcmF n (fun i => orderOf (χ i)) / orderOf (χ i)) * ((∏ j, p j) / p i))) := by
  rw [zeta_prod_split p K w c h χ hχ t ht]
  exact ord_prod_general p (fun i => (hp i).out) hp2 hinj _
    (fun i => (single_facts (hp2 i) (c i) (hc i) (χ i) (hχ i)).1)
    (fun i => (single_facts (hp2 i) (c i) (hc i) (χ i) (hχ i)).2) _

end PAG.Part169

#print axioms PAG.Part169.ord_split
#print axioms PAG.Part169.ord_prod_primes
#print axioms PAG.Part169.ord_prod_general
#print axioms PAG.Part169.single_facts
#print axioms PAG.Part169.zeta_prod_split
#print axioms PAG.Part169.orderOf_zeta_prod_formula
