/-
  PAG 2.0 Part 169（2026-10-22）— 導手 p の因子を含む積のケット
  1. not_root_prod: 1 の冪根でない因子がちょうど 1 つ（指数 > 0）、他は 1 の冪根 ⇒ 積も 1 の冪根でない
  2. gauss_inv_pair: 原始指標 χ（法 N）で z(χ) · z(χ⁻¹) = χ(−1)（無限位数の因子どうしは打ち消しうる）
  3. pair_zeta_sq: (z(χ) z(χ⁻¹))^{ord χ} の 2 乗は 1
  4. zeta_prod_infinite: 積のケットで、導手 p の 3 次または 4 次の因子が 1 つ、残りが導手 p_i^{c_i+1}（c_i ≥ 1）なら ζ は無限位数
-/
import PAG172

namespace PAG.Part173

open Finset Complex
open ZMod (stdAddChar)

/-- **1. 1 の冪根でない因子がちょうど 1 つなら、積も 1 の冪根でない**。 -/
theorem not_root_prod {n : ℕ} (ζ : Fin n → ℂ) (e : Fin n → ℕ) (i₀ : Fin n) (he : 0 < e i₀)
    (hbad : ∀ N : ℕ, 0 < N → ζ i₀ ^ N ≠ 1) (hgood : ∀ i, i ≠ i₀ → ∃ M : ℕ, 0 < M ∧ ζ i ^ M = 1) :
    ∀ N : ℕ, 0 < N → (∏ i, ζ i ^ e i) ^ N ≠ 1 := by
  classical
  choose M hM using hgood
  set Mt := ∏ i ∈ univ.erase i₀, (if h : i = i₀ then 1 else M i h)
  have hMt : 0 < Mt := Finset.prod_pos (fun i hi => by
    have hne := Finset.ne_of_mem_erase hi
    simp only [hne, ↓reduceDIte]; exact (hM i hne).1)
  intro N hN hX
  apply hbad (e i₀ * N * Mt) (Nat.mul_pos (Nat.mul_pos he hN) hMt)
  have hX' : ((∏ i, ζ i ^ e i) ^ N) ^ Mt = 1 := by rw [hX, one_pow]
  rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.mul_prod_erase univ _ (mem_univ i₀)] at hX'
  have hrest : ∏ i ∈ univ.erase i₀, ((ζ i ^ e i) ^ N) ^ Mt = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hne := Finset.ne_of_mem_erase hi
    obtain ⟨k, hk⟩ : M i hne ∣ Mt := by
      have := Finset.dvd_prod_of_mem (fun j => if h : j = i₀ then 1 else M j h) hi
      simpa [hne] using this
    rw [hk, ← pow_mul, ← pow_mul, show e i * (N * (M i hne * k)) = M i hne * (e i * N * k) by ring, pow_mul,
      (hM i hne).2, one_pow]
  rw [hrest, mul_one, ← pow_mul, ← pow_mul, ← mul_assoc] at hX'
  exact hX'

/-- **2. z(χ) · z(χ⁻¹) = χ(−1)**（χ は法 N の原始指標）。 -/
theorem gauss_inv_pair {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (gaussSum χ stdAddChar / ((Real.sqrt N : ℝ) : ℂ)) * (gaussSum χ⁻¹ stdAddChar / ((Real.sqrt N : ℝ) : ℂ))
      = χ (-1) := by
  have h := PAG.Part16.gauss_mul_gauss_inv_eq hχ
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hs : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = N := by
    rw [← ofReal_mul, Real.mul_self_sqrt hN.le]; push_cast; rfl
  have hs0 : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN
    exact_mod_cast this.ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [div_mul_div_comm, h, hs, mul_div_assoc, div_self hN0, mul_one]

/-- **3. (z(χ) z(χ⁻¹))^{ord χ} の 2 乗は 1**。 -/
theorem pair_zeta_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (((gaussSum χ stdAddChar / ((Real.sqrt N : ℝ) : ℂ)) * (gaussSum χ⁻¹ stdAddChar / ((Real.sqrt N : ℝ) : ℂ)))
      ^ orderOf χ) ^ 2 = 1 := by
  rw [gauss_inv_pair χ hχ, ← pow_mul, mul_comm, pow_mul, ← map_pow, neg_one_sq, map_one, one_pow]

open ZMod PAG.Part125 PAG.Part126 PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part120

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)

/-- 単独の ζ が 1 の冪根（c ≥ 1 のとき）。 -/
theorem single_root (i : Fin n) (hc : 1 ≤ c i) (χ : DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : χ.IsPrimitive) :
    ∃ M : ℕ, 0 < M ∧ ((gaussSum χ stdAddChar / ((Real.sqrt ((p i : ℝ) ^ (c i + 1)) : ℝ) : ℂ)) ^ orderOf χ) ^ M = 1 := by
  by_cases h2 : p i = 2
  · refine ⟨4, by norm_num, ?_⟩
    have key : ∀ (q : ℕ) [Fact q.Prime] (hq : q = 2) (χ' : DirichletCharacter ℂ (q ^ (c i + 1))),
        χ'.IsPrimitive →
        ((gaussSum χ' stdAddChar / ((Real.sqrt ((q : ℝ) ^ (c i + 1)) : ℝ) : ℂ)) ^ orderOf χ') ^ 4 = 1 := by
      intro q _ hq χ' hχ'
      subst hq
      exact_mod_cast PAG.Part170.two_zeta4 (c i) hc χ' hχ'
    exact key (p i) h2 χ hχ
  · exact ⟨4 * p i, by have := (hp i).out.pos; omega, (PAG.Part169.single_facts h2 (c i) hc χ hχ).1⟩

/-- **4. 積のケット：1 の冪根でない因子が 1 つ（i₀）、残りが c_i ≥ 1 なら ζ は無限位数**。 -/
theorem zeta_prod_infinite (i₀ : Fin n) (hc : ∀ i, i ≠ i₀ → 1 ≤ c i) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := p i) (K i) (K i - (c i + 1) - w i))
    (hbad : ∀ N : ℕ, 0 < N →
      ((gaussSum (χ i₀) stdAddChar / ((Real.sqrt ((p i₀ : ℝ) ^ (c i₀ + 1)) : ℝ) : ℂ)) ^ orderOf (χ i₀)) ^ N ≠ 1) :
    orderOf ((∏ i, cnorm (p i) (K i) (K i - (c i + 1) - w i) * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i))
        ^ lcmF n (fun i => orderOf (χ i))) = 0 := by
  rw [PAG.Part169.zeta_prod_split p K w c h χ hχ t ht, orderOf_eq_zero_iff']
  apply not_root_prod _ _ i₀
  · apply Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (PAG.Part132.lcmF_ne_zero n _
      (fun i => (orderOf_pos (χ i)).ne'))) (dvd_lcmF n (fun i => orderOf (χ i)) i₀)) (orderOf_pos _)
  · exact hbad
  · intro i hi; exact single_root p c i (hc i hi) (χ i) (hχ i)

/-- **4'. 導手 p の 3 次の因子なら hbad が成り立つ**。 -/
theorem bad_cubic (i₀ : Fin n) (hc0 : c i₀ = 0) (h3p : p i₀ % 3 = 1)
    (χ : DirichletCharacter ℂ (p i₀ ^ (c i₀ + 1))) (h3 : orderOf χ = 3) :
    ∀ N : ℕ, 0 < N →
      ((gaussSum χ stdAddChar / ((Real.sqrt ((p i₀ : ℝ) ^ (c i₀ + 1)) : ℝ) : ℂ)) ^ orderOf χ) ^ N ≠ 1 := by
  have key : ∀ (k : ℕ) (hk : k = 0) (χ' : DirichletCharacter ℂ (p i₀ ^ (k + 1))), orderOf χ' = 3 →
      ∀ N : ℕ, 0 < N →
        ((gaussSum χ' stdAddChar / ((Real.sqrt ((p i₀ : ℝ) ^ (k + 1)) : ℝ) : ℂ)) ^ orderOf χ') ^ N ≠ 1 := by
    intro k hk χ' h3' N hN
    subst hk
    have : Fact (p i₀ ^ (0 + 1)).Prime := ⟨by rw [zero_add, pow_one]; exact (hp i₀).out⟩
    have h3q : p i₀ ^ (0 + 1) % 3 = 1 := by rw [zero_add, pow_one]; exact h3p
    have hc : ((p i₀ ^ (0 + 1) : ℕ) : ℝ) = (p i₀ : ℝ) ^ (0 + 1) := by push_cast; ring
    have := PAG.Part171.zeta_cubic_infinite h3q χ' h3'
    rw [hc] at this
    rw [orderOf_eq_zero_iff'] at this
    exact this N hN
  exact key (c i₀) hc0 χ h3

/-- **4''. 導手 p の 4 次の因子なら hbad が成り立つ**。 -/
theorem bad_quartic (i₀ : Fin n) (hc0 : c i₀ = 0)
    (χ : DirichletCharacter ℂ (p i₀ ^ (c i₀ + 1))) (h4 : orderOf χ = 4) :
    ∀ N : ℕ, 0 < N →
      ((gaussSum χ stdAddChar / ((Real.sqrt ((p i₀ : ℝ) ^ (c i₀ + 1)) : ℝ) : ℂ)) ^ orderOf χ) ^ N ≠ 1 := by
  have key : ∀ (k : ℕ) (hk : k = 0) (χ' : DirichletCharacter ℂ (p i₀ ^ (k + 1))), orderOf χ' = 4 →
      ∀ N : ℕ, 0 < N →
        ((gaussSum χ' stdAddChar / ((Real.sqrt ((p i₀ : ℝ) ^ (k + 1)) : ℝ) : ℂ)) ^ orderOf χ') ^ N ≠ 1 := by
    intro k hk χ' h4' N hN
    subst hk
    have : Fact (p i₀ ^ (0 + 1)).Prime := ⟨by rw [zero_add, pow_one]; exact (hp i₀).out⟩
    have hc : ((p i₀ ^ (0 + 1) : ℕ) : ℝ) = (p i₀ : ℝ) ^ (0 + 1) := by push_cast; ring
    have := PAG.Part172.zeta_quartic_infinite χ' h4'
    rw [hc] at this
    rw [orderOf_eq_zero_iff'] at this
    exact this N hN
  exact key (c i₀) hc0 χ h4

end PAG.Part173

#print axioms PAG.Part173.not_root_prod
#print axioms PAG.Part173.gauss_inv_pair
#print axioms PAG.Part173.pair_zeta_sq
#print axioms PAG.Part173.single_root
#print axioms PAG.Part173.zeta_prod_infinite
#print axioms PAG.Part173.bad_cubic
#print axioms PAG.Part173.bad_quartic
