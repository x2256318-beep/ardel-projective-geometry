/-
  PAG 2.0 Part 180（2026-10-22）— 指標を重複を許して並べた積の判定（多重集合 → 指数の形式化）
  各素数 p_j に基準の 3 次の指標 ψ_j、各素数 q_j に基準の 4 次の指標 φ_j を固定する。
  1. cubic_cases: 法 p の 3 次の指標は ψ か ψ⁻¹（quartic_cases も同様）。6 次の指標は ψL か ψ⁻¹L（exists_type6）
  2. 各因子は 1 の冪根 × z(基準)^{重み}（ψ: 1、ψ⁻¹: −1、ψL: −2、ψ⁻¹L: 2、φ: 1、φ⁻¹: −1）
  3. list_root_iff: 因子を任意個（重複可）並べた積が 1 の冪根 ⇔ 各素数で重みの和が 0
-/
import PAG183

namespace PAG.Part184

open Complex Finset PAG.Part119 PAG.Part160 PAG.Part171 PAG.Part173 PAG.Part180 PAG.Part181 PAG.Part182 PAG.Part183
open ZMod (stdAddChar)

theorem prod_zpow_same {ι : Type*} (s : Finset ι) (x : ℂ) (hx : x ≠ 0) (w : ι → ℤ) :
    ∏ i ∈ s, x ^ w i = x ^ (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hx]

variable {p : ℕ} [hp : Fact p.Prime]

noncomputable def zOf (χ : DirichletCharacter ℂ p) : ℂ := gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)

theorem zOf_ne_zero (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) : zOf χ ≠ 0 := by
  apply div_ne_zero (PAG.Part16.gaussSum_ne_zero (primitive_of_ne_one _ hχ))
  have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)
  exact_mod_cast this.ne'

/-- 3 次の族の 4 種類の指標。 -/
noncomputable def chiOf (ψ : DirichletCharacter ℂ p) : Fin 4 → DirichletCharacter ℂ p :=
  ![ψ, ψ⁻¹, ψ * Lc p, ψ⁻¹ * Lc p]

def wt : Fin 4 → ℤ := ![1, -1, -2, 2]

/-- 4 次の族の 2 種類の指標。 -/
noncomputable def chiOf4 (φ : DirichletCharacter ℂ p) : Fin 2 → DirichletCharacter ℂ p := ![φ, φ⁻¹]

def wt4 : Fin 2 → ℤ := ![1, -1]

omit hp in
theorem inv_order3 (ψ : DirichletCharacter ℂ p) (h3 : orderOf ψ = 3) : orderOf ψ⁻¹ = 3 := by
  rw [orderOf_inv]; exact h3

/-- **2a. 3 次の族の各因子 = (1 の冪根) × z(ψ)^{重み}**。 -/
theorem val_cubic (h3p : p % 3 = 1) (ψ : DirichletCharacter ℂ p) (h3 : orderOf ψ = 3) (t : Fin 4) :
    ∃ r : ℂ, r ^ 12 = 1 ∧ zOf (chiOf ψ t) = r * zOf ψ ^ wt t := by
  have hne : ψ ≠ 1 := by intro h; rw [h, orderOf_one] at h3; norm_num at h3
  have hz0 := zOf_ne_zero ψ hne
  have hpair := gauss_inv_pair (N := p) ψ (primitive_of_ne_one ψ hne)
  rw [chi_neg_one ψ h3] at hpair
  have hinv : zOf ψ⁻¹ = (zOf ψ)⁻¹ := by
    unfold zOf at hz0 ⊢; exact eq_inv_of_mul_eq_one_right hpair
  fin_cases t
  · exact ⟨1, one_pow _, by simp [chiOf, wt]⟩
  · exact ⟨1, one_pow _, by simp [chiOf, wt, hinv]⟩
  · refine ⟨(ψ 4)⁻¹ * epsG p, c12 h3p ψ h3, ?_⟩
    show zOf (ψ * Lc p) = _ * zOf ψ ^ (-2 : ℤ)
    simp only [zOf]
    have := sextic_zpow h3p ψ h3 1
    simp only [zpow_one] at this
    rw [this]; norm_num
  · refine ⟨(ψ⁻¹ 4)⁻¹ * epsG p, c12 h3p ψ⁻¹ (inv_order3 ψ h3), ?_⟩
    show zOf (ψ⁻¹ * Lc p) = _ * zOf ψ ^ (2 : ℤ)
    simp only [zOf]
    have := sextic_zpow h3p ψ⁻¹ (inv_order3 ψ h3) 1
    simp only [zpow_one] at this
    rw [this]
    have hinv' : gaussSum ψ⁻¹ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)
        = (gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ))⁻¹ := hinv
    rw [hinv', inv_zpow', show -(-2 * (1 : ℤ)) = 2 by norm_num]

/-- **2b. 4 次の族の各因子 = (1 の冪根) × z(φ)^{重み}**。 -/
theorem val_quartic (φ : DirichletCharacter ℂ p) (h4 : orderOf φ = 4) (t : Fin 2) :
    ∃ r : ℂ, r ^ 12 = 1 ∧ zOf (chiOf4 φ t) = r * zOf φ ^ wt4 t := by
  have hne : φ ≠ 1 := by intro h; rw [h, orderOf_one] at h4; norm_num at h4
  have hz0 := zOf_ne_zero φ hne
  have hpair := gauss_inv_pair (N := p) φ (primitive_of_ne_one φ hne)
  have hs2 : (φ (-1)) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  fin_cases t
  · exact ⟨1, one_pow _, by simp [chiOf4, wt4]⟩
  · refine ⟨φ (-1), by rw [show (12 : ℕ) = 2 * 6 by rfl, pow_mul, hs2, one_pow], ?_⟩
    show zOf φ⁻¹ = _ * zOf φ ^ (-1 : ℤ)
    unfold zOf at hz0 ⊢
    have hg : gaussSum φ stdAddChar ≠ 0 := (div_ne_zero_iff.mp hz0).1
    rw [zpow_neg_one, ← hpair]
    field_simp

/-- **1. 法 p の位数 3 の指標は ψ か ψ⁻¹**。 -/
theorem cubic_cases (ψ φ : DirichletCharacter ℂ p) (h3 : orderOf ψ = 3) (h3' : orderOf φ = 3) :
    φ = ψ ∨ φ = ψ⁻¹ := by
  classical
  have hcyc : IsCyclic (DirichletCharacter ℂ p) := by
    have : IsCyclic (ZMod p)ˣ := inferInstance
    exact isCyclic_of_surjective (MulChar.equiv_rootsOfUnity (ZMod p) ℂ).symm
      (MulChar.equiv_rootsOfUnity (ZMod p) ℂ).symm.surjective
  by_contra hc
  push Not at hc
  have hψ3 : ψ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one ψ
  have hφ3 : φ ^ 3 = 1 := by rw [← h3']; exact pow_orderOf_eq_one φ
  have hne1 : ψ ≠ 1 := by intro h; rw [h, orderOf_one] at h3; norm_num at h3
  have hne2 : ψ⁻¹ ≠ 1 := inv_ne_one.mpr hne1
  have hne3 : ψ ≠ ψ⁻¹ := by
    intro h
    have : ψ ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel ψ
    have := orderOf_dvd_of_pow_eq_one this; rw [h3] at this; norm_num at this
  have hφ1 : φ ≠ 1 := by intro h; rw [h, orderOf_one] at h3'; norm_num at h3'
  have hsub : ({1, ψ, ψ⁻¹, φ} : Finset (DirichletCharacter ℂ p)) ⊆ univ.filter (fun x => x ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact hψ3
    · rw [inv_pow, hψ3, inv_one]
    · exact hφ3
  have h4 : ({1, ψ, ψ⁻¹, φ} : Finset (DirichletCharacter ℂ p)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact fun h => hc.2 h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
      exact ⟨hne3, fun h => hc.1 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
      exact ⟨hne1.symm, hne2.symm, hφ1.symm⟩
  have := Finset.card_le_card hsub
  have hle := IsCyclic.card_pow_eq_one_le (α := DirichletCharacter ℂ p) (n := 3) (by norm_num)
  omega

/-- **1b. 法 p の位数 4 の指標は φ か φ⁻¹**。 -/
theorem quartic_cases (φ χ : DirichletCharacter ℂ p) (h4 : orderOf φ = 4) (h4' : orderOf χ = 4) :
    χ = φ ∨ χ = φ⁻¹ := by
  classical
  have hcyc : IsCyclic (DirichletCharacter ℂ p) := by
    have : IsCyclic (ZMod p)ˣ := inferInstance
    exact isCyclic_of_surjective (MulChar.equiv_rootsOfUnity (ZMod p) ℂ).symm
      (MulChar.equiv_rootsOfUnity (ZMod p) ℂ).symm.surjective
  by_contra hc
  push Not at hc
  have hφ4 : φ ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one φ
  have hχ4 : χ ^ 4 = 1 := by rw [← h4']; exact pow_orderOf_eq_one χ
  have hord : ∀ x : DirichletCharacter ℂ p, orderOf x = 4 → x ≠ 1 ∧ x ^ 2 ≠ 1 := by
    intro x hx
    refine ⟨fun h => by rw [h, orderOf_one] at hx; norm_num at hx, fun h => ?_⟩
    have := orderOf_dvd_of_pow_eq_one h; rw [hx] at this; norm_num at this
  obtain ⟨hφ1, hφ2⟩ := hord φ h4
  obtain ⟨hχ1, hχ2⟩ := hord χ h4'
  have hφi : φ⁻¹ ≠ φ := by
    intro h; apply hφ2; rw [sq]; nth_rewrite 1 [← h]; exact inv_mul_cancel φ
  have hφsq : φ ^ 2 ≠ φ := by
    intro h; apply hφ1; have := congrArg (· * φ⁻¹) h; simpa [sq, mul_assoc] using this
  have hφsqi : φ ^ 2 ≠ φ⁻¹ := by
    intro h; apply hφ1
    have : φ ^ 3 = 1 := by rw [pow_succ, h, inv_mul_cancel]
    have hd := orderOf_dvd_of_pow_eq_one this; rw [h4] at hd; norm_num at hd
  have hχsq : χ ≠ φ ^ 2 := by
    intro h; apply hχ2; rw [h, ← pow_mul]; exact hφ4
  have hsub : ({1, φ, φ⁻¹, φ ^ 2, χ} : Finset (DirichletCharacter ℂ p)) ⊆
      univ.filter (fun x => x ^ 4 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact one_pow 4
    · exact hφ4
    · rw [inv_pow, hφ4, inv_one]
    · rw [← pow_mul, show 2 * 4 = 4 * 2 by rfl, pow_mul, hφ4, one_pow]
    · exact hχ4
  have h5 : ({1, φ, φ⁻¹, φ ^ 2, χ} : Finset (DirichletCharacter ℂ p)).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact fun h => hχsq h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
      exact ⟨hφsqi.symm, fun h => hc.2 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
      exact ⟨hφi.symm, hφsq.symm, fun h => hc.1 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
      exact ⟨hφ1.symm, (inv_ne_one.mpr hφ1).symm, hφ2.symm, hχ1.symm⟩
  have := Finset.card_le_card hsub
  have hle := IsCyclic.card_pow_eq_one_le (α := DirichletCharacter ℂ p) (n := 4) (by norm_num)
  omega

/-- **1c. 種類への分類**：位数 3 の指標 χ と、χ·L（χ は位数 3）は、すべて chiOf ψ のどれか。 -/
theorem exists_type3 (ψ χ : DirichletCharacter ℂ p) (h3 : orderOf ψ = 3) (h3' : orderOf χ = 3) :
    (∃ t : Fin 4, chiOf ψ t = χ) ∧ (∃ t : Fin 4, chiOf ψ t = χ * Lc p) := by
  rcases cubic_cases ψ χ h3 h3' with rfl | rfl
  · exact ⟨⟨0, rfl⟩, ⟨2, rfl⟩⟩
  · exact ⟨⟨1, rfl⟩, ⟨3, rfl⟩⟩

theorem exists_type4 (φ χ : DirichletCharacter ℂ p) (h4 : orderOf φ = 4) (h4' : orderOf χ = 4) :
    ∃ t : Fin 2, chiOf4 φ t = χ := by
  rcases quartic_cases φ χ h4 h4' with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- **1d. 位数 6 の指標の分解**：η = η⁴ · L、η⁴ は位数 3（PAG182.sextic_general の証明の中の式を独立させた）。 -/
theorem sextic_decomp (η : DirichletCharacter ℂ p) (h6 : orderOf η = 6) :
    orderOf (η ^ 4) = 3 ∧ η = η ^ 4 * Lc p := by
  have hd := orderOf_dvd_natCard η
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime hp.out, h6] at hd
  have := hp.out.two_le
  have hp2 : p ≠ 2 := by omega
  have hη6 : η ^ 6 = 1 := by rw [← h6]; exact pow_orderOf_eq_one η
  have hψ : orderOf (η ^ 4) = 3 := by rw [orderOf_pow' _ (by norm_num), h6]; rfl
  have hL : η ^ 3 = Lc p := by
    rcases sq_one_cases hp2 (η ^ 3) (by rw [← pow_mul]; exact hη6) with h | h
    · exfalso
      have : orderOf η ∣ 3 := orderOf_dvd_of_pow_eq_one h
      rw [h6] at this; norm_num at this
    · exact h
  refine ⟨hψ, ?_⟩
  rw [← hL, ← pow_add, show 4 + 3 = 6 + 1 by rfl, pow_add, hη6, one_mul, pow_one]

/-- **1e. 位数 6 の指標も chiOf ψ の種類のどれか**（ψL か ψ⁻¹L）。 -/
theorem exists_type6 (ψ η : DirichletCharacter ℂ p) (h3 : orderOf ψ = 3) (h6 : orderOf η = 6) :
    ∃ t : Fin 4, chiOf ψ t = η := by
  obtain ⟨h3', he⟩ := sextic_decomp η h6
  obtain ⟨t, ht⟩ := (exists_type3 ψ (η ^ 4) h3 h3').2
  exact ⟨t, ht.trans he.symm⟩

theorem prod_owner {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (o : ι → κ) (x : κ → ℂ)
    (hx : ∀ j, x j ≠ 0) (w : ι → ℤ) :
    ∏ i, x (o i) ^ w i = ∏ j, x j ^ (∑ i ∈ univ.filter (fun i => o i = j), w i) := by
  rw [← Finset.prod_fiberwise univ o (fun i => x (o i) ^ w i)]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← prod_zpow_same _ _ (hx j)]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [(Finset.mem_filter.mp hi).2]

variable {nc nq : ℕ} (pc : Fin nc → ℕ) [hpc : ∀ i, Fact (pc i).Prime] (pq : Fin nq → ℕ) [hpq : ∀ j, Fact (pq j).Prime]

/-- 素数 j の重みの和（3 次の族）。 -/
def wsum {m : ℕ} (oc : Fin m → Fin nc) (tc : Fin m → Fin 4) (j : Fin nc) : ℤ :=
  ∑ i ∈ univ.filter (fun i => oc i = j), wt (tc i)

def wsum4 {m : ℕ} (oq : Fin m → Fin nq) (tq : Fin m → Fin 2) (j : Fin nq) : ℤ :=
  ∑ i ∈ univ.filter (fun i => oq i = j), wt4 (tq i)

theorem zOf_congr {n : ℕ} (P : Fin n → ℕ) [∀ j, Fact (P j).Prime] (χ : ∀ j, DirichletCharacter ℂ (P j))
    (f : ∀ j, DirichletCharacter ℂ (P j) → DirichletCharacter ℂ (P j)) (j j' : Fin n) (h : j = j') :
    zOf (f j (χ j)) = zOf (f j' (χ j')) := by subst h; rfl

/-- **3. 重複を許して並べた積の判定**：
  3 次の族の因子 m 個（素数 oc i 上の種類 tc i）と 4 次の族の因子 m' 個（素数 oq k 上の種類 tq k）の積が
  1 の冪根 ⇔ 各素数で重みの和が 0。 -/
theorem list_root_iff (hinjc : Function.Injective pc) (h3p : ∀ i, pc i % 3 = 1)
    (ψ : ∀ i, DirichletCharacter ℂ (pc i)) (h3 : ∀ i, orderOf (ψ i) = 3)
    (hinjq : Function.Injective pq) (φ : ∀ j, DirichletCharacter ℂ (pq j)) (h4 : ∀ j, orderOf (φ j) = 4)
    {m m' : ℕ} (oc : Fin m → Fin nc) (tc : Fin m → Fin 4) (oq : Fin m' → Fin nq) (tq : Fin m' → Fin 2) :
    (∃ N : ℕ, 0 < N ∧ ((∏ i, zOf (chiOf (ψ (oc i)) (tc i))) * ∏ k, zOf (chiOf4 (φ (oq k)) (tq k))) ^ N = 1)
      ↔ (∀ j, wsum oc tc j = 0) ∧ (∀ j, wsum4 oq tq j = 0) := by
  choose r hr12 hr using fun i => val_cubic (h3p (oc i)) (ψ (oc i)) (h3 (oc i)) (tc i)
  choose r' hr12' hr' using fun k => val_quartic (φ (oq k)) (h4 (oq k)) (tq k)
  have hzc : ∀ j, zOf (ψ j) ≠ 0 := fun j => zOf_ne_zero _ (by
    intro h; have := h3 j; rw [h, orderOf_one] at this; norm_num at this)
  have hzq : ∀ j, zOf (φ j) ≠ 0 := fun j => zOf_ne_zero _ (by
    intro h; have := h4 j; rw [h, orderOf_one] at this; norm_num at this)
  set R := (∏ i, r i) * ∏ k, r' k
  have hR : R ^ 12 = 1 := by
    simp only [R, mul_pow, ← Finset.prod_pow, hr12, hr12', Finset.prod_const_one, mul_one]
  have hsplit : (∏ i, zOf (chiOf (ψ (oc i)) (tc i))) * ∏ k, zOf (chiOf4 (φ (oq k)) (tq k))
      = R * ((∏ j, (gaussSum (ψ j) stdAddChar / ((Real.sqrt (pc j) : ℝ) : ℂ)) ^ wsum oc tc j
          * (gaussSum (ψ j * Lc (pc j)) stdAddChar / ((Real.sqrt (pc j) : ℝ) : ℂ)) ^ (0 : ℤ))
        * (∏ j, (gaussSum (φ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ)) ^ wsum4 oq tq j)) := by
    simp only [zpow_zero, mul_one]
    have e1 : ∏ i, zOf (chiOf (ψ (oc i)) (tc i)) = (∏ i, r i) * ∏ i, zOf (ψ (oc i)) ^ wt (tc i) := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => hr i)
    have e2 : ∏ k, zOf (chiOf4 (φ (oq k)) (tq k)) = (∏ k, r' k) * ∏ k, zOf (φ (oq k)) ^ wt4 (tq k) := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun k _ => hr' k)
    have f1 := prod_owner oc (fun j => zOf (ψ j)) hzc (fun i => wt (tc i))
    have f2 := prod_owner oq (fun j => zOf (φ j)) hzq (fun k => wt4 (tq k))
    rw [e1, e2, f1, f2]
    simp only [R, wsum, wsum4, zOf]; ring
  rw [hsplit, root_mul_iff _ _ 12 (by norm_num) hR,
    full_root_iff pc pq hinjc h3p ψ h3 _ _ hinjq φ h4 _]
  simp only [mul_zero]

end PAG.Part184

#print axioms PAG.Part184.prod_zpow_same
#print axioms PAG.Part184.zOf_ne_zero
#print axioms PAG.Part184.inv_order3
#print axioms PAG.Part184.val_cubic
#print axioms PAG.Part184.val_quartic
#print axioms PAG.Part184.cubic_cases
#print axioms PAG.Part184.quartic_cases
#print axioms PAG.Part184.exists_type3
#print axioms PAG.Part184.exists_type4
#print axioms PAG.Part184.sextic_decomp
#print axioms PAG.Part184.exists_type6
#print axioms PAG.Part184.prod_owner
#print axioms PAG.Part184.zOf_congr
#print axioms PAG.Part184.list_root_iff

