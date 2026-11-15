/-
  PAG 2.0 Part 184（2026-10-23）— 積のケットの完全な判定（相異なる素数、素数冪の導手、整数冪）
  p_i は相異なる素数、χ_i は法 p_i^{c_i}（c_i ≥ 1）の原始指標、z_i = τ(χ_i)/√(p_i^{c_i})、a_i ∈ ℤ。
  1. multi_root_iff_fintype：Part 182 の判定を任意の有限な添字集合に移す
  2. prod_root_of_root：1 の冪根の有限積・整数冪は 1 の冪根
  3. ord_ge_two：法 p^c（c ≥ 1）の原始指標は ord χ ≥ 2
  4. prod_root_iff：∏ z_i^{a_i} が 1 の冪根 ⇔ すべての i で c_i ≥ 2 または ord χ_i = 2 または a_i = 0
     （1 の冪根でない因子は「導手 p_i・位数 ≥ 3」のものだけで、それらの冪がすべて 0 のときに限る）
  5. prod_root_iff_ones：a_i = 1（積のケット ∏ z_i）の場合
-/
import PAG187

namespace PAG.Part188

open Complex Finset
open ZMod (stdAddChar)

/-! ### 1. 任意の有限な添字集合での Part 182 -/

/-- **1.** Part 182 の判定（相異なる素数・位数 ≥ 3）を、任意の有限な添字集合に移したもの。 -/
theorem multi_root_iff_fintype {ι : Type*} [Fintype ι] (P : ι → ℕ) [hP : ∀ i, Fact (P i).Prime]
    (hinj : Function.Injective P) (χ : ∀ i, MulChar (ZMod (P i)) ℂ) (hn : ∀ i, 3 ≤ orderOf (χ i))
    (ψ : ∀ i, AddChar (ZMod (P i)) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive) (a : ι → ℤ) :
    (∃ N : ℕ, 0 < N ∧ (∏ i, (gaussSum (χ i) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i) ^ N = 1)
      ↔ ∀ i, a i = 0 := by
  classical
  let e := Fintype.equivFin ι
  have key := PAG.Part186.multi_root_iff (fun j => P (e.symm j)) (hinj.comp e.symm.injective)
    (fun j => χ (e.symm j)) (fun j => hn (e.symm j)) (fun j => ψ (e.symm j)) (fun j => hψ (e.symm j))
    (fun j => a (e.symm j))
  have hprod : ∏ i, (gaussSum (χ i) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i
      = ∏ j, (gaussSum (χ (e.symm j)) (ψ (e.symm j)) / ((Real.sqrt (P (e.symm j)) : ℝ) : ℂ)) ^ a (e.symm j) :=
    (Equiv.prod_comp e.symm (fun i => (gaussSum (χ i) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i)).symm
  rw [hprod, key]
  constructor
  · intro h i
    have := h (e i)
    simpa using this
  · intro h j
    exact h _

/-! ### 2. 1 の冪根の積 -/

/-- 1 の冪根の整数冪は 1 の冪根。 -/
theorem zpow_root (x : ℂ) (k : ℤ) (h : ∃ N : ℕ, 0 < N ∧ x ^ N = 1) : ∃ N : ℕ, 0 < N ∧ (x ^ k) ^ N = 1 := by
  obtain ⟨N, hN, hx⟩ := h
  refine ⟨N, hN, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

/-- **2.** 1 の冪根の有限積は 1 の冪根。 -/
theorem prod_root_of_root {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, ∃ N : ℕ, 0 < N ∧ f i ^ N = 1) : ∃ N : ℕ, 0 < N ∧ (∏ i ∈ s, f i) ^ N = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert j s hj ih =>
    obtain ⟨N₁, hN₁, h₁⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨N₂, hN₂, h₂⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨N₁ * N₂, Nat.mul_pos hN₁ hN₂, ?_⟩
    rw [Finset.prod_insert hj, mul_pow, pow_mul, h₁, one_pow, one_mul, mul_comm, pow_mul, h₂, one_pow]

/-! ### 3. 原始指標の位数 -/

/-- **3.** 法 p^c（c ≥ 1）の原始指標は ord χ ≥ 2。 -/
theorem ord_ge_two {p : ℕ} [hp : Fact p.Prime] (c : ℕ) (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ c))
    (hχ : χ.IsPrimitive) : 2 ≤ orderOf χ := by
  have hne : χ ≠ 1 := by
    rintro rfl
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
    have : p ≤ p ^ c := Nat.le_self_pow (by omega) p
    have := hp.out.two_le
    omega
  have h1 : orderOf χ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have h0 : 0 < orderOf χ := orderOf_pos χ
  omega

/-! ### 4. 積の判定 -/

variable {ι : Type*} [Fintype ι] (P : ι → ℕ) [hP : ∀ i, Fact (P i).Prime]

/-- **4. 積のケットの完全な判定**：相異なる素数 p_i、法 p_i^{c_i}（c_i ≥ 1）の原始指標 χ_i について、
  ∏ z_i^{a_i} が 1 の冪根 ⇔ すべての i で c_i ≥ 2 または ord χ_i = 2 または a_i = 0。 -/
theorem prod_root_iff (hinj : Function.Injective P) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (χ : ∀ i, DirichletCharacter ℂ (P i ^ c i)) (hχ : ∀ i, (χ i).IsPrimitive) (a : ι → ℤ) :
    (∃ N : ℕ, 0 < N ∧
      (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt ((P i : ℝ) ^ c i) : ℝ) : ℂ)) ^ a i) ^ N = 1)
      ↔ ∀ i, 2 ≤ c i ∨ orderOf (χ i) = 2 ∨ a i = 0 := by
  classical
  set z : ι → ℂ := fun i => gaussSum (χ i) stdAddChar / ((Real.sqrt ((P i : ℝ) ^ c i) : ℝ) : ℂ)
    with hz
  -- 悪い添字：導手 p_i（c_i = 1）で位数 ≥ 3
  set S := univ.filter (fun i => c i = 1 ∧ 3 ≤ orderOf (χ i)) with hS
  have hsplit : ∏ i, z i ^ a i = (∏ i ∈ univ.filter (fun i => ¬(c i = 1 ∧ 3 ≤ orderOf (χ i))), z i ^ a i)
      * ∏ i ∈ S, z i ^ a i := by
    rw [mul_comm, hS, Finset.prod_filter_mul_prod_filter_not]
  -- 良い添字の因子は 1 の冪根
  obtain ⟨M, hM, hY⟩ := prod_root_of_root (univ.filter (fun i => ¬(c i = 1 ∧ 3 ≤ orderOf (χ i))))
    (fun i => z i ^ a i) (fun i hi => by
      have hi' := (Finset.mem_filter.mp hi).2
      apply zpow_root
      have hroot := (PAG.Part187.single_root_iff (p := P i) (c i) (hc i) (χ i) (hχ i)).mpr (by
        have h2 := ord_ge_two (p := P i) (c i) (hc i) (χ i) (hχ i)
        by_contra hcon
        push Not at hcon
        exact hi' ⟨by have := hc i; omega, by omega⟩)
      exact hroot)
  -- 悪い添字の部分に Part 182 を使う
  have hfact : ∀ i : S, Fact (P i.1 ^ c i.1).Prime := fun i => ⟨by
    rw [(Finset.mem_filter.mp i.2).2.1, pow_one]; exact (hP i.1).out⟩
  have hinjS : Function.Injective (fun i : S => P i.1 ^ c i.1) := by
    intro i j hij
    simp only at hij
    rw [(Finset.mem_filter.mp i.2).2.1, (Finset.mem_filter.mp j.2).2.1, pow_one, pow_one] at hij
    exact Subtype.ext (hinj hij)
  have hbad := multi_root_iff_fintype (ι := S) (fun i => P i.1 ^ c i.1) hinjS (fun i => χ i.1)
    (fun i => (Finset.mem_filter.mp i.2).2.2) (fun i => stdAddChar)
    (fun i => ZMod.isPrimitive_stdAddChar (P i.1 ^ c i.1)) (fun i => a i.1)
  have hbad' : (∃ N : ℕ, 0 < N ∧ (∏ i ∈ S, z i ^ a i) ^ N = 1) ↔ ∀ i ∈ S, a i = 0 := by
    have e1 : ∏ i ∈ S, z i ^ a i
        = ∏ i : S, (gaussSum (χ i.1) stdAddChar / ((Real.sqrt ((P i.1 ^ c i.1 : ℕ) : ℝ) : ℝ) : ℂ)) ^ a i.1 := by
      rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [hz, Nat.cast_pow]
    rw [e1, hbad]
    constructor
    · intro h i hi; exact h ⟨i, hi⟩
    · intro h i; exact h i.1 i.2
  rw [hsplit, PAG.Part183.root_mul_iff _ _ M hM hY, hbad']
  constructor
  · intro h i
    by_cases hi : c i = 1 ∧ 3 ≤ orderOf (χ i)
    · exact Or.inr (Or.inr (h i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)))
    · have h2 := ord_ge_two (p := P i) (c i) (hc i) (χ i) (hχ i)
      push Not at hi
      by_cases hc1 : c i = 1
      · exact Or.inr (Or.inl (by have := hi hc1; omega))
      · exact Or.inl (by have := hc i; omega)
  · intro h i hi
    obtain ⟨hc1, h3⟩ := (Finset.mem_filter.mp hi).2
    rcases h i with h' | h' | h'
    · omega
    · omega
    · exact h'

/-- **5.** 積のケット ∏ z_i（すべての冪が 1）：1 の冪根 ⇔ すべての i で c_i ≥ 2 または ord χ_i = 2。 -/
theorem prod_root_iff_ones (hinj : Function.Injective P) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (χ : ∀ i, DirichletCharacter ℂ (P i ^ c i)) (hχ : ∀ i, (χ i).IsPrimitive) :
    (∃ N : ℕ, 0 < N ∧
      (∏ i, gaussSum (χ i) stdAddChar / ((Real.sqrt ((P i : ℝ) ^ c i) : ℝ) : ℂ)) ^ N = 1)
      ↔ ∀ i, 2 ≤ c i ∨ orderOf (χ i) = 2 := by
  have h := prod_root_iff P hinj c hc χ hχ (fun _ => 1)
  simp only [zpow_one, one_ne_zero, or_false] at h
  exact h

end PAG.Part188

#print axioms PAG.Part188.multi_root_iff_fintype
#print axioms PAG.Part188.zpow_root
#print axioms PAG.Part188.prod_root_of_root
#print axioms PAG.Part188.ord_ge_two
#print axioms PAG.Part188.prod_root_iff
#print axioms PAG.Part188.prod_root_iff_ones
