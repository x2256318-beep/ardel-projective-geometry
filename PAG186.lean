/-
  PAG 2.0 Part 182（2026-10-22）— 相異なる素数・位数 ≥ 3 の指標の整数冪の積の判定
  p_i は相異なる素数、χ_i は法 p_i の指標で n_i = ord χ_i ≥ 3、ψ_i は原始的、z_i = τ(χ_i)/√p_i、a_i ∈ ℤ。
  1. exists_prime_over：代数的整数環 B = integralClosure ℤ ℂ の素イデアル Q で、P ∈ Q、P̄ ∉ Q、p ∈ Q
     （Part 181 の評価 ev の核の上に、going-up で Q をとる）
  2. natPow_not_mem：p ∈ Q なら、p と異なる素数 q の冪は Q に入らない
  3. multi_root_iff：∏ z_i^{a_i} が 1 の冪根 ⇔ すべての a_i = 0
     （z_i^{2n_i} = P_i/P̄_i から ∏ P_i^{e_i}P̄_i^{f_i} = ∏ P_i^{f_i}P̄_i^{e_i} とし、a_j ≠ 0 の素数の Q で矛盾）
-/
import PAG185
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

namespace PAG.Part186

open Complex Finset PAG.Part185

/-! ### 1. p の上の素イデアル -/

section prime_over

variable {p : ℕ} [hp : Fact p.Prime]

theorem Pj_mem (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ) : Pj χ ∈ integralClosure ℤ ℂ := by
  obtain ⟨A, -, x, -, hA, hx, -⟩ := exists_eval_Pj χ hn
  exact hx ▸ hA x.2

theorem Pjbar_mem (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ) : Pjbar χ ∈ integralClosure ℤ ℂ := by
  obtain ⟨A, -, -, y, hA, -, hy, -⟩ := exists_eval_Pj χ hn
  exact hy ▸ hA y.2

/-- **1.** 代数的整数環の素イデアル Q で、P ∈ Q、P̄ ∉ Q、p ∈ Q となるものがある。 -/
theorem exists_prime_over (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ) :
    ∃ Q : Ideal (integralClosure ℤ ℂ), Q.IsPrime ∧
      (⟨Pj χ, Pj_mem χ hn⟩ : integralClosure ℤ ℂ) ∈ Q ∧
      (⟨Pjbar χ, Pjbar_mem χ hn⟩ : integralClosure ℤ ℂ) ∉ Q ∧
      ((p : ℕ) : integralClosure ℤ ℂ) ∈ Q := by
  obtain ⟨A, ev, x, y, hA, hx, hy, hx0, hy0⟩ := exists_eval_Pj χ hn
  let f : A →+* integralClosure ℤ ℂ := (Subalgebra.inclusion hA).toRingHom
  let _ : Algebra A (integralClosure ℤ ℂ) := f.toAlgebra
  have : IsScalarTower ℤ A (integralClosure ℤ ℂ) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [eq_intCast (algebraMap ℤ (integralClosure ℤ ℂ)), eq_intCast (algebraMap ℤ A), map_intCast])
  have : Algebra.IsIntegral A (integralClosure ℤ ℂ) :=
    ⟨fun b => (integralClosure.isIntegral b).tower_top⟩
  have hcoe : ∀ a : A, ((algebraMap A (integralClosure ℤ ℂ) a : integralClosure ℤ ℂ) : ℂ) = (a : ℂ) :=
    fun a => rfl
  have hker : RingHom.ker (algebraMap A (integralClosure ℤ ℂ)) ≤ RingHom.ker ev := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have h0 : (a : ℂ) = 0 := by rw [← hcoe, ha]; rfl
    rw [show a = 0 from Subtype.ext h0, map_zero]
  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (RingHom.ker ev) hker
  have hmem : ∀ a : A, algebraMap A (integralClosure ℤ ℂ) a ∈ Q ↔ ev a = 0 := by
    intro a
    rw [← RingHom.mem_ker, ← hQP]
    rfl
  refine ⟨Q, hQ, ?_, ?_, ?_⟩
  · have e : (⟨Pj χ, Pj_mem χ hn⟩ : integralClosure ℤ ℂ) = algebraMap A _ x :=
      Subtype.ext (show Pj χ = ((algebraMap A (integralClosure ℤ ℂ) x : integralClosure ℤ ℂ) : ℂ) by
        rw [hcoe, hx])
    rw [e, hmem]; exact hx0
  · have e : (⟨Pjbar χ, Pjbar_mem χ hn⟩ : integralClosure ℤ ℂ) = algebraMap A _ y :=
      Subtype.ext (show Pjbar χ = ((algebraMap A (integralClosure ℤ ℂ) y : integralClosure ℤ ℂ) : ℂ) by
        rw [hcoe, hy])
    rw [e, hmem]; exact hy0
  · rw [show ((p : ℕ) : integralClosure ℤ ℂ) = algebraMap A _ (p : A) by rw [map_natCast], hmem,
      map_natCast, ZMod.natCast_self]

end prime_over

/-- **2.** 素イデアル Q が素数 p を含むなら、p と異なる素数 q の冪は Q に入らない。 -/
theorem natPow_not_mem {B : Type*} [CommRing B] (Q : Ideal B) (hQ : Q.IsPrime) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpQ : (p : B) ∈ Q) (e : ℕ) : (q : B) ^ e ∉ Q := by
  intro h
  have hqQ : (q : B) ∈ Q := hQ.mem_of_pow_mem e h
  have hcop : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (1 : B) ∈ Q := by
    have := Q.add_mem (Q.mul_mem_left (u : B) hpQ) (Q.mul_mem_left (v : B) hqQ)
    have e : ((u * p + v * q : ℤ) : B) = (u : B) * (p : B) + (v : B) * (q : B) := by push_cast; ring
    rwa [← e, huv, Int.cast_one] at this
  exact hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)

/-! ### 3. 相異なる素数の積 -/

section multi

variable {m : ℕ} (P : Fin m → ℕ) [hP : ∀ i, Fact (P i).Prime]

/-- z_i^{2n_i} = P_i/P̄_i。 -/
theorem z_pow_eq_div {p : ℕ} [Fact p.Prime] (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    (gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * orderOf χ) = Pj χ / Pjbar χ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hb : Pjbar χ ≠ 0 := right_ne_zero_of_mul (by rw [Pj_mul_Pjbar χ hn]; exact pow_ne_zero _ hp0)
  rw [eq_div_iff hb]
  exact z_pow_mul_Pjbar χ hn hψ

/-- 整数冪の分解：w^c = (P^e P̄^f)/(P^f P̄^e)（w = P/P̄、e = c⁺、f = c⁻）。 -/
theorem zpow_div_split (x y : ℂ) (c : ℤ) :
    (x / y) ^ c = (x ^ c.toNat * y ^ (-c).toNat) / (x ^ (-c).toNat * y ^ c.toNat) := by
  rcases le_or_gt 0 c with h | h
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp only [zpow_natCast, Int.toNat_natCast, div_pow]
    rw [show (-(k : ℤ)).toNat = 0 by omega, pow_zero, pow_zero, mul_one, one_mul]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, c = -((k : ℤ)) := ⟨(-c).toNat, by omega⟩
    subst hk
    rw [show (-(k : ℤ)).toNat = 0 by omega, neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast,
      pow_zero, pow_zero, one_mul, mul_one, div_pow, inv_div]

/-- 冪の付け替え：(w^{2n})^{aNq} = (w^a)^{N·2nq}。 -/
theorem zpow_aux (w : ℂ) (n q : ℕ) (a : ℤ) (N : ℕ) :
    (w ^ (2 * n)) ^ (a * N * (q : ℤ)) = (w ^ a) ^ (N * (2 * (n * q))) := by
  rw [← zpow_natCast w (2 * n), ← zpow_mul, ← zpow_natCast (w ^ a), ← zpow_mul]
  congr 1
  push_cast
  ring

theorem prod_mem_of_mem {B : Type*} [CommRing B] {Q : Ideal B} (hQ : Q.IsPrime) {ι : Type*}
    (s : Finset ι) (f : ι → B) : (∏ i ∈ s, f i) ∈ Q ↔ ∃ i ∈ s, f i ∈ Q := by
  have := hQ
  exact Ideal.IsPrime.prod_mem_iff

/-- **3a. 主定理**：∏ z_i^{a_i} が 1 の冪根なら、すべての a_i = 0。 -/
theorem multi_not_root (hinj : Function.Injective P) (χ : ∀ i, MulChar (ZMod (P i)) ℂ)
    (hn : ∀ i, 3 ≤ orderOf (χ i)) (ψ : ∀ i, AddChar (ZMod (P i)) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (a : Fin m → ℤ) (N : ℕ) (hN : 0 < N)
    (h : (∏ i, (gaussSum (χ i) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i) ^ N = 1) : ∀ j, a j = 0 := by
  -- 記号
  set L : ℕ := ∏ i, orderOf (χ i) with hL
  have hnL : ∀ i, orderOf (χ i) * (L / orderOf (χ i)) = L := fun i =>
    Nat.mul_div_cancel' (Finset.dvd_prod_of_mem (fun i => orderOf (χ i)) (Finset.mem_univ i))
  have hp0 : ∀ i, ((P i : ℕ) : ℂ) ≠ 0 := fun i => by exact_mod_cast (hP i).out.ne_zero
  have hPPb : ∀ i, Pj (χ i) * Pjbar (χ i) = ((P i : ℕ) : ℂ) ^ (orderOf (χ i) - 2) :=
    fun i => Pj_mul_Pjbar (χ i) (hn i)
  have hPne : ∀ i, Pj (χ i) ≠ 0 :=
    fun i => left_ne_zero_of_mul (by rw [hPPb i]; exact pow_ne_zero _ (hp0 i))
  have hPbne : ∀ i, Pjbar (χ i) ≠ 0 :=
    fun i => right_ne_zero_of_mul (by rw [hPPb i]; exact pow_ne_zero _ (hp0 i))
  -- c_i = a_i·N·(L/n_i)、∏ (P_i/P̄_i)^{c_i} = 1
  set c : Fin m → ℤ := fun i => a i * N * ((L / orderOf (χ i) : ℕ) : ℤ) with hc_def
  have hzero : ∏ i, (Pj (χ i) / Pjbar (χ i)) ^ c i = 1 := by
    calc ∏ i, (Pj (χ i) / Pjbar (χ i)) ^ c i
        = ∏ i, ((gaussSum (χ i) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i) ^ (N * (2 * L)) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [← z_pow_eq_div (χ i) (hn i) (hψ i), ← hnL i]
          exact zpow_aux _ _ _ _ _
      _ = ((∏ i, (gaussSum (χ i) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i) ^ N) ^ (2 * L) := by
          rw [← pow_mul, Finset.prod_pow]
      _ = 1 := by rw [h, one_pow]
  -- 整数冪を分けて、∏ P^e P̄^f = ∏ P^f P̄^e
  have hsplit : ∏ i, (Pj (χ i) ^ (c i).toNat * Pjbar (χ i) ^ (-c i).toNat)
      = ∏ i, (Pj (χ i) ^ (-c i).toNat * Pjbar (χ i) ^ (c i).toNat) := by
    have hden : ∏ i, (Pj (χ i) ^ (-c i).toNat * Pjbar (χ i) ^ (c i).toNat) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => mul_ne_zero (pow_ne_zero _ (hPne i)) (pow_ne_zero _ (hPbne i)))
    rw [← div_eq_one_iff_eq hden, ← Finset.prod_div_distrib, ← hzero]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [zpow_div_split]
  -- 代数的整数環へ
  intro j
  by_contra hj
  have hcj : c j ≠ 0 := by
    have hL0 : 0 < L / orderOf (χ j) := by
      apply Nat.div_pos (Nat.le_of_dvd (Finset.prod_pos (fun i _ => by have := hn i; omega))
        (Finset.dvd_prod_of_mem (fun i => orderOf (χ i)) (Finset.mem_univ j)))
      have := hn j; omega
    exact mul_ne_zero (mul_ne_zero hj (by exact_mod_cast hN.ne')) (by exact_mod_cast hL0.ne')
  obtain ⟨Q, hQ, hXj, hYj, hpj⟩ := exists_prime_over (χ j) (hn j)
  let X : Fin m → integralClosure ℤ ℂ := fun i => ⟨Pj (χ i), Pj_mem (χ i) (hn i)⟩
  let Y : Fin m → integralClosure ℤ ℂ := fun i => ⟨Pjbar (χ i), Pjbar_mem (χ i) (hn i)⟩
  have hB : ∏ i, (X i ^ (c i).toNat * Y i ^ (-c i).toNat) = ∏ i, (X i ^ (-c i).toNat * Y i ^ (c i).toNat) := by
    apply Subtype.val_injective
    simp only [SubmonoidClass.coe_finsetProd, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    exact hsplit
  -- i ≠ j では X_i, Y_i ∉ Q
  have hother : ∀ i, i ≠ j → X i ∉ Q ∧ Y i ∉ Q := by
    intro i hij
    have hXY : X i * Y i = ((P i : ℕ) : integralClosure ℤ ℂ) ^ (orderOf (χ i) - 2) := by
      apply Subtype.val_injective
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
      exact hPPb i
    have hnot := natPow_not_mem Q hQ (hP j).out (hP i).out (fun e => hij (hinj e).symm) hpj
      (orderOf (χ i) - 2)
    rw [← hXY] at hnot
    exact ⟨fun hx => hnot (Q.mul_mem_right _ hx), fun hy => hnot (Q.mul_mem_left _ hy)⟩
  have hYjn : Y j ∉ Q := hYj
  have hXj' : X j ∈ Q := hXj
  -- 一方の辺は Q に入り、他方は入らない
  have notin : ∀ (e f : Fin m → ℕ), (e j = 0) → (∏ i, (X i ^ e i * Y i ^ f i)) ∉ Q := by
    intro e f hej hmem
    obtain ⟨i, -, hi⟩ := (prod_mem_of_mem hQ _ _).mp hmem
    rcases hQ.mem_or_mem hi with hx | hy
    · by_cases hij : i = j
      · subst hij; rw [hej, pow_zero] at hx; exact hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr hx)
      · exact (hother i hij).1 (hQ.mem_of_pow_mem _ hx)
    · by_cases hij : i = j
      · subst hij; exact hYjn (hQ.mem_of_pow_mem _ hy)
      · exact (hother i hij).2 (hQ.mem_of_pow_mem _ hy)
  have isin : ∀ (e f : Fin m → ℕ), 0 < e j → (∏ i, (X i ^ e i * Y i ^ f i)) ∈ Q := by
    intro e f hej
    exact (prod_mem_of_mem hQ _ _).mpr ⟨j, Finset.mem_univ j,
      Q.mul_mem_right _ (Q.pow_mem_of_mem hXj' _ hej)⟩
  rcases lt_or_gt_of_ne hcj with hneg | hpos
  · -- c_j < 0：右辺が Q に入り、左辺は入らない
    have h1 := isin (fun i => (-c i).toNat) (fun i => (c i).toNat) (show 0 < (-c j).toNat by omega)
    have h2 := notin (fun i => (c i).toNat) (fun i => (-c i).toNat) (show (c j).toNat = 0 by omega)
    rw [← hB] at h1
    exact h2 h1
  · -- c_j > 0：左辺が Q に入り、右辺は入らない
    have h1 := isin (fun i => (c i).toNat) (fun i => (-c i).toNat) (show 0 < (c j).toNat by omega)
    have h2 := notin (fun i => (-c i).toNat) (fun i => (c i).toNat) (show (-c j).toNat = 0 by omega)
    rw [hB] at h1
    exact h2 h1

/-- **3b. 判定**：∏ z_i^{a_i} が 1 の冪根 ⇔ すべての a_i = 0。 -/
theorem multi_root_iff (hinj : Function.Injective P) (χ : ∀ i, MulChar (ZMod (P i)) ℂ)
    (hn : ∀ i, 3 ≤ orderOf (χ i)) (ψ : ∀ i, AddChar (ZMod (P i)) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (a : Fin m → ℤ) :
    (∃ N : ℕ, 0 < N ∧ (∏ i, (gaussSum (χ i) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i) ^ N = 1)
      ↔ ∀ i, a i = 0 := by
  constructor
  · rintro ⟨N, hN, h⟩
    exact multi_not_root P hinj χ hn ψ hψ a N hN h
  · intro h0
    refine ⟨1, one_pos, ?_⟩
    simp [h0]

/-- **3c.** 標準の加法的指標・ディリクレ指標での形。 -/
theorem multi_root_iff_std (hinj : Function.Injective P) (χ : ∀ i, DirichletCharacter ℂ (P i))
    (hn : ∀ i, 3 ≤ orderOf (χ i)) (a : Fin m → ℤ) :
    (∃ N : ℕ, 0 < N ∧
      (∏ i, (gaussSum (χ i) (ZMod.stdAddChar (N := P i)) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i) ^ N = 1)
      ↔ ∀ i, a i = 0 :=
  multi_root_iff P hinj χ hn (fun _ => ZMod.stdAddChar) (fun i => ZMod.isPrimitive_stdAddChar (P i)) a

/-- **3d.** PAG184 の `zOf` での形。 -/
theorem multi_root_iff_chain (hinj : Function.Injective P) (χ : ∀ i, DirichletCharacter ℂ (P i))
    (hn : ∀ i, 3 ≤ orderOf (χ i)) (a : Fin m → ℤ) :
    (∃ N : ℕ, 0 < N ∧ (∏ i, PAG.Part184.zOf (χ i) ^ a i) ^ N = 1) ↔ ∀ i, a i = 0 :=
  multi_root_iff_std P hinj χ hn a

end multi

end PAG.Part186

#print axioms PAG.Part186.Pj_mem
#print axioms PAG.Part186.Pjbar_mem
#print axioms PAG.Part186.exists_prime_over
#print axioms PAG.Part186.natPow_not_mem
#print axioms PAG.Part186.z_pow_eq_div
#print axioms PAG.Part186.zpow_div_split
#print axioms PAG.Part186.zpow_aux
#print axioms PAG.Part186.prod_mem_of_mem
#print axioms PAG.Part186.multi_not_root
#print axioms PAG.Part186.multi_root_iff
#print axioms PAG.Part186.multi_root_iff_std
#print axioms PAG.Part186.multi_root_iff_chain
