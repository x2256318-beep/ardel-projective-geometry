/-
  PAG 2.0 Part 193（2026-10-23）— 導手がばらばらの原始指標の z の積の判定
  χ_i は法 N_i（任意）の原始指標、a_i ∈ ℤ、z = zN（τ/√N）。q 成分は pcomp q（Part 192）。
  1. family_regroup：法 p の指標 ω^{k_t} の族の積を、ω^j（1 ≤ j < ord ω）の指数の形にまとめる
  2. sep_family：法 p の自明でない指標の族の積 X と、L·Y^{±m} が代数的整数（L は p と互いに素）な Y で、
     X·Y が 1 の冪根なら X も 1 の冪根（ベズーと ℤ_p の付値、Part 187 の方法の一般化）
  3. prod_root_iff_local：∏_i z(χ_i)^{a_i} が 1 の冪根 ⇔ 素数 q ごとに ∏_{i : q ∥ N_i} z(χ_{i,q})^{a_i} が 1 の冪根
     （∏ N_i についての強い帰納法で素数 p を 1 つずつはがす）
  4. prod_root_iff_stickelberger：χ_{i,q} = ω_q^{k_{i,q}}（ord ω_q = q − 1）と書けば、
     ⇔ すべての素数 q と、q − 1 と互いに素なすべての c で Σ_{i : q ∥ N_i} a_i ((q − 1) − 2⟨c k_{i,q}⟩) = 0
  5. exists_stickelberger_data：4 の前提の ω_q と k_{i,q} はいつでもとれる
-/
import PAG196

namespace PAG.Part197

open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194 PAG.Part196

/-! ### 1. 族を指数の形にまとめる -/

/-- **1.** ω^{k_t}（ord ω ∤ k_t）の族の積 = ∏_{1 ≤ j < ord ω} z(ω^j)^{e_j}（e_j = Σ_{k_t ≡ j} b_t）。 -/
theorem family_regroup {p : ℕ} [hp : Fact p.Prime] (ω : DirichletCharacter ℂ p) {κ : Type*}
    (s : Finset κ) (k : κ → ℕ) (hk : ∀ t ∈ s, ¬ orderOf ω ∣ k t) (b : κ → ℤ) :
    ∏ t ∈ s, zN (ω ^ k t) ^ b t =
      ∏ j ∈ Ico 1 (orderOf ω), zN (ω ^ j) ^ (∑ t ∈ s with k t % orderOf ω = j, b t) := by
  classical
  have hnpos : 0 < orderOf ω := PAG.Part185.orderOf_pos_chi ω
  have hmaps : ∀ t ∈ s, k t % orderOf ω ∈ Ico 1 (orderOf ω) := by
    intro t ht
    rw [mem_Ico]
    exact ⟨Nat.pos_of_ne_zero (fun h0 => hk t ht (Nat.dvd_of_mod_eq_zero h0)), Nat.mod_lt _ hnpos⟩
  rw [← prod_fiberwise_of_maps_to hmaps]
  refine prod_congr rfl (fun j hj => ?_)
  rw [mem_Ico] at hj
  have hz : zN (ω ^ j) ≠ 0 :=
    PAG.Part192.z_ne_zero _ (pow_ne_one_of_lt_orderOf (by omega) hj.2) (ZMod.isPrimitive_stdAddChar p)
  rw [← PAG.Part192.prod_zpow_const _ _ hz]
  refine prod_congr rfl (fun t ht => ?_)
  rw [mem_filter] at ht
  rw [← pow_mod_orderOf ω (k t), ht.2]

/-! ### 2. 分離 -/

/-- **2. 分離**：法 p の自明でない指標 φ_t の族の積 X と、L·Y^m・L·Y^{−m} が代数的整数（L は p と
  互いに素）な Y について、X·Y が 1 の冪根なら X も 1 の冪根。 -/
theorem sep_family {p : ℕ} [hp : Fact p.Prime] {κ : Type*} (s : Finset κ)
    (φ : κ → DirichletCharacter ℂ p) (hφ : ∀ t ∈ s, φ t ≠ 1) (b : κ → ℤ) (Y : ℂ) (L : ℕ)
    (hL : p.Coprime L) (m : ℕ) (hm : 0 < m) (hY1 : IsIntegral ℤ ((L : ℂ) * Y ^ m))
    (hY2 : IsIntegral ℤ ((L : ℂ) * (Y ^ m)⁻¹))
    (h : ∃ K : ℕ, 0 < K ∧ ((∏ t ∈ s, zN (φ t) ^ b t) * Y) ^ K = 1) :
    ∃ K : ℕ, 0 < K ∧ (∏ t ∈ s, zN (φ t) ^ b t) ^ K = 1 := by
  classical
  obtain ⟨K, hK, hXY⟩ := h
  obtain ⟨ω, -, hgen⟩ := exists_generator p
  choose k hk using fun t => hgen (φ t)
  have hkn : ∀ t ∈ s, ¬ orderOf ω ∣ k t := by
    intro t ht hdvd
    apply hφ t ht
    obtain ⟨c, hc⟩ := hdvd
    rw [hk t, hc, pow_mul, pow_orderOf_eq_one, one_pow]
  set e : ℕ → ℤ := fun j => ∑ t ∈ s with k t % orderOf ω = j, b t with he
  have hX : ∏ t ∈ s, zN (φ t) ^ b t = ∏ j ∈ Ico 1 (orderOf ω), zN (ω ^ j) ^ e j := by
    rw [← family_regroup ω s k hkn b]
    exact prod_congr rfl (fun t _ => by rw [hk t])
  rcases Nat.lt_or_ge (orderOf ω) 2 with hn | hn
  · refine ⟨1, one_pos, ?_⟩
    rw [hX, Ico_eq_empty_of_le (by omega), prod_empty, one_pow]
  suffices hS : ∀ c : ℕ, c.Coprime (orderOf ω) →
      ∑ j ∈ Ico 1 (orderOf ω), e j * ((orderOf ω : ℤ) - 2 * ((c * j % orderOf ω : ℕ) : ℤ)) = 0 by
    obtain ⟨N, hN, hN1⟩ := PAG.Part190.same_prime_sufficient ω (ZMod.isPrimitive_stdAddChar p) e hS
    exact ⟨N, hN, by rw [hX]; exact hN1⟩
  intro c hc
  obtain ⟨A, U, V, M₀, hYUV, h1, h2, -, -, hval⟩ :=
    PAG.Part191.exists_UV (p := p) ω (ZMod.isPrimitive_stdAddChar p) hn e
  obtain ⟨ι, hιU, hιV, hdiff⟩ := hval c hc
  set n := orderOf ω with hn_def
  set X := ∏ t ∈ s, zN (φ t) ^ b t with hX_def
  have hY₁ : X ^ (2 * n) = (U : ℂ) / (V : ℂ) := by rw [hX]; exact hYUV
  have hrel : (X ^ (2 * n)) ^ (m * K) * (Y ^ m) ^ (2 * n * K) = 1 := by
    rw [← pow_mul, ← pow_mul, show 2 * n * (m * K) = K * (2 * n * m) by ring,
      show m * (2 * n * K) = K * (2 * n * m) by ring, ← mul_pow, pow_mul, hXY, one_pow]
  rw [hY₁] at hrel
  set T := m * K with hT
  have hTpos : 0 < T := Nat.mul_pos hm hK
  set R := 2 * n * K with hR
  have hZ : ((U : ℂ) / (V : ℂ)) ^ T = ((Y ^ m)⁻¹) ^ R := by
    rw [inv_pow]; exact eq_inv_of_mul_eq_one_left hrel
  have hZinv : ((V : ℂ) / (U : ℂ)) ^ T = (Y ^ m) ^ R := by
    rw [← inv_div, inv_pow, hZ, inv_pow, inv_inv]
  have hcop : IsCoprime ((p : ℤ) ^ (M₀ * T)) ((L : ℤ) ^ R) :=
    (Nat.isCoprime_iff_coprime.mpr hL).pow
  have hint : IsIntegral ℤ (((U : ℂ) / (V : ℂ)) ^ T) := by
    apply PAG.Part191.isIntegral_of_coprime _ _ _ hcop
    · push_cast
      rw [pow_mul, ← mul_pow]
      exact h1.pow _
    · push_cast
      rw [hZ, ← mul_pow]
      exact hY2.pow _
  have hint' : IsIntegral ℤ (((V : ℂ) / (U : ℂ)) ^ T) := by
    apply PAG.Part191.isIntegral_of_coprime _ _ _ hcop
    · push_cast
      rw [pow_mul, ← mul_pow]
      exact h2.pow _
    · push_cast
      rw [hZinv, ← mul_pow]
      exact hY1.pow _
  have hZ' : IsIntegral ℤ (((U ^ T : A) : ℂ) / ((V ^ T : A) : ℂ)) := by
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← div_pow]; exact hint
  have hZinv' : IsIntegral ℤ (((V ^ T : A) : ℂ) / ((U ^ T : A) : ℂ)) := by
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← div_pow]; exact hint'
  have v1 := PAG.Part191.val_le_of_isIntegral ι (U ^ T) (V ^ T)
    (by rw [map_pow]; exact pow_ne_zero _ hιU) (by rw [map_pow]; exact pow_ne_zero _ hιV) hZ'
  have v2 := PAG.Part191.val_le_of_isIntegral ι (V ^ T) (U ^ T)
    (by rw [map_pow]; exact pow_ne_zero _ hιV) (by rw [map_pow]; exact pow_ne_zero _ hιU) hZinv'
  rw [map_pow, map_pow, PadicInt.valuation_pow, PadicInt.valuation_pow] at v1 v2
  have heq : (ι U).valuation = (ι V).valuation :=
    le_antisymm (Nat.le_of_mul_le_mul_left v2 hTpos) (Nat.le_of_mul_le_mul_left v1 hTpos)
  rw [← hdiff, heq, sub_self]

/-! ### 3. 整数性の補題 -/

/-- 代数的整数の有限積は代数的整数。 -/
theorem isIntegral_prod {κ : Type*} (s : Finset κ) (f : κ → ℂ) (hf : ∀ t ∈ s, IsIntegral ℤ (f t)) :
    IsIntegral ℤ (∏ t ∈ s, f t) := by
  have : (∏ t ∈ s, f t) ∈ integralClosure ℤ ℂ :=
    prod_mem (fun t ht => (mem_integralClosure_iff ℤ ℂ).mpr (hf t ht))
  exact (mem_integralClosure_iff ℤ ℂ).mp this

/-- M·w と M·w⁻¹ が代数的整数なら、M^{|a|}·w^a も代数的整数。 -/
theorem isIntegral_natAbs_zpow (M : ℕ) (w : ℂ) (h1 : IsIntegral ℤ ((M : ℂ) * w))
    (h2 : IsIntegral ℤ ((M : ℂ) * w⁻¹)) (a : ℤ) : IsIntegral ℤ ((M : ℂ) ^ a.natAbs * w ^ a) := by
  rcases Int.eq_nat_or_neg a with ⟨n, rfl | rfl⟩
  · rw [Int.natAbs_natCast, zpow_natCast, ← mul_pow]; exact h1.pow n
  · rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]
    exact h2.pow n

theorem pow_two_zpow (w : ℂ) (a : ℤ) : (w ^ a) ^ 2 = (w ^ 2) ^ a := by
  rw [← zpow_natCast, ← zpow_natCast w 2, ← zpow_mul, ← zpow_mul, mul_comm]

/-- 原始指標の族の z の積 Y について、Y ≠ 0 で、L·Y² と L·Y⁻² は代数的整数（L = ∏ M_t^{|a_t|}）。 -/
theorem isIntegral_prod_zN {κ : Type*} (s : Finset κ) (M : κ → ℕ) [∀ t, NeZero (M t)]
    (ψ : ∀ t, DirichletCharacter ℂ (M t)) (hψ : ∀ t, (ψ t).IsPrimitive) (a : κ → ℤ) :
    (∏ t ∈ s, zN (ψ t) ^ a t) ≠ 0 ∧
    IsIntegral ℤ (((∏ t ∈ s, M t ^ (a t).natAbs : ℕ) : ℂ) * (∏ t ∈ s, zN (ψ t) ^ a t) ^ 2) ∧
    IsIntegral ℤ (((∏ t ∈ s, M t ^ (a t).natAbs : ℕ) : ℂ) * ((∏ t ∈ s, zN (ψ t) ^ a t) ^ 2)⁻¹) := by
  have hz := fun t => isIntegral_zN_sq (ψ t) (hψ t)
  refine ⟨prod_ne_zero_iff.mpr (fun t _ => zpow_ne_zero _ (hz t).1), ?_, ?_⟩
  · have e1 : ((∏ t ∈ s, M t ^ (a t).natAbs : ℕ) : ℂ) * (∏ t ∈ s, zN (ψ t) ^ a t) ^ 2
        = ∏ t ∈ s, ((M t : ℂ) ^ (a t).natAbs * (zN (ψ t) ^ 2) ^ a t) := by
      rw [Nat.cast_prod, ← prod_pow, ← prod_mul_distrib]
      refine prod_congr rfl (fun t _ => ?_)
      rw [Nat.cast_pow, pow_two_zpow]
    rw [e1]
    exact isIntegral_prod _ _ (fun t _ => isIntegral_natAbs_zpow _ _ (hz t).2.1 (hz t).2.2 _)
  · have e2 : ((∏ t ∈ s, M t ^ (a t).natAbs : ℕ) : ℂ) * ((∏ t ∈ s, zN (ψ t) ^ a t) ^ 2)⁻¹
        = ∏ t ∈ s, ((M t : ℂ) ^ (a t).natAbs * ((zN (ψ t) ^ 2)⁻¹) ^ a t) := by
      rw [Nat.cast_prod, ← prod_pow, ← prod_inv_distrib, ← prod_mul_distrib]
      refine prod_congr rfl (fun t _ => ?_)
      rw [Nat.cast_pow, ← inv_pow, ← inv_zpow, pow_two_zpow, inv_pow]
    rw [e2]
    exact isIntegral_prod _ _ (fun t _ => isIntegral_natAbs_zpow _ _ (hz t).2.2
      (by rw [inv_inv]; exact (hz t).2.1) _)

/-! ### 4. 成分の両立 -/

/-- q ∥ A（A·B = N、互いに素）なら、A 成分の q 成分は χ の q 成分。 -/
theorem pcomp_hall {N A B : ℕ} [NeZero A] [NeZero B] (hAB : A * B = N) (hcop : A.Coprime B)
    (q : ℕ) [hq : Fact q.Prime] (hqA : q ∣ A) (hq2A : ¬ q ^ 2 ∣ A) (χ : DirichletCharacter ℂ N) :
    pcomp q (hall A B hAB hcop χ) = pcomp q χ := by
  have hqB : q.Coprime B := Nat.Coprime.coprime_dvd_left hqA hcop
  have hqN : q ∣ N := hAB ▸ dvd_mul_of_dvd_left hqA B
  have hq2N : ¬ q ^ 2 ∣ N := by
    rw [← hAB]
    intro h
    exact hq2A ((Nat.Coprime.pow_left 2 hqB).dvd_of_dvd_mul_right h)
  have hA' : q ∣ A ∧ ¬ q ^ 2 ∣ A := ⟨hqA, hq2A⟩
  have hN' : q ∣ N ∧ ¬ q ^ 2 ∣ N := ⟨hqN, hq2N⟩
  have : NeZero (A / q) := ⟨(pcomp_aux hq.out hA').1.ne'⟩
  have : NeZero (N / q) := ⟨(pcomp_aux hq.out hN').1.ne'⟩
  rw [pcomp_of q _ hA', pcomp_of q χ hN']
  exact hall_hall hAB hcop (Nat.mul_div_cancel' hqA) (pcomp_aux hq.out hA').2
    (Nat.mul_div_cancel' hqN) (pcomp_aux hq.out hN').2
    (by rw [Nat.div_mul_right_comm hqA, hAB])
    (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hqA) hcop) χ

/-- q ≠ p（素数）なら q^k ∣ p^e·M ⇔ q^k ∣ M。 -/
theorem pow_dvd_iff_of_ne {q p e M : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) (k : ℕ) :
    q ^ k ∣ p ^ e * M ↔ q ^ k ∣ M :=
  ⟨fun h => (Nat.Coprime.pow k e ((Nat.coprime_primes hq hp).mpr hqp)).dvd_of_dvd_mul_left h,
    fun h => dvd_mul_of_dvd_right h _⟩

/-! ### 5. 主定理 -/

/-- 判定の右辺：素数 q ごとに、q ∥ N_i となる i の q 成分の z の積が 1 の冪根。 -/
def LocalCrit {ι : Type*} [Fintype ι] (N : ι → ℕ) (χ : ∀ i, DirichletCharacter ℂ (N i))
    (a : ι → ℤ) : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], ∃ K : ℕ, 0 < K ∧
    (∏ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i), zN (pcomp q (χ i)) ^ a i) ^ K = 1

/-- q = q′ なら右辺の q の積は同じ。 -/
theorem localProd_congr {ι : Type*} [Fintype ι] (N : ι → ℕ) (χ : ∀ i, DirichletCharacter ℂ (N i))
    (a : ι → ℤ) {q q' : ℕ} (h : q = q') [Fact q.Prime] [Fact q'.Prime] :
    ∏ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i), zN (pcomp q (χ i)) ^ a i =
      ∏ i ∈ univ.filter (fun i => q' ∣ N i ∧ ¬ q' ^ 2 ∣ N i), zN (pcomp q' (χ i)) ^ a i := by
  subst h
  rfl

/-- 帰納法のための形。 -/
theorem prod_root_iff_aux {ι : Type*} [Fintype ι] (a : ι → ℤ) (D : ℕ) :
    ∀ (N : ι → ℕ) (_ : ∀ i, NeZero (N i)), ∏ i, N i = D →
      ∀ (χ : ∀ i, DirichletCharacter ℂ (N i)), (∀ i, (χ i).IsPrimitive) →
        ((∃ K : ℕ, 0 < K ∧ (∏ i, zN (χ i) ^ a i) ^ K = 1) ↔ LocalCrit N χ a) := by
  induction D using Nat.strong_induction_on with
  | _ D IH =>
  intro N hNZ hD χ hχ
  classical
  by_cases hD1 : D = 1
  · have hN1 : ∀ i, N i = 1 := by
      intro i
      have h := Finset.dvd_prod_of_mem N (mem_univ i)
      rw [hD, hD1] at h
      exact Nat.dvd_one.mp h
    have hz1 : ∏ i, zN (χ i) ^ a i = 1 :=
      prod_eq_one (fun i _ => by rw [zN_level_one (hN1 i) (χ i), one_zpow])
    constructor
    · intro _ q hq
      refine ⟨1, one_pos, ?_⟩
      rw [pow_one]
      apply prod_eq_one
      intro i hi
      have h := (mem_filter.mp hi).2.1
      rw [hN1 i] at h
      exact absurd (Nat.le_of_dvd one_pos h) (by have := hq.out.two_le; omega)
    · intro _
      exact ⟨1, one_pos, by rw [hz1, one_pow]⟩
  -- D > 1：素数 p をはがす
  have hD0 : D ≠ 0 := by
    rw [← hD]; exact prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (N i))
  obtain ⟨p, hp, hpD⟩ : ∃ p, p.Prime ∧ p ∣ D := ⟨D.minFac, Nat.minFac_prime hD1, Nat.minFac_dvd D⟩
  have : Fact p.Prime := ⟨hp⟩
  set e : ι → ℕ := fun i => (N i).factorization p with he
  set M : ι → ℕ := fun i => N i / p ^ e i with hM
  have hNM : ∀ i, p ^ e i * M i = N i := fun i => Nat.ordProj_mul_ordCompl_eq_self (N i) p
  have hpM : ∀ i, p.Coprime (M i) := fun i => Nat.coprime_ordCompl hp (NeZero.ne (N i))
  have hcop : ∀ i, (p ^ e i).Coprime (M i) := fun i => (hpM i).pow_left _
  have hMZ : ∀ i, NeZero (M i) := fun i => ⟨(Nat.ordCompl_pos p (NeZero.ne (N i))).ne'⟩
  have hMN : ∀ i, M i * p ^ e i = N i := fun i => (mul_comm _ _).trans (hNM i)
  set χp : ∀ i, DirichletCharacter ℂ (p ^ e i) := fun i => hall (p ^ e i) (M i) (hNM i) (hcop i) (χ i)
    with hχp
  set χb : ∀ i, DirichletCharacter ℂ (M i) := fun i => hall (M i) (p ^ e i) (hMN i) (hcop i).symm (χ i)
    with hχb
  have hz : ∀ i, ∃ ζ : ℂ, (∃ K : ℕ, 0 < K ∧ ζ ^ K = 1) ∧ zN (χ i) = ζ * (zN (χp i) * zN (χb i)) :=
    fun i => z_hall (p ^ e i) (M i) (hNM i) (hcop i) (χ i)
  choose ζ hζ hzi using hz
  have hχp_prim : ∀ i, (χp i).IsPrimitive := fun i => hall_isPrimitive _ _ _ _ (χ i) (hχ i)
  have hχb_prim : ∀ i, (χb i).IsPrimitive := fun i => hall_isPrimitive _ _ _ _ (χ i) (hχ i)
  -- p 部分
  set S := univ.filter (fun i => p ∣ N i ∧ ¬ p ^ 2 ∣ N i) with hS
  have he1 : ∀ i, (p ∣ N i ∧ ¬ p ^ 2 ∣ N i) ↔ e i = 1 := by
    intro i
    have h1 := hp.pow_dvd_iff_le_factorization (k := 1) (NeZero.ne (N i))
    have h2 := hp.pow_dvd_iff_le_factorization (k := 2) (NeZero.ne (N i))
    rw [pow_one] at h1
    rw [h1, h2]
    show 1 ≤ e i ∧ ¬ 2 ≤ e i ↔ e i = 1
    omega
  have hXp : ∀ i ∈ S, zN (χp i) = zN (pcomp p (χ i)) := by
    intro i hi
    have h := (mem_filter.mp hi).2
    have hei := (he1 i).mp h
    have : NeZero (N i / p) := ⟨(pcomp_aux hp h).1.ne'⟩
    rw [pcomp_of p (χ i) h]
    exact zN_hall_congr (by rw [hei, pow_one]) (by show N i / p ^ e i = N i / p; rw [hei, pow_one])
      (hNM i) (Nat.mul_div_cancel' h.1) (hcop i) (pcomp_aux hp h).2 (χ i)
  have hXroot : ∀ i, ¬ (p ∣ N i ∧ ¬ p ^ 2 ∣ N i) → ∃ K : ℕ, 0 < K ∧ zN (χp i) ^ K = 1 := by
    intro i hi
    have hne : e i ≠ 1 := fun h => hi ((he1 i).mpr h)
    rcases Nat.lt_or_ge (e i) 1 with h0 | h2
    · refine ⟨1, one_pos, ?_⟩
      rw [pow_one]
      exact zN_level_one (by rw [show e i = 0 by omega, pow_zero]) (χp i)
    · obtain ⟨K, hK, hK1⟩ := (PAG.Part187.single_root_iff (p := p) (e i) (by omega) (χp i)
        (hχp_prim i)).mpr (Or.inl (by omega))
      refine ⟨K, hK, ?_⟩
      unfold zN
      rw [Nat.cast_pow]
      exact hK1
  set X₁ := ∏ i ∈ S, zN (pcomp p (χ i)) ^ a i with hX₁
  set R := ∏ i ∈ univ.filter (fun i => ¬ (p ∣ N i ∧ ¬ p ^ 2 ∣ N i)), zN (χp i) ^ a i with hR_def
  set Y := ∏ i, zN (χb i) ^ a i with hY
  have hXsplit : ∏ i, zN (χp i) ^ a i = X₁ * R := by
    rw [← prod_filter_mul_prod_filter_not univ (fun i => p ∣ N i ∧ ¬ p ^ 2 ∣ N i)]
    congr 1
    exact prod_congr rfl (fun i hi => by rw [hXp i hi])
  obtain ⟨KR, hKR, hR⟩ := PAG.Part188.prod_root_of_root _ (fun i => zN (χp i) ^ a i)
    (fun i hi => PAG.Part188.zpow_root _ _ (hXroot i (mem_filter.mp hi).2))
  obtain ⟨KC, hKC, hC⟩ := PAG.Part188.prod_root_of_root univ (fun i => ζ i ^ a i)
    (fun i _ => PAG.Part188.zpow_root _ _ (hζ i))
  have hfac : ∏ i, zN (χ i) ^ a i = (∏ i, ζ i ^ a i) * ((X₁ * R) * Y) := by
    rw [← hXsplit, hY, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl (fun i _ => ?_)
    rw [hzi i, mul_zpow, mul_zpow]
  have step1 : (∃ K : ℕ, 0 < K ∧ (∏ i, zN (χ i) ^ a i) ^ K = 1) ↔
      (∃ K : ℕ, 0 < K ∧ (X₁ * Y) ^ K = 1) := by
    rw [hfac, PAG.Part183.root_mul_iff _ _ KC hKC hC, show X₁ * R * Y = R * (X₁ * Y) by ring,
      PAG.Part183.root_mul_iff _ _ KR hKR hR]
  -- 分離
  obtain ⟨hY0, hYint1, hYint2⟩ := isIntegral_prod_zN univ M χb hχb_prim a
  have hL : p.Coprime (∏ i, M i ^ (a i).natAbs) :=
    Nat.Coprime.prod_right (fun i _ => (hpM i).pow_right _)
  have hX₁φ : ∀ i ∈ S, pcomp p (χ i) ≠ 1 := by
    intro i hi
    have h := (mem_filter.mp hi).2
    have : NeZero (N i / p) := ⟨(pcomp_aux hp h).1.ne'⟩
    rw [pcomp_of p (χ i) h]
    exact PAG.Part195.ne_one_of_isPrimitive hp.two_le _ (hall_isPrimitive _ _ _ _ (χ i) (hχ i))
  have step2 : (∃ K : ℕ, 0 < K ∧ (X₁ * Y) ^ K = 1) ↔
      (∃ K : ℕ, 0 < K ∧ X₁ ^ K = 1) ∧ (∃ K : ℕ, 0 < K ∧ Y ^ K = 1) := by
    constructor
    · intro h
      obtain ⟨K1, hK1, hK1'⟩ := sep_family S (fun i => pcomp p (χ i)) hX₁φ a Y _ hL 2 two_pos
        hYint1 hYint2 h
      exact ⟨⟨K1, hK1, hK1'⟩, (PAG.Part183.root_mul_iff _ _ K1 hK1 hK1').mp h⟩
    · rintro ⟨⟨K1, hK1, hK1'⟩, hYr⟩
      exact (PAG.Part183.root_mul_iff _ _ K1 hK1 hK1').mpr hYr
  -- 帰納法の仮定
  have hlt : ∏ i, M i < D := by
    rw [← hD]
    obtain ⟨i₀, -, hi₀⟩ := (Prime.dvd_finsetProd_iff hp.prime N).mp (hD ▸ hpD)
    have hprod : ∏ i, N i = (∏ i, p ^ e i) * ∏ i, M i := by
      rw [← prod_mul_distrib]; exact prod_congr rfl (fun i _ => (hNM i).symm)
    have hP : 2 ≤ ∏ i, p ^ e i := by
      rw [prod_pow_eq_pow_sum]
      have hs : 1 ≤ ∑ i, e i :=
        le_trans (hp.factorization_pos_of_dvd (NeZero.ne (N i₀)) hi₀)
          (single_le_sum (fun i _ => Nat.zero_le (e i)) (mem_univ i₀))
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ ∑ i, e i := Nat.pow_le_pow_right hp.pos hs
    have hQ : 0 < ∏ i, M i := prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (M i)))
    rw [hprod]
    nlinarith
  have hIH := IH (∏ i, M i) hlt M hMZ rfl χb hχb_prim
  -- 右辺を比べる
  have hfil : ∀ q : ℕ, q.Prime → q ≠ p →
      univ.filter (fun i => q ∣ M i ∧ ¬ q ^ 2 ∣ M i) = univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i) := by
    intro q hq hqp
    apply filter_congr
    intro i _
    have k1 := pow_dvd_iff_of_ne (e := e i) (M := M i) hq hp hqp 1
    have k2 := pow_dvd_iff_of_ne (e := e i) (M := M i) hq hp hqp 2
    rw [pow_one, hNM i] at k1
    rw [hNM i] at k2
    rw [k1, k2]
  have hpc : ∀ (q : ℕ) [Fact q.Prime], ∀ i, q ∣ M i → ¬ q ^ 2 ∣ M i → pcomp q (χb i) = pcomp q (χ i) :=
    fun q _ i h1 h2 => pcomp_hall (hMN i) (hcop i).symm q h1 h2 (χ i)
  have step3 : LocalCrit N χ a ↔ (∃ K : ℕ, 0 < K ∧ X₁ ^ K = 1) ∧ LocalCrit M χb a := by
    constructor
    · intro H
      refine ⟨H p, fun q hq => ?_⟩
      by_cases hqp : q = p
      · refine ⟨1, one_pos, ?_⟩
        rw [pow_one]
        apply prod_eq_one
        intro i hi
        exfalso
        have h := (mem_filter.mp hi).2.1
        rw [hqp] at h
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp (hpM i) h
      · obtain ⟨K, hK, hK1⟩ := H q
        refine ⟨K, hK, ?_⟩
        have e3 : ∏ i ∈ univ.filter (fun i => q ∣ M i ∧ ¬ q ^ 2 ∣ M i), zN (pcomp q (χb i)) ^ a i
            = ∏ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i), zN (pcomp q (χ i)) ^ a i := by
          rw [hfil q hq.out hqp]
          refine prod_congr rfl (fun i hi => ?_)
          have hiM : q ∣ M i ∧ ¬ q ^ 2 ∣ M i := by
            rw [← hfil q hq.out hqp] at hi
            exact (mem_filter.mp hi).2
          rw [hpc q i hiM.1 hiM.2]
        rw [e3]
        exact hK1
    · rintro ⟨hX₁r, H'⟩ q hq
      by_cases hqp : q = p
      · rw [localProd_congr N χ a hqp]
        exact hX₁r
      · obtain ⟨K, hK, hK1⟩ := H' q
        refine ⟨K, hK, ?_⟩
        have e3 : ∏ i ∈ univ.filter (fun i => q ∣ M i ∧ ¬ q ^ 2 ∣ M i), zN (pcomp q (χb i)) ^ a i
            = ∏ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i), zN (pcomp q (χ i)) ^ a i := by
          rw [hfil q hq.out hqp]
          refine prod_congr rfl (fun i hi => ?_)
          have hiM : q ∣ M i ∧ ¬ q ^ 2 ∣ M i := by
            rw [← hfil q hq.out hqp] at hi
            exact (mem_filter.mp hi).2
          rw [hpc q i hiM.1 hiM.2]
        rw [← e3]
        exact hK1
  rw [step1, step2, hIH, step3]

/-- **3. 主定理**：原始指標 χ_i（法 N_i）と a_i ∈ ℤ について、∏_i z(χ_i)^{a_i} が 1 の冪根 ⇔
  素数 q ごとに、q ∥ N_i となる i の q 成分の z の積 ∏ z(χ_{i,q})^{a_i} が 1 の冪根。 -/
theorem prod_root_iff_local {ι : Type*} [Fintype ι] (N : ι → ℕ) [hN : ∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i)) (hχ : ∀ i, (χ i).IsPrimitive) (a : ι → ℤ) :
    (∃ K : ℕ, 0 < K ∧ (∏ i, zN (χ i) ^ a i) ^ K = 1) ↔ LocalCrit N χ a :=
  prod_root_iff_aux a _ N hN rfl χ hχ

/-! ### 6. シュティッケルベルガー型の判定 -/

/-- 法 q の族（生成指標 ω の冪）：1 の冪根 ⇔ q − 1 と互いに素なすべての c で Σ b_t((q−1) − 2⟨c k_t⟩) = 0。 -/
theorem local_root_iff {q : ℕ} [Fact q.Prime] (ω : DirichletCharacter ℂ q) (hω : orderOf ω = q - 1)
    {κ : Type*} (s : Finset κ) (k : κ → ℕ) (hk : ∀ t ∈ s, ¬ (q - 1) ∣ k t) (b : κ → ℤ) :
    (∃ K : ℕ, 0 < K ∧ (∏ t ∈ s, zN (ω ^ k t) ^ b t) ^ K = 1) ↔
      ∀ c : ℕ, c.Coprime (q - 1) →
        ∑ t ∈ s, b t * (((q - 1 : ℕ) : ℤ) - 2 * ((c * k t % (q - 1) : ℕ) : ℤ)) = 0 := by
  have h := PAG.Part192.family_root_iff ω (ZMod.isPrimitive_stdAddChar q) s k (by rwa [hω]) b
  rw [hω] at h
  exact h

/-- **4. シュティッケルベルガー型の判定**：素数 q ごとに位数 q − 1 の指標 ω_q をとり、
  q ∥ N_i のとき χ_i の q 成分を ω_q^{k_{i,q}} と書く。このとき ∏_i z(χ_i)^{a_i} が 1 の冪根 ⇔
  すべての素数 q と、q − 1 と互いに素なすべての c で Σ_{i : q ∥ N_i} a_i ((q − 1) − 2⟨c k_{i,q}⟩) = 0。 -/
theorem prod_root_iff_stickelberger {ι : Type*} [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i)) (hχ : ∀ i, (χ i).IsPrimitive) (a : ι → ℤ)
    (ω : ∀ q : ℕ, DirichletCharacter ℂ q) (hω : ∀ q : ℕ, q.Prime → orderOf (ω q) = q - 1)
    (k : ι → ℕ → ℕ)
    (hk : ∀ (q : ℕ) [Fact q.Prime] (i : ι), q ∣ N i → ¬ q ^ 2 ∣ N i → pcomp q (χ i) = ω q ^ k i q) :
    (∃ K : ℕ, 0 < K ∧ (∏ i, zN (χ i) ^ a i) ^ K = 1) ↔
      ∀ q : ℕ, q.Prime → ∀ c : ℕ, c.Coprime (q - 1) →
        ∑ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i),
          a i * (((q - 1 : ℕ) : ℤ) - 2 * ((c * k i q % (q - 1) : ℕ) : ℤ)) = 0 := by
  rw [prod_root_iff_local N χ hχ a]
  have key : ∀ (q : ℕ) [hq : Fact q.Prime],
      ((∃ K : ℕ, 0 < K ∧ (∏ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i),
        zN (pcomp q (χ i)) ^ a i) ^ K = 1) ↔
      ∀ c : ℕ, c.Coprime (q - 1) →
        ∑ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i),
          a i * (((q - 1 : ℕ) : ℤ) - 2 * ((c * k i q % (q - 1) : ℕ) : ℤ)) = 0) := by
    intro q hq
    have hprod : ∏ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i), zN (pcomp q (χ i)) ^ a i
        = ∏ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i), zN (ω q ^ k i q) ^ a i :=
      prod_congr rfl (fun i hi => by rw [hk q i (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2])
    have hkn : ∀ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i), ¬ (q - 1) ∣ k i q := by
      intro i hi hdvd
      have h := (mem_filter.mp hi).2
      have : NeZero (N i / q) := ⟨(pcomp_aux hq.out h).1.ne'⟩
      have hne : pcomp q (χ i) ≠ 1 := by
        rw [pcomp_of q (χ i) h]
        exact PAG.Part195.ne_one_of_isPrimitive hq.out.two_le _ (hall_isPrimitive _ _ _ _ (χ i) (hχ i))
      apply hne
      rw [hk q i h.1 h.2]
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, pow_mul, ← hω q hq.out, pow_orderOf_eq_one, one_pow]
    rw [hprod]
    exact local_root_iff (ω q) (hω q hq.out) _ (fun i => k i q) hkn a
  unfold LocalCrit
  constructor
  · intro H q hq
    have : Fact q.Prime := ⟨hq⟩
    exact (key q).mp (H q)
  · intro H q hq
    exact (key q).mpr (H q hq.out)

/-- **5.** 判定の前提（各素数 q の位数 q − 1 の指標 ω_q と、成分の指数 k_{i,q}）はいつでもとれる。 -/
theorem exists_stickelberger_data {ι : Type*} (N : ι → ℕ) (χ : ∀ i, DirichletCharacter ℂ (N i)) :
    ∃ (ω : ∀ q : ℕ, DirichletCharacter ℂ q) (k : ι → ℕ → ℕ),
      (∀ q : ℕ, q.Prime → orderOf (ω q) = q - 1) ∧
      (∀ (q : ℕ) [Fact q.Prime] (i : ι), pcomp q (χ i) = ω q ^ k i q) := by
  classical
  have hω : ∀ q : ℕ, ∃ ω : DirichletCharacter ℂ q, q.Prime →
      (orderOf ω = q - 1 ∧ ∀ φ : DirichletCharacter ℂ q, ∃ k : ℕ, φ = ω ^ k) := by
    intro q
    by_cases hq : q.Prime
    · have : Fact q.Prime := ⟨hq⟩
      obtain ⟨ω, h1, h2⟩ := exists_generator q
      exact ⟨ω, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hq⟩
  choose ω hω using hω
  have hk : ∀ (i : ι) (q : ℕ), ∃ k : ℕ, ∀ [Fact q.Prime], pcomp q (χ i) = ω q ^ k := by
    intro i q
    by_cases hq : q.Prime
    · have : Fact q.Prime := ⟨hq⟩
      obtain ⟨k, hk⟩ := (hω q hq).2 (pcomp q (χ i))
      refine ⟨k, ?_⟩
      intro _
      exact hk
    · refine ⟨0, ?_⟩
      intro h
      exact absurd h.out hq
  choose k hk using hk
  exact ⟨ω, k, fun q hq => (hω q hq).1, fun q _ i => hk i q⟩

end PAG.Part197

#print axioms PAG.Part197.family_regroup
#print axioms PAG.Part197.sep_family
#print axioms PAG.Part197.isIntegral_prod
#print axioms PAG.Part197.isIntegral_natAbs_zpow
#print axioms PAG.Part197.pow_two_zpow
#print axioms PAG.Part197.isIntegral_prod_zN
#print axioms PAG.Part197.pcomp_hall
#print axioms PAG.Part197.pow_dvd_iff_of_ne
#print axioms PAG.Part197.localProd_congr
#print axioms PAG.Part197.prod_root_iff_aux
#print axioms PAG.Part197.prod_root_iff_local
#print axioms PAG.Part197.local_root_iff
#print axioms PAG.Part197.prod_root_iff_stickelberger
#print axioms PAG.Part197.exists_stickelberger_data
