/-
  PAG 2.0 Part 185（2026-10-23）— 同じ素数の上の積：Stickelberger 型の付値による必要条件
  p は素数、χ は法 p の乗法的指標で n = ord χ、ψ は原始的な加法的指標、z_j = τ(χ^j)/√p（1 ≤ j ≤ n − 1）、
  ⟨x⟩ = x mod n。
  1. ヘンゼル：𝔽_p の 1 の原始 n 乗根は ℤ_p の 1 の原始 n 乗根に持ち上がる（exists_padic_root）
  2. 埋め込み：c が n と互いに素なら、ℤ[μ] → ℤ_p の環準同型 ι_c で、mod p で χ ↦ (x ↦ x^{kc})
     （k = (p − 1)/n、exists_padic_embedding）
  3. 付値：xy = p（ℤ_p）なら v(x) ∈ {0, 1}、v(x) = 1 ⇔ x ≡ 0 (mod p)。
     ℂ での整数冪の関係 ∏ (α_i/β_i)^{b_i} = 1 から付値の関係 Σ b_i (v(α_i) − v(β_i)) = 0（val_relation）
  4. v_c(J(χ, χ^i)) = 1 ⇔ ⟨c⟩ + ⟨ci⟩ < n（val_jacobi）。n·v_c(Q_j) = (j − 1)n − j⟨c⟩ + ⟨cj⟩（val_QA）
  5. W_j = z_j^{2n} は W_j·p^n·Q_j^{2n} = (pP)^{2j} をみたし（W_eq）、その付値は n − 2⟨cj⟩（val_diff）
  6. 主定理 same_prime_necessary：∏_j z_j^{a_j} が 1 の冪根なら、n と互いに素なすべての c で
     Σ_j a_j (n − 2⟨cj⟩) = 0
  7. 系：z(χ^j) が 1 の冪根 ⇔ 2j = n（single_power_root_iff）。位数 5 で z(χ)^a z(χ²)^b が 1 の冪根
     ⇔ a = b = 0（quintic_pair_root_iff）
-/
import PAG188
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

namespace PAG.Part189

open Complex Finset Polynomial
open PAG.Part185 (powChar)

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### 1. ヘンゼル：ℤ_p の 1 の冪根 -/

/-- toZMod x = 0 ⇔ ‖x‖ < 1。 -/
theorem toZMod_eq_zero_iff (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

theorem norm_eq_one_of_toZMod_ne_zero (x : ℤ_[p]) (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one x) (not_lt.mp fun h' => h ((toZMod_eq_zero_iff x).mpr h'))

/-- **1.** 𝔽_p の 1 の原始 n 乗根 y（n ≢ 0 mod p）は、ℤ_p の 1 の原始 n 乗根 z に持ち上がる。 -/
theorem exists_padic_root (n : ℕ) (hn : 0 < n) (hnp : (n : ZMod p) ≠ 0) (y : ZMod p)
    (hy : IsPrimitiveRoot y n) : ∃ z : ℤ_[p], IsPrimitiveRoot z n ∧ PadicInt.toZMod z = y := by
  set a : ℤ_[p] := ((y.val : ℕ) : ℤ_[p]) with ha
  have hay : PadicInt.toZMod a = y := by rw [ha, map_natCast, ZMod.natCast_zmod_val]
  have hy0 : y ≠ 0 := hy.ne_zero hn.ne'
  set F : Polynomial ℤ_[p] := X ^ n - 1 with hF
  have hFa : F.aeval a = a ^ n - 1 := by simp [hF]
  have hdF : (derivative F).aeval a = (n : ℤ_[p]) * a ^ (n - 1) := by simp [hF, derivative_X_pow]
  have h1 : ‖F.aeval a‖ < 1 := by
    rw [hFa, ← toZMod_eq_zero_iff, map_sub, map_pow, hay, map_one, hy.pow_eq_one, sub_self]
  have h2 : ‖(derivative F).aeval a‖ = 1 := by
    apply norm_eq_one_of_toZMod_ne_zero
    rw [hdF, map_mul, map_pow, hay, map_natCast]
    exact mul_ne_zero hnp (pow_ne_zero _ hy0)
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a) (by rw [h2, one_pow]; exact h1)
  rw [h2] at hza
  have hzy : PadicInt.toZMod z = y := by
    have h0 : PadicInt.toZMod (z - a) = 0 := (toZMod_eq_zero_iff _).mpr hza
    rwa [map_sub, sub_eq_zero, hay] at h0
  have hzn : z ^ n = 1 := by
    have : z ^ n - 1 = 0 := by simpa [hF] using hz
    exact sub_eq_zero.mp this
  refine ⟨z, ⟨hzn, fun l hl => hy.dvd_of_pow_eq_one l ?_⟩, hzy⟩
  rw [← hzy, ← map_pow, hl, map_one]

/-! ### 2. ℤ[μ] から ℤ_p への埋め込み -/

/-- **2.** c が n = ord χ と互いに素なら、部分環 A = ℤ[μ] ⊆ ℂ、A に値をもつ χ_A、環準同型 ι : A → ℤ_p が
  あって、χ_A を ℂ に戻すと χ、ι のあと mod p で見ると x ↦ x^{kc}（k = (p − 1)/n）。 -/
theorem exists_padic_embedding (χ : MulChar (ZMod p) ℂ) (c : ℕ) (hc : c.Coprime (orderOf χ)) :
    ∃ (A : Subalgebra ℤ ℂ) (χA : MulChar (ZMod p) A) (ι : A →+* ℤ_[p]),
      χA.ringHomComp A.val.toRingHom = χ ∧
        χA.ringHomComp (PadicInt.toZMod.comp ι) = powChar ((p - 1) / orderOf χ * c) := by
  obtain ⟨a, ha⟩ := PAG.Part185.exists_gen (p := p)
  have hμ := PAG.Part185.isPrimitiveRoot_gen χ a ha
  have hnpos : 0 < orderOf χ := PAG.Part185.orderOf_pos_chi χ
  have hdvd : orderOf χ ∣ p - 1 := PAG.Part185.orderOf_dvd_sub_one χ
  have h2 := hp.out.two_le
  have hkn : (p - 1) / orderOf χ * orderOf χ = p - 1 := Nat.div_mul_cancel hdvd
  have hkpos : 0 < (p - 1) / orderOf χ := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hnpos
  have hga : IsPrimitiveRoot ((a : ZMod p)) (p - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, ← PAG.Part185.orderOf_gen a ha]
    exact IsPrimitiveRoot.orderOf a
  have hg : IsPrimitiveRoot ((a : ZMod p) ^ ((p - 1) / orderOf χ)) (orderOf χ) := by
    have := hga.pow_of_dvd hkpos.ne' (Dvd.intro _ hkn)
    rwa [Nat.div_div_self hdvd (by omega)] at this
  have hgc : IsPrimitiveRoot ((a : ZMod p) ^ ((p - 1) / orderOf χ * c)) (orderOf χ) := by
    rw [pow_mul]; exact hg.pow_of_coprime c hc
  have hnp : ((orderOf χ : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
    have := Nat.le_of_dvd hnpos h; have := Nat.le_of_dvd (by omega) hdvd; omega
  obtain ⟨z, hz, hzy⟩ := exists_padic_root (orderOf χ) hnpos hnp _ hgc
  have hint : IsIntegral ℤ (χ a) := hμ.isIntegral hnpos
  obtain ⟨pb, hgen⟩ : ∃ pb : PowerBasis ℤ (Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ)),
      pb.gen = ⟨χ a, Algebra.subset_adjoin (Set.mem_singleton _)⟩ :=
    ⟨Algebra.adjoin.powerBasis' hint, Algebra.adjoin.powerBasis'_gen hint⟩
  have hmin : minpoly ℤ pb.gen = cyclotomic (orderOf χ) ℤ := by
    rw [hgen, ← minpoly.algHom_eq (Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ)).val Subtype.val_injective]
    exact (cyclotomic_eq_minpoly hμ hnpos).symm
  have hroot : aeval z (minpoly ℤ pb.gen) = 0 := by
    rw [hmin, aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hz.isRoot_cyclotomic hnpos
  obtain ⟨ι, hιg⟩ : ∃ ι : Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ) →ₐ[ℤ] ℤ_[p], ι pb.gen = z :=
    ⟨pb.lift _ hroot, pb.lift_gen _ hroot⟩
  refine ⟨_, PAG.Part185.chiA χ hμ, ι.toRingHom, MulChar.ext' (fun x => rfl),
    MulChar.ext (fun u => ?_)⟩
  obtain ⟨j, hj⟩ := ha u
  have hcj : PAG.Part185.chiA χ hμ (u : ZMod p) = pb.gen ^ j := by
    rw [hgen]
    apply Subtype.ext
    rw [PAG.Part185.chiA_apply, SubmonoidClass.coe_pow, ← hj, Units.val_pow_eq_pow_val, map_pow]
  have hlhs : PadicInt.toZMod (ι (pb.gen ^ j)) = ((a : ZMod p) ^ ((p - 1) / orderOf χ * c)) ^ j := by
    rw [map_pow, hιg, map_pow, hzy]
  rw [MulChar.ringHomComp_apply, RingHom.comp_apply, hcj]
  change PadicInt.toZMod (ι (pb.gen ^ j)) = _
  rw [hlhs, PAG.Part185.powChar, MulChar.ofUnitHom_coe, powMonoidHom_apply, ← hj,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, mul_comm]

/-! ### 3. 付値 -/

/-- **3a.** xy = p（ℤ_p）なら x ≠ 0、v(x) ≤ 1、v(x) = 1 ⇔ x ≡ 0 (mod p)。 -/
theorem val_of_mul_eq_p (x y : ℤ_[p]) (h : x * y = p) :
    x ≠ 0 ∧ x.valuation ≤ 1 ∧ (x.valuation = 1 ↔ PadicInt.toZMod x = 0) := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hx : x ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact hp0 h.symm
  have hy : y ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact hp0 h.symm
  have hv : x.valuation + y.valuation = 1 := by
    rw [← PadicInt.valuation_mul hx hy, h, PadicInt.valuation_p]
  refine ⟨hx, by omega, ?_⟩
  have key : PadicInt.toZMod x = 0 ↔ 1 ≤ x.valuation := by
    rw [toZMod_eq_zero_iff, PadicInt.norm_lt_one_iff_dvd,
      ← PadicInt.mem_span_pow_iff_le_valuation x hx, pow_one, Ideal.mem_span_singleton]
  rw [key]; omega

/-- 有限積の付値。 -/
theorem valuation_prod {κ : Type*} (s : Finset κ) (x y : κ → ℤ_[p]) (m m' : κ → ℕ)
    (hx : ∀ i ∈ s, x i ≠ 0) (hy : ∀ i ∈ s, y i ≠ 0) :
    (∏ i ∈ s, x i ^ m i * y i ^ m' i).valuation
      = ∑ i ∈ s, (m i * (x i).valuation + m' i * (y i).valuation) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hx' : ∀ i ∈ s, x i ≠ 0 := fun i hi => hx i (mem_insert_of_mem hi)
    have hy' : ∀ i ∈ s, y i ≠ 0 := fun i hi => hy i (mem_insert_of_mem hi)
    have hxj := hx j (mem_insert_self j s)
    have hyj := hy j (mem_insert_self j s)
    have hs0 : ∏ i ∈ s, x i ^ m i * y i ^ m' i ≠ 0 :=
      prod_ne_zero_iff.mpr fun i hi => mul_ne_zero (pow_ne_zero _ (hx' i hi)) (pow_ne_zero _ (hy' i hi))
    rw [prod_insert hj, sum_insert hj,
      PadicInt.valuation_mul (mul_ne_zero (pow_ne_zero _ hxj) (pow_ne_zero _ hyj)) hs0, ih hx' hy',
      PadicInt.valuation_mul (pow_ne_zero _ hxj) (pow_ne_zero _ hyj), PadicInt.valuation_pow,
      PadicInt.valuation_pow]

/-- **3b. 付値の関係**：A の元 α_i, β_i（ι で 0 にならない）について、ℂ で ∏ (α_i/β_i)^{b_i} = 1 なら
  Σ b_i (v(ι α_i) − v(ι β_i)) = 0。 -/
theorem val_relation {A : Subalgebra ℤ ℂ} (ι : A →+* ℤ_[p]) {κ : Type*} (s : Finset κ)
    (α β : κ → A) (b : κ → ℤ) (hα : ∀ i ∈ s, ι (α i) ≠ 0) (hβ : ∀ i ∈ s, ι (β i) ≠ 0)
    (h : ∏ i ∈ s, ((α i : ℂ) / (β i : ℂ)) ^ b i = 1) :
    ∑ i ∈ s, b i * (((ι (α i)).valuation : ℤ) - (ι (β i)).valuation) = 0 := by
  have hα' : ∀ i ∈ s, (α i : ℂ) ≠ 0 := fun i hi h0 => hα i hi (by
    rw [show α i = 0 from Subtype.ext h0, map_zero])
  have hβ' : ∀ i ∈ s, (β i : ℂ) ≠ 0 := fun i hi h0 => hβ i hi (by
    rw [show β i = 0 from Subtype.ext h0, map_zero])
  simp only [PAG.Part186.zpow_div_split] at h
  rw [prod_div_distrib, div_eq_one_iff_eq (prod_ne_zero_iff.mpr fun i hi =>
    mul_ne_zero (pow_ne_zero _ (hα' i hi)) (pow_ne_zero _ (hβ' i hi)))] at h
  have hA : ∏ i ∈ s, (α i ^ (b i).toNat * β i ^ (-b i).toNat)
      = ∏ i ∈ s, (α i ^ (-b i).toNat * β i ^ (b i).toNat) := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_finsetProd, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    exact h
  have hZ := congrArg ι hA
  simp only [map_prod, map_mul, map_pow] at hZ
  have hv := congrArg PadicInt.valuation hZ
  rw [valuation_prod s _ _ _ _ hα hβ, valuation_prod s _ _ _ _ hα hβ] at hv
  have hv' : (∑ i ∈ s, (((b i).toNat * (ι (α i)).valuation + (-b i).toNat * (ι (β i)).valuation : ℕ) : ℤ))
      = ∑ i ∈ s, (((-b i).toNat * (ι (α i)).valuation + (b i).toNat * (ι (β i)).valuation : ℕ) : ℤ) := by
    exact_mod_cast hv
  rw [← sub_eq_zero, ← sum_sub_distrib] at hv'
  rw [← hv']
  refine sum_congr rfl (fun i _ => ?_)
  have hb : ((b i).toNat : ℤ) - ((-b i).toNat : ℤ) = b i := Int.toNat_sub_toNat_neg (b i)
  push_cast
  linear_combination (-(((ι (α i)).valuation : ℤ) - (ι (β i)).valuation)) * hb

/-! ### 4. ヤコビ和の付値 -/

omit hp in
/-- n と互いに素な c と 0 < x < n について、cx mod n ≠ 0。 -/
theorem mul_mod_ne_zero (c n x : ℕ) (hc : c.Coprime n) (hx0 : 0 < x) (hxn : x < n) : c * x % n ≠ 0 := by
  intro h
  have hdvd : n ∣ c * x := Nat.dvd_of_mod_eq_zero h
  have : n ∣ x := (Nat.Coprime.symm hc).dvd_of_dvd_mul_left hdvd
  exact absurd (Nat.le_of_dvd hx0 this) (by omega)

omit hp in
/-- (x + y) mod n の 2 通り。 -/
theorem add_mod_cases (n x y : ℕ) (hn : 0 < n) :
    ((x + y) % n = x % n + y % n ∧ x % n + y % n < n) ∨
      ((x + y) % n + n = x % n + y % n ∧ n ≤ x % n + y % n) := by
  have h := Nat.add_mod x y n
  have hx := Nat.mod_lt x hn
  have hy := Nat.mod_lt y hn
  by_cases hlt : x % n + y % n < n
  · left; rw [h, Nat.mod_eq_of_lt hlt]; exact ⟨rfl, hlt⟩
  · right
    have e : (x % n + y % n) % n = x % n + y % n - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h, e]; omega

/-- powChar の指数は p − 1 を法として見てよい。 -/
theorem powChar_mod (m : ℕ) : powChar (p := p) m = powChar (m % (p - 1)) := by
  refine MulChar.ext (fun u => ?_)
  simp only [PAG.Part185.powChar, MulChar.ofUnitHom_coe, powMonoidHom_apply]
  congr 1
  conv_lhs => rw [← Nat.div_add_mod m (p - 1), pow_add, pow_mul, ZMod.units_pow_card_sub_one_eq_one,
    one_pow, one_mul]

section Embedding

variable {χ : MulChar (ZMod p) ℂ} {c : ℕ} {A : Subalgebra ℤ ℂ} {χA : MulChar (ZMod p) A}
  {ι : A →+* ℤ_[p]}

/-- ヤコビ和の対：1 ≤ i ≤ n − 2 で J(χ_A, χ_A^i)·J(χ_A^{n−1}, χ_A^{n−i}) = p（A で）。 -/
theorem jacobi_pair (hval : χA.ringHomComp A.val.toRingHom = χ) (i : ℕ) (hi1 : 1 ≤ i)
    (hi2 : i + 2 ≤ orderOf χ) :
    jacobiSum χA (χA ^ i) * jacobiSum (χA ^ (orderOf χ - 1)) (χA ^ (orderOf χ - i)) = (p : A) := by
  have hpow : ∀ l, 0 < l → l < orderOf χ → χ ^ l ≠ 1 :=
    fun l hl hln => pow_ne_one_of_lt_orderOf hl.ne' hln
  have hχ1 : χ ≠ 1 := by simpa using hpow 1 (by omega) (by omega)
  have hC := jacobiSum_mul_jacobiSum_inv PAG.Part185.ringChar_ne hχ1 (hpow i (by omega) (by omega))
    (by rw [← pow_succ']; exact hpow (i + 1) (by omega) (by omega))
  have h1 := PAG.Part185.inv_pow_eq χ 1 (by omega)
  rw [pow_one] at h1
  rw [h1, PAG.Part185.inv_pow_eq χ i (by omega), ZMod.card] at hC
  apply Subtype.ext
  have e1 := PAG.Part185.jacobi_val hval 1 i
  have e2 := PAG.Part185.jacobi_val hval (orderOf χ - 1) (orderOf χ - i)
  rw [pow_one, pow_one] at e1
  rw [MulMemClass.coe_mul, ← e1, ← e2, hC]
  simp

variable (hval : χA.ringHomComp A.val.toRingHom = χ)
  (hev : χA.ringHomComp (PadicInt.toZMod.comp ι) = powChar ((p - 1) / orderOf χ * c))
include hval hev

/-- **4a.** c が n と互いに素、1 ≤ i ≤ n − 2 なら、ι J(χ_A, χ_A^i) ≠ 0 で、その付値は
  ⟨c⟩ + ⟨ci⟩ < n なら 1、そうでなければ 0。 -/
theorem val_jacobi (hc : c.Coprime (orderOf χ)) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i + 2 ≤ orderOf χ) :
    ι (jacobiSum χA (χA ^ i)) ≠ 0 ∧
      (ι (jacobiSum χA (χA ^ i))).valuation
        = if c % orderOf χ + c * i % orderOf χ < orderOf χ then 1 else 0 := by
  set n := orderOf χ with hn
  have hnpos : 0 < n := PAG.Part185.orderOf_pos_chi χ
  have hdvd : n ∣ p - 1 := PAG.Part185.orderOf_dvd_sub_one χ
  set k := (p - 1) / n with hk
  have hkn : k * n = p - 1 := Nat.div_mul_cancel hdvd
  have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd (by have := hp.out.two_le; omega) hdvd) hnpos
  have hpair := congrArg ι (jacobi_pair hval i hi1 hi2)
  rw [map_mul, map_natCast] at hpair
  obtain ⟨h0, hle, hiff⟩ := val_of_mul_eq_p _ _ hpair
  refine ⟨h0, ?_⟩
  -- mod p での値
  have hJ : PadicInt.toZMod (ι (jacobiSum χA (χA ^ i)))
      = jacobiSum (powChar (p := p) (k * (c % n))) (powChar (k * (c * i % n))) := by
    have := PAG.Part185.jacobi_ev hev 1 i
    rw [pow_one] at this
    rw [← RingHom.comp_apply, this, powChar_mod (k * c * 1), powChar_mod (k * c * i), ← hkn,
      mul_one, Nat.mul_mod_mul_left, mul_assoc, Nat.mul_mod_mul_left]
  have hr1 : c % n ≠ 0 := by
    have := mul_mod_ne_zero c n 1 hc one_pos (by omega); rwa [mul_one] at this
  have hr2 : c * i % n ≠ 0 := mul_mod_ne_zero c n i hc (by omega) (by omega)
  have hr1' := Nat.mod_lt c hnpos
  have hr2' := Nat.mod_lt (c * i) hnpos
  have hu : 0 < k * (c % n) := Nat.mul_pos hkpos (Nat.pos_of_ne_zero hr1)
  have hv : 0 < k * (c * i % n) := Nat.mul_pos hkpos (Nat.pos_of_ne_zero hr2)
  have hu' : k * (c % n) < p - 1 := by rw [← hkn]; exact Nat.mul_lt_mul_of_pos_left hr1' hkpos
  have hv' : k * (c * i % n) < p - 1 := by rw [← hkn]; exact Nat.mul_lt_mul_of_pos_left hr2' hkpos
  by_cases hlt : c % n + c * i % n < n
  · rw [ite_eq_left hlt]
    apply hiff.mpr
    rw [hJ]
    apply PAG.Part185.jacobi_powChar_eq_zero _ _ hu hv
    rw [← hkn, ← mul_add]
    exact Nat.mul_lt_mul_of_pos_left hlt hkpos
  · rw [ite_eq_right hlt]
    have hne : PadicInt.toZMod (ι (jacobiSum χA (χA ^ i))) ≠ 0 := by
      rw [hJ]
      apply PAG.Part185.jacobi_powChar_ne_zero _ _ hu hv hu' hv'
      rw [← hkn, ← mul_add]
      exact Nat.mul_le_mul_left k (by omega)
    have : (ι (jacobiSum χA (χA ^ i))).valuation ≠ 1 := fun h1 => hne (hiff.mp h1)
    omega

/-- **4b.** Q_j = ∏_{i=1}^{j−1} J(χ_A, χ_A^i)（1 ≤ j ≤ n − 1）について、ι Q_j ≠ 0 で
  n·v(ι Q_j) = (j − 1)n − j⟨c⟩ + ⟨cj⟩。 -/
theorem val_QA (hc : c.Coprime (orderOf χ)) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j + 1 ≤ orderOf χ) :
    ι (∏ i ∈ Ico 1 j, jacobiSum χA (χA ^ i)) ≠ 0 ∧
      (orderOf χ : ℤ) * (ι (∏ i ∈ Ico 1 j, jacobiSum χA (χA ^ i))).valuation
        = ((j : ℤ) - 1) * orderOf χ - j * ((c % orderOf χ : ℕ) : ℤ)
          + ((c * j % orderOf χ : ℕ) : ℤ) := by
  have hnpos : 0 < orderOf χ := PAG.Part185.orderOf_pos_chi χ
  induction j, hj1 using Nat.le_induction with
  | base =>
    rw [Ico_self, prod_empty, map_one, PadicInt.valuation_one, mul_one]
    refine ⟨one_ne_zero, ?_⟩
    push_cast; ring
  | succ j hj ih =>
    obtain ⟨ih0, ihv⟩ := ih (by omega)
    obtain ⟨hJ0, hJv⟩ := val_jacobi hval hev hc j hj (by omega)
    rw [prod_Ico_succ_top hj, map_mul]
    refine ⟨mul_ne_zero ih0 hJ0, ?_⟩
    rw [PadicInt.valuation_mul ih0 hJ0, Nat.cast_add, mul_add, ihv, hJv]
    have hcases := add_mod_cases (orderOf χ) (c * j) c hnpos
    rw [show c * (j + 1) = c * j + c by ring]
    set n := orderOf χ
    set r1 := c % n
    set rj := c * j % n
    set rj1 := (c * j + c) % n
    by_cases hlt : r1 + rj < n
    · rw [ite_eq_left hlt]
      rcases hcases with ⟨h1, _⟩ | ⟨_, h2⟩
      · have : (rj1 : ℤ) = rj + r1 := by exact_mod_cast h1
        push_cast; rw [this]; ring
      · omega
    · rw [ite_eq_right (by omega)]
      rcases hcases with ⟨_, h2⟩ | ⟨h1, _⟩
      · omega
      · have : (rj1 : ℤ) + n = rj + r1 := by exact_mod_cast h1
        push_cast; linear_combination (-1 : ℤ) * this

/-- **4c.** P = ∏_{i=1}^{n−2} J(χ_A, χ_A^i)（n ≥ 2）について、ι P ≠ 0 で v(ι P) = n − 1 − ⟨c⟩。 -/
theorem val_PA (hc : c.Coprime (orderOf χ)) (hn : 2 ≤ orderOf χ) :
    ι (∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum χA (χA ^ i)) ≠ 0 ∧
      ((ι (∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum χA (χA ^ i))).valuation : ℤ)
        = orderOf χ - 1 - ((c % orderOf χ : ℕ) : ℤ) := by
  have hnpos : 0 < orderOf χ := PAG.Part185.orderOf_pos_chi χ
  obtain ⟨h0, hv⟩ := val_QA hval hev hc (orderOf χ - 1) (by omega) (by omega)
  refine ⟨h0, ?_⟩
  -- ⟨c(n − 1)⟩ + ⟨c⟩ = n
  have hsum : c * (orderOf χ - 1) % orderOf χ + c % orderOf χ = orderOf χ := by
    have hz : (c * (orderOf χ - 1) + c) % orderOf χ = 0 := by
      rw [show c * (orderOf χ - 1) + c = c * orderOf χ by
        rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right c hnpos)]]
      exact Nat.mul_mod_left c (orderOf χ)
    have hr1 : c % orderOf χ ≠ 0 := by
      have := mul_mod_ne_zero c (orderOf χ) 1 hc one_pos (by omega); rwa [mul_one] at this
    rcases add_mod_cases (orderOf χ) (c * (orderOf χ - 1)) c hnpos with ⟨h1, _⟩ | ⟨h1, _⟩
    · omega
    · omega
  have hsumZ : ((c * (orderOf χ - 1) % orderOf χ : ℕ) : ℤ) = orderOf χ - ((c % orderOf χ : ℕ) : ℤ) := by
    have : ((c * (orderOf χ - 1) % orderOf χ : ℕ) : ℤ) + ((c % orderOf χ : ℕ) : ℤ) = orderOf χ := by
      exact_mod_cast hsum
    linarith
  rw [hsumZ, Nat.cast_sub (by omega : 1 ≤ orderOf χ)] at hv
  have hn0 : (orderOf χ : ℤ) ≠ 0 := by exact_mod_cast hnpos.ne'
  apply mul_left_cancel₀ hn0
  rw [hv]; push_cast; ring

end Embedding

/-! ### 5. W_j = z_j^{2n} -/

/-- **5a.** 1 ≤ j < n：(τ(χ^j)/√p)^{2n} · (p^n · Q_j^{2n}) = (p·P)^{2j}（ℂ）。 -/
theorem W_eq (χ : MulChar (ZMod p) ℂ) (hn : 2 ≤ orderOf χ) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j < orderOf χ) :
    (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * orderOf χ) *
        ((p : ℂ) ^ orderOf χ * (∏ i ∈ Ico 1 j, jacobiSum χ (χ ^ i)) ^ (2 * orderOf χ))
      = ((p : ℂ) * PAG.Part185.Pj χ) ^ (2 * j) := by
  have hsq : ((Real.sqrt p : ℝ) : ℂ) ^ (2 * orderOf χ) = (p : ℂ) ^ orderOf χ := by
    rw [pow_mul, PAG.Part185.sqrt_sq_cast]
  have hpn : (p : ℂ) ^ orderOf χ ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have haux := gaussSum_pow_eq_prod_jacobiSum_aux χ ψ hj1 hjn
  have hT := PAG.Part185.gauss_pow_order χ hn hψ
  have hm1 : χ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  rw [div_pow, hsq]
  calc gaussSum (χ ^ j) ψ ^ (2 * orderOf χ) / (p : ℂ) ^ orderOf χ *
        ((p : ℂ) ^ orderOf χ * (∏ i ∈ Ico 1 j, jacobiSum χ (χ ^ i)) ^ (2 * orderOf χ))
      = (gaussSum (χ ^ j) ψ * ∏ i ∈ Ico 1 j, jacobiSum χ (χ ^ i)) ^ (2 * orderOf χ) := by
        field_simp; ring
    _ = (gaussSum χ ψ ^ orderOf χ) ^ (2 * j) := by
        rw [← haux, ← pow_mul, ← pow_mul]; congr 1; ring
    _ = (χ (-1) ^ 2) ^ j * ((p : ℂ) * PAG.Part185.Pj χ) ^ (2 * j) := by rw [hT]; ring
    _ = ((p : ℂ) * PAG.Part185.Pj χ) ^ (2 * j) := by rw [hm1, one_pow, one_mul]

/-! ### 6. 主定理 -/

/-- **6. 主定理（必要条件）**：∏_{j=1}^{n−1} z_j^{a_j} が 1 の冪根なら、n と互いに素なすべての c で
  Σ_j a_j (n − 2⟨cj⟩) = 0（z_j = τ(χ^j)/√p、⟨x⟩ = x mod n）。 -/
theorem same_prime_necessary (χ : MulChar (ZMod p) ℂ) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (a : ℕ → ℤ) (N : ℕ) (hN : 0 < N)
    (h : (∏ j ∈ Ico 1 (orderOf χ), (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a j) ^ N = 1)
    (c : ℕ) (hc : c.Coprime (orderOf χ)) :
    ∑ j ∈ Ico 1 (orderOf χ), a j * ((orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ)) = 0 := by
  rcases Nat.lt_or_ge (orderOf χ) 2 with hn | hn
  · rw [Ico_eq_empty_of_le (by omega), sum_empty]
  obtain ⟨A, χA, ι, hval, hev⟩ := exists_padic_embedding χ c hc
  have hnpos : 0 < orderOf χ := by omega
  -- A の元
  set PA : A := ∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum χA (χA ^ i) with hPA
  set α : ℕ → A := fun j => ((p : A) * PA) ^ (2 * j) with hα
  set β : ℕ → A := fun j => (p : A) ^ orderOf χ * (∏ i ∈ Ico 1 j, jacobiSum χA (χA ^ i)) ^ (2 * orderOf χ)
    with hβ
  have hJ : ∀ i, ((jacobiSum χA (χA ^ i) : A) : ℂ) = jacobiSum χ (χ ^ i) := by
    intro i
    have := PAG.Part185.jacobi_val hval 1 i
    rw [pow_one, pow_one] at this
    exact this.symm
  have hαC : ∀ j, ((α j : A) : ℂ) = ((p : ℂ) * PAG.Part185.Pj χ) ^ (2 * j) := by
    intro j
    simp only [hα, hPA, SubmonoidClass.coe_pow, MulMemClass.coe_mul, SubmonoidClass.coe_finsetProd,
      hJ, PAG.Part185.Pj]
    simp
  have hβC : ∀ j, ((β j : A) : ℂ)
      = (p : ℂ) ^ orderOf χ * (∏ i ∈ Ico 1 j, jacobiSum χ (χ ^ i)) ^ (2 * orderOf χ) := by
    intro j
    simp only [hβ, SubmonoidClass.coe_pow, MulMemClass.coe_mul, SubmonoidClass.coe_finsetProd, hJ]
    simp
  -- 付値の計算
  obtain ⟨hP0, hPv⟩ := val_PA hval hev hc hn
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hα0 : ∀ j ∈ Ico 1 (orderOf χ), ι (α j) ≠ 0 := by
    intro j _
    simp only [hα, map_pow, map_mul, map_natCast]
    exact pow_ne_zero _ (mul_ne_zero hp0 hP0)
  have hβ0 : ∀ j ∈ Ico 1 (orderOf χ), ι (β j) ≠ 0 := by
    intro j hj
    rw [mem_Ico] at hj
    obtain ⟨hQ0, -⟩ := val_QA hval hev hc j hj.1 (by omega)
    simp only [hβ, map_pow, map_mul, map_natCast]
    exact mul_ne_zero (pow_ne_zero _ hp0) (pow_ne_zero _ hQ0)
  have hdiff : ∀ j ∈ Ico 1 (orderOf χ),
      ((ι (α j)).valuation : ℤ) - (ι (β j)).valuation
        = (orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ) := by
    intro j hj
    rw [mem_Ico] at hj
    obtain ⟨hQ0, hQv⟩ := val_QA hval hev hc j hj.1 (by omega)
    have ea : (ι (α j)).valuation = 2 * j * (1 + (ι PA).valuation) := by
      simp only [hα, map_pow, map_mul, map_natCast]
      rw [PadicInt.valuation_pow, PadicInt.valuation_mul hp0 hP0, PadicInt.valuation_p]
    have eb : (ι (β j)).valuation
        = orderOf χ + 2 * orderOf χ * (ι (∏ i ∈ Ico 1 j, jacobiSum χA (χA ^ i))).valuation := by
      simp only [hβ, map_pow, map_mul, map_natCast]
      rw [PadicInt.valuation_mul (pow_ne_zero _ hp0) (pow_ne_zero _ hQ0), PadicInt.valuation_pow,
        PadicInt.valuation_pow, PadicInt.valuation_p, mul_one]
    rw [ea, eb]
    push_cast
    rw [hPv]
    push_cast at hQv ⊢
    linear_combination (-2 : ℤ) * hQv
  -- 関係式
  have hrel : ∏ j ∈ Ico 1 (orderOf χ), ((α j : ℂ) / (β j : ℂ)) ^ (a j * N) = 1 := by
    have e1 : ∀ j ∈ Ico 1 (orderOf χ), ((α j : ℂ) / (β j : ℂ)) ^ (a j * N)
        = ((gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a j) ^ (N * (2 * orderOf χ)) := by
      intro j hj
      rw [mem_Ico] at hj
      have hβne : (β j : ℂ) ≠ 0 := fun h0 => hβ0 j (mem_Ico.mpr hj) (by
        rw [show β j = 0 from Subtype.ext h0, map_zero])
      have hW : (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * orderOf χ)
          = (α j : ℂ) / (β j : ℂ) := by
        rw [eq_div_iff hβne, hαC, hβC]
        exact W_eq χ hn hψ j hj.1 hj.2
      rw [← hW, ← zpow_natCast _ (2 * orderOf χ), ← zpow_mul, ← zpow_natCast _ (N * (2 * orderOf χ)),
        ← zpow_mul]
      congr 1
      push_cast; ring
    rw [prod_congr rfl e1, prod_pow, pow_mul, h, one_pow]
  have hv := val_relation ι (Ico 1 (orderOf χ)) α β (fun j => a j * N) hα0 hβ0 hrel
  rw [sum_congr rfl (fun j hj => by rw [hdiff j hj])] at hv
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have : (N : ℤ) * ∑ j ∈ Ico 1 (orderOf χ), a j * ((orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ))
      = 0 := by
    rw [mul_sum, ← hv]
    refine sum_congr rfl (fun j _ => ?_)
    ring
  exact (mul_eq_zero.mp this).resolve_left hN'

/-! ### 7. 系 -/

/-- **7a.** 1 ≤ j < n：z(χ^j) が 1 の冪根 ⇔ 2j = n（主定理の c = 1 と Part 181 の位数 2 の場合）。 -/
theorem single_power_root_iff (χ : MulChar (ZMod p) ℂ) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j < orderOf χ) :
    (∃ N : ℕ, 0 < N ∧ (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ N = 1) ↔ 2 * j = orderOf χ := by
  constructor
  · rintro ⟨N, hN, hz⟩
    have hprod : (∏ i ∈ Ico 1 (orderOf χ), (gaussSum (χ ^ i) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^
        (if i = j then (1 : ℤ) else 0)) ^ N = 1 := by
      rw [prod_eq_single j (fun i _ hij => by rw [ite_eq_right hij, zpow_zero])
        (fun hj' => absurd (mem_Ico.mpr ⟨hj1, hjn⟩) hj'), ite_eq_left rfl, zpow_one, hz]
    have h1 := same_prime_necessary χ hψ (fun i => if i = j then (1 : ℤ) else 0) N hN hprod 1
      (Nat.coprime_one_left _)
    rw [sum_eq_single j (fun i _ hij => by rw [ite_eq_right hij, zero_mul])
      (fun hj' => absurd (mem_Ico.mpr ⟨hj1, hjn⟩) hj'), ite_eq_left rfl, one_mul, one_mul,
      Nat.mod_eq_of_lt hjn] at h1
    omega
  · intro h2
    -- χ^j の位数は 2
    have hord : orderOf (χ ^ j) = 2 := by
      rw [orderOf_pow' χ (show j ≠ 0 by omega), ← h2, Nat.gcd_mul_left_left,
        Nat.mul_div_cancel _ (by omega)]
    exact (PAG.Part185.gauss_root_iff (χ ^ j) hψ).mpr hord

/-- **7b.** 位数 5：z(χ)^a z(χ²)^b が 1 の冪根 ⇔ a = b = 0（主定理の c = 1, 2 から 3a + b = 0、a − 3b = 0）。 -/
theorem quintic_pair_root_iff (χ : MulChar (ZMod p) ℂ) (h5 : orderOf χ = 5) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) (a b : ℤ) :
    (∃ N : ℕ, 0 < N ∧ ((gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a *
      (gaussSum (χ ^ 2) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ b) ^ N = 1) ↔ a = 0 ∧ b = 0 := by
  constructor
  · rintro ⟨N, hN, h⟩
    set e : ℕ → ℤ := fun j => if j = 1 then a else if j = 2 then b else 0 with he
    have hI : Ico 1 5 = ({1, 2, 3, 4} : Finset ℕ) := by decide
    have hprod : (∏ j ∈ Ico 1 (orderOf χ), (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ e j) ^ N
        = 1 := by
      rw [h5, hI]
      simpa [he] using h
    have h1 := same_prime_necessary χ hψ e N hN hprod 1 (by rw [h5]; norm_num)
    have h2 := same_prime_necessary χ hψ e N hN hprod 2 (by rw [h5]; norm_num)
    rw [h5, hI] at h1 h2
    simp [he] at h1 h2
    omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, one_pos, by simp⟩

/-- **7c.** 鎖の記号（PAG184 の zOf）での主定理。 -/
theorem same_prime_necessary_chain (χ : DirichletCharacter ℂ p) (a : ℕ → ℤ) (N : ℕ) (hN : 0 < N)
    (h : (∏ j ∈ Ico 1 (orderOf χ), PAG.Part184.zOf (χ ^ j) ^ a j) ^ N = 1) (c : ℕ)
    (hc : c.Coprime (orderOf χ)) :
    ∑ j ∈ Ico 1 (orderOf χ), a j * ((orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ)) = 0 :=
  same_prime_necessary χ (ZMod.isPrimitive_stdAddChar p) a N hN h c hc

end PAG.Part189

#print axioms PAG.Part189.toZMod_eq_zero_iff
#print axioms PAG.Part189.norm_eq_one_of_toZMod_ne_zero
#print axioms PAG.Part189.exists_padic_root
#print axioms PAG.Part189.exists_padic_embedding
#print axioms PAG.Part189.val_of_mul_eq_p
#print axioms PAG.Part189.valuation_prod
#print axioms PAG.Part189.val_relation
#print axioms PAG.Part189.mul_mod_ne_zero
#print axioms PAG.Part189.add_mod_cases
#print axioms PAG.Part189.powChar_mod
#print axioms PAG.Part189.jacobi_pair
#print axioms PAG.Part189.val_jacobi
#print axioms PAG.Part189.val_QA
#print axioms PAG.Part189.val_PA
#print axioms PAG.Part189.W_eq
#print axioms PAG.Part189.same_prime_necessary
#print axioms PAG.Part189.single_power_root_iff
#print axioms PAG.Part189.quintic_pair_root_iff
#print axioms PAG.Part189.same_prime_necessary_chain
