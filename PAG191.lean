/-
  PAG 2.0 Part 187（2026-10-23）— 素数をまたぐ積：素数ごとに分かれることと、全体の完全な判定
  相異なる素数 q_i、法 q_i の指標 χ_i（位数 n_i）、指数 a_i : ℕ → ℤ について
  X_i = ∏_{j=1}^{n_i−1} z(χ_i^j)^{a_i(j)}、S_c(a_i) = Σ_j a_i(j)(n_i − 2⟨cj⟩)。
  1. val_le_of_isIntegral：ℤ[μ] の元 U, V で U/V が代数的整数なら、ℤ_p への ι で v(ι V) ≤ v(ι U)
     （ℚ_p で t = ιU/ιV が整数係数のモニック多項式の根になり、ℤ_p が整閉なので t ∈ ℤ_p）
  2. isIntegral_of_coprime：a z、b z が代数的整数で a, b が互いに素なら z も代数的整数（ベズー）
  3. exists_UV：各素数で Y = X^{2n} = U/V、p^M Y^{±1} が代数的整数、v(ιU) − v(ιV) = S_c
  4. separate_core：∏ Y_i^{e_i} = 1 なら Y_{i₀}^{e_{i₀}} とその逆数は代数的整数
  5. multi_same_root_iff：∏_i X_i が 1 の冪根 ⇔ すべての i と c で S_c(a_i) = 0
     multi_same_root_iff_each：⇔ すべての X_i が 1 の冪根
  6. full_root_iff：さらに導手 p^k（k ≥ 2）の原始指標の z の整数冪を掛けても判定は変わらない
-/
import PAG190

namespace PAG.Part191

open Complex Finset Polynomial
open PAG.Part185 (powChar)

/-! ### 1. 代数的整数と ℤ_p の付値 -/

section Val

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1.** A ⊆ ℂ の元 U, V（ι U, ι V ≠ 0）で U/V が代数的整数なら、v(ι V) ≤ v(ι U)。 -/
theorem val_le_of_isIntegral {A : Subalgebra ℤ ℂ} (ι : A →+* ℤ_[p]) (U V : A) (hU : ι U ≠ 0)
    (hV : ι V ≠ 0) (h : IsIntegral ℤ ((U : ℂ) / (V : ℂ))) : (ι V).valuation ≤ (ι U).valuation := by
  obtain ⟨f, hfm, hf⟩ := h
  set d := f.natDegree with hd
  have hV0 : (V : ℂ) ≠ 0 := fun h0 => hV (by rw [show V = 0 from Subtype.ext h0, map_zero])
  -- ℂ で Σ f_i U^i V^{d−i} = 0、したがって A でも 0
  have hA : (∑ i ∈ range (d + 1), f.coeff i • (U ^ i * V ^ (d - i)) : A) = 0 := by
    apply Subtype.ext
    have h1 : aeval ((U : ℂ) / (V : ℂ)) f = 0 := by rw [aeval_def]; exact hf
    rw [aeval_eq_sum_range, ← hd] at h1
    rw [ZeroMemClass.coe_zero]
    have h2 : (V : ℂ) ^ d * ∑ i ∈ range (d + 1), f.coeff i • ((U : ℂ) / (V : ℂ)) ^ i = 0 := by
      rw [h1, mul_zero]
    rw [← h2, mul_sum]
    simp only [AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_zsmul, MulMemClass.coe_mul,
      SubmonoidClass.coe_pow]
    refine sum_congr rfl (fun i hi => ?_)
    rw [mem_range] at hi
    have hVd : (V : ℂ) ^ d = (V : ℂ) ^ (d - i) * (V : ℂ) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [hVd, zsmul_eq_mul, zsmul_eq_mul, div_pow]
    field_simp
  -- ℤ_p に送る
  have hZ := congrArg ι hA
  rw [map_sum, map_zero] at hZ
  simp only [map_zsmul, map_mul, map_pow] at hZ
  -- ℚ_p で t = ι U / ι V
  set x := ι U with hx
  set y := ι V with hy
  have hy' : algebraMap ℤ_[p] ℚ_[p] y ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])]
  set t : ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] x / algebraMap ℤ_[p] ℚ_[p] y with ht
  have hroot : aeval t f = 0 := by
    rw [aeval_eq_sum_range]
    have hZ' := congrArg (algebraMap ℤ_[p] ℚ_[p]) hZ
    rw [map_sum, map_zero] at hZ'
    simp only [map_zsmul, map_mul, map_pow] at hZ'
    have h3 : (algebraMap ℤ_[p] ℚ_[p] y) ^ d * ∑ i ∈ range (d + 1), f.coeff i • t ^ i = 0 := by
      rw [← hZ', mul_sum]
      refine sum_congr rfl (fun i hi => ?_)
      rw [mem_range] at hi
      have hyd : (algebraMap ℤ_[p] ℚ_[p] y) ^ d
          = (algebraMap ℤ_[p] ℚ_[p] y) ^ (d - i) * (algebraMap ℤ_[p] ℚ_[p] y) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      rw [hyd, ht, zsmul_eq_mul, zsmul_eq_mul, div_pow]
      field_simp
    exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero _ hy')
  have hint : IsIntegral ℤ t := ⟨f, hfm, by rw [← aeval_def]; exact hroot⟩
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hint.tower_top (A := ℤ_[p]))
  have hsy : s * y = x := by
    apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    rw [map_mul, hs, ht, div_mul_cancel₀ _ hy']
  have hs0 : s ≠ 0 := by rintro rfl; rw [zero_mul] at hsy; exact hU hsy.symm
  rw [← hsy, PadicInt.valuation_mul hs0 hV]
  omega

end Val

/-! ### 2. ベズー -/

/-- **2.** m₁ z と m₂ z が代数的整数で m₁, m₂ ∈ ℤ が互いに素なら、z も代数的整数。 -/
theorem isIntegral_of_coprime (z : ℂ) (m₁ m₂ : ℤ) (hcop : IsCoprime m₁ m₂)
    (h₁ : IsIntegral ℤ ((m₁ : ℂ) * z)) (h₂ : IsIntegral ℤ ((m₂ : ℂ) * z)) : IsIntegral ℤ z := by
  obtain ⟨u, v, huv⟩ := hcop
  have hz : z = (u : ℂ) * ((m₁ : ℂ) * z) + (v : ℂ) * ((m₂ : ℂ) * z) := by
    have : ((u * m₁ + v * m₂ : ℤ) : ℂ) = 1 := by rw [huv]; simp
    push_cast at this
    linear_combination (-z) * this
  have hu : IsIntegral ℤ ((u : ℂ)) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := u)
  have hv : IsIntegral ℤ ((v : ℂ)) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := v)
  rw [hz]
  exact (hu.mul h₁).add (hv.mul h₂)

/-! ### 3. 各素数の部分 -/

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- **3.** 各素数の部分 X = ∏ z_j^{a_j}（n ≥ 2）について：部分環 A ⊆ 代数的整数、U, V ∈ A、M があって
  X^{2n} = U/V、p^M·(U/V) と p^M·(V/U) は代数的整数、U, V ≠ 0、そして n と互いに素な c ごとに
  ι : A → ℤ_p で v(ι U) − v(ι V) = S_c(a)。 -/
theorem exists_UV (χ : MulChar (ZMod p) ℂ) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (hn : 2 ≤ orderOf χ) (a : ℕ → ℤ) :
    ∃ (A : Subalgebra ℤ ℂ) (U V : A) (M : ℕ),
      (∏ j ∈ Ico 1 (orderOf χ), (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a j) ^ (2 * orderOf χ)
        = (U : ℂ) / (V : ℂ) ∧
      IsIntegral ℤ ((p : ℂ) ^ M * ((U : ℂ) / (V : ℂ))) ∧
      IsIntegral ℤ ((p : ℂ) ^ M * ((V : ℂ) / (U : ℂ))) ∧ (U : ℂ) ≠ 0 ∧ (V : ℂ) ≠ 0 ∧
      ∀ c : ℕ, c.Coprime (orderOf χ) → ∃ ι : A →+* ℤ_[p], ι U ≠ 0 ∧ ι V ≠ 0 ∧
        ((ι U).valuation : ℤ) - (ι V).valuation
          = ∑ j ∈ Ico 1 (orderOf χ), a j * ((orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ)) := by
  have hnpos : 0 < orderOf χ := by omega
  obtain ⟨g, hg⟩ := PAG.Part185.exists_gen (p := p)
  have hμ := PAG.Part185.isPrimitiveRoot_gen χ g hg
  have hint : IsIntegral ℤ (χ g) := hμ.isIntegral hnpos
  obtain ⟨pb, hgen⟩ : ∃ pb : PowerBasis ℤ (Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)),
      pb.gen = ⟨χ g, Algebra.subset_adjoin (Set.mem_singleton _)⟩ :=
    ⟨Algebra.adjoin.powerBasis' hint, Algebra.adjoin.powerBasis'_gen hint⟩
  have hgen' : (pb.gen : ℂ) = χ g := by rw [hgen]
  have hmin : minpoly ℤ pb.gen = cyclotomic (orderOf χ) ℤ := by
    rw [hgen, ← minpoly.algHom_eq (Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)).val Subtype.val_injective]
    exact (cyclotomic_eq_minpoly hμ hnpos).symm
  have hval : (PAG.Part185.chiA χ hμ).ringHomComp
      (Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)).val.toRingHom = χ := MulChar.ext' (fun x => rfl)
  have hAint : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ) ≤ integralClosure ℤ ℂ :=
    adjoin_le_integralClosure hint
  have hmemI : ∀ w : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ), IsIntegral ℤ (w : ℂ) :=
    fun w => (mem_integralClosure_iff ℤ ℂ).mp (hAint w.2)
  set χA := PAG.Part185.chiA χ hμ with hχA
  set n := orderOf χ with hn_def
  set U := ∏ j ∈ Ico 1 n, PAG.Part190.alphaA χA n j ^ (a j).toNat *
    PAG.Part190.betaA χA n j ^ (-a j).toNat with hU
  set V := ∏ j ∈ Ico 1 n, PAG.Part190.alphaA χA n j ^ (-a j).toNat *
    PAG.Part190.betaA χA n j ^ (a j).toNat with hV
  set Ub := ∏ j ∈ Ico 1 n, PAG.Part190.alphaB χA n j ^ (a j).toNat *
    PAG.Part190.betaB χA n j ^ (-a j).toNat with hUb
  set Vb := ∏ j ∈ Ico 1 n, PAG.Part190.alphaB χA n j ^ (-a j).toNat *
    PAG.Part190.betaB χA n j ^ (a j).toNat with hVb
  set M := ∑ j ∈ Ico 1 n, 2 * n * j * ((a j).toNat + (-a j).toNat) with hM
  have hVVb : V * Vb = (p : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)) ^ M :=
    PAG.Part190.V_mul_Vb hval hn a
  have hUUb : U * Ub = (p : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)) ^ M := by
    have := PAG.Part190.V_mul_Vb hval hn (fun j => -a j)
    simp only [neg_neg] at this
    rw [this]
    congr 1
    exact sum_congr rfl (fun j _ => by ring)
  have hpM : ((p : ℂ)) ^ M ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have eV : (V : ℂ) * (Vb : ℂ) = (p : ℂ) ^ M := by
    have := congrArg (fun x : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ) => (x : ℂ)) hVVb
    simpa using this
  have eU : (U : ℂ) * (Ub : ℂ) = (p : ℂ) ^ M := by
    have := congrArg (fun x : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ) => (x : ℂ)) hUUb
    simpa using this
  have hV0 : (V : ℂ) ≠ 0 := left_ne_zero_of_mul (by rw [eV]; exact hpM)
  have hU0 : (U : ℂ) ≠ 0 := left_ne_zero_of_mul (by rw [eU]; exact hpM)
  -- X^{2n} = U/V
  have hβC : ∀ j ∈ Ico 1 n,
      (Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)).val.toRingHom (PAG.Part190.betaA χA n j) ≠ 0 :=
    fun j hj => PAG.Part190.map_betaA_ne_zero hval _ j (mem_Ico.mp hj).1
      (by have := (mem_Ico.mp hj).2; omega)
  have hY := PAG.Part190.map_U_div_V (Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)).val.toRingHom hval n rfl
    hn hψ a hβC
  have hX : (∏ j ∈ Ico 1 n, (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a j) ^ (2 * n)
      = ∏ j ∈ Ico 1 n, ((gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * n)) ^ a j := by
    rw [← prod_pow]
    refine prod_congr rfl (fun j _ => ?_)
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast _ (2 * n), ← zpow_mul, mul_comm]
  refine ⟨_, U, V, M, by rw [hX, ← hY]; rfl, ?_, ?_, hU0, hV0, ?_⟩
  · -- p^M (U/V) = U V̄
    have : (p : ℂ) ^ M * ((U : ℂ) / (V : ℂ)) = (U : ℂ) * (Vb : ℂ) := by
      rw [← eV]; field_simp
    rw [this]
    exact (hmemI U).mul (hmemI Vb)
  · have : (p : ℂ) ^ M * ((V : ℂ) / (U : ℂ)) = (V : ℂ) * (Ub : ℂ) := by
      rw [← eU]; field_simp
    rw [this]
    exact (hmemI V).mul (hmemI Ub)
  · intro c hc
    -- ℤ_p の 1 の原始 n 乗根
    have hdvd : n ∣ p - 1 := PAG.Part185.orderOf_dvd_sub_one χ
    have h2p := hp.out.two_le
    have hkn : (p - 1) / n * n = p - 1 := Nat.div_mul_cancel hdvd
    have hkpos : 0 < (p - 1) / n := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hnpos
    have hga : IsPrimitiveRoot ((g : ZMod p)) (p - 1) := by
      rw [IsPrimitiveRoot.coe_units_iff, ← PAG.Part185.orderOf_gen g hg]
      exact IsPrimitiveRoot.orderOf g
    have hgk : IsPrimitiveRoot ((g : ZMod p) ^ ((p - 1) / n)) n := by
      have := hga.pow_of_dvd hkpos.ne' (Dvd.intro _ hkn)
      rwa [Nat.div_div_self hdvd (by omega)] at this
    have hnp : ((n : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
      have := Nat.le_of_dvd hnpos h; have := Nat.le_of_dvd (by omega) hdvd; omega
    obtain ⟨z, hz, hzy⟩ := PAG.Part189.exists_padic_root n hnpos hnp _ hgk
    obtain ⟨ι, hιg⟩ := PAG.Part190.exists_lift pb hnpos hmin (z ^ c) (hz.pow_of_coprime c hc)
    have hev : χA.ringHomComp (PadicInt.toZMod.comp ι) = powChar ((p - 1) / n * c) :=
      PAG.Part190.hev_of_lift χ g hg hμ pb hgen' ι _ (by rw [hιg, map_pow, hzy, ← pow_mul])
    have hab := fun j (hj : j ∈ Ico 1 n) =>
      PAG.Part190.val_alpha_beta hval hev hc hn j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2
    have hx : ∀ j ∈ Ico 1 n, ι (PAG.Part190.alphaA χA n j) ≠ 0 := fun j hj => (hab j hj).1
    have hy : ∀ j ∈ Ico 1 n, ι (PAG.Part190.betaA χA n j) ≠ 0 := fun j hj => (hab j hj).2.1
    refine ⟨ι, ?_, ?_, ?_⟩
    · simp only [hU, map_prod, map_mul, map_pow]
      exact prod_ne_zero_iff.mpr fun j hj => mul_ne_zero (pow_ne_zero _ (hx j hj)) (pow_ne_zero _ (hy j hj))
    · simp only [hV, map_prod, map_mul, map_pow]
      exact prod_ne_zero_iff.mpr fun j hj => mul_ne_zero (pow_ne_zero _ (hx j hj)) (pow_ne_zero _ (hy j hj))
    · have hs := PAG.Part190.val_split (Ico 1 n) (fun j => ι (PAG.Part190.alphaA χA n j))
        (fun j => ι (PAG.Part190.betaA χA n j)) hx hy a
      rw [sum_congr rfl (fun j hj => by rw [(hab j hj).2.2])] at hs
      simp only [hU, hV, map_prod, map_mul, map_pow]
      exact hs

end Prime

/-! ### 4. 素数ごとに分ける -/

/-- **4.** 相異なる素数 P_i（i ∈ s）と Y_i で、P_i^{M_i} Y_i^{±1} が代数的整数、∏ Y_i^{e_i} = 1 なら、
  i₀ ∈ s について Y_{i₀}^{e_{i₀}} とその逆数は代数的整数。 -/
theorem separate_core {ι : Type*} (s : Finset ι) (P : ι → ℕ) (hP : ∀ i, (P i).Prime)
    (hinj : Set.InjOn P s) (Y : ι → ℂ) (M e : ι → ℕ)
    (h1 : ∀ i ∈ s, IsIntegral ℤ ((P i : ℂ) ^ M i * Y i))
    (h2 : ∀ i ∈ s, IsIntegral ℤ ((P i : ℂ) ^ M i * (Y i)⁻¹))
    (hrel : ∏ i ∈ s, Y i ^ e i = 1) (i₀ : ι) (hi₀ : i₀ ∈ s) :
    IsIntegral ℤ (Y i₀ ^ e i₀) ∧ IsIntegral ℤ ((Y i₀ ^ e i₀)⁻¹) := by
  classical
  have hsplit := mul_prod_erase s (fun i => Y i ^ e i) hi₀
  rw [hrel] at hsplit
  -- Y₀^{e₀} = ∏_{i ≠ i₀} (Y_i⁻¹)^{e_i}、(Y₀^{e₀})⁻¹ = ∏_{i ≠ i₀} Y_i^{e_i}
  have hinv : (Y i₀ ^ e i₀)⁻¹ = ∏ i ∈ s.erase i₀, Y i ^ e i := by
    rw [inv_eq_of_mul_eq_one_right hsplit]
  have hZ : Y i₀ ^ e i₀ = ∏ i ∈ s.erase i₀, (Y i)⁻¹ ^ e i := by
    rw [← inv_inv (Y i₀ ^ e i₀), hinv, ← prod_inv_distrib]
    exact prod_congr rfl (fun i _ => by rw [inv_pow])
  set m : ℤ := ∏ i ∈ s.erase i₀, (P i : ℤ) ^ (M i * e i) with hm
  have hcop : IsCoprime ((P i₀ : ℤ) ^ (M i₀ * e i₀)) m := by
    apply IsCoprime.prod_right
    intro i hi
    apply IsCoprime.pow
    rw [Nat.isCoprime_iff_coprime, Nat.coprime_primes (hP i₀) (hP i)]
    intro h
    exact (mem_erase.mp hi).1 (hinj (mem_of_mem_erase hi) hi₀ h.symm)
  have hmC : ((m : ℤ) : ℂ) = ∏ i ∈ s.erase i₀, (P i : ℂ) ^ (M i * e i) := by
    rw [hm]; push_cast; rfl
  have hint_prod : ∀ (f : ι → ℂ), (∀ i ∈ s.erase i₀, IsIntegral ℤ (f i)) →
      IsIntegral ℤ (∏ i ∈ s.erase i₀, f i) := by
    intro f hf
    have : (∏ i ∈ s.erase i₀, f i) ∈ integralClosure ℤ ℂ :=
      prod_mem (fun i hi => (mem_integralClosure_iff ℤ ℂ).mpr (hf i hi))
    exact (mem_integralClosure_iff ℤ ℂ).mp this
  constructor
  · apply isIntegral_of_coprime _ _ _ hcop
    · push_cast
      rw [pow_mul, ← mul_pow]
      exact (h1 i₀ hi₀).pow _
    · rw [hmC, hZ, ← prod_mul_distrib]
      apply hint_prod
      intro i hi
      rw [pow_mul, ← mul_pow]
      exact (h2 i (mem_of_mem_erase hi)).pow _
  · apply isIntegral_of_coprime _ _ _ hcop
    · push_cast
      rw [← inv_pow, pow_mul, ← mul_pow]
      exact (h2 i₀ hi₀).pow _
    · rw [hmC, hinv, ← prod_mul_distrib]
      apply hint_prod
      intro i hi
      rw [pow_mul, ← mul_pow]
      exact (h1 i (mem_of_mem_erase hi)).pow _

/-! ### 5. 主定理 -/

section Main

variable {ι : Type*} [Fintype ι] (P : ι → ℕ) [hP : ∀ i, Fact (P i).Prime]

/-- **5a. 分離**：∏_i X_i が 1 の冪根なら、各 i と、n_i と互いに素な各 c で S_c(a_i) = 0。 -/
theorem multi_same_necessary (hinj : Function.Injective P) (χ : ∀ i, MulChar (ZMod (P i)) ℂ)
    (ψ : ∀ i, AddChar (ZMod (P i)) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive) (a : ι → ℕ → ℤ) (N : ℕ)
    (hN : 0 < N)
    (h : (∏ i, ∏ j ∈ Ico 1 (orderOf (χ i)),
      (gaussSum (χ i ^ j) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i j) ^ N = 1)
    (i₀ : ι) (c : ℕ) (hc : c.Coprime (orderOf (χ i₀))) :
    ∑ j ∈ Ico 1 (orderOf (χ i₀)),
      a i₀ j * ((orderOf (χ i₀) : ℤ) - 2 * ((c * j % orderOf (χ i₀) : ℕ) : ℤ)) = 0 := by
  classical
  rcases Nat.lt_or_ge (orderOf (χ i₀)) 2 with hn0 | hn0
  · rw [Ico_eq_empty_of_le (by omega), sum_empty]
  set X : ι → ℂ := fun i => ∏ j ∈ Ico 1 (orderOf (χ i)),
    (gaussSum (χ i ^ j) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i j with hX
  set Y : ι → ℂ := fun i => X i ^ (2 * orderOf (χ i)) with hY
  set s := univ.filter (fun i => 2 ≤ orderOf (χ i)) with hs
  have hi₀ : i₀ ∈ s := mem_filter.mpr ⟨mem_univ _, hn0⟩
  have hX1 : ∀ i, i ∉ s → X i = 1 := by
    intro i hi
    have : orderOf (χ i) < 2 := by
      by_contra hcon
      exact hi (mem_filter.mpr ⟨mem_univ _, by omega⟩)
    simp only [hX]
    rw [Ico_eq_empty_of_le (by omega), prod_empty]
  have hprod : ∏ i ∈ s, X i = ∏ i, X i := prod_subset (subset_univ s) (fun i _ hi => hX1 i hi)
  -- 各素数で P_i^{M_i} Y_i^{±1} は代数的整数
  have hMint : ∀ i, ∃ M : ℕ, IsIntegral ℤ ((P i : ℂ) ^ M * Y i) ∧
      IsIntegral ℤ ((P i : ℂ) ^ M * (Y i)⁻¹) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨A, U, V, M, hYUV, h1, h2, -, -, -⟩ :=
        exists_UV (p := P i) (χ i) (hψ i) (mem_filter.mp hi).2 (a i)
      refine ⟨M, ?_, ?_⟩
      · simp only [hY, hX]; rw [hYUV]; exact h1
      · simp only [hY, hX]; rw [hYUV, inv_div]; exact h2
    · refine ⟨0, ?_, ?_⟩
      · simp only [hY, hX1 i hi, one_pow, pow_zero, mul_one]; exact isIntegral_one
      · simp only [hY, hX1 i hi, one_pow, pow_zero, inv_one, mul_one]; exact isIntegral_one
  choose M hM using hMint
  -- 冪をそろえる：e_i = N ∏_{k ≠ i} 2n_k
  set e : ι → ℕ := fun i => N * ∏ k ∈ s.erase i, (2 * orderOf (χ k)) with he
  set L := ∏ k ∈ s, (2 * orderOf (χ k)) with hL
  have heL : ∀ i ∈ s, 2 * orderOf (χ i) * e i = N * L := by
    intro i hi
    rw [he, hL, ← mul_prod_erase s (fun k => 2 * orderOf (χ k)) hi]
    ring
  have hrel : ∏ i ∈ s, Y i ^ e i = 1 := by
    rw [prod_congr rfl (fun i hi => by rw [hY, ← pow_mul, heL i hi]), prod_pow, hprod, pow_mul, h,
      one_pow]
  obtain ⟨hZ, hZinv⟩ := separate_core s P (fun i => (hP i).out) hinj.injOn Y M e
    (fun i _ => (hM i).1) (fun i _ => (hM i).2) hrel i₀ hi₀
  -- i₀ の U, V
  obtain ⟨A, U, V, M₀, hYUV, -, -, hU0, hV0, hval⟩ :=
    exists_UV (p := P i₀) (χ i₀) (hψ i₀) hn0 (a i₀)
  obtain ⟨φ, hφU, hφV, hdiff⟩ := hval c hc
  have he0 : 0 < e i₀ := by
    rw [he]
    exact Nat.mul_pos hN (prod_pos (fun k hk => by
      have := (mem_filter.mp (mem_of_mem_erase hk)).2; omega))
  have hYi : Y i₀ = (U : ℂ) / (V : ℂ) := hYUV
  have hZ' : IsIntegral ℤ (((U ^ e i₀ : A) : ℂ) / ((V ^ e i₀ : A) : ℂ)) := by
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← div_pow, ← hYi]; exact hZ
  have hZinv' : IsIntegral ℤ (((V ^ e i₀ : A) : ℂ) / ((U ^ e i₀ : A) : ℂ)) := by
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← div_pow, ← inv_div, ← hYi, inv_pow]
    exact hZinv
  have v1 := val_le_of_isIntegral φ (U ^ e i₀) (V ^ e i₀) (by rw [map_pow]; exact pow_ne_zero _ hφU)
    (by rw [map_pow]; exact pow_ne_zero _ hφV) hZ'
  have v2 := val_le_of_isIntegral φ (V ^ e i₀) (U ^ e i₀) (by rw [map_pow]; exact pow_ne_zero _ hφV)
    (by rw [map_pow]; exact pow_ne_zero _ hφU) hZinv'
  rw [map_pow, map_pow, PadicInt.valuation_pow, PadicInt.valuation_pow] at v1 v2
  have heq : (φ U).valuation = (φ V).valuation :=
    le_antisymm (Nat.le_of_mul_le_mul_left v2 he0) (Nat.le_of_mul_le_mul_left v1 he0)
  rw [← hdiff, heq, sub_self]

/-- **5b. 完全な判定**：∏_i X_i が 1 の冪根 ⇔ すべての i と、n_i と互いに素なすべての c で S_c(a_i) = 0。 -/
theorem multi_same_root_iff (hinj : Function.Injective P) (χ : ∀ i, MulChar (ZMod (P i)) ℂ)
    (ψ : ∀ i, AddChar (ZMod (P i)) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive) (a : ι → ℕ → ℤ) :
    (∃ N : ℕ, 0 < N ∧ (∏ i, ∏ j ∈ Ico 1 (orderOf (χ i)),
      (gaussSum (χ i ^ j) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i j) ^ N = 1) ↔
      ∀ i, ∀ c : ℕ, c.Coprime (orderOf (χ i)) →
        ∑ j ∈ Ico 1 (orderOf (χ i)), a i j * ((orderOf (χ i) : ℤ) - 2 * ((c * j % orderOf (χ i) : ℕ) : ℤ))
          = 0 := by
  constructor
  · rintro ⟨N, hN, h⟩ i c hc
    exact multi_same_necessary P hinj χ ψ hψ a N hN h i c hc
  · intro hS
    exact PAG.Part188.prod_root_of_root univ _ (fun i _ =>
      PAG.Part190.same_prime_sufficient (p := P i) (χ i) (hψ i) (a i) (hS i))

/-- **5c.** ∏_i X_i が 1 の冪根 ⇔ 各 X_i が 1 の冪根（素数ごとに分かれる）。 -/
theorem multi_same_root_iff_each (hinj : Function.Injective P) (χ : ∀ i, MulChar (ZMod (P i)) ℂ)
    (ψ : ∀ i, AddChar (ZMod (P i)) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive) (a : ι → ℕ → ℤ) :
    (∃ N : ℕ, 0 < N ∧ (∏ i, ∏ j ∈ Ico 1 (orderOf (χ i)),
      (gaussSum (χ i ^ j) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i j) ^ N = 1) ↔
      ∀ i, ∃ N : ℕ, 0 < N ∧ (∏ j ∈ Ico 1 (orderOf (χ i)),
        (gaussSum (χ i ^ j) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i j) ^ N = 1 := by
  rw [multi_same_root_iff P hinj χ ψ hψ a]
  exact forall_congr' (fun i => (PAG.Part190.same_prime_root_iff (p := P i) (χ i) (hψ i) (a i)).symm)

/-- **6. 全体の判定**：さらに、導手 Q_k^{e_k}（e_k ≥ 2）の原始指標 φ_k の z の整数冪を掛けても、
  1 の冪根になる条件は変わらない（それらの因子は Part 183 によりつねに 1 の冪根）。 -/
theorem full_root_iff (hinj : Function.Injective P) (χ : ∀ i, MulChar (ZMod (P i)) ℂ)
    (ψ : ∀ i, AddChar (ZMod (P i)) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive) (a : ι → ℕ → ℤ)
    {κ : Type*} [Fintype κ] (Q : κ → ℕ) [hQ : ∀ k, Fact (Q k).Prime] (e : κ → ℕ) (he : ∀ k, 2 ≤ e k)
    (φ : ∀ k, DirichletCharacter ℂ (Q k ^ e k)) (hφ : ∀ k, (φ k).IsPrimitive) (b : κ → ℤ) :
    (∃ N : ℕ, 0 < N ∧ ((∏ i, ∏ j ∈ Ico 1 (orderOf (χ i)),
        (gaussSum (χ i ^ j) (ψ i) / ((Real.sqrt (P i) : ℝ) : ℂ)) ^ a i j) *
      ∏ k, (gaussSum (φ k) ZMod.stdAddChar / ((Real.sqrt ((Q k : ℝ) ^ e k) : ℝ) : ℂ)) ^ b k) ^ N = 1) ↔
      ∀ i, ∀ c : ℕ, c.Coprime (orderOf (χ i)) →
        ∑ j ∈ Ico 1 (orderOf (χ i)), a i j * ((orderOf (χ i) : ℤ) - 2 * ((c * j % orderOf (χ i) : ℕ) : ℤ))
          = 0 := by
  obtain ⟨M, hM, hC⟩ := PAG.Part188.prod_root_of_root univ
    (fun k => (gaussSum (φ k) ZMod.stdAddChar / ((Real.sqrt ((Q k : ℝ) ^ e k) : ℝ) : ℂ)) ^ b k)
    (fun k _ => PAG.Part188.zpow_root _ _ ((PAG.Part187.single_root_iff (p := Q k) (e k)
      (by have := he k; omega) (φ k) (hφ k)).mpr (Or.inl (he k))))
  rw [mul_comm, PAG.Part183.root_mul_iff _ _ M hM hC]
  exact multi_same_root_iff P hinj χ ψ hψ a

end Main

end PAG.Part191

#print axioms PAG.Part191.val_le_of_isIntegral
#print axioms PAG.Part191.isIntegral_of_coprime
#print axioms PAG.Part191.exists_UV
#print axioms PAG.Part191.separate_core
#print axioms PAG.Part191.multi_same_necessary
#print axioms PAG.Part191.multi_same_root_iff
#print axioms PAG.Part191.multi_same_root_iff_each
#print axioms PAG.Part191.full_root_iff
