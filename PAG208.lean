/-
  PAG 2.0 Part 204（2026-10-24）— V_s の完全性（ケットの V_s 成分による直交基底）
  双対殻 s（s·n = N）の空間 V_s = {f : ε_s ⋆ f = f}。g_ψ = 𝓕⁻¹(ι_{s,*}ψ)（ψ は法 n のディリクレ指標）
  1. 𝓕g_ψ(ξ) = [s ∣ ξ]·ψ(ξ/s)、𝓕g_ψ の台は D_s、g_ψ ∈ V_s
  2. 直交性：⟨g_ψ, g_ψ′⟩ = [ψ = ψ′]·φ(n)/N。g_ψ は一次独立で、張る空間の次元は φ(n)。単位指標では g_1 = ε_s
  3. 完全性：f ∈ V_s なら f = Σ_ψ (N/φ(n))·⟨g_ψ, f⟩·g_ψ。V_s = span{g_ψ}、dim V_s = φ(n)
  4. ケットの V_s 成分：c ∣ n、χ が法 c の原始指標なら ε_s ⋆ |n/c, χ⟩_N = B·g_{χ̄′}
     （χ̄′ は χ⁻¹ を法 n に持ち上げたもの、B = φ(sc)^(−1/2)·s·χ̄(−1)·τ(χ) ≠ 0）。
     n/c の素因数がすべて c を割るなら、ケット自身が B·g_{χ̄′}。異なる組の成分は直交する
  5. 対応 (c, χ) ↦ χ̄′ は「c ∣ n と法 c の原始指標の組」から「法 n の指標」への全単射（χ̄′ の導手は c）。
     個数：Σ_{c ∣ n} #{法 c の原始指標} = φ(n)
  6. 結論：V_s は双対殻 s のケットの V_s 成分で張られる。s を動かすと ℓ²(ℤ/N) 全体の直交基底
     （個数 Σ_{s ∣ N} φ(N/s) = N）になる（局所の Part 89・91 の大域版）
-/
import PAG207

namespace PAG.Part208

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 基底の候補 g_ψ -/

/-- 双対殻 s の基底ベクトル g_ψ = 𝓕⁻¹(ι_{s,*}ψ)：𝓕g_ψ(ξ) = [s ∣ ξ]·ψ(ξ/s)（ψ は法 n の指標。s·n = N で使う）。 -/
noncomputable def gbas (s n N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ n) : ZMod N → ℂ :=
  𝓕⁻ (fun ξ => if s ∣ ξ.val then ψ ((ξ.val / s : ℕ) : ZMod n) else 0)

/-- **1a.** 𝓕g_ψ(ξ) = [s ∣ ξ]·ψ(ξ/s)。 -/
theorem dft_gbas_apply (s n N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ n) (ξ : ZMod N) :
    𝓕 (gbas s n N ψ) ξ = if s ∣ ξ.val then ψ ((ξ.val / s : ℕ) : ZMod n) else 0 := by
  unfold gbas
  rw [LinearEquiv.apply_symm_apply]

/-- **1b.** 𝓕g_ψ = ι_{s,*}ψ（s·n = N）。 -/
theorem dft_gbas (s n N : ℕ) [NeZero N] [NeZero n] (h : s * n = N) (ψ : DirichletCharacter ℂ n) :
    𝓕 (gbas s n N ψ) = PAG.Part17.push (memb s n N h) ψ := by
  funext ξ
  rw [dft_gbas_apply, push_memb_apply]

/-- **1c.** 𝓕g_ψ(s·y) = ψ(y)。 -/
theorem dft_gbas_memb (s n N : ℕ) [NeZero N] (h : s * n = N) (ψ : DirichletCharacter ℂ n) (y : ZMod n) :
    𝓕 (gbas s n N ψ) (memb s n N h y) = ψ y := by
  have : NeZero n := neZero_of_mul h
  rw [dft_gbas_apply, memb_val, ite_eq_left (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (pos_of_mul h),
    ZMod.natCast_zmod_val]

/-- **1d.** s ∣ x のとき gcd(N, x) = s ⇔ x/s と n は互いに素。 -/
theorem gcd_eq_iff_coprime (s n N : ℕ) [NeZero N] (h : s * n = N) (x : ℕ) (hd : s ∣ x) :
    Nat.gcd N x = s ↔ (x / s).Coprime n := by
  obtain ⟨y, rfl⟩ := hd
  have hs0 : 0 < s := pos_of_mul h
  rw [Nat.mul_div_cancel_left y hs0, ← h, Nat.gcd_mul_left, Nat.coprime_comm]
  constructor
  · intro e
    exact Nat.eq_of_mul_eq_mul_left hs0 (e.trans (mul_one s).symm)
  · intro e
    rw [Nat.Coprime.gcd_eq_one e, mul_one]

/-- **1e.** gcd(N, s·b) = s ⇔ b は単数。 -/
theorem gcd_memb_eq_iff (s n N : ℕ) [NeZero N] (h : s * n = N) (b : ZMod n) :
    Nat.gcd N (memb s n N h b).val = s ↔ IsUnit b := by
  have : NeZero n := neZero_of_mul h
  rw [memb_val, gcd_eq_iff_coprime s n N h _ (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (pos_of_mul h),
    ← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]

/-- **1f.** 𝓕g_ψ の台は D_s：1_{D_s}·𝓕g_ψ = 𝓕g_ψ。 -/
theorem dind_mul_dft_gbas (s n N : ℕ) [NeZero N] (h : s * n = N) (ψ : DirichletCharacter ℂ n) :
    dind N s * 𝓕 (gbas s n N ψ) = 𝓕 (gbas s n N ψ) := by
  funext ξ
  rw [Pi.mul_apply, dft_gbas_apply]
  by_cases hd : s ∣ ξ.val
  · rw [ite_eq_left hd]
    by_cases h0 : ψ ((ξ.val / s : ℕ) : ZMod n) = 0
    · rw [h0, mul_zero]
    · have hu : IsUnit ((ξ.val / s : ℕ) : ZMod n) := by
        by_contra hn
        exact h0 (MulChar.map_nonunit _ hn)
      have hg : Nat.gcd N ξ.val = s :=
        (gcd_eq_iff_coprime s n N h ξ.val hd).mpr ((ZMod.isUnit_iff_coprime _ _).mp hu)
      have h1 : dind N s ξ = 1 := by simp only [dind]; rw [ite_eq_left hg]
      rw [h1, one_mul]
  · rw [ite_eq_right hd, mul_zero]

/-- **1g.** g_ψ ∈ V_s：ε_s ⋆ g_ψ = g_ψ。 -/
theorem geps_conv_gbas (s n N : ℕ) [NeZero N] (h : s * n = N) (ψ : DirichletCharacter ℂ n) :
    PAG.Part15.conv (geps N s) (gbas s n N ψ) = gbas s n N ψ := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv, dft_geps, dind_mul_dft_gbas s n N h ψ]

/-! ### 2. 直交性 -/

/-- **2a.** ⟨g_ψ, f⟩ = N⁻¹·Σ_b ψ⁻¹(b)·𝓕f(s·b)（内積は Σ_j conj(a_j)·b_j）。 -/
theorem inner_gbas_left (s n N : ℕ) [NeZero N] [NeZero n] (h : s * n = N) (ψ : DirichletCharacter ℂ n)
    (f : ZMod N → ℂ) :
    ∑ j, starRingEnd ℂ (gbas s n N ψ j) * f j =
      (N : ℂ)⁻¹ * ∑ b : ZMod n, ψ⁻¹ b * 𝓕 f (memb s n N h b) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hp := PAG.Part39.plancherel (gbas s n N ψ) f
  have e : ∑ k, starRingEnd ℂ (𝓕 (gbas s n N ψ) k) * 𝓕 f k =
      ∑ b : ZMod n, ψ⁻¹ b * 𝓕 f (memb s n N h b) := by
    rw [← PAG.Part17.sum_push_mul (memb s n N h) (memb_injective s n N h) (⇑ψ⁻¹) (𝓕 f)]
    refine sum_congr rfl (fun k _ => ?_)
    rw [dft_gbas_apply, push_memb_apply]
    split_ifs
    · rw [starRingEnd_apply, MulChar.star_apply']
    · rw [map_zero]
  rw [e] at hp
  rw [hp, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- **2b.** ‖g_ψ‖² = ⟨g_ψ, g_ψ⟩ = φ(n)/N。 -/
theorem inner_gbas_self (s n N : ℕ) [NeZero N] (h : s * n = N) (ψ : DirichletCharacter ℂ n) :
    ∑ j, starRingEnd ℂ (gbas s n N ψ j) * gbas s n N ψ j = (Nat.totient n : ℂ) / N := by
  have : NeZero n := neZero_of_mul h
  rw [inner_gbas_left s n N h ψ]
  simp_rw [dft_gbas_memb s n N h ψ]
  have e : ∑ b : ZMod n, ψ⁻¹ b * ψ b = ∑ b : ZMod n, (ψ⁻¹ * ψ) b :=
    sum_congr rfl (fun b _ => (MulChar.mul_apply ψ⁻¹ ψ b).symm)
  rw [e, inv_mul_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, inv_mul_eq_div]

/-- **2c.** ψ ≠ ψ′ なら ⟨g_ψ, g_ψ′⟩ = 0。 -/
theorem inner_gbas_of_ne (s n N : ℕ) [NeZero N] (h : s * n = N) (ψ ψ' : DirichletCharacter ℂ n)
    (hne : ψ ≠ ψ') : ∑ j, starRingEnd ℂ (gbas s n N ψ j) * gbas s n N ψ' j = 0 := by
  have : NeZero n := neZero_of_mul h
  rw [inner_gbas_left s n N h ψ]
  simp_rw [dft_gbas_memb s n N h ψ']
  have e : ∑ b : ZMod n, ψ⁻¹ b * ψ' b = ∑ b : ZMod n, (ψ⁻¹ * ψ') b :=
    sum_congr rfl (fun b _ => (MulChar.mul_apply ψ⁻¹ ψ' b).symm)
  rw [e, MulChar.sum_eq_zero_of_ne_one (fun h1 => hne (inv_mul_eq_one.mp h1)), mul_zero]

open Classical in
/-- **2d. 直交性**：⟨g_ψ, g_ψ′⟩ = [ψ = ψ′]·φ(n)/N。 -/
theorem inner_gbas (s n N : ℕ) [NeZero N] (h : s * n = N) (ψ ψ' : DirichletCharacter ℂ n) :
    ∑ j, starRingEnd ℂ (gbas s n N ψ j) * gbas s n N ψ' j =
      if ψ = ψ' then (Nat.totient n : ℂ) / N else 0 := by
  by_cases hpp : ψ = ψ'
  · subst hpp
    rw [ite_eq_left rfl, inner_gbas_self s n N h]
  · rw [ite_eq_right hpp, inner_gbas_of_ne s n N h ψ ψ' hpp]

/-- **2e.** g_ψ ≠ 0（𝓕g_ψ(s) = ψ(1) = 1）。 -/
theorem gbas_ne_zero (s n N : ℕ) [NeZero N] (h : s * n = N) (ψ : DirichletCharacter ℂ n) :
    gbas s n N ψ ≠ 0 := by
  intro h0
  have e := dft_gbas_memb s n N h ψ 1
  rw [h0, map_zero, Pi.zero_apply, MulChar.map_one] at e
  exact zero_ne_one e

/-- **2f.** g_ψ（ψ は法 n の指標）は一次独立。 -/
theorem gbas_linearIndependent (s n N : ℕ) [NeZero N] (h : s * n = N) :
    LinearIndependent ℂ (gbas s n N) := by
  have : NeZero n := neZero_of_mul h
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hφ : (Nat.totient n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  rw [linearIndependent_iff']
  intro t g hg i hi
  have e := congrArg (fun F : ZMod N → ℂ => ∑ j, starRingEnd ℂ (gbas s n N i j) * F j) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, sum_const_zero] at e
  simp_rw [Finset.mul_sum] at e
  rw [Finset.sum_comm] at e
  have e2 : ∀ i' ∈ t, ∑ j, starRingEnd ℂ (gbas s n N i j) * (g i' * gbas s n N i' j) =
      g i' * ∑ j, starRingEnd ℂ (gbas s n N i j) * gbas s n N i' j := by
    intro i' _
    rw [Finset.mul_sum]
    exact sum_congr rfl (fun j _ => by ring)
  rw [sum_congr rfl e2, Finset.sum_eq_single i (fun b _ hb => by
      rw [inner_gbas_of_ne s n N h i b (Ne.symm hb), mul_zero])
    (fun hi' => absurd hi hi'), inner_gbas_self s n N h i] at e
  exact (mul_eq_zero.mp e).resolve_right (div_ne_zero hφ hN)

/-- **2g.** g_ψ が張る空間の次元は φ(n)。 -/
theorem finrank_span_gbas (s n N : ℕ) [NeZero N] (h : s * n = N) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (gbas s n N))) = Nat.totient n := by
  have : NeZero n := neZero_of_mul h
  rw [finrank_span_eq_card (gbas_linearIndependent s n N h), ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ n]

/-- **2h.** 単位指標の基底ベクトルは ε_s：g_1 = ε_s（局所の Part 89 の「∪ {ε_a}」に当たる）。 -/
theorem gbas_one (s n N : ℕ) [NeZero N] (h : s * n = N) : gbas s n N 1 = geps N s := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [dft_gbas_apply, dft_geps]
  simp only [dind]
  by_cases hd : s ∣ ξ.val
  · rw [ite_eq_left hd]
    by_cases hu : IsUnit ((ξ.val / s : ℕ) : ZMod n)
    · rw [MulChar.one_apply hu, ite_eq_left ((gcd_eq_iff_coprime s n N h ξ.val hd).mpr
        ((ZMod.isUnit_iff_coprime _ _).mp hu))]
    · rw [MulChar.map_nonunit _ hu, ite_eq_right (fun e => hu ((ZMod.isUnit_iff_coprime _ _).mpr
        ((gcd_eq_iff_coprime s n N h ξ.val hd).mp e)))]
  · rw [ite_eq_right hd, ite_eq_right (fun e => hd (by rw [← e]; exact Nat.gcd_dvd_right N ξ.val))]

/-! ### 3. 完全性 -/

/-- **3a.** ⟨g_ψ, ε_s ⋆ f⟩ = ⟨g_ψ, f⟩。 -/
theorem inner_gbas_geps_conv (s n N : ℕ) [NeZero N] (h : s * n = N) (ψ : DirichletCharacter ℂ n)
    (f : ZMod N → ℂ) :
    ∑ j, starRingEnd ℂ (gbas s n N ψ j) * PAG.Part15.conv (geps N s) f j =
      ∑ j, starRingEnd ℂ (gbas s n N ψ j) * f j := by
  have : NeZero n := neZero_of_mul h
  rw [inner_gbas_left s n N h, inner_gbas_left s n N h]
  congr 1
  refine sum_congr rfl (fun b _ => ?_)
  rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps]
  by_cases hb : IsUnit b
  · have h1 : dind N s (memb s n N h b) = 1 := by
      simp only [dind]; rw [ite_eq_left ((gcd_memb_eq_iff s n N h b).mpr hb)]
    rw [h1, one_mul]
  · rw [MulChar.map_nonunit _ hb, zero_mul, zero_mul]

/-- **3b. 完全性**：f ∈ V_s なら f = Σ_ψ (N/φ(n))·⟨g_ψ, f⟩·g_ψ。 -/
theorem eq_sum_gbas (s n N : ℕ) [NeZero N] (h : s * n = N) (f : ZMod N → ℂ)
    (hf : PAG.Part15.conv (geps N s) f = f) :
    f = ∑ ψ : DirichletCharacter ℂ n,
      ((N : ℂ) / (Nat.totient n : ℂ) * ∑ j, starRingEnd ℂ (gbas s n N ψ j) * f j) • gbas s n N ψ := by
  have : NeZero n := neZero_of_mul h
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hφ : (Nat.totient n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  -- 𝓕f = 1_{D_s}·𝓕f
  have hF : 𝓕 f = dind N s * 𝓕 f := by
    conv_lhs => rw [← hf]
    rw [PAG.Part16.dft_conv, dft_geps]
  -- 𝓕f(s·b) は b が単数でなければ 0
  have hz : ∀ b : ZMod n, ¬ IsUnit b → 𝓕 f (memb s n N h b) = 0 := by
    intro b hb
    rw [hF, Pi.mul_apply]
    have h0 : dind N s (memb s n N h b) = 0 := by
      simp only [dind]
      rw [ite_eq_right (fun e => hb ((gcd_memb_eq_iff s n N h b).mp e))]
    rw [h0, zero_mul]
  -- 指標の直交関係（b が単数でないときは 𝓕f(s·b) = 0 で消える）
  have key : ∀ y b : ZMod n, (Nat.totient n : ℂ)⁻¹ *
      ((∑ ψ : DirichletCharacter ℂ n, ψ⁻¹ b * ψ y) * 𝓕 f (memb s n N h b)) =
        if b = y then 𝓕 f (memb s n N h b) else 0 := by
    intro y b
    by_cases hb : IsUnit b
    · have hinv : ∀ ψ : DirichletCharacter ℂ n, ψ⁻¹ b = ψ b⁻¹ := by
        obtain ⟨u, rfl⟩ := hb
        intro ψ
        rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
      have e : ∑ ψ : DirichletCharacter ℂ n, ψ⁻¹ b * ψ y =
          if b = y then (Nat.totient n : ℂ) else 0 := by
        rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb y]
        exact sum_congr rfl (fun ψ _ => by rw [hinv ψ])
      rw [e]
      split_ifs
      · rw [← mul_assoc, inv_mul_cancel₀ hφ, one_mul]
      · rw [zero_mul, mul_zero]
    · rw [hz b hb, mul_zero, mul_zero, ite_self]
  have hc : ∀ X : ℂ, (N : ℂ) / (Nat.totient n : ℂ) * ((N : ℂ)⁻¹ * X) = (Nat.totient n : ℂ)⁻¹ * X := by
    intro X
    field_simp
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, dft_gbas_apply]
  by_cases hd : s ∣ ξ.val
  · obtain ⟨y, rfl⟩ := (exists_memb_iff s n N h ξ).mpr hd
    have hy : (((memb s n N h y).val / s : ℕ) : ZMod n) = y := by
      rw [memb_val, Nat.mul_div_cancel_left _ (pos_of_mul h), ZMod.natCast_zmod_val]
    simp only [ite_eq_left hd, hy]
    simp_rw [inner_gbas_left s n N h, hc]
    calc 𝓕 f (memb s n N h y) = ∑ b : ZMod n, if b = y then 𝓕 f (memb s n N h b) else 0 := by simp
      _ = ∑ b : ZMod n, (Nat.totient n : ℂ)⁻¹ *
            ((∑ ψ : DirichletCharacter ℂ n, ψ⁻¹ b * ψ y) * 𝓕 f (memb s n N h b)) :=
          sum_congr rfl (fun b _ => (key y b).symm)
      _ = ∑ ψ : DirichletCharacter ℂ n, (Nat.totient n : ℂ)⁻¹ *
            (∑ b : ZMod n, ψ⁻¹ b * 𝓕 f (memb s n N h b)) * ψ y := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by ring))
  · simp only [ite_eq_right hd, mul_zero, sum_const_zero]
    rw [hF, Pi.mul_apply]
    have h0 : dind N s ξ = 0 := by
      simp only [dind]
      rw [ite_eq_right (fun e => hd (by rw [← e]; exact Nat.gcd_dvd_right N ξ.val))]
    rw [h0, zero_mul]

/-- 双対殻 s の空間 V_s = {f : ε_s ⋆ f = f}。 -/
noncomputable def Vs (N s : ℕ) [NeZero N] : Submodule ℂ (ZMod N → ℂ) :=
  LinearMap.ker (PAG.Part15.convL (geps N s) - LinearMap.id)

/-- **3c.** f ∈ V_s ⇔ ε_s ⋆ f = f。 -/
theorem mem_Vs (N s : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    f ∈ Vs N s ↔ PAG.Part15.conv (geps N s) f = f := by
  rw [Vs, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
    PAG.Part15.convL_apply]

/-- **3d.** V_s = span{g_ψ}。 -/
theorem Vs_eq_span (s n N : ℕ) [NeZero N] (h : s * n = N) :
    Vs N s = Submodule.span ℂ (Set.range (gbas s n N)) := by
  apply le_antisymm
  · intro f hf
    rw [mem_Vs] at hf
    rw [eq_sum_gbas s n N h f hf]
    exact Submodule.sum_mem _ (fun ψ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ψ, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨ψ, rfl⟩
    exact (mem_Vs N s _).mpr (geps_conv_gbas s n N h ψ)

/-- **3e.** dim V_s = φ(n)。 -/
theorem finrank_Vs (s n N : ℕ) [NeZero N] (h : s * n = N) :
    Module.finrank ℂ (Vs N s) = Nat.totient n := by
  rw [Vs_eq_span s n N h, finrank_span_gbas s n N h]

/-! ### 4. ケットの V_s 成分 -/

/-- 双対殻 s のケットの等式 (n/c)·(s·c) = N。 -/
theorem dual_shell_eq {s n N c : ℕ} (h : s * n = N) (hcn : c ∣ n) : n / c * (s * c) = N := by
  rw [← h, show n / c * (s * c) = s * (n / c * c) by ring, Nat.div_mul_cancel hcn]

/-- **4a. ケットの V_s 成分**：c ∣ n、χ が法 c の原始指標なら
ε_s ⋆ |n/c, χ⟩_N = B·g_{χ̄′}（χ̄′ = χ⁻¹ を法 n に持ち上げたもの、B = φ(sc)^(−1/2)·s·χ̄(−1)·τ(χ)）。 -/
theorem geps_conv_gket (s n N : ℕ) [NeZero N] (h : s * n = N) (c : ℕ) [NeZero c] (hcn : c ∣ n)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    PAG.Part15.conv (geps N s) (gket (n / c) (s * c) N (dual_shell_eq h hcn) c (dvd_mul_left c s) χ) =
      ((((Real.sqrt (Nat.totient (s * c)))⁻¹ : ℝ) : ℂ) * (s : ℂ) * χ⁻¹ (-1) * gaussSum χ stdAddChar) •
        gbas s n N ((χ⁻¹).changeLevel hcn) := by
  have hsc : s * c / c = s := Nat.mul_div_cancel s (Nat.pos_of_ne_zero (NeZero.ne c))
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps, map_smul, Pi.smul_apply, smul_eq_mul, dft_gbas_apply,
    dft_gket_apply (n / c) (s * c) N (dual_shell_eq h hcn) c (dvd_mul_left c s) χ hχ ξ, hsc]
  by_cases hg : Nat.gcd N ξ.val = s
  · have hd : s ∣ ξ.val := by rw [← hg]; exact Nat.gcd_dvd_right N ξ.val
    have hcop : (ξ.val / s).Coprime n := (gcd_eq_iff_coprime s n N h ξ.val hd).mp hg
    have h1 : dind N s ξ = 1 := by simp only [dind]; rw [ite_eq_left hg]
    rw [ite_eq_left hd, ite_eq_left hd, h1, one_mul, changeLevel_natCast hcn χ⁻¹ _ hcop]
  · have h0 : dind N s ξ = 0 := by simp only [dind]; rw [ite_eq_right hg]
    rw [h0, zero_mul]
    by_cases hd : s ∣ ξ.val
    · have hnu : ¬ IsUnit ((ξ.val / s : ℕ) : ZMod n) := by
        rw [ZMod.isUnit_iff_coprime]
        exact fun hc => hg ((gcd_eq_iff_coprime s n N h ξ.val hd).mpr hc)
      rw [ite_eq_left hd, MulChar.map_nonunit _ hnu, mul_zero]
    · rw [ite_eq_right hd, mul_zero]

/-- **4b.** n/c の素因数がすべて c を割るなら、ケット自身が B·g_{χ̄′}。 -/
theorem gket_eq_smul_gbas (s n N : ℕ) [NeZero N] (h : s * n = N) (c : ℕ) [NeZero c] (hcn : c ∣ n)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ n / c → q ∣ c) :
    gket (n / c) (s * c) N (dual_shell_eq h hcn) c (dvd_mul_left c s) χ =
      ((((Real.sqrt (Nat.totient (s * c)))⁻¹ : ℝ) : ℂ) * (s : ℂ) * χ⁻¹ (-1) * gaussSum χ stdAddChar) •
        gbas s n N ((χ⁻¹).changeLevel hcn) := by
  have hsc : s * c / c = s := Nat.mul_div_cancel s (Nat.pos_of_ne_zero (NeZero.ne c))
  have e := geps_conv_gket_self (n / c) (s * c) N (dual_shell_eq h hcn) c (dvd_mul_left c s) χ hχ hrad
  rw [hsc] at e
  rw [← e, geps_conv_gket s n N h c hcn χ hχ]

/-- **4c.** 係数 B = φ(sc)^(−1/2)·s·χ̄(−1)·τ(χ) は 0 でない。 -/
theorem ket_coef_ne_zero (s c : ℕ) [NeZero c] (hs : s ≠ 0) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    (((Real.sqrt (Nat.totient (s * c)))⁻¹ : ℝ) : ℂ) * (s : ℂ) * χ⁻¹ (-1) * gaussSum χ stdAddChar ≠ 0 := by
  have hφ : (0 : ℝ) < Real.sqrt (Nat.totient (s * c)) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (mul_ne_zero hs (NeZero.ne c))))
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (PAG.Part16.gaussSum_ne_zero hχ)
  · exact_mod_cast (inv_pos.mpr hφ).ne'
  · exact_mod_cast hs
  · exact ((isUnit_one.neg).map χ⁻¹).ne_zero

/-- **4d.** ケットの V_s 成分は 0 でない。 -/
theorem geps_conv_gket_ne_zero (s n N : ℕ) [NeZero N] (h : s * n = N) (c : ℕ) [NeZero c] (hcn : c ∣ n)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    PAG.Part15.conv (geps N s) (gket (n / c) (s * c) N (dual_shell_eq h hcn) c (dvd_mul_left c s) χ) ≠ 0 := by
  rw [geps_conv_gket s n N h c hcn χ hχ]
  exact smul_ne_zero (ket_coef_ne_zero s c (pos_of_mul h).ne' χ hχ) (gbas_ne_zero s n N h _)

/-- 内積のスカラー倍：⟨a·u, b·v⟩ = conj(a)·b·⟨u, v⟩。 -/
theorem inner_smul_smul {N : ℕ} [NeZero N] (a b : ℂ) (u v : ZMod N → ℂ) :
    ∑ j, starRingEnd ℂ ((a • u) j) * (b • v) j = starRingEnd ℂ a * b * ∑ j, starRingEnd ℂ (u j) * v j := by
  rw [Finset.mul_sum]
  exact sum_congr rfl (fun j _ => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring)

/-- **4e.** 異なる組の成分は直交する：χ̄₁′ ≠ χ̄₂′ なら ⟨ε_s ⋆ |n/c₁, χ₁⟩, ε_s ⋆ |n/c₂, χ₂⟩⟩ = 0。 -/
theorem inner_geps_conv_gket (s n N : ℕ) [NeZero N] (h : s * n = N)
    (c₁ : ℕ) [NeZero c₁] (h₁ : c₁ ∣ n) (χ₁ : DirichletCharacter ℂ c₁) (hχ₁ : χ₁.IsPrimitive)
    (c₂ : ℕ) [NeZero c₂] (h₂ : c₂ ∣ n) (χ₂ : DirichletCharacter ℂ c₂) (hχ₂ : χ₂.IsPrimitive)
    (hne : (χ₁⁻¹).changeLevel h₁ ≠ (χ₂⁻¹).changeLevel h₂) :
    ∑ j, starRingEnd ℂ (PAG.Part15.conv (geps N s)
        (gket (n / c₁) (s * c₁) N (dual_shell_eq h h₁) c₁ (dvd_mul_left c₁ s) χ₁) j) *
      PAG.Part15.conv (geps N s) (gket (n / c₂) (s * c₂) N (dual_shell_eq h h₂) c₂ (dvd_mul_left c₂ s) χ₂) j
        = 0 := by
  rw [geps_conv_gket s n N h c₁ h₁ χ₁ hχ₁, geps_conv_gket s n N h c₂ h₂ χ₂ hχ₂, inner_smul_smul,
    inner_gbas_of_ne s n N h _ _ hne, mul_zero]

/-! ### 5. (c, χ) ↦ χ̄′ の全単射 -/

/-- **5a.** χ が法 c の原始指標、c ∣ n なら χ̄′（χ⁻¹ の持ち上げ）の導手は c。 -/
theorem conductor_changeLevel_inv (n c : ℕ) [NeZero n] (hcn : c ∣ n) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : ((χ⁻¹).changeLevel hcn).conductor = c := by
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_inv]
  exact (DirichletCharacter.isPrimitive_def χ).mp hχ

/-- **5b. 単射**：同じ c で χ̄₁′ = χ̄₂′ なら χ₁ = χ₂。 -/
theorem changeLevel_inv_injective (n c : ℕ) [NeZero n] (hcn : c ∣ n) (χ₁ χ₂ : DirichletCharacter ℂ c)
    (e : (χ₁⁻¹).changeLevel hcn = (χ₂⁻¹).changeLevel hcn) : χ₁ = χ₂ :=
  inv_injective (DirichletCharacter.changeLevel_injective hcn e)

/-- **5c. 全射**：法 n のどの指標 ψ も、ある c ∣ n と法 c の原始指標 χ で ψ = χ̄′ と書ける（c は ψ の導手）。 -/
theorem exists_primitive_changeLevel (n : ℕ) (ψ : DirichletCharacter ℂ n) :
    ∃ (c : ℕ) (hcn : c ∣ n) (χ : DirichletCharacter ℂ c), χ.IsPrimitive ∧ (χ⁻¹).changeLevel hcn = ψ :=
  ⟨(ψ⁻¹).conductor, (ψ⁻¹).conductor_dvd_level, (ψ⁻¹).primitiveCharacter,
    (ψ⁻¹).primitiveCharacter_isPrimitive, by
      rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter, inv_inv]⟩

/-- **5d. 個数**：Σ_{c ∣ n} #{法 c の原始指標} = φ(n)（(c, χ) ↦ χ̄′ が全単射であることから）。 -/
theorem sum_card_primitive (n : ℕ) [NeZero n] :
    ∑ c ∈ n.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} = Nat.totient n := by
  rw [← DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ n, ← Finset.sum_coe_sort n.divisors,
    ← Nat.card_sigma]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => (p.2.1⁻¹).changeLevel (Nat.dvd_of_mem_divisors p.1.2)) ⟨?_, ?_⟩)
  · rintro ⟨⟨c₁, hc₁⟩, ⟨χ₁, p₁⟩⟩ ⟨⟨c₂, hc₂⟩, ⟨χ₂, p₂⟩⟩ e
    simp only at e
    have hc : c₁ = c₂ :=
      (conductor_changeLevel_inv n c₁ _ χ₁ p₁).symm.trans
        ((congrArg DirichletCharacter.conductor e).trans (conductor_changeLevel_inv n c₂ _ χ₂ p₂))
    subst hc
    have := changeLevel_inv_injective n c₁ (Nat.dvd_of_mem_divisors hc₁) χ₁ χ₂ e
    subst this
    rfl
  · intro ψ
    obtain ⟨c, hcn, χ, hχ, e⟩ := exists_primitive_changeLevel n ψ
    exact ⟨⟨⟨c, Nat.mem_divisors.mpr ⟨hcn, NeZero.ne n⟩⟩, ⟨χ, hχ⟩⟩, e⟩

/-! ### 6. 結論 -/

/-- **6a. 完全性（ケット版）**：V_s は双対殻 s のケットの V_s 成分 ε_s ⋆ |n/c, χ⟩_N
（c ∣ n、χ は法 c の原始指標）で張られる。 -/
theorem Vs_eq_span_ket (s n N : ℕ) [NeZero N] (h : s * n = N) :
    Vs N s = Submodule.span ℂ {g | ∃ (c : ℕ) (hcn : c ∣ n) (χ : DirichletCharacter ℂ c), χ.IsPrimitive ∧
      g = PAG.Part15.conv (geps N s) (gket (n / c) (s * c) N (dual_shell_eq h hcn) c (dvd_mul_left c s) χ)} := by
  have : NeZero n := neZero_of_mul h
  rw [Vs_eq_span s n N h]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨ψ, rfl⟩
    obtain ⟨c, hcn, χ, hχ, e⟩ := exists_primitive_changeLevel n ψ
    have : NeZero c := NeZero.of_pos (Nat.pos_of_dvd_of_pos hcn (Nat.pos_of_ne_zero (NeZero.ne n)))
    have key := geps_conv_gket s n N h c hcn χ hχ
    rw [e] at key
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ (ket_coef_ne_zero s c (pos_of_mul h).ne' χ hχ), ← key]
    exact Submodule.subset_span ⟨c, hcn, χ, hχ, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨c, hcn, χ, hχ, rfl⟩
    have : NeZero c := NeZero.of_pos (Nat.pos_of_dvd_of_pos hcn (Nat.pos_of_ne_zero (NeZero.ne n)))
    rw [SetLike.mem_coe, geps_conv_gket s n N h c hcn χ hχ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- **6b.** 異なる双対殻の基底ベクトルは直交する：s ≠ s′ なら ⟨g_{s,ψ}, g_{s′,ψ′}⟩ = 0。 -/
theorem inner_gbas_ne (s n s' n' N : ℕ) [NeZero N] (h : s * n = N) (h' : s' * n' = N) (hne : s ≠ s')
    (ψ : DirichletCharacter ℂ n) (ψ' : DirichletCharacter ℂ n') :
    ∑ j, starRingEnd ℂ (gbas s n N ψ j) * gbas s' n' N ψ' j = 0 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hp := PAG.Part39.plancherel (gbas s n N ψ) (gbas s' n' N ψ')
  have e : ∑ k, starRingEnd ℂ (𝓕 (gbas s n N ψ) k) * 𝓕 (gbas s' n' N ψ') k = 0 := by
    refine sum_eq_zero (fun k _ => ?_)
    rw [← dind_mul_dft_gbas s n N h ψ, ← dind_mul_dft_gbas s' n' N h' ψ', Pi.mul_apply, Pi.mul_apply]
    by_cases hk : Nat.gcd N k.val = s
    · have h0 : dind N s' k = 0 := by
        simp only [dind]; rw [ite_eq_right (fun e => hne (hk.symm.trans e))]
      rw [h0, zero_mul, mul_zero]
    · have h0 : dind N s k = 0 := by simp only [dind]; rw [ite_eq_right hk]
      rw [h0, zero_mul, map_zero, zero_mul]
  rw [e] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left hN

/-- **6c. ℓ²(ℤ/N) 全体の展開**：f = Σ_{s ∣ N} Σ_ψ (N/φ(N/s))·⟨g_{s,ψ}, f⟩·g_{s,ψ}（ψ は法 N/s の指標）。 -/
theorem eq_sum_sum_gbas (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    f = ∑ s ∈ N.divisors, ∑ ψ : DirichletCharacter ℂ (N / s),
      ((N : ℂ) / (Nat.totient (N / s) : ℂ) * ∑ j, starRingEnd ℂ (gbas s (N / s) N ψ j) * f j) •
        gbas s (N / s) N ψ := by
  conv_lhs => rw [← sum_geps_conv N f]
  refine sum_congr rfl (fun s hs => ?_)
  have h : s * (N / s) = N := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hs)
  have hmem : PAG.Part15.conv (geps N s) (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) f := by
    rw [← PAG.Part89.conv_assoc', geps_conv_geps, ite_eq_left rfl]
  rw [eq_sum_gbas s (N / s) N h _ hmem]
  refine sum_congr rfl (fun ψ _ => ?_)
  rw [inner_gbas_geps_conv s (N / s) N h ψ f]

/-- **6d.** 基底ベクトルの総数：Σ_{s ∣ N} φ(N/s) = N。 -/
theorem sum_totient_div (N : ℕ) : ∑ s ∈ N.divisors, Nat.totient (N / s) = N := by
  rw [Nat.sum_div_divisors, Nat.sum_totient]

end PAG.Part208

#print axioms PAG.Part208.dft_gbas_apply
#print axioms PAG.Part208.dft_gbas
#print axioms PAG.Part208.dft_gbas_memb
#print axioms PAG.Part208.gcd_eq_iff_coprime
#print axioms PAG.Part208.gcd_memb_eq_iff
#print axioms PAG.Part208.dind_mul_dft_gbas
#print axioms PAG.Part208.geps_conv_gbas
#print axioms PAG.Part208.inner_gbas_left
#print axioms PAG.Part208.inner_gbas_self
#print axioms PAG.Part208.inner_gbas_of_ne
#print axioms PAG.Part208.inner_gbas
#print axioms PAG.Part208.gbas_ne_zero
#print axioms PAG.Part208.gbas_linearIndependent
#print axioms PAG.Part208.finrank_span_gbas
#print axioms PAG.Part208.gbas_one
#print axioms PAG.Part208.inner_gbas_geps_conv
#print axioms PAG.Part208.eq_sum_gbas
#print axioms PAG.Part208.mem_Vs
#print axioms PAG.Part208.Vs_eq_span
#print axioms PAG.Part208.finrank_Vs
#print axioms PAG.Part208.dual_shell_eq
#print axioms PAG.Part208.geps_conv_gket
#print axioms PAG.Part208.gket_eq_smul_gbas
#print axioms PAG.Part208.ket_coef_ne_zero
#print axioms PAG.Part208.geps_conv_gket_ne_zero
#print axioms PAG.Part208.inner_smul_smul
#print axioms PAG.Part208.inner_geps_conv_gket
#print axioms PAG.Part208.conductor_changeLevel_inv
#print axioms PAG.Part208.changeLevel_inv_injective
#print axioms PAG.Part208.exists_primitive_changeLevel
#print axioms PAG.Part208.sum_card_primitive
#print axioms PAG.Part208.Vs_eq_span_ket
#print axioms PAG.Part208.inner_gbas_ne
#print axioms PAG.Part208.eq_sum_sum_gbas
#print axioms PAG.Part208.sum_totient_div
