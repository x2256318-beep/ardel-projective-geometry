/-
  PAG 2.0 Part 201（2026-10-24）— ℤ/N の双対殻分解（べき等元 ε_s と、ケットの作用素の構造）
  D_s = {ξ ∈ ℤ/N : gcd(N, ξ) = s}（s ∣ N、双対殻 s）、1_{D_s} はその指示関数、ε_s = 𝓕⁻¹(1_{D_s})
  1. 𝓕ε_s = 1_{D_s}（dft_geps）
  2. ε_s ⋆ ε_{s'} = [s = s']·ε_s、Σ_{s ∣ N} ε_s = δ₀、f = Σ_s ε_s ⋆ f
  3. 球の交代和（ラマヌジャン和）：ε_s = Σ_{e ∣ N/s} (μ(e)/(se))·1_{(N/(se))ℤ}
  4. 大きさ：|D_s| = φ(N/s)、ε_s(0) = φ(N/s)/N
  5. ケット |u, χ⟩_N（χ 原始的、法 c、s₀ = M/c）：u の素因数がすべて c を割るなら 𝓕|u, χ⟩ の台はちょうど D_{s₀}、
     ε_{s₀} ⋆ k = k、ε_s ⋆ k = 0（s ≠ s₀）。逆に、そうでなければ k は V_{s₀} に収まらない（gket_mem_iff）
  6. 作用素：k̃ ⋆ (k ⋆ f) = λ·ε_{s₀} ⋆ f（λ = s₀²c/φ(M)）、‖k ⋆ f‖² ≤ λ‖f‖²、V_{s₀} 上で等長、直交補空間で 0
  7. 定理 B の言い換え：|u, A⟩ ⋆ |u, Ā⟩ = A(−1)·λ·ε_{s₀}
-/
import PAG204

namespace PAG.Part205

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 定義とフーリエ変換 -/

/-- 双対殻 s の指示関数 1_{D_s}、D_s = {ξ ∈ ℤ/N : gcd(N, ξ) = s}。 -/
noncomputable def dind (N s : ℕ) : ZMod N → ℂ := fun ξ => if Nat.gcd N ξ.val = s then 1 else 0

/-- 双対殻 s のべき等元 ε_s = 𝓕⁻¹(1_{D_s})。 -/
noncomputable def geps (N s : ℕ) [NeZero N] : ZMod N → ℂ := 𝓕⁻ (dind N s)

/-- **1.** 𝓕ε_s = 1_{D_s}。 -/
theorem dft_geps (N s : ℕ) [NeZero N] : 𝓕 (geps N s) = dind N s := by
  unfold geps
  exact LinearEquiv.apply_symm_apply _ _

/-! ### 2. 直交するべき等元 -/

/-- 1_{D_s}·1_{D_{s'}} = [s = s']·1_{D_s}。 -/
theorem dind_mul (N s s' : ℕ) : dind N s * dind N s' = if s = s' then dind N s else 0 := by
  funext ξ
  by_cases hss : s = s'
  · subst hss
    rw [ite_eq_left rfl, Pi.mul_apply]
    simp only [dind]
    split_ifs <;> simp
  · rw [ite_eq_right hss, Pi.mul_apply, Pi.zero_apply]
    simp only [dind]
    split_ifs with h1 h2 <;> first | exact absurd (h1.symm.trans h2) hss | simp

/-- **2a.** ε_s ⋆ ε_{s'} = [s = s']·ε_s。 -/
theorem geps_conv_geps (N s s' : ℕ) [NeZero N] :
    PAG.Part15.conv (geps N s) (geps N s') = if s = s' then geps N s else 0 := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv, dft_geps, dft_geps, dind_mul]
  split_ifs
  · rw [dft_geps]
  · rw [map_zero]

/-- Σ_{s ∣ N} 1_{D_s} = 1。 -/
theorem sum_dind (N : ℕ) [NeZero N] : ∑ s ∈ N.divisors, dind N s = 1 := by
  funext ξ
  rw [Finset.sum_apply, Pi.one_apply]
  simp only [dind, Finset.sum_ite_eq]
  rw [ite_eq_left (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left N ξ.val, NeZero.ne N⟩)]

/-- 𝓕δ₀ = 1。 -/
theorem dft_delta (N : ℕ) [NeZero N] : 𝓕 (Pi.single (0 : ZMod N) (1 : ℂ)) = 1 := by
  funext k
  rw [ZMod.dft_apply, Pi.one_apply,
    Fintype.sum_eq_single 0 (fun j hj => by rw [Pi.single_eq_of_ne hj, smul_zero])]
  simp

/-- **2b.** Σ_{s ∣ N} ε_s = δ₀。 -/
theorem sum_geps (N : ℕ) [NeZero N] : ∑ s ∈ N.divisors, geps N s = Pi.single (0 : ZMod N) (1 : ℂ) := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [map_sum, dft_delta]
  simp only [dft_geps]
  exact sum_dind N

/-- **2c.** 分解：f = Σ_{s ∣ N} ε_s ⋆ f。 -/
theorem sum_geps_conv (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    ∑ s ∈ N.divisors, PAG.Part15.conv (geps N s) f = f := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [map_sum]
  simp only [PAG.Part16.dft_conv, dft_geps]
  rw [← Finset.sum_mul, sum_dind, one_mul]

/-! ### 3. 球の交代和 -/

/-- Σ_{e ∣ n} [e ∣ y]·μ(e) = [gcd(n, y) = 1]（n ≠ 0）。 -/
theorem sum_moebius_dvd (n y : ℕ) (hn : n ≠ 0) :
    ∑ e ∈ n.divisors, (if e ∣ y then (ArithmeticFunction.moebius e : ℂ) else 0) =
      if Nat.gcd n y = 1 then 1 else 0 := by
  rw [← Finset.sum_filter]
  have hset : n.divisors.filter (fun e => e ∣ y) = (Nat.gcd n y).divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hen, _⟩, hey⟩
      exact ⟨Nat.dvd_gcd hen hey, Nat.gcd_ne_zero_left hn⟩
    · rintro ⟨heg, _⟩
      exact ⟨⟨heg.trans (Nat.gcd_dvd_left n y), hn⟩, heg.trans (Nat.gcd_dvd_right n y)⟩
  rw [hset, sum_moebius_divisors]

/-- 球の指示関数のフーリエ変換：v·W = N なら 𝓕1_{vℤ}(ξ) = [W ∣ ξ]·W。 -/
theorem dft_ball (v W N : ℕ) [NeZero N] (h : v * W = N) (ξ : ZMod N) :
    𝓕 (rk (N := N) v 1 (fun _ => 1)) ξ = if W ∣ ξ.val then (W : ℂ) else 0 := by
  have hone : ((1 : DirichletCharacter ℂ 1) : ZMod 1 → ℂ) = fun _ => 1 := by
    funext x; exact chi_level_one 1 x
  rw [← hone, dft_rk v W N h 1 (one_dvd W) 1 DirichletCharacter.isPrimitive_one_level_one ξ,
    gaussSum_level_one, Nat.div_one]
  simp [chi_level_one]

/-- **3. 球の交代和**：ε_s = Σ_{e ∣ N/s} (μ(e)/(se))·1_{(N/(se))ℤ}（s ∣ N）。 -/
theorem geps_eq_balls (N s : ℕ) [NeZero N] (hs : s ∣ N) :
    geps N s = ∑ e ∈ (N / s).divisors,
      ((ArithmeticFunction.moebius e : ℂ) / ((s * e : ℕ) : ℂ)) • rk (N := N) (N / (s * e)) 1 (fun _ => 1) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have hs0 : 0 < s := Nat.pos_of_dvd_of_pos hs (Nat.pos_of_ne_zero hN0)
  have hNs : N / s ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hs) hs0).ne'
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [dft_geps, map_sum]
  funext ξ
  rw [Finset.sum_apply]
  have hterm : ∀ e ∈ (N / s).divisors,
      𝓕 (((ArithmeticFunction.moebius e : ℂ) / ((s * e : ℕ) : ℂ)) •
          rk (N := N) (N / (s * e)) 1 (fun _ => 1)) ξ
        = if s * e ∣ ξ.val then (ArithmeticFunction.moebius e : ℂ) else 0 := by
    intro e he
    have heN : e ∣ N / s := (Nat.mem_divisors.mp he).1
    have hse : s * e ∣ N := by
      have h' := Nat.mul_dvd_mul_left s heN
      rwa [Nat.mul_div_cancel' hs] at h'
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos heN (Nat.pos_of_ne_zero hNs)
    have hseC : ((s * e : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hs0 he0).ne'
    rw [map_smul, Pi.smul_apply, smul_eq_mul, dft_ball (N / (s * e)) (s * e) N (Nat.div_mul_cancel hse) ξ]
    split_ifs
    · field_simp
    · rw [mul_zero]
  rw [Finset.sum_congr rfl hterm]
  simp only [dind]
  by_cases hsξ : s ∣ ξ.val
  · obtain ⟨y, hy⟩ := hsξ
    have hcond : ∀ e, s * e ∣ ξ.val ↔ e ∣ y := fun e => by
      rw [hy]; exact Nat.mul_dvd_mul_iff_left hs0
    simp only [hcond]
    rw [sum_moebius_dvd (N / s) y hNs]
    have hg : Nat.gcd N ξ.val = s * Nat.gcd (N / s) y := by
      rw [hy, ← Nat.gcd_mul_left, Nat.mul_div_cancel' hs]
    rw [hg]
    by_cases h1 : Nat.gcd (N / s) y = 1
    · simp [h1]
    · have h2 : ¬ (s * Nat.gcd (N / s) y = s) := fun h =>
        h1 (Nat.eq_of_mul_eq_mul_left hs0 (by rw [h, mul_one]))
      rw [ite_eq_right h1, ite_eq_right h2]
  · have h2 : ¬ (Nat.gcd N ξ.val = s) := fun h => hsξ (by rw [← h]; exact Nat.gcd_dvd_right N ξ.val)
    rw [ite_eq_right h2]
    symm
    apply Finset.sum_eq_zero
    intro e _
    rw [ite_eq_right (fun h => hsξ ((dvd_mul_right s e).trans h))]

/-! ### 4. 大きさ -/

/-- **4a.** |D_s| = φ(N/s)（s ∣ N）。 -/
theorem card_dsh (N s : ℕ) [NeZero N] (hs : s ∣ N) :
    (Finset.univ.filter (fun ξ : ZMod N => Nat.gcd N ξ.val = s)).card = Nat.totient (N / s) := by
  rw [Nat.totient_div_of_dvd hs]
  apply Finset.card_bij (fun ξ _ => ξ.val)
  · intro ξ hξ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ZMod.val_lt ξ, hξ⟩
  · intro a _ b _ hab
    exact ZMod.val_injective N hab
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨(k : ZMod N), ?_, ZMod.val_cast_of_lt hk.1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ZMod.val_cast_of_lt hk.1]
    exact hk.2

/-- **4b.** ε_s(0) = φ(N/s)/N（s ∣ N）。 -/
theorem geps_apply_zero (N s : ℕ) [NeZero N] (hs : s ∣ N) :
    geps N s 0 = (Nat.totient (N / s) : ℂ) / N := by
  unfold geps
  rw [ZMod.invDFT_apply]
  simp only [mul_zero, AddChar.map_zero_eq_one, smul_eq_mul, one_mul, dind]
  rw [Finset.sum_boole, card_dsh N s hs, inv_mul_eq_div]

/-! ### 5. ケットの台 -/

/-- u の素因数がすべて c を割るとき：(t, c) = 1 なら (t, uc) = 1。 -/
theorem coprime_mul_of_rad {u c t : ℕ} (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c) (ht : t.Coprime c) :
    t.Coprime (u * c) := by
  have htu : t.Coprime u := Nat.coprime_of_dvd (fun q hq hqt hqu =>
    hq.not_dvd_one (by rw [← Nat.Coprime.gcd_eq_one ht]; exact Nat.dvd_gcd hqt (hrad q hq hqu)))
  exact Nat.Coprime.mul_right htu ht

/-- u の素因数がすべて c を割るとき：gcd(N, s₀t) = s₀ ⇔ (t, c) = 1（s₀ = M/c）。 -/
theorem gcd_dual_iff (u M N : ℕ) (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M) (hM : M ≠ 0)
    (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c) (t : ℕ) :
    Nat.gcd N (M / c * t) = M / c ↔ t.Coprime c := by
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hc)
    (Nat.pos_of_ne_zero (NeZero.ne c))
  have hg : Nat.gcd N (M / c * t) = M / c * Nat.gcd (u * c) t := by
    rw [← dual_eq h hc, Nat.gcd_mul_left]
  rw [hg]
  constructor
  · intro he
    have h1 : (u * c).Coprime t := Nat.eq_of_mul_eq_mul_left hs0 (by rw [he, mul_one])
    exact (Nat.Coprime.symm h1).coprime_dvd_right (dvd_mul_left c u)
  · intro htc
    rw [Nat.Coprime.gcd_eq_one (coprime_mul_of_rad hrad htc).symm, mul_one]

/-- **5a. ケットのフーリエ変換の台**：u の素因数がすべて c を割るなら、𝓕|u, χ⟩(ξ) ≠ 0 ⇔ gcd(N, ξ) = M/c。 -/
theorem dft_gket_ne_zero_iff (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c)
    (ξ : ZMod N) :
    𝓕 (gket u M N h c hc χ) ξ ≠ 0 ↔ Nat.gcd N ξ.val = M / c := by
  have hMZ := neZero_of_mul h
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc) hc0
  have hφ : (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))
    exact_mod_cast (inv_pos.mpr this).ne'
  have hsC : ((M / c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hneg : χ⁻¹ (-1) ≠ 0 := ((isUnit_one.neg : IsUnit (-1 : ZMod c)).map χ⁻¹).ne_zero
  have hB : (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * ((M / c : ℕ) : ℂ) * χ⁻¹ (-1) *
      gaussSum χ stdAddChar ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hφ hsC) hneg) (PAG.Part16.gaussSum_ne_zero hχ)
  rw [dft_gket_apply u M N h c hc χ hχ ξ]
  constructor
  · intro hne
    by_cases hdvd : M / c ∣ ξ.val
    · obtain ⟨t, ht⟩ := hdvd
      rw [ite_eq_left ⟨t, ht⟩, ht, Nat.mul_div_cancel_left t hs0] at hne
      have htc : t.Coprime c := by
        by_contra hcop
        apply hne
        rw [MulChar.map_nonunit χ⁻¹ (fun hu => hcop ((ZMod.isUnit_iff_coprime t c).mp hu)), mul_zero]
      rw [ht]
      exact (gcd_dual_iff u M N h c hc (NeZero.ne M) hrad t).mpr htc
    · rw [ite_eq_right hdvd] at hne
      exact absurd rfl hne
  · intro hg
    have hdvd : M / c ∣ ξ.val := by rw [← hg]; exact Nat.gcd_dvd_right N ξ.val
    obtain ⟨t, ht⟩ := hdvd
    rw [ite_eq_left ⟨t, ht⟩, ht, Nat.mul_div_cancel_left t hs0]
    rw [ht] at hg
    exact mul_ne_zero hB (chi_natCast_ne_zero χ⁻¹ t ((gcd_dual_iff u M N h c hc (NeZero.ne M) hrad t).mp hg))

/-- **5b.** u の素因数がすべて c を割るなら 𝓕|u, χ⟩ = 1_{D_{s₀}}·𝓕|u, χ⟩。 -/
theorem dft_gket_eq_dind_mul (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c) :
    𝓕 (gket u M N h c hc χ) = dind N (M / c) * 𝓕 (gket u M N h c hc χ) := by
  funext ξ
  rw [Pi.mul_apply]
  by_cases h0 : 𝓕 (gket u M N h c hc χ) ξ = 0
  · rw [h0, mul_zero]
  · have hg := (dft_gket_ne_zero_iff u M N h c hc χ hχ hrad ξ).mp h0
    have h1 : dind N (M / c) ξ = 1 := by simp [dind, hg]
    rw [h1, one_mul]

/-- **5c.** u の素因数がすべて c を割るなら ε_{s₀} ⋆ |u, χ⟩ = |u, χ⟩。 -/
theorem geps_conv_gket_self (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c) :
    PAG.Part15.conv (geps N (M / c)) (gket u M N h c hc χ) = gket u M N h c hc χ := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv, dft_geps, ← dft_gket_eq_dind_mul u M N h c hc χ hχ hrad]

/-- **5d.** u の素因数がすべて c を割り s ≠ s₀ なら ε_s ⋆ |u, χ⟩ = 0。 -/
theorem geps_conv_gket_ne (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c)
    (s : ℕ) (hs : s ≠ M / c) :
    PAG.Part15.conv (geps N s) (gket u M N h c hc χ) = 0 := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv, dft_geps, dft_gket_eq_dind_mul u M N h c hc χ hχ hrad, ← mul_assoc, dind_mul,
    ite_eq_right hs, zero_mul, map_zero]

/-- **5e. 逆**：u の素因数 q で c を割らないものがあれば ε_{q·s₀} ⋆ |u, χ⟩ ≠ 0。 -/
theorem geps_conv_gket_spread (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (q : ℕ) (hq : q.Prime) (hqu : q ∣ u)
    (hqc : ¬ q ∣ c) :
    PAG.Part15.conv (geps N (q * (M / c))) (gket u M N h c hc χ) ≠ 0 := by
  intro h0
  have hMZ := neZero_of_mul h
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc) hc0
  have hqs0 : 0 < q * (M / c) := Nat.mul_pos hq.pos hs0
  -- q·s₀ ∣ N
  have hqN : q * (M / c) ∣ N := by
    obtain ⟨u', hu'⟩ := hqu
    exact ⟨u' * c, by rw [← dual_eq h hc, hu']; ring⟩
  have key : 𝓕 (PAG.Part15.conv (geps N (q * (M / c))) (gket u M N h c hc χ))
      ((q * (M / c) : ℕ) : ZMod N) = 0 := by
    rw [h0, map_zero, Pi.zero_apply]
  rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps, dft_gket_apply u M N h c hc χ hχ,
    ZMod.val_natCast] at key
  -- r = q·s₀ mod N：r = q·s₀（q·s₀ < N）か r = 0（q·s₀ = N、このとき c = 1）
  have hgcd : Nat.gcd N (q * (M / c) % N) = q * (M / c) := by
    rcases Nat.lt_or_ge (q * (M / c)) N with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; exact Nat.gcd_eq_right hqN
    · have heq : q * (M / c) = N := le_antisymm (Nat.le_of_dvd hN0 hqN) hge
      rw [heq, Nat.mod_self, Nat.gcd_zero_right]
  have hdvd : M / c ∣ q * (M / c) % N :=
    (Nat.dvd_mod_iff (dvd_trans (dvd_mul_left (M / c) q) hqN)).mpr (dvd_mul_left (M / c) q)
  have hcop : (q * (M / c) % N / (M / c)).Coprime c := by
    rcases Nat.lt_or_ge (q * (M / c)) N with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel _ hs0]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hqc
    · have heq : q * (M / c) = N := le_antisymm (Nat.le_of_dvd hN0 hqN) hge
      -- q·s₀ = s₀·u·c なので u·c = q、q ∣ u から c = 1
      have huc : u * c = q := by
        have e1 : M / c * (u * c) = M / c * q := by rw [dual_eq h hc, ← heq, mul_comm]
        exact Nat.eq_of_mul_eq_mul_left hs0 e1
      have hc1 : c = 1 := by
        obtain ⟨u', hu'⟩ := hqu
        have : q * (u' * c) = q * 1 := by rw [mul_one, ← mul_assoc, ← hu', huc]
        have h2 := Nat.eq_of_mul_eq_mul_left hq.pos this
        exact Nat.eq_one_of_mul_eq_one_left h2
      rw [hc1]
      exact Nat.coprime_one_right _
  have hφ : (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))
    exact_mod_cast (inv_pos.mpr this).ne'
  have hsC : ((M / c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hneg : χ⁻¹ (-1) ≠ 0 := ((isUnit_one.neg : IsUnit (-1 : ZMod c)).map χ⁻¹).ne_zero
  have hd1 : dind N (q * (M / c)) ((q * (M / c) : ℕ) : ZMod N) = 1 := by
    simp only [dind]
    rw [ZMod.val_natCast, hgcd, ite_eq_left rfl]
  rw [hd1, one_mul, ite_eq_left hdvd] at key
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hφ hsC) hneg) (PAG.Part16.gaussSum_ne_zero hχ))
    (chi_natCast_ne_zero χ⁻¹ _ hcop) key

/-- **5f.** ケットが 1 つの双対殻に収まる条件：ε_{s₀} ⋆ |u, χ⟩ = |u, χ⟩ ⇔ u の素因数がすべて c を割る。 -/
theorem gket_mem_iff (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    PAG.Part15.conv (geps N (M / c)) (gket u M N h c hc χ) = gket u M N h c hc χ ↔
      ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c := by
  constructor
  · intro hmem q hq hqu
    by_contra hqc
    have hMZ := neZero_of_mul h
    have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc)
      (Nat.pos_of_ne_zero (NeZero.ne c))
    have hne : q * (M / c) ≠ M / c := by
      intro he
      have : q * (M / c) = 1 * (M / c) := by rw [he, one_mul]
      exact hq.one_lt.ne' (Nat.eq_of_mul_eq_mul_right hs0 this)
    apply geps_conv_gket_spread u M N h c hc χ hχ q hq hqu hqc
    rw [← hmem, ← PAG.Part89.conv_assoc', geps_conv_geps, ite_eq_right hne]
    funext x
    simp [PAG.Part15.conv]
  · intro hrad
    exact geps_conv_gket_self u M N h c hc χ hχ hrad

/-! ### 6. 作用素の構造 -/

/-- **6a.** u の素因数がすべて c を割るなら conj(𝓕k)·𝓕k = λ·1_{D_{s₀}}（λ = s₀²c/φ(M)）。 -/
theorem conj_mul_dft_gket (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c)
    (ξ : ZMod N) :
    starRingEnd ℂ (𝓕 (gket u M N h c hc χ) ξ) * 𝓕 (gket u M N h c hc χ) ξ =
      ((((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M : ℝ) : ℂ) * dind N (M / c) ξ := by
  by_cases h0 : 𝓕 (gket u M N h c hc χ) ξ = 0
  · have hd : dind N (M / c) ξ = 0 := by
      simp only [dind]
      rw [ite_eq_right (fun hg => (dft_gket_ne_zero_iff u M N h c hc χ hχ hrad ξ).mpr hg h0)]
    rw [h0, map_zero, zero_mul, hd, mul_zero]
  · have hd : dind N (M / c) ξ = 1 := by
      simp [dind, (dft_gket_ne_zero_iff u M N h c hc χ hχ hrad ξ).mp h0]
    rw [← Complex.normSq_eq_conj_mul_self, normSq_dft_gket u M N h c hc χ hχ ξ h0, hd, mul_one]

/-- **6b.** k̃ ⋆ (k ⋆ f) = λ·ε_{s₀} ⋆ f（k̃(x) = conj k(−x)、u の素因数がすべて c を割るとき）。 -/
theorem adjoint_mul_gket (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c)
    (f : ZMod N → ℂ) :
    PAG.Part15.conv (PAG.Part30.tilde (gket u M N h c hc χ)) (PAG.Part15.conv (gket u M N h c hc χ) f) =
      ((((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M : ℝ) : ℂ) • PAG.Part15.conv (geps N (M / c)) f := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [PAG.Part16.dft_conv, Pi.mul_apply, PAG.Part38.dft_tilde, PAG.Part16.dft_conv, Pi.mul_apply, map_smul,
    Pi.smul_apply, smul_eq_mul, PAG.Part16.dft_conv, Pi.mul_apply, dft_geps]
  linear_combination (𝓕 f ξ) * conj_mul_dft_gket u M N h c hc χ hχ hrad ξ

/-- **6c.** ‖k ⋆ f‖² ≤ λ‖f‖²（λ = s₀²c/φ(M)。条件なし）。 -/
theorem norm_conv_gket_le (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) :
    ∑ x, Complex.normSq (PAG.Part15.conv (gket u M N h c hc χ) f x) ≤
      ((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M * ∑ x, Complex.normSq (f x) := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlam : (0 : ℝ) ≤ ((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M := by positivity
  have P1 := PAG.Part39.plancherel_normSq (PAG.Part15.conv (gket u M N h c hc χ) f)
  have P2 := PAG.Part39.plancherel_normSq f
  have key : ∑ t, Complex.normSq (𝓕 (PAG.Part15.conv (gket u M N h c hc χ) f) t) ≤
      ((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M * ∑ t, Complex.normSq (𝓕 f t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun t _ => ?_)
    rw [PAG.Part16.dft_conv, Pi.mul_apply, Complex.normSq_mul]
    by_cases h0 : 𝓕 (gket u M N h c hc χ) t = 0
    · rw [h0, Complex.normSq_zero, zero_mul]
      exact mul_nonneg hlam (Complex.normSq_nonneg _)
    · rw [normSq_dft_gket u M N h c hc χ hχ t h0]
  rw [P1, P2] at key
  have key' : (N : ℝ) * ∑ x, Complex.normSq (PAG.Part15.conv (gket u M N h c hc χ) f x) ≤
      (N : ℝ) * (((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M * ∑ x, Complex.normSq (f x)) := by
    calc _ ≤ _ := key
      _ = _ := by ring
  exact le_of_mul_le_mul_left key' hN

/-- **6d.** V_{s₀} 上で等長：ε_{s₀} ⋆ f = f なら ‖k ⋆ f‖² = λ‖f‖²（u の素因数がすべて c を割るとき）。 -/
theorem norm_conv_gket_eq_of_mem (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c)
    (f : ZMod N → ℂ) (hf : PAG.Part15.conv (geps N (M / c)) f = f) :
    ∑ x, Complex.normSq (PAG.Part15.conv (gket u M N h c hc χ) f x) =
      ((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M * ∑ x, Complex.normSq (f x) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have P1 := PAG.Part39.plancherel_normSq (PAG.Part15.conv (gket u M N h c hc χ) f)
  have P2 := PAG.Part39.plancherel_normSq f
  have key : ∑ t, Complex.normSq (𝓕 (PAG.Part15.conv (gket u M N h c hc χ) f) t) =
      ((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M * ∑ t, Complex.normSq (𝓕 f t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [PAG.Part16.dft_conv, Pi.mul_apply, Complex.normSq_mul]
    by_cases h0 : 𝓕 (gket u M N h c hc χ) t = 0
    · have hd : dind N (M / c) t = 0 := by
        simp only [dind]
        rw [ite_eq_right (fun hg => (dft_gket_ne_zero_iff u M N h c hc χ hχ hrad t).mpr hg h0)]
      have hft : 𝓕 f t = 0 := by
        have e := congrArg (fun g => 𝓕 g t) hf
        simp only [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps] at e
        rw [hd, zero_mul] at e
        exact e.symm
      rw [h0, hft, Complex.normSq_zero, mul_zero, mul_zero]
    · rw [normSq_dft_gket u M N h c hc χ hχ t h0]
  rw [P1, P2] at key
  apply mul_left_cancel₀ hN
  rw [key]; ring

/-- **6e.** 直交補空間で 0：ε_{s₀} ⋆ f = 0 なら k ⋆ f = 0（u の素因数がすべて c を割るとき）。 -/
theorem conv_gket_eq_zero_of_perp (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c)
    (f : ZMod N → ℂ) (hf : PAG.Part15.conv (geps N (M / c)) f = 0) :
    PAG.Part15.conv (gket u M N h c hc χ) f = 0 := by
  rw [← geps_conv_gket_self u M N h c hc χ hχ hrad, PAG.Part15.conv_comm (geps N (M / c)),
    PAG.Part89.conv_assoc', hf]
  funext x
  simp [PAG.Part15.conv]

/-! ### 7. 定理 B の言い換え -/

/-- **7.** u の素因数がすべて c を割るなら |u, A⟩ ⋆ |u, Ā⟩ = A(−1)·λ·ε_{s₀}（λ = s₀²c/φ(M)）。 -/
theorem thmB_geps (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (A : DirichletCharacter ℂ c) (hA : A.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c) :
    PAG.Part15.conv (gket u M N h c hc A) (gket u M N h c hc (A⁻¹ : DirichletCharacter ℂ c)) =
      (A (-1) * ((((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M : ℝ) : ℂ)) • geps N (M / c) := by
  have hMZ := neZero_of_mul h
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc) hc0
  have hφ : (0 : ℝ) < Nat.totient M := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [dft_conv_gket u M N h c hc A A⁻¹ hA (PAG.Part16.isPrimitive_inv hA) ξ, map_smul, Pi.smul_apply,
    smul_eq_mul, dft_geps]
  simp only [dind]
  by_cases hdvd : M / c ∣ ξ.val
  · obtain ⟨t, ht⟩ := hdvd
    rw [ite_eq_left ⟨t, ht⟩, ht, Nat.mul_div_cancel_left t hs0, inv_inv]
    -- Ā(t)A(t) = [(t, c) = 1]、gcd(N, s₀t) = s₀ ⇔ (t, c) = 1
    have hu : A⁻¹ (t : ZMod c) * A (t : ZMod c) =
        if Nat.gcd N (M / c * t) = M / c then 1 else 0 := by
      by_cases htc : t.Coprime c
      · rw [ite_eq_left ((gcd_dual_iff u M N h c hc (NeZero.ne M) hrad t).mpr htc),
          ← MulChar.mul_apply, inv_mul_cancel]
        exact MulChar.one_apply ((ZMod.isUnit_iff_coprime t c).mpr htc)
      · rw [ite_eq_right (fun hg => htc ((gcd_dual_iff u M N h c hc (NeZero.ne M) hrad t).mp hg)),
          MulChar.map_nonunit A⁻¹ (fun hu => htc ((ZMod.isUnit_iff_coprime t c).mp hu)), zero_mul]
    have hm1 : A⁻¹ (-1) * A (-1) = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel]
      exact MulChar.one_apply isUnit_one.neg
    have hs1 : (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ)
        = ((Nat.totient M : ℝ) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_inv]
    rw [hu]
    calc _ = ((((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ)) *
          (((M / c : ℕ) : ℂ) * ((M / c : ℕ) : ℂ)) * (A⁻¹ (-1) * A (-1)) *
          (gaussSum A stdAddChar * gaussSum A⁻¹ stdAddChar) *
          (if Nat.gcd N (M / c * t) = M / c then (1 : ℂ) else 0) := by ring
      _ = _ := by
        rw [hs1, hm1, PAG.Part16.gauss_mul_gauss_inv_eq hA]
        push_cast
        ring
  · rw [ite_eq_right hdvd, ite_eq_right (fun hg => hdvd (by rw [← hg]; exact Nat.gcd_dvd_right N ξ.val)),
      mul_zero]

end PAG.Part205

#print axioms PAG.Part205.dft_geps
#print axioms PAG.Part205.dind_mul
#print axioms PAG.Part205.geps_conv_geps
#print axioms PAG.Part205.sum_dind
#print axioms PAG.Part205.dft_delta
#print axioms PAG.Part205.sum_geps
#print axioms PAG.Part205.sum_geps_conv
#print axioms PAG.Part205.sum_moebius_dvd
#print axioms PAG.Part205.dft_ball
#print axioms PAG.Part205.geps_eq_balls
#print axioms PAG.Part205.card_dsh
#print axioms PAG.Part205.geps_apply_zero
#print axioms PAG.Part205.coprime_mul_of_rad
#print axioms PAG.Part205.gcd_dual_iff
#print axioms PAG.Part205.dft_gket_ne_zero_iff
#print axioms PAG.Part205.dft_gket_eq_dind_mul
#print axioms PAG.Part205.geps_conv_gket_self
#print axioms PAG.Part205.geps_conv_gket_ne
#print axioms PAG.Part205.geps_conv_gket_spread
#print axioms PAG.Part205.gket_mem_iff
#print axioms PAG.Part205.conj_mul_dft_gket
#print axioms PAG.Part205.adjoint_mul_gket
#print axioms PAG.Part205.norm_conv_gket_le
#print axioms PAG.Part205.norm_conv_gket_eq_of_mem
#print axioms PAG.Part205.conv_gket_eq_zero_of_perp
#print axioms PAG.Part205.thmB_geps
