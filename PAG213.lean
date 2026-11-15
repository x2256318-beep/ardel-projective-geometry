/-
  PAG 2.0 Part 209（2026-10-24）— ケット基底のグラム行列（ブロックの中）とケットの大きさ
  ケット k_u = |u, χ⟩_N（χ は法 c の指標、M = N/u、s₀ = M/c）、B_u = kcoef(M, c, χ)
  1. ケットの大きさ：‖|u, χ⟩‖² = s₀·φ(c)/φ(M)（χ は法 c のどの指標でもよい。Part 205 の残る問い）
     数え上げ：Σ_{t ∣ u, (t,c)=1} φ((u/t)c) = u·φ(c)（法 uc の元を gcd(uc, x) で分ける）
  2. ブロックの中のグラム行列（同じ (c, χ)、χ 原始的）：
     ⟨k_u, k_u′⟩ = Σ_{t ∣ u, (t,c)=1} conj(B_u χ̄(t))·[s₀′ ∣ s₀t, s₀t/s₀′ ∣ u′]·B_u′ χ̄(s₀t/s₀′)·φ((u/t)c)/N
     = conj(B_u)·B_u′/N · Σ_{v ∣ gcd(u,u′)} χ(u/v)·χ̄(u′/v)·φ(vc)
     球のブロック（c = 1）：⟨|u, 1⟩, |u′, 1⟩⟩ = M·M′·gcd(u, u′)/(√φ(M)·√φ(M′)·N)
  3. ブロックの数え上げ：(u ∣ N、c ∣ N/u) ⇔ (c ∣ N、u ∣ N/c)、Σ_{c ∣ N} #原始(c)·d(N/c) = N
  4. スミス型の行列式：A_χ(u, u′) = Σ_{v ∣ gcd(u,u′)} χ(u/v)χ̄(u′/v)φ(vc)（u, u′ ∣ L）は X_χ·diag(φ(vc))·X_χ*
     （X_χ(u, v) = [v ∣ u]χ(u/v) は下三角で対角成分 1）なので det A_χ = ∏_{v ∣ L} φ(vc)。
     c = 1 はスミスの行列式 det(gcd(u, u′))_{u,u′ ∣ L} = ∏_{v ∣ L} φ(v)。
     ブロックのグラム行列は G = diag(conj(B_u)/N)·A_χ·diag(B_u) で、det G = ∏_u (|B_u|²/N)·∏_{v ∣ N/c} φ(vc)
-/
import PAG212
import Mathlib.LinearAlgebra.Matrix.Block

namespace PAG.Part213

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

/-- **0a.** conj(χ̄(x)) = χ(x)。 -/
theorem conj_inv_apply {c : ℕ} [NeZero c] (χ : DirichletCharacter ℂ c) (x : ZMod c) :
    starRingEnd ℂ (χ⁻¹ x) = χ x := by
  rw [starRingEnd_apply, MulChar.star_apply', inv_inv]

/-- **0b.** Σ_{z mod c} |χ(z)|² = φ(c)（χ は法 c のどの指標でもよい）。 -/
theorem sum_normSq_char (c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) :
    ∑ z : ZMod c, (Complex.normSq (χ z) : ℂ) = (Nat.totient c : ℂ) := by
  have e : ∀ z : ZMod c, (Complex.normSq (χ z) : ℂ) = (χ⁻¹ * χ) z := by
    intro z
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply, MulChar.star_apply', MulChar.mul_apply]
  rw [Finset.sum_congr rfl (fun z _ => e z), inv_mul_cancel, MulChar.sum_one_eq_card_units,
    ZMod.card_units_eq_totient]

/-- **0c.** c ∣ M なら Σ_{y mod M} |χ(y mod c)|² = (M/c)·φ(c)。 -/
theorem sum_normSq_char_comp (c M : ℕ) [NeZero c] [NeZero M] (hc : c ∣ M) (χ : DirichletCharacter ℂ c) :
    ∑ y : ZMod M, (Complex.normSq (χ (ZMod.castHom hc (ZMod c) y)) : ℂ) =
      ((M / c : ℕ) : ℂ) * (Nat.totient c : ℂ) := by
  have e := PAG.Part17.sum_comp_surj (ZMod.castHom hc (ZMod c)).toAddMonoidHom (ZMod.ringHom_surjective _)
    (fun z => (Complex.normSq (χ z) : ℂ))
  have hk := PAG.Part201.card_ker_cast (N := c) (N' := M) hc
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hkc : ((Finset.univ.filter (fun z : ZMod M => (ZMod.castHom hc (ZMod c)).toAddMonoidHom z = 0)).card : ℂ)
      = ((M / c : ℕ) : ℂ) := by
    rw [Nat.cast_div hc hc0, eq_div_iff hc0]
    exact hk
  calc ∑ y : ZMod M, (Complex.normSq (χ (ZMod.castHom hc (ZMod c) y)) : ℂ)
      = ∑ y : ZMod M, (fun z => (Complex.normSq (χ z) : ℂ)) ((ZMod.castHom hc (ZMod c)).toAddMonoidHom y) := rfl
    _ = _ := e
    _ = ((M / c : ℕ) : ℂ) * (Nat.totient c : ℂ) := by
        rw [hkc, sum_normSq_char c χ]

/-! ### 1. ケットの大きさと数え上げ -/

/-- **1a. ケットの大きさ**：‖|u, χ⟩‖² = s₀·φ(c)/φ(M)（s₀ = M/c。χ は法 c のどの指標でもよい）。 -/
theorem normSq_gket_eq (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) :
    ∑ x, Complex.normSq (gket u M N h c hc χ x) = ((M / c : ℕ) : ℝ) * Nat.totient c / Nat.totient M := by
  have hMZ := neZero_of_mul h
  rw [sum_normSq_gket u M N h c hc χ]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum]
  have hsum : ∑ y : ZMod M, Complex.normSq (χ (ZMod.castHom hc (ZMod c) y)) =
      ((M / c : ℕ) : ℝ) * Nat.totient c := by
    apply Complex.ofReal_injective
    push_cast
    exact sum_normSq_char_comp c M hc χ
  rw [hsum, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), inv_mul_eq_div]

/-- **1b. 数え上げ**：Σ_{t ∣ u, (t,c)=1} φ((u/t)·c) = u·φ(c)
（法 uc の元 x で x mod c が単数のものを、gcd(uc, x) = t で分ける）。 -/
theorem sum_totient_coprime (u c : ℕ) (hu : u ≠ 0) (hc : c ≠ 0) :
    ∑ t ∈ u.divisors.filter (fun t => t.Coprime c), Nat.totient (u / t * c) = u * Nat.totient c := by
  have : NeZero (u * c) := ⟨mul_ne_zero hu hc⟩
  have : NeZero c := ⟨hc⟩
  have hcuc : c ∣ u * c := dvd_mul_left c u
  -- x mod c が単数 ⇔ x.val と c が互いに素
  have hunit : ∀ x : ZMod (u * c), IsUnit (ZMod.castHom hcuc (ZMod c) x) ↔ x.val.Coprime c := by
    intro x
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.isUnit_iff_coprime]
  -- 個数 = u·φ(c)
  have hS : ((Finset.univ.filter (fun x : ZMod (u * c) => x.val.Coprime c)).card : ℂ) = (u : ℂ) * Nat.totient c := by
    have e := PAG.Part17.sum_comp_surj (ZMod.castHom hcuc (ZMod c)).toAddMonoidHom (ZMod.ringHom_surjective _)
      (fun z => (1 : DirichletCharacter ℂ c) z)
    have hk := PAG.Part201.card_ker_cast (N := c) (N' := u * c) hcuc
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hku : ((Finset.univ.filter (fun z : ZMod (u * c) =>
        (ZMod.castHom hcuc (ZMod c)).toAddMonoidHom z = 0)).card : ℂ) = (u : ℂ) := by
      apply mul_right_cancel₀ hc0
      rw [hk]
      push_cast
      ring
    rw [Finset.natCast_card_filter]
    calc ∑ x : ZMod (u * c), (if x.val.Coprime c then (1 : ℂ) else 0)
        = ∑ x : ZMod (u * c), (fun z => (1 : DirichletCharacter ℂ c) z)
            ((ZMod.castHom hcuc (ZMod c)).toAddMonoidHom x) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          show (if x.val.Coprime c then (1 : ℂ) else 0) = (1 : DirichletCharacter ℂ c) (ZMod.castHom hcuc (ZMod c) x)
          by_cases hx : x.val.Coprime c
          · rw [ite_eq_left hx, MulChar.one_apply ((hunit x).mpr hx)]
          · rw [ite_eq_right hx, MulChar.map_nonunit _ (fun h' => hx ((hunit x).mp h'))]
      _ = _ := e
      _ = (u : ℂ) * Nat.totient c := by
          rw [hku, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  -- gcd(uc, x) で分ける
  have hfib : (Finset.univ.filter (fun x : ZMod (u * c) => x.val.Coprime c)).card =
      ∑ t ∈ u.divisors.filter (fun t => t.Coprime c),
        (Finset.univ.filter (fun x : ZMod (u * c) => Nat.gcd (u * c) x.val = t)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : ZMod (u * c) => Nat.gcd (u * c) x.val)
      (t := u.divisors.filter (fun t => t.Coprime c))]
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      have htc : t.Coprime c := (Finset.mem_filter.mp ht).2
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hx⟩
        exact hx
      · intro hx
        refine ⟨?_, hx⟩
        have h1 : Nat.gcd x.val c ∣ t := by
          rw [← hx]
          exact Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_right _ _) hcuc) (Nat.gcd_dvd_left _ _)
        have h2 : Nat.gcd x.val c ∣ Nat.gcd t c := Nat.dvd_gcd h1 (Nat.gcd_dvd_right _ _)
        rw [Nat.Coprime.gcd_eq_one htc] at h2
        exact Nat.dvd_one.mp h2
    · intro x hx
      have hx' : x.val.Coprime c := (Finset.mem_filter.mp hx).2
      have hgc : (Nat.gcd (u * c) x.val).Coprime c := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hx'
      have hgu : Nat.gcd (u * c) x.val ∣ u := Nat.Coprime.dvd_of_dvd_mul_right hgc (Nat.gcd_dvd_left _ _)
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hgu, hu⟩, hgc⟩
  have hfib' : ∑ t ∈ u.divisors.filter (fun t => t.Coprime c),
      (Finset.univ.filter (fun x : ZMod (u * c) => Nat.gcd (u * c) x.val = t)).card =
      ∑ t ∈ u.divisors.filter (fun t => t.Coprime c), Nat.totient (u / t * c) := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have htu : t ∣ u := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ht).1
    rw [card_dsh (u * c) t (dvd_mul_of_dvd_left htu c), Nat.div_mul_right_comm htu]
  have key : ((∑ t ∈ u.divisors.filter (fun t => t.Coprime c), Nat.totient (u / t * c) : ℕ) : ℂ) =
      ((u * Nat.totient c : ℕ) : ℂ) := by
    rw [← hfib', ← hfib, hS]
    push_cast
    ring
  exact_mod_cast key

/-! ### 2. ブロックの中のグラム行列 -/

/-- **2a. グラム行列（t の形）**：同じ (c, χ) の 2 つのケットについて
⟨|u, χ⟩, |u′, χ⟩⟩ = Σ_{t ∣ u, (t,c)=1} conj(B·χ̄(t))·[s₀′ ∣ s₀t, s₀t/s₀′ ∣ u′]·B′·χ̄(s₀t/s₀′)·φ((u/t)c)/N。 -/
theorem inner_gket_block (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (u' M' : ℕ) (h' : u' * M' = N) (hc' : c ∣ M') :
    ∑ x, starRingEnd ℂ (gket u M N h c hc χ x) * gket u' M' N h' c hc' χ x =
      ∑ t ∈ u.divisors.filter (fun t => t.Coprime c),
        starRingEnd ℂ (kcoef M c χ * χ⁻¹ (t : ZMod c)) *
          (if M' / c ∣ M / c * t ∧ M / c * t / (M' / c) ∣ u' then
            kcoef M' c χ * χ⁻¹ ((M / c * t / (M' / c) : ℕ) : ZMod c) *
              ((Nat.totient (u / t * c) : ℂ) / N)
          else 0) := by
  rw [gket_eq_sum_gbas u M N h c hc χ hχ, inner_sum_smul_left]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have htu : t ∣ u := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ht).1
  rw [inner_gbas_gket (M / c * t) (u / t * c) N (shell_eq h hc htu) _ u' M' h' c hc' χ hχ,
    liftc_of_dvd χ⁻¹ (dvd_mul_left c (u / t)), ite_eq_left rfl]

/-- **2b. グラム行列（v の形）**：⟨|u, χ⟩, |u′, χ⟩⟩ = conj(B)·B′/N · Σ_{v ∣ gcd(u,u′)} χ(u/v)·χ̄(u′/v)·φ(vc)。 -/
theorem inner_gket_block_gcd (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (u' M' : ℕ) (h' : u' * M' = N) (hc' : c ∣ M') :
    ∑ x, starRingEnd ℂ (gket u M N h c hc χ x) * gket u' M' N h' c hc' χ x =
      starRingEnd ℂ (kcoef M c χ) * kcoef M' c χ / N *
        ∑ v ∈ (Nat.gcd u u').divisors,
          χ ((u / v : ℕ) : ZMod c) * χ⁻¹ ((u' / v : ℕ) : ZMod c) * (Nat.totient (v * c) : ℂ) := by
  have hMZ := neZero_of_mul h
  have hM'Z := neZero_of_mul h'
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hu0 : u ≠ 0 := (pos_of_mul h).ne'
  have hs0' : 0 < M' / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M')) hc') hc0
  have hL : M / c * u = M' / c * u' := Nat.eq_of_mul_eq_mul_right hc0 (by
    rw [show M / c * u * c = u * (M / c * c) by ring, Nat.div_mul_cancel hc, h,
      show M' / c * u' * c = u' * (M' / c * c) by ring, Nat.div_mul_cancel hc', h'])
  rw [inner_gket_block u M N h c hc χ hχ u' M' h' hc', Finset.sum_filter, ← Nat.sum_div_divisors]
  have hterm : ∀ v ∈ u.divisors,
      (if (u / v).Coprime c then
        starRingEnd ℂ (kcoef M c χ * χ⁻¹ ((u / v : ℕ) : ZMod c)) *
          (if M' / c ∣ M / c * (u / v) ∧ M / c * (u / v) / (M' / c) ∣ u' then
            kcoef M' c χ * χ⁻¹ ((M / c * (u / v) / (M' / c) : ℕ) : ZMod c) *
              ((Nat.totient (u / (u / v) * c) : ℂ) / N)
          else 0)
      else 0) =
      if v ∣ u' then
        starRingEnd ℂ (kcoef M c χ) * kcoef M' c χ / N *
          (χ ((u / v : ℕ) : ZMod c) * χ⁻¹ ((u' / v : ℕ) : ZMod c) * (Nat.totient (v * c) : ℂ))
      else 0 := by
    intro v hv
    have hv' : v ∣ u := Nat.dvd_of_mem_divisors hv
    have hvL : v ∣ M' / c * u' := by rw [← hL]; exact dvd_mul_of_dvd_right hv' _
    have hq : M / c * (u / v) = M' / c * u' / v := by rw [← Nat.mul_div_assoc _ hv', hL]
    rw [hq, Nat.div_div_self hv' hu0]
    by_cases hcop : (u / v).Coprime c
    · rw [ite_eq_left hcop]
      by_cases hvu' : v ∣ u'
      · have hd1 : M' / c ∣ M' / c * u' / v := (dvd_div_iff_dvd _ _ _ hs0' hvL).mpr hvu'
        have hq2 : M' / c * u' / v / (M' / c) = u' / v := mul_div_div_cancel _ _ _ hs0' hvu'
        rw [hq2, ite_eq_left (And.intro hd1 (Nat.div_dvd_of_dvd hvu')), ite_eq_left hvu', map_mul,
          conj_inv_apply]
        ring
      · rw [ite_eq_right (fun hh => hvu' ((dvd_div_iff_dvd _ _ _ hs0' hvL).mp hh.1)), ite_eq_right hvu',
          mul_zero]
    · have h0 : χ ((u / v : ℕ) : ZMod c) = 0 :=
        MulChar.map_nonunit _ (fun hh => hcop ((ZMod.isUnit_iff_coprime _ _).mp hh))
      rw [ite_eq_right hcop]
      split_ifs <;> simp [h0]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext v
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨hvu, _⟩, hvu'⟩
    exact ⟨⟨hvu, hvu'⟩, (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hu0)).ne'⟩
  · rintro ⟨⟨hvu, hvu'⟩, _⟩
    exact ⟨⟨hvu, hu0⟩, hvu'⟩

/-- **2c. 球のブロック**（c = 1）：⟨|u, 1⟩, |u′, 1⟩⟩ = M·M′·gcd(u, u′)/(√φ(M)·√φ(M′)·N)。 -/
theorem inner_gket_ball (u M N : ℕ) [NeZero N] (h : u * M = N) (u' M' : ℕ) (h' : u' * M' = N) :
    ∑ x, starRingEnd ℂ (gket u M N h 1 (one_dvd M) (1 : DirichletCharacter ℂ 1) x) *
        gket u' M' N h' 1 (one_dvd M') (1 : DirichletCharacter ℂ 1) x =
      (M : ℂ) * M' * (Nat.gcd u u' : ℂ) /
        (((Real.sqrt (Nat.totient M) : ℝ) : ℂ) * ((Real.sqrt (Nat.totient M') : ℝ) : ℂ) * N) := by
  have hMZ := neZero_of_mul h
  have hM'Z := neZero_of_mul h'
  have hφ : ∀ m : ℕ, m ≠ 0 → ((Real.sqrt (Nat.totient m) : ℝ) : ℂ) ≠ 0 := by
    intro m hm
    have : (0 : ℝ) < Real.sqrt (Nat.totient m) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm))
    exact_mod_cast this.ne'
  have hk : ∀ m : ℕ, kcoef m 1 (1 : DirichletCharacter ℂ 1) = (m : ℂ) / ((Real.sqrt (Nat.totient m) : ℝ) : ℂ) := by
    intro m
    unfold kcoef
    rw [chi_level_one, gaussSum_level_one, Nat.div_one, Complex.ofReal_inv]
    ring
  have hsum : ∑ v ∈ (Nat.gcd u u').divisors,
      (1 : DirichletCharacter ℂ 1) ((u / v : ℕ) : ZMod 1) * (1 : DirichletCharacter ℂ 1)⁻¹ ((u' / v : ℕ) : ZMod 1) *
        (Nat.totient (v * 1) : ℂ) = (Nat.gcd u u' : ℂ) := by
    simp only [chi_level_one, one_mul, mul_one]
    exact_mod_cast Nat.sum_totient (Nat.gcd u u')
  rw [inner_gket_block_gcd u M N h 1 (one_dvd M) 1 DirichletCharacter.isPrimitive_one_level_one u' M' h'
    (one_dvd M'), hsum, hk M, hk M', map_div₀, Complex.conj_ofReal, map_natCast]
  field_simp

/-! ### 3. ブロックの数え上げ -/

/-- **3a.** (u ∣ N かつ c ∣ N/u) ⇔ (c ∣ N かつ u ∣ N/c)（N ≠ 0）。ブロック (c, χ) のケットの番号 u は N/c の約数。 -/
theorem mem_block_iff (N u c : ℕ) (hN : N ≠ 0) :
    (u ∈ N.divisors ∧ c ∈ (N / u).divisors) ↔ (c ∈ N.divisors ∧ u ∈ (N / c).divisors) := by
  have key : ∀ a b : ℕ, (a ∈ N.divisors ∧ b ∈ (N / a).divisors) ↔ a * b ∣ N := by
    intro a b
    simp only [Nat.mem_divisors]
    constructor
    · rintro ⟨⟨ha, _⟩, hb, _⟩
      exact (Nat.dvd_div_iff_mul_dvd ha).mp hb
    · intro hab
      have ha : a ∣ N := dvd_of_mul_right_dvd hab
      refine ⟨⟨ha, hN⟩, (Nat.dvd_div_iff_mul_dvd ha).mpr hab, ?_⟩
      intro h0
      have := Nat.mul_div_cancel' ha
      rw [h0, mul_zero] at this
      exact hN this.symm
  rw [key u c, key c u, mul_comm]

/-- **3b. ブロックの数え上げ**：Σ_{c ∣ N} #{法 c の原始指標}·d(N/c) = N
（ブロック (c, χ) の大きさは d(N/c)。Part 207 の個数 N のブロックごとの数え直し）。 -/
theorem sum_card_primitive_mul_card_divisors (N : ℕ) [NeZero N] :
    ∑ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} * (N / c).divisors.card = N := by
  have hN : N ≠ 0 := NeZero.ne N
  calc ∑ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} * (N / c).divisors.card
      = ∑ c ∈ N.divisors, ∑ u ∈ (N / c).divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ u ∈ N.divisors, ∑ c ∈ (N / u).divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} :=
        Finset.sum_comm' (fun c u => by rw [← mem_block_iff N u c hN]; exact and_comm)
    _ = ∑ u ∈ N.divisors, Nat.totient (N / u) := by
        refine Finset.sum_congr rfl (fun u hu => ?_)
        have hu' : u ∣ N := Nat.dvd_of_mem_divisors hu
        have : NeZero (N / u) := ⟨fun h0 => hN (by
          have := Nat.mul_div_cancel' hu'
          rw [h0, mul_zero] at this
          exact this.symm)⟩
        exact sum_card_primitive (N / u)
    _ = N := sum_totient_div N

/-! ### 4. ブロックのグラム行列の行列式（スミス型） -/

/-- 三角行列 X_χ(u, v) = [v ∣ u]·χ(u/v)（u, v は L の約数）。 -/
noncomputable def blockX (L c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) : Matrix L.divisors L.divisors ℂ :=
  Matrix.of fun u v => if (v : ℕ) ∣ u then χ (((u : ℕ) / v : ℕ) : ZMod c) else 0

/-- A_χ(u, u′) = Σ_{v ∣ gcd(u,u′)} χ(u/v)·χ̄(u′/v)·φ(vc)（u, u′ は L の約数）。 -/
noncomputable def blockA (L c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) : Matrix L.divisors L.divisors ℂ :=
  Matrix.of fun u u' => ∑ v ∈ (Nat.gcd (u : ℕ) u').divisors,
    χ (((u : ℕ) / v : ℕ) : ZMod c) * χ⁻¹ (((u' : ℕ) / v : ℕ) : ZMod c) * (Nat.totient (v * c) : ℂ)

/-- **4a.** A_χ = X_χ·diag(φ(vc))·X_χ*（L ≠ 0）。 -/
theorem blockA_eq (L c : ℕ) [NeZero c] (hL : L ≠ 0) (χ : DirichletCharacter ℂ c) :
    blockA L c χ = blockX L c χ * Matrix.diagonal (fun v : L.divisors => (Nat.totient ((v : ℕ) * c) : ℂ)) *
      (blockX L c χ).conjTranspose := by
  ext u u'
  rw [Matrix.mul_apply]
  simp only [blockA, blockX, Matrix.of_apply, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  have hg : (Nat.gcd (u : ℕ) u').divisors = L.divisors.filter (fun v => v ∣ Nat.gcd (u : ℕ) u') := by
    ext v
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hv, _⟩
      exact ⟨⟨dvd_trans hv (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_of_mem_divisors u.2)), hL⟩, hv⟩
    · rintro ⟨_, hv⟩
      exact ⟨hv, (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_mem_divisors u.2)).ne'⟩
  rw [hg, Finset.sum_filter, ← Finset.sum_coe_sort L.divisors]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases h1 : (v : ℕ) ∣ u
  · by_cases h2 : (v : ℕ) ∣ u'
    · rw [ite_eq_left (Nat.dvd_gcd h1 h2), ite_eq_left h1, ite_eq_left h2, MulChar.star_apply']
      ring
    · rw [ite_eq_right (fun hh => h2 (dvd_trans hh (Nat.gcd_dvd_right _ _))), ite_eq_right h2, star_zero,
        mul_zero]
  · rw [ite_eq_right (fun hh => h1 (dvd_trans hh (Nat.gcd_dvd_left _ _))), ite_eq_right h1, zero_mul, zero_mul]

/-- **4b.** X_χ は下三角で対角成分は 1：det X_χ = 1。 -/
theorem det_blockX (L c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) : (blockX L c χ).det = 1 := by
  have hlow : (blockX L c χ).IsLowerTriangular := by
    intro i j hij
    have hij' : (i : ℕ) < j := by simpa using hij
    simp only [blockX, Matrix.of_apply]
    exact ite_eq_right (fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_mem_divisors i.2) hd) (not_le.mpr hij'))
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  refine Finset.prod_eq_one (fun i _ => ?_)
  simp only [blockX, Matrix.of_apply]
  rw [ite_eq_left (dvd_refl _), Nat.div_self (Nat.pos_of_mem_divisors i.2), Nat.cast_one, map_one]

/-- **4c. スミス型の行列式**：det A_χ = ∏_{v ∣ L} φ(vc)（L ≠ 0）。 -/
theorem det_blockA (L c : ℕ) [NeZero c] (hL : L ≠ 0) (χ : DirichletCharacter ℂ c) :
    (blockA L c χ).det = ∏ v ∈ L.divisors, (Nat.totient (v * c) : ℂ) := by
  rw [blockA_eq L c hL χ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, det_blockX, star_one,
    Matrix.det_diagonal, one_mul, mul_one]
  exact Finset.prod_coe_sort L.divisors (fun v => (Nat.totient (v * c) : ℂ))

/-- **4d. スミスの行列式**（c = 1）：det(gcd(u, u′))_{u, u′ ∣ L} = ∏_{v ∣ L} φ(v)。 -/
theorem smith_det (L : ℕ) (hL : L ≠ 0) :
    (Matrix.of fun u u' : L.divisors => (Nat.gcd (u : ℕ) u' : ℂ)).det = ∏ v ∈ L.divisors, (Nat.totient v : ℂ) := by
  have e : (Matrix.of fun u u' : L.divisors => (Nat.gcd (u : ℕ) u' : ℂ)) =
      blockA L 1 (1 : DirichletCharacter ℂ 1) := by
    ext u u'
    simp only [blockA, Matrix.of_apply, chi_level_one, one_mul, mul_one]
    exact_mod_cast (Nat.sum_totient (Nat.gcd (u : ℕ) u')).symm
  rw [e, det_blockA L 1 hL 1]
  simp only [mul_one]

/-- **4e.** ブロック (c, χ) の番号：c ∣ N、u ∣ N/c なら u ∣ N かつ c ∣ N/u。 -/
theorem block_dvd {N c u : ℕ} (hcN : c ∣ N) (hu : u ∣ N / c) : u ∣ N ∧ c ∣ N / u := by
  have h1 : c * u ∣ N := (Nat.dvd_div_iff_mul_dvd hcN).mp hu
  have h2 : u ∣ N := dvd_of_mul_left_dvd h1
  exact ⟨h2, (Nat.dvd_div_iff_mul_dvd h2).mpr (by rw [mul_comm]; exact h1)⟩

/-- ブロック (c, χ) のグラム行列：G(u, u′) = ⟨|u, χ⟩, |u′, χ⟩⟩（u, u′ は N/c の約数）。 -/
noncomputable def blockGram (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) :
    Matrix (N / c).divisors (N / c).divisors ℂ :=
  Matrix.of fun u u' =>
    ∑ x, starRingEnd ℂ (gket u (N / u) N (Nat.mul_div_cancel' (block_dvd hcN (Nat.dvd_of_mem_divisors u.2)).1) c
        (block_dvd hcN (Nat.dvd_of_mem_divisors u.2)).2 χ x) *
      gket u' (N / u') N (Nat.mul_div_cancel' (block_dvd hcN (Nat.dvd_of_mem_divisors u'.2)).1) c
        (block_dvd hcN (Nat.dvd_of_mem_divisors u'.2)).2 χ x

/-- **4f.** G = diag(conj(B_u)/N)·A_χ·diag(B_u)（χ 原始的、B_u = kcoef(N/u, c, χ)）。 -/
theorem blockGram_eq (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    blockGram N c hcN χ =
      Matrix.diagonal (fun u : (N / c).divisors => starRingEnd ℂ (kcoef (N / u) c χ) / N) *
        blockA (N / c) c χ * Matrix.diagonal (fun u : (N / c).divisors => kcoef (N / u) c χ) := by
  ext u u'
  simp only [blockGram, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, blockA]
  rw [inner_gket_block_gcd u (N / u) N _ c _ χ hχ u' (N / u') _ _]
  ring

/-- **4g. グラム行列の行列式**：det G = ∏_u (|B_u|²/N)·∏_{v ∣ N/c} φ(vc)。 -/
theorem det_blockGram (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    (blockGram N c hcN χ).det =
      (∏ u : (N / c).divisors, starRingEnd ℂ (kcoef (N / u) c χ) * kcoef (N / u) c χ / N) *
        ∏ v ∈ (N / c).divisors, (Nat.totient (v * c) : ℂ) := by
  have hL : N / c ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hcN)
    (Nat.pos_of_ne_zero (NeZero.ne c))).ne'
  rw [blockGram_eq N c hcN χ hχ, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    det_blockA (N / c) c hL χ, mul_right_comm, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl (fun u _ => by ring)

end PAG.Part213

#print axioms PAG.Part213.conj_inv_apply
#print axioms PAG.Part213.sum_normSq_char
#print axioms PAG.Part213.sum_normSq_char_comp
#print axioms PAG.Part213.normSq_gket_eq
#print axioms PAG.Part213.sum_totient_coprime
#print axioms PAG.Part213.inner_gket_block
#print axioms PAG.Part213.inner_gket_block_gcd
#print axioms PAG.Part213.inner_gket_ball
#print axioms PAG.Part213.mem_block_iff
#print axioms PAG.Part213.sum_card_primitive_mul_card_divisors
#print axioms PAG.Part213.blockX
#print axioms PAG.Part213.blockA
#print axioms PAG.Part213.blockA_eq
#print axioms PAG.Part213.det_blockX
#print axioms PAG.Part213.det_blockA
#print axioms PAG.Part213.smith_det
#print axioms PAG.Part213.block_dvd
#print axioms PAG.Part213.blockGram
#print axioms PAG.Part213.blockGram_eq
#print axioms PAG.Part213.det_blockGram
