/-
  PAG 2.0 Part 205（2026-10-24）— 一般のケットの双対殻への分解（Part 204 の基底による展開）
  k = |u, χ⟩_N（χ は法 c の原始指標、M = N/u、s₀ = M/c）、B = φ(M)^(−1/2)·s₀·χ̄(−1)·τ(χ)（def kcoef）
  1. 成分：t ∣ u なら ε_{s₀t} ⋆ k = B·χ̄(t)·g_{s₀t, χ̄′_t}（χ̄′_t は χ⁻¹ を法 n_t = (u/t)·c へ持ち上げたもの。(t, c) ≠ 1 なら 0）
  2. それ以外の双対殻の成分は 0。ε_s ⋆ k ≠ 0 ⇔ s = s₀t（t ∣ u、(t, c) = 1）。0 でない成分の個数 = #{t}
  3. 展開：k = Σ_{t ∣ u, (t,c)=1} B·χ̄(t)·g_{s₀t, χ̄′_t}
  4. 大きさ：‖ε_{s₀t} ⋆ k‖² = (s₀²c/φ(M))·φ((u/t)c)/N、ピタゴラス ‖k‖² = Σ_t ‖ε_{s₀t} ⋆ k‖²
  5. 旧部分（ℤ/NT、P = oldP N T）：P k = Σ_{T ∣ s₀t} 成分、k − P k = Σ_{T ∤ s₀t} 成分（Part 202 の残る問いの答え）
  6. 細かいケットとの関係：ε_{s₀t} ⋆ |u, χ⟩ = (√φ(Mt)/(√φ(M)·t))·χ̄(t)·ε_{s₀t} ⋆ |u/t, χ⟩
-/
import PAG208

namespace PAG.Part209

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 係数と殻の等式 -/

/-- ケットのフーリエ係数 B = φ(M)^(−1/2)·(M/c)·χ̄(−1)·τ(χ)（Part 198 の `dft_gket_apply` の係数）。 -/
noncomputable def kcoef (M c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) : ℂ :=
  (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * ((M / c : ℕ) : ℂ) * χ⁻¹ (-1) * gaussSum χ stdAddChar

/-- **0a.** 𝓕k(ξ) = [s₀ ∣ ξ]·B·χ̄(ξ/s₀)（`dft_gket_apply` を kcoef で書いたもの）。 -/
theorem dft_gket_apply' (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (ξ : ZMod N) :
    𝓕 (gket u M N h c hc χ) ξ =
      if M / c ∣ ξ.val then kcoef M c χ * χ⁻¹ ((ξ.val / (M / c) : ℕ) : ZMod c) else 0 :=
  dft_gket_apply u M N h c hc χ hχ ξ

/-- **0b.** B ≠ 0。 -/
theorem kcoef_ne_zero (M c : ℕ) [NeZero c] (hM : M ≠ 0) (hc : c ∣ M) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : kcoef M c χ ≠ 0 := by
  have hφ : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hM))
  have hs0 : M / c ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hc) (Nat.pos_of_ne_zero (NeZero.ne c))).ne'
  unfold kcoef
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (PAG.Part16.gaussSum_ne_zero hχ)
  · exact_mod_cast (inv_pos.mpr hφ).ne'
  · exact_mod_cast hs0
  · exact ((isUnit_one.neg).map χ⁻¹).ne_zero

/-- **0c.** |B|² = s₀²c/φ(M)。 -/
theorem normSq_kcoef (M c : ℕ) [NeZero c] (hM : M ≠ 0) (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    Complex.normSq (kcoef M c χ) = ((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M := by
  have hφM : (0 : ℝ) < Nat.totient M := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hM)
  have hm1 : ((-1 : (ZMod c)ˣ) : ZMod c) = -1 := by simp
  unfold kcoef
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul, ← hm1, normSq_chi_unit χ⁻¹ (-1),
    PAG.Part16.normSq_gaussSum hχ, Complex.normSq_ofReal, Complex.normSq_natCast]
  have hs : Real.sqrt (Nat.totient M) * Real.sqrt (Nat.totient M) = Nat.totient M :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [← mul_inv, hs]
  field_simp

/-- **0d.** 殻の等式 (s₀t)·((u/t)c) = N（t ∣ u）。 -/
theorem shell_eq {u M N c t : ℕ} [NeZero N] (h : u * M = N) (hc : c ∣ M) (ht : t ∣ u) :
    M / c * t * (u / t * c) = N := by
  obtain ⟨w, rfl⟩ := ht
  have ht0 : 0 < t := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, zero_mul, zero_mul] at h; exact NeZero.ne N h.symm)
  rw [Nat.mul_div_cancel_left w ht0, ← h, show M / c * t * (w * c) = t * w * (M / c * c) by ring,
    Nat.div_mul_cancel hc]

/-- **0e.** 細かいケットの等式 (u/t)·(Mt) = N（t ∣ u）。 -/
theorem fine_eq {u M N t : ℕ} [NeZero N] (h : u * M = N) (ht : t ∣ u) : u / t * (M * t) = N := by
  obtain ⟨w, rfl⟩ := ht
  have ht0 : 0 < t := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, zero_mul, zero_mul] at h; exact NeZero.ne N h.symm)
  rw [Nat.mul_div_cancel_left w ht0, ← h]
  ring

/-! ### 1. 双対殻ごとの成分 -/

/-- **1a. 成分**：t ∣ u なら ε_{s₀t} ⋆ k = B·χ̄(t)·g_{s₀t, χ̄′_t}（(t, c) ≠ 1 なら両辺とも 0）。 -/
theorem geps_conv_gket_comp (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (t : ℕ) (ht : t ∣ u) :
    PAG.Part15.conv (geps N (M / c * t)) (gket u M N h c hc χ) =
      (kcoef M c χ * χ⁻¹ (t : ZMod c)) •
        gbas (M / c * t) (u / t * c) N ((χ⁻¹).changeLevel (dvd_mul_left c (u / t))) := by
  have hst := shell_eq h hc ht
  have hMZ := neZero_of_mul h
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc)
    (Nat.pos_of_ne_zero (NeZero.ne c))
  have ht0 : 0 < t := Nat.pos_of_dvd_of_pos ht (pos_of_mul h)
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps, map_smul, Pi.smul_apply, smul_eq_mul, dft_gbas_apply,
    dft_gket_apply' u M N h c hc χ hχ ξ]
  by_cases hg : Nat.gcd N ξ.val = M / c * t
  · have hd : M / c * t ∣ ξ.val := by rw [← hg]; exact Nat.gcd_dvd_right N ξ.val
    have hd0 : M / c ∣ ξ.val := (Nat.dvd_mul_right (M / c) t).trans hd
    have hcop : (ξ.val / (M / c * t)).Coprime (u / t * c) :=
      (gcd_eq_iff_coprime _ _ N hst ξ.val hd).mp hg
    have hq : ξ.val / (M / c) = t * (ξ.val / (M / c * t)) := by
      obtain ⟨y, hy⟩ := hd
      rw [hy, Nat.mul_div_cancel_left y (Nat.mul_pos hs0 ht0), mul_assoc, Nat.mul_div_cancel_left _ hs0]
    have h1 : dind N (M / c * t) ξ = 1 := by simp only [dind]; rw [ite_eq_left hg]
    rw [ite_eq_left hd0, ite_eq_left hd, h1, one_mul, hq, Nat.cast_mul, map_mul,
      changeLevel_natCast (dvd_mul_left c (u / t)) χ⁻¹ _ hcop]
    ring
  · have h0 : dind N (M / c * t) ξ = 0 := by simp only [dind]; rw [ite_eq_right hg]
    rw [h0, zero_mul]
    by_cases hd : M / c * t ∣ ξ.val
    · have hnu : ¬ IsUnit ((ξ.val / (M / c * t) : ℕ) : ZMod (u / t * c)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact fun hcop => hg ((gcd_eq_iff_coprime _ _ N hst ξ.val hd).mpr hcop)
      rw [ite_eq_left hd, MulChar.map_nonunit _ hnu, mul_zero]
    · rw [ite_eq_right hd, mul_zero]

/-- **1b.** s がどの s₀t（t ∣ u、(t, c) = 1）とも違えば ε_s ⋆ k = 0。 -/
theorem geps_conv_gket_eq_zero (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (s : ℕ)
    (hs : ∀ t : ℕ, t ∣ u → t.Coprime c → s ≠ M / c * t) :
    PAG.Part15.conv (geps N s) (gket u M N h c hc χ) = 0 := by
  have hN : N = M / c * (u * c) := by
    rw [← h, show M / c * (u * c) = u * (M / c * c) by ring, Nat.div_mul_cancel hc]
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps, map_zero, Pi.zero_apply,
    dft_gket_apply' u M N h c hc χ hχ ξ]
  by_cases hg : Nat.gcd N ξ.val = s
  · by_cases hd : M / c ∣ ξ.val
    · rw [ite_eq_left hd]
      by_cases hu : IsUnit ((ξ.val / (M / c) : ℕ) : ZMod c)
      · exfalso
        have hx : (ξ.val / (M / c)).Coprime c := (ZMod.isUnit_iff_coprime _ _).mp hu
        have hξ : ξ.val = M / c * (ξ.val / (M / c)) := (Nat.mul_div_cancel' hd).symm
        have hgcd : Nat.gcd N ξ.val = M / c * Nat.gcd (u * c) (ξ.val / (M / c)) := by
          have e1 : Nat.gcd N ξ.val = Nat.gcd (M / c * (u * c)) (M / c * (ξ.val / (M / c))) := by
            rw [← hN, ← hξ]
          rw [e1, Nat.gcd_mul_left]
        have htc : (Nat.gcd (u * c) (ξ.val / (M / c))).Coprime c :=
          Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hx
        have htu : Nat.gcd (u * c) (ξ.val / (M / c)) ∣ u :=
          Nat.Coprime.dvd_of_dvd_mul_right htc (Nat.gcd_dvd_left _ _)
        exact hs _ htu htc (hg.symm.trans hgcd)
      · rw [MulChar.map_nonunit _ hu, mul_zero, mul_zero]
    · rw [ite_eq_right hd, mul_zero]
  · have h0 : dind N s ξ = 0 := by simp only [dind]; rw [ite_eq_right hg]
    rw [h0, zero_mul]

/-- **1c. 判定**：ε_s ⋆ k ≠ 0 ⇔ s = s₀t（t ∣ u、(t, c) = 1）。 -/
theorem geps_conv_gket_ne_zero_iff (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (s : ℕ) :
    PAG.Part15.conv (geps N s) (gket u M N h c hc χ) ≠ 0 ↔ ∃ t, t ∣ u ∧ t.Coprime c ∧ s = M / c * t := by
  constructor
  · intro hne
    by_contra hno
    exact hne (geps_conv_gket_eq_zero u M N h c hc χ hχ s (fun t ht htc e => hno ⟨t, ht, htc, e⟩))
  · rintro ⟨t, ht, htc, rfl⟩
    have hMZ := neZero_of_mul h
    rw [geps_conv_gket_comp u M N h c hc χ hχ t ht]
    exact smul_ne_zero (mul_ne_zero (kcoef_ne_zero M c (NeZero.ne M) hc χ hχ)
      (chi_natCast_ne_zero χ⁻¹ t htc)) (gbas_ne_zero _ _ N (shell_eq h hc ht) _)

/-! ### 2. 展開 -/

/-- **2a.** k = Σ_{t ∣ u, (t,c)=1} ε_{s₀t} ⋆ k（0 でない成分だけの和）。 -/
theorem gket_eq_sum_geps_conv (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    gket u M N h c hc χ = ∑ t ∈ u.divisors.filter (fun t => t.Coprime c),
      PAG.Part15.conv (geps N (M / c * t)) (gket u M N h c hc χ) := by
  have hMZ := neZero_of_mul h
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc)
    (Nat.pos_of_ne_zero (NeZero.ne c))
  have hu0 : u ≠ 0 := (pos_of_mul h).ne'
  have himg : (u.divisors.filter (fun t => t.Coprime c)).image (fun t => M / c * t) ⊆ N.divisors := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact Nat.mem_divisors.mpr
      ⟨Dvd.intro _ (shell_eq h hc (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ht).1)), NeZero.ne N⟩
  have hzero : ∀ s ∈ N.divisors, s ∉ (u.divisors.filter (fun t => t.Coprime c)).image (fun t => M / c * t) →
      PAG.Part15.conv (geps N s) (gket u M N h c hc χ) = 0 := by
    intro s _ hs
    apply geps_conv_gket_eq_zero u M N h c hc χ hχ s
    intro t ht htc e
    exact hs (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨ht, hu0⟩, htc⟩, e.symm⟩)
  have hsum := sum_geps_conv N (gket u M N h c hc χ)
  rw [← Finset.sum_subset himg hzero,
    Finset.sum_image (fun t₁ _ t₂ _ e => Nat.eq_of_mul_eq_mul_left hs0 e)] at hsum
  exact hsum.symm

/-- **2b. 展開**：k = Σ_{t ∣ u, (t,c)=1} B·χ̄(t)·g_{s₀t, χ̄′_t}。 -/
theorem gket_eq_sum_gbas (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    gket u M N h c hc χ = ∑ t ∈ u.divisors.filter (fun t => t.Coprime c),
      (kcoef M c χ * χ⁻¹ (t : ZMod c)) •
        gbas (M / c * t) (u / t * c) N ((χ⁻¹).changeLevel (dvd_mul_left c (u / t))) := by
  conv_lhs => rw [gket_eq_sum_geps_conv u M N h c hc χ hχ]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have ht' := Finset.mem_filter.mp ht
  exact geps_conv_gket_comp u M N h c hc χ hχ t (Nat.dvd_of_mem_divisors ht'.1)

open Classical in
/-- **2c.** 0 でない成分の個数は #{t ∣ u : (t, c) = 1}。 -/
theorem card_shells (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    (N.divisors.filter (fun s => PAG.Part15.conv (geps N s) (gket u M N h c hc χ) ≠ 0)).card =
      (u.divisors.filter (fun t => t.Coprime c)).card := by
  have hMZ := neZero_of_mul h
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc)
    (Nat.pos_of_ne_zero (NeZero.ne c))
  have hu0 : u ≠ 0 := (pos_of_mul h).ne'
  have e : N.divisors.filter (fun s => PAG.Part15.conv (geps N s) (gket u M N h c hc χ) ≠ 0) =
      (u.divisors.filter (fun t => t.Coprime c)).image (fun t => M / c * t) := by
    ext s
    rw [Finset.mem_filter, Finset.mem_image, geps_conv_gket_ne_zero_iff u M N h c hc χ hχ s]
    constructor
    · rintro ⟨_, t, ht, htc, rfl⟩
      exact ⟨t, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨ht, hu0⟩, htc⟩, rfl⟩
    · rintro ⟨t, htm, rfl⟩
      have htm' := Finset.mem_filter.mp htm
      have ht := Nat.dvd_of_mem_divisors htm'.1
      exact ⟨Nat.mem_divisors.mpr ⟨Dvd.intro _ (shell_eq h hc ht), NeZero.ne N⟩, t, ht, htm'.2, rfl⟩
  rw [e, Finset.card_image_of_injective _ (fun t₁ t₂ e => Nat.eq_of_mul_eq_mul_left hs0 e)]

/-! ### 3. 大きさ -/

/-- **3a.** 異なる双対殻の成分は直交する：s ≠ s′ なら ⟨ε_s ⋆ f, ε_{s′} ⋆ g⟩ = 0。 -/
theorem inner_geps_conv_ne {N : ℕ} [NeZero N] (s s' : ℕ) (hne : s ≠ s') (f g : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (PAG.Part15.conv (geps N s) f x) * PAG.Part15.conv (geps N s') g x = 0 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hp := PAG.Part39.plancherel (PAG.Part15.conv (geps N s) f) (PAG.Part15.conv (geps N s') g)
  have e : ∑ k, starRingEnd ℂ (𝓕 (PAG.Part15.conv (geps N s) f) k) *
      𝓕 (PAG.Part15.conv (geps N s') g) k = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [PAG.Part16.dft_conv, PAG.Part16.dft_conv, Pi.mul_apply, Pi.mul_apply, dft_geps, dft_geps]
    by_cases hk : Nat.gcd N k.val = s
    · have h0 : dind N s' k = 0 := by
        simp only [dind]; rw [ite_eq_right (fun e => hne (hk.symm.trans e))]
      rw [h0, zero_mul, mul_zero]
    · have h0 : dind N s k = 0 := by simp only [dind]; rw [ite_eq_right hk]
      rw [h0, zero_mul, map_zero, zero_mul]
  rw [e] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left hN

/-- **3b. ピタゴラス**：直交する族では ‖Σ_i v_i‖² = Σ_i ‖v_i‖²。 -/
theorem normSq_sum_orth {N : ℕ} [NeZero N] {ι : Type*} (F : Finset ι) (v : ι → ZMod N → ℂ)
    (horth : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∑ x, starRingEnd ℂ (v i x) * v j x = 0) :
    ∑ x, Complex.normSq (∑ i ∈ F, v i x) = ∑ i ∈ F, ∑ x, Complex.normSq (v i x) := by
  have key : ((∑ x, Complex.normSq (∑ i ∈ F, v i x) : ℝ) : ℂ) =
      ((∑ i ∈ F, ∑ x, Complex.normSq (v i x) : ℝ) : ℂ) := by
    push_cast
    have e1 : ∀ x, ((Complex.normSq (∑ i ∈ F, v i x) : ℝ) : ℂ) =
        ∑ i ∈ F, ∑ j ∈ F, starRingEnd ℂ (v i x) * v j x := by
      intro x
      rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
    have e2 : ∀ i x, ((Complex.normSq (v i x) : ℝ) : ℂ) = starRingEnd ℂ (v i x) * v i x :=
      fun i x => Complex.normSq_eq_conj_mul_self
    simp only [e1, e2]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    conv_lhs => rw [Finset.sum_comm]
    rw [Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji)) (fun h => absurd hi h)]
  exact_mod_cast key

/-- **3c.** 成分の大きさ：‖ε_{s₀t} ⋆ k‖² = (s₀²c/φ(M))·φ((u/t)c)/N。 -/
theorem normSq_comp (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (t : ℕ) (ht : t ∣ u) (htc : t.Coprime c) :
    ∑ x, Complex.normSq (PAG.Part15.conv (geps N (M / c * t)) (gket u M N h c hc χ) x) =
      ((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M * (Nat.totient (u / t * c) / N) := by
  have hMZ := neZero_of_mul h
  have hst := shell_eq h hc ht
  have hg : ((∑ x, Complex.normSq (gbas (M / c * t) (u / t * c) N
      ((χ⁻¹).changeLevel (dvd_mul_left c (u / t))) x) : ℝ) : ℂ) = (Nat.totient (u / t * c) : ℂ) / N := by
    push_cast
    simp only [Complex.normSq_eq_conj_mul_self]
    exact inner_gbas_self _ _ N hst _
  have hg' : ∑ x, Complex.normSq (gbas (M / c * t) (u / t * c) N
      ((χ⁻¹).changeLevel (dvd_mul_left c (u / t))) x) = (Nat.totient (u / t * c) : ℝ) / N := by
    apply Complex.ofReal_injective
    rw [hg, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
  have hχt : Complex.normSq (χ⁻¹ (t : ZMod c)) = 1 := by
    rw [← ZMod.coe_unitOfCoprime t htc]
    exact normSq_chi_unit χ⁻¹ _
  rw [geps_conv_gket_comp u M N h c hc χ hχ t ht]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [← Finset.mul_sum, hg', normSq_kcoef M c (NeZero.ne M) χ hχ, hχt, mul_one]

/-- **3d. ピタゴラス（ケット）**：‖k‖² = Σ_{t ∣ u, (t,c)=1} ‖ε_{s₀t} ⋆ k‖²。 -/
theorem normSq_gket_eq_sum (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    ∑ x, Complex.normSq (gket u M N h c hc χ x) = ∑ t ∈ u.divisors.filter (fun t => t.Coprime c),
      ∑ x, Complex.normSq (PAG.Part15.conv (geps N (M / c * t)) (gket u M N h c hc χ) x) := by
  have hMZ := neZero_of_mul h
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc)
    (Nat.pos_of_ne_zero (NeZero.ne c))
  conv_lhs => rw [gket_eq_sum_geps_conv u M N h c hc χ hχ]
  simp only [Finset.sum_apply]
  apply normSq_sum_orth
  intro t₁ _ t₂ _ hne
  exact inner_geps_conv_ne (M / c * t₁) (M / c * t₂) (fun e => hne (Nat.eq_of_mul_eq_mul_left hs0 e)) _ _

/-! ### 4. 旧部分と新しい部分（ℤ/NT） -/

/-- **4a.** P g_{s,ψ} = [T ∣ s]·g_{s,ψ}（ℤ/NT、s·n = NT）。 -/
theorem oldP_gbas (s n N T : ℕ) [NeZero N] [NeZero T] (h : s * n = N * T) (ψ : DirichletCharacter ℂ n) :
    oldP N T (gbas s n (N * T) ψ) = if T ∣ s then gbas s n (N * T) ψ else 0 := by
  apply (ZMod.dft (N := N * T) (E := ℂ)).injective
  funext ξ
  have hsupp := congrFun (dind_mul_dft_gbas s n (N * T) h ψ) ξ
  rw [Pi.mul_apply] at hsupp
  rw [dft_oldP]
  by_cases hTs : T ∣ s
  · rw [ite_eq_left hTs]
    by_cases hTξ : T ∣ ξ.val
    · rw [ite_eq_left hTξ]
    · rw [ite_eq_right hTξ, ← hsupp]
      have h0 : dind (N * T) s ξ = 0 := by
        simp only [dind]
        rw [ite_eq_right (fun e => hTξ (hTs.trans (by rw [← e]; exact Nat.gcd_dvd_right _ _)))]
      rw [h0, zero_mul]
  · rw [ite_eq_right hTs, map_zero, Pi.zero_apply]
    by_cases hTξ : T ∣ ξ.val
    · rw [ite_eq_left hTξ, ← hsupp]
      have h0 : dind (N * T) s ξ = 0 := by
        simp only [dind]
        rw [ite_eq_right (fun e => hTs (by rw [← e]; exact Nat.dvd_gcd (dvd_mul_left T N) hTξ))]
      rw [h0, zero_mul]
    · rw [ite_eq_right hTξ]

/-- **4b.** P は線形：P(Σ_i a_i f_i) = Σ_i a_i P f_i。 -/
theorem oldP_sum_smul (N T : ℕ) [NeZero N] [NeZero T] {ι : Type*} (F : Finset ι) (a : ι → ℂ)
    (f : ι → ZMod (N * T) → ℂ) :
    oldP N T (∑ i ∈ F, a i • f i) = ∑ i ∈ F, a i • oldP N T (f i) := by
  apply (ZMod.dft (N := N * T) (E := ℂ)).injective
  funext ξ
  simp only [dft_oldP, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **4c. 旧部分**：P k = Σ_{t ∣ u, (t,c)=1, T ∣ s₀t} B·χ̄(t)·g_{s₀t, χ̄′_t}（k は ℤ/NT のケット）。 -/
theorem oldP_gket_eq_sum (N T u M : ℕ) [NeZero N] [NeZero T] (h : u * M = N * T) (c : ℕ) [NeZero c]
    (hc : c ∣ M) (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    oldP N T (gket u M (N * T) h c hc χ) =
      ∑ t ∈ u.divisors.filter (fun t => t.Coprime c ∧ T ∣ M / c * t),
        (kcoef M c χ * χ⁻¹ (t : ZMod c)) •
          gbas (M / c * t) (u / t * c) (N * T) ((χ⁻¹).changeLevel (dvd_mul_left c (u / t))) := by
  rw [gket_eq_sum_gbas u M (N * T) h c hc χ hχ, oldP_sum_smul]
  conv_rhs => rw [← Finset.filter_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [oldP_gbas (M / c * t) (u / t * c) N T
    (shell_eq h hc (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ht).1))]
  split_ifs <;> simp

/-- **4d. 新しい部分**：k − P k = Σ_{t ∣ u, (t,c)=1, T ∤ s₀t} B·χ̄(t)·g_{s₀t, χ̄′_t}
（Part 202 の残る問い「一部が旧のケットの新しい部分の分解」の答え）。 -/
theorem sub_oldP_gket_eq_sum (N T u M : ℕ) [NeZero N] [NeZero T] (h : u * M = N * T) (c : ℕ) [NeZero c]
    (hc : c ∣ M) (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    gket u M (N * T) h c hc χ - oldP N T (gket u M (N * T) h c hc χ) =
      ∑ t ∈ u.divisors.filter (fun t => t.Coprime c ∧ ¬ T ∣ M / c * t),
        (kcoef M c χ * χ⁻¹ (t : ZMod c)) •
          gbas (M / c * t) (u / t * c) (N * T) ((χ⁻¹).changeLevel (dvd_mul_left c (u / t))) := by
  rw [oldP_gket_eq_sum N T u M h c hc χ hχ]
  conv_lhs => rw [gket_eq_sum_gbas u M (N * T) h c hc χ hχ]
  rw [← Finset.filter_filter, ← Finset.filter_filter,
    ← Finset.sum_filter_add_sum_filter_not (u.divisors.filter (fun t => t.Coprime c))
      (fun t => T ∣ M / c * t), add_sub_cancel_left]

/-! ### 5. 細かいケットとの関係 -/

/-- **5a.** B(M)/B(Mt) = √φ(Mt)/(√φ(M)·t)（c ∣ M）。 -/
theorem kcoef_div (M c t : ℕ) [NeZero c] (hM : M ≠ 0) (hc : c ∣ M) (ht : t ≠ 0)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    kcoef M c χ / kcoef (M * t) c χ =
      ((Real.sqrt (Nat.totient (M * t)) / (Real.sqrt (Nat.totient M) * t) : ℝ) : ℂ) := by
  have hφM : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hM))
  have hφMt : (0 : ℝ) < Real.sqrt (Nat.totient (M * t)) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (mul_ne_zero hM ht)))
  have hs0 : ((M / c : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hc) (Nat.pos_of_ne_zero (NeZero.ne c))).ne'
  have hτ : gaussSum χ stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero hχ
  have hm : χ⁻¹ (-1) ≠ 0 := ((isUnit_one.neg).map χ⁻¹).ne_zero
  have htC : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have a1 : ((Real.sqrt (Nat.totient M) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφM.ne'
  have a2 : ((Real.sqrt (Nat.totient (M * t)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφMt.ne'
  unfold kcoef
  rw [(Nat.div_mul_right_comm hc t).symm, Nat.cast_mul]
  push_cast
  field_simp

/-- **5b.** ε_{s₀t} ⋆ |u, χ⟩ = (B(M)·χ̄(t)/B(Mt))·ε_{s₀t} ⋆ |u/t, χ⟩（t ∣ u）。 -/
theorem geps_conv_gket_ratio (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (t : ℕ) (ht : t ∣ u) :
    PAG.Part15.conv (geps N (M / c * t)) (gket u M N h c hc χ) =
      (kcoef M c χ * χ⁻¹ (t : ZMod c) / kcoef (M * t) c χ) •
        PAG.Part15.conv (geps N (M / c * t))
          (gket (u / t) (M * t) N (fine_eq h ht) c (dvd_mul_of_dvd_left hc t) χ) := by
  have hMZ := neZero_of_mul h
  have ht0 : 0 < t := Nat.pos_of_dvd_of_pos ht (pos_of_mul h)
  have hk : kcoef (M * t) c χ ≠ 0 :=
    kcoef_ne_zero (M * t) c (mul_ne_zero (NeZero.ne M) ht0.ne') (dvd_mul_of_dvd_left hc t) χ hχ
  have e2 := geps_conv_gket_comp (u / t) (M * t) N (fine_eq h ht) c (dvd_mul_of_dvd_left hc t) χ hχ 1
    (one_dvd _)
  rw [(Nat.div_mul_right_comm hc t).symm, mul_one, Nat.div_one] at e2
  rw [e2, geps_conv_gket_comp u M N h c hc χ hχ t ht, smul_smul, Nat.cast_one, map_one, mul_one,
    div_mul_cancel₀ _ hk]

/-- **5c.** 係数を書き出した形：ε_{s₀t} ⋆ |u, χ⟩ = (√φ(Mt)/(√φ(M)·t))·χ̄(t)·ε_{s₀t} ⋆ |u/t, χ⟩。 -/
theorem geps_conv_gket_ratio' (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (t : ℕ) (ht : t ∣ u) :
    PAG.Part15.conv (geps N (M / c * t)) (gket u M N h c hc χ) =
      (((Real.sqrt (Nat.totient (M * t)) / (Real.sqrt (Nat.totient M) * t) : ℝ) : ℂ) * χ⁻¹ (t : ZMod c)) •
        PAG.Part15.conv (geps N (M / c * t))
          (gket (u / t) (M * t) N (fine_eq h ht) c (dvd_mul_of_dvd_left hc t) χ) := by
  have hMZ := neZero_of_mul h
  have ht0 : 0 < t := Nat.pos_of_dvd_of_pos ht (pos_of_mul h)
  rw [geps_conv_gket_ratio u M N h c hc χ hχ t ht, ← kcoef_div M c t (NeZero.ne M) hc ht0.ne' χ hχ,
    mul_div_right_comm]

end PAG.Part209

#print axioms PAG.Part209.dft_gket_apply'
#print axioms PAG.Part209.kcoef_ne_zero
#print axioms PAG.Part209.normSq_kcoef
#print axioms PAG.Part209.shell_eq
#print axioms PAG.Part209.fine_eq
#print axioms PAG.Part209.geps_conv_gket_comp
#print axioms PAG.Part209.geps_conv_gket_eq_zero
#print axioms PAG.Part209.geps_conv_gket_ne_zero_iff
#print axioms PAG.Part209.gket_eq_sum_geps_conv
#print axioms PAG.Part209.gket_eq_sum_gbas
#print axioms PAG.Part209.card_shells
#print axioms PAG.Part209.inner_geps_conv_ne
#print axioms PAG.Part209.normSq_sum_orth
#print axioms PAG.Part209.normSq_comp
#print axioms PAG.Part209.normSq_gket_eq_sum
#print axioms PAG.Part209.oldP_gbas
#print axioms PAG.Part209.oldP_sum_smul
#print axioms PAG.Part209.oldP_gket_eq_sum
#print axioms PAG.Part209.sub_oldP_gket_eq_sum
#print axioms PAG.Part209.kcoef_div
#print axioms PAG.Part209.geps_conv_gket_ratio
#print axioms PAG.Part209.geps_conv_gket_ratio'
