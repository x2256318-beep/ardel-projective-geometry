/-
  PAG 2.0 Part 202（2026-10-24）— 帰納系 ℤ/Nt → ℤ/N と双対殻分解の整合、旧部分への射影
  π : ℤ/Nt → ℤ/N、π^*f = f ∘ π（Part 197 の pull）、旧部分への射影 P f = (1/t)·1_{Nℤ} ⋆ f（def oldP）
  1. 𝓕(π^*f)(ξ) = [t ∣ ξ]·t·𝓕f(ξ/t)（dft_pull_apply）
  2. π^*ε_s^(N) = t·ε_{ts}^(Nt)（pull_geps）、ε_{ts} ⋆ π^*f = π^*(ε_s ⋆ f)（geps_conv_pull）
  3. 𝓕(Pf) = [t ∣ ξ]·𝓕f、P² = P、P = Σ_{s′ ∣ Nt, t ∣ s′} ε_{s′}、1 − P = Σ_{t ∤ s′} ε_{s′}、P は自己共役で旧部分と新しい部分は直交
  4. 像：Pg = g ⇔ g = π^*f（降下）、π^* は単射、V_{ts}^(Nt) = π^*V_s^(N)。Σ_{t ∣ s′} φ(Nt/s′) = N、Σ_{t ∤ s′} φ(Nt/s′) + N = Nt
  5. ケットの射影（Part 200 の混合公式で c₁ = 1）：k = |u, χ⟩_{Nt}、s₀ = M′/c、S = lcm(t, s₀)、g = gcd(t, s₀) として
     P k = (g/(t√φ(M′)))·χ̄(S/s₀)·R(Nt/(Sc), χ)、P k = 0 ⇔ (S/s₀, c) ≠ 1、t ∣ s₀ なら P k = k
-/
import PAG205

namespace PAG.Part206

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part201 PAG.Part202 PAG.Part203 PAG.Part204 PAG.Part205
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 引き戻しのフーリエ変換 -/

/-- **1.** 𝓕(π^*f)(ξ) = [t ∣ ξ]·t·𝓕f(ξ/t)（π : ℤ/Nt → ℤ/N）。 -/
theorem dft_pull_apply (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod N → ℂ) (ξ : ZMod (N * t)) :
    𝓕 (pull (dvd_mul_right N t) f) ξ =
      if t ∣ ξ.val then (t : ℂ) * 𝓕 f ((ξ.val / t : ℕ) : ZMod N) else 0 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have e : pull (dvd_mul_right N t) f = fun x => f (ZMod.castHom (dvd_mul_right N t) (ZMod N) x) := rfl
  rw [e, dft_pull (N * t) N (dvd_mul_right N t) f, Pi.smul_apply, smul_eq_mul, push_memb_apply,
    Nat.mul_div_cancel_left t hN0]
  split_ifs <;> simp

/-! ### 2. 双対殻のべき等元の引き戻し -/

/-- **2a.** π^*ε_s^(N) = t·ε_{ts}^(Nt)。 -/
theorem pull_geps (N t s : ℕ) [NeZero N] [NeZero t] :
    pull (dvd_mul_right N t) (geps N s) = (t : ℂ) • geps (N * t) (t * s) := by
  have ht0 : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  apply (ZMod.dft (N := N * t) (E := ℂ)).injective
  funext ξ
  rw [dft_pull_apply, map_smul, Pi.smul_apply, smul_eq_mul, dft_geps, dft_geps]
  simp only [dind]
  by_cases htξ : t ∣ ξ.val
  · obtain ⟨y, hy⟩ := htξ
    have hyN : y < N := by
      have hv := ZMod.val_lt ξ
      rw [hy, mul_comm] at hv
      exact Nat.lt_of_mul_lt_mul_right hv
    rw [ite_eq_left ⟨y, hy⟩, hy, Nat.mul_div_cancel_left y ht0, ZMod.val_cast_of_lt hyN]
    have hg : Nat.gcd (N * t) (t * y) = t * Nat.gcd N y := by
      rw [mul_comm t y, Nat.gcd_mul_right, mul_comm]
    rw [hg]
    by_cases h1 : Nat.gcd N y = s
    · simp [h1]
    · have h2 : ¬ (t * Nat.gcd N y = t * s) := fun h => h1 (Nat.eq_of_mul_eq_mul_left ht0 h)
      rw [ite_eq_right h1, ite_eq_right h2]
  · rw [ite_eq_right htξ]
    have h2 : ¬ (Nat.gcd (N * t) ξ.val = t * s) := fun h =>
      htξ ((dvd_mul_right t s).trans (by rw [← h]; exact Nat.gcd_dvd_right (N * t) ξ.val))
    rw [ite_eq_right h2, mul_zero]

/-- 畳み込みのスカラー倍（左）。 -/
theorem conv_smul_left {N : ℕ} [NeZero N] (a : ℂ) (f g : ZMod N → ℂ) :
    PAG.Part15.conv (a • f) g = a • PAG.Part15.conv f g := by
  funext x
  simp only [PAG.Part15.conv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- **2b.** ε_{ts}^(Nt) ⋆ π^*f = π^*(ε_s^(N) ⋆ f)。 -/
theorem geps_conv_pull (N t s : ℕ) [NeZero N] [NeZero t] (f : ZMod N → ℂ) :
    PAG.Part15.conv (geps (N * t) (t * s)) (pull (dvd_mul_right N t) f) =
      pull (dvd_mul_right N t) (PAG.Part15.conv (geps N s) f) := by
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have e : geps (N * t) (t * s) = (t : ℂ)⁻¹ • pull (dvd_mul_right N t) (geps N s) := by
    rw [pull_geps, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hc : (t : ℂ)⁻¹ * (((N * t : ℕ) : ℂ) / N) = 1 := by push_cast; field_simp
  rw [e, conv_smul_left, conv_pull, smul_smul, hc, one_smul]

/-! ### 3. 旧部分への射影 -/

/-- 旧部分への射影 P f = (1/t)·1_{Nℤ} ⋆ f（ℤ/Nt 上）。 -/
noncomputable def oldP (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod (N * t) → ℂ) : ZMod (N * t) → ℂ :=
  ((t : ℂ)⁻¹) • PAG.Part15.conv (rk (N := N * t) N 1 (fun _ => 1)) f

/-- **3a.** 𝓕(Pf)(ξ) = [t ∣ ξ]·𝓕f(ξ)。 -/
theorem dft_oldP (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod (N * t) → ℂ) (ξ : ZMod (N * t)) :
    𝓕 (oldP N t f) ξ = if t ∣ ξ.val then 𝓕 f ξ else 0 := by
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  unfold oldP
  rw [map_smul, Pi.smul_apply, smul_eq_mul, PAG.Part16.dft_conv, Pi.mul_apply, dft_ball N t (N * t) rfl ξ]
  split_ifs
  · field_simp
  · rw [zero_mul, mul_zero]

/-- **3b.** P² = P。 -/
theorem oldP_idem (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod (N * t) → ℂ) :
    oldP N t (oldP N t f) = oldP N t f := by
  apply (ZMod.dft (N := N * t) (E := ℂ)).injective
  funext ξ
  rw [dft_oldP, dft_oldP]
  split_ifs <;> rfl

/-- Σ_{s′ ∣ Nt, t ∣ s′} 1_{D_{s′}}(ξ) = [t ∣ ξ]。 -/
theorem sum_dind_dvd (N t : ℕ) [NeZero N] [NeZero t] (ξ : ZMod (N * t)) :
    ∑ s ∈ (N * t).divisors.filter (fun s => t ∣ s), dind (N * t) s ξ = if t ∣ ξ.val then 1 else 0 := by
  have hmem : Nat.gcd (N * t) ξ.val ∈ (N * t).divisors.filter (fun s => t ∣ s) ↔ t ∣ ξ.val := by
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · intro h; exact ⟨⟨Nat.gcd_dvd_left _ _, NeZero.ne _⟩, dvd_mul_left t N, h⟩
  simp only [dind, Finset.sum_ite_eq]
  by_cases h : t ∣ ξ.val
  · rw [ite_eq_left (hmem.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hm => h (hmem.mp hm)), ite_eq_right h]

/-- Σ_{s′ ∣ Nt, t ∤ s′} 1_{D_{s′}}(ξ) = [t ∤ ξ]。 -/
theorem sum_dind_not_dvd (N t : ℕ) [NeZero N] [NeZero t] (ξ : ZMod (N * t)) :
    ∑ s ∈ (N * t).divisors.filter (fun s => ¬ t ∣ s), dind (N * t) s ξ = if t ∣ ξ.val then 0 else 1 := by
  have hall := congrFun (sum_dind (N * t)) ξ
  rw [Finset.sum_apply, Pi.one_apply,
    ← Finset.sum_filter_add_sum_filter_not _ (fun s => t ∣ s), sum_dind_dvd] at hall
  split_ifs at hall ⊢ <;> linear_combination hall

/-- **3c.** P f = Σ_{s′ ∣ Nt, t ∣ s′} ε_{s′} ⋆ f。 -/
theorem oldP_eq_sum (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod (N * t) → ℂ) :
    oldP N t f = ∑ s ∈ (N * t).divisors.filter (fun s => t ∣ s), PAG.Part15.conv (geps (N * t) s) f := by
  apply (ZMod.dft (N := N * t) (E := ℂ)).injective
  funext ξ
  rw [dft_oldP, map_sum, Finset.sum_apply]
  simp only [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps]
  rw [← Finset.sum_mul, sum_dind_dvd]
  split_ifs <;> simp

/-- **3d.** f − P f = Σ_{s′ ∣ Nt, t ∤ s′} ε_{s′} ⋆ f（新しい部分）。 -/
theorem sub_oldP_eq_sum (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod (N * t) → ℂ) :
    f - oldP N t f =
      ∑ s ∈ (N * t).divisors.filter (fun s => ¬ t ∣ s), PAG.Part15.conv (geps (N * t) s) f := by
  apply (ZMod.dft (N := N * t) (E := ℂ)).injective
  funext ξ
  rw [map_sub, Pi.sub_apply, dft_oldP, map_sum, Finset.sum_apply]
  simp only [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps]
  rw [← Finset.sum_mul, sum_dind_not_dvd]
  split_ifs <;> simp

/-- **3e.** P は自己共役：⟨Pf, g⟩ = ⟨f, Pg⟩。 -/
theorem oldP_selfAdjoint (N t : ℕ) [NeZero N] [NeZero t] (f g : ZMod (N * t) → ℂ) :
    ∑ x, starRingEnd ℂ (oldP N t f x) * g x = ∑ x, starRingEnd ℂ (f x) * oldP N t g x := by
  have hN : ((N * t : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have P1 := PAG.Part39.plancherel (oldP N t f) g
  have P2 := PAG.Part39.plancherel f (oldP N t g)
  apply mul_left_cancel₀ hN
  rw [← P1, ← P2]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [dft_oldP, dft_oldP]
  split_ifs <;> simp

/-- **3f.** 旧部分と新しい部分は直交：⟨Pf, g − Pg⟩ = 0。 -/
theorem oldP_orth (N t : ℕ) [NeZero N] [NeZero t] (f g : ZMod (N * t) → ℂ) :
    ∑ x, starRingEnd ℂ (oldP N t f x) * (g x - oldP N t g x) = 0 := by
  have e1 := oldP_selfAdjoint N t f g
  have e2 := oldP_selfAdjoint N t f (oldP N t g)
  rw [oldP_idem] at e2
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [e1, e2, sub_self]

/-! ### 4. 像（旧部分 = 引き戻しの像） -/

/-- **4a.** P(π^*f) = π^*f。 -/
theorem oldP_pull (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod N → ℂ) :
    oldP N t (pull (dvd_mul_right N t) f) = pull (dvd_mul_right N t) f := by
  apply (ZMod.dft (N := N * t) (E := ℂ)).injective
  funext ξ
  rw [dft_oldP, dft_pull_apply]
  split_ifs <;> rfl

/-- π^* は単射。 -/
theorem pull_injective (N t : ℕ) [NeZero N] [NeZero t] :
    Function.Injective (pull (N' := N * t) (dvd_mul_right N t)) := by
  intro f g hfg
  funext y
  obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (ZMod.castHom (dvd_mul_right N t) (ZMod N)) y
  have e := congrFun hfg x
  simp only [pull_apply] at e
  rw [← hx]; exact e

/-- **4b. 降下**：Pg = g なら g = π^*f となる f がある（𝓕_N f(η) = 𝓕_{Nt} g(tη)/t）。 -/
theorem exists_pull_of_oldP (N t : ℕ) [NeZero N] [NeZero t] (g : ZMod (N * t) → ℂ)
    (hg : oldP N t g = g) : ∃ f : ZMod N → ℂ, pull (dvd_mul_right N t) f = g := by
  have ht0 : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  refine ⟨𝓕⁻ (fun η : ZMod N => (t : ℂ)⁻¹ * 𝓕 g ((t * η.val : ℕ) : ZMod (N * t))), ?_⟩
  apply (ZMod.dft (N := N * t) (E := ℂ)).injective
  funext ξ
  rw [dft_pull_apply]
  simp only [LinearEquiv.apply_symm_apply]
  have hgξ := congrFun (congrArg (ZMod.dft (N := N * t) (E := ℂ)) hg) ξ
  rw [dft_oldP] at hgξ
  by_cases htξ : t ∣ ξ.val
  · obtain ⟨y, hy⟩ := htξ
    have hyN : y < N := by
      have hv := ZMod.val_lt ξ
      rw [hy, mul_comm] at hv
      exact Nat.lt_of_mul_lt_mul_right hv
    rw [ite_eq_left ⟨y, hy⟩, hy, Nat.mul_div_cancel_left y ht0, ZMod.val_cast_of_lt hyN, ← hy,
      ZMod.natCast_zmod_val]
    field_simp
  · rw [ite_eq_right htξ]
    rw [ite_eq_right htξ] at hgξ
    exact hgξ

/-- **4c. 旧部分の特徴づけ**：Pg = g ⇔ g = π^*f となる f がある。 -/
theorem oldP_eq_self_iff (N t : ℕ) [NeZero N] [NeZero t] (g : ZMod (N * t) → ℂ) :
    oldP N t g = g ↔ ∃ f : ZMod N → ℂ, pull (dvd_mul_right N t) f = g := by
  constructor
  · exact exists_pull_of_oldP N t g
  · rintro ⟨f, rfl⟩
    exact oldP_pull N t f

/-- **4d.** V_{ts}^(Nt) = π^*V_s^(N)：ε_{ts} ⋆ g = g ⇔ g = π^*f かつ ε_s ⋆ f = f となる f がある。 -/
theorem mem_geps_pull_iff (N t s : ℕ) [NeZero N] [NeZero t] (g : ZMod (N * t) → ℂ) :
    PAG.Part15.conv (geps (N * t) (t * s)) g = g ↔
      ∃ f : ZMod N → ℂ, PAG.Part15.conv (geps N s) f = f ∧ pull (dvd_mul_right N t) f = g := by
  constructor
  · intro hg
    have hold : oldP N t g = g := by
      apply (ZMod.dft (N := N * t) (E := ℂ)).injective
      funext ξ
      rw [dft_oldP]
      by_cases htξ : t ∣ ξ.val
      · rw [ite_eq_left htξ]
      · rw [ite_eq_right htξ]
        have e := congrFun (congrArg (ZMod.dft (N := N * t) (E := ℂ)) hg) ξ
        rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps] at e
        have hd : dind (N * t) (t * s) ξ = 0 := by
          simp only [dind]
          rw [ite_eq_right (fun h => htξ ((dvd_mul_right t s).trans
            (by rw [← h]; exact Nat.gcd_dvd_right (N * t) ξ.val)))]
        rw [hd, zero_mul] at e
        exact e
    obtain ⟨f, hf⟩ := exists_pull_of_oldP N t g hold
    refine ⟨f, ?_, hf⟩
    apply pull_injective N t
    rw [← geps_conv_pull, hf, hg]
  · rintro ⟨f, hf, rfl⟩
    rw [geps_conv_pull, hf]

/-- **4e.** Σ_{s′ ∣ Nt, t ∣ s′} φ(Nt/s′) = N（旧部分のフーリエ側の点の数）。 -/
theorem sum_totient_dvd (N t : ℕ) [NeZero N] [NeZero t] :
    ∑ s ∈ (N * t).divisors.filter (fun s => t ∣ s), Nat.totient (N * t / s) = N := by
  have ht0 : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  have himg : (N * t).divisors.filter (fun s => t ∣ s) = N.divisors.image (fun s => t * s) := by
    ext s'
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hs', _⟩, ⟨s, rfl⟩⟩
      refine ⟨s, ⟨?_, NeZero.ne N⟩, rfl⟩
      rw [mul_comm N t] at hs'
      exact Nat.dvd_of_mul_dvd_mul_left ht0 hs'
    · rintro ⟨s, ⟨hs, _⟩, rfl⟩
      refine ⟨⟨?_, NeZero.ne _⟩, dvd_mul_right t s⟩
      rw [mul_comm N t]
      exact Nat.mul_dvd_mul_left t hs
  rw [himg, Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left ht0 hab)]
  have e : ∀ s ∈ N.divisors, Nat.totient (N * t / (t * s)) = Nat.totient (N / s) := by
    intro s _
    rw [mul_comm N t, Nat.mul_div_mul_left N s ht0]
  rw [Finset.sum_congr rfl e, Nat.sum_div_divisors N Nat.totient, Nat.sum_totient]

/-- **4f.** Σ_{s′ ∣ Nt, t ∤ s′} φ(Nt/s′) + N = Nt（新しい部分の次元は Nt − N）。 -/
theorem sum_totient_not_dvd (N t : ℕ) [NeZero N] [NeZero t] :
    ∑ s ∈ (N * t).divisors.filter (fun s => ¬ t ∣ s), Nat.totient (N * t / s) + N = N * t := by
  have h := Finset.sum_filter_add_sum_filter_not (N * t).divisors (fun s => t ∣ s)
    (fun s => Nat.totient (N * t / s))
  rw [sum_totient_dvd, Nat.sum_div_divisors, Nat.sum_totient] at h
  linarith

/-! ### 5. ケットの旧部分への射影 -/

/-- **5a. ケットの射影**：k = |u, χ⟩_{Nt}（χ 原始的、法 c、s₀ = M′/c、S = lcm(t, s₀)、g = gcd(t, s₀)）で
P k = (g/(t√φ(M′)))·χ̄(S/s₀)·R(Nt/(Sc), χ)（Part 200 の混合公式で、球のケット |N, 1⟩_{Nt} との畳み込み）。 -/
theorem oldP_gket (N t : ℕ) [NeZero N] [NeZero t] (u M' : ℕ) (h : u * M' = N * t) (c : ℕ) [NeZero c]
    (hc : c ∣ M') (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    oldP N t (gket u M' (N * t) h c hc χ) =
      (((Nat.gcd t (M' / c) : ℕ) : ℂ) / ((t : ℂ) * ((Real.sqrt (Nat.totient M') : ℝ) : ℂ)) *
        χ⁻¹ ((Nat.lcm t (M' / c) / (M' / c) : ℕ) : ZMod c)) •
      rk (N := N * t) (N * t / (Nat.lcm t (M' / c) * c)) c χ := by
  have hMZ := neZero_of_mul h
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  have hφt : ((Real.sqrt (Nat.totient t) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (Nat.totient t) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne t)))
    exact_mod_cast this.ne'
  have hφM : ((Real.sqrt (Nat.totient M') : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (Nat.totient M') :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M')))
    exact_mod_cast this.ne'
  have hτ : gaussSum χ stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero hχ
  have hone : ((1 : DirichletCharacter ℂ 1) : ZMod 1 → ℂ) = fun _ => 1 := by
    funext x; exact chi_level_one 1 x
  have hprod : (1 : DirichletCharacter ℂ 1).changeLevel (Nat.dvd_lcm_left 1 c) *
      χ.changeLevel (Nat.dvd_lcm_right 1 c) = χ.changeLevel (Nat.dvd_lcm_right 1 c) := by
    rw [map_one, one_mul]
  have hrad : ∀ q : ℕ, q.Prime → q ∣ Nat.lcm 1 c → q ∣ c := fun q _ hq => by
    rwa [Nat.lcm_one_left] at hq
  unfold oldP
  rw [rk_eq_gket N t (N * t) rfl 1 (one_dvd t) (fun _ => 1), conv_smul_left, ← hone,
    conv_mixed_single N t u M' (N * t) rfl h 1 c c (one_dvd t) hc (Nat.dvd_lcm_right 1 c) 1 χ χ
      DirichletCharacter.isPrimitive_one_level_one hχ hχ hprod hrad,
    smul_smul, smul_smul]
  simp only [Nat.div_one]
  congr 1
  simp only [chi_level_one, gaussSum_level_one, one_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  push_cast
  field_simp

/-- **5b.** P k = 0 ⇔ (S/s₀, c) ≠ 1（Part 200 の 0 になる条件）。 -/
theorem oldP_gket_eq_zero_iff (N t : ℕ) [NeZero N] [NeZero t] (u M' : ℕ) (h : u * M' = N * t) (c : ℕ)
    [NeZero c] (hc : c ∣ M') (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    oldP N t (gket u M' (N * t) h c hc χ) = 0 ↔ ¬ (Nat.lcm t (M' / c) / (M' / c)).Coprime c := by
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  have hφt : ((Real.sqrt (Nat.totient t) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (Nat.totient t) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne t)))
    exact_mod_cast this.ne'
  have hone : ((1 : DirichletCharacter ℂ 1) : ZMod 1 → ℂ) = fun _ => 1 := by
    funext x; exact chi_level_one 1 x
  have hz := conv_mixed_eq_zero_iff N t u M' (N * t) rfl h 1 c (one_dvd t) hc 1 χ
    DirichletCharacter.isPrimitive_one_level_one hχ
  simp only [Nat.div_one, Nat.coprime_one_right_eq_true, true_and] at hz
  unfold oldP
  rw [rk_eq_gket N t (N * t) rfl 1 (one_dvd t) (fun _ => 1), conv_smul_left, ← hone, smul_smul,
    smul_eq_zero, or_iff_right (mul_ne_zero (inv_ne_zero ht) hφt)]
  exact hz

/-- **5c.** t ∣ s₀（uc ∣ N。旧部分のケット）なら P k = k。 -/
theorem oldP_gket_of_dvd (N t : ℕ) [NeZero N] [NeZero t] (u M' : ℕ) (h : u * M' = N * t) (c : ℕ)
    [NeZero c] (hc : c ∣ M') (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (ht : t ∣ M' / c) :
    oldP N t (gket u M' (N * t) h c hc χ) = gket u M' (N * t) h c hc χ := by
  apply (ZMod.dft (N := N * t) (E := ℂ)).injective
  funext ξ
  rw [dft_oldP, dft_gket_apply u M' (N * t) h c hc χ hχ ξ]
  by_cases htξ : t ∣ ξ.val
  · rw [ite_eq_left htξ]
  · rw [ite_eq_right htξ, ite_eq_right (fun hs => htξ (ht.trans hs))]

/-- **5d. ケットの形**：(S/s₀, c) = 1、u′·(Sc) = Nt なら P k = κ·|u′, χ⟩_{Nt}、
κ = (g/(t√φ(M′)))·χ̄(S/s₀)·√φ(Sc)。 -/
theorem oldP_gket_ket (N t : ℕ) [NeZero N] [NeZero t] (u M' : ℕ) (h : u * M' = N * t) (c : ℕ) [NeZero c]
    (hc : c ∣ M') (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive)
    (u' : ℕ) (h' : u' * (Nat.lcm t (M' / c) * c) = N * t) :
    oldP N t (gket u M' (N * t) h c hc χ) =
      (((Nat.gcd t (M' / c) : ℕ) : ℂ) / ((t : ℂ) * ((Real.sqrt (Nat.totient M') : ℝ) : ℂ)) *
        χ⁻¹ ((Nat.lcm t (M' / c) / (M' / c) : ℕ) : ZMod c) *
        ((Real.sqrt (Nat.totient (Nat.lcm t (M' / c) * c)) : ℝ) : ℂ)) •
      gket u' (Nat.lcm t (M' / c) * c) (N * t) h' c (dvd_mul_left c _) χ := by
  have hW : 0 < Nat.lcm t (M' / c) * c := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, mul_zero] at h'
    exact NeZero.ne (N * t) h'.symm
  have hv : N * t / (Nat.lcm t (M' / c) * c) = u' := Nat.div_eq_of_eq_mul_left hW h'.symm
  rw [oldP_gket N t u M' h c hc χ hχ, hv, rk_eq_gket u' _ (N * t) h' c (dvd_mul_left c _) χ, smul_smul]

end PAG.Part206

#print axioms PAG.Part206.dft_pull_apply
#print axioms PAG.Part206.pull_geps
#print axioms PAG.Part206.conv_smul_left
#print axioms PAG.Part206.geps_conv_pull
#print axioms PAG.Part206.dft_oldP
#print axioms PAG.Part206.oldP_idem
#print axioms PAG.Part206.sum_dind_dvd
#print axioms PAG.Part206.sum_dind_not_dvd
#print axioms PAG.Part206.oldP_eq_sum
#print axioms PAG.Part206.sub_oldP_eq_sum
#print axioms PAG.Part206.oldP_selfAdjoint
#print axioms PAG.Part206.oldP_orth
#print axioms PAG.Part206.oldP_pull
#print axioms PAG.Part206.pull_injective
#print axioms PAG.Part206.exists_pull_of_oldP
#print axioms PAG.Part206.oldP_eq_self_iff
#print axioms PAG.Part206.mem_geps_pull_iff
#print axioms PAG.Part206.sum_totient_dvd
#print axioms PAG.Part206.sum_totient_not_dvd
#print axioms PAG.Part206.oldP_gket
#print axioms PAG.Part206.oldP_gket_eq_zero_iff
#print axioms PAG.Part206.oldP_gket_of_dvd
#print axioms PAG.Part206.oldP_gket_ket
