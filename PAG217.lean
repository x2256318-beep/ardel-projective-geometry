/-
  PAG 2.0 Part 213（2026-10-28）— フーリエ変換とブロック・殻の分解
  ブロック (c, χ)（χ は法 c の原始指標）、L = N/c。u, v, w は L の約数
  k_u = |u, χ⟩_N（Part 210 の kblock）、k′_u = |u, χ̄⟩_N（ブロック (c, χ̄) のケット）、P = P_{c,χ}（Part 211 の blockProj）
  G_v = g_{N/(vc), χ̄′}（Part 210 の gblock）、D_s = {x : gcd(N, x) = s}（1_{D_s} は Part 201 の dind）
  1. ケットのフーリエ変換（Part 198 をブロックの記号で）：𝓕 k_u = C_u·k′_{L/u}、C_u ≠ 0
  2. 射影の特徴づけ：ブロックのケットの一次結合 p で、すべての w について ⟨k_w, p⟩ = ⟨k_w, g⟩ なら p = P g
  3. 𝓕 (P_{c,χ} f) = P_{c,χ̄} (𝓕 f)
  4. 空間の殻との可換性：1_{D_s}·(P f) = P (1_{D_s}·f)。1_{D_s}·k_w はブロックに入る
  5. フーリエ双対性：k_u が 1 つの双対殻に入る（Part 201 の (R)：rad(u) ∣ c）⇔ k′_{L/u} の大きさが 1。
     逆に ‖k_u‖ = 1 ⇔ k′_{L/u} が 1 つの双対殻 V_u に入る
  6. 𝓕 G_v はブロック (c, χ̄) の直交基底：台は D_{N/(vc)}、P_{c,χ̄} 𝓕 G_v = 𝓕 G_v、⟨𝓕 G_v, 𝓕 G_w⟩ = [v = w]·φ(vc)
  7. 空間の殻ごとの形：P_{c,χ} f = Σ_v (1/φ(vc))·⟨H_v, f⟩·H_v（H_v = 𝓕 G′_v、G′_v はブロック (c, χ̄) の G_v）、
     1_{D_{N/(vc)}}·(P f) = (1/φ(vc))·⟨H_v, f⟩·H_v
-/
import PAG216

namespace PAG.Part217

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

/-- **0a.** N/u/c = N/c/u。 -/
theorem div_div_swap (N c u : ℕ) : N / u / c = N / c / u := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]

/-- **0b.** u ∣ N/c（c ∣ N）なら N/(N/c/u) = u·c。 -/
theorem div_dual_eq {N c u : ℕ} [NeZero N] (hcN : c ∣ N) (hu : u ∣ N / c) : N / (N / c / u) = u * c := by
  have hprod : N / c / u * (u * c) = N := by
    rw [show N / c / u * (u * c) = N / c / u * u * c by ring, Nat.div_mul_cancel hu, Nat.div_mul_cancel hcN]
  have hpos : 0 < N / c / u :=
    Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hprod; exact NeZero.ne N hprod.symm)
  exact Nat.div_eq_of_eq_mul_left hpos (by rw [mul_comm (u * c)]; exact hprod.symm)

/-- **0c.** gket の番号と法の付け替え（証明の項の付け替え）。 -/
theorem gket_congr2 (N : ℕ) [NeZero N] {u u' M M' : ℕ} (eu : u = u') (eM : M = M') (h : u * M = N)
    (h' : u' * M' = N) (c : ℕ) (hc : c ∣ M) (hc' : c ∣ M') (χ : ZMod c → ℂ) :
    gket u M N h c hc χ = gket u' M' N h' c hc' χ := by
  subst eu
  subst eM
  rfl

/-- **0d.** ⟨r·a, b⟩ = conj(r)·⟨a, b⟩。 -/
theorem inner_smul_left' {N : ℕ} [NeZero N] (r : ℂ) (a b : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ ((r • a) x) * b x = starRingEnd ℂ r * ∑ x, starRingEnd ℂ (a x) * b x := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

/-- **0e.** 同じブロックのケット（番号を自然数で書いた形）：w ∣ N/c なら ⟨k_w, P f⟩ = ⟨k_w, f⟩。 -/
theorem inner_kblock_blockProj' (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {w : ℕ} (hw : w ∣ N / c) (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (kblock N c χ w x) * blockProj N c χ f x = ∑ x, starRingEnd ℂ (kblock N c χ w x) * f x :=
  inner_kblock_blockProj N c hcN χ hχ ⟨w, Nat.mem_divisors.mpr ⟨hw, div_ne_zero_of_dvd (NeZero.ne N) hcN⟩⟩ f

/-! ### 1. ケットのフーリエ変換 -/

/-- ケットのフーリエ変換の係数 C_u = √φ(uc)/√φ(N/u)·(N/u/c)·χ̄(−1)·τ(χ)。 -/
noncomputable def fcoef (N c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) (u : ℕ) : ℂ :=
  ((Real.sqrt (Nat.totient (u * c)) / Real.sqrt (Nat.totient (N / u)) : ℝ) : ℂ) * ((N / u / c : ℕ) : ℂ) *
    χ⁻¹ (-1) * gaussSum χ stdAddChar

/-- **1a.** C_u ≠ 0（u ∣ N/c、χ 原始的）。 -/
theorem fcoef_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {u : ℕ} (hu : u ∣ N / c) : fcoef N c χ u ≠ 0 := by
  obtain ⟨h1, h2⟩ := block_dvd hcN hu
  have hu0 : 0 < u := Nat.pos_of_dvd_of_pos hu (Nat.pos_of_ne_zero (div_ne_zero_of_dvd (NeZero.ne N) hcN))
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hNu : N / u ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) h1
  have hs0 : N / u / c ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hNu) h2) hc0).ne'
  have hq : (0 : ℝ) < Real.sqrt (Nat.totient (u * c)) / Real.sqrt (Nat.totient (N / u)) :=
    div_pos (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hu0 hc0)))
      (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hNu)))
  unfold fcoef
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (PAG.Part16.gaussSum_ne_zero hχ)
  · exact_mod_cast hq.ne'
  · exact_mod_cast hs0
  · exact ((isUnit_one.neg).map χ⁻¹).ne_zero

/-- **1b. ケットのフーリエ変換**：u ∣ N/c なら 𝓕 k_u = C_u·k′_{L/u}（k′ はブロック (c, χ̄) のケット、χ 原始的）。 -/
theorem dft_kblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {u : ℕ} (hu : u ∣ N / c) :
    𝓕 (kblock N c χ u) =
      fcoef N c χ u • kblock N c ((χ⁻¹ : DirichletCharacter ℂ c) : ZMod c → ℂ) (N / c / u) := by
  obtain ⟨h1, h2⟩ := block_dvd hcN hu
  have hd : N / c / u ∣ N / c := Nat.div_dvd_of_dvd hu
  obtain ⟨h1', h2'⟩ := block_dvd hcN hd
  rw [kblock_of_dvd N c χ h1 h2, dft_gket u (N / u) N (Nat.mul_div_cancel' h1) c h2 χ hχ,
    kblock_of_dvd N c _ h1' h2']
  unfold fcoef
  congr 1
  exact gket_congr2 N (div_div_swap N c u) (div_dual_eq hcN hu).symm _ _ c _ _ _

/-- **1c.** 逆向き：k′_w = 𝓕(C_{L/w}⁻¹·k_{L/w})（w ∣ N/c）。 -/
theorem kblock_inv_eq_dft (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {w : ℕ} (hw : w ∣ N / c) :
    kblock N c ((χ⁻¹ : DirichletCharacter ℂ c) : ZMod c → ℂ) w =
      𝓕 ((fcoef N c χ (N / c / w))⁻¹ • kblock N c χ (N / c / w)) := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  have hd : N / c / w ∣ N / c := Nat.div_dvd_of_dvd hw
  rw [map_smul, dft_kblock N c hcN χ hχ hd, smul_smul, inv_mul_cancel₀ (fcoef_ne_zero N c hcN χ hχ hd), one_smul,
    Nat.div_div_self hw hL0]

/-! ### 2. ブロックへの射影の特徴づけ -/

/-- **2a. 射影の特徴づけ**：p = Σ_{u ∣ N/c} d_u·k_u で、すべての w ∣ N/c について ⟨k_w, p⟩ = ⟨k_w, g⟩ なら p = P g。 -/
theorem eq_blockProj_of_inner (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (d : ℕ → ℂ) (g : ZMod N → ℂ)
    (h : ∀ w : (N / c).divisors,
      ∑ x, starRingEnd ℂ (kblock N c χ w x) * (∑ u ∈ (N / c).divisors, d u • kblock N c χ u) x =
        ∑ x, starRingEnd ℂ (kblock N c χ w x) * g x) :
    ∑ u ∈ (N / c).divisors, d u • kblock N c χ u = blockProj N c χ g := by
  apply eq_of_inner_ketFam_eq N
  intro j
  rw [inner_conj_symm (∑ u ∈ (N / c).divisors, d u • kblock N c χ u) (ketFam N j),
    inner_conj_symm (blockProj N c χ g) (ketFam N j)]
  congr 1
  rcases ketIdx_cases N c χ j with ⟨w, hw⟩ | hne
  · rw [hw, h w, inner_kblock_blockProj N c hcN χ hχ w g]
  · rw [inner_ketFam_blockProj_of_ne N c hcN χ hχ g j hne, inner_sum_smul_right]
    refine Finset.sum_eq_zero (fun u hu => ?_)
    rw [show kblock N c χ u = kblock N c χ ((⟨u, hu⟩ : (N / c).divisors) : ℕ) from rfl,
      ← ketFam_blockIdx N c hcN χ hχ ⟨u, hu⟩,
      inner_ketFam_of_ketClass_ne N j (blockIdx N c hcN χ hχ ⟨u, hu⟩) hne, mul_zero]

/-! ### 3. フーリエ変換とブロックへの射影 -/

/-- **3a.** 𝓕 (P f) をブロック (c, χ̄) のケットで書く：𝓕 (P f) = Σ_{u ∣ L} ⟨k^∨_{L/u}, f⟩·C_{L/u}·k′_u。 -/
theorem dft_blockProj_eq_sum (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) :
    𝓕 (blockProj N c χ f) = ∑ u ∈ (N / c).divisors,
      ((∑ x, starRingEnd ℂ (kdual N (N / c / u) c χ x) * f x) * fcoef N c χ (N / c / u)) •
        kblock N c ((χ⁻¹ : DirichletCharacter ℂ c) : ZMod c → ℂ) u := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  calc 𝓕 (blockProj N c χ f)
      = ∑ u ∈ (N / c).divisors, ((∑ x, starRingEnd ℂ (kdual N u c χ x) * f x) * fcoef N c χ u) •
          kblock N c ((χ⁻¹ : DirichletCharacter ℂ c) : ZMod c → ℂ) (N / c / u) := by
        unfold blockProj
        rw [map_sum]
        simp only [map_smul]
        rw [Finset.sum_coe_sort (N / c).divisors
          (fun u => (∑ x, starRingEnd ℂ (kdual N u c χ x) * f x) • 𝓕 (kblock N c χ u))]
        refine Finset.sum_congr rfl (fun u hu => ?_)
        rw [dft_kblock N c hcN χ hχ (Nat.dvd_of_mem_divisors hu), smul_smul]
    _ = _ := by
        rw [← Nat.sum_div_divisors (N / c) (fun u => ((∑ x, starRingEnd ℂ (kdual N (N / c / u) c χ x) * f x) *
          fcoef N c χ (N / c / u)) • kblock N c ((χ⁻¹ : DirichletCharacter ℂ c) : ZMod c → ℂ) u)]
        refine Finset.sum_congr rfl (fun u hu => ?_)
        rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hu) hL0]

/-- **3b. フーリエ変換とブロックへの射影**：𝓕 (P_{c,χ} f) = P_{c,χ̄} (𝓕 f)（χ 原始的）。 -/
theorem dft_blockProj (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) :
    𝓕 (blockProj N c χ f) = blockProj N c χ⁻¹ (𝓕 f) := by
  have hχ' : (χ⁻¹).IsPrimitive := PAG.Part16.isPrimitive_inv hχ
  rw [dft_blockProj_eq_sum N c hcN χ hχ f]
  apply eq_blockProj_of_inner N c hcN χ⁻¹ hχ'
  intro w
  have hw : (w : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors w.2
  rw [← dft_blockProj_eq_sum N c hcN χ hχ f, kblock_inv_eq_dft N c hcN χ hχ hw, PAG.Part39.plancherel,
    PAG.Part39.plancherel, inner_smul_left', inner_smul_left',
    inner_kblock_blockProj' N c hcN χ hχ (Nat.div_dvd_of_dvd hw) f]

/-! ### 4. 空間の殻との可換性 -/

/-- **4a. 空間の殻との可換性**：1_{D_s}·(P f) = P (1_{D_s}·f)（D_s = {x : gcd(N, x) = s}、χ 原始的）。 -/
theorem dind_mul_blockProj (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (s : ℕ) (f : ZMod N → ℂ) :
    dind N s * blockProj N c χ f = blockProj N c χ (dind N s * f) := by
  have hχ' : (χ⁻¹).IsPrimitive := PAG.Part16.isPrimitive_inv hχ
  have e1 : ∀ g : ZMod N → ℂ, 𝓕 (blockProj N c χ⁻¹ g) = blockProj N c χ (𝓕 g) := by
    intro g
    have e := dft_blockProj N c hcN χ⁻¹ hχ' g
    rwa [inv_inv] at e
  obtain ⟨h, rfl⟩ : ∃ h : ZMod N → ℂ, 𝓕 h = f := ⟨𝓕⁻ f, LinearEquiv.apply_symm_apply _ f⟩
  rw [← e1 h, ← dft_geps N s, ← PAG.Part16.dft_conv, geps_conv_blockProj N c hcN χ⁻¹ hχ' s h, e1,
    PAG.Part16.dft_conv]

/-- **4b.** 1_{D_s}·k_w はブロックに入る：P (1_{D_s}·k_w) = 1_{D_s}·k_w。 -/
theorem blockProj_dind_mul_kblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (s : ℕ) (w : (N / c).divisors) :
    blockProj N c χ (dind N s * kblock N c χ w) = dind N s * kblock N c χ w := by
  rw [← dind_mul_blockProj N c hcN χ hχ s, blockProj_kblock N c hcN χ hχ w]

/-! ### 5. フーリエ双対性 -/

/-- **5a.** u ∣ N/c なら、k_u が 1 つの双対殻に入る（ε_{s₀} ⋆ k_u = k_u、Part 201 の (R)）⇔
フーリエ双対のケット k′_{L/u} の大きさが 1（χ 原始的）。 -/
theorem geps_conv_kblock_iff_normSq_dual (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {u : ℕ} (hu : u ∣ N / c) :
    PAG.Part15.conv (geps N (N / u / c)) (kblock N c χ u) = kblock N c χ u ↔
      ∑ x, Complex.normSq (kblock N c ((χ⁻¹ : DirichletCharacter ℂ c) : ZMod c → ℂ) (N / c / u) x) = 1 := by
  obtain ⟨h1, h2⟩ := block_dvd hcN hu
  have hd : N / c / u ∣ N / c := Nat.div_dvd_of_dvd hu
  obtain ⟨h1', h2'⟩ := block_dvd hcN hd
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have e : N / (N / c / u) / c = u := by rw [div_dual_eq hcN hu, Nat.mul_div_cancel u hc0]
  rw [kblock_of_dvd N c χ h1 h2, kblock_of_dvd N c _ h1' h2', gket_mem_iff u (N / u) N _ c h2 χ hχ,
    normSq_gket_eq_one_iff (N / c / u) (N / (N / c / u)) N _ c h2' _, e]

/-- **5b.** 逆向き：‖k_u‖ = 1 ⇔ フーリエ双対のケット k′_{L/u} が 1 つの双対殻 V_u に入る（ε_u ⋆ k′_{L/u} = k′_{L/u}）。 -/
theorem normSq_kblock_iff_geps_conv_dual (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {u : ℕ} (hu : u ∣ N / c) :
    ∑ x, Complex.normSq (kblock N c χ u x) = 1 ↔
      PAG.Part15.conv (geps N u) (kblock N c ((χ⁻¹ : DirichletCharacter ℂ c) : ZMod c → ℂ) (N / c / u)) =
        kblock N c ((χ⁻¹ : DirichletCharacter ℂ c) : ZMod c → ℂ) (N / c / u) := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hχ' : (χ⁻¹).IsPrimitive := PAG.Part16.isPrimitive_inv hχ
  have e : N / (N / c / u) / c = u := by rw [div_dual_eq hcN hu, Nat.mul_div_cancel u hc0]
  have key := geps_conv_kblock_iff_normSq_dual N c hcN χ⁻¹ hχ' (Nat.div_dvd_of_dvd hu)
  rw [inv_inv, Nat.div_div_self hu hL0, e] at key
  exact key.symm

/-! ### 6. 𝓕 G_v：ブロック (c, χ̄) の空間の殻ごとの直交基底 -/

/-- **6a.** 𝓕 G_v の台は D_{N/(vc)}：1_{D_s}·𝓕 G_v = [s = N/(vc)]·𝓕 G_v。 -/
theorem dind_mul_dft_gblock (N c : ℕ) [NeZero N] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) {v : ℕ}
    (hv : v ∣ N / c) (s : ℕ) :
    dind N s * 𝓕 (gblock N c χ v) = if s = N / (v * c) then 𝓕 (gblock N c χ v) else 0 := by
  rw [← dft_geps N s, ← PAG.Part16.dft_conv, geps_conv_gblock N c hcN χ hv s]
  split_ifs
  · rfl
  · exact map_zero _

/-- **6b.** 𝓕 G_v はブロック (c, χ̄) に入る：P_{c,χ̄} 𝓕 G_v = 𝓕 G_v（χ 原始的）。 -/
theorem blockProj_dft_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {v : ℕ} (hv : v ∣ N / c) :
    blockProj N c χ⁻¹ (𝓕 (gblock N c χ v)) = 𝓕 (gblock N c χ v) := by
  rw [← dft_blockProj N c hcN χ hχ, blockProj_gblock N c hcN χ hχ hv]

/-- **6c.** ⟨𝓕 G_v, 𝓕 G_w⟩ = [v = w]·φ(vc)（v, w ∣ N/c）。 -/
theorem inner_dft_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {v w : ℕ} (hv : v ∣ N / c) (hw : w ∣ N / c) :
    ∑ k, starRingEnd ℂ (𝓕 (gblock N c χ v) k) * 𝓕 (gblock N c χ w) k =
      if v = w then (Nat.totient (v * c) : ℂ) else 0 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [PAG.Part39.plancherel, inner_gblock N c hcN χ hv hw]
  split_ifs
  · field_simp
  · rw [mul_zero]

/-! ### 7. ブロックへの射影の空間の殻ごとの形 -/

/-- **7a.** P_{c,χ} f = Σ_{v ∣ L} (1/φ(vc))·⟨H_v, f⟩·H_v（H_v = 𝓕 G′_v、G′_v はブロック (c, χ̄) の G_v。H_v の台は
D_{N/(vc)}。χ 原始的）。 -/
theorem blockProj_eq_sum_dft_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) :
    blockProj N c χ f = ∑ v ∈ (N / c).divisors,
      ((Nat.totient (v * c) : ℂ)⁻¹ * ∑ k, starRingEnd ℂ (𝓕 (gblock N c χ⁻¹ v) k) * f k) •
        𝓕 (gblock N c χ⁻¹ v) := by
  have hχ' : (χ⁻¹).IsPrimitive := PAG.Part16.isPrimitive_inv hχ
  have e1 : ∀ g : ZMod N → ℂ, 𝓕 (blockProj N c χ⁻¹ g) = blockProj N c χ (𝓕 g) := by
    intro g
    have e := dft_blockProj N c hcN χ⁻¹ hχ' g
    rwa [inv_inv] at e
  obtain ⟨h, rfl⟩ : ∃ h : ZMod N → ℂ, 𝓕 h = f := ⟨𝓕⁻ f, LinearEquiv.apply_symm_apply _ f⟩
  rw [← e1 h, blockProj_eq_blockProjG N c hcN χ⁻¹ hχ' h]
  unfold blockProjG
  rw [map_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [map_smul, PAG.Part39.plancherel]
  congr 1
  ring

/-- **7b. 空間の殻の成分**：v ∣ N/c なら 1_{D_{N/(vc)}}·(P f) = (1/φ(vc))·⟨H_v, f⟩·H_v（ほかの v′ の項は消える）。 -/
theorem dind_mul_blockProj_dft_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {v : ℕ} (hv : v ∣ N / c) (f : ZMod N → ℂ) :
    dind N (N / (v * c)) * blockProj N c χ f =
      ((Nat.totient (v * c) : ℂ)⁻¹ * ∑ k, starRingEnd ℂ (𝓕 (gblock N c χ⁻¹ v) k) * f k) •
        𝓕 (gblock N c χ⁻¹ v) := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  rw [blockProj_eq_sum_dft_gblock N c hcN χ hχ f, Finset.mul_sum, Finset.sum_eq_single v]
  · rw [mul_smul_comm, dind_mul_dft_gblock N c hcN χ⁻¹ hv, ite_eq_left rfl]
  · intro w hw hwv
    have hne : ¬(N / (v * c) = N / (w * c)) := fun e =>
      hwv (gblock_shell_inj (Nat.pos_of_ne_zero (NeZero.ne c)) hcN hv (Nat.dvd_of_mem_divisors hw) e).symm
    rw [mul_smul_comm, dind_mul_dft_gblock N c hcN χ⁻¹ (Nat.dvd_of_mem_divisors hw), ite_eq_right hne, smul_zero]
  · intro h
    exact absurd (Nat.mem_divisors.mpr ⟨hv, hL0⟩) h

end PAG.Part217

#print axioms PAG.Part217.div_div_swap
#print axioms PAG.Part217.div_dual_eq
#print axioms PAG.Part217.gket_congr2
#print axioms PAG.Part217.inner_smul_left'
#print axioms PAG.Part217.inner_kblock_blockProj'
#print axioms PAG.Part217.fcoef
#print axioms PAG.Part217.fcoef_ne_zero
#print axioms PAG.Part217.dft_kblock
#print axioms PAG.Part217.kblock_inv_eq_dft
#print axioms PAG.Part217.eq_blockProj_of_inner
#print axioms PAG.Part217.dft_blockProj_eq_sum
#print axioms PAG.Part217.dft_blockProj
#print axioms PAG.Part217.dind_mul_blockProj
#print axioms PAG.Part217.blockProj_dind_mul_kblock
#print axioms PAG.Part217.geps_conv_kblock_iff_normSq_dual
#print axioms PAG.Part217.normSq_kblock_iff_geps_conv_dual
#print axioms PAG.Part217.dind_mul_dft_gblock
#print axioms PAG.Part217.blockProj_dft_gblock
#print axioms PAG.Part217.inner_dft_gblock
#print axioms PAG.Part217.blockProj_eq_sum_dft_gblock
#print axioms PAG.Part217.dind_mul_blockProj_dft_gblock
