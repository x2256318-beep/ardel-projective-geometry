/-
  PAG 2.0 Part 219（2026-10-29）— 導手の違うブロックの間の Hom = 0（スペクトルのかなめ）
  ブロック (c, χ)・(c′, χ′)（χ は法 c、χ′ は法 c′ の原始指標、c, c′ ∣ N）、L = N/c、L′ = N/c′
  V = V_{c,χ}、V′ = V_{c′,χ′}、W(d) = W_{c,χ}(d)、W′(d′) = W_{c′,χ′}(d′)（Part 216）
  G_v（Part 210、E_{N/(vc)} の固有ベクトル）、H_w = 𝓕 G′_w（Part 213、D_{N/(wc)} の固有ベクトル）
  0. スペクトル：f ∈ W(d) で ε_s ⋆ f ≠ 0 なら s = N/(vc)（v は d の層）。1_{D_s}·f ≠ 0 なら s = N/(wc)（d の層）
  1. かなめ：G_d ∈ W(d)（E_{N/(dc)} で動かない）、H_{L/d} ∈ W(d)（D_d で動かない、N/((L/d)c) = d）、H_w ≠ 0
  2. 成分の上だけで可換な写像：0 でない元を 0 に写せば全体で 0。0 でなければ W′(d′) の上への写像
  3. 主定理：c ≠ c′ なら、W(d) の上で E_s・D_s と可換で W(d) を W′(d′) に写す写像は 0
     （かなめを行き来させると d = d′、dc = d m′ c′、d m c = d c′ となり c = c′）。
     W(d) を V′ に写すもの（層の射影で分ける）、V を V′ に写すものも 0。
     成分の分類：(c, d) ≠ (c′, d′) なら Hom = 0（c = c′ のときは Part 218 のねじりで Part 217 に帰着）
  4. 型つき：c ≠ c′ なら blockHom(χ, χ′) = 0。dim blockHom(χ, χ′) = [c = c′]·Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)
-/
import PAG222

namespace PAG.Part223

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 成分のスペクトル -/

/-- **0a. E 側**：f ∈ W(d)（rad(d) ∣ c）で ε_s ⋆ f ≠ 0 なら、ある v ∣ N/c（v は d の層）で s = N/(vc)。 -/
theorem exists_of_geps_conv_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hd : RadDvd d c) {f : ZMod N → ℂ} (hf : f ∈ layerPart N c χ d) (s : ℕ)
    (hs : PAG.Part15.conv (geps N s) f ≠ 0) :
    ∃ v : ℕ, v ∣ N / c ∧ InLayer c d v ∧ s = N / (v * c) := by
  have hPf := blockProj_of_mem N c hcN χ hχ ((mem_layerPart N c χ d f).mp hf).1
  by_cases hex : ∃ v ∈ (N / c).divisors, s = N / (v * c)
  · obtain ⟨v, hv, rfl⟩ := hex
    have hv' : v ∣ N / c := Nat.dvd_of_mem_divisors hv
    refine ⟨v, hv', ?_, rfl⟩
    by_contra hvd
    apply hs
    rw [← hPf, geps_conv_blockProj_gblock N c hcN χ hχ hv' f,
      inner_gblock_eq_zero_of_not_inLayer N c hcN χ hχ hv' hd hvd hf, mul_zero, zero_smul]
  · push Not at hex
    apply absurd _ hs
    rw [← hPf]
    exact geps_conv_blockProj_eq_zero N c hcN χ hχ s hex f

/-- **0b.** f ∈ W(d)（rad(d) ∣ c、d > 0）で ⟨H_w, f⟩ ≠ 0 なら N/(wc) は d の層。 -/
theorem layer_of_inner_dft_gblock_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) {d w : ℕ} (hd : RadDvd d c) (hd0 : 0 < d) (hw : w ∣ N / c)
    {f : ZMod N → ℂ} (hf : f ∈ layerPart N c χ d)
    (h : ∑ k, starRingEnd ℂ (𝓕 (gblock N c χ⁻¹ w) k) * f k ≠ 0) : InLayer c d (N / (w * c)) := by
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hHx : 𝓕 (gblock N c χ⁻¹ w) x ≠ 0 := fun h0 => hx (by rw [h0, map_zero, zero_mul])
  have hfx : f x ≠ 0 := right_ne_zero_of_mul hx
  have hxd : InLayer c d x.val := by
    by_contra hn
    exact hfx (((mem_layerPart N c χ d f).mp hf).2 x hn)
  exact layer_of_dft_gblock N c hcN χ hw hd hd0 x hHx hxd

/-- **0c. D 側**：f ∈ W(d)（rad(d) ∣ c、d > 0）で 1_{D_s}·f ≠ 0 なら、ある w ∣ N/c で s = N/(wc)、
N/(wc) は d の層。 -/
theorem exists_of_dind_mul_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hd : RadDvd d c) (hd0 : 0 < d) {f : ZMod N → ℂ}
    (hf : f ∈ layerPart N c χ d) (s : ℕ) (hs : dind N s * f ≠ 0) :
    ∃ w : ℕ, w ∣ N / c ∧ InLayer c d (N / (w * c)) ∧ s = N / (w * c) := by
  have hPf := blockProj_of_mem N c hcN χ hχ ((mem_layerPart N c χ d f).mp hf).1
  rw [← hPf, blockProj_eq_sum_dft_gblock N c hcN χ hχ f, Finset.mul_sum] at hs
  obtain ⟨w, hw, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  have hw' : w ∣ N / c := Nat.dvd_of_mem_divisors hw
  rw [mul_smul_comm, dind_mul_dft_gblock N c hcN χ⁻¹ hw' s] at hne
  by_cases hsw : s = N / (w * c)
  · refine ⟨w, hw', ?_, hsw⟩
    rw [ite_eq_left hsw] at hne
    have hcoef := (smul_ne_zero_iff.mp hne).1
    exact layer_of_inner_dft_gblock_ne_zero N c hcN χ hd hd0 hw' hf (right_ne_zero_of_mul hcoef)
  · rw [ite_eq_right hsw, smul_zero] at hne
    exact absurd rfl hne

/-! ### 1. かなめ -/

/-- **1a.** d ∣ N/c なら N/((N/c/d)·c) = d。 -/
theorem div_shell_hub {N c d : ℕ} (hN : N ≠ 0) (hc0 : 0 < c) (hcN : c ∣ N) (hdL : d ∣ N / c) :
    N / (N / c / d * c) = d := by
  obtain ⟨k, hk⟩ := hdL
  have hNc : N = c * (N / c) := (Nat.mul_div_cancel' hcN).symm
  have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hN (by rw [hNc, hk, h, mul_zero, mul_zero]))
  have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => hN (by rw [hNc, hk, h, zero_mul, mul_zero]))
  have hN' : N = d * (k * c) := by rw [hNc, hk]; ring
  rw [hk, Nat.mul_div_cancel_left k hd0]
  rw [hN', Nat.mul_div_cancel d (Nat.mul_pos hk0 hc0)]

/-- **1b.** H_{N/c/d} ∈ W(d)（d ∣ N/c。N/((N/c/d)c) = d は d の層）。 -/
theorem dft_gblock_mem_layerPart_hub (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) : 𝓕 (gblock N c χ⁻¹ (N / c / d)) ∈ layerPart N c χ d := by
  have hw : N / c / d ∣ N / c := Nat.div_dvd_of_dvd hdL
  have hsh := div_shell_hub (NeZero.ne N) (Nat.pos_of_ne_zero (NeZero.ne c)) hcN hdL
  refine (mem_layerPart N c χ d _).mpr ⟨dft_gblock_mem N c hcN χ hχ hw, fun x hx => ?_⟩
  by_contra hne
  exact hx (dft_gblock_layer N c hcN χ hw (by rw [hsh]; exact ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩)
    x hne)

/-- **1c.** 1_{D_d}·H_{N/c/d} = H_{N/c/d}。 -/
theorem dind_mul_dft_gblock_hub (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {d : ℕ} (hdL : d ∣ N / c) :
    dind N d * 𝓕 (gblock N c χ⁻¹ (N / c / d)) = 𝓕 (gblock N c χ⁻¹ (N / c / d)) := by
  rw [dind_mul_dft_gblock N c hcN χ⁻¹ (Nat.div_dvd_of_dvd hdL) d,
    ite_eq_left (div_shell_hub (NeZero.ne N) (Nat.pos_of_ne_zero (NeZero.ne c)) hcN hdL).symm]

/-- **1d.** H_w ≠ 0（w ∣ N/c）。 -/
theorem dft_gblock_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) {w : ℕ}
    (hw : w ∣ N / c) : 𝓕 (gblock N c χ⁻¹ w) ≠ 0 := by
  intro h
  apply gblock_ne_zero N c hcN χ⁻¹ hw
  exact (ZMod.dft (N := N) (E := ℂ)).injective (by rw [h, map_zero])

/-! ### 2. 成分の上だけで可換な写像 -/

/-- **2a. 生成**：W(d)（d ∈ D）の 0 でない元 g から、A の元で W(d) のすべての元が得られる。 -/
theorem layerPart_exists_apply_of_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c)
    {g : ZMod N → ℂ} (hg : g ∈ layerPart N c χ d) (hg0 : g ≠ 0) {f : ZMod N → ℂ}
    (hf : f ∈ layerPart N c χ d) : ∃ S ∈ shellAlg N, S g = f := by
  let W : Submodule ℂ (ZMod N → ℂ) := (Subalgebra.toSubmodule (shellAlg N)).map (LinearMap.applyₗ g)
  have hmem : ∀ h, h ∈ W ↔ ∃ S ∈ shellAlg N, S g = h := by
    intro h
    simp only [W, Submodule.mem_map, Subalgebra.mem_toSubmodule, LinearMap.applyₗ_apply_apply]
  have hinvd := (shellInvariant_iff N (layerPart N c χ d)).mp (layerPart_shellInvariant N c hcN χ hχ hd)
  have hWinv : ShellInvariant W := by
    intro s h hh
    obtain ⟨S, hS, rfl⟩ := (hmem h).mp hh
    constructor
    · refine (hmem _).mpr ⟨PAG.Part15.convL (geps N s) * S, ?_, rfl⟩
      refine Subalgebra.mul_mem _ ?_ hS
      unfold shellAlg
      exact Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)
    · refine (hmem _).mpr ⟨LinearMap.mulLeft ℂ (dind N s) * S, ?_, rfl⟩
      refine Subalgebra.mul_mem _ ?_ hS
      unfold shellAlg
      exact Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)
  have hWd : W ≤ layerPart N c χ d := by
    intro h hh
    obtain ⟨S, hS, rfl⟩ := (hmem h).mp hh
    exact hinvd S hS _ hg
  have hgW : g ∈ W := (hmem _).mpr ⟨1, Subalgebra.one_mem _, rfl⟩
  rcases layerPart_irreducible N c hcN χ hχ hdL hd W hWinv hWd with h | h
  · exfalso
    rw [h, Submodule.mem_bot] at hgW
    exact hg0 hgW
  · rw [← h] at hf
    exact (hmem f).mp hf

/-- **2b.** T が W(d) の上で E_s・D_s と可換で、W(d) の 0 でない元 g を 0 に写すなら、T は W(d) の上で 0。 -/
theorem layerPart_eq_zero_of_apply_eq_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c)
    (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d,
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d, T (dind N s * f) = dind N s * T f)
    {g : ZMod N → ℂ} (hg : g ∈ layerPart N c χ d) (hg0 : g ≠ 0) (hTg : T g = 0) :
    ∀ f ∈ layerPart N c χ d, T f = 0 := by
  intro f hf
  obtain ⟨S, hS, rfl⟩ := layerPart_exists_apply_of_ne_zero N c hcN χ hχ hdL hd hg hg0 hf
  rw [commute_shellAlg_on N (layerPart_shellInvariant N c hcN χ hχ hd) T hTE hTD hS g hg, hTg, map_zero]

/-- **2c. 上への写像**：T が W(d) の上で E_s・D_s と可換で W(d) を W′(d′) に写し、W(d) の上で 0 でないなら、
W′(d′) の元はすべて T f（f ∈ W(d)）の形。 -/
theorem layerPart_surj_of_commute (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    {d d' : ℕ} (hd : RadDvd d c) (hd'L : d' ∣ N / c') (hd' : RadDvd d' c') (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d,
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d, T (dind N s * f) = dind N s * T f)
    (hT : ∀ f ∈ layerPart N c χ d, T f ∈ layerPart N c' χ' d')
    (hne : ∃ f ∈ layerPart N c χ d, T f ≠ 0) :
    ∀ g ∈ layerPart N c' χ' d', ∃ f ∈ layerPart N c χ d, T f = g := by
  have hinv := layerPart_shellInvariant N c hcN χ hχ hd
  let Wi : Submodule ℂ (ZMod N → ℂ) := (layerPart N c χ d).map T
  have hWi : ShellInvariant Wi := by
    intro s y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    exact ⟨Submodule.mem_map.mpr ⟨_, (hinv s f hf).1, hTE s f hf⟩,
      Submodule.mem_map.mpr ⟨_, (hinv s f hf).2, hTD s f hf⟩⟩
  have hle : Wi ≤ layerPart N c' χ' d' := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    exact hT f hf
  rcases layerPart_irreducible N c' hc'N χ' hχ' hd'L hd' Wi hWi hle with h | h
  · exfalso
    obtain ⟨f, hf, hTf⟩ := hne
    have hTfW : T f ∈ Wi := Submodule.mem_map.mpr ⟨f, hf, rfl⟩
    rw [h, Submodule.mem_bot] at hTfW
    exact hTf hTfW
  · intro g hg
    rw [← h] at hg
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hg
    exact ⟨f, hf, rfl⟩

/-! ### 3. 主定理：導手の違う成分の間の写像は 0 -/

/-- **3a. 算術**：d > 0、d が d′ の層（法 c′）、d′ が d の層（法 c）なら d = d′。 -/
theorem eq_of_inLayer_inLayer {c c' d d' : ℕ} (hd0 : 0 < d) (h1 : InLayer c' d' d) (h2 : InLayer c d d') :
    d = d' := by
  obtain ⟨e', he', -⟩ := h1
  obtain ⟨e, he, -⟩ := h2
  have h : d * (e * e') = d * 1 := by rw [mul_one, ← mul_assoc, ← he, ← he']
  have he1 : e = 1 := Nat.eq_one_of_mul_eq_one_right (Nat.eq_of_mul_eq_mul_left hd0 h)
  rw [he, he1, mul_one]

/-- **3b. 算術**：N/(dc) = N/(d m′ c′)、N/(d m c) = N/(d c′)（どれも N を割る）なら c = c′。 -/
theorem conductor_eq_of_shells {N c c' d m m' : ℕ} (hN : N ≠ 0) (hd0 : 0 < d) (hc0 : 0 < c)
    (h1 : d * c ∣ N) (h1' : d * m' * c' ∣ N) (h2 : d * m * c ∣ N) (h2' : d * c' ∣ N)
    (e1 : N / (d * c) = N / (d * m' * c')) (e2 : N / (d * m * c) = N / (d * c')) : c = c' := by
  have k1 : d * c = d * m' * c' := by
    rw [← Nat.div_div_self h1 hN, e1, Nat.div_div_self h1' hN]
  have k2 : d * m * c = d * c' := by
    rw [← Nat.div_div_self h2 hN, e2, Nat.div_div_self h2' hN]
  have k1' : c = m' * c' := by
    apply Nat.eq_of_mul_eq_mul_left hd0
    rw [k1, mul_assoc]
  have k2' : m * c = c' := by
    apply Nat.eq_of_mul_eq_mul_left hd0
    rw [← mul_assoc, k2]
  have hm : m' * m * c = 1 * c := by rw [one_mul, mul_assoc, k2', ← k1']
  have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_left (Nat.eq_of_mul_eq_mul_right hc0 hm)
  rw [← k2', hm1, one_mul]

/-- **3c. 主定理（成分）**：c ≠ c′ なら、W_{c,χ}(d) の上で E_s・D_s と可換で W_{c,χ}(d) を W_{c′,χ′}(d′) に
写す写像 T は、W_{c,χ}(d) の上で 0。 -/
theorem layerPart_hom_eq_zero_of_ne (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    (hcc : c ≠ c') {d d' : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) (hd'L : d' ∣ N / c') (hd' : RadDvd d' c')
    (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d,
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d, T (dind N s * f) = dind N s * T f)
    (hT : ∀ f ∈ layerPart N c χ d, T f ∈ layerPart N c' χ' d') :
    ∀ f ∈ layerPart N c χ d, T f = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨f₀, hf₀, hTf₀⟩ := hcon
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hc'0 : 0 < c' := Nat.pos_of_ne_zero (NeZero.ne c')
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hL'0 : 0 < N / c' := Nat.div_pos (Nat.le_of_dvd hN0 hc'N) hc'0
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdL hL0
  have hd'0 : 0 < d' := Nat.pos_of_dvd_of_pos hd'L hL'0
  -- W(d) のかなめ
  have hGd : gblock N c χ d ∈ layerPart N c χ d :=
    gblock_mem_layerPart N c hcN χ hχ hdL hd ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩
  have hH := dft_gblock_mem_layerPart_hub N c hcN χ hχ hdL
  have hTG : T (gblock N c χ d) ≠ 0 := fun h =>
    hTf₀ (layerPart_eq_zero_of_apply_eq_zero N c hcN χ hχ hdL hd T hTE hTD hGd (gblock_ne_zero N c hcN χ hdL) h
      f₀ hf₀)
  have hTH : T (𝓕 (gblock N c χ⁻¹ (N / c / d))) ≠ 0 := fun h =>
    hTf₀ (layerPart_eq_zero_of_apply_eq_zero N c hcN χ hχ hdL hd T hTE hTD hH
      (dft_gblock_ne_zero N c hcN χ (Nat.div_dvd_of_dvd hdL)) h f₀ hf₀)
  -- (i) E 側の最大 N/(dc) は W′(d′) にもある
  have hEG : PAG.Part15.conv (geps N (N / (d * c))) (gblock N c χ d) = gblock N c χ d := by
    rw [geps_conv_gblock N c hcN χ hdL, ite_eq_left rfl]
  obtain ⟨v', hv'L, hv'd', hv's⟩ := exists_of_geps_conv_ne_zero N c' hc'N χ' hχ' hd' (hT _ hGd) (N / (d * c))
    (by rw [← hTE (N / (d * c)) _ hGd, hEG]; exact hTG)
  -- (iii) D 側の最小 d は W′(d′) にもある
  obtain ⟨w', hw'L, hw'd', hw's⟩ := exists_of_dind_mul_ne_zero N c' hc'N χ' hχ' hd' hd'0 (hT _ hH) d
    (by rw [← hTD d _ hH, dind_mul_dft_gblock_hub N c hcN χ hdL]; exact hTH)
  -- 上への写像
  have hsurj := layerPart_surj_of_commute N c c' hcN hc'N χ χ' hχ hχ' hd hd'L hd' T hTE hTD hT ⟨f₀, hf₀, hTf₀⟩
  -- (ii) W′(d′) の E 側の最大 N/(d′c′) は W(d) にもある
  obtain ⟨f₁, hf₁, hTf₁⟩ := hsurj _
    (gblock_mem_layerPart N c' hc'N χ' hχ' hd'L hd' ⟨1, (mul_one d').symm, Nat.coprime_one_left c'⟩)
  have hEf₁ : PAG.Part15.conv (geps N (N / (d' * c'))) f₁ ≠ 0 := by
    intro h0
    apply gblock_ne_zero N c' hc'N χ' hd'L
    have h1 := hTE (N / (d' * c')) f₁ hf₁
    rw [h0, map_zero, hTf₁, geps_conv_gblock N c' hc'N χ' hd'L, ite_eq_left rfl] at h1
    exact h1.symm
  obtain ⟨v, hvL, hvd, hvs⟩ := exists_of_geps_conv_ne_zero N c hcN χ hχ hd hf₁ _ hEf₁
  -- (iv) W′(d′) の D 側の最小 d′ は W(d) にもある
  obtain ⟨f₂, hf₂, hTf₂⟩ := hsurj _ (dft_gblock_mem_layerPart_hub N c' hc'N χ' hχ' hd'L)
  have hDf₂ : dind N d' * f₂ ≠ 0 := by
    intro h0
    apply dft_gblock_ne_zero N c' hc'N χ' (Nat.div_dvd_of_dvd hd'L)
    have h1 := hTD d' f₂ hf₂
    rw [h0, map_zero, hTf₂, dind_mul_dft_gblock_hub N c' hc'N χ' hd'L] at h1
    exact h1.symm
  obtain ⟨w, hwL, hwd, hws⟩ := exists_of_dind_mul_ne_zero N c hcN χ hχ hd hd0 hf₂ d' hDf₂
  -- 算術：d = d′、そして c = c′
  have h3 : InLayer c' d' d := by rw [hw's]; exact hw'd'
  have h4 : InLayer c d d' := by rw [hws]; exact hwd
  have hdd : d = d' := eq_of_inLayer_inLayer hd0 h3 h4
  subst hdd
  obtain ⟨m', hv'm, -⟩ := hv'd'
  obtain ⟨m, hvm, -⟩ := hvd
  have hdc : d * c ∣ N := by
    have := (Nat.dvd_div_iff_mul_dvd hcN).mp hdL
    rwa [mul_comm] at this
  have hdc' : d * c' ∣ N := by
    have := (Nat.dvd_div_iff_mul_dvd hc'N).mp hd'L
    rwa [mul_comm] at this
  have hv'c' : d * m' * c' ∣ N := by
    have := (Nat.dvd_div_iff_mul_dvd hc'N).mp hv'L
    rwa [mul_comm, hv'm] at this
  have hvc : d * m * c ∣ N := by
    have := (Nat.dvd_div_iff_mul_dvd hcN).mp hvL
    rwa [mul_comm, hvm] at this
  rw [hv'm] at hv's
  rw [hvm] at hvs
  exact hcc (conductor_eq_of_shells (NeZero.ne N) hd0 hc0 hdc hv'c' hvc hdc' hv's hvs.symm)

/-- **3d.** c ≠ c′ なら、W_{c,χ}(d) の上で E_s・D_s と可換で W_{c,χ}(d) を V_{c′,χ′} に写す写像は
W_{c,χ}(d) の上で 0（像を層の射影で W′(d′) に分ける）。 -/
theorem layerPart_hom_blockSpan_eq_zero_of_ne (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N)
    (hc'N : c' ∣ N) (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive)
    (hχ' : χ'.IsPrimitive) (hcc : c ≠ c') {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c)
    (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d,
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d, T (dind N s * f) = dind N s * T f)
    (hT : ∀ f ∈ layerPart N c χ d, T f ∈ blockSpan N c' χ') :
    ∀ f ∈ layerPart N c χ d, T f = 0 := by
  intro f hf
  rw [← sum_layerInd_mul N c' hc'N χ' (hT f hf)]
  refine Finset.sum_eq_zero (fun d' hd'I => ?_)
  obtain ⟨hd'D, hd'⟩ := (mem_layerIdx c' (N / c') d').mp hd'I
  have key := layerPart_hom_eq_zero_of_ne N c c' hcN hc'N χ χ' hχ hχ' hcc hdL hd (Nat.dvd_of_mem_divisors hd'D) hd'
    (LinearMap.mulLeft ℂ (layerInd N c' d') ∘ₗ T)
    (fun s g hg => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [hTE s g hg]
      exact layerInd_mul_geps_conv N c' hc'N χ' hχ' hd' s (hT g hg))
    (fun s g hg => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [hTD s g hg]
      exact mul_left_comm _ _ _)
    (fun g hg => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact layerInd_mul_mem N c' hc'N χ' hd' (hT g hg))
    f hf
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply] using key

/-- **3e.** c ≠ c′ なら、V_{c,χ} の上で E_s・D_s と可換で V_{c,χ} を V_{c′,χ′} に写す写像は V_{c,χ} の上で 0。 -/
theorem blockSpan_hom_eq_zero_of_ne (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    (hcc : c ≠ c') (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ blockSpan N c χ,
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ blockSpan N c χ, T (dind N s * f) = dind N s * T f)
    (hT : ∀ f ∈ blockSpan N c χ, T f ∈ blockSpan N c' χ') :
    ∀ f ∈ blockSpan N c χ, T f = 0 := by
  intro f hf
  rw [← sum_layerInd_mul N c hcN χ hf, map_sum]
  refine Finset.sum_eq_zero (fun d hdI => ?_)
  obtain ⟨hdD, hd⟩ := (mem_layerIdx c (N / c) d).mp hdI
  have hW : ∀ g ∈ layerPart N c χ d, g ∈ blockSpan N c χ := fun g hg => ((mem_layerPart N c χ d g).mp hg).1
  exact layerPart_hom_blockSpan_eq_zero_of_ne N c c' hcN hc'N χ χ' hχ hχ' hcc (Nat.dvd_of_mem_divisors hdD) hd T
    (fun s g hg => hTE s g (hW g hg)) (fun s g hg => hTD s g (hW g hg)) (fun g hg => hT g (hW g hg))
    _ (layerInd_mul_mem N c hcN χ hd hf)

/-- **3f. 成分の分類**：(c, d) ≠ (c′, d′) なら、W_{c,χ}(d) の上で E_s・D_s と可換で W_{c,χ}(d) を
W_{c′,χ′}(d′) に写す写像は 0（c = c′ なら Part 218 のねじりで同じブロックに戻し、Part 217 を使う）。
(c, d) = (c′, d′) なら W_{c,χ}(d) ≅ W_{c′,χ′}(d′)（Part 218 の `block_twist_iso`）。 -/
theorem layerPart_hom_eq_zero_of_index_ne (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N)
    (hc'N : c' ∣ N) (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive)
    (hχ' : χ'.IsPrimitive) {d d' : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) (hd'L : d' ∣ N / c')
    (hd' : RadDvd d' c') (hne : c ≠ c' ∨ d ≠ d') (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d,
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d, T (dind N s * f) = dind N s * T f)
    (hT : ∀ f ∈ layerPart N c χ d, T f ∈ layerPart N c' χ' d') :
    ∀ f ∈ layerPart N c χ d, T f = 0 := by
  by_cases hcc : c = c'
  · subst hcc
    have hdd : d ≠ d' := hne.resolve_left (fun h => h rfl)
    intro f hf
    -- Θ′ = Θ_{χ′→χ} を合わせると W_χ(d) → W_χ(d′) の写像
    have key := layerPart_hom_eq_zero_of_commute N c hcN χ hχ hdL hd hd' hdd
      (LinearMap.mulLeft ℂ (twistFn N c χ' χ) ∘ₗ T)
      (fun s g hg => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
        rw [hTE s g hg]
        exact twistFn_mul_geps_conv N c hcN χ' χ hχ' hχ s ((mem_layerPart N c χ' d' _).mp (hT g hg)).1)
      (fun s g hg => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
        rw [hTD s g hg]
        exact mul_left_comm _ _ _)
      (fun g hg => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
        exact twistFn_mul_mem_layerPart N c hcN χ' χ (hT g hg))
      f hf
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at key
    rw [← twistFn_mul_twistFn N c hcN χ' χ ((mem_layerPart N c χ' d' _).mp (hT f hf)).1, key, mul_zero]
  · exact layerPart_hom_eq_zero_of_ne N c c' hcN hc'N χ χ' hχ hχ' hcc hdL hd hd'L hd' T hTE hTD hT

/-! ### 4. 型つき：ブロックの間の A 準同型の空間 -/

/-- V_{c,χ} → V_{c′,χ′} の線形写像 T を空間全体に延ばしたもの：f ↦ T(P f)（P はブロックへの射影）。 -/
noncomputable def blockHomExt (N c c' : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c)
    (χ' : DirichletCharacter ℂ c') (T : blockSpan N c χ →ₗ[ℂ] blockSpan N c' χ') : Module.End ℂ (ZMod N → ℂ) :=
  (blockSpan N c' χ').subtype ∘ₗ T ∘ₗ LinearMap.codRestrict (blockSpan N c χ) (blockProjL N c χ) (blockProjL_mem N c χ)

/-- **4a.** f ∈ V_{c,χ} なら（T の延長）(f) = T f。 -/
theorem blockHomExt_apply (N c c' : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (T : blockSpan N c χ →ₗ[ℂ] blockSpan N c' χ')
    {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) : blockHomExt N c c' χ χ' T f = (T ⟨f, hf⟩ : ZMod N → ℂ) := by
  have hc : LinearMap.codRestrict (blockSpan N c χ) (blockProjL N c χ) (blockProjL_mem N c χ) f = ⟨f, hf⟩ :=
    Subtype.ext (by rw [LinearMap.codRestrict_apply, blockProjL_apply, blockProj_of_mem N c hcN χ hχ hf])
  simp only [blockHomExt, LinearMap.comp_apply, Submodule.subtype_apply, hc]

/-- **4b.** c ≠ c′ なら blockHom(χ, χ′) = 0（導手の違うブロックの間の A 準同型は 0）。 -/
theorem blockHom_eq_bot_of_ne (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    (hcc : c ≠ c') : blockHom N c c' χ χ' = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro T hT
  have hinv := blockSpan_shellInvariant N c hcN χ hχ
  have hz := blockSpan_hom_eq_zero_of_ne N c c' hcN hc'N χ χ' hχ hχ' hcc (blockHomExt N c c' χ χ' T)
    (fun s g hg => by
      rw [blockHomExt_apply N c c' hcN χ χ' hχ T (hinv s g hg).1, blockHomExt_apply N c c' hcN χ χ' hχ T hg]
      exact ((mem_blockHom N c c' χ χ' T).mp hT s g hg).1 (hinv s g hg).1)
    (fun s g hg => by
      rw [blockHomExt_apply N c c' hcN χ χ' hχ T (hinv s g hg).2, blockHomExt_apply N c c' hcN χ χ' hχ T hg]
      exact ((mem_blockHom N c c' χ χ' T).mp hT s g hg).2 (hinv s g hg).2)
    (fun g hg => by
      rw [blockHomExt_apply N c c' hcN χ χ' hχ T hg]
      exact (T ⟨g, hg⟩).2)
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  have h1 := hz f f.2
  rw [blockHomExt_apply N c c' hcN χ χ' hχ T f.2] at h1
  rw [LinearMap.zero_apply, Submodule.coe_zero]
  exact h1

/-- **4c.** c ≠ c′ なら dim blockHom(χ, χ′) = 0。 -/
theorem finrank_blockHom_of_ne (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    (hcc : c ≠ c') : Module.finrank ℂ (blockHom N c c' χ χ') = 0 := by
  rw [blockHom_eq_bot_of_ne N c c' hcN hc'N χ χ' hχ hχ' hcc, finrank_bot]

/-- **4d. ブロックの間の Hom の次元（まとめ）**：dim blockHom(χ, χ′) = [c = c′]·Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)
（Part 214 で数値だけだった dim Hom_A = [c = c′]π(c)）。 -/
theorem finrank_blockHom_eq_ite (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) :
    Module.finrank ℂ (blockHom N c c' χ χ') =
      if c = c' then ∏ p ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization p + 1) else 0 := by
  by_cases hcc : c = c'
  · subst hcc
    rw [ite_eq_left rfl, finrank_blockHom_eq_prod N c hcN χ χ' hχ hχ']
  · rw [ite_eq_right hcc, finrank_blockHom_of_ne N c c' hcN hc'N χ χ' hχ hχ' hcc]

end PAG.Part223

#print axioms PAG.Part223.exists_of_geps_conv_ne_zero
#print axioms PAG.Part223.layer_of_inner_dft_gblock_ne_zero
#print axioms PAG.Part223.exists_of_dind_mul_ne_zero
#print axioms PAG.Part223.div_shell_hub
#print axioms PAG.Part223.dft_gblock_mem_layerPart_hub
#print axioms PAG.Part223.dind_mul_dft_gblock_hub
#print axioms PAG.Part223.dft_gblock_ne_zero
#print axioms PAG.Part223.layerPart_exists_apply_of_ne_zero
#print axioms PAG.Part223.layerPart_eq_zero_of_apply_eq_zero
#print axioms PAG.Part223.layerPart_surj_of_commute
#print axioms PAG.Part223.eq_of_inLayer_inLayer
#print axioms PAG.Part223.conductor_eq_of_shells
#print axioms PAG.Part223.layerPart_hom_eq_zero_of_ne
#print axioms PAG.Part223.layerPart_hom_blockSpan_eq_zero_of_ne
#print axioms PAG.Part223.blockSpan_hom_eq_zero_of_ne
#print axioms PAG.Part223.layerPart_hom_eq_zero_of_index_ne
#print axioms PAG.Part223.blockHomExt
#print axioms PAG.Part223.blockHomExt_apply
#print axioms PAG.Part223.blockHom_eq_bot_of_ne
#print axioms PAG.Part223.finrank_blockHom_of_ne
#print axioms PAG.Part223.finrank_blockHom_eq_ite
