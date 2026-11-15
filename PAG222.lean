/-
  PAG 2.0 Part 218（2026-10-29）— 同じ導手のブロックのねじり同型（掛け算の作用素）
  ブロック (c, χ)・(c, χ′)（χ, χ′ は法 c の原始指標）、L = N/c、V_χ = V_{c,χ}（Part 215 の blockSpan）
  層・W(d)・D（Part 216）、ι_d（Part 217 の layerInd）、可換子 blockComm（Part 217）
  ψ = χ′·χ⁻¹（法 c の指標）、ねじりの関数 Θ = Σ_{d ∈ D} ι_d·ψ(x/d)（def twistFn）
  κ = χ′⁻¹(−1)τ(χ′) / (χ⁻¹(−1)τ(χ))（def twistConst）
  0. Θ の値：x が d の層（d ∈ D）なら Θ(x) = ψ(x/d)
  1. ケット：u ∣ L が d の層なら Θ·k^χ_u = ψ(u/d)·k^{χ′}_u。Θ は V_χ を V_χ′ に、W_χ(d) を W_χ′(d) に写し、
     逆向きのねじり Θ′（χ′ → χ）と合わせて Θ′Θ = 1（V_χ の上）
  2. G：kcoef(M, c, χ′) = κ·kcoef(M, c, χ)、Θ·G^χ_v = κ·ψ(v/d)·G^{χ′}_v。
     V_χ の上で Θ と E_s は可換（D_s とは空間全体で可換。空間全体では E_s と一般に可換でない：数値）
  3. 主定理：Θ は V_χ から V_χ′ への A 加群の同型（成分ごとに W_χ(d) → W_χ′(d)）
  4. ブロックの間の A 準同型の空間（def blockHom）：同じ導手なら blockComm と線形同型で、次元 #D = π(c)
-/
import PAG221

namespace PAG.Part222

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. ねじりの関数 -/

/-- ねじりの関数 Θ = Σ_{d ∈ D} ι_d·ψ(x/d)（ψ = χ′·χ⁻¹）。 -/
noncomputable def twistFn (N c : ℕ) (χ χ' : DirichletCharacter ℂ c) : ZMod N → ℂ :=
  fun x => ∑ d ∈ layerIdx c (N / c), layerInd N c d x * (χ' * χ⁻¹) ((x.val / d : ℕ) : ZMod c)

/-- **0a.** x.val が d の層なら ι_d(x) = 1。 -/
theorem layerInd_apply_of_inLayer (N c d : ℕ) {x : ZMod N} (hx : InLayer c d x.val) : layerInd N c d x = 1 := by
  simp only [layerInd]
  exact ite_eq_left hx

/-- **0b.** x.val が d の層でなければ ι_d(x) = 0。 -/
theorem layerInd_apply_of_not_inLayer (N c d : ℕ) {x : ZMod N} (hx : ¬ InLayer c d x.val) :
    layerInd N c d x = 0 := by
  simp only [layerInd]
  exact ite_eq_right hx

/-- **0c.** x が d の層（d ∈ D）なら Θ(x) = ψ(x/d)。 -/
theorem twistFn_apply (N c : ℕ) (χ χ' : DirichletCharacter ℂ c) {d : ℕ} (hdI : d ∈ layerIdx c (N / c))
    {x : ZMod N} (hx : InLayer c d x.val) :
    twistFn N c χ χ' x = (χ' * χ⁻¹) ((x.val / d : ℕ) : ZMod c) := by
  have hd := ((mem_layerIdx c (N / c) d).mp hdI).2
  unfold twistFn
  rw [Finset.sum_eq_single d]
  · rw [layerInd_apply_of_inLayer N c d hx, one_mul]
  · intro d' hd' hne
    have hd'' := ((mem_layerIdx c (N / c) d').mp hd').2
    have hx' : ¬ InLayer c d' x.val := fun h => hne (layer_unique hd'' hd h hx)
    rw [layerInd_apply_of_not_inLayer N c d' hx', zero_mul]
  · intro h
    exact absurd hdI h

/-! ### 1. ケットのねじり -/

/-- **1a.** u ∣ N/c が d の層（rad(d) ∣ c）なら Θ·k^χ_u = ψ(u/d)·k^{χ′}_u。 -/
theorem twistFn_mul_kblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    {u d : ℕ} (hu : u ∣ N / c) (hd : RadDvd d c) (hud : InLayer c d u) :
    twistFn N c χ χ' * kblock N c χ u = (χ' * χ⁻¹) ((u / d : ℕ) : ZMod c) • kblock N c χ' u := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hu0 : 0 < u := Nat.pos_of_dvd_of_pos hu hL0
  obtain ⟨m, hum, hmc⟩ := hud
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos ⟨m, hum⟩ hu0
  have hdI : d ∈ layerIdx c (N / c) :=
    (mem_layerIdx c (N / c) d).mpr ⟨Nat.mem_divisors.mpr ⟨dvd_trans ⟨m, hum⟩ hu, hL0.ne'⟩, hd⟩
  have hud' : u / d = m := by rw [hum, Nat.mul_div_cancel_left m hd0]
  obtain ⟨h1, h2⟩ := block_dvd hcN hu
  funext x
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, kblock_of_dvd N c χ h1 h2, kblock_of_dvd N c χ' h1 h2,
    gket_apply, gket_apply]
  by_cases hux : u ∣ x.val
  · rw [ite_eq_left hux, ite_eq_left hux]
    obtain ⟨a, ha⟩ := hux
    have hxa : x.val / u = a := by rw [ha, Nat.mul_div_cancel_left a hu0]
    rw [hxa, hud']
    by_cases hac : Nat.Coprime a c
    · have hxd : InLayer c d x.val := ⟨m * a, by rw [ha, hum, mul_assoc], Nat.Coprime.mul_left hmc hac⟩
      have hxd' : x.val / d = m * a := by rw [ha, hum, mul_assoc, Nat.mul_div_cancel_left _ hd0]
      rw [twistFn_apply N c χ χ' hdI hxd, hxd']
      have hunit : χ⁻¹ (a : ZMod c) * χ (a : ZMod c) = 1 := by
        rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply ((ZMod.isUnit_iff_coprime a c).mpr hac)]
      have e1 : (χ' * χ⁻¹) ((m * a : ℕ) : ZMod c) =
          (χ' * χ⁻¹) (m : ZMod c) * (χ' (a : ZMod c) * χ⁻¹ (a : ZMod c)) := by
        rw [Nat.cast_mul, map_mul, MulChar.mul_apply χ' χ⁻¹ (a : ZMod c)]
      rw [e1]
      linear_combination ((χ' * χ⁻¹) (m : ZMod c) * χ' (a : ZMod c) *
        (((Real.sqrt (Nat.totient (N / u)))⁻¹ : ℝ) : ℂ)) * hunit
    · have h0 : χ (a : ZMod c) = 0 :=
        MulChar.map_nonunit _ (fun h => hac ((ZMod.isUnit_iff_coprime a c).mp h))
      have h0' : χ' (a : ZMod c) = 0 :=
        MulChar.map_nonunit _ (fun h => hac ((ZMod.isUnit_iff_coprime a c).mp h))
      simp only [h0, h0', mul_zero]
  · rw [ite_eq_right hux, ite_eq_right hux, mul_zero, mul_zero]

/-- **1b.** f ∈ V_χ なら Θ·f ∈ V_χ′。 -/
theorem twistFn_mul_mem (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) : twistFn N c χ χ' * f ∈ blockSpan N c χ' := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  unfold blockSpan at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    have hu : (u : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors u.2
    obtain ⟨du, hdu, hudu⟩ := exists_layer c u (Nat.pos_of_dvd_of_pos hu hL0).ne'
    show twistFn N c χ χ' * kblock N c χ u ∈ blockSpan N c χ'
    rw [twistFn_mul_kblock N c hcN χ χ' hu hdu hudu]
    have hk : kblock N c χ' u ∈ blockSpan N c χ' := by
      unfold blockSpan
      exact Submodule.subset_span ⟨u, rfl⟩
    exact Submodule.smul_mem _ _ hk
  | zero =>
    rw [mul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact add_mem hx hy
  | smul r x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hx

/-- **1c.** f ∈ V_χ なら Θ′·(Θ·f) = f（Θ′ は逆向きのねじり χ′ → χ）。 -/
theorem twistFn_mul_twistFn (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) :
    twistFn N c χ' χ * (twistFn N c χ χ' * f) = f := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hgrp : (χ' * χ⁻¹) * (χ * χ'⁻¹) = 1 := by
    rw [mul_assoc, ← mul_assoc χ⁻¹, inv_mul_cancel, one_mul, mul_inv_cancel]
  unfold blockSpan at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    have hu : (u : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors u.2
    obtain ⟨du, hdu, hudu⟩ := exists_layer c u (Nat.pos_of_dvd_of_pos hu hL0).ne'
    show twistFn N c χ' χ * (twistFn N c χ χ' * kblock N c χ u) = kblock N c χ u
    have hcop : Nat.Coprime ((u : ℕ) / du) c := by
      obtain ⟨m, hum, hmc⟩ := hudu
      have hu0 : 0 < (u : ℕ) := Nat.pos_of_dvd_of_pos hu hL0
      have hd0 : 0 < du := Nat.pos_of_dvd_of_pos ⟨m, hum⟩ hu0
      rw [hum, Nat.mul_div_cancel_left m hd0]
      exact hmc
    rw [twistFn_mul_kblock N c hcN χ χ' hu hdu hudu, mul_smul_comm, twistFn_mul_kblock N c hcN χ' χ hu hdu hudu,
      smul_smul, ← MulChar.mul_apply, hgrp, MulChar.one_apply ((ZMod.isUnit_iff_coprime _ c).mpr hcop), one_smul]
  | zero =>
    rw [mul_zero, mul_zero]
  | add x y _ _ hx hy =>
    rw [mul_add, mul_add, hx, hy]
  | smul r x _ hx =>
    rw [mul_smul_comm, mul_smul_comm, hx]

/-- **1d.** f ∈ W_χ(d) なら Θ·f ∈ W_χ′(d)（Θ は台を変えない）。 -/
theorem twistFn_mul_mem_layerPart (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    {d : ℕ} {f : ZMod N → ℂ} (hf : f ∈ layerPart N c χ d) : twistFn N c χ χ' * f ∈ layerPart N c χ' d :=
  (mem_layerPart N c χ' d _).mpr ⟨twistFn_mul_mem N c hcN χ χ' ((mem_layerPart N c χ d f).mp hf).1,
    fun x hx => by rw [Pi.mul_apply, ((mem_layerPart N c χ d f).mp hf).2 x hx, mul_zero]⟩

/-! ### 2. G のねじりと E_s との可換性 -/

/-- κ = χ′⁻¹(−1)·τ(χ′) / (χ⁻¹(−1)·τ(χ))（kcoef の比）。 -/
noncomputable def twistConst {c : ℕ} [NeZero c] (χ χ' : DirichletCharacter ℂ c) : ℂ :=
  (χ'⁻¹ (-1) * gaussSum χ' stdAddChar) / (χ⁻¹ (-1) * gaussSum χ stdAddChar)

/-- **2a.** kcoef(M, c, χ′) = κ·kcoef(M, c, χ)（M ≠ 0、c ∣ M、χ 原始的）。 -/
theorem kcoef_twist (M c : ℕ) [NeZero c] (hM : M ≠ 0) (hc : c ∣ M) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : kcoef M c χ' = twistConst χ χ' * kcoef M c χ := by
  have hB := kcoef_ne_zero M c hM hc χ hχ
  have hden : χ⁻¹ (-1) * gaussSum χ stdAddChar ≠ 0 := by
    intro h0
    apply hB
    unfold kcoef
    rw [mul_assoc, h0, mul_zero]
  unfold twistConst
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  unfold kcoef
  ring

/-- **2b.** κ ≠ 0（χ, χ′ 原始的）。 -/
theorem twistConst_ne_zero (c : ℕ) [NeZero c] (χ χ' : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive)
    (hχ' : χ'.IsPrimitive) : twistConst χ χ' ≠ 0 := by
  intro h0
  have h := kcoef_twist c c (NeZero.ne c) dvd_rfl χ χ' hχ
  rw [h0, zero_mul] at h
  exact kcoef_ne_zero c c (NeZero.ne c) dvd_rfl χ' hχ' h

/-- **2c.** 係数の恒等式（補助）：μ·a·B⁻¹·ψ = κ·(ψ·(x·a))·(μ·x⁻¹·(κB)⁻¹)（κ, x ≠ 0）。 -/
theorem twist_scalar_aux (μ a B κ ψ x : ℂ) (hκ : κ ≠ 0) (hx : x ≠ 0) :
    μ * a * B⁻¹ * ψ = κ * (ψ * (x * a)) * (μ * x⁻¹ * (κ * B)⁻¹) := by
  rw [mul_inv]
  have h1 : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  have h2 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  linear_combination (-(μ * a * B⁻¹ * ψ)) * h1 + (-(μ * a * B⁻¹ * ψ * (κ * κ⁻¹))) * h2

/-- **2d.** Θ·G^χ_v = κ·ψ(v/d)·G^{χ′}_v（v ∣ N/c が d の層、χ・χ′ 原始的）。 -/
theorem twistFn_mul_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) {v d : ℕ} (hv : v ∣ N / c) (hd : RadDvd d c)
    (hvd : InLayer c d v) :
    twistFn N c χ χ' * gblock N c χ v = (twistConst χ χ' * (χ' * χ⁻¹) ((v / d : ℕ) : ZMod c)) • gblock N c χ' v := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hv0 : 0 < v := Nat.pos_of_dvd_of_pos hv hL0
  obtain ⟨m, hvm, hmc⟩ := hvd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos ⟨m, hvm⟩ hv0
  have hvd' : v / d = m := by rw [hvm, Nat.mul_div_cancel_left m hd0]
  rw [gblock_eq_sum N c hcN χ hχ v hv, gblock_eq_sum N c hcN χ' hχ' v hv, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  have hwv : w ∣ v := Nat.dvd_of_mem_divisors hw
  have hw0 : 0 < w := Nat.pos_of_dvd_of_pos hwv hv0
  have hwL : w ∣ N / c := dvd_trans hwv hv
  obtain ⟨hwN, hcw⟩ := block_dvd hcN hwL
  have hNw : N / w ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hwN
  rw [mul_smul_comm, smul_smul]
  by_cases hcop : Nat.Coprime (v / w) c
  · obtain ⟨k, hk⟩ := hwv
    have hvw : v / w = k := by rw [hk, Nat.mul_div_cancel_left k hw0]
    rw [hvw] at hcop ⊢
    have hdw : d ∣ w := by
      have h1 : d ∣ w * k := by rw [← hk, hvm]; exact Dvd.intro m rfl
      exact (coprime_of_radDvd hd hcop).dvd_of_dvd_mul_right h1
    obtain ⟨m', hwm'⟩ := hdw
    have hm : m = m' * k := by
      have h := hvm.symm.trans hk
      rw [hwm', mul_assoc] at h
      exact Nat.eq_of_mul_eq_mul_left hd0 h
    have hm'c : Nat.Coprime m' c := Nat.Coprime.coprime_dvd_left (Dvd.intro k hm.symm) hmc
    have hwd' : w / d = m' := by rw [hwm', Nat.mul_div_cancel_left m' hd0]
    rw [twistFn_mul_kblock N c hcN χ χ' hwL hd ⟨m', hwm', hm'c⟩, smul_smul, hwd', hvd', hm]
    congr 1
    have hku : IsUnit (k : ZMod c) := (ZMod.isUnit_iff_coprime k c).mpr hcop
    have hunit : χ' (k : ZMod c) * χ'⁻¹ (k : ZMod c) = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply hku]
    have hx0 : χ' (k : ZMod c) ≠ 0 := left_ne_zero_of_mul_eq_one hunit
    have hinv : χ'⁻¹ (k : ZMod c) = (χ' (k : ZMod c))⁻¹ := (inv_eq_of_mul_eq_one_right hunit).symm
    rw [Nat.cast_mul, map_mul (χ' * χ⁻¹), MulChar.mul_apply χ' χ⁻¹ (k : ZMod c), hinv,
      kcoef_twist (N / w) c hNw hcw χ χ' hχ]
    exact twist_scalar_aux _ _ _ _ _ _ (twistConst_ne_zero c χ χ' hχ hχ') hx0
  · have h0 : χ⁻¹ ((v / w : ℕ) : ZMod c) = 0 :=
      MulChar.map_nonunit _ (fun h => hcop ((ZMod.isUnit_iff_coprime _ c).mp h))
    have h0' : χ'⁻¹ ((v / w : ℕ) : ZMod c) = 0 :=
      MulChar.map_nonunit _ (fun h => hcop ((ZMod.isUnit_iff_coprime _ c).mp h))
    simp only [h0, h0', mul_zero, zero_mul, zero_smul]

/-- **2e.** f ∈ V_χ なら Θ·(ε_s ⋆ f) = ε_s ⋆ (Θ·f)（V_χ の上で Θ と E_s は可換）。 -/
theorem twistFn_mul_geps_conv (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) (s : ℕ) {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) :
    twistFn N c χ χ' * PAG.Part15.conv (geps N s) f = PAG.Part15.conv (geps N s) (twistFn N c χ χ' * f) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hadd : ∀ a b : ZMod N → ℂ, PAG.Part15.conv (geps N s) (a + b) =
      PAG.Part15.conv (geps N s) a + PAG.Part15.conv (geps N s) b := fun a b => by
    rw [← PAG.Part15.convL_apply, map_add, PAG.Part15.convL_apply, PAG.Part15.convL_apply]
  have hsmul : ∀ (r : ℂ) (a : ZMod N → ℂ), PAG.Part15.conv (geps N s) (r • a) =
      r • PAG.Part15.conv (geps N s) a := fun r a => by
    rw [← PAG.Part15.convL_apply, map_smul, PAG.Part15.convL_apply]
  have hzero : PAG.Part15.conv (geps N s) (0 : ZMod N → ℂ) = 0 := by
    rw [← PAG.Part15.convL_apply, map_zero]
  rw [blockSpan_eq_span_gblock N c hcN χ hχ] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hv : (v : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors v.2
    obtain ⟨dv, hdv, hvdv⟩ := exists_layer c v (Nat.pos_of_dvd_of_pos hv hL0).ne'
    show twistFn N c χ χ' * PAG.Part15.conv (geps N s) (gblock N c χ v) =
      PAG.Part15.conv (geps N s) (twistFn N c χ χ' * gblock N c χ v)
    rw [twistFn_mul_gblock N c hcN χ χ' hχ hχ' hv hdv hvdv, hsmul, geps_conv_gblock N c hcN χ hv s,
      geps_conv_gblock N c hcN χ' hv s]
    by_cases hs : s = N / ((v : ℕ) * c)
    · rw [ite_eq_left hs, ite_eq_left hs, twistFn_mul_gblock N c hcN χ χ' hχ hχ' hv hdv hvdv]
    · rw [ite_eq_right hs, ite_eq_right hs, mul_zero, smul_zero]
  | zero =>
    rw [hzero, mul_zero, hzero]
  | add x y _ _ hx hy =>
    rw [hadd x y, mul_add (twistFn N c χ χ') (PAG.Part15.conv (geps N s) x) (PAG.Part15.conv (geps N s) y), hx, hy,
      mul_add (twistFn N c χ χ') x y, hadd]
  | smul r x _ hx =>
    rw [hsmul r x, mul_smul_comm r (twistFn N c χ χ') (PAG.Part15.conv (geps N s) x), hx,
      mul_smul_comm r (twistFn N c χ χ') x, hsmul]

/-! ### 3. 主定理：同じ導手のブロックのねじり同型 -/

/-- **3a. ねじり同型**：χ, χ′ が法 c の原始指標なら、Θ = Θ_{χ→χ′} は V_χ を V_χ′ に写し、
Θ_{χ′→χ}·Θ = 1（V_χ の上）、Θ·Θ_{χ′→χ} = 1（V_χ′ の上）、V_χ の上で E_s と、空間全体で D_s と可換で、
成分 W_χ(d) を W_χ′(d) に写す（V_{c,χ} と V_{c,χ′} は A 加群として同型）。 -/
theorem block_twist_iso (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) :
    (∀ f ∈ blockSpan N c χ, twistFn N c χ χ' * f ∈ blockSpan N c χ') ∧
    (∀ f ∈ blockSpan N c χ, twistFn N c χ' χ * (twistFn N c χ χ' * f) = f) ∧
    (∀ g ∈ blockSpan N c χ', twistFn N c χ χ' * (twistFn N c χ' χ * g) = g) ∧
    (∀ (s : ℕ), ∀ f ∈ blockSpan N c χ, twistFn N c χ χ' * PAG.Part15.conv (geps N s) f =
      PAG.Part15.conv (geps N s) (twistFn N c χ χ' * f)) ∧
    (∀ (s : ℕ) (f : ZMod N → ℂ), twistFn N c χ χ' * (dind N s * f) = dind N s * (twistFn N c χ χ' * f)) ∧
    (∀ (d : ℕ), ∀ f ∈ layerPart N c χ d, twistFn N c χ χ' * f ∈ layerPart N c χ' d) :=
  ⟨fun _ hf => twistFn_mul_mem N c hcN χ χ' hf, fun _ hf => twistFn_mul_twistFn N c hcN χ χ' hf,
    fun _ hg => twistFn_mul_twistFn N c hcN χ' χ hg, fun s _ hf => twistFn_mul_geps_conv N c hcN χ χ' hχ hχ' s hf,
    fun _ _ => mul_left_comm _ _ _, fun _ _ hf => twistFn_mul_mem_layerPart N c hcN χ χ' hf⟩

/-! ### 4. ブロックの間の A 準同型の空間 -/

/-- ブロックの間の A 準同型：V_{c,χ} → V_{c′,χ′} の線形写像で、E_s・D_s と可換なもの
（E_s f・D_s f が V_{c,χ} に入るときの式で書く。Part 217 の blockComm と同じ形）。 -/
noncomputable def blockHom (N c c' : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') :
    Submodule ℂ (blockSpan N c χ →ₗ[ℂ] blockSpan N c' χ') where
  carrier := {T | ∀ (s : ℕ) (f : ZMod N → ℂ) (hf : f ∈ blockSpan N c χ),
    (∀ h : PAG.Part15.conv (geps N s) f ∈ blockSpan N c χ,
      (T ⟨_, h⟩ : ZMod N → ℂ) = PAG.Part15.conv (geps N s) (T ⟨f, hf⟩ : ZMod N → ℂ)) ∧
    (∀ h : dind N s * f ∈ blockSpan N c χ,
      (T ⟨_, h⟩ : ZMod N → ℂ) = dind N s * (T ⟨f, hf⟩ : ZMod N → ℂ))}
  add_mem' := by
    intro T₁ T₂ h₁ h₂
    simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
    intro s f hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, (h₁ s f hf).1 h,
        (h₂ s f hf).1 h, ← PAG.Part15.convL_apply, ← PAG.Part15.convL_apply, ← PAG.Part15.convL_apply, map_add]
    · rw [LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, (h₁ s f hf).2 h,
        (h₂ s f hf).2 h, mul_add]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    intro s f hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [LinearMap.zero_apply, LinearMap.zero_apply, Submodule.coe_zero, ← PAG.Part15.convL_apply, map_zero]
    · rw [LinearMap.zero_apply, LinearMap.zero_apply, Submodule.coe_zero, mul_zero]
  smul_mem' := by
    intro r T hT
    simp only [Set.mem_ofPred_eq] at hT ⊢
    intro s f hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, Submodule.coe_smul, (hT s f hf).1 h,
        ← PAG.Part15.convL_apply, ← PAG.Part15.convL_apply, map_smul]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, Submodule.coe_smul, (hT s f hf).2 h,
        mul_smul_comm]

/-- **4a.** A 準同型の判定。 -/
theorem mem_blockHom (N c c' : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c')
    (T : blockSpan N c χ →ₗ[ℂ] blockSpan N c' χ') :
    T ∈ blockHom N c c' χ χ' ↔ ∀ (s : ℕ) (f : ZMod N → ℂ) (hf : f ∈ blockSpan N c χ),
      (∀ h : PAG.Part15.conv (geps N s) f ∈ blockSpan N c χ,
        (T ⟨_, h⟩ : ZMod N → ℂ) = PAG.Part15.conv (geps N s) (T ⟨f, hf⟩ : ZMod N → ℂ)) ∧
      (∀ h : dind N s * f ∈ blockSpan N c χ,
        (T ⟨_, h⟩ : ZMod N → ℂ) = dind N s * (T ⟨f, hf⟩ : ZMod N → ℂ)) := Iff.rfl

/-- V_χ から V_χ′ へのねじり（型つきの線形写像）。 -/
noncomputable def twistV (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c) :
    blockSpan N c χ →ₗ[ℂ] blockSpan N c χ' :=
  (LinearMap.mulLeft ℂ (twistFn N c χ χ')).restrict (fun _ hf => twistFn_mul_mem N c hcN χ χ' hf)

/-- **4b.** (twistV f) = Θ·f。 -/
theorem twistV_apply (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (f : blockSpan N c χ) : (twistV N c hcN χ χ' f : ZMod N → ℂ) = twistFn N c χ χ' * f := rfl

/-- **4c.** S ∈ blockComm(χ) なら Θ∘S ∈ blockHom(χ, χ′)。 -/
theorem twistV_comp_mem_blockHom (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) {S : Module.End ℂ (blockSpan N c χ)} (hS : S ∈ blockComm N c χ) :
    twistV N c hcN χ χ' ∘ₗ S ∈ blockHom N c c χ χ' := by
  rw [mem_blockHom]
  intro s f hf
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, twistV_apply, twistV_apply,
      ((mem_blockComm N c χ S).mp hS s f hf).1 h]
    exact twistFn_mul_geps_conv N c hcN χ χ' hχ hχ' s (S ⟨f, hf⟩).2
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, twistV_apply, twistV_apply,
      ((mem_blockComm N c χ S).mp hS s f hf).2 h]
    exact mul_left_comm _ _ _

/-- **4d.** T ∈ blockHom(χ, χ′) なら Θ′∘T ∈ blockComm(χ)。 -/
theorem twistV_comp_mem_blockComm (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) {T : blockSpan N c χ →ₗ[ℂ] blockSpan N c χ'}
    (hT : T ∈ blockHom N c c χ χ') : twistV N c hcN χ' χ ∘ₗ T ∈ blockComm N c χ := by
  rw [mem_blockComm]
  intro s f hf
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, twistV_apply, twistV_apply,
      ((mem_blockHom N c c χ χ' T).mp hT s f hf).1 h]
    exact twistFn_mul_geps_conv N c hcN χ' χ hχ' hχ s (T ⟨f, hf⟩).2
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, twistV_apply, twistV_apply,
      ((mem_blockHom N c c χ χ' T).mp hT s f hf).2 h]
    exact mul_left_comm _ _ _

/-- **4e. 同じ導手のブロックの間の A 準同型の空間の次元**：dim blockHom(χ, χ′) = #D。 -/
theorem finrank_blockHom (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) :
    Module.finrank ℂ (blockHom N c c χ χ') = (layerIdx c (N / c)).card := by
  let F : blockComm N c χ →ₗ[ℂ] blockHom N c c χ χ' :=
    { toFun := fun S => ⟨twistV N c hcN χ χ' ∘ₗ (S : Module.End ℂ (blockSpan N c χ)),
        twistV_comp_mem_blockHom N c hcN χ χ' hχ hχ' S.2⟩
      map_add' := fun S₁ S₂ => by
        apply Subtype.ext
        exact LinearMap.comp_add _ _ _
      map_smul' := fun r S => by
        apply Subtype.ext
        exact LinearMap.comp_smul _ _ _ }
  let G : blockHom N c c χ χ' →ₗ[ℂ] blockComm N c χ :=
    { toFun := fun T => ⟨twistV N c hcN χ' χ ∘ₗ (T : blockSpan N c χ →ₗ[ℂ] blockSpan N c χ'),
        twistV_comp_mem_blockComm N c hcN χ χ' hχ hχ' T.2⟩
      map_add' := fun T₁ T₂ => by
        apply Subtype.ext
        exact LinearMap.comp_add _ _ _
      map_smul' := fun r T => by
        apply Subtype.ext
        exact LinearMap.comp_smul _ _ _ }
  have hGF : G.comp F = LinearMap.id := by
    apply LinearMap.ext
    intro S
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact twistFn_mul_twistFn N c hcN χ χ' ((S : Module.End ℂ (blockSpan N c χ)) f).2
  have hFG : F.comp G = LinearMap.id := by
    apply LinearMap.ext
    intro T
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact twistFn_mul_twistFn N c hcN χ' χ ((T : blockSpan N c χ →ₗ[ℂ] blockSpan N c χ') f).2
  rw [(LinearEquiv.ofLinearMap G F hGF hFG).finrank_eq, finrank_blockComm N c hcN χ hχ]

/-- **4f.** dim blockHom(χ, χ′) = Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)（同じ導手。Part 214 で数値だけだった
dim Hom_A = [c = c′]π(c) の c = c′ の側）。 -/
theorem finrank_blockHom_eq_prod (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) :
    Module.finrank ℂ (blockHom N c c χ χ') =
      ∏ p ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization p + 1) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  rw [finrank_blockHom N c hcN χ χ' hχ hχ', card_layerIdx c (N / c) hL0.ne']

end PAG.Part222

#print axioms PAG.Part222.twistFn
#print axioms PAG.Part222.layerInd_apply_of_inLayer
#print axioms PAG.Part222.layerInd_apply_of_not_inLayer
#print axioms PAG.Part222.twistFn_apply
#print axioms PAG.Part222.twistFn_mul_kblock
#print axioms PAG.Part222.twistFn_mul_mem
#print axioms PAG.Part222.twistFn_mul_twistFn
#print axioms PAG.Part222.twistFn_mul_mem_layerPart
#print axioms PAG.Part222.twistConst
#print axioms PAG.Part222.kcoef_twist
#print axioms PAG.Part222.twistConst_ne_zero
#print axioms PAG.Part222.twist_scalar_aux
#print axioms PAG.Part222.twistFn_mul_gblock
#print axioms PAG.Part222.twistFn_mul_geps_conv
#print axioms PAG.Part222.block_twist_iso
#print axioms PAG.Part222.blockHom
#print axioms PAG.Part222.mem_blockHom
#print axioms PAG.Part222.twistV
#print axioms PAG.Part222.twistV_apply
#print axioms PAG.Part222.twistV_comp_mem_blockHom
#print axioms PAG.Part222.twistV_comp_mem_blockComm
#print axioms PAG.Part222.finrank_blockHom
#print axioms PAG.Part222.finrank_blockHom_eq_prod
