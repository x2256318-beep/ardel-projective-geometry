/-
  PAG 2.0 Part 217（2026-10-29）— ブロックに制限した可換子の次元 π(c) と、成分の次元（層の射影）
  ブロック (c, χ)（χ は法 c の原始指標）、L = N/c。V = V_{c,χ}（Part 215 の blockSpan）
  層・W(d)・D（Part 216 の InLayer・RadDvd・layerPart・layerIdx）
  ι_d = 層 d の指示関数（def layerInd）、Q_d f = ι_d·f（層の射影）
  S_d = {v ∣ L : v は d の層}（def layerDivs）
  0. 層の射影：W(d′) の上で ι_d· = [d = d′]、f ∈ V なら ι_d·f ∈ W(d)、Σ_{d ∈ D} ι_d·f = f、
     V の上で ι_d· と E_s は可換（空間全体では一般に可換でない：数値）
  1. 成分の次元：G_v（v ∣ L）は一次独立、W(d) = span{G_v : v ∈ S_d}、dim W(d) = #S_d、
     V = span{G_v}、dim V = d(L)、Σ_{d ∈ D} dim W(d) = dim V、固有空間 {f : U_a f = χ_N(a)f} の次元 d(L)
  2. 可換な写像（空間全体の写像。仮定は部分空間の上だけ）：
     W(d) の上で E_s・D_s と可換で W(d) を V に写す T は、W(d) の上でスカラー μ_d(T) = (N/φ(dc))⟨G_d, T G_d⟩。
     V の上で可換で V を V に写す T は、V の上で Σ_{d ∈ D} μ_d(T)·ι_d·
  3. ブロックに制限した可換子（def blockComm ⊆ End(V)）= span{Q_d|_V}、次元 #D = Π_{p ∣ gcd(c, L)} (v_p(L) + 1)
  4. 成分は A 加群として互いに同型でない（W(d) の上だけで定義された写像の形）：
     W(d) → W(d′)（d ≠ d′）で E_s・D_s と可換な線形写像は 0、W(d) → W(d) のものはスカラー倍
-/
import PAG220

namespace PAG.Part221

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 層の射影 -/

open Classical in
/-- 層 d の指示関数 ι_d：x.val が d の層なら 1、そうでなければ 0。 -/
noncomputable def layerInd (N c d : ℕ) : ZMod N → ℂ := fun x => if InLayer c d x.val then 1 else 0

/-- **0a.** x.val が d の層なら (ι_d·f)(x) = f(x)。 -/
theorem layerInd_mul_of_inLayer (N c d : ℕ) (f : ZMod N → ℂ) {x : ZMod N} (hx : InLayer c d x.val) :
    (layerInd N c d * f) x = f x := by
  simp only [layerInd, Pi.mul_apply]
  rw [ite_eq_left hx, one_mul]

/-- **0b.** x.val が d の層でなければ (ι_d·f)(x) = 0。 -/
theorem layerInd_mul_of_not_inLayer (N c d : ℕ) (f : ZMod N → ℂ) {x : ZMod N} (hx : ¬ InLayer c d x.val) :
    (layerInd N c d * f) x = 0 := by
  simp only [layerInd, Pi.mul_apply]
  rw [ite_eq_right hx, zero_mul]

/-- **0c.** W(d′) の元 g について ι_d·g = [d = d′]·g（rad(d), rad(d′) ∣ c）。 -/
theorem layerInd_mul_of_mem (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) {d d' : ℕ}
    (hd : RadDvd d c) (hd' : RadDvd d' c) {g : ZMod N → ℂ} (hg : g ∈ layerPart N c χ d') :
    layerInd N c d * g = if d = d' then g else 0 := by
  by_cases hdd : d = d'
  · rw [ite_eq_left hdd]
    funext x
    by_cases hx : InLayer c d x.val
    · exact layerInd_mul_of_inLayer N c d g hx
    · rw [layerInd_mul_of_not_inLayer N c d g hx]
      rw [hdd] at hx
      exact (((mem_layerPart N c χ d' g).mp hg).2 x hx).symm
  · rw [ite_eq_right hdd]
    funext x
    rw [Pi.zero_apply]
    by_cases hx : InLayer c d x.val
    · rw [layerInd_mul_of_inLayer N c d g hx]
      exact layerPart_apply_eq_zero N c χ hd' hd (Ne.symm hdd) hg x hx
    · exact layerInd_mul_of_not_inLayer N c d g hx

/-- **0d.** f ∈ V なら ι_d·f ∈ W(d)（rad(d) ∣ c）。 -/
theorem layerInd_mul_mem (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {d : ℕ} (hd : RadDvd d c) {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) :
    layerInd N c d * f ∈ layerPart N c χ d := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  unfold blockSpan at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    have hu : (u : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors u.2
    obtain ⟨du, hdu, hudu⟩ := exists_layer c u (Nat.pos_of_dvd_of_pos hu hL0).ne'
    have hk := kblock_mem_layerPart N c hcN χ hu hudu
    show layerInd N c d * kblock N c χ u ∈ layerPart N c χ d
    rw [layerInd_mul_of_mem N c χ hd hdu hk]
    by_cases hdd : d = du
    · rw [ite_eq_left hdd, hdd]
      exact hk
    · rw [ite_eq_right hdd]
      exact zero_mem _
  | zero =>
    rw [mul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact add_mem hx hy
  | smul r x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hx

/-- **0e.** f ∈ V なら Σ_{d ∈ D} ι_d·f = f。 -/
theorem sum_layerInd_mul (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) :
    ∑ d ∈ layerIdx c (N / c), layerInd N c d * f = f := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  unfold blockSpan at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    have hu : (u : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors u.2
    obtain ⟨du, hdu, hudu⟩ := exists_layer c u (Nat.pos_of_dvd_of_pos hu hL0).ne'
    have hk := kblock_mem_layerPart N c hcN χ hu hudu
    have hduI : du ∈ layerIdx c (N / c) := by
      refine (mem_layerIdx c (N / c) du).mpr ⟨Nat.mem_divisors.mpr ⟨?_, hL0.ne'⟩, hdu⟩
      obtain ⟨e, he, -⟩ := hudu
      exact dvd_trans ⟨e, he⟩ hu
    show ∑ d ∈ layerIdx c (N / c), layerInd N c d * kblock N c χ u = kblock N c χ u
    rw [Finset.sum_eq_single du]
    · rw [layerInd_mul_of_mem N c χ hdu hdu hk, ite_eq_left rfl]
    · intro d hd hne
      rw [layerInd_mul_of_mem N c χ ((mem_layerIdx c (N / c) d).mp hd).2 hdu hk, ite_eq_right hne]
    · intro h
      exact absurd hduI h
  | zero =>
    simp only [mul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hx, hy]
  | smul r x _ hx =>
    simp only [mul_smul_comm]
    rw [← Finset.smul_sum, hx]

/-- **0f.** f ∈ V なら ι_d·(ε_s ⋆ f) = ε_s ⋆ (ι_d·f)（rad(d) ∣ c。V の上で Q_d と E_s は可換）。 -/
theorem layerInd_mul_geps_conv (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hd : RadDvd d c) (s : ℕ) {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) :
    layerInd N c d * PAG.Part15.conv (geps N s) f = PAG.Part15.conv (geps N s) (layerInd N c d * f) := by
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
  unfold blockSpan at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    have hu : (u : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors u.2
    obtain ⟨du, hdu, hudu⟩ := exists_layer c u (Nat.pos_of_dvd_of_pos hu hL0).ne'
    have hk := kblock_mem_layerPart N c hcN χ hu hudu
    have hEk := ((layerPart_shellInvariant N c hcN χ hχ hdu) s _ hk).1
    show layerInd N c d * PAG.Part15.conv (geps N s) (kblock N c χ u) =
      PAG.Part15.conv (geps N s) (layerInd N c d * kblock N c χ u)
    rw [layerInd_mul_of_mem N c χ hd hdu hEk, layerInd_mul_of_mem N c χ hd hdu hk]
    by_cases hdd : d = du
    · rw [ite_eq_left hdd, ite_eq_left hdd]
    · rw [ite_eq_right hdd, ite_eq_right hdd, hzero]
  | zero =>
    rw [hzero, mul_zero, hzero]
  | add x y _ _ hx hy =>
    rw [hadd x y, mul_add (layerInd N c d) (PAG.Part15.conv (geps N s) x) (PAG.Part15.conv (geps N s) y), hx, hy,
      mul_add (layerInd N c d) x y, hadd]
  | smul r x _ hx =>
    rw [hsmul r x, mul_smul_comm r (layerInd N c d) (PAG.Part15.conv (geps N s) x), hx,
      mul_smul_comm r (layerInd N c d) x, hsmul]

/-! ### 1. 成分の次元 -/

open Classical in
/-- S_d = {v ∣ L : v は d の層}（W(d) に入る G_v の番号）。 -/
noncomputable def layerDivs (c d L : ℕ) : Finset ℕ := L.divisors.filter (fun v => InLayer c d v)

/-- **1a.** S_d の元の判定。 -/
theorem mem_layerDivs (c d L v : ℕ) : v ∈ layerDivs c d L ↔ v ∈ L.divisors ∧ InLayer c d v := by
  classical
  unfold layerDivs
  rw [Finset.mem_filter]

/-- **1b.** f ∈ W(d)、v ∣ L が d の層でなければ ⟨G_v, f⟩ = 0（台が交わらない）。 -/
theorem inner_gblock_eq_zero_of_not_inLayer (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {v d : ℕ} (hv : v ∣ N / c) (hd : RadDvd d c)
    (hvd : ¬ InLayer c d v) {f : ZMod N → ℂ} (hf : f ∈ layerPart N c χ d) :
    ∑ x, starRingEnd ℂ (gblock N c χ v x) * f x = 0 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  refine Finset.sum_eq_zero (fun x _ => ?_)
  by_cases hfx : f x = 0
  · rw [hfx, mul_zero]
  · have hxd : InLayer c d x.val := by
      by_contra hn
      exact hfx (((mem_layerPart N c χ d f).mp hf).2 x hn)
    have hg0 : gblock N c χ v x = 0 := by
      by_contra hne
      obtain ⟨dv, hdv, hvdv⟩ := exists_layer c v (Nat.pos_of_dvd_of_pos hv hL0).ne'
      have hx' := gblock_layer N c hcN χ hχ hv hdv hvdv x hne
      have heq := layer_unique hd hdv hxd hx'
      rw [← heq] at hvdv
      exact hvd hvdv
    rw [hg0, map_zero, zero_mul]

/-- **1c.** G_v（v ∣ L）は一次独立。 -/
theorem gblock_linearIndependent (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) :
    LinearIndependent ℂ (fun v : (N / c).divisors => gblock N c χ v) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hiL : (i : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors i.2
  have hφ : (Nat.totient ((i : ℕ) * c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (Nat.pos_of_dvd_of_pos hiL hL0) hc0)).ne'
  have h1 : ∑ x, starRingEnd ℂ (gblock N c χ i x) * (∑ j ∈ s, g j • gblock N c χ j) x = 0 := by
    rw [hsum]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have h2 : ∑ x, starRingEnd ℂ (gblock N c χ i x) * (∑ j ∈ s, g j • gblock N c χ j) x =
      ∑ j ∈ s, g j * (if (i : ℕ) = j then (Nat.totient ((i : ℕ) * c) : ℂ) / N else 0) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← inner_gblock N c hcN χ hiL (Nat.dvd_of_mem_divisors j.2), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [h2, Finset.sum_eq_single i] at h1
  · rw [ite_eq_left rfl] at h1
    exact (mul_eq_zero.mp h1).resolve_right (div_ne_zero hφ hN)
  · intro j _ hji
    rw [ite_eq_right (fun h => hji (Subtype.ext h).symm), mul_zero]
  · intro his
    exact absurd hi his

/-- **1d.** W(d) = span{G_v : v ∈ S_d}（rad(d) ∣ c）。 -/
theorem layerPart_eq_span (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hd : RadDvd d c) :
    layerPart N c χ d = Submodule.span ℂ (Set.range fun v : layerDivs c d (N / c) => gblock N c χ v) := by
  classical
  apply le_antisymm
  · intro f hf
    have hPf := blockProj_of_mem N c hcN χ hχ ((mem_layerPart N c χ d f).mp hf).1
    rw [← hPf, blockProj_eq_blockProjG N c hcN χ hχ]
    unfold blockProjG
    rw [← Finset.sum_filter_add_sum_filter_not (N / c).divisors (fun v => InLayer c d v)]
    refine add_mem (Submodule.sum_mem _ (fun v hv => ?_)) (Submodule.sum_mem _ (fun v hv => ?_))
    · obtain ⟨hvD, hvd⟩ := Finset.mem_filter.mp hv
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨v, (mem_layerDivs c d (N / c) v).mpr ⟨hvD, hvd⟩⟩, rfl⟩)
    · obtain ⟨hvD, hvd⟩ := Finset.mem_filter.mp hv
      rw [inner_gblock_eq_zero_of_not_inLayer N c hcN χ hχ (Nat.dvd_of_mem_divisors hvD) hd hvd hf, mul_zero,
        zero_smul]
      exact zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    obtain ⟨hvD, hvd⟩ := (mem_layerDivs c d (N / c) v).mp v.2
    exact gblock_mem_layerPart N c hcN χ hχ (Nat.dvd_of_mem_divisors hvD) hd hvd

/-- **1e. 成分の次元**：dim W(d) = #S_d（rad(d) ∣ c）。 -/
theorem finrank_layerPart (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hd : RadDvd d c) :
    Module.finrank ℂ (layerPart N c χ d) = (layerDivs c d (N / c)).card := by
  have hinc : Function.Injective (fun v : layerDivs c d (N / c) =>
      (⟨v, ((mem_layerDivs c d (N / c) v).mp v.2).1⟩ : (N / c).divisors)) := by
    intro a b h
    have h' : (a : ℕ) = b := congrArg (fun z : (N / c).divisors => (z : ℕ)) h
    exact Subtype.ext h'
  have hli : LinearIndependent ℂ (fun v : layerDivs c d (N / c) => gblock N c χ v) :=
    (gblock_linearIndependent N c hcN χ).comp (fun v : layerDivs c d (N / c) =>
      (⟨v, ((mem_layerDivs c d (N / c) v).mp v.2).1⟩ : (N / c).divisors)) hinc
  rw [layerPart_eq_span N c hcN χ hχ hd, finrank_span_eq_card hli, Fintype.card_coe]

/-- **1f.** V = span{G_v : v ∣ L}。 -/
theorem blockSpan_eq_span_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    blockSpan N c χ = Submodule.span ℂ (Set.range fun v : (N / c).divisors => gblock N c χ v) := by
  apply le_antisymm
  · intro f hf
    rw [← blockProj_of_mem N c hcN χ hχ hf, blockProj_eq_blockProjG N c hcN χ hχ]
    unfold blockProjG
    exact Submodule.sum_mem _ (fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact gblock_mem N c hcN χ hχ (Nat.dvd_of_mem_divisors v.2)

/-- **1g.** dim V = d(L)（L = N/c）。 -/
theorem finrank_blockSpan (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : Module.finrank ℂ (blockSpan N c χ) = (N / c).divisors.card := by
  rw [blockSpan_eq_span_gblock N c hcN χ hχ, finrank_span_eq_card (gblock_linearIndependent N c hcN χ),
    Fintype.card_coe]

/-- **1h.** Σ_{d ∈ D} dim W(d) = dim V。 -/
theorem sum_finrank_layerPart (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    ∑ d ∈ layerIdx c (N / c), Module.finrank ℂ (layerPart N c χ d) = Module.finrank ℂ (blockSpan N c χ) := by
  classical
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  rw [Finset.sum_congr rfl (fun d hd => finrank_layerPart N c hcN χ hχ ((mem_layerIdx c (N / c) d).mp hd).2),
    finrank_blockSpan N c hcN χ hχ]
  have hdisj : ((layerIdx c (N / c) : Set ℕ)).PairwiseDisjoint (fun d => layerDivs c d (N / c)) := by
    intro d₁ hd₁ d₂ hd₂ hne
    show Disjoint (layerDivs c d₁ (N / c)) (layerDivs c d₂ (N / c))
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    exact hne (layer_unique ((mem_layerIdx c (N / c) d₁).mp (Finset.mem_coe.mp hd₁)).2
      ((mem_layerIdx c (N / c) d₂).mp (Finset.mem_coe.mp hd₂)).2
      ((mem_layerDivs c d₁ (N / c) v).mp hv1).2 ((mem_layerDivs c d₂ (N / c) v).mp hv2).2)
  calc ∑ d ∈ layerIdx c (N / c), (layerDivs c d (N / c)).card
      = ((layerIdx c (N / c)).biUnion (fun d => layerDivs c d (N / c))).card := (Finset.card_biUnion hdisj).symm
    _ = (N / c).divisors.card := by
      congr 1
      ext v
      rw [Finset.mem_biUnion]
      constructor
      · rintro ⟨d, -, hv⟩
        exact ((mem_layerDivs c d (N / c) v).mp hv).1
      · intro hv
        obtain ⟨d, hd, hvd⟩ := exists_layer c v (Nat.pos_of_mem_divisors hv).ne'
        refine ⟨d, (mem_layerIdx c (N / c) d).mpr ⟨Nat.mem_divisors.mpr ⟨?_, hL0.ne'⟩, hd⟩,
          (mem_layerDivs c d (N / c) v).mpr ⟨hv, hvd⟩⟩
        obtain ⟨e, he, -⟩ := hvd
        exact dvd_trans ⟨e, he⟩ (Nat.dvd_of_mem_divisors hv)

/-- **1i.** 固有空間 {f : U_a f = χ_N(a)·f（すべての単数 a）} の次元は d(N/c)
（Part 214 の `mem_span_iff_dil` で V と一致する部分空間）。 -/
theorem finrank_eigenspace_dil (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (W : Submodule ℂ (ZMod N → ℂ))
    (hW : ∀ f, f ∈ W ↔ ∀ a : (ZMod N)ˣ, dil a f = liftc χ N (a : ZMod N) • f) :
    Module.finrank ℂ W = (N / c).divisors.card := by
  have hWV : W = blockSpan N c χ := by
    ext f
    rw [hW f]
    exact (mem_span_iff_dil N c hcN χ hχ f).symm
  rw [hWV, finrank_blockSpan N c hcN χ hχ]

/-! ### 2. 可換な写像（仮定は部分空間の上だけ） -/

/-- **2a.** W が殻の射影で閉じていて、T が W の上で E_s・D_s と可換なら、T は W の上で A のすべての元と可換。 -/
theorem commute_shellAlg_on (N : ℕ) [NeZero N] {W : Submodule ℂ (ZMod N → ℂ)} (hW : ShellInvariant W)
    (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ W, T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ W, T (dind N s * f) = dind N s * T f)
    {S : Module.End ℂ (ZMod N → ℂ)} (hS : S ∈ shellAlg N) : ∀ f ∈ W, T (S f) = S (T f) := by
  have hinv := (shellInvariant_iff N W).mp hW
  unfold shellAlg at hS
  induction hS using Algebra.adjoin_induction with
  | mem x hx =>
    intro f hf
    rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact hTE s f hf
    · exact hTD s f hf
  | algebraMap r =>
    intro f _
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add x y _ _ hx hy =>
    intro f hf
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, hx f hf, hy f hf]
  | mul x y _ hyA hx hy =>
    intro f hf
    rw [Module.End.mul_apply, Module.End.mul_apply, hx _ (hinv y hyA f hf), hy f hf]

/-- **2b.** T が W(d) の上で E_s・D_s と可換で W(d) を V に写すなら、T は W(d) の上でスカラー
μ_d(T) = (N/φ(dc))·⟨G_d, T G_d⟩（d ∣ N/c、rad(d) ∣ c）。 -/
theorem layerPart_smul_of_commute (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d,
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d, T (dind N s * f) = dind N s * T f)
    (hTV : ∀ f ∈ layerPart N c χ d, T f ∈ blockSpan N c χ) :
    ∀ f ∈ layerPart N c χ d, T f = ((N : ℂ) / (Nat.totient (d * c) : ℂ) *
      ∑ x, starRingEnd ℂ (gblock N c χ d x) * T (gblock N c χ d) x) • f := by
  have hGd : gblock N c χ d ∈ layerPart N c χ d :=
    gblock_mem_layerPart N c hcN χ hχ hdL hd ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩
  set μ : ℂ := (N : ℂ) / (Nat.totient (d * c) : ℂ) *
    ∑ x, starRingEnd ℂ (gblock N c χ d x) * T (gblock N c χ d) x
  have hTG : T (gblock N c χ d) = μ • gblock N c χ d := by
    have hE : PAG.Part15.conv (geps N (N / (d * c))) (gblock N c χ d) = gblock N c χ d := by
      rw [geps_conv_gblock N c hcN χ hdL (N / (d * c)), ite_eq_left rfl]
    have hP := blockProj_of_mem N c hcN χ hχ (hTV _ hGd)
    calc T (gblock N c χ d) = T (PAG.Part15.conv (geps N (N / (d * c))) (gblock N c χ d)) := by rw [hE]
      _ = PAG.Part15.conv (geps N (N / (d * c))) (T (gblock N c χ d)) := hTE _ _ hGd
      _ = PAG.Part15.conv (geps N (N / (d * c))) (blockProj N c χ (T (gblock N c χ d))) := by rw [hP]
      _ = μ • gblock N c χ d := geps_conv_blockProj_gblock N c hcN χ hχ hdL _
  intro f hf
  obtain ⟨S, hS, rfl⟩ := layerPart_exists_apply N c hcN χ hχ hdL hd hf
  rw [commute_shellAlg_on N (layerPart_shellInvariant N c hcN χ hχ hd) T hTE hTD hS _ hGd, hTG, map_smul]

/-- **2c. 成分は互いに同型でない（仮定は W(d) の上だけ）**：d ≠ d′ で、T が W(d) の上で E_s・D_s と可換で
W(d) を W(d′) に写すなら、T は W(d) の上で 0。 -/
theorem layerPart_hom_eq_zero_of_commute (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {d d' : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c)
    (hd' : RadDvd d' c) (hne : d ≠ d') (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d,
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ layerPart N c χ d, T (dind N s * f) = dind N s * T f)
    (hT : ∀ f ∈ layerPart N c χ d, T f ∈ layerPart N c χ d') :
    ∀ f ∈ layerPart N c χ d, T f = 0 := by
  have hGd : gblock N c χ d ∈ layerPart N c χ d :=
    gblock_mem_layerPart N c hcN χ hχ hdL hd ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩
  have hTGd := hT _ hGd
  have h0 : ∑ x, starRingEnd ℂ (gblock N c χ d x) * T (gblock N c χ d) x = 0 := by
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hgx : gblock N c χ d x = 0
    · rw [hgx, map_zero, zero_mul]
    · have hxd : InLayer c d x.val := by
        by_contra hn
        exact hgx (((mem_layerPart N c χ d _).mp hGd).2 x hn)
      rw [layerPart_apply_eq_zero N c χ hd' hd (Ne.symm hne) hTGd x hxd, mul_zero]
  intro f hf
  rw [layerPart_smul_of_commute N c hcN χ hχ hdL hd T hTE hTD
    (fun g hg => ((mem_layerPart N c χ d' _).mp (hT g hg)).1) f hf, h0, mul_zero, zero_smul]

/-- **2d.** T が V の上で E_s・D_s と可換で V を V に写すなら、f ∈ V について
T f = Σ_{d ∈ D} μ_d(T)·(ι_d·f)、μ_d(T) = (N/φ(dc))·⟨G_d, T G_d⟩。 -/
theorem commute_eq_sum_layerInd (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ blockSpan N c χ,
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ blockSpan N c χ, T (dind N s * f) = dind N s * T f)
    (hTV : ∀ f ∈ blockSpan N c χ, T f ∈ blockSpan N c χ) :
    ∀ f ∈ blockSpan N c χ, T f = ∑ d ∈ layerIdx c (N / c), ((N : ℂ) / (Nat.totient (d * c) : ℂ) *
      ∑ x, starRingEnd ℂ (gblock N c χ d x) * T (gblock N c χ d) x) • (layerInd N c d * f) := by
  intro f hf
  calc T f = T (∑ d ∈ layerIdx c (N / c), layerInd N c d * f) := by rw [sum_layerInd_mul N c hcN χ hf]
    _ = ∑ d ∈ layerIdx c (N / c), T (layerInd N c d * f) := map_sum T _ _
    _ = _ := by
      refine Finset.sum_congr rfl (fun d hdI => ?_)
      obtain ⟨hdD, hd⟩ := (mem_layerIdx c (N / c) d).mp hdI
      have hdL := Nat.dvd_of_mem_divisors hdD
      have hW : ∀ g ∈ layerPart N c χ d, g ∈ blockSpan N c χ := fun g hg =>
        ((mem_layerPart N c χ d g).mp hg).1
      exact layerPart_smul_of_commute N c hcN χ hχ hdL hd T (fun s g hg => hTE s g (hW g hg))
        (fun s g hg => hTD s g (hW g hg)) (fun g hg => hTV g (hW g hg)) _ (layerInd_mul_mem N c hcN χ hd hf)

/-! ### 3. ブロックに制限した可換子 -/

/-- **3a.** V は殻の射影で閉じる。 -/
theorem blockSpan_shellInvariant (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : ShellInvariant (blockSpan N c χ) := by
  intro s f hf
  have hPf := blockProj_of_mem N c hcN χ hχ hf
  constructor
  · rw [← hPf, geps_conv_blockProj N c hcN χ hχ s f]
    exact blockProj_mem_span N c χ _
  · rw [← hPf, dind_mul_blockProj N c hcN χ hχ s f]
    exact blockProj_mem_span N c χ _

/-- ブロックに制限した可換子：V_{c,χ} の線形変換 T で、V の上で E_s・D_s と可換なもの
（E_s f・D_s f が V に入るときの式で書く。V は殻の射影で閉じている：`blockSpan_shellInvariant`）。 -/
noncomputable def blockComm (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) :
    Submodule ℂ (Module.End ℂ (blockSpan N c χ)) where
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

/-- **3b.** 可換子の元の判定。 -/
theorem mem_blockComm (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (T : Module.End ℂ (blockSpan N c χ)) :
    T ∈ blockComm N c χ ↔ ∀ (s : ℕ) (f : ZMod N → ℂ) (hf : f ∈ blockSpan N c χ),
      (∀ h : PAG.Part15.conv (geps N s) f ∈ blockSpan N c χ,
        (T ⟨_, h⟩ : ZMod N → ℂ) = PAG.Part15.conv (geps N s) (T ⟨f, hf⟩ : ZMod N → ℂ)) ∧
      (∀ h : dind N s * f ∈ blockSpan N c χ,
        (T ⟨_, h⟩ : ZMod N → ℂ) = dind N s * (T ⟨f, hf⟩ : ZMod N → ℂ)) := Iff.rfl

/-- **3c.** P f ∈ V（線形写像 P の形）。 -/
theorem blockProjL_mem (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) (f : ZMod N → ℂ) :
    blockProjL N c χ f ∈ blockSpan N c χ :=
  blockProj_mem_span N c χ f

/-- V の線形変換 T を空間全体に延ばしたもの：f ↦ T(P f)（P はブロックへの射影）。 -/
noncomputable def blockExt (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c)
    (T : Module.End ℂ (blockSpan N c χ)) : Module.End ℂ (ZMod N → ℂ) :=
  (blockSpan N c χ).subtype ∘ₗ T ∘ₗ LinearMap.codRestrict (blockSpan N c χ) (blockProjL N c χ) (blockProjL_mem N c χ)

/-- **3d.** f ∈ V なら（T の延長）(f) = T f。 -/
theorem blockExt_apply (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (T : Module.End ℂ (blockSpan N c χ)) {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) :
    blockExt N c χ T f = (T ⟨f, hf⟩ : ZMod N → ℂ) := by
  have hc : LinearMap.codRestrict (blockSpan N c χ) (blockProjL N c χ) (blockProjL_mem N c χ) f = ⟨f, hf⟩ :=
    Subtype.ext (by rw [LinearMap.codRestrict_apply, blockProjL_apply, blockProj_of_mem N c hcN χ hχ hf])
  simp only [blockExt, LinearMap.comp_apply, Submodule.subtype_apply, hc]

/-- 層の射影 Q_d（d ∈ D）を V に制限したもの。 -/
noncomputable def layerProjV (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (d : layerIdx c (N / c)) : Module.End ℂ (blockSpan N c χ) :=
  (LinearMap.mulLeft ℂ (layerInd N c d)).restrict (fun _ hf =>
    ((mem_layerPart N c χ d _).mp (layerInd_mul_mem N c hcN χ ((mem_layerIdx c (N / c) d).mp d.2).2 hf)).1)

/-- **3e.** (Q_d|_V)(f) = ι_d·f。 -/
theorem layerProjV_apply (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (d : layerIdx c (N / c)) (f : blockSpan N c χ) :
    (layerProjV N c hcN χ d f : ZMod N → ℂ) = layerInd N c d * f := rfl

/-- **3f.** Q_d|_V は可換子に入る。 -/
theorem layerProjV_mem_blockComm (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (d : layerIdx c (N / c)) : layerProjV N c hcN χ d ∈ blockComm N c χ := by
  rw [mem_blockComm]
  intro s f hf
  have hd := ((mem_layerIdx c (N / c) d).mp d.2).2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [layerProjV_apply, layerProjV_apply]
    exact layerInd_mul_geps_conv N c hcN χ hχ hd s hf
  · rw [layerProjV_apply, layerProjV_apply]
    exact mul_left_comm _ _ _

/-- **3g.** Q_d|_V（d ∈ D）は一次独立。 -/
theorem layerProjV_linearIndependent (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : LinearIndependent ℂ (layerProjV N c hcN χ) := by
  rw [linearIndependent_iff'ₛ]
  intro s f g hfg i hi
  obtain ⟨hiD, hi'⟩ := (mem_layerIdx c (N / c) i).mp i.2
  have hiL : (i : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors hiD
  have hGi : gblock N c χ i ∈ layerPart N c χ i :=
    gblock_mem_layerPart N c hcN χ hχ hiL hi' ⟨1, (mul_one _).symm, Nat.coprime_one_left c⟩
  have hGV : gblock N c χ i ∈ blockSpan N c χ := ((mem_layerPart N c χ i _).mp hGi).1
  -- Σ_j h_j·Q_j を G_i に当てると h_i·G_i
  have key : ∀ h : layerIdx c (N / c) → ℂ,
      (((∑ j ∈ s, h j • layerProjV N c hcN χ j) ⟨_, hGV⟩ : blockSpan N c χ) : ZMod N → ℂ) =
        h i • gblock N c χ i := by
    intro h
    simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul,
      layerProjV_apply]
    rw [Finset.sum_eq_single i]
    · rw [layerInd_mul_of_mem N c χ hi' hi' hGi, ite_eq_left rfl]
    · intro j _ hji
      rw [layerInd_mul_of_mem N c χ ((mem_layerIdx c (N / c) j).mp j.2).2 hi' hGi,
        ite_eq_right (fun h => hji (Subtype.ext h)), smul_zero]
    · intro his
      exact absurd hi his
  have h1 : (((∑ j ∈ s, f j • layerProjV N c hcN χ j) ⟨_, hGV⟩ : blockSpan N c χ) : ZMod N → ℂ) =
      (((∑ j ∈ s, g j • layerProjV N c hcN χ j) ⟨_, hGV⟩ : blockSpan N c χ) : ZMod N → ℂ) := by
    rw [hfg]
  rw [key f, key g] at h1
  have h2 : (f i - g i) • gblock N c χ i = 0 := by rw [sub_smul, h1, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (gblock_ne_zero N c hcN χ hiL))

/-- **3h. 可換子の元の形**：T ∈ blockComm なら、f ∈ V について T f = Σ_{d ∈ D} μ_d·(ι_d·f)、
μ_d = (N/φ(dc))·⟨G_d, T̃ G_d⟩（T̃ は T の延長 `blockExt`。G_d ∈ V なので T̃ G_d = T G_d）。 -/
theorem blockComm_apply (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {T : Module.End ℂ (blockSpan N c χ)} (hT : T ∈ blockComm N c χ)
    (f : blockSpan N c χ) :
    (T f : ZMod N → ℂ) = ∑ d ∈ layerIdx c (N / c), ((N : ℂ) / (Nat.totient (d * c) : ℂ) *
      ∑ x, starRingEnd ℂ (gblock N c χ d x) * blockExt N c χ T (gblock N c χ d) x) • (layerInd N c d * f) := by
  have hinv := blockSpan_shellInvariant N c hcN χ hχ
  have hTE : ∀ (s : ℕ), ∀ g ∈ blockSpan N c χ,
      blockExt N c χ T (PAG.Part15.conv (geps N s) g) = PAG.Part15.conv (geps N s) (blockExt N c χ T g) := by
    intro s g hg
    rw [blockExt_apply N c hcN χ hχ T (hinv s g hg).1, blockExt_apply N c hcN χ hχ T hg]
    exact ((mem_blockComm N c χ T).mp hT s g hg).1 (hinv s g hg).1
  have hTD : ∀ (s : ℕ), ∀ g ∈ blockSpan N c χ,
      blockExt N c χ T (dind N s * g) = dind N s * blockExt N c χ T g := by
    intro s g hg
    rw [blockExt_apply N c hcN χ hχ T (hinv s g hg).2, blockExt_apply N c hcN χ hχ T hg]
    exact ((mem_blockComm N c χ T).mp hT s g hg).2 (hinv s g hg).2
  have hTV : ∀ g ∈ blockSpan N c χ, blockExt N c χ T g ∈ blockSpan N c χ := by
    intro g hg
    rw [blockExt_apply N c hcN χ hχ T hg]
    exact (T ⟨g, hg⟩).2
  have h := commute_eq_sum_layerInd N c hcN χ hχ (blockExt N c χ T) hTE hTD hTV f f.2
  rw [blockExt_apply N c hcN χ hχ T f.2] at h
  exact h

/-- **3i.** 可換子 = span{Q_d|_V : d ∈ D}。 -/
theorem blockComm_eq_span (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : blockComm N c χ = Submodule.span ℂ (Set.range (layerProjV N c hcN χ)) := by
  apply le_antisymm
  · intro T hT
    have hTeq : T = ∑ d : layerIdx c (N / c), ((N : ℂ) / (Nat.totient ((d : ℕ) * c) : ℂ) *
        ∑ x, starRingEnd ℂ (gblock N c χ d x) * blockExt N c χ T (gblock N c χ d) x) •
          layerProjV N c hcN χ d := by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      rw [blockComm_apply N c hcN χ hχ hT f]
      simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul,
        layerProjV_apply]
      exact (Finset.sum_coe_sort (layerIdx c (N / c)) (fun d => ((N : ℂ) / (Nat.totient (d * c) : ℂ) *
        ∑ x, starRingEnd ℂ (gblock N c χ d x) * blockExt N c χ T (gblock N c χ d) x) •
          (layerInd N c d * (f : ZMod N → ℂ)))).symm
    rw [hTeq]
    exact Submodule.sum_mem _ (fun d _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨d, rfl⟩
    exact layerProjV_mem_blockComm N c hcN χ hχ d

/-- **3j. ブロックに制限した可換子の次元**：dim blockComm = #D。 -/
theorem finrank_blockComm (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : Module.finrank ℂ (blockComm N c χ) = (layerIdx c (N / c)).card := by
  rw [blockComm_eq_span N c hcN χ hχ, finrank_span_eq_card (layerProjV_linearIndependent N c hcN χ hχ),
    Fintype.card_coe]

/-- **3k.** dim blockComm = Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)（Part 214 の π(c)）。 -/
theorem finrank_blockComm_eq_prod (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    Module.finrank ℂ (blockComm N c χ) =
      ∏ p ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization p + 1) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  rw [finrank_blockComm N c hcN χ hχ, card_layerIdx c (N / c) hL0.ne']

/-! ### 4. 成分は A 加群として互いに同型でない（W(d) の上だけで定義された写像） -/

/-- **4a.** d ≠ d′ で、線形写像 ψ : W(d) → W(d′) が W(d) の上で E_s・D_s と可換なら ψ = 0。 -/
theorem layerPart_linearMap_eq_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d d' : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) (hd' : RadDvd d' c) (hne : d ≠ d')
    (ψ : layerPart N c χ d →ₗ[ℂ] layerPart N c χ d')
    (hψE : ∀ (s : ℕ) (f : ZMod N → ℂ) (hf : f ∈ layerPart N c χ d)
      (h : PAG.Part15.conv (geps N s) f ∈ layerPart N c χ d),
      (ψ ⟨_, h⟩ : ZMod N → ℂ) = PAG.Part15.conv (geps N s) (ψ ⟨f, hf⟩ : ZMod N → ℂ))
    (hψD : ∀ (s : ℕ) (f : ZMod N → ℂ) (hf : f ∈ layerPart N c χ d) (h : dind N s * f ∈ layerPart N c χ d),
      (ψ ⟨_, h⟩ : ZMod N → ℂ) = dind N s * (ψ ⟨f, hf⟩ : ZMod N → ℂ)) : ψ = 0 := by
  obtain ⟨T, hT⟩ := LinearMap.exists_extend ((layerPart N c χ d').subtype ∘ₗ ψ)
  have hTf : ∀ (f : ZMod N → ℂ) (hf : f ∈ layerPart N c χ d), T f = (ψ ⟨f, hf⟩ : ZMod N → ℂ) := by
    intro f hf
    have h1 := LinearMap.congr_fun hT ⟨f, hf⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    exact h1
  have hinv := layerPart_shellInvariant N c hcN χ hχ hd
  have hz := layerPart_hom_eq_zero_of_commute N c hcN χ hχ hdL hd hd' hne T
    (fun s f hf => by rw [hTf _ (hinv s f hf).1, hTf f hf]; exact hψE s f hf (hinv s f hf).1)
    (fun s f hf => by rw [hTf _ (hinv s f hf).2, hTf f hf]; exact hψD s f hf (hinv s f hf).2)
    (fun f hf => by rw [hTf f hf]; exact (ψ ⟨f, hf⟩).2)
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  have h1 := hz f f.2
  rw [hTf f f.2] at h1
  rw [LinearMap.zero_apply, Submodule.coe_zero]
  exact h1

/-- **4b. 成分の中のシューア型**：線形写像 ψ : W(d) → W(d) が W(d) の上で E_s・D_s と可換なら、ψ はスカラー倍。 -/
theorem layerPart_linearMap_eq_smul (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c)
    (ψ : layerPart N c χ d →ₗ[ℂ] layerPart N c χ d)
    (hψE : ∀ (s : ℕ) (f : ZMod N → ℂ) (hf : f ∈ layerPart N c χ d)
      (h : PAG.Part15.conv (geps N s) f ∈ layerPart N c χ d),
      (ψ ⟨_, h⟩ : ZMod N → ℂ) = PAG.Part15.conv (geps N s) (ψ ⟨f, hf⟩ : ZMod N → ℂ))
    (hψD : ∀ (s : ℕ) (f : ZMod N → ℂ) (hf : f ∈ layerPart N c χ d) (h : dind N s * f ∈ layerPart N c χ d),
      (ψ ⟨_, h⟩ : ZMod N → ℂ) = dind N s * (ψ ⟨f, hf⟩ : ZMod N → ℂ)) :
    ∃ μ : ℂ, ψ = μ • LinearMap.id := by
  obtain ⟨T, hT⟩ := LinearMap.exists_extend ((layerPart N c χ d).subtype ∘ₗ ψ)
  have hTf : ∀ (f : ZMod N → ℂ) (hf : f ∈ layerPart N c χ d), T f = (ψ ⟨f, hf⟩ : ZMod N → ℂ) := by
    intro f hf
    have h1 := LinearMap.congr_fun hT ⟨f, hf⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    exact h1
  have hinv := layerPart_shellInvariant N c hcN χ hχ hd
  have hs := layerPart_smul_of_commute N c hcN χ hχ hdL hd T
    (fun s f hf => by rw [hTf _ (hinv s f hf).1, hTf f hf]; exact hψE s f hf (hinv s f hf).1)
    (fun s f hf => by rw [hTf _ (hinv s f hf).2, hTf f hf]; exact hψD s f hf (hinv s f hf).2)
    (fun f hf => by rw [hTf f hf]; exact ((mem_layerPart N c χ d _).mp (ψ ⟨f, hf⟩).2).1)
  refine ⟨(N : ℂ) / (Nat.totient (d * c) : ℂ) *
    ∑ x, starRingEnd ℂ (gblock N c χ d x) * T (gblock N c χ d) x, ?_⟩
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  have h1 := hs f f.2
  rw [hTf f f.2] at h1
  rw [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul]
  exact h1

end PAG.Part221

#print axioms PAG.Part221.layerInd
#print axioms PAG.Part221.layerInd_mul_of_inLayer
#print axioms PAG.Part221.layerInd_mul_of_not_inLayer
#print axioms PAG.Part221.layerInd_mul_of_mem
#print axioms PAG.Part221.layerInd_mul_mem
#print axioms PAG.Part221.sum_layerInd_mul
#print axioms PAG.Part221.layerInd_mul_geps_conv
#print axioms PAG.Part221.layerDivs
#print axioms PAG.Part221.mem_layerDivs
#print axioms PAG.Part221.inner_gblock_eq_zero_of_not_inLayer
#print axioms PAG.Part221.gblock_linearIndependent
#print axioms PAG.Part221.layerPart_eq_span
#print axioms PAG.Part221.finrank_layerPart
#print axioms PAG.Part221.blockSpan_eq_span_gblock
#print axioms PAG.Part221.finrank_blockSpan
#print axioms PAG.Part221.sum_finrank_layerPart
#print axioms PAG.Part221.finrank_eigenspace_dil
#print axioms PAG.Part221.commute_shellAlg_on
#print axioms PAG.Part221.layerPart_smul_of_commute
#print axioms PAG.Part221.layerPart_hom_eq_zero_of_commute
#print axioms PAG.Part221.commute_eq_sum_layerInd
#print axioms PAG.Part221.blockSpan_shellInvariant
#print axioms PAG.Part221.blockComm
#print axioms PAG.Part221.mem_blockComm
#print axioms PAG.Part221.blockProjL_mem
#print axioms PAG.Part221.blockExt
#print axioms PAG.Part221.blockExt_apply
#print axioms PAG.Part221.layerProjV
#print axioms PAG.Part221.layerProjV_apply
#print axioms PAG.Part221.layerProjV_mem_blockComm
#print axioms PAG.Part221.layerProjV_linearIndependent
#print axioms PAG.Part221.blockComm_apply
#print axioms PAG.Part221.blockComm_eq_span
#print axioms PAG.Part221.finrank_blockComm
#print axioms PAG.Part221.finrank_blockComm_eq_prod
#print axioms PAG.Part221.layerPart_linearMap_eq_zero
#print axioms PAG.Part221.layerPart_linearMap_eq_smul
