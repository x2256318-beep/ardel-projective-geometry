/-
  PAG 2.0 Part 223（2026-10-29）— 可換子 A′ ≅ ⊕_{(c,d) ∈ S} M_{m(c)}(ℂ)（代数の同型）
  A′（Part 220 の fullComm、部分代数は Part 222 の fullCommAlg）、ブロック b = (c, χ)、V_b、P_b、層 d ∈ D(c)、ι_d、
  ねじりの関数 Θ_{χ→χ′}（Part 218 の twistFn）、法 c の原始指標の型 Prim c（m(c) = 元の数）、
  S = {(c, d) : c ∣ N、m(c) > 0、d ∈ D(c)}（Part 222 の centerIdx）
  0. ねじりの関数の合成：Θ_{χ′→χ″}·Θ_{χ→χ′} = Θ_{χ→χ″}（関数として。定数 κ による正規化は要らない）、
     Θ_{χ→χ}·ι_d = ι_d、ι_d·ι_{d′} = [d = d′]·ι_d
  1. 行列単位 E^d_{χ→χ′} = Θ_{χ→χ′}·ι_d·P_χ（def matUnit）：A′ に入り、値は W_{c,χ′}(d) に入る。
     積の規則 E^d_{χ′→χ″}·E^d_{χ→χ′} = E^d_{χ→χ″}。文字・層・導手のどれかが合わなければ積は 0。E ≠ 0
  2. Σ_χ E^d_{χ→χ} = z_{c,d}（Part 222 の中心の元）、Σ_{(c,d) ∈ S} Σ_χ E^d_{χ→χ} = 1
  3. Φ(M) = Σ_{p ∈ S} Σ_{i,j} M_p(i, j)·E^{d_p}_{j→i}（def matSum）は A′ に入り、和・スカラー倍・積・単位元を保つ。
     E_p(i→i)·Φ(M)·E_p(j→j) = M_p(i, j)·E_p(j→i) から単射。dim Π_{p ∈ S} M_{m(c)}(ℂ) = Σ_c m(c)²π(c) = dim A′
     （Part 220）なので全単射。代数の同型 Π_{p ∈ S} M_{m(c)}(ℂ) ≅ A′（def fullCommMatrixEquiv）、Φ(Pi.single p 1) = z_p
-/
import PAG226

namespace PAG.Part227

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. ねじりの関数の合成と層の指示関数 -/

/-- **0a.** Θ_{χ′→χ″}·Θ_{χ→χ′} = Θ_{χ→χ″}（関数として。κ による正規化は要らない）。 -/
theorem twistFn_mul_twistFn_eq (N c : ℕ) (χ χ' χ'' : DirichletCharacter ℂ c) :
    twistFn N c χ' χ'' * twistFn N c χ χ' = twistFn N c χ χ'' := by
  funext x
  rw [Pi.mul_apply]
  by_cases h : ∃ d ∈ layerIdx c (N / c), InLayer c d x.val
  · obtain ⟨d, hdI, hx⟩ := h
    have hg : (χ'' * χ'⁻¹) * (χ' * χ⁻¹) = χ'' * χ⁻¹ := by
      rw [mul_assoc, ← mul_assoc χ'⁻¹, inv_mul_cancel, one_mul]
    rw [twistFn_apply N c χ' χ'' hdI hx, twistFn_apply N c χ χ' hdI hx, twistFn_apply N c χ χ'' hdI hx,
      ← MulChar.mul_apply, hg]
  · have h0 : ∀ ψ ψ' : DirichletCharacter ℂ c, twistFn N c ψ ψ' x = 0 := by
      intro ψ ψ'
      unfold twistFn
      exact Finset.sum_eq_zero (fun d hd => by
        rw [layerInd_apply_of_not_inLayer N c d (fun hx => h ⟨d, hd, hx⟩), zero_mul])
    rw [h0, h0, h0, mul_zero]

/-- **0b.** Θ_{χ→χ}·ι_d = ι_d（d ∈ D(c)）。 -/
theorem twistFn_self_mul_layerInd (N c : ℕ) (χ : DirichletCharacter ℂ c) {d : ℕ}
    (hdI : d ∈ layerIdx c (N / c)) : twistFn N c χ χ * layerInd N c d = layerInd N c d := by
  have hd0 : 0 < d := Nat.pos_of_mem_divisors ((mem_layerIdx c (N / c) d).mp hdI).1
  funext x
  rw [Pi.mul_apply]
  by_cases hx : InLayer c d x.val
  · rw [twistFn_apply N c χ χ hdI hx, mul_inv_cancel, layerInd_apply_of_inLayer N c d hx, mul_one]
    obtain ⟨e, he, hec⟩ := hx
    rw [he, Nat.mul_div_cancel_left e hd0]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime e c).mpr hec)
  · rw [layerInd_apply_of_not_inLayer N c d hx, mul_zero]

/-- **0c.** ι_d·ι_{d′} = [d = d′]·ι_d（rad(d), rad(d′) ∣ c）。 -/
theorem layerInd_mul_layerInd (N c : ℕ) {d d' : ℕ} (hd : RadDvd d c) (hd' : RadDvd d' c) :
    layerInd N c d * layerInd N c d' = if d = d' then layerInd N c d else 0 := by
  by_cases hdd : d = d'
  · subst hdd
    rw [ite_eq_left rfl]
    funext x
    rw [Pi.mul_apply]
    by_cases hx : InLayer c d x.val
    · rw [layerInd_apply_of_inLayer N c d hx, mul_one]
    · rw [layerInd_apply_of_not_inLayer N c d hx, mul_zero]
  · rw [ite_eq_right hdd]
    funext x
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases hx : InLayer c d x.val
    · rw [layerInd_apply_of_not_inLayer N c d' (fun h => hdd (layer_unique hd hd' hx h)), mul_zero]
    · rw [layerInd_apply_of_not_inLayer N c d hx, zero_mul]

/-! ### 1. 行列単位 -/

/-- 行列単位 E^d_{χ→χ′} = Θ_{χ→χ′}·ι_d·P_χ（V_χ の d の層を V_χ′ の d の層へ写し、ほかのブロックでは 0）。 -/
noncomputable def matUnit (N c d : ℕ) [NeZero N] [NeZero c] (χ χ' : DirichletCharacter ℂ c) :
    Module.End ℂ (ZMod N → ℂ) :=
  LinearMap.mulLeft ℂ (twistFn N c χ χ' * layerInd N c d) ∘ₗ blockProjL N c χ

/-- **1a.** 値：E^d_{χ→χ′} f = Θ_{χ→χ′}·(ι_d·P_χ f)。 -/
theorem matUnit_apply (N c d : ℕ) [NeZero N] [NeZero c] (χ χ' : DirichletCharacter ℂ c) (f : ZMod N → ℂ) :
    matUnit N c d χ χ' f = twistFn N c χ χ' * (layerInd N c d * blockProj N c χ f) := by
  rw [← mul_assoc]
  rfl

/-- **1b.** E^d_{χ→χ′} f ∈ W_{c,χ′}(d)。 -/
theorem matUnit_mem_layerPart (N c d : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hd : RadDvd d c) (f : ZMod N → ℂ) : matUnit N c d χ χ' f ∈ layerPart N c χ' d := by
  rw [matUnit_apply]
  exact twistFn_mul_mem_layerPart N c hcN χ χ' (layerInd_mul_mem N c hcN χ hd (blockProjL_mem N c χ f))

/-- **1c.** E^d_{χ→χ′} f ∈ V_χ′。 -/
theorem matUnit_mem_blockSpan (N c d : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hd : RadDvd d c) (f : ZMod N → ℂ) : matUnit N c d χ χ' f ∈ blockSpan N c χ' :=
  ((mem_layerPart N c χ' d _).mp (matUnit_mem_layerPart N c d hcN χ χ' hd f)).1

/-- **1d.** E^d_{χ→χ′} ∈ A′（rad(d) ∣ c、χ, χ′ は原始的）。 -/
theorem matUnit_mem_fullComm (N c d : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) (hd : RadDvd d c) : matUnit N c d χ χ' ∈ fullComm N := by
  rw [mem_fullComm]
  intro s f
  have hPf : blockProj N c χ f ∈ blockSpan N c χ := blockProjL_mem N c χ f
  have hιf : layerInd N c d * blockProj N c χ f ∈ blockSpan N c χ :=
    ((mem_layerPart N c χ d _).mp (layerInd_mul_mem N c hcN χ hd hPf)).1
  refine ⟨?_, ?_⟩
  · rw [matUnit_apply, matUnit_apply, ← geps_conv_blockProj N c hcN χ hχ s f,
      layerInd_mul_geps_conv N c hcN χ hχ hd s hPf, twistFn_mul_geps_conv N c hcN χ χ' hχ hχ' s hιf]
  · rw [matUnit_apply, matUnit_apply, ← dind_mul_blockProj N c hcN χ hχ s f,
      mul_left_comm (layerInd N c d) (dind N s), mul_left_comm (twistFn N c χ χ') (dind N s)]

/-- **1e.** f ∈ V_χ なら E^d_{χ→χ′} f = Θ_{χ→χ′}·(ι_d·f)。 -/
theorem matUnit_apply_of_mem_self (N c d : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ χ' : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) :
    matUnit N c d χ χ' f = twistFn N c χ χ' * (layerInd N c d * f) := by
  rw [matUnit_apply, blockProj_of_mem N c hcN χ hχ hf]

/-- **1f.** f ∈ V_ψ、χ ≠ ψ（同じ導手）なら E^d_{χ→χ′} f = 0。 -/
theorem matUnit_apply_of_mem_ne (N c d : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ χ' ψ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (h : χ ≠ ψ)
    {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c ψ) : matUnit N c d χ χ' f = 0 := by
  rw [matUnit_apply, blockProj_eq_zero_of_mem N c c hcN hcN ψ χ hψ hχ
    (fun e => h (eq_of_heq (Sigma.mk.inj e).2).symm) hf, mul_zero, mul_zero]

/-- **1g.** f ∈ V_{c′,ψ}、c ≠ c′ なら E^d_{χ→χ′} f = 0。 -/
theorem matUnit_apply_of_mem_of_ne (N c c' d : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N)
    (hc'N : c' ∣ N) (χ χ' : DirichletCharacter ℂ c) (ψ : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive)
    (hψ : ψ.IsPrimitive) (hcc : c ≠ c') {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c' ψ) :
    matUnit N c d χ χ' f = 0 := by
  rw [matUnit_apply, blockProj_eq_zero_of_mem N c' c hc'N hcN ψ χ hψ hχ
    (fun e => hcc (Sigma.mk.inj e).1.symm) hf, mul_zero, mul_zero]

/-- **1h.** 積の規則：E^d_{χ′→χ″}·E^d_{χ→χ′} = E^d_{χ→χ″}。 -/
theorem matUnit_mul_self (N c d : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (hd : RadDvd d c)
    (χ χ' χ'' : DirichletCharacter ℂ c) (hχ' : χ'.IsPrimitive) :
    matUnit N c d χ' χ'' * matUnit N c d χ χ' = matUnit N c d χ χ'' := by
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply,
    matUnit_apply_of_mem_self N c d hcN χ' χ'' hχ' (matUnit_mem_blockSpan N c d hcN χ χ' hd f),
    matUnit_apply, matUnit_apply, mul_left_comm (layerInd N c d) (twistFn N c χ χ'),
    ← mul_assoc (layerInd N c d) (layerInd N c d), layerInd_mul_layerInd N c hd hd, ite_eq_left rfl,
    ← mul_assoc, twistFn_mul_twistFn_eq]

/-- **1i.** ψ ≠ χ′（同じ導手）なら E^d_{ψ→χ″}·E^{d′}_{χ→χ′} = 0。 -/
theorem matUnit_mul_of_ne_char (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (d d' : ℕ) (hd' : RadDvd d' c)
    (ψ χ'' χ χ' : DirichletCharacter ℂ c) (hψ : ψ.IsPrimitive) (hχ' : χ'.IsPrimitive) (h : ψ ≠ χ') :
    matUnit N c d ψ χ'' * matUnit N c d' χ χ' = 0 := by
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply, LinearMap.zero_apply]
  exact matUnit_apply_of_mem_ne N c d hcN ψ χ'' χ' hψ hχ' h (matUnit_mem_blockSpan N c d' hcN χ χ' hd' f)

/-- **1j.** c ≠ c′ なら E^d_{ψ→χ″}·E^{d′}_{χ→χ′} = 0。 -/
theorem matUnit_mul_of_ne_cond (N c c' d d' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N)
    (hc'N : c' ∣ N) (hcc : c ≠ c') (ψ χ'' : DirichletCharacter ℂ c) (χ χ' : DirichletCharacter ℂ c')
    (hψ : ψ.IsPrimitive) (hχ' : χ'.IsPrimitive) (hd' : RadDvd d' c') :
    matUnit N c d ψ χ'' * matUnit N c' d' χ χ' = 0 := by
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply, LinearMap.zero_apply]
  exact matUnit_apply_of_mem_of_ne N c c' d hcN hc'N ψ χ'' χ' hψ hχ' hcc
    (matUnit_mem_blockSpan N c' d' hc'N χ χ' hd' f)

/-- **1k.** d ≠ d′ なら E^d_{ψ→χ″}·E^{d′}_{χ→χ′} = 0（導手は任意）。 -/
theorem matUnit_mul_of_ne_layer (N c c' d d' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N)
    (hc'N : c' ∣ N) (hdd : d ≠ d') (ψ χ'' : DirichletCharacter ℂ c) (χ χ' : DirichletCharacter ℂ c')
    (hψ : ψ.IsPrimitive) (hχ' : χ'.IsPrimitive) (hd : RadDvd d c) (hd' : RadDvd d' c') :
    matUnit N c d ψ χ'' * matUnit N c' d' χ χ' = 0 := by
  by_cases hcc : c = c'
  · subst c'
    by_cases hψχ : ψ = χ'
    · subst χ'
      apply LinearMap.ext
      intro f
      rw [Module.End.mul_apply, LinearMap.zero_apply,
        matUnit_apply_of_mem_self N c d hcN ψ χ'' hψ (matUnit_mem_blockSpan N c d' hcN χ ψ hd' f),
        layerInd_mul_of_mem N c ψ hd hd' (matUnit_mem_layerPart N c d' hcN χ ψ hd' f), ite_eq_right hdd,
        mul_zero]
    · exact matUnit_mul_of_ne_char N c hcN d d' hd' ψ χ'' χ χ' hψ hχ' hψχ
  · exact matUnit_mul_of_ne_cond N c c' d d' hcN hc'N hcc ψ χ'' χ χ' hψ hχ' hd'

/-- **1l.** E^d_{χ→χ′} ≠ 0（d ∈ D(c)、χ, χ′ は原始的）。 -/
theorem matUnit_ne_zero (N c d : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) (hdI : d ∈ layerIdx c (N / c)) : matUnit N c d χ χ' ≠ 0 := by
  intro h0
  obtain ⟨hdD, hd⟩ := (mem_layerIdx c (N / c) d).mp hdI
  have hdL := Nat.dvd_of_mem_divisors hdD
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hdD
  have hdd : InLayer c d d := ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩
  have hG := gblock_mem_layerPart N c hcN χ hχ hdL hd hdd
  have e := LinearMap.congr_fun h0 (gblock N c χ d)
  rw [matUnit_apply_of_mem_self N c d hcN χ χ' hχ ((mem_layerPart N c χ d _).mp hG).1, LinearMap.zero_apply,
    layerInd_mul_of_mem N c χ hd hd hG, ite_eq_left rfl, twistFn_mul_gblock N c hcN χ χ' hχ hχ' hdL hd hdd,
    Nat.div_self hd0, Nat.cast_one, map_one, mul_one] at e
  rcases smul_eq_zero.mp e with h1 | h1
  · exact twistConst_ne_zero c χ χ' hχ hχ' h1
  · exact gblock_ne_zero N c hcN χ' hdL h1

/-! ### 2. 原始指標の型、中心の元、S の番号どうしの積 -/

/-- 法 c の原始指標の型（Part 211 の BlockIdx の 2 番目の成分と同じ）。 -/
abbrev Prim (c : ℕ) : Type := {χ : DirichletCharacter ℂ c // χ.IsPrimitive}

/-- Prim c は有限（行列環の添字にする）。 -/
noncomputable instance fintypePrim (c : ℕ) : Fintype (Prim c) := Fintype.ofFinite _

/-- Prim c の等号の判定（古典論理）。 -/
noncomputable instance decEqPrim (c : ℕ) : DecidableEq (Prim c) := Classical.decEq _

/-- S の元の導手は 0 でない。 -/
instance neZero_centerIdx (N : ℕ) (p : centerIdx N) : NeZero p.1.1 :=
  ⟨(Nat.pos_of_mem_divisors ((mem_centerIdx N p.1).mp p.2).1).ne'⟩

/-- **2a.** Σ_{χ 原始} E^d_{χ→χ} = z_{c,d}（Part 222 の中心の元）。 -/
theorem sum_matUnit_self (N c : ℕ) [NeZero N] [NeZero c] (hc : c ∈ N.divisors) {d : ℕ}
    (hdI : d ∈ layerIdx c (N / c)) : ∑ i : Prim c, matUnit N c d i.1 i.1 = centralElt N c d := by
  apply LinearMap.ext
  intro f
  rw [LinearMap.sum_apply, centralElt_apply, Fintype.sum_sigma, Finset.sum_eq_single (⟨c, hc⟩ : N.divisors)]
  · dsimp only
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ite_eq_left rfl, matUnit_apply, ← mul_assoc, twistFn_self_mul_layerInd N c i.1 hdI]
  · intro c' _ hc'
    refine Finset.sum_eq_zero (fun i _ => ?_)
    exact ite_eq_right (fun h => hc' (Subtype.ext h))
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **2b.** Σ_{p ∈ S} Σ_χ E^{d_p}_{χ→χ} = 1。 -/
theorem sum_sum_matUnit_self (N : ℕ) [NeZero N] :
    ∑ p : centerIdx N, ∑ i : Prim p.1.1, matUnit N p.1.1 p.1.2 i.1 i.1 = 1 := by
  rw [← sum_centralElt N]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  exact sum_matUnit_self N p.1.1 hc hdI

/-- **2c.** p ≠ q（S の元）なら E_p(j→i)·E_q(l→k) = 0。 -/
theorem matUnit_mul_of_ne_idx (N : ℕ) [NeZero N] {p q : centerIdx N} (hpq : p ≠ q) (i j : Prim p.1.1)
    (k l : Prim q.1.1) : matUnit N p.1.1 p.1.2 j.1 i.1 * matUnit N q.1.1 q.1.2 l.1 k.1 = 0 := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  obtain ⟨hc', -, hdI'⟩ := (mem_centerIdx N q.1).mp q.2
  have hd := ((mem_layerIdx _ _ _).mp hdI).2
  have hd' := ((mem_layerIdx _ _ _).mp hdI').2
  by_cases hcc : p.1.1 = q.1.1
  · have hdd : p.1.2 ≠ q.1.2 := fun h => hpq (Subtype.ext (Sigma.ext hcc (heq_of_eq h)))
    exact matUnit_mul_of_ne_layer N p.1.1 q.1.1 p.1.2 q.1.2 (Nat.dvd_of_mem_divisors hc)
      (Nat.dvd_of_mem_divisors hc') hdd j.1 i.1 l.1 k.1 j.2 k.2 hd hd'
  · exact matUnit_mul_of_ne_cond N p.1.1 q.1.1 p.1.2 q.1.2 (Nat.dvd_of_mem_divisors hc)
      (Nat.dvd_of_mem_divisors hc') hcc j.1 i.1 l.1 k.1 j.2 k.2 hd'

/-! ### 3. Φ：Π_{p ∈ S} M_{m(c)}(ℂ) ≅ A′ -/

/-- Φ(M) = Σ_{p ∈ S} Σ_{i,j} M_p(i, j)·E^{d_p}_{j→i}。 -/
noncomputable def matSum (N : ℕ) [NeZero N] (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) :
    Module.End ℂ (ZMod N → ℂ) :=
  ∑ p : centerIdx N, ∑ i : Prim p.1.1, ∑ j : Prim p.1.1, M p i j • matUnit N p.1.1 p.1.2 j.1 i.1

/-- **3a.** Φ(M) ∈ A′。 -/
theorem matSum_mem_fullComm (N : ℕ) [NeZero N] (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) :
    matSum N M ∈ fullComm N := by
  unfold matSum
  refine Submodule.sum_mem _ (fun p _ => Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_)))
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  exact Submodule.smul_mem _ _ (matUnit_mem_fullComm N p.1.1 p.1.2 (Nat.dvd_of_mem_divisors hc) j.1 i.1 j.2 i.2
    ((mem_layerIdx _ _ _).mp hdI).2)

/-- **3b.** Φ は和を保つ。 -/
theorem matSum_add (N : ℕ) [NeZero N] (M M' : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) :
    matSum N (M + M') = matSum N M + matSum N M' := by
  unfold matSum
  simp only [Pi.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

/-- **3c.** Φ はスカラー倍を保つ。 -/
theorem matSum_smul (N : ℕ) [NeZero N] (r : ℂ) (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) :
    matSum N (r • M) = r • matSum N M := by
  unfold matSum
  simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Φ（線形写像）。 -/
noncomputable def matSumL (N : ℕ) [NeZero N] :
    (Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) →ₗ[ℂ] Module.End ℂ (ZMod N → ℂ) where
  toFun := matSum N
  map_add' := matSum_add N
  map_smul' := matSum_smul N

/-- **3d.** Φ(M)·T = Σ_p Σ_{i,j} M_p(i, j)·(E_p(j→i)·T)。 -/
theorem matSum_mul_eq (N : ℕ) [NeZero N] (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (T : Module.End ℂ (ZMod N → ℂ)) :
    matSum N M * T = ∑ p : centerIdx N, ∑ i : Prim p.1.1, ∑ j : Prim p.1.1,
      M p i j • (matUnit N p.1.1 p.1.2 j.1 i.1 * T) := by
  unfold matSum
  simp only [Finset.sum_mul, smul_mul_assoc]

/-- **3e.** E_p(j→i)·Φ(M) = Σ_l M_p(j, l)·E_p(l→i)。 -/
theorem matUnit_mul_matSum (N : ℕ) [NeZero N] (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (p : centerIdx N) (i j : Prim p.1.1) :
    matUnit N p.1.1 p.1.2 j.1 i.1 * matSum N M = ∑ l : Prim p.1.1, M p j l • matUnit N p.1.1 p.1.2 l.1 i.1 := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  have hcN := Nat.dvd_of_mem_divisors hc
  have hd := ((mem_layerIdx _ _ _).mp hdI).2
  unfold matSum
  rw [Finset.mul_sum, Finset.sum_eq_single p]
  · rw [Finset.mul_sum, Finset.sum_eq_single j]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [mul_smul_comm, matUnit_mul_self N p.1.1 p.1.2 hcN hd l.1 j.1 i.1 j.2]
    · intro k _ hkj
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      rw [mul_smul_comm, matUnit_mul_of_ne_char N p.1.1 hcN p.1.2 p.1.2 hd j.1 i.1 l.1 k.1 j.2 k.2
        (fun h => hkj (Subtype.ext h).symm), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q _ hqp
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [mul_smul_comm, matUnit_mul_of_ne_idx N (Ne.symm hqp) i j k l, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **3f.** Φ は積を保つ：Φ(MM′) = Φ(M)Φ(M′)。 -/
theorem matSum_mul (N : ℕ) [NeZero N] (M M' : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) :
    matSum N (M * M') = matSum N M * matSum N M' := by
  rw [matSum_mul_eq N M (matSum N M')]
  simp only [matUnit_mul_matSum, Finset.smul_sum, smul_smul]
  unfold matSum
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Pi.mul_apply, Matrix.mul_apply, Finset.sum_smul]

/-- **3g.** Φ(1) = 1。 -/
theorem matSum_one (N : ℕ) [NeZero N] : matSum N 1 = 1 := by
  rw [← sum_sum_matUnit_self N]
  unfold matSum
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [Finset.sum_eq_single i]
  · rw [Pi.one_apply, Matrix.one_apply_eq, one_smul]
  · intro j _ hji
    rw [Pi.one_apply, Matrix.one_apply_ne (Ne.symm hji), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **3h.** E_p(i→i)·Φ(M)·E_p(j→j) = M_p(i, j)·E_p(j→i)。 -/
theorem matUnit_mul_matSum_mul_matUnit (N : ℕ) [NeZero N]
    (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) (p : centerIdx N) (i j : Prim p.1.1) :
    matUnit N p.1.1 p.1.2 i.1 i.1 * matSum N M * matUnit N p.1.1 p.1.2 j.1 j.1 =
      M p i j • matUnit N p.1.1 p.1.2 j.1 i.1 := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  have hcN := Nat.dvd_of_mem_divisors hc
  have hd := ((mem_layerIdx _ _ _).mp hdI).2
  rw [matUnit_mul_matSum, Finset.sum_mul, Finset.sum_eq_single j]
  · rw [smul_mul_assoc, matUnit_mul_self N p.1.1 p.1.2 hcN hd j.1 j.1 i.1 j.2]
  · intro l _ hlj
    rw [smul_mul_assoc, matUnit_mul_of_ne_char N p.1.1 hcN p.1.2 p.1.2 hd l.1 i.1 j.1 j.1 l.2 j.2
      (fun h => hlj (Subtype.ext h)), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **3i.** Φ(M) = 0 なら M = 0。 -/
theorem matSum_eq_zero (N : ℕ) [NeZero N] {M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ}
    (h : matSum N M = 0) : M = 0 := by
  ext p i j
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  have e := matUnit_mul_matSum_mul_matUnit N M p i j
  rw [h, mul_zero, zero_mul] at e
  exact (smul_eq_zero.mp e.symm).resolve_right
    (matUnit_ne_zero N p.1.1 p.1.2 (Nat.dvd_of_mem_divisors hc) j.1 i.1 j.2 i.2 hdI)

/-- Φ（代数の準同型。値は A′ の部分代数）。 -/
noncomputable def matAlgHom (N : ℕ) [NeZero N] :
    (Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) →ₐ[ℂ] fullCommAlg N :=
  AlgHom.ofLinearMap
    { toFun := fun M => ⟨matSum N M, (mem_fullCommAlg N _).mpr (matSum_mem_fullComm N M)⟩
      map_add' := fun M M' => Subtype.ext (by
        show matSum N (M + M') = matSum N M + matSum N M'
        exact matSum_add N M M')
      map_smul' := fun r M => Subtype.ext (by
        show matSum N (r • M) = r • matSum N M
        exact matSum_smul N r M) }
    (Subtype.ext (by
      show matSum N 1 = 1
      exact matSum_one N))
    (fun M M' => Subtype.ext (by
      show matSum N (M * M') = matSum N M * matSum N M'
      exact matSum_mul N M M'))

/-- **3j.** (matAlgHom M) = Φ(M)。 -/
theorem matAlgHom_apply (N : ℕ) [NeZero N] (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) :
    (matAlgHom N M : Module.End ℂ (ZMod N → ℂ)) = matSum N M := rfl

/-- **3k.** Φ は単射。 -/
theorem matAlgHom_injective (N : ℕ) [NeZero N] : Function.Injective (matAlgHom N) := by
  intro M M' h
  have h1 : matSum N M = matSum N M' := congrArg Subtype.val h
  have h2 : matSum N (M - M') = 0 := by
    rw [show matSum N (M - M') = matSumL N (M - M') from rfl, map_sub]
    exact sub_eq_zero.mpr h1
  exact sub_eq_zero.mp (matSum_eq_zero N h2)

/-- A′ の部分代数と部分空間の線形同型（T ↦ T）。 -/
noncomputable def fullCommAlgLinearEquiv (N : ℕ) [NeZero N] : fullCommAlg N ≃ₗ[ℂ] fullComm N where
  toFun T := ⟨T.1, (mem_fullCommAlg N _).mp T.2⟩
  invFun T := ⟨T.1, (mem_fullCommAlg N _).mpr T.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **3l.** dim A′（部分代数として）= Σ_c m(c)²π(c)（Part 220）。 -/
theorem finrank_fullCommAlg (N : ℕ) [NeZero N] :
    Module.finrank ℂ (fullCommAlg N) = ∑ c ∈ N.divisors, Nat.card (Prim c) ^ 2 *
      ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1) :=
  (fullCommAlgLinearEquiv N).finrank_eq.trans (finrank_fullComm N)

/-- **3m.** dim Π_{p ∈ S} M_{m(c)}(ℂ) = Σ_{p ∈ S} m(c)² = Σ_c m(c)²π(c)。 -/
theorem finrank_matrixPi (N : ℕ) [NeZero N] :
    Module.finrank ℂ (Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) =
      ∑ c ∈ N.divisors, Nat.card (Prim c) ^ 2 *
        ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  calc Module.finrank ℂ (Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
      = ∑ p : centerIdx N, Fintype.card (Prim p.1.1) * Fintype.card (Prim p.1.1) := by
        rw [Module.finrank_pi_fintype ℂ]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Module.finrank_matrix, Module.finrank_self, mul_one]
    _ = ∑ p ∈ centerIdx N, Fintype.card (Prim p.1) * Fintype.card (Prim p.1) :=
        Finset.sum_coe_sort (centerIdx N) (fun p => Fintype.card (Prim p.1) * Fintype.card (Prim p.1))
    _ = ∑ c ∈ N.divisors.filter (fun c => 0 < Nat.card (Prim c)), Nat.card (Prim c) ^ 2 *
          ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1) := by
        unfold centerIdx
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl (fun c hc => ?_)
        have hc' := (Finset.mem_filter.mp hc).1
        calc ∑ s ∈ layerIdx c (N / c), Fintype.card (Prim c) * Fintype.card (Prim c)
            = ∑ s ∈ layerIdx c (N / c), Nat.card (Prim c) ^ 2 :=
              Finset.sum_congr rfl (fun s _ => by rw [Nat.card_eq_fintype_card, sq])
          _ = _ := by
              rw [Finset.sum_const, smul_eq_mul, card_layerIdx c (N / c)
                (Nat.div_pos (Nat.le_of_dvd hN0 (Nat.dvd_of_mem_divisors hc')) (Nat.pos_of_mem_divisors hc')).ne',
                mul_comm]
    _ = _ := Finset.sum_filter_of_ne (fun c _ h => Nat.pos_of_ne_zero (fun h0 => h (by
          rw [h0, zero_pow two_ne_zero, zero_mul])))

/-- Φ（線形写像、値は A′ の部分代数。加群の構造は既定のもの）。 -/
noncomputable def matLin (N : ℕ) [NeZero N] :
    (Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) →ₗ[ℂ] fullCommAlg N where
  toFun M := ⟨matSum N M, (mem_fullCommAlg N _).mpr (matSum_mem_fullComm N M)⟩
  map_add' M M' := Subtype.ext (by
    show matSum N (M + M') = matSum N M + matSum N M'
    exact matSum_add N M M')
  map_smul' r M := Subtype.ext (by
    show matSum N (r • M) = r • matSum N M
    exact matSum_smul N r M)

/-- **3n.** Φ は全単射（単射と次元の一致）。 -/
theorem matAlgHom_bijective (N : ℕ) [NeZero N] : Function.Bijective (matAlgHom N) := by
  refine ⟨matAlgHom_injective N, ?_⟩
  have H : Module.finrank ℂ (Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) =
      Module.finrank ℂ (fullCommAlg N) := (finrank_matrixPi N).trans (finrank_fullCommAlg N).symm
  have hinj : Function.Injective (matLin N) := fun M M' h => matAlgHom_injective N h
  have key := LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℂ)
    (V := Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) (V₂ := fullCommAlg N) H (f := matLin N)
  exact fun T => key.mp hinj T

/-- **3o. 代数の同型** Π_{p ∈ S} M_{m(c)}(ℂ) ≅ A′。 -/
noncomputable def fullCommMatrixEquiv (N : ℕ) [NeZero N] :
    (Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) ≃ₐ[ℂ] fullCommAlg N :=
  AlgEquiv.ofBijective (matAlgHom N) (matAlgHom_bijective N)

/-- **3p.** Φ(Pi.single p 1) = z_p（中心の冪等元は Part 222 の z_{c,d} に写る）。 -/
theorem matSum_single_one (N : ℕ) [NeZero N] (p : centerIdx N) :
    matSum N (Pi.single p 1) = centralElt N p.1.1 p.1.2 := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  rw [← sum_matUnit_self N p.1.1 hc hdI]
  unfold matSum
  rw [Finset.sum_eq_single p]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, Matrix.one_apply_eq, one_smul]
    · intro j _ hji
      rw [Pi.single_eq_same, Matrix.one_apply_ne (Ne.symm hji), zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q _ hqp
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    rw [Pi.single_eq_of_ne hqp, Matrix.zero_apply, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end PAG.Part227

#print axioms PAG.Part227.twistFn_mul_twistFn_eq
#print axioms PAG.Part227.twistFn_self_mul_layerInd
#print axioms PAG.Part227.layerInd_mul_layerInd
#print axioms PAG.Part227.matUnit
#print axioms PAG.Part227.matUnit_apply
#print axioms PAG.Part227.matUnit_mem_layerPart
#print axioms PAG.Part227.matUnit_mem_blockSpan
#print axioms PAG.Part227.matUnit_mem_fullComm
#print axioms PAG.Part227.matUnit_apply_of_mem_self
#print axioms PAG.Part227.matUnit_apply_of_mem_ne
#print axioms PAG.Part227.matUnit_apply_of_mem_of_ne
#print axioms PAG.Part227.matUnit_mul_self
#print axioms PAG.Part227.matUnit_mul_of_ne_char
#print axioms PAG.Part227.matUnit_mul_of_ne_cond
#print axioms PAG.Part227.matUnit_mul_of_ne_layer
#print axioms PAG.Part227.matUnit_ne_zero
#print axioms PAG.Part227.Prim
#print axioms PAG.Part227.fintypePrim
#print axioms PAG.Part227.decEqPrim
#print axioms PAG.Part227.neZero_centerIdx
#print axioms PAG.Part227.sum_matUnit_self
#print axioms PAG.Part227.sum_sum_matUnit_self
#print axioms PAG.Part227.matUnit_mul_of_ne_idx
#print axioms PAG.Part227.matSum
#print axioms PAG.Part227.matSum_mem_fullComm
#print axioms PAG.Part227.matSum_add
#print axioms PAG.Part227.matSum_smul
#print axioms PAG.Part227.matSumL
#print axioms PAG.Part227.matSum_mul_eq
#print axioms PAG.Part227.matUnit_mul_matSum
#print axioms PAG.Part227.matSum_mul
#print axioms PAG.Part227.matSum_one
#print axioms PAG.Part227.matUnit_mul_matSum_mul_matUnit
#print axioms PAG.Part227.matSum_eq_zero
#print axioms PAG.Part227.matAlgHom
#print axioms PAG.Part227.matAlgHom_apply
#print axioms PAG.Part227.matAlgHom_injective
#print axioms PAG.Part227.fullCommAlgLinearEquiv
#print axioms PAG.Part227.finrank_fullCommAlg
#print axioms PAG.Part227.finrank_matrixPi
#print axioms PAG.Part227.matLin
#print axioms PAG.Part227.matAlgHom_bijective
#print axioms PAG.Part227.fullCommMatrixEquiv
#print axioms PAG.Part227.matSum_single_one
