/-
  PAG 2.0 Part 222（2026-10-29）— 可換子 A′ の中心
  A′（Part 220 の fullComm）、ブロック b = (c, χ)、V_b、P_b、層 d ∈ D(c)、ι_d（Part 217 の layerInd）、
  m(c) = 法 c の原始指標の数、S = {(c, d) : c ∣ N、m(c) > 0、d ∈ D(c)}（def centerIdx）
  0. 同じ導手のブロックの間の A 準同型 X : V_χ → V_χ′ は、V_χ の上で関数 Θ_{χ→χ′}·φ を掛ける作用素
     （Part 218 のねじりと Part 221）。導手が違えば成分は 0（Part 219）。よって A′ の元は各ブロックの上で
     関数を掛ける作用素
  1. z_{c,d} = Σ_{b : c_b = c} ι_d·P_b（def centralElt）は V_b の上で [c_b = c]·ι_d。A′ に入り、A′ のすべての元と可換
  2. 中心（def fullCommCenter）の元 Z は各ブロックを保ち（P_χ の延長と可換）、層 W_{c,χ}(d) の上でスカラー
     μ_{c,χ,d}(Z)（def layerScalar）。ねじりの延長と可換なので、μ は同じ導手のブロックで等しい
  3. p ∈ S と g ∈ W_{c,χ}(d) について (Σ_j a_j·z_j) g = a_p·g。よって z_p は一次独立で、中心 = span{z_p}。
     dim（中心）= #S = Σ_{c ∣ N, m(c) > 0} Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)
  4. A′ と中心は部分代数（def fullCommAlg・centerAlg）。z_p z_q = [p = q]·z_p、Σ_p z_p = 1 で、
     a ↦ Σ_p a_p·z_p は代数の同型 ℂ^S ≅ 中心（def centerAlgEquiv）。中心は Mathlib の Subalgebra.center ℂ (fullCommAlg N)
     と一致し（def centerMathlibEquiv・centerEquivPi・centerLinearEquiv）、その次元も同じ式
-/
import PAG225

namespace PAG.Part226

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. A′ の元は各ブロックの上で関数を掛ける作用素 -/

/-- **0a.** 同じ導手のブロックの間の A 準同型 X : V_χ → V_χ′ は、V_χ の上で関数 ψ = Θ_{χ→χ′}·φ を掛ける作用素。 -/
theorem blockHom_exists_mul (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) {X : blockSpan N c χ →ₗ[ℂ] blockSpan N c χ'}
    (hX : X ∈ blockHom N c c χ χ') : ∃ ψ : ZMod N → ℂ, ∀ g : blockSpan N c χ, (X g : ZMod N → ℂ) = ψ * g := by
  obtain ⟨φ, hφ⟩ := blockComm_exists_mul N c hcN χ hχ (twistV_comp_mem_blockComm N c hcN χ χ' hχ hχ' hX)
  refine ⟨twistFn N c χ χ' * φ, fun g => ?_⟩
  have h1 := hφ g
  rw [LinearMap.comp_apply, twistV_apply] at h1
  calc (X g : ZMod N → ℂ) = twistFn N c χ χ' * (twistFn N c χ' χ * (X g : ZMod N → ℂ)) :=
        (twistFn_mul_twistFn N c hcN χ' χ (X g).2).symm
    _ = twistFn N c χ χ' * φ * g := by rw [h1, mul_assoc]

/-- **0b.** T ∈ A′、f ∈ V_b、c_b ≠ c_{b′} なら P_{b′}(T f) = 0（Part 219）。 -/
theorem blockProj_fullComm_eq_zero (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N)
    {b b' : BlockIdx N} (hcc : (b.1 : ℕ) ≠ b'.1) {f : ZMod N → ℂ} (hf : f ∈ blockSpan N b.1 b.2.1) :
    blockProj N b'.1 b'.2.1 (T f) = 0 := by
  have hm := commBlock_mem N b b' hT
  rw [blockHom_eq_bot_of_ne N b.1 b'.1 (Nat.dvd_of_mem_divisors b.1.2) (Nat.dvd_of_mem_divisors b'.1.2)
    b.2.1 b'.2.1 b.2.2 b'.2.2 hcc, Submodule.mem_bot] at hm
  have h1 : (commBlock N b b' T ⟨f, hf⟩ : ZMod N → ℂ) = 0 := by rw [hm]; rfl
  exact (commBlock_apply N b b' T ⟨f, hf⟩).symm.trans h1

/-- **0c.** T ∈ A′ の (b, b′) 成分は、V_b の上で関数を掛ける作用素（導手が違えば 0）。 -/
theorem commBlock_exists_mul (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N)
    (b b' : BlockIdx N) :
    ∃ ψ : ZMod N → ℂ, ∀ f ∈ blockSpan N b.1 b.2.1, blockProj N b'.1 b'.2.1 (T f) = ψ * f := by
  by_cases hcc : (b.1 : ℕ) = b'.1
  · obtain ⟨⟨c, hc⟩, ⟨χ, hχ⟩⟩ := b
    obtain ⟨⟨c', hc'⟩, ⟨χ', hχ'⟩⟩ := b'
    have hcc' : c = c' := hcc
    subst hcc'
    have : NeZero c := ⟨(Nat.pos_of_mem_divisors hc).ne'⟩
    obtain ⟨ψ, hψ⟩ := blockHom_exists_mul N c (Nat.dvd_of_mem_divisors hc) χ χ' hχ hχ'
      (commBlock_mem N ⟨⟨c, hc⟩, ⟨χ, hχ⟩⟩ ⟨⟨c, hc'⟩, ⟨χ', hχ'⟩⟩ hT)
    exact ⟨ψ, fun f hf => (commBlock_apply N ⟨⟨c, hc⟩, ⟨χ, hχ⟩⟩ ⟨⟨c, hc'⟩, ⟨χ', hχ'⟩⟩ T ⟨f, hf⟩).symm.trans
      (hψ ⟨f, hf⟩)⟩
  · exact ⟨0, fun f hf => by rw [zero_mul]; exact blockProj_fullComm_eq_zero N hT hcc hf⟩

/-- **0d. A′ の元は各ブロック V_b の上で関数を掛ける作用素**：T f = Ψ_b·f（f ∈ V_b）。 -/
theorem fullComm_exists_mul (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N)
    (b : BlockIdx N) : ∃ Ψ : ZMod N → ℂ, ∀ f ∈ blockSpan N b.1 b.2.1, T f = Ψ * f := by
  classical
  choose ψ hψ using fun b' => commBlock_exists_mul N hT b b'
  refine ⟨∑ b', ψ b', fun f hf => ?_⟩
  rw [Finset.sum_mul, ← sum_blockProj N (T f)]
  exact Finset.sum_congr rfl (fun b' _ => hψ b' f hf)

/-! ### 1. 中心の元 z_{c,d} -/

/-- z_{c,d} = Σ_{b : c_b = c} ι_d·P_b。 -/
noncomputable def centralElt (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (c d : ℕ) : Module.End ℂ (ZMod N → ℂ) :=
  ∑ b : BlockIdx N, if (b.1 : ℕ) = c then LinearMap.mulLeft ℂ (layerInd N c d) ∘ₗ blockProjL N b.1 b.2.1 else 0

/-- **1a.** z_{c,d} f = Σ_{b : c_b = c} ι_d·(P_b f)。 -/
theorem centralElt_apply (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (c d : ℕ) (f : ZMod N → ℂ) :
    centralElt N c d f =
      ∑ b : BlockIdx N, if (b.1 : ℕ) = c then layerInd N c d * blockProj N b.1 b.2.1 f else 0 := by
  unfold centralElt
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs <;> rfl

/-- **1b.** f ∈ V_{b₀} なら z_{c,d} f = [c_{b₀} = c]·ι_d·f。 -/
theorem centralElt_apply_of_mem (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (c d : ℕ) {b₀ : BlockIdx N}
    {f : ZMod N → ℂ} (hf : f ∈ blockSpan N b₀.1 b₀.2.1) :
    centralElt N c d f = if (b₀.1 : ℕ) = c then layerInd N c d * f else 0 := by
  rw [centralElt_apply, Finset.sum_eq_single b₀]
  · rw [blockProj_of_mem N b₀.1 (Nat.dvd_of_mem_divisors b₀.1.2) b₀.2.1 b₀.2.2 hf]
  · intro b _ hb
    rw [blockProj_eq_zero_of_mem_idx N (Ne.symm hb) hf, mul_zero, ite_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **1c.** （法と指標を明示した形）f ∈ V_{c,χ} なら z_{c′,d} f = [c = c′]·ι_d·f。 -/
theorem centralElt_apply_of_mem' (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] {c : ℕ} (hc : c ∈ N.divisors)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {c' d : ℕ} {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) :
    centralElt N c' d f = if c = c' then layerInd N c' d * f else 0 :=
  centralElt_apply_of_mem N c' d (b₀ := ⟨⟨c, hc⟩, ⟨χ, hχ⟩⟩) hf

/-- **1d.** z_{c,d} ∈ A′（rad(d) ∣ c）。 -/
theorem centralElt_mem_fullComm (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (c d : ℕ) (hd : RadDvd d c) :
    centralElt N c d ∈ fullComm N := by
  unfold centralElt
  refine Submodule.sum_mem _ (fun b _ => ?_)
  split_ifs with hbc
  · subst hbc
    have hb := Nat.dvd_of_mem_divisors b.1.2
    rw [mem_fullComm]
    intro s f
    refine ⟨?_, ?_⟩
    · show layerInd N b.1 d * blockProj N b.1 b.2.1 (PAG.Part15.conv (geps N s) f) =
        PAG.Part15.conv (geps N s) (layerInd N b.1 d * blockProj N b.1 b.2.1 f)
      rw [← geps_conv_blockProj N b.1 hb b.2.1 b.2.2 s f]
      exact layerInd_mul_geps_conv N b.1 hb b.2.1 b.2.2 hd s (blockProjL_mem N b.1 b.2.1 f)
    · show layerInd N b.1 d * blockProj N b.1 b.2.1 (dind N s * f) =
        dind N s * (layerInd N b.1 d * blockProj N b.1 b.2.1 f)
      rw [← dind_mul_blockProj N b.1 hb b.2.1 b.2.2 s f, mul_left_comm]
  · exact Submodule.zero_mem _

/-- **1e.** T ∈ A′、f ∈ V_b なら z_{c,d}(T f) = [c_b = c]·ι_d·(T f)（ほかの導手への成分は 0）。 -/
theorem centralElt_apply_fullComm (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (c d : ℕ)
    {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N) {b : BlockIdx N} {f : ZMod N → ℂ}
    (hf : f ∈ blockSpan N b.1 b.2.1) :
    centralElt N c d (T f) = if (b.1 : ℕ) = c then layerInd N c d * T f else 0 := by
  rw [centralElt_apply]
  by_cases hbc : (b.1 : ℕ) = c
  · rw [ite_eq_left hbc]
    conv_rhs => rw [← sum_blockProj N (T f), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    by_cases hb'c : (b'.1 : ℕ) = c
    · rw [ite_eq_left hb'c]
    · rw [ite_eq_right hb'c, blockProj_fullComm_eq_zero N hT (fun h => hb'c (h.symm.trans hbc)) hf, mul_zero]
  · rw [ite_eq_right hbc]
    refine Finset.sum_eq_zero (fun b' _ => ?_)
    by_cases hb'c : (b'.1 : ℕ) = c
    · rw [ite_eq_left hb'c, blockProj_fullComm_eq_zero N hT (fun h => hbc (h.trans hb'c)) hf, mul_zero]
    · rw [ite_eq_right hb'c]

/-- **1f.** z_{c,d} は A′ のすべての元と可換（rad(d) ∣ c）。 -/
theorem centralElt_commute (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (c d : ℕ) (hd : RadDvd d c)
    {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N) : Commute (centralElt N c d) T := by
  apply LinearMap.ext
  intro g
  rw [Module.End.mul_apply, Module.End.mul_apply, ← sum_blockProj N g]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hPg : blockProj N b.1 b.2.1 g ∈ blockSpan N b.1 b.2.1 := blockProjL_mem N b.1 b.2.1 g
  rw [centralElt_apply_fullComm N c d hT hPg, centralElt_apply_of_mem N c d hPg]
  by_cases hbc : (b.1 : ℕ) = c
  · subst hbc
    obtain ⟨Ψ, hΨ⟩ := fullComm_exists_mul N hT b
    have hmem : layerInd N b.1 d * blockProj N b.1 b.2.1 g ∈ blockSpan N b.1 b.2.1 :=
      ((mem_layerPart N b.1 b.2.1 d _).mp
        (layerInd_mul_mem N b.1 (Nat.dvd_of_mem_divisors b.1.2) b.2.1 hd hPg)).1
    rw [ite_eq_left rfl, ite_eq_left rfl, hΨ _ hPg, hΨ _ hmem, mul_left_comm]
  · rw [ite_eq_right hbc, ite_eq_right hbc, map_zero]

/-! ### 2. 中心 -/

/-- A′ の中心：A′ の元で、A′ のすべての元と可換なもの。 -/
noncomputable def fullCommCenter (N : ℕ) [NeZero N] : Submodule ℂ (Module.End ℂ (ZMod N → ℂ)) where
  carrier := {Z | Z ∈ fullComm N ∧ ∀ T ∈ fullComm N, Commute Z T}
  add_mem' := by
    intro Z₁ Z₂ h₁ h₂
    simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
    exact ⟨Submodule.add_mem _ h₁.1 h₂.1, fun T hT => (h₁.2 T hT).add_left (h₂.2 T hT)⟩
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact ⟨Submodule.zero_mem _, fun T _ => Commute.zero_left T⟩
  smul_mem' := by
    intro r Z h
    simp only [Set.mem_ofPred_eq] at h ⊢
    exact ⟨Submodule.smul_mem _ r h.1, fun T hT => (h.2 T hT).smul_left r⟩

/-- **2a.** 中心の元の判定。 -/
theorem mem_fullCommCenter (N : ℕ) [NeZero N] (Z : Module.End ℂ (ZMod N → ℂ)) :
    Z ∈ fullCommCenter N ↔ Z ∈ fullComm N ∧ ∀ T ∈ fullComm N, Commute Z T := Iff.rfl

/-- **2b.** z_{c,d} は中心に入る（rad(d) ∣ c）。 -/
theorem centralElt_mem_center (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (c d : ℕ) (hd : RadDvd d c) :
    centralElt N c d ∈ fullCommCenter N :=
  (mem_fullCommCenter N _).mpr ⟨centralElt_mem_fullComm N c d hd, fun _ hT => centralElt_commute N c d hd hT⟩

/-- **2c.** 中心の元は各ブロックを保つ（V_χ の恒等写像の延長 = P_χ と可換）。 -/
theorem center_preserves (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {Z : Module.End ℂ (ZMod N → ℂ)} (hZ : Z ∈ fullCommCenter N) {f : ZMod N → ℂ}
    (hf : f ∈ blockSpan N c χ) : Z f ∈ blockSpan N c χ := by
  have hY := blockHomExt_mem_fullComm N c c hcN χ χ hχ (id_mem_blockHom N c χ)
  have e := LinearMap.congr_fun (((mem_fullCommCenter N Z).mp hZ).2 _ hY).eq f
  rw [Module.End.mul_apply, Module.End.mul_apply] at e
  have hYf : blockHomExt N c c χ χ LinearMap.id f = f := blockProj_of_mem N c hcN χ hχ hf
  rw [hYf] at e
  rw [e]
  exact blockProjL_mem N c χ _

/-- 層 d の上のスカラー：μ_{c,χ,d}(Z) = (N/φ(dc))·⟨G_d, Z G_d⟩。 -/
noncomputable def layerScalar (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (d : ℕ)
    (Z : Module.End ℂ (ZMod N → ℂ)) : ℂ :=
  (N : ℂ) / (Nat.totient (d * c) : ℂ) * ∑ x, starRingEnd ℂ (gblock N c χ d x) * Z (gblock N c χ d) x

/-- **2d.** 中心の元は層 W_{c,χ}(d) の上でスカラー μ_{c,χ,d}(Z)。 -/
theorem center_smul_layerPart (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) {Z : Module.End ℂ (ZMod N → ℂ)}
    (hZ : Z ∈ fullCommCenter N) {g : ZMod N → ℂ} (hg : g ∈ layerPart N c χ d) :
    Z g = layerScalar N c χ d Z • g := by
  have hZA := ((mem_fullCommCenter N Z).mp hZ).1
  exact layerPart_smul_of_commute N c hcN χ hχ hdL hd Z (fun s f _ => ((mem_fullComm N Z).mp hZA s f).1)
    (fun s f _ => ((mem_fullComm N Z).mp hZA s f).2)
    (fun f hf => center_preserves N c hcN χ hχ hZ ((mem_layerPart N c χ d f).mp hf).1) g hg

/-- **2e.** 中心の元のスカラーは同じ導手のブロックで等しい：μ_{c,χ,d}(Z) = μ_{c,χ′,d}(Z)
（ねじり Θ_{χ→χ′} の延長と可換で、Θ G^χ_d = κ·G^{χ′}_d、κ ≠ 0）。 -/
theorem layerScalar_eq_of_center (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c)
    {Z : Module.End ℂ (ZMod N → ℂ)} (hZ : Z ∈ fullCommCenter N) :
    layerScalar N c χ d Z = layerScalar N c χ' d Z := by
  have hdd : InLayer c d d := ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩
  have hG := gblock_mem_layerPart N c hcN χ hχ hdL hd hdd
  have hG' := gblock_mem_layerPart N c hcN χ' hχ' hdL hd hdd
  have hG'0 := gblock_ne_zero N c hcN χ' hdL
  have hL0 : 0 < N / c :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hcN) (Nat.pos_of_ne_zero (NeZero.ne c))
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdL hL0
  have hX := blockHomExt_mem_fullComm N c c hcN χ χ' hχ
    (twistV_comp_mem_blockHom N c hcN χ χ' hχ hχ' (id_mem_blockComm N c χ))
  have hXG : blockHomExt N c c χ χ' (twistV N c hcN χ χ' ∘ₗ LinearMap.id) (gblock N c χ d) =
      twistConst χ χ' • gblock N c χ' d := by
    have h1 := twistFn_mul_gblock N c hcN χ χ' hχ hχ' hdL hd hdd
    rw [Nat.div_self hd0, Nat.cast_one, map_one, mul_one] at h1
    calc blockHomExt N c c χ χ' (twistV N c hcN χ χ' ∘ₗ LinearMap.id) (gblock N c χ d)
        = twistFn N c χ χ' * blockProj N c χ (gblock N c χ d) := rfl
      _ = twistFn N c χ χ' * gblock N c χ d := by
          rw [blockProj_of_mem N c hcN χ hχ ((mem_layerPart N c χ d _).mp hG).1]
      _ = _ := h1
  have e := LinearMap.congr_fun (((mem_fullCommCenter N Z).mp hZ).2 _ hX).eq (gblock N c χ d)
  rw [Module.End.mul_apply, Module.End.mul_apply] at e
  rw [hXG, center_smul_layerPart N c hcN χ hχ hdL hd hZ hG, map_smul, map_smul, hXG,
    center_smul_layerPart N c hcN χ' hχ' hdL hd hZ hG', smul_smul, smul_smul] at e
  have h3 : (twistConst χ χ' * layerScalar N c χ' d Z - layerScalar N c χ d Z * twistConst χ χ') •
      gblock N c χ' d = 0 := by
    rw [sub_smul, e, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · have h5 : twistConst χ χ' * layerScalar N c χ' d Z = twistConst χ χ' * layerScalar N c χ d Z := by
      rw [sub_eq_zero.mp h4, mul_comm]
    exact (mul_left_cancel₀ (twistConst_ne_zero c χ χ' hχ hχ') h5).symm
  · exact absurd h4 hG'0

/-! ### 3. 中心 = span{z_{c,d}}、中心の次元 -/

/-- 中心の番号：S = {(c, d) : c ∣ N、m(c) > 0、d ∈ D(c)}。 -/
noncomputable def centerIdx (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (N.divisors.filter (fun c => 0 < Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive})).sigma
    (fun c => layerIdx c (N / c))

/-- **3a.** S の元の判定。 -/
theorem mem_centerIdx (N : ℕ) (p : Σ _ : ℕ, ℕ) : p ∈ centerIdx N ↔
    p.1 ∈ N.divisors ∧ 0 < Nat.card {χ : DirichletCharacter ℂ p.1 // χ.IsPrimitive} ∧
      p.2 ∈ layerIdx p.1 (N / p.1) := by
  unfold centerIdx
  rw [Finset.mem_sigma, Finset.mem_filter, and_assoc]

/-- **3b.** i ∈ S、g ∈ W_{c,χ}(d)（(c, d) = i）なら (Σ_{j ∈ S} a_j·z_j) g = a_i·g。 -/
theorem sum_centralElt_apply (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (a : centerIdx N → ℂ)
    (i : centerIdx N) (χ : DirichletCharacter ℂ i.1.1) (hχ : χ.IsPrimitive) {g : ZMod N → ℂ}
    (hg : g ∈ layerPart N i.1.1 χ i.1.2) :
    (∑ j : centerIdx N, a j • centralElt N j.1.1 j.1.2) g = a i • g := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N i.1).mp i.2
  have hd := ((mem_layerIdx _ _ _).mp hdI).2
  have hgV : g ∈ blockSpan N i.1.1 χ := ((mem_layerPart N _ χ _ g).mp hg).1
  rw [LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [LinearMap.smul_apply, centralElt_apply_of_mem' N hc χ hχ hgV, ite_eq_left rfl,
      layerInd_mul_of_mem N _ χ hd hd hg, ite_eq_left rfl]
  · intro j _ hji
    rw [LinearMap.smul_apply, centralElt_apply_of_mem' N hc χ hχ hgV]
    by_cases hcj : i.1.1 = j.1.1
    · rw [ite_eq_left hcj]
      have hdj : j.1.2 ≠ i.1.2 := fun h => hji (Subtype.ext (Sigma.ext hcj.symm (heq_of_eq h)))
      have hj := ((mem_layerIdx _ _ _).mp ((mem_centerIdx N j.1).mp j.2).2.2).2
      rw [← hcj] at hj ⊢
      rw [layerInd_mul_of_mem N _ χ hj hd hg, ite_eq_right hdj, smul_zero]
    · rw [ite_eq_right hcj, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **3c.** 中心の元 Z が、各 p ∈ S について、ある原始指標 χ_p の層 W_{c,χ_p}(d) の上で 0 なら Z = 0
（μ は同じ導手で等しいので、すべての層の上で 0）。 -/
theorem center_eq_zero (N : ℕ) [NeZero N] {Z : Module.End ℂ (ZMod N → ℂ)} (hZ : Z ∈ fullCommCenter N)
    (h0 : ∀ p ∈ centerIdx N, ∃ χ : DirichletCharacter ℂ p.1, χ.IsPrimitive ∧
      ∀ g ∈ layerPart N p.1 χ p.2, Z g = 0) : Z = 0 := by
  classical
  apply LinearMap.ext
  intro f
  rw [LinearMap.zero_apply, ← sum_blockProj N f, map_sum]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  obtain ⟨⟨c, hc⟩, ⟨χ, hχ⟩⟩ := b
  have : NeZero c := ⟨(Nat.pos_of_mem_divisors hc).ne'⟩
  have hcN := Nat.dvd_of_mem_divisors hc
  have hPf : blockProj N c χ f ∈ blockSpan N c χ := blockProjL_mem N c χ f
  show Z (blockProj N c χ f) = 0
  rw [← sum_layerInd_mul N c hcN χ hPf, map_sum]
  refine Finset.sum_eq_zero (fun d hdI => ?_)
  obtain ⟨hdD, hd⟩ := (mem_layerIdx c (N / c) d).mp hdI
  have hdL := Nat.dvd_of_mem_divisors hdD
  have hpos : 0 < Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨χ, hχ⟩⟩, inferInstance⟩
  have hp : (⟨c, d⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx N := (mem_centerIdx N _).mpr ⟨hc, hpos, hdI⟩
  obtain ⟨χ₀, hχ₀, hz⟩ := h0 _ hp
  have hG₀ := gblock_mem_layerPart N c hcN χ₀ hχ₀ hdL hd ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩
  have hμ₀ : layerScalar N c χ₀ d Z = 0 := by
    have e := center_smul_layerPart N c hcN χ₀ hχ₀ hdL hd hZ hG₀
    rw [hz _ hG₀] at e
    exact (smul_eq_zero.mp e.symm).resolve_right (gblock_ne_zero N c hcN χ₀ hdL)
  have hμ : layerScalar N c χ d Z = 0 := by
    rw [layerScalar_eq_of_center N c hcN χ χ₀ hχ hχ₀ hdL hd hZ]
    exact hμ₀
  rw [center_smul_layerPart N c hcN χ hχ hdL hd hZ (layerInd_mul_mem N c hcN χ hd hPf), hμ, zero_smul]

/-- **3d.** z_p（p ∈ S）は一次独立。 -/
theorem centralElt_linearIndependent (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    LinearIndependent ℂ (fun j : centerIdx N => centralElt N j.1.1 j.1.2) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg i
  obtain ⟨hc, hpos, hdI⟩ := (mem_centerIdx N i.1).mp i.2
  obtain ⟨hdD, hd⟩ := (mem_layerIdx _ _ _).mp hdI
  have : NeZero i.1.1 := ⟨(Nat.pos_of_mem_divisors hc).ne'⟩
  obtain ⟨⟨χ, hχ⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  have hcN := Nat.dvd_of_mem_divisors hc
  have hG := gblock_mem_layerPart N i.1.1 hcN χ hχ (Nat.dvd_of_mem_divisors hdD) hd
    ⟨1, (mul_one _).symm, Nat.coprime_one_left _⟩
  have e := LinearMap.congr_fun hfg (gblock N i.1.1 χ i.1.2)
  rw [sum_centralElt_apply N f i χ hχ hG, sum_centralElt_apply N g i χ hχ hG] at e
  have h3 : (f i - g i) • gblock N i.1.1 χ i.1.2 = 0 := by rw [sub_smul, e, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp h4
  · exact absurd h4 (gblock_ne_zero N i.1.1 hcN χ (Nat.dvd_of_mem_divisors hdD))

/-- 中心の元の係数：(c, d) ↦ μ_{c,χ_c,d}(Z)（χ_c は法 c の原始指標の 1 つ。m(c) = 0 なら 0）。 -/
noncomputable def centerCoef (N : ℕ) [NeZero N] (Z : Module.End ℂ (ZMod N → ℂ)) (p : Σ _ : ℕ, ℕ) : ℂ :=
  if h : 0 < Nat.card {χ : DirichletCharacter ℂ p.1 // χ.IsPrimitive} then
    layerScalar N p.1 (Classical.choice (Nat.card_pos_iff.mp h).1).1 p.2 Z else 0

/-- **3e.** 中心の元は z_p の一次結合：Z = Σ_{p ∈ S} μ_p(Z)·z_p。 -/
theorem center_eq_sum (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] {Z : Module.End ℂ (ZMod N → ℂ)}
    (hZ : Z ∈ fullCommCenter N) :
    Z = ∑ j : centerIdx N, centerCoef N Z j.1 • centralElt N j.1.1 j.1.2 := by
  have hmem : ∀ j : centerIdx N, centralElt N j.1.1 j.1.2 ∈ fullCommCenter N := fun j =>
    centralElt_mem_center N j.1.1 j.1.2 ((mem_layerIdx _ _ _).mp ((mem_centerIdx N j.1).mp j.2).2.2).2
  have hW : Z - ∑ j : centerIdx N, centerCoef N Z j.1 • centralElt N j.1.1 j.1.2 ∈ fullCommCenter N :=
    Submodule.sub_mem _ hZ (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hmem j)))
  refine sub_eq_zero.mp (center_eq_zero N hW (fun p hp => ?_))
  obtain ⟨hc, hpos, hdI⟩ := (mem_centerIdx N p).mp hp
  obtain ⟨hdD, hd⟩ := (mem_layerIdx _ _ _).mp hdI
  have : NeZero p.1 := ⟨(Nat.pos_of_mem_divisors hc).ne'⟩
  refine ⟨(Classical.choice (Nat.card_pos_iff.mp hpos).1).1, (Classical.choice (Nat.card_pos_iff.mp hpos).1).2,
    fun g hg => ?_⟩
  rw [LinearMap.sub_apply, sum_centralElt_apply N (fun j => centerCoef N Z j.1) ⟨p, hp⟩ _
      (Classical.choice (Nat.card_pos_iff.mp hpos).1).2 hg,
    center_smul_layerPart N p.1 (Nat.dvd_of_mem_divisors hc) _ (Classical.choice (Nat.card_pos_iff.mp hpos).1).2
      (Nat.dvd_of_mem_divisors hdD) hd hZ hg]
  show layerScalar N p.1 (Classical.choice (Nat.card_pos_iff.mp hpos).1).1 p.2 Z • g - centerCoef N Z p • g = 0
  unfold centerCoef
  rw [dite_eq_left hpos, sub_self]

/-- **3f.** 中心 = span{z_p : p ∈ S}。 -/
theorem center_eq_span (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    fullCommCenter N = Submodule.span ℂ (Set.range (fun j : centerIdx N => centralElt N j.1.1 j.1.2)) := by
  apply le_antisymm
  · intro Z hZ
    rw [center_eq_sum N hZ]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact centralElt_mem_center N j.1.1 j.1.2 ((mem_layerIdx _ _ _).mp ((mem_centerIdx N j.1).mp j.2).2.2).2

/-- **3g. A′ の中心の次元**：dim = Σ_{c ∣ N, m(c) > 0} Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)
（成分の型 (c, d) の数。Part 220 の step243 の (4) で数値だけだった読み取り）。 -/
theorem finrank_fullCommCenter (N : ℕ) [NeZero N] :
    Module.finrank ℂ (fullCommCenter N) =
      ∑ c ∈ N.divisors.filter (fun c => 0 < Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive}),
        ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1) := by
  classical
  rw [center_eq_span N, finrank_span_eq_card (centralElt_linearIndependent N), Fintype.card_coe]
  unfold centerIdx
  rw [Finset.card_sigma]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  have hc' := (Finset.mem_filter.mp hc).1
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [card_layerIdx c (N / c)
    (Nat.div_pos (Nat.le_of_dvd hN0 (Nat.dvd_of_mem_divisors hc')) (Nat.pos_of_mem_divisors hc')).ne']

/-! ### 4. 中心は ℂ^S と代数として同型。Mathlib の中心（Subalgebra.center）との一致 -/

/-- **4a.** A′ は積で閉じる（A′ = 生成元の可換子：Part 220 の mem_fullComm_iff_commute）。 -/
theorem fullComm_mul_mem (N : ℕ) [NeZero N] {T T' : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N)
    (hT' : T' ∈ fullComm N) : T * T' ∈ fullComm N :=
  (mem_fullComm_iff_commute N _).mpr (fun S hS =>
    ((mem_fullComm_iff_commute N T).mp hT S hS).mul_left ((mem_fullComm_iff_commute N T').mp hT' S hS))

/-- **4b.** 恒等写像は A′ に入る。 -/
theorem one_mem_fullComm (N : ℕ) [NeZero N] : (1 : Module.End ℂ (ZMod N → ℂ)) ∈ fullComm N :=
  (mem_fullComm_iff_commute N _).mpr (fun S _ => Commute.one_left S)

/-- A′ の部分代数。 -/
noncomputable def fullCommAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  (fullComm N).toSubalgebra (one_mem_fullComm N) (fun _ _ hT hT' => fullComm_mul_mem N hT hT')

/-- **4c.** 判定（元は fullComm と同じ）。 -/
theorem mem_fullCommAlg (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ fullCommAlg N ↔ T ∈ fullComm N := Iff.rfl

/-- **4d.** 中心は積で閉じる。 -/
theorem center_mul_mem (N : ℕ) [NeZero N] {Z Z' : Module.End ℂ (ZMod N → ℂ)} (hZ : Z ∈ fullCommCenter N)
    (hZ' : Z' ∈ fullCommCenter N) : Z * Z' ∈ fullCommCenter N := by
  rw [mem_fullCommCenter] at hZ hZ' ⊢
  exact ⟨fullComm_mul_mem N hZ.1 hZ'.1, fun T hT => (hZ.2 T hT).mul_left (hZ'.2 T hT)⟩

/-- **4e.** 恒等写像は中心に入る。 -/
theorem one_mem_center (N : ℕ) [NeZero N] : (1 : Module.End ℂ (ZMod N → ℂ)) ∈ fullCommCenter N :=
  (mem_fullCommCenter N _).mpr ⟨one_mem_fullComm N, fun T _ => Commute.one_left T⟩

/-- 中心の部分代数。 -/
noncomputable def centerAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  (fullCommCenter N).toSubalgebra (one_mem_center N) (fun _ _ hZ hZ' => center_mul_mem N hZ hZ')

/-- **4f.** 判定（元は fullCommCenter と同じ）。 -/
theorem mem_centerAlg (N : ℕ) [NeZero N] (Z : Module.End ℂ (ZMod N → ℂ)) :
    Z ∈ centerAlg N ↔ Z ∈ fullCommCenter N := Iff.rfl

/-- **4g. Mathlib の中心との一致**：A′ の元 Z が代数 A′ の中心（Subalgebra.center）に入る ⇔ Z ∈ fullCommCenter。 -/
theorem mem_center_fullCommAlg (N : ℕ) [NeZero N] (Z : fullCommAlg N) :
    Z ∈ Subalgebra.center ℂ (fullCommAlg N) ↔ (Z : Module.End ℂ (ZMod N → ℂ)) ∈ fullCommCenter N := by
  rw [Subalgebra.mem_center_iff, mem_fullCommCenter]
  constructor
  · intro h
    refine ⟨(mem_fullCommAlg N _).mp Z.2, fun T hT => ?_⟩
    show (Z : Module.End ℂ (ZMod N → ℂ)) * T = T * Z
    exact (congrArg Subtype.val (h ⟨T, (mem_fullCommAlg N T).mpr hT⟩)).symm
  · rintro ⟨-, h⟩ T
    exact Subtype.ext (h T.1 ((mem_fullCommAlg N _).mp T.2)).eq.symm

/-- **4h.** r, p ∈ S、g ∈ W_{c_r,χ}(d_r) なら z_p g = [p = r]·g。 -/
theorem centralElt_apply_layer (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (r p : centerIdx N)
    (χ : DirichletCharacter ℂ r.1.1) (hχ : χ.IsPrimitive) {g : ZMod N → ℂ}
    (hg : g ∈ layerPart N r.1.1 χ r.1.2) : centralElt N p.1.1 p.1.2 g = if p = r then g else 0 := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N r.1).mp r.2
  have hd := ((mem_layerIdx _ _ _).mp hdI).2
  have hgV : g ∈ blockSpan N r.1.1 χ := ((mem_layerPart N _ χ _ g).mp hg).1
  rw [centralElt_apply_of_mem' N hc χ hχ hgV]
  by_cases hpr : p = r
  · subst hpr
    rw [layerInd_mul_of_mem N _ χ hd hd hg]
    simp
  · rw [ite_eq_right hpr]
    by_cases hcp : r.1.1 = p.1.1
    · rw [ite_eq_left hcp]
      have hdp : p.1.2 ≠ r.1.2 := fun h => hpr (Subtype.ext (Sigma.ext hcp.symm (heq_of_eq h)))
      have hp := ((mem_layerIdx _ _ _).mp ((mem_centerIdx N p.1).mp p.2).2.2).2
      rw [← hcp] at hp ⊢
      rw [layerInd_mul_of_mem N _ χ hp hd hg, ite_eq_right hdp]
    · rw [ite_eq_right hcp]

/-- **4i.** z_p z_q = [p = q]·z_p（p, q ∈ S。直交する冪等元）。 -/
theorem centralElt_mul (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (p q : centerIdx N) :
    centralElt N p.1.1 p.1.2 * centralElt N q.1.1 q.1.2 = if p = q then centralElt N p.1.1 p.1.2 else 0 := by
  have hmem : ∀ j : centerIdx N, centralElt N j.1.1 j.1.2 ∈ fullCommCenter N := fun j =>
    centralElt_mem_center N j.1.1 j.1.2 ((mem_layerIdx _ _ _).mp ((mem_centerIdx N j.1).mp j.2).2.2).2
  have hW : centralElt N p.1.1 p.1.2 * centralElt N q.1.1 q.1.2 -
      (if p = q then centralElt N p.1.1 p.1.2 else 0) ∈ fullCommCenter N := by
    refine Submodule.sub_mem _ (center_mul_mem N (hmem p) (hmem q)) ?_
    split_ifs
    · exact hmem p
    · exact Submodule.zero_mem _
  refine sub_eq_zero.mp (center_eq_zero N hW (fun r hr => ?_))
  obtain ⟨-, hpos, -⟩ := (mem_centerIdx N r).mp hr
  obtain ⟨⟨χ, hχ⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  refine ⟨χ, hχ, fun g hg => ?_⟩
  have hq := centralElt_apply_layer N ⟨r, hr⟩ q χ hχ hg
  have hp := centralElt_apply_layer N ⟨r, hr⟩ p χ hχ hg
  rw [LinearMap.sub_apply, Module.End.mul_apply, hq]
  by_cases hqr : q = ⟨r, hr⟩
  · rw [ite_eq_left hqr, hp]
    by_cases hpq : p = q
    · rw [ite_eq_left hpq, hp, sub_self]
    · rw [ite_eq_right hpq, ite_eq_right (fun h => hpq (h.trans hqr.symm)), LinearMap.zero_apply, sub_self]
  · rw [ite_eq_right hqr, map_zero]
    by_cases hpq : p = q
    · rw [ite_eq_left hpq, hp, ite_eq_right (fun h => hqr (hpq.symm.trans h)), sub_self]
    · rw [ite_eq_right hpq, LinearMap.zero_apply, sub_self]

/-- **4j.** Σ_{p ∈ S} z_p = 1。 -/
theorem sum_centralElt (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    ∑ j : centerIdx N, centralElt N j.1.1 j.1.2 = 1 := by
  have hmem : ∀ j : centerIdx N, centralElt N j.1.1 j.1.2 ∈ fullCommCenter N := fun j =>
    centralElt_mem_center N j.1.1 j.1.2 ((mem_layerIdx _ _ _).mp ((mem_centerIdx N j.1).mp j.2).2.2).2
  have hW : ∑ j : centerIdx N, centralElt N j.1.1 j.1.2 - 1 ∈ fullCommCenter N :=
    Submodule.sub_mem _ (Submodule.sum_mem _ (fun j _ => hmem j)) (one_mem_center N)
  refine sub_eq_zero.mp (center_eq_zero N hW (fun r hr => ?_))
  obtain ⟨-, hpos, -⟩ := (mem_centerIdx N r).mp hr
  obtain ⟨⟨χ, hχ⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  refine ⟨χ, hχ, fun g hg => ?_⟩
  have h := sum_centralElt_apply N (fun _ => 1) ⟨r, hr⟩ χ hχ hg
  simp only [one_smul] at h
  rw [LinearMap.sub_apply, h, Module.End.one_apply, sub_self]

/-- **4k.** Σ_p a_p·z_p は中心に入る。 -/
theorem sum_smul_centralElt_mem (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (a : centerIdx N → ℂ) :
    ∑ j : centerIdx N, a j • centralElt N j.1.1 j.1.2 ∈ fullCommCenter N :=
  Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (centralElt_mem_center N j.1.1 j.1.2
    ((mem_layerIdx _ _ _).mp ((mem_centerIdx N j.1).mp j.2).2.2).2))

/-- ℂ^S → 中心：a ↦ Σ_p a_p·z_p（代数の準同型）。 -/
noncomputable def centerAlgHom (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    (centerIdx N → ℂ) →ₐ[ℂ] centerAlg N :=
  AlgHom.ofLinearMap
    { toFun := fun a => ⟨∑ j, a j • centralElt N j.1.1 j.1.2, (mem_centerAlg N _).mpr (sum_smul_centralElt_mem N a)⟩
      map_add' := fun a b => by
        apply Subtype.ext
        show ∑ j, (a + b) j • centralElt N j.1.1 j.1.2 =
          ∑ j, a j • centralElt N j.1.1 j.1.2 + ∑ j, b j • centralElt N j.1.1 j.1.2
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by
        apply Subtype.ext
        show ∑ j, (r • a) j • centralElt N j.1.1 j.1.2 = r • ∑ j, a j • centralElt N j.1.1 j.1.2
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum] }
    (by
      apply Subtype.ext
      show ∑ j, (1 : centerIdx N → ℂ) j • centralElt N j.1.1 j.1.2 = 1
      simp only [Pi.one_apply, one_smul]
      exact sum_centralElt N)
    (fun a b => by
      apply Subtype.ext
      show ∑ j, (a * b) j • centralElt N j.1.1 j.1.2 =
        (∑ j, a j • centralElt N j.1.1 j.1.2) * ∑ j, b j • centralElt N j.1.1 j.1.2
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      simp only [smul_mul_smul_comm, centralElt_mul, smul_ite, smul_zero]
      rw [Finset.sum_ite_eq]
      simp)

/-- **4l.** (centerAlgHom a) = Σ_p a_p·z_p。 -/
theorem centerAlgHom_apply (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (a : centerIdx N → ℂ) :
    (centerAlgHom N a : Module.End ℂ (ZMod N → ℂ)) = ∑ j, a j • centralElt N j.1.1 j.1.2 := rfl

/-- **4m.** a ↦ Σ_p a_p·z_p は全単射（z_p は一次独立で中心を張る：3d・3e）。 -/
theorem centerAlgHom_bijective (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    Function.Bijective (centerAlgHom N) := by
  constructor
  · intro a b hab
    have h := congrArg (fun Z : centerAlg N => (Z : Module.End ℂ (ZMod N → ℂ))) hab
    simp only [centerAlgHom_apply] at h
    funext j
    exact Fintype.linearIndependent_iffₛ.mp (centralElt_linearIndependent N) a b h j
  · intro Z
    exact ⟨fun j => centerCoef N Z j.1, Subtype.ext (center_eq_sum N ((mem_centerAlg N _).mp Z.2)).symm⟩

/-- **4n. 代数の同型** ℂ^S ≅ (A′ の中心)。 -/
noncomputable def centerAlgEquiv (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    (centerIdx N → ℂ) ≃ₐ[ℂ] centerAlg N :=
  AlgEquiv.ofBijective (centerAlgHom N) (centerAlgHom_bijective N)

/-- Mathlib の中心 Z(A′)（Subalgebra.center）と centerAlg の代数の同型（Z ↦ Z）。 -/
noncomputable def centerMathlibEquiv (N : ℕ) [NeZero N] :
    Subalgebra.center ℂ (fullCommAlg N) ≃ₐ[ℂ] centerAlg N where
  toFun Z := ⟨Z.1.1, (mem_centerAlg N _).mpr ((mem_center_fullCommAlg N Z.1).mp Z.2)⟩
  invFun Z := ⟨⟨Z.1, (mem_fullCommAlg N _).mpr ((mem_fullCommCenter N _).mp ((mem_centerAlg N _).mp Z.2)).1⟩,
    (mem_center_fullCommAlg N _).mpr ((mem_centerAlg N _).mp Z.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- **4o. Mathlib の中心は ℂ^S と代数として同型**：Z(A′) ≅ ℂ^S。 -/
noncomputable def centerEquivPi (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    (centerIdx N → ℂ) ≃ₐ[ℂ] Subalgebra.center ℂ (fullCommAlg N) :=
  (centerAlgEquiv N).trans (centerMathlibEquiv N).symm

/-- Mathlib の中心と fullCommCenter の線形同型（Z ↦ Z）。 -/
noncomputable def centerLinearEquiv (N : ℕ) [NeZero N] :
    Subalgebra.center ℂ (fullCommAlg N) ≃ₗ[ℂ] fullCommCenter N where
  toFun Z := ⟨Z.1.1, (mem_center_fullCommAlg N Z.1).mp Z.2⟩
  invFun Z := ⟨⟨Z.1, (mem_fullCommAlg N _).mpr ((mem_fullCommCenter N _).mp Z.2).1⟩,
    (mem_center_fullCommAlg N _).mpr Z.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **4p. dim Z(A′)（Mathlib の Subalgebra.center）** = Σ_{c ∣ N, m(c) > 0} Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)。 -/
theorem finrank_center_fullCommAlg (N : ℕ) [NeZero N] :
    Module.finrank ℂ (Subalgebra.center ℂ (fullCommAlg N)) =
      ∑ c ∈ N.divisors.filter (fun c => 0 < Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive}),
        ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1) :=
  (centerLinearEquiv N).finrank_eq.trans (finrank_fullCommCenter N)

end PAG.Part226

#print axioms PAG.Part226.blockHom_exists_mul
#print axioms PAG.Part226.blockProj_fullComm_eq_zero
#print axioms PAG.Part226.commBlock_exists_mul
#print axioms PAG.Part226.fullComm_exists_mul
#print axioms PAG.Part226.centralElt
#print axioms PAG.Part226.centralElt_apply
#print axioms PAG.Part226.centralElt_apply_of_mem
#print axioms PAG.Part226.centralElt_apply_of_mem'
#print axioms PAG.Part226.centralElt_mem_fullComm
#print axioms PAG.Part226.centralElt_apply_fullComm
#print axioms PAG.Part226.centralElt_commute
#print axioms PAG.Part226.fullCommCenter
#print axioms PAG.Part226.mem_fullCommCenter
#print axioms PAG.Part226.centralElt_mem_center
#print axioms PAG.Part226.center_preserves
#print axioms PAG.Part226.layerScalar
#print axioms PAG.Part226.center_smul_layerPart
#print axioms PAG.Part226.layerScalar_eq_of_center
#print axioms PAG.Part226.centerIdx
#print axioms PAG.Part226.mem_centerIdx
#print axioms PAG.Part226.sum_centralElt_apply
#print axioms PAG.Part226.center_eq_zero
#print axioms PAG.Part226.centralElt_linearIndependent
#print axioms PAG.Part226.centerCoef
#print axioms PAG.Part226.center_eq_sum
#print axioms PAG.Part226.center_eq_span
#print axioms PAG.Part226.finrank_fullCommCenter
#print axioms PAG.Part226.fullComm_mul_mem
#print axioms PAG.Part226.one_mem_fullComm
#print axioms PAG.Part226.fullCommAlg
#print axioms PAG.Part226.mem_fullCommAlg
#print axioms PAG.Part226.center_mul_mem
#print axioms PAG.Part226.one_mem_center
#print axioms PAG.Part226.centerAlg
#print axioms PAG.Part226.mem_centerAlg
#print axioms PAG.Part226.mem_center_fullCommAlg
#print axioms PAG.Part226.centralElt_apply_layer
#print axioms PAG.Part226.centralElt_mul
#print axioms PAG.Part226.sum_centralElt
#print axioms PAG.Part226.sum_smul_centralElt_mem
#print axioms PAG.Part226.centerAlgHom
#print axioms PAG.Part226.centerAlgHom_apply
#print axioms PAG.Part226.centerAlgHom_bijective
#print axioms PAG.Part226.centerAlgEquiv
#print axioms PAG.Part226.centerMathlibEquiv
#print axioms PAG.Part226.centerEquivPi
#print axioms PAG.Part226.centerLinearEquiv
#print axioms PAG.Part226.finrank_center_fullCommAlg
