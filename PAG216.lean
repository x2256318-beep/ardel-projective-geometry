/-
  PAG 2.0 Part 212（2026-10-25）— 殻とブロックの同時分解
  ブロック (c, χ)（χ は法 c の原始指標）、L = N/c。v, w は L の約数
  G_v = g_{N/(vc), χ̄′}（Part 210 の gblock）、P = P_{c,χ}（Part 211 の blockProj）、ε_s ⋆（Part 201 の殻の射影）
  0. G_v は直交：⟨G_v, G_w⟩ = [v = w]·φ(vc)/N。ε_s ⋆ G_v = [s = N/(vc)]·G_v。ε_s ⋆ は自己共役で線形
  1. ブロックへの射影の G_v による式：P f = Σ_{v ∣ L} (N/φ(vc))·⟨G_v, f⟩·G_v（G⁻¹ を使わない）
  2. 可換性：ε_s ⋆ (P f) = P (ε_s ⋆ f)。殻の成分 ε_{N/(vc)} ⋆ P f = (N/φ(vc))·⟨G_v, f⟩·G_v、それ以外の殻では 0
  3. 共通部分：ε_s ⋆ f = f かつ P f = f なら、s = N/(vc)（v ∣ L）のとき f = (N/φ(vc))·⟨G_v, f⟩·G_v、それ以外は f = 0。
     P G_v = G_v、ほかのブロックの射影では 0
  4. 同時分解：f = Σ_{(c, χ)} Σ_{v ∣ N/c} (N/φ(vc))·⟨G_v, f⟩·G_v
-/
import PAG215

namespace PAG.Part216

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

/-- **0a.** v ∣ N/c（c ∣ N）なら N/(vc)·(vc) = N。 -/
theorem gblock_shell {N c v : ℕ} (hcN : c ∣ N) (hv : v ∣ N / c) : N / (v * c) * (v * c) = N := by
  have hvc : v * c ∣ N := by
    have := (Nat.dvd_div_iff_mul_dvd hcN).mp hv
    rwa [mul_comm] at this
  exact Nat.div_mul_cancel hvc

/-- **0b.** v, w ∣ N/c で N/(vc) = N/(wc) なら v = w。 -/
theorem gblock_shell_inj {N c v w : ℕ} [NeZero N] (hc : 0 < c) (hcN : c ∣ N) (hv : v ∣ N / c)
    (hw : w ∣ N / c) (e : N / (v * c) = N / (w * c)) : v = w := by
  have h1 := gblock_shell hcN hv
  have h2 := gblock_shell hcN hw
  rw [e] at h1
  have hpos : 0 < N / (w * c) :=
    Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at h2; exact NeZero.ne N h2.symm)
  exact Nat.eq_of_mul_eq_mul_right hc (Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm))

/-- **0c. G_v は直交**：⟨G_v, G_w⟩ = [v = w]·φ(vc)/N（v, w ∣ N/c）。 -/
theorem inner_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {v w : ℕ} (hv : v ∣ N / c) (hw : w ∣ N / c) :
    ∑ x, starRingEnd ℂ (gblock N c χ v x) * gblock N c χ w x =
      if v = w then (Nat.totient (v * c) : ℂ) / N else 0 := by
  by_cases hvw : v = w
  · subst hvw
    rw [ite_eq_left rfl]
    exact inner_gbas_self (N / (v * c)) (v * c) N (gblock_shell hcN hv) _
  · rw [ite_eq_right hvw]
    exact inner_gbas_ne (N / (v * c)) (v * c) (N / (w * c)) (w * c) N (gblock_shell hcN hv)
      (gblock_shell hcN hw) (fun e => hvw (gblock_shell_inj (Nat.pos_of_ne_zero (NeZero.ne c)) hcN hv hw e)) _ _

/-- **0d.** ε_s ⋆ G_v = [s = N/(vc)]·G_v。 -/
theorem geps_conv_gblock (N c : ℕ) [NeZero N] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) {v : ℕ}
    (hv : v ∣ N / c) (s : ℕ) :
    PAG.Part15.conv (geps N s) (gblock N c χ v) = if s = N / (v * c) then gblock N c χ v else 0 := by
  have h := gblock_shell hcN hv
  split_ifs with hs
  · subst hs
    exact geps_conv_gbas (N / (v * c)) (v * c) N h _
  · apply (ZMod.dft (N := N) (E := ℂ)).injective
    rw [PAG.Part16.dft_conv, dft_geps, map_zero]
    unfold gblock
    rw [← dind_mul_dft_gbas (N / (v * c)) (v * c) N h, ← mul_assoc, dind_mul, ite_eq_right hs, zero_mul]

/-- **0e.** ε_s ⋆ は自己共役：⟨ε_s ⋆ f, g⟩ = ⟨f, ε_s ⋆ g⟩。 -/
theorem inner_geps_conv_comm (N s : ℕ) [NeZero N] (f g : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (PAG.Part15.conv (geps N s) f x) * g x =
      ∑ x, starRingEnd ℂ (f x) * PAG.Part15.conv (geps N s) g x := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have P1 := PAG.Part39.plancherel (PAG.Part15.conv (geps N s) f) g
  have P2 := PAG.Part39.plancherel f (PAG.Part15.conv (geps N s) g)
  apply mul_left_cancel₀ hN
  rw [← P1, ← P2]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [PAG.Part16.dft_conv, PAG.Part16.dft_conv, Pi.mul_apply, Pi.mul_apply, dft_geps]
  simp only [dind]
  split_ifs <;> simp

/-- **0f.** ⟨G_v, ε_s ⋆ f⟩ = [s = N/(vc)]·⟨G_v, f⟩。 -/
theorem inner_gblock_geps_conv (N c : ℕ) [NeZero N] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) {v : ℕ}
    (hv : v ∣ N / c) (s : ℕ) (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (gblock N c χ v x) * PAG.Part15.conv (geps N s) f x =
      if s = N / (v * c) then ∑ x, starRingEnd ℂ (gblock N c χ v x) * f x else 0 := by
  rw [← inner_geps_conv_comm N s (gblock N c χ v) f, geps_conv_gblock N c hcN χ hv s]
  split_ifs <;> simp

/-- **0g.** 畳み込みは線形：h ⋆ Σ_v a_v·F_v = Σ_v a_v·(h ⋆ F_v)。 -/
theorem conv_sum_smul {N : ℕ} [NeZero N] (h : ZMod N → ℂ) {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    (F : ι → ZMod N → ℂ) :
    PAG.Part15.conv h (∑ v ∈ S, a v • F v) = ∑ v ∈ S, a v • PAG.Part15.conv h (F v) := by
  rw [← PAG.Part15.convL_apply, map_sum]
  simp only [map_smul, PAG.Part15.convL_apply]

/-- **0h.** ケットの番号 j は、ブロック (c, χ) の番号 w のケットか、ほかのブロックのもの。 -/
theorem ketIdx_cases (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) (j : KetIdx N) :
    (∃ w : (N / c).divisors, ketFam N j = kblock N c χ w) ∨ ketClass j ≠ ⟨c, χ⟩ := by
  obtain ⟨⟨u', hu'⟩, ⟨c', hc'⟩, ⟨χ', hχ'⟩⟩ := j
  by_cases hcc : c = c'
  · subst hcc
    by_cases hχχ : χ = χ'
    · subst hχχ
      left
      have hu'L : u' ∈ (N / c).divisors := ((mem_block_iff N u' c (NeZero.ne N)).mp ⟨hu', hc'⟩).2
      exact ⟨⟨u', hu'L⟩, (kblock_of_dvd N c χ (Nat.dvd_of_mem_divisors hu') (Nat.dvd_of_mem_divisors hc')).symm⟩
    · right
      intro hcl
      exact hχχ (eq_of_heq (Sigma.mk.inj_iff.mp hcl).2).symm
  · right
    intro hcl
    exact hcc (congrArg Sigma.fst hcl).symm

/-! ### 1. ブロックへの射影の G_v による式 -/

/-- ブロック (c, χ) への射影の G_v による形：Σ_{v ∣ N/c} (N/φ(vc))·⟨G_v, f⟩·G_v。 -/
noncomputable def blockProjG (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (f : ZMod N → ℂ) : ZMod N → ℂ :=
  ∑ v ∈ (N / c).divisors,
    ((N : ℂ) / (Nat.totient (v * c) : ℂ) * ∑ x, starRingEnd ℂ (gblock N c χ v x) * f x) • gblock N c χ v

/-- **1a.** ⟨G_w, Σ_v (N/φ(vc))⟨G_v, f⟩G_v⟩ = ⟨G_w, f⟩（w ∣ N/c）。 -/
theorem inner_gblock_blockProjG (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {w : ℕ} (hw : w ∣ N / c) (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (gblock N c χ w x) * blockProjG N c χ f x =
      ∑ x, starRingEnd ℂ (gblock N c χ w x) * f x := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  have hφ : (Nat.totient (w * c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (Nat.pos_of_dvd_of_pos hw (Nat.pos_of_ne_zero hL0))
      (Nat.pos_of_ne_zero (NeZero.ne c)))).ne'
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold blockProjG
  rw [inner_sum_smul_right, Finset.sum_eq_single w]
  · rw [inner_gblock N c hcN χ hw hw, ite_eq_left rfl]
    field_simp
  · intro v hv hvw
    rw [inner_gblock N c hcN χ hw (Nat.dvd_of_mem_divisors hv), ite_eq_right (Ne.symm hvw), mul_zero]
  · intro h
    exact absurd (Nat.mem_divisors.mpr ⟨hw, hL0⟩) h

/-- **1b.** ほかのブロックのケットは G_v と直交：ketClass j ≠ (c, χ) なら ⟨k_j, G_v⟩ = 0。 -/
theorem inner_ketFam_gblock_of_ne (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {v : ℕ} (hv : v ∣ N / c) (j : KetIdx N) (hne : ketClass j ≠ ⟨c, χ⟩) :
    ∑ x, starRingEnd ℂ (ketFam N j x) * gblock N c χ v x = 0 := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  rw [gblock_eq_sum N c hcN χ hχ v hv, inner_sum_smul_right]
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have hwL : w ∈ (N / c).divisors := Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_of_mem_divisors hw) hv, hL0⟩
  rw [show kblock N c χ w = kblock N c χ ((⟨w, hwL⟩ : (N / c).divisors) : ℕ) from rfl,
    ← ketFam_blockIdx N c hcN χ hχ ⟨w, hwL⟩,
    inner_ketFam_of_ketClass_ne N j (blockIdx N c hcN χ hχ ⟨w, hwL⟩) hne, mul_zero]

/-- **1c.** ほかのブロックのケットとは Σ_v (N/φ(vc))⟨G_v, f⟩G_v も直交。 -/
theorem inner_ketFam_blockProjG_of_ne (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) (j : KetIdx N)
    (hne : ketClass j ≠ ⟨c, χ⟩) :
    ∑ x, starRingEnd ℂ (ketFam N j x) * blockProjG N c χ f x = 0 := by
  unfold blockProjG
  rw [inner_sum_smul_right]
  refine Finset.sum_eq_zero (fun v hv => ?_)
  rw [inner_ketFam_gblock_of_ne N c hcN χ hχ (Nat.dvd_of_mem_divisors hv) j hne, mul_zero]

/-- **1d.** 同じブロックのケットについて ⟨k_w, Σ_v (N/φ(vc))⟨G_v, f⟩G_v⟩ = ⟨k_w, f⟩。 -/
theorem inner_kblock_blockProjG (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (w : (N / c).divisors) (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (kblock N c χ w x) * blockProjG N c χ f x =
      ∑ x, starRingEnd ℂ (kblock N c χ w x) * f x := by
  rw [kblock_eq_sum N c hcN χ hχ w (Nat.dvd_of_mem_divisors w.2), Finset.smul_sum]
  simp only [smul_smul]
  rw [inner_sum_smul_left, inner_sum_smul_left]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [inner_gblock_blockProjG N c hcN χ (dvd_trans (Nat.dvd_of_mem_divisors hv) (Nat.dvd_of_mem_divisors w.2)) f]

/-- **1e. ブロックへの射影の G_v による式**：P f = Σ_{v ∣ N/c} (N/φ(vc))·⟨G_v, f⟩·G_v（χ 原始的）。 -/
theorem blockProj_eq_blockProjG (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) : blockProj N c χ f = blockProjG N c χ f := by
  apply eq_of_inner_ketFam_eq N
  intro j
  rw [inner_conj_symm (blockProj N c χ f) (ketFam N j), inner_conj_symm (blockProjG N c χ f) (ketFam N j)]
  congr 1
  rcases ketIdx_cases N c χ j with ⟨w, hw⟩ | hne
  · rw [hw, inner_kblock_blockProj N c hcN χ hχ w f, inner_kblock_blockProjG N c hcN χ hχ w f]
  · rw [inner_ketFam_blockProj_of_ne N c hcN χ hχ f j hne, inner_ketFam_blockProjG_of_ne N c hcN χ hχ f j hne]

/-! ### 2. 殻とブロックの可換性 -/

/-- **2a. 可換性**：ε_s ⋆ (P f) = P (ε_s ⋆ f)。 -/
theorem geps_conv_blockProj (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (s : ℕ) (f : ZMod N → ℂ) :
    PAG.Part15.conv (geps N s) (blockProj N c χ f) = blockProj N c χ (PAG.Part15.conv (geps N s) f) := by
  rw [blockProj_eq_blockProjG N c hcN χ hχ, blockProj_eq_blockProjG N c hcN χ hχ]
  unfold blockProjG
  rw [conv_sum_smul]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [geps_conv_gblock N c hcN χ (Nat.dvd_of_mem_divisors hv) s,
    inner_gblock_geps_conv N c hcN χ (Nat.dvd_of_mem_divisors hv) s f]
  split_ifs <;> simp

/-- **2b. 殻の成分**：v ∣ N/c なら ε_{N/(vc)} ⋆ P f = (N/φ(vc))·⟨G_v, f⟩·G_v。 -/
theorem geps_conv_blockProj_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {v : ℕ} (hv : v ∣ N / c) (f : ZMod N → ℂ) :
    PAG.Part15.conv (geps N (N / (v * c))) (blockProj N c χ f) =
      ((N : ℂ) / (Nat.totient (v * c) : ℂ) * ∑ x, starRingEnd ℂ (gblock N c χ v x) * f x) • gblock N c χ v := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  rw [blockProj_eq_blockProjG N c hcN χ hχ]
  unfold blockProjG
  rw [conv_sum_smul, Finset.sum_eq_single v]
  · rw [geps_conv_gblock N c hcN χ hv, ite_eq_left rfl]
  · intro w hw hwv
    have hne : N / (v * c) ≠ N / (w * c) := fun e =>
      hwv (gblock_shell_inj (Nat.pos_of_ne_zero (NeZero.ne c)) hcN hv (Nat.dvd_of_mem_divisors hw) e).symm
    rw [geps_conv_gblock N c hcN χ (Nat.dvd_of_mem_divisors hw), ite_eq_right hne, smul_zero]
  · intro h
    exact absurd (Nat.mem_divisors.mpr ⟨hv, hL0⟩) h

/-- **2c.** v ∣ N/c の形でない殻 s では ε_s ⋆ P f = 0。 -/
theorem geps_conv_blockProj_eq_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (s : ℕ)
    (hs : ∀ v ∈ (N / c).divisors, s ≠ N / (v * c)) (f : ZMod N → ℂ) :
    PAG.Part15.conv (geps N s) (blockProj N c χ f) = 0 := by
  rw [blockProj_eq_blockProjG N c hcN χ hχ]
  unfold blockProjG
  rw [conv_sum_smul]
  refine Finset.sum_eq_zero (fun v hv => ?_)
  rw [geps_conv_gblock N c hcN χ (Nat.dvd_of_mem_divisors hv) s, ite_eq_right (hs v hv), smul_zero]

/-! ### 3. 殻とブロックの共通部分 -/

/-- **3a. 共通部分**：ε_{N/(vc)} ⋆ f = f かつ P f = f（v ∣ N/c）なら f = (N/φ(vc))·⟨G_v, f⟩·G_v。 -/
theorem eq_smul_gblock_of_mem (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {v : ℕ} (hv : v ∣ N / c) (f : ZMod N → ℂ)
    (hs : PAG.Part15.conv (geps N (N / (v * c))) f = f) (hP : blockProj N c χ f = f) :
    f = ((N : ℂ) / (Nat.totient (v * c) : ℂ) * ∑ x, starRingEnd ℂ (gblock N c χ v x) * f x) • gblock N c χ v :=
  calc f = PAG.Part15.conv (geps N (N / (v * c))) f := hs.symm
    _ = PAG.Part15.conv (geps N (N / (v * c))) (blockProj N c χ f) := by rw [hP]
    _ = _ := geps_conv_blockProj_gblock N c hcN χ hχ hv f

/-- **3b.** v ∣ N/c の形でない殻 s では、ε_s ⋆ f = f かつ P f = f なら f = 0。 -/
theorem eq_zero_of_mem (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (s : ℕ) (hs : ∀ v ∈ (N / c).divisors, s ≠ N / (v * c)) (f : ZMod N → ℂ)
    (hfs : PAG.Part15.conv (geps N s) f = f) (hP : blockProj N c χ f = f) : f = 0 :=
  calc f = PAG.Part15.conv (geps N s) f := hfs.symm
    _ = PAG.Part15.conv (geps N s) (blockProj N c χ f) := by rw [hP]
    _ = 0 := geps_conv_blockProj_eq_zero N c hcN χ hχ s hs f

/-- **3c.** G_v はブロックの射影で動かない：P G_v = G_v。 -/
theorem blockProj_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {v : ℕ} (hv : v ∣ N / c) : blockProj N c χ (gblock N c χ v) = gblock N c χ v := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  have hφ : (Nat.totient (v * c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (Nat.pos_of_dvd_of_pos hv (Nat.pos_of_ne_zero hL0))
      (Nat.pos_of_ne_zero (NeZero.ne c)))).ne'
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [blockProj_eq_blockProjG N c hcN χ hχ]
  unfold blockProjG
  rw [Finset.sum_eq_single v]
  · rw [inner_gblock N c hcN χ hv hv, ite_eq_left rfl]
    have e : (N : ℂ) / (Nat.totient (v * c) : ℂ) * ((Nat.totient (v * c) : ℂ) / N) = 1 := by
      field_simp
    rw [e, one_smul]
  · intro w hw hwv
    rw [inner_gblock N c hcN χ (Nat.dvd_of_mem_divisors hw) hv, ite_eq_right hwv, mul_zero, zero_smul]
  · intro h
    exact absurd (Nat.mem_divisors.mpr ⟨hv, hL0⟩) h

/-- **3d.** ほかのブロックの射影で G_v は 0：(c′, χ′) ≠ (c, χ) なら P_{c′,χ′} G_v = 0。 -/
theorem blockProj_gblock_of_ne (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    (hne : (⟨c', χ'⟩ : Σ c : ℕ, DirichletCharacter ℂ c) ≠ ⟨c, χ⟩) {v : ℕ} (hv : v ∣ N / c) :
    blockProj N c' χ' (gblock N c χ v) = 0 := by
  have h0 : ∀ u' : (N / c').divisors,
      ∑ x, starRingEnd ℂ (kblock N c' χ' u' x) * gblock N c χ v x = 0 := by
    intro u'
    rw [← ketFam_blockIdx N c' hc'N χ' hχ' u']
    exact inner_ketFam_gblock_of_ne N c hcN χ hχ hv _ hne
  unfold blockProj
  refine Finset.sum_eq_zero (fun u _ => ?_)
  rw [kdual_eq_kdualB N c' hc'N χ' hχ' u]
  unfold kdualB
  rw [inner_sum_smul_left]
  simp only [h0, mul_zero, Finset.sum_const_zero, zero_smul]

/-! ### 4. 殻とブロックの同時分解 -/

/-- 番号 b = (c, χ) のブロックへの射影の G_v による形。 -/
noncomputable def blockProjGI (N : ℕ) [NeZero N] (b : BlockIdx N) (f : ZMod N → ℂ) : ZMod N → ℂ :=
  blockProjG N b.1 b.2.1 f

/-- **4a. 同時分解**：f = Σ_{(c, χ)} Σ_{v ∣ N/c} (N/φ(vc))·⟨G_v, f⟩·G_v（ブロックの番号の Fintype はどれでもよい）。 -/
theorem sum_blockProjGI (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (f : ZMod N → ℂ) :
    f = ∑ b : BlockIdx N, blockProjGI N b f := by
  conv_lhs => rw [sum_blockProjI N f]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have : NeZero (b.1 : ℕ) := ⟨(Nat.pos_of_mem_divisors b.1.2).ne'⟩
  exact blockProj_eq_blockProjG N b.1 (Nat.dvd_of_mem_divisors b.1.2) b.2.1 b.2.2 f

end PAG.Part216

#print axioms PAG.Part216.gblock_shell
#print axioms PAG.Part216.gblock_shell_inj
#print axioms PAG.Part216.inner_gblock
#print axioms PAG.Part216.geps_conv_gblock
#print axioms PAG.Part216.inner_geps_conv_comm
#print axioms PAG.Part216.inner_gblock_geps_conv
#print axioms PAG.Part216.conv_sum_smul
#print axioms PAG.Part216.ketIdx_cases
#print axioms PAG.Part216.blockProjG
#print axioms PAG.Part216.inner_gblock_blockProjG
#print axioms PAG.Part216.inner_ketFam_gblock_of_ne
#print axioms PAG.Part216.inner_ketFam_blockProjG_of_ne
#print axioms PAG.Part216.inner_kblock_blockProjG
#print axioms PAG.Part216.blockProj_eq_blockProjG
#print axioms PAG.Part216.geps_conv_blockProj
#print axioms PAG.Part216.geps_conv_blockProj_gblock
#print axioms PAG.Part216.geps_conv_blockProj_eq_zero
#print axioms PAG.Part216.eq_smul_gblock_of_mem
#print axioms PAG.Part216.eq_zero_of_mem
#print axioms PAG.Part216.blockProj_gblock
#print axioms PAG.Part216.blockProj_gblock_of_ne
#print axioms PAG.Part216.blockProjGI
#print axioms PAG.Part216.sum_blockProjGI
