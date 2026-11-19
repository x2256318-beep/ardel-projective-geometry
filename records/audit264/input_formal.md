# 入力：PAG264.lean の形式文の全文（docstring・コメントを除いた）と、使う定義

## A. PAG264.lean（形式文）
```lean
import PAG263

open Complex Finset

namespace PAG.Part264

open PAG.Part201 PAG.Part205 PAG.Part206 PAG.Part218 PAG.Part232

section general

variable {N M : ℕ} [NeZero N] [NeZero M]

noncomputable def fsum (h : N ∣ M) (g : ZMod M → ℂ) : ZMod N → ℂ :=
  fun x => ∑ y ∈ univ.filter (fun y : ZMod M => ZMod.castHom h (ZMod N) y = x), g y

omit [NeZero N] in
theorem fsum_add (h : N ∣ M) (g g' : ZMod M → ℂ) : fsum h (g + g') = fsum h g + fsum h g' := by
  funext x; simp only [fsum, Pi.add_apply, sum_add_distrib]

omit [NeZero N] in
theorem fsum_smul (h : N ∣ M) (c : ℂ) (g : ZMod M → ℂ) : fsum h (c • g) = c • fsum h g := by
  funext x; simp only [fsum, Pi.smul_apply, smul_eq_mul, mul_sum]

noncomputable def pullLin (h : N ∣ M) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod M → ℂ) where
  toFun := pull h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def fsumLin (h : N ∣ M) : (ZMod M → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun := fsum h
  map_add' := fsum_add h
  map_smul' := fsum_smul h

theorem card_fiber (h : N ∣ M) (x : ZMod N) :
    ((univ.filter (fun y : ZMod M => ZMod.castHom h (ZMod N) y = x)).card : ℂ) = (M : ℂ) / N := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  obtain ⟨y0, hy0⟩ := ZMod.ringHom_surjective (ZMod.castHom h (ZMod N)) x
  have e : univ.filter (fun y : ZMod M => ZMod.castHom h (ZMod N) y = x) =
      (univ.filter (fun z : ZMod M => (ZMod.castHom h (ZMod N)).toAddMonoidHom z = 0)).map
        (addRightEmbedding y0) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_map, addRightEmbedding_apply,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    constructor
    · intro hy
      exact ⟨y - y0, by rw [map_sub, hy, hy0, sub_self], sub_add_cancel y y0⟩
    · rintro ⟨z, hz, rfl⟩
      rw [map_add, hz, zero_add, hy0]
  rw [e, card_map, eq_div_iff hN]
  exact card_ker_cast h

theorem fsum_pull (h : N ∣ M) (f : ZMod N → ℂ) : fsum h (pull h f) = ((M : ℂ) / N) • f := by
  funext x
  simp only [fsum, pull_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_congr rfl (fun y hy => by rw [(mem_filter.mp hy).2]), sum_const, nsmul_eq_mul, card_fiber]

noncomputable def cornerOp (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) : Module.End ℂ (ZMod M → ℂ) :=
  ((N : ℂ) / M) • (pullLin h ∘ₗ S ∘ₗ fsumLin h)

omit [NeZero N] in
theorem cornerOp_apply (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) (g : ZMod M → ℂ) :
    cornerOp h S g = ((N : ℂ) / M) • pull h (S (fsum h g)) := rfl

theorem scal_cancel (N M : ℕ) [NeZero N] [NeZero M] : ((N : ℂ) / M) * ((M : ℂ) / N) = 1 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  field_simp

theorem cornerOp_pull (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) (f : ZMod N → ℂ) :
    cornerOp h S (pull h f) = pull h (S f) := by
  rw [cornerOp_apply, fsum_pull, map_smul, pull_smul, smul_smul, scal_cancel, one_smul]

theorem cornerOp_mul (h : N ∣ M) (S T : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h (S * T) = cornerOp h S * cornerOp h T := by
  apply LinearMap.ext; intro g
  rw [Module.End.mul_apply, cornerOp_apply, cornerOp_apply, cornerOp_apply, fsum_smul, fsum_pull,
    smul_smul, scal_cancel, one_smul, Module.End.mul_apply]

omit [NeZero N] in
theorem cornerOp_add (h : N ∣ M) (S T : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h (S + T) = cornerOp h S + cornerOp h T := by
  apply LinearMap.ext; intro g
  rw [LinearMap.add_apply, cornerOp_apply, cornerOp_apply, cornerOp_apply, LinearMap.add_apply]
  funext y
  simp only [pull_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add]

omit [NeZero N] in
theorem cornerOp_smul (h : N ∣ M) (c : ℂ) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h (c • S) = c • cornerOp h S := by
  apply LinearMap.ext; intro g
  rw [LinearMap.smul_apply, cornerOp_apply, cornerOp_apply, LinearMap.smul_apply, pull_smul, smul_comm]

omit [NeZero N] in
theorem cornerOp_zero (h : N ∣ M) : cornerOp h 0 = 0 := by
  simpa using cornerOp_smul h 0 0

theorem cornerOp_one_mul (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h 1 * cornerOp h S = cornerOp h S := by
  rw [← cornerOp_mul, one_mul]

theorem cornerOp_mul_one (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h S * cornerOp h 1 = cornerOp h S := by
  rw [← cornerOp_mul, mul_one]

theorem cornerOp_injective (h : N ∣ M) : Function.Injective (cornerOp h) := by
  intro S T hST
  apply LinearMap.ext; intro f
  have e := congrArg (fun X : Module.End ℂ (ZMod M → ℂ) => X (pull h f)) hST
  simp only [cornerOp_pull] at e
  exact PAG.Part263.pull_injective' h e

omit [NeZero N] in
theorem fsum_single (h : N ∣ M) (y0 : ZMod M) (c : ℂ) (x : ZMod N) :
    fsum h (Pi.single y0 c) x = if ZMod.castHom h (ZMod N) y0 = x then c else 0 := by
  simp only [fsum]
  rw [sum_pi_single']
  simp only [mem_filter, mem_univ, true_and]

omit [NeZero N] in
theorem cornerOp_one_single (h : N ∣ M) :
    cornerOp h 1 (Pi.single 0 1) 0 = (N : ℂ) / M := by
  rw [cornerOp_apply, Pi.smul_apply, pull_apply, Module.End.one_apply, fsum_single, map_zero,
    ite_eq_left rfl, smul_eq_mul, mul_one]

omit [NeZero N] in
theorem cornerOp_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerOp h 1 ≠ 1 := by
  intro e
  have e2 := cornerOp_one_single h
  rw [e, Module.End.one_apply, Pi.single_eq_same] at e2
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  rw [eq_div_iff hM, one_mul] at e2
  exact absurd (Nat.cast_injective e2) (Nat.ne_of_lt hlt).symm

end general

section gens

variable {N t : ℕ} [NeZero N] [NeZero t]

theorem pull_fsum (g : ZMod (N * t) → ℂ) :
    pull (dvd_mul_right N t) (fsum (dvd_mul_right N t) g) = (t : ℂ) • oldP N t g := by
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  funext x
  rw [pull_apply, Pi.smul_apply, oldP, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ ht, one_mul]
  have hre : (∑ y : ZMod (N * t), PAG.Part203.rk (N := N * t) N 1 (fun _ => (1 : ℂ)) y * g (x - y)) =
      ∑ z : ZMod (N * t), PAG.Part203.rk (N := N * t) N 1 (fun _ => (1 : ℂ)) (x - z) * g z :=
    (Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun z => by simp [Equiv.subLeft_apply])).symm
  simp only [PAG.Part15.conv]
  rw [hre, fsum, sum_filter]
  refine sum_congr rfl (fun z _ => ?_)
  have key : N ∣ (x - z).val ↔ ZMod.castHom (dvd_mul_right N t) (ZMod N) z =
      ZMod.castHom (dvd_mul_right N t) (ZMod N) x := by
    rw [← ZMod.natCast_eq_zero_iff, ← ZMod.cast_eq_val, ← ZMod.castHom_apply (h := dvd_mul_right N t),
      map_sub, sub_eq_zero, eq_comm]
  simp only [PAG.Part203.rk]
  by_cases hz : N ∣ (x - z).val
  · rw [ite_eq_left hz, ite_eq_left (key.mp hz), one_mul]
  · rw [ite_eq_right hz, ite_eq_right (fun e => hz (key.mpr e)), zero_mul]

theorem cornerOp_one_apply (g : ZMod (N * t) → ℂ) :
    cornerOp (dvd_mul_right N t) 1 g = oldP N t g := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  rw [cornerOp_apply, Module.End.one_apply, pull_fsum, smul_smul]
  have : (N : ℂ) / ((N * t : ℕ) : ℂ) * t = 1 := by push_cast; field_simp
  rw [this, one_smul]

theorem conv_geps_oldP (s : ℕ) (g : ZMod (N * t) → ℂ) :
    PAG.Part15.conv (geps (N * t) (t * s)) (oldP N t g) = PAG.Part15.conv (geps (N * t) (t * s)) g := by
  apply (ZMod.dft (N := N * t) (E := ℂ)).injective
  funext ξ
  rw [PAG.Part16.dft_conv, PAG.Part16.dft_conv, Pi.mul_apply, Pi.mul_apply, dft_oldP]
  by_cases htξ : t ∣ ξ.val
  · rw [ite_eq_left htξ]
  · rw [ite_eq_right htξ, dft_geps]
    have hd : dind (N * t) (t * s) ξ = 0 := by
      simp only [dind]
      rw [ite_eq_right (fun h => htξ ((dvd_mul_right t s).trans
        (by rw [← h]; exact Nat.gcd_dvd_right (N * t) ξ.val)))]
    rw [hd, zero_mul, zero_mul]

theorem cornerOp_geps_mul (s : ℕ) :
    cornerOp (dvd_mul_right N t) (PAG.Part15.convL (geps N s)) =
      PAG.Part15.convL (geps (N * t) (t * s)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  apply LinearMap.ext; intro g
  rw [cornerOp_apply]
  show ((N : ℂ) / ((N * t : ℕ) : ℂ)) • pull (dvd_mul_right N t)
      (PAG.Part15.conv (geps N s) (fsum (dvd_mul_right N t) g)) = PAG.Part15.conv (geps (N * t) (t * s)) g
  rw [← geps_conv_pull, pull_fsum]
  have hcs : PAG.Part15.conv (geps (N * t) (t * s)) ((t : ℂ) • oldP N t g) =
      (t : ℂ) • PAG.Part15.conv (geps (N * t) (t * s)) (oldP N t g) := by
    rw [PAG.Part15.conv_comm, conv_smul_left, PAG.Part15.conv_comm]
  rw [hcs, conv_geps_oldP, smul_smul]
  have : (N : ℂ) / ((N * t : ℕ) : ℂ) * t = 1 := by push_cast; field_simp
  rw [this, one_smul]

end gens

section mem

variable {N M : ℕ} [NeZero N] [NeZero M]

theorem cornerOp_one (h : N ∣ M) :
    cornerOp h 1 = ∑ s ∈ M.divisors.filter (fun s => M / N ∣ s), PAG.Part15.convL (geps M s) := by
  obtain ⟨t, rfl⟩ := h
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have : NeZero t := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
  rw [Nat.mul_div_cancel_left t hN0]
  apply LinearMap.ext; intro g
  rw [cornerOp_one_apply, oldP_eq_sum, LinearMap.sum_apply]
  rfl

theorem cornerOp_geps (h : N ∣ M) (s : ℕ) :
    cornerOp h (PAG.Part15.convL (geps N s)) = PAG.Part15.convL (geps M (M / N * s)) := by
  obtain ⟨t, rfl⟩ := h
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have : NeZero t := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
  rw [Nat.mul_div_cancel_left t hN0]
  exact cornerOp_geps_mul s

omit [NeZero N] in
theorem pull_dind (h : N ∣ M) (s : ℕ) :
    pull h (dind N s) = ∑ u ∈ M.divisors.filter (fun u => Nat.gcd u N = s), dind M u := by
  funext y
  rw [pull_apply, Finset.sum_apply]
  simp only [dind]
  rw [sum_ite_eq]
  have hg : Nat.gcd N (ZMod.castHom h (ZMod N) y).val = Nat.gcd (Nat.gcd M y.val) N := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, Nat.gcd_comm N, ← Nat.gcd_rec,
      Nat.gcd_comm N, Nat.gcd_comm M, Nat.gcd_assoc, Nat.gcd_eq_right h]
  have hmem : Nat.gcd M y.val ∈ M.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, NeZero.ne M⟩
  rw [hg]
  by_cases hs : Nat.gcd (Nat.gcd M y.val) N = s
  · rw [ite_eq_left hs, ite_eq_left (show Nat.gcd M y.val ∈ M.divisors.filter (fun u => Nat.gcd u N = s) from
      mem_filter.mpr ⟨hmem, hs⟩)]
  · rw [ite_eq_right hs, ite_eq_right (show Nat.gcd M y.val ∉ M.divisors.filter (fun u => Nat.gcd u N = s) from
      fun hm => hs (mem_filter.mp hm).2)]

omit [NeZero M] in
theorem mulLeft_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod M → ℂ) :
    LinearMap.mulLeft ℂ (∑ i ∈ s, f i) = ∑ i ∈ s, LinearMap.mulLeft ℂ (f i) := by
  apply LinearMap.ext; intro g
  rw [LinearMap.mulLeft_apply, LinearMap.sum_apply, Finset.sum_mul]
  rfl

omit [NeZero N] in
theorem mulLeft_pull_dind_mem (h : N ∣ M) (s : ℕ) :
    LinearMap.mulLeft ℂ (pull h (dind N s)) ∈ shellAlg M := by
  rw [pull_dind, mulLeft_sum]
  exact Subalgebra.sum_mem _ (fun u _ => mulLeft_dind_mem M u)

omit [NeZero N] in
theorem cornerOp_dind (h : N ∣ M) (s : ℕ) :
    cornerOp h (LinearMap.mulLeft ℂ (dind N s)) =
      LinearMap.mulLeft ℂ (pull h (dind N s)) * cornerOp h 1 := by
  apply LinearMap.ext; intro g
  rw [Module.End.mul_apply, cornerOp_apply, cornerOp_apply, Module.End.one_apply, LinearMap.mulLeft_apply,
    LinearMap.mulLeft_apply]
  funext y
  simp only [pull_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

theorem cornerOp_one_mem (h : N ∣ M) : cornerOp h 1 ∈ shellAlg M := by
  rw [cornerOp_one]
  exact Subalgebra.sum_mem _ (fun s _ => convL_geps_mem M s)

theorem cornerOp_mem (h : N ∣ M) {S : Module.End ℂ (ZMod N → ℂ)} (hS : S ∈ shellAlg N) :
    cornerOp h S ∈ shellAlg M := by
  unfold shellAlg at hS
  induction hS using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [cornerOp_geps]; exact convL_geps_mem M _
    · rw [cornerOp_dind]; exact Subalgebra.mul_mem _ (mulLeft_pull_dind_mem h s) (cornerOp_one_mem h)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, cornerOp_smul]
    exact Subalgebra.smul_mem _ (cornerOp_one_mem h) r
  | add x y _ _ hx hy => rw [cornerOp_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [cornerOp_mul]; exact Subalgebra.mul_mem _ hx hy

noncomputable def cornerHom (h : N ∣ M) : shellAlg N →ₙₐ[ℂ] shellAlg M where
  toFun S := ⟨cornerOp h S, cornerOp_mem h S.2⟩
  map_smul' c S := Subtype.ext (show cornerOp h (c • (S : Module.End ℂ (ZMod N → ℂ))) = c • cornerOp h S from
    cornerOp_smul h c S)
  map_zero' := Subtype.ext (cornerOp_zero h)
  map_add' S T := Subtype.ext (cornerOp_add h S T)
  map_mul' S T := Subtype.ext (cornerOp_mul h S T)

theorem cornerHom_coe (h : N ∣ M) (S : shellAlg N) :
    ((cornerHom h S : shellAlg M) : Module.End ℂ (ZMod M → ℂ)) = cornerOp h S := rfl

end mem

section uniq

variable {N M : ℕ} [NeZero N] [NeZero M]

theorem existsUnique_corner (h : N ∣ M) :
    ∃! φ : shellAlg N →ₙₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (pull h f) = pull h ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (φ 1 : Module.End ℂ (ZMod M → ℂ)) =
        ∑ s ∈ M.divisors.filter (fun s => M / N ∣ s), PAG.Part15.convL (geps M s) := by
  refine ⟨cornerHom h, ⟨fun S f => cornerOp_pull h S f, ?_⟩, ?_⟩
  · rw [← cornerOp_one]; rfl
  · rintro ψ ⟨hpull, hone⟩
    apply NonUnitalAlgHom.ext; intro S
    apply Subtype.ext
    apply LinearMap.ext; intro g
    have e1 : ψ S = ψ S * ψ 1 := by rw [← map_mul, mul_one]
    rw [cornerHom_coe, e1, Subalgebra.coe_mul, Module.End.mul_apply, hone, ← cornerOp_one,
      cornerOp_apply, Module.End.one_apply, ← pull_smul, hpull, map_smul, pull_smul, cornerOp_apply]

omit [NeZero N] in
theorem fsum_trans {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) (g : ZMod L → ℂ) :
    fsum (h1.trans h2) g = fsum h1 (fsum h2 g) := by
  funext x
  simp only [fsum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := ZMod.castHom h2 (ZMod M))
    (t := univ.filter (fun y : ZMod M => ZMod.castHom h1 (ZMod N) y = x))]
  · refine sum_congr rfl (fun y hy => ?_)
    apply sum_congr _ (fun _ _ => rfl)
    ext z
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    constructor
    · rintro ⟨_, hz⟩; exact hz
    · intro hz
      refine ⟨?_, hz⟩
      rw [← ZMod.castHom_comp h1 h2, RingHom.comp_apply, hz, hy]
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    rw [← RingHom.comp_apply, ZMod.castHom_comp h1 h2, hz]

omit [NeZero N] in
theorem cornerOp_comp {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h2 (cornerOp h1 S) = cornerOp (h1.trans h2) S := by
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  apply LinearMap.ext; intro g
  rw [cornerOp_apply, cornerOp_apply, cornerOp_apply, pull_smul, smul_smul, PAG.Part263.pull_pull h1 h2, fsum_trans h1 h2]
  congr 1
  field_simp

theorem cornerHom_comp {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) :
    (cornerHom h2).comp (cornerHom h1) = cornerHom (h1.trans h2) := by
  apply NonUnitalAlgHom.ext; intro S
  apply Subtype.ext
  exact cornerOp_comp h1 h2 S

theorem cornerHom_injective (h : N ∣ M) : Function.Injective (cornerHom h) :=
  fun _ _ hST => Subtype.ext (cornerOp_injective h (congrArg Subtype.val hST))

theorem cornerHom_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerHom h 1 ≠ 1 :=
  fun e => cornerOp_one_ne_one h hlt (congrArg Subtype.val e)

end uniq

theorem cornerOp_dind_not_mem_span :
    cornerOp (show 2 ∣ 4 by norm_num) (LinearMap.mulLeft ℂ (dind 2 2)) ∉
      Submodule.span ℂ (Set.range fun u : ℕ => LinearMap.mulLeft ℂ (dind 4 u)) := by
  intro hmem
  obtain ⟨m, hm⟩ := PAG.Part262.exists_mulLeft_of_mem_span 4 hmem
  have e : cornerOp (show 2 ∣ 4 by norm_num) (LinearMap.mulLeft ℂ (dind 2 2)) (Pi.single 0 1) 2 = 0 := by
    rw [hm, LinearMap.mulLeft_apply, Pi.mul_apply, Pi.single_eq_of_ne (by decide), mul_zero]
  rw [cornerOp_apply, Pi.smul_apply, pull_apply, LinearMap.mulLeft_apply, Pi.mul_apply, fsum_single] at e
  have hc : ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) (2 : ZMod 4) = 0 := by
    rw [map_ofNat]; rfl
  rw [hc, map_zero, ite_eq_left rfl] at e
  simp [dind] at e

end PAG.Part264
```

## B. 使う定義と、証明で使う前の鎖の補題の文（証明は省略）
```lean
-- PAG201（Part 197）
noncomputable def pull {N N' : ℕ} (h : N ∣ N') (f : ZMod N → ℂ) : ZMod N' → ℂ :=
  f ∘ (ZMod.castHom h (ZMod N)).toAddMonoidHom
theorem card_ker_cast {N N' : ℕ} [NeZero N] [NeZero N'] (h : N ∣ N') :
    ((Finset.univ.filter (fun z : ZMod N' => (ZMod.castHom h (ZMod N)).toAddMonoidHom z = 0)).card : ℂ)
      * N = N'
-- PAG15
def conv (f g : G → K) : G → K := fun x => ∑ y, f y * g (x - y)
def convL : (G → K) →ₗ[K] (G → K) →ₗ[K] (G → K) := LinearMap.mk₂ K conv ...   -- convL f g = conv f g
-- PAG203（Part 199）
noncomputable def rk {N : ℕ} (v d : ℕ) (Ψ : ZMod d → ℂ) : ZMod N → ℂ :=
  fun x => if v ∣ x.val then Ψ ((x.val / v : ℕ) : ZMod d) else 0
-- PAG205（Part 201）。𝓕 は Mathlib の ZMod.dft、𝓕⁻ はその逆
noncomputable def dind (N s : ℕ) : ZMod N → ℂ := fun ξ => if Nat.gcd N ξ.val = s then 1 else 0
noncomputable def geps (N s : ℕ) [NeZero N] : ZMod N → ℂ := 𝓕⁻ (dind N s)
-- PAG206（Part 202）
noncomputable def oldP (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod (N * t) → ℂ) : ZMod (N * t) → ℂ :=
  ((t : ℂ)⁻¹) • PAG.Part15.conv (rk (N := N * t) N 1 (fun _ => 1)) f
theorem oldP_eq_sum (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod (N * t) → ℂ) :
    oldP N t f = ∑ s ∈ (N * t).divisors.filter (fun s => t ∣ s), PAG.Part15.conv (geps (N * t) s) f
theorem geps_conv_pull (N t s : ℕ) [NeZero N] [NeZero t] (f : ZMod N → ℂ) :
    PAG.Part15.conv (geps (N * t) (t * s)) (pull (dvd_mul_right N t) f) =
      pull (dvd_mul_right N t) (PAG.Part15.conv (geps N s) f)
-- PAG218（Part 214）
noncomputable def shellAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪
    Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)))
-- PAG232（Part 228）
theorem convL_geps_mem (N s : ℕ) [NeZero N] : PAG.Part15.convL (geps N s) ∈ shellAlg N
theorem mulLeft_dind_mem (N s : ℕ) [NeZero N] : LinearMap.mulLeft ℂ (dind N s) ∈ shellAlg N
-- PAG262（Part 258）
theorem exists_mulLeft_of_mem_span (M : ℕ) [NeZero M] {T : Module.End ℂ (ZMod M → ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) :
    ∃ h : ZMod M → ℂ, T = LinearMap.mulLeft ℂ h
-- PAG263（Part 259）
theorem pull_pull (hNM : N ∣ M) (hML : M ∣ L) (f : ZMod N → ℂ) :
    PAG.Part201.pull hML (PAG.Part201.pull hNM f) = PAG.Part201.pull (hNM.trans hML) f
theorem pull_injective' (hNM : N ∣ M) : Function.Injective (PAG.Part201.pull hNM)
```
