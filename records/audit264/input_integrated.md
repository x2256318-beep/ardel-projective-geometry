# 統合照合の入力：PAG264（Part 260）の形式文の全文、使う定義、散文

## A. PAG264.lean（形式文。docstring・コメントを除いた）
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

theorem fsum_self (g : ZMod N → ℂ) : fsum (dvd_refl N) g = g := by
  funext x
  simp [fsum, Finset.sum_filter]

theorem cornerOp_self (S : Module.End ℂ (ZMod N → ℂ)) : cornerOp (dvd_refl N) S = S := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  apply LinearMap.ext; intro g
  rw [cornerOp_apply, fsum_self, PAG.Part263.pull_self, div_self hN, one_smul]

theorem cornerHom_self : cornerHom (dvd_refl N) = NonUnitalAlgHom.id ℂ (shellAlg N) := by
  apply NonUnitalAlgHom.ext; intro S
  apply Subtype.ext
  exact cornerOp_self (S : Module.End ℂ (ZMod N → ℂ))

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
theorem pull_self (f : ZMod N → ℂ) : PAG.Part201.pull (dvd_refl N) f = f
```

## C. 散文その 1：PAG264.lean の冒頭の説明
```
/-
アーデル射影幾何 — Part 260（PAG264、短期層の小さいノート、2026-11-19）：角の写像 A_N → A_M（N ∣ M、非単位的な代数準同型）

問いの出所：方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §4）。2026-11-19 09:37 に著者が採用した。
基礎文書の第 5 章（索引 5.2 の留保「代数版にはならない」）と第 6 章 6.3（Bost–Connes との接続）の材料。新しいパートではない。

記号：N, M ≥ 1（`NeZero`）、N ∣ M、π : ℤ/M → ℤ/N。
- A_N = `shellAlg N`。D^{(N)}_s = mulLeft(dind N s)、E^{(N)}_s = convL(geps N s)（水準を上付きで書く）。
- π^* = `pull`（Part 197（PAG201））。P = `oldP N t`（Part 202（PAG206）、M = N·t のときの旧部分への射影）。
- ε^{(M)}_u = geps M u（E^{(M)}_u の畳み込み核）。

定義：
- `fsum h`（h : N ∣ M）：繊維の和 π_* g(x) = Σ_{π y = x} g(y)。
- `cornerOp h S = (N/M)·π^* ∘ S ∘ π_*`（S ∈ End(ℂ^{ℤ/N})）。
  - 読み：ι = π^*/√(M/N) とおくと ι S ι^† に当たる。π_* が π^* の随伴であること（数え上げの内積）は Lean の外。
- `cornerHom h : shellAlg N →ₙₐ[ℂ] shellAlg M`：非単位的な代数準同型。型は単位元の保存を課さない。

Lean の文：
1. 一般の S ∈ End(ℂ^{ℤ/N})：
   - π_*(π^* f) = (M/N)·f（`fsum_pull`）。
   - 引き戻しと両立 φ(S) π^* = π^* S（`cornerOp_pull`）。
   - 積（`cornerOp_mul`）、和・スカラー倍・0（`cornerOp_add`・`cornerOp_smul`・`cornerOp_zero`）。
   - φ(1)φ(S) = φ(S) = φ(S)φ(1)（`cornerOp_one_mul`・`cornerOp_mul_one`）。
   - 単射（`cornerOp_injective`）。
   - φ(1)(δ₀)(0) = N/M（`cornerOp_one_single`）。N < M なら φ(1) ≠ 1（`cornerOp_one_ne_one`）。
2. M = N·t の形：
   - π^*(π_* g) = t·P g（`pull_fsum`）。
   - φ(1) = P（`cornerOp_one_apply`）。
   - ε^{(Nt)}_{ts} ⋆ P g = ε^{(Nt)}_{ts} ⋆ g（`conv_geps_oldP`）。
   - φ(E^{(N)}_s) = E^{(Nt)}_{ts}（`cornerOp_geps_mul`）。
3. 一般の N ∣ M：
   - φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s（`cornerOp_one`）。
   - φ(E^{(N)}_s) = E^{(M)}_{(M/N)s}（`cornerOp_geps`）。
   - π^*(dind N s) = Σ_{u ∣ M, gcd(u, N) = s} dind M u（`pull_dind`）。
   - φ(D^{(N)}_s) = mulLeft(π^*(dind N s))·φ(1)（`cornerOp_dind`）。
   - φ は A_N を A_M に送る（`cornerOp_mem`）。gcd(N, M/N) は仮定にない。
   - まとめたものが `cornerHom`（値は `cornerHom_coe`）。
   - 像が φ(1) の角に入ること（⊆）は、`cornerOp_mem`・`cornerOp_one_mem`・`cornerOp_one_mul`・`cornerOp_mul_one` から直ちに出る（単独の宣言はない）。
4. 一意性と合成：
   - (a) すべての S, f で φ(S)(π^* f) = π^*(S f)、(b) φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
   - (a)(b) を満たす非単位的な代数準同型 A_N → A_M（`→ₙₐ` の中で）は、ちょうど 1 つ（`existsUnique_corner`）。
   - 一意性の証明は φ(S) = φ(S)φ(1) と (a)(b) だけを使う短い議論で、引き戻しとの両立だけで決まるという文ではない。
   - 独立照合の手計算の反例（Lean にしていない）：(b) を外すと一意でない（(N, M) = (1,2) で φ'(c) = c·1 も (a) を満たす）。(a) を外しても、積を保つことを外しても一意でない。
   - 繊維の和の合成（`fsum_trans`）。
   - N ∣ M ∣ L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}（`cornerOp_comp`・`cornerHom_comp`）。引き戻しの合成は Part 259（PAG263）の `pull_pull`。
   - 単射（`cornerHom_injective`）。N < M なら cornerHom(1) ≠ 1（`cornerHom_one_ne_one`）。
   - 恒等の法則（2026-11-19 午後に追加）：N → N の繊維の和は恒等（`fsum_self`）、φ_{N,N} = id（`cornerOp_self`・`cornerHom_self`。引き戻しの恒等は Part 259（PAG263）の `pull_self`）。
   - 合成の法則と恒等の法則が揃ったので、(A_N, φ_{N,M}) は整除の順序（N ∣ M）の上で、帰納系の 2 法則を満たす。Mathlib の `DirectedSystem` としての束ねと、極限の対象は Lean にしていない。
5. D 側の証人：(N, M) = (2, 4) で、φ(D^{(2)}_2) は D^{(4)}_u の線形結合でない（`cornerOp_dind_not_mem_span`）。
   - Part 258（PAG262）の殻を混ぜない条件（強い読み）の D 側を満たさない。E 側は 3 の φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} から満たす。
   - この現象は素数冪の段に固有ではない。N ∣ M、N < M なら、すべての s ∣ N で φ(D^{(N)}_s) は D^{(M)}_u の span に入らない。
     - 数値：M ≤ 30 の N < M の 81 組。
     - 手計算：(1,2)・(2,6)、独立照合。
     - Lean にあるのは (2,4)、s = 2 だけ。

範囲（Lean にしていないもの）：
- 像が角全体であること（φ(1) A_M φ(1) ⊆ φ(A_N) の側）。
  - 数値：111 組。
  - 手計算：構築側と盲検が一致。三重正則性（文献）からの短い帰結の見込み。
- 帰納系の `DirectedSystem` としての束ねと、その極限 A_∞（有限次元の代数の和集合。完備化は解像度が落ちる側の操作と読む）。
- Bost–Connes の ρ との対応（数値と手計算）。
- 随伴を保つこと φ(S^*) = φ(S)^*（行列の形からの手計算）。
- 対照群 F_p[t]/(t^e) → F_p[t]/(t^{e'})（数値。ℤ/p^e の段に当たる場合だけを試した）。

位置づけ（ラベル）：
- ［既知］：E 側の像 φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} と φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
  - Bose–Mesner 代数の商スキームの古典的事実（べき等元による角。Zieschang 2005、Kodalen 2019 §2.5）の作用素版。
  - 関数のレベルは Part 202（PAG206）。
- ［再導出（小さい）］：A_N を A_M に送ること、非単位的であること（N < M）、単射、一意性、合成、恒等の法則、D 側の証人。
  - 初等的な議論。
  - T(0) 版の文献は、盲検の問いテスト（2026-11-19）では見つからなかった（確信度：低〜中。MathSciNet・zbMATH は未実施）。
- 新規候補はない。対照群でも成り立つ（数値）ので、算術の内容ではない。
- A1 とは関係しない。

内部照合：
- 着手前（言葉の検索）：商に沿った非単位的な写像 A_N → A_M の宣言は、鎖になかった（網羅ではない）。
  - Part 202（PAG206）の `oldP` 系を使った：φ(1) = P、`oldP_eq_sum`（P = Σ E）、`geps_conv_pull`、`dft_oldP`。
  - Part 201（PAG205）の `dft_geps` も使った。
- 閉じる前（機械的）：全宣言 4470 件。PAG264 の対象は 46 件で、定理 41（自動生成の congr_simp を含む）と定義 5。
  - 候補は上位 20。定理は両向きに、定義は 1 回で照合し、41·20·2 + 5·20 = 1740 回。
  - 一致と出たのは `cornerOp_apply` と Part 197（PAG201）の `pull_smul` の 1 組だけ。どちらも定義を展開すると等しくなる式で、中身の重複ではない。
  - 候補の上位を言葉で確かめて、下書きの次の 2 つを消した。
    - `pull_trans`：Part 259（PAG263）の `pull_pull` と向きが逆の同じ文（A）。
    - `apply_single_two_of_mem_span`：Part 258（PAG262）の `exists_mulLeft_of_mem_span` から直ちに出る（B）。
  - 単射の証明は Part 259（PAG263）の `pull_injective'` を使う形に直した。
- 2 回目：全宣言 4468 件、対象 44 件（定理 39・定義 5）、39·20·2 + 5·20 = 1660 回。上の定義の展開の 1 組だけ。
- 宣言は定理 37・定義 5 で、自動生成の宣言は数えない。
- 「見つからなかった」は「重複はない」ではない。

照合（恒等の法則の追加と、それまでの尾をまとめた統合照合の記録は `records/audit264/`）：
- 独立照合（形式文と定義だけ）：偽・空虚な文はなかった。除去テストの反例を文面に反映した。
- 直した文面の再照合で、7 点の指摘を受けて直した。
  - 直した内容：非単位的の言い方、恒等の法則が Lean の外であること、条件の記号 (a)(b)、M = N·t の形、D 側の量化と根拠、水準の明示、件数の内訳、対照群の範囲。
  - 再照合の後のこの直しは、主張を狭めるか明確にするもので、照合を受けていない（尾。次の統合照合の対象）。
- 記録は `records/audit264/`。
-/
```

## D. 散文その 2：ノートの §1〜§3
## §1 結果（Lean の文から起こした）

記号：
- N, M ≥ 1 で N ∣ M。π : ℤ/M → ℤ/N。
- A_N = `shellAlg N`。Terwilliger 代数 T(0) とは辞書による同一視で、Lean の定理ではない。
- D^{(N)}_s・E^{(N)}_s は水準 N の殻の掛け算と双対殻への射影。
- π^* は引き戻し（Part 197（PAG201）の `pull`）、π_* は繊維の和（`fsum`）。

主な文：
- **写像**：φ(S) = (N/M)·π^* ∘ S ∘ π_*（`cornerOp`）。
  - 読み：ι = π^*/√(M/N) とおくと ι S ι^† に当たる。π_* が π^* の随伴であることは Lean の外。
- **A_N を A_M に送る**（`cornerOp_mem`）。
  - gcd(N, M/N) は仮定にないので、素数冪の段 (2,4)・(3,9) なども含む。
  - 非単位的な代数準同型 `cornerHom : A_N →ₙₐ A_M`（型は単位元の保存を課さない）としてまとめた。
- **生成元の像**：
  - φ(E^{(N)}_s) = E^{(M)}_{(M/N)s}（`cornerOp_geps`）。
  - φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s（`cornerOp_one`）。M = N·t と書いたとき、Part 202（PAG206）の `oldP N t` に等しい（`cornerOp_one_apply`）。
  - φ(D^{(N)}_s) = mulLeft(π^*(dind N s))·φ(1)（`cornerOp_dind`）。ここで π^*(dind N s) = Σ_{u ∣ M, gcd(u, N) = s} dind M u（`pull_dind`）。
- **引き戻しと両立**：φ(S)π^* = π^* S（`cornerOp_pull`）。
- **像は φ(1) の角に入る**（⊆。`cornerOp_one_mul`・`cornerOp_mul_one` と `cornerOp_mem` から）。
- **単射**（`cornerOp_injective`・`cornerHom_injective`）。
- **非単位的**：N < M なら φ(1) ≠ 1（`cornerOp_one_ne_one`・`cornerHom_one_ne_one`）。N = M の場合について、Lean の文は何も言っていない。
- **一意性**：次の (a)(b) を満たす非単位的な代数準同型 A_N → A_M は、`→ₙₐ` の中でちょうど 1 つ（`existsUnique_corner`）。
  - (a) 引き戻しと両立する。
  - (b) φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
  - 証明は φ(S) = φ(S)φ(1) と (a)(b) だけを使う短い議論。
  - 「引き戻しとの両立だけで決まる」という文ではない。独立照合の手計算の反例（Lean にしていない）：
    - (b) を外すと一意でない。(1,2) では φ'(c) = c·1 も (a) を満たす。
    - (a) を外しても、積を保つことを外しても一意でない。
- **合成**：N ∣ M ∣ L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}（`cornerOp_comp`・`cornerHom_comp`）。
  - 恒等の法則 φ_{N,N} = id（`cornerOp_self`・`cornerHom_self`。N → N の繊維の和は恒等 `fsum_self`、引き戻しの恒等は Part 259（PAG263）の `pull_self`）。2026-11-19 午後に追加（§9）。
  - 合成と恒等の 2 法則が揃い、(A_N, φ_{N,M}) は整除の順序の上で帰納系の法則を満たす。Mathlib の `DirectedSystem` としての束ねと、極限の対象は Lean の外。
- **D 側の証人**：(N, M) = (2, 4) で、φ(D^{(2)}_2) は D^{(4)}_u の線形結合でない（`cornerOp_dind_not_mem_span`）。
  - Part 258（PAG262）の殻を混ぜない条件（強い読み）の D 側を満たさない。E 側は満たす。
  - この現象は素数冪の段に固有ではない。N ∣ M、N < M なら、すべての s ∣ N で φ(D^{(N)}_s) は span に入らない。
    - 数値：M ≤ 30 の N < M の 81 組。
    - 手計算：(1,2)・(2,6)、独立照合。
    - Lean にあるのは (2,4)、s = 2 だけ。

## §2 ラベル

- **［既知］**：E 側の像 φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} と φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
  - Bose–Mesner 代数の商スキームの古典的事実（べき等元による角。Zieschang 2005、Kodalen 2019 §2.5。どちらも盲検が挙げたもの）の作用素版。
  - 関数のレベルは Part 202（PAG206）（`geps_conv_pull`、`oldP_eq_sum`）。
- **［再導出（小さい）］**：A_N を A_M に送ること、非単位的であること（N < M）、単射、一意性、合成、恒等の法則、D 側の証人。
  - どれも初等的な議論。
  - 盲検の問いテスト（2026-11-19）で見つからなかったもの（確信度：低〜中）：T(0) 版（部分スキーム・商スキームの T(0) が角として現れること）、整除の順序全体の帰納系、Bost–Connes と T(0) を結ぶ文献。
  - 検索語：Terwilliger algebra quotient scheme closed subset subscheme、triply regular、Terwilliger algebra Bost-Connes、inductive limit Terwilliger algebras ほか 17 本（`records/gamma_corner/outputs/blind_output.md`）。
  - 検索先はウェブだけ。MathSciNet・zbMATH は未実施（著者側）。「見つからなかった」は不存在の証明ではない。
- **新規候補はない**。対照群（F_p[t]/(t^e)）でも成り立つ（数値）ので、ℚ に固有の算術ではない。

## §3 範囲（Lean にしていないもの）

- **像が角全体であること**（φ(1) A_M φ(1) ⊆ φ(A_N) の側。逆の包含は §1）。
  - 数値：111/111 組。
  - 手計算：構築側と盲検の手計算が一致。三重正則性（Bhattacharyya–Song–Tanaka 2010、Munemasa 1993 の Lemma 4）からの短い帰結の見込み。
  - 鎖には三重正則性がない。
- **帰納系の `DirectedSystem` としての束ねと、整除の順序全体の極限 A_∞**。
  - A_∞ は有限次元の代数の和集合で、Ẑ 上の局所定数関数に作用する。
  - 完備化（L²(Ẑ)、C* 完備化）は解像度が落ちる側の操作と読み、目標として書かない（§1 の 08:41 の定義）。
- **Bost–Connes の ρ との対応**：群環の側で φ = ρ_{M/N}（数値）。L²(Ẑ) の表現では T(0) の片側だけが BC に対応する（盲検の手計算）。
- **随伴を保つこと** φ(S^*) = φ(S)^*（照合者の手計算）。
- **対照群** F_p[t]/(t^e) → F_p[t]/(t^{e'})：同じ文が成り立つ（数値）。これは関数体そのものではなく有限な剰余環で、ℤ/p^e の段に当たる場合だけを試した。

## E. 散文その 3：ノートの §8（前回の再照合を受けて直したことの一覧）
## §8 直した文面の再照合

- **条件**：新しいエージェントに、冒頭の説明とこのノートの §1〜§3、形式文と定義を渡した（Read 1 回、約 251 秒）。出力は `records/audit264/outputs/recheck_output.md`。
- **結果**：宣言名の取り違えと、形式文にあるのに Lean の外と書いたものは、なかった。
- **散文が形式文より強い・あいまいな箇所（7 点）を直した**：
  1. 「単位元を保たない代数準同型」を「非単位的な代数準同型（型は単位元の保存を課さない）。N < M なら φ(1) ≠ 1」にした。
  2. 「したがって帰納系をなす」を外した。恒等の法則 φ_{N,N} = id は Lean の外と書いた。
  3. `cornerOp_one_apply` が M = N·t の形の文であることを書いた。
  4. D 側の一般化を「N ∣ M、N < M、すべての s ∣ N」と量化し、根拠（数値 81 組と手計算）を揃えた。
  5. 三重正則性からの帰結を「見込み」に揃えた。
  6. ι S ι^† は読みで、随伴の同定は Lean の外と書いた。
  7. 一意性の条件を (a)(b) と書き、Part 258 の (ii) と区別した。
- **ほかに直したこと**：
  - Σ の添字に s ∣ M を書き、水準を E^{(N)}・E^{(M)} と明示した。
  - 件数の内訳を書いた（46 件 = 定理 41（自動生成の congr_simp を含む）＋定義 5、1740 = 41·20·2 + 5·20）。
  - 対照群の範囲を ℤ/p^e の段に当たる場合に狭めた。
  - PAG 番号を併記した。
  - 像が角に入る側（⊆）は Lean の文から直ちに出ると書き分けた。
- **再照合の後のこの直し**：主張を狭めるか明確にするもので、照合を受けていない。補足8の停止の規約の範囲内で、尾として次の統合照合の対象にする。
