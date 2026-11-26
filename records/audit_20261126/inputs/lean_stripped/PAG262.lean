
import PAG261

open Complex Finset

namespace PAG.Part262

open PAG.Part205 PAG.Part218 PAG.Part232
open ZMod (stdAddChar)
open scoped ZMod

variable {a b : ℕ} [NeZero a] [NeZero b]

noncomputable def shellLift (hab : a.Coprime b) : shellAlg a →ₐ[ℂ] shellAlg (a * b) :=
  (shellAlgTensorEquiv hab).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft : shellAlg a →ₐ[ℂ] TensorProduct ℂ (shellAlg a) (shellAlg b))

theorem shellLift_apply (hab : a.Coprime b) (S : shellAlg a) :
    shellLift hab S = shellAlgTensorEquiv hab (S ⊗ₜ[ℂ] (1 : shellAlg b)) := rfl

theorem crtConj_shellLift (hab : a.Coprime b) (S : shellAlg a) :
    crtConj hab (shellLift hab S : Module.End ℂ (ZMod (a * b) → ℂ)) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) := by
  rw [shellLift_apply, crtConj_shellAlgTensorEquiv_tmul]
  have h1 : ((1 : shellAlg b) : Module.End ℂ (ZMod b → ℂ)) = 1 := rfl
  rw [h1, PAG.Part251.rightOp_one' a, mul_one]

omit [NeZero a] [NeZero b] in

theorem castHom_crt_symm (hab : a.Coprime b) (q : ZMod a × ZMod b) :
    ZMod.castHom (dvd_mul_right a b) (ZMod a) ((ZMod.chineseRemainder hab).symm q) = q.1 := by
  rw [← PAG.Part240.crt_fst_eq_castHom hab, RingEquiv.apply_symm_apply]

omit [NeZero a] [NeZero b] in
theorem crtLin_pull (hab : a.Coprime b) (f : ZMod a → ℂ) (q : ZMod a × ZMod b) :
    crtLin hab (PAG.Part201.pull (dvd_mul_right a b) f) q = f q.1 := by
  rw [crtLin_apply, PAG.Part201.pull_apply, castHom_crt_symm]

theorem shellLift_pull (hab : a.Coprime b) (S : shellAlg a) (f : ZMod a → ℂ) :
    (shellLift hab S : Module.End ℂ (ZMod (a * b) → ℂ)) (PAG.Part201.pull (dvd_mul_right a b) f) =
      PAG.Part201.pull (dvd_mul_right a b) ((S : Module.End ℂ (ZMod a → ℂ)) f) := by
  apply (crtLin hab).injective
  have h1 : ∀ (T : Module.End ℂ (ZMod (a * b) → ℂ)) (g : ZMod (a * b) → ℂ),
      crtLin hab (T g) = crtConj hab T (crtLin hab g) := by
    intro T g; rw [crtConj_apply, LinearEquiv.symm_apply_apply]
  rw [h1, crtConj_shellLift]
  funext p
  rw [leftOp_apply, crtLin_pull]
  have h2 : (fun x : ZMod a => crtLin hab (PAG.Part201.pull (dvd_mul_right a b) f) (x, p.2)) = f := by
    funext x; rw [crtLin_pull]
  rw [h2]

set_option synthInstance.maxHeartbeats 200000 in

theorem shellLift_dind (hab : a.Coprime b) {s : ℕ} (hs : s ∣ a) :
    (shellLift hab ⟨_, mulLeft_dind_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) =
      ∑ u ∈ b.divisors, LinearMap.mulLeft ℂ (dind (a * b) (s * u)) := by
  have h1 : (1 : shellAlg b) = ∑ u ∈ b.divisors, (⟨_, mulLeft_dind_mem b u⟩ : shellAlg b) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_mulLeft_dind b).symm
  rw [shellLift_apply, h1, TensorProduct.tmul_sum, map_sum, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro u hu
  exact shellAlgTensorEquiv_dind hab hs (Nat.dvd_of_mem_divisors hu)

set_option synthInstance.maxHeartbeats 200000 in

theorem shellLift_geps (hab : a.Coprime b) {s : ℕ} (hs : s ∣ a) :
    (shellLift hab ⟨_, convL_geps_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) =
      ∑ u ∈ b.divisors, PAG.Part15.convL (geps (a * b) (s * u)) := by
  have h1 : (1 : shellAlg b) = ∑ u ∈ b.divisors, (⟨_, convL_geps_mem b u⟩ : shellAlg b) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_convL_geps b).symm
  rw [shellLift_apply, h1, TensorProduct.tmul_sum, map_sum, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro u hu
  exact shellAlgTensorEquiv_geps hab hs (Nat.dvd_of_mem_divisors hu)

theorem shellLift_injective (hab : a.Coprime b) : Function.Injective (shellLift hab) := by
  intro S S' h
  apply Subtype.ext
  apply leftHom_injective a b
  rw [leftHom_apply, leftHom_apply, ← crtConj_shellLift hab, ← crtConj_shellLift hab, h]

theorem exists_compatible_hom (hab : a.Coprime b) :
    ∃ φ : shellAlg a →ₐ[ℂ] shellAlg (a * b),
      (∀ (S : shellAlg a) (f : ZMod a → ℂ),
        (φ S : Module.End ℂ (ZMod (a * b) → ℂ)) (PAG.Part201.pull (dvd_mul_right a b) f) =
          PAG.Part201.pull (dvd_mul_right a b) ((S : Module.End ℂ (ZMod a → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind (a * b) t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps (a * b) t))) := by
  refine ⟨shellLift hab, shellLift_pull hab, fun s => ?_, fun s => ?_⟩
  · by_cases hs : s ∣ a
    · rw [shellLift_dind hab hs]
      exact Submodule.sum_mem _ fun u _ => Submodule.subset_span ⟨s * u, rfl⟩
    · have h0 : (⟨_, mulLeft_dind_mem a s⟩ : shellAlg a) = 0 := by
        apply Subtype.ext
        show LinearMap.mulLeft ℂ (dind a s) = 0
        rw [dind_eq_zero_of_not_dvd hs]; exact LinearMap.mulLeft_zero_eq_zero ℂ _
      rw [h0, map_zero]
      exact Submodule.zero_mem _
  · by_cases hs : s ∣ a
    · rw [shellLift_geps hab hs]
      exact Submodule.sum_mem _ fun u _ => Submodule.subset_span ⟨s * u, rfl⟩
    · have h0 : (⟨_, convL_geps_mem a s⟩ : shellAlg a) = 0 := by
        apply Subtype.ext
        show PAG.Part15.convL (geps a s) = 0
        rw [geps_eq_zero_of_not_dvd hs, map_zero]
      rw [h0, map_zero]
      exact Submodule.zero_mem _

theorem conv_single (M : ℕ) [NeZero M] (g : ZMod M → ℂ) :
    PAG.Part15.conv g (Pi.single 0 1) = g := by
  rw [PAG.Part15.conv_comm]; exact PAG.Part111.conv_single_gen g

noncomputable def dTop (N : ℕ) [NeZero N] : shellAlg N := ⟨_, mulLeft_dind_mem N N⟩

noncomputable def eTop (N : ℕ) [NeZero N] : shellAlg N := ⟨_, convL_geps_mem N N⟩

theorem dTop_eTop_dTop (N : ℕ) [NeZero N] :
    dTop N * eTop N * dTop N = (N : ℂ)⁻¹ • dTop N := by
  apply Subtype.ext
  apply LinearMap.ext; intro f; funext x
  show dind N N x * PAG.Part15.conv (geps N N) (dind N N * f) x = (N : ℂ)⁻¹ * (dind N N x * f x)
  rw [show geps N N = fun _ => (N : ℂ)⁻¹ from funext (PAG.Part243.geps_self N)]
  by_cases hx : x = 0
  · subst hx
    unfold PAG.Part15.conv
    rw [Finset.sum_eq_single (0 : ZMod N)]
    · simp [PAG.Part251.dind_self_apply]
    · intro y _ hy
      simp [PAG.Part251.dind_self_apply, hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp [PAG.Part251.dind_self_apply, hx]

theorem eTop_mul_self (N : ℕ) [NeZero N] : eTop N * eTop N = eTop N := by
  apply Subtype.ext
  apply LinearMap.ext; intro f
  show PAG.Part15.conv (geps N N) (PAG.Part15.conv (geps N N) f) = PAG.Part15.conv (geps N N) f
  rw [← PAG.Part89.conv_assoc', geps_conv_geps]; simp

theorem exists_mulLeft_of_mem_span (M : ℕ) [NeZero M] {T : Module.End ℂ (ZMod M → ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) :
    ∃ h : ZMod M → ℂ, T = LinearMap.mulLeft ℂ h := by
  have hle : Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)) ≤
      LinearMap.range (LinearMap.mul ℂ (ZMod M → ℂ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact ⟨dind M t, rfl⟩
  obtain ⟨h, hh⟩ := hle hT
  exact ⟨h, hh.symm⟩

theorem exists_convL_of_mem_span (M : ℕ) [NeZero M] {T : Module.End ℂ (ZMod M → ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t))) :
    ∃ g ∈ Submodule.span ℂ (Set.range fun t : ℕ => geps M t), T = PAG.Part15.convL g := by
  have heq : (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) =
      (PAG.Part15.convL : (ZMod M → ℂ) →ₗ[ℂ] _) '' (Set.range fun t : ℕ => geps M t) := by
    rw [← Set.range_comp]; rfl
  rw [heq, Submodule.span_image] at hT
  obtain ⟨g, hg, rfl⟩ := hT
  exact ⟨g, hg, rfl⟩

theorem dft_const_on_shells (M : ℕ) [NeZero M] {g : ZMod M → ℂ}
    (hg : g ∈ Submodule.span ℂ (Set.range fun t : ℕ => geps M t)) (ξ ξ' : ZMod M)
    (h : Nat.gcd M ξ.val = Nat.gcd M ξ'.val) : 𝓕 g ξ = 𝓕 g ξ' := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    rw [dft_geps]; unfold dind; rw [h]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]
  | smul c x _ hx => rw [map_smul, Pi.smul_apply, Pi.smul_apply, hx]

theorem mem_ker_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (y : ZMod M) :
    ZMod.castHom hNM (ZMod N) y = 0 ↔ ∃ c : ZMod M, y = (N : ZMod M) * c := by
  constructor
  · intro hy
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨(c : ZMod M), ?_⟩
    rw [← ZMod.natCast_zmod_val y, hc]; push_cast; ring
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem sum_ker_stdAddChar {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (a : ZMod M) :
    ∑ y ∈ univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0), stdAddChar (a * y) =
      if a * (N : ZMod M) = 0 then ((univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0)).card : ℂ)
      else 0 := by
  set H := univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0) with hH
  by_cases ha : a * (N : ZMod M) = 0
  · simp only [ha, ↓reduceIte]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro y hy
    obtain ⟨c, rfl⟩ := (mem_ker_iff hNM y).mp (Finset.mem_filter.mp hy).2
    rw [← mul_assoc, ha, zero_mul, AddChar.map_zero_eq_one]
  · simp only [ha, ↓reduceIte]
    set y0 : ZMod M := (N : ZMod M)
    have hy0 : stdAddChar (a * y0) ≠ 1 := by
      intro h1
      apply ha
      rw [← AddChar.map_zero_eq_one (stdAddChar (N := M))] at h1
      exact ZMod.injective_stdAddChar h1
    have hshift : ∑ y ∈ H, stdAddChar (a * (y + y0)) = ∑ y ∈ H, stdAddChar (a * y) := by
      refine Finset.sum_equiv (Equiv.addRight y0) (fun y => ?_) (fun y _ => rfl)
      simp only [hH, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight, map_add]
      have : ZMod.castHom hNM (ZMod N) y0 = 0 := by
        rw [map_natCast, ZMod.natCast_self]
      rw [this, add_zero]
    have hmul : ∑ y ∈ H, stdAddChar (a * (y + y0)) = stdAddChar (a * y0) * ∑ y ∈ H, stdAddChar (a * y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [mul_add, AddChar.map_add_eq_mul, mul_comm]
    have h0 : (stdAddChar (a * y0) - 1) * ∑ y ∈ H, stdAddChar (a * y) = 0 := by
      rw [sub_mul, ← hmul, hshift, one_mul, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hy0
    · exact h

theorem p_dvd_div_p {N M p : ℕ} [NeZero M] (hNM : N ∣ M) (hpN : p ∣ N) (hpk : p ∣ M / N) : p ∣ M / p := by
  have hM : M = N * (M / N) := (Nat.mul_div_cancel' hNM).symm
  have hpp : p * p ∣ M := by rw [hM]; exact Nat.mul_dvd_mul hpN hpk
  exact Nat.dvd_div_of_mul_dvd hpp

theorem sq_x_eq_zero {N M p : ℕ} [NeZero M] (hNM : N ∣ M) (hpN : p ∣ N) (hpk : p ∣ M / N) :
    ((M / p : ℕ) : ZMod M) * ((M / p : ℕ) : ZMod M) = 0 := by
  obtain ⟨r, hr⟩ := p_dvd_div_p hNM hpN hpk
  have hpM : p ∣ M := (hpN.trans hNM)
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  refine ⟨r, ?_⟩
  calc M / p * (M / p) = M / p * (p * r) := by rw [← hr]
    _ = M / p * p * r := by ring
    _ = M * r := by rw [Nat.div_mul_cancel hpM]

theorem x_mul_N {N M p : ℕ} [NeZero M] (hNM : N ∣ M) (hpN : p ∣ N) :
    ((M / p : ℕ) : ZMod M) * (N : ZMod M) = 0 := by
  have hpM : p ∣ M := (hpN.trans hNM)
  obtain ⟨c, hc⟩ := hpN
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  refine ⟨c, ?_⟩
  calc M / p * N = M / p * (p * c) := by rw [← hc]
    _ = M / p * p * c := by ring
    _ = M * c := by rw [Nat.div_mul_cancel hpM]

theorem mul_x_ne_zero {N M p : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (hp : p.Prime) (hpN : p ∣ N)
    (hpk : p ∣ M / N) (ξ : ZMod M) (hξ : (ξ - 1) * (N : ZMod M) = 0) :
    ξ * ((M / p : ℕ) : ZMod M) ≠ 0 := by
  intro h0
  have hpM : p ∣ M := (hpN.trans hNM)
  set v := ξ.val
  have hξv : ((v : ℕ) : ZMod M) = ξ := ZMod.natCast_zmod_val ξ

  have h1 : p ∣ v := by
    rw [← hξv, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
    have hpos : 0 < M / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) hp.pos
    have h0' : M / p * p ∣ M / p * v := by
      rw [Nat.div_mul_cancel hpM, mul_comm (M / p)]; exact h0
    exact Nat.dvd_of_mul_dvd_mul_left hpos h0'

  have h2 : (p : ℤ) ∣ (v : ℤ) - 1 := by
    have e : (((((v : ℤ) - 1) * (N : ℤ)) : ℤ) : ZMod M) = 0 := by
      push_cast; rw [hξv]; exact hξ
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at e
    have hM : (M : ℤ) = (N : ℤ) * ((M / N : ℕ) : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hNM).symm
    rw [hM, mul_comm ((v : ℤ) - 1)] at e
    have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hk : ((M / N : ℕ) : ℤ) ∣ (v : ℤ) - 1 := (mul_dvd_mul_iff_left hN0).mp e
    exact (Int.natCast_dvd_natCast.mpr hpk).trans hk
  have h3 : (p : ℤ) ∣ 1 := by
    have := dvd_sub (Int.natCast_dvd_natCast.mpr h1) h2
    simpa using this
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h3)

theorem no_compatible_hom {N M p : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (hp : p.Prime) (hpN : p ∣ N)
    (hpk : p ∣ M / N) :
    ¬ ∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t))) := by
  rintro ⟨φ, h2, hD, hE⟩
  obtain ⟨h, hh⟩ := exists_mulLeft_of_mem_span M (hD N)
  obtain ⟨g, hg, hgg⟩ := exists_convL_of_mem_span M (hE N)
  change (φ (dTop N) : Module.End ℂ (ZMod M → ℂ)) = _ at hh
  change (φ (eTop N) : Module.End ℂ (ZMod M → ℂ)) = _ at hgg

  have hH : ∀ y, h y = dind N N (ZMod.castHom hNM (ZMod N) y) := by
    intro y
    have e := congrFun (h2 (dTop N) (fun _ => 1)) y
    rw [hh] at e
    simpa [PAG.Part201.pull_apply, dTop] using e

  have hidem : PAG.Part15.conv g g = g := by
    have e := congrArg (fun S : shellAlg N => ((φ S : shellAlg M) : Module.End ℂ (ZMod M → ℂ)))
      (eTop_mul_self N)
    simp only [map_mul, Subalgebra.coe_mul, hgg] at e
    have e2 := LinearMap.congr_fun e (Pi.single 0 1)
    simpa [PAG.Part15.convL_apply, conv_single] using e2
  set m := 𝓕 g with hm
  have hm01 : ∀ ξ, m ξ = 0 ∨ m ξ = 1 := by
    intro ξ
    have e := congrFun (congrArg 𝓕 hidem) ξ
    rw [PAG.Part16.dft_conv, Pi.mul_apply] at e
    have : m ξ * (m ξ - 1) = 0 := by rw [mul_sub, e, mul_one, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)

  have hδ : h * Pi.single 0 1 = Pi.single 0 1 := by
    funext z
    by_cases hz : z = 0
    · subst hz; simp [hH, PAG.Part251.dind_self_apply]
    · simp [hz]
  have hgH : ∀ y, ZMod.castHom hNM (ZMod N) y = 0 → g y = (N : ℂ)⁻¹ * (if y = 0 then 1 else 0) := by
    intro y hy
    have e := congrArg (fun S : shellAlg N => ((φ S : shellAlg M) : Module.End ℂ (ZMod M → ℂ)))
      (dTop_eTop_dTop N)
    simp only [map_mul, map_smul, Subalgebra.coe_mul, Subalgebra.coe_smul, hh, hgg] at e
    have e2 := congrFun (LinearMap.congr_fun e (Pi.single 0 1)) y
    have hy1 : h y = 1 := by rw [hH, hy, PAG.Part251.dind_self_apply]; simp
    have key1 : ∀ F : ZMod M → ℂ, (LinearMap.mulLeft ℂ h * PAG.Part15.convL g * LinearMap.mulLeft ℂ h) F =
        h * PAG.Part15.conv g (h * F) := fun F => rfl
    have key2 : ∀ F : ZMod M → ℂ, ((N : ℂ)⁻¹ • LinearMap.mulLeft ℂ h) F = (N : ℂ)⁻¹ • (h * F) := fun F => rfl
    rw [key1, key2, hδ, conv_single, Pi.mul_apply, Pi.smul_apply, hy1, one_mul, smul_eq_mul] at e2
    rw [e2]
    by_cases hy0 : y = 0
    · subst hy0; simp
    · simp [hy0]

  have hginv : ∀ y, g y = (M : ℂ)⁻¹ * ∑ ξ, stdAddChar (ξ * y) * m ξ := by
    intro y
    have e : 𝓕⁻ m = g := by rw [hm]; exact (ZMod.dft).symm_apply_apply g
    rw [← e, ZMod.invDFT_apply]
    simp [smul_eq_mul]
  set H := univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0) with hHdef
  set C1 := univ.filter (fun ξ : ZMod M => (ξ - 1) * (N : ZMod M) = 0) with hC1def
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)

  have hS1 : ∑ y ∈ H, stdAddChar (-y) * ((M : ℂ) * g y) = (M : ℂ) * (N : ℂ)⁻¹ := by
    rw [Finset.sum_eq_single (0 : ZMod M)]
    · rw [hgH 0 (map_zero _)]; simp
    · intro y hyH hy0
      rw [hgH y (Finset.mem_filter.mp hyH).2]; simp [hy0]
    · intro h0
      have h0H : (0 : ZMod M) ∈ H := by
        rw [hHdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, map_zero _⟩
      exact absurd h0H h0
  have hS2 : ∑ y ∈ H, stdAddChar (-y) * ((M : ℂ) * g y) = (H.card : ℂ) * ∑ ξ ∈ C1, m ξ := by
    have step : ∀ y, stdAddChar (-y) * ((M : ℂ) * g y) = ∑ ξ, m ξ * stdAddChar ((ξ - 1) * y) := by
      intro y
      rw [hginv, ← mul_assoc (M : ℂ), mul_inv_cancel₀ hM, one_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      rw [sub_mul, one_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun y _ => step y), Finset.sum_comm]
    have hinner : ∀ ξ, ∑ y ∈ H, m ξ * stdAddChar ((ξ - 1) * y) =
        m ξ * (if (ξ - 1) * (N : ZMod M) = 0 then (H.card : ℂ) else 0) := by
      intro ξ; rw [← Finset.mul_sum]; congr 1; exact sum_ker_stdAddChar hNM (ξ - 1)
    rw [Finset.sum_congr rfl (fun ξ _ => hinner ξ), hC1def, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    split_ifs <;> ring
  have hcard : (H.card : ℂ) * N = M := by
    have := PAG.Part201.card_ker_cast (N := N) (N' := M) hNM
    exact this
  have hC1 : ∑ ξ ∈ C1, m ξ = 1 := by
    have e := hS2.symm.trans hS1
    have hHc : (H.card : ℂ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hcard; exact hM hcard.symm
    have : (H.card : ℂ) * ∑ ξ ∈ C1, m ξ = (H.card : ℂ) * 1 := by
      rw [e, ← hcard]; field_simp
    exact mul_left_cancel₀ hHc this
  have hS : ∑ ξ ∈ C1, m ξ = ((C1.filter (fun ξ => m ξ = 1)).card : ℂ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter (fun ξ => m ξ = 1)]
    apply Finset.sum_congr rfl
    intro ξ _
    rcases hm01 ξ with h0 | h1
    · simp [h0]
    · simp [h1]
  have hone : (C1.filter (fun ξ => m ξ = 1)).card = 1 := by
    have := hS.symm.trans hC1
    exact_mod_cast this
  obtain ⟨ξ0, hξ0⟩ := Finset.card_eq_one.mp hone
  have hξ0mem : ξ0 ∈ C1.filter (fun ξ => m ξ = 1) := by rw [hξ0]; exact Finset.mem_singleton_self _

  set x : ZMod M := ((M / p : ℕ) : ZMod M) with hx
  have hx2 : x * x = 0 := sq_x_eq_zero hNM hpN hpk
  have hxN : x * (N : ZMod M) = 0 := x_mul_N hNM hpN
  let u : (ZMod M)ˣ := ⟨1 + x, 1 - x, by linear_combination (-1 : ZMod M) * hx2,
    by linear_combination (-1 : ZMod M) * hx2⟩
  have hξ1mem : (u : ZMod M) * ξ0 ∈ C1.filter (fun ξ => m ξ = 1) := by
    simp only [hC1def, Finset.mem_filter, Finset.mem_univ, true_and] at hξ0mem ⊢
    refine ⟨?_, ?_⟩
    · show ((1 + x) * ξ0 - 1) * (N : ZMod M) = 0
      linear_combination hξ0mem.1 + ξ0 * hxN
    · rw [← hξ0mem.2]
      exact dft_const_on_shells M hg _ _ (PAG.Part207.gcd_val_unit_mul M u ξ0)
  have hne : (u : ZMod M) * ξ0 ≠ ξ0 := by
    intro e
    have hξ0C : (ξ0 - 1) * (N : ZMod M) = 0 := by
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hξ0mem).1).2
      exact this
    apply mul_x_ne_zero hNM hp hpN hpk ξ0 hξ0C
    have e' : (1 + x) * ξ0 = ξ0 := e
    linear_combination e'
  have : (u : ZMod M) * ξ0 ∈ ({ξ0} : Finset (ZMod M)) := hξ0 ▸ hξ1mem
  exact hne (Finset.mem_singleton.mp this)

theorem exists_compatible_hom_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) :
    (∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)))) ↔
    Nat.Coprime N (M / N) := by
  constructor
  · intro hex
    by_contra hc
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
    exact no_compatible_hom hNM hp (hpd.trans (Nat.gcd_dvd_left _ _)) (hpd.trans (Nat.gcd_dvd_right _ _)) hex
  · intro hc
    rcases hNM with ⟨k, rfl⟩
    have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    rw [Nat.mul_div_cancel_left k hN0] at hc
    have : NeZero k := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
    exact exists_compatible_hom hc

end PAG.Part262

#print axioms PAG.Part262.shellLift_apply
#print axioms PAG.Part262.crtConj_shellLift
#print axioms PAG.Part262.castHom_crt_symm
#print axioms PAG.Part262.crtLin_pull
#print axioms PAG.Part262.shellLift_pull
#print axioms PAG.Part262.shellLift_dind
#print axioms PAG.Part262.shellLift_geps
#print axioms PAG.Part262.shellLift_injective
#print axioms PAG.Part262.exists_compatible_hom
#print axioms PAG.Part262.conv_single
#print axioms PAG.Part262.dTop_eTop_dTop
#print axioms PAG.Part262.eTop_mul_self
#print axioms PAG.Part262.exists_mulLeft_of_mem_span
#print axioms PAG.Part262.exists_convL_of_mem_span
#print axioms PAG.Part262.dft_const_on_shells
#print axioms PAG.Part262.mem_ker_iff
#print axioms PAG.Part262.sum_ker_stdAddChar
#print axioms PAG.Part262.p_dvd_div_p
#print axioms PAG.Part262.sq_x_eq_zero
#print axioms PAG.Part262.x_mul_N
#print axioms PAG.Part262.mul_x_ne_zero
#print axioms PAG.Part262.no_compatible_hom
#print axioms PAG.Part262.exists_compatible_hom_iff
