
import PAG257
import Mathlib.Algebra.Colimit.Module

namespace PAG.Part258

open ZMod Complex Finset PAG.Part256 PAG.Part257 DirichletCharacter

variable {N : ℕ} [NeZero N]

instance conductor_neZero (χ : DirichletCharacter ℂ N) : NeZero χ.conductor :=
  ⟨conductor_ne_zero (χ := χ)⟩

noncomputable def phaseA1 (χ : DirichletCharacter ℂ N) : ℂ := rootNum χ.primitiveCharacter

omit [NeZero N] in

theorem rootNum_congr {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂] (h : d₁ = d₂)
    (χ₁ : DirichletCharacter ℂ d₁) (χ₂ : DirichletCharacter ℂ d₂)
    (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) : rootNum χ₁ = rootNum χ₂ := by
  subst h
  have : χ₁ = χ₂ := by
    refine MulChar.ext (fun u => ?_)
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod d₁)
    rw [← ha]
    exact hχ a
  rw [this]

theorem phaseA1_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    phaseA1 χ = rootNum χ := by
  have hc : χ.conductor = N := (isPrimitive_def χ).mp hχ
  unfold phaseA1
  refine rootNum_congr hc _ _ (fun a => ?_)
  by_cases ha : IsCoprime a N
  · exact primitiveCharacter_apply_of_isCoprime χ ha
  · have ha' : ¬IsCoprime a χ.conductor := by rwa [hc]
    rw [(apply_eq_zero_iff χ.primitiveCharacter a).mpr ha', (apply_eq_zero_iff χ a).mpr ha]

theorem normSq_phaseA1 (χ : DirichletCharacter ℂ N) : Complex.normSq (phaseA1 χ) = 1 :=
  normSq_rootNum (primitiveCharacter_isPrimitive χ)

theorem phaseA1_changeLevel {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    phaseA1 (changeLevel hNM χ) = phaseA1 χ := by
  unfold phaseA1
  exact rootNum_congr (conductor_changeLevel χ hNM) _ _ (primitiveCharacter_changeLevel_apply hNM χ)

omit [NeZero N] in

theorem rootNum_one_of_eq_one {d : ℕ} [NeZero d] (hd : d = 1) :
    rootNum (1 : DirichletCharacter ℂ d) = 1 := by
  subst hd
  have heven : (1 : DirichletCharacter ℂ 1).Even := MulChar.one_apply isUnit_neg_one
  have hg : gaussSum (1 : DirichletCharacter ℂ 1) (stdAddChar (N := 1)) = 1 := by
    unfold gaussSum
    rw [Finset.univ_unique, Finset.sum_singleton,
      MulChar.one_apply (isUnit_of_subsingleton _), one_mul]
    have h0 : ∀ x : ZMod 1, (stdAddChar (N := 1)) x = 1 := fun x => by
      rw [Subsingleton.elim x 0, AddChar.map_zero_eq_one]
    exact h0 _
  rw [rootNum_eq, parFac_of_even heven, hg]
  simp

theorem phaseA1_one : phaseA1 (1 : DirichletCharacter ℂ N) = 1 := by
  unfold phaseA1
  rw [primitiveCharacter_one]
  exact rootNum_one_of_eq_one (conductor_one (R := ℂ) (n := N))

theorem ip_add_right (f g h : (ZMod N)ˣ → ℂ) : ip f (g + h) = ip f g + ip f h := by
  unfold ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun u _ => by rw [Pi.add_apply, mul_add])

theorem ip_smul_right (f g : (ZMod N)ˣ → ℂ) (c : ℂ) : ip f (c • g) = c * ip f g := by
  unfold ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun u _ => by rw [Pi.smul_apply, smul_eq_mul]; ring)

noncomputable def UA1 : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := ∑ χ : DirichletCharacter ℂ N,
    (phaseA1 χ * ip (charU χ) f / (Nat.totient N : ℂ)) • charU χ
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_add_right, mul_add, add_div, add_smul]
  map_smul' c f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_smul_right, smul_smul]
    congr 1
    ring

theorem UA1_charU (χ : DirichletCharacter ℂ N) : UA1 (charU χ) = phaseA1 χ • charU χ := by
  classical
  have hφ : (Nat.totient N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  show ∑ ψ : DirichletCharacter ℂ N,
    (phaseA1 ψ * ip (charU ψ) (charU χ) / (Nat.totient N : ℂ)) • charU ψ = phaseA1 χ • charU χ
  rw [Finset.sum_eq_single χ]
  · rw [ip_charU]
    simp only [↓reduceIte]
    congr 1
    field_simp
  · intro ψ _ hψ
    rw [ip_charU]
    simp only [hψ, ↓reduceIte, mul_zero, zero_div, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ χ) h

theorem ip_UA1 (f g : (ZMod N)ˣ → ℂ) : ip (UA1 f) (UA1 g) = ip f g := by
  classical
  have hf : f ∈ Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ N => charU χ) := by
    rw [span_charU_eq_top]
    exact Submodule.mem_top
  have hg : g ∈ Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ N => charU χ) := by
    rw [span_charU_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hg
  simp only [map_sum, _root_.map_smul, UA1_charU, smul_smul]
  rw [ip_sum_sum, ip_sum_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [ip_charU]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte]
    have hp : (starRingEnd ℂ) (phaseA1 i) * phaseA1 i = 1 := by
      rw [mul_comm, Complex.mul_conj, normSq_phaseA1, Complex.ofReal_one]
    rw [map_mul]
    linear_combination ((starRingEnd ℂ) (a i) * b i * (Nat.totient N : ℂ)) * hp
  · simp [h]

theorem UA1_eq_TopL_of_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f = TopL f :=
  TopL_eq_of_A1 UA1 (fun χ hχ => by rw [UA1_charU, phaseA1_of_isPrimitive hχ]) hf

noncomputable def pullL {M : ℕ} (hNM : N ∣ M) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod M)ˣ → ℂ) where
  toFun f u := f (ZMod.unitsMap hNM u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero N] in

theorem pullL_charU {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    pullL hNM (charU χ) = charU (changeLevel hNM χ) := by
  funext u
  show χ ((ZMod.unitsMap hNM u : (ZMod N)ˣ) : ZMod N) = (changeLevel hNM χ) (u : ZMod M)
  rw [changeLevel_eq_cast_of_dvd χ hNM u, ZMod.unitsMap_val]

theorem UA1_charU_eq_pull_TopL (χ : DirichletCharacter ℂ N) :
    UA1 (charU χ) = pullL χ.conductor_dvd_level (TopL (charU χ.primitiveCharacter)) := by
  rw [UA1_charU, TopL_charU, _root_.map_smul, pullL_charU, changeLevel_primitiveCharacter]
  rfl

theorem UA1_unique (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N,
      U (charU χ) = pullL χ.conductor_dvd_level (TopL (charU χ.primitiveCharacter))) :
    U = UA1 :=
  LinearMap.ext_on_range span_charU_eq_top (fun χ => by rw [hU, UA1_charU_eq_pull_TopL])

theorem UA1_comp_pullL {M : ℕ} [NeZero M] (hNM : N ∣ M) (f : (ZMod N)ˣ → ℂ) :
    UA1 (pullL hNM f) = pullL hNM (UA1 f) := by
  have h : (UA1 (N := M)).comp (pullL hNM) = (pullL hNM).comp (UA1 (N := N)) := by
    refine LinearMap.ext_on_range (span_charU_eq_top (N := N)) (fun χ => ?_)
    simp only [LinearMap.comp_apply]
    rw [pullL_charU, UA1_charU, UA1_charU, _root_.map_smul, pullL_charU, phaseA1_changeLevel]
  exact LinearMap.congr_fun h f

theorem TopL_not_compat :
    ∃ f : (ZMod 1)ˣ → ℂ, TopL (pullL (one_dvd 2) f) ≠ pullL (one_dvd 2) (TopL f) := by
  refine ⟨charU (1 : DirichletCharacter ℂ 1), ?_⟩
  rw [pullL_charU, changeLevel_one, TopL_charU, TopL_charU, _root_.map_smul, pullL_charU,
    changeLevel_one]
  intro h
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul, charU, Units.val_one, map_one, mul_one] at h1
  have h2 := congrArg Complex.normSq h1
  rw [removal_counterexample_normSq, normSq_rootNum isPrimitive_one_level_one] at h2
  norm_num at h2

theorem UA1_ne_TopL_prime (p : ℕ) [hp : Fact p.Prime] :
    charU (1 : DirichletCharacter ℂ p) ∈ Vimprim p ∧
      UA1 (charU (1 : DirichletCharacter ℂ p)) ≠ TopL (charU (1 : DirichletCharacter ℂ p)) := by
  refine ⟨charU_one_mem_Vimprim hp.out.two_le, ?_⟩
  rw [UA1_charU, TopL_charU, phaseA1_one]
  intro h
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul, charU, Units.val_one, map_one, mul_one] at h1
  have h2 := congrArg Complex.normSq h1
  rw [Complex.normSq_one, normSq_rootNum_one_prime] at h2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp at h2
  linarith

theorem UA1_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f ∈ Vprim N := by
  have hle : Vprim N ≤ (Vprim N).comap UA1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show UA1 (charU χ.1) ∈ Vprim N
    rw [UA1_charU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)
  exact hle hf

theorem UA1_mem_Vimprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vimprim N) : UA1 f ∈ Vimprim N := by
  have hle : Vimprim N ≤ (Vimprim N).comap UA1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show UA1 (charU χ.1) ∈ Vimprim N
    rw [UA1_charU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)
  exact hle hf

theorem UA1_comp_TopL (f : (ZMod N)ˣ → ℂ) : UA1 (TopL f) = TopL (UA1 f) := by
  have h : (UA1 (N := N)).comp TopL = TopL.comp UA1 := by
    refine LinearMap.ext_on_range (span_charU_eq_top (N := N)) (fun χ => ?_)
    simp only [LinearMap.comp_apply]
    rw [TopL_charU, _root_.map_smul, UA1_charU, _root_.map_smul, TopL_charU, smul_smul,
      smul_smul, mul_comm]
  exact LinearMap.congr_fun h f

theorem rootNum_one_prime (p : ℕ) [Fact p.Prime] :
    rootNum (1 : DirichletCharacter ℂ p) = -(((Real.sqrt p)⁻¹ : ℝ) : ℂ) := by
  have heven : (1 : DirichletCharacter ℂ p).Even := MulChar.one_apply isUnit_neg_one
  rw [rootNum_eq, parFac_of_even heven, gaussSum_one_prime, one_mul]
  push_cast
  ring

theorem TopL_not_compat_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ f : (ZMod 1)ˣ → ℂ, TopL (pullL (one_dvd p) f) ≠ pullL (one_dvd p) (TopL f) := by
  refine ⟨charU (1 : DirichletCharacter ℂ 1), ?_⟩
  rw [pullL_charU, changeLevel_one, TopL_charU, TopL_charU, _root_.map_smul, pullL_charU,
    changeLevel_one]
  intro h
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul, charU, Units.val_one, map_one, mul_one] at h1
  have h2 := congrArg Complex.normSq h1
  rw [normSq_rootNum_one_prime, normSq_rootNum isPrimitive_one_level_one] at h2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp at h2
  linarith

theorem gaussSum_inv (χ : DirichletCharacter ℂ N) :
    gaussSum χ⁻¹ (stdAddChar (N := N)) = χ (-1) * (starRingEnd ℂ) (gaussSum χ stdAddChar) := by
  have h1 : (starRingEnd ℂ) (gaussSum χ stdAddChar) = gaussSum χ⁻¹ (stdAddChar (N := N))⁻¹ := by
    rw [starRingEnd_apply, star_gaussSum_eq]
  have h2 : gaussSum χ⁻¹ (stdAddChar (N := N))⁻¹ = χ (-1) * gaussSum χ⁻¹ (stdAddChar (N := N)) := by
    rw [AddChar.inv_mulShift]
    have := gaussSum_mulShift_eq χ⁻¹ (stdAddChar (N := N)) (-1)
    rw [Units.val_neg, Units.val_one, inv_inv] at this
    rw [this]
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [h1, h2, ← mul_assoc, hsq, one_mul]

theorem rootNum_inv (χ : DirichletCharacter ℂ N) :
    rootNum χ⁻¹ = (starRingEnd ℂ) (rootNum χ) := by
  have hpar : χ⁻¹ (-1) = χ (-1) := by
    rw [MulChar.inv_apply_eq_inv']
    rcases χ.even_or_odd with h | h
    · rw [show χ (-1) = 1 from h, inv_one]
    · rw [show χ (-1) = -1 from h, inv_neg, inv_one]
  rw [rootNum_eq, rootNum_eq, gaussSum_inv]
  unfold parFac
  rw [hpar]
  rcases χ.even_or_odd with h | h
  · rw [show χ (-1) = 1 from h]
    simp only [map_div₀, map_add, map_sub, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat]
    ring
  · rw [show χ (-1) = -1 from h]
    simp only [map_div₀, map_add, map_sub, map_mul, map_one, map_neg, Complex.conj_I,
      Complex.conj_ofReal, map_ofNat]
    ring

theorem primitiveCharacter_inv_apply (χ : DirichletCharacter ℂ N) (a : ℤ) :
    (χ⁻¹).primitiveCharacter a = (χ.primitiveCharacter)⁻¹ a := by
  by_cases ha : IsCoprime a χ.conductor
  · have key : changeLevel (dvd_of_eq (conductor_inv χ)) (χ⁻¹).primitiveCharacter =
        (χ.primitiveCharacter)⁻¹ := by
      apply changeLevel_injective χ.conductor_dvd_level
      rw [← changeLevel_trans, changeLevel_primitiveCharacter, map_inv,
        changeLevel_primitiveCharacter]
    have := congrArg (fun ψ : DirichletCharacter ℂ χ.conductor => ψ (a : ZMod χ.conductor)) key
    rwa [changeLevel_eq_cast_of_dvd' _ _ ha] at this
  · have ha' : ¬IsCoprime a (χ⁻¹).conductor := by rwa [conductor_inv]
    rw [(apply_eq_zero_iff _ a).mpr ha', (apply_eq_zero_iff _ a).mpr ha]

theorem phaseA1_inv (χ : DirichletCharacter ℂ N) :
    phaseA1 χ⁻¹ = (starRingEnd ℂ) (phaseA1 χ) := by
  unfold phaseA1
  rw [rootNum_congr (conductor_inv χ) _ _ (primitiveCharacter_inv_apply χ), rootNum_inv]

theorem UA1_star (f : (ZMod N)ˣ → ℂ) :
    UA1 (fun u => (starRingEnd ℂ) (f u)) = fun u => (starRingEnd ℂ) (UA1 f u) := by
  classical
  have hf : f ∈ Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ N => charU χ) := by
    rw [span_charU_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  have hstar : (fun u => (starRingEnd ℂ) ((∑ χ, c χ • charU χ) u)) =
      ∑ χ, (starRingEnd ℂ) (c χ) • charU χ⁻¹ := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    congr 1
    show (starRingEnd ℂ) (χ (u : ZMod N)) = χ⁻¹ (u : ZMod N)
    rw [starRingEnd_apply, MulChar.star_apply']
  rw [hstar]
  simp only [map_sum, _root_.map_smul, UA1_charU, smul_smul]
  funext u
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  have hχ : (starRingEnd ℂ) (charU χ u) = charU χ⁻¹ u := by
    show (starRingEnd ℂ) (χ (u : ZMod N)) = χ⁻¹ (u : ZMod N)
    rw [starRingEnd_apply, MulChar.star_apply']
  rw [phaseA1_inv, hχ]

omit [NeZero N] in

theorem pullL_injective {M : ℕ} [NeZero M] (hNM : N ∣ M) : Function.Injective (pullL hNM) := by
  intro f g h
  funext v
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective hNM v
  exact congrFun h u

theorem sum_units_unitsMap {M : ℕ} [NeZero M] (hNM : N ∣ M) (F : (ZMod N)ˣ → ℂ) :
    (Nat.totient N : ℂ) * ∑ u : (ZMod M)ˣ, F (ZMod.unitsMap hNM u) =
      (Nat.totient M : ℂ) * ∑ v : (ZMod N)ˣ, F v := by
  classical
  set c := (Finset.univ.filter fun u : (ZMod M)ˣ => ZMod.unitsMap hNM u = 1).card with hc
  have hfib : ∀ v : (ZMod N)ˣ,
      (Finset.univ.filter fun u : (ZMod M)ˣ => ZMod.unitsMap hNM u = v).card = c := by
    intro v
    exact MonoidHom.card_fiber_eq_of_mem_range (ZMod.unitsMap hNM)
      (ZMod.unitsMap_surjective hNM v) (ZMod.unitsMap_surjective hNM 1)
  have hsum : ∑ u : (ZMod M)ˣ, F (ZMod.unitsMap hNM u) = (c : ℂ) * ∑ v : (ZMod N)ˣ, F v := by
    rw [← Finset.sum_fiberwise Finset.univ (fun u => ZMod.unitsMap hNM u)
      (fun u => F (ZMod.unitsMap hNM u)), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2]),
      Finset.sum_const, hfib, nsmul_eq_mul]
  have hcard : Nat.totient M = c * Nat.totient N := by
    rw [← ZMod.card_units_eq_totient M, ← ZMod.card_units_eq_totient N, ← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := fun u => ZMod.unitsMap hNM u) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
    rw [Finset.sum_congr rfl (fun v _ => hfib v), Finset.sum_const, smul_eq_mul, Finset.card_univ,
      mul_comm]
  rw [hsum, hcard]
  push_cast
  ring

theorem ip_pullL {M : ℕ} [NeZero M] (hNM : N ∣ M) (f g : (ZMod N)ˣ → ℂ) :
    (Nat.totient N : ℂ) * ip (pullL hNM f) (pullL hNM g) = (Nat.totient M : ℂ) * ip f g :=
  sum_units_unitsMap hNM (fun v => (starRingEnd ℂ) (f v) * g v)

theorem UA1_bijective : Function.Bijective (UA1 (N := N)) := by
  have hinj : Function.Injective (UA1 (N := N)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply eq_zero_of_ip_self
    rw [← ip_UA1, hf]
    simp [ip]
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

structure Lvl where

  val : ℕ
  pos : 0 < val
deriving DecidableEq

instance : Preorder Lvl where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

instance : IsDirectedOrder Lvl :=
  ⟨fun a b => ⟨⟨a.val * b.val, Nat.mul_pos a.pos b.pos⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance : Nonempty Lvl := ⟨⟨1, Nat.one_pos⟩⟩

instance (a : Lvl) : NeZero a.val := ⟨a.pos.ne'⟩

abbrev Gsp (a : Lvl) : Type := (ZMod a.val)ˣ → ℂ

noncomputable def pullSys (a b : Lvl) (h : a ≤ b) : Gsp a →ₗ[ℂ] Gsp b :=
  pullL (N := a.val) (M := b.val) h

instance : DirectedSystem Gsp (fun a b h => (pullSys a b h : Gsp a → Gsp b)) where
  map_self a f := by
    funext u
    show f (ZMod.unitsMap (dvd_refl a.val) u) = f u
    rw [ZMod.unitsMap_self]
    rfl
  map_map c b a hab hbc f := by
    funext u
    show f (ZMod.unitsMap hab (ZMod.unitsMap hbc u)) = f (ZMod.unitsMap (dvd_trans hab hbc) u)
    rw [← ZMod.unitsMap_comp hab hbc]
    rfl

theorem UA1_family_unique (U : ∀ a : Lvl, Gsp a →ₗ[ℂ] Gsp a)
    (hT : ∀ (a : Lvl) (f : Gsp a), f ∈ Vprim a.val → U a f = TopL f)
    (hc : ∀ (a b : Lvl) (h : a ≤ b) (f : Gsp a), U b (pullSys a b h f) = pullSys a b h (U a f))
    (a : Lvl) : U a = UA1 := by
  refine LinearMap.ext_on_range (span_charU_eq_top (N := a.val)) (fun χ => ?_)
  let q : Lvl := ⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩
  have hq : q ≤ a := χ.conductor_dvd_level
  have h1 : charU χ = pullSys q a hq (charU χ.primitiveCharacter) := by
    show charU χ = pullL χ.conductor_dvd_level (charU χ.primitiveCharacter)
    rw [pullL_charU, changeLevel_primitiveCharacter]
  have hprim : charU χ.primitiveCharacter ∈ Vprim q.val :=
    Submodule.subset_span ⟨⟨χ.primitiveCharacter, primitiveCharacter_isPrimitive χ⟩, rfl⟩
  rw [UA1_charU_eq_pull_TopL, h1, hc q a hq, hT q _ hprim]
  rfl

abbrev Lim : Type := Module.DirectLimit Gsp pullSys

noncomputable abbrev ofL (a : Lvl) : Gsp a →ₗ[ℂ] Lim := Module.DirectLimit.of ℂ Lvl Gsp pullSys a

theorem ofL_injective (a : Lvl) : Function.Injective (ofL a) := by
  intro f g h
  obtain ⟨b, hab, hb⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  exact pullL_injective hab hb

noncomputable def Uinf : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map (fun a => UA1 (N := a.val)) (fun a b h => by
    refine LinearMap.ext (fun f => ?_)
    exact UA1_comp_pullL (N := a.val) (M := b.val) h f)

theorem Uinf_ofL (a : Lvl) (f : Gsp a) : Uinf (ofL a f) = ofL a (UA1 f) :=
  Module.DirectLimit.map_apply_of _ _ _

theorem Uinf_unique (V : Lim →ₗ[ℂ] Lim) (hV : ∀ a (f : Gsp a), V (ofL a f) = ofL a (UA1 f)) :
    V = Uinf :=
  Module.DirectLimit.hom_ext (fun a => LinearMap.ext (fun f => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hV, Uinf_ofL]))

theorem Uinf_bijective : Function.Bijective Uinf := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨a, f, rfl⟩ := Module.DirectLimit.exists_of z
    rw [Uinf_ofL] at hz
    have h1 : UA1 f = 0 := ofL_injective a (by rw [hz, map_zero])
    have h2 : f = 0 := UA1_bijective.1 (by rw [h1, map_zero])
    rw [h2, map_zero]
  · intro z
    obtain ⟨a, g, rfl⟩ := Module.DirectLimit.exists_of z
    obtain ⟨f, rfl⟩ := UA1_bijective.2 g
    exact ⟨ofL a f, Uinf_ofL a f⟩

theorem Uinf_ofL_of_mem_Vprim (q : Lvl) {f : Gsp q} (hf : f ∈ Vprim q.val) :
    Uinf (ofL q f) = ofL q (TopL f) := by
  rw [Uinf_ofL, UA1_eq_TopL_of_mem_Vprim hf]

theorem ofL_charU (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
    ofL a (charU χ) =
      ofL ⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩ (charU χ.primitiveCharacter) := by
  have h : charU χ = pullL χ.conductor_dvd_level (charU χ.primitiveCharacter) := by
    rw [pullL_charU, changeLevel_primitiveCharacter]
  rw [h]
  exact Module.DirectLimit.of_f (G := Gsp) (f := pullSys)
    (i := ⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩) (j := a)
    (hij := χ.conductor_dvd_level) (x := charU χ.primitiveCharacter)

theorem span_ofL_Vprim : Submodule.span ℂ (⋃ q : Lvl, ofL q '' (Vprim q.val : Set (Gsp q))) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr (fun z => ?_)
  obtain ⟨a, f, rfl⟩ := Module.DirectLimit.exists_of z
  have hf : f ∈ Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ a.val => charU χ) := by
    rw [span_charU_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  rw [map_sum]
  refine Submodule.sum_mem _ (fun χ _ => ?_)
  rw [_root_.map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [ofL_charU]
  refine Set.mem_iUnion.mpr ⟨⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩,
    charU χ.primitiveCharacter, ?_, rfl⟩
  exact Submodule.subset_span ⟨⟨χ.primitiveCharacter, primitiveCharacter_isPrimitive χ⟩, rfl⟩

theorem Uinf_unique_TopL (V : Lim →ₗ[ℂ] Lim)
    (hV : ∀ q (f : Gsp q), f ∈ Vprim q.val → V (ofL q f) = ofL q (TopL f)) : V = Uinf := by
  refine LinearMap.ext_on span_ofL_Vprim (fun z hz => ?_)
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe] at hz
  obtain ⟨q, f, hf, rfl⟩ := hz
  rw [hV q f hf, Uinf_ofL_of_mem_Vprim q hf]

noncomputable def ipn {a : Lvl} (f g : Gsp a) : ℂ := ip f g / (Nat.totient a.val : ℂ)

theorem totient_ne_zero' (a : Lvl) : (Nat.totient a.val : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.totient_pos.mpr a.pos).ne'

theorem ipn_pullSys {a b : Lvl} (h : a ≤ b) (f g : Gsp a) :
    ipn (pullSys a b h f) (pullSys a b h g) = ipn f g := by
  unfold ipn
  have := ip_pullL (N := a.val) (M := b.val) h f g
  have ha := totient_ne_zero' a
  have hb := totient_ne_zero' b
  rw [div_eq_div_iff hb ha]
  calc ip (pullSys a b h f) (pullSys a b h g) * (Nat.totient a.val : ℂ)
      = (Nat.totient a.val : ℂ) * ip (pullL (N := a.val) (M := b.val) h f)
          (pullL (N := a.val) (M := b.val) h g) := by rw [mul_comm]; rfl
    _ = ip f g * (Nat.totient b.val : ℂ) := by rw [this, mul_comm]

theorem ipn_eq_of_ofL_eq {a b : Lvl} {f g : Gsp a} {f' g' : Gsp b}
    (hf : ofL a f = ofL b f') (hg : ofL a g = ofL b g') : ipn f g = ipn f' g' := by
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  have e1 : pullSys a c hac f = pullSys b c hbc f' := by
    apply ofL_injective c
    rw [Module.DirectLimit.of_f, Module.DirectLimit.of_f]
    exact hf
  have e2 : pullSys a c hac g = pullSys b c hbc g' := by
    apply ofL_injective c
    rw [Module.DirectLimit.of_f, Module.DirectLimit.of_f]
    exact hg
  rw [← ipn_pullSys hac, e1, e2, ipn_pullSys]

noncomputable def ipLim (z w : Lim) : ℂ :=
  ipn (Module.DirectLimit.exists_of₂ z w).choose_spec.choose
    (Module.DirectLimit.exists_of₂ z w).choose_spec.choose_spec.choose

theorem ipLim_ofL (a : Lvl) (f g : Gsp a) : ipLim (ofL a f) (ofL a g) = ipn f g := by
  unfold ipLim
  set h := Module.DirectLimit.exists_of₂ (ofL a f) (ofL a g)
  exact ipn_eq_of_ofL_eq h.choose_spec.choose_spec.choose_spec.1
    h.choose_spec.choose_spec.choose_spec.2

theorem ipLim_Uinf (z w : Lim) : ipLim (Uinf z) (Uinf w) = ipLim z w := by
  obtain ⟨a, f, g, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  rw [Uinf_ofL, Uinf_ofL, ipLim_ofL, ipLim_ofL]
  unfold ipn
  rw [ip_UA1]

theorem ipLim_add_right (z w w' : Lim) : ipLim z (w + w') = ipLim z w + ipLim z w' := by
  obtain ⟨a, f, g, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  obtain ⟨b, f', g', hf', rfl⟩ := Module.DirectLimit.exists_of₂ (ofL a f) w'
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  rw [← hf']
  rw [← Module.DirectLimit.of_f (hij := hbc) (x := f'), ← Module.DirectLimit.of_f (hij := hbc) (x := g'),
    ← Module.DirectLimit.of_f (hij := hac) (x := g), ← map_add, ipLim_ofL, ipLim_ofL, ipLim_ofL]
  unfold ipn
  rw [ip_add_right, add_div]

theorem ipLim_smul_right (z w : Lim) (r : ℂ) : ipLim z (r • w) = r * ipLim z w := by
  obtain ⟨a, f, g, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  rw [← _root_.map_smul, ipLim_ofL, ipLim_ofL]
  unfold ipn
  rw [ip_smul_right, mul_div_assoc]

theorem ipLim_conj (z w : Lim) : ipLim w z = (starRingEnd ℂ) (ipLim z w) := by
  obtain ⟨a, f, g, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  rw [ipLim_ofL, ipLim_ofL]
  unfold ipn ip
  rw [map_div₀, map_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem eq_zero_of_ipLim_self (z : Lim) (h : ipLim z z = 0) : z = 0 := by
  obtain ⟨a, f, rfl⟩ := Module.DirectLimit.exists_of z
  rw [ipLim_ofL] at h
  unfold ipn at h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · rw [eq_zero_of_ip_self f h, map_zero]
  · exact absurd h (totient_ne_zero' a)

theorem ipLim_self_nonneg (z : Lim) : ∃ r : ℝ, 0 ≤ r ∧ ipLim z z = r := by
  obtain ⟨a, f, rfl⟩ := Module.DirectLimit.exists_of z
  refine ⟨(∑ u, Complex.normSq (f u)) / (Nat.totient a.val : ℝ), ?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg (fun u _ => Complex.normSq_nonneg _)) (Nat.cast_nonneg _)
  · rw [ipLim_ofL]
    unfold ipn ip
    push_cast
    congr 1
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [mul_comm, Complex.mul_conj]

theorem UA1_pullL_of_mem_Vprim {M : ℕ} [NeZero M] (hNM : N ∣ M) {g : (ZMod N)ˣ → ℂ}
    (hg : g ∈ Vprim N) : UA1 (pullL hNM g) = pullL hNM (TopL g) := by
  rw [UA1_comp_pullL, UA1_eq_TopL_of_mem_Vprim hg]

noncomputable def condPart (N : ℕ) [NeZero N] (q : ℕ) : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.conductor = q} => charU χ.1)

theorem condPart_eq_map {M : ℕ} [NeZero M] (hNM : N ∣ M) :
    condPart M N = (Vprim N).map (pullL hNM) := by
  have key : ∀ (ψ : DirichletCharacter ℂ M) (d : ℕ) [NeZero d] (hd : ψ.conductor = d)
      (hdM : d ∣ M), charU ψ ∈ (Vprim d).map (pullL hdM) := by
    intro ψ d _ hd hdM
    subst hd
    refine ⟨charU ψ.primitiveCharacter,
      Submodule.subset_span ⟨⟨ψ.primitiveCharacter, primitiveCharacter_isPrimitive ψ⟩, rfl⟩, ?_⟩
    rw [pullL_charU]
    exact congrArg charU (changeLevel_primitiveCharacter ψ)
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨ψ, rfl⟩
    exact key ψ.1 N ψ.2 hNM
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show pullL hNM (charU χ.1) ∈ condPart M N
    rw [pullL_charU]
    refine Submodule.subset_span ⟨⟨changeLevel hNM χ.1, ?_⟩, rfl⟩
    rw [conductor_changeLevel]
    exact (isPrimitive_def χ.1).mp χ.2

theorem ip_condPart {q q' : ℕ} (hqq : q ≠ q') {f g : (ZMod N)ˣ → ℂ}
    (hf : f ∈ condPart N q) (hg : g ∈ condPart N q') : ip f g = 0 := by
  classical
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hg
  rw [ip_sum_sum]
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
  have hne : i.1 ≠ j.1 := fun h => hqq (i.2.symm.trans (h ▸ j.2))
  rw [ip_charU]
  simp [hne]

theorem iSup_condPart : ⨆ q, condPart N q = ⊤ := by
  rw [eq_top_iff, ← span_charU_eq_top, Submodule.span_le]
  rintro _ ⟨χ, rfl⟩
  exact Submodule.mem_iSup_of_mem χ.conductor (Submodule.subset_span ⟨⟨χ, rfl⟩, rfl⟩)

noncomputable def ipR (f : (ZMod N)ˣ → ℂ) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ℂ where
  toFun := ip f
  map_add' := ip_add_right f
  map_smul' c g := by rw [ip_smul_right, smul_eq_mul, RingHom.id_apply]

theorem iSupIndep_condPart : iSupIndep (condPart N) := by
  rw [iSupIndep_def]
  intro q
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ q), condPart N j) ≤ LinearMap.ker (ipR x) := by
    refine iSup₂_le (fun j hj => fun y hy => ?_)
    rw [LinearMap.mem_ker]
    exact ip_condPart (Ne.symm hj) hx hy
  have h0 : ip x x = 0 := LinearMap.mem_ker.mp (hle hx')
  exact eq_zero_of_ip_self x h0

theorem UA1_mem_condPart {q : ℕ} {f : (ZMod N)ˣ → ℂ} (hf : f ∈ condPart N q) :
    UA1 f ∈ condPart N q := by
  have hle : condPart N q ≤ (condPart N q).comap UA1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show UA1 (charU χ.1) ∈ condPart N q
    rw [UA1_charU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)
  exact hle hf

theorem ipLim_ofL_Vprim {q q' : Lvl} (hqq : q.val ≠ q'.val) {f : Gsp q} {g : Gsp q'}
    (hf : f ∈ Vprim q.val) (hg : g ∈ Vprim q'.val) : ipLim (ofL q f) (ofL q' g) = 0 := by
  let c : Lvl := ⟨q.val * q'.val, Nat.mul_pos q.pos q'.pos⟩
  have hqc : q ≤ c := dvd_mul_right q.val q'.val
  have hq'c : q' ≤ c := dvd_mul_left q'.val q.val
  rw [← Module.DirectLimit.of_f (hij := hqc) (x := f), ← Module.DirectLimit.of_f (hij := hq'c) (x := g),
    ipLim_ofL]
  unfold ipn
  have h1 : pullSys q c hqc f ∈ condPart c.val q.val := by
    rw [condPart_eq_map (N := q.val) (M := c.val) hqc]
    exact ⟨f, hf, rfl⟩
  have h2 : pullSys q' c hq'c g ∈ condPart c.val q'.val := by
    rw [condPart_eq_map (N := q'.val) (M := c.val) hq'c]
    exact ⟨g, hg, rfl⟩
  rw [ip_condPart hqq h1 h2, zero_div]

end PAG.Part258

#print axioms PAG.Part258.rootNum_congr
#print axioms PAG.Part258.phaseA1_of_isPrimitive
#print axioms PAG.Part258.normSq_phaseA1
#print axioms PAG.Part258.phaseA1_changeLevel
#print axioms PAG.Part258.rootNum_one_of_eq_one
#print axioms PAG.Part258.phaseA1_one
#print axioms PAG.Part258.ip_add_right
#print axioms PAG.Part258.ip_smul_right
#print axioms PAG.Part258.UA1_charU
#print axioms PAG.Part258.ip_UA1
#print axioms PAG.Part258.UA1_eq_TopL_of_mem_Vprim
#print axioms PAG.Part258.pullL_charU
#print axioms PAG.Part258.UA1_charU_eq_pull_TopL
#print axioms PAG.Part258.UA1_unique
#print axioms PAG.Part258.UA1_comp_pullL
#print axioms PAG.Part258.TopL_not_compat
#print axioms PAG.Part258.UA1_ne_TopL_prime
#print axioms PAG.Part258.UA1_mem_Vprim
#print axioms PAG.Part258.UA1_mem_Vimprim
#print axioms PAG.Part258.UA1_comp_TopL
#print axioms PAG.Part258.rootNum_one_prime
#print axioms PAG.Part258.TopL_not_compat_prime
#print axioms PAG.Part258.gaussSum_inv
#print axioms PAG.Part258.rootNum_inv
#print axioms PAG.Part258.primitiveCharacter_inv_apply
#print axioms PAG.Part258.phaseA1_inv
#print axioms PAG.Part258.UA1_star
#print axioms PAG.Part258.pullL_injective
#print axioms PAG.Part258.sum_units_unitsMap
#print axioms PAG.Part258.ip_pullL
#print axioms PAG.Part258.UA1_bijective
#print axioms PAG.Part258.UA1_family_unique
#print axioms PAG.Part258.ofL_injective
#print axioms PAG.Part258.Uinf_ofL
#print axioms PAG.Part258.Uinf_unique
#print axioms PAG.Part258.Uinf_bijective
#print axioms PAG.Part258.Uinf_ofL_of_mem_Vprim
#print axioms PAG.Part258.ofL_charU
#print axioms PAG.Part258.span_ofL_Vprim
#print axioms PAG.Part258.Uinf_unique_TopL
#print axioms PAG.Part258.totient_ne_zero'
#print axioms PAG.Part258.ipn_pullSys
#print axioms PAG.Part258.ipn_eq_of_ofL_eq
#print axioms PAG.Part258.ipLim_ofL
#print axioms PAG.Part258.ipLim_Uinf
#print axioms PAG.Part258.ipLim_add_right
#print axioms PAG.Part258.ipLim_smul_right
#print axioms PAG.Part258.ipLim_conj
#print axioms PAG.Part258.eq_zero_of_ipLim_self
#print axioms PAG.Part258.ipLim_self_nonneg
#print axioms PAG.Part258.UA1_pullL_of_mem_Vprim
#print axioms PAG.Part258.condPart_eq_map
#print axioms PAG.Part258.ip_condPart
#print axioms PAG.Part258.iSup_condPart
#print axioms PAG.Part258.iSupIndep_condPart
#print axioms PAG.Part258.UA1_mem_condPart
#print axioms PAG.Part258.ipLim_ofL_Vprim
