
import PAG256

namespace PAG.Part257

open ZMod Complex Finset PAG.Part256

variable {N : ℕ} [NeZero N]

open Classical in

noncomputable def extL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun g x := if h : IsUnit x then g h.unit else 0
  map_add' f g := by
    funext x
    by_cases h : IsUnit x <;> simp [h]
  map_smul' c f := by
    funext x
    by_cases h : IsUnit x <;> simp [h]

open Classical in
theorem extL_apply (g : (ZMod N)ˣ → ℂ) (x : ZMod N) :
    extL g x = if h : IsUnit x then g h.unit else 0 := rfl

noncomputable def JHL : (ZMod N → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := JH f
  map_add' f g := by
    funext u
    show JH (f + g) u = JH f u + JH g u
    unfold JH hartley
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by rw [Pi.add_apply, add_mul])
  map_smul' c f := by
    funext u
    show JH (c • f) u = c * JH f u
    unfold JH hartley
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc])

noncomputable def TopL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) := JHL.comp extL

def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u

theorem extL_charU (χ : DirichletCharacter ℂ N) : extL (charU χ) = (χ : ZMod N → ℂ) := by
  funext x
  rw [extL_apply]
  by_cases h : IsUnit x
  · simp only [h, ↓reduceDIte, charU, IsUnit.unit_spec]
  · simp only [h, ↓reduceDIte, MulChar.map_nonunit χ h]

theorem TopL_charU (χ : DirichletCharacter ℂ N) : TopL (charU χ) = rootNum χ • charU χ := by
  funext u
  show JH (extL (charU χ)) u = rootNum χ * charU χ u
  rw [extL_charU]
  exact JH_eq_rootNum_mul_any χ u

noncomputable def ip (f g : (ZMod N)ˣ → ℂ) : ℂ := ∑ u, (starRingEnd ℂ) (f u) * g u

theorem ip_smul_smul (a b : ℂ) (f g : (ZMod N)ˣ → ℂ) :
    ip (a • f) (b • g) = (starRingEnd ℂ) a * b * ip f g := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  ring

theorem ip_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℂ) (v : ι → (ZMod N)ˣ → ℂ)
    (b : κ → ℂ) (w : κ → (ZMod N)ˣ → ℂ) :
    ip (N := N) (∑ i, a i • v i) (∑ j, b j • w j) =
      ∑ i, ∑ j, (starRingEnd ℂ) (a i) * b j * ip (v i) (w j) := by
  unfold ip
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]

  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun u _ => ?_)))
  ring

open Classical in

theorem ip_charU (χ ψ : DirichletCharacter ℂ N) :
    ip (charU χ) (charU ψ) = if χ = ψ then (Nat.totient N : ℂ) else 0 := by
  have h : ∀ u : (ZMod N)ˣ, (starRingEnd ℂ) (charU χ u) * charU ψ u = (χ⁻¹ * ψ) (u : ZMod N) := by
    intro u
    rw [MulChar.mul_apply, ← MulChar.star_apply']
    rfl
  rw [show ip (charU χ) (charU ψ) = ∑ u : (ZMod N)ˣ, (χ⁻¹ * ψ) (u : ZMod N) from
    Finset.sum_congr rfl (fun u _ => h u), PAG.Part218.sum_units_char]
  by_cases hχψ : χ = ψ
  · subst hχψ
    simp
  · have hne : χ⁻¹ * ψ ≠ 1 := fun h' => hχψ (inv_mul_eq_one.mp h')
    simp [hχψ, hne]

noncomputable def Vprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.IsPrimitive} => charU χ.1)

noncomputable def Vimprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // ¬χ.IsPrimitive} => charU χ.1)

theorem TopL_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : TopL f ∈ Vprim N := by
  have hle : Vprim N ≤ (Vprim N).comap TopL := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show TopL (charU χ.1) ∈ Vprim N
    rw [TopL_charU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)
  exact hle hf

theorem TopL_mem_Vimprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vimprim N) : TopL f ∈ Vimprim N := by
  have hle : Vimprim N ≤ (Vimprim N).comap TopL := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show TopL (charU χ.1) ∈ Vimprim N
    rw [TopL_charU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)
  exact hle hf

theorem rootNum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : rootNum χ ≠ 0 := by
  intro h
  have h1 := normSq_rootNum hχ
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem map_TopL_Vprim : (Vprim N).map TopL = Vprim N := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro f hf
    exact TopL_mem_Vprim hf
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    refine ⟨(rootNum χ.1)⁻¹ • charU χ.1, Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩), ?_⟩
    rw [_root_.map_smul, TopL_charU, smul_smul, inv_mul_cancel₀ (rootNum_ne_zero χ.2), one_smul]

theorem ip_TopL_charU_prim {χ ψ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ip (TopL (charU χ)) (TopL (charU ψ)) = ip (charU χ) (charU ψ) := by
  classical
  rw [TopL_charU, TopL_charU, ip_smul_smul, ip_charU]
  by_cases h : χ = ψ
  · subst h
    have hn : (starRingEnd ℂ) (rootNum χ) * rootNum χ = 1 := by
      rw [mul_comm, Complex.mul_conj, normSq_rootNum hχ, Complex.ofReal_one]
    rw [hn, one_mul]
  · simp [h]

theorem ip_TopL_of_mem_Vprim {f g : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) (hg : g ∈ Vprim N) :
    ip (TopL f) (TopL g) = ip f g := by
  classical
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hg
  simp only [map_sum, _root_.map_smul]
  rw [ip_sum_sum, ip_sum_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [ip_TopL_charU_prim i.2]

theorem TopL_eq_of_A1 (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → U (charU χ) = rootNum χ • charU χ)
    {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : U f = TopL f := by
  refine LinearMap.eqOn_span ?_ hf
  rintro _ ⟨χ, rfl⟩
  rw [hU χ.1 χ.2, TopL_charU]

theorem ip_Vprim_Vimprim {f g : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) (hg : g ∈ Vimprim N) :
    ip f g = 0 := by
  classical
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hg
  rw [ip_sum_sum]
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
  have hne : i.1 ≠ j.1 := fun h => j.2 (h ▸ i.2)
  rw [ip_charU]
  simp [hne]

theorem ip_sum_right {κ : Type*} [Fintype κ] (f : (ZMod N)ˣ → ℂ) (b : κ → ℂ)
    (w : κ → (ZMod N)ˣ → ℂ) : ip (N := N) f (∑ j, b j • w j) = ∑ j, b j * ip f (w j) := by
  unfold ip
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun u _ => ?_))
  ring

theorem linearIndependent_charU :
    LinearIndependent ℂ (fun χ : DirichletCharacter ℂ N => charU χ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg ψ
  have h := congrArg (ip (charU ψ)) hg
  rw [ip_sum_right] at h
  have hφ : (Nat.totient N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  simp only [ip_charU, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at h
  have h0 : ip (charU ψ) 0 = 0 := by simp [ip]
  rw [h0] at h
  exact (mul_eq_zero.mp h).resolve_right hφ

theorem span_charU_eq_top :
    Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ N => charU χ) = ⊤ := by
  classical
  refine linearIndependent_charU.span_eq_top_of_card_eq_finrank ?_
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card_units_eq_totient, Fintype.card_eq_nat_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

theorem Vprim_sup_Vimprim : Vprim N ⊔ Vimprim N = ⊤ := by
  rw [Vprim, Vimprim, ← Submodule.span_union, ← span_charU_eq_top]
  congr 1
  ext f
  constructor
  · rintro (⟨χ, rfl⟩ | ⟨χ, rfl⟩) <;> exact ⟨χ.1, rfl⟩
  · rintro ⟨χ, rfl⟩
    by_cases h : χ.IsPrimitive
    · exact Or.inl ⟨⟨χ, h⟩, rfl⟩
    · exact Or.inr ⟨⟨χ, h⟩, rfl⟩

theorem eq_zero_of_ip_self (f : (ZMod N)ˣ → ℂ) (h : ip f f = 0) : f = 0 := by
  have hsum : ip f f = ((∑ u, Complex.normSq (f u) : ℝ) : ℂ) := by
    unfold ip
    push_cast
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [mul_comm, Complex.mul_conj]
  rw [hsum] at h
  have h' : ∑ u, Complex.normSq (f u) = 0 := by exact_mod_cast h
  funext u
  have hu := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => Complex.normSq_nonneg (f u))).mp h' u
    (Finset.mem_univ u)
  exact Complex.normSq_eq_zero.mp hu

theorem Vprim_inf_Vimprim : Vprim N ⊓ Vimprim N = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_inf] at hf
  rw [Submodule.mem_bot]
  exact eq_zero_of_ip_self f (ip_Vprim_Vimprim hf.1 hf.2)

theorem isCompl_Vprim_Vimprim : IsCompl (Vprim N) (Vimprim N) :=
  isCompl_iff.mpr ⟨disjoint_iff.mpr Vprim_inf_Vimprim, codisjoint_iff.mpr Vprim_sup_Vimprim⟩

theorem Vprim_ne_bot_three : Vprim 3 ≠ ⊥ := by
  obtain ⟨χ, hχ, -⟩ := exists_primitive_odd_three
  intro h
  have hmem : charU χ ∈ Vprim 3 := Submodule.subset_span ⟨⟨χ, hχ⟩, rfl⟩
  rw [h, Submodule.mem_bot] at hmem
  have h1 := congrFun hmem 1
  simp [charU] at h1

theorem not_isometry_Vimprim_two : ∃ f ∈ Vimprim 2, ip (TopL f) (TopL f) ≠ ip f f := by
  classical
  refine ⟨charU (N := 2) 1,
    Submodule.subset_span ⟨⟨(1 : DirichletCharacter ℂ 2), removal_counterexample.1⟩, rfl⟩, ?_⟩
  rw [TopL_charU, ip_smul_smul, ip_charU]
  have hn : (starRingEnd ℂ) (rootNum (1 : DirichletCharacter ℂ 2)) *
      rootNum (1 : DirichletCharacter ℂ 2) = 1 / 2 := by
    rw [mul_comm, Complex.mul_conj, removal_counterexample_normSq]
    push_cast
    ring
  rw [hn]
  simp only [↓reduceIte]
  have h2 : (Nat.totient 2 : ℂ) = 1 := by
    rw [Nat.totient_prime Nat.prime_two]
    norm_num
  rw [h2]
  norm_num

theorem TopL_charU_one_four :
    TopL (charU (1 : DirichletCharacter ℂ 4)) = 0 ∧ charU (1 : DirichletCharacter ℂ 4) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [TopL_charU, Complex.normSq_eq_zero.mp removal_counterexample_four.2.2.2.2, zero_smul]
  · intro h
    have h1 := congrFun h 1
    simp [charU] at h1

theorem unitary_Vprim : ∃ e : Vprim N ≃ₗ[ℂ] Vprim N,
    (∀ f : Vprim N, ((e f : Vprim N) : (ZMod N)ˣ → ℂ) = TopL (f : (ZMod N)ˣ → ℂ)) ∧
    ∀ f g : Vprim N, ip ((e f : Vprim N) : (ZMod N)ˣ → ℂ) ((e g : Vprim N) : (ZMod N)ˣ → ℂ) =
      ip (f : (ZMod N)ˣ → ℂ) (g : (ZMod N)ˣ → ℂ) := by
  have hres : ∀ f ∈ Vprim N, TopL f ∈ Vprim N := fun f hf => TopL_mem_Vprim hf
  have hL : ∀ f : Vprim N, ((TopL.restrict hres f : Vprim N) : (ZMod N)ˣ → ℂ) =
      TopL (f : (ZMod N)ˣ → ℂ) := fun f => rfl
  have hinj : Function.Injective (TopL.restrict hres) := by
    intro f g hfg
    have hfg' := congrArg Subtype.val hfg
    rw [hL, hL] at hfg'
    have h0 : TopL ((f : (ZMod N)ˣ → ℂ) - (g : (ZMod N)ˣ → ℂ)) = 0 := by
      rw [map_sub, hfg', sub_self]
    have hmem : (f : (ZMod N)ˣ → ℂ) - (g : (ZMod N)ˣ → ℂ) ∈ Vprim N := Submodule.sub_mem _ f.2 g.2
    have hip : ip ((f : (ZMod N)ˣ → ℂ) - (g : (ZMod N)ˣ → ℂ))
        ((f : (ZMod N)ˣ → ℂ) - (g : (ZMod N)ˣ → ℂ)) = 0 := by
      rw [← ip_TopL_of_mem_Vprim hmem hmem, h0]
      simp [ip]
    exact Subtype.ext (sub_eq_zero.mp (eq_zero_of_ip_self _ hip))
  have hsurj : Function.Surjective (TopL.restrict hres) := by
    intro g
    have hg : (g : (ZMod N)ˣ → ℂ) ∈ (Vprim N).map TopL := by
      rw [map_TopL_Vprim]
      exact g.2
    obtain ⟨f, hf, hfg⟩ := hg
    exact ⟨⟨f, hf⟩, Subtype.ext hfg⟩
  have hbij : Function.Bijective (TopL.restrict hres) := ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.ofBijective (TopL.restrict hres) hbij, fun f => ?_, fun f g => ?_⟩
  · rw [LinearEquiv.ofBijective_apply, hL]
  · rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hL, hL]
    exact ip_TopL_of_mem_Vprim f.2 g.2

theorem gaussSum_one_prime (p : ℕ) [Fact p.Prime] :
    gaussSum (1 : DirichletCharacter ℂ p) (stdAddChar (N := p)) = -1 := by
  have hne : (stdAddChar (N := p)) ≠ 1 := by
    have h := (ZMod.isPrimitive_stdAddChar p) (one_ne_zero : (1 : ZMod p) ≠ 0)
    simpa [AddChar.mulShift_one] using h
  have hsum : ∑ x : ZMod p, (stdAddChar (N := p)) x = 0 := AddChar.sum_eq_zero_of_ne_one hne
  have h1 : ∀ x : ZMod p, (1 : DirichletCharacter ℂ p) x * stdAddChar x =
      stdAddChar x - (if x = 0 then 1 else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [MulChar.map_nonunit _ not_isUnit_zero, zero_mul, AddChar.map_zero_eq_one]
      simp
    · rw [MulChar.one_apply (Ne.isUnit hx), one_mul]
      simp [hx]
  unfold gaussSum
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_sub_distrib, hsum]
  simp

theorem normSq_rootNum_one_prime (p : ℕ) [hp : Fact p.Prime] :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ p)) = 1 / p := by
  have heven : (1 : DirichletCharacter ℂ p).Even := MulChar.one_apply isUnit_neg_one
  have hsq : Complex.normSq (Real.sqrt p : ℂ) = p := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg p)]
  rw [rootNum_eq, parFac_of_even heven, gaussSum_one_prime, one_mul, map_div₀, Complex.normSq_neg,
    Complex.normSq_one, hsq]

theorem not_isPrimitive_one_prime (p : ℕ) [hp : Fact p.Prime] :
    ¬(1 : DirichletCharacter ℂ p).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]
  exact fun h => hp.out.one_lt.ne h

theorem not_isometry_Vimprim_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ f ∈ Vimprim p, ip (TopL f) (TopL f) ≠ ip f f := by
  classical
  refine ⟨charU (N := p) 1,
    Submodule.subset_span ⟨⟨(1 : DirichletCharacter ℂ p), not_isPrimitive_one_prime p⟩, rfl⟩, ?_⟩
  rw [TopL_charU, ip_smul_smul, ip_charU]
  have hn : (starRingEnd ℂ) (rootNum (1 : DirichletCharacter ℂ p)) *
      rootNum (1 : DirichletCharacter ℂ p) = 1 / (p : ℂ) := by
    rw [mul_comm, Complex.mul_conj, normSq_rootNum_one_prime]
    push_cast
    ring
  rw [hn]
  simp only [↓reduceIte]
  have hφ : (Nat.totient p : ℂ) ≠ 0 := by
    rw [Nat.totient_prime hp.out]
    exact_mod_cast (Nat.sub_pos_of_lt hp.out.one_lt).ne'
  have hp1 : (p : ℂ) ≠ 1 := by exact_mod_cast hp.out.one_lt.ne'
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  intro h
  have h2 : (Nat.totient p : ℂ) * (1 / (p : ℂ) - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hφ h3
  · apply hp1
    field_simp at h3
    linear_combination -h3

theorem Vprim_ne_bot_prime (p : ℕ) [hp : Fact p.Prime] (h3 : 3 ≤ p) : Vprim p ≠ ⊥ := by
  have : Fact (2 < p) := ⟨by omega⟩
  obtain ⟨χ, hχ⟩ :=
    DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ (ZMod.neg_one_ne_one (n := p))
  have hne : χ ≠ 1 := by
    rintro rfl
    exact hχ (MulChar.one_apply isUnit_neg_one)
  intro h
  have hmem : charU χ ∈ Vprim p :=
    Submodule.subset_span ⟨⟨χ, PAG.Part256.isPrimitive_of_prime_of_ne_one hne⟩, rfl⟩
  rw [h, Submodule.mem_bot] at hmem
  have h1 := congrFun hmem 1
  simp [charU] at h1

theorem not_isPrimitive_one_of_two_le (hN : 2 ≤ N) : ¬(1 : DirichletCharacter ℂ N).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]
  omega

theorem charU_one_mem_Vimprim (hN : 2 ≤ N) : charU (1 : DirichletCharacter ℂ N) ∈ Vimprim N :=
  Submodule.subset_span ⟨⟨1, not_isPrimitive_one_of_two_le hN⟩, rfl⟩

theorem eq_one_of_two (χ : DirichletCharacter ℂ 2) : χ = 1 := by
  have hcard : Fintype.card (ZMod 2)ˣ ≤ 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_two]
  refine MulChar.ext (fun u => ?_)
  rw [Fintype.card_le_one_iff.mp hcard u 1, Units.val_one, map_one, map_one]

theorem Vprim_two : Vprim 2 = ⊥ := by
  rw [Vprim, Submodule.span_eq_bot]
  rintro _ ⟨⟨χ, hχ⟩, rfl⟩
  have h1 := eq_one_of_two χ
  subst h1
  exact absurd hχ (not_isPrimitive_one_prime 2)

end PAG.Part257

#print axioms PAG.Part257.extL_apply
#print axioms PAG.Part257.extL_charU
#print axioms PAG.Part257.TopL_charU
#print axioms PAG.Part257.ip_smul_smul
#print axioms PAG.Part257.ip_sum_sum
#print axioms PAG.Part257.ip_charU
#print axioms PAG.Part257.TopL_mem_Vprim
#print axioms PAG.Part257.TopL_mem_Vimprim
#print axioms PAG.Part257.rootNum_ne_zero
#print axioms PAG.Part257.map_TopL_Vprim
#print axioms PAG.Part257.ip_TopL_charU_prim
#print axioms PAG.Part257.ip_TopL_of_mem_Vprim
#print axioms PAG.Part257.TopL_eq_of_A1
#print axioms PAG.Part257.ip_Vprim_Vimprim
#print axioms PAG.Part257.ip_sum_right
#print axioms PAG.Part257.linearIndependent_charU
#print axioms PAG.Part257.span_charU_eq_top
#print axioms PAG.Part257.Vprim_sup_Vimprim
#print axioms PAG.Part257.eq_zero_of_ip_self
#print axioms PAG.Part257.Vprim_inf_Vimprim
#print axioms PAG.Part257.isCompl_Vprim_Vimprim
#print axioms PAG.Part257.Vprim_ne_bot_three
#print axioms PAG.Part257.not_isometry_Vimprim_two
#print axioms PAG.Part257.TopL_charU_one_four
#print axioms PAG.Part257.unitary_Vprim
#print axioms PAG.Part257.gaussSum_one_prime
#print axioms PAG.Part257.normSq_rootNum_one_prime
#print axioms PAG.Part257.not_isPrimitive_one_prime
#print axioms PAG.Part257.not_isometry_Vimprim_prime
#print axioms PAG.Part257.Vprim_ne_bot_prime
#print axioms PAG.Part257.not_isPrimitive_one_of_two_le
#print axioms PAG.Part257.charU_one_mem_Vimprim
#print axioms PAG.Part257.eq_one_of_two
#print axioms PAG.Part257.Vprim_two
