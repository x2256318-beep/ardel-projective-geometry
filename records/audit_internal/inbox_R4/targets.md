
######## PAG258.lean（Part 254）
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part258
open ZMod Complex Finset PAG.Part256 PAG.Part257 DirichletCharacter
variable {N : ℕ} [NeZero N]
end PAG.Part258

### 対象 PAG258::Gsp（def）
abbrev Gsp (a : Lvl) : Type := (ZMod a.val)ˣ → ℂ
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG98::Equivariant、PAG257::charU、PAG207::Radial、PAG253::unitShift、PAG253::scaleShift、PAG68::Faithful、PAG218::dil、PAG257::ip

### 対象 PAG258::Lim（def）
abbrev Lim : Type := Module.DirectLimit Gsp pullSys
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG67::red、PAG37::toFour、PAG210::liftc、PAG232::leftOp、PAG232::rightOp、PAG257::extL、PAG214::gblock、PAG218::blockProjL

### 対象 PAG.Part258.Lvl.pos（thm）
（ソースに独立の宣言がない：構造体のフィールドなど自動で作られたもの）
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG199::pos_of_mul、PAG216::gblock_shell_inj、PAG214::div_mul_div_of_dvd、PAG212::mul_div_div_cancel、PAG204::div_mul_aux、PAG174::not_root_mul、PAG147::eq_of_dvd_not_dvd_div、PAG30::fourLe

### 対象 PAG.Part258.Lvl.val（def）
（ソースに独立の宣言がない：構造体のフィールドなど自動で作られたもの）
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：

### 対象 PAG258::TopL_not_compat（thm）
theorem TopL_not_compat :
    ∃ f : (ZMod 1)ˣ → ℂ, TopL (pullL (one_dvd 2) f) ≠ pullL (one_dvd 2) (TopL f)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::TopL_charU_one_four、PAG257::ip_TopL_charU_prim、PAG257::not_isometry_Vimprim_two、PAG257::TopL_mem_Vprim、PAG257::TopL_mem_Vimprim、PAG257::TopL_charU、PAG257::not_isometry_Vimprim_prime

### 対象 PAG258::TopL_not_compat_prime（thm）
theorem TopL_not_compat_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ f : (ZMod 1)ˣ → ℂ, TopL (pullL (one_dvd p) f) ≠ pullL (one_dvd p) (TopL f)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::TopL_charU_one_four、PAG257::ip_TopL_charU_prim、PAG257::TopL_mem_Vprim、PAG257::TopL_mem_Vimprim、PAG257::TopL_charU、PAG257::not_isometry_Vimprim_prime、PAG257::ip_TopL_of_mem_Vprim

### 対象 PAG258::UA1（def）
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
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::rootNum、PAG257::ip、PAG52::ip、PAG229::herm、PAG257::Vprim、PAG257::Vimprim、PAG253::ipG、PAG257::extL

### 対象 PAG258::UA1_bijective（thm）
theorem UA1_bijective : Function.Bijective (UA1 (N := N))
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::eq_zero_of_ip_self

### 対象 PAG258::UA1_charU（thm）
theorem UA1_charU (χ : DirichletCharacter ℂ N) : UA1 (charU χ) = phaseA1 χ • charU χ
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::eq_zero_of_ip_self

### 対象 PAG258::UA1_charU_eq_pull_TopL（thm）
theorem UA1_charU_eq_pull_TopL (χ : DirichletCharacter ℂ N) :
    UA1 (charU χ) = pullL χ.conductor_dvd_level (TopL (charU χ.primitiveCharacter))
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::TopL_charU、PAG257::ip_TopL_charU_prim、PAG257::TopL_eq_of_A1、PAG257::ip_TopL_of_mem_Vprim、PAG257::TopL_charU_one_four、PAG257::unitary_Vprim、PAG257::not_isometry_Vimprim_prime

### 対象 PAG258::UA1_comp_TopL（thm）
theorem UA1_comp_TopL (f : (ZMod N)ˣ → ℂ) : UA1 (TopL f) = TopL (UA1 f)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::TopL_charU、PAG257::ip_TopL_charU_prim、PAG257::TopL_eq_of_A1、PAG257::ip_TopL_of_mem_Vprim、PAG257::TopL_charU_one_four、PAG257::unitary_Vprim、PAG257::not_isometry_Vimprim_prime

### 対象 PAG258::UA1_comp_pullL（thm）
theorem UA1_comp_pullL {M : ℕ} [NeZero M] (hNM : N ∣ M) (f : (ZMod N)ˣ → ℂ) :
    UA1 (pullL hNM f) = pullL hNM (UA1 f)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::eq_zero_of_ip_self

### 対象 PAG258::UA1_eq_TopL_of_mem_Vprim（thm）
theorem UA1_eq_TopL_of_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f = TopL f
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::TopL_eq_of_A1、PAG257::ip_TopL_of_mem_Vprim、PAG257::unitary_Vprim、PAG257::TopL_charU、PAG257::TopL_mem_Vprim、PAG257::ip_TopL_charU_prim、PAG257::not_isometry_Vimprim_prime、PAG257::not_isometry_Vimprim_two

### 対象 PAG258::UA1_family_unique（thm）
theorem UA1_family_unique (U : ∀ a : Lvl, Gsp a →ₗ[ℂ] Gsp a)
    (hT : ∀ (a : Lvl) (f : Gsp a), f ∈ Vprim a.val → U a f = TopL f)
    (hc : ∀ (a b : Lvl) (h : a ≤ b) (f : Gsp a), U b (pullSys a b h f) = pullSys a b h (U a f))
    (a : Lvl) : U a = UA1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::TopL_eq_of_A1、PAG257::ip_TopL_of_mem_Vprim、PAG257::unitary_Vprim、PAG257::TopL_charU、PAG257::TopL_mem_Vprim、PAG257::ip_TopL_charU_prim、PAG257::not_isometry_Vimprim_prime、PAG257::not_isometry_Vimprim_two

### 対象 PAG258::UA1_mem_Vimprim（thm）
theorem UA1_mem_Vimprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vimprim N) : UA1 f ∈ Vimprim N
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_Vprim_Vimprim、PAG257::ip_charU、PAG257::charU_one_mem_Vimprim、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right

### 対象 PAG258::UA1_mem_Vprim（thm）
theorem UA1_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f ∈ Vprim N
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_Vprim_Vimprim、PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right

### 対象 PAG258::UA1_mem_condPart（thm）
theorem UA1_mem_condPart {q : ℕ} {f : (ZMod N)ˣ → ℂ} (hf : f ∈ condPart N q) :
    UA1 f ∈ condPart N q
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_Vprim_Vimprim、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right

### 対象 PAG258::UA1_ne_TopL_prime（thm）
theorem UA1_ne_TopL_prime (p : ℕ) [hp : Fact p.Prime] :
    charU (1 : DirichletCharacter ℂ p) ∈ Vimprim p ∧
      UA1 (charU (1 : DirichletCharacter ℂ p)) ≠ TopL (charU (1 : DirichletCharacter ℂ p))
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::not_isometry_Vimprim_prime、PAG257::not_isometry_Vimprim_two、PAG257::TopL_charU、PAG257::TopL_mem_Vimprim、PAG257::TopL_eq_of_A1、PAG257::ip_TopL_charU_prim、PAG257::ip_TopL_of_mem_Vprim、PAG257::unitary_Vprim

### 対象 PAG258::UA1_pullL_of_mem_Vprim（thm）
theorem UA1_pullL_of_mem_Vprim {M : ℕ} [NeZero M] (hNM : N ∣ M) {g : (ZMod N)ˣ → ℂ}
    (hg : g ∈ Vprim N) : UA1 (pullL hNM g) = pullL hNM (TopL g)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::TopL_eq_of_A1、PAG257::ip_TopL_of_mem_Vprim、PAG257::unitary_Vprim、PAG257::TopL_charU、PAG257::TopL_mem_Vprim、PAG257::ip_TopL_charU_prim、PAG257::not_isometry_Vimprim_prime、PAG257::not_isometry_Vimprim_two

### 対象 PAG258::UA1_star（thm）
theorem UA1_star (f : (ZMod N)ˣ → ℂ) :
    UA1 (fun u => (starRingEnd ℂ) (f u)) = fun u => (starRingEnd ℂ) (UA1 f u)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::eq_zero_of_ip_self

### 対象 PAG258::UA1_unique（thm）
theorem UA1_unique (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N,
      U (charU χ) = pullL χ.conductor_dvd_level (TopL (charU χ.primitiveCharacter))) :
    U = UA1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::TopL_charU、PAG257::ip_TopL_charU_prim、PAG257::TopL_eq_of_A1、PAG257::ip_TopL_of_mem_Vprim、PAG257::TopL_charU_one_four、PAG257::unitary_Vprim、PAG257::not_isometry_Vimprim_prime

### 対象 PAG258::Uinf（def）
noncomputable def Uinf : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map (fun a => UA1 (N := a.val)) (fun a b h => by
    refine LinearMap.ext (fun f => ?_)
    exact UA1_comp_pullL (N := a.val) (M := b.val) h f)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::rootNum、PAG257::ip、PAG67::red、PAG257::Vimprim、PAG52::ip、PAG229::herm、PAG257::extL、PAG257::Vprim

### 対象 PAG258::Uinf_bijective（thm）
theorem Uinf_bijective : Function.Bijective Uinf
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::eq_zero_of_ip_self

### 対象 PAG258::Uinf_ofL（thm）
theorem Uinf_ofL (a : Lvl) (f : Gsp a) : Uinf (ofL a f) = ofL a (UA1 f)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::eq_zero_of_ip_self

### 対象 PAG258::Uinf_ofL_of_mem_Vprim（thm）
theorem Uinf_ofL_of_mem_Vprim (q : Lvl) {f : Gsp q} (hf : f ∈ Vprim q.val) :
    Uinf (ofL q f) = ofL q (TopL f)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::TopL_eq_of_A1、PAG257::ip_TopL_of_mem_Vprim、PAG257::unitary_Vprim、PAG257::TopL_charU、PAG257::TopL_mem_Vprim、PAG257::ip_TopL_charU_prim、PAG257::not_isometry_Vimprim_prime、PAG257::not_isometry_Vimprim_two

### 対象 PAG258::Uinf_unique（thm）
theorem Uinf_unique (V : Lim →ₗ[ℂ] Lim) (hV : ∀ a (f : Gsp a), V (ofL a f) = ofL a (UA1 f)) :
    V = Uinf
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::eq_zero_of_ip_self

### 対象 PAG258::Uinf_unique_TopL（thm）
theorem Uinf_unique_TopL (V : Lim →ₗ[ℂ] Lim)
    (hV : ∀ q (f : Gsp q), f ∈ Vprim q.val → V (ofL q f) = ofL q (TopL f)) : V = Uinf
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::TopL_eq_of_A1、PAG257::ip_TopL_of_mem_Vprim、PAG257::unitary_Vprim、PAG257::TopL_charU、PAG257::TopL_mem_Vprim、PAG257::ip_TopL_charU_prim、PAG257::not_isometry_Vimprim_prime、PAG257::not_isometry_Vimprim_two

### 対象 PAG258::condPart（def）
noncomputable def condPart (N : ℕ) [NeZero N] (q : ℕ) : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.conductor = q} => charU χ.1)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::Vprim、PAG257::Vimprim、PAG98::Equivariant、PAG257::charU、PAG207::Radial、PAG68::Faithful、PAG218::dil、PAG219::blockSpan

### 対象 PAG258::condPart_eq_map（thm）
theorem condPart_eq_map {M : ℕ} [NeZero M] (hNM : N ∣ M) :
    condPart M N = (Vprim N).map (pullL hNM)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::map_TopL_Vprim、PAG255::units_eq_of_coprime_parts、PAG257::Vprim_ne_bot_prime、PAG257::ip_Vprim_Vimprim、PAG257::Vprim_two、PAG257::Vprim_ne_bot_three、PAG257::Vprim_inf_Vimprim、PAG257::charU_one_mem_Vimprim

### 対象 PAG258::conductor_neZero（thm）
instance conductor_neZero (χ : DirichletCharacter ℂ N) : NeZero χ.conductor :=
  ⟨conductor_ne_zero (χ := χ)⟩


候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG31::conductor_ne_two、PAG64::exists_conductor_pow、PAG47::conductor_eq_pow、PAG47::exists_prim_of_conductor、PAG208::conductor_changeLevel_inv、PAG236::dvd_conductor_of_eq_mul、PAG33::conductor_eq_iff、PAG14::conductor_pow_pn_dvd_p

### 対象 PAG258::eq_zero_of_ipLim_self（thm）
theorem eq_zero_of_ipLim_self (z : Lim) (h : ipLim z z = 0) : z = 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::ip_charU、PAG255::units_eq_of_coprime_parts、PAG195::general_root_iff_units

### 対象 PAG258::gaussSum_inv（thm）
theorem gaussSum_inv (χ : DirichletCharacter ℂ N) :
    gaussSum χ⁻¹ (stdAddChar (N := N)) = χ (-1) * (starRingEnd ℂ) (gaussSum χ stdAddChar)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG9::conj_gaussSum、PAG16::gauss_mul_gauss_inv_eq、PAG173::gauss_inv_pair、PAG212::kcoef_inv、PAG30::star_chi_neg_one、PAG9::inv_apply_neg_one、PAG171::conj_jacobi、PAG9::gauss_mul_gauss_inv_of_norm

### 対象 PAG258::iSupIndep_condPart（thm）
theorem iSupIndep_condPart : iSupIndep (condPart N)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG220::layerPart_iSupIndep、PAG257::isCompl_Vprim_Vimprim、PAG257::charU_one_mem_Vimprim、PAG220::block_decomposition、PAG257::span_charU_eq_top、PAG31::conductor_ne_two、PAG257::linearIndependent_charU、PAG257::Vprim_ne_bot_prime

### 対象 PAG258::iSup_condPart（thm）
theorem iSup_condPart : ⨆ q, condPart N q = ⊤
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::span_charU_eq_top、PAG220::iSup_layerPart、PAG257::Vprim_sup_Vimprim、PAG220::block_decomposition、PAG224::top_shellInvariant、PAG257::isCompl_Vprim_Vimprim、PAG241::range_tpLift、PAG211::span_ketFam

### 対象 PAG258::ipLim（def）
noncomputable def ipLim (z w : Lim) : ℂ :=
  ipn (Module.DirectLimit.exists_of₂ z w).choose_spec.choose
    (Module.DirectLimit.exists_of₂ z w).choose_spec.choose_spec.choose
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip、PAG67::red、PAG52::ip、PAG229::herm、PAG226::layerScalar、PAG253::ipG、PAG216::blockProjG、PAG37::toFour

### 対象 PAG258::ipLim_Uinf（thm）
theorem ipLim_Uinf (z w : Lim) : ipLim (Uinf z) (Uinf w) = ipLim z w
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::eq_zero_of_ip_self

### 対象 PAG258::ipLim_add_right（thm）
theorem ipLim_add_right (z w w' : Lim) : ipLim z (w + w') = ipLim z w + ipLim z w'
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::ip_charU、PAG255::units_eq_of_coprime_parts、PAG195::general_root_iff_units

### 対象 PAG258::ipLim_conj（thm）
theorem ipLim_conj (z w : Lim) : ipLim w z = (starRingEnd ℂ) (ipLim z w)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::ip_charU、PAG255::units_eq_of_coprime_parts、PAG195::general_root_iff_units

### 対象 PAG258::ipLim_ofL（thm）
theorem ipLim_ofL (a : Lvl) (f g : Gsp a) : ipLim (ofL a f) (ofL a g) = ipn f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::ip_charU、PAG255::units_eq_of_coprime_parts、PAG195::general_root_iff_units

### 対象 PAG258::ipLim_ofL_Vprim（thm）
theorem ipLim_ofL_Vprim {q q' : Lvl} (hqq : q.val ≠ q'.val) {f : Gsp q} {g : Gsp q'}
    (hf : f ∈ Vprim q.val) (hg : g ∈ Vprim q'.val) : ipLim (ofL q f) (ofL q' g) = 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_Vprim_Vimprim、PAG257::ip_charU、PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::unitary_Vprim

### 対象 PAG258::ipLim_self_nonneg（thm）
theorem ipLim_self_nonneg (z : Lim) : ∃ r : ℝ, 0 ≤ r ∧ ipLim z z = r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::ip_charU、PAG255::units_eq_of_coprime_parts、PAG89::lam_nonneg

### 対象 PAG258::ipLim_smul_right（thm）
theorem ipLim_smul_right (z w : Lim) (r : ℂ) : ipLim z (r • w) = r * ipLim z w
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::ip_charU、PAG255::units_eq_of_coprime_parts、PAG218::blockProjL_eq_sum_dil

### 対象 PAG258::ipR（def）
noncomputable def ipR (f : (ZMod N)ˣ → ℂ) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ℂ where
  toFun := ip f
  map_add' := ip_add_right f
  map_smul' c g := by rw [ip_smul_right, smul_eq_mul, RingHom.id_apply]
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip、PAG52::ip、PAG229::herm、PAG253::ipG、PAG257::extL、PAG229::adjOp、PAG30::tilde、PAG234::inclY

### 対象 PAG258::ip_UA1（thm）
theorem ip_UA1 (f g : (ZMod N)ˣ → ℂ) : ip (UA1 f) (UA1 g) = ip f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::rootNum_ne_zero、PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::eq_zero_of_ip_self

### 対象 PAG258::ip_add_right（thm）
theorem ip_add_right (f g h : (ZMod N)ˣ → ℂ) : ip f (g + h) = ip f g + ip f h
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG229::herm_add_right、PAG229::herm_add_left、PAG93::conv_add_right'

### 対象 PAG258::ip_condPart（thm）
theorem ip_condPart {q q' : ℕ} (hqq : q ≠ q') {f g : (ZMod N)ˣ → ℂ}
    (hf : f ∈ condPart N q) (hg : g ∈ condPart N q') : ip f g = 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_charU、PAG257::ip_Vprim_Vimprim、PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::charU_one_mem_Vimprim

### 対象 PAG258::ip_pullL（thm）
theorem ip_pullL {M : ℕ} [NeZero M] (hNM : N ∣ M) (f g : (ZMod N)ˣ → ℂ) :
    (Nat.totient N : ℂ) * ip (pullL hNM f) (pullL hNM g) = (Nat.totient M : ℂ) * ip f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::ip_charU、PAG255::units_eq_of_coprime_parts、PAG219::sum_changeLevel_mul_conj

### 対象 PAG258::ip_smul_right（thm）
theorem ip_smul_right (f g : (ZMod N)ˣ → ℂ) (c : ℂ) : ip f (c • g) = c * ip f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::eq_zero_of_ip_self、PAG257::ip_charU、PAG217::inner_smul_left'、PAG208::inner_smul_smul

### 対象 PAG258::ipn（def）
noncomputable def ipn {a : Lvl} (f g : Gsp a) : ℂ := ip f g / (Nat.totient a.val : ℂ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip、PAG52::ip、PAG229::herm、PAG253::ipG、PAG30::tilde、PAG61::phi、PAG7::push、PAG216::blockProjG

### 対象 PAG258::ipn_eq_of_ofL_eq（thm）
theorem ipn_eq_of_ofL_eq {a b : Lvl} {f g : Gsp a} {f' g' : Gsp b}
    (hf : ofL a f = ofL b f') (hg : ofL a g = ofL b g') : ipn f g = ipn f' g'
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::ip_charU、PAG255::units_eq_of_coprime_parts、PAG219::sum_changeLevel_mul_conj

### 対象 PAG258::ipn_pullSys（thm）
theorem ipn_pullSys {a b : Lvl} (h : a ≤ b) (f g : Gsp a) :
    ipn (pullSys a b h f) (pullSys a b h g) = ipn f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::ip_smul_smul、PAG257::eq_zero_of_ip_self、PAG257::ip_sum_sum、PAG257::ip_sum_right、PAG257::ip_charU、PAG255::units_eq_of_coprime_parts、PAG219::sum_changeLevel_mul_conj

### 対象 PAG258::normSq_phaseA1（thm）
theorem normSq_phaseA1 (χ : DirichletCharacter ℂ N) : Complex.normSq (phaseA1 χ) = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::normSq_rootNum、PAG257::normSq_rootNum_one_prime、PAG256::removal_counterexample_normSq、PAG199::normSq_chi_natCast、PAG202::normSq_chi_unit、PAG16::normSq_gaussSum、PAG47::normSq_coef_of

### 対象 PAG258::ofL（def）
noncomputable abbrev ofL (a : Lvl) : Gsp a →ₗ[ℂ] Lim := Module.DirectLimit.of ℂ Lvl Gsp pullSys a
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG67::red、PAG37::toFour、PAG210::liftc、PAG257::extL、PAG232::leftOp、PAG232::rightOp、PAG218::blockProjL、PAG234::restrY

### 対象 PAG258::ofL_charU（thm）
theorem ofL_charU (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
    ofL a (charU χ) =
      ofL ⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩ (charU χ.primitiveCharacter)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG255::units_eq_of_coprime_parts、PAG195::general_root_iff_units、PAG195::factorsThrough_sq_iff_units、PAG257::extL_charU、PAG37::unitsMap_neg_one、PAG47::exists_prim_of_conductor、PAG37::unitsMap_five、PAG9::ker_pow_p

### 対象 PAG258::ofL_injective（thm）
theorem ofL_injective (a : Lvl) : Function.Injective (ofL a)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG255::units_eq_of_coprime_parts、PAG195::general_root_iff_units、PAG37::unitsMap_neg_one、PAG37::unitsMap_five、PAG195::factorsThrough_sq_iff_units、PAG190::exists_nodes、PAG9::ker_pow_p、PAG8::unit_mul_eq_of_ker

### 対象 PAG258::phaseA1（def）
noncomputable def phaseA1 (χ : DirichletCharacter ℂ N) : ℂ := rootNum χ.primitiveCharacter
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::rootNum、PAG196::zN、PAG201::jt、PAG184::zOf、PAG199::thmAConst、PAG222::twistConst、PAG2::Wpow、PAG44::zeta

### 対象 PAG258::phaseA1_changeLevel（thm）
theorem phaseA1_changeLevel {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    phaseA1 (changeLevel hNM χ) = phaseA1 χ
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::rootNum_ne_zero、PAG47::exists_prim_of_conductor、PAG208::conductor_changeLevel_inv、PAG236::dvd_conductor_of_eq_mul、PAG199::changeLevel_natCast、PAG208::changeLevel_inv_injective、PAG256::normSq_rootNum

### 対象 PAG258::phaseA1_inv（thm）
theorem phaseA1_inv (χ : DirichletCharacter ℂ N) :
    phaseA1 χ⁻¹ = (starRingEnd ℂ) (phaseA1 χ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::rootNum_ne_zero、PAG256::normSq_rootNum、PAG257::normSq_rootNum_one_prime、PAG256::rootNum_eq、PAG213::conj_inv_apply、PAG256::removal_counterexample_normSq、PAG215::inner_conj_symm

### 対象 PAG258::phaseA1_of_isPrimitive（thm）
theorem phaseA1_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    phaseA1 χ = rootNum χ
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::rootNum_ne_zero、PAG256::normSq_rootNum、PAG257::normSq_rootNum_one_prime、PAG256::rootNum_eq、PAG256::removal_counterexample_normSq、PAG256::exists_primitive_even_five、PAG256::JH_eq_rootNum_mul

### 対象 PAG258::phaseA1_one（thm）
theorem phaseA1_one : phaseA1 (1 : DirichletCharacter ℂ N) = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::rootNum_ne_zero、PAG256::normSq_rootNum、PAG257::normSq_rootNum_one_prime、PAG256::rootNum_eq、PAG256::removal_counterexample_normSq、PAG256::exists_primitive_even_five、PAG256::JH_eq_rootNum_mul_any

### 対象 PAG258::primitiveCharacter_inv_apply（thm）
theorem primitiveCharacter_inv_apply (χ : DirichletCharacter ℂ N) (a : ℤ) :
    (χ⁻¹).primitiveCharacter a = (χ.primitiveCharacter)⁻¹ a
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG31::conductor_ne_two、PAG18::stdAddChar_scale、PAG198::two_ne_zero_zmod、PAG64::exists_conductor_pow、PAG198::legendre_values、PAG198::odd_base_values、PAG47::conductor_eq_pow、PAG198::neg_one_ne_zero_zmod

### 対象 PAG258::pullL（def）
noncomputable def pullL {M : ℕ} (hNM : N ∣ M) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod M)ˣ → ℂ) where
  toFun f u := f (ZMod.unitsMap hNM u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG67::red、PAG37::toFour、PAG232::leftOp、PAG232::rightOp、PAG234::restrY、PAG234::inclY、PAG257::extL、PAG4::T

### 対象 PAG258::pullL_charU（thm）
omit [NeZero N] in
theorem pullL_charU {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    pullL hNM (charU χ) = charU (changeLevel hNM χ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG255::units_eq_of_coprime_parts、PAG195::factorsThrough_sq_iff_units、PAG199::changeLevel_natCast、PAG208::changeLevel_inv_injective、PAG218::liftc_mul_liftc_inv、PAG231::exists_unit_liftc_ne、PAG208::exists_primitive_changeLevel、PAG203::inv_mul_inv_apply

### 対象 PAG258::pullL_injective（thm）
omit [NeZero N] in
theorem pullL_injective {M : ℕ} [NeZero M] (hNM : N ∣ M) : Function.Injective (pullL hNM)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG255::units_eq_of_coprime_parts、PAG37::unitsMap_neg_one、PAG195::factorsThrough_sq_iff_units、PAG37::unitsMap_five、PAG253::unitsMap_kUnit、PAG195::general_root_iff_units、PAG9::ker_pow_p、PAG8::exists_ker_ne_one_of_primitive

### 対象 PAG258::pullSys（def）
noncomputable def pullSys (a b : Lvl) (h : a ≤ b) : Gsp a →ₗ[ℂ] Gsp b :=
  pullL (N := a.val) (M := b.val) h
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG67::red、PAG37::toFour、PAG232::leftOp、PAG232::rightOp、PAG257::extL、PAG234::restrY、PAG210::liftc、PAG234::inclY

### 対象 PAG258::rootNum_congr（thm）
omit [NeZero N] in
theorem rootNum_congr {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂] (h : d₁ = d₂)
    (χ₁ : DirichletCharacter ℂ d₁) (χ₂ : DirichletCharacter ℂ d₂)
    (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) : rootNum χ₁ = rootNum χ₂
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::rootNum_ne_zero、PAG256::normSq_rootNum、PAG257::normSq_rootNum_one_prime、PAG256::rootNum_eq、PAG256::removal_counterexample_normSq、PAG18::stdAddChar_scale、PAG256::JH_eq_rootNum_mul_any

### 対象 PAG258::rootNum_inv（thm）
theorem rootNum_inv (χ : DirichletCharacter ℂ N) :
    rootNum χ⁻¹ = (starRingEnd ℂ) (rootNum χ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::rootNum_ne_zero、PAG256::normSq_rootNum、PAG257::normSq_rootNum_one_prime、PAG256::rootNum_eq、PAG213::conj_inv_apply、PAG256::removal_counterexample_normSq、PAG215::inner_conj_symm

### 対象 PAG258::rootNum_one_of_eq_one（thm）
omit [NeZero N] in
theorem rootNum_one_of_eq_one {d : ℕ} [NeZero d] (hd : d = 1) :
    rootNum (1 : DirichletCharacter ℂ d) = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::rootNum_ne_zero、PAG256::normSq_rootNum、PAG257::normSq_rootNum_one_prime、PAG256::rootNum_eq、PAG256::removal_counterexample_normSq、PAG256::exists_primitive_even_five、PAG256::JH_eq_rootNum_mul_any

### 対象 PAG258::rootNum_one_prime（thm）
theorem rootNum_one_prime (p : ℕ) [Fact p.Prime] :
    rootNum (1 : DirichletCharacter ℂ p) = -(((Real.sqrt p)⁻¹ : ℝ) : ℂ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::rootNum_ne_zero、PAG257::gaussSum_one_prime、PAG257::normSq_rootNum_one_prime、PAG256::normSq_rootNum、PAG256::removal_counterexample_normSq、PAG256::rootNum_eq、PAG198::gaussSum_real

### 対象 PAG258::span_ofL_Vprim（thm）
theorem span_ofL_Vprim : Submodule.span ℂ (⋃ q : Lvl, ofL q '' (Vprim q.val : Set (Gsp q))) = ⊤
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG257::span_charU_eq_top、PAG257::Vprim_sup_Vimprim、PAG224::top_shellInvariant、PAG257::ip_Vprim_Vimprim、PAG255::units_eq_of_coprime_parts、PAG257::Vprim_ne_bot_prime、PAG257::Vprim_two、PAG257::Vprim_ne_bot_three

### 対象 PAG258::sum_units_unitsMap（thm）
theorem sum_units_unitsMap {M : ℕ} [NeZero M] (hNM : N ∣ M) (F : (ZMod N)ˣ → ℂ) :
    (Nat.totient N : ℂ) * ∑ u : (ZMod M)ˣ, F (ZMod.unitsMap hNM u) =
      (Nat.totient M : ℂ) * ∑ v : (ZMod N)ˣ, F v
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG255::units_eq_of_coprime_parts、PAG37::unitsMap_neg_one、PAG195::factorsThrough_sq_iff_units、PAG37::unitsMap_five、PAG218::sum_units_char、PAG253::unitsMap_kUnit、PAG195::general_root_iff_units、PAG9::ker_pow_p

### 対象 PAG258::totient_ne_zero'（thm）
theorem totient_ne_zero' (a : Lvl) : (Nat.totient a.val : ℂ) ≠ 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG248::not_dvd_two_mul、PAG215::chi_eq_zero_of_rad、PAG247::three_le_div、PAG201::totient_ratio、PAG201::totient_mul_of_primes、PAG214::totient_mul_eq_iff'、PAG214::totient_mul_eq_iff、PAG185::sqrt_ne_zero
