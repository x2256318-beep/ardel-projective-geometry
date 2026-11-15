
######## PAG257.lean（Part 253）
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part257
open ZMod Complex Finset PAG.Part256
variable {N : ℕ} [NeZero N]
open Classical in
open Classical in
open Classical in
end PAG.Part257

### 対象 PAG257::JHL（def）
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
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::JH、PAG256::hartley、PAG256::casKer、PAG253::scaleShift、PAG253::primeShiftInv、PAG256::parFac、PAG253::kUnit、PAG98::Equivariant

### 対象 PAG257::TopL（def）
noncomputable def TopL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) := JHL.comp extL
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::JH、PAG256::hartley、PAG256::casKer、PAG253::scaleShift、PAG27::ofRep、PAG25::Eq1、PAG253::primeShiftInv、PAG256::parFac

### 対象 PAG257::TopL_charU（thm）
theorem TopL_charU (χ : DirichletCharacter ℂ N) : TopL (charU χ) = rootNum χ • charU χ
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::JH_eq_rootNum_mul_any、PAG256::JH_eq_rootNum_mul、PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::removal_counterexample_four、PAG256::removal_counterexample、PAG256::hartley_one、PAG256::hartley_eq_of_isPrimitive

### 対象 PAG257::TopL_charU_one_four（thm）
theorem TopL_charU_one_four :
    TopL (charU (1 : DirichletCharacter ℂ 4)) = 0 ∧ charU (1 : DirichletCharacter ℂ 4) ≠ 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::JH_eq_rootNum_mul_any、PAG256::JH_eq_rootNum_mul、PAG256::removal_counterexample、PAG256::removal_counterexample_four、PAG256::hartley_one、PAG256::casKer_eq

### 対象 PAG257::TopL_eq_of_A1（thm）
theorem TopL_eq_of_A1 (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → U (charU χ) = rootNum χ • charU χ)
    {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : U f = TopL f
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::JH_eq_rootNum_mul、PAG256::JH_eq_rootNum_mul_any、PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::removal_counterexample_four、PAG256::removal_counterexample、PAG256::hartley_one、PAG256::hartley_eq_of_isPrimitive

### 対象 PAG257::TopL_mem_Vimprim（thm）
theorem TopL_mem_Vimprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vimprim N) : TopL f ∈ Vimprim N
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::JH_eq_rootNum_mul、PAG256::JH_eq_rootNum_mul_any、PAG256::removal_counterexample、PAG256::hartley_one、PAG256::hartley_eq_of_isPrimitive、PAG256::removal_counterexample_four

### 対象 PAG257::TopL_mem_Vprim（thm）
theorem TopL_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : TopL f ∈ Vprim N
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::JH_eq_rootNum_mul、PAG256::JH_eq_rootNum_mul_any、PAG256::removal_counterexample、PAG256::hartley_one、PAG256::hartley_eq_of_isPrimitive、PAG256::removal_counterexample_four

### 対象 PAG257::Vimprim（def）
noncomputable def Vimprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // ¬χ.IsPrimitive} => charU χ.1)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG98::Equivariant、PAG207::Radial、PAG68::Faithful、PAG218::dil、PAG219::blockSpan、PAG227::Prim、PAG59::EpsSpan、PAG220::layerPart

### 対象 PAG257::Vprim（def）
noncomputable def Vprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.IsPrimitive} => charU χ.1)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG98::Equivariant、PAG207::Radial、PAG68::Faithful、PAG218::dil、PAG219::blockSpan、PAG227::Prim、PAG59::EpsSpan、PAG25::Eq1

### 対象 PAG257::Vprim_inf_Vimprim（thm）
theorem Vprim_inf_Vimprim : Vprim N ⊓ Vimprim N = ⊥
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG220::layerPart_ne_bot、PAG219::not_blockIrreducible_of_dvd、PAG219::blockIrreducible_of_coprime、PAG219::pPart_ne_bot、PAG219::blockIrreducible_iff、PAG220::layerPart_irreducible、PAG223::blockHom_eq_bot_of_ne、PAG224::mem_dilComm

### 対象 PAG257::Vprim_ne_bot_prime（thm）
theorem Vprim_ne_bot_prime (p : ℕ) [hp : Fact p.Prime] (h3 : 3 ≤ p) : Vprim p ≠ ⊥
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG220::layerPart_ne_bot、PAG219::pPart_ne_bot、PAG219::not_blockIrreducible_of_dvd、PAG219::blockIrreducible_of_coprime、PAG219::blockIrreducible_iff、PAG220::layerPart_irreducible、PAG223::blockHom_eq_bot_of_ne、PAG220::block_decomposition

### 対象 PAG257::Vprim_ne_bot_three（thm）
theorem Vprim_ne_bot_three : Vprim 3 ≠ ⊥
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG220::layerPart_ne_bot、PAG219::pPart_ne_bot、PAG219::not_blockIrreducible_of_dvd、PAG219::blockIrreducible_of_coprime、PAG219::blockIrreducible_iff、PAG223::blockHom_eq_bot_of_ne、PAG220::layerPart_irreducible、PAG220::block_decomposition

### 対象 PAG257::Vprim_sup_Vimprim（thm）
theorem Vprim_sup_Vimprim : Vprim N ⊔ Vimprim N = ⊤
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG224::top_shellInvariant、PAG17::AS_sup_AN、PAG211::span_ketFam、PAG54::span_family_eq_top、PAG251::mulLeft_dind_mul_self、PAG248::finrank_sup_add_one、PAG232::sum_mulLeft_dind、PAG249::finrank_sumSub_primePow_add

### 対象 PAG257::Vprim_two（thm）
theorem Vprim_two : Vprim 2 = ⊥
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG220::layerPart_ne_bot、PAG219::not_blockIrreducible_of_dvd、PAG219::blockIrreducible_of_coprime、PAG219::pPart_ne_bot、PAG219::blockIrreducible_iff、PAG220::layerPart_irreducible、PAG223::blockHom_eq_bot_of_ne、PAG120::psi_two_one

### 対象 PAG257::charU（def）
def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG98::Equivariant、PAG207::Radial、PAG68::Faithful、PAG218::dil、PAG25::Eq1、PAG23::extS、PAG23::extN、PAG23::BS

### 対象 PAG257::charU_one_mem_Vimprim（thm）
theorem charU_one_mem_Vimprim (hN : 2 ≤ N) : charU (1 : DirichletCharacter ℂ N) ∈ Vimprim N
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG195::ne_one_of_isPrimitive、PAG135::unit_pow_two、PAG218::radial_iff_mem_span、PAG207::gcd_val_unit_mul、PAG100::char_eq_one_of_units、PAG218::mem_span_iff_dil、PAG218::dil_of_mem_span、PAG207::exists_unit_mul_gcd

### 対象 PAG257::eq_one_of_two（thm）
theorem eq_one_of_two (χ : DirichletCharacter ℂ 2) : χ = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG198::level_two_trivial、PAG256::isPrimitive_of_prime_of_ne_one、PAG171::primitive_of_ne_one、PAG195::ne_one_of_isPrimitive、PAG31::mod4_mul_trivial、PAG187::chi_sq_eight、PAG151::sq_eq_one_mod8、PAG151::sq_eq_one_mod4

### 対象 PAG257::eq_zero_of_ip_self（thm）
theorem eq_zero_of_ip_self (f : (ZMod N)ˣ → ℂ) (h : ip f f = 0) : f = 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG215::inner_conj_symm、PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG213::conj_inv_apply、PAG212::inner_sum_smul_right、PAG212::inner_sum_smul_left、PAG229::conj_dind、PAG39::plancherel

### 対象 PAG257::extL（def）
open Classical in
noncomputable def extL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun g x := if h : IsUnit x then g h.unit else 0
  map_add' f g := by
    funext x
    by_cases h : IsUnit x <;> simp [h]
  map_smul' c f := by
    funext x
    by_cases h : IsUnit x <;> simp [h]
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG27::ofRep、PAG25::Eq1、PAG23::extS、PAG23::extN、PAG27::ofProj、PAG55::VanishNU、PAG98::Equivariant、PAG207::Radial

### 対象 PAG257::extL_apply（thm）
open Classical in
theorem extL_apply (g : (ZMod N)ˣ → ℂ) (x : ZMod N) :
    extL g x = if h : IsUnit x then g h.unit else 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG145::card_units_filter、PAG214::card_isUnit、PAG214::card_isUnit_castHom、PAG218::sum_units_char、PAG244::card_fiber_eq、PAG27::isUnit_units_mul_iff、PAG118::sum_mult_eq_zero、PAG244::card_stab_mul_totient

### 対象 PAG257::extL_charU（thm）
theorem extL_charU (χ : DirichletCharacter ℂ N) : extL (charU χ) = (χ : ZMod N → ℂ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG145::card_units_filter、PAG214::card_isUnit、PAG214::card_isUnit_castHom、PAG218::sum_units_char、PAG244::card_fiber_eq、PAG27::isUnit_units_mul_iff、PAG118::sum_mult_eq_zero、PAG244::card_stab_mul_totient

### 対象 PAG257::gaussSum_one_prime（thm）
theorem gaussSum_one_prime (p : ℕ) [Fact p.Prime] :
    gaussSum (1 : DirichletCharacter ℂ p) (stdAddChar (N := p)) = -1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG198::gaussSum_real、PAG151::phase_mod4、PAG153::orderOf_of_sq_neg_one、PAG172::zeta_quartic_infinite、PAG184::zOf_ne_zero、PAG185::zeta_infinite、PAG185::quintic_not_root、PAG182::sextic_general

### 対象 PAG257::ip（def）
noncomputable def ip (f g : (ZMod N)ˣ → ℂ) : ℂ := ∑ u, (starRingEnd ℂ) (f u) * g u
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG52::ip、PAG229::herm、PAG253::ipG、PAG30::tilde、PAG61::phi、PAG7::push、PAG31::tildeP1、PAG229::adjOp

### 対象 PAG257::ip_TopL_charU_prim（thm）
theorem ip_TopL_charU_prim {χ ψ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ip (TopL (charU χ)) (TopL (charU ψ)) = ip (charU χ) (charU ψ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::JH_eq_rootNum_mul、PAG256::JH_eq_rootNum_mul_any、PAG256::removal_counterexample、PAG256::hartley_one、PAG256::hartley_eq_of_isPrimitive、PAG256::removal_counterexample_four

### 対象 PAG257::ip_TopL_of_mem_Vprim（thm）
theorem ip_TopL_of_mem_Vprim {f g : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) (hg : g ∈ Vprim N) :
    ip (TopL f) (TopL g) = ip f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::JH_eq_rootNum_mul、PAG256::JH_eq_rootNum_mul_any、PAG256::removal_counterexample、PAG256::hartley_one、PAG256::hartley_eq_of_isPrimitive、PAG256::removal_counterexample_four

### 対象 PAG257::ip_Vprim_Vimprim（thm）
theorem ip_Vprim_Vimprim {f g : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) (hg : g ∈ Vimprim N) :
    ip f g = 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG215::inner_conj_symm、PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG218::sum_units_char、PAG213::conj_inv_apply、PAG212::inner_sum_smul_right、PAG212::inner_sum_smul_left、PAG244::card_fiber_eq

### 対象 PAG257::ip_charU（thm）
open Classical in
theorem ip_charU (χ ψ : DirichletCharacter ℂ N) :
    ip (charU χ) (charU ψ) = if χ = ψ then (Nat.totient N : ℂ) else 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG218::sum_units_char、PAG215::inner_conj_symm、PAG244::card_stab_mul_totient、PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG213::conj_inv_apply、PAG212::inner_sum_smul_right、PAG212::inner_sum_smul_left

### 対象 PAG257::ip_smul_smul（thm）
theorem ip_smul_smul (a b : ℂ) (f g : (ZMod N)ˣ → ℂ) :
    ip (a • f) (b • g) = (starRingEnd ℂ) a * b * ip f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG215::inner_conj_symm、PAG212::inner_sum_smul_right、PAG212::inner_sum_smul_left、PAG213::conj_inv_apply、PAG229::conj_dind、PAG39::plancherel

### 対象 PAG257::ip_sum_right（thm）
theorem ip_sum_right {κ : Type*} [Fintype κ] (f : (ZMod N)ˣ → ℂ) (b : κ → ℂ)
    (w : κ → (ZMod N)ˣ → ℂ) : ip (N := N) f (∑ j, b j • w j) = ∑ j, b j * ip f (w j)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG215::inner_conj_symm、PAG212::inner_sum_smul_right、PAG212::inner_sum_smul_left、PAG213::conj_inv_apply、PAG229::conj_dind、PAG39::plancherel

### 対象 PAG257::ip_sum_sum（thm）
theorem ip_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℂ) (v : ι → (ZMod N)ˣ → ℂ)
    (b : κ → ℂ) (w : κ → (ZMod N)ˣ → ℂ) :
    ip (N := N) (∑ i, a i • v i) (∑ j, b j • w j) =
      ∑ i, ∑ j, (starRingEnd ℂ) (a i) * b j * ip (v i) (w j)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG215::inner_conj_symm、PAG212::inner_sum_smul_right、PAG212::inner_sum_smul_left、PAG213::conj_inv_apply、PAG229::conj_dind、PAG39::plancherel

### 対象 PAG257::isCompl_Vprim_Vimprim（thm）
theorem isCompl_Vprim_Vimprim : IsCompl (Vprim N) (Vimprim N)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG229::isCompl_perpSub、PAG220::layerPart_iSupIndep、PAG220::block_decomposition、PAG220::iSup_layerPart、PAG207::gcd_val_unit_mul、PAG207::exists_unit_mul_gcd、PAG211::span_ketFam、PAG219::not_blockIrreducible_of_dvd

### 対象 PAG257::linearIndependent_charU（thm）
theorem linearIndependent_charU :
    LinearIndependent ℂ (fun χ : DirichletCharacter ℂ N => charU χ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG208::gbas_linearIndependent、PAG207::geps_linearIndependent、PAG221::gblock_linearIndependent、PAG207::gcd_val_unit_mul、PAG59::eps_linearIndependent、PAG207::exists_unit_mul_gcd、PAG121::Psi_linearIndependent、PAG233::exists_linearIndependent_subalg

### 対象 PAG257::map_TopL_Vprim（thm）
theorem map_TopL_Vprim : (Vprim N).map TopL = Vprim N
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::JH_eq_rootNum_mul、PAG256::JH_eq_rootNum_mul_any、PAG256::removal_counterexample、PAG256::hartley_one、PAG256::hartley_eq_of_isPrimitive、PAG256::removal_counterexample_four

### 対象 PAG257::normSq_rootNum_one_prime（thm）
theorem normSq_rootNum_one_prime (p : ℕ) [hp : Fact p.Prime] :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ p)) = 1 / p
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::normSq_rootNum、PAG256::removal_counterexample_normSq、PAG199::normSq_chi_natCast、PAG202::normSq_chi_unit、PAG16::normSq_gaussSum、PAG47::normSq_coef_of、PAG117::normSq_inv_neg_one、PAG42::normSq_mixed_coef

### 対象 PAG257::not_isPrimitive_one_of_two_le（thm）
theorem not_isPrimitive_one_of_two_le (hN : 2 ≤ N) : ¬(1 : DirichletCharacter ℂ N).IsPrimitive
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG195::ne_one_of_isPrimitive、PAG200::split_dvd、PAG198::level_two_trivial、PAG30::two_mul_not_prim、PAG30::two_equator_vacuous、PAG30::no_prim_mod_two、PAG256::isPrimitive_of_prime_of_ne_one、PAG171::primitive_of_ne_one

### 対象 PAG257::not_isPrimitive_one_prime（thm）
theorem not_isPrimitive_one_prime (p : ℕ) [hp : Fact p.Prime] :
    ¬(1 : DirichletCharacter ℂ p).IsPrimitive
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::isPrimitive_of_prime_of_ne_one、PAG171::primitive_of_ne_one、PAG198::level_two_trivial、PAG30::no_prim_mod_two、PAG32::prim_level_p_iff、PAG195::ne_one_of_isPrimitive、PAG31::mod4_mul_trivial、PAG85::no_prim_mod2

### 対象 PAG257::not_isometry_Vimprim_prime（thm）
theorem not_isometry_Vimprim_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ f ∈ Vimprim p, ip (TopL f) (TopL f) ≠ ip f f
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::JH_eq_rootNum_mul、PAG256::JH_eq_rootNum_mul_any、PAG256::removal_counterexample、PAG256::hartley_one、PAG256::hartley_eq_of_isPrimitive、PAG256::removal_counterexample_four

### 対象 PAG257::not_isometry_Vimprim_two（thm）
theorem not_isometry_Vimprim_two : ∃ f ∈ Vimprim 2, ip (TopL f) (TopL f) ≠ ip f f
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::removal_counterexample、PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::JH_eq_rootNum_mul、PAG256::JH_eq_rootNum_mul_any、PAG256::hartley_one、PAG256::hartley_eq_of_isPrimitive、PAG256::removal_counterexample_four

### 対象 PAG257::rootNum_ne_zero（thm）
theorem rootNum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : rootNum χ ≠ 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::normSq_rootNum、PAG256::rootNum_eq、PAG256::exists_primitive_even_five、PAG256::removal_counterexample_normSq、PAG256::JH_eq_rootNum_mul、PAG256::JH_eq_rootNum_mul_any、PAG16::gaussSum_ne_zero、PAG152::phase_mod4_eq

### 対象 PAG257::span_charU_eq_top（thm）
theorem span_charU_eq_top :
    Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ N => charU χ) = ⊤
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG224::top_shellInvariant、PAG211::span_ketFam、PAG54::span_family_eq_top、PAG207::gcd_val_unit_mul、PAG239::span_tensorFamily_eq_top、PAG207::exists_unit_mul_gcd、PAG17::AS_sup_AN、PAG253::eq_top_of_prime

### 対象 PAG257::unitary_Vprim（thm）
theorem unitary_Vprim : ∃ e : Vprim N ≃ₗ[ℂ] Vprim N,
    (∀ f : Vprim N, ((e f : Vprim N) : (ZMod N)ˣ → ℂ) = TopL (f : (ZMod N)ˣ → ℂ)) ∧
    ∀ f g : Vprim N, ip ((e f : Vprim N) : (ZMod N)ˣ → ℂ) ((e g : Vprim N) : (ZMod N)ˣ → ℂ) =
      ip (f : (ZMod N)ˣ → ℂ) (g : (ZMod N)ˣ → ℂ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::hartley_units_inv、PAG256::hartley_eq_zero_of_not_isUnit、PAG256::JH_eq_rootNum_mul、PAG256::JH_eq_rootNum_mul_any、PAG256::removal_counterexample、PAG256::hartley_one、PAG256::hartley_eq_of_isPrimitive、PAG256::removal_counterexample_four
