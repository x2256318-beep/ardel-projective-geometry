
######## PAG253.lean（Part 249）
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part253
open Complex PAG.Part218 PAG.Part224
end PAG.Part253

### 対象 PAG253::commSubmonoid（def）
def commSubmonoid {G : Type*} [CommGroup G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ)) : Submonoid G where
  carrier := {g | U ∘ₗ PAG.transl g = PAG.transl g ∘ₗ U}
  one_mem' := by
    show U ∘ₗ PAG.transl 1 = PAG.transl 1 ∘ₗ U
    rw [transl_one, LinearMap.comp_id, LinearMap.id_comp]
  mul_mem' := by
    intro g h hg hh
    have hg' : U ∘ₗ PAG.transl g = PAG.transl g ∘ₗ U := hg
    have hh' : U ∘ₗ PAG.transl h = PAG.transl h ∘ₗ U := hh
    show U ∘ₗ PAG.transl (g * h) = PAG.transl (g * h) ∘ₗ U
    apply LinearMap.ext
    intro f
    have e1 := LinearMap.congr_fun hg' (PAG.transl h f)
    have e2 := LinearMap.congr_fun hh' f
    simp only [LinearMap.comp_apply] at e1 e2
    simp only [transl_mul, LinearMap.comp_apply]
    rw [e1, e2]
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG232::leftOp、PAG210::liftc、PAG232::rightOp、PAG234::restrY、PAG223::blockHomExt、PAG234::inclY、PAG218::blockProjL、PAG4::T

### 対象 PAG253::commute_transl_of_prime（thm）
theorem commute_transl_of_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U)
    (g : (ZMod N)ˣ) : U ∘ₗ PAG.transl g = PAG.transl g ∘ₗ U
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG199::changeLevel_natCast、PAG118::sum_mult_eq_zero、PAG185::powChar_pow、PAG208::changeLevel_inv_injective、PAG218::dft_dil、PAG4::F_comm_M、PAG4::F_comm_T、PAG225::not_commute_of_ne

### 対象 PAG253::conj_eigen_of_adjoint（thm）
theorem conj_eigen_of_adjoint {G : Type*} [CommGroup G] [Fintype G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ))
    (hadj : ∀ f g, ipG (PAG.rev (U (PAG.rev f))) g = ipG f (U g)) (c : (G →* ℂˣ) → ℂ)
    (hc : ∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) (χ : G →* ℂˣ) :
    c χ⁻¹ = starRingEnd ℂ (c χ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG17::glue_identity、PAG17::equator_from_south、PAG11::sum_idempotent_eq_unit、PAG10::Bcv_idempotent、PAG11::Bcv_unit、PAG11::Bcv_idempotent_orthogonal、PAG219::sum_changeLevel_mul_conj、PAG15::ball_avg_absorb'

### 対象 PAG253::eigenFun_of_commute_prime（thm）
theorem eigenFun_of_commute_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U) :
    ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧
      ((∀ χ, ‖c χ‖ = 1) → (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) → ∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG190::norm_z、PAG190::norm_prod_z、PAG219::sum_changeLevel_mul_conj、PAG190::coord_bound、PAG199::changeLevel_natCast、PAG172::quartic_eq_one、PAG231::exists_unit_liftc_ne、PAG208::exists_primitive_changeLevel

### 対象 PAG253::eigen_of_commute_prime（thm）
theorem eigen_of_commute_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U)
    (χ : (ZMod N)ˣ →* ℂˣ) : ∃ c : ℂ, U (PAG.charFun χ) = c • PAG.charFun χ
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG199::changeLevel_natCast、PAG231::exists_unit_liftc_ne、PAG208::exists_primitive_changeLevel、PAG218::liftc_mul_liftc_inv、PAG208::changeLevel_inv_injective、PAG195::factorsThrough_sq_iff_units、PAG37::unitsMap_five、PAG203::inv_mul_inv_apply

### 対象 PAG253::eq_of_euler（thm）
theorem eq_of_euler {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (χ₁ χ₂ : (ZMod N)ˣ →* ℂˣ) (l₁ l₂ : ℝ)
    (h : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M),
      (χ₁ (kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) : ℂ) *
          Complex.exp (-((l₁ * Real.log p : ℝ) : ℂ) * Complex.I) =
        (χ₂ (kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) : ℂ) *
          Complex.exp (-((l₂ * Real.log p : ℝ) : ℂ) * Complex.I)) :
    χ₁ = χ₂ ∧ l₁ = l₂
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG172::quartic_eq_one、PAG37::unitsMap_five、PAG14::lift_invariance、PAG198::gs_combine、PAG153::orderOf_of_sq_neg_one、PAG195::factorsThrough_sq_iff_units、PAG198::gaussSum_real、PAG37::unitsMap_neg_one

### 対象 PAG253::eq_of_prime_invariant（thm）
theorem eq_of_prime_invariant {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (f : (ZMod N)ˣ → ℝ → ℂ)
    (hf : ∀ k, Continuous (f k))
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = f k u)
    (k₁ k₂ : (ZMod N)ˣ) (u₁ u₂ : ℝ) : f k₁ u₁ = f k₂ u₂
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::units_pm5、PAG218::dil_dil、PAG44::pm5_eq_iff、PAG14::lift_invariance、PAG37::pm5_injective、PAG37::pm5_bijective、PAG218::dft_dil、PAG15::radial_column_unitary

### 対象 PAG253::eq_of_prime_invariant'（thm）
theorem eq_of_prime_invariant' {N : ℕ} [NeZero N] (f : (ZMod N)ˣ → ℝ → ℂ) (hf : ∀ k, Continuous (f k))
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p hpN) (u - Real.log p) = f k u)
    (k₁ k₂ : (ZMod N)ˣ) (u₁ u₂ : ℝ) : f k₁ u₁ = f k₂ u₂
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::units_pm5、PAG218::dil_dil、PAG44::pm5_eq_iff、PAG14::lift_invariance、PAG37::pm5_injective、PAG37::pm5_bijective、PAG218::dft_dil、PAG15::radial_column_unitary

### 対象 PAG253::eq_top_of_prime（thm）
theorem eq_top_of_prime {N : ℕ} [NeZero N] (S : Submonoid (ZMod N)ˣ)
    (hS : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N), kUnit p hpN ∈ S) : S = ⊤
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::unitsMap_five、PAG224::top_shellInvariant、PAG14::lift_invariance、PAG218::dft_dil、PAG37::five_two、PAG44::orderOf_five'、PAG37::ker_five、PAG37::orderOf_five_ge3

### 対象 PAG253::exists_cls_near（thm）
theorem exists_cls_near {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (hm : m.Coprime N) (hn : n.Coprime N), 0 < m ∧ 0 < n ∧
      kUnit m hm * (kUnit n hn)⁻¹ = a ∧ |Real.log n - Real.log m - t| < ε
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG112::inj_of_isoOn、PAG51::caseII_target_unique、PAG37::units_pm5、PAG223::eq_of_inLayer_inLayer

### 対象 PAG253::exists_cls_near_of_dvd（thm）
theorem exists_cls_near_of_dvd {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (a : (ZMod N)ˣ) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (hm : m.Coprime M) (hn : n.Coprime M), 0 < m ∧ 0 < n ∧
      kUnit m (Nat.Coprime.coprime_dvd_right hNM hm) * (kUnit n (Nat.Coprime.coprime_dvd_right hNM hn))⁻¹ = a ∧
      |Real.log n - Real.log m - t| < ε
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG112::inj_of_isoOn、PAG51::caseII_target_unique、PAG37::units_pm5、PAG223::eq_of_inLayer_inLayer

### 対象 PAG253::exists_kUnit_eq（thm）
theorem exists_kUnit_eq {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) :
    ∃ (n : ℕ) (h : n.Coprime N), 0 < n ∧ kUnit n h = a
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG223::eq_of_inLayer_inLayer、PAG196::pcomp_aux、PAG14::lift_invariance、PAG199::pos_of_mul、PAG235::inLayer_iff_dvd、PAG187::root_pow_iff、PAG183::root_mul_iff、PAG218::dft_dil

### 対象 PAG253::globalInv（def）
def globalInv {N : ℕ} (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F k⁻¹ (-u)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG98::Equivariant、PAG207::Radial、PAG235::unitRight、PAG235::unitLeft、PAG68::Faithful、PAG218::dil、PAG37::five、PAG30::tilde

### 対象 PAG253::globalInv_globalInv（thm）
theorem globalInv_globalInv {N : ℕ} (F : (ZMod N)ˣ → ℝ → ℂ) : globalInv (globalInv F) = F
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG14::lift_invariance、PAG218::dft_dil、PAG235::crt_unitRight、PAG235::crt_unitLeft、PAG207::gcd_val_unit_mul、PAG207::exists_unit_mul_gcd、PAG37::neg_one_ne_one_four、PAG198::real_val_gen

### 対象 PAG253::globalInv_primeShift_globalInv（thm）
theorem globalInv_primeShift_globalInv {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) :
    globalInv (primeShift p hp (globalInv F)) = primeShiftInv p hp F
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG15::radial_column_unitary、PAG37::units_pm5、PAG14::lift_invariance、PAG44::pm5_eq_iff、PAG218::dil_dil、PAG37::pm5_injective、PAG37::pm5_bijective、PAG44::rep_spec

### 対象 PAG253::globalInv_scaleShift_globalInv（thm）
theorem globalInv_scaleShift_globalInv {N : ℕ} (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) :
    globalInv (scaleShift s (globalInv F)) = scaleShift (-s) F
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG14::lift_invariance、PAG218::dft_dil、PAG15::radial_column_unitary、PAG2::cas_Kl_even、PAG235::crt_unitRight、PAG235::crt_unitLeft、PAG207::gcd_val_unit_mul、PAG2::S_odd

### 対象 PAG253::invariant_cls（thm）
theorem invariant_cls {N M : ℕ} (hNM : N ∣ M) (f : (ZMod N)ˣ → ℝ → ℂ)
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = f k u)
    {m n : ℕ} (hm : m.Coprime M) (hn : n.Coprime M) (hm0 : 0 < m) (hn0 : 0 < n) (k : (ZMod N)ˣ) (u : ℝ) :
    f (k * (kUnit m (Nat.Coprime.coprime_dvd_right hNM hm) * (kUnit n (Nat.Coprime.coprime_dvd_right hNM hn))⁻¹))
      (u + (Real.log n - Real.log m)) = f k u
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG15::radial_column_unitary、PAG37::units_pm5、PAG218::dil_dil、PAG44::pm5_eq_iff、PAG14::lift_invariance、PAG37::pm5_injective、PAG199::pos_of_mul、PAG196::pcomp_aux

### 対象 PAG253::invariant_kUnit（thm）
theorem invariant_kUnit {N M : ℕ} (hNM : N ∣ M) (f : (ZMod N)ˣ → ℝ → ℂ)
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = f k u) :
    ∀ (n : ℕ) (hn : n.Coprime M), 0 < n → ∀ (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit n (Nat.Coprime.coprime_dvd_right hNM hn)) (u - Real.log n) = f k u
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::units_pm5、PAG218::dil_dil、PAG44::pm5_eq_iff、PAG14::lift_invariance、PAG37::pm5_injective、PAG199::pos_of_mul、PAG196::pcomp_aux、PAG37::pm5_bijective

### 対象 PAG253::ipG（def）
noncomputable def ipG {G : Type*} [Fintype G] (f g : G → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG52::ip、PAG229::herm、PAG30::tilde、PAG31::tildeP1、PAG216::blockProjG、PAG226::layerScalar、PAG229::AdjClosed、PAG229::adjOp

### 対象 PAG253::ipG_charFun_self_ne_zero（thm）
theorem ipG_charFun_self_ne_zero {G : Type*} [CommGroup G] [Fintype G] (χ : G →* ℂˣ) :
    ipG (PAG.charFun χ) (PAG.charFun χ) ≠ 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG219::sum_changeLevel_mul_conj、PAG231::exists_unit_liftc_ne、PAG51::prim_not_changeLevel、PAG218::liftc_mul_liftc_inv、PAG199::changeLevel_natCast、PAG215::inner_conj_symm、PAG208::changeLevel_inv_injective、PAG219::inner_gblock_one_dft_ne_zero

### 対象 PAG253::ipG_smul_left（thm）
theorem ipG_smul_left {G : Type*} [Fintype G] (a : ℂ) (f g : G → ℂ) :
    ipG (a • f) g = starRingEnd ℂ a * ipG f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG215::inner_conj_symm、PAG212::inner_sum_smul_right、PAG212::inner_sum_smul_left、PAG213::conj_inv_apply、PAG229::conj_dind、PAG39::plancherel

### 対象 PAG253::ipG_smul_right（thm）
theorem ipG_smul_right {G : Type*} [Fintype G] (a : ℂ) (f g : G → ℂ) :
    ipG f (a • g) = a * ipG f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG215::inner_conj_symm、PAG212::inner_sum_smul_right、PAG212::inner_sum_smul_left、PAG213::conj_inv_apply、PAG229::conj_dind、PAG39::plancherel

### 対象 PAG253::kUnit（def）
def kUnit {N : ℕ} (n : ℕ) (h : n.Coprime N) : (ZMod N)ˣ := (ZMod.unitOfCoprime n h)⁻¹
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::five、PAG235::unitRight、PAG235::unitLeft、PAG37::pm5、PAG98::Equivariant、PAG207::Radial、PAG220::InLayer、PAG44::rep

### 対象 PAG253::kUnit_mem_of_prime（thm）
theorem kUnit_mem_of_prime {N : ℕ} (S : Submonoid (ZMod N)ˣ)
    (hS : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N), kUnit p hpN ∈ S) :
    ∀ (n : ℕ) (hn : n.Coprime N), kUnit n hn ∈ S
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::unitsMap_five、PAG14::lift_invariance、PAG218::dft_dil、PAG37::five_two、PAG44::orderOf_five'、PAG37::ker_five、PAG37::orderOf_five_ge3、PAG37::orderOf_five

### 対象 PAG253::kUnit_mul（thm）
theorem kUnit_mul {N : ℕ} {a b : ℕ} (ha : a.Coprime N) (hb : b.Coprime N) (hab : (a * b).Coprime N) :
    kUnit (a * b) hab = kUnit a ha * kUnit b hb
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::units_pm5、PAG218::dil_dil、PAG44::pm5_eq_iff、PAG14::lift_invariance、PAG37::pm5_injective、PAG37::pm5_bijective、PAG218::dft_dil、PAG37::five_two

### 対象 PAG253::kUnit_mul_natCast（thm）
theorem kUnit_mul_natCast {N : ℕ} (n : ℕ) (h : n.Coprime N) :
    ((kUnit n h : (ZMod N)ˣ) : ZMod N) * (n : ZMod N) = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG14::lift_invariance、PAG218::dft_dil、PAG207::gcd_val_unit_mul、PAG135::unit_pow_two、PAG207::exists_unit_mul_gcd、PAG37::five_pow_val、PAG37::five_two、PAG44::orderOf_five'

### 対象 PAG253::kUnit_one（thm）
theorem kUnit_one {N : ℕ} (h : (1 : ℕ).Coprime N) : kUnit 1 h = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::five_two、PAG187::units_eight_sq、PAG37::units_pm5、PAG218::dil_one、PAG37::neg_one_ne_one_four、PAG14::lift_invariance、PAG44::pm5_eq_iff、PAG37::toFour_five

### 対象 PAG253::mem_dilCommute_of_prime（thm）
theorem mem_dilCommute_of_prime {N : ℕ} [NeZero N] (T : Module.End ℂ (ZMod N → ℂ))
    (hT : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N) (f : ZMod N → ℂ),
      T (dil (kUnit p hpN) f) = dil (kUnit p hpN) (T f)) :
    T ∈ dilCommute N
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG224::mem_dilCommute、PAG224::mem_dilComm、PAG225::dilComm_commute、PAG225::dilCommute_preserves、PAG235::finrank_dilComm_mul、PAG224::finrank_dilComm、PAG224::finrank_dilComm_eq_sum、PAG224::blockHomExt_mem_dilCommute

### 対象 PAG253::norm_eq_one_of_isometry（thm）
theorem norm_eq_one_of_isometry {G : Type*} [CommGroup G] [Fintype G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ))
    (hiso : ∀ f g, ipG (U f) (U g) = ipG f g) (χ : G →* ℂˣ) {c : ℂ}
    (hc : U (PAG.charFun χ) = c • PAG.charFun χ) : ‖c‖ = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG190::norm_z、PAG190::norm_prod_z、PAG219::sum_changeLevel_mul_conj、PAG190::coord_bound、PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG218::liftc_mul_liftc_inv、PAG199::changeLevel_natCast

### 対象 PAG253::primeShift（def）
noncomputable def primeShift {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ :=
  fun k u => F (k * kUnit p hp) (u - Real.log p)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::five、PAG37::pm5、PAG44::rep、PAG44::val、PAG44::unitHom、PAG44::chiSJ、PAG235::unitRight、PAG235::unitLeft

### 対象 PAG253::primeShiftInv（def）
noncomputable def primeShiftInv {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ :=
  fun k u => F (k * (kUnit p hp)⁻¹) (u + Real.log p)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::five、PAG37::pm5、PAG44::rep、PAG2::cas、PAG44::val、PAG44::unitHom、PAG44::chiSJ、PAG235::unitRight

### 対象 PAG253::primeShift_eq（thm）
theorem primeShift_eq {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) :
    primeShift p hp F = unitShift (kUnit p hp) (scaleShift (-Real.log p) F)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG15::radial_column_unitary、PAG37::units_pm5、PAG14::lift_invariance、PAG44::pm5_eq_iff、PAG218::dil_dil、PAG37::pm5_injective、PAG37::pm5_bijective、PAG44::rep_spec

### 対象 PAG253::primeShift_primeShiftInv（thm）
theorem primeShift_primeShiftInv {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) :
    primeShift p hp (primeShiftInv p hp F) = F
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG15::radial_column_unitary、PAG37::units_pm5、PAG218::dil_dil、PAG44::pm5_eq_iff、PAG14::lift_invariance、PAG37::pm5_injective、PAG37::pm5_bijective、PAG218::dft_dil

### 対象 PAG253::primeShift_scaleShift（thm）
theorem primeShift_scaleShift {N : ℕ} (p : ℕ) (hp : p.Coprime N) (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) :
    primeShift p hp (scaleShift s F) = scaleShift s (primeShift p hp F)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG15::radial_column_unitary、PAG37::units_pm5、PAG218::dil_dil、PAG44::pm5_eq_iff、PAG14::lift_invariance、PAG37::pm5_injective、PAG37::pm5_bijective、PAG218::dft_dil

### 対象 PAG253::scaleShift（def）
def scaleShift {N : ℕ} (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F k (u + s)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG2::cas、PAG98::Equivariant、PAG207::Radial、PAG68::Faithful、PAG218::dil、PAG37::five、PAG61::phi、PAG25::Eq1

### 対象 PAG253::shift_invariant_of_prime_invariant（thm）
theorem shift_invariant_of_prime_invariant {N : ℕ} [NeZero N] (F : (ZMod N)ˣ → ℝ → ℂ)
    (hF : ∀ k, Continuous (F k))
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N), primeShift p hpN F = F)
    (a : (ZMod N)ˣ) (s : ℝ) : unitShift a F = F ∧ scaleShift s F = F
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG15::radial_column_unitary、PAG37::units_pm5、PAG218::dil_dil、PAG44::pm5_eq_iff、PAG14::lift_invariance、PAG37::pm5_injective、PAG37::pm5_bijective、PAG218::dft_dil

### 対象 PAG253::signMul（def）
noncomputable def signMul {G : Type*} [Group G] [DecidableEq G] : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f g := (if g = 1 then (1 : ℂ) else -1) * f g
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG10::ind、PAG15::ballAvg、PAG232::leftOp、PAG232::rightOp、PAG234::restrY、PAG227::decEqPrim、PAG234::inclY、PAG4::T

### 対象 PAG253::signMul_adjoint（thm）
theorem signMul_adjoint {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G] (f g : G → ℂ) :
    ipG (PAG.rev (signMul (PAG.rev f))) g = ipG f (signMul g)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG11::sum_idempotent_eq_unit、PAG11::Bcv_idempotent_orthogonal、PAG17::glue_identity、PAG17::equator_from_south、PAG10::Bcv_idempotent、PAG11::Bcv_unit、PAG15::ball_avg_absorb'、PAG15::ball_avg_absorb

### 対象 PAG253::signMul_apply（thm）
theorem signMul_apply {G : Type*} [Group G] [DecidableEq G] (f : G → ℂ) (g : G) :
    signMul f g = (if g = 1 then (1 : ℂ) else -1) * f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG11::sum_idempotent_eq_unit、PAG11::Bcv_idempotent_orthogonal、PAG17::glue_identity、PAG17::equator_from_south、PAG153::orderOf_of_sq_neg_one、PAG10::Bcv_idempotent、PAG11::Bcv_unit、PAG118::sum_mult_eq_zero

### 対象 PAG253::signMul_isometry（thm）
theorem signMul_isometry {G : Type*} [Group G] [DecidableEq G] [Fintype G] (f g : G → ℂ) :
    ipG (signMul f) (signMul g) = ipG f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG215::inner_conj_symm、PAG11::sum_idempotent_eq_unit、PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG11::Bcv_idempotent_orthogonal、PAG213::conj_inv_apply、PAG212::inner_sum_smul_right、PAG212::inner_sum_smul_left

### 対象 PAG253::signMul_not_commute（thm）
theorem signMul_not_commute {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    ¬ ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      (signMul : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) ∘ₗ PAG.transl (kUnit p hpN) =
        PAG.transl (kUnit p hpN) ∘ₗ signMul
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG11::sum_idempotent_eq_unit、PAG11::Bcv_idempotent_orthogonal、PAG17::glue_identity、PAG17::equator_from_south、PAG118::sum_mult_eq_zero、PAG199::changeLevel_natCast、PAG153::orderOf_of_sq_neg_one、PAG10::pow_isPrimitive_of_coprime

### 対象 PAG253::thm26_full（thm）
theorem thm26_full {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U)
    (hiso : ∀ f g, ipG (U f) (U g) = ipG f g)
    (hadj : ∀ f g, ipG (PAG.rev (U (PAG.rev f))) g = ipG f (U g)) :
    ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧ (∀ χ, ‖c χ‖ = 1) ∧
      (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) ∧ (∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG17::glue_identity、PAG17::equator_from_south、PAG190::norm_z、PAG11::sum_idempotent_eq_unit、PAG10::Bcv_idempotent、PAG11::Bcv_unit、PAG11::Bcv_idempotent_orthogonal、PAG190::norm_prod_z

### 対象 PAG253::thm26_full_hyp_transl（thm）
theorem thm26_full_hyp_transl {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) :
    (∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      PAG.transl h ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ PAG.transl h) ∧
    (∀ f g, ipG (PAG.transl h f) (PAG.transl h g) = ipG f g) ∧
    (∀ f g, ipG (PAG.rev (PAG.transl h (PAG.rev f))) g = ipG f (PAG.transl h g))
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG17::glue_identity、PAG17::equator_from_south、PAG11::sum_idempotent_eq_unit、PAG10::Bcv_idempotent、PAG11::Bcv_unit、PAG11::Bcv_idempotent_orthogonal、PAG15::ball_avg_absorb'、PAG15::ball_avg_absorb

### 対象 PAG253::thm26_full_of_commute（thm）
theorem thm26_full_of_commute {G : Type*} [CommGroup G] [Fintype G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ))
    (hU : ∀ h, U ∘ₗ PAG.transl h = PAG.transl h ∘ₗ U)
    (hiso : ∀ f g, ipG (U f) (U g) = ipG f g)
    (hadj : ∀ f g, ipG (PAG.rev (U (PAG.rev f))) g = ipG f (U g)) :
    ∃ c : (G →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧ (∀ χ, ‖c χ‖ = 1) ∧
      (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) ∧ (∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG17::glue_identity、PAG17::equator_from_south、PAG190::norm_z、PAG11::sum_idempotent_eq_unit、PAG10::Bcv_idempotent、PAG11::Bcv_unit、PAG11::Bcv_idempotent_orthogonal、PAG190::norm_prod_z

### 対象 PAG253::thm26_needs_adjoint（thm）
theorem thm26_needs_adjoint {N : ℕ} [NeZero N] :
    (∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      (Complex.I • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) ∘ₗ PAG.transl (kUnit p hpN) =
        PAG.transl (kUnit p hpN) ∘ₗ (Complex.I • LinearMap.id)) ∧
    (∀ f g : (ZMod N)ˣ → ℂ, ipG ((Complex.I • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) f)
        ((Complex.I • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) g) = ipG f g) ∧
    ¬ ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ,
      (∀ χ, (Complex.I • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) (PAG.charFun χ) =
        c χ • PAG.charFun χ) ∧ (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ))
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG251::leftOp_smul'、PAG234::leftOp_sum_smul、PAG234::rightOp_sum_smul、PAG218::blockProjL_eq_sum_dil、PAG234::exists_basis_subalg、PAG251::convL_geps_self_mul_mulLeft_dind_self、PAG4::heisenberg_unique、PAG227::matUnit_mul_matSum_mul_matUnit

### 対象 PAG253::thm26_needs_commute（thm）
theorem thm26_needs_commute {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    (∀ f g : (ZMod N)ˣ → ℂ, ipG (signMul f) (signMul g) = ipG f g) ∧
    (∀ f g : (ZMod N)ˣ → ℂ, ipG (PAG.rev (signMul (PAG.rev f))) g = ipG f (signMul g)) ∧
    ¬ ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, ∀ χ, signMul (PAG.charFun χ) = c χ • PAG.charFun χ
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG11::sum_idempotent_eq_unit、PAG11::Bcv_idempotent_orthogonal、PAG17::glue_identity、PAG17::equator_from_south、PAG10::Bcv_idempotent、PAG11::Bcv_unit、PAG219::sum_changeLevel_mul_conj、PAG15::ball_avg_absorb'

### 対象 PAG253::thm26_needs_isometry（thm）
theorem thm26_needs_isometry {N : ℕ} [NeZero N] :
    (∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      ((2 : ℂ) • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) ∘ₗ PAG.transl (kUnit p hpN) =
        PAG.transl (kUnit p hpN) ∘ₗ ((2 : ℂ) • LinearMap.id)) ∧
    (∀ f g : (ZMod N)ˣ → ℂ,
      ipG (PAG.rev (((2 : ℂ) • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) (PAG.rev f))) g =
        ipG f (((2 : ℂ) • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) g)) ∧
    ¬ ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ,
      (∀ χ, ((2 : ℂ) • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) (PAG.charFun χ) =
        c χ • PAG.charFun χ) ∧ (∀ χ, ‖c χ‖ = 1)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG251::leftOp_smul'、PAG234::leftOp_sum_smul、PAG234::rightOp_sum_smul、PAG17::glue_identity、PAG17::equator_from_south、PAG218::blockProjL_eq_sum_dil、PAG234::exists_basis_subalg、PAG251::convL_geps_of_two_mul

### 対象 PAG253::transl_adjoint（thm）
theorem transl_adjoint {G : Type*} [CommGroup G] [Fintype G] (h : G) (f g : G → ℂ) :
    ipG (PAG.rev (PAG.transl h (PAG.rev f))) g = ipG f (PAG.transl h g)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG17::glue_identity、PAG17::equator_from_south、PAG11::sum_idempotent_eq_unit、PAG10::Bcv_idempotent、PAG11::Bcv_unit、PAG11::Bcv_idempotent_orthogonal、PAG15::ball_avg_absorb'、PAG15::ball_avg_absorb

### 対象 PAG253::transl_charFun（thm）
theorem transl_charFun {G : Type*} [CommGroup G] (h : G) (χ : G →* ℂˣ) :
    PAG.transl h (PAG.charFun χ) = ((χ h : ℂˣ) : ℂ) • PAG.charFun χ
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG218::liftc_mul_liftc_inv、PAG199::changeLevel_natCast、PAG231::exists_unit_liftc_ne、PAG208::changeLevel_inv_injective、PAG195::factorsThrough_sq_iff_units、PAG208::exists_primitive_changeLevel、PAG203::inv_mul_inv_apply、PAG51::prim_not_changeLevel

### 対象 PAG253::transl_isometry（thm）
theorem transl_isometry {G : Type*} [CommGroup G] [Fintype G] (h : G) (f g : G → ℂ) :
    ipG (PAG.transl h f) (PAG.transl h g) = ipG f g
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG219::sum_changeLevel_mul_conj、PAG215::inner_conj_symm、PAG217::inner_smul_left'、PAG208::inner_smul_smul、PAG213::conj_inv_apply、PAG212::inner_sum_smul_right、PAG212::inner_sum_smul_left、PAG229::conj_dind

### 対象 PAG253::transl_mul（thm）
theorem transl_mul {G : Type*} [CommGroup G] (g h : G) :
    PAG.transl (g * h) = PAG.transl g ∘ₗ PAG.transl h
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG118::sum_mult_eq_zero、PAG199::changeLevel_natCast、PAG208::changeLevel_inv_injective、PAG4::F_comm_M、PAG4::F_comm_T、PAG208::exists_primitive_changeLevel、PAG203::inv_mul_inv_apply、PAG51::prim_not_changeLevel

### 対象 PAG253::transl_one（thm）
theorem transl_one {G : Type*} [CommGroup G] : PAG.transl (1 : G) = LinearMap.id
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG17::glue_identity、PAG17::equator_from_south、PAG10::Bcv_idempotent、PAG11::sum_idempotent_eq_unit、PAG11::Bcv_unit、PAG11::Bcv_idempotent_orthogonal、PAG15::ball_avg_absorb'、PAG15::ball_avg_absorb

### 対象 PAG253::unitShift（def）
def unitShift {N : ℕ} (a : (ZMod N)ˣ) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F (k * a) u
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::pm5、PAG44::rep、PAG98::Equivariant、PAG207::Radial、PAG44::val、PAG44::unitHom、PAG44::chiSJ、PAG68::Faithful

### 対象 PAG253::unitShift_scaleShift（thm）
theorem unitShift_scaleShift {N : ℕ} (a : (ZMod N)ˣ) (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) :
    unitShift a (scaleShift s F) = scaleShift s (unitShift a F)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG218::dil_dil、PAG37::units_pm5、PAG15::radial_column_unitary、PAG44::pm5_eq_iff、PAG37::pm5_injective、PAG37::pm5_bijective、PAG44::rep_spec、PAG2::cas_Kl_even

### 対象 PAG253::unitsMap_kUnit（thm）
theorem unitsMap_kUnit {N M : ℕ} (hNM : N ∣ M) (n : ℕ) (hM : n.Coprime M) :
    ZMod.unitsMap hNM (kUnit n hM) = kUnit n (Nat.Coprime.coprime_dvd_right hNM hM)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::unitsMap_five、PAG37::unitsMap_neg_one、PAG195::factorsThrough_sq_iff_units、PAG37::toFour_five、PAG195::general_root_iff_units、PAG9::ker_pow_p、PAG8::exists_ker_ne_one_of_primitive、PAG133::exists_ker_ne

######## PAG254.lean（Part 250）
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part254
end PAG.Part254

### 対象 PAG254::abs_log_sub_log_le（thm）
theorem abs_log_sub_log_le {x y m : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / m
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG89::lam_nonneg、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG7::W_sq、PAG112::inj_of_isoOn

### 対象 PAG254::chainIn（def）
def chainIn {α : Type*} (S : Set α) (d : α → α → ℝ) (ε : ℝ) (x y : α) : Prop :=
  ∃ (n : ℕ) (c : ℕ → α), c 0 = x ∧ c n = y ∧ (∀ i, i ≤ n → c i ∈ S) ∧ ∀ i, i < n → d (c i) (c (i + 1)) < ε
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG58::Good、PAG55::familyBasis、PAG17::AS、PAG14::epsBall、PAG220::InLayer、PAG54::family、PAG93::Bset、PAG95::Va

### 対象 PAG254::chainIn_dInf（thm）
theorem chainIn_dInf {ε : ℝ} (hε : 0 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat dInf ε q r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG253::invariant_kUnit、PAG51::caseII_target_unique

### 対象 PAG254::chainIn_dP_classification（thm）
theorem chainIn_dP_classification (p : ℕ) [Fact p.Prime] {ε : ℝ} (hε0 : 0 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat (dP p) ε q r ↔ (ε ≤ 1 → padicValRat p q = padicValRat p r)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG89::lam_nonneg、PAG7::W_sq、PAG187::root_pow_iff

### 対象 PAG254::chainIn_dP_iff（thm）
theorem chainIn_dP_iff (p : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat (dP p) ε q r ↔ padicValRat p q = padicValRat p r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG89::lam_nonneg、PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG187::root_pow_iff

### 対象 PAG254::chainIn_dP_of_one_lt（thm）
theorem chainIn_dP_of_one_lt (p : ℕ) [hp : Fact p.Prime] {ε : ℝ} (hε : 1 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat (dP p) ε q r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG249::ineq_odd、PAG185::aux_ineq、PAG30::fourLe、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos

### 対象 PAG254::chainIn_invariant（thm）
theorem chainIn_invariant {α β : Type*} {S : Set α} {d : α → α → ℝ} {ε : ℝ} (f : α → β)
    (hf : ∀ x y, x ∈ S → y ∈ S → d x y < ε → f x = f y) {x y : α} (hc : chainIn S d ε x y) :
    f x = f y
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG249::ineq_odd、PAG185::aux_ineq、PAG30::fourLe、PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG146::twist_digit_uniform

### 対象 PAG254::chainIn_mono（thm）
theorem chainIn_mono {α : Type*} {S : Set α} {d : α → α → ℝ} {ε ε' : ℝ} (h : ε ≤ ε') {x y : α}
    (hc : chainIn S d ε x y) : chainIn S d ε' x y
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG249::ineq_odd、PAG185::aux_ineq、PAG30::fourLe、PAG89::lam_nonneg、PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos

### 対象 PAG254::chainIn_of_lt（thm）
theorem chainIn_of_lt {α : Type*} {S : Set α} {d : α → α → ℝ} {ε : ℝ} {x y : α} (hx : x ∈ S) (hy : y ∈ S)
    (h : d x y < ε) : chainIn S d ε x y
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG249::ineq_odd、PAG185::aux_ineq、PAG30::fourLe、PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG146::twist_digit_uniform

### 対象 PAG254::chainIn_refl（thm）
theorem chainIn_refl {α : Type*} {S : Set α} (d : α → α → ℝ) (ε : ℝ) {x : α} (hx : x ∈ S) :
    chainIn S d ε x x
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG249::ineq_odd、PAG185::aux_ineq、PAG30::fourLe、PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG146::twist_digit_uniform

### 対象 PAG254::dInf（def）
noncomputable def dInf (q r : ℚ) : ℝ := |Real.log q - Real.log r|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::primeShift、PAG176::InQi、PAG176::InQω、PAG253::primeShiftInv

### 対象 PAG254::dInf_eq_dist（thm）
theorem dInf_eq_dist (q r : ℚ) : dInf q r = dist (Real.log q) (Real.log r)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG253::invariant_kUnit、PAG253::eq_of_prime_invariant'、PAG253::invariant_cls、PAG179::InQi_one、PAG176::InQi_pow、PAG176::InQi_mul

### 対象 PAG254::dInf_mul_left（thm）
theorem dInf_mul_left {s q r : ℚ} (hs : 0 < s) (hq : 0 < q) (hr : 0 < r) :
    dInf (s * q) (s * r) = dInf q r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG253::invariant_kUnit、PAG253::invariant_cls、PAG179::InQi_one、PAG176::InQi_pow、PAG176::InQi_mul、PAG179::InQi_prod

### 対象 PAG254::dInf_zpow（thm）
theorem dInf_zpow {p : ℕ} (a b : ℤ) :
    dInf ((p : ℚ) ^ a) ((p : ℚ) ^ b) = |((a - b : ℤ) : ℝ)| * |Real.log p|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG253::invariant_kUnit、PAG171::not_root_of_trace、PAG253::invariant_cls、PAG179::InQi_one、PAG176::InQi_pow、PAG176::InQi_mul

### 対象 PAG254::dP（def）
noncomputable def dP (p : ℕ) (q r : ℚ) : ℝ := |((padicValRat p q - padicValRat p r : ℤ) : ℝ)|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG9::D、PAG178::Tlin4、PAG177::Tlin、PAG175::T4、PAG174::Tpoly、PAG176::InQi、PAG176::InQω、PAG172::InZi

### 対象 PAG254::dP_eq_dist（thm）
theorem dP_eq_dist (p : ℕ) (q r : ℚ) :
    dP p q r = dist ((padicValRat p q : ℤ) : ℝ) ((padicValRat p r : ℤ) : ℝ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG247::abs_ramSum_primePow_le、PAG9::D_comp、PAG178::trace_lin4、PAG244::sum_divisors_primePow_moebius_int、PAG171::not_root_of_trace、PAG175::trace4_identity

### 対象 PAG254::dP_lt_one_iff（thm）
theorem dP_lt_one_iff (p : ℕ) (q r : ℚ) : dP p q r < 1 ↔ padicValRat p q = padicValRat p r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG189::toZMod_eq_zero_iff、PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG212::dvd_div_iff_dvd

### 対象 PAG254::dP_mul_left（thm）
theorem dP_mul_left (p : ℕ) [Fact p.Prime] {s q r : ℚ} (hs : s ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    dP p (s * q) (s * r) = dP p q r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG185::sqrt_ne_zero、PAG247::abs_ramSum_primePow_le、PAG171::not_root_of_trace、PAG9::D_comp、PAG178::trace_lin4、PAG244::sum_divisors_primePow_moebius_int

### 対象 PAG254::dense_closure_log_two_three（thm）
theorem dense_closure_log_two_three :
    Dense ((AddSubgroup.closure ({Real.log 2, Real.log 3} : Set ℝ) : AddSubgroup ℝ) : Set ℝ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG120::quad_root_two、PAG45::five_pow_M、PAG15::cardH_pos、PAG37::prim_iff_five、PAG152::five_mod8、PAG152::gauss_mod4、PAG45::char_ext、PAG253::eq_of_prime_invariant'

### 対象 PAG254::dense_logSet（thm）
theorem dense_logSet : Dense logSet
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::eq_of_prime_invariant'、PAG253::eq_of_prime_invariant、PAG253::shift_invariant_of_prime_invariant、PAG179::InQi_one、PAG176::InQi_pow、PAG176::InQi_mul、PAG179::InQi_prod、PAG179::InQi_conj

### 対象 PAG254::dense_logSet_coprime（thm）
theorem dense_logSet_coprime {N : ℕ} [NeZero N] (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧ m.Coprime N ∧ n.Coprime N ∧ |Real.log n - Real.log m - t| < ε
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG253::invariant_kUnit、PAG253::invariant_cls

### 対象 PAG254::emergence_contrast（thm）
theorem emergence_contrast :
    (∀ ε : ℝ, 0 < ε → ∀ q r : ℚ, 0 < q → 0 < r → chainIn posRat dInf ε q r) ∧
    (∀ p : ℕ, p.Prime → ¬ chainIn posRat (dP p) 1 1 (p : ℚ))
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG15::radial_column_unitary、PAG253::invariant_kUnit

### 対象 PAG254::eq_of_chainIn_primePow（thm）
theorem eq_of_chainIn_primePow {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε : ε ≤ Real.log p) {x y : ℚ}
    (hc : chainIn (primePow p) dInf ε x y) : x = y
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG253::invariant_kUnit、PAG253::invariant_cls、PAG249::ineq_odd、PAG185::aux_ineq、PAG179::InQi_one、PAG176::InQi_pow

### 対象 PAG254::exists_padicValRat_eq（thm）
theorem exists_padicValRat_eq (p : ℕ) [hp : Fact p.Prime] (k : ℤ) :
    ∃ q : ℚ, 0 < q ∧ padicValRat p q = k
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG179::InQi_one、PAG176::InQi_pow、PAG176::InQi_mul、PAG187::root_pow_iff、PAG183::root_mul_iff、PAG179::z4_facts、PAG179::InQi_prod、PAG179::InQi_conj

### 対象 PAG254::half_le_abs_padicValRat_sub_half（thm）
theorem half_le_abs_padicValRat_sub_half (p : ℕ) (q : ℚ) :
    (1 / 2 : ℝ) ≤ |((padicValRat p q : ℤ) : ℝ) - 1 / 2|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG45::five_pow_M、PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG37::prim_iff_five、PAG152::five_mod8、PAG152::gauss_mod4、PAG152::e8_one、PAG45::char_ext

### 対象 PAG254::logSet（def）
def logSet : Set ℝ := {x | ∃ q : ℚ, 0 < q ∧ x = Real.log q}
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG176::InQi、PAG176::InQω、PAG253::primeShiftInv、PAG253::primeShift、PAG220::InLayer、PAG54::family、PAG93::Bset、PAG95::Va

### 対象 PAG254::logSet_countable（thm）
theorem logSet_countable : logSet.Countable
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG179::InQi_one、PAG176::InQi_pow、PAG176::InQi_mul、PAG179::InQi_prod、PAG179::InQi_conj、PAG181::InQi_zpow、PAG171::not_root_of_trace、PAG179::z4_facts

### 対象 PAG254::log_inj（thm）
theorem log_inj {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (h : Real.log q = Real.log r) : q = r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG179::InQi_one、PAG176::InQi_pow、PAG176::InQi_mul、PAG179::InQi_prod、PAG179::InQi_conj、PAG171::not_root_of_trace、PAG181::InQi_zpow、PAG179::z4_facts

### 対象 PAG254::not_Icc_subset_logSet（thm）
theorem not_Icc_subset_logSet {a b : ℝ} (hab : a < b) : ¬ Set.Icc a b ⊆ logSet
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG179::InQi_one、PAG176::InQi_pow、PAG176::InQi_mul、PAG179::InQi_prod、PAG179::InQi_conj、PAG253::exists_cls_near、PAG7::W_sq、PAG181::InQi_zpow

### 対象 PAG254::not_forall_chainIn_dP（thm）
theorem not_forall_chainIn_dP (p : ℕ) (hp : p.Prime) :
    ¬ ∀ ε : ℝ, 0 < ε → ∀ q r : ℚ, 0 < q → 0 < r → chainIn posRat (dP p) ε q r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG7::W_sq、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos、PAG51::caseII_target_unique、PAG112::inj_of_isoOn

### 対象 PAG254::padicValRat_eq_of_chainIn（thm）
theorem padicValRat_eq_of_chainIn (p : ℕ) {ε : ℝ} (hε : ε ≤ 1) {q r : ℚ}
    (hc : chainIn posRat (dP p) ε q r) : padicValRat p q = padicValRat p r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG249::ineq_odd、PAG185::aux_ineq、PAG30::fourLe、PAG89::lam_nonneg、PAG7::W_sq、PAG46::lam_pos

### 対象 PAG254::posRat（def）
def posRat : Set ℚ := {q | 0 < q}
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG176::InQi、PAG176::InQω、PAG54::family、PAG93::Bset、PAG95::Va、PAG58::Good、PAG17::AS、PAG55::familyBasis

### 対象 PAG254::primePow（def）
def primePow (p : ℕ) : Set ℚ := {q | ∃ k : ℤ, q = (p : ℚ) ^ k}
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG176::InQi、PAG176::InQω、PAG220::InLayer、PAG54::family、PAG93::Bset、PAG95::Va、PAG17::AS、PAG58::Good

### 対象 PAG254::subsingleton_of_isPreconnected（thm）
theorem subsingleton_of_isPreconnected {S : Set ℝ} (hS : IsPreconnected S) (hSL : S ⊆ logSet) :
    S.Subsingleton
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::eq_of_prime_invariant'、PAG253::eq_of_prime_invariant、PAG253::shift_invariant_of_prime_invariant、PAG179::InQi_one、PAG176::InQi_pow、PAG176::InQi_mul、PAG179::InQi_prod、PAG179::InQi_conj
