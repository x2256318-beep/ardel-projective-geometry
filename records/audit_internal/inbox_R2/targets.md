
######## PAG255.lean（Part 251）
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part255
open PAG.Part253 Nat
end PAG.Part255

### 対象 PAG255::dense_closure_allPrimes（thm）
theorem dense_closure_allPrimes :
    Dense ((Subgroup.closure (primeGens 1) : Subgroup (unitSys × Multiplicative ℝ)) :
      Set (unitSys × Multiplicative ℝ))
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG240::eq_bot_of_one、PAG234::centralizer_bot_eq_top、PAG254::dense_logSet、PAG254::dense_closure_log_two_three、PAG253::unitsMap_kUnit、PAG253::exists_kUnit_eq、PAG253::eq_of_prime_invariant'、PAG253::eq_of_euler

### 対象 PAG255::dense_closure_primeGens（thm）
theorem dense_closure_primeGens (L : ℕ+) :
    Dense ((Subgroup.closure (primeGens L) : Subgroup (unitSys × Multiplicative ℝ)) :
      Set (unitSys × Multiplicative ℝ))
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG240::eq_bot_of_one、PAG234::centralizer_bot_eq_top、PAG254::dense_logSet、PAG254::dense_closure_log_two_three、PAG253::unitsMap_kUnit、PAG253::exists_kUnit_eq、PAG253::eq_of_prime_invariant'、PAG253::eq_of_euler

### 対象 PAG255::exists_level（thm）
theorem exists_level {u : Set unitSys} (hu : IsOpen u) {a : unitSys} (ha : a ∈ u) :
    ∃ N : ℕ+, ∀ b : unitSys, (b : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = (a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N → b ∈ u
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG240::eq_bot_of_one、PAG234::centralizer_bot_eq_top、PAG62::card_ker_mul、PAG62::card_ker、PAG37::ker_five、PAG234::centralizer_map_rightHom、PAG234::centralizer_map_leftHom、PAG68::faithful_pow_factors_iff

### 対象 PAG255::exists_mem_closure_level（thm）
theorem exists_mem_closure_level {L : ℕ} (N : ℕ+) (hL : L ∣ (N : ℕ)) :
    ∀ (m : ℕ), 0 < m → ∀ (hm : m.Coprime N), ∃ g ∈ Subgroup.closure (primeGens L),
      (g.1 : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = kUnit m hm ∧ g.2 = Multiplicative.ofAdd (-Real.log m)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::exists_kUnit_eq、PAG253::unitsMap_kUnit、PAG253::eq_of_euler、PAG253::kUnit_mul_natCast、PAG253::exists_cls_near、PAG37::ker_five、PAG62::card_ker、PAG253::kUnit_one

### 対象 PAG255::kUnit_congr（thm）
theorem kUnit_congr {N : ℕ} {m n : ℕ} (hm : m.Coprime N) (hn : n.Coprime N)
    (h : (m : ZMod N) = (n : ZMod N)) : kUnit m hm = kUnit n hn
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::kUnit_mul_natCast、PAG253::exists_kUnit_eq、PAG253::kUnit_one、PAG253::kUnit_mul、PAG253::unitsMap_kUnit、PAG253::invariant_kUnit、PAG253::kUnit_mem_of_prime

### 対象 PAG255::pow_dvd_pow_factorial（thm）
theorem pow_dvd_pow_factorial {p a M' N K : ℕ} (hp : p.Prime) (hN : N = p ^ a * M') (hN0 : 0 < N)
    (hK : N ≤ K) : p ^ a ∣ p ^ K !
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG30::fourLe、PAG166::factorial_sq、PAG249::ineq_odd、PAG185::aux_ineq、PAG199::pos_of_mul、PAG216::gblock_shell_inj、PAG214::div_mul_div_of_dvd、PAG212::mul_div_div_cancel

### 対象 PAG255::pow_factorial_modEq（thm）
theorem pow_factorial_modEq {p N K : ℕ} (hp : p.Prime) (hN0 : 0 < N) (hK : N ≤ K) :
    p ^ K ! ≡ p ^ N ! [MOD N]
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG30::fourLe、PAG166::factorial_sq、PAG249::ineq_odd、PAG185::aux_ineq、PAG199::pos_of_mul、PAG216::gblock_shell_inj、PAG214::div_mul_div_of_dvd、PAG212::mul_div_div_cancel

### 対象 PAG255::pow_factorial_modEq_one（thm）
theorem pow_factorial_modEq_one {p a M' N K : ℕ} (hp : p.Prime) (hN : N = p ^ a * M') (hpM : ¬ p ∣ M')
    (hN0 : 0 < N) (hK : N ≤ K) : p ^ K ! ≡ 1 [MOD M']
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG30::fourLe、PAG166::factorial_sq、PAG249::ineq_odd、PAG147::eq_of_dvd_not_dvd_div、PAG185::aux_ineq、PAG199::pos_of_mul、PAG200::split_dvd、PAG196::pcomp_aux

### 対象 PAG255::primeCls（def）
def primeCls (p : ℕ) (hp : p.Prime) (N : ℕ+) : (ZMod (N : ℕ))ˣ :=
  kUnit (wNat p N) (wNat_coprime hp N.pos)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::kUnit、PAG253::primeShiftInv、PAG253::primeShift、PAG240::CoprimeList、PAG37::five、PAG253::globalInv、PAG240::liftL、PAG240::prodList

### 対象 PAG255::primeCls_mem（thm）
theorem primeCls_mem (p : ℕ) (hp : p.Prime) : (fun N => primeCls p hp N) ∈ unitSys
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::unitsMap_kUnit、PAG253::kUnit_mul_natCast、PAG253::exists_kUnit_eq、PAG62::card_ker、PAG253::kUnit_one、PAG37::ker_five、PAG253::kUnit_mul、PAG62::card_ker_mul

### 対象 PAG255::primeCls_of_coprime（thm）
theorem primeCls_of_coprime (p : ℕ) (hp : p.Prime) (N : ℕ+) (hpN : p.Coprime N) :
    primeCls p hp N = kUnit p hpN
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::kUnit_mul_natCast、PAG253::exists_kUnit_eq、PAG253::kUnit_one、PAG253::kUnit_mul、PAG253::unitsMap_kUnit、PAG253::invariant_kUnit、PAG253::kUnit_mem_of_prime

### 対象 PAG255::primeGens（def）
noncomputable def primeGens (L : ℕ) : Set (unitSys × Multiplicative ℝ) :=
  {g | ∃ (p : ℕ) (hp : p.Prime), ¬ p ∣ L ∧ g = (primeSys p hp, Multiplicative.ofAdd (-Real.log p))}
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::globalInv、PAG253::primeShiftInv、PAG253::primeShift、PAG253::kUnit、PAG143::freqHom、PAG253::commSubmonoid、PAG67::red、PAG240::CoprimeList

### 対象 PAG255::primeSys（def）
def primeSys (p : ℕ) (hp : p.Prime) : unitSys := ⟨fun N => primeCls p hp N, primeCls_mem p hp⟩
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::kUnit、PAG253::primeShiftInv、PAG253::primeShift、PAG253::commSubmonoid、PAG67::red、PAG240::CoprimeList、PAG37::toFour、PAG61::gen

### 対象 PAG255::primeSys_unique（thm）
theorem primeSys_unique (p : ℕ) (hp : p.Prime) (a : unitSys)
    (h1 : ∀ (N : ℕ+) (hpN : p.Coprime N), (a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = kUnit p hpN)
    (h2 : ∀ (N : ℕ+) (k : ℕ) (h : p ^ k ∣ (N : ℕ)),
      ZMod.unitsMap h ((a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N) = 1) :
    a = primeSys p hp
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::kUnit_one、PAG253::unitsMap_kUnit、PAG253::kUnit_mul_natCast、PAG253::exists_kUnit_eq、PAG62::card_ker、PAG37::ker_five、PAG253::kUnit_mul、PAG62::card_ker_mul

### 対象 PAG255::unitSys（def）
def unitSys : Subgroup (∀ N : ℕ+, (ZMod (N : ℕ))ˣ) where
  carrier := {a | ∀ (N M : ℕ+) (h : (N : ℕ) ∣ (M : ℕ)), ZMod.unitsMap h (a M) = a N}
  mul_mem' := by
    intro a b ha hb N M h
    rw [Pi.mul_apply, map_mul, ha N M h, hb N M h, Pi.mul_apply]
  one_mem' := by
    intro N M h
    rw [Pi.one_apply, map_one, Pi.one_apply]
  inv_mem' := by
    intro a ha N M h
    rw [Pi.inv_apply, map_inv, ha N M h, Pi.inv_apply]
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::commSubmonoid、PAG67::red、PAG240::CoprimeList、PAG37::toFour、PAG210::liftc、PAG67::omegaLow、PAG61::gen、PAG214::gblock

### 対象 PAG255::unitsMap_primeCls_pow（thm）
theorem unitsMap_primeCls_pow (p : ℕ) (hp : p.Prime) (N : ℕ+) {a : ℕ} (h : p ^ a ∣ (N : ℕ)) :
    ZMod.unitsMap h (primeCls p hp N) = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::kUnit_one、PAG253::unitsMap_kUnit、PAG253::kUnit_mul_natCast、PAG253::exists_kUnit_eq、PAG253::kUnit_mul、PAG253::eq_of_euler、PAG37::unitsMap_neg_one

### 対象 PAG255::units_eq_of_coprime_parts（thm）
theorem units_eq_of_coprime_parts {N A B : ℕ} [NeZero N] (hN : N = A * B) (hAB : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) (b c : (ZMod N)ˣ)
    (h1 : ZMod.unitsMap hA b = ZMod.unitsMap hA c) (h2 : ZMod.unitsMap hB b = ZMod.unitsMap hB c) :
    b = c
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG37::unitsMap_neg_one、PAG195::factorsThrough_sq_iff_units、PAG37::unitsMap_five、PAG253::unitsMap_kUnit、PAG195::general_root_iff_units、PAG9::ker_pow_p、PAG8::exists_ker_ne_one_of_primitive、PAG133::exists_ker_ne

### 対象 PAG255::wNat（def）
def wNat (p N : ℕ) : ℕ := 1 + p ^ N ! * (p - 1)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG19::sz、PAG15::shellSize、PAG29::cB、PAG80::mu、PAG32::gp、PAG31::gg、PAG30::kk、PAG95::J

### 対象 PAG255::wNat_cast_eq（thm）
theorem wNat_cast_eq {p N K : ℕ} (hp : p.Prime) (hN0 : 0 < N) (hK : N ≤ K) :
    ((wNat p K : ℕ) : ZMod N) = ((wNat p N : ℕ) : ZMod N)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG185::aux_ineq、PAG249::ineq_odd、PAG166::factorial_sq、PAG30::fourLe、PAG249::half_mul_succ_add_three、PAG249::half_mul_succ_add_one、PAG106::sz_succ、PAG249::ineq_two

### 対象 PAG255::wNat_cast_of_coprime（thm）
theorem wNat_cast_of_coprime {p N : ℕ} (hp : p.Prime) (hN0 : 0 < N) (hpN : p.Coprime N) :
    ((wNat p N : ℕ) : ZMod N) = (p : ZMod N)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG166::factorial_sq、PAG185::aux_ineq、PAG106::sz_succ、PAG199::pos_of_mul、PAG196::pcomp_aux、PAG249::ineq_odd、PAG169::ord_split、PAG216::gblock_shell_inj

### 対象 PAG255::wNat_coprime（thm）
theorem wNat_coprime {p N : ℕ} (hp : p.Prime) (hN0 : 0 < N) : (wNat p N).Coprime N
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG166::factorial_sq、PAG185::aux_ineq、PAG106::sz_succ、PAG199::pos_of_mul、PAG196::pcomp_aux、PAG249::ineq_odd、PAG169::ord_split、PAG216::gblock_shell_inj

######## PAG256.lean（Part 252）
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part256
open ZMod Complex Finset
variable {N : ℕ} [NeZero N]
open Classical in
end PAG.Part256

### 対象 PAG256::JH（def）
noncomputable def JH (f : ZMod N → ℂ) (u : (ZMod N)ˣ) : ℂ :=
  hartley f ((u⁻¹ : (ZMod N)ˣ) : ZMod N) / (Real.sqrt N : ℂ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::scaleShift、PAG253::primeShiftInv、PAG253::kUnit、PAG98::Equivariant、PAG207::Radial、PAG44::zeta、PAG199::thmAConst、PAG165::zp

### 対象 PAG256::JH_eq_rootNum_mul（thm）
theorem JH_eq_rootNum_mul {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG165::gb_sin、PAG209::kcoef_div、PAG2::parity_weight、PAG20::coef_sqrt、PAG19::coef_identity_real、PAG152::phase_mod4_eq、PAG14::lift_invariance、PAG152::gauss_mod4

### 対象 PAG256::JH_eq_rootNum_mul_any（thm）
theorem JH_eq_rootNum_mul_any (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG165::gb_sin、PAG209::kcoef_div、PAG2::parity_weight、PAG20::coef_sqrt、PAG19::coef_identity_real、PAG14::lift_invariance、PAG253::eq_of_euler、PAG152::phase_mod4_eq

### 対象 PAG256::casKer（def）
noncomputable def casKer (t : ZMod N) : ℂ :=
  ((Real.cos (2 * Real.pi * t.val / N) + Real.sin (2 * Real.pi * t.val / N) : ℝ) : ℂ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::scaleShift、PAG44::zeta、PAG165::zp、PAG199::thmAConst、PAG116::cnorm、PAG2::cas、PAG165::gb、PAG61::zeta

### 対象 PAG256::casKer_eq（thm）
theorem casKer_eq (t : ZMod N) :
    casKer t = ((1 - I) * stdAddChar t + (1 + I) * stdAddChar (-t)) / 2
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG152::e8_one、PAG2::parity_weight、PAG165::gb_sin、PAG152::gauss_mod8、PAG45::char_ext、PAG152::gauss_mod4、PAG152::e4_pow、PAG152::e8_sq

### 対象 PAG256::exists_primitive_even_five（thm）
theorem exists_primitive_even_five :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Even ∧ χ ≠ 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG171::primitive_of_ne_one、PAG195::ne_one_of_isPrimitive、PAG200::exists_split、PAG32::prim_level_p_iff、PAG198::level_two_trivial、PAG72::exists_prim4、PAG16::gaussSum_ne_zero、PAG215::chi_eq_zero_of_rad

### 対象 PAG256::exists_primitive_odd_three（thm）
theorem exists_primitive_odd_three : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Odd
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG72::exists_prim4、PAG195::squarefull_root、PAG200::exists_split、PAG72::prim4_unique、PAG144::exists_primitive、PAG188::prod_root_of_root、PAG118::gauss_even_root、PAG120::gauss_root_ge_two

### 対象 PAG256::hartley（def）
noncomputable def hartley (f : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * casKer (x * y)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG253::scaleShift、PAG44::zeta、PAG165::zp、PAG199::thmAConst、PAG116::cnorm、PAG2::cas、PAG165::gb、PAG61::zeta

### 対象 PAG256::hartley_eq_of_isPrimitive（thm）
theorem hartley_eq_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (y : ZMod N) :
    hartley (χ : ZMod N → ℂ) y = parFac χ * gaussSum χ stdAddChar * χ⁻¹ y
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG209::kcoef_div、PAG2::parity_weight、PAG165::gb_sin、PAG208::ket_coef_ne_zero、PAG210::kcoef_mul_kcoef_inv、PAG209::normSq_kcoef、PAG209::kcoef_ne_zero

### 対象 PAG256::hartley_eq_zero_of_not_isUnit（thm）
theorem hartley_eq_zero_of_not_isUnit {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {y : ZMod N} (hy : ¬IsUnit y) : hartley (χ : ZMod N → ℂ) y = 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG165::gb_sin、PAG20::coef_sqrt、PAG19::coef_identity_real、PAG209::kcoef_div、PAG8::p_dvd_val_of_not_isUnit、PAG15::radial_column_unitary、PAG15::abs_F_eq、PAG57::not_dvd_val_of_unit

### 対象 PAG256::hartley_one（thm）
theorem hartley_one (χ : DirichletCharacter ℂ N) :
    hartley (χ : ZMod N → ℂ) 1 = parFac χ * gaussSum χ stdAddChar
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG209::kcoef_div、PAG2::parity_weight、PAG165::gb_sin、PAG152::e8_one、PAG152::gauss_mod8、PAG210::kcoef_mul_kcoef_inv、PAG209::normSq_kcoef、PAG151::real_phase_sq

### 対象 PAG256::hartley_units_inv（thm）
theorem hartley_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    hartley (χ : ZMod N → ℂ) ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u * hartley (χ : ZMod N → ℂ) 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG165::gb_sin、PAG20::coef_sqrt、PAG19::coef_identity_real、PAG253::kUnit_mul_natCast、PAG209::kcoef_div、PAG14::lift_invariance、PAG253::globalInv_scaleShift_globalInv、PAG218::dft_dil

### 対象 PAG256::inv_apply_neg_one（thm）
omit [NeZero N] in
theorem inv_apply_neg_one (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG81::inv_neg_one、PAG25::chi_inv_neg_one、PAG29::chi_neg_one_sq'、PAG75::chi_neg_one_ne_zero、PAG9::inv_apply_neg_one、PAG208::ket_coef_ne_zero、PAG9::chi_neg_one_sq、PAG117::inv_neg_one_pow

### 対象 PAG256::inv_apply_units_inv（thm）
omit [NeZero N] in
theorem inv_apply_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ⁻¹ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG14::lift_invariance、PAG253::kUnit_mul_natCast、PAG218::dft_dil、PAG207::gcd_val_unit_mul、PAG255::kUnit_congr、PAG207::exists_unit_mul_gcd、PAG253::exists_kUnit_eq、PAG253::kUnit_one

### 対象 PAG256::isPrimitive_of_prime_of_ne_one（thm）
theorem isPrimitive_of_prime_of_ne_one {p : ℕ} [hp : Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (h : χ ≠ 1) : χ.IsPrimitive
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG171::primitive_of_ne_one、PAG32::prim_level_p_iff、PAG195::ne_one_of_isPrimitive、PAG198::level_two_trivial、PAG185::sqrt_ne_zero、PAG215::chi_eq_zero_of_rad、PAG31::mod4_mul_trivial、PAG215::div_ne_zero_of_dvd

### 対象 PAG256::neg_one_mul_self（thm）
omit [NeZero N] in
theorem neg_one_mul_self (χ : DirichletCharacter ℂ N) : χ (-1) * χ (-1) = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG29::chi_neg_one_sq'、PAG75::chi_neg_one_ne_zero、PAG81::inv_neg_one、PAG25::chi_inv_neg_one、PAG9::chi_neg_one_sq、PAG198::castHom_neg_one、PAG72::prim4_neg_one、PAG151::neg_one_mod4

### 対象 PAG256::normSq_rootNum（thm）
theorem normSq_rootNum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (rootNum χ) = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG199::normSq_chi_natCast、PAG202::normSq_chi_unit、PAG16::normSq_gaussSum、PAG47::normSq_coef_of、PAG117::normSq_inv_neg_one、PAG213::sum_normSq_char、PAG213::sum_normSq_char_comp、PAG42::normSq_mixed_coef

### 対象 PAG256::parFac（def）
noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG2::Wpow、PAG198::gs、PAG29::cB、PAG180::Rep2、PAG222::twistConst、PAG247::testFn、PAG171::ω、PAG172::InZi

### 対象 PAG256::parFac_of_even（thm）
omit [NeZero N] in
theorem parFac_of_even {χ : DirichletCharacter ℂ N} (h : χ.Even) : parFac χ = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG2::parity_weight、PAG29::chi_neg_one_sq'、PAG171::ω_sq、PAG171::cube_eq_one、PAG75::chi_neg_one_ne_zero、PAG171::conj_ω、PAG152::gauss_mod8、PAG81::inv_neg_one

### 対象 PAG256::parFac_of_odd（thm）
omit [NeZero N] in
theorem parFac_of_odd {χ : DirichletCharacter ℂ N} (h : χ.Odd) : parFac χ = -I
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG2::parity_weight、PAG72::prim4_neg_one、PAG151::neg_one_mod4、PAG171::ω_sq、PAG152::gauss_mod8、PAG171::cube_eq_one、PAG198::gaussSum_real、PAG171::conj_ω

### 対象 PAG256::removal_counterexample（thm）
theorem removal_counterexample :
    ¬(1 : DirichletCharacter ℂ 2).IsPrimitive ∧ ¬IsUnit (0 : ZMod 2) ∧
      hartley ((1 : DirichletCharacter ℂ 2) : ZMod 2 → ℂ) 0 = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG120::quad_root_two、PAG165::gb_sin、PAG185::sum_pow_lt、PAG120::psi_two_one、PAG20::coef_sqrt、PAG19::coef_identity_real、PAG120::quad_root_all、PAG119::quad_root'

### 対象 PAG256::removal_counterexample_four（thm）
theorem removal_counterexample_four :
    (∃ χ : DirichletCharacter ℂ (2 ^ 2), χ.IsPrimitive) ∧
    ¬(1 : DirichletCharacter ℂ 4).IsPrimitive ∧ ¬IsUnit (2 : ZMod 4) ∧
      hartley ((1 : DirichletCharacter ℂ 4) : ZMod 4 → ℂ) 2 = -2 ∧
      Complex.normSq (rootNum (1 : DirichletCharacter ℂ 4)) = 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG16::normSq_gaussSum、PAG209::normSq_kcoef、PAG204::normSq_mixed_coef、PAG2::parity_weight、PAG152::gauss_mod8、PAG42::normSq_mixed_coef、PAG152::gauss_mod4、PAG213::sum_normSq_char

### 対象 PAG256::removal_counterexample_normSq（thm）
theorem removal_counterexample_normSq :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ 2)) = 1 / 2
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG199::normSq_chi_natCast、PAG202::normSq_chi_unit、PAG16::normSq_gaussSum、PAG47::normSq_coef_of、PAG117::normSq_inv_neg_one、PAG85::p2_mixed_general、PAG213::sum_normSq_char、PAG42::normSq_mixed_coef

### 対象 PAG256::rootNum（def）
open Classical in
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG196::zN、PAG201::jt、PAG184::zOf、PAG199::thmAConst、PAG222::twistConst、PAG2::Wpow、PAG44::zeta、PAG217::fcoef

### 対象 PAG256::rootNum_eq（thm）
theorem rootNum_eq (χ : DirichletCharacter ℂ N) :
    rootNum χ = parFac χ * gaussSum χ stdAddChar / (Real.sqrt N : ℂ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG2::parity_weight、PAG152::gauss_mod8、PAG210::kcoef_mul_kcoef_inv、PAG151::real_phase_sq、PAG151::phase_mod8、PAG208::ket_coef_ne_zero、PAG29::chi_neg_one_sq'、PAG198::gaussSum_real

### 対象 PAG256::sum_mul_stdAddChar（thm）
theorem sum_mul_stdAddChar (χ : DirichletCharacter ℂ N) (y : ZMod N) :
    ∑ x : ZMod N, χ x * stdAddChar (x * y) = gaussSum χ (stdAddChar.mulShift y)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG117::stdAddChar_mul_cast、PAG2::addChar_sum、PAG140::exists_delta、PAG152::e8_pow、PAG127::gauss_even_phase、PAG142::freq_mul、PAG127::stdAddChar_pow_eq_one_iff

### 対象 PAG256::sum_mul_stdAddChar_neg（thm）
theorem sum_mul_stdAddChar_neg (χ : DirichletCharacter ℂ N) :
    ∑ x : ZMod N, χ x * stdAddChar (-x) = χ (-1) * gaussSum χ stdAddChar
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG14::stationary_phase、PAG16::conv_char_inv、PAG154::orderOf_gauss_freq、PAG14::lift_invariance、PAG250::dft_single、PAG121::sum_chr_mul、PAG29::chi_neg_one_sq'
