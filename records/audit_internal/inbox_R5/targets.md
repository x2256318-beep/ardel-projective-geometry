
######## PAG259.lean（Part 255）
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part259
end PAG.Part259

### 対象 PAG259::BoxCoord（def）
def BoxCoord : Type := Nat.Primes → ℤ
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：

### 対象 PAG259::closure_logSet（thm）
theorem closure_logSet : closure PAG.Part254.logSet = Set.univ
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dense_logSet、PAG254::subsingleton_of_isPreconnected、PAG254::logSet_countable、PAG254::log_inj、PAG254::not_Icc_subset_logSet、PAG254::dInf_mul_left、PAG254::exists_padicValRat_eq、PAG254::chainIn_dInf

### 対象 PAG259::closure_rho_not_image（thm）
theorem closure_rho_not_image :
    ((1 : ℝ), (0 : Nat.Primes → ℤ)) ∈ closure (rho '' {q : ℚ | 0 < q}) ∧
      ((1 : ℝ), (0 : Nat.Primes → ℤ)) ∉ rho '' {q : ℚ | 0 < q}
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dense_logSet、PAG254::log_inj、PAG254::subsingleton_of_isPreconnected、PAG254::exists_padicValRat_eq、PAG254::logSet_countable、PAG254::emergence_contrast、PAG254::chainIn_dInf、PAG254::dInf_mul_left

### 対象 PAG259::dense_closure_log_primes（thm）
theorem dense_closure_log_primes {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) :
    Dense ((AddSubgroup.closure ({Real.log p, Real.log r} : Set ℝ) : AddSubgroup ℝ) : Set ℝ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dense_closure_log_two_three、PAG254::dense_logSet、PAG15::cardH_pos、PAG254::subsingleton_of_isPreconnected、PAG253::eq_of_prime_invariant'、PAG253::eq_of_prime_invariant、PAG255::dense_closure_primeGens、PAG255::dense_closure_allPrimes

### 対象 PAG259::dense_imgST_iff（thm）
theorem dense_imgST_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    Dense (imgST S T) ↔ ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dense_logSet、PAG254::log_inj、PAG254::subsingleton_of_isPreconnected、PAG254::exists_padicValRat_eq、PAG254::logSet_countable、PAG254::dense_closure_log_two_three、PAG254::dInf_mul_left、PAG254::not_Icc_subset_logSet

### 対象 PAG259::dense_rho_image（thm）
theorem dense_rho_image : Dense (rho '' {q : ℚ | 0 < q})
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dense_logSet、PAG254::log_inj、PAG254::subsingleton_of_isPreconnected、PAG254::exists_padicValRat_eq、PAG254::logSet_countable、PAG254::dense_closure_log_two_three、PAG254::dInf_mul_left、PAG254::not_Icc_subset_logSet

### 対象 PAG259::eq_mul_zpow_of_agree（thm）
theorem eq_mul_zpow_of_agree {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q) (hq' : 0 < q')
    (h : ∀ t : ℕ, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q * (p : ℚ) ^ (padicValRat p q' - padicValRat p q)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::exists_padicValRat_eq、PAG254::dP_mul_left、PAG254::dInf_mul_left、PAG254::dInf_zpow、PAG254::emergence_contrast、PAG254::log_inj、PAG254::chainIn_dP_of_one_lt、PAG254::not_forall_chainIn_dP

### 対象 PAG259::eq_of_padicValRat_eq（thm）
theorem eq_of_padicValRat_eq {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (h : ∀ p : ℕ, p.Prime → padicValRat p q = padicValRat p r) : q = r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::exists_padicValRat_eq、PAG254::log_inj、PAG254::chainIn_dP_of_one_lt、PAG254::not_forall_chainIn_dP、PAG254::padicValRat_eq_of_chainIn、PAG254::logSet_countable、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification

### 対象 PAG259::eq_one_of_padicValRat_eq_zero（thm）
theorem eq_one_of_padicValRat_eq_zero {q : ℚ} (hq : 0 < q)
    (h : ∀ p : ℕ, p.Prime → padicValRat p q = 0) : q = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::exists_padicValRat_eq、PAG254::log_inj、PAG254::chainIn_dP_of_one_lt、PAG254::not_forall_chainIn_dP、PAG254::padicValRat_eq_of_chainIn、PAG254::logSet_countable、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification

### 対象 PAG259::eq_prod_of_support（thm）
theorem eq_prod_of_support (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) {q : ℚ} (hq : 0 < q)
    (hsupp : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) :
    q = ∏ s ∈ S, (s : ℚ) ^ (padicValRat s q)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::exists_padicValRat_eq、PAG254::log_inj、PAG254::emergence_contrast、PAG254::dInf_zpow、PAG254::not_forall_chainIn_dP、PAG254::eq_of_chainIn_primePow、PAG254::chainIn_dP_of_one_lt、PAG254::padicValRat_eq_of_chainIn

### 対象 PAG259::eq_prod_support（thm）
theorem eq_prod_support {q : ℚ} (hq : 0 < q) :
    q = ∏ s ∈ (finite_support_padicValRat hq).toFinset, (s : ℚ) ^ (padicValRat s q)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::exists_padicValRat_eq、PAG254::log_inj、PAG254::emergence_contrast、PAG254::dInf_zpow、PAG254::eq_of_chainIn_primePow、PAG254::chainIn_dP_of_one_lt、PAG254::not_forall_chainIn_dP、PAG254::logSet_countable

### 対象 PAG259::exists_between_one（thm）
theorem exists_between_one {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) {y : ℝ}
    (hy : 1 < y) :
    ∃ a b : ℤ, 1 < (p : ℝ) ^ a * (r : ℝ) ^ b ∧ (p : ℝ) ^ a * (r : ℝ) ^ b < y
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG188::zpow_root、PAG197::pow_two_zpow、PAG181::zpow_four_comm、PAG180::zpow_six_comm、PAG15::F_sq_eq_inv_p、PAG46::lam_pos、PAG31::lam_pos、PAG116::lam_pos

### 対象 PAG259::exists_mem_one_le_abs_of_support（thm）
theorem exists_mem_one_le_abs_of_support (S : Finset ℕ) {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (hqS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
    (hrS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t r = 0) (hne : q ≠ r) :
    ∃ p ∈ S, p.Prime ∧ (1 : ℝ) ≤ |((padicValRat p q - padicValRat p r : ℤ) : ℝ)|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::padicValRat_eq_of_chainIn、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification、PAG254::half_le_abs_padicValRat_sub_half、PAG254::dP_lt_one_iff、PAG254::chainIn_dP_of_one_lt、PAG254::dP_mul_left、PAG254::not_forall_chainIn_dP

### 対象 PAG259::exists_near_in_subgroup（thm）
theorem exists_near_in_subgroup (S : Finset ℕ) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hne : p ≠ r) (hpS : p ∈ S) (hrS : r ∈ S) (T : Finset ℕ) (hpT : p ∉ T) (hrT : r ∉ T)
    {q₀ : ℚ} (hq₀ : 0 < q₀) (hq₀S : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q₀ = 0) (x : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) ∧
      (∀ s ∈ T, s.Prime → padicValRat s q = padicValRat s q₀) ∧ |Real.log q - x| < ε
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::chainIn_dInf、PAG254::dense_logSet_coprime、PAG254::dInf_mul_left、PAG254::emergence_contrast、PAG254::abs_log_sub_log_le、PAG254::log_inj、PAG253::exists_cls_near、PAG254::not_forall_chainIn_dP

### 対象 PAG259::exists_near_measured（thm）
theorem exists_near_measured {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r)
    (M : Finset ℕ) (hpM : p ∉ M) (hrM : r ∉ M) {q₀ : ℚ} (hq₀ : 0 < q₀) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ s ∈ M, s.Prime → padicValRat s q = padicValRat s q₀) ∧
      |Real.log q - x| < ε
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::chainIn_dInf、PAG254::dense_logSet_coprime、PAG254::dInf_mul_left、PAG254::emergence_contrast、PAG254::abs_log_sub_log_le、PAG254::log_inj、PAG253::exists_cls_near、PAG254::not_forall_chainIn_dP

### 対象 PAG259::exists_near_of_two_unmeasured（thm）
theorem exists_near_of_two_unmeasured {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r)
    {q₀ : ℚ} (hq₀ : 0 < q₀) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ≠ p → t ≠ r → padicValRat t q = padicValRat t q₀) ∧
      |Real.log q - x| < ε
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::chainIn_dInf、PAG254::dense_logSet_coprime、PAG254::dInf_mul_left、PAG254::emergence_contrast、PAG254::abs_log_sub_log_le、PAG254::log_inj、PAG253::exists_cls_near、PAG254::not_forall_chainIn_dP

### 対象 PAG259::exists_padicValRat_eq（thm）
theorem exists_padicValRat_eq (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (k : ℕ → ℤ) :
    ∃ q : ℚ, 0 < q ∧ (∀ s ∈ S, padicValRat s q = k s) ∧
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::exists_padicValRat_eq、PAG254::log_inj、PAG254::not_forall_chainIn_dP、PAG254::chainIn_dP_of_one_lt、PAG254::padicValRat_eq_of_chainIn、PAG254::logSet_countable、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification

### 対象 PAG259::exists_prime_one_le_abs（thm）
theorem exists_prime_one_le_abs {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (hne : q ≠ r) :
    ∃ p : ℕ, p.Prime ∧ (1 : ℝ) ≤ |((padicValRat p q - padicValRat p r : ℤ) : ℝ)|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::padicValRat_eq_of_chainIn、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification、PAG254::half_le_abs_padicValRat_sub_half、PAG254::dP_lt_one_iff、PAG254::chainIn_dP_of_one_lt、PAG254::dP_mul_left、PAG254::not_forall_chainIn_dP

### 対象 PAG259::exists_two_primes_not_mem（thm）
theorem exists_two_primes_not_mem (I : Set Nat.Primes) (hI : I.Finite) :
    ∃ p r : Nat.Primes, p ∉ I ∧ r ∉ I ∧ (p : ℕ) ≠ (r : ℕ)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::chainIn_refl、PAG254::chainIn_of_lt、PAG254::chainIn_invariant、PAG200::exists_split、PAG254::chainIn_mono、PAG190::finite_of_bounded、PAG219::not_dvd_of_chi_ne_zero、PAG146::twist_digit_uniform

### 対象 PAG259::exists_zpow_near（thm）
theorem exists_zpow_near {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ a b : ℤ, |(a : ℝ) * Real.log p + (b : ℝ) * Real.log r - x| < ε
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dense_logSet_coprime、PAG254::abs_log_sub_log_le、PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG254::dInf_zpow、PAG254::dP_lt_one_iff、PAG254::emergence_contrast、PAG254::chainIn_dInf

### 対象 PAG259::fiber_sep（thm）
theorem fiber_sep (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime)
    (h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r) :
    ∃ c : ℝ, 0 < c ∧ ∀ q q' : ℚ, 0 < q → 0 < q' →
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) →
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q' = 0) →
      (∀ t ∈ T, padicValRat t q' = padicValRat t q) →
      q' = q ∨ c ≤ |Real.log q' - Real.log q|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::abs_log_sub_log_le、PAG254::chainIn_dInf、PAG254::dense_logSet_coprime、PAG254::dInf_mul_left、PAG254::emergence_contrast、PAG254::log_inj、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification

### 対象 PAG259::finite_support_padicValRat（thm）
theorem finite_support_padicValRat {q : ℚ} (hq : 0 < q) :
    {p : ℕ | p.Prime ∧ padicValRat p q ≠ 0}.Finite
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::exists_padicValRat_eq、PAG254::log_inj、PAG254::chainIn_dP_of_one_lt、PAG254::not_forall_chainIn_dP、PAG254::logSet_countable、PAG254::padicValRat_eq_of_chainIn、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification

### 対象 PAG259::imgST（def）
def imgST (S T : Finset ℕ) : Set (ℝ × (T → ℤ)) :=
  {z | ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) ∧
    z = (Real.log q, fun t : T => padicValRat (t : ℕ) q)}
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::logSet、PAG254::posRat、PAG254::dInf、PAG176::InQi、PAG254::dP、PAG254::primePow、PAG176::InQω、PAG23::P1F

### 対象 PAG259::irrational_log_div_log（thm）
theorem irrational_log_div_log {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) :
    Irrational (Real.log r / Real.log p)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::abs_log_sub_log_le、PAG116::cnorm_ne_zero、PAG215::chi_eq_zero_of_rad、PAG254::log_inj、PAG209::kcoef_div、PAG20::coef_sqrt、PAG19::coef_identity_real

### 対象 PAG259::isClosed_and_discrete_of_subsingleton（thm）
theorem isClosed_and_discrete_of_subsingleton {X : Type*} [TopologicalSpace X] [T1Space X]
    {A : Set X} (h : ∀ z : X, ∃ U ∈ nhds z, (U ∩ A).Subsingleton) :
    IsClosed A ∧ DiscreteTopology A
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG255::exists_level、PAG55::family_linearIndependent、PAG254::subsingleton_of_isPreconnected、PAG254::chainIn_refl、PAG254::chainIn_of_lt、PAG254::chainIn_invariant、PAG56::expand、PAG254::chainIn_mono

### 対象 PAG259::isClosed_discrete_imgST（thm）
theorem isClosed_discrete_imgST (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime)
    (h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r) :
    IsClosed (imgST S T) ∧ DiscreteTopology (imgST S T)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dense_logSet、PAG254::log_inj、PAG254::subsingleton_of_isPreconnected、PAG254::exists_padicValRat_eq、PAG254::logSet_countable、PAG254::chainIn_dInf、PAG254::emergence_contrast、PAG254::dInf_mul_left

### 対象 PAG259::isClosed_discrete_rhoBox_image（thm）
theorem isClosed_discrete_rhoBox_image :
    IsClosed (rhoBox '' {q : ℚ | 0 < q}) ∧ DiscreteTopology (rhoBox '' {q : ℚ | 0 < q})
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG240::eq_bot_of_one、PAG255::exists_level、PAG255::dense_closure_primeGens、PAG255::dense_closure_allPrimes、PAG254::dense_logSet、PAG234::centralizer_bot_eq_top、PAG254::log_inj、PAG254::subsingleton_of_isPreconnected

### 対象 PAG259::log_eq_sum_of_support（thm）
theorem log_eq_sum_of_support (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) {q : ℚ} (hq : 0 < q)
    (hsupp : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) :
    Real.log q = ∑ s ∈ S, (padicValRat s q : ℝ) * Real.log s
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::log_inj、PAG254::exists_padicValRat_eq、PAG254::logSet_countable、PAG254::emergence_contrast、PAG254::dInf_mul_left、PAG254::dense_logSet、PAG254::dInf_zpow、PAG254::not_Icc_subset_logSet

### 対象 PAG259::log_mul_zpow_zpow（thm）
theorem log_mul_zpow_zpow {p r : ℕ} (hp : p.Prime) (hr : r.Prime) {q₀ : ℚ} (hq₀ : 0 < q₀)
    (a b : ℤ) :
    Real.log ((q₀ * (p : ℚ) ^ a * (r : ℚ) ^ b : ℚ) : ℝ) =
      Real.log q₀ + (a : ℝ) * Real.log p + (b : ℝ) * Real.log r
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::log_inj、PAG254::dInf_zpow、PAG254::dInf_mul_left、PAG254::emergence_contrast、PAG254::logSet_countable、PAG254::dP_mul_left、PAG254::dense_logSet、PAG254::eq_of_chainIn_primePow

### 対象 PAG259::log_sep_of_agree（thm）
theorem log_sep_of_agree {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q) (hq' : 0 < q')
    (h : ∀ t : ℕ, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q ∨ Real.log p ≤ |Real.log q' - Real.log q|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dInf_mul_left、PAG254::log_inj、PAG254::chainIn_dInf、PAG254::abs_log_sub_log_le、PAG254::emergence_contrast、PAG254::half_le_abs_padicValRat_sub_half、PAG254::dInf_zpow、PAG254::eq_of_chainIn_primePow

### 対象 PAG259::log_sep_one_unmeasured（thm）
theorem log_sep_one_unmeasured (S : Finset ℕ) {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q)
    (hq' : 0 < q') (hqS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
    (hq'S : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q' = 0)
    (h : ∀ t ∈ S, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q ∨ Real.log p ≤ |Real.log q' - Real.log q|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dInf_mul_left、PAG254::log_inj、PAG254::chainIn_dInf、PAG254::abs_log_sub_log_le、PAG254::emergence_contrast、PAG254::half_le_abs_padicValRat_sub_half、PAG254::dInf_zpow、PAG254::eq_of_chainIn_primePow

### 対象 PAG259::mem_closure_line_prod（thm）
theorem mem_closure_line_prod (x : ℝ) :
    (x, (0 : Nat.Primes → ℤ)) ∈ closure (rho '' {q : ℚ | 0 < q})
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dense_logSet、PAG254::log_inj、PAG254::subsingleton_of_isPreconnected、PAG254::exists_padicValRat_eq、PAG254::logSet_countable、PAG254::chainIn_dInf、PAG254::emergence_contrast、PAG254::dInf_mul_left

### 対象 PAG259::mem_zmultiples_of_commensurable（thm）
theorem mem_zmultiples_of_commensurable {L₁ L₂ : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) * L₂ = m * L₁) (a b : ℤ) :
    (a : ℝ) * L₁ + b * L₂ = ((a * n + b * m : ℤ) : ℝ) * (L₁ / n)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG12::pow_p_pow_congr、PAG12::pow_p_congr、PAG20::coef_sqrt、PAG19::coef_identity_real、PAG175::trace4_identity、PAG12::key_binom、PAG12::one_add_pow_expand、PAG178::Tlin4_not_dvd

### 対象 PAG259::one_le_abs_intCast_sub（thm）
theorem one_le_abs_intCast_sub {a b : ℤ} (hne : a ≠ b) : (1 : ℝ) ≤ |((a - b : ℤ) : ℝ)|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::half_le_abs_padicValRat_sub_half、PAG254::dP_lt_one_iff、PAG254::padicValRat_eq_of_chainIn、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification、PAG254::dP_mul_left、PAG254::chainIn_dP_of_one_lt、PAG254::abs_log_sub_log_le

### 対象 PAG259::padicValRat_mul_zpow_zpow（thm）
theorem padicValRat_mul_zpow_zpow {p r t : ℕ} (hp : p.Prime) (hr : r.Prime) (ht : t.Prime)
    {q₀ : ℚ} (hq₀ : q₀ ≠ 0) (a b : ℤ) :
    padicValRat t (q₀ * (p : ℚ) ^ a * (r : ℚ) ^ b) =
      padicValRat t q₀ + (if t = p then a else 0) + (if t = r then b else 0)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dP_mul_left、PAG254::exists_padicValRat_eq、PAG254::dInf_mul_left、PAG254::dInf_zpow、PAG254::eq_of_chainIn_primePow、PAG254::emergence_contrast、PAG254::log_inj、PAG12::pow_p_pow_congr

### 対象 PAG259::padicValRat_prime_ne（thm）
theorem padicValRat_prime_ne {s p : ℕ} (hs : s.Prime) (hp : p.Prime) (hne : s ≠ p) :
    padicValRat s (p : ℚ) = 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::exists_padicValRat_eq、PAG254::emergence_contrast、PAG254::dInf_zpow、PAG254::dP_mul_left、PAG254::dP_lt_one_iff、PAG254::eq_of_chainIn_primePow、PAG254::half_le_abs_padicValRat_sub_half、PAG254::dP_eq_dist

### 対象 PAG259::padicValRat_prime_zpow（thm）
theorem padicValRat_prime_zpow {s p : ℕ} (hs : s.Prime) (hp : p.Prime) (k : ℤ) :
    padicValRat s ((p : ℚ) ^ k) = if s = p then k else 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dInf_zpow、PAG254::eq_of_chainIn_primePow、PAG254::exists_padicValRat_eq、PAG254::emergence_contrast、PAG254::dP_lt_one_iff、PAG254::half_le_abs_padicValRat_sub_half、PAG254::dP_mul_left、PAG254::dP_eq_dist

### 対象 PAG259::padicValRat_prod_zpow（thm）
theorem padicValRat_prod_zpow (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (k : ℕ → ℤ) {t : ℕ}
    (ht : t.Prime) :
    padicValRat t (∏ s ∈ S, (s : ℚ) ^ (k s)) = if t ∈ S then k t else 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dInf_zpow、PAG254::eq_of_chainIn_primePow、PAG254::exists_padicValRat_eq、PAG162::count_set、PAG254::emergence_contrast、PAG188::prod_root_of_root、PAG179::InQi_prod、PAG254::dP_lt_one_iff

### 対象 PAG259::rho（def）
noncomputable def rho (q : ℚ) : ℝ × (Nat.Primes → ℤ) := (Real.log q, fun p => padicValRat p q)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::logSet、PAG254::dInf、PAG176::InQi、PAG254::dP、PAG176::InQω、PAG23::P1F、PAG254::posRat、PAG253::primeShiftInv

### 対象 PAG259::rhoBox（def）
noncomputable def rhoBox (q : ℚ) : ℝ × BoxCoord := (Real.log q, fun p => padicValRat p q)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::logSet、PAG254::dInf、PAG176::InQi、PAG254::dP、PAG176::InQω、PAG23::P1F、PAG254::posRat、PAG253::primeShiftInv

### 対象 PAG259::rho_one（thm）
theorem rho_one : rho 1 = (0, 0)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::log_inj、PAG254::logSet_countable、PAG254::exists_padicValRat_eq、PAG254::chainIn_dInf、PAG254::emergence_contrast、PAG254::dInf_mul_left、PAG254::dense_logSet、PAG254::not_Icc_subset_logSet

### 対象 PAG259::rho_one_mem_closure_ne_one（thm）
theorem rho_one_mem_closure_ne_one :
    rho 1 ∈ closure (rho '' {q : ℚ | 0 < q ∧ q ≠ 1})
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dense_logSet、PAG254::log_inj、PAG254::subsingleton_of_isPreconnected、PAG254::exists_padicValRat_eq、PAG254::logSet_countable、PAG254::chainIn_dInf、PAG254::emergence_contrast、PAG254::dInf_mul_left

### 対象 PAG259::rho_sep（thm）
theorem rho_sep {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (hne : q ≠ r) :
    ∃ p : Nat.Primes, (1 : ℝ) ≤ |(((rho q).2 p - (rho r).2 p : ℤ) : ℝ)|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::padicValRat_eq_of_chainIn、PAG254::emergence_contrast、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification、PAG254::half_le_abs_padicValRat_sub_half、PAG254::dP_lt_one_iff、PAG254::chainIn_dP_of_one_lt、PAG254::dP_mul_left

### 対象 PAG259::sep_of_commensurable（thm）
theorem sep_of_commensurable {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) * L₂ = m * L₁) (a b a' b' : ℤ)
    (hne : (a : ℝ) * L₁ + b * L₂ ≠ a' * L₁ + b' * L₂) :
    L₁ / n ≤ |((a : ℝ) * L₁ + b * L₂) - (a' * L₁ + b' * L₂)|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::abs_log_sub_log_le、PAG254::dense_logSet_coprime、PAG254::half_le_abs_padicValRat_sub_half、PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification、PAG254::dP_lt_one_iff

### 対象 PAG259::sep_of_inf_unmeasured（thm）
theorem sep_of_inf_unmeasured (M : Finset ℕ) {q r : ℚ}
    (hne : ∃ s ∈ M, padicValRat s q ≠ padicValRat s r) :
    ∃ s ∈ M, (1 : ℝ) ≤ |((padicValRat s q - padicValRat s r : ℤ) : ℝ)|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::half_le_abs_padicValRat_sub_half、PAG254::dP_lt_one_iff、PAG254::padicValRat_eq_of_chainIn、PAG254::dP_mul_left、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification、PAG254::chainIn_dP_of_one_lt、PAG254::dP_eq_dist

### 対象 PAG259::sep_of_mem_zmultiples（thm）
theorem sep_of_mem_zmultiples {c x y : ℝ} (hc : 0 < c) (hx : ∃ m : ℤ, x = m * c)
    (hy : ∃ n : ℤ, y = n * c) (hne : x ≠ y) : c ≤ |x - y|
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::abs_log_sub_log_le、PAG254::dense_logSet_coprime、PAG254::half_le_abs_padicValRat_sub_half、PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd、PAG254::chainIn_dP_iff、PAG254::chainIn_dP_classification、PAG254::dP_lt_one_iff

### 対象 PAG259::threshold_iff（thm）
theorem threshold_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    (∃ k : T → ℤ, ∀ x : ℝ, (x, k) ∈ closure (imgST S T)) ↔
      ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::dense_logSet、PAG254::log_inj、PAG254::subsingleton_of_isPreconnected、PAG254::exists_padicValRat_eq、PAG254::logSet_countable、PAG254::chainIn_dInf、PAG254::emergence_contrast、PAG254::dInf_mul_left

### 対象 PAG259::val_ne_of_mem_of_not_mem（thm）
theorem val_ne_of_mem_of_not_mem {I : Set Nat.Primes} {i p : Nat.Primes} (hi : i ∈ I)
    (hp : p ∉ I) : (i : ℕ) ≠ p
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG254::chainIn_refl、PAG254::chainIn_of_lt、PAG254::chainIn_invariant、PAG254::chainIn_mono、PAG219::not_dvd_of_chi_ne_zero、PAG149::fiber_digit、PAG146::twist_digit_uniform、PAG215::chi_eq_zero_of_rad

### 対象 PAG259::zpow_ge_of_one_lt（thm）
theorem zpow_ge_of_one_lt {p : ℕ} (hp : p.Prime) {k : ℤ} (hk : 1 < (p : ℝ) ^ k) :
    (p : ℝ) ≤ (p : ℝ) ^ k
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG197::pow_two_zpow、PAG181::zpow_four_comm、PAG180::zpow_six_comm、PAG188::zpow_root、PAG254::chainIn_mono、PAG254::abs_log_sub_log_le、PAG89::lam_nonneg、PAG46::lam_pos

######## PAG260.lean（Part 256）
-- 文脈（open・variable・namespace の行の写し）
open DirichletCharacter ZMod Complex
namespace PAG.Part260
variable {M N : ℕ} [NeZero M] [NeZero N]
open Classical in
end PAG.Part260

### 対象 PAG260::UA1_charU_prodChar（thm）
theorem UA1_charU_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    PAG.Part258.UA1 (PAG.Part257.charU (prodChar χ₁ χ₂)) =
      (crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂)) •
        PAG.Part257.charU (prodChar χ₁ χ₂)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG258::ip_UA1、PAG258::UA1_star、PAG258::UA1_charU、PAG258::UA1_bijective、PAG258::UA1_mem_Vprim、PAG258::UA1_mem_Vimprim、PAG258::UA1_mem_condPart

### 対象 PAG260::cast_crtMap_fst（thm）
theorem cast_crtMap_fst (x : ZMod M × ZMod N) :
    ((crtMap M N x : ZMod (M * N)).cast : ZMod M) = x.1 * (N : ZMod M)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG143::P_mul_eq_zero_iff、PAG236::cast_crt_fst、PAG236::cast_crt_snd、PAG139::cast_eq_of_P、PAG143::freq_unique、PAG154::chi_pow_of_cast_eq、PAG114::tens_smul_left、PAG140::isUnit_iff_cast_ne_zero

### 対象 PAG260::cast_crtMap_snd（thm）
theorem cast_crtMap_snd (x : ZMod M × ZMod N) :
    ((crtMap M N x : ZMod (M * N)).cast : ZMod N) = x.2 * (M : ZMod N)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG143::P_mul_eq_zero_iff、PAG236::cast_crt_fst、PAG236::cast_crt_snd、PAG139::cast_eq_of_P、PAG143::freq_unique、PAG154::chi_pow_of_cast_eq、PAG114::tens_smul_left、PAG140::isUnit_iff_cast_ne_zero

### 対象 PAG260::charU_prodChar（thm）
theorem charU_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (u : (ZMod (M * N))ˣ) :
    PAG.Part257.charU (prodChar χ₁ χ₂) u =
      PAG.Part257.charU χ₁ (ZMod.unitsMap (dvd_mul_right M N) u) *
        PAG.Part257.charU χ₂ (ZMod.unitsMap (dvd_mul_left N M) u)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG195::sq_mul_changeLevel、PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG194::isPrimitive_mul、PAG193::mul_changeLevel_apply、PAG236::charMul_mul、PAG193::gaussSum_mul_coprime、PAG236::charMul_inv

### 対象 PAG260::crossSign（def）
open Classical in
noncomputable def crossSign (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
  if χ₁.Odd ∧ χ₂.Odd then -1 else 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG171::ω、PAG2::Wpow、PAG221::layerInd、PAG171::InZω、PAG180::Rep2、PAG221::layerDivs、PAG176::InQω、PAG220::layerIdx

### 対象 PAG260::crossSign_of_even_left（thm）
omit [NeZero M] [NeZero N] in
theorem crossSign_of_even_left {χ₁ : DirichletCharacter ℂ M} (χ₂ : DirichletCharacter ℂ N)
    (h1 : χ₁.Even) : crossSign χ₁ χ₂ = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::exists_primitive_odd_three、PAG258::rootNum_one_prime、PAG256::exists_primitive_even_five、PAG256::parFac_of_odd、PAG2::parity_weight、PAG153::orderOf_of_sq_neg_one、PAG257::rootNum_ne_zero

### 対象 PAG260::crossSign_of_even_right（thm）
omit [NeZero M] [NeZero N] in
theorem crossSign_of_even_right (χ₁ : DirichletCharacter ℂ M) {χ₂ : DirichletCharacter ℂ N}
    (h2 : χ₂.Even) : crossSign χ₁ χ₂ = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::exists_primitive_odd_three、PAG258::rootNum_one_prime、PAG256::exists_primitive_even_five、PAG256::parFac_of_odd、PAG2::parity_weight、PAG153::orderOf_of_sq_neg_one、PAG257::rootNum_ne_zero

### 対象 PAG260::crossSign_of_odd（thm）
omit [NeZero M] [NeZero N] in
theorem crossSign_of_odd {χ₁ : DirichletCharacter ℂ M} {χ₂ : DirichletCharacter ℂ N}
    (h1 : χ₁.Odd) (h2 : χ₂.Odd) : crossSign χ₁ χ₂ = -1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::exists_primitive_odd_three、PAG256::parFac_of_odd、PAG153::orderOf_of_sq_neg_one、PAG257::gaussSum_one_prime、PAG72::prim4_neg_one、PAG151::neg_one_mod4、PAG172::quartic_eq_one、PAG151::phase_mod4

### 対象 PAG260::cross_eq_sign_of_rootNum_one（thm）
theorem cross_eq_sign_of_rootNum_one (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) (w1 : PAG.Part256.rootNum χ₁ = 1)
    (w2 : PAG.Part256.rootNum χ₂ = 1) (w12 : PAG.Part256.rootNum (prodChar χ₁ χ₂) = 1) :
    crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG194::isPrimitive_mul、PAG193::gaussSum_mul_coprime、PAG193::z_mul_coprime、PAG195::sq_mul_changeLevel、PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG193::composite_root_iff、PAG193::mul_changeLevel_apply

### 対象 PAG260::crtMap（def）
def crtMap (M N : ℕ) [NeZero M] [NeZero N] (x : ZMod M × ZMod N) : ZMod (M * N) :=
  ((x.1.val * N + x.2.val * M : ℕ) : ZMod (M * N))
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG193::param、PAG236::tens、PAG108::tens、PAG27::Unimod、PAG23::W、PAG23::P1F、PAG23::Compat、PAG238::gaugeP

### 対象 PAG260::crtMap_bijective（thm）
theorem crtMap_bijective (h : M.Coprime N) : Function.Bijective (crtMap M N)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG193::param_bijective、PAG37::pm5_bijective、PAG236::primMul_bijective、PAG194::rho_bijective、PAG114::tens_smul_left、PAG108::tens_sum、PAG199::tens_smul_smul、PAG27::swap_unimod

### 対象 PAG260::exists_primitive_odd_five（thm）
theorem exists_primitive_odd_five : ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Odd
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::exists_primitive_odd_three、PAG256::parFac_of_odd、PAG72::exists_prim4、PAG195::squarefull_root、PAG200::exists_split、PAG72::prim4_unique、PAG144::exists_primitive、PAG256::exists_primitive_even_five

### 対象 PAG260::gaussSum_prodChar（thm）
theorem gaussSum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    gaussSum (prodChar χ₁ χ₂) stdAddChar =
      χ₁ (N : ZMod M) * χ₂ (M : ZMod N) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG194::isPrimitive_mul、PAG193::gaussSum_mul_coprime、PAG195::sq_mul_changeLevel、PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG193::z_mul_coprime、PAG193::mul_changeLevel_apply、PAG193::composite_root_iff

### 対象 PAG260::isPrimitive_prodChar（thm）
theorem isPrimitive_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (prodChar χ₁ χ₂).IsPrimitive
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG194::isPrimitive_mul、PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG195::sq_mul_changeLevel、PAG193::mul_changeLevel_apply、PAG236::isPrimitive_charMul、PAG193::gaussSum_mul_coprime、PAG236::charMul_injective

### 対象 PAG260::norm_char_unit（thm）
theorem norm_char_unit {n : ℕ} (χ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) : ‖χ a‖ = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG190::norm_z、PAG253::norm_eq_one_of_isometry、PAG190::norm_prod_z、PAG190::coord_bound、PAG253::eigenFun_of_commute_prime、PAG190::finite_of_bounded、PAG189::norm_eq_one_of_toZMod_ne_zero、PAG253::thm26_full_of_commute

### 対象 PAG260::norm_cross（thm）
omit [NeZero M] [NeZero N] in
theorem norm_cross (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    ‖χ₁ (N : ZMod M) * χ₂ (M : ZMod N)‖ = 1
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG190::norm_z、PAG253::norm_eq_one_of_isometry、PAG190::norm_prod_z、PAG190::coord_bound、PAG253::eigenFun_of_commute_prime、PAG190::finite_of_bounded、PAG189::norm_eq_one_of_toZMod_ne_zero、PAG189::toZMod_eq_zero_iff

### 対象 PAG260::parFac_prodChar（thm）
theorem parFac_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.parFac (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * PAG.Part256.parFac χ₁ * PAG.Part256.parFac χ₂
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG256::parFac_of_odd、PAG195::sq_mul_changeLevel、PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG194::isPrimitive_mul、PAG256::parFac_of_even、PAG193::mul_changeLevel_apply、PAG193::gaussSum_mul_coprime

### 対象 PAG260::phaseA1_prodChar（thm）
theorem phaseA1_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    PAG.Part258.phaseA1 (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG258::phaseA1_changeLevel、PAG258::phaseA1_of_isPrimitive、PAG258::phaseA1_one、PAG194::isPrimitive_mul、PAG258::phaseA1_inv、PAG194::isPrimitive_right、PAG194::isPrimitive_left

### 対象 PAG260::phaseA1_prodChar_ne_mul（thm）
theorem phaseA1_prodChar_ne_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      PAG.Part258.phaseA1 (prodChar χ₁ χ₂) ≠ PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG258::phaseA1_changeLevel、PAG258::phaseA1_of_isPrimitive、PAG258::phaseA1_one、PAG258::phaseA1_inv、PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG195::sq_mul_changeLevel

### 対象 PAG260::prodChar（def）
noncomputable def prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ (M * N) :=
  changeLevel (dvd_mul_right M N) χ₁ * changeLevel (dvd_mul_left N M) χ₂
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG236::charMul、PAG199::cmul、PAG236::primMul、PAG236::primEquiv、PAG194::rho、PAG238::kronG、PAG210::liftc、PAG237::gaugeUnit

### 対象 PAG260::prodChar_apply（thm）
theorem prodChar_apply (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (a : ZMod (M * N)) :
    prodChar χ₁ χ₂ a = χ₁ (a.cast : ZMod M) * χ₂ (a.cast : ZMod N)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG236::charMul_apply、PAG195::sq_mul_changeLevel、PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG236::charMul_apply_unit、PAG194::isPrimitive_mul、PAG193::mul_changeLevel_apply、PAG236::charMul_mul

### 対象 PAG260::prodChar_neg_one（thm）
theorem prodChar_neg_one (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    prodChar χ₁ χ₂ (-1) = χ₁ (-1) * χ₂ (-1)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG195::sq_mul_changeLevel、PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG194::isPrimitive_mul、PAG193::mul_changeLevel_apply、PAG236::charMul_mul、PAG193::gaussSum_mul_coprime、PAG236::charMul_inv

### 対象 PAG260::rootNum_prodChar（thm）
theorem rootNum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.rootNum (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂)
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG194::isPrimitive_mul、PAG193::gaussSum_mul_coprime、PAG193::z_mul_coprime、PAG195::sq_mul_changeLevel、PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG193::composite_root_iff、PAG193::mul_changeLevel_apply

### 対象 PAG260::rootNum_prodChar_eq_neg_mul（thm）
theorem rootNum_prodChar_eq_neg_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 13), χ₁.IsPrimitive ∧
      χ₂.IsPrimitive ∧ χ₁.Odd ∧ χ₂.Odd ∧ χ₁ ((13 : ℕ) : ZMod 3) * χ₂ ((3 : ℕ) : ZMod 13) = 1 ∧
      PAG.Part256.rootNum (prodChar χ₁ χ₂) =
        -(PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂) ∧
      PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂ ≠ 0
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG195::sq_mul_changeLevel、PAG193::z_mul_coprime、PAG194::isPrimitive_mul、PAG193::pq_root_iff、PAG193::gaussSum_mul_coprime、PAG193::composite_root_iff

### 対象 PAG260::rootNum_prodChar_ne_mul（thm）
theorem rootNum_prodChar_ne_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      χ₁.Odd ∧ χ₂.Odd ∧
      PAG.Part256.rootNum (prodChar χ₁ χ₂) ≠ PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG194::isPrimitive_right、PAG194::isPrimitive_left、PAG195::sq_mul_changeLevel、PAG193::z_mul_coprime、PAG194::isPrimitive_mul、PAG193::pq_root_iff、PAG193::gaussSum_mul_coprime、PAG193::composite_root_iff

### 対象 PAG260::stdAddChar_crtMap（thm）
theorem stdAddChar_crtMap (x : ZMod M × ZMod N) :
    stdAddChar (crtMap M N x) = stdAddChar x.1 * stdAddChar x.2
候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：PAG117::stdAddChar_mul_cast、PAG193::stdAddChar_param、PAG140::exists_delta、PAG152::e8_pow、PAG142::freq_mul、PAG2::addChar_sum、PAG127::stdAddChar_pow_eq_one_iff
