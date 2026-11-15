/-
  PAG 2.0 Part 183（2026-10-23）— 単独ケットの完全な判定（素数冪の導手、すべての素数）
  χ は法 p^c（c ≥ 1）の原始指標、z = τ(χ)/√(p^c)（τ は stdAddChar のガウス和）。
  1. c ≥ 2、p 奇素数：z は 1 の冪根（Part 124 の位数の上界 ord z ∣ lcm(ord χ, p^c, 4)）
  2. c ≥ 2、p = 2：c 偶数と c ≥ 5 の奇数は Part 126（ord z = 2^c）。c = 3 は z⁴ = 1
     （法 8 の指標は χ² = 1 なので χ⁻¹ = χ、Part 169 の z(χ)z(χ⁻¹) = χ(−1) から z² = χ(−1)）
  3. c = 1：Part 181（z が 1 の冪根 ⇔ ord χ = 2）を素数 p¹ に適用
  4. single_root_iff：z が 1 の冪根 ⇔ c ≥ 2 または ord χ = 2
  5. 系：ζ = z^{ord χ} でも同じ（single_zeta_root_iff）、位数の形（single_orderOf_ne_zero_iff）、
     p 奇素数・法 p では z が 1 の冪根 ⇔ χ = L（root_iff_eq_L）
-/
import PAG186

namespace PAG.Part187

open Complex Finset
open ZMod (stdAddChar)

/-! ### 1. 1 の冪根の言い換え -/

/-- k > 0 なら、x^k が 1 の冪根 ⇔ x が 1 の冪根。 -/
theorem root_pow_iff (x : ℂ) (k : ℕ) (hk : 0 < k) :
    (∃ N : ℕ, 0 < N ∧ (x ^ k) ^ N = 1) ↔ (∃ N : ℕ, 0 < N ∧ x ^ N = 1) := by
  constructor
  · rintro ⟨N, hN, h⟩
    exact ⟨k * N, Nat.mul_pos hk hN, by rw [pow_mul]; exact h⟩
  · rintro ⟨N, hN, h⟩
    exact ⟨N, hN, by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]⟩

/-- 位数が 0 でない ⇔ 1 の冪根。 -/
theorem orderOf_ne_zero_iff_root (x : ℂ) : orderOf x ≠ 0 ↔ ∃ N : ℕ, 0 < N ∧ x ^ N = 1 := by
  rw [Ne, orderOf_eq_zero_iff']
  push Not
  rfl

/-! ### 2. c ≥ 2 -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- **2a. p 奇素数・c ≥ 2**：z は 1 の冪根。 -/
theorem root_of_two_le_odd (hp2 : p ≠ 2) (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (p ^ c))
    (hχ : χ.IsPrimitive) :
    ∃ N : ℕ, 0 < N ∧ (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N = 1 := by
  have h := (PAG.Part128.orderOf_gauss_bounds hp2 c hc χ hχ).2
  refine ⟨Nat.lcm (Nat.lcm (orderOf χ) (p ^ c)) 4,
    Nat.lcm_pos (Nat.lcm_pos (orderOf_pos χ) (pow_pos hp.out.pos c)) (by norm_num), ?_⟩
  exact orderOf_dvd_iff_pow_eq_one.mp h

omit hp in
/-- 法 8 の単数 u は u² = 1。 -/
theorem units_eight_sq (u : (ZMod (2 ^ 3))ˣ) : u ^ 2 = 1 := by
  revert u
  decide

omit hp in
/-- 法 8 の指標は χ² = 1。 -/
theorem chi_sq_eight (χ : DirichletCharacter ℂ (2 ^ 3)) : χ ^ 2 = 1 := by
  rw [MulChar.eq_one_iff]
  intro u
  rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, units_eight_sq, Units.val_one,
    map_one]

omit hp in
/-- **2b. p = 2・c = 3**：z⁴ = 1。 -/
theorem root_eight (χ : DirichletCharacter ℂ (2 ^ 3)) (hχ : χ.IsPrimitive) :
    (gaussSum χ stdAddChar / ((Real.sqrt ((2 : ℝ) ^ 3) : ℝ) : ℂ)) ^ 4 = 1 := by
  have hinv : χ⁻¹ = χ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact chi_sq_eight χ)
  have h := PAG.Part173.gauss_inv_pair χ hχ
  rw [hinv] at h
  have hcast : ((Real.sqrt ((2 : ℝ) ^ 3) : ℝ) : ℂ) = ((Real.sqrt ((2 ^ 3 : ℕ) : ℝ) : ℝ) : ℂ) := by
    norm_num
  have hm1 : χ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  rw [hcast, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
    sq (gaussSum χ stdAddChar / ((Real.sqrt ((2 ^ 3 : ℕ) : ℝ) : ℝ) : ℂ)), h, hm1]

omit hp in
/-- **2c. p = 2・c ≥ 2**：z は 1 の冪根。 -/
theorem root_of_two_le_two (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (2 ^ c)) (hχ : χ.IsPrimitive) :
    ∃ N : ℕ, 0 < N ∧ (gaussSum χ stdAddChar / ((Real.sqrt ((2 : ℝ) ^ c) : ℝ) : ℂ)) ^ N = 1 := by
  rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
  · have h := PAG.Part130.orderOf_gauss_two_even c m (by omega) (by omega) χ hχ
    exact ⟨2 ^ c, by positivity, orderOf_dvd_iff_pow_eq_one.mp (by rw [h])⟩
  · rcases (show m = 1 ∨ 2 ≤ m by omega) with h1 | h2
    · subst h1
      obtain rfl : c = 3 := by omega
      exact ⟨4, by norm_num, root_eight χ hχ⟩
    · have h := PAG.Part130.orderOf_gauss_two_odd c m hm h2 χ hχ
      exact ⟨2 ^ c, by positivity, orderOf_dvd_iff_pow_eq_one.mp (by rw [h])⟩

/-! ### 3. c = 1 -/

/-- **3. c = 1**：Part 181 を素数 p¹ に適用。z が 1 の冪根 ⇔ ord χ = 2。 -/
theorem root_iff_c_one (χ : DirichletCharacter ℂ (p ^ 1)) :
    (∃ N : ℕ, 0 < N ∧ (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ 1) : ℝ) : ℂ)) ^ N = 1)
      ↔ orderOf χ = 2 := by
  have : Fact (p ^ 1).Prime := ⟨by rw [pow_one]; exact hp.out⟩
  have h := PAG.Part185.zOf_root_iff (p := p ^ 1) χ
  have hcast : ((Real.sqrt ((p : ℝ) ^ 1) : ℝ) : ℂ) = ((Real.sqrt ((p ^ 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hcast]
  exact h

/-! ### 4. 主定理 -/

/-- **4. 単独ケットの完全な判定**：法 p^c（c ≥ 1）の原始指標 χ で、
  z = τ(χ)/√(p^c) が 1 の冪根 ⇔ c ≥ 2 または ord χ = 2。 -/
theorem single_root_iff (c : ℕ) (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    (∃ N : ℕ, 0 < N ∧ (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N = 1)
      ↔ (2 ≤ c ∨ orderOf χ = 2) := by
  rcases (show c = 1 ∨ 2 ≤ c by omega) with h1 | h2
  · subst h1
    rw [root_iff_c_one χ]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · omega
      · exact h
  · refine ⟨fun _ => Or.inl h2, fun _ => ?_⟩
    by_cases hp2 : p = 2
    · subst hp2
      exact root_of_two_le_two c h2 χ hχ
    · exact root_of_two_le_odd hp2 c h2 χ hχ

/-- **5a.** ζ = z^{ord χ} についても同じ判定。 -/
theorem single_zeta_root_iff (c : ℕ) (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ c))
    (hχ : χ.IsPrimitive) :
    (∃ N : ℕ, 0 < N ∧
      ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ orderOf χ) ^ N = 1)
      ↔ (2 ≤ c ∨ orderOf χ = 2) := by
  rw [root_pow_iff _ _ (orderOf_pos χ)]
  exact single_root_iff c hc χ hχ

/-- **5b.** 位数の形：ord ζ ≠ 0 ⇔ c ≥ 2 または ord χ = 2。 -/
theorem single_orderOf_ne_zero_iff (c : ℕ) (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ c))
    (hχ : χ.IsPrimitive) :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ orderOf χ) ≠ 0
      ↔ (2 ≤ c ∨ orderOf χ = 2) := by
  rw [orderOf_ne_zero_iff_root]
  exact single_zeta_root_iff c hc χ hχ

/-- **5c.** p 奇素数・法 p：z が 1 の冪根 ⇔ χ は 2 次の指標 L。 -/
theorem root_iff_eq_L (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) :
    (∃ N : ℕ, 0 < N ∧ PAG.Part184.zOf χ ^ N = 1) ↔ χ = PAG.Part119.Lc p := by
  rw [PAG.Part185.zOf_root_iff_chain]
  constructor
  · intro h2
    rcases PAG.Part182.sq_one_cases hp2 χ (by rw [← h2]; exact pow_orderOf_eq_one χ) with h | h
    · rw [h, orderOf_one] at h2; norm_num at h2
    · exact h
  · rintro rfl
    exact orderOf_eq_prime (by rw [sq]; exact PAG.Part182.Lc_mul_self) (PAG.Part119.Lc_ne_one hp2)

end PAG.Part187

#print axioms PAG.Part187.root_pow_iff
#print axioms PAG.Part187.orderOf_ne_zero_iff_root
#print axioms PAG.Part187.root_of_two_le_odd
#print axioms PAG.Part187.units_eight_sq
#print axioms PAG.Part187.chi_sq_eight
#print axioms PAG.Part187.root_eight
#print axioms PAG.Part187.root_of_two_le_two
#print axioms PAG.Part187.root_iff_c_one
#print axioms PAG.Part187.single_root_iff
#print axioms PAG.Part187.single_zeta_root_iff
#print axioms PAG.Part187.single_orderOf_ne_zero_iff
#print axioms PAG.Part187.root_iff_eq_L
