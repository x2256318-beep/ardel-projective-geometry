/-
  PAG 2.0 Part 189（2026-10-23）— 互いに素な法のガウス和の積公式と、合成数の導手
  N₁, N₂ ≥ 1 は互いに素、χ₁, χ₂ は法 N₁, N₂ のディリクレ指標、χ = χ₁′χ₂′（法 N₁N₂ に持ち上げた積）、
  τ は stdAddChar のガウス和。
  1. param_bijective：(a, b) ↦ a N₂ + b N₁ は ZMod N₁ × ZMod N₂ → ZMod (N₁N₂) の全単射
  2. mul_changeLevel_apply：χ(x) = χ₁(x mod N₁)·χ₂(x mod N₂)（単数でないときも両辺 0）
  3. stdAddChar_param：e_N(a N₂ + b N₁) = e_{N₁}(a)·e_{N₂}(b)
  4. gaussSum_mul_coprime：τ(χ) = χ₁(N₂)χ₂(N₁)τ(χ₁)τ(χ₂)
  5. z_mul_coprime：z(χ) = χ₁(N₂)χ₂(N₁)·z(χ₁)z(χ₂)（z = τ/√N）、係数は 1 の冪根
  6. composite_root_iff：z(χ) が 1 の冪根 ⇔ z(χ₁)z(χ₂) が 1 の冪根
  7. pq_root_iff：相異なる素数 p, q と自明でない χ₁（法 p）、χ₂（法 q）で、
     z(χ) が 1 の冪根 ⇔ ord χ₁ = 2 かつ ord χ₂ = 2
-/
import PAG192

namespace PAG.Part193

open Complex Finset
open ZMod (stdAddChar)

/-! ### 1. 媒介変数 -/

/-- (a, b) ↦ a N₂ + b N₁（ZMod (N₁N₂) の元）。 -/
noncomputable def param (N₁ N₂ : ℕ) (x : ZMod N₁ × ZMod N₂) : ZMod (N₁ * N₂) :=
  ((x.1.val * N₂ + x.2.val * N₁ : ℕ) : ZMod (N₁ * N₂))

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]

omit [NeZero N₂] in
/-- 法 N₁ への還元：param(a, b) ≡ a N₂。 -/
theorem param_cast₁ (x : ZMod N₁ × ZMod N₂) :
    ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁) (param N₁ N₂ x) = x.1 * (N₂ : ZMod N₁) := by
  simp only [param, map_natCast]
  push_cast
  rw [ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val]

omit [NeZero N₁] in
/-- 法 N₂ への還元：param(a, b) ≡ b N₁。 -/
theorem param_cast₂ (x : ZMod N₁ × ZMod N₂) :
    ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂) (param N₁ N₂ x) = x.2 * (N₁ : ZMod N₂) := by
  simp only [param, map_natCast]
  push_cast
  rw [ZMod.natCast_self, mul_zero, zero_add, ZMod.natCast_zmod_val]

/-- **1.** N₁, N₂ が互いに素なら param は全単射。 -/
theorem param_bijective (hcop : N₁.Coprime N₂) : Function.Bijective (param N₁ N₂) := by
  have hinj : Function.Injective (param N₁ N₂) := by
    intro x y hxy
    have u₁ : IsUnit (N₂ : ZMod N₁) := (ZMod.isUnit_iff_coprime N₂ N₁).mpr hcop.symm
    have u₂ : IsUnit (N₁ : ZMod N₂) := (ZMod.isUnit_iff_coprime N₁ N₂).mpr hcop
    have h1 := congrArg (ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁)) hxy
    have h2 := congrArg (ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂)) hxy
    rw [param_cast₁, param_cast₁] at h1
    rw [param_cast₂, param_cast₂] at h2
    exact Prod.ext (u₁.mul_left_inj.mp h1) (u₂.mul_left_inj.mp h2)
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  simp [ZMod.card]

/-! ### 2. 積の指標 -/

/-- **2.** 法 N₁N₂ に持ち上げた積の指標の値：χ(x) = χ₁(x mod N₁)·χ₂(x mod N₂)。 -/
theorem mul_changeLevel_apply (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) (x : ZMod (N₁ * N₂)) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) x
      = χ₁ (ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁) x) *
        χ₂ (ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂) x) := by
  rw [MulChar.mul_apply]
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      ZMod.castHom_apply, ZMod.castHom_apply]
  · rw [MulChar.map_nonunit _ hx, zero_mul]
    -- 法 N₁ か法 N₂ のどちらかで単数でない
    have hval : ¬ (x.val.Coprime N₁ ∧ x.val.Coprime N₂) := by
      rintro ⟨h1, h2⟩
      apply hx
      have := (ZMod.isUnit_iff_coprime x.val (N₁ * N₂)).mpr (Nat.Coprime.mul_right h1 h2)
      rwa [ZMod.natCast_zmod_val] at this
    have c₁ : ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁) x = (x.val : ZMod N₁) := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    have c₂ : ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂) x = (x.val : ZMod N₂) := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    rw [c₁, c₂]
    by_cases h1 : x.val.Coprime N₁
    · have h2 : ¬ x.val.Coprime N₂ := fun h2 => hval ⟨h1, h2⟩
      rw [MulChar.map_nonunit χ₂ (fun hu => h2 ((ZMod.isUnit_iff_coprime _ _).mp hu)), mul_zero]
    · rw [MulChar.map_nonunit χ₁ (fun hu => h1 ((ZMod.isUnit_iff_coprime _ _).mp hu)), zero_mul]

/-! ### 3. 加法的指標 -/

/-- **3.** e_N(a N₂ + b N₁) = e_{N₁}(a)·e_{N₂}(b)（e は stdAddChar）。 -/
theorem stdAddChar_param (x : ZMod N₁ × ZMod N₂) :
    stdAddChar (param N₁ N₂ x) = stdAddChar x.1 * stdAddChar x.2 := by
  have hN₁ : (N₁ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N₁
  have hN₂ : (N₂ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N₂
  have e0 : param N₁ N₂ x = (((x.1.val * N₂ + x.2.val * N₁ : ℕ) : ℤ) : ZMod (N₁ * N₂)) := by
    rw [param, Int.cast_natCast]
  have e1 : x.1 = (((x.1.val : ℕ) : ℤ) : ZMod N₁) := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have e2 : x.2 = (((x.2.val : ℕ) : ℤ) : ZMod N₂) := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [e0, ZMod.stdAddChar_coe]
  conv_rhs => rw [e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp

/-! ### 4. ガウス和の積公式 -/

/-- **4. τ(χ₁′χ₂′) = χ₁(N₂)χ₂(N₁)τ(χ₁)τ(χ₂)**（N₁, N₂ は互いに素）。 -/
theorem gaussSum_mul_coprime (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar
      = χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar := by
  rw [gaussSum, ← (param_bijective hcop).sum_comp, Fintype.sum_prod_type]
  simp only [mul_changeLevel_apply, param_cast₁, param_cast₂, stdAddChar_param, map_mul]
  rw [gaussSum, gaussSum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine sum_congr rfl (fun b _ => ?_)
  ring

/-- 単数での指標の値は 1 の冪根。 -/
theorem chi_unit_root {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ u ^ orderOf u = 1 := by
  rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]

/-- **5.** z(χ) = χ₁(N₂)χ₂(N₁)·z(χ₁)z(χ₂)（z = τ/√N）で、係数 χ₁(N₂)χ₂(N₁) は 1 の冪根。 -/
theorem z_mul_coprime (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar
        / ((Real.sqrt ((N₁ * N₂ : ℕ) : ℝ) : ℝ) : ℂ)
      = χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) *
        ((gaussSum χ₁ stdAddChar / ((Real.sqrt (N₁ : ℝ) : ℝ) : ℂ)) *
          (gaussSum χ₂ stdAddChar / ((Real.sqrt (N₂ : ℝ) : ℝ) : ℂ))) ∧
      ∃ M : ℕ, 0 < M ∧ (χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂)) ^ M = 1 := by
  constructor
  · rw [gaussSum_mul_coprime hcop, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
    have h1 : ((Real.sqrt (N₁ : ℝ) : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < Real.sqrt N₁ := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N₁))
      exact_mod_cast this.ne'
    have h2 : ((Real.sqrt (N₂ : ℝ) : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < Real.sqrt N₂ := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N₂))
      exact_mod_cast this.ne'
    field_simp
  · set u₁ := ZMod.unitOfCoprime N₂ hcop.symm
    set u₂ := ZMod.unitOfCoprime N₁ hcop
    have e₁ : (N₂ : ZMod N₁) = (u₁ : ZMod N₁) := (ZMod.coe_unitOfCoprime N₂ hcop.symm).symm
    have e₂ : (N₁ : ZMod N₂) = (u₂ : ZMod N₂) := (ZMod.coe_unitOfCoprime N₁ hcop).symm
    refine ⟨orderOf u₁ * orderOf u₂, Nat.mul_pos (orderOf_pos u₁) (orderOf_pos u₂), ?_⟩
    rw [e₁, e₂, mul_pow, pow_mul, chi_unit_root, one_pow, mul_comm (orderOf u₁), pow_mul,
      chi_unit_root, one_pow, one_mul]

/-! ### 6. 1 の冪根の判定 -/

/-- **6.** z(χ₁′χ₂′) が 1 の冪根 ⇔ z(χ₁)z(χ₂) が 1 の冪根。 -/
theorem composite_root_iff (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    (∃ N : ℕ, 0 < N ∧ (gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) *
        χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar / ((Real.sqrt ((N₁ * N₂ : ℕ) : ℝ) : ℝ) : ℂ)) ^ N
          = 1) ↔
      ∃ N : ℕ, 0 < N ∧ ((gaussSum χ₁ stdAddChar / ((Real.sqrt (N₁ : ℝ) : ℝ) : ℂ)) *
        (gaussSum χ₂ stdAddChar / ((Real.sqrt (N₂ : ℝ) : ℝ) : ℂ))) ^ N = 1 := by
  obtain ⟨hz, M, hM, hc⟩ := z_mul_coprime hcop χ₁ χ₂
  rw [hz]
  exact PAG.Part183.root_mul_iff _ _ M hM hc

/-! ### 7. 導手 pq -/

/-- **7.** 相異なる素数 p, q と自明でない χ₁（法 p）、χ₂（法 q）について、導手 pq の指標 χ₁′χ₂′ の z が
  1 の冪根 ⇔ ord χ₁ = 2 かつ ord χ₂ = 2。 -/
theorem pq_root_iff {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (χ₁ : DirichletCharacter ℂ p) (χ₂ : DirichletCharacter ℂ q) (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) :
    (∃ N : ℕ, 0 < N ∧ (gaussSum (χ₁.changeLevel (dvd_mul_right p q) *
        χ₂.changeLevel (dvd_mul_left q p)) stdAddChar / ((Real.sqrt ((p * q : ℕ) : ℝ) : ℝ) : ℂ)) ^ N
          = 1) ↔ orderOf χ₁ = 2 ∧ orderOf χ₂ = 2 := by
  have hcop : p.Coprime q := (Nat.coprime_primes hp.out hq.out).mpr hpq
  rw [composite_root_iff hcop]
  have r₁ := PAG.Part185.zOf_root_iff (p := p) χ₁
  have r₂ := PAG.Part185.zOf_root_iff (p := q) χ₂
  have o₁ : 2 ≤ orderOf χ₁ := by
    have h0 := PAG.Part185.orderOf_pos_chi χ₁
    have : orderOf χ₁ ≠ 1 := fun h => h₁ (orderOf_eq_one_iff.mp h)
    omega
  have o₂ : 2 ≤ orderOf χ₂ := by
    have h0 := PAG.Part185.orderOf_pos_chi χ₂
    have : orderOf χ₂ ≠ 1 := fun h => h₂ (orderOf_eq_one_iff.mp h)
    omega
  constructor
  · intro h
    by_cases e₁ : orderOf χ₁ = 2
    · obtain ⟨M, hM, hz1⟩ := r₁.mpr e₁
      exact ⟨e₁, r₂.mp ((PAG.Part183.root_mul_iff _ _ M hM hz1).mp h)⟩
    · by_cases e₂ : orderOf χ₂ = 2
      · obtain ⟨M, hM, hz2⟩ := r₂.mpr e₂
        rw [mul_comm] at h
        exact absurd (r₁.mp ((PAG.Part183.root_mul_iff _ _ M hM hz2).mp h)) e₁
      · exfalso
        -- 両方とも位数 ≥ 3：Part 182 の判定を 2 つの素数に使う
        let P : Fin 2 → ℕ := ![p, q]
        have hP : ∀ i, Fact (P i).Prime := fun i => by
          fin_cases i
          · exact hp
          · exact hq
        have hinj : Function.Injective P := by
          intro i j hij
          fin_cases i <;> fin_cases j
          · rfl
          · exact absurd hij hpq
          · exact absurd hij.symm hpq
          · rfl
        let χ : ∀ i, MulChar (ZMod (P i)) ℂ := Fin.cons χ₁ (Fin.cons χ₂ finZeroElim)
        let ψ : ∀ i, AddChar (ZMod (P i)) ℂ := Fin.cons stdAddChar (Fin.cons stdAddChar finZeroElim)
        have hn : ∀ i, 3 ≤ orderOf (χ i) := by
          intro i
          fin_cases i
          · show 3 ≤ orderOf χ₁; omega
          · show 3 ≤ orderOf χ₂; omega
        have hψ : ∀ i, (ψ i).IsPrimitive := by
          intro i
          fin_cases i
          · exact ZMod.isPrimitive_stdAddChar p
          · exact ZMod.isPrimitive_stdAddChar q
        have key := (PAG.Part186.multi_root_iff P hinj χ hn ψ hψ (fun _ => 1)).mp (by
          obtain ⟨N, hN, hh⟩ := h
          refine ⟨N, hN, ?_⟩
          rw [Fin.prod_univ_two, zpow_one, zpow_one]
          exact hh)
        exact one_ne_zero (key 0)
  · rintro ⟨e₁, e₂⟩
    obtain ⟨M₁, hM₁, hz1⟩ := r₁.mpr e₁
    exact (PAG.Part183.root_mul_iff _ _ M₁ hM₁ hz1).mpr (r₂.mpr e₂)

end PAG.Part193

#print axioms PAG.Part193.param_cast₁
#print axioms PAG.Part193.param_cast₂
#print axioms PAG.Part193.param_bijective
#print axioms PAG.Part193.mul_changeLevel_apply
#print axioms PAG.Part193.stdAddChar_param
#print axioms PAG.Part193.gaussSum_mul_coprime
#print axioms PAG.Part193.chi_unit_root
#print axioms PAG.Part193.z_mul_coprime
#print axioms PAG.Part193.composite_root_iff
#print axioms PAG.Part193.pq_root_iff
