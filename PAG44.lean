/-
  PAG 2.0 Part 40（2026-10-19）— p = 2 の指標 χ_{s,j} の構成と、ν₂ による導手の式
  法 2^(d+3)、M = 2^(d+1)、ζ = e^(2πi/M)。単数 u = (−1)^a·5^b に対し χ_{s,j}(u) = (−1)^(sa)·ζ^(jb)。
  1. (−1)^a 5^b = (−1)^a' 5^b' ⇔ a ≡ a' (mod 2) ∧ b ≡ b' (mod M)
  2. χ_{s,j} は乗法的指標（MulChar）、χ(5) = ζ^j、χ(−1) = (−1)^s、χ_{s,j}·χ_{s',j'} = χ_{s+s',j+j'}
  3. χ_{s,j} 原始的 ⇔ j 奇数
  4. 導手 = 2^m ⇔ 2^(d+3−m) ∣ j ∧ ¬ 2^(d+4−m) ∣ j（3 ≤ m ≤ d+3）、すなわち ν₂(j) = d+3−m
-/
import PAG43

namespace PAG.Part44

open ZMod Finset PAG.Part37 Complex

variable {d : ℕ}

/-! ## 1. 表示の一意性 -/

theorem neg_one_pow_mod {G : Type*} [Monoid G] [HasDistribNeg G] (a : ℕ) : (-1 : G) ^ a = (-1) ^ (a % 2) := by
  conv_lhs => rw [← Nat.div_add_mod a 2, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

theorem orderOf_five' : orderOf (five (d + 3)) = 2 ^ (d + 1) := by
  have ho := orderOf_five (m := d + 3) (by omega)
  rwa [show d + 3 - 2 = d + 1 by omega] at ho

theorem five_pow_mod (b : ℕ) : (five (d + 3)) ^ b = (five (d + 3)) ^ (b % 2 ^ (d + 1)) := by
  have h := pow_mod_orderOf (five (d + 3)) b
  rw [orderOf_five'] at h
  exact h.symm

theorem neg_one_pow_eq_iff (a a' : ℕ) :
    ((-1 : (ZMod (2 ^ 2))ˣ) ^ a = (-1) ^ a' ↔ a % 2 = a' % 2) := by
  rw [neg_one_pow_mod a, neg_one_pow_mod a']
  have ha := Nat.mod_lt a (by norm_num : 0 < 2)
  have ha' := Nat.mod_lt a' (by norm_num : 0 < 2)
  interval_cases (a % 2) <;> interval_cases (a' % 2) <;> simp only [pow_zero, pow_one]
  all_goals first
    | (simp; done)
    | (simp; exact fun h => neg_one_ne_one_four h.symm)
    | (simp; exact neg_one_ne_one_four)

/-- **表示の一意性**: (−1)^a 5^b = (−1)^a' 5^b' ⇔ a ≡ a' (mod 2) ∧ b ≡ b' (mod 2^(d+1))。 -/
theorem pm5_eq_iff (a b a' b' : ℕ) :
    (-1 : (ZMod (2 ^ (d + 3)))ˣ) ^ a * (five (d + 3)) ^ b = (-1) ^ a' * (five (d + 3)) ^ b' ↔
      a % 2 = a' % 2 ∧ b % 2 ^ (d + 1) = b' % 2 ^ (d + 1) := by
  constructor
  · intro h
    have h4 := congrArg (toFour d) h
    simp only [map_mul, map_pow, toFour_five, one_pow, mul_one, toFour_neg_one] at h4
    have ha := (neg_one_pow_eq_iff a a').mp h4
    refine ⟨ha, ?_⟩
    rw [neg_one_pow_mod a, neg_one_pow_mod a', ha] at h
    have hb := mul_left_cancel h
    rwa [pow_inj_mod, orderOf_five'] at hb
  · rintro ⟨ha, hb⟩
    rw [neg_one_pow_mod a, neg_one_pow_mod a', ha, five_pow_mod b, five_pow_mod b', hb]

/-! ## 2. 指標の構成 -/

/-- M = 2^(d+1) と ζ = e^(2πi/M)。 -/
noncomputable def zeta (d : ℕ) : ℂ := exp (2 * Real.pi * I / ((2 ^ (d + 1) : ℕ) : ℂ))

theorem zeta_prim : IsPrimitiveRoot (zeta d) (2 ^ (d + 1)) := by
  unfold zeta; exact Complex.isPrimitiveRoot_exp (2 ^ (d + 1)) (pow_ne_zero _ two_ne_zero)

theorem zeta_pow_mod (b : ℕ) : zeta d ^ b = zeta d ^ (b % 2 ^ (d + 1)) := by
  conv_lhs => rw [← Nat.div_add_mod b (2 ^ (d + 1)), pow_add (zeta d), pow_mul (zeta d),
    (zeta_prim (d := d)).pow_eq_one, one_pow, one_mul]

theorem zeta_ne_zero : zeta d ≠ 0 := exp_ne_zero _

/-- 単数の表示 (a, b)。 -/
noncomputable def rep (d : ℕ) (u : (ZMod (2 ^ (d + 3)))ˣ) : Fin 2 × Fin (2 ^ (d + 1)) :=
  (Equiv.ofBijective (pm5 d) pm5_bijective).symm u

theorem rep_spec (u : (ZMod (2 ^ (d + 3)))ˣ) :
    u = (-1) ^ ((rep d u).1 : ℕ) * (five (d + 3)) ^ ((rep d u).2 : ℕ) := by
  have := (Equiv.ofBijective (pm5 d) pm5_bijective).apply_symm_apply u
  rw [Equiv.ofBijective_apply] at this
  exact this.symm

/-- 値 (−1)^(sa)·ζ^(jb)。 -/
noncomputable def val (d s j : ℕ) (u : (ZMod (2 ^ (d + 3)))ˣ) : ℂ :=
  (-1) ^ (s * ((rep d u).1 : ℕ)) * zeta d ^ (j * ((rep d u).2 : ℕ))

/-- 任意の表示で値が計算できる: u = (−1)^a 5^b ⇒ val u = (−1)^(sa) ζ^(jb)。 -/
theorem val_formula (s j a b : ℕ) :
    val d s j ((-1) ^ a * (five (d + 3)) ^ b) = (-1) ^ (s * a) * zeta d ^ (j * b) := by
  set u := (-1 : (ZMod (2 ^ (d + 3)))ˣ) ^ a * (five (d + 3)) ^ b
  have h := rep_spec u
  have e := (pm5_eq_iff _ _ a b).mp h.symm
  unfold val
  congr 1
  · rw [mul_comm s, mul_comm s, pow_mul (-1 : ℂ), pow_mul (-1 : ℂ), neg_one_pow_mod ((rep d u).1 : ℕ),
      neg_one_pow_mod a, e.1]
  · rw [zeta_pow_mod, zeta_pow_mod (j * b), Nat.mul_mod, e.2, ← Nat.mul_mod]

theorem val_ne_zero (s j : ℕ) (u : (ZMod (2 ^ (d + 3)))ˣ) : val d s j u ≠ 0 := by
  unfold val
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ zeta_ne_zero)

/-- 単数群の準同型（値は ℂˣ）。 -/
noncomputable def unitHom (d s j : ℕ) : (ZMod (2 ^ (d + 3)))ˣ →* ℂˣ where
  toFun u := Units.mk0 (val d s j u) (val_ne_zero s j u)
  map_one' := by
    ext
    have := val_formula (d := d) s j 0 0
    simp only [pow_zero, mul_one, mul_zero] at this
    simp [this]
  map_mul' u u' := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    rw [rep_spec u, rep_spec u']
    rw [show (-1 : (ZMod (2 ^ (d + 3)))ˣ) ^ ((rep d u).1 : ℕ) * five (d + 3) ^ ((rep d u).2 : ℕ) *
        ((-1) ^ ((rep d u').1 : ℕ) * five (d + 3) ^ ((rep d u').2 : ℕ))
        = (-1) ^ (((rep d u).1 : ℕ) + ((rep d u').1 : ℕ)) * five (d + 3) ^ (((rep d u).2 : ℕ) + ((rep d u').2 : ℕ)) by
      rw [pow_add (-1 : (ZMod (2 ^ (d + 3)))ˣ), pow_add (five (d + 3))]; exact mul_mul_mul_comm _ _ _ _]
    rw [val_formula, val_formula, val_formula, mul_add, mul_add, pow_add (-1 : ℂ), pow_add (zeta d)]
    ring

/-- **指標 χ_{s,j}**。 -/
noncomputable def chiSJ (d s j : ℕ) : DirichletCharacter ℂ (2 ^ (d + 3)) := MulChar.ofUnitHom (unitHom d s j)

theorem chiSJ_unit (s j : ℕ) (u : (ZMod (2 ^ (d + 3)))ˣ) : chiSJ d s j (u : ZMod _) = val d s j u := by
  rw [chiSJ, MulChar.ofUnitHom_coe]; rfl

/-- χ_{s,j}(5) = ζ^j。 -/
theorem chiSJ_five (s j : ℕ) : chiSJ d s j 5 = zeta d ^ j := by
  rw [← five_val, chiSJ_unit, show five (d + 3) = (-1) ^ 0 * five (d + 3) ^ 1 by simp, val_formula]
  simp

/-- χ_{s,j}(−1) = (−1)^s。 -/
theorem chiSJ_neg_one (s j : ℕ) : chiSJ d s j (-1) = (-1) ^ s := by
  have : (((-1 : (ZMod (2 ^ (d + 3)))ˣ) : ZMod (2 ^ (d + 3)))) = -1 := by simp
  rw [← this, chiSJ_unit, show (-1 : (ZMod (2 ^ (d + 3)))ˣ) = (-1) ^ 1 * five (d + 3) ^ 0 by simp, val_formula]
  simp

/-- **積**: χ_{s,j}·χ_{s',j'} = χ_{s+s',j+j'}。 -/
theorem chiSJ_mul (s j s' j' : ℕ) : chiSJ d s j * chiSJ d s' j' = chiSJ d (s + s') (j + j') := by
  apply MulChar.ext
  intro u
  rw [MulChar.coeToFun_mul, Pi.mul_apply, chiSJ_unit, chiSJ_unit, chiSJ_unit, rep_spec u,
    val_formula, val_formula, val_formula, add_mul, add_mul, pow_add (-1 : ℂ), pow_add (zeta d)]
  ring

/-! ## 3. 原始性と導手 -/

/-- 2^a ∣ j·2^b ⇔ 2^(a−b) ∣ j（b ≤ a）。 -/
theorem two_pow_dvd_mul_iff {a b j : ℕ} (hb : b ≤ a) : 2 ^ a ∣ j * 2 ^ b ↔ 2 ^ (a - b) ∣ j := by
  rw [show 2 ^ a = 2 ^ (a - b) * 2 ^ b by rw [← pow_add]; congr 1; omega]
  exact Nat.mul_dvd_mul_iff_right (by positivity)

/-- **χ_{s,j} 原始的 ⇔ j 奇数**。 -/
theorem chiSJ_prim_iff (s j : ℕ) : (chiSJ d s j).IsPrimitive ↔ Odd j := by
  rw [prim_iff_five, chiSJ_five, ← pow_mul, ne_eq, (zeta_prim (d := d)).pow_eq_one_iff_dvd,
    two_pow_dvd_mul_iff (by omega), show d + 1 - d = 1 by omega, pow_one, ← even_iff_two_dvd, Nat.not_even_iff_odd]

/-- **導手の ν₂ 公式**: 導手 = 2^m ⇔ 2^(d+3−m) ∣ j ∧ ¬ 2^(d+4−m) ∣ j（3 ≤ m ≤ d+3）。 -/
theorem chiSJ_conductor_iff (s j : ℕ) {m : ℕ} (hm3 : 3 ≤ m) (hm : m ≤ d + 3) :
    (chiSJ d s j).conductor = 2 ^ m ↔ 2 ^ (d + 3 - m) ∣ j ∧ ¬ 2 ^ (d + 4 - m) ∣ j := by
  rw [conductor_eq_iff_five hm3 hm, chiSJ_five, ← pow_mul, ← pow_mul, ne_eq,
    (zeta_prim (d := d)).pow_eq_one_iff_dvd, (zeta_prim (d := d)).pow_eq_one_iff_dvd,
    two_pow_dvd_mul_iff (by omega), two_pow_dvd_mul_iff (by omega),
    show d + 1 - (m - 2) = d + 3 - m by omega, show d + 1 - (m - 3) = d + 4 - m by omega]

/-- **積の導手の ν₂ 公式**（Part 27 の閉じた式）: 導手(χ_{s,j}χ_{s',j'}) = 2^m ⇔ ν₂(j+j') = d+3−m。 -/
theorem chiSJ_mul_conductor_iff (s j s' j' : ℕ) {m : ℕ} (hm3 : 3 ≤ m) (hm : m ≤ d + 3) :
    (chiSJ d s j * chiSJ d s' j').conductor = 2 ^ m ↔
      2 ^ (d + 3 - m) ∣ (j + j') ∧ ¬ 2 ^ (d + 4 - m) ∣ (j + j') := by
  rw [chiSJ_mul, chiSJ_conductor_iff _ _ hm3 hm]

/-- 導手 4 ⇔ 2^(d+1) ∣ j ∧ s 奇数。 -/
theorem chiSJ_conductor_four_iff (s j : ℕ) :
    (chiSJ d s j).conductor = 2 ^ 2 ↔ 2 ^ (d + 1) ∣ j ∧ Odd s := by
  rw [conductor_eq_four_iff, chiSJ_five, chiSJ_neg_one, (zeta_prim (d := d)).pow_eq_one_iff_dvd]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases Nat.even_or_odd s with ⟨k, rfl⟩ | hs
    · exfalso; apply h2; rw [← two_mul, pow_mul, neg_one_sq, one_pow]
    · exact hs
  · rintro ⟨h1, ⟨k, rfl⟩⟩
    refine ⟨h1, ?_⟩
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    norm_num

end PAG.Part44

#print axioms PAG.Part44.neg_one_pow_mod
#print axioms PAG.Part44.orderOf_five'
#print axioms PAG.Part44.five_pow_mod
#print axioms PAG.Part44.neg_one_pow_eq_iff
#print axioms PAG.Part44.pm5_eq_iff
#print axioms PAG.Part44.zeta
#print axioms PAG.Part44.zeta_prim
#print axioms PAG.Part44.zeta_pow_mod
#print axioms PAG.Part44.zeta_ne_zero
#print axioms PAG.Part44.rep
#print axioms PAG.Part44.rep_spec
#print axioms PAG.Part44.val
#print axioms PAG.Part44.val_formula
#print axioms PAG.Part44.val_ne_zero
#print axioms PAG.Part44.unitHom
#print axioms PAG.Part44.chiSJ
#print axioms PAG.Part44.chiSJ_unit
#print axioms PAG.Part44.chiSJ_five
#print axioms PAG.Part44.chiSJ_neg_one
#print axioms PAG.Part44.chiSJ_mul
#print axioms PAG.Part44.two_pow_dvd_mul_iff
#print axioms PAG.Part44.chiSJ_prim_iff
#print axioms PAG.Part44.chiSJ_conductor_iff
#print axioms PAG.Part44.chiSJ_mul_conductor_iff
#print axioms PAG.Part44.chiSJ_conductor_four_iff
