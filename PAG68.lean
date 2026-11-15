/-
  PAG 2.0 Part 64（2026-10-19）— 忠実な指標の一般論と、生成元指標の塔
  p 奇素数。
  1. 忠実な指標 χ（χ(u) = 1 ⇒ u = 1）一般について、PAG61・62 の結果を述べ直す：
     χ^j 原始 ⇔ p ∤ j、χ^j が法 p^m を経由 ⇔ |K_m| ∣ j、導手の ν_p 公式
  2. ω（PAG61）と ω''（PAG67）はどちらも忠実
  3. 塔の整合性: c'' ≤ c' ≤ c で changeLevel_{c''→c'}(ω''_{c''}) = (ω''_{c'})^(p^(c'−c''))
     （同じ最上段の生成元から作った指標は、レベルの間で添字 j ↦ p^(c'−c'') j で両立する）
-/
import PAG67

namespace PAG.Part68

open ZMod Finset PAG.Part32 PAG.Part61 PAG.Part62 PAG.Part67

variable {p : ℕ} [hp : Fact p.Prime]

/-- 忠実な指標。 -/
def Faithful {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := ∀ u : (ZMod N)ˣ, χ u = 1 → u = 1

/-- 忠実な χ について χ(1+p^c) は 1 の原始 p 乗根。 -/
theorem faithful_gp_prim {c : ℕ} (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : Faithful χ) :
    IsPrimitiveRoot (χ (gp p c)) p := by
  obtain ⟨u, hu⟩ := isUnit_gp (p := p) hc
  have hp1 : (χ (gp p c)) ^ p = 1 := by rw [← map_pow, gp_pow_p hc, map_one]
  have hne : χ (gp p c) ≠ 1 := by
    intro h
    rw [← hu] at h
    have := hχ u h
    rw [this, Units.val_one] at hu
    have e := hu.symm
    rw [gp, add_eq_left, ZMod.natCast_eq_zero_iff] at e
    exact absurd (Nat.le_of_dvd (pow_pos hp.out.pos _) e)
      (not_le.mpr (Nat.pow_lt_pow_right hp.out.one_lt (Nat.lt_succ_self c)))
  have h := IsPrimitiveRoot.orderOf (χ (gp p c))
  rwa [orderOf_eq_prime hp1 hne] at h

/-- **忠実な χ について χ^j 原始 ⇔ p ∤ j**。 -/
theorem faithful_pow_prim_iff {c : ℕ} (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : Faithful χ)
    (j : ℕ) : (χ ^ j).IsPrimitive ↔ ¬ p ∣ j := by
  obtain ⟨u, hu⟩ := isUnit_gp (p := p) hc
  rw [prim_iff_gp hc, ← hu, MulChar.pow_apply_coe, hu, ne_eq, (faithful_gp_prim hc χ hχ).pow_eq_one_iff_dvd]

/-- **忠実な χ について経由の判定**: χ^j が法 p^m を経由 ⇔ |K_m| ∣ j。 -/
theorem faithful_pow_factors_iff (hp2 : p ≠ 2) {c : ℕ} (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : Faithful χ)
    (m : ℕ) (hm : m ≤ c + 1) (j : ℕ) :
    (χ ^ j).FactorsThrough (p ^ m) ↔ Nat.card (ZMod.unitsMap (pow_dvd_pow p hm)).ker ∣ j := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have := isCyclic_units c hp2
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (pow_dvd_pow p hm),
    ← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  constructor
  · intro h u
    have hu := h u.2
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.pow_apply_coe,
      ← map_pow, ← Units.val_pow_eq_pow_val] at hu
    exact Subtype.ext (hχ _ hu)
  · intro h u hu
    have e := h ⟨u, hu⟩
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.pow_apply_coe,
      ← map_pow, ← Units.val_pow_eq_pow_val]
    have : u ^ j = 1 := congrArg Subtype.val e
    rw [this, Units.val_one, map_one]

/-- **忠実な χ の導手の ν_p 公式（m ≥ 2）**。 -/
theorem faithful_pow_conductor_iff (hp2 : p ≠ 2) {c : ℕ} (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : Faithful χ)
    (m : ℕ) (hm2 : 2 ≤ m) (hm : m ≤ c + 1) (j : ℕ) :
    (χ ^ j).conductor = p ^ m ↔ p ^ (c + 1 - m) ∣ j ∧ ¬ p ^ (c + 1 - m + 1) ∣ j := by
  rw [PAG.Part33.conductor_eq_iff (by omega) hm, faithful_pow_factors_iff hp2 χ hχ m hm,
    card_ker c m (by omega) hm, faithful_pow_factors_iff hp2 χ hχ (m - 1) (by omega),
    card_ker c (m - 1) (by omega) (by omega), show c + 1 - (m - 1) = c + 1 - m + 1 by omega]

/-- 忠実な χ の導手 p。 -/
theorem faithful_pow_conductor_p_iff (hp2 : p ≠ 2) {c : ℕ} (χ : DirichletCharacter ℂ (p ^ (c + 1)))
    (hχ : Faithful χ) (j : ℕ) :
    (χ ^ j).conductor = p ^ 1 ↔ p ^ c ∣ j ∧ ¬ phi (p := p) c ∣ j := by
  rw [PAG.Part33.conductor_eq_iff le_rfl (by omega), faithful_pow_factors_iff hp2 χ hχ 1 (by omega),
    card_ker c 1 le_rfl (by omega), Nat.sub_self, faithful_pow_factors_iff hp2 χ hχ 0 (by omega), card_ker_zero,
    show c + 1 - 1 = c by omega]

/-- ω は忠実。 -/
theorem omega_isFaithful (hp2 : p ≠ 2) (c : ℕ) : Faithful (omega c hp2) := omega_faithful c hp2

/-- ω'' は忠実。 -/
theorem omegaLow_isFaithful (hp2 : p ≠ 2) (c c' : ℕ) (hcc : c' ≤ c) : Faithful (omegaLow hp2 c c' hcc) :=
  omegaLow_faithful hp2 c c' hcc

/-- **塔の整合性**: changeLevel_{c''→c'}(ω''_{c''}) = (ω''_{c'})^(p^(c'−c''))。 -/
theorem tower_compat (hp2 : p ≠ 2) (c c' c'' : ℕ) (h1 : c'' ≤ c') (h2 : c' ≤ c) :
    DirichletCharacter.changeLevel (pow_dvd_pow p (by omega : c'' + 1 ≤ c' + 1)) (omegaLow hp2 c c'' (by omega))
      = omegaLow hp2 c c' h2 ^ (p ^ (c' - c'')) := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  apply DirichletCharacter.changeLevel_injective (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1))
  rw [← DirichletCharacter.changeLevel_trans, map_pow, changeLevel_omegaLow hp2 c c'' (by omega),
    changeLevel_omegaLow hp2 c c' h2, ← pow_mul, ← pow_add, show c - c' + (c' - c'') = c - c'' by omega]

/-- 最上段では ω''_c = ω。 -/
theorem omegaLow_top (hp2 : p ≠ 2) (c : ℕ) : omegaLow hp2 c c le_rfl = omega c hp2 := by
  have h := changeLevel_omegaLow hp2 c c le_rfl
  rw [Nat.sub_self, pow_zero, pow_one] at h
  rwa [DirichletCharacter.changeLevel_self] at h

end PAG.Part68

#print axioms PAG.Part68.Faithful
#print axioms PAG.Part68.faithful_gp_prim
#print axioms PAG.Part68.faithful_pow_prim_iff
#print axioms PAG.Part68.faithful_pow_factors_iff
#print axioms PAG.Part68.faithful_pow_conductor_iff
#print axioms PAG.Part68.faithful_pow_conductor_p_iff
#print axioms PAG.Part68.omega_isFaithful
#print axioms PAG.Part68.omegaLow_isFaithful
#print axioms PAG.Part68.tower_compat
#print axioms PAG.Part68.omegaLow_top
