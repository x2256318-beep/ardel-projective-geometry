/-
  PAG 2.0 Part 28（2026-10-19）
  1. 射影直線 ProjLine(p^K) 上の反転共役 ~_proj（Φ ↦ conj ∘ Φ ∘ [a:b ↦ −a:b]）と、
     {1, W, ~, W~} の作用（B_S^proj, B_N^proj との可換性、ケット・べき等元への作用）
  2. 一般の素数 p の原始性判定: 法 p^(c+1)（c ≥ 1）で g = 1 + p^c とすると
     χ が原始的 ⇔ χ(g) ≠ 1、積 χ₁χ₂ が原始的 ⇔ χ₁(g)χ₂(g) ≠ 1。法 p では 原始的 ⇔ χ ≠ 1。
-/
import PAG31

namespace PAG.Part32

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part23 PAG.Part25 PAG.Part26
  PAG.Part27 PAG.Part28 PAG.Part29 PAG.Part30 PAG.Part31

/-! ## 1. 射影直線上の反転共役 -/

section ProjTilde

variable {N : ℕ}

/-- 射影直線の反転 [a:b] ↦ [−a:b]（well-defined）。 -/
def negProj : ProjLine N → ProjLine N :=
  Quotient.lift (fun v : Unimod N => mk ⟨(-v.1.1, v.1.2), by
      obtain ⟨s, t, h⟩ := v.2; exact ⟨-s, t, by rw [neg_mul_neg]; exact h⟩⟩)
    (fun _v _w ⟨u, h1, h2⟩ => mk_eq_mk u (by simp [h1]) h2)

theorem negProj_negProj (q : ProjLine N) : negProj (negProj q) = q := by
  induction q using Quotient.inductionOn with
  | h v => exact mk_eq_mk 1 (by simp) (by simp)

theorem negProj_south (x : ZMod N) :
    negProj (mk ⟨(x, 1), 0, 1, by simp⟩ : ProjLine N) = mk ⟨(-x, 1), 0, 1, by simp⟩ := rfl

theorem negProj_north (y : ZMod N) :
    negProj (mk ⟨(1, y), 1, 0, by simp⟩ : ProjLine N) = mk ⟨(1, -y), 1, 0, by simp⟩ :=
  mk_eq_mk (-1) (by simp) (by simp)

/-- 射影直線上の反転共役 ~_proj Φ = conj ∘ Φ ∘ negProj。 -/
noncomputable def tildePull (Φ : ProjLine N → ℂ) : ProjLine N → ℂ := fun q => starRingEnd ℂ (Φ (negProj q))

theorem tildePull_tildePull (Φ : ProjLine N → ℂ) : tildePull (tildePull Φ) = Φ := by
  funext q; simp [tildePull, negProj_negProj]

end ProjTilde

section ProjTildeK

variable {p : ℕ} [hp : Fact p.Prime] (K : ℕ) (hK : 1 ≤ K)

/-- **~_proj は 2 チャートの ~ に対応**。 -/
theorem projFun_tilde (Φ : ProjLine (p ^ K) → ℂ) :
    (projFunEquiv K hK (tildePull Φ)).1 = tildeP1 (projFunEquiv K hK Φ).1 := by
  ext y
  · rw [projFun_south]
    show starRingEnd ℂ (Φ (negProj _)) = starRingEnd ℂ ((projFunEquiv K hK Φ).1.1 (-y))
    rw [projFun_south]; rfl
  · rw [projFun_north]
    show starRingEnd ℂ (Φ (negProj _)) = starRingEnd ℂ ((projFunEquiv K hK Φ).1.2 (-y))
    rw [projFun_north, negProj_north]

include hK in
/-- **~_proj と W_proj は可換**。 -/
theorem tildePull_Wpull (Φ : ProjLine (p ^ K) → ℂ) : tildePull (Wpull Φ) = Wpull (tildePull Φ) := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  rw [projFun_tilde, projFun_Wpull, projFun_Wpull, projFun_tilde]
  rfl

/-- **B_S^proj と ~_proj の可換性**。 -/
theorem BSproj_tilde (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    BSproj K hK (tildePull Φ) (tildePull Ψ) = tildePull (BSproj K hK Φ Ψ) := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  rw [projFun_BSproj, projFun_tilde, projFun_tilde, projFun_tilde, projFun_BSproj, BS_tilde]

/-- **B_N^proj と ~_proj の可換性**。 -/
theorem BNproj_tilde (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    BNproj K hK (tildePull Φ) (tildePull Ψ) = tildePull (BNproj K hK Φ Ψ) := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  rw [projFun_BNproj, projFun_tilde, projFun_tilde, projFun_tilde, projFun_BNproj, BN_tilde]

/-- **~_proj|w,χ⟩_S = χ(−1)|w,χ̄⟩_S**（射影直線上）。 -/
theorem tildePull_ketS (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    tildePull (ketS_proj K hK w c h χ) = χ (-1) • ketS_proj K hK w c h χ⁻¹ := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  simp only [LinearEquiv.map_smul, Submodule.coe_smul, projFun_tilde, projFun_ketS]
  exact tildeP1_kS K w c h χ

/-- **~_proj|−w,χ⟩_N = χ(−1)|−w,χ̄⟩_N**（射影直線上）。 -/
theorem tildePull_ketN (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    tildePull (ketN_proj K hK w c h χ) = χ (-1) • ketN_proj K hK w c h χ⁻¹ := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  simp only [LinearEquiv.map_smul, Submodule.coe_smul, projFun_tilde, projFun_ketN]
  exact tildeP1_kN K w c h χ

/-- **W_proj ~_proj|w,χ⟩_S = χ(−1)|−w,χ⟩_N**（射影直線上）。 -/
theorem Wpull_tildePull_ketS (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    Wpull (tildePull (ketS_proj K hK w c h χ)) = χ (-1) • ketN_proj K hK w c h χ := by
  rw [tildePull_ketS]
  have : Wpull (χ (-1) • ketS_proj K hK w c h χ⁻¹) = χ (-1) • Wpull (ketS_proj K hK w c h χ⁻¹) := rfl
  rw [this, Wpull_ketS_proj, inv_inv]

/-- ε^S_proj, ε^N_proj は ~_proj で不変。 -/
theorem tildePull_epsS (a : ℕ) : tildePull (epsS_proj (p := p) K hK a) = epsS_proj (p := p) K hK a := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  rw [projFun_tilde, projFun_epsS, tildeP1_epsS]

theorem tildePull_epsN (a : ℕ) : tildePull (epsN_proj (p := p) K hK a) = epsN_proj (p := p) K hK a := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  rw [projFun_tilde, projFun_epsN, tildeP1_epsN]

end ProjTildeK

/-! ## 2. 一般の素数での原始性判定 -/

section Prim

variable {p : ℕ} [hp : Fact p.Prime] {c : ℕ}

/-- 核の生成元 g = 1 + p^c ∈ Z/p^(c+1)。 -/
def gp (p c : ℕ) : ZMod (p ^ (c + 1)) := 1 + ((p ^ c : ℕ) : ZMod (p ^ (c + 1)))

omit hp in
theorem pc_sq (hc : 1 ≤ c) :
    ((p ^ c : ℕ) : ZMod (p ^ (c + 1))) * ((p ^ c : ℕ) : ZMod (p ^ (c + 1))) = 0 := by
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ← pow_add]
  exact pow_dvd_pow p (by omega)

omit hp in
/-- g^t = 1 + t·p^c。 -/
theorem gp_pow (hc : 1 ≤ c) (t : ℕ) :
    gp p c ^ t = 1 + (t : ZMod (p ^ (c + 1))) * ((p ^ c : ℕ) : ZMod (p ^ (c + 1))) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ (gp p c), ih, gp]
    have := pc_sq (p := p) hc
    push_cast at this ⊢
    linear_combination (t : ZMod (p ^ (c + 1))) * this

omit hp in
/-- g^p = 1。 -/
theorem gp_pow_p (hc : 1 ≤ c) : gp p c ^ p = 1 := by
  rw [gp_pow hc, ← Nat.cast_mul, ← pow_succ', ZMod.natCast_self, add_zero]

theorem isUnit_gp (hc : 1 ≤ c) : IsUnit (gp p c) := by
  have hp1 : p = (p - 1) + 1 := by have := hp.out.one_lt; omega
  refine isUnit_iff_exists_inv.mpr ⟨gp p c ^ (p - 1), ?_⟩
  rw [← pow_succ', ← hp1, gp_pow_p hc]

/-- 核 {u ≡ 1 mod p^c} の元は g の冪。 -/
theorem ker_gen (hc : 1 ≤ c) (u : (ZMod (p ^ (c + 1)))ˣ)
    (hu : u ∈ (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ c))).ker) :
    ∃ t : ℕ, (u : ZMod (p ^ (c + 1))) = gp p c ^ t := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one, ZMod.cast_eq_val] at hu
  have hpc : 1 < p ^ c := Nat.one_lt_pow (by omega) hp.out.one_lt
  have h1 : (u : ZMod (p ^ (c + 1))).val % p ^ c = 1 := by
    have := congrArg ZMod.val hu
    rwa [ZMod.val_natCast, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hpc] at this
  have hd := Nat.div_add_mod (u : ZMod (p ^ (c + 1))).val (p ^ c)
  refine ⟨(u : ZMod (p ^ (c + 1))).val / p ^ c, ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val (u : ZMod (p ^ (c + 1)))]
  generalize (u : ZMod (p ^ (c + 1))).val = m at h1 hd ⊢
  rw [gp_pow hc]
  conv_lhs => rw [← hd, h1]
  push_cast; ring

/-- g は法 p^c への核に入る（単数として）。 -/
theorem gp_mem_ker (hc : 1 ≤ c) :
    (isUnit_gp (p := p) hc).unit ∈ (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ c))).ker := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, IsUnit.unit_spec, Units.val_one, gp,
    show (1 : ZMod (p ^ (c + 1))) + ((p ^ c : ℕ) : ZMod (p ^ (c + 1))) = ((1 + p ^ c : ℕ) : ZMod _) by push_cast; ring,
    ZMod.cast_natCast (pow_dvd_pow p (Nat.le_succ c))]
  push_cast
  have h0 : ((p : ZMod (p ^ c))) ^ c = 0 := by exact_mod_cast ZMod.natCast_self (p ^ c)
  rw [h0, add_zero]

/-- **経由の判定**: ψ が法 p^c を経由 ⇔ ψ(g) = 1。 -/
theorem factors_iff_gp (hc : 1 ≤ c) (ψ : DirichletCharacter ℂ (p ^ (c + 1))) :
    ψ.FactorsThrough (p ^ c) ↔ ψ (gp p c) = 1 := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (pow_dvd_pow p (Nat.le_succ c))]
  constructor
  · intro h
    have := congrArg Units.val (h (gp_mem_ker hc))
    rwa [MulChar.coe_toUnitHom, IsUnit.unit_spec, Units.val_one] at this
  · intro hg u hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    obtain ⟨t, ht⟩ := ker_gen hc u hu
    rw [ht, map_pow, hg, one_pow]

/-- 非原始 ⇔ 法 p^c を経由。 -/
theorem not_prim_iff_factors (_hc : 1 ≤ c) (ψ : DirichletCharacter ℂ (p ^ (c + 1))) :
    ¬ ψ.IsPrimitive ↔ ψ.FactorsThrough (p ^ c) := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  constructor
  · intro hnp
    obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow hp.out).mp ψ.conductor_dvd_level
    have hi' : i ≤ c := by
      by_contra h
      exact hnp (by rw [DirichletCharacter.isPrimitive_def, he, show i = c + 1 by omega])
    exact (DirichletCharacter.mem_conductorSet_iff _).mp
      ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ (pow_dvd_pow p (Nat.le_succ c))).mpr
        (by rw [he]; exact pow_dvd_pow p hi'))
  · intro hf hpr
    have hle : ψ.conductor ≤ p ^ c := Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff ψ).mpr hf)
    rw [DirichletCharacter.isPrimitive_def] at hpr
    rw [hpr] at hle
    have : p ^ c < p ^ (c + 1) := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
    omega

/-- **原始性の判定**（一般の素数）: χ が原始的 ⇔ χ(1 + p^c) ≠ 1。 -/
theorem prim_iff_gp (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ (c + 1))) :
    χ.IsPrimitive ↔ χ (gp p c) ≠ 1 := by
  rw [ne_eq, ← factors_iff_gp hc, ← not_prim_iff_factors hc, not_not]

/-- **積の原始性**: χ₁χ₂ が原始的 ⇔ χ₁(g)χ₂(g) ≠ 1。 -/
theorem mul_prim_iff (hc : 1 ≤ c) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (c + 1))) :
    (χ₁ * χ₂).IsPrimitive ↔ χ₁ (gp p c) * χ₂ (gp p c) ≠ 1 := by
  rw [prim_iff_gp hc, MulChar.coeToFun_mul, Pi.mul_apply]

omit hp in
/-- χ(g) は 1 の p 乗根。 -/
theorem chi_gp_pow (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ (c + 1))) : χ (gp p c) ^ p = 1 := by
  rw [← map_pow, gp_pow_p hc, map_one]

/-- 積が原始的でない ⇔ χ₂(g) = χ₁(g)⁻¹（χ₁ 原始的）。 -/
theorem mul_not_prim_iff (hc : 1 ≤ c) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (c + 1))) :
    ¬ (χ₁ * χ₂).IsPrimitive ↔ χ₂ (gp p c) = (χ₁ (gp p c))⁻¹ := by
  have hne : χ₁ (gp p c) ≠ 0 := by
    intro h; have := chi_gp_pow hc χ₁; rw [h, zero_pow hp.out.ne_zero] at this; exact zero_ne_one this
  rw [mul_prim_iff hc, not_not]
  constructor
  · intro h; field_simp; linear_combination h
  · intro h; rw [h, mul_inv_cancel₀ hne]

/-- **法 p（素数）では 原始的 ⇔ 非自明**。 -/
theorem prim_level_p_iff (χ : DirichletCharacter ℂ p) : χ.IsPrimitive ↔ χ ≠ 1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  constructor
  · intro h h1
    rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at h
    exact hp.out.one_lt.ne h
  · intro h
    rw [DirichletCharacter.isPrimitive_def]
    rcases (Nat.dvd_prime hp.out).mp χ.conductor_dvd_level with h1 | h1
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1) h
    · exact h1

end Prim

end PAG.Part32

#print axioms PAG.Part32.negProj
#print axioms PAG.Part32.negProj_negProj
#print axioms PAG.Part32.negProj_south
#print axioms PAG.Part32.negProj_north
#print axioms PAG.Part32.tildePull
#print axioms PAG.Part32.tildePull_tildePull
#print axioms PAG.Part32.projFun_tilde
#print axioms PAG.Part32.tildePull_Wpull
#print axioms PAG.Part32.BSproj_tilde
#print axioms PAG.Part32.BNproj_tilde
#print axioms PAG.Part32.tildePull_ketS
#print axioms PAG.Part32.tildePull_ketN
#print axioms PAG.Part32.Wpull_tildePull_ketS
#print axioms PAG.Part32.tildePull_epsS
#print axioms PAG.Part32.tildePull_epsN
#print axioms PAG.Part32.gp
#print axioms PAG.Part32.pc_sq
#print axioms PAG.Part32.gp_pow
#print axioms PAG.Part32.gp_pow_p
#print axioms PAG.Part32.isUnit_gp
#print axioms PAG.Part32.ker_gen
#print axioms PAG.Part32.gp_mem_ker
#print axioms PAG.Part32.factors_iff_gp
#print axioms PAG.Part32.not_prim_iff_factors
#print axioms PAG.Part32.prim_iff_gp
#print axioms PAG.Part32.mul_prim_iff
#print axioms PAG.Part32.chi_gp_pow
#print axioms PAG.Part32.mul_not_prim_iff
#print axioms PAG.Part32.prim_level_p_iff
