
import PAG267
import PAG29

namespace PAG.Part268

open ZMod PAG.Part27 PAG.Part258 PAG.Part267 DirichletCharacter

section chiPt

variable {N : ℕ}

theorem mul_inv_apply_unit (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1 := by
  rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]

noncomputable def chiPt (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
  Quotient.lift (fun v : Unimod N => χ v.1.1 * χ⁻¹ v.1.2) (fun v w ⟨u, h1, h2⟩ => by
    show χ v.1.1 * χ⁻¹ v.1.2 = χ w.1.1 * χ⁻¹ w.1.2
    rw [h1, h2, map_mul, map_mul]
    calc χ v.1.1 * χ⁻¹ v.1.2
        = (χ (u : ZMod N) * χ⁻¹ (u : ZMod N)) * (χ v.1.1 * χ⁻¹ v.1.2) := by
          rw [mul_inv_apply_unit, one_mul]
      _ = χ (u : ZMod N) * χ v.1.1 * (χ⁻¹ (u : ZMod N) * χ⁻¹ v.1.2) := by ring)

theorem chiPt_mk (χ : DirichletCharacter ℂ N) (v : Unimod N) :
    chiPt χ (mk v) = χ v.1.1 * χ⁻¹ v.1.2 := rfl

theorem chiPt_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : chiPt χ (eqPt x) = χ x := by
  show χ (x : ZMod N) * χ⁻¹ 1 = χ x
  rw [map_one, mul_one]

theorem chiPt_Wproj (χ : DirichletCharacter ℂ N) (q : ProjLine N) :
    chiPt χ (Wproj q) = chiPt χ⁻¹ q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show χ v.1.2 * χ⁻¹ v.1.1 = χ⁻¹ v.1.1 * χ⁻¹⁻¹ v.1.2
    rw [inv_inv, mul_comm]

def torusU (u : (ZMod N)ˣ) (v : Unimod N) : Unimod N :=
  ⟨((u : ZMod N) * v.1.1, v.1.2), by
    obtain ⟨s, t, h⟩ := v.2
    refine ⟨s * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), t, ?_⟩
    have hu : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := Units.inv_mul u
    linear_combination h + s * v.1.1 * hu⟩

def torus (u : (ZMod N)ˣ) : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk (torusU u v)) (fun _v _w ⟨c, h1, h2⟩ =>
    mk_eq_mk c (by change (u : ZMod N) * _ = c * ((u : ZMod N) * _); rw [h1]; ring) h2)

theorem torus_eqPt (u x : (ZMod N)ˣ) : torus u (eqPt x) = eqPt (u * x) := rfl

theorem chiPt_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
    chiPt χ (torus u q) = χ u * chiPt χ q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show χ ((u : ZMod N) * v.1.1) * χ⁻¹ v.1.2 = χ u * (χ v.1.1 * χ⁻¹ v.1.2)
    rw [map_mul, mul_assoc]

theorem chiPt_red_congr {d₁ d₂ M : ℕ} (hd : d₁ = d₂) (χ₁ : DirichletCharacter ℂ d₁)
    (χ₂ : DirichletCharacter ℂ d₂) (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) (h₁ : d₁ ∣ M) (h₂ : d₂ ∣ M)
    (q : ProjLine M) : chiPt χ₁ (red h₁ q) = chiPt χ₂ (red h₂ q) := by
  subst hd
  have : χ₁ = χ₂ := by
    refine MulChar.ext (fun u => ?_)
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod d₁)
    rw [← ha]
    exact hχ a
  subst this
  rfl

end chiPt

section ext

variable {N : ℕ} [NeZero N]

noncomputable def extChi (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
  fun q => chiPt χ.primitiveCharacter (red χ.conductor_dvd_level q)

theorem extChi_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : extChi χ (eqPt x) = χ x := by
  show chiPt χ.primitiveCharacter (red χ.conductor_dvd_level (eqPt x)) = χ x
  rw [red_eqPt, chiPt_eqPt]
  have := congrFun (pullL_charU (N := χ.conductor) χ.conductor_dvd_level χ.primitiveCharacter) x
  rw [changeLevel_primitiveCharacter] at this
  exact this

omit [NeZero N] in

theorem extChi_changeLevel {M : ℕ} [NeZero M] (h : N ∣ M) (χ : DirichletCharacter ℂ N)
    (q : ProjLine M) : extChi (changeLevel h χ) q = extChi χ (red h q) := by
  show chiPt (changeLevel h χ).primitiveCharacter (red (changeLevel h χ).conductor_dvd_level q) =
    chiPt χ.primitiveCharacter (red χ.conductor_dvd_level (red h q))
  rw [red_comp]
  exact chiPt_red_congr (conductor_changeLevel χ h) _ _ (primitiveCharacter_changeLevel_apply h χ)
    _ _ q

theorem extChi_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
    extChi χ (torus u q) = χ u * extChi χ q := by
  have hr : red χ.conductor_dvd_level (torus u q) =
      torus (unitsMap χ.conductor_dvd_level u) (red χ.conductor_dvd_level q) := by
    induction q using Quotient.inductionOn with
    | h v =>
      show mk (redU _ (torusU u v)) = mk (torusU _ (redU _ v))
      congr 1
      apply Subtype.ext
      show (castHom _ (ZMod χ.conductor) ((u : ZMod N) * v.1.1), castHom _ (ZMod χ.conductor) v.1.2) =
        (((unitsMap χ.conductor_dvd_level u : (ZMod χ.conductor)ˣ) : ZMod χ.conductor) *
          castHom _ (ZMod χ.conductor) v.1.1, castHom _ (ZMod χ.conductor) v.1.2)
      rw [map_mul]
      rfl
  show chiPt χ.primitiveCharacter (red _ (torus u q)) = χ u * chiPt χ.primitiveCharacter (red _ q)
  rw [hr, chiPt_torus]
  congr 1
  have := congrFun (pullL_charU (N := χ.conductor) χ.conductor_dvd_level χ.primitiveCharacter) u
  rw [changeLevel_primitiveCharacter] at this
  exact this

end ext

theorem pullP_extChi (a b : Lvl) (h : a ≤ b) (χ : DirichletCharacter ℂ a.val) :
    pullP a b h (extChi χ) = extChi (changeLevel (n := a.val) (m := b.val) h χ) :=
  funext (fun q => (extChi_changeLevel (N := a.val) (M := b.val) h χ q).symm)

theorem resE_extChi (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
    resE a (extChi χ) = PAG.Part257.charU χ :=
  funext (fun x => extChi_eqPt χ x)

theorem chiPt_not_compat :
    chiPt (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) (zeroPt 2) ≠
      chiPt (1 : DirichletCharacter ℂ 1) (red (one_dvd 2) (zeroPt 2)) := by
  have h0 : ¬ IsUnit (0 : ZMod 2) := not_isUnit_zero
  show (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) 0 *
      (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1))⁻¹ 1 ≠
    (1 : DirichletCharacter ℂ 1) (castHom (one_dvd 2) (ZMod 1) 0) *
      (1 : DirichletCharacter ℂ 1)⁻¹ (castHom (one_dvd 2) (ZMod 1) 1)
  rw [MulChar.map_nonunit _ h0, zero_mul, map_one, inv_one]
  rw [MulChar.one_apply (isUnit_of_subsingleton _), MulChar.one_apply (isUnit_of_subsingleton _)]
  norm_num

section ket

variable {p : ℕ} [hp : Fact p.Prime]

theorem ketS_proj_zero_eq (K c : ℕ) (hK : 1 ≤ K) (h : 0 + c ≤ K) (hc : 1 ≤ c)
    (χ : DirichletCharacter ℂ (p ^ c)) :
    PAG.Part29.ketS_proj K hK 0 c h χ = fun q =>
      (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
        chiPt χ (red (pow_dvd_pow p (by omega : c ≤ K)) q) := by
  apply (PAG.Part28.projFunEquiv K hK).injective
  apply Subtype.ext
  rw [PAG.Part29.projFun_ketS]
  refine Prod.ext (funext (fun x => ?_)) (funext (fun y => ?_))
  · rw [PAG.Part28.projFun_south]
    show PAG.Part21.ket K 0 c h χ x = (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
      (χ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) x) *
        χ⁻¹ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) 1))
    rw [PAG.Part24.ket0_apply, map_one, map_one, mul_one]
  · rw [PAG.Part28.projFun_north]
    show (PAG.Part23.extS (PAG.Part21.ket K 0 c h χ)).2 y = (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
      (χ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) 1) *
        χ⁻¹ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) y))
    rw [map_one, map_one, one_mul]
    unfold PAG.Part23.extS
    dsimp only
    split_ifs with hy
    · rw [PAG.Part24.ket0_apply, PAG.Part24.chi_cast_inv (by omega) χ hy]
    · have hy' : ¬ IsUnit (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) y) := by
        intro hu
        apply hy
        rw [castHom_apply, ZMod.cast_eq_val, ZMod.isUnit_iff_coprime,
          Nat.coprime_pow_right_iff (by omega)] at hu
        rw [← ZMod.natCast_zmod_val y, ZMod.isUnit_iff_coprime,
          Nat.coprime_pow_right_iff (by omega)]
        exact hu
      rw [MulChar.map_nonunit _ hy', mul_zero]

end ket

end PAG.Part268

#print axioms PAG.Part268.mul_inv_apply_unit
#print axioms PAG.Part268.chiPt_mk
#print axioms PAG.Part268.chiPt_eqPt
#print axioms PAG.Part268.chiPt_Wproj
#print axioms PAG.Part268.torus_eqPt
#print axioms PAG.Part268.chiPt_torus
#print axioms PAG.Part268.chiPt_red_congr
#print axioms PAG.Part268.extChi_eqPt
#print axioms PAG.Part268.extChi_changeLevel
#print axioms PAG.Part268.extChi_torus
#print axioms PAG.Part268.pullP_extChi
#print axioms PAG.Part268.resE_extChi
#print axioms PAG.Part268.chiPt_not_compat
#print axioms PAG.Part268.ketS_proj_zero_eq
