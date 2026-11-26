
import PAG258
import PAG262
import PAG27
import PAG28

namespace PAG.Part267

open ZMod PAG.Part27 PAG.Part258

section red

variable {N M L : ℕ}

def redU (h : N ∣ M) (v : Unimod M) : Unimod N :=
  ⟨(castHom h (ZMod N) v.1.1, castHom h (ZMod N) v.1.2), by
    obtain ⟨s, t, hst⟩ := v.2
    exact ⟨castHom h (ZMod N) s, castHom h (ZMod N) t, by
      rw [← map_mul, ← map_mul, ← map_add, hst, map_one]⟩⟩

def red (h : N ∣ M) : ProjLine M → ProjLine N :=
  Quotient.lift (fun v => mk (redU h v)) (fun _v _w ⟨u, h1, h2⟩ =>
    mk_eq_mk (unitsMap h u)
      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h1, map_mul]; rfl)
      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h2, map_mul]; rfl))

theorem red_mk (h : N ∣ M) (v : Unimod M) : red h (mk v) = mk (redU h v) := rfl

theorem red_self (q : ProjLine N) : red (dvd_refl N) q = q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show mk (redU (dvd_refl N) v) = mk v
    congr 1
    apply Subtype.ext
    show (castHom (dvd_refl N) (ZMod N) v.1.1, castHom (dvd_refl N) (ZMod N) v.1.2) = v.1
    simp only [castHom_apply, ZMod.cast_id', id]

theorem red_comp (h₁ : N ∣ M) (h₂ : M ∣ L) (q : ProjLine L) :
    red h₁ (red h₂ q) = red (dvd_trans h₁ h₂) q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show mk (redU h₁ (redU h₂ v)) = mk (redU (dvd_trans h₁ h₂) v)
    congr 1
    apply Subtype.ext
    show (castHom h₁ (ZMod N) (castHom h₂ (ZMod M) v.1.1),
        castHom h₁ (ZMod N) (castHom h₂ (ZMod M) v.1.2)) =
      (castHom (dvd_trans h₁ h₂) (ZMod N) v.1.1, castHom (dvd_trans h₁ h₂) (ZMod N) v.1.2)
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, castHom_comp]

theorem red_Wproj (h : N ∣ M) (q : ProjLine M) : red h (Wproj q) = Wproj (red h q) := by
  induction q using Quotient.inductionOn with
  | h v => rfl

def zeroU (N : ℕ) : Unimod N := ⟨(0, 1), ⟨0, 1, by simp⟩⟩

def infU (N : ℕ) : Unimod N := ⟨(1, 0), ⟨1, 0, by simp⟩⟩

def zeroPt (N : ℕ) : ProjLine N := mk (zeroU N)

def infPt (N : ℕ) : ProjLine N := mk (infU N)

theorem Wproj_zeroPt : Wproj (zeroPt N) = infPt N := rfl

theorem Wproj_infPt : Wproj (infPt N) = zeroPt N := rfl

theorem red_zeroPt (h : N ∣ M) : red h (zeroPt M) = zeroPt N := by
  show mk (redU h (zeroU M)) = mk (zeroU N)
  congr 1
  apply Subtype.ext
  show (castHom h (ZMod N) 0, castHom h (ZMod N) 1) = ((0 : ZMod N), (1 : ZMod N))
  rw [map_zero, map_one]

theorem red_infPt (h : N ∣ M) : red h (infPt M) = infPt N := by
  show mk (redU h (infU M)) = mk (infU N)
  congr 1
  apply Subtype.ext
  show (castHom h (ZMod N) 1, castHom h (ZMod N) 0) = ((1 : ZMod N), (0 : ZMod N))
  rw [map_zero, map_one]

theorem zeroPt_ne_infPt (hN : N ≠ 1) : zeroPt N ≠ infPt N := by
  intro h
  have h' : mk (zeroU N) = mk (infU N) := h
  obtain ⟨u, h1, _⟩ := Quotient.exact h'
  change (1 : ZMod N) = u * 0 at h1
  rw [mul_zero] at h1
  have h2 : ((1 : ℕ) : ZMod N) = 0 := by exact_mod_cast h1
  exact hN (Nat.dvd_one.mp ((ZMod.natCast_eq_zero_iff 1 N).mp h2))

theorem exists_redU [NeZero M] (h : N ∣ M) (v : Unimod N) :
    ∃ w : Unimod M, mk (redU h w) = mk v := by
  have : NeZero N := ⟨by rintro rfl; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd h)⟩
  obtain ⟨d, hdN, u, hu, hau⟩ := ZMod.eq_unit_mul_divisor v.1.1
  obtain ⟨s, t, hst⟩ := v.2
  obtain ⟨m, hm⟩ := hdN
  set U := hu.unit with hUdef
  have hau' : v.1.1 = (U : ZMod N) * (d : ZMod N) := by rw [hau, hUdef, IsUnit.unit_spec]
  have hUU : (U : ZMod N) * ((U⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := Units.mul_inv U
  obtain ⟨b₂, hb₂⟩ := castHom_surjective h (((U⁻¹ : (ZMod N)ˣ) : ZMod N) * v.1.2)
  obtain ⟨s₂, hs₂⟩ := castHom_surjective h (s * U)
  obtain ⟨t₂, ht₂⟩ := castHom_surjective h (t * U)
  have he : castHom h (ZMod N) (s₂ * (d : ZMod M) + t₂ * b₂ - 1) = 0 := by
    rw [map_sub, map_add, map_mul, map_mul, hs₂, ht₂, hb₂, map_natCast, map_one]
    linear_combination hst - s * hau' + t * v.1.2 * hUU
  obtain ⟨k, hk⟩ := (PAG.Part262.mem_ker_iff h _).mp he
  have hNdm : (N : ZMod M) = (d : ZMod M) * (m : ZMod M) := by rw [← Nat.cast_mul, ← hm]
  refine ⟨⟨((d : ZMod M), b₂), ⟨s₂ - (m : ZMod M) * k, t₂, ?_⟩⟩, ?_⟩
  · show (s₂ - (m : ZMod M) * k) * (d : ZMod M) + t₂ * b₂ = 1
    linear_combination hk + k * hNdm
  · refine mk_eq_mk U ?_ ?_
    · change v.1.1 = U * castHom h (ZMod N) (d : ZMod M)
      rw [map_natCast]
      exact hau'
    · change v.1.2 = U * castHom h (ZMod N) b₂
      rw [hb₂, ← mul_assoc, hUU, one_mul]

theorem red_surjective [NeZero M] (h : N ∣ M) : Function.Surjective (red h) := by
  intro q
  induction q using Quotient.inductionOn with
  | h v =>
    obtain ⟨w, hw⟩ := exists_redU h v
    exact ⟨mk w, hw⟩

def eqU (x : (ZMod N)ˣ) : Unimod N := ⟨((x : ZMod N), 1), ⟨0, 1, by simp⟩⟩

def eqPt (x : (ZMod N)ˣ) : ProjLine N := mk (eqU x)

theorem eqPt_injective : Function.Injective (eqPt (N := N)) := by
  intro x y hxy
  have h' : mk (eqU x) = mk (eqU y) := hxy
  obtain ⟨u, h1, h2⟩ := Quotient.exact h'
  change (y : ZMod N) = u * x at h1
  change (1 : ZMod N) = u * 1 at h2
  rw [mul_one] at h2
  apply Units.ext
  rw [h1, ← h2, one_mul]

theorem red_eqPt (h : N ∣ M) (x : (ZMod M)ˣ) : red h (eqPt x) = eqPt (unitsMap h x) := by
  show mk (redU h (eqU x)) = mk (eqU (unitsMap h x))
  congr 1
  apply Subtype.ext
  show (castHom h (ZMod N) (x : ZMod M), castHom h (ZMod N) 1) =
    (((unitsMap h x : (ZMod N)ˣ) : ZMod N), (1 : ZMod N))
  rw [map_one]
  rfl

theorem isUnit_of_castHom [NeZero M] (h : N ∣ M) (hp : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N)
    (c : ZMod M) (hc : IsUnit (castHom h (ZMod N) c)) : IsUnit c := by
  rw [castHom_apply, ZMod.cast_eq_val, ZMod.isUnit_iff_coprime] at hc
  rw [← ZMod.natCast_zmod_val c, ZMod.isUnit_iff_coprime]
  refine Nat.coprime_of_dvd (fun k hk hkc hkM => ?_)
  exact hk.not_dvd_one (Nat.Coprime.gcd_eq_one hc ▸ Nat.dvd_gcd hkc (hp k hk hkM))

theorem exists_eqPt_of_red [NeZero M] (h : N ∣ M) (hp : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N)
    (q : ProjLine M) (x : (ZMod N)ˣ) (hx : eqPt x = red h q) : ∃ y, eqPt y = q := by
  induction q using Quotient.inductionOn with
  | h v =>
    have hx' : mk (eqU x) = mk (redU h v) := hx
    obtain ⟨u, h1, h2⟩ := Quotient.exact hx'
    change castHom h (ZMod N) v.1.1 = u * x at h1
    change castHom h (ZMod N) v.1.2 = u * 1 at h2
    have hc : IsUnit v.1.1 :=
      isUnit_of_castHom h hp _ (by rw [h1]; exact u.isUnit.mul x.isUnit)
    have he : IsUnit v.1.2 :=
      isUnit_of_castHom h hp _ (by rw [h2, mul_one]; exact u.isUnit)
    refine ⟨he.unit⁻¹ * hc.unit, ?_⟩
    symm
    refine mk_eq_mk he.unit⁻¹ ?_ ?_
    · change ((he.unit⁻¹ * hc.unit : (ZMod M)ˣ) : ZMod M) = _ * v.1.1
      rw [Units.val_mul, IsUnit.unit_spec]
    · change (1 : ZMod M) = _ * v.1.2
      rw [IsUnit.val_inv_mul]

end red

abbrev Fsp (a : Lvl) : Type := ProjLine a.val → ℂ

noncomputable def pullP (a b : Lvl) (h : a ≤ b) : Fsp a →ₗ[ℂ] Fsp b where
  toFun f q := f (red (N := a.val) (M := b.val) h q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : DirectedSystem Fsp (fun a b h => (pullP a b h : Fsp a → Fsp b)) where
  map_self a f := by
    funext q
    show f (red (dvd_refl a.val) q) = f q
    rw [red_self]
  map_map c b a hab hbc f := by
    funext q
    show f (red hab (red hbc q)) = f (red (dvd_trans hab hbc) q)
    rw [red_comp]

abbrev LimP : Type := Module.DirectLimit Fsp pullP

noncomputable abbrev ofP (a : Lvl) : Fsp a →ₗ[ℂ] LimP := Module.DirectLimit.of ℂ Lvl Fsp pullP a

theorem pullP_injective (a b : Lvl) (h : a ≤ b) : Function.Injective (pullP a b h) := by
  intro f g hfg
  funext q
  obtain ⟨q', rfl⟩ := red_surjective (N := a.val) (M := b.val) h q
  exact congrFun hfg q'

theorem ofP_injective (a : Lvl) : Function.Injective (ofP a) := by
  intro f g h
  obtain ⟨b, hab, hb⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  exact pullP_injective a b hab hb

noncomputable def Wfun (a : Lvl) : Fsp a →ₗ[ℂ] Fsp a where
  toFun := PAG.Part28.Wpull
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Wfun_comp_pullP (a b : Lvl) (h : a ≤ b) :
    Wfun b ∘ₗ pullP a b h = pullP a b h ∘ₗ Wfun a := by
  refine LinearMap.ext (fun f => funext (fun q => ?_))
  show f (red (N := a.val) (M := b.val) h (Wproj q)) = f (Wproj (red (N := a.val) (M := b.val) h q))
  rw [red_Wproj]

noncomputable def WL : LimP →ₗ[ℂ] LimP :=
  Module.DirectLimit.map Wfun (fun a b h => Wfun_comp_pullP a b h)

theorem WL_ofP (a : Lvl) (f : Fsp a) : WL (ofP a f) = ofP a (Wfun a f) :=
  Module.DirectLimit.map_apply_of _ _ _

theorem WL_WL (x : LimP) : WL (WL x) = x := by
  refine Module.DirectLimit.induction_on x (fun a f => ?_)
  rw [WL_ofP, WL_ofP]
  exact congrArg (ofP a) (PAG.Part28.Wpull_Wpull f)

noncomputable def resE (a : Lvl) : Fsp a →ₗ[ℂ] Gsp a where
  toFun f x := f (eqPt x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resE_comp_pullP (a b : Lvl) (h : a ≤ b) :
    resE b ∘ₗ pullP a b h = pullSys a b h ∘ₗ resE a := by
  refine LinearMap.ext (fun f => funext (fun x => ?_))
  show f (red (N := a.val) (M := b.val) h (eqPt x)) = f (eqPt (unitsMap (n := a.val) (m := b.val) h x))
  rw [red_eqPt]

noncomputable def resL : LimP →ₗ[ℂ] Lim :=
  Module.DirectLimit.map resE (fun a b h => resE_comp_pullP a b h)

theorem resL_ofP (a : Lvl) (f : Fsp a) : resL (ofP a f) = ofL a (resE a f) :=
  Module.DirectLimit.map_apply_of _ _ _

noncomputable def invG (a : Lvl) : Gsp a →ₗ[ℂ] Gsp a where
  toFun g x := g x⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem invG_comp_pullSys (a b : Lvl) (h : a ≤ b) :
    invG b ∘ₗ pullSys a b h = pullSys a b h ∘ₗ invG a := by
  refine LinearMap.ext (fun g => funext (fun x => ?_))
  show g (unitsMap (n := a.val) (m := b.val) h x⁻¹) = g (unitsMap (n := a.val) (m := b.val) h x)⁻¹
  rw [map_inv]

noncomputable def invL : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map invG (fun a b h => invG_comp_pullSys a b h)

theorem invL_ofL (a : Lvl) (g : Gsp a) : invL (ofL a g) = ofL a (invG a g) :=
  Module.DirectLimit.map_apply_of _ _ _

theorem Wproj_eqPt {N : ℕ} (x : (ZMod N)ˣ) : Wproj (eqPt x) = eqPt x⁻¹ := by
  show mk ⟨(((1 : ZMod N)), (x : ZMod N)), _⟩ = mk (eqU x⁻¹)
  refine mk_eq_mk x⁻¹ ?_ ?_
  · change ((x⁻¹ : (ZMod N)ˣ) : ZMod N) = ((x⁻¹ : (ZMod N)ˣ) : ZMod N) * 1
    rw [mul_one]
  · change (1 : ZMod N) = ((x⁻¹ : (ZMod N)ˣ) : ZMod N) * x
    rw [Units.inv_mul]

theorem resL_WL (z : LimP) : resL (WL z) = invL (resL z) := by
  refine Module.DirectLimit.induction_on z (fun a f => ?_)
  rw [WL_ofP, resL_ofP, resL_ofP, invL_ofL]
  congr 1
  funext x
  show f (Wproj (eqPt x)) = f (eqPt x⁻¹)
  rw [Wproj_eqPt]

open Classical in

noncomputable def extE (a : Lvl) : Gsp a →ₗ[ℂ] Fsp a where
  toFun g q := if h : ∃ x, eqPt x = q then g h.choose else 0
  map_add' g g' := by
    funext q
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c g := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem extE_eqPt (a : Lvl) (g : Gsp a) (x : (ZMod a.val)ˣ) : extE a g (eqPt x) = g x := by
  classical
  show (if h : ∃ y, eqPt y = eqPt x then g h.choose else 0) = g x
  split_ifs with h'
  · rw [eqPt_injective h'.choose_spec]
  · exact absurd ⟨x, rfl⟩ h'

theorem extE_off (a : Lvl) (g : Gsp a) (q : ProjLine a.val) (hq : ∀ x, eqPt x ≠ q) :
    extE a g q = 0 := by
  classical
  show (if h : ∃ y, eqPt y = q then g h.choose else 0) = 0
  split_ifs with h'
  · exact absurd h'.choose_spec (hq _)
  · rfl

theorem resE_extE (a : Lvl) (g : Gsp a) : resE a (extE a g) = g :=
  funext (fun x => extE_eqPt a g x)

theorem resL_surjective : Function.Surjective resL := by
  intro z
  refine Module.DirectLimit.induction_on z (fun a g => ?_)
  exact ⟨ofP a (extE a g), by rw [resL_ofP, resE_extE]⟩

theorem extE_compat_iff (a b : Lvl) (h : a ≤ b) :
    (∀ g : Gsp a, extE b (pullSys a b h g) = pullP a b h (extE a g)) ↔
      ∀ p : ℕ, p.Prime → p ∣ b.val → p ∣ a.val := by
  constructor
  · intro H p hp hpb
    by_contra hpa
    have hunit : IsUnit ((p : ZMod a.val)) :=
      (ZMod.isUnit_iff_coprime p a.val).mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa)
    let v : Unimod b.val := ⟨((p : ZMod b.val), 1), ⟨0, 1, by simp⟩⟩
    have hred : red (N := a.val) (M := b.val) h (mk v) = eqPt hunit.unit := by
      show mk (redU h v) = mk (eqU hunit.unit)
      congr 1
      apply Subtype.ext
      show (castHom h (ZMod a.val) (p : ZMod b.val), castHom h (ZMod a.val) 1) =
        (((hunit.unit : (ZMod a.val)ˣ) : ZMod a.val), (1 : ZMod a.val))
      rw [map_natCast, map_one, IsUnit.unit_spec]
    have hoff : ∀ y : (ZMod b.val)ˣ, eqPt y ≠ mk v := by
      intro y hy
      have hy' : mk (eqU y) = mk v := hy
      obtain ⟨u, h1, _⟩ := Quotient.exact hy'
      change (p : ZMod b.val) = u * y at h1
      have hpu : IsUnit ((p : ZMod b.val)) := by rw [h1]; exact u.isUnit.mul y.isUnit
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp
        ((ZMod.isUnit_iff_coprime p b.val).mp hpu) hpb
    have key := congrFun (H 1) (mk v)
    rw [extE_off b _ (mk v) hoff] at key
    change (0 : ℂ) = extE a 1 (red (N := a.val) (M := b.val) h (mk v)) at key
    rw [hred, extE_eqPt] at key
    exact zero_ne_one key
  · intro hp g
    funext q
    by_cases hq : ∃ y, eqPt y = q
    · obtain ⟨y, rfl⟩ := hq
      rw [extE_eqPt]
      show pullSys a b h g y = extE a g (red (N := a.val) (M := b.val) h (eqPt y))
      rw [red_eqPt, extE_eqPt]
      rfl
    · rw [extE_off b _ q (fun y hy => hq ⟨y, hy⟩)]
      show 0 = extE a g (red (N := a.val) (M := b.val) h q)
      rw [extE_off]
      intro x hx
      exact hq (exists_eqPt_of_red h hp q x hx)

def lv1 : Lvl := ⟨1, Nat.one_pos⟩

def lv2 : Lvl := ⟨2, Nat.two_pos⟩

theorem lv1_le_lv2 : lv1 ≤ lv2 := one_dvd 2

theorem extE_not_compat :
    ∃ g : Gsp lv1, extE lv2 (pullSys lv1 lv2 lv1_le_lv2 g) ≠ pullP lv1 lv2 lv1_le_lv2 (extE lv1 g) := by
  by_contra H
  have H' : ∀ g : Gsp lv1,
      extE lv2 (pullSys lv1 lv2 lv1_le_lv2 g) = pullP lv1 lv2 lv1_le_lv2 (extE lv1 g) :=
    fun g => by_contra (fun hne => H ⟨g, hne⟩)
  have h2 := (extE_compat_iff lv1 lv2 lv1_le_lv2).mp H' 2 Nat.prime_two (dvd_refl 2)
  exact absurd (Nat.le_of_dvd Nat.one_pos h2) (by norm_num)

theorem not_exists_extL :
    ¬ ∃ E : Lim →ₗ[ℂ] LimP, ∀ (a : Lvl) (g : Gsp a), E (ofL a g) = ofP a (extE a g) := by
  rintro ⟨E, hE⟩
  obtain ⟨g, hg⟩ := extE_not_compat
  apply hg
  apply ofP_injective lv2
  have e1 : ofL lv2 (pullSys lv1 lv2 lv1_le_lv2 g) = ofL lv1 g := Module.DirectLimit.of_f
  have e2 : ofP lv2 (pullP lv1 lv2 lv1_le_lv2 (extE lv1 g)) = ofP lv1 (extE lv1 g) :=
    Module.DirectLimit.of_f
  rw [← hE, e1, hE, e2]

end PAG.Part267

#print axioms PAG.Part267.red_comp
#print axioms PAG.Part267.red_surjective
#print axioms PAG.Part267.zeroPt_ne_infPt
#print axioms PAG.Part267.WL_WL
#print axioms PAG.Part267.ofP_injective
#print axioms PAG.Part267.resL_ofP
#print axioms PAG.Part267.resL_surjective
#print axioms PAG.Part267.resL_WL
#print axioms PAG.Part267.extE_compat_iff
#print axioms PAG.Part267.extE_not_compat
#print axioms PAG.Part267.not_exists_extL
