/-
  PAG 2.0 Part 23（2026-10-18）— 射影直線 P¹(Z/p^K) の本来の定義と点モデルの同型
  P¹(Z/N) := {(a, b) 単模（∃ s t, sa + tb = 1）} / 単数倍。
  1. N = p^K（K ≥ 1）では 単模 ⇔ a または b が単数
  2. Pt(p^K) ≃ P¹(Z/p^K)（x ↦ [x:1]、y ↦ [1:y]）
  3. 反転 [a:b] ↦ [b:a] は well-defined で、同型のもとで Wpt に対応
  4. |P¹(Z/p^K)| = p^K + p^(K−1)
-/
import PAG26

namespace PAG.Part27

open ZMod PAG.Part23 PAG.Part26

open Classical

variable {N : ℕ}

/-- 単模ベクトル。 -/
def Unimod (N : ℕ) := {v : ZMod N × ZMod N // ∃ s t : ZMod N, s * v.1 + t * v.2 = 1}

/-- 単数倍の同値関係。 -/
def projSetoid (N : ℕ) : Setoid (Unimod N) where
  r v w := ∃ u : (ZMod N)ˣ, w.1.1 = u * v.1.1 ∧ w.1.2 = u * v.1.2
  iseqv := {
    refl := fun v => ⟨1, by simp, by simp⟩
    symm := fun {v w} ⟨u, h1, h2⟩ => ⟨u⁻¹, by rw [h1, ← mul_assoc, Units.inv_mul, one_mul],
      by rw [h2, ← mul_assoc, Units.inv_mul, one_mul]⟩
    trans := fun {v w z} ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩ => ⟨u' * u, by rw [h1', h1, Units.val_mul, mul_assoc],
      by rw [h2', h2, Units.val_mul, mul_assoc]⟩ }

/-- **射影直線** P¹(Z/N)。 -/
def ProjLine (N : ℕ) := Quotient (projSetoid N)

/-- 点 [a:b]。 -/
def mk (v : Unimod N) : ProjLine N := Quotient.mk (projSetoid N) v

theorem mk_eq_mk {v w : Unimod N} (u : (ZMod N)ˣ) (h1 : w.1.1 = u * v.1.1) (h2 : w.1.2 = u * v.1.2) :
    mk v = mk w := Quotient.sound ⟨u, h1, h2⟩

variable {p : ℕ} [hp : Fact p.Prime]

/-- **単模 ⇔ どちらかが単数**（N = p^K, K ≥ 1）。 -/
theorem unimod_iff {K : ℕ} (hK : 1 ≤ K) (a b : ZMod (p ^ K)) :
    (∃ s t : ZMod (p ^ K), s * a + t * b = 1) ↔ IsUnit a ∨ IsUnit b := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  constructor
  · rintro ⟨s, t, h⟩
    by_contra hn
    simp only [not_or] at hn
    rw [PAG.Part25.isUnit_iff_not_dvd hK, not_not] at hn
    rw [PAG.Part25.isUnit_iff_not_dvd hK, not_not] at hn
    have hd : p ∣ p ^ K := dvd_pow_self p (by omega)
    have e := congrArg (ZMod.castHom hd (ZMod p)) h
    rw [map_add, map_mul, map_mul, map_one, PAG.Part21.castHom_eq_natCast hd a,
      PAG.Part21.castHom_eq_natCast hd b, (ZMod.natCast_eq_zero_iff _ _).mpr hn.1,
      (ZMod.natCast_eq_zero_iff _ _).mpr hn.2, mul_zero, mul_zero, add_zero] at e
    exact zero_ne_one e
  · rintro (h | h)
    · exact ⟨a⁻¹, 0, by rw [ZMod.inv_mul_of_unit a h, zero_mul, add_zero]⟩
    · exact ⟨0, b⁻¹, by rw [ZMod.inv_mul_of_unit b h, zero_mul, zero_add]⟩

omit hp in
theorem isUnit_units_mul_iff (u : (ZMod N)ˣ) (x : ZMod N) : IsUnit ((u : ZMod N) * x) ↔ IsUnit x :=
  Units.isUnit_units_mul u x

omit hp in
/-- 単数 b について (u a)(u b)⁻¹ = a b⁻¹。 -/
theorem scale_div {u : (ZMod N)ˣ} {b : ZMod N} (hb : IsUnit b) (a : ZMod N) :
    (u * a) * ((u : ZMod N) * b)⁻¹ = a * b⁻¹ := by
  obtain ⟨ub, rfl⟩ := hb
  rw [← Units.val_mul, ZMod.inv_coe_unit, ZMod.inv_coe_unit, mul_inv, Units.val_mul,
    show (u : ZMod N) * a * (↑u⁻¹ * ↑ub⁻¹) = a * ↑ub⁻¹ * (↑u * ↑u⁻¹) by ring, Units.mul_inv, mul_one]

omit hp in
theorem nonunit_div {a b : ZMod N} (ha : IsUnit a) (hb : ¬ IsUnit b) : ¬ IsUnit (b * a⁻¹) := by
  intro h
  apply hb
  have : b = (b * a⁻¹) * a := by rw [mul_assoc, ZMod.inv_mul_of_unit a ha, mul_one]
  rw [this]
  exact h.mul ha

section Iso

variable (K : ℕ) (hK : 1 ≤ K)

/-- 点モデル → 射影直線: [x:1]、[1:y]。 -/
def toProj : Pt (p ^ K) → ProjLine (p ^ K)
  | Sum.inl x => mk ⟨(x, 1), 0, 1, by simp⟩
  | Sum.inr y => mk ⟨(1, y.1), 1, 0, by simp⟩

include hK in
theorem a_unit_of {v : Unimod (p ^ K)} (hb : ¬ IsUnit v.1.2) : IsUnit v.1.1 :=
  ((unimod_iff hK v.1.1 v.1.2).mp v.2).resolve_right hb

/-- 代表元での逆写像。 -/
noncomputable def ofRep (v : Unimod (p ^ K)) : Pt (p ^ K) :=
  if h : IsUnit v.1.2 then Sum.inl (v.1.1 * v.1.2⁻¹)
  else Sum.inr ⟨v.1.2 * v.1.1⁻¹, nonunit_div (a_unit_of K hK h) h⟩

include hK in
theorem ofRep_resp (v w : Unimod (p ^ K)) (hvw : (projSetoid (p ^ K)) v w) :
    ofRep K hK v = ofRep K hK w := by
  obtain ⟨u, h1, h2⟩ := hvw
  unfold ofRep
  by_cases hb : IsUnit v.1.2
  · have hb' : IsUnit w.1.2 := by rw [h2]; exact (isUnit_units_mul_iff u _).mpr hb
    simp only [hb, hb', ↓reduceDIte]
    rw [h1, h2, scale_div hb]
  · have hb' : ¬ IsUnit w.1.2 := by rw [h2, isUnit_units_mul_iff]; exact hb
    simp only [hb, hb', ↓reduceDIte]
    congr 2
    rw [h1, h2, scale_div (a_unit_of K hK hb)]

/-- 射影直線 → 点モデル。 -/
noncomputable def ofProj : ProjLine (p ^ K) → Pt (p ^ K) :=
  Quotient.lift (ofRep K hK) (ofRep_resp K hK)

theorem ofProj_toProj (z : Pt (p ^ K)) : ofProj K hK (toProj K z) = z := by
  rcases z with x | ⟨y, hy⟩
  · show ofRep K hK _ = _
    simp [ofRep]
  · show ofRep K hK _ = _
    simp [ofRep, hy]

theorem toProj_ofProj (q : ProjLine (p ^ K)) : toProj K (ofProj K hK q) = q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show toProj K (ofRep K hK v) = mk v
    unfold ofRep
    by_cases hb : IsUnit v.1.2
    · simp only [hb, ↓reduceDIte]
      obtain ⟨ub, hub⟩ := hb
      apply mk_eq_mk ub
      · show v.1.1 = ub * (v.1.1 * v.1.2⁻¹)
        rw [← hub, ZMod.inv_coe_unit, mul_left_comm, Units.mul_inv, mul_one]
      · show v.1.2 = ub * 1
        rw [mul_one, hub]
    · simp only [hb, ↓reduceDIte]
      obtain ⟨ua, hua⟩ := a_unit_of K hK hb
      apply mk_eq_mk ua
      · show v.1.1 = ua * 1
        rw [mul_one, hua]
      · show v.1.2 = ua * (v.1.2 * v.1.1⁻¹)
        rw [← hua, ZMod.inv_coe_unit, mul_left_comm, Units.mul_inv, mul_one]

/-- **点モデル ≃ 射影直線** Pt(p^K) ≃ P¹(Z/p^K)。 -/
noncomputable def projEquiv : Pt (p ^ K) ≃ ProjLine (p ^ K) where
  toFun := toProj K
  invFun := ofProj K hK
  left_inv := ofProj_toProj K hK
  right_inv := toProj_ofProj K hK

include hK in
/-- **点の数**: |P¹(Z/p^K)| = p^K + p^(K−1)。 -/
theorem card_ProjLine : Nat.card (ProjLine (p ^ K)) = p ^ K + p ^ (K - 1) := by
  rw [← Nat.card_congr (projEquiv K hK), Nat.card_eq_fintype_card, card_Pt K hK]

end Iso

/-! ## 反転 [a:b] ↦ [b:a] -/

omit hp in
theorem swap_unimod (v : Unimod N) : ∃ s t : ZMod N, s * v.1.2 + t * v.1.1 = 1 := by
  obtain ⟨s, t, h⟩ := v.2
  exact ⟨t, s, by rw [add_comm]; exact h⟩

/-- 反転 W[a:b] = [b:a]（well-defined）。 -/
def Wproj : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk ⟨(v.1.2, v.1.1), swap_unimod v⟩)
    (fun _v _w ⟨u, h1, h2⟩ => mk_eq_mk u h2 h1)

omit hp in
theorem Wproj_Wproj (q : ProjLine N) : Wproj (Wproj q) = q := by
  induction q using Quotient.inductionOn with
  | h v => rfl

/-- **同型のもとで W は Wpt**: toProj(Wpt z) = Wproj(toProj z)。 -/
theorem toProj_Wpt (K : ℕ) (z : Pt (p ^ K)) : toProj K (Wpt z) = Wproj (toProj K z) := by
  rcases z with x | ⟨y, hy⟩
  · by_cases hx : IsUnit x
    · simp only [Wpt, hx, ↓reduceDIte, toProj]
      obtain ⟨ux, rfl⟩ := hx
      apply mk_eq_mk ux
      · show (1 : ZMod (p ^ K)) = ux * (ux : ZMod (p ^ K))⁻¹
        rw [ZMod.inv_coe_unit, Units.mul_inv]
      · show (ux : ZMod (p ^ K)) = ux * 1
        rw [mul_one]
    · simp only [Wpt, hx, ↓reduceDIte, toProj]
      rfl
  · rfl

end PAG.Part27

#print axioms PAG.Part27.projSetoid
#print axioms PAG.Part27.mk_eq_mk
#print axioms PAG.Part27.unimod_iff
#print axioms PAG.Part27.scale_div
#print axioms PAG.Part27.nonunit_div
#print axioms PAG.Part27.ofRep_resp
#print axioms PAG.Part27.ofProj_toProj
#print axioms PAG.Part27.toProj_ofProj
#print axioms PAG.Part27.projEquiv
#print axioms PAG.Part27.card_ProjLine
#print axioms PAG.Part27.Wproj_Wproj
#print axioms PAG.Part27.toProj_Wpt
