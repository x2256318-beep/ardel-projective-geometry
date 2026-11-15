/-
  Projective Adelic Geometry — formalization Part 3（付録 A.3）
  対象:
    1. 単数 a に対する χ(a⁻¹) = conj χ(a)（付録 A.2 の注記の解消）
    2. 命題 4.6（周回の重みの実数性 ⇔ 反転対称性）の両方向
    3. 命題 2.8 の代数的核心（偶奇分解による H_N = i^{−a} F_N）
    4. 系 2.6a（複素指標では素朴な接着 U = J が許されないこと）
  依存: PAG.lean（Part 1）, PAG2.lean（Part 2）。追加の Mathlib モジュールは使わない。
-/
import PAG
import PAG2

open Complex Finset

namespace PAG.Part3

/-! ## 1. 単数での χ(a⁻¹) = conj χ(a) -/

section Conj

variable {N : ℕ}

/-- 任意の a について conj χ(a) = χ⁻¹(a)（指標の値は 1 の冪根なので）。 -/
theorem conj_apply_eq_inv (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    starRingEnd ℂ (χ a) = χ⁻¹ a :=
  MulChar.star_apply' χ a

/-- 単数 a について χ(a⁻¹) = χ⁻¹(a)（a⁻¹ は ZMod N の逆元）。 -/
theorem apply_inv_eq_inv_apply (χ : DirichletCharacter ℂ N) {a : ZMod N} (ha : IsUnit a) :
    χ a⁻¹ = χ⁻¹ a := by
  obtain ⟨u, rfl⟩ := ha
  rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

/-- **付録 A.2 の注記**: 単数 a について χ(a⁻¹) = conj χ(a)。 -/
theorem apply_inv_eq_conj (χ : DirichletCharacter ℂ N) {a : ZMod N} (ha : IsUnit a) :
    χ a⁻¹ = starRingEnd ℂ (χ a) := by
  rw [apply_inv_eq_inv_apply χ ha, conj_apply_eq_inv]

end Conj

/-! ## 2. 命題 4.6: 周回の重みの実数性と反転対称性の同値性
重み w : {指標} → ℂ（本文では w(χ) = e^{irα_χ}）に対し S_w(a) = Σ_χ χ(a⁻¹) w(χ)。 -/

section Prop46

variable {N : ℕ} [NeZero N]

/-- 周回の重み S_w(a) = Σ_χ χ(a⁻¹) w(χ)。 -/
noncomputable def wsum (w : DirichletCharacter ℂ N → ℂ) (a : ZMod N) : ℂ :=
  ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * w χ

omit [NeZero N] in
/-- 命題 4.6 (⇐): w(χ⁻¹) = conj w(χ) なら、すべての a で S_w(a) は実数（conj S = S）。
χ ↦ χ⁻¹ の並べ替え（`Equiv.inv`）で示す。 -/
theorem wsum_conj_of_symm (w : DirichletCharacter ℂ N → ℂ)
    (hw : ∀ χ, w χ⁻¹ = starRingEnd ℂ (w χ)) (a : ZMod N) :
    starRingEnd ℂ (wsum w a) = wsum w a := by
  unfold wsum
  rw [map_sum]
  simp_rw [map_mul, conj_apply_eq_inv, ← hw]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ fun χ => rfl

omit [NeZero N] in
/-- 命題 4.6 (⇐) の虚部の形。 -/
theorem wsum_im_of_symm (w : DirichletCharacter ℂ N → ℂ)
    (hw : ∀ χ, w χ⁻¹ = starRingEnd ℂ (w χ)) (a : ZMod N) :
    (wsum w a).im = 0 :=
  Complex.conj_eq_iff_im.mp (wsum_conj_of_symm w hw a)

/-- 各点で ψ(a) χ(a⁻¹) = (ψ χ⁻¹)(a)（非単数では両辺 0）。 -/
lemma apply_mul_apply_inv (ψ χ : DirichletCharacter ℂ N) (a : ZMod N) :
    ψ a * χ a⁻¹ = (ψ * χ⁻¹) a := by
  by_cases ha : IsUnit a
  · rw [MulChar.coeToFun_mul, Pi.mul_apply, apply_inv_eq_inv_apply χ ha]
  · rw [MulChar.map_nonunit ψ ha, zero_mul, MulChar.map_nonunit _ ha]

open scoped Classical in
/-- 指標の直交関係（元についての和）: Σ_a ψ(a) χ(a⁻¹) = φ(N)·[χ = ψ]。 -/
lemma sum_apply_mul_apply_inv (ψ χ : DirichletCharacter ℂ N) :
    ∑ a : ZMod N, ψ a * χ a⁻¹ = if χ = ψ then (N.totient : ℂ) else 0 := by
  classical
  simp_rw [apply_mul_apply_inv]
  split_ifs with h
  · subst h
    rw [mul_inv_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · apply MulChar.sum_eq_zero_of_ne_one
    intro h'
    exact h (mul_inv_eq_one.mp h').symm

open scoped Classical in
/-- フーリエ反転: Σ_a ψ(a) S_w(a) = φ(N) w(ψ)。 -/
theorem sum_mul_wsum (w : DirichletCharacter ℂ N → ℂ) (ψ : DirichletCharacter ℂ N) :
    ∑ a : ZMod N, ψ a * wsum w a = N.totient * w ψ := by
  classical
  unfold wsum
  simp_rw [mul_sum]
  rw [sum_comm]
  have : ∀ χ : DirichletCharacter ℂ N,
      ∑ a : ZMod N, ψ a * (χ a⁻¹ * w χ) = (if χ = ψ then (N.totient : ℂ) else 0) * w χ := by
    intro χ
    simp_rw [← mul_assoc]
    rw [← sum_mul, sum_apply_mul_apply_inv]
  simp_rw [this, ite_mul, zero_mul]
  rw [sum_ite_eq' univ ψ, ite_eq_left (mem_univ ψ)]

/-- 命題 4.6 (⇒): すべての単数 a で S_w(a) が実数なら、w(ψ⁻¹) = conj w(ψ)。
（指標の直交関係によるフーリエ反転で示す。） -/
theorem symm_of_wsum_conj (w : DirichletCharacter ℂ N → ℂ)
    (hreal : ∀ a : ZMod N, IsUnit a → starRingEnd ℂ (wsum w a) = wsum w a)
    (ψ : DirichletCharacter ℂ N) :
    w ψ⁻¹ = starRingEnd ℂ (w ψ) := by
  have hφ : (N.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos N)).ne'
  have h1 := sum_mul_wsum w ψ
  have h2 := sum_mul_wsum w ψ⁻¹
  -- conj (Σ ψ(a) S(a)) = Σ ψ⁻¹(a) S(a)
  have h3 : starRingEnd ℂ (∑ a : ZMod N, ψ a * wsum w a)
      = ∑ a : ZMod N, ψ⁻¹ a * wsum w a := by
    rw [map_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [map_mul, conj_apply_eq_inv]
    by_cases ha : IsUnit a
    · rw [hreal a ha]
    · rw [MulChar.map_nonunit _ ha, zero_mul, zero_mul]
  rw [h1, h2, map_mul, Complex.conj_natCast] at h3
  exact (mul_left_cancel₀ hφ h3).symm

/-- **命題 4.6（同値）**: w(χ⁻¹) = conj w(χ)（すべての χ）⇔ S_w(a) がすべての単数 a で実数。 -/
theorem prop46 (w : DirichletCharacter ℂ N → ℂ) :
    (∀ χ, w χ⁻¹ = starRingEnd ℂ (w χ)) ↔ ∀ a : ZMod N, IsUnit a → (wsum w a).im = 0 := by
  constructor
  · intro hw a _
    exact wsum_im_of_symm w hw a
  · intro h ψ
    exact symm_of_wsum_conj w (fun a ha => Complex.conj_eq_iff_im.mpr (h a ha)) ψ

end Prop46

/-! ## 3. 命題 2.8 の代数的核心: 偶奇分解による H_N = i^{−a} F_N
ψ = e(·/N)、cas 核 cas(t) = Re ψ(t) + Im ψ(t)。 -/

section Hartley

variable {N : ℕ} [NeZero N]

/-- cas 核 cas(2π t/N) = Re e(t/N) + Im e(t/N)。 -/
noncomputable def casK (t : ZMod N) : ℂ := PAG.Kloosterman.cas (ZMod.stdAddChar t)

/-- 核の偶部分: cas(t) + cas(−t) = ψ(t) + ψ(−t)（= 2 cos）。 -/
lemma casK_even_part (t : ZMod N) :
    casK t + casK (-t) = ZMod.stdAddChar t + ZMod.stdAddChar (-t) := by
  unfold casK PAG.Kloosterman.cas
  rw [AddChar.map_neg_eq_conj]
  set z := ZMod.stdAddChar t
  apply Complex.ext
  · simp; ring
  · simp

/-- 核の奇部分: cas(t) − cas(−t) = −i (ψ(t) − ψ(−t))（= 2 sin）。 -/
lemma casK_odd_part (t : ZMod N) :
    casK t - casK (-t) = -I * (ZMod.stdAddChar t - ZMod.stdAddChar (-t)) := by
  unfold casK PAG.Kloosterman.cas
  rw [AddChar.map_neg_eq_conj]
  set z := ZMod.stdAddChar t
  apply Complex.ext <;> simp

/-- y ↦ −y の並べ替え: Σ_y ψ(−xy) χ(y) = χ(−1) Σ_y ψ(xy) χ(y)。 -/
lemma sum_neg_twist (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    ∑ y : ZMod N, ZMod.stdAddChar (-(x * y)) * χ y
      = χ (-1) * ∑ y : ZMod N, ZMod.stdAddChar (x * y) * χ y := by
  rw [mul_sum]
  refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun y => ?_
  simp only [Equiv.neg_apply, mul_neg]
  have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [show χ (-y) = χ (-1) * χ y by rw [← map_mul, neg_one_mul]]
  linear_combination (-(ZMod.stdAddChar (-(x * y)) * χ y)) * hsq

open scoped Classical in
/-- **命題 2.8 の核心**: 偶指標で Σ cas(xy) χ(y) = Σ e(xy/N) χ(y)、
奇指標で Σ cas(xy) χ(y) = −i Σ e(xy/N) χ(y)。すなわち H_N χ = i^{−a} F_N χ。 -/
theorem hartley_char (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    ∑ y : ZMod N, casK (x * y) * χ y
      = (if χ.Even then 1 else -I) * ∑ y : ZMod N, ZMod.stdAddChar (x * y) * χ y := by
  have hk : ∀ t : ZMod N, casK t
      = ((ZMod.stdAddChar t + ZMod.stdAddChar (-t))
          + -I * (ZMod.stdAddChar t - ZMod.stdAddChar (-t))) / 2 := by
    intro t
    rw [← casK_even_part, ← casK_odd_part]; ring
  simp_rw [hk]
  have e : ∀ y : ZMod N,
      ((ZMod.stdAddChar (x * y) + ZMod.stdAddChar (-(x * y)))
          + -I * (ZMod.stdAddChar (x * y) - ZMod.stdAddChar (-(x * y)))) / 2 * χ y
        = (1 - I) / 2 * (ZMod.stdAddChar (x * y) * χ y)
          + (1 + I) / 2 * (ZMod.stdAddChar (-(x * y)) * χ y) := fun y => by ring
  simp_rw [e, sum_add_distrib, ← mul_sum, sum_neg_twist]
  rcases χ.even_or_odd with h | h
  · rw [ite_eq_left h, show χ (-1) = 1 from h]; ring
  · rw [ite_eq_right h.not_even, show χ (-1) = -1 from h]; ring

end Hartley

/-! ## 4. 系 2.6a: 複素指標では U = J は平行移動と可換なクラスに入らない
（Part 1 の `transl`, `rev`, `charFun`, `eigen_of_commute` を使う。） -/

section Cor26a

variable {G : Type*} [CommGroup G]

/-- 反転 J は charFun χ を charFun χ⁻¹ に移す。 -/
theorem rev_charFun (χ : G →* ℂˣ) : PAG.rev (PAG.charFun χ) = PAG.charFun χ⁻¹ := by
  funext g
  simp [PAG.rev, PAG.charFun]

/-- χ⁻¹ ≠ χ（複素指標）なら、J(charFun χ) はどんなスカラー倍の charFun χ とも異なる。 -/
theorem rev_not_eigen (χ : G →* ℂˣ) (hχ : χ⁻¹ ≠ χ) (c : ℂ) :
    PAG.rev (PAG.charFun χ) ≠ c • PAG.charFun χ := by
  intro h
  rw [rev_charFun] at h
  have h1 := congrFun h 1
  simp [PAG.charFun] at h1
  -- h1 : 1 = c
  apply hχ
  ext g
  have hg := congrFun h g
  simp only [PAG.charFun, Pi.smul_apply, smul_eq_mul, ← h1, one_mul] at hg
  exact hg

/-- **系 2.6a**: 複素指標が 1 つでもあれば、J はすべての平行移動とは可換でない
（可換なら定理 2.6 の前半 `eigen_of_commute` により charFun χ の固有ベクトルになるはず）。 -/
theorem rev_not_commute (χ : G →* ℂˣ) (hχ : χ⁻¹ ≠ χ) :
    ¬ ∀ h : G, PAG.rev ∘ₗ PAG.transl h = PAG.transl h ∘ₗ PAG.rev := by
  intro hU
  obtain ⟨c, hc⟩ := PAG.eigen_of_commute PAG.rev hU χ
  exact rev_not_eigen χ hχ c hc

/-- 対照: 実指標（χ⁻¹ = χ）では J(charFun χ) = charFun χ（固有値 1）。 -/
theorem rev_charFun_real (χ : G →* ℂˣ) (hχ : χ⁻¹ = χ) :
    PAG.rev (PAG.charFun χ) = PAG.charFun χ := by
  rw [rev_charFun, hχ]

end Cor26a

end PAG.Part3

#print axioms PAG.Part3.conj_apply_eq_inv
#print axioms PAG.Part3.apply_inv_eq_inv_apply
#print axioms PAG.Part3.apply_inv_eq_conj
#print axioms PAG.Part3.wsum_conj_of_symm
#print axioms PAG.Part3.wsum_im_of_symm
#print axioms PAG.Part3.sum_apply_mul_apply_inv
#print axioms PAG.Part3.sum_mul_wsum
#print axioms PAG.Part3.symm_of_wsum_conj
#print axioms PAG.Part3.prop46
#print axioms PAG.Part3.casK_even_part
#print axioms PAG.Part3.casK_odd_part
#print axioms PAG.Part3.hartley_char
#print axioms PAG.Part3.rev_charFun
#print axioms PAG.Part3.rev_not_eigen
#print axioms PAG.Part3.rev_not_commute
#print axioms PAG.Part3.rev_charFun_real
