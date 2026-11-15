/-
  PAG 2.0 Part 47（2026-10-19）— ケット表示の一意性（分類の場合 (ii) の行き先は一意）
  C ≠ 0、ψ, ψ' 原始（導手 p^c, p^c'、c, c' ≥ 1）について C·|w,ψ⟩ = C'·|w',ψ'⟩ なら
  1. w = w'（殻の一意性：p^w での値を比べる）
  2. c = c'（導手の一意性：原始性）
  3. C = C' かつ ψ = ψ'
-/
import PAG50

namespace PAG.Part51

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21

variable {p : ℕ} [hp : Fact p.Prime]

/-- 規格化係数 a_w = |S_w|^(−1/2) ≠ 0。 -/
theorem coef_ne_zero (K w : ℕ) : ((((Real.sqrt (sz p K w))⁻¹ : ℝ)) : ℂ) ≠ 0 := by
  have h1 : 0 < sz p K w := by
    unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
  have : (0 : ℝ) < Real.sqrt (sz p K w) := Real.sqrt_pos.mpr (by exact_mod_cast h1)
  exact_mod_cast (inv_pos.mpr this).ne'

/-- 殻の上での値: ket K w c h χ (ι y) = a_w · χ(π y)。 -/
theorem ket_apply_emb (K w c : ℕ) (h : w + c ≤ K) (χ : ZMod (p ^ c) → ℂ) (y : ZMod (p ^ (K - w))) :
    ket K w c h χ (shellEmb (p := p) K w (by omega) y)
      = (((Real.sqrt (sz p K w))⁻¹ : ℝ) : ℂ) * χ (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) _ y) := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  unfold ket
  rw [Pi.smul_apply, push_apply_emb _ (shellEmb_injective K w (by omega)), smul_eq_mul]
  rfl

/-- p^w の殻の上での表示: shellEmb_{w'}(p^(w−w')) = shellEmb_w(1)（w' ≤ w < K）。 -/
theorem shellEmb_pow (K w w' : ℕ) (hw' : w' ≤ w) (hw : w < K) :
    shellEmb (p := p) K w' (by omega) ((p ^ (w - w') : ℕ) : ZMod (p ^ (K - w')))
      = shellEmb (p := p) K w hw.le 1 := by
  have : Fact (1 < p ^ (K - w)) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  rw [shellEmb_apply, shellEmb_apply, ZMod.val_one, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp.out.one_lt (by omega)), mul_one, ← pow_add]
  congr 2; omega

/-- p^k（k ≥ 1）は法 p^c（c ≥ 1）で非単数。 -/
theorem not_isUnit_pow (k c : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ c) : ¬ IsUnit ((p ^ k : ℕ) : ZMod (p ^ c)) := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_left_iff (by omega), Nat.coprime_pow_right_iff (by omega),
    Nat.coprime_self]
  exact hp.out.one_lt.ne'

/-- 殻 w の点 shellEmb_w(1) で、殻 w' < w のケットは 0。 -/
theorem ket_lower_shell_zero (K w w' c' : ℕ) (hw' : w' < w) (hw : w < K) (hc' : 1 ≤ c') (h' : w' + c' ≤ K)
    (ψ' : DirichletCharacter ℂ (p ^ c')) :
    ket K w' c' h' ψ' (shellEmb (p := p) K w hw.le 1) = 0 := by
  rw [← shellEmb_pow K w w' hw'.le hw, ket_apply_emb, map_natCast,
    MulChar.map_nonunit ψ' (not_isUnit_pow (w - w') c' (by omega) hc'), mul_zero]

/-- 殻 w の点 shellEmb_w(1) で、殻 w のケットは a_w。 -/
theorem ket_own_shell (K w c : ℕ) (h : w + c ≤ K) (ψ : DirichletCharacter ℂ (p ^ c)) :
    ket K w c h ψ (shellEmb (p := p) K w (by omega) 1) = (((Real.sqrt (sz p K w))⁻¹ : ℝ) : ℂ) := by
  rw [ket_apply_emb, map_one, MulChar.map_one, mul_one]

/-- **殻の一意性**: C ≠ 0 で C·|w,ψ⟩ = C'·|w',ψ'⟩ なら w' ≥ w（対称に使って w = w'）。 -/
theorem shell_le (K w c w' c' : ℕ) (hc : 1 ≤ c) (hc' : 1 ≤ c') (h : w + c ≤ K) (h' : w' + c' ≤ K)
    (ψ : DirichletCharacter ℂ (p ^ c)) (ψ' : DirichletCharacter ℂ (p ^ c')) (C C' : ℂ) (hC : C ≠ 0)
    (H : C • ket K w c h ψ = C' • ket K w' c' h' ψ') : w ≤ w' := by
  by_contra hlt
  rw [not_le] at hlt
  have e := congrFun H (shellEmb (p := p) K w (by omega) 1)
  rw [Pi.smul_apply, Pi.smul_apply, ket_own_shell, ket_lower_shell_zero K w w' c' hlt (by omega) hc' h',
    smul_eq_mul, smul_eq_mul, mul_zero] at e
  exact mul_ne_zero hC (coef_ne_zero K w) e

theorem shell_eq (K w c w' c' : ℕ) (hc : 1 ≤ c) (hc' : 1 ≤ c') (h : w + c ≤ K) (h' : w' + c' ≤ K)
    (ψ : DirichletCharacter ℂ (p ^ c)) (ψ' : DirichletCharacter ℂ (p ^ c')) (C C' : ℂ) (hC : C ≠ 0)
    (H : C • ket K w c h ψ = C' • ket K w' c' h' ψ') : w = w' ∧ C' ≠ 0 := by
  have hC' : C' ≠ 0 := by
    rintro rfl
    have e := congrFun H (shellEmb (p := p) K w (by omega) 1)
    rw [Pi.smul_apply, Pi.smul_apply, ket_own_shell, zero_smul, smul_eq_mul] at e
    exact mul_ne_zero hC (coef_ne_zero K w) e
  exact ⟨le_antisymm (shell_le K w c w' c' hc hc' h h' ψ ψ' C C' hC H)
    (shell_le K w' c' w c hc' hc h' h ψ' ψ C' C hC' H.symm), hC'⟩

/-- 同じ殻で C·|w,ψ⟩ = C'·|w,ψ'⟩ なら C = C' かつ ψ∘π = ψ'∘π'（殻の上）。 -/
theorem same_shell_values (K w c c' : ℕ) (h : w + c ≤ K) (h' : w + c' ≤ K)
    (ψ : DirichletCharacter ℂ (p ^ c)) (ψ' : DirichletCharacter ℂ (p ^ c')) (C C' : ℂ) (hC : C ≠ 0)
    (H : C • ket K w c h ψ = C' • ket K w c' h' ψ') :
    C = C' ∧ ∀ y : ZMod (p ^ (K - w)), ψ (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) _ y)
      = ψ' (ZMod.castHom (pow_dvd_pow p (by omega : c' ≤ K - w)) _ y) := by
  have ha := coef_ne_zero (p := p) K w
  have hval : ∀ y : ZMod (p ^ (K - w)), C * ψ (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) _ y)
      = C' * ψ' (ZMod.castHom (pow_dvd_pow p (by omega : c' ≤ K - w)) _ y) := by
    intro y
    have e := congrFun H (shellEmb (p := p) K w (by omega) y)
    rw [Pi.smul_apply, Pi.smul_apply, ket_apply_emb, ket_apply_emb, smul_eq_mul, smul_eq_mul] at e
    apply mul_left_cancel₀ ha
    linear_combination e
  have h1 := hval 1
  simp only [map_one, mul_one] at h1
  refine ⟨h1, fun y => ?_⟩
  have := hval y
  rw [← h1] at this
  exact mul_left_cancel₀ hC this

/-- 原始指標は、より低い法の指標の changeLevel にはならない。 -/
theorem prim_not_changeLevel {c c' : ℕ} (hlt : c' < c) (ψ : DirichletCharacter ℂ (p ^ c)) (hψ : ψ.IsPrimitive)
    (ψ' : DirichletCharacter ℂ (p ^ c')) (hdvd : p ^ c' ∣ p ^ c) :
    ψ ≠ DirichletCharacter.changeLevel hdvd ψ' := by
  intro e
  have hf : DirichletCharacter.FactorsThrough ψ (p ^ c') := ⟨hdvd, ψ', e⟩
  have hle : ψ.conductor ≤ p ^ c' := Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff ψ).mpr hf)
  rw [(DirichletCharacter.isPrimitive_def ψ).mp hψ] at hle
  exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right hp.out.one_lt hlt))

/-- **導手の一意性**: 同じ殻で C ≠ 0、ψ, ψ' 原始なら c' ≥ c。 -/
theorem cond_le (K w c c' : ℕ) (hc' : 1 ≤ c') (h : w + c ≤ K) (h' : w + c' ≤ K)
    (ψ : DirichletCharacter ℂ (p ^ c)) (hψ : ψ.IsPrimitive) (ψ' : DirichletCharacter ℂ (p ^ c'))
    (C C' : ℂ) (hC : C ≠ 0) (H : C • ket K w c h ψ = C' • ket K w c' h' ψ') : c ≤ c' := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨-, hv⟩ := same_shell_values K w c c' h h' ψ ψ' C C' hC H
  apply prim_not_changeLevel hlt ψ hψ ψ' (pow_dvd_pow p hlt.le)
  apply MulChar.ext
  intro u
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨y, hy⟩ := ZMod.ringHom_surjective (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) (ZMod (p ^ c)))
    (u : ZMod (p ^ c))
  have hcomp : (ZMod.castHom (pow_dvd_pow p hlt.le) (ZMod (p ^ c'))).comp
      (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) (ZMod (p ^ c)))
      = ZMod.castHom (pow_dvd_pow p (by omega : c' ≤ K - w)) (ZMod (p ^ c')) := Subsingleton.elim _ _
  rw [← hy, hv y, ← hcomp, RingHom.comp_apply, ZMod.castHom_apply]

/-- **ケット表示の一意性**: C ≠ 0、ψ, ψ' 原始で C·|w,ψ⟩ = C'·|w',ψ'⟩ なら w = w'、c = c'、C = C'。 -/
theorem ket_rep_unique (K w c w' c' : ℕ) (hc : 1 ≤ c) (hc' : 1 ≤ c') (h : w + c ≤ K) (h' : w' + c' ≤ K)
    (ψ : DirichletCharacter ℂ (p ^ c)) (hψ : ψ.IsPrimitive) (ψ' : DirichletCharacter ℂ (p ^ c'))
    (hψ' : ψ'.IsPrimitive) (C C' : ℂ) (hC : C ≠ 0)
    (H : C • ket K w c h ψ = C' • ket K w' c' h' ψ') : w = w' ∧ c = c' ∧ C = C' := by
  obtain ⟨rfl, hC'⟩ := shell_eq K w c w' c' hc hc' h h' ψ ψ' C C' hC H
  have e1 := cond_le K w c c' hc' h h' ψ hψ ψ' C C' hC H
  have e2 := cond_le K w c' c hc h' h ψ' hψ' ψ C' C hC' H.symm
  exact ⟨rfl, le_antisymm e1 e2, (same_shell_values K w c c' h h' ψ ψ' C C' hC H).1⟩

/-- **指標の一意性**: 同じ殻・同じ導手で C·|w,ψ⟩ = C'·|w,ψ'⟩（C ≠ 0）なら ψ = ψ'。 -/
theorem ket_char_unique (K w c : ℕ) (h : w + c ≤ K) (ψ ψ' : DirichletCharacter ℂ (p ^ c)) (C C' : ℂ) (hC : C ≠ 0)
    (H : C • ket K w c h ψ = C' • ket K w c h ψ') : ψ = ψ' := by
  obtain ⟨-, hv⟩ := same_shell_values K w c c h h ψ ψ' C C' hC H
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  apply MulChar.ext
  intro u
  obtain ⟨y, hy⟩ := ZMod.ringHom_surjective (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) (ZMod (p ^ c)))
    (u : ZMod (p ^ c))
  rw [← hy, hv y]

/-- 系: 分類の場合 (ii) で、行き先 (w, c, C) は組から一意に決まる（C ≠ 0 は |C|² = λ > 0 から）。 -/
theorem caseII_target_unique (K : ℕ) (w c w' c' : ℕ) (hc : 1 ≤ c) (hc' : 1 ≤ c') (h : w + c ≤ K) (h' : w' + c' ≤ K)
    (ψ : DirichletCharacter ℂ (p ^ c)) (hψ : ψ.IsPrimitive) (ψ' : DirichletCharacter ℂ (p ^ c'))
    (hψ' : ψ'.IsPrimitive) (C C' : ℂ) (lam : ℝ) (hlam : 0 < lam) (hCl : Complex.normSq C = lam)
    (F : ZMod (p ^ K) → ℂ) (hF : F = C • ket K w c h ψ) (hF' : F = C' • ket K w' c' h' ψ') :
    w = w' ∧ c = c' ∧ C = C' := by
  have hC : C ≠ 0 := by
    rintro rfl; rw [map_zero] at hCl; exact hlam.ne hCl
  exact ket_rep_unique K w c w' c' hc hc' h h' ψ hψ ψ' hψ' C C' hC (hF.symm.trans hF')

end PAG.Part51

#print axioms PAG.Part51.coef_ne_zero
#print axioms PAG.Part51.ket_apply_emb
#print axioms PAG.Part51.shellEmb_pow
#print axioms PAG.Part51.not_isUnit_pow
#print axioms PAG.Part51.ket_lower_shell_zero
#print axioms PAG.Part51.ket_own_shell
#print axioms PAG.Part51.shell_le
#print axioms PAG.Part51.shell_eq
#print axioms PAG.Part51.same_shell_values
#print axioms PAG.Part51.prim_not_changeLevel
#print axioms PAG.Part51.cond_le
#print axioms PAG.Part51.ket_rep_unique
#print axioms PAG.Part51.ket_char_unique
#print axioms PAG.Part51.caseII_target_unique
