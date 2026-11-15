/-
  PAG 2.0 Part 63（2026-10-19）— 奇素数で生成元を法の間で両立させる
  p 奇素数、c' ≤ c、g = 法 p^(c+1) の生成元（PAG61）、π = 簡約。
  1. π(g) は法 p^(c'+1) の生成元
  2. φ' ∣ φ（φ = φ(p^(c+1))、φ' = φ(p^(c'+1))）
  3. ω'' を ω''(π g) = ζ^(φ/φ') で定めると changeLevel(ω'') = ω^(φ/φ')、φ/φ' = p^(c−c')（r が確定）
  4. ω'' も忠実（低い法の生成元指標）
-/
import PAG66

namespace PAG.Part67

open ZMod Finset PAG.Part61 PAG.Part62

variable {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (c c' : ℕ) (hcc : c' ≤ c)

/-- 簡約写像。 -/
noncomputable abbrev red : (ZMod (p ^ (c + 1)))ˣ →* (ZMod (p ^ (c' + 1)))ˣ :=
  ZMod.unitsMap (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1))

include hp2 hcc

/-- **π(g) は低い法の生成元**。 -/
theorem red_gen_spec : ∀ x, x ∈ Subgroup.zpowers (red c c' hcc (gen c hp2)) := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  intro x
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1)) x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (gen_spec c hp2 u)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk]⟩

omit hp2 in
/-- φ' ∣ φ。 -/
theorem phi_dvd : phi (p := p) c' ∣ phi (p := p) c := by
  have h := card_ker_mul (p := p) c (c' + 1) (by omega)
  rw [phi, phi, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient]
  exact ⟨_, by rw [← h, mul_comm]⟩

omit hp2 in
/-- φ/φ' = p^(c−c')。 -/
theorem phi_div : phi (p := p) c / phi (p := p) c' = p ^ (c - c') := by
  have h := card_ker_mul (p := p) c (c' + 1) (by omega)
  rw [card_ker c (c' + 1) (by omega) (by omega)] at h
  rw [phi, phi, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, ← h,
    show c + 1 - (c' + 1) = c - c' by omega]
  exact Nat.mul_div_cancel _ (Nat.totient_pos.mpr (pow_pos hp.out.pos _))

omit hp2 in
/-- ζ^(φ/φ') は 1 の φ' 乗根。 -/
theorem zeta_pow_mem : zetaU (p := p) c ^ (phi (p := p) c / phi (p := p) c') ∈ rootsOfUnity (phi (p := p) c') ℂ := by
  rw [_root_.mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel (phi_dvd c c' hcc)]
  exact (_root_.mem_rootsOfUnity _ _).mp (zetaU_mem (p := p) c)

/-- **両立する低い法の指標** ω''（ω''(π g) = ζ^(φ/φ')）。 -/
noncomputable def omegaLow : DirichletCharacter ℂ (p ^ (c' + 1)) :=
  MulChar.ofRootOfUnity (zeta_pow_mem c c' hcc) (red_gen_spec hp2 c c' hcc)

theorem omegaLow_gen : omegaLow hp2 c c' hcc (red c c' hcc (gen c hp2))
    = zeta (p := p) c ^ (phi (p := p) c / phi (p := p) c') := by
  have := MulChar.ofRootOfUnity_spec (zeta_pow_mem c c' hcc) (red_gen_spec hp2 c c' hcc)
  rw [omegaLow, this, Units.val_pow_eq_pow_val]; rfl

/-- **r の確定**: changeLevel(ω'') = ω^(φ/φ') = ω^(p^(c−c'))。 -/
theorem changeLevel_omegaLow :
    DirichletCharacter.changeLevel (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1)) (omegaLow hp2 c c' hcc)
      = omega c hp2 ^ (p ^ (c - c')) := by
  apply char_ext_gen c hp2
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, MulChar.pow_apply_coe, omega_gen, ← phi_div c c' hcc]
  have e : (ZMod.cast ((gen c hp2 : (ZMod (p ^ (c + 1)))ˣ) : ZMod (p ^ (c + 1))) : ZMod (p ^ (c' + 1)))
      = ((red c c' hcc (gen c hp2) : (ZMod (p ^ (c' + 1)))ˣ) : ZMod (p ^ (c' + 1))) := by
    rw [ZMod.unitsMap_val]
  rw [e, omegaLow_gen]

/-- ω'' は忠実。 -/
theorem omegaLow_faithful (u : (ZMod (p ^ (c' + 1)))ˣ) (h : omegaLow hp2 c c' hcc u = 1) : u = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, red c c' hcc (gen c hp2) ^ m = u := by
    have := mem_powers_iff_mem_zpowers.mpr (red_gen_spec hp2 c c' hcc u)
    exact this
  rw [Units.val_pow_eq_pow_val, map_pow, omegaLow_gen, ← pow_mul,
    (zeta_prim (p := p) c).pow_eq_one_iff_dvd] at h
  have hφ' : 0 < phi (p := p) c' := phi_pos c'
  have hq : 0 < phi (p := p) c / phi (p := p) c' := Nat.div_pos (Nat.le_of_dvd (phi_pos c) (phi_dvd c c' hcc)) hφ'
  have hdiv := (Nat.div_mul_cancel (phi_dvd (p := p) c c' hcc)).symm
  set q := phi (p := p) c / phi (p := p) c' with hqdef
  rw [hdiv] at h
  have h2 : phi (p := p) c' ∣ m := Nat.dvd_of_mul_dvd_mul_left hq h
  have hord : orderOf (red c c' hcc (gen c hp2)) = phi (p := p) c' := by
    rw [orderOf_eq_card_of_forall_mem_zpowers (red_gen_spec hp2 c c' hcc), Nat.card_eq_fintype_card]
  rw [← hord] at h2
  exact orderOf_dvd_iff_pow_eq_one.mp h2

/-- **混合の添字表示（r 確定版）**: |w, ω^j⟩ ⋆ |w+(c−c'), ω''^j'⟩ = C·|w, ω^(j + p^(c−c') j')⟩、|C|² = λ。 -/
theorem mixed_ket_exact (hc : 1 ≤ c) (hlt : c' < c) (K w : ℕ) (hK : w + (c + 1) ≤ K)
    (h₂ : w + (c - c') + (c' + 1) ≤ K) (j j' : ℕ) (hj : ¬ p ∣ j)
    (hc'1 : (omegaLow hp2 c c' hcc ^ j').IsPrimitive) :
    ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (PAG.Part19.sz p K (K - (c + 1) - w) : ℝ) ∧
      PAG.Part15.conv (PAG.Part21.ket K w (c + 1) hK ((omega c hp2 ^ j : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ))
        (PAG.Part21.ket K (w + (c - c')) (c' + 1) h₂
          ((omegaLow hp2 c c' hcc ^ j' : DirichletCharacter ℂ (p ^ (c' + 1))) : ZMod _ → ℂ))
        = C • PAG.Part21.ket K w (c + 1) hK
          ((omega c hp2 ^ (j + p ^ (c - c') * j') : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ) := by
  have h₁ := (omega_pow_prim_iff c hp2 hc j).mpr hj
  have hprod : ∀ x, (omega c hp2 ^ (j + p ^ (c - c') * j')) x
      = (omega c hp2 ^ j) x * (omegaLow hp2 c c' hcc ^ j')
          (ZMod.castHom (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1)) _ x) := by
    intro x
    rw [pow_add (omega c hp2) j (p ^ (c - c') * j'), MulChar.coeToFun_mul, Pi.mul_apply, pow_mul,
      ← changeLevel_omegaLow hp2 c c' hcc, ← map_pow,
      PAG.Part47.changeLevel_apply_cast (by omega) (by omega)]
  exact PAG.Part65.mixed_general_psi K w c (c - c') (w + (c - c')) (c' + 1) (by omega) hK rfl (by omega) h₂
    _ h₁ _ hc'1 _ (PAG.Part65.mixed_index_prim hp2 c c' hc hlt (p ^ (c - c')) dvd_rfl j j' hj) hprod

end PAG.Part67

#print axioms PAG.Part67.red
#print axioms PAG.Part67.red_gen_spec
#print axioms PAG.Part67.phi_dvd
#print axioms PAG.Part67.phi_div
#print axioms PAG.Part67.zeta_pow_mem
#print axioms PAG.Part67.omegaLow
#print axioms PAG.Part67.omegaLow_gen
#print axioms PAG.Part67.changeLevel_omegaLow
#print axioms PAG.Part67.omegaLow_faithful
#print axioms PAG.Part67.mixed_ket_exact
