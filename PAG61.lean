/-
  PAG 2.0 Part 57（2026-10-19）— 奇素数 p での指標の具体化: 生成元による指標 ω^j
  p 奇素数、c ≥ 1、N = p^(c+1)、φ = φ(N)。(Z/N)ˣ は巡回群（Mathlib）。生成元 g と ζ = e^(2πi/φ) で
  ω(g) = ζ となる指標 ω をとる。
  1. ω は忠実（ω(u) = 1 ⇒ u = 1）
  2. 任意の指標は ω^j（j < φ）
  3. ω^j 原始的 ⇔ p ∤ j
  4. (ω^j)(ω^j') = ω^(j+j')、積が原始的 ⇔ p ∤ j+j'
  5. 同じ殻のケット積: p ∤ j+j' なら行き先は同じ殻・同じ導手のケット（降下なし）
-/
import PAG60
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace PAG.Part61

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part32 Complex

variable {p : ℕ} [hp : Fact p.Prime] (c : ℕ)

/-- φ = |(Z/N)ˣ|。 -/
abbrev phi : ℕ := Fintype.card (ZMod (p ^ (c + 1)))ˣ

theorem phi_pos : 0 < phi (p := p) c := Fintype.card_pos

/-- ζ = e^(2πi/φ)。 -/
noncomputable def zeta : ℂ := exp (2 * Real.pi * I / (phi (p := p) c : ℂ))

theorem zeta_prim : IsPrimitiveRoot (zeta (p := p) c) (phi (p := p) c) :=
  Complex.isPrimitiveRoot_exp _ (phi_pos (p := p) c).ne'

noncomputable def zetaU : ℂˣ := Units.mk0 (zeta (p := p) c) ((zeta_prim (p := p) c).ne_zero (phi_pos (p := p) c).ne')

theorem zetaU_mem : zetaU (p := p) c ∈ rootsOfUnity (phi (p := p) c) ℂ := by
  rw [_root_.mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  exact (zeta_prim (p := p) c).pow_eq_one

variable (hp2 : p ≠ 2)
include hp2

theorem isCyclic_units : IsCyclic (ZMod (p ^ (c + 1)))ˣ :=
  ZMod.isCyclic_units_of_prime_pow p hp.out hp2 (c + 1)

/-- 生成元 g。 -/
noncomputable def gen : (ZMod (p ^ (c + 1)))ˣ :=
  have := isCyclic_units c hp2
  Classical.choose (IsCyclic.exists_generator (α := (ZMod (p ^ (c + 1)))ˣ))

theorem gen_spec : ∀ x, x ∈ Subgroup.zpowers (gen c hp2) := by
  have := isCyclic_units c hp2
  exact Classical.choose_spec (IsCyclic.exists_generator (α := (ZMod (p ^ (c + 1)))ˣ))

theorem orderOf_gen : orderOf (gen c hp2) = phi (p := p) c := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (gen_spec c hp2), Nat.card_eq_fintype_card]

/-- **ω**: ω(g) = ζ。 -/
noncomputable def omega : DirichletCharacter ℂ (p ^ (c + 1)) :=
  MulChar.ofRootOfUnity (zetaU_mem (p := p) c) (gen_spec c hp2)

theorem omega_gen : omega c hp2 (gen c hp2) = zeta (p := p) c := by
  have := MulChar.ofRootOfUnity_spec (zetaU_mem (p := p) c) (gen_spec c hp2)
  rw [omega, this]; rfl

/-- 単数は g の自然数冪。 -/
theorem exists_pow_gen (u : (ZMod (p ^ (c + 1)))ˣ) : ∃ k : ℕ, gen c hp2 ^ k = u :=
  (mem_powers_iff_mem_zpowers.mpr (gen_spec c hp2 u))

/-- **ω は忠実**。 -/
theorem omega_faithful (u : (ZMod (p ^ (c + 1)))ˣ) (h : omega c hp2 u = 1) : u = 1 := by
  obtain ⟨k, rfl⟩ := exists_pow_gen c hp2 u
  rw [Units.val_pow_eq_pow_val, map_pow, omega_gen, (zeta_prim (p := p) c).pow_eq_one_iff_dvd] at h
  rw [← orderOf_gen c hp2] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

/-- 指標は生成元での値で決まる。 -/
theorem char_ext_gen (χ χ' : DirichletCharacter ℂ (p ^ (c + 1)))
    (h : χ (gen c hp2) = χ' (gen c hp2)) : χ = χ' := by
  apply MulChar.ext
  intro u
  obtain ⟨k, rfl⟩ := exists_pow_gen c hp2 u
  rw [Units.val_pow_eq_pow_val, map_pow, map_pow, h]

/-- **任意の指標は ω^j（j < φ）**。 -/
theorem exists_eq_omega_pow (χ : DirichletCharacter ℂ (p ^ (c + 1))) :
    ∃ j < phi (p := p) c, χ = omega c hp2 ^ j := by
  have : NeZero (phi (p := p) c) := ⟨(phi_pos (p := p) c).ne'⟩
  have h1 : χ (gen c hp2) ^ phi (p := p) c = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← orderOf_gen c hp2, pow_orderOf_eq_one, Units.val_one, map_one]
  obtain ⟨j, hj, hz⟩ := (zeta_prim (p := p) c).eq_pow_of_pow_eq_one h1
  refine ⟨j, hj, char_ext_gen c hp2 _ _ ?_⟩
  rw [MulChar.pow_apply_coe, omega_gen, hz]

/-- ω(1+p^c) は 1 の原始 p 乗根。 -/
theorem omega_gp_prim (hc : 1 ≤ c) : IsPrimitiveRoot (omega c hp2 (gp p c)) p := by
  obtain ⟨u, hu⟩ := isUnit_gp (p := p) hc
  have hp1 : (omega c hp2 (gp p c)) ^ p = 1 := by rw [← map_pow, gp_pow_p hc, map_one]
  have hne : omega c hp2 (gp p c) ≠ 1 := by
    intro h
    rw [← hu] at h
    have := omega_faithful c hp2 u h
    rw [this, Units.val_one] at hu
    have e := hu.symm
    rw [gp, add_eq_left, ZMod.natCast_eq_zero_iff] at e
    exact absurd (Nat.le_of_dvd (pow_pos hp.out.pos _) e)
      (not_le.mpr (Nat.pow_lt_pow_right hp.out.one_lt (Nat.lt_succ_self c)))
  have h := IsPrimitiveRoot.orderOf (omega c hp2 (gp p c))
  rwa [orderOf_eq_prime hp1 hne] at h

/-- **ω^j 原始的 ⇔ p ∤ j**。 -/
theorem omega_pow_prim_iff (hc : 1 ≤ c) (j : ℕ) : (omega c hp2 ^ j).IsPrimitive ↔ ¬ p ∣ j := by
  obtain ⟨u, hu⟩ := isUnit_gp (p := p) hc
  rw [prim_iff_gp hc, ← hu, MulChar.pow_apply_coe, hu, ne_eq, (omega_gp_prim c hp2 hc).pow_eq_one_iff_dvd]

/-- **積の原始性**: ω^j·ω^j' が原始的 ⇔ p ∤ j+j'。 -/
theorem omega_mul_prim_iff (hc : 1 ≤ c) (j j' : ℕ) :
    (omega c hp2 ^ j * omega c hp2 ^ j').IsPrimitive ↔ ¬ p ∣ j + j' := by
  rw [← pow_add, omega_pow_prim_iff c hp2 hc]

/-- **奇素数・同じ殻**: p ∤ j, j', j+j' なら行き先は同じ殻・同じ導手のケット（降下なし）、|C|² = λ。 -/
theorem odd_same_shell_no_descent (hc : 1 ≤ c) (K w : ℕ) (hK : w + (c + 1) ≤ K) (j j' : ℕ)
    (hj : ¬ p ∣ j) (hj' : ¬ p ∣ j') (hjj : ¬ p ∣ j + j') :
    ∃ ψ : DirichletCharacter ℂ (p ^ (c + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (c + 1) - w) : ℝ) ∧
      conv (ket K w (c + 1) hK ((omega c hp2 ^ j : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ))
        (ket K w (c + 1) hK ((omega c hp2 ^ j' : DirichletCharacter ℂ (p ^ (c + 1))) : ZMod _ → ℂ))
        = C • ket K w (c + 1) hK ψ := by
  have hprim := (omega_mul_prim_iff c hp2 hc j j').mpr hjj
  have hcond : (omega c hp2 ^ j * omega c hp2 ^ j').conductor = p ^ (c + 1) :=
    (DirichletCharacter.isPrimitive_def _).mp hprim
  exact PAG.Part50.thmA_of_conductor (p := p) K w c w (c + 1) hK (by omega) le_rfl (by omega) hK
    (omega c hp2 ^ j) (omega c hp2 ^ j')
    ((omega_pow_prim_iff c hp2 hc j).mpr hj) ((omega_pow_prim_iff c hp2 hc j').mpr hj') hcond

end PAG.Part61

#print axioms PAG.Part61.isCyclic_units
#print axioms PAG.Part61.gen
#print axioms PAG.Part61.gen_spec
#print axioms PAG.Part61.phi_pos
#print axioms PAG.Part61.orderOf_gen
#print axioms PAG.Part61.zeta
#print axioms PAG.Part61.zeta_prim
#print axioms PAG.Part61.zetaU
#print axioms PAG.Part61.zetaU_mem
#print axioms PAG.Part61.omega
#print axioms PAG.Part61.omega_gen
#print axioms PAG.Part61.exists_pow_gen
#print axioms PAG.Part61.omega_faithful
#print axioms PAG.Part61.char_ext_gen
#print axioms PAG.Part61.exists_eq_omega_pow
#print axioms PAG.Part61.omega_gp_prim
#print axioms PAG.Part61.omega_pow_prim_iff
#print axioms PAG.Part61.omega_mul_prim_iff
#print axioms PAG.Part61.odd_same_shell_no_descent
