/-
  PAG 2.0 Part 140（2026-10-22）— 周波数写像の全射性と原始指標の存在
  1. χ(1 + p^{c−1}) ≠ 1 ⇒ χ 原始（c ≥ 2）
  2. 原始指標 mod p^c が存在する（c ≥ 2、指標の分離性: Mathlib の双対性）
  3. freq(χ^n) = n · freq χ
  4. freq は全射
-/
import PAG143
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace PAG.Part144

open ZMod Finset PAG.Part143

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. χ(1 + p^{c−1}) ≠ 1 ⇒ χ 原始**。 -/
theorem primitive_of_ne (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (p ^ c))
    (h : χ (1 + (p : ZMod (p ^ c)) ^ (c - 1)) ≠ 1) : χ.IsPrimitive := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  by_contra hnp
  have hdvd : p ^ (c - 1) ∣ p ^ c := pow_dvd_pow p (by omega)
  have hcond : χ.conductor ∣ p ^ (c - 1) := by
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp.out).mp (DirichletCharacter.conductor_dvd_level χ)
    have hjne : j ≠ c := fun he => hnp (by rw [DirichletCharacter.isPrimitive_def, hjc, he])
    rw [hjc]; exact pow_dvd_pow p (by omega)
  have hft := ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hdvd).mpr hcond)
  have hker := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd).mp hft
  set w : ZMod (p ^ c) := 1 + (p : ZMod (p ^ c)) ^ (c - 1)
  have hw2 : (p : ZMod (p ^ c)) ^ (c - 1) * (p : ZMod (p ^ c)) ^ (c - 1) = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (show c ≤ c - 1 + (c - 1) by omega) (by rw [← Nat.cast_pow, ZMod.natCast_self])
  have hwu : IsUnit w := isUnit_iff_exists_inv.mpr ⟨1 - (p : ZMod (p ^ c)) ^ (c - 1), by
    simp only [w]; linear_combination (-1 : ZMod (p ^ c)) * hw2⟩
  have hk : ZMod.unitsMap hdvd hwu.unit = 1 := by
    apply Units.ext
    rw [ZMod.unitsMap_val, IsUnit.unit_spec, Units.val_one]
    simp only [w]
    rw [ZMod.cast_add hdvd, ZMod.cast_one hdvd, ZMod.cast_pow hdvd, ZMod.cast_natCast hdvd,
      ← Nat.cast_pow, ZMod.natCast_self, add_zero]
  have := hker hk
  rw [MonoidHom.mem_ker] at this
  have e := congrArg Units.val this
  rw [MulChar.coe_toUnitHom, IsUnit.unit_spec, Units.val_one] at e
  exact h e

instance (N : ℕ) [NeZero N] : NeZero ((Monoid.exponent (ZMod N)ˣ : ℕ) : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩

/-- **2. 原始指標の存在**（c ≥ 2）。 -/
theorem exists_primitive (c : ℕ) (hc : 2 ≤ c) : ∃ χ : DirichletCharacter ℂ (p ^ c), χ.IsPrimitive := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hne : (1 + (p : ZMod (p ^ c)) ^ (c - 1)) ≠ 1 := by
    intro h
    have h0 : ((p ^ (c - 1) : ℕ) : ZMod (p ^ c)) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h0
    omega
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hne
  exact ⟨χ, primitive_of_ne c hc χ hχ⟩

section Surj

variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)

/-- **3. freq(χ^n) = n · freq χ**。 -/
theorem freq_pow (χ : DirichletCharacter ℂ (p ^ c)) : ∀ n : ℕ, freq hkc h2k (χ ^ n) = n * freq hkc h2k χ := by
  intro n
  induction n with
  | zero => rw [pow_zero, freq_one]; simp
  | succ n ih => rw [pow_succ, freq_mul, ih]; push_cast; ring

/-- **4. freq は全射**。 -/
theorem freq_surjective : Function.Surjective (freq hkc h2k : DirichletCharacter ℂ (p ^ c) → ZMod (p ^ (c - k))) := by
  have : NeZero (p ^ (c - k)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨χ₀, hχ₀⟩ := exists_primitive (p := p) c (by omega)
  have hu := (primitive_iff_freq_unit hkc h2k χ₀).mp hχ₀
  intro t
  refine ⟨χ₀ ^ (t * hu.unit⁻¹ : ZMod (p ^ (c - k))).val, ?_⟩
  rw [freq_pow, ZMod.natCast_zmod_val, mul_assoc]
  have : ((hu.unit⁻¹ : (ZMod (p ^ (c - k)))ˣ) : ZMod (p ^ (c - k))) * freq hkc h2k χ₀ = 1 := by
    exact hu.val_inv_mul
  rw [this, mul_one]

end Surj

end PAG.Part144

#print axioms PAG.Part144.primitive_of_ne
#print axioms PAG.Part144.exists_primitive
#print axioms PAG.Part144.freq_pow
#print axioms PAG.Part144.freq_surjective
