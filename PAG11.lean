/-
  PAG 2.0 Part 7（2026-10-18）
  1. 双対べき等元の完全系: 指示関数の和 = 1、べき等元の直交性、畳み込みの単位元、Σ ε_w = δ₀
  2. p 乗降下の厳密値: p 奇素数、n ≥ 2、χ 原始的（法 p^(n+1)）⇒ χ^p の導手はちょうど p^n
-/
import PAG10

namespace PAG.Part11

open PAG.Part10

/-! ## 1. 単位元の分解 -/

section Unit

/-- 重み 1 の指示関数の総和は定数関数 1。 -/
theorem ind_sum_eq_one {R : Type*} [CommRing R] {X W : Type*} [Fintype W] [DecidableEq W]
    (shell : X → W) : ∑ w : W, ind shell (fun _ => (1 : R)) w = 1 := by
  funext x
  simp [ind, Finset.sum_apply]

variable {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B]

/-- w₀ ≠ w₁ なら正規化べき等元は直交: B(ε_{w₀}, ε_{w₁}) = 0。 -/
theorem Bcv_idempotent_orthogonal {W : Type*} [DecidableEq W] (F : B ≃ₗ[K] B) (α : K)
    (e : W → B) (c : W → K) (he : ∀ w₀ w₁, e w₀ * e w₁ = if w₀ = w₁ then c w₀ • e w₀ else 0)
    {w₀ w₁ : W} (h : w₀ ≠ w₁) :
    Bcv F α ((α * c w₀)⁻¹ • F.symm (e w₀)) ((α * c w₁)⁻¹ • F.symm (e w₁)) = 0 := by
  unfold Bcv
  simp only [map_smul, LinearEquiv.apply_symm_apply, smul_mul_smul_comm, he, h, ite_false,
    smul_zero, map_zero]

/-- δ₀ := α⁻¹ F⁻¹(1) は畳み込みの単位元（α ≠ 0）。 -/
theorem Bcv_unit (F : B ≃ₗ[K] B) {α : K} (hα : α ≠ 0) (f : B) :
    Bcv F α (α⁻¹ • F.symm 1) f = f := by
  unfold Bcv
  rw [map_smul, LinearEquiv.apply_symm_apply, smul_mul_assoc, one_mul, map_smul,
    LinearEquiv.symm_apply_apply, smul_smul, mul_inv_cancel₀ hα, one_smul]

/-- 重み 1 の殻指示関数に対し、べき等元の和は単位元 δ₀ に一致する。 -/
theorem sum_idempotent_eq_unit {X W : Type*} [Fintype W] [DecidableEq W] (shell : X → W)
    (F : (X → K) ≃ₗ[K] (X → K)) (α : K) :
    ∑ w : W, (α * 1)⁻¹ • F.symm (ind shell (fun _ => (1 : K)) w) = α⁻¹ • F.symm 1 := by
  rw [← Finset.smul_sum, ← map_sum, ind_sum_eq_one, mul_one]

end Unit

/-! ## 2. p 乗でちょうど 1 段だけ降下する -/

section Exact

variable {p n : ℕ} [hp : Fact p.Prime]

/-- d³ = 0 なら (1 + d)^m = 1 + m d + C(m,2) d²。 -/
theorem one_add_pow_of_cube_zero {R : Type*} [CommRing R] (d : R) (hd : d * d * d = 0) (m : ℕ) :
    (1 + d) ^ m = 1 + (m : R) * d + (m.choose 2 : R) * (d * d) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination ((m.choose 2 : R)) * hd

omit hp in
/-- **核の生成**: p 奇数（素数でなくてよい）・n ≥ 2 で (1 + q p^(n−1))^p = 1 + q p^n（法 p^(n+1)）。 -/
theorem one_add_pow_p (hodd : Odd p) (hn : 2 ≤ n) (q : ℕ) :
    (1 + ((q * p ^ (n - 1) : ℕ) : ZMod (p ^ (n + 1)))) ^ p
      = 1 + ((q * p ^ n : ℕ) : ZMod (p ^ (n + 1))) := by
  set d : ZMod (p ^ (n + 1)) := ((q * p ^ (n - 1) : ℕ) : ZMod (p ^ (n + 1))) with hdef
  have hcube : d * d * d = 0 := by
    rw [hdef, ← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    have : p ^ (n + 1) ∣ p ^ (n - 1) * p ^ (n - 1) * p ^ (n - 1) := by
      rw [← pow_add, ← pow_add]; exact pow_dvd_pow p (by omega)
    exact this.trans (Nat.mul_dvd_mul (Nat.mul_dvd_mul (Dvd.intro_left _ rfl) (Dvd.intro_left _ rfl))
      (Dvd.intro_left _ rfl))
  have hsq : (p.choose 2 : ZMod (p ^ (n + 1))) * (d * d) = 0 := by
    rw [hdef, ← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    have h22 : p.choose 2 * 2 = p * (p - 1) := by
      rw [Nat.choose_two_right]; exact Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
    have hc : p ∣ p.choose 2 :=
      (Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_right (h22 ▸ Dvd.intro _ rfl)
    have : p ^ (n + 1) ∣ p * (p ^ (n - 1) * p ^ (n - 1)) := by
      rw [← pow_add, ← pow_succ']; exact pow_dvd_pow p (by omega)
    exact this.trans (Nat.mul_dvd_mul hc (Nat.mul_dvd_mul (Dvd.intro_left _ rfl) (Dvd.intro_left _ rfl)))
  rw [one_add_pow_of_cube_zero d hcube p, hsq, add_zero, hdef, ← Nat.cast_mul]
  congr 2
  have : n = (n - 1) + 1 := by omega
  conv_rhs => rw [this, pow_succ]
  ring

/-- **ちょうど 1 段の降下**: p 奇素数、n ≥ 2、χ 原始的なら、k ≤ n − 1 の任意の k について
χ^p は p^k を経由しない。 -/
theorem pow_p_not_factorsThrough_le (hodd : Odd p) (hn : 2 ≤ n)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) {k : ℕ} (hk : k ≤ n - 1) :
    ¬ (χ ^ p).FactorsThrough (p ^ k) := by
  obtain ⟨v, hker, hne⟩ := PAG.Part8.exists_ker_ne_one_of_primitive χ hχ
  have hd : p ^ n ∣ p ^ (n + 1) := pow_dvd_pow p (Nat.le_succ n)
  -- v = 1 + e、p^n ∣ e.val
  set e : ZMod (p ^ (n + 1)) := (v : ZMod (p ^ (n + 1))) - 1 with hedef
  have hc : ZMod.castHom hd (ZMod (p ^ n)) e = 0 := by
    rw [hedef, map_sub, map_one, ZMod.castHom_apply, ← ZMod.unitsMap_val hd, hker, Units.val_one,
      sub_self]
  have h1' : ((e.val : ℕ) : ZMod (p ^ n)) = 0 := by
    rw [← hc, ZMod.castHom_apply (h := hd), ZMod.cast_eq_val]
  obtain ⟨q, hq⟩ : p ^ n ∣ e.val := (ZMod.natCast_eq_zero_iff _ _).mp h1'
  -- u₀ = 1 + q p^(n−1) は u₀^p = v を満たす
  set u₀ : ZMod (p ^ (n + 1)) := 1 + ((q * p ^ (n - 1) : ℕ) : ZMod (p ^ (n + 1))) with hu₀
  have hpow : u₀ ^ p = v := by
    rw [hu₀, one_add_pow_p hodd hn q]
    have hv : (v : ZMod (p ^ (n + 1))) = 1 + e := by rw [hedef]; ring
    rw [hv, ← ZMod.natCast_zmod_val e, hq, mul_comm]
  have hunit : IsUnit u₀ := by
    rw [← isUnit_pow_iff hp.out.ne_zero, hpow]; exact v.isUnit
  have hdk : p ^ k ∣ p ^ (n + 1) := pow_dvd_pow p (by omega)
  have hmem : hunit.unit ∈ (ZMod.unitsMap hdk).ker := by
    rw [MonoidHom.mem_ker]
    ext
    rw [ZMod.unitsMap_val, IsUnit.unit_spec, Units.val_one]
    show ZMod.castHom hdk (ZMod (p ^ k)) u₀ = 1
    rw [hu₀, map_add, map_one, map_natCast,
      (ZMod.natCast_eq_zero_iff _ _).mpr (Dvd.dvd.mul_left (pow_dvd_pow p hk) q), add_zero]
  intro hft
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ ^ p) hdk] at hft
  have := hft hmem
  rw [MonoidHom.mem_ker] at this
  have h' := congrArg (fun w : ℂˣ => (w : ℂ)) this
  simp only [MulChar.coe_toUnitHom, IsUnit.unit_spec, Units.val_one] at h'
  apply hne
  rw [MulChar.pow_apply' χ hp.out.ne_zero, ← map_pow, hpow] at h'
  exact h'

/-- 指示どおりの形（k = n − 1）。 -/
theorem pow_p_not_factorsThrough_pred (hodd : Odd p) (hn : 2 ≤ n)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    ¬ (χ ^ p).FactorsThrough (p ^ (n - 1)) :=
  pow_p_not_factorsThrough_le hodd hn χ hχ le_rfl

/-- **系**: χ^p の導手はちょうど p^n。 -/
theorem conductor_pow_p_eq (hodd : Odd p) (hn : 2 ≤ n)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    (χ ^ p).conductor = p ^ n := by
  obtain ⟨k, hk, hkeq⟩ :=
    (Nat.dvd_prime_pow hp.out).mp (DirichletCharacter.conductor_dvd_level (χ ^ p))
  have hle : (χ ^ p).conductor ≤ p ^ n :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff _).mpr
      (pow_p_factorsThrough (by omega) χ))
  rw [hkeq] at hle ⊢
  have hkn : k ≤ n := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hle
  have hft := DirichletCharacter.factorsThrough_conductor (χ ^ p)
  rw [hkeq] at hft
  rcases Nat.lt_or_ge k n with h | h
  · exact absurd hft (pow_p_not_factorsThrough_le hodd hn χ hχ (by omega))
  · rw [show k = n by omega]

end Exact

end PAG.Part11

#print axioms PAG.Part11.ind_sum_eq_one
#print axioms PAG.Part11.Bcv_idempotent_orthogonal
#print axioms PAG.Part11.Bcv_unit
#print axioms PAG.Part11.sum_idempotent_eq_unit
#print axioms PAG.Part11.one_add_pow_of_cube_zero
#print axioms PAG.Part11.one_add_pow_p
#print axioms PAG.Part11.pow_p_not_factorsThrough_le
#print axioms PAG.Part11.pow_p_not_factorsThrough_pred
#print axioms PAG.Part11.conductor_pow_p_eq
