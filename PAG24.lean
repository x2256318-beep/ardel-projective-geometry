/-
  PAG 2.0 Part 20（2026-10-18）— 赤道での南北ケットの一致と、赤道での絡み合い B_N = (conj J/J) B_S
  1. |0, χ⟩_S = |0, χ⟩_N（同じ P¹ 関数）
  2. 赤道上の定理 A を南北それぞれで述べ、比が conj J / J（= conj(Ĵ)²）であることを示す（Part 7 の数値結果）
-/
import PAG23

namespace PAG.Part24

open ZMod Finset PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part23

variable {p : ℕ} [hp : Fact p.Prime]

/-- 射影 Z/p^K → Z/p^c（c ≥ 1）は非単数を非単数に写す（単数性の引き戻し）。 -/
theorem isUnit_of_castHom {K c : ℕ} (hc1 : 1 ≤ c) (hcK : c ≤ K) (x : ZMod (p ^ K))
    (h : IsUnit (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x)) : IsUnit x := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [castHom_eq_natCast, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega)] at h
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega)]
  exact h

/-- 殻 0 のケットの値: ket K 0 c f x = |S_0|^(−1/2) f(π x)。 -/
theorem ket0_apply (K c : ℕ) (h : 0 + c ≤ K) (f : ZMod (p ^ c) → ℂ) (x : ZMod (p ^ K)) :
    ket K 0 c h f x = (((Real.sqrt (sz p K 0))⁻¹ : ℝ) : ℂ) *
      f (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) x) := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (K - 0)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨y, hy⟩ := (PAG.Part22.mem_range_iff (p := p) K 0 (Nat.zero_le K) x).mpr (by simp)
  unfold ket
  rw [Pi.smul_apply, smul_eq_mul, ← hy, push_apply_emb _ (shellEmb_injective K 0 (Nat.zero_le K))]
  congr 1
  simp only [Function.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
  rw [castHom_eq_natCast, castHom_eq_natCast, shellEmb_apply, ZMod.val_natCast, pow_zero, one_mul,
    Nat.mod_eq_of_lt (by simpa using ZMod.val_lt y)]

omit hp in
/-- 単数 x について χ(π(x⁻¹)) = χ⁻¹(π x)。 -/
theorem chi_cast_inv {K c : ℕ} (hcK : c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) {x : ZMod (p ^ K)}
    (hx : IsUnit x) :
    χ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x⁻¹)
      = χ⁻¹ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x) := by
  rw [MulChar.inv_apply_eq_inv']
  have h1 : χ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x⁻¹)
      * χ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x) = 1 := by
    rw [← map_mul, ← map_mul, ZMod.inv_mul_of_unit x hx, map_one, map_one]
  exact eq_inv_of_mul_eq_one_left h1

/-- 非単数 x では χ(π x) = 0（c ≥ 1）。 -/
theorem chi_cast_nonunit {K c : ℕ} (hc1 : 1 ≤ c) (hcK : c ≤ K) (χ : DirichletCharacter ℂ (p ^ c))
    {x : ZMod (p ^ K)} (hx : ¬ IsUnit x) : χ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x) = 0 :=
  MulChar.map_nonunit _ (fun h => hx (isUnit_of_castHom hc1 hcK x h))

/-- **赤道での一致**: |0, χ⟩_S = |0, χ⟩_N（同じ P¹ 関数）。 -/
theorem kS0_eq_kN0 (K c : ℕ) (hc1 : 1 ≤ c) (h : 0 + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    kS K 0 c h χ = kN K 0 c h χ := by
  have hcK : c ≤ K := by omega
  unfold kS kN extS extN
  ext x
  · simp only
    split_ifs with hx
    · rw [ket0_apply, ket0_apply, chi_cast_inv hcK χ⁻¹ hx, inv_inv]
    · rw [ket0_apply, chi_cast_nonunit hc1 hcK χ hx, mul_zero]
  · simp only
    split_ifs with hx
    · rw [ket0_apply, ket0_apply, chi_cast_inv hcK χ hx]
    · rw [ket0_apply, chi_cast_nonunit hc1 hcK χ⁻¹ hx, mul_zero]

/-- J(χ₁⁻¹, χ₂⁻¹) = conj J(χ₁, χ₂)。 -/
theorem J_inv {N : ℕ} [NeZero N] (χ₁ χ₂ : DirichletCharacter ℂ N) :
    PAG.Part7.J χ₁⁻¹ χ₂⁻¹ = starRingEnd ℂ (PAG.Part7.J χ₁ χ₂) := by
  unfold PAG.Part7.J
  rw [map_sum]
  refine sum_congr rfl (fun x _ => ?_)
  rw [map_mul, starRingEnd_apply, starRingEnd_apply, MulChar.star_apply', MulChar.star_apply']

variable {n : ℕ}

/-- 赤道上の南の定理 A: B_S(|0,χ₁⟩, |0,χ₂⟩) = C |0, χ₁χ₂⟩、C = |S_0|^(−1/2) q J(χ₁,χ₂)。 -/
theorem equator_south (K : ℕ) (h : 0 + (n + 1) ≤ K) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    BS (kS K 0 (n + 1) h χ₁) (kS K 0 (n + 1) h χ₂)
      = ((((Real.sqrt (sz p K 0))⁻¹ : ℝ) : ℂ) * (((p ^ (K - (n + 1)) : ℕ) : ℂ) * PAG.Part7.J χ₁ χ₂)) •
          kS K 0 (n + 1) h (χ₁ * χ₂) := by
  have : NeZero (p ^ (K - 0)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hq := card_ker_castHom p (K - 0) (n + 1) (by omega)
  simp only at hq
  unfold BS kS ket
  simp only [extS]
  rw [PAG.Part15.conv_smul_smul]
  have hA := conv_shell_chars_zmod (p := p) (n := n) K 0 (Nat.zero_le K) (pow_dvd_pow p (by omega)) χ₁ χ₂ h₁ h₂ h₁₂
  simp only at hA
  rw [hA, hq, show K - 0 - (n + 1) = K - (n + 1) by omega]
  ext x
  · simp only [Prod.smul_mk, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [Prod.smul_mk, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring

/-- 赤道上の北の定理 A: B_N(|0,χ₁⟩_N, |0,χ₂⟩_N) = C' |0, χ₁χ₂⟩_N、C' = |S_0|^(−1/2) q conj J。 -/
theorem equator_north (K : ℕ) (h : 0 + (n + 1) ≤ K) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    BN (kN K 0 (n + 1) h χ₁) (kN K 0 (n + 1) h χ₂)
      = ((((Real.sqrt (sz p K 0))⁻¹ : ℝ) : ℂ) *
          (((p ^ (K - (n + 1)) : ℕ) : ℂ) * starRingEnd ℂ (PAG.Part7.J χ₁ χ₂))) •
          kN K 0 (n + 1) h (χ₁ * χ₂) := by
  have : NeZero (p ^ (K - 0)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hq := card_ker_castHom p (K - 0) (n + 1) (by omega)
  simp only at hq
  have hi₁ := PAG.Part16.isPrimitive_inv h₁
  have hi₂ := PAG.Part16.isPrimitive_inv h₂
  have hi₁₂ : (χ₁⁻¹ * χ₂⁻¹).IsPrimitive := by rw [← mul_inv]; exact PAG.Part16.isPrimitive_inv h₁₂
  rw [BN_eq]
  unfold kN ket
  simp only [extN]
  rw [PAG.Part15.conv_smul_smul]
  have hA := conv_shell_chars_zmod (p := p) (n := n) K 0 (Nat.zero_le K) (pow_dvd_pow p (by omega))
    χ₁⁻¹ χ₂⁻¹ hi₁ hi₂ hi₁₂
  simp only at hA
  rw [hA, hq, show K - 0 - (n + 1) = K - (n + 1) by omega, J_inv, ← mul_inv]
  ext x
  · simp only [Prod.smul_mk, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  · simp only [Prod.smul_mk, Pi.smul_apply, smul_eq_mul]; ring

/-- **赤道での絡み合い**: 赤道ケット（南北で同じ P¹ 関数）について
B_N(|0,χ₁⟩, |0,χ₂⟩) = (conj J / J) · B_S(|0,χ₁⟩, |0,χ₂⟩)。|J|² = p^c なので conj J/J = conj(Ĵ)²。 -/
theorem equator_intertwine (K : ℕ) (h : 0 + (n + 1) ≤ K) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    BN (kS K 0 (n + 1) h χ₁) (kS K 0 (n + 1) h χ₂)
      = (starRingEnd ℂ (PAG.Part7.J χ₁ χ₂) / PAG.Part7.J χ₁ χ₂) •
          BS (kS K 0 (n + 1) h χ₁) (kS K 0 (n + 1) h χ₂) := by
  have hJ : PAG.Part7.J χ₁ χ₂ ≠ 0 := by
    intro hJ
    have := PAG.Part8.gauss_mul_gauss_eq_jacobi_mul_primitive χ₁ χ₂ h₁₂ stdAddChar
    rw [hJ, zero_mul] at this
    exact mul_ne_zero (PAG.Part16.gaussSum_ne_zero h₁) (PAG.Part16.gaussSum_ne_zero h₂) this
  have hpos : (0 : ℝ) < sz p K 0 := by
    unfold sz; exact_mod_cast Nat.mul_pos (pow_pos hp.out.pos _) (by have := hp.out.two_le; omega)
  have ha : (((Real.sqrt (sz p K 0))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (Real.sqrt_pos.mpr hpos).ne'
  have hq : (((p ^ (K - (n + 1)) : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  rw [kS0_eq_kN0 K (n + 1) (by omega) h χ₁, kS0_eq_kN0 K (n + 1) (by omega) h χ₂,
    equator_north K h χ₁ χ₂ h₁ h₂ h₁₂, ← kS0_eq_kN0 K (n + 1) (by omega) h χ₁,
    ← kS0_eq_kN0 K (n + 1) (by omega) h χ₂, equator_south K h χ₁ χ₂ h₁ h₂ h₁₂,
    ← kS0_eq_kN0 K (n + 1) (by omega) h (χ₁ * χ₂), smul_smul]
  congr 1
  field_simp

end PAG.Part24

#print axioms PAG.Part24.isUnit_of_castHom
#print axioms PAG.Part24.ket0_apply
#print axioms PAG.Part24.chi_cast_inv
#print axioms PAG.Part24.chi_cast_nonunit
#print axioms PAG.Part24.kS0_eq_kN0
#print axioms PAG.Part24.J_inv
#print axioms PAG.Part24.equator_south
#print axioms PAG.Part24.equator_north
#print axioms PAG.Part24.equator_intertwine
