/-
  PAG 2.0 Part 115（2026-10-20）— 法 p（奇素数）の 2 次ガウス和
  ψ = stdAddChar（ZMod p）、L = ルジャンドル指標（ℂ 値）について
  1. Σ_t ψ(A t²) = L(A) τ(L)（A ≠ 0）
  2. 平方完成: Σ_t ψ(A t² + B t) = ψ(κ) Σ_t ψ(A t²)
  3. 「2 次の関数等式」F(t+s) = F(t)F(s)ψ(a t s)、F(0) = 1、a ≠ 0 をみたす F について
     F(t) = ψ(A t² + B t) と書け、(Σ F)^{4p} = p^{2p}（Σ F / √p は 1 の冪根）
-/
import PAG118
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace PAG.Part119

open ZMod Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- ℂ 値のルジャンドル指標。 -/
noncomputable def Lc (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem ringChar_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

theorem Lc_isQuadratic : (Lc p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp _

theorem Lc_ne_one (hp2 : p ≠ 2) : Lc p ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).mpr (quadraticChar_ne_one (ringChar_ne_two hp2))

theorem Lc_apply (a : ZMod p) : Lc p a = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := rfl

theorem Lc_sq (a : ZMod p) (ha : a ≠ 0) : Lc p a ^ 2 = 1 := by
  rw [Lc_apply]; exact_mod_cast quadraticChar_sq_one ha

/-- **1. Σ_t ψ(A t²) = L(A) τ(L)**。 -/
theorem sum_sq_char (hp2 : p ≠ 2) (A : ZMod p) (hA : A ≠ 0) :
    ∑ t : ZMod p, stdAddChar (A * t ^ 2) = Lc p A * gaussSum (Lc p) stdAddChar := by
  classical
  -- ファイバーごとに数える
  have hfib : ∑ t : ZMod p, stdAddChar (A * t ^ 2)
      = ∑ y : ZMod p, ((univ.filter (fun t : ZMod p => t ^ 2 = y)).card : ℂ) * stdAddChar (A * y) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun t : ZMod p => t ^ 2) (t := univ) (fun _ _ => mem_univ _)]
    apply sum_congr rfl; intro y _
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), Finset.sum_const, nsmul_eq_mul]
  have hcard : ∀ y : ZMod p, ((univ.filter (fun t : ZMod p => t ^ 2 = y)).card : ℂ) = Lc p y + 1 := by
    intro y
    have h := quadraticChar_card_sqrts (ringChar_ne_two hp2) y
    rw [Set.toFinset_ofPred] at h
    rw [Lc_apply]
    exact_mod_cast h
  rw [hfib]
  simp only [hcard, add_mul, one_mul, Finset.sum_add_distrib]
  have hzero : ∑ y : ZMod p, stdAddChar (A * y) = 0 := by
    have := AddChar.sum_eq_zero_of_ne_one ((ZMod.isPrimitive_stdAddChar p) hA)
    simpa [AddChar.mulShift_apply] using this
  rw [hzero, add_zero]
  have hu : IsUnit A := isUnit_iff_ne_zero.mpr hA
  have e := gaussSum_mulShift_eq (Lc p) stdAddChar hu.unit
  rw [(Lc_isQuadratic (p := p)).inv] at e
  rw [← show (Lc p) (hu.unit : ZMod p) = Lc p A from rfl, ← e]
  unfold gaussSum
  apply sum_congr rfl; intro y _
  rw [AddChar.mulShift_apply]; rfl

/-- **2. 平方完成**: d = B/(2A) として Σ ψ(A t² + B t) = ψ(−A d²) Σ ψ(A t²)。 -/
theorem complete_square (A B : ZMod p) (hA : A ≠ 0) (h2 : (2 : ZMod p) ≠ 0) :
    ∑ t : ZMod p, stdAddChar (A * t ^ 2 + B * t)
      = stdAddChar (-(A * (B * (2 * A)⁻¹) ^ 2)) * ∑ t : ZMod p, stdAddChar (A * t ^ 2) := by
  set d := B * (2 * A)⁻¹
  have hd : 2 * A * d = B := by simp only [d]; field_simp
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight d) _ _ (fun t => ?_)
  simp only [Equiv.coe_addRight]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  linear_combination (-t) * hd

theorem two_ne_zero' (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have h2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this
  exact hp2 h2

theorem psi_one_primitive : IsPrimitiveRoot (stdAddChar (1 : ZMod p)) p := by
  have h := Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by simp, stdAddChar_apply, toCircle_natCast]
  convert h using 2
  push_cast; ring

/-- **3a. 2 次の関数等式の解は 2 次多項式の位相**。 -/
theorem quad_closed (hp2 : p ≠ 2) (F : ZMod p → ℂ) (a : ZMod p) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    ∃ b : ZMod p, ∀ t, F t = stdAddChar (a * 2⁻¹ * t ^ 2 + b * t) := by
  have h2 := two_ne_zero' (p := p) hp2
  set c := a * 2⁻¹
  have hc2 : 2 * c = a := by simp only [c]; field_simp
  have hpow : ∀ n : ℕ, F n = F 1 ^ n * stdAddChar (c * ((n : ZMod p) * ((n : ZMod p) - 1))) := by
    intro n
    induction n with
    | zero => simp [hF0]
    | succ n ih =>
      rw [Nat.cast_succ, hF, ih, pow_succ, mul_one]
      rw [show F 1 ^ n * stdAddChar (c * ((n : ZMod p) * ((n : ZMod p) - 1))) * F 1 * stdAddChar (a * (n : ZMod p))
          = F 1 ^ n * F 1 * (stdAddChar (c * ((n : ZMod p) * ((n : ZMod p) - 1))) * stdAddChar (a * (n : ZMod p))) by ring,
        ← AddChar.map_add_eq_mul]
      congr 2
      linear_combination (-(n : ZMod p)) * hc2
  have hF1 : F 1 ^ p = 1 := by
    have := hpow p
    rw [ZMod.natCast_self, hF0] at this
    simp at this
    exact this.symm
  obtain ⟨j, -, hj⟩ := psi_one_primitive (p := p) |>.eq_pow_of_pow_eq_one (ξ := F 1) (k := p)
    (by have : NeZero p := ⟨hp.out.ne_zero⟩; exact hF1)
  refine ⟨(j : ZMod p) - c, fun t => ?_⟩
  rw [← ZMod.natCast_zmod_val t, hpow, ← hj, ← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow,
    ← AddChar.map_add_eq_mul]
  congr 1
  simp only [nsmul_eq_mul, mul_one]
  ring

/-- **3b. 2 次の関数等式の解の和**: (Σ F)^{4p} = p^{2p}。 -/
theorem quad_root (hp2 : p ≠ 2) (F : ZMod p → ℂ) (a : ZMod p) (ha : a ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    (∑ t, F t) ^ (4 * p) = (p : ℂ) ^ (2 * p) := by
  obtain ⟨b, hb⟩ := quad_closed hp2 F a hF0 hF
  have h2 := two_ne_zero' (p := p) hp2
  set A := a * 2⁻¹
  have hA : A ≠ 0 := mul_ne_zero ha (inv_ne_zero h2)
  set κ := -(A * (b * (2 * A)⁻¹) ^ 2)
  have hsum : ∑ t, F t = stdAddChar κ * (Lc p A * gaussSum (Lc p) stdAddChar) := by
    rw [Finset.sum_congr rfl (fun t _ => hb t), complete_square A b hA h2, sum_sq_char hp2 A hA]
  have hsq : gaussSum (Lc p) stdAddChar ^ 2 = Lc p (-1) * p := by
    have := gaussSum_sq (χ := Lc p) (Lc_ne_one hp2) Lc_isQuadratic (ZMod.isPrimitive_stdAddChar p)
    rw [ZMod.card] at this; exact this
  have hψ : stdAddChar κ ^ (2 * (2 * p)) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    push_cast
    rw [ZMod.natCast_self]; simp
  have hL : Lc p (-1) ^ (2 * p) = 1 := by
    rw [pow_mul, Lc_sq (-1) (neg_ne_zero.mpr one_ne_zero), one_pow]
  rw [hsum, show 4 * p = 2 * (2 * p) by ring, mul_pow, mul_pow, hψ, one_mul, pow_mul (Lc p A), Lc_sq A hA, one_pow,
    one_mul, pow_mul, hsq, mul_pow, hL, one_mul]

/-- 系: Σ F / √p は 1 の冪根。 -/
theorem quad_root' (hp2 : p ≠ 2) (F : ZMod p → ℂ) (a : ZMod p) (ha : a ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    ((∑ t, F t) / ((Real.sqrt p : ℝ) : ℂ)) ^ (4 * p) = 1 := by
  have hs : ((Real.sqrt p : ℝ) : ℂ) ^ (4 * p) = (p : ℂ) ^ (2 * p) := by
    rw [show 4 * p = 2 * (2 * p) by ring, pow_mul, ← Complex.ofReal_pow,
      Real.sq_sqrt (by exact_mod_cast hp.out.pos.le)]
    push_cast; ring
  have hp0 : (p : ℂ) ^ (2 * p) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [div_pow, quad_root hp2 F a ha hF0 hF, hs, div_self hp0]

end PAG.Part119

#print axioms PAG.Part119.Lc_ne_one
#print axioms PAG.Part119.Lc_sq
#print axioms PAG.Part119.sum_sq_char
#print axioms PAG.Part119.complete_square
#print axioms PAG.Part119.psi_one_primitive
#print axioms PAG.Part119.quad_closed
#print axioms PAG.Part119.quad_root
#print axioms PAG.Part119.quad_root'
