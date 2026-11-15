/-
  PAG 2.0 Part 172（2026-10-22）— 導手 p の 3 次の因子と 4 次の因子は打ち消さない
  χ は法 p の位数 3（p ≡ 1 (mod 3)）、ψ は法 q の位数 4（p = q も可）
  1. InQω・InQi（ℚ + ℚω、ℚ + ℚi）は積と冪で閉じる
  2. inter_rat: ℚ(ω) ∩ ℚ(i) の元は有理数（√3 の無理性）
  3. cubic_quartic_not_root: (z_χ z_ψ)^N ≠ 1（N > 0）
     証明: u = z_χ⁶ ∈ ℚ(ω)、v = z_ψ⁴ ∈ ℚ(i)。(z_χ z_ψ)^{12N} = u^{2N} v^{3N} = 1 なら u^{2N} ∈ ℚ(ω) ∩ ℚ(i) = ℚ、
     |u| = 1 から u^{4N} = 1。これは Part 167 に反する
-/
import PAG175
import Mathlib.NumberTheory.Real.Irrational

namespace PAG.Part176

open Complex Finset PAG.Part171 PAG.Part172 PAG.Part174 PAG.Part175
open ZMod (stdAddChar)

/-- ℚ + ℚω の元。 -/
def InQω (y : ℂ) : Prop := ∃ A B : ℚ, y = A + B * ω

/-- ℚ + ℚi の元。 -/
def InQi (y : ℂ) : Prop := ∃ A B : ℚ, y = A + B * I

theorem InQω_mul {y y' : ℂ} (h : InQω y) (h' : InQω y') : InQω (y * y') := by
  obtain ⟨A, B, rfl⟩ := h; obtain ⟨C, D, rfl⟩ := h'
  exact ⟨A * C - B * D, A * D + B * C - B * D, by push_cast; linear_combination (B * D : ℂ) * ω_sq⟩

theorem InQi_mul {y y' : ℂ} (h : InQi y) (h' : InQi y') : InQi (y * y') := by
  obtain ⟨A, B, rfl⟩ := h; obtain ⟨C, D, rfl⟩ := h'
  exact ⟨A * C - B * D, A * D + B * C, by push_cast; linear_combination (B * D : ℂ) * I_sq⟩

theorem InQω_pow {y : ℂ} (h : InQω y) : ∀ n : ℕ, InQω (y ^ n)
  | 0 => ⟨1, 0, by simp⟩
  | n + 1 => by rw [pow_succ]; exact InQω_mul (InQω_pow h n) h

theorem InQi_pow {y : ℂ} (h : InQi y) : ∀ n : ℕ, InQi (y ^ n)
  | 0 => ⟨1, 0, by simp⟩
  | n + 1 => by rw [pow_succ]; exact InQi_mul (InQi_pow h n) h

/-- **2. ℚ(ω) ∩ ℚ(i) ⊆ ℚ**。 -/
theorem inter_rat {y : ℂ} (h : InQω y) (h' : InQi y) : ∃ r : ℚ, y = r := by
  obtain ⟨A, B, hy⟩ := h
  obtain ⟨C, D, hy'⟩ := h'
  have him := congrArg Complex.im (hy.symm.trans hy')
  simp only [ω, add_im, mul_im, div_im, ratCast_re, ratCast_im, neg_im, one_im, ofReal_im, ofReal_re,
    I_re, I_im, add_re, neg_re, one_re, mul_re, div_re] at him
  norm_num at him
  have hB : B = 0 := by
    by_contra hB
    have hirr := Nat.prime_three.irrational_sqrt
    apply hirr.ne_rat (2 * D / B)
    push_cast
    have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB
    field_simp
    linarith
  refine ⟨A - B / 2, ?_⟩
  rw [hy, hB]; push_cast; ring

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- **3. 3 次の因子と 4 次の因子は打ち消さない**。 -/
theorem cubic_quartic_not_root (h3p : p % 3 = 1) (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q)
    (h3 : orderOf χ = 3) (h4 : orderOf ψ = 4) :
    ∀ N : ℕ, 0 < N →
      ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) * (gaussSum ψ stdAddChar / ((Real.sqrt q : ℝ) : ℂ))) ^ N ≠ 1 := by
  obtain ⟨a, b, hJ, hJc, hab⟩ := jacobi_data χ h3
  obtain ⟨c, d, hK, hKc, hcd⟩ := jacobi_data4 ψ h4
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hnJ := jacobi_norm χ h3
  have hnK := jacobi_norm4 ψ h4
  set J := jacobiSum χ χ
  set K := jacobiSum ψ ψ
  have hJ0 : J ≠ 0 := by intro h; rw [h, zero_mul] at hnJ; exact hp0 hnJ.symm
  have hK0 : K ≠ 0 := by intro h; rw [h, zero_mul] at hnK; exact hq0 hnK.symm
  set zχ := gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)
  set zψ := gaussSum ψ stdAddChar / ((Real.sqrt q : ℝ) : ℂ)
  set s := (ψ * ψ) (-1)
  have hs2 : s ^ 2 = 1 := by simp only [s]; rw [← map_pow, neg_one_sq, map_one]
  have hu : zχ ^ 6 = J ^ 2 / p := z6_eq χ h3
  have hv : zψ ^ 4 = s * K ^ 2 / q := z4_eq ψ h4
  -- u ∈ ℚ(ω)
  have huQ : InQω (zχ ^ 6) := by
    rw [hu, hJ]
    exact ⟨(a ^ 2 - b ^ 2 : ℚ) / p, (2 * a * b - b ^ 2 : ℚ) / p, by
      push_cast; field_simp; linear_combination ((b : ℂ) ^ 2) * ω_sq⟩
  -- v⁻¹ ∈ ℚ(i)
  have hsQ : ∃ σ : ℚ, s = σ := by
    have : (s - 1) * (s + 1) = 0 := by linear_combination hs2
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨1, by push_cast; linear_combination h⟩
    · exact ⟨-1, by push_cast; linear_combination h⟩
  obtain ⟨σ, hσ⟩ := hsQ
  have hσ0 : (σ : ℂ) ≠ 0 := by rw [← hσ]; intro h; rw [h] at hs2; norm_num at hs2
  have hvinv : (zψ ^ 4)⁻¹ = s * ((starRingEnd ℂ) K) ^ 2 / q := by
    have hKbar : (starRingEnd ℂ) K = q / K := by rw [eq_div_iff hK0, mul_comm]; exact hnK
    rw [hv, hKbar, hσ]; field_simp
    have : (σ : ℂ) ^ 2 = 1 := by rw [← hσ]; exact hs2
    linear_combination (-1 : ℂ) * this
  have hviQ : InQi ((zψ ^ 4)⁻¹) := by
    rw [hvinv, hKc, hσ]
    exact ⟨σ * (c ^ 2 - d ^ 2 : ℚ) / q, σ * (-2 * c * d : ℚ) / q, by
      push_cast; field_simp; linear_combination ((d : ℂ) ^ 2) * I_sq⟩
  -- conj u = u⁻¹
  have hubar : (starRingEnd ℂ) (zχ ^ 6) = (zχ ^ 6)⁻¹ := by
    have hJbar : (starRingEnd ℂ) J = p / J := by rw [eq_div_iff hJ0, mul_comm]; exact hnJ
    rw [hu, map_div₀, map_pow, hJbar, map_natCast]; field_simp
  intro N hN hX
  have h12 : (zχ ^ 6) ^ (2 * N) * (zψ ^ 4) ^ (3 * N) = 1 := by
    rw [← pow_mul, ← pow_mul, show 6 * (2 * N) = 12 * N by ring, show 4 * (3 * N) = 12 * N by ring, ← mul_pow,
      mul_comm 12 N, pow_mul, hX, one_pow]
  have heq : (zχ ^ 6) ^ (2 * N) = ((zψ ^ 4)⁻¹) ^ (3 * N) := by
    rw [inv_pow]; exact eq_inv_of_mul_eq_one_left h12
  obtain ⟨r, hr⟩ := inter_rat (InQω_pow huQ _) (heq ▸ InQi_pow hviQ _)
  -- r² = 1
  have hu0 : zχ ^ 6 ≠ 0 := by rw [hu]; exact div_ne_zero (pow_ne_zero 2 hJ0) hp0
  have hrr : (r : ℂ) * r = 1 := by
    have hc := congrArg (starRingEnd ℂ) hr
    rw [map_pow, hubar, map_ratCast, inv_pow, hr] at hc
    have hr0 : (r : ℂ) ≠ 0 := by rw [← hr]; exact pow_ne_zero _ hu0
    calc (r : ℂ) * r = r * (r : ℂ)⁻¹ := by rw [hc]
      _ = 1 := mul_inv_cancel₀ hr0
  have h4N : zχ ^ (6 * (4 * N)) = 1 := by
    rw [pow_mul, show 4 * N = 2 * N * 2 by ring, pow_mul, hr, sq]; exact hrr
  exact gauss_cubic_not_root h3p χ h3 (6 * (4 * N)) (by omega) h4N

end PAG.Part176

#print axioms PAG.Part176.InQω_mul
#print axioms PAG.Part176.InQi_mul
#print axioms PAG.Part176.InQω_pow
#print axioms PAG.Part176.InQi_pow
#print axioms PAG.Part176.inter_rat
#print axioms PAG.Part176.cubic_quartic_not_root
