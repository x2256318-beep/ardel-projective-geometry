/-
  PAG 2.0 Part 170（2026-10-22）— 導手 p の 3 次の因子 2 つ：異なる素数なら打ち消さない
  p ≠ q は素数で p ≡ q ≡ 1 (mod 3)、χ_p, χ_q は位数 3、z_p, z_q はガウス和の位相
  1. z6_eq: z⁶ = J²/p
  2. trace_identity: J_p = a + bω、J_q = c + dω のとき w + w̄ = T(a, b, c, d)（w = J_p² J_q²）
  3. T_not_dvd: p ∤ T（a² − ab + b² = p、c² − cd + d² = q、p ≠ q）
  4. cubic_pair_not_root: (z_p z_q)^N ≠ 1（N > 0）
  5. not_root_mul: A が 1 の冪根でなく B が 1 の冪根なら AB も 1 の冪根でない
-/
import PAG173

namespace PAG.Part174

open Complex Finset PAG.Part171
open ZMod (stdAddChar)

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. z⁶ = J²/p**（位数 3）。 -/
theorem z6_eq (χ : DirichletCharacter ℂ p) (h3 : orderOf χ = 3) :
    (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 6 = jacobiSum χ χ ^ 2 / p := by
  have hs : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = p := by
    rw [← ofReal_pow, Real.sq_sqrt (by exact_mod_cast hp.out.pos.le)]; push_cast; ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [jacobi_eq_gauss_cube χ h3, div_pow, show (((Real.sqrt p : ℝ) : ℂ)) ^ 6 = ((((Real.sqrt p : ℝ) : ℂ)) ^ 2) ^ 3 by ring,
    hs]
  field_simp

/-- T(a, b, c, d) = Tr(J_p² J_q²)。 -/
def Tpoly (a b c d : ℤ) : ℤ :=
  2*a^2*c^2 - 2*a^2*c*d - a^2*d^2 - 2*a*b*c^2 - 4*a*b*c*d + 4*a*b*d^2 - b^2*c^2 + 4*b^2*c*d - b^2*d^2

/-- **2. w + w̄ = T**。 -/
theorem trace_identity (a b c d : ℤ) :
    ((a : ℂ) + b * ω) ^ 2 * ((c : ℂ) + d * ω) ^ 2 + ((a : ℂ) + b * (-1 - ω)) ^ 2 * ((c : ℂ) + d * (-1 - ω)) ^ 2
      = (Tpoly a b c d : ℂ) := by
  unfold Tpoly; push_cast
  linear_combination (2 * (a:ℂ)^2 * d^2 + 8*a*b*c*d - 6*a*b*d^2 + 2*b^2*c^2 - 6*b^2*c*d + 2*b^2*d^2*ω^2
    + 2*b^2*d^2*ω + 2*b^2*d^2) * ω_sq

/-- **3. p ∤ T**。 -/
theorem T_not_dvd {q : ℕ} (hq : q.Prime) (hpq : p ≠ q) (h3p : p % 3 = 1) (a b c d : ℤ)
    (hab : a ^ 2 - a * b + b ^ 2 = p) (hcd : c ^ 2 - c * d + d ^ 2 = q) : ¬ (p : ℤ) ∣ Tpoly a b c d := by
  intro hT
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  set E := b * (c ^ 2 - d ^ 2) + (a - b) * (2 * c * d - d ^ 2)
  have id1 : Tpoly a b c d = -3 * b * E + (a ^ 2 - a * b + b ^ 2) * (2 * c ^ 2 - 2 * c * d - d ^ 2) := by
    unfold Tpoly; simp only [E]; ring
  have id2 : b ^ 2 * (c ^ 2 - c * d + d ^ 2) ^ 2 - (2 * c * d - d ^ 2) ^ 2 * (a ^ 2 - a * b + b ^ 2)
      = E * (b * c ^ 2 - b * d ^ 2 - 2 * a * c * d + a * d ^ 2) := by simp only [E]; ring
  -- p ∤ b
  have hb : ¬ (p : ℤ) ∣ b := by
    intro ⟨k, hk⟩
    have ha : (p : ℤ) ∣ a ^ 2 := ⟨1 + a * k - p * k ^ 2, by rw [hk] at hab; linear_combination hab⟩
    obtain ⟨l, hl⟩ := hpi.dvd_of_dvd_pow ha
    have : (p : ℤ) * p ∣ p := ⟨l ^ 2 - l * k + k ^ 2, by
      calc (p : ℤ) = a ^ 2 - a * b + b ^ 2 := hab.symm
        _ = _ := by rw [hl, hk]; ring⟩
    have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.out.one_lt
    obtain ⟨m, hm⟩ := this
    have : (p : ℤ) * (p * m - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · omega
    · have : (p : ℤ) * m = 1 := by linarith
      have := Int.eq_one_of_mul_eq_one_right (by omega) this
      omega
  have h3 : ¬ (p : ℤ) ∣ 3 := by
    intro h
    have := Int.le_of_dvd (by norm_num) h
    have h7 : 7 ≤ p := by
      have := hp.out.two_le
      have : p ≠ 4 := by intro h4; subst h4; exact absurd hp.out (by decide)
      omega
    omega
  -- p ∣ E
  have hE : (p : ℤ) ∣ E := by
    have : (p : ℤ) ∣ -3 * b * E := by
      have h' : (p : ℤ) ∣ (a ^ 2 - a * b + b ^ 2) * (2 * c ^ 2 - 2 * c * d - d ^ 2) :=
        ⟨2 * c ^ 2 - 2 * c * d - d ^ 2, by rw [hab]⟩
      have := dvd_sub hT h'
      rwa [id1, add_sub_cancel_right] at this
    rcases hpi.dvd_or_dvd this with h | h
    · rcases hpi.dvd_or_dvd h with h | h
      · exact absurd (by simpa using h) h3
      · exact absurd h hb
    · exact h
  -- p ∣ b² q²
  have hbq : (p : ℤ) ∣ b ^ 2 * (q : ℤ) ^ 2 := by
    have h1 : (p : ℤ) ∣ E * (b * c ^ 2 - b * d ^ 2 - 2 * a * c * d + a * d ^ 2) := dvd_mul_of_dvd_left hE _
    have h2 : (p : ℤ) ∣ (2 * c * d - d ^ 2) ^ 2 * (a ^ 2 - a * b + b ^ 2) := ⟨(2 * c * d - d ^ 2) ^ 2, by rw [hab]; ring⟩
    have := dvd_add h1 h2
    rw [← id2, sub_add_cancel, hcd] at this
    exact this
  rcases hpi.dvd_or_dvd hbq with h | h
  · exact hb (hpi.dvd_of_dvd_pow h)
  · have hq' : (p : ℤ) ∣ q := hpi.dvd_of_dvd_pow h
    have : p ∣ q := by exact_mod_cast hq'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp this)

/-- **5. A が 1 の冪根でなく B が 1 の冪根なら AB も 1 の冪根でない**。 -/
theorem not_root_mul (A B : ℂ) (hA : ∀ N : ℕ, 0 < N → A ^ N ≠ 1) (M : ℕ) (hM : 0 < M) (hB : B ^ M = 1) :
    ∀ N : ℕ, 0 < N → (A * B) ^ N ≠ 1 := by
  intro N hN h
  apply hA (N * M) (Nat.mul_pos hN hM)
  have := congrArg (· ^ M) h
  simp only [one_pow, mul_pow, ← pow_mul, mul_comm N M, pow_mul B M N, hB, one_pow, mul_one] at this
  rwa [mul_comm M N] at this

/-- J = a + bω、conj J = a + b(−1 − ω)、a² − ab + b² = p。 -/
theorem jacobi_data (χ : DirichletCharacter ℂ p) (h3 : orderOf χ = 3) :
    ∃ a b : ℤ, jacobiSum χ χ = a + b * ω ∧ (starRingEnd ℂ) (jacobiSum χ χ) = a + b * (-1 - ω) ∧
      a ^ 2 - a * b + b ^ 2 = p := by
  have hχ3 : χ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one χ
  obtain ⟨a, b, hJ⟩ := jacobi_InZω χ hχ3
  have hnorm := jacobi_norm χ h3
  have hJc : (starRingEnd ℂ) (jacobiSum χ χ) = a + b * (-1 - ω) := by
    rw [hJ, map_add, map_mul, conj_ω, map_intCast, map_intCast]
  refine ⟨a, b, hJ, hJc, ?_⟩
  have h : ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℂ) = p := by
    rw [← hnorm, hJc, hJ]; push_cast; linear_combination ((b : ℂ) ^ 2) * ω_sq
  exact_mod_cast h

/-- **4. 異なる素数の 3 次の因子 2 つ：(z_p z_q)^N ≠ 1**。 -/
theorem cubic_pair_not_root {q : ℕ} [hq : Fact q.Prime] (hpq : p ≠ q) (h3p : p % 3 = 1)
    (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) (h3 : orderOf χ = 3) (h3' : orderOf ψ = 3) :
    ∀ N : ℕ, 0 < N →
      ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) * (gaussSum ψ stdAddChar / ((Real.sqrt q : ℝ) : ℂ))) ^ N ≠ 1 := by
  obtain ⟨a, b, hJ, hJc, hab⟩ := jacobi_data χ h3
  obtain ⟨c, d, hK, hKc, hcd⟩ := jacobi_data ψ h3'
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hnJ := jacobi_norm χ h3
  have hnK := jacobi_norm ψ h3'
  set J := jacobiSum χ χ
  set K := jacobiSum ψ ψ
  have hJ0 : J ≠ 0 := by intro h; rw [h, zero_mul] at hnJ; exact hp0 hnJ.symm
  have hK0 : K ≠ 0 := by intro h; rw [h, zero_mul] at hnK; exact hq0 hnK.symm
  set y := (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 6 * (gaussSum ψ stdAddChar / ((Real.sqrt q : ℝ) : ℂ)) ^ 6
  have hy : y = J ^ 2 / p * (K ^ 2 / q) := by simp only [y]; rw [z6_eq χ h3, z6_eq ψ h3']
  set r : ℚ := (Tpoly a b c d : ℚ) / (p * q)
  have hr : y + y⁻¹ = (r : ℂ) := by
    have hJbar : (starRingEnd ℂ) J = p / J := by rw [eq_div_iff hJ0, mul_comm]; exact hnJ
    have hKbar : (starRingEnd ℂ) K = q / K := by rw [eq_div_iff hK0, mul_comm]; exact hnK
    have hinv : y⁻¹ = ((starRingEnd ℂ) J) ^ 2 / p * (((starRingEnd ℂ) K) ^ 2 / q) := by
      rw [hy, hJbar, hKbar]; field_simp
    rw [hinv, hy]
    simp only [r]; push_cast
    rw [← trace_identity a b c d, ← hJ, ← hK, ← hJc, ← hKc]
    field_simp
  have hnot : ∀ n : ℤ, r ≠ n := by
    intro n hn
    have hpq0 : (p : ℚ) * q ≠ 0 := mul_ne_zero (by exact_mod_cast hp.out.ne_zero) (by exact_mod_cast hq.out.ne_zero)
    have h1 : ((Tpoly a b c d : ℤ) : ℚ) = ((n * q * p : ℤ) : ℚ) := by
      simp only [r] at hn; rw [div_eq_iff hpq0] at hn; rw [hn]; push_cast; ring
    have h2 : Tpoly a b c d = n * q * p := by exact_mod_cast h1
    exact T_not_dvd hq.out hpq h3p a b c d hab hcd ⟨n * q, by rw [h2]; ring⟩
  intro N hN hX
  apply not_root_of_trace y r hr hnot N hN
  simp only [y]
  rw [← mul_pow, ← pow_mul, mul_comm 6 N, pow_mul, hX, one_pow]

end PAG.Part174

#print axioms PAG.Part174.z6_eq
#print axioms PAG.Part174.trace_identity
#print axioms PAG.Part174.T_not_dvd
#print axioms PAG.Part174.not_root_mul
#print axioms PAG.Part174.jacobi_data
#print axioms PAG.Part174.cubic_pair_not_root
