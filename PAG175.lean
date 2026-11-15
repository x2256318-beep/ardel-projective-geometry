/-
  PAG 2.0 Part 171（2026-10-22）— 導手 p の 4 次の因子 2 つ：異なる素数なら打ち消さない
  p ≠ q は素数、χ_p, χ_q は位数 4、J_p = a + bi、J_q = c + di、ψ = χ²
  1. z4_eq: z⁴ = ψ(−1) J²/p
  2. trace4_identity: w + w̄ = T₄(a, b, c, d)（w = J_p² J_q²）
  3. T4_not_dvd: p ∤ T₄
  4. quartic_pair_not_root: (z_p z_q)^N ≠ 1
-/
import PAG174

namespace PAG.Part175

open Complex Finset PAG.Part171 PAG.Part172
open ZMod (stdAddChar)

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. z⁴ = ψ(−1) J²/p**（位数 4、ψ = χ²）。 -/
theorem z4_eq (χ : DirichletCharacter ℂ p) (h4 : orderOf χ = 4) :
    (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 4 = (χ * χ) (-1) * jacobiSum χ χ ^ 2 / p := by
  have hχ4 : χ ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one χ
  have hψ1 : χ * χ ≠ 1 := by
    intro h
    have : orderOf χ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [h4] at this; norm_num at this
  have hψ2 : (χ * χ) ^ 2 = 1 := by rw [← sq, ← pow_mul]; exact hχ4
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hprψ := primitive_of_ne_one (χ * χ) hψ1
  have hJτ : jacobiSum χ χ = gaussSum χ stdAddChar * gaussSum χ stdAddChar / gaussSum (χ * χ) stdAddChar :=
    jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum (by rw [ZMod.card]; exact hp0) hψ1
      (ZMod.isPrimitive_stdAddChar p)
  have hτψ0 : gaussSum (χ * χ) stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero hprψ
  have hτψ := PAG.Part151.real_gauss_sq (χ * χ) hprψ hψ2
  have hsq : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = p := by
    rw [← ofReal_pow, Real.sq_sqrt (by exact_mod_cast hp.out.pos.le)]; push_cast; ring
  have e1 : gaussSum χ stdAddChar ^ 2 = jacobiSum χ χ * gaussSum (χ * χ) stdAddChar := by
    rw [hJτ]; field_simp
  rw [div_pow, show gaussSum χ stdAddChar ^ 4 = (gaussSum χ stdAddChar ^ 2) ^ 2 by ring, e1, mul_pow, hτψ,
    show (((Real.sqrt p : ℝ) : ℂ)) ^ 4 = ((((Real.sqrt p : ℝ) : ℂ)) ^ 2) ^ 2 by ring, hsq]
  field_simp

/-- T₄ = Tr(J_p² J_q²)。 -/
def T4 (a b c d : ℤ) : ℤ := 2*a^2*c^2 - 2*a^2*d^2 - 8*a*b*c*d - 2*b^2*c^2 + 2*b^2*d^2

/-- **2. w + w̄ = T₄**。 -/
theorem trace4_identity (a b c d : ℤ) :
    ((a : ℂ) + b * I) ^ 2 * ((c : ℂ) + d * I) ^ 2 + ((a : ℂ) - b * I) ^ 2 * ((c : ℂ) - d * I) ^ 2
      = (T4 a b c d : ℂ) := by
  unfold T4; push_cast
  linear_combination (2 * I ^ 2 * (b:ℂ) ^ 2 * d ^ 2 + 2 * a ^ 2 * d ^ 2 + 8 * a * b * c * d + 2 * b ^ 2 * c ^ 2
    - 2 * b ^ 2 * d ^ 2) * I_sq

/-- **3. p ∤ T₄**。 -/
theorem T4_not_dvd {q : ℕ} (hq : q.Prime) (hpq : p ≠ q) (hp5 : 5 ≤ p) (a b c d : ℤ)
    (hab : a ^ 2 + b ^ 2 = p) (hcd : c ^ 2 + d ^ 2 = q) : ¬ (p : ℤ) ∣ T4 a b c d := by
  intro hT
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  set E := b * (c ^ 2 - d ^ 2) + a * (2 * c * d)
  have id1 : T4 a b c d = -4 * b * E + (a ^ 2 + b ^ 2) * (2 * (c ^ 2 - d ^ 2)) := by
    unfold T4; simp only [E]; ring
  have id2 : b ^ 2 * (c ^ 2 + d ^ 2) ^ 2 - (2 * c * d) ^ 2 * (a ^ 2 + b ^ 2)
      = E * (b * (c ^ 2 - d ^ 2) - a * (2 * c * d)) := by simp only [E]; ring
  have hb : ¬ (p : ℤ) ∣ b := by
    intro ⟨k, hk⟩
    have ha : (p : ℤ) ∣ a ^ 2 := ⟨1 - p * k ^ 2, by rw [hk] at hab; linear_combination hab⟩
    obtain ⟨l, hl⟩ := hpi.dvd_of_dvd_pow ha
    have : (p : ℤ) * p ∣ p := ⟨l ^ 2 + k ^ 2, by
      calc (p : ℤ) = a ^ 2 + b ^ 2 := hab.symm
        _ = _ := by rw [hl, hk]; ring⟩
    have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.out.one_lt
    obtain ⟨m, hm⟩ := this
    have : (p : ℤ) * (p * m - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · omega
    · have : (p : ℤ) * m = 1 := by linarith
      have := Int.eq_one_of_mul_eq_one_right (by omega) this
      omega
  have h4 : ¬ (p : ℤ) ∣ 4 := by
    intro h
    have := Int.le_of_dvd (by norm_num) h
    have : (5 : ℤ) ≤ p := by exact_mod_cast hp5
    omega
  have hE : (p : ℤ) ∣ E := by
    have : (p : ℤ) ∣ -4 * b * E := by
      have h' : (p : ℤ) ∣ (a ^ 2 + b ^ 2) * (2 * (c ^ 2 - d ^ 2)) := ⟨2 * (c ^ 2 - d ^ 2), by rw [hab]⟩
      have := dvd_sub hT h'
      rwa [id1, add_sub_cancel_right] at this
    rcases hpi.dvd_or_dvd this with h | h
    · rcases hpi.dvd_or_dvd h with h | h
      · exact absurd (by simpa using h) h4
      · exact absurd h hb
    · exact h
  have hbq : (p : ℤ) ∣ b ^ 2 * (q : ℤ) ^ 2 := by
    have h1 : (p : ℤ) ∣ E * (b * (c ^ 2 - d ^ 2) - a * (2 * c * d)) := dvd_mul_of_dvd_left hE _
    have h2 : (p : ℤ) ∣ (2 * c * d) ^ 2 * (a ^ 2 + b ^ 2) := ⟨(2 * c * d) ^ 2, by rw [hab]; ring⟩
    have := dvd_add h1 h2
    rw [← id2, sub_add_cancel, hcd] at this
    exact this
  rcases hpi.dvd_or_dvd hbq with h | h
  · exact hb (hpi.dvd_of_dvd_pow h)
  · have hq' : (p : ℤ) ∣ q := hpi.dvd_of_dvd_pow h
    have : p ∣ q := by exact_mod_cast hq'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp this)

/-- J = a + bi、conj J = a − bi、a² + b² = p（位数 4）。 -/
theorem jacobi_data4 (χ : DirichletCharacter ℂ p) (h4 : orderOf χ = 4) :
    ∃ a b : ℤ, jacobiSum χ χ = a + b * I ∧ (starRingEnd ℂ) (jacobiSum χ χ) = a - b * I ∧
      a ^ 2 + b ^ 2 = p := by
  have hχ4 : χ ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one χ
  obtain ⟨a, b, hJ⟩ := jacobi_InZi χ hχ4
  have hnorm := jacobi_norm4 χ h4
  have hJc : (starRingEnd ℂ) (jacobiSum χ χ) = a - b * I := by
    rw [hJ, map_add, map_mul, conj_I, map_intCast, map_intCast]; ring
  refine ⟨a, b, hJ, hJc, ?_⟩
  have h : ((a ^ 2 + b ^ 2 : ℤ) : ℂ) = p := by
    rw [← hnorm, hJc, hJ]; push_cast; linear_combination ((b : ℂ) ^ 2) * I_sq
  exact_mod_cast h

theorem p_ge_five (χ : DirichletCharacter ℂ p) (h4 : orderOf χ = 4) : 5 ≤ p := by
  have hd := orderOf_dvd_natCard χ
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime hp.out, h4] at hd
  have := hp.out.two_le
  omega

/-- **4. 異なる素数の 4 次の因子 2 つ：(z_p z_q)^N ≠ 1**。 -/
theorem quartic_pair_not_root {q : ℕ} [hq : Fact q.Prime] (hpq : p ≠ q)
    (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) (h4 : orderOf χ = 4) (h4' : orderOf ψ = 4) :
    ∀ N : ℕ, 0 < N →
      ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) * (gaussSum ψ stdAddChar / ((Real.sqrt q : ℝ) : ℂ))) ^ N ≠ 1 := by
  obtain ⟨a, b, hJ, hJc, hab⟩ := jacobi_data4 χ h4
  obtain ⟨c, d, hK, hKc, hcd⟩ := jacobi_data4 ψ h4'
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hnJ := jacobi_norm4 χ h4
  have hnK := jacobi_norm4 ψ h4'
  set J := jacobiSum χ χ
  set K := jacobiSum ψ ψ
  have hJ0 : J ≠ 0 := by intro h; rw [h, zero_mul] at hnJ; exact hp0 hnJ.symm
  have hK0 : K ≠ 0 := by intro h; rw [h, zero_mul] at hnK; exact hq0 hnK.symm
  -- 符号 s = ψ(−1)
  have hsgn : ∀ {r : ℕ} [Fact r.Prime] (φ : DirichletCharacter ℂ r), ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ (φ * φ) (-1) = σ := by
    intro r _ φ
    have hs2 : ((φ * φ) (-1)) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
    have : ((φ * φ) (-1) - 1) * ((φ * φ) (-1) + 1) = 0 := by linear_combination hs2
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨1, Or.inl rfl, by push_cast; linear_combination h⟩
    · exact ⟨-1, Or.inr rfl, by push_cast; linear_combination h⟩
  obtain ⟨σ, hσ, hsσ⟩ := hsgn χ
  obtain ⟨τ, hτ, hsτ⟩ := hsgn ψ
  have hσ2 : (σ : ℂ) ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hτ2 : (τ : ℂ) ^ 2 = 1 := by rcases hτ with h | h <;> rw [h] <;> norm_num
  have hσ0 : (σ : ℂ) ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hτ0 : (τ : ℂ) ≠ 0 := by rcases hτ with h | h <;> rw [h] <;> norm_num
  set y := (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 4 * (gaussSum ψ stdAddChar / ((Real.sqrt q : ℝ) : ℂ)) ^ 4
  have hy : y = σ * J ^ 2 / p * (τ * K ^ 2 / q) := by simp only [y]; rw [z4_eq χ h4, z4_eq ψ h4', hsσ, hsτ]
  set r : ℚ := (σ * τ * T4 a b c d : ℚ) / (p * q)
  have hr : y + y⁻¹ = (r : ℂ) := by
    have hJbar : (starRingEnd ℂ) J = p / J := by rw [eq_div_iff hJ0, mul_comm]; exact hnJ
    have hKbar : (starRingEnd ℂ) K = q / K := by rw [eq_div_iff hK0, mul_comm]; exact hnK
    have hinv : y⁻¹ = σ * ((starRingEnd ℂ) J) ^ 2 / p * (τ * ((starRingEnd ℂ) K) ^ 2 / q) := by
      rw [hy, hJbar, hKbar]; field_simp
      linear_combination (-(τ : ℂ) ^ 2) * hσ2 - hτ2
    rw [hinv, hy]
    simp only [r]; push_cast
    rw [← trace4_identity a b c d, ← hJ, ← hK, ← hJc, ← hKc]
    field_simp
  have hnot : ∀ n : ℤ, r ≠ n := by
    intro n hn
    have hpq0 : (p : ℚ) * q ≠ 0 := mul_ne_zero (by exact_mod_cast hp.out.ne_zero) (by exact_mod_cast hq.out.ne_zero)
    have h1 : ((σ * τ * T4 a b c d : ℤ) : ℚ) = ((n * q * p : ℤ) : ℚ) := by
      simp only [r] at hn; rw [div_eq_iff hpq0] at hn; push_cast; rw [hn]; ring
    have h2 : σ * τ * T4 a b c d = n * q * p := by exact_mod_cast h1
    have hστ : σ * τ * (σ * τ) = 1 := by rcases hσ with h | h <;> rcases hτ with h' | h' <;> rw [h, h'] <;> norm_num
    exact T4_not_dvd hq.out hpq (p_ge_five χ h4) a b c d hab hcd
      ⟨σ * τ * n * q, by linear_combination (σ * τ) * h2 - T4 a b c d * hστ⟩
  intro N hN hX
  apply not_root_of_trace y r hr hnot N hN
  simp only [y]
  rw [← mul_pow, ← pow_mul, mul_comm 4 N, pow_mul, hX, one_pow]

end PAG.Part175

#print axioms PAG.Part175.z4_eq
#print axioms PAG.Part175.trace4_identity
#print axioms PAG.Part175.T4_not_dvd
#print axioms PAG.Part175.jacobi_data4
#print axioms PAG.Part175.p_ge_five
#print axioms PAG.Part175.quartic_pair_not_root
