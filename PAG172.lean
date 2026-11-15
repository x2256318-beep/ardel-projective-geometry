/-
  PAG 2.0 Part 168（2026-10-22）— 導手 p の場合：4 次の指標のガウス和の位相も 1 の冪根ではない
  p ≡ 1 (mod 4)、χ は位数 4 の指標、z = τ(χ)/√p、J = J(χ, χ)、ψ = χ²（2 次の指標）
  1. J = a + bi（a, b ∈ ℤ）、a² + b² = p
  2. z⁴ = ψ(−1) J²/p、z⁴ + z⁻⁴ = ψ(−1) · 2(a² − b²)/p ∉ ℤ
  3. gauss_quartic_not_root: z^N ≠ 1（N > 0）。ζ = z^{ord χ} は無限位数
  4. exists_quartic: p ≡ 1 (mod 4) なら位数 4 の指標が存在する
-/
import PAG171

namespace PAG.Part172

open Complex Finset Polynomial PAG.Part171
open ZMod (stdAddChar)

theorem quartic_eq_one (u : ℂ) (hu : u ^ 4 = 1) : u = 1 ∨ u = -1 ∨ u = I ∨ u = -I := by
  have h : (u - 1) * (u + 1) * (u - I) * (u + I) = 0 := by
    linear_combination hu - (u ^ 2 - 1) * I_sq
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; linear_combination h
      · right; left; linear_combination h
    · right; right; left; linear_combination h
  · right; right; right; linear_combination h

/-- ℤ[i] の元。 -/
def InZi (y : ℂ) : Prop := ∃ a b : ℤ, y = a + b * I

theorem InZi_add {y y' : ℂ} (h : InZi y) (h' : InZi y') : InZi (y + y') := by
  obtain ⟨a, b, rfl⟩ := h; obtain ⟨a', b', rfl⟩ := h'
  exact ⟨a + a', b + b', by push_cast; ring⟩

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1a. χ⁴ = 1 ⇒ J(χ, χ) ∈ ℤ[i]**。 -/
theorem jacobi_InZi (χ : MulChar (ZMod p) ℂ) (h4 : χ ^ 4 = 1) : InZi (jacobiSum χ χ) := by
  unfold jacobiSum
  apply Finset.sum_induction _ InZi (fun _ _ => InZi_add) ⟨0, 0, by simp⟩
  intro x _
  rw [← map_mul]
  by_cases h0 : x * (1 - x) = 0
  · rw [h0, MulChar.map_zero]; exact ⟨0, 0, by simp⟩
  · have hu : (χ (x * (1 - x))) ^ 4 = 1 := by
      rw [← MulChar.pow_apply' χ (by norm_num), h4, MulChar.one_apply (Ne.isUnit h0)]
    rcases quartic_eq_one _ hu with h | h | h | h
    · exact ⟨1, 0, by rw [h]; simp⟩
    · exact ⟨-1, 0, by rw [h]; simp⟩
    · exact ⟨0, 1, by rw [h]; simp⟩
    · exact ⟨0, -1, by rw [h]; simp⟩

/-- **1b. 位数 4: J · conj J = p**。 -/
theorem jacobi_norm4 (χ : MulChar (ZMod p) ℂ) (h4 : orderOf χ = 4) :
    jacobiSum χ χ * (starRingEnd ℂ) (jacobiSum χ χ) = p := by
  have hne : χ ≠ 1 := by intro h; rw [h, orderOf_one] at h4; norm_num at h4
  have hne2 : χ * χ ≠ 1 := by
    intro h
    have : orderOf χ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [h4] at this; norm_num at this
  have hch : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact hp.out.ne_zero.symm
  rw [conj_jacobi, jacobiSum_mul_jacobiSum_inv hch hne hne hne2, ZMod.card]

/-- **3. 4 次の指標のガウス和の位相は 1 の冪根ではない**（p ≡ 1 (mod 4)）。 -/
theorem gauss_quartic_not_root (χ : DirichletCharacter ℂ p) (h4 : orderOf χ = 4) :
    ∀ N : ℕ, 0 < N → (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ N ≠ 1 := by
  have hχ4 : χ ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one χ
  have hne : χ ≠ 1 := by intro h; rw [h, orderOf_one] at h4; norm_num at h4
  have hp5 : 5 ≤ p := by
    have hd := orderOf_dvd_natCard χ
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime hp.out, h4] at hd
    have := hp.out.two_le
    omega
  set ψ := χ * χ
  have hψ1 : ψ ≠ 1 := by
    intro h
    have : orderOf χ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [h4] at this; norm_num at this
  have hψ2 : ψ ^ 2 = 1 := by simp only [ψ]; rw [← sq, ← pow_mul]; exact hχ4
  obtain ⟨a, b, hJ⟩ := jacobi_InZi χ hχ4
  have hnorm := jacobi_norm4 χ h4
  set J := jacobiSum χ χ
  have hJc : (starRingEnd ℂ) J = a - b * I := by
    rw [hJ, map_add, map_mul, conj_I, map_intCast, map_intCast]; ring
  have hab : (a ^ 2 + b ^ 2 : ℤ) = p := by
    have h : ((a ^ 2 + b ^ 2 : ℤ) : ℂ) = p := by
      rw [← hnorm, hJc, hJ]; push_cast; linear_combination ((b : ℂ) ^ 2) * I_sq
    exact_mod_cast h
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hJ0 : J ≠ 0 := by intro h; rw [h, zero_mul] at hnorm; exact hp0 hnorm.symm
  -- τ(χ)² = J τ(ψ)、τ(ψ)² = ψ(−1) p
  have hpr := primitive_of_ne_one χ hne
  have hprψ := primitive_of_ne_one ψ hψ1
  have hJτ : J = gaussSum χ stdAddChar * gaussSum χ stdAddChar / gaussSum ψ stdAddChar :=
    jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum (by rw [ZMod.card]; exact hp0) hψ1
      (ZMod.isPrimitive_stdAddChar p)
  have hτψ0 : gaussSum ψ stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero hprψ
  have hτψ := PAG.Part151.real_gauss_sq ψ hprψ hψ2
  set s := ψ (-1)
  have hs2 : s ^ 2 = 1 := by simp only [s]; rw [← map_pow, neg_one_sq, map_one]
  set z := gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)
  have hsq : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = p := by
    rw [← ofReal_pow, Real.sq_sqrt (by exact_mod_cast hp.out.pos.le)]; push_cast; ring
  have hz4 : z ^ 4 = s * J ^ 2 / p := by
    have e1 : gaussSum χ stdAddChar ^ 2 = J * gaussSum ψ stdAddChar := by
      rw [hJτ]; field_simp
    simp only [z]
    rw [div_pow, show gaussSum χ stdAddChar ^ 4 = (gaussSum χ stdAddChar ^ 2) ^ 2 by ring, e1, mul_pow, hτψ,
      show (((Real.sqrt p : ℝ) : ℂ)) ^ 4 = ((((Real.sqrt p : ℝ) : ℂ)) ^ 2) ^ 2 by ring, hsq]
    field_simp
  -- s = ±1 を整数で扱う
  obtain ⟨σ, hσ, hsσ⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ s = σ := by
    have : (s - 1) * (s + 1) = 0 := by linear_combination hs2
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨1, Or.inl rfl, by push_cast; linear_combination h⟩
    · exact ⟨-1, Or.inr rfl, by push_cast; linear_combination h⟩
  set t : ℚ := σ * (2 * (a ^ 2 - b ^ 2)) / p
  have ht : z ^ 4 + (z ^ 4)⁻¹ = (t : ℂ) := by
    rw [hz4]
    have hJbar : (starRingEnd ℂ) J = p / J := by rw [eq_div_iff hJ0, mul_comm]; exact hnorm
    have hσ2 : (σ : ℂ) ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    have hinv : (s * J ^ 2 / p)⁻¹ = s * ((starRingEnd ℂ) J) ^ 2 / p := by
      have hσne : (σ : ℂ) ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
      rw [hJbar, hsσ]; field_simp; linear_combination (-1 : ℂ) * hσ2
    rw [hinv]
    simp only [t]; push_cast
    rw [← add_div, div_left_inj' hp0, hJc, hJ, hsσ]
    linear_combination ((2 : ℂ) * σ * b ^ 2) * I_sq
  have hnot : ∀ n : ℤ, t ≠ n := by
    intro n hn
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h1 : ((σ * (2 * (a ^ 2 - b ^ 2)) : ℤ) : ℚ) = (n * p : ℤ) := by
      simp only [t] at hn; field_simp at hn; push_cast; linear_combination hn
    have h2 : σ * (2 * (a ^ 2 - b ^ 2)) = n * (p : ℤ) := by exact_mod_cast h1
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    -- p ∣ 4a²
    have h3 : (p : ℤ) ∣ 4 * a ^ 2 := by
      have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
      refine ⟨σ * n + 2, ?_⟩
      have : 2 * (a ^ 2 - b ^ 2) = σ * n * p := by
        calc 2 * (a ^ 2 - b ^ 2) = σ * σ * (2 * (a ^ 2 - b ^ 2)) := by rw [hσσ, one_mul]
          _ = σ * (n * p) := by rw [← h2]; ring
          _ = σ * n * p := by ring
      linear_combination this + 2 * hab
    have hp2 : ¬ (p : ℤ) ∣ 4 := by
      intro h
      have := Int.le_of_dvd (by norm_num) h
      have h5 : (5 : ℤ) ≤ p := by exact_mod_cast hp5
      omega
    have hda : (p : ℤ) ∣ a := by
      rcases hpi.dvd_or_dvd h3 with h | h
      · exact absurd h hp2
      · exact hpi.dvd_of_dvd_pow h
    obtain ⟨k, hk⟩ := hda
    have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.out.one_lt
    have hk0 : k = 0 := by
      by_contra hk0
      have hk1 : 1 ≤ k ^ 2 := by have := sq_pos_of_ne_zero hk0; omega
      rw [hk] at hab
      have e : ((p : ℤ) * k) ^ 2 = (p : ℤ) ^ 2 * k ^ 2 := by ring
      rw [e] at hab
      have hm : (p : ℤ) ^ 2 * 1 ≤ (p : ℤ) ^ 2 * k ^ 2 := mul_le_mul_of_nonneg_left hk1 (sq_nonneg _)
      nlinarith [sq_nonneg b]
    rw [hk, hk0, mul_zero] at hab
    have hb : (p : ℤ) = b * b := by rw [← hab]; ring
    rcases hpi.irreducible.isUnit_or_isUnit hb with hu | hu <;>
    · rcases Int.isUnit_iff.mp hu with h | h <;> rw [h] at hb <;> norm_num at hb <;> omega
  intro N hN hzN
  apply not_root_of_trace (z ^ 4) t ht hnot N hN
  rw [← pow_mul, mul_comm, pow_mul, hzN, one_pow]

/-- **3'. ζ = z^{ord χ} は無限位数**。 -/
theorem zeta_quartic_infinite (χ : DirichletCharacter ℂ p) (h4 : orderOf χ = 4) :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ orderOf χ) = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn h
  rw [← pow_mul] at h
  exact gauss_quartic_not_root χ h4 _ (Nat.mul_pos (orderOf_pos χ) hn) h

open Classical in
/-- **4. p ≡ 1 (mod 4) なら位数 4 の指標が存在する**。 -/
theorem exists_quartic (h4p : p % 4 = 1) : ∃ χ : DirichletCharacter ℂ p, orderOf χ = 4 := by
  have hcyc : IsCyclic (DirichletCharacter ℂ p) := by
    have : IsCyclic (ZMod p)ˣ := inferInstance
    exact isCyclic_of_surjective (MulChar.equiv_rootsOfUnity (ZMod p) ℂ).symm
      (MulChar.equiv_rootsOfUnity (ZMod p) ℂ).symm.surjective
  have hcard : Fintype.card (DirichletCharacter ℂ p) = p - 1 := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity,
      Nat.totient_prime hp.out]
  have h := IsCyclic.card_orderOf_eq_totient (α := DirichletCharacter ℂ p) (d := 4) (by rw [hcard]; omega)
  have hpos : 0 < #{χ : DirichletCharacter ℂ p | orderOf χ = 4} := by rw [h]; decide
  obtain ⟨χ, hχ⟩ := Finset.card_pos.mp hpos
  exact ⟨χ, (Finset.mem_filter.mp hχ).2⟩

end PAG.Part172

#print axioms PAG.Part172.quartic_eq_one
#print axioms PAG.Part172.jacobi_InZi
#print axioms PAG.Part172.jacobi_norm4
#print axioms PAG.Part172.gauss_quartic_not_root
#print axioms PAG.Part172.zeta_quartic_infinite
#print axioms PAG.Part172.exists_quartic
