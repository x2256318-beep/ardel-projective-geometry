/-
  PAG 2.0 Part 174（2026-10-22）— 導手 p の 4 次の因子をいくつ掛けても（素数が相異なれば）打ち消さない
  1. Tlin4(a, b, C, D) = Tr((a + bi)²(C + Di))、p ∤ C² + D² なら p ∤ Tlin4
  2. prod_repr4: ℤ[i] の元の積の表示とノルムの乗法性
  3. quartic_multi_not_root: 相異なる素数の 4 次の指標 χ_i（n ≥ 1 個）について (∏ z_i)^N ≠ 1
-/
import PAG177

namespace PAG.Part178

open Complex Finset PAG.Part171 PAG.Part172 PAG.Part175
open ZMod (stdAddChar)

/-- Tlin4 = Tr((a + bi)²(C + Di))。 -/
def Tlin4 (a b C D : ℤ) : ℤ := 2 * ((a ^ 2 - b ^ 2) * C - 2 * a * b * D)

theorem trace_lin4 (a b C D : ℤ) :
    ((a : ℂ) + b * I) ^ 2 * ((C : ℂ) + D * I) + ((a : ℂ) - b * I) ^ 2 * ((C : ℂ) - D * I) = (Tlin4 a b C D : ℂ) := by
  unfold Tlin4; push_cast
  linear_combination (2 * (C : ℂ) * b ^ 2 + 4 * D * a * b) * I_sq

/-- **1. p ∤ Tlin4**。 -/
theorem Tlin4_not_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a b C D : ℤ)
    (hab : a ^ 2 + b ^ 2 = p) (hCD : ¬ (p : ℤ) ∣ C ^ 2 + D ^ 2) : ¬ (p : ℤ) ∣ Tlin4 a b C D := by
  intro hT
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set E := b * C + a * D
  have id1 : Tlin4 a b C D = -4 * b * E + (a ^ 2 + b ^ 2) * (2 * C) := by unfold Tlin4; simp only [E]; ring
  have id2 : b ^ 2 * (C ^ 2 + D ^ 2) - D ^ 2 * (a ^ 2 + b ^ 2) = E * (b * C - a * D) := by simp only [E]; ring
  have hb : ¬ (p : ℤ) ∣ b := by
    intro ⟨k, hk⟩
    have ha : (p : ℤ) ∣ a ^ 2 := ⟨1 - p * k ^ 2, by rw [hk] at hab; linear_combination hab⟩
    obtain ⟨l, hl⟩ := hpi.dvd_of_dvd_pow ha
    have : (p : ℤ) * p ∣ p := ⟨l ^ 2 + k ^ 2, by
      calc (p : ℤ) = a ^ 2 + b ^ 2 := hab.symm
        _ = _ := by rw [hl, hk]; ring⟩
    have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
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
      have h' : (p : ℤ) ∣ (a ^ 2 + b ^ 2) * (2 * C) := ⟨2 * C, by rw [hab]⟩
      have := dvd_sub hT h'
      rwa [id1, add_sub_cancel_right] at this
    rcases hpi.dvd_or_dvd this with h | h
    · rcases hpi.dvd_or_dvd h with h | h
      · exact absurd (by simpa using h) h4
      · exact absurd h hb
    · exact h
  have hbN : (p : ℤ) ∣ b ^ 2 * (C ^ 2 + D ^ 2) := by
    have h1 : (p : ℤ) ∣ E * (b * C - a * D) := dvd_mul_of_dvd_left hE _
    have h2 : (p : ℤ) ∣ D ^ 2 * (a ^ 2 + b ^ 2) := ⟨D ^ 2, by rw [hab]; ring⟩
    have := dvd_add h1 h2
    rwa [← id2, sub_add_cancel] at this
  rcases hpi.dvd_or_dvd hbN with h | h
  · exact hb (hpi.dvd_of_dvd_pow h)
  · exact hCD h

/-- **2. ℤ[i] の元の積の表示とノルムの乗法性**。 -/
theorem prod_repr4 {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) (c d m : ι → ℤ)
    (hf : ∀ i ∈ s, f i = c i + d i * I) (hm : ∀ i ∈ s, c i ^ 2 + d i ^ 2 = m i) :
    ∃ C D : ℤ, ∏ i ∈ s, f i = C + D * I ∧ C ^ 2 + D ^ 2 = ∏ i ∈ s, m i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, 0, by simp, by simp⟩
  | insert j s hj ih =>
    obtain ⟨C, D, h1, h2⟩ := ih (fun i hi => hf i (by simp [hi])) (fun i hi => hm i (by simp [hi]))
    refine ⟨c j * C - d j * D, c j * D + d j * C, ?_, ?_⟩
    · rw [Finset.prod_insert hj, h1, hf j (by simp)]; push_cast
      linear_combination ((d j : ℂ) * D) * I_sq
    · rw [Finset.prod_insert hj, ← h2, ← hm j (by simp)]; ring

/-- 符号 ψ(−1) は ±1 の整数。 -/
theorem sign_int {q : ℕ} [Fact q.Prime] (φ : DirichletCharacter ℂ q) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ (φ * φ) (-1) = σ := by
  have hs2 : ((φ * φ) (-1)) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have : ((φ * φ) (-1) - 1) * ((φ * φ) (-1) + 1) = 0 := by linear_combination hs2
  rcases mul_eq_zero.mp this with h | h
  · exact ⟨1, Or.inl rfl, by push_cast; linear_combination h⟩
  · exact ⟨-1, Or.inr rfl, by push_cast; linear_combination h⟩

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime]

/-- **3. 相異なる素数の 4 次の因子の積は 1 の冪根でない**。 -/
theorem quartic_multi_not_root (hn : 0 < n) (hinj : Function.Injective p)
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (h4 : ∀ i, orderOf (χ i) = 4) :
    ∀ N : ℕ, 0 < N → (∏ i, gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ N ≠ 1 := by
  choose a b hJ hJc hab using fun i => jacobi_data4 (χ i) (h4 i)
  choose σ hσ hsσ using fun i => sign_int (χ i)
  let i₀ : Fin n := ⟨0, hn⟩
  have hp0 : ∀ i, (p i : ℂ) ≠ 0 := fun i => by exact_mod_cast (hp i).out.ne_zero
  have hnJ : ∀ i, jacobiSum (χ i) (χ i) * (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) = p i :=
    fun i => jacobi_norm4 (χ i) (h4 i)
  have hJ0 : ∀ i, jacobiSum (χ i) (χ i) ≠ 0 := fun i h => by
    have := hnJ i; rw [h, zero_mul] at this; exact hp0 i this.symm
  have hσ2 : ∀ i, (σ i : ℂ) ^ 2 = 1 := fun i => by rcases hσ i with h | h <;> rw [h] <;> norm_num
  have hσ0 : ∀ i, (σ i : ℂ) ≠ 0 := fun i => by rcases hσ i with h | h <;> rw [h] <;> norm_num
  obtain ⟨C, D, hW, hWn⟩ := prod_repr4 (univ.erase i₀) (fun i => jacobiSum (χ i) (χ i) ^ 2)
    (fun i => a i ^ 2 - b i ^ 2) (fun i => 2 * a i * b i) (fun i => (p i : ℤ) ^ 2)
    (fun i _ => by rw [hJ i]; push_cast; linear_combination ((b i : ℂ) ^ 2) * I_sq)
    (fun i _ => by rw [← hab i]; ring)
  have hWc : ∏ i ∈ univ.erase i₀, (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) ^ 2 = C - D * I := by
    have := congrArg (starRingEnd ℂ) hW
    rw [map_prod] at this
    simp only [map_pow] at this
    rw [this, map_add, map_mul, conj_I, map_intCast, map_intCast]; ring
  have hCD : ¬ (p i₀ : ℤ) ∣ C ^ 2 + D ^ 2 := by
    rw [hWn]
    intro h
    obtain ⟨j, hj, hdj⟩ := (Nat.prime_iff_prime_int.mp (hp i₀).out).exists_mem_finset_dvd h
    have hd : (p i₀ : ℤ) ∣ p j := (Nat.prime_iff_prime_int.mp (hp i₀).out).dvd_of_dvd_pow hdj
    have : p i₀ ∣ p j := by exact_mod_cast hd
    have := (Nat.prime_dvd_prime_iff_eq (hp i₀).out (hp j).out).mp this
    exact Finset.ne_of_mem_erase hj (hinj this).symm
  set S : ℤ := ∏ i, σ i
  have hS : S = 1 ∨ S = -1 := by
    simp only [S]
    induction (univ : Finset (Fin n)) using Finset.induction_on with
    | empty => left; simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj]
      rcases hσ j with h | h <;> rcases ih with h' | h' <;> rw [h, h'] <;> norm_num
  have hY : ∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 4
      = S * (jacobiSum (χ i₀) (χ i₀) ^ 2 * ∏ i ∈ univ.erase i₀, jacobiSum (χ i) (χ i) ^ 2) / ∏ i, (p i : ℂ) := by
    rw [Finset.prod_congr rfl (fun i _ => z4_eq (χ i) (h4 i))]
    simp only [hsσ, S]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.mul_prod_erase univ (fun i => jacobiSum (χ i) (χ i) ^ 2) (mem_univ i₀)]
    push_cast; ring
  have hYinv : (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 4)⁻¹
      = S * ((starRingEnd ℂ) (jacobiSum (χ i₀) (χ i₀)) ^ 2
          * ∏ i ∈ univ.erase i₀, (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) ^ 2) / ∏ i, (p i : ℂ) := by
    rw [Finset.prod_congr rfl (fun i _ => z4_eq (χ i) (h4 i)), ← Finset.prod_inv_distrib,
      Finset.mul_prod_erase univ (fun i => (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) ^ 2) (mem_univ i₀)]
    simp only [S]; push_cast
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hJbar : (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) = p i / jacobiSum (χ i) (χ i) := by
      rw [eq_div_iff (hJ0 i), mul_comm]; exact hnJ i
    rw [hJbar, hsσ i]; field_simp [hJ0 i, hp0 i, hσ0 i]
    linear_combination (-1 : ℂ) * hσ2 i
  set r : ℚ := (S * Tlin4 (a i₀) (b i₀) C D : ℚ) / (∏ i, p i : ℕ)
  have hr : (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 4)
      + (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 4)⁻¹ = (r : ℂ) := by
    rw [hYinv, hY, hWc, hW, hJc i₀, hJ i₀, ← add_div]
    simp only [r]; push_cast
    rw [← trace_lin4]; ring
  have hnot : ∀ m : ℤ, r ≠ m := by
    intro m hm
    have hPrQ : ((∏ i, p i : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show (∏ i, p i) ≠ 0 from Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).out.ne_zero))
    have h1 : ((S * Tlin4 (a i₀) (b i₀) C D : ℤ) : ℚ) = ((m * (∏ i, p i : ℕ) : ℤ) : ℚ) := by
      simp only [r] at hm; rw [div_eq_iff hPrQ] at hm; push_cast at hm ⊢; exact hm
    have h2 : S * Tlin4 (a i₀) (b i₀) C D = m * (∏ i, p i : ℕ) := by exact_mod_cast h1
    have hSS : S * S = 1 := by rcases hS with h | h <;> rw [h] <;> norm_num
    apply Tlin4_not_dvd (hp i₀).out (p_ge_five (χ i₀) (h4 i₀)) _ _ C D (hab i₀) hCD
    have h3 : Tlin4 (a i₀) (b i₀) C D = S * (m * (∏ i, p i : ℕ)) := by
      rw [← h2, ← mul_assoc, hSS, one_mul]
    rw [h3]
    have : (p i₀ : ℤ) ∣ ((∏ i, p i : ℕ) : ℤ) := by
      exact_mod_cast (Finset.dvd_prod_of_mem p (mem_univ i₀))
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right this m) S
  intro N hN hX
  apply not_root_of_trace _ r hr hnot N hN
  rw [Finset.prod_pow, ← pow_mul, mul_comm 4 N, pow_mul, hX, one_pow]

end PAG.Part178

#print axioms PAG.Part178.trace_lin4
#print axioms PAG.Part178.Tlin4_not_dvd
#print axioms PAG.Part178.prod_repr4
#print axioms PAG.Part178.sign_int
#print axioms PAG.Part178.quartic_multi_not_root
