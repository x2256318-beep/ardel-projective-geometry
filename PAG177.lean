/-
  PAG 2.0 Part 173（2026-10-22）— 導手 p の 3 次の因子をいくつ掛けても（素数が相異なれば）打ち消さない
  1. Tlin(a, b, C, D) = Tr((a + bω)²(C + Dω))、p ∤ C² − CD + D² なら p ∤ Tlin
  2. prod_repr: ℤ[ω] の元の積の表示とノルムの乗法性
  3. cubic_multi_not_root: 相異なる素数 p_i ≡ 1 (mod 3) の 3 次の指標 χ_i（n ≥ 1 個）について (∏ z_i)^N ≠ 1
-/
import PAG176

namespace PAG.Part177

open Complex Finset PAG.Part171 PAG.Part174
open ZMod (stdAddChar)

/-- Tlin = Tr((a + bω)²(C + Dω))。 -/
def Tlin (a b C D : ℤ) : ℤ := 2*C*a^2 - 2*C*a*b - C*b^2 - D*a^2 - 2*D*a*b + 2*D*b^2

theorem trace_lin (a b C D : ℤ) :
    ((a : ℂ) + b * ω) ^ 2 * ((C : ℂ) + D * ω) + ((a : ℂ) + b * (-1 - ω)) ^ 2 * ((C : ℂ) + D * (-1 - ω))
      = (Tlin a b C D : ℂ) := by
  unfold Tlin; push_cast
  linear_combination (2 * (C : ℂ) * b ^ 2 + 4 * D * a * b - 3 * D * b ^ 2) * ω_sq

/-- **1. p ∤ Tlin**。 -/
theorem Tlin_not_dvd {p : ℕ} (hp : p.Prime) (h3p : p % 3 = 1) (a b C D : ℤ)
    (hab : a ^ 2 - a * b + b ^ 2 = p) (hCD : ¬ (p : ℤ) ∣ C ^ 2 - C * D + D ^ 2) : ¬ (p : ℤ) ∣ Tlin a b C D := by
  intro hT
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set E := b * C + (a - b) * D
  have id1 : Tlin a b C D = -3 * b * E + (a ^ 2 - a * b + b ^ 2) * (2 * C - D) := by
    unfold Tlin; simp only [E]; ring
  have id2 : b ^ 2 * (C ^ 2 - C * D + D ^ 2) - D ^ 2 * (a ^ 2 - a * b + b ^ 2) = E * (b * C - a * D) := by
    simp only [E]; ring
  have hb : ¬ (p : ℤ) ∣ b := by
    intro ⟨k, hk⟩
    have ha : (p : ℤ) ∣ a ^ 2 := ⟨1 + a * k - p * k ^ 2, by rw [hk] at hab; linear_combination hab⟩
    obtain ⟨l, hl⟩ := hpi.dvd_of_dvd_pow ha
    have : (p : ℤ) * p ∣ p := ⟨l ^ 2 - l * k + k ^ 2, by
      calc (p : ℤ) = a ^ 2 - a * b + b ^ 2 := hab.symm
        _ = _ := by rw [hl, hk]; ring⟩
    have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
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
      have := hp.two_le
      have : p ≠ 4 := by intro h4; subst h4; exact absurd hp (by decide)
      omega
    omega
  have hE : (p : ℤ) ∣ E := by
    have : (p : ℤ) ∣ -3 * b * E := by
      have h' : (p : ℤ) ∣ (a ^ 2 - a * b + b ^ 2) * (2 * C - D) := ⟨2 * C - D, by rw [hab]⟩
      have := dvd_sub hT h'
      rwa [id1, add_sub_cancel_right] at this
    rcases hpi.dvd_or_dvd this with h | h
    · rcases hpi.dvd_or_dvd h with h | h
      · exact absurd (by simpa using h) h3
      · exact absurd h hb
    · exact h
  have hbN : (p : ℤ) ∣ b ^ 2 * (C ^ 2 - C * D + D ^ 2) := by
    have h1 : (p : ℤ) ∣ E * (b * C - a * D) := dvd_mul_of_dvd_left hE _
    have h2 : (p : ℤ) ∣ D ^ 2 * (a ^ 2 - a * b + b ^ 2) := ⟨D ^ 2, by rw [hab]; ring⟩
    have := dvd_add h1 h2
    rwa [← id2, sub_add_cancel] at this
  rcases hpi.dvd_or_dvd hbN with h | h
  · exact hb (hpi.dvd_of_dvd_pow h)
  · exact hCD h

/-- **2. ℤ[ω] の元の積の表示とノルムの乗法性**。 -/
theorem prod_repr {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) (c d m : ι → ℤ)
    (hf : ∀ i ∈ s, f i = c i + d i * ω) (hm : ∀ i ∈ s, c i ^ 2 - c i * d i + d i ^ 2 = m i) :
    ∃ C D : ℤ, ∏ i ∈ s, f i = C + D * ω ∧ C ^ 2 - C * D + D ^ 2 = ∏ i ∈ s, m i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, 0, by simp, by simp⟩
  | insert j s hj ih =>
    obtain ⟨C, D, h1, h2⟩ := ih (fun i hi => hf i (by simp [hi])) (fun i hi => hm i (by simp [hi]))
    refine ⟨c j * C - d j * D, c j * D + d j * C - d j * D, ?_, ?_⟩
    · rw [Finset.prod_insert hj, h1, hf j (by simp)]; push_cast
      linear_combination ((d j : ℂ) * D) * ω_sq
    · rw [Finset.prod_insert hj, ← h2, ← hm j (by simp)]; ring

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime]

/-- **3. 相異なる素数の 3 次の因子の積は 1 の冪根でない**。 -/
theorem cubic_multi_not_root (hn : 0 < n) (hinj : Function.Injective p) (h3p : ∀ i, p i % 3 = 1)
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (h3 : ∀ i, orderOf (χ i) = 3) :
    ∀ N : ℕ, 0 < N → (∏ i, gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ N ≠ 1 := by
  choose a b hJ hJc hab using fun i => jacobi_data (χ i) (h3 i)
  let i₀ : Fin n := ⟨0, hn⟩
  have hp0 : ∀ i, (p i : ℂ) ≠ 0 := fun i => by exact_mod_cast (hp i).out.ne_zero
  have hnJ : ∀ i, jacobiSum (χ i) (χ i) * (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) = p i :=
    fun i => jacobi_norm (χ i) (h3 i)
  have hJ0 : ∀ i, jacobiSum (χ i) (χ i) ≠ 0 := fun i h => by
    have := hnJ i; rw [h, zero_mul] at this; exact hp0 i this.symm
  -- W = ∏_{i ≠ i₀} J_i²
  obtain ⟨C, D, hW, hWn⟩ := prod_repr (univ.erase i₀) (fun i => jacobiSum (χ i) (χ i) ^ 2)
    (fun i => a i ^ 2 - b i ^ 2) (fun i => 2 * a i * b i - b i ^ 2) (fun i => (p i : ℤ) ^ 2)
    (fun i _ => by rw [hJ i]; push_cast; linear_combination ((b i : ℂ) ^ 2) * ω_sq)
    (fun i _ => by rw [← hab i]; ring)
  have hWc : ∏ i ∈ univ.erase i₀, (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) ^ 2 = C + D * (-1 - ω) := by
    have := congrArg (starRingEnd ℂ) hW
    rw [map_prod] at this
    simp only [map_pow] at this
    rw [this, map_add, map_mul, conj_ω, map_intCast, map_intCast]
  have hCD : ¬ (p i₀ : ℤ) ∣ C ^ 2 - C * D + D ^ 2 := by
    rw [hWn]
    intro h
    obtain ⟨j, hj, hdj⟩ := (Nat.prime_iff_prime_int.mp (hp i₀).out).exists_mem_finset_dvd h
    have hd : (p i₀ : ℤ) ∣ p j := (Nat.prime_iff_prime_int.mp (hp i₀).out).dvd_of_dvd_pow hdj
    have : p i₀ ∣ p j := by exact_mod_cast hd
    have := (Nat.prime_dvd_prime_iff_eq (hp i₀).out (hp j).out).mp this
    exact Finset.ne_of_mem_erase hj (hinj this).symm
  have hPr : ((∏ i, p i : ℕ) : ℂ) = ∏ i, (p i : ℂ) := by push_cast; rfl
  have hPr0 : (∏ i, (p i : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i)
  -- Y = ∏ J_i²/p_i
  have hY : ∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 6
      = (jacobiSum (χ i₀) (χ i₀) ^ 2 * ∏ i ∈ univ.erase i₀, jacobiSum (χ i) (χ i) ^ 2) / ∏ i, (p i : ℂ) := by
    rw [Finset.prod_congr rfl (fun i _ => z6_eq (χ i) (h3 i)), Finset.prod_div_distrib,
      Finset.mul_prod_erase univ (fun i => jacobiSum (χ i) (χ i) ^ 2) (mem_univ i₀)]
  have hYinv : (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 6)⁻¹
      = ((starRingEnd ℂ) (jacobiSum (χ i₀) (χ i₀)) ^ 2
          * ∏ i ∈ univ.erase i₀, (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) ^ 2) / ∏ i, (p i : ℂ) := by
    rw [Finset.prod_congr rfl (fun i _ => z6_eq (χ i) (h3 i)), ← Finset.prod_inv_distrib,
      Finset.mul_prod_erase univ (fun i => (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) ^ 2) (mem_univ i₀),
      ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hJbar : (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) = p i / jacobiSum (χ i) (χ i) := by
      rw [eq_div_iff (hJ0 i), mul_comm]; exact hnJ i
    rw [hJbar]; field_simp [hJ0 i, hp0 i]
  set r : ℚ := (Tlin (a i₀) (b i₀) C D : ℚ) / (∏ i, p i : ℕ)
  have hr : (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 6)
      + (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 6)⁻¹ = (r : ℂ) := by
    rw [hYinv, hY, hWc, hW, hJc i₀, hJ i₀, ← add_div]
    simp only [r]; push_cast
    rw [← trace_lin]
  have hnot : ∀ m : ℤ, r ≠ m := by
    intro m hm
    have hPrQ : ((∏ i, p i : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show (∏ i, p i) ≠ 0 from Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).out.ne_zero))
    have h1 : ((Tlin (a i₀) (b i₀) C D : ℤ) : ℚ) = ((m * (∏ i, p i : ℕ) : ℤ) : ℚ) := by
      simp only [r] at hm; rw [div_eq_iff hPrQ] at hm; push_cast at hm ⊢; exact hm
    have h2 : Tlin (a i₀) (b i₀) C D = m * (∏ i, p i : ℕ) := by exact_mod_cast h1
    apply Tlin_not_dvd (hp i₀).out (h3p i₀) _ _ C D (hab i₀) hCD
    rw [h2]
    have : (p i₀ : ℤ) ∣ ((∏ i, p i : ℕ) : ℤ) := by
      exact_mod_cast (Finset.dvd_prod_of_mem p (mem_univ i₀))
    exact dvd_mul_of_dvd_right this m
  intro N hN hX
  apply not_root_of_trace _ r hr hnot N hN
  rw [Finset.prod_pow, ← pow_mul, mul_comm 6 N, pow_mul, hX, one_pow]

end PAG.Part177

#print axioms PAG.Part177.trace_lin
#print axioms PAG.Part177.Tlin_not_dvd
#print axioms PAG.Part177.prod_repr
#print axioms PAG.Part177.cubic_multi_not_root
