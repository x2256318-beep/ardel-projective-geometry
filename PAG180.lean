/-
  PAG 2.0 Part 176（2026-10-22）— 3 次の因子の整数冪の積：素数ごとの冪の和が 0 でない素数があれば 1 の冪根でない
  1. Rep2: w = C + Dω と、ℤ[ω] → ℤ/P の二つの準同型（ω ↦ μ、ω ↦ −1 − μ）での値の組
  2. 積・冪で閉じる
  3. cubic_zpow_not_root: 相異なる素数 p_i の 3 次の指標 χ_i、整数 k_i、k_{i₀} ≠ 0 ⇒ ∏ z_i^{k_i} は 1 の冪根でない
-/
import PAG179

namespace PAG.Part180

open Complex Finset PAG.Part171 PAG.Part174 PAG.Part177 PAG.Part179
open ZMod (stdAddChar)

variable {P : ℕ} (μ : ZMod P)

/-- w = C + Dω で、ev_μ = C + Dμ、ev'_μ = C + D(−1 − μ)。 -/
def Rep2 (w : ℂ) (e e' : ZMod P) : Prop :=
  ∃ C D : ℤ, w = C + D * ω ∧ ((C : ZMod P) + D * μ = e) ∧ ((C : ZMod P) + D * (-1 - μ) = e')

variable {μ}

theorem Rep2_one : Rep2 μ 1 1 1 := ⟨1, 0, by simp, by simp, by simp⟩

theorem Rep2_mul (hμ : μ ^ 2 + μ + 1 = 0) {w w' : ℂ} {e f e' f' : ZMod P}
    (h : Rep2 μ w e e') (h' : Rep2 μ w' f f') : Rep2 μ (w * w') (e * f) (e' * f') := by
  obtain ⟨C, D, rfl, rfl, rfl⟩ := h
  obtain ⟨C', D', rfl, rfl, rfl⟩ := h'
  refine ⟨C * C' - D * D', C * D' + D * C' - D * D', ?_, ?_, ?_⟩
  · push_cast; linear_combination ((D : ℂ) * D') * ω_sq
  · push_cast; linear_combination (-(D : ZMod P) * D') * hμ
  · push_cast; linear_combination (-(D : ZMod P) * D') * hμ

theorem Rep2_pow (hμ : μ ^ 2 + μ + 1 = 0) {w : ℂ} {e e' : ZMod P} (h : Rep2 μ w e e') :
    ∀ m : ℕ, Rep2 μ (w ^ m) (e ^ m) (e' ^ m)
  | 0 => by simpa using Rep2_one
  | m + 1 => by rw [pow_succ, pow_succ, pow_succ]; exact Rep2_mul hμ (Rep2_pow hμ h m) h

theorem Rep2_prod (hμ : μ ^ 2 + μ + 1 = 0) {ι : Type*} (s : Finset ι) (w : ι → ℂ) (e e' : ι → ZMod P)
    (h : ∀ i ∈ s, Rep2 μ (w i) (e i) (e' i)) : Rep2 μ (∏ i ∈ s, w i) (∏ i ∈ s, e i) (∏ i ∈ s, e' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rep2_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj]
    exact Rep2_mul hμ (h j (by simp)) (ih (fun i hi => h i (by simp [hi])))

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime]

theorem zpow_nonneg' (x : ℂ) (k : ℤ) (hk : 0 ≤ k) : x ^ k = x ^ k.natAbs := by
  rw [← zpow_natCast, Int.natAbs_of_nonneg hk]

theorem zpow_neg' (x : ℂ) (k : ℤ) (hk : k < 0) : x ^ k = (x ^ k.natAbs)⁻¹ := by
  rw [← zpow_natCast, ← zpow_neg, Int.ofNat_natAbs_of_nonpos hk.le, neg_neg]

theorem zpow_six_comm (z : ℂ) (k : ℤ) : (z ^ k) ^ 6 = (z ^ 6) ^ k := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

/-- **3. 3 次の因子の整数冪の積**。 -/
theorem cubic_zpow_not_root (hinj : Function.Injective p) (h3p : ∀ i, p i % 3 = 1)
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (h3 : ∀ i, orderOf (χ i) = 3) (k : Fin n → ℤ) (i₀ : Fin n)
    (hk : k i₀ ≠ 0) :
    ∀ N : ℕ, 0 < N → (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ k i) ^ N ≠ 1 := by
  classical
  choose a b hJ hJc hab using fun i => jacobi_data (χ i) (h3 i)
  have hp0 : ∀ i, (p i : ℂ) ≠ 0 := fun i => by exact_mod_cast (hp i).out.ne_zero
  have hnJ : ∀ i, jacobiSum (χ i) (χ i) * (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) = p i :=
    fun i => jacobi_norm (χ i) (h3 i)
  have hJ0 : ∀ i, jacobiSum (χ i) (χ i) ≠ 0 := fun i h => by
    have := hnJ i; rw [h, zero_mul] at this; exact hp0 i this.symm
  have hJbar : ∀ i, (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) = p i / jacobiSum (χ i) (χ i) := fun i => by
    rw [eq_div_iff (hJ0 i), mul_comm]; exact hnJ i
  -- g_i と表示
  set K : Fin n → ℕ := fun i => (k i).natAbs
  set g : Fin n → ℂ := fun i =>
    if 0 ≤ k i then jacobiSum (χ i) (χ i) else (starRingEnd ℂ) (jacobiSum (χ i) (χ i))
  set gc : Fin n → ℤ := fun i => if 0 ≤ k i then a i else a i - b i
  set gd : Fin n → ℤ := fun i => if 0 ≤ k i then b i else -b i
  have hg : ∀ i, g i = gc i + gd i * ω := by
    intro i; simp only [g, gc, gd]
    split_ifs
    · exact hJ i
    · rw [hJc i]; push_cast; ring
  have hgn : ∀ i, gc i ^ 2 - gc i * gd i + gd i ^ 2 = p i := by
    intro i; simp only [gc, gd]; split_ifs
    · exact hab i
    · rw [← hab i]; ring
  have hg0 : ∀ i, g i ≠ 0 := by
    intro i; simp only [g]; split_ifs
    · exact hJ0 i
    · rw [hJbar i]; exact div_ne_zero (hp0 i) (hJ0 i)
  have hgbar : ∀ i, (starRingEnd ℂ) (g i) = p i / g i := by
    intro i; simp only [g]; split_ifs
    · exact hJbar i
    · rw [Complex.conj_conj, hJbar i]; field_simp [hJ0 i, hp0 i]
  -- (z_i⁶)^{k_i} = g_i^{2K_i} / p_i^{K_i}
  have hG : ∀ i, ((gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 6) ^ k i
      = g i ^ (2 * K i) / (p i : ℂ) ^ K i := by
    intro i
    rw [z6_eq (χ i) (h3 i)]
    simp only [g, K]
    split_ifs with hki
    · rw [zpow_nonneg' _ _ hki, div_pow, pow_mul]
    · rw [zpow_neg' _ _ (by omega), hJbar i, pow_mul, ← div_pow, ← inv_pow]
      congr 1
      field_simp [hJ0 i, hp0 i]
  -- V = ∏ g_i^{2K_i}、Pr = ∏ p_i^{K_i}
  set V := ∏ i, g i ^ (2 * K i)
  set Pr := ∏ i, (p i : ℂ) ^ K i
  have hPr0 : Pr ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp0 i))
  have hV0 : V ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hg0 i))
  have hy : ∏ i, ((gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 6) ^ k i = V / Pr := by
    rw [Finset.prod_congr rfl (fun i _ => hG i), Finset.prod_div_distrib]
  have hVbar : (starRingEnd ℂ) V = Pr ^ 2 / V := by
    simp only [V, Pr]
    rw [map_prod, ← Finset.prod_pow, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_pow, hgbar i, div_pow, ← pow_mul, mul_comm (K i) 2]
  -- 表示と ℤ/P での値
  set P := p i₀
  have hP := (hp i₀).out
  have : Fact P.Prime := hp i₀
  set c := gc i₀
  set d := gd i₀
  have hcd : c ^ 2 - c * d + d ^ 2 = P := hgn i₀
  have hd0 : (d : ZMod P) ≠ 0 := by
    intro h
    have hPd : (P : ℤ) ∣ d := (ZMod.intCast_zmod_eq_zero_iff_dvd d P).mp h
    obtain ⟨t, ht⟩ := hPd
    have hpi : Prime (P : ℤ) := Nat.prime_iff_prime_int.mp hP
    have hc2 : (P : ℤ) ∣ c ^ 2 := ⟨1 + c * t - P * t ^ 2, by rw [ht] at hcd; linear_combination hcd⟩
    obtain ⟨l, hl⟩ := hpi.dvd_of_dvd_pow hc2
    have hPP : (P : ℤ) * P ∣ P := ⟨l ^ 2 - l * t + t ^ 2, by
      calc (P : ℤ) = c ^ 2 - c * d + d ^ 2 := hcd.symm
        _ = _ := by rw [hl, ht]; ring⟩
    have hP1 : (1 : ℤ) < P := by exact_mod_cast hP.one_lt
    obtain ⟨m, hm⟩ := hPP
    have : (P : ℤ) * (P * m - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · omega
    · have : (P : ℤ) * m = 1 := by linarith
      have := Int.eq_one_of_mul_eq_one_right (by omega) this
      omega
  set μ : ZMod P := -(c : ZMod P) / d
  have hμ : μ ^ 2 + μ + 1 = 0 := by
    have hcdP : ((c : ZMod P)) ^ 2 - c * d + (d : ZMod P) ^ 2 = 0 := by
      have := congrArg (fun x : ℤ => (x : ZMod P)) hcd
      push_cast at this; rw [this, ZMod.natCast_self]
    simp only [μ]; field_simp; linear_combination hcdP
  set ev : Fin n → ZMod P := fun i => (gc i : ZMod P) + gd i * μ
  set ev' : Fin n → ZMod P := fun i => (gc i : ZMod P) + gd i * (-1 - μ)
  have hrepV : Rep2 μ V (∏ i, ev i ^ (2 * K i)) (∏ i, ev' i ^ (2 * K i)) :=
    Rep2_prod hμ _ _ _ _ (fun i _ => Rep2_pow hμ ⟨gc i, gd i, hg i, rfl, rfl⟩ _)
  obtain ⟨C, D, hV, hev, hev'⟩ := hrepV
  have he0 : ∏ i, ev i ^ (2 * K i) = 0 := by
    apply Finset.prod_eq_zero (mem_univ i₀)
    have : ev i₀ = 0 := by simp only [ev, μ]; field_simp; ring
    rw [this, zero_pow]
    have : K i₀ ≠ 0 := by simp only [K]; exact Int.natAbs_ne_zero.mpr hk
    omega
  have he'0 : ∏ i, ev' i ^ (2 * K i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply pow_ne_zero
    by_cases hi : i = i₀
    · rw [hi]
      have hval : ev' i₀ = 2 * c - d := by simp only [ev', μ]; field_simp; ring
      rw [hval]
      intro h0
      have hcdP : ((c : ZMod P)) ^ 2 - c * d + (d : ZMod P) ^ 2 = 0 := by
        have := congrArg (fun x : ℤ => (x : ZMod P)) hcd
        push_cast at this; rw [this, ZMod.natCast_self]
      have h3d : (3 : ZMod P) * d ^ 2 = 0 := by linear_combination 4 * hcdP - (2 * (c : ZMod P) - d) * h0
      rcases mul_eq_zero.mp h3d with h | h
      · have : (P : ℤ) ∣ 3 := by
          have h' : ((3 : ℤ) : ZMod P) = 0 := by exact_mod_cast h
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd 3 P).mp h'
        have := Int.le_of_dvd (by norm_num) this
        have h7 : 7 ≤ P := by
          have := hP.two_le
          have h3 := h3p i₀
          have : P ≠ 4 := by intro h4; have h' := hP; rw [show p i₀ = 4 from h4] at h'; exact absurd h' (by decide)
          omega
        omega
      · exact hd0 (pow_eq_zero_iff (by norm_num) |>.mp h)
    · have hprod : ev i * ev' i = (p i : ZMod P) := by
        have := congrArg (fun x : ℤ => (x : ZMod P)) (hgn i)
        push_cast at this
        simp only [ev, ev']; rw [← this]; linear_combination (-(gd i : ZMod P) ^ 2) * hμ
      intro h0
      rw [h0, mul_zero] at hprod
      have : P ∣ p i := (ZMod.natCast_eq_zero_iff _ _).mp hprod.symm
      have := (Nat.prime_dvd_prime_iff_eq hP (hp i).out).mp this
      exact hi (hinj this).symm
  -- y + y⁻¹ = (2C − D)/Pr
  have hVc : (starRingEnd ℂ) V = C + D * (-1 - ω) := by
    rw [hV, map_add, map_mul, conj_ω, map_intCast, map_intCast]
  set Prn : ℕ := ∏ i, p i ^ K i
  have hPrn : ((Prn : ℕ) : ℂ) = Pr := by simp only [Prn, Pr]; push_cast; rfl
  set r : ℚ := ((2 * C - D : ℤ) : ℚ) / Prn
  have hr : V / Pr + (V / Pr)⁻¹ = (r : ℂ) := by
    have hinv : (V / Pr)⁻¹ = (starRingEnd ℂ) V / Pr := by
      rw [hVbar, inv_div]; field_simp
    rw [hinv, ← add_div, hVc]
    simp only [r]; push_cast; rw [hPrn, hV]; ring
  have hnot : ∀ m : ℤ, r ≠ m := by
    intro m hm
    have hPrQ : (Prn : ℚ) ≠ 0 := by
      have : (Prn : ℂ) ≠ 0 := by rw [hPrn]; exact hPr0
      exact_mod_cast this
    have h1 : ((2 * C - D : ℤ) : ℚ) = ((m * Prn : ℤ) : ℚ) := by
      simp only [r] at hm; rw [div_eq_iff hPrQ] at hm; push_cast at hm ⊢; exact hm
    have h2 : 2 * C - D = m * Prn := by exact_mod_cast h1
    have hdv : P ∣ Prn := by
      have : K i₀ ≠ 0 := by simp only [K]; exact Int.natAbs_ne_zero.mpr hk
      exact (dvd_pow_self _ this).trans (Finset.dvd_prod_of_mem (fun i => p i ^ K i) (mem_univ i₀))
    have hz : ((2 * C - D : ℤ) : ZMod P) = 0 := by
      rw [h2]; push_cast
      rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdv, mul_zero]
    have hsum : ((2 * C - D : ℤ) : ZMod P) = ∏ i, ev i ^ (2 * K i) + ∏ i, ev' i ^ (2 * K i) := by
      rw [← hev, ← hev']; push_cast; ring
    rw [hsum, he0, zero_add] at hz
    exact he'0 hz
  intro N hN hX
  have hX6 : (∏ i, ((gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 6) ^ k i) ^ N = 1 := by
    rw [Finset.prod_congr rfl (fun i _ => (zpow_six_comm _ (k i)).symm), Finset.prod_pow, ← pow_mul,
      mul_comm 6 N, pow_mul, hX, one_pow]
  rw [hy] at hX6
  exact not_root_of_trace (V / Pr) r hr hnot N hN hX6

/-- **3'. 判定**：∏ z_i^{k_i} が 1 の冪根 ⇔ すべての k_i = 0。 -/
theorem cubic_zpow_root_iff (hinj : Function.Injective p) (h3p : ∀ i, p i % 3 = 1)
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (h3 : ∀ i, orderOf (χ i) = 3) (k : Fin n → ℤ) :
    (∃ N : ℕ, 0 < N ∧ (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ k i) ^ N = 1)
      ↔ ∀ i, k i = 0 := by
  constructor
  · rintro ⟨N, hN, h⟩
    by_contra hall
    push Not at hall
    obtain ⟨i₀, hk⟩ := hall
    exact cubic_zpow_not_root p hinj h3p χ h3 k i₀ hk N hN h
  · intro h
    exact ⟨1, one_pos, by simp [h]⟩

end PAG.Part180

#print axioms PAG.Part180.Rep2_mul
#print axioms PAG.Part180.Rep2_pow
#print axioms PAG.Part180.Rep2_prod
#print axioms PAG.Part180.zpow_six_comm
#print axioms PAG.Part180.cubic_zpow_not_root
#print axioms PAG.Part180.zpow_nonneg'
#print axioms PAG.Part180.zpow_neg'
#print axioms PAG.Part180.cubic_zpow_root_iff
