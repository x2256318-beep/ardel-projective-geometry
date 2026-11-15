/-
  PAG 2.0 Part 177（2026-10-22）— 3 次・4 次の因子の整数冪の積の完全な判定
  1. Rep4: w = C + Di と ℤ[i] → ℤ/P（i ↦ μ、i ↦ −μ、μ² = −1）
  2. quartic_zpow_not_root / quartic_zpow_root_iff: 4 次の因子の整数冪の積
  3. mixed_zpow_root_iff: 3 次（相異なる素数）と 4 次（相異なる素数）の整数冪の積が 1 の冪根 ⇔ すべての冪指数が 0
-/
import PAG180

namespace PAG.Part181

open Complex Finset PAG.Part171 PAG.Part172 PAG.Part175 PAG.Part176 PAG.Part178 PAG.Part179 PAG.Part180
open ZMod (stdAddChar)

variable {P : ℕ} (μ : ZMod P)

def Rep4 (w : ℂ) (e e' : ZMod P) : Prop :=
  ∃ C D : ℤ, w = C + D * I ∧ ((C : ZMod P) + D * μ = e) ∧ ((C : ZMod P) - D * μ = e')

variable {μ}

theorem Rep4_one : Rep4 μ 1 1 1 := ⟨1, 0, by simp, by simp, by simp⟩

theorem Rep4_mul (hμ : μ ^ 2 + 1 = 0) {w w' : ℂ} {e f e' f' : ZMod P}
    (h : Rep4 μ w e e') (h' : Rep4 μ w' f f') : Rep4 μ (w * w') (e * f) (e' * f') := by
  obtain ⟨C, D, rfl, rfl, rfl⟩ := h
  obtain ⟨C', D', rfl, rfl, rfl⟩ := h'
  refine ⟨C * C' - D * D', C * D' + D * C', ?_, ?_, ?_⟩
  · push_cast; linear_combination ((D : ℂ) * D') * I_sq
  · push_cast; linear_combination (-(D : ZMod P) * D') * hμ
  · push_cast; linear_combination (-(D : ZMod P) * D') * hμ

theorem Rep4_pow (hμ : μ ^ 2 + 1 = 0) {w : ℂ} {e e' : ZMod P} (h : Rep4 μ w e e') :
    ∀ m : ℕ, Rep4 μ (w ^ m) (e ^ m) (e' ^ m)
  | 0 => by simpa using Rep4_one
  | m + 1 => by rw [pow_succ, pow_succ, pow_succ]; exact Rep4_mul hμ (Rep4_pow hμ h m) h

theorem Rep4_prod (hμ : μ ^ 2 + 1 = 0) {ι : Type*} (s : Finset ι) (w : ι → ℂ) (e e' : ι → ZMod P)
    (h : ∀ i ∈ s, Rep4 μ (w i) (e i) (e' i)) : Rep4 μ (∏ i ∈ s, w i) (∏ i ∈ s, e i) (∏ i ∈ s, e' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rep4_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj]
    exact Rep4_mul hμ (h j (by simp)) (ih (fun i hi => h i (by simp [hi])))

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime]

theorem zpow_four_comm (z : ℂ) (k : ℤ) : (z ^ k) ^ 4 = (z ^ 4) ^ k := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

/-- **2. 4 次の因子の整数冪の積**。 -/
theorem quartic_zpow_not_root (hinj : Function.Injective p)
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (h4 : ∀ i, orderOf (χ i) = 4) (k : Fin n → ℤ) (i₀ : Fin n)
    (hk : k i₀ ≠ 0) :
    ∀ N : ℕ, 0 < N → (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ k i) ^ N ≠ 1 := by
  classical
  choose a b hJ hJc hab using fun i => jacobi_data4 (χ i) (h4 i)
  choose σ hσ hsσ using fun i => sign_int (χ i)
  have hp0 : ∀ i, (p i : ℂ) ≠ 0 := fun i => by exact_mod_cast (hp i).out.ne_zero
  have hnJ : ∀ i, jacobiSum (χ i) (χ i) * (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) = p i :=
    fun i => jacobi_norm4 (χ i) (h4 i)
  have hJ0 : ∀ i, jacobiSum (χ i) (χ i) ≠ 0 := fun i h => by
    have := hnJ i; rw [h, zero_mul] at this; exact hp0 i this.symm
  have hJbar : ∀ i, (starRingEnd ℂ) (jacobiSum (χ i) (χ i)) = p i / jacobiSum (χ i) (χ i) := fun i => by
    rw [eq_div_iff (hJ0 i), mul_comm]; exact hnJ i
  have hσ2 : ∀ i, (σ i : ℂ) ^ 2 = 1 := fun i => by rcases hσ i with h | h <;> rw [h] <;> norm_num
  have hσ0 : ∀ i, (σ i : ℂ) ≠ 0 := fun i => by rcases hσ i with h | h <;> rw [h] <;> norm_num
  have hσinv : ∀ i, (σ i : ℂ)⁻¹ = σ i := fun i => by rcases hσ i with h | h <;> rw [h] <;> norm_num
  set K : Fin n → ℕ := fun i => (k i).natAbs
  set g : Fin n → ℂ := fun i =>
    if 0 ≤ k i then jacobiSum (χ i) (χ i) else (starRingEnd ℂ) (jacobiSum (χ i) (χ i))
  set gc : Fin n → ℤ := fun i => a i
  set gd : Fin n → ℤ := fun i => if 0 ≤ k i then b i else -b i
  have hg : ∀ i, g i = gc i + gd i * I := by
    intro i; simp only [g, gc, gd]
    split_ifs
    · exact hJ i
    · rw [hJc i]; push_cast; ring
  have hgn : ∀ i, gc i ^ 2 + gd i ^ 2 = p i := by
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
  -- (z_i⁴)^{k_i} = σ_i^{K_i} g_i^{2K_i} / p_i^{K_i}
  have hG : ∀ i, ((gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 4) ^ k i
      = (σ i : ℂ) ^ K i * g i ^ (2 * K i) / (p i : ℂ) ^ K i := by
    intro i
    rw [z4_eq (χ i) (h4 i), hsσ i]
    simp only [g, K]
    split_ifs with hki
    · rw [zpow_nonneg' _ _ hki, div_pow, mul_pow, pow_mul]
    · rw [zpow_neg' _ _ (by omega), hJbar i, ← inv_pow,
        show (σ i : ℂ) ^ (k i).natAbs * ((p i : ℂ) / jacobiSum (χ i) (χ i)) ^ (2 * (k i).natAbs) / (p i : ℂ) ^ (k i).natAbs
          = ((σ i : ℂ) * (((p i : ℂ) / jacobiSum (χ i) (χ i)) ^ 2 / p i)) ^ (k i).natAbs by
          rw [mul_pow, div_pow _ (p i : ℂ), ← pow_mul]; ring]
      congr 1
      have hJi := hJ0 i; have hpi := hp0 i
      rcases hσ i with h | h <;> rw [h] <;> push_cast <;> field_simp
  set V := ∏ i, g i ^ (2 * K i)
  set Pr := ∏ i, (p i : ℂ) ^ K i
  set S : ℤ := ∏ i, σ i ^ K i
  have hS : S = 1 ∨ S = -1 := by
    simp only [S]
    induction (univ : Finset (Fin n)) using Finset.induction_on with
    | empty => left; simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj]
      rcases hσ j with h | h <;> rcases ih with h' | h' <;> rw [h, h'] <;>
        rcases neg_one_pow_eq_or ℤ (K j) with h'' | h'' <;> simp [h'']
  have hSS : (S : ℂ) * S = 1 := by rcases hS with h | h <;> rw [h] <;> norm_num
  have hPr0 : Pr ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp0 i))
  have hV0 : V ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hg0 i))
  have hy : ∏ i, ((gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 4) ^ k i = S * V / Pr := by
    rw [Finset.prod_congr rfl (fun i _ => hG i), Finset.prod_div_distrib, Finset.prod_mul_distrib]
    simp only [S, V, Pr]; push_cast; ring
  have hVbar : (starRingEnd ℂ) V = Pr ^ 2 / V := by
    simp only [V, Pr]
    rw [map_prod, ← Finset.prod_pow, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_pow, hgbar i, div_pow, ← pow_mul, mul_comm (K i) 2]
  set Q := p i₀
  have hP := (hp i₀).out
  have : Fact Q.Prime := hp i₀
  set c := gc i₀
  set d := gd i₀
  have hcd : c ^ 2 + d ^ 2 = Q := hgn i₀
  have hcdQ : ((c : ZMod Q)) ^ 2 + (d : ZMod Q) ^ 2 = 0 := by
    have := congrArg (fun x : ℤ => (x : ZMod Q)) hcd
    push_cast at this; rw [this, ZMod.natCast_self]
  have hd0 : (d : ZMod Q) ≠ 0 := by
    intro h
    have hPd : (Q : ℤ) ∣ d := (ZMod.intCast_zmod_eq_zero_iff_dvd d Q).mp h
    obtain ⟨t, ht⟩ := hPd
    have hpi : Prime (Q : ℤ) := Nat.prime_iff_prime_int.mp hP
    have hc2 : (Q : ℤ) ∣ c ^ 2 := ⟨1 - Q * t ^ 2, by rw [ht] at hcd; linear_combination hcd⟩
    obtain ⟨l, hl⟩ := hpi.dvd_of_dvd_pow hc2
    have hPP : (Q : ℤ) * Q ∣ Q := ⟨l ^ 2 + t ^ 2, by
      calc (Q : ℤ) = c ^ 2 + d ^ 2 := hcd.symm
        _ = _ := by rw [hl, ht]; ring⟩
    have hP1 : (1 : ℤ) < Q := by exact_mod_cast hP.one_lt
    obtain ⟨m, hm⟩ := hPP
    have : (Q : ℤ) * (Q * m - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · omega
    · have : (Q : ℤ) * m = 1 := by linarith
      have := Int.eq_one_of_mul_eq_one_right (by omega) this
      omega
  set μ : ZMod Q := -(c : ZMod Q) / d
  have hμ : μ ^ 2 + 1 = 0 := by simp only [μ]; field_simp; linear_combination hcdQ
  set ev : Fin n → ZMod Q := fun i => (gc i : ZMod Q) + gd i * μ
  set ev' : Fin n → ZMod Q := fun i => (gc i : ZMod Q) - gd i * μ
  have hrepV : Rep4 μ V (∏ i, ev i ^ (2 * K i)) (∏ i, ev' i ^ (2 * K i)) :=
    Rep4_prod hμ _ _ _ _ (fun i _ => Rep4_pow hμ ⟨gc i, gd i, hg i, rfl, rfl⟩ _)
  obtain ⟨C, D, hV, hev, hev'⟩ := hrepV
  have he0 : ∏ i, ev i ^ (2 * K i) = 0 := by
    apply Finset.prod_eq_zero (mem_univ i₀)
    have : ev i₀ = 0 := by simp only [ev, μ]; field_simp; ring
    rw [this, zero_pow]
    have : K i₀ ≠ 0 := by simp only [K]; exact Int.natAbs_ne_zero.mpr hk
    omega
  have h2ne : (2 : ZMod Q) ≠ 0 := PAG.Part119.two_ne_zero' (p := Q) (by
    intro h2; have := p_ge_five (χ i₀) (h4 i₀); omega)
  have he'0 : ∏ i, ev' i ^ (2 * K i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply pow_ne_zero
    by_cases hi : i = i₀
    · rw [hi]
      have hval : ev' i₀ = 2 * c := by simp only [ev', μ]; field_simp; ring
      rw [hval]
      intro h0
      have hc0 : (c : ZMod Q) = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h h2ne
        · exact h
      rw [hc0] at hcdQ
      have hd2 : (d : ZMod Q) ^ 2 = 0 := by linear_combination hcdQ
      exact hd0 (pow_eq_zero_iff two_ne_zero |>.mp hd2)
    · have hprod : ev i * ev' i = (p i : ZMod Q) := by
        have := congrArg (fun x : ℤ => (x : ZMod Q)) (hgn i)
        push_cast at this
        simp only [ev, ev']; rw [← this]; linear_combination (-(gd i : ZMod Q) ^ 2) * hμ
      intro h0
      rw [h0, mul_zero] at hprod
      have : Q ∣ p i := (ZMod.natCast_eq_zero_iff _ _).mp hprod.symm
      have := (Nat.prime_dvd_prime_iff_eq hP (hp i).out).mp this
      exact hi (hinj this).symm
  have hVc : (starRingEnd ℂ) V = C - D * I := by
    rw [hV, map_add, map_mul, conj_I, map_intCast, map_intCast]; ring
  set Pn : ℕ := ∏ i, p i ^ K i
  have hPn : ((Pn : ℕ) : ℂ) = Pr := by simp only [Pn, Pr]; push_cast; rfl
  set r : ℚ := ((S * (2 * C) : ℤ) : ℚ) / Pn
  have hr : S * V / Pr + (S * V / Pr)⁻¹ = (r : ℂ) := by
    have hinv : (S * V / Pr)⁻¹ = S * (starRingEnd ℂ) V / Pr := by
      rw [hVbar]
      rcases hS with h | h <;> rw [h] <;> push_cast <;> field_simp
    rw [hinv, ← add_div, hVc]
    simp only [r]; push_cast; rw [hPn, hV]; ring
  have hnot : ∀ m : ℤ, r ≠ m := by
    intro m hm
    have hPQ : (Pn : ℚ) ≠ 0 := by
      have : (Pn : ℂ) ≠ 0 := by rw [hPn]; exact hPr0
      exact_mod_cast this
    have h1 : ((S * (2 * C) : ℤ) : ℚ) = ((m * Pn : ℤ) : ℚ) := by
      simp only [r] at hm; rw [div_eq_iff hPQ] at hm; push_cast at hm ⊢; exact hm
    have h2 : S * (2 * C) = m * Pn := by exact_mod_cast h1
    have hdv : Q ∣ Pn := by
      have : K i₀ ≠ 0 := by simp only [K]; exact Int.natAbs_ne_zero.mpr hk
      exact (dvd_pow_self _ this).trans (Finset.dvd_prod_of_mem (fun i => p i ^ K i) (mem_univ i₀))
    have hz : ((S * (2 * C) : ℤ) : ZMod Q) = 0 := by
      rw [h2]; push_cast
      rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdv, mul_zero]
    have hsum : ((2 * C : ℤ) : ZMod Q) = ∏ i, ev i ^ (2 * K i) + ∏ i, ev' i ^ (2 * K i) := by
      rw [← hev, ← hev']; push_cast; ring
    have hSu : ((S : ℤ) : ZMod Q) ≠ 0 := by
      rcases hS with h | h <;> rw [h] <;> simp
    rw [Int.cast_mul, hsum, he0, zero_add] at hz
    rcases mul_eq_zero.mp hz with h | h
    · exact hSu h
    · exact he'0 h
  intro N hN hX
  have hX4 : (∏ i, ((gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ 4) ^ k i) ^ N = 1 := by
    rw [Finset.prod_congr rfl (fun i _ => (zpow_four_comm _ (k i)).symm), Finset.prod_pow, ← pow_mul,
      mul_comm 4 N, pow_mul, hX, one_pow]
  rw [hy] at hX4
  exact not_root_of_trace (S * V / Pr) r hr hnot N hN hX4

theorem quartic_zpow_root_iff (hinj : Function.Injective p)
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (h4 : ∀ i, orderOf (χ i) = 4) (k : Fin n → ℤ) :
    (∃ N : ℕ, 0 < N ∧ (∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (p i) : ℝ) : ℂ)) ^ k i) ^ N = 1)
      ↔ ∀ i, k i = 0 := by
  constructor
  · rintro ⟨N, hN, h⟩
    by_contra hall
    push Not at hall
    obtain ⟨i₀, hk⟩ := hall
    exact quartic_zpow_not_root p hinj χ h4 k i₀ hk N hN h
  · intro h
    exact ⟨1, one_pos, by simp [h]⟩

theorem InQω_zpow {u : ℂ} (hu : InQω u) (hu' : (starRingEnd ℂ) u = u⁻¹) (k : ℤ) :
    InQω (u ^ k) ∧ (starRingEnd ℂ) (u ^ k) = (u ^ k)⁻¹ := by
  rcases le_or_gt 0 k with hk | hk
  · rw [zpow_nonneg' _ _ hk]
    exact ⟨InQω_pow hu _, by rw [map_pow, hu', inv_pow]⟩
  · rw [zpow_neg' _ _ hk]
    refine ⟨?_, by rw [map_inv₀, map_pow, hu', inv_pow]⟩
    rw [← inv_pow, ← hu']; exact InQω_pow (InQω_conj hu) _

theorem InQi_zpow {u : ℂ} (hu : InQi u) (hu' : (starRingEnd ℂ) u = u⁻¹) (k : ℤ) :
    InQi (u ^ k) ∧ (starRingEnd ℂ) (u ^ k) = (u ^ k)⁻¹ := by
  rcases le_or_gt 0 k with hk | hk
  · rw [zpow_nonneg' _ _ hk]
    exact ⟨InQi_pow hu _, by rw [map_pow, hu', inv_pow]⟩
  · rw [zpow_neg' _ _ hk]
    refine ⟨?_, by rw [map_inv₀, map_pow, hu', inv_pow]⟩
    rw [← inv_pow, ← hu']; exact InQi_pow (InQi_conj hu) _

variable {nc nq : ℕ} (pc : Fin nc → ℕ) [hpc : ∀ i, Fact (pc i).Prime] (pq : Fin nq → ℕ) [hpq : ∀ j, Fact (pq j).Prime]

/-- **3. 3 次・4 次の因子の整数冪の積の完全な判定**。 -/
theorem mixed_zpow_root_iff (hinjc : Function.Injective pc) (h3p : ∀ i, pc i % 3 = 1)
    (χ : ∀ i, DirichletCharacter ℂ (pc i)) (h3 : ∀ i, orderOf (χ i) = 3) (k : Fin nc → ℤ)
    (hinjq : Function.Injective pq) (ψ : ∀ j, DirichletCharacter ℂ (pq j)) (h4 : ∀ j, orderOf (ψ j) = 4)
    (l : Fin nq → ℤ) :
    (∃ N : ℕ, 0 < N ∧ ((∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ k i)
        * (∏ j, (gaussSum (ψ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ)) ^ l j)) ^ N = 1)
      ↔ (∀ i, k i = 0) ∧ (∀ j, l j = 0) := by
  constructor
  · rintro ⟨N, hN, hX⟩
    set Zc := ∏ i, (gaussSum (χ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ k i
    set Zq := ∏ j, (gaussSum (ψ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ)) ^ l j
    have hcf : ∀ i, InQω (((gaussSum (χ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ 6) ^ k i) ∧
        (starRingEnd ℂ) (((gaussSum (χ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ 6) ^ k i)
          = (((gaussSum (χ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ 6) ^ k i)⁻¹ :=
      fun i => InQω_zpow (z6_facts (χ i) (h3 i)).1 (z6_facts (χ i) (h3 i)).2 (k i)
    have hqf : ∀ j, InQi (((gaussSum (ψ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ)) ^ 4) ^ l j) ∧
        (starRingEnd ℂ) (((gaussSum (ψ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ)) ^ 4) ^ l j)
          = (((gaussSum (ψ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ)) ^ 4) ^ l j)⁻¹ :=
      fun j => InQi_zpow (z4_facts (ψ j) (h4 j)).1 (z4_facts (ψ j) (h4 j)).2 (l j)
    have hZc6 : Zc ^ 6 = ∏ i, ((gaussSum (χ i) stdAddChar / ((Real.sqrt (pc i) : ℝ) : ℂ)) ^ 6) ^ k i := by
      simp only [Zc]; rw [← Finset.prod_pow]; exact Finset.prod_congr rfl (fun i _ => zpow_six_comm _ _)
    have hZq4 : Zq ^ 4 = ∏ j, ((gaussSum (ψ j) stdAddChar / ((Real.sqrt (pq j) : ℝ) : ℂ)) ^ 4) ^ l j := by
      simp only [Zq]; rw [← Finset.prod_pow]; exact Finset.prod_congr rfl (fun j _ => zpow_four_comm _ _)
    have hu : InQω (Zc ^ 6) := by rw [hZc6]; exact InQω_prod _ _ (fun i _ => (hcf i).1)
    have hu' : (starRingEnd ℂ) (Zc ^ 6) = (Zc ^ 6)⁻¹ := by rw [hZc6]; exact conj_prod_inv _ _ (fun i _ => (hcf i).2)
    have hv : InQi (Zq ^ 4) := by rw [hZq4]; exact InQi_prod _ _ (fun j _ => (hqf j).1)
    have hv' : (starRingEnd ℂ) (Zq ^ 4) = (Zq ^ 4)⁻¹ := by rw [hZq4]; exact conj_prod_inv _ _ (fun j _ => (hqf j).2)
    obtain ⟨h1, h2⟩ := key_lemma _ _ hu hv hu' hv' N hN (split_pow Zc Zq N hX)
    rw [← pow_mul] at h1 h2
    exact ⟨(cubic_zpow_root_iff pc hinjc h3p χ h3 k).mp ⟨_, by omega, h1⟩,
      (quartic_zpow_root_iff pq hinjq ψ h4 l).mp ⟨_, by omega, h2⟩⟩
  · rintro ⟨hk, hl⟩
    exact ⟨1, one_pos, by simp [hk, hl]⟩

end PAG.Part181

#print axioms PAG.Part181.Rep4_mul
#print axioms PAG.Part181.Rep4_pow
#print axioms PAG.Part181.Rep4_prod
#print axioms PAG.Part181.zpow_four_comm
#print axioms PAG.Part181.quartic_zpow_not_root
#print axioms PAG.Part181.quartic_zpow_root_iff
#print axioms PAG.Part181.InQω_zpow
#print axioms PAG.Part181.InQi_zpow
#print axioms PAG.Part181.mixed_zpow_root_iff
