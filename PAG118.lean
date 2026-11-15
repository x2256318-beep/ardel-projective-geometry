/-
  PAG 2.0 Part 114（2026-10-19）— 導手 p^{2m} のガウス和: τ(χ) = p^m · χ(u₀) e(u₀)、とくに τ/p^m は 1 の冪根
  N = p^c、c = 2m、χ 原始、P = p^m（P² = 0 in ℤ/N）について
  1. φ(y) = χ(1 + P y) は加法的（φ(y+z) = φ(y)φ(z)）
  2. 平均化: τ = Σ_{u ∈ S} χ(u) e(u)、S = {u : ∀ y, φ(y) e(P u y) = 1}
  3. S 上で χ(u)e(u) は一定（定常位相）: τ = |S| · χ(u₀)e(u₀)
  4. |τ|² = N から |S| = p^m、τ/p^m = χ(u₀)e(u₀) は 1 の冪根（(·)^{ord χ · N} = 1）
  系: 導手 p^{2m} の原始ケットの ζ_k は 1 の冪根
-/
import PAG117

namespace PAG.Part118

open ZMod Finset

section CharSum

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- 乗法的な関数の和: 自明でなければ 0。 -/
theorem sum_mult_eq_zero (g : G → ℂ) (hg : ∀ y z, g (y + z) = g y * g z) (h : ¬ ∀ y, g y = 1) :
    ∑ y, g y = 0 := by
  push Not at h
  obtain ⟨z, hz⟩ := h
  have e : ∑ y, g y = g z * ∑ y, g y := by
    rw [Finset.mul_sum]
    symm
    calc ∑ y, g z * g y = ∑ y, g (y + z) := sum_congr rfl (fun y _ => by rw [hg, mul_comm])
      _ = ∑ y, g y := Fintype.sum_equiv (Equiv.addRight z) _ _ (fun y => rfl)
  have : (1 - g z) * ∑ y, g y = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hz))

end CharSum

variable {p : ℕ} [hp : Fact p.Prime]

section Gauss

variable (c m : ℕ) (hc : c = 2 * m)

omit hp in
include hc in
theorem P_sq : ((p : ZMod (p ^ c)) ^ m) * ((p : ZMod (p ^ c)) ^ m) = 0 := by
  rw [← pow_add, show m + m = c by omega, ← Nat.cast_pow, ZMod.natCast_self]

include hc in
/-- P w = 0 ⇒ w = P z。 -/
theorem dvd_of_P_mul (w : ZMod (p ^ c)) (h : (p : ZMod (p ^ c)) ^ m * w = 0) :
    ∃ z : ZMod (p ^ c), w = (p : ZMod (p ^ c)) ^ m * z := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [← ZMod.natCast_zmod_val w, ← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
  have hc' : p ^ m * p ^ m = p ^ c := by rw [← pow_add]; congr 1; omega
  obtain ⟨z, hz⟩ := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos m) ((dvd_of_eq hc').trans h)
  refine ⟨(z : ZMod (p ^ c)), ?_⟩
  rw [← ZMod.natCast_zmod_val w, hz]; push_cast; ring

variable {c m}

/-- φ(y) = χ(1 + P y)。 -/
noncomputable def phi (χ : DirichletCharacter ℂ (p ^ c)) (y : ZMod (p ^ c)) : ℂ :=
  χ (1 + (p : ZMod (p ^ c)) ^ m * y)

omit hp in
include hc in
theorem phi_add (χ : DirichletCharacter ℂ (p ^ c)) (y z : ZMod (p ^ c)) :
    phi (m := m) χ (y + z) = phi (m := m) χ y * phi (m := m) χ z := by
  unfold phi
  rw [← map_mul]
  congr 1
  have h2 := P_sq (p := p) c m hc
  linear_combination (-(y * z)) * h2

include hc in
theorem one_add_P_unit (y : ZMod (p ^ c)) : IsUnit (1 + (p : ZMod (p ^ c)) ^ m * y) := by
  refine isUnit_iff_exists_inv.mpr ⟨1 - (p : ZMod (p ^ c)) ^ m * y, ?_⟩
  have h2 := P_sq (p := p) c m hc
  linear_combination (-(y * y)) * h2

include hc in
/-- **2. 平均化**: τ = Σ_{u ∈ S} χ(u) e(u)。 -/
theorem gauss_eq_sum_S (χ : DirichletCharacter ℂ (p ^ c)) :
    gaussSum χ stdAddChar = ∑ u ∈ univ.filter (fun u : ZMod (p ^ c) =>
      ∀ y, phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u * y) = 1), χ u * stdAddChar u := by
  classical
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set P := (p : ZMod (p ^ c)) ^ m
  set τ := gaussSum χ stdAddChar
  -- 各 y で τ = Σ_u χ u e u φ(y) e(P u y)
  have hy : ∀ y : ZMod (p ^ c), τ = ∑ u, χ u * stdAddChar u * (phi (m := m) χ y * stdAddChar (P * u * y)) := by
    intro y
    have hv := one_add_P_unit (p := p) hc y
    have hre : ∑ u, χ (u * (1 + P * y)) * stdAddChar (u * (1 + P * y)) = τ :=
      Fintype.sum_equiv (Units.mulRight hv.unit) _ (fun u => χ u * stdAddChar u) (fun u => rfl)
    rw [← hre]
    apply sum_congr rfl; intro u _
    simp only [phi, P]
    rw [map_mul, show u * (1 + (p : ZMod (p ^ c)) ^ m * y) = u + (p : ZMod (p ^ c)) ^ m * u * y by ring,
      AddChar.map_add_eq_mul]
    ring
  have hmult : ∀ u : ZMod (p ^ c), ∀ y z, phi (m := m) χ (y + z) * stdAddChar (P * u * (y + z))
      = (phi (m := m) χ y * stdAddChar (P * u * y)) * (phi (m := m) χ z * stdAddChar (P * u * z)) := by
    intro u y z
    rw [phi_add hc, mul_add, AddChar.map_add_eq_mul]; ring
  have hinner : ∀ u : ZMod (p ^ c), ∑ y, phi (m := m) χ y * stdAddChar (P * u * y)
      = if (∀ y, phi (m := m) χ y * stdAddChar (P * u * y) = 1) then ((p ^ c : ℕ) : ℂ) else 0 := by
    intro u
    split_ifs with hS
    · simp only [hS, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    · exact sum_mult_eq_zero _ (hmult u) hS
  have hN : ((p ^ c : ℕ) : ℂ) * τ = ((p ^ c : ℕ) : ℂ) * ∑ u ∈ univ.filter (fun u : ZMod (p ^ c) =>
      ∀ y, phi (m := m) χ y * stdAddChar (P * u * y) = 1), χ u * stdAddChar u := by
    calc ((p ^ c : ℕ) : ℂ) * τ = ∑ _y : ZMod (p ^ c), τ := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      _ = ∑ y : ZMod (p ^ c), ∑ u, χ u * stdAddChar u * (phi (m := m) χ y * stdAddChar (P * u * y)) :=
          sum_congr rfl (fun y _ => hy y)
      _ = ∑ u, χ u * stdAddChar u * ∑ y, phi (m := m) χ y * stdAddChar (P * u * y) := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ = _ := by
          simp only [hinner, mul_ite, mul_zero]
          rw [← Finset.sum_filter, Finset.mul_sum]
          apply sum_congr rfl; intro u _; ring
  have hN0 : ((p ^ c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  exact mul_left_cancel₀ hN0 hN

include hc in
/-- **3. S 上で χ(u)e(u) は一定**。 -/
theorem const_on_S (χ : DirichletCharacter ℂ (p ^ c)) (u₀ u : ZMod (p ^ c)) (hu₀ : IsUnit u₀)
    (hS₀ : ∀ y, phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u₀ * y) = 1)
    (hS : ∀ y, phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u * y) = 1) :
    χ u * stdAddChar u = χ u₀ * stdAddChar u₀ := by
  set P := (p : ZMod (p ^ c)) ^ m
  -- P u = P u₀
  have hPu : P * u = P * u₀ := by
    have h1 := hS 1; have h2 := hS₀ 1
    rw [mul_one] at h1 h2
    have hφ : phi (m := m) χ 1 ≠ 0 := by intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
    exact ZMod.injective_stdAddChar (mul_left_cancel₀ hφ (h1.trans h2.symm))
  obtain ⟨z, hz⟩ := dvd_of_P_mul (p := p) c m hc (u - u₀) (by rw [mul_sub, hPu, sub_self])
  set U := hu₀.unit
  have hUU : u₀ * (↑U⁻¹ : ZMod (p ^ c)) = 1 := by
    have := U.mul_inv; simp [U]
  have hu : u = u₀ * (1 + P * ((↑U⁻¹ : ZMod (p ^ c)) * z)) := by
    linear_combination hz - (P * z) * hUU
  have hy := hS₀ ((↑U⁻¹ : ZMod (p ^ c)) * z)
  have hPz : P * u₀ * ((↑U⁻¹ : ZMod (p ^ c)) * z) = P * z := by
    linear_combination (P * z) * hUU
  rw [hPz] at hy
  have hu' : u = u₀ + P * z := by linear_combination hz
  calc χ u * stdAddChar u
      = χ u₀ * phi (m := m) χ ((↑U⁻¹ : ZMod (p ^ c)) * z) * (stdAddChar u₀ * stdAddChar (P * z)) := by
        conv_lhs => rw [hu]
        rw [map_mul]
        simp only [phi]
        congr 1
        rw [← hu, hu', AddChar.map_add_eq_mul]
    _ = χ u₀ * stdAddChar u₀ * (phi (m := m) χ ((↑U⁻¹ : ZMod (p ^ c)) * z) * stdAddChar (P * z)) := by ring
    _ = χ u₀ * stdAddChar u₀ := by rw [hy, mul_one]

include hc in
/-- **4. 導手 p^{2m} のガウス和の位相は 1 の冪根**。 -/
theorem gauss_even_root (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ M : ℕ, 0 < M ∧ (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ M = 1 := by
  classical
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set P := (p : ZMod (p ^ c)) ^ m
  set S := univ.filter (fun u : ZMod (p ^ c) => ∀ y, phi (m := m) χ y * stdAddChar (P * u * y) = 1)
  have hτ := gauss_eq_sum_S (p := p) hc χ
  have hτ0 := PAG.Part16.gaussSum_ne_zero hχ
  rw [hτ] at hτ0
  obtain ⟨u₀, hu₀S, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ0
  have hχu₀ : χ u₀ ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have hunit : IsUnit u₀ := by
    by_contra hn; exact hχu₀ (MulChar.map_nonunit χ hn)
  have hS₀ := (Finset.mem_filter.mp hu₀S).2
  set ε := χ u₀ * stdAddChar u₀
  have hsum : gaussSum χ stdAddChar = (S.card : ℂ) * ε := by
    rw [hτ, Finset.sum_congr rfl (fun u hu => const_on_S (p := p) hc χ u₀ u hunit hS₀ (Finset.mem_filter.mp hu).2),
      Finset.sum_const, nsmul_eq_mul]
  -- ε^{o N} = 1
  set o := orderOf χ
  have hεpow : ε ^ (o * p ^ c) = 1 := by
    have h1 : χ u₀ ^ o = 1 := by
      rw [← MulChar.pow_apply' _ (orderOf_pos χ).ne', pow_orderOf_eq_one]; exact MulChar.one_apply hunit
    have h2 : stdAddChar u₀ ^ (p ^ c) = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    rw [mul_pow, pow_mul, h1, one_pow, one_mul, mul_comm, pow_mul, h2, one_pow]
  have hMpos : 0 < o * p ^ c := Nat.mul_pos (orderOf_pos χ) (pow_pos hp.out.pos _)
  have hεn : Complex.normSq ε = 1 := by
    have h := congrArg Complex.normSq hεpow
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg ε) hMpos.ne').mp h
  -- |S| = √(p^c)
  have hpc : (0 : ℝ) < (p : ℝ) ^ c := pow_pos (by exact_mod_cast hp.out.pos) _
  have hcard : (S.card : ℝ) = Real.sqrt ((p : ℝ) ^ c) := by
    have h := PAG.Part16.normSq_gaussSum hχ
    rw [hsum, map_mul, hεn, mul_one, Complex.normSq_natCast] at h
    rw [← Real.sqrt_mul_self (Nat.cast_nonneg (S.card : ℕ))]
    congr 1; rw [h]; push_cast; ring
  refine ⟨o * p ^ c, hMpos, ?_⟩
  have hs0 : ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ) ≠ 0 := by
    have := Real.sqrt_pos.mpr hpc; exact_mod_cast this.ne'
  rw [hsum, ← hcard]
  have hS0 : (S.card : ℂ) ≠ 0 := by
    have : (S.card : ℝ) ≠ 0 := by rw [hcard]; exact (Real.sqrt_pos.mpr hpc).ne'
    exact_mod_cast this
  rw [show ((S.card : ℝ) : ℂ) = (S.card : ℂ) by push_cast; rfl, mul_div_cancel_left₀ _ hS0, hεpow]

end Gauss

/-! ## 系: 導手 p^{2m} の原始ケットの ζ_k は 1 の冪根 -/

open PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117 in
theorem zeta_root_even (K w n m : ℕ) (hnm : n + 1 = 2 * m) (h : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K))
    (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w)) :
    ∃ N : ℕ, 0 < N ∧ ((cnorm p K (K - (n + 1) - w) * 𝓕 (ket K w (n + 1) h χ) t₀) ^ orderOf χ) ^ N = 1 :=
  (zeta_root_iff K w n h χ hχ t₀ ht₀).mpr (gauss_even_root (p := p) hnm χ hχ)

end PAG.Part118

#print axioms PAG.Part118.sum_mult_eq_zero
#print axioms PAG.Part118.P_sq
#print axioms PAG.Part118.dvd_of_P_mul
#print axioms PAG.Part118.phi_add
#print axioms PAG.Part118.one_add_P_unit
#print axioms PAG.Part118.gauss_eq_sum_S
#print axioms PAG.Part118.const_on_S
#print axioms PAG.Part118.gauss_even_root
#print axioms PAG.Part118.zeta_root_even
