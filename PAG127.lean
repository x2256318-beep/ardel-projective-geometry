/-
  PAG 2.0 Part 123（2026-10-21）— 導手 p^{2m} のガウス和の位相の正確な位数
  N = p^c、c = 2m（m ≥ 1）、χ 原始について z = τ(χ)/√(p^c) とおくと
  1. e(u)^n = 1 ↔ p^c ∣ n（u 単元）、χ(u)^{φ(p^c)} = 1
  2. 抽象補題: x の位数が p^c、y^{p^{c-1}(p-1)} = 1 なら (y x)^d = 1 ⇒ p^c ∣ d
  3. z = χ(u₀) e(u₀)（u₀ 単元）
  4. ord z = lcm(ord χ(u₀), p^c)。系: p^c ∣ ord z ∣ lcm(ord χ, p^c)
-/
import PAG126

namespace PAG.Part127

open ZMod Finset PAG.Part118

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1a. e(u) の位数は p^c**（u 単元）。 -/
theorem stdAddChar_pow_eq_one_iff {c : ℕ} (u : ZMod (p ^ c)) (hu : IsUnit u) (n : ℕ) :
    stdAddChar u ^ n = 1 ↔ p ^ c ∣ n := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  constructor
  · intro h
    have h0 : (n : ZMod (p ^ c)) * u = 0 :=
      ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm)
    exact (ZMod.natCast_eq_zero_iff _ _).mp (hu.mul_left_eq_zero.mp h0)
  · rintro ⟨k, rfl⟩
    rw [Nat.cast_mul, Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, zero_mul,
      AddChar.map_zero_eq_one]

omit hp in
/-- **1b. χ(u)^{φ(p^c)} = 1**（u 単元）。 -/
theorem chi_pow_totient {c : ℕ} (χ : DirichletCharacter ℂ (p ^ c)) (u : ZMod (p ^ c)) (hu : IsUnit u) :
    χ u ^ Nat.totient (p ^ c) = 1 := by
  rw [← map_pow]
  have : u ^ Nat.totient (p ^ c) = 1 := by
    rw [← hu.unit_spec, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one]
  rw [this, map_one]

/-- **2. 抽象補題**: x^n = 1 ↔ p^c ∣ n、y^{p^{c-1}(p-1)} = 1 なら (y x)^d = 1 ⇒ p^c ∣ d。 -/
theorem pdvd_of_mul (c : ℕ) (hc : 1 ≤ c) (x y : ℂ) (hx : ∀ n, x ^ n = 1 ↔ p ^ c ∣ n)
    (hy : y ^ (p ^ (c - 1) * (p - 1)) = 1) (d : ℕ) (hd : (y * x) ^ d = 1) : p ^ c ∣ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · exact dvd_zero _
  by_contra hnd
  obtain ⟨j, d', hnot, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0.ne' p hp.out.ne_one
  have hj : j < c := by
    by_contra hj
    exact hnd (dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) _)
  have hsplit : p ^ (c - 1) = p ^ j * p ^ (c - 1 - j) := by rw [← pow_add]; congr 1; omega
  have hE : p ^ j * d' * ((p - 1) * p ^ (c - 1 - j)) = p ^ (c - 1) * (p - 1) * d' := by
    rw [hsplit]; ring
  have h1 : (y * x) ^ (p ^ j * d' * ((p - 1) * p ^ (c - 1 - j))) = 1 := by rw [pow_mul, hd, one_pow]
  rw [mul_pow, hE, pow_mul y, hy, one_pow, one_mul, ← hE] at h1
  have h4 := (hx _).mp h1
  rw [hE, show p ^ (c - 1) * (p - 1) * d' = p ^ (c - 1) * ((p - 1) * d') by ring] at h4
  have hnd' : ¬ p ∣ (p - 1) * d' := by
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · have := Nat.le_of_dvd (by have := hp.out.two_le; omega) h
      have := hp.out.two_le; omega
    · exact hnot h
  have hcop : Nat.Coprime (p ^ c) ((p - 1) * d') :=
    Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd')
  have h5 := hcop.dvd_of_dvd_mul_right h4
  have h6 := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h5
  omega

section Even

variable {c m : ℕ} (hc : c = 2 * m)

include hc in
/-- **3. 位相の明示形**: τ/√(p^c) = χ(u₀) e(u₀)、u₀ 単元。 -/
theorem gauss_even_phase (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧
      gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ) = χ u₀ * stdAddChar u₀ := by
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
  have hpc : (0 : ℝ) < (p : ℝ) ^ c := pow_pos (by exact_mod_cast hp.out.pos) _
  have hcard : (S.card : ℝ) = Real.sqrt ((p : ℝ) ^ c) := by
    have h := PAG.Part16.normSq_gaussSum hχ
    rw [hsum, map_mul, hεn, mul_one, Complex.normSq_natCast] at h
    rw [← Real.sqrt_mul_self (Nat.cast_nonneg (S.card : ℕ))]
    congr 1; rw [h]; push_cast; ring
  refine ⟨u₀, hunit, ?_⟩
  rw [hsum, ← hcard]
  have hS0 : (S.card : ℂ) ≠ 0 := by
    have : (S.card : ℝ) ≠ 0 := by rw [hcard]; exact (Real.sqrt_pos.mpr hpc).ne'
    exact_mod_cast this
  rw [show ((S.card : ℝ) : ℂ) = (S.card : ℂ) by push_cast; rfl, mul_div_cancel_left₀ _ hS0]

include hc in
/-- **4. 正確な位数**: ord(τ/√(p^c)) = lcm(ord χ(u₀), p^c)。 -/
theorem orderOf_gauss_even (hm : 1 ≤ m) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧
      orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ))
        = Nat.lcm (orderOf (χ u₀)) (p ^ c) := by
  obtain ⟨u₀, hu, hz⟩ := gauss_even_phase hc χ hχ
  refine ⟨u₀, hu, ?_⟩
  rw [hz]
  have hc1 : 1 ≤ c := by omega
  have hx := stdAddChar_pow_eq_one_iff (p := p) u₀ hu
  have hy : χ u₀ ^ (p ^ (c - 1) * (p - 1)) = 1 := by
    rw [← Nat.totient_prime_pow hp.out (by omega : 0 < c)]; exact chi_pow_totient χ u₀ hu
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [mul_pow]
    obtain ⟨a, ha⟩ := Nat.dvd_lcm_left (orderOf (χ u₀)) (p ^ c)
    obtain ⟨b, hb⟩ := Nat.dvd_lcm_right (orderOf (χ u₀)) (p ^ c)
    rw [show stdAddChar u₀ ^ Nat.lcm (orderOf (χ u₀)) (p ^ c) = 1 from (hx _).mpr (Nat.dvd_lcm_right _ _),
      mul_one, ha, pow_mul, pow_orderOf_eq_one, one_pow]
  · have hz1 := pow_orderOf_eq_one (χ u₀ * stdAddChar u₀)
    have hpd := pdvd_of_mul c hc1 _ _ hx hy _ hz1
    have he : stdAddChar u₀ ^ orderOf (χ u₀ * stdAddChar u₀) = 1 := (hx _).mpr hpd
    have hχ1 : χ u₀ ^ orderOf (χ u₀ * stdAddChar u₀) = 1 := by
      have := hz1; rw [mul_pow, he, mul_one] at this; exact this
    exact Nat.lcm_dvd (orderOf_dvd_of_pow_eq_one hχ1) hpd

include hc in
/-- 系: p^c ∣ ord z ∣ lcm(ord χ, p^c)。 -/
theorem orderOf_gauss_even_bounds (hm : 1 ≤ m) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    p ^ c ∣ orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ∧
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ∣ Nat.lcm (orderOf χ) (p ^ c) := by
  obtain ⟨u₀, hu, ho⟩ := orderOf_gauss_even hc hm χ hχ
  rw [ho]
  have h1 : orderOf (χ u₀) ∣ orderOf χ := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← MulChar.pow_apply' _ (orderOf_pos χ).ne', pow_orderOf_eq_one]; exact MulChar.one_apply hu
  exact ⟨Nat.dvd_lcm_right _ _, Nat.lcm_dvd (h1.trans (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _)⟩

end Even

end PAG.Part127

#print axioms PAG.Part127.stdAddChar_pow_eq_one_iff
#print axioms PAG.Part127.chi_pow_totient
#print axioms PAG.Part127.pdvd_of_mul
#print axioms PAG.Part127.gauss_even_phase
#print axioms PAG.Part127.orderOf_gauss_even
#print axioms PAG.Part127.orderOf_gauss_even_bounds
