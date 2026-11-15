/-
  PAG 2.0 Part 150（2026-10-22）— 位数の p と素な部分: 停留点・周波数による明示
  導手 p^c（c = 2m、m ≥ 1）、χ 原始、z = τ/√(p^c)
  1. 停留集合 S の任意の単元 u₀ で z = χ(u₀) e(u₀)
  2. ord(χ(u₀) e(u₀)) = lcm(ord χ(u₀), p^c)
  3. x^{p^{c−1}(p−1)} = 1 ⇒ lcm(ord x, p^c) = p^c · ord(x^{p^{c−1}})
  4. u ≡ v (mod p) の単元なら u^{p^{c−1}} = v^{p^{c−1}}（1 + pℤ の位数は p^{c−1}）
  5. 位数の公式: ord z = p^c · ord(χ(−δ)^{p^{c−1}})（δ は χ の周波数）
-/
import PAG153

namespace PAG.Part154

open ZMod Finset PAG.Part118 PAG.Part127

variable {p : ℕ} [hp : Fact p.Prime]

section Even

variable {c m : ℕ} (hc : c = 2 * m)

include hc in
/-- **1. 停留集合の任意の単元で z = χ(u₀) e(u₀)**。 -/
theorem phase_of_S (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) (u₀ : ZMod (p ^ c))
    (hunit : IsUnit u₀) (hS₀ : ∀ y, phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u₀ * y) = 1) :
    gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ) = χ u₀ * stdAddChar u₀ := by
  classical
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set P := (p : ZMod (p ^ c)) ^ m
  set S := univ.filter (fun u : ZMod (p ^ c) => ∀ y, phi (m := m) χ y * stdAddChar (P * u * y) = 1)
  have hτ := gauss_eq_sum_S (p := p) hc χ
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
  rw [hsum, ← hcard]
  have hS0 : (S.card : ℂ) ≠ 0 := by
    have : (S.card : ℝ) ≠ 0 := by rw [hcard]; exact (Real.sqrt_pos.mpr hpc).ne'
    exact_mod_cast this
  rw [show ((S.card : ℝ) : ℂ) = (S.card : ℂ) by push_cast; rfl, mul_div_cancel_left₀ _ hS0]


end Even

/-- **2. ord(χ(u₀) e(u₀)) = lcm(ord χ(u₀), p^c)**（c ≥ 1）。 -/
theorem ord_of_phase {c : ℕ} (hc1 : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (u₀ : ZMod (p ^ c)) (hu : IsUnit u₀) :
    orderOf (χ u₀ * stdAddChar u₀) = Nat.lcm (orderOf (χ u₀)) (p ^ c) := by
  have hx := stdAddChar_pow_eq_one_iff (p := p) u₀ hu
  have hy : χ u₀ ^ (p ^ (c - 1) * (p - 1)) = 1 := by
    rw [← Nat.totient_prime_pow hp.out (by omega : 0 < c)]; exact chi_pow_totient χ u₀ hu
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [mul_pow]
    obtain ⟨a, ha⟩ := Nat.dvd_lcm_left (orderOf (χ u₀)) (p ^ c)
    rw [show stdAddChar u₀ ^ Nat.lcm (orderOf (χ u₀)) (p ^ c) = 1 from (hx _).mpr (Nat.dvd_lcm_right _ _),
      mul_one, ha, pow_mul, pow_orderOf_eq_one, one_pow]
  · have hz1 := pow_orderOf_eq_one (χ u₀ * stdAddChar u₀)
    have hpd := pdvd_of_mul c hc1 _ _ hx hy _ hz1
    have he : stdAddChar u₀ ^ orderOf (χ u₀ * stdAddChar u₀) = 1 := (hx _).mpr hpd
    have hχ1 : χ u₀ ^ orderOf (χ u₀ * stdAddChar u₀) = 1 := by
      have := hz1; rw [mul_pow, he, mul_one] at this; exact this
    exact Nat.lcm_dvd (orderOf_dvd_of_pow_eq_one hχ1) hpd

/-- **3. lcm(ord x, p^c) = p^c · ord(x^{p^{c−1}})**。 -/
theorem lcm_tame (c : ℕ) (hc1 : 1 ≤ c) (x : ℂ) (hx : x ^ (p ^ (c - 1) * (p - 1)) = 1) :
    Nat.lcm (orderOf x) (p ^ c) = p ^ c * orderOf (x ^ (p ^ (c - 1))) := by
  have hpos : 0 < p ^ (c - 1) * (p - 1) := Nat.mul_pos (pow_pos hp.out.pos _) (by have := hp.out.two_le; omega)
  have ho0 : orderOf x ≠ 0 := (orderOf_pos_iff.mpr ((isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hpos, hx⟩))).ne'
  obtain ⟨j, r, hr, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho0 p hp.out.ne_one
  have hdvd : orderOf x ∣ p ^ (c - 1) * (p - 1) := orderOf_dvd_of_pow_eq_one hx
  have hcopr : Nat.Coprime r p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hr))
  have hcop1 : Nat.Coprime (p ^ j) (p - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro h; have h2 := hp.out.two_le; have := Nat.le_of_dvd (by omega) h; omega
  have hj : j ≤ c - 1 := by
    have h1 : p ^ j ∣ p ^ (c - 1) * (p - 1) := (Dvd.intro _ hor.symm).trans hdvd
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp (hcop1.dvd_of_dvd_mul_right h1)
  -- ord(x^{p^{c−1}}) = r
  have hord : orderOf (x ^ (p ^ (c - 1))) = r := by
    rw [orderOf_pow' _ (pow_ne_zero _ hp.out.ne_zero), hor]
    have hg : Nat.gcd (p ^ j * r) (p ^ (c - 1)) = p ^ j := by
      rw [Nat.Coprime.gcd_mul_right_cancel _ (Nat.Coprime.pow_right _ hcopr)]
      exact Nat.gcd_eq_left (pow_dvd_pow p hj)
    rw [hg, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos j)]
  rw [hord, hor]
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · exact Nat.mul_dvd_mul (pow_dvd_pow p (by omega)) dvd_rfl
    · exact dvd_mul_right _ _
  · have hcop : Nat.Coprime (p ^ c) r := Nat.Coprime.pow_left c (Nat.coprime_comm.mp hcopr)
    exact hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_right _ _) ((dvd_mul_left r (p ^ j)).trans (Nat.dvd_lcm_left _ _))

/-- 1 + pℤ（単元）の位数は p^{c−1}。 -/
theorem card_ker_unitsMap (c : ℕ) (hc1 : 1 ≤ c) :
    Nat.card (ZMod.unitsMap (dvd_pow_self p (by omega : c ≠ 0))).ker = p ^ (c - 1) := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set f := ZMod.unitsMap (n := p) (m := p ^ c) (dvd_pow_self p (by omega : c ≠ 0))
  have hsurj : Function.Surjective f := ZMod.unitsMap_surjective _
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top] at h1
  have hG : Nat.card (ZMod (p ^ c))ˣ = Nat.totient (p ^ c) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hH : Nat.card (ZMod p)ˣ = Nat.totient p := by
    have : NeZero p := ⟨hp.out.ne_zero⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [hH, hG, Nat.totient_prime_pow hp.out (by omega), Nat.totient_prime hp.out] at h1
  exact Nat.eq_of_mul_eq_mul_right (by have := hp.out.two_le; omega) h1

/-- **4. u ≡ v (mod p) なら u^{p^{c−1}} = v^{p^{c−1}}**。 -/
theorem pow_eq_of_cast_eq (c : ℕ) (hc1 : 1 ≤ c) (u v : (ZMod (p ^ c))ˣ)
    (h : ((u : ZMod (p ^ c)).cast : ZMod p) = ((v : ZMod (p ^ c)).cast : ZMod p)) :
    u ^ (p ^ (c - 1)) = v ^ (p ^ (c - 1)) := by
  set f := ZMod.unitsMap (n := p) (m := p ^ c) (dvd_pow_self p (by omega : c ≠ 0))
  have hw : u * v⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.unitsMap_val]; exact h
  have hpow := pow_card_eq_one' (G := f.ker) (x := ⟨u * v⁻¹, hw⟩)
  rw [card_ker_unitsMap c hc1] at hpow
  have e := congrArg Subtype.val hpow
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at e
  rw [mul_pow, inv_pow, mul_inv_eq_one] at e
  exact e

/-- χ(u)^{p^{c−1}} は u mod p だけで決まる。 -/
theorem chi_pow_of_cast_eq (c : ℕ) (hc1 : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (u v : ZMod (p ^ c))
    (hu : IsUnit u) (hv : IsUnit v) (h : (u.cast : ZMod p) = (v.cast : ZMod p)) :
    χ u ^ (p ^ (c - 1)) = χ v ^ (p ^ (c - 1)) := by
  have e := pow_eq_of_cast_eq c hc1 hu.unit hv.unit (by rw [IsUnit.unit_spec, IsUnit.unit_spec]; exact h)
  rw [← map_pow, ← map_pow, ← hu.unit_spec, ← hv.unit_spec, ← Units.val_pow_eq_pow_val,
    ← Units.val_pow_eq_pow_val, e]

/-- **5. 位数の公式**: ord z = p^c · ord(χ(−δ)^{p^{c−1}})（導手 p^{2m}）。 -/
theorem orderOf_gauss_freq {c m : ℕ} (hc : c = 2 * m) (hm : 1 ≤ m) (χ : DirichletCharacter ℂ (p ^ c))
    (hχ : χ.IsPrimitive) (δ : ZMod (p ^ c))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ m * y) = stdAddChar ((p : ZMod (p ^ c)) ^ m * δ * y)) :
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ))
      = p ^ c * orderOf (χ (-δ) ^ (p ^ (c - 1))) := by
  have hc1 : 1 ≤ c := by omega
  obtain ⟨u₀, hu, hS₀⟩ := PAG.Part138.exists_stationary (p := p) hc χ hχ
  have hz := phase_of_S hc χ hχ u₀ hu hS₀
  -- S の条件を phiP の形へ
  have hS' : ∀ y, PAG.Part120.phiP χ ((p : ZMod (p ^ c)) ^ m) y
      * stdAddChar ((p : ZMod (p ^ c)) ^ m * u₀ * y) = 1 := fun y => hS₀ y
  have hcast := PAG.Part142.stationary_cast (p := p) (k := m) (by omega) χ δ hδ u₀ hS'
  have hδu : IsUnit δ := (PAG.Part142.primitive_iff_freq (p := p) (k := m) (by omega) (by omega) χ δ hδ).mp hχ
  rw [hz, ord_of_phase hc1 χ u₀ hu]
  have hy : χ u₀ ^ (p ^ (c - 1) * (p - 1)) = 1 := by
    rw [← Nat.totient_prime_pow hp.out (by omega : 0 < c)]; exact chi_pow_totient χ u₀ hu
  rw [lcm_tame c hc1 _ hy, chi_pow_of_cast_eq c hc1 χ u₀ (-δ) hu hδu.neg hcast]

end PAG.Part154

#print axioms PAG.Part154.phase_of_S
#print axioms PAG.Part154.ord_of_phase
#print axioms PAG.Part154.lcm_tame
#print axioms PAG.Part154.card_ker_unitsMap
#print axioms PAG.Part154.pow_eq_of_cast_eq
#print axioms PAG.Part154.chi_pow_of_cast_eq
#print axioms PAG.Part154.orderOf_gauss_freq
