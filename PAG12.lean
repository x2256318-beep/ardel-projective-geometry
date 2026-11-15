/-
  PAG 2.0 Part 8（2026-10-18）— 導手公式の野生部分の完全な形式化
  p 奇素数、χ が法 p^(n+1) で原始的（c = n + 1）、gcd(m, p) = 1 のとき
    r ≤ n − 1（r < c − 1）: cond(χ^(p^r m)) = p^(n+1−r) = p^(c−r)
    r ≥ n    （r ≥ c − 1）: χ^(p^r m) は p を経由する（cond ∣ p）。自明でなければ cond = p
  道具: 整数での「p 乗の持ち上げ」補題（LTE の初等版）
-/
import PAG11

namespace PAG.Part12

open Finset

/-! ## 1. 整数の持ち上げ補題 -/

section Int

variable {p : ℕ}

/-- (1 + d)^p = 1 + p d + Σ_{m < p−1} C(p, m+2) d^(m+2)（p ≥ 2）。 -/
theorem one_add_pow_expand (hp2 : 2 ≤ p) (d : ℤ) :
    (1 + d) ^ p = 1 + p * d + ∑ m ∈ range (p - 1), d ^ (m + 2) * (p.choose (m + 2) : ℤ) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  rw [add_comm (1 : ℤ) d, add_pow, sum_range_succ', sum_range_succ']
  simp only [show q + 2 - 1 = q + 1 by omega, one_pow, mul_one, pow_zero, Nat.choose_zero_right,
    zero_add, Nat.choose_one_right, Nat.cast_one]
  push_cast
  ring

/-- **鍵の補題**: p 奇素数、k ≥ 1、p^k ∣ d ⇒ p^(k+2) ∣ (1 + d)^p − 1 − p d。 -/
theorem key_binom (hp : p.Prime) (hodd : Odd p) {k : ℕ} (hk : 1 ≤ k) (d : ℤ)
    (hd : (p : ℤ) ^ k ∣ d) : (p : ℤ) ^ (k + 2) ∣ (1 + d) ^ p - 1 - p * d := by
  rw [one_add_pow_expand hp.two_le d, show ∀ a b : ℤ, 1 + a + b - 1 - a = b by intros; ring]
  apply Finset.dvd_sum
  intro m _
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0
    have h22 : p.choose 2 * 2 = p * (p - 1) := by
      rw [Nat.choose_two_right]; exact Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
    have hc : p ∣ p.choose 2 :=
      (Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_right (h22 ▸ Dvd.intro _ rfl)
    have h1 : (p : ℤ) ^ (2 * k) ∣ d ^ 2 := by rw [pow_mul']; exact pow_dvd_pow_of_dvd hd 2
    have h2 : (p : ℤ) ∣ (p.choose 2 : ℤ) := Int.natCast_dvd_natCast.mpr hc
    have h3 : (p : ℤ) ^ (2 * k + 1) ∣ d ^ (0 + 2) * (p.choose (0 + 2) : ℤ) := by
      rw [pow_succ]; exact mul_dvd_mul h1 h2
    exact (pow_dvd_pow (p : ℤ) (by omega)).trans h3
  · have h1 : (p : ℤ) ^ (k * (m + 2)) ∣ d ^ (m + 2) := by
      rw [pow_mul]; exact pow_dvd_pow_of_dvd hd _
    have : k + 2 ≤ k * (m + 2) := by nlinarith
    exact ((pow_dvd_pow (p : ℤ) this).trans h1).mul_right _

/-- x − 1 = p^k t（k ≥ 1）⇒ x^p − 1 = p^(k+1) t + p^(k+2) s。 -/
theorem pow_p_congr (hp : p.Prime) (hodd : Odd p) {k : ℕ} (hk : 1 ≤ k) (x t : ℤ)
    (hx : x - 1 = (p : ℤ) ^ k * t) : ∃ s, x ^ p - 1 = (p : ℤ) ^ (k + 1) * t + (p : ℤ) ^ (k + 2) * s := by
  have hd : (p : ℤ) ^ k ∣ x - 1 := ⟨t, hx⟩
  obtain ⟨s, hs⟩ := key_binom hp hodd hk (x - 1) hd
  refine ⟨s, ?_⟩
  rw [show (1 : ℤ) + (x - 1) = x by ring] at hs
  rw [pow_succ, hx] at *
  linear_combination hs

/-- **持ち上げの反復**: x − 1 = p^k t + p^(k+1) s₀（k ≥ 1）⇒ x^(p^r) − 1 = p^(k+r) t + p^(k+r+1) s。 -/
theorem pow_p_pow_congr (hp : p.Prime) (hodd : Odd p) {k : ℕ} (hk : 1 ≤ k) (x t s₀ : ℤ)
    (hx : x - 1 = (p : ℤ) ^ k * t + (p : ℤ) ^ (k + 1) * s₀) (r : ℕ) :
    ∃ s, x ^ (p ^ r) - 1 = (p : ℤ) ^ (k + r) * t + (p : ℤ) ^ (k + r + 1) * s := by
  induction r with
  | zero => exact ⟨s₀, by simpa using hx⟩
  | succ r ih =>
    obtain ⟨s, hs⟩ := ih
    have hy : x ^ (p ^ r) - 1 = (p : ℤ) ^ (k + r) * (t + p * s) := by rw [hs]; ring
    obtain ⟨s', hs'⟩ := pow_p_congr hp hodd (by omega) _ _ hy
    refine ⟨s + s', ?_⟩
    rw [pow_succ, pow_mul, hs']
    ring

/-- 上界版: p^k ∣ x − 1（k ≥ 1）⇒ p^(k+r) ∣ x^(p^r) − 1。 -/
theorem pow_p_pow_dvd (hp : p.Prime) (hodd : Odd p) {k : ℕ} (hk : 1 ≤ k) (x : ℤ)
    (hx : (p : ℤ) ^ k ∣ x - 1) (r : ℕ) : (p : ℤ) ^ (k + r) ∣ x ^ (p ^ r) - 1 := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨s, hs⟩ := pow_p_pow_congr hp hodd hk x t 0 (by rw [ht]; ring) r
  rw [hs]
  exact dvd_add (dvd_mul_right _ _) ((pow_dvd_pow _ (by omega)).trans (dvd_mul_right _ _))

end Int

/-! ## 2. 導手の厳密値 -/

section Cond

variable {p n : ℕ} [hp : Fact p.Prime]

/-- 単数 u が法 p^j（j ≥ 1、j + r ≥ n + 1）で 1 なら u^(p^r) = 1（法 p^(n+1)）。 -/
theorem zmod_pow_pr_eq_one (hodd : Odd p) {j r : ℕ} (hj : 1 ≤ j) (hjr : n + 1 ≤ j + r)
    (hdj : p ^ j ∣ p ^ (n + 1)) (u : ZMod (p ^ (n + 1)))
    (hu : ZMod.castHom hdj (ZMod (p ^ j)) u = 1) : u ^ (p ^ r) = 1 := by
  set x : ℤ := ((u.val : ℕ) : ℤ) with hxdef
  have hux : u = (x : ZMod (p ^ (n + 1))) := by rw [hxdef, Int.cast_natCast, ZMod.natCast_zmod_val]
  have h1 : ((x - 1 : ℤ) : ZMod (p ^ j)) = 0 := by
    rw [Int.cast_sub, Int.cast_one, sub_eq_zero, ← map_intCast (ZMod.castHom hdj (ZMod (p ^ j))),
      ← hux, hu]
  have h2 : ((p ^ j : ℕ) : ℤ) ∣ x - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1
  rw [Nat.cast_pow] at h2
  have h3 := pow_p_pow_dvd hp.out hodd hj x h2 r
  have h4 : ((p ^ (n + 1) : ℕ) : ℤ) ∣ x ^ (p ^ r) - 1 := by
    rw [Nat.cast_pow]; exact (pow_dvd_pow _ hjr).trans h3
  have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h4
  rw [Int.cast_sub, Int.cast_pow, Int.cast_one, sub_eq_zero, ← hux] at h5
  exact h5

/-- **上界**: r ≤ n なら任意の m で χ^(p^r m) は p^(n+1−r) を経由する。 -/
theorem pow_pr_factorsThrough (hodd : Odd p) {r : ℕ} (hr : r ≤ n) (m : ℕ)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    (χ ^ (p ^ r * m)).FactorsThrough (p ^ (n + 1 - r)) := by
  have hd : p ^ (n + 1 - r) ∣ p ^ (n + 1) := pow_dvd_pow p (by omega)
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ ^ (p ^ r * m)) hd]
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have hu' : ZMod.castHom hd (ZMod (p ^ (n + 1 - r))) (u : ZMod (p ^ (n + 1))) = 1 := by
    rw [ZMod.castHom_apply, ← ZMod.unitsMap_val hd, hu, Units.val_one]
  have hpow := zmod_pow_pr_eq_one hodd (r := r) (by omega) (by omega) hd _ hu'
  ext
  simp only [MulChar.coe_toUnitHom, Units.val_one]
  rw [MulChar.pow_apply_coe, pow_mul, ← map_pow, hpow, map_one, one_pow]

/-- **野生部分の消滅**: r ≥ n なら χ^(p^r m) は p を経由する（導手 ∣ p）。 -/
theorem pow_pr_factorsThrough_p (hodd : Odd p) {r : ℕ} (hr : n ≤ r) (m : ℕ)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) : (χ ^ (p ^ r * m)).FactorsThrough p := by
  have hd : p ^ 1 ∣ p ^ (n + 1) := pow_dvd_pow p (by omega)
  have h := (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ ^ (p ^ r * m)) hd).mpr ?_
  · simpa using h
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have hu' : ZMod.castHom hd (ZMod (p ^ 1)) (u : ZMod (p ^ (n + 1))) = 1 := by
    rw [ZMod.castHom_apply, ← ZMod.unitsMap_val hd, hu, Units.val_one]
  have hpow := zmod_pow_pr_eq_one hodd (r := r) le_rfl (by omega) hd _ hu'
  ext
  simp only [MulChar.coe_toUnitHom, Units.val_one]
  rw [MulChar.pow_apply_coe, pow_mul, ← map_pow, hpow, map_one, one_pow]

/-- **下界**: p 奇素数、χ 原始的、r ≤ n − 1、gcd(m, p) = 1 なら、j ≤ n − r の任意の j で
χ^(p^r m) は p^j を経由しない。 -/
theorem pow_pr_not_factorsThrough (hodd : Odd p) (hn : 1 ≤ n) {r : ℕ} (hr : r ≤ n - 1)
    {m : ℕ} (hcop : Nat.Coprime m p) (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive)
    {j : ℕ} (hj : j ≤ n - r) : ¬ (χ ^ (p ^ r * m)).FactorsThrough (p ^ j) := by
  obtain ⟨v, hker, hne⟩ := PAG.Part8.exists_ker_ne_one_of_primitive χ hχ
  have hd : p ^ n ∣ p ^ (n + 1) := pow_dvd_pow p (Nat.le_succ n)
  set e : ZMod (p ^ (n + 1)) := (v : ZMod (p ^ (n + 1))) - 1 with hedef
  have hc : ZMod.castHom hd (ZMod (p ^ n)) e = 0 := by
    rw [hedef, map_sub, map_one, ZMod.castHom_apply, ← ZMod.unitsMap_val hd, hker, Units.val_one,
      sub_self]
  have h1' : ((e.val : ℕ) : ZMod (p ^ n)) = 0 := by
    rw [← hc, ZMod.castHom_apply (h := hd), ZMod.cast_eq_val]
  obtain ⟨q, hq⟩ : p ^ n ∣ e.val := (ZMod.natCast_eq_zero_iff _ _).mp h1'
  -- d = p^n は d² = 0, p d = 0
  set D : ZMod (p ^ (n + 1)) := (p : ZMod (p ^ (n + 1))) ^ n with hD
  have hDD : D * D = 0 := by
    rw [hD, ← pow_add, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow p (by omega)
  have hpD : (p : ZMod (p ^ (n + 1))) * D = 0 := by
    rw [hD, ← pow_succ', ← Nat.cast_pow, ZMod.natCast_self]
  -- 整数 x = 1 + p^(n−r) の p^r 乗は 1 + p^n（法 p^(n+1)）
  obtain ⟨s, hs⟩ := pow_p_pow_congr hp.out hodd (k := n - r) (by omega) (1 + (p : ℤ) ^ (n - r)) 1 0
    (by ring) r
  set u₀ : ZMod (p ^ (n + 1)) := ((1 + (p : ℤ) ^ (n - r) : ℤ) : ZMod (p ^ (n + 1))) with hu₀
  have hw : u₀ ^ (p ^ r) = 1 + D := by
    have := congrArg (fun z : ℤ => (z : ZMod (p ^ (n + 1)))) hs
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_one, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, mul_one, show n - r + r = n by omega] at this
    have hz : ((p : ZMod (p ^ (n + 1))) ^ (n + 1)) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hz, zero_mul, add_zero, sub_eq_iff_eq_add] at this
    rw [hu₀]; push_cast; rw [this, hD]; ring
  -- w₀ = 1 + D は単数、w₀^q = v、w₀^p = 1
  have hwq : (1 + D) ^ q = v := by
    rw [PAG.Part9.one_add_pow_of_sq_zero D hDD q]
    have hv : (v : ZMod (p ^ (n + 1))) = 1 + e := by rw [hedef]; ring
    rw [hv, ← ZMod.natCast_zmod_val e, hq, hD]; push_cast; ring
  have hwp : (1 + D) ^ p = 1 := by
    rw [PAG.Part9.one_add_pow_of_sq_zero D hDD p, hpD, add_zero]
  have hwunit : IsUnit (1 + D) := isUnit_iff_exists_inv.mpr ⟨(1 + D) ^ (p - 1), by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, hwp]⟩
  have hu₀unit : IsUnit u₀ := by
    rw [← isUnit_pow_iff (pow_ne_zero r hp.out.ne_zero), hw]; exact hwunit
  -- u₀ は法 p^j で 1
  have hdj : p ^ j ∣ p ^ (n + 1) := pow_dvd_pow p (by omega)
  have hmem : hu₀unit.unit ∈ (ZMod.unitsMap hdj).ker := by
    rw [MonoidHom.mem_ker]
    ext
    rw [ZMod.unitsMap_val, IsUnit.unit_spec, Units.val_one]
    show ZMod.castHom hdj (ZMod (p ^ j)) u₀ = 1
    rw [hu₀, map_intCast]
    push_cast
    rw [← Nat.cast_pow, (ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow p (by omega)), add_zero]
  intro hft
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ ^ (p ^ r * m)) hdj] at hft
  have := hft hmem
  rw [MonoidHom.mem_ker] at this
  have h' := congrArg (fun w : ℂˣ => (w : ℂ)) this
  simp only [MulChar.coe_toUnitHom, Units.val_one] at h'
  -- z := χ(w₀) は z^m = 1, z^p = 1 ⇒ z = 1 ⇒ χ(v) = z^q = 1
  set z := χ (1 + D) with hz
  have hzm : z ^ m = 1 := by
    have hcoe : ((hu₀unit.unit : (ZMod (p ^ (n + 1)))ˣ) : ZMod (p ^ (n + 1))) = u₀ := IsUnit.unit_spec _
    rw [MulChar.pow_apply_coe, hcoe, pow_mul, ← map_pow, hw] at h'
    exact h'
  have hzp : z ^ p = 1 := by rw [hz, ← map_pow, hwp, map_one]
  have hz1 : z = 1 := PAG.Part10.eq_one_of_pow_coprime hcop hzm hzp
  apply hne
  rw [← hwq, map_pow, ← hz, hz1, one_pow]

/-- **系（導手公式の野生部分）**: r ≤ n − 1、gcd(m, p) = 1 なら cond(χ^(p^r m)) = p^(n+1−r)。 -/
theorem conductor_pow_pr (hodd : Odd p) (hn : 1 ≤ n) {r : ℕ} (hr : r ≤ n - 1)
    {m : ℕ} (hcop : Nat.Coprime m p) (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    (χ ^ (p ^ r * m)).conductor = p ^ (n + 1 - r) := by
  obtain ⟨k, hk, hkeq⟩ :=
    (Nat.dvd_prime_pow hp.out).mp (DirichletCharacter.conductor_dvd_level (χ ^ (p ^ r * m)))
  have hle : (χ ^ (p ^ r * m)).conductor ≤ p ^ (n + 1 - r) :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff _).mpr
      (pow_pr_factorsThrough hodd (by omega) m χ))
  rw [hkeq] at hle ⊢
  have hkn : k ≤ n + 1 - r := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hle
  have hft := DirichletCharacter.factorsThrough_conductor (χ ^ (p ^ r * m))
  rw [hkeq] at hft
  rcases Nat.lt_or_ge k (n + 1 - r) with h | h
  · exact absurd hft (pow_pr_not_factorsThrough hodd hn hr hcop χ hχ (by omega))
  · rw [show k = n + 1 - r by omega]

/-- 系（r ≥ n）: 導手は p を割る。 -/
theorem conductor_pow_pr_dvd_p (hodd : Odd p) {r : ℕ} (hr : n ≤ r) (m : ℕ)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) : (χ ^ (p ^ r * m)).conductor ∣ p :=
  DirichletCharacter.conductor_dvd_of_mem_conductorSet _
    ((DirichletCharacter.mem_conductorSet_iff _).mpr (pow_pr_factorsThrough_p hodd hr m χ))

/-- **馴部分の二分法（r ≥ n）**: χ^(p^r m) が自明でなければ導手はちょうど p
（自明なら導手 1: Mathlib の eq_one_iff_conductor_eq_one）。 -/
theorem conductor_pow_pr_tame (hodd : Odd p) {r : ℕ} (hr : n ≤ r) (m : ℕ)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (h : χ ^ (p ^ r * m) ≠ 1) :
    (χ ^ (p ^ r * m)).conductor = p := by
  rcases (Nat.dvd_prime hp.out).mp (conductor_pow_pr_dvd_p hodd hr m χ) with h1 | h1
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1) h
  · exact h1

end Cond

end PAG.Part12

#print axioms PAG.Part12.one_add_pow_expand
#print axioms PAG.Part12.key_binom
#print axioms PAG.Part12.pow_p_congr
#print axioms PAG.Part12.pow_p_pow_congr
#print axioms PAG.Part12.pow_p_pow_dvd
#print axioms PAG.Part12.zmod_pow_pr_eq_one
#print axioms PAG.Part12.pow_pr_factorsThrough
#print axioms PAG.Part12.pow_pr_factorsThrough_p
#print axioms PAG.Part12.pow_pr_not_factorsThrough
#print axioms PAG.Part12.conductor_pow_pr
#print axioms PAG.Part12.conductor_pow_pr_dvd_p
#print axioms PAG.Part12.conductor_pow_pr_tame
