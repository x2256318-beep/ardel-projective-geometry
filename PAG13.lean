/-
  PAG 2.0 Part 9（2026-10-18）— 導手公式の馴部分: 位数の分解と「導手 1 に落ちる」条件
  p 奇素数、χ が法 p^(n+1) で原始的のとき
    ord(χ) = p^n · d、d ∣ p − 1（d = 馴分の位数、gcd(d, p) = 1）
    gcd(m, p) = 1 なら  χ^(p^r m) = 1 ⇔ n ≤ r ∧ d ∣ m
  これで Part 6 の公式 c_N = c − r / 1 / 0 の三つの場合が、d を用いた形のまま形式化される。
-/
import PAG12

namespace PAG.Part13

variable {p n : ℕ} [hp : Fact p.Prime]

/-- χ^(φ(p^(n+1))) = 1、すなわち χ^(p^n (p−1)) = 1。 -/
theorem pow_totient_eq_one (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    χ ^ (p ^ n * (p - 1)) = 1 := by
  apply MulChar.ext
  intro a
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
    ← Nat.totient_prime_pow_succ hp.out, ZMod.pow_totient, Units.val_one, map_one]

/-- 位数は p^n (p − 1) を割る。 -/
theorem orderOf_dvd_totient (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    orderOf χ ∣ p ^ n * (p - 1) :=
  orderOf_dvd_of_pow_eq_one (pow_totient_eq_one χ)

theorem orderOf_ne_zero (χ : DirichletCharacter ℂ (p ^ (n + 1))) : orderOf χ ≠ 0 := by
  intro h
  have := orderOf_dvd_totient χ
  rw [h, zero_dvd_iff] at this
  exact absurd this (Nat.mul_ne_zero (pow_ne_zero n hp.out.ne_zero) (by have := hp.out.two_le; omega))

/-- **野生部分の位数**: χ 原始的（p 奇素数）なら p^n は ord(χ) を割る。 -/
theorem pow_dvd_orderOf (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : p ^ n ∣ orderOf χ := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_ne_zero χ) p hp.out.ne_one
  rcases Nat.lt_or_ge e n with h | h
  · exfalso
    have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm).symm
    have h1 : χ ^ (p ^ e * m) = 1 := by rw [← he]; exact pow_orderOf_eq_one χ
    have h2 := PAG.Part12.conductor_pow_pr hodd hn (r := e) (by omega) hcop χ hχ
    rw [h1, DirichletCharacter.conductor_one] at h2
    have : 1 < p ^ (n + 1 - e) := Nat.one_lt_pow (by omega) hp.out.one_lt
    omega
  · rw [he]; exact (pow_dvd_pow p h).trans (dvd_mul_right _ _)

/-- 馴分の位数 d := ord(χ) / p^n。 -/
noncomputable def tameOrder (χ : DirichletCharacter ℂ (p ^ (n + 1))) : ℕ := orderOf χ / p ^ n

/-- **位数の分解**: ord(χ) = p^n · d。 -/
theorem orderOf_eq (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    orderOf χ = p ^ n * tameOrder χ :=
  (Nat.mul_div_cancel' (pow_dvd_orderOf hodd χ hχ)).symm

/-- d ∣ p − 1。 -/
theorem tameOrder_dvd (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    tameOrder χ ∣ p - 1 := by
  have h := orderOf_dvd_totient χ
  rw [orderOf_eq hodd χ hχ] at h
  exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos n) h

/-- gcd(d, p) = 1。 -/
theorem tameOrder_coprime (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : Nat.Coprime (tameOrder χ) p := by
  have hc : Nat.Coprime (p - 1) p := by
    have : p = (p - 1) + 1 := by have := hp.out.one_lt; omega
    conv_rhs => rw [this]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  exact Nat.Coprime.coprime_dvd_left (tameOrder_dvd hodd χ hχ) hc

/-- **自明になる条件**: gcd(m, p) = 1 なら χ^(p^r m) = 1 ⇔ n ≤ r ∧ d ∣ m。 -/
theorem pow_eq_one_iff (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive)
    {r m : ℕ} (hcop : Nat.Coprime m p) :
    χ ^ (p ^ r * m) = 1 ↔ n ≤ r ∧ tameOrder χ ∣ m := by
  rw [← orderOf_dvd_iff_pow_eq_one, orderOf_eq hodd χ hχ]
  constructor
  · intro h
    have h1 : p ^ n ∣ p ^ r * m := (dvd_mul_right _ _).trans h
    have hpm : Nat.Coprime (p ^ n) m := (Nat.Coprime.pow_left n hcop.symm)
    have h2 : p ^ n ∣ p ^ r := hpm.dvd_of_dvd_mul_right h1
    have h3 : tameOrder χ ∣ p ^ r * m := (dvd_mul_left _ _).trans h
    have hdp : Nat.Coprime (tameOrder χ) (p ^ r) := Nat.Coprime.pow_right r (tameOrder_coprime hodd χ hχ)
    exact ⟨(Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h2, hdp.dvd_of_dvd_mul_left h3⟩
  · rintro ⟨h1, h2⟩
    exact mul_dvd_mul (pow_dvd_pow p h1) h2

/-! ## 導手公式（三つの場合） -/

/-- (i) r < c − 1: cond = p^(c−r)。 -/
theorem conductor_wild (hodd : Odd p) (hn : 1 ≤ n) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) {r m : ℕ} (hcop : Nat.Coprime m p) (hr : r < n) :
    (χ ^ (p ^ r * m)).conductor = p ^ (n + 1 - r) :=
  PAG.Part12.conductor_pow_pr hodd hn (by omega) hcop χ hχ

/-- (ii) r ≥ c − 1 かつ d ∤ m: cond = p。 -/
theorem conductor_tame_one (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) {r m : ℕ} (hcop : Nat.Coprime m p) (hr : n ≤ r) (hd : ¬ tameOrder χ ∣ m) :
    (χ ^ (p ^ r * m)).conductor = p :=
  PAG.Part12.conductor_pow_pr_tame hodd hr m χ
    (fun h => hd ((pow_eq_one_iff hodd χ hχ hcop).mp h).2)

/-- (iii) r ≥ c − 1 かつ d ∣ m: cond = 1（χ^(p^r m) = 1）。 -/
theorem conductor_tame_zero (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) {r m : ℕ} (hcop : Nat.Coprime m p) (hr : n ≤ r) (hd : tameOrder χ ∣ m) :
    (χ ^ (p ^ r * m)).conductor = 1 := by
  rw [(pow_eq_one_iff hodd χ hχ hcop).mpr ⟨hr, hd⟩, DirichletCharacter.conductor_one]

end PAG.Part13

#print axioms PAG.Part13.pow_totient_eq_one
#print axioms PAG.Part13.orderOf_dvd_totient
#print axioms PAG.Part13.orderOf_ne_zero
#print axioms PAG.Part13.pow_dvd_orderOf
#print axioms PAG.Part13.orderOf_eq
#print axioms PAG.Part13.tameOrder_dvd
#print axioms PAG.Part13.tameOrder_coprime
#print axioms PAG.Part13.pow_eq_one_iff
#print axioms PAG.Part13.conductor_wild
#print axioms PAG.Part13.conductor_tame_one
#print axioms PAG.Part13.conductor_tame_zero
