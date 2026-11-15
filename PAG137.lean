/-
  PAG 2.0 Part 133（2026-10-21）— 積の位数の p 部分: 超距離的な最大値と、打ち消しの判定式
  A, B ∈ ℂ（有限位数）、ord A の p 部分 p^a ちょうど、ord B の p 部分 p^E ちょうど
  1. a < E ⇒ ord(AB) の p 部分は p^E ちょうど（a > E も対称）
  2. a = E ⇒ ord(AB) の p 部分は p^E 以下
  3. 判定式: lcm(ord A, ord B) = p^E M'（p ∤ M'、E ≥ 1）なら
     p^E ∣ ord(AB) ↔ (AB)^{p^{E−1} M'} ≠ 1
  4. 桁 A^N, B^N（N = p^{E−1}M'）は p 乗根、p^E ∣ ord A なら A^N ≠ 1、判定は A^N B^N ≠ 1
  5. p = 2 では a = E ≥ 1 のとき必ず打ち消す（桁はともに −1）
-/
import PAG136

namespace PAG.Part137

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- 上界: p^{E+1} ∤ ord A、p^{E+1} ∤ ord B ⇒ p^{E+1} ∤ ord(AB)。 -/
theorem not_pow_dvd_mul (A B : ℂ) (hA0 : orderOf A ≠ 0) (hB0 : orderOf B ≠ 0) (E : ℕ)
    (hA : ¬ p ^ (E + 1) ∣ orderOf A) (hB : ¬ p ^ (E + 1) ∣ orderOf B) : ¬ p ^ (E + 1) ∣ orderOf (A * B) := by
  intro h
  rcases PAG.Part134.pow_dvd_lcm_two hp.out hA0 hB0 (h.trans (Commute.all A B).orderOf_mul_dvd_lcm) with h' | h'
  · exact hA h'
  · exact hB h'

/-- **1. a < E ⇒ ord(AB) の p 部分は p^E ちょうど**。 -/
theorem ppart_mul_lt (A B : ℂ) (hA0 : orderOf A ≠ 0) (hB0 : orderOf B ≠ 0) (a E : ℕ) (haE : a < E)
    (hA' : ¬ p ^ (a + 1) ∣ orderOf A) (hB : p ^ E ∣ orderOf B) (hB' : ¬ p ^ (E + 1) ∣ orderOf B) :
    p ^ E ∣ orderOf (A * B) ∧ ¬ p ^ (E + 1) ∣ orderOf (A * B) := by
  refine ⟨PAG.Part131.pdvd_orderOf_mul p E A B hB (orderOf A) hA0 (pow_orderOf_eq_one A)
    (fun h => hA' ((pow_dvd_pow p (by omega)).trans h)), ?_⟩
  exact not_pow_dvd_mul A B hA0 hB0 E (fun h => hA' ((pow_dvd_pow p (by omega)).trans h)) hB'

/-- **2. a = E ⇒ p 部分は p^E 以下**。 -/
theorem ppart_mul_eq (A B : ℂ) (hA0 : orderOf A ≠ 0) (hB0 : orderOf B ≠ 0) (E : ℕ)
    (hA' : ¬ p ^ (E + 1) ∣ orderOf A) (hB' : ¬ p ^ (E + 1) ∣ orderOf B) :
    ¬ p ^ (E + 1) ∣ orderOf (A * B) :=
  not_pow_dvd_mul A B hA0 hB0 E hA' hB'

/-- 補題: o ∣ p^E M'、p ∤ M'、p^E ∤ o（o ≠ 0、E ≥ 1）⇒ o ∣ p^{E−1} M'。 -/
theorem dvd_pred_of_not (o E M' : ℕ) (hE : 1 ≤ E) (ho0 : o ≠ 0) (hM' : ¬ p ∣ M') (h : o ∣ p ^ E * M')
    (hn : ¬ p ^ E ∣ o) : o ∣ p ^ (E - 1) * M' := by
  obtain ⟨j, o', ho', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho0 p hp.out.ne_one
  have hcop1 : Nat.Coprime o' (p ^ E) :=
    (Nat.Coprime.pow_left E ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr ho')).symm
  have h1 : o' ∣ M' := hcop1.dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans h)
  have hcop2 : Nat.Coprime (p ^ j) M' := Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hM')
  have h2 : p ^ j ∣ p ^ E := hcop2.dvd_of_dvd_mul_right ((Dvd.intro _ rfl).trans h)
  have hj : j ≤ E := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h2
  have hj' : j ≠ E := fun he => hn (he ▸ Dvd.intro _ rfl)
  exact Nat.mul_dvd_mul (pow_dvd_pow p (by omega)) h1

/-- **3. 打ち消しの判定式**。 -/
theorem ppart_mul_criterion (A B : ℂ) (E M' : ℕ) (hE : 1 ≤ E) (hM' : ¬ p ∣ M')
    (hlcm : Nat.lcm (orderOf A) (orderOf B) = p ^ E * M') :
    p ^ E ∣ orderOf (A * B) ↔ (A * B) ^ (p ^ (E - 1) * M') ≠ 1 := by
  have hdvd : orderOf (A * B) ∣ p ^ E * M' := hlcm ▸ (Commute.all A B).orderOf_mul_dvd_lcm
  have hM0 : M' ≠ 0 := fun h0 => hM' (h0 ▸ dvd_zero p)
  have hN0 : p ^ E * M' ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) hM0
  have ho0 : orderOf (A * B) ≠ 0 := fun h0 => hN0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  constructor
  · intro h h1
    have h2 := h.trans (orderOf_dvd_of_pow_eq_one h1)
    have hcop : Nat.Coprime (p ^ E) M' := Nat.Coprime.pow_left E ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hM')
    have h3 := hcop.dvd_of_dvd_mul_right h2
    have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h3
    omega
  · intro h
    by_contra hn
    exact h (orderOf_dvd_iff_pow_eq_one.mp (dvd_pred_of_not _ E M' hE ho0 hM' hdvd hn))

omit hp in
/-- **4a. 判定式の「桁」は p 乗根**: (A^{p^{E−1} M'})^p = 1。 -/
theorem digit_pow_p (A B : ℂ) (E M' : ℕ) (hE : 1 ≤ E)
    (hlcm : Nat.lcm (orderOf A) (orderOf B) = p ^ E * M') :
    (A ^ (p ^ (E - 1) * M')) ^ p = 1 := by
  rw [← pow_mul, show p ^ (E - 1) * M' * p = p ^ E * M' by
    rw [show p ^ E = p ^ (E - 1) * p by rw [← pow_succ]; congr 1; omega]; ring]
  exact orderOf_dvd_iff_pow_eq_one.mp (hlcm ▸ Nat.dvd_lcm_left _ _)

/-- **4b. p^E ∣ ord A なら桁は 1 でない**。 -/
theorem digit_ne_one (A : ℂ) (E M' : ℕ) (hE : 1 ≤ E) (hM' : ¬ p ∣ M') (hA : p ^ E ∣ orderOf A) :
    A ^ (p ^ (E - 1) * M') ≠ 1 := by
  intro h1
  have h2 := hA.trans (orderOf_dvd_of_pow_eq_one h1)
  have hcop : Nat.Coprime (p ^ E) M' := Nat.Coprime.pow_left E ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hM')
  have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp (hcop.dvd_of_dvd_mul_right h2)
  omega

/-- **4c. 桁による判定**: p^E ∣ ord(AB) ↔ A^N B^N ≠ 1（N = p^{E−1} M'）。 -/
theorem ppart_mul_digit (A B : ℂ) (E M' : ℕ) (hE : 1 ≤ E) (hM' : ¬ p ∣ M')
    (hlcm : Nat.lcm (orderOf A) (orderOf B) = p ^ E * M') :
    p ^ E ∣ orderOf (A * B) ↔ A ^ (p ^ (E - 1) * M') * B ^ (p ^ (E - 1) * M') ≠ 1 := by
  rw [← mul_pow]; exact ppart_mul_criterion A B E M' hE hM' hlcm

/-- **5. p = 2 では a = E ≥ 1 のとき必ず打ち消す**: 2^E ∤ ord(AB)。 -/
theorem two_always_cancel (A B : ℂ) (E M' : ℕ) (hE : 1 ≤ E) (hM' : ¬ 2 ∣ M')
    (hlcm : Nat.lcm (orderOf A) (orderOf B) = 2 ^ E * M')
    (hA : 2 ^ E ∣ orderOf A) (hB : 2 ^ E ∣ orderOf B) : ¬ 2 ^ E ∣ orderOf (A * B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ x : ℂ, x ^ 2 = 1 → x ≠ 1 → x = -1 := by
    intro x hx hx1
    have : (x - 1) * (x + 1) = 0 := by ring_nf; rw [hx]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hx1
    · exact eq_neg_of_add_eq_zero_left h
  have hA1 := key _ (digit_pow_p (p := 2) A B E M' hE hlcm) (digit_ne_one (p := 2) A E M' hE hM' hA)
  have hB1 := key _ (digit_pow_p (p := 2) B A E M' hE (by rw [Nat.lcm_comm]; exact hlcm))
    (digit_ne_one (p := 2) B E M' hE hM' hB)
  rw [ppart_mul_digit (p := 2) A B E M' hE hM' hlcm, hA1, hB1]
  norm_num

end PAG.Part137

#print axioms PAG.Part137.not_pow_dvd_mul
#print axioms PAG.Part137.ppart_mul_lt
#print axioms PAG.Part137.ppart_mul_eq
#print axioms PAG.Part137.dvd_pred_of_not
#print axioms PAG.Part137.ppart_mul_criterion
#print axioms PAG.Part137.digit_pow_p
#print axioms PAG.Part137.digit_ne_one
#print axioms PAG.Part137.ppart_mul_digit
#print axioms PAG.Part137.two_always_cancel
