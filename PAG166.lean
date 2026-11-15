/-
  PAG 2.0 Part 162（2026-10-22）— ガウスの符号決定（その 2）：多項式の係数比較
  P = Σ_{a<p} χ(a) X^a、Q = ∏_{a=1}^{m} (X^a − X^{p−a})（ℤ 係数、p = 2m+1）
  T(f) = (f mod p)(X + 1)
  1. T(Φ_p) = X^{p−1}
  2. m! · [X^m] T(P) = −1
  3. [X^m] T(Q) = 2^m m!
  4. (m!)² = (−1)^{m+1}（法 p）
  5. sign_from_poly: Φ_p ∣ P − ε Q ⇒ ε ≡ (−1)^m χ(2)（法 p）
-/
import PAG165
import Mathlib.NumberTheory.Wilson

namespace PAG.Part166

open Finset Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

/-- T(f) = (f mod p)(X + 1)。 -/
noncomputable def T (f : ℤ[X]) : (ZMod p)[X] := (f.map (Int.castRingHom (ZMod p))).comp (X + 1)

theorem T_mul (f g : ℤ[X]) : T p (f * g) = T p f * T p g := by
  unfold T; rw [Polynomial.map_mul, mul_comp]

theorem T_sub (f g : ℤ[X]) : T p (f - g) = T p f - T p g := by
  unfold T; rw [Polynomial.map_sub, sub_comp]

/-- **1. T(Φ_p) = X^{p−1}**。 -/
theorem T_cyclotomic : T p (cyclotomic p ℤ) = X ^ (p - 1) := by
  unfold T
  rw [map_cyclotomic]
  have h := cyclotomic_mul_prime_pow_eq (ZMod p) (p := p) (m := 1) (by
    rw [Nat.dvd_one]; exact hp.out.one_lt.ne') (k := 1) one_pos
  rw [pow_one, mul_one, pow_zero, cyclotomic_one] at h
  rw [h, pow_comp, sub_comp, X_comp, one_comp, add_sub_cancel_right]

/-- 和の付け替え：Σ_{a<p} f(a) = Σ_{x : ZMod p} f(x)。 -/
theorem sum_range_zmod {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ a ∈ range p, f (a : ZMod p) = ∑ x : ZMod p, f x := by
  apply Finset.sum_nbij' (i := fun a : ℕ => (a : ZMod p)) (j := fun x : ZMod p => x.val)
  · intro a _; exact Finset.mem_coe.mpr (mem_univ _)
  · intro x _; exact Finset.mem_coe.mpr (Finset.mem_range.mpr (ZMod.val_lt x))
  · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro a _; rfl

/-- **べき和**。 -/
theorem sum_pow_top : ∑ x : ZMod p, x ^ (p - 1) = -1 := by
  classical
  have h : ∀ x : ZMod p, x ^ (p - 1) = if x = 0 then 0 else 1 := by
    intro x
    split_ifs with hx
    · rw [hx]; exact zero_pow (by have := hp.out.two_le; omega)
    · exact ZMod.pow_card_sub_one_eq_one hx
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_ne' univ (0 : ZMod p),
    Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, ZMod.card]
  rw [Nat.cast_sub hp.out.one_le, ZMod.natCast_self]; simp

/-- **2. Σ_x x^m D(x) = −1**（D は m 次の下降階乗の多項式、p = 2m+1）。 -/
theorem sum_desc (m : ℕ) (hpm : p = 2 * m + 1) :
    ∑ x : ZMod p, x ^ m * (descPochhammer (ZMod p) m).eval x = -1 := by
  set D := descPochhammer (ZMod p) m
  have hdeg : D.natDegree = m := descPochhammer_natDegree (ZMod p) m
  have hmon : D.coeff m = 1 := by
    have := monic_descPochhammer (R := ZMod p) m
    rw [Monic, leadingCoeff, hdeg] at this; exact this
  have hev : ∀ x : ZMod p, D.eval x = ∑ k ∈ range (m + 1), D.coeff k * x ^ k := by
    intro x; rw [eval_eq_sum_range' (by omega : D.natDegree < m + 1)]
  simp_rw [hev, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_range_succ]
  have hlow : ∀ k ∈ range m, ∑ x : ZMod p, x ^ m * (D.coeff k * x ^ k) = 0 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [show (∑ x : ZMod p, x ^ m * (D.coeff k * x ^ k)) = D.coeff k * ∑ x : ZMod p, x ^ (m + k) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring]
    rw [FiniteField.sum_pow_lt_card_sub_one (ZMod p) (m + k) (by rw [ZMod.card]; omega), mul_zero]
  rw [Finset.sum_eq_zero hlow, zero_add, hmon]
  rw [show (∑ x : ZMod p, x ^ m * (1 * x ^ m)) = ∑ x : ZMod p, x ^ (p - 1) by
    apply Finset.sum_congr rfl; intro x _; rw [show p - 1 = m + m by omega]; ring]
  exact sum_pow_top p

/-- ℤ 係数の P。 -/
noncomputable def Pz : ℤ[X] := ∑ a ∈ range p, C (quadraticChar (ZMod p) (a : ZMod p)) * X ^ a

/-- ℤ 係数の Q。 -/
noncomputable def Qz (m : ℕ) : ℤ[X] := ∏ a ∈ Ico 1 (m + 1), (X ^ a - X ^ (p - a))

/-- **2'. m! · [X^m] T(P) = −1**。 -/
theorem coeff_TP (m : ℕ) (hpm : p = 2 * m + 1) : (m.factorial : ZMod p) * (T p (Pz p)).coeff m = -1 := by
  have hp2 : p ≠ 2 := by omega
  have hTP : T p (Pz p) = ∑ a ∈ range p, C ((quadraticChar (ZMod p) (a : ZMod p) : ℤ) : ZMod p) * (X + 1) ^ a := by
    unfold T Pz
    simp [Polynomial.map_sum, Polynomial.sum_comp, mul_comp, pow_comp]
  rw [hTP, Polynomial.finsetSum_coeff, Finset.mul_sum]
  simp_rw [coeff_C_mul, coeff_X_add_one_pow]
  have e : ∀ a ∈ range p, (m.factorial : ZMod p) * (((quadraticChar (ZMod p) (a : ZMod p) : ℤ) : ZMod p) * (a.choose m : ZMod p))
      = (a : ZMod p) ^ m * (descPochhammer (ZMod p) m).eval (a : ZMod p) := by
    intro a _
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
      quadraticChar_eq_pow_of_char_ne_two' (PAG.Part119.ringChar_ne_two hp2), ZMod.card,
      show p / 2 = m by omega]
    push_cast; ring
  rw [Finset.sum_congr rfl e, sum_range_zmod p (fun x => x ^ m * (descPochhammer (ZMod p) m).eval x)]
  exact sum_desc p m hpm

/-- **3a. 定数項 0 の多項式の積の係数**：[X^{|s|}] ∏ F_i = ∏ [X^1] F_i。 -/
theorem coeff_prod_X {ι : Type*} (s : Finset ι) (F : ι → (ZMod p)[X]) (h0 : ∀ i ∈ s, (F i).coeff 0 = 0) :
    (∏ i ∈ s, F i).coeff s.card = ∏ i ∈ s, (F i).coeff 1 := by
  have hF : ∀ i ∈ s, F i = X * divX (F i) := by
    intro i hi
    have := X_mul_divX_add (F i)
    rw [h0 i hi, C_0, add_zero] at this
    exact this.symm
  rw [Finset.prod_congr rfl hF, Finset.prod_mul_distrib, Finset.prod_const, mul_comm,
    coeff_mul_X_pow']
  simp only [le_refl, ↓reduceIte, Nat.sub_self]
  rw [coeff_zero_eq_eval_zero, eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [← coeff_zero_eq_eval_zero, coeff_divX]

/-- **3. [X^m] T(Q) = 2^m m!**。 -/
theorem coeff_TQ (m : ℕ) (hpm : p = 2 * m + 1) : (T p (Qz p m)).coeff m = 2 ^ m * (m.factorial : ZMod p) := by
  have hTQ : T p (Qz p m) = ∏ a ∈ Ico 1 (m + 1), ((X + 1) ^ a - (X + 1) ^ (p - a)) := by
    unfold T Qz
    simp [Polynomial.map_prod, Polynomial.prod_comp, sub_comp, pow_comp]
  rw [hTQ]
  have hc := coeff_prod_X p (Ico 1 (m + 1)) (fun a => (X + 1) ^ a - (X + 1) ^ (p - a)) (by
    intro a _; simp only [coeff_sub, coeff_X_add_one_pow, Nat.choose_zero_right, sub_self])
  rw [Nat.card_Ico, Nat.add_sub_cancel] at hc
  rw [hc]
  have e : ∀ a ∈ Ico 1 (m + 1), ((X + 1) ^ a - (X + 1) ^ (p - a) : (ZMod p)[X]).coeff 1 = 2 * (a : ZMod p) := by
    intro a ha
    simp only [Finset.mem_Ico] at ha
    rw [coeff_sub, coeff_X_add_one_pow, coeff_X_add_one_pow, Nat.choose_one_right, Nat.choose_one_right,
      Nat.cast_sub (by omega : a ≤ p), ZMod.natCast_self]
    ring
  rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, Nat.add_sub_cancel]
  congr 1
  rw [← Finset.prod_Ico_id_eq_factorial]; push_cast; rfl

/-- **4. (m!)² = (−1)^{m+1}（法 p）**。 -/
theorem factorial_sq (m : ℕ) (hpm : p = 2 * m + 1) : ((m.factorial : ZMod p)) ^ 2 = (-1) ^ (m + 1) := by
  have hodd : Odd p := ⟨m, hpm⟩
  have h := ZMod.factorial_eq_neg_one_pow_mul_half_factorial_sq (p := p) hodd
  rw [ZMod.wilsons_lemma, show (p - 1) / 2 = m by omega] at h
  have h1 : ((-1 : ZMod p) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  linear_combination (-(-1 : ZMod p) ^ m) * h - ((m.factorial : ZMod p)) ^ 2 * h1

/-- **5. 係数比較：Φ_p ∣ P − ε Q ⇒ ε ≡ (−1)^m χ(2)（法 p）**。 -/
theorem sign_from_poly (m : ℕ) (hpm : p = 2 * m + 1) (ε : ℤ) (hdvd : cyclotomic p ℤ ∣ Pz p - C ε * Qz p m) :
    (ε : ZMod p) = (-1) ^ m * ((quadraticChar (ZMod p) 2 : ℤ) : ZMod p) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨h, hh⟩ := hdvd
  have hT := congrArg (T p) hh
  rw [T_sub, T_mul, T_mul, T_cyclotomic] at hT
  have hTC : T p (C ε) = C (ε : ZMod p) := by unfold T; simp
  rw [hTC] at hT
  have hc := congrArg (fun f => f.coeff m) hT
  simp only [coeff_sub, coeff_C_mul, coeff_X_pow_mul'] at hc
  have hm1 : 1 ≤ m := by have := hp.out.two_le; omega
  have hlt : ¬ (p - 1 ≤ m) := by omega
  simp only [hlt, ↓reduceIte] at hc
  have hP := coeff_TP p m hpm
  have hQ := coeff_TQ p m hpm
  have hF := factorial_sq p m hpm
  rw [hQ] at hc
  set c := ((quadraticChar (ZMod p) 2 : ℤ) : ZMod p)
  have h2 : (2 : ZMod p) ^ m = c := by
    simp only [c]
    rw [quadraticChar_eq_pow_of_char_ne_two' (PAG.Part119.ringChar_ne_two hp2), ZMod.card, show p / 2 = m by omega]
  have hc2 : c ^ 2 = 1 := by
    simp only [c]
    have h20 : (2 : ZMod p) ≠ 0 := PAG.Part119.two_ne_zero' hp2
    have := quadraticChar_sq_one h20
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) this
  have hs2 : ((-1 : ZMod p) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hE : -1 + (ε : ZMod p) * c * (-1) ^ m = 0 := by
    have := congrArg (fun z => (m.factorial : ZMod p) * z) hc
    simp only [mul_zero] at this
    linear_combination this - hP + (ε : ZMod p) * 2 ^ m * hF
      + (ε : ZMod p) * (-1) ^ (m + 1) * h2
  linear_combination (c * (-1) ^ m) * hE - (ε : ZMod p) * ((-1 : ZMod p) ^ m) ^ 2 * hc2 - (ε : ZMod p) * hs2

end PAG.Part166

#print axioms PAG.Part166.T_cyclotomic
#print axioms PAG.Part166.sum_range_zmod
#print axioms PAG.Part166.sum_pow_top
#print axioms PAG.Part166.sum_desc
#print axioms PAG.Part166.coeff_TP
#print axioms PAG.Part166.coeff_prod_X
#print axioms PAG.Part166.coeff_TQ
#print axioms PAG.Part166.factorial_sq
#print axioms PAG.Part166.sign_from_poly
