/-
  Projective Adelic Geometry — formalization Part 2（付録 A の続き）
  対象: 定理 4.5（周回数ごとの指標和 = 実数化された超 Kloosterman 和）
  使用する Mathlib: DirichletCharacter（直交関係）, gaussSum, ZMod.stdAddChar
-/
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Complex Finset

namespace PAG.Kloosterman

variable {N : ℕ} [NeZero N]

/-- 超 Kloosterman 和 Kl_r(c; N) = Σ_{x₁⋯x_r = c} ψ(x₁ + ⋯ + x_r)。
`ψ` は任意の加法的指標（本文では ψ = e(·/N) = `ZMod.stdAddChar`）。 -/
noncomputable def Kl (ψ : AddChar (ZMod N) ℂ) (r : ℕ) (c : ZMod N) : ℂ :=
  ∑ x : Fin r → ZMod N, if ∏ i, x i = c then ψ (∑ i, x i) else 0

omit [NeZero N] in
/-- 加法的指標は和を積に移す。 -/
lemma addChar_sum {ι : Type*} (ψ : AddChar (ZMod N) ℂ) (s : Finset ι) (x : ι → ZMod N) :
    ψ (∑ i ∈ s, x i) = ∏ i ∈ s, ψ (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert j s hj ih => rw [sum_insert hj, prod_insert hj, AddChar.map_add_eq_mul, ih]

/-- ガウス和の r 乗の展開: τ(χ)^r = Σ_x χ(∏ x) ψ(Σ x)。 -/
lemma gaussSum_pow (χ : DirichletCharacter ℂ N) (ψ : AddChar (ZMod N) ℂ) (r : ℕ) :
    gaussSum χ ψ ^ r = ∑ x : Fin r → ZMod N, χ (∏ i, x i) * ψ (∑ i, x i) := by
  classical
  rw [gaussSum, ← Fin.prod_const, Fintype.prod_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [prod_mul_distrib, map_prod, addChar_sum]

/-- **定理 4.5 の核心**（指標の直交性）:
a が単数のとき Σ_χ χ(a⁻¹) τ(χ)^r = φ(N) · Kl_r(a)。 -/
theorem charSum_gaussSum_pow (ψ : AddChar (ZMod N) ℂ) (r : ℕ) {a : ZMod N} (ha : IsUnit a) :
    ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * gaussSum χ ψ ^ r = N.totient * Kl ψ r a := by
  classical
  simp_rw [gaussSum_pow, mul_sum]
  rw [sum_comm, Kl, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp_rw [← mul_assoc]
  rw [← sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

omit [NeZero N] in
/-- 単数の符号反転: (−a)⁻¹ = a⁻¹ · (−1)（ZMod N の逆元）。 -/
lemma inv_neg_unit {a : ZMod N} (ha : IsUnit a) : (-a)⁻¹ = a⁻¹ * (-1) := by
  obtain ⟨u, rfl⟩ := ha
  have : -(u : ZMod N) = ((-u : (ZMod N)ˣ) : ZMod N) := by simp
  rw [this, ZMod.inv_coe_unit, ZMod.inv_coe_unit, inv_neg, mul_neg_one]
  simp

/-- 偶奇で重みを分けた指標和（i^{-a r} の偶奇分解の一般形）:
Σ_χ χ(a⁻¹) · (w_e(1+χ(−1)) + w_o(1−χ(−1)))/2 · τ(χ)^r
  = φ(N)/2 · ((w_e + w_o) Kl_r(a) + (w_e − w_o) Kl_r(−a))。 -/
theorem charSum_parity (ψ : AddChar (ZMod N) ℂ) (r : ℕ) (we wo : ℂ)
    {a : ZMod N} (ha : IsUnit a) :
    ∑ χ : DirichletCharacter ℂ N,
        χ a⁻¹ * ((we * (1 + χ (-1)) + wo * (1 - χ (-1))) / 2) * gaussSum χ ψ ^ r
      = N.totient / 2 * ((we + wo) * Kl ψ r a + (we - wo) * Kl ψ r (-a)) := by
  have hna : IsUnit (-a) := ha.neg
  have key : ∀ χ : DirichletCharacter ℂ N,
      χ a⁻¹ * ((we * (1 + χ (-1)) + wo * (1 - χ (-1))) / 2) * gaussSum χ ψ ^ r
        = (we + wo) / 2 * (χ a⁻¹ * gaussSum χ ψ ^ r)
          + (we - wo) / 2 * (χ (-a)⁻¹ * gaussSum χ ψ ^ r) := by
    intro χ
    rw [inv_neg_unit ha, map_mul]
    ring
  simp_rw [key, sum_add_distrib, ← mul_sum, charSum_gaussSum_pow ψ r ha,
    charSum_gaussSum_pow ψ r hna]
  ring

/-! ### ψ = e(·/N) のときの対称性 -/

/-- x ↦ −x で並べ替えると、ψ(−s) = conj ψ(s) と ∏(−x) = (−1)^r ∏ x から
conj Kl_r(c) = Kl_r((−1)^r c)。 -/
theorem conj_Kl (r : ℕ) (c : ZMod N) :
    starRingEnd ℂ (Kl ZMod.stdAddChar r c) = Kl ZMod.stdAddChar r ((-1) ^ r * c) := by
  classical
  unfold Kl
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.neg (Fin r → ZMod N)) _ _ fun x => ?_
  simp only [Equiv.neg_apply, Pi.neg_apply, prod_neg, card_univ, Fintype.card_fin, sum_neg_distrib,
    apply_ite (starRingEnd ℂ), map_zero, AddChar.map_neg_eq_conj]
  have hpow : ((-1 : ZMod N) ^ r) * (-1) ^ r = 1 := by rw [← mul_pow]; simp
  by_cases h : ∏ i, x i = c
  · rw [ite_eq_left h, ite_eq_left (by rw [h])]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    apply h
    calc ∏ i, x i = ((-1) ^ r * (-1) ^ r) * ∏ i, x i := by rw [hpow, one_mul]
      _ = (-1) ^ r * ((-1) ^ r * ∏ i, x i) := by ring
      _ = c := by rw [h', ← mul_assoc, hpow, one_mul]

/-- r 奇数: Kl_r(−c) = conj Kl_r(c)。 -/
theorem Kl_neg_of_odd {r : ℕ} (hr : Odd r) (c : ZMod N) :
    Kl ZMod.stdAddChar r (-c) = starRingEnd ℂ (Kl ZMod.stdAddChar r c) := by
  rw [conj_Kl, hr.neg_one_pow, neg_one_mul]

/-- r 偶数: Kl_r(c) は実数。 -/
theorem Kl_real_of_even {r : ℕ} (hr : Even r) (c : ZMod N) :
    (Kl ZMod.stdAddChar r c).im = 0 := by
  have h := conj_Kl (N := N) r c
  rw [hr.neg_one_pow, one_mul] at h
  exact Complex.conj_eq_iff_im.mp h

/-! ### 定理 4.5 本体（cas 形）
W(χ) = τ(χ)/(i^a √N) なので W(χ)^r = i^{−a r} τ(χ)^r / √N^r。
i^{−a} は偶指標で 1、奇指標で −i。これを偶奇射影 (1 ± χ(−1))/2 で書く。 -/

/-- cas z = Re z + Im z（実数値を ℂ に埋め込んだもの）。 -/
noncomputable def cas (z : ℂ) : ℂ := ((z.re + z.im : ℝ) : ℂ)

/-- ルート数の r 乗 W(χ)^r（偶奇射影で i^{−a r} を表したもの）。 -/
noncomputable def Wpow (χ : DirichletCharacter ℂ N) (r : ℕ) : ℂ :=
  ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 * gaussSum χ ZMod.stdAddChar ^ r
    / (Real.sqrt N : ℂ) ^ r

omit [NeZero N] in
open scoped Classical in
/-- 偶奇射影による表示が本文の i^{−a r} と一致すること（偶: 1、奇: (−i)^r）。 -/
lemma parity_weight (χ : DirichletCharacter ℂ N) (r : ℕ) :
    ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 = if χ.Even then 1 else (-I) ^ r := by
  rcases χ.even_or_odd with h | h
  · rw [ite_eq_left h, show χ (-1) = 1 from h]; ring
  · rw [ite_eq_right h.not_even, show χ (-1) = -1 from h]; ring

/-- 共通の前段: S_r(a) = φ/(2√N^r) · ((1+(−i)^r) Kl_r(a) + (1−(−i)^r) Kl_r(−a))。 -/
lemma S_eq (r : ℕ) {a : ZMod N} (ha : IsUnit a) :
    ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * Wpow χ r
      = N.totient / 2 / (Real.sqrt N : ℂ) ^ r
          * ((1 + (-I) ^ r) * Kl ZMod.stdAddChar r a
              + (1 - (-I) ^ r) * Kl ZMod.stdAddChar r (-a)) := by
  have := charSum_parity ZMod.stdAddChar r 1 ((-I) ^ r) ha
  simp only [one_mul] at this
  unfold Wpow
  have e : ∀ χ : DirichletCharacter ℂ N,
      χ a⁻¹ * (((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 * gaussSum χ ZMod.stdAddChar ^ r
          / (Real.sqrt N : ℂ) ^ r)
        = (χ a⁻¹ * (((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2)
            * gaussSum χ ZMod.stdAddChar ^ r) / (Real.sqrt N : ℂ) ^ r := fun χ => by ring
  simp_rw [e, ← sum_div, this]
  ring

/-- **定理 4.5（r 奇数）**: r = 2k+1 のとき
S_r(a) = φ(N)/√N^r · cas Kl_r((−1)^k a)。 -/
theorem S_odd (k : ℕ) {a : ZMod N} (ha : IsUnit a) :
    ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * Wpow χ (2 * k + 1)
      = N.totient / (Real.sqrt N : ℂ) ^ (2 * k + 1)
          * cas (Kl ZMod.stdAddChar (2 * k + 1) ((-1) ^ k * a)) := by
  have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  rw [S_eq _ ha, Kl_neg_of_odd hodd]
  set K := Kl ZMod.stdAddChar (2 * k + 1) a with hK
  have hI : (-I) ^ (2 * k + 1) = (-1) ^ k * (-I) := by
    rw [pow_succ, pow_mul, neg_sq, I_sq]
  have hz : starRingEnd ℂ K = (K.re : ℂ) - K.im * I := by
    apply Complex.ext <;> simp
  have hK' : K = (K.re : ℂ) + K.im * I := (Complex.re_add_im K).symm
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow, one_mul, ← hK, hI, hk.neg_one_pow, cas]
    rw [hz]; nth_rewrite 1 [hK']
    push_cast
    ring_nf
    rw [I_sq]
    ring
  · rw [hk.neg_one_pow, neg_one_mul, Kl_neg_of_odd hodd, ← hK, hI, hk.neg_one_pow, cas]
    have hre : (starRingEnd ℂ K).re = K.re := by simp
    have him : (starRingEnd ℂ K).im = -K.im := by simp
    rw [hre, him, hz]; nth_rewrite 1 [hK']
    push_cast
    ring_nf
    rw [I_sq]
    ring

/-- **定理 4.5（r 偶数）**: r = 2k のとき S_r(a) = φ(N)/N^k · Kl_r((−1)^k a)、
かつ右辺の Kl は実数（`Kl_real_of_even`）なので cas Kl = Kl。 -/
theorem S_even (k : ℕ) {a : ZMod N} (ha : IsUnit a) :
    ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * Wpow χ (2 * k)
      = N.totient / (Real.sqrt N : ℂ) ^ (2 * k)
          * Kl ZMod.stdAddChar (2 * k) ((-1) ^ k * a) := by
  rw [S_eq _ ha]
  have hI : (-I) ^ (2 * k) = (-1) ^ k := by rw [pow_mul, neg_sq, I_sq]
  rw [hI]
  rcases Nat.even_or_odd k with hk | hk
  · simp only [hk.neg_one_pow, one_mul]; ring
  · simp only [hk.neg_one_pow, neg_one_mul]; ring

/-- 偶数 r で cas Kl = Kl（実数性）。S_even と合わせて本文の cas 形になる。 -/
theorem cas_Kl_even (k : ℕ) (c : ZMod N) :
    cas (Kl ZMod.stdAddChar (2 * k) c) = Kl ZMod.stdAddChar (2 * k) c := by
  have him := Kl_real_of_even (N := N) (even_two_mul k) c
  unfold cas
  apply Complex.ext <;> simp [him]

end PAG.Kloosterman

#print axioms PAG.Kloosterman.charSum_gaussSum_pow
#print axioms PAG.Kloosterman.charSum_parity
#print axioms PAG.Kloosterman.conj_Kl
#print axioms PAG.Kloosterman.Kl_neg_of_odd
#print axioms PAG.Kloosterman.Kl_real_of_even
#print axioms PAG.Kloosterman.parity_weight
#print axioms PAG.Kloosterman.S_eq
#print axioms PAG.Kloosterman.S_odd
#print axioms PAG.Kloosterman.S_even
#print axioms PAG.Kloosterman.cas_Kl_even
