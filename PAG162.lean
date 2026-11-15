/-
  PAG 2.0 Part 158（2026-10-22）— p ≡ 1、導手 p^{2m+1}、ord χ 奇数で ord ζ = p と 2p はちょうど半々
  1. fp χ = freq χ mod p（加法的）
  2. fiber_const: {χ^N = 1} 上で fp のファイバーはすべて同じ大きさ（fp が全射のとき）
  3. card_res: {t ≠ 0 | L(−t/2) = ε} と {t ≠ 0 | L(−t/2) ≠ ε} は同数（ε² = 1）
  4. half_half: #{ord χ 奇・原始・ord ζ = p} = #{ord χ 奇・原始・ord ζ ≠ p}
-/
import PAG161

namespace PAG.Part162

open ZMod Finset PAG.Part119 PAG.Part143 PAG.Part144 PAG.Part160

variable {p : ℕ} [hp : Fact p.Prime]

section Gen

variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)

/-- 周波数の法 p での値。 -/
noncomputable def fp (χ : DirichletCharacter ℂ (p ^ c)) : ZMod p := ((freq hkc h2k χ).cast : ZMod p)

theorem fp_mul (χ ψ : DirichletCharacter ℂ (p ^ c)) : fp hkc h2k (χ * ψ) = fp hkc h2k χ + fp hkc h2k ψ := by
  unfold fp; rw [freq_mul]; exact ZMod.cast_add (dvd_pow_self p (by omega)) _ _

theorem fp_one : fp hkc h2k (1 : DirichletCharacter ℂ (p ^ c)) = 0 := by
  unfold fp; rw [freq_one]; exact ZMod.cast_zero

theorem fp_inv (χ : DirichletCharacter ℂ (p ^ c)) : fp hkc h2k χ⁻¹ = - fp hkc h2k χ := by
  have h := fp_mul hkc h2k χ χ⁻¹
  rw [mul_inv_cancel, fp_one] at h
  linear_combination -h

theorem fp_pow (χ : DirichletCharacter ℂ (p ^ c)) (j : ℕ) : fp hkc h2k (χ ^ j) = j * fp hkc h2k χ := by
  unfold fp; rw [freq_pow, ZMod.cast_mul (dvd_pow_self p (by omega)), ZMod.cast_natCast (dvd_pow_self p (by omega))]

theorem fp_ne_zero_iff (χ : DirichletCharacter ℂ (p ^ c)) : χ.IsPrimitive ↔ fp hkc h2k χ ≠ 0 := by
  rw [primitive_iff_freq_unit hkc h2k, PAG.Part140.isUnit_iff_cast_ne_zero (c - k) (by omega)]; rfl

open Classical in
/-- **2. ファイバーの大きさは一定**。 -/
theorem fiber_const (N : ℕ) (hω : ∀ t : ZMod p, ∃ ω : DirichletCharacter ℂ (p ^ c), ω ^ N = 1 ∧ fp hkc h2k ω = t)
    (t : ZMod p) :
    #{χ : DirichletCharacter ℂ (p ^ c) | χ ^ N = 1 ∧ fp hkc h2k χ = t}
      = #{χ : DirichletCharacter ℂ (p ^ c) | χ ^ N = 1 ∧ fp hkc h2k χ = 0} := by
  obtain ⟨ω, hωN, hωt⟩ := hω t
  apply Finset.card_nbij' (fun χ => χ * ω⁻¹) (fun χ => χ * ω)
  · intro χ hχ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hχ ⊢
    refine ⟨by rw [mul_pow, inv_pow, hχ.1, hωN, inv_one, mul_one], ?_⟩
    rw [fp_mul, fp_inv, hχ.2, hωt, add_neg_cancel]
  · intro χ hχ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hχ ⊢
    refine ⟨by rw [mul_pow, hχ.1, hωN, mul_one], ?_⟩
    rw [fp_mul, hχ.2, hωt, zero_add]
  · intro χ _; simp
  · intro χ _; simp

open Classical in
/-- **2'. 集合 S への逆像の大きさ = |S| · (ファイバーの大きさ)**。 -/
theorem count_set (N : ℕ) (hω : ∀ t : ZMod p, ∃ ω : DirichletCharacter ℂ (p ^ c), ω ^ N = 1 ∧ fp hkc h2k ω = t)
    (S : Finset (ZMod p)) :
    #{χ : DirichletCharacter ℂ (p ^ c) | χ ^ N = 1 ∧ fp hkc h2k χ ∈ S}
      = S.card * #{χ : DirichletCharacter ℂ (p ^ c) | χ ^ N = 1 ∧ fp hkc h2k χ = 0} := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fp hkc h2k) (t := S)
    (fun χ hχ => (Finset.mem_filter.mp hχ).2.2)]
  rw [Finset.sum_congr rfl (fun t ht => by
    rw [Finset.filter_filter, show (univ.filter fun χ : DirichletCharacter ℂ (p ^ c) =>
        (χ ^ N = 1 ∧ fp hkc h2k χ ∈ S) ∧ fp hkc h2k χ = t)
        = univ.filter (fun χ => χ ^ N = 1 ∧ fp hkc h2k χ = t) from by
          ext χ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ ht⟩, h2⟩])]
  rw [Finset.sum_congr rfl (fun t _ => fiber_const hkc h2k N hω t), Finset.sum_const, smul_eq_mul]

end Gen

open Classical in
/-- **3. 剰余と非剰余の数え上げ**。 -/
theorem card_res (hp2 : p ≠ 2) (ε : ℂ) (hε : ε ^ 2 = 1) :
    #{t : ZMod p | t ≠ 0 ∧ Lc p (-t * 2⁻¹) = ε} = #{t : ZMod p | t ≠ 0 ∧ Lc p (-t * 2⁻¹) ≠ ε} := by
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (ringChar_ne_two hp2)
  have hg0 : g ≠ 0 := by rintro rfl; exact hg ⟨0, by ring⟩
  have hLg : Lc p g = -1 := by
    rw [Lc_apply, quadraticChar_neg_one_iff_not_isSquare.mpr hg]; simp
  have hLg' : Lc p g⁻¹ = -1 := by
    have h := map_mul (Lc p) g g⁻¹
    rw [mul_inv_cancel₀ hg0, map_one, hLg] at h
    linear_combination h
  have hε0 : ε ≠ 0 := by rintro rfl; norm_num at hε
  have h2 := PAG.Part119.two_ne_zero' hp2
  apply Finset.card_nbij' (fun t => g * t) (fun t => g⁻¹ * t)
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    refine ⟨mul_ne_zero hg0 ht.1, ?_⟩
    rw [show -(g * t) * 2⁻¹ = g * (-t * 2⁻¹) by ring, map_mul, hLg, ht.2]
    intro h; apply hε0; linear_combination -h / 2
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    refine ⟨mul_ne_zero (inv_ne_zero hg0) ht.1, ?_⟩
    rw [show -(g⁻¹ * t) * 2⁻¹ = g⁻¹ * (-t * 2⁻¹) by ring, map_mul, hLg']
    have hA : -t * 2⁻¹ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr ht.1) (inv_ne_zero h2)
    have hL2 := Lc_sq _ hA
    have hprod : (Lc p (-t * 2⁻¹) - ε) * (Lc p (-t * 2⁻¹) + ε) = 0 := by linear_combination hL2 - hε
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (by linear_combination h) ht.2
    · linear_combination -h
  · intro t _; simp [hg0]
  · intro t _; simp [hg0]

/-- **4. 奇数位数で fp が全射になる指標の存在**。 -/
theorem exists_omega (hp2 : p ≠ 2) (n : ℕ) {k : ℕ} (hkc : k < n + 1) (h2k : n + 1 ≤ 2 * k)
    (v o : ℕ) (hvo : p - 1 = 2 ^ v * o) (t : ZMod p) :
    ∃ ω : DirichletCharacter ℂ (p ^ (n + 1)), ω ^ (p ^ n * o) = 1 ∧ fp hkc h2k ω = t := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨χ₁, hχ₁⟩ := exists_primitive (p := p) (n + 1) (by omega)
  set χ₀ := χ₁ ^ (2 ^ v)
  have hN : χ₀ ^ (p ^ n * o) = 1 := by
    have h := PAG.Part134.orderOf_dvd_totient χ₁
    rw [Nat.totient_prime_pow hp.out (by omega), Nat.add_sub_cancel, hvo] at h
    simp only [χ₀]; rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp (h.trans ⟨1, by ring⟩)
  have hf0 : fp hkc h2k χ₀ ≠ 0 := by
    simp only [χ₀]; rw [fp_pow]
    push_cast
    exact mul_ne_zero (pow_ne_zero _ (PAG.Part119.two_ne_zero' hp2)) ((fp_ne_zero_iff hkc h2k χ₁).mp hχ₁)
  refine ⟨χ₀ ^ (t * (fp hkc h2k χ₀)⁻¹).val, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hN, one_pow]
  · rw [fp_pow, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hf0, mul_one]

open Classical in
/-- **5. p ≡ 1、導手 p^{2m+1}：ord χ 奇数の原始指標のうち、ord ζ = p と ord ζ ≠ p（= 2p）は同数**。 -/
theorem half_half (h4 : p % 4 = 1) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m) :
    #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | ¬ 2 ∣ orderOf χ ∧ χ.IsPrimitive ∧
        orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = p}
      = #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | ¬ 2 ∣ orderOf χ ∧ χ.IsPrimitive ∧
        orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ≠ p} := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hkc : m + 1 < n + 1 := by omega
  have h2k : n + 1 ≤ 2 * (m + 1) := by omega
  obtain ⟨v, o, ho, hvo⟩ := Nat.exists_eq_two_pow_mul_odd (n := p - 1) (by have := hp.out.two_le; omega)
  have hω := fun t => exists_omega hp2 n hkc h2k v o hvo t
  have hε : epsG p ^ 2 = 1 := by rw [epsG_sq hp2, PAG.Part129.Lc_neg_one_of_one h4]
  -- ord χ 奇数 ⇔ χ^{p^n o} = 1
  have hodd : ∀ χ : DirichletCharacter ℂ (p ^ (n + 1)), ¬ 2 ∣ orderOf χ ↔ χ ^ (p ^ n * o) = 1 := by
    intro χ
    have hNodd : Odd (p ^ n * o) := (hp.out.odd_of_ne_two hp2).pow.mul ho
    constructor
    · intro h
      have hd := PAG.Part134.orderOf_dvd_totient χ
      rw [Nat.totient_prime_pow hp.out (by omega), Nat.add_sub_cancel, hvo,
        show p ^ n * (2 ^ v * o) = 2 ^ v * (p ^ n * o) by ring] at hd
      have hcop : Nat.Coprime (orderOf χ) (2 ^ v) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h)))
      exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hd)
    · intro h h2
      have := (orderOf_dvd_of_pow_eq_one h)
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr (h2.trans this))
  -- ζ の条件を fp で書き直す
  have hζ : ∀ χ : DirichletCharacter ℂ (p ^ (n + 1)), ¬ 2 ∣ orderOf χ → χ.IsPrimitive →
      (orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = p ↔
        Lc p (-(fp hkc h2k χ) * 2⁻¹) = epsG p) := by
    intro χ ho' hpr
    have hδ := Classical.choose_spec (freq_exists hkc h2k χ)
    rw [zeta_order_one_odd_iff h4 n m hnm hm χ hpr _ hδ ho']
    have hcast : (((-Classical.choose (freq_exists hkc h2k χ) : ZMod (p ^ (n + 1)))).cast : ZMod p)
        = -(fp hkc h2k χ) := by
      rw [ZMod.cast_neg (dvd_pow_self p (by omega))]
      congr 1
      unfold fp freq
      have hc := congrArg (fun f => f (Classical.choose (freq_exists hkc h2k χ)))
        (ZMod.castHom_comp (n := p) (dvd_pow_self p (by omega : n + 1 - (m + 1) ≠ 0))
          (pow_dvd_pow p (by omega : n + 1 - (m + 1) ≤ n + 1)))
      simpa [ZMod.castHom_apply] using hc.symm
    rw [hcast]
  set SP := univ.filter (fun t : ZMod p => t ≠ 0 ∧ Lc p (-t * 2⁻¹) = epsG p)
  set SN := univ.filter (fun t : ZMod p => t ≠ 0 ∧ Lc p (-t * 2⁻¹) ≠ epsG p)
  have e1 : (univ.filter fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => ¬ 2 ∣ orderOf χ ∧ χ.IsPrimitive ∧
        orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = p)
      = univ.filter (fun χ => χ ^ (p ^ n * o) = 1 ∧ fp hkc h2k χ ∈ SP) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SP]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(hodd χ).mp h1, (fp_ne_zero_iff hkc h2k χ).mp h2, (hζ χ h1 h2).mp h3⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' := (hodd χ).mpr h1
      have h2' := (fp_ne_zero_iff hkc h2k χ).mpr h2
      exact ⟨h1', h2', (hζ χ h1' h2').mpr h3⟩
  have e2 : (univ.filter fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => ¬ 2 ∣ orderOf χ ∧ χ.IsPrimitive ∧
        orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ≠ p)
      = univ.filter (fun χ => χ ^ (p ^ n * o) = 1 ∧ fp hkc h2k χ ∈ SN) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SN]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(hodd χ).mp h1, (fp_ne_zero_iff hkc h2k χ).mp h2, fun h => h3 ((hζ χ h1 h2).mpr h)⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' := (hodd χ).mpr h1
      have h2' := (fp_ne_zero_iff hkc h2k χ).mpr h2
      exact ⟨h1', h2', fun h => h3 ((hζ χ h1' h2').mp h)⟩
  rw [e1, e2, count_set hkc h2k _ hω, count_set hkc h2k _ hω, card_res hp2 _ hε]

end PAG.Part162

#print axioms PAG.Part162.fp_mul
#print axioms PAG.Part162.fp_one
#print axioms PAG.Part162.fp_inv
#print axioms PAG.Part162.fp_pow
#print axioms PAG.Part162.fp_ne_zero_iff
#print axioms PAG.Part162.fiber_const
#print axioms PAG.Part162.count_set
#print axioms PAG.Part162.card_res
#print axioms PAG.Part162.exists_omega
#print axioms PAG.Part162.half_half
