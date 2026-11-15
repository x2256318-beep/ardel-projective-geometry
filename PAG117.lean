/-
  PAG 2.0 Part 113（2026-10-19）— ζ_k とガウス和: ζ_k = (τ(χ)/p^{c/2})^o
  1. 引き戻しのフーリエ変換: M' = M d のとき 𝓕_{M'}(f ∘ π)(d k) = d · 𝓕_M f(π k)
  2. ケットの点 t* = p^a での値: 𝓕k(p^a) = |S_w|^{-1/2} p^a χ⁻¹(−1) τ(χ)、とくに p^a ∈ T_a
  3. ζ_k = (λ^{-1/2}𝓕k(t₀))^o = (τ(χ)/√(p^c))^o（任意の t₀ ∈ T_a）
  系: ζ_k が 1 の冪根であることは、τ(χ)/p^{c/2} が 1 の冪根であることと同値
-/
import PAG116

namespace PAG.Part117

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part55 PAG.Part59 PAG.Part90 PAG.Part95 PAG.Part116

section Pullback

variable {M M' : ℕ} [NeZero M] [NeZero M']

/-- stdAddChar_{M'}(d z) = stdAddChar_M(π z)（M' = M d）。 -/
theorem stdAddChar_mul_cast (h : M ∣ M') (d : ℕ) (hd : M' = M * d) (z : ZMod M') :
    stdAddChar ((d : ZMod M') * z) = stdAddChar (ZMod.castHom h (ZMod M) z) := by
  rw [← ZMod.natCast_zmod_val z, map_natCast, ← Nat.cast_mul, stdAddChar_apply, stdAddChar_apply,
    toCircle_natCast, toCircle_natCast]
  congr 1
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hd0 : (d : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; simp at hd; exact NeZero.ne M' hd
    exact Nat.cast_ne_zero.mpr this
  have hM' : (M' : ℂ) = M * d := by rw [hd]; push_cast; ring
  rw [hM']; push_cast; field_simp

/-- **1. 引き戻しのフーリエ変換**。 -/
theorem dft_pullback_mul (h : M ∣ M') (d : ℕ) (hd : M' = M * d) (f : ZMod M → ℂ) (k : ZMod M') :
    𝓕 (fun x => f (ZMod.castHom h (ZMod M) x)) ((d : ZMod M') * k)
      = (d : ℂ) * 𝓕 f (ZMod.castHom h (ZMod M) k) := by
  classical
  have hsurj : Function.Surjective (ZMod.castHom h (ZMod M)).toAddMonoidHom := ZMod.ringHom_surjective _
  rw [dft_apply, dft_apply]
  have e1 : ∀ x : ZMod M', stdAddChar (-(x * ((d : ZMod M') * k))) • f (ZMod.castHom h (ZMod M) x)
      = (fun y => stdAddChar (-(y * ZMod.castHom h (ZMod M) k)) • f y)
          ((ZMod.castHom h (ZMod M)).toAddMonoidHom x) := by
    intro x
    show _ = stdAddChar (-((ZMod.castHom h (ZMod M)) x * ZMod.castHom h (ZMod M) k)) • f ((ZMod.castHom h (ZMod M)) x)
    congr 1
    rw [show -(x * ((d : ZMod M') * k)) = (d : ZMod M') * (-(x * k)) by ring, stdAddChar_mul_cast h d hd,
      map_neg, map_mul]
  rw [Finset.sum_congr rfl (fun x _ => e1 x),
    sum_comp_surj _ hsurj (fun y => stdAddChar (-(y * ZMod.castHom h (ZMod M) k)) • f y)]
  congr 1
  -- 核の大きさ = d
  have e2 := sum_comp_surj _ hsurj (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at e2
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hM' : (M' : ℂ) = M * d := by rw [hd]; push_cast; ring
  exact mul_right_cancel₀ hM (by rw [← e2, hM']; ring)

end Pullback

section Ket

variable {p : ℕ} [hp : Fact p.Prime]

/-- **2. 点 p^a でのケットのフーリエ変換**。 -/
theorem dft_ket_pa (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) :
    𝓕 (ket K w (n + 1) h χ) ((p : ZMod (p ^ K)) ^ (K - (n + 1) - w))
      = ((((Real.sqrt (sz p K w))⁻¹ * (p : ℝ) ^ (K - (n + 1) - w) : ℝ)) : ℂ)
          * (χ⁻¹ (-1) * gaussSum χ stdAddChar) := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [ket_eq_push, dft_const_smul, Pi.smul_apply, PAG.Part18.dft_push K w (by omega)]
  have hcast : ZMod.castHom (pow_dvd_pow p (Nat.sub_le K w)) (ZMod (p ^ (K - w))) ((p : ZMod (p ^ K)) ^ (K - (n + 1) - w))
      = ((p ^ (K - (n + 1) - w) : ℕ) : ZMod (p ^ (K - w))) * 1 := by
    rw [map_pow, map_natCast, mul_one, Nat.cast_pow]
  rw [hcast, dft_pullback_mul _ (p ^ (K - (n + 1) - w)) (by rw [← pow_add]; congr 1; omega), map_one,
    hχ.fourierTransform_eq_inv_mul_gaussSum, smul_eq_mul]
  push_cast
  ring

omit hp in
theorem inv_neg_one_pow {n : ℕ} (χ : DirichletCharacter ℂ (p ^ (n + 1))) : (χ⁻¹ (-1)) ^ orderOf χ = 1 := by
  rw [← MulChar.pow_apply' _ (orderOf_pos χ).ne', inv_pow, pow_orderOf_eq_one, inv_one]
  exact MulChar.one_apply (isUnit_one.neg)

omit hp in
theorem normSq_inv_neg_one {n : ℕ} (χ : DirichletCharacter ℂ (p ^ (n + 1))) : Complex.normSq (χ⁻¹ (-1)) = 1 := by
  have h2 : (χ⁻¹ (-1)) * (χ⁻¹ (-1)) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have h3 : Complex.normSq (χ⁻¹ (-1)) * Complex.normSq (χ⁻¹ (-1)) = 1 := by
    rw [← map_mul, h2, map_one]
  have h0 := Complex.normSq_nonneg (χ⁻¹ (-1))
  nlinarith [sq_nonneg (Complex.normSq (χ⁻¹ (-1)) - 1)]

theorem pa_mem_Tset (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : ((p : ZMod (p ^ K)) ^ (K - (n + 1) - w)) ∈ Tset (p := p) K (K - (n + 1) - w) := by
  by_contra hn
  have hkd : KetDual (p := p) K (K - (n + 1) - w) (ket K w (n + 1) h χ) := ⟨w, n, h, χ, hχ, rfl, rfl⟩
  have h0 := (PAG.Part97.eigen_abs K _ _ hkd _).2 hn
  rw [dft_ket_pa K w n h χ hχ] at h0
  have hr : (((Real.sqrt (sz p K w))⁻¹ * (p : ℝ) ^ (K - (n + 1) - w) : ℝ) : ℂ) ≠ 0 := by
    have hs : 0 < sz p K w := by
      unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
    have : (0 : ℝ) < (Real.sqrt (sz p K w))⁻¹ * (p : ℝ) ^ (K - (n + 1) - w) :=
      mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hs))) (pow_pos (by exact_mod_cast hp.out.pos) _)
    exact_mod_cast this.ne'
  have hu : χ⁻¹ (-1) ≠ 0 := by
    intro h'; have := normSq_inv_neg_one (p := p) χ; rw [h', map_zero] at this; exact zero_ne_one this
  exact mul_ne_zero hr (mul_ne_zero hu (PAG.Part16.gaussSum_ne_zero hχ)) h0

/-- **3. ζ_k = (τ(χ)/√(p^c))^o**。 -/
theorem zeta_eq_gauss (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K)) (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w)) :
    (cnorm p K (K - (n + 1) - w) * 𝓕 (ket K w (n + 1) h χ) t₀) ^ orderOf χ
      = (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ := by
  set a := K - (n + 1) - w
  set k := ket K w (n + 1) h χ
  set o := orderOf χ
  set ts := (p : ZMod (p ^ K)) ^ a
  have hts := pa_mem_Tset K w n h χ hχ
  have hkd : KetDual (p := p) K a k := ⟨w, n, h, χ, hχ, rfl, rfl⟩
  -- t₀ を t* = p^a に取り替える
  have hswap : 𝓕 k t₀ ^ o = 𝓕 k ts ^ o := by
    obtain ⟨m, hm⟩ : ∃ m, o = m + 1 := ⟨o - 1, by have := orderOf_pos χ; omega⟩
    have hχo : χ ^ (m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one χ
    rw [hm]; exact PAG.Part98.pow_eigen_const K w (n + 1) h (by omega) χ hχ m hχo t₀ ts ht₀ hts
  rw [mul_pow, hswap, ← mul_pow]
  -- 実数の係数
  set r' : ℝ := (Real.sqrt (sz p K w))⁻¹ * (p : ℝ) ^ a
  set lam : ℝ := (p : ℝ) ^ K / (sz p K a : ℝ)
  have hl : 0 < lam := lam_pos K a
  have hr' : 0 < r' := by
    have hs : 0 < sz p K w := by
      unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
    exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hs))) (pow_pos (by exact_mod_cast hp.out.pos) _)
  have hval : 𝓕 k ts = (r' : ℂ) * (χ⁻¹ (-1) * gaussSum χ stdAddChar) := dft_ket_pa K w n h χ hχ
  -- ノルム: r'² p^c = λ
  have hnorm : r' ^ 2 * (p : ℝ) ^ (n + 1) = lam := by
    have e := (PAG.Part97.eigen_abs K a k hkd ts).1 hts
    rw [hval, map_mul, map_mul, Complex.normSq_ofReal, normSq_inv_neg_one, PAG.Part16.normSq_gaussSum hχ] at e
    show r' ^ 2 * (p : ℝ) ^ (n + 1) = (p : ℝ) ^ K / (sz p K a : ℝ)
    rw [← e]; push_cast; ring
  -- cnorm · r' = 1/√(p^c)
  have hcr : (Real.sqrt lam)⁻¹ * r' = (Real.sqrt ((p : ℝ) ^ (n + 1)))⁻¹ := by
    have hpc : (0 : ℝ) < (p : ℝ) ^ (n + 1) := pow_pos (by exact_mod_cast hp.out.pos) _
    rw [← pow_left_inj₀ (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hr'.le)
      (inv_nonneg.mpr (Real.sqrt_nonneg _)) (two_ne_zero)]
    rw [mul_pow, inv_pow, inv_pow, Real.sq_sqrt hl.le, Real.sq_sqrt hpc.le, ← hnorm]
    field_simp
  have hc : cnorm p K a * 𝓕 k ts
      = (((Real.sqrt ((p : ℝ) ^ (n + 1)))⁻¹ : ℝ) : ℂ) * (χ⁻¹ (-1) * gaussSum χ stdAddChar) := by
    rw [hval, ← mul_assoc, ← hcr]
    unfold cnorm
    push_cast; ring
  rw [hc, mul_pow, mul_pow, inv_neg_one_pow, one_mul, ← mul_pow]
  congr 1
  rw [div_eq_inv_mul]; push_cast; ring

/-- 系: ζ_k が 1 の冪根 ⟺ τ(χ)/√(p^c) が 1 の冪根。 -/
theorem zeta_root_iff (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K)) (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w)) :
    (∃ N : ℕ, 0 < N ∧ ((cnorm p K (K - (n + 1) - w) * 𝓕 (ket K w (n + 1) h χ) t₀) ^ orderOf χ) ^ N = 1) ↔
      (∃ N : ℕ, 0 < N ∧ (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ N = 1) := by
  rw [zeta_eq_gauss K w n h χ hχ t₀ ht₀]
  constructor
  · rintro ⟨N, hN, e⟩; exact ⟨orderOf χ * N, Nat.mul_pos (orderOf_pos χ) hN, by rw [pow_mul, e]⟩
  · rintro ⟨N, hN, e⟩; exact ⟨N, hN, by rw [← pow_mul, mul_comm, pow_mul, e, one_pow]⟩

end Ket

end PAG.Part117

#print axioms PAG.Part117.stdAddChar_mul_cast
#print axioms PAG.Part117.dft_pullback_mul
#print axioms PAG.Part117.dft_ket_pa
#print axioms PAG.Part117.inv_neg_one_pow
#print axioms PAG.Part117.normSq_inv_neg_one
#print axioms PAG.Part117.pa_mem_Tset
#print axioms PAG.Part117.zeta_eq_gauss
#print axioms PAG.Part117.zeta_root_iff
