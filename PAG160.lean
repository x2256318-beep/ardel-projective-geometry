/-
  PAG 2.0 Part 156（2026-10-22）— 2 次の因子 q の明示形と、p ≡ 1・ord χ 奇数での ζ^p
  1. quad_explicit: 2 次の関数等式の解 H について (Σ H)/√p = e(κ) L(a/2) ε、ε = τ(L)/√p
  2. phase_explicit: 導手 p^{2m+1}、停留点 u₀ で z = χ(u₀) e(u₀) · e(κ) L(ū₀/2) ε
  3. Q_explicit: Q = q^{p^n} = L(A) ε^{p^n}
  4. zeta_pow_p: ζ^p = (q^{p^{n+1}})^{s'}
  5. zeta_p_one_odd: p ≡ 1、ord χ 奇数 ⇒ ζ^p = L(−δ/2) ε、ε² = 1。ord ζ = p ⇔ L(−δ/2) = ε
-/
import PAG159

namespace PAG.Part160

open ZMod Finset PAG.Part118 PAG.Part119 PAG.Part120 PAG.Part127 PAG.Part128 PAG.Part129 PAG.Part156

variable {p : ℕ} [hp : Fact p.Prime]

/-- ε = τ(L)/√p（χ によらない定数）。 -/
noncomputable def epsG (p : ℕ) [Fact p.Prime] : ℂ := gaussSum (Lc p) stdAddChar / ((Real.sqrt p : ℝ) : ℂ)

theorem epsG_sq (hp2 : p ≠ 2) : epsG p ^ 2 = Lc p (-1) := by
  have hsq : gaussSum (Lc p) stdAddChar ^ 2 = Lc p (-1) * p := by
    have := gaussSum_sq (χ := Lc p) (Lc_ne_one hp2) Lc_isQuadratic (ZMod.isPrimitive_stdAddChar p)
    rw [ZMod.card] at this; exact this
  have hs : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hp.out.pos.le)]; push_cast; ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [epsG, div_pow, hsq, hs, mul_div_assoc, div_self hp0, mul_one]

/-- **1. (Σ H)/√p = e(κ) L(a/2) ε**。 -/
theorem quad_explicit (hp2 : p ≠ 2) (F : ZMod p → ℂ) (a : ZMod p) (ha : a ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    ∃ κ : ZMod p, (∑ t, F t) / ((Real.sqrt p : ℝ) : ℂ) = stdAddChar κ * Lc p (a * 2⁻¹) * epsG p := by
  obtain ⟨b, hb⟩ := quad_closed hp2 F a hF0 hF
  have h2 := two_ne_zero' (p := p) hp2
  set A := a * 2⁻¹
  have hA : A ≠ 0 := mul_ne_zero ha (inv_ne_zero h2)
  refine ⟨-(A * (b * (2 * A)⁻¹) ^ 2), ?_⟩
  rw [Finset.sum_congr rfl (fun t _ => hb t), complete_square A b hA h2, sum_sq_char hp2 A hA, epsG]
  ring

section Odd

variable {c m : ℕ} (hc : c = 2 * m + 1) (hm : 1 ≤ m)

include hc hm in
/-- **2. 位相の明示形**：z = χ(u₀) e(u₀) · e(κ) L(ū₀/2) ε。 -/
theorem phase_explicit (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) (u₀ : ZMod (p ^ c))
    (hunit : IsUnit u₀)
    (hS₀ : ∀ y, phiP χ ((p : ZMod (p ^ c)) ^ (m + 1)) y * stdAddChar ((p : ZMod (p ^ c)) ^ (m + 1) * u₀ * y) = 1) :
    ∃ κ : ZMod p, gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)
      = χ u₀ * stdAddChar u₀ * (stdAddChar κ * Lc p ((u₀.cast : ZMod p) * 2⁻¹) * epsG p) := by
  classical
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set Q : ZMod (p ^ c) := (p : ZMod (p ^ c)) ^ m
  set P : ZMod (p ^ c) := (p : ZMod (p ^ c)) ^ (m + 1)
  set e : AddChar (ZMod (p ^ c)) ℂ := stdAddChar
  have hP : P * P = 0 := by
    simp only [P]; rw [← pow_add]; exact pow_zero_of_le _ (by omega)
  have hPQ : P * Q = 0 := by
    simp only [P, Q]; rw [← pow_add]; exact pow_zero_of_le _ (by omega)
  have hQ3 : Q * Q * Q = 0 := by
    simp only [Q]; rw [← pow_add, ← pow_add]; exact pow_zero_of_le _ (by omega)
  have hQQp : Q * Q * (p : ZMod (p ^ c)) = 0 := by
    simp only [Q]; rw [← pow_add, ← pow_succ]; exact pow_zero_of_le _ (by omega)
  have hQp : Q * (p : ZMod (p ^ c)) = P := by simp only [Q, P]; rw [← pow_succ]
  have hQQ : Q * Q = P * (p : ZMod (p ^ c)) ^ (m - 1) := by
    simp only [Q, P]; rw [← pow_add, ← pow_add]; congr 1; omega
  -- 平均化と u₀
  have hτ := gauss_eq_sum_SP χ P hP
  set S := univ.filter (fun u : ZMod (p ^ c) => ∀ y, phiP χ P y * e (P * u * y) = 1)
  -- S = u₀ + Q ℤ/N
  have memS : ∀ u, u ∈ S ↔ ∃ z, u = u₀ + Q * z := by
    intro u
    constructor
    · intro hu
      have h1 := (Finset.mem_filter.mp hu).2 1
      have h2 := hS₀ 1
      rw [mul_one] at h1 h2
      have hφ : phiP χ P 1 ≠ 0 := by intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
      have hPu : P * u = P * u₀ := ZMod.injective_stdAddChar (mul_left_cancel₀ hφ (h1.trans h2.symm))
      obtain ⟨z, hz⟩ := divQ (p := p) hc (u - u₀) (by rw [mul_sub, hPu, sub_self])
      exact ⟨z, by linear_combination hz⟩
    · rintro ⟨z, rfl⟩
      refine Finset.mem_filter.mpr ⟨mem_univ _, fun y => ?_⟩
      rw [show P * (u₀ + Q * z) * y = P * u₀ * y + (P * Q) * (z * y) by ring, hPQ, zero_mul, add_zero]
      exact hS₀ y
  -- 数え上げ: Σ_t f(u₀ + Q t) = κ Σ_S f
  set μ : ZMod (p ^ c) →+ ZMod (p ^ c) := AddMonoidHom.mulLeft Q
  set κ := (univ.filter (fun t : ZMod (p ^ c) => μ t = 0)).card
  have hcount : ∀ f : ZMod (p ^ c) → ℂ, ∑ t, f (u₀ + Q * t) = (κ : ℂ) * ∑ u ∈ S, f u := by
    intro f
    have e1 : ∑ t, f (u₀ + Q * t) = ∑ t, (fun w => f (u₀ + w)) (μ t) := rfl
    rw [e1, Finset.sum_comp (fun w => f (u₀ + w)) μ]
    have e2 : ∀ w ∈ univ.image μ, (univ.filter (fun t => μ t = w)).card = κ := by
      intro w hw
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hw
      exact AddMonoidHom.card_fiber_eq_of_mem_range μ ⟨t, rfl⟩ ⟨0, map_zero μ⟩
    rw [Finset.sum_congr rfl (fun w hw => by rw [e2 w hw]), ← Finset.smul_sum, nsmul_eq_mul]
    congr 1
    refine Finset.sum_nbij' (fun w => u₀ + w) (fun u => u - u₀) ?_ ?_ ?_ ?_ ?_
    · intro w hw
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hw
      exact (memS _).mpr ⟨t, rfl⟩
    · intro u hu
      obtain ⟨z, rfl⟩ := (memS u).mp hu
      exact Finset.mem_image.mpr ⟨z, mem_univ _, by simp [μ]⟩
    · intro w _; simp
    · intro u _; simp
    · intro w _; rfl
  -- 付け替え t = u₀ s と h の定義
  set h : ZMod (p ^ c) → ℂ := fun s => χ (1 + Q * s) * e (u₀ * Q * s)
  have hre : ∑ t, χ (u₀ + Q * t) * e (u₀ + Q * t) = χ u₀ * e u₀ * ∑ s, h s := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Units.mulLeft hunit.unit) (fun s => χ (u₀ + Q * (u₀ * s)) * e (u₀ + Q * (u₀ * s)))
      _ (fun s => rfl)).symm.trans ?_
    apply sum_congr rfl; intro s _
    simp only [h]
    rw [show u₀ + Q * (u₀ * s) = u₀ * (1 + Q * s) by ring, map_mul,
      show u₀ * (1 + Q * s) = u₀ + u₀ * Q * s by ring, AddChar.map_add_eq_mul]
    ring
  -- h の性質
  have h0 : h 0 = 1 := by simp [h]
  have hQQchar : ∀ w, χ (1 + Q * Q * w) * e (u₀ * Q * Q * w) = 1 := by
    intro w
    have := hS₀ ((p : ZMod (p ^ c)) ^ (m - 1) * w)
    simp only [phiP] at this
    have e1 : P * ((p : ZMod (p ^ c)) ^ (m - 1) * w) = Q * Q * w := by linear_combination (-w) * hQQ
    have e2 : P * u₀ * ((p : ZMod (p ^ c)) ^ (m - 1) * w) = u₀ * Q * Q * w := by linear_combination (-(u₀ * w)) * hQQ
    rw [e1, e2] at this
    exact this
  have hhom : ∀ t s, h (t + s) = h t * h s * e (u₀ * Q * Q * t * s) := by
    intro t s
    have hprod : (1 + Q * t) * (1 + Q * s) = (1 + Q * (t + s)) * (1 + Q * Q * (t * s)) := by
      linear_combination (-(t + s) * (t * s)) * hQ3
    have hc1 := hQQchar (t * s)
    simp only [h]
    have hχ2 : χ (1 + Q * t) * χ (1 + Q * s) = χ (1 + Q * (t + s)) * χ (1 + Q * Q * (t * s)) := by
      rw [← map_mul, hprod, map_mul]
    have he2 : e (u₀ * Q * (t + s)) = e (u₀ * Q * t) * e (u₀ * Q * s) := by
      rw [mul_add, AddChar.map_add_eq_mul]
    calc χ (1 + Q * (t + s)) * e (u₀ * Q * (t + s))
        = χ (1 + Q * (t + s)) * e (u₀ * Q * (t + s)) *
            (χ (1 + Q * Q * (t * s)) * e (u₀ * Q * Q * (t * s))) := by rw [hc1, mul_one]
      _ = χ (1 + Q * t) * e (u₀ * Q * t) * (χ (1 + Q * s) * e (u₀ * Q * s)) * e (u₀ * Q * Q * t * s) := by
          rw [show u₀ * Q * Q * t * s = u₀ * Q * Q * (t * s) by ring, he2]
          linear_combination (-(e (u₀ * Q * t) * e (u₀ * Q * s) * e (u₀ * Q * Q * (t * s)))) * hχ2
  have hper : ∀ t y, h (t + (p : ZMod (p ^ c)) * y) = h t := by
    intro t y
    rw [hhom, show u₀ * Q * Q * t * ((p : ZMod (p ^ c)) * y) = (Q * Q * (p : ZMod (p ^ c))) * (u₀ * t * y) by ring, hQQp,
      zero_mul, AddChar.map_zero_eq_one, mul_one]
    have : h ((p : ZMod (p ^ c)) * y) = 1 := by
      simp only [h]
      have := hS₀ y
      simp only [phiP] at this
      rw [show Q * ((p : ZMod (p ^ c)) * y) = P * y by rw [← hQp]; ring,
        show u₀ * Q * ((p : ZMod (p ^ c)) * y) = P * u₀ * y by rw [← hQp]; ring]
      exact this
    rw [this, mul_one]
  -- ℤ/p への降下
  have hdvd : p ∣ p ^ c := dvd_pow_self p (by omega)
  set π := ZMod.castHom hdvd (ZMod p)
  set H : ZMod p → ℂ := fun x => h ((x.val : ZMod (p ^ c)))
  have hπ : ∀ t, h t = H (π t) := by
    intro t
    have hv : (π t).val = t.val % p := by
      simp only [π, ZMod.castHom_apply]; rw [ZMod.cast_eq_val, ZMod.val_natCast]
    simp only [H, hv]
    conv_lhs => rw [← ZMod.natCast_zmod_val t, ← Nat.mod_add_div t.val p]
    push_cast
    exact hper _ _
  have hπlift : ∀ x : ZMod p, π ((x.val : ZMod (p ^ c))) = x := by
    intro x; rw [map_natCast, ZMod.natCast_zmod_val]
  set a := π u₀
  have ha : a ≠ 0 := (hunit.map π).ne_zero
  have hH0 : H 0 = 1 := by simp only [H, ZMod.val_zero, Nat.cast_zero]; exact h0
  have hHfe : ∀ x y, H (x + y) = H x * H y * stdAddChar (a * x * y) := by
    intro x y
    set x' : ZMod (p ^ c) := (x.val : ZMod (p ^ c))
    set y' : ZMod (p ^ c) := (y.val : ZMod (p ^ c))
    have e1 : H (x + y) = h (x' + y') := by rw [hπ (x' + y'), map_add, hπlift, hπlift]
    rw [e1, hhom]
    have e3 : e (u₀ * Q * Q * x' * y') = stdAddChar (a * x * y) := by
      have hd : p ^ c = p * p ^ (2 * m) := by rw [← pow_succ']; congr 1
      have := PAG.Part117.stdAddChar_mul_cast hdvd (p ^ (2 * m)) hd (u₀ * x' * y')
      rw [show ((p ^ (2 * m) : ℕ) : ZMod (p ^ c)) * (u₀ * x' * y') = u₀ * Q * Q * x' * y' by
        simp only [Q]; push_cast; rw [show 2 * m = m + m by ring, pow_add]; ring] at this
      rw [this]; congr 1; rw [map_mul π, map_mul π, hπlift, hπlift]
    rw [e3]
  -- Σ h = κ' Σ H
  have hsurj : Function.Surjective π.toAddMonoidHom := ZMod.ringHom_surjective _
  set κ' := (univ.filter (fun t : ZMod (p ^ c) => π.toAddMonoidHom t = 0)).card
  have hsumh : ∑ s, h s = (κ' : ℂ) * ∑ x, H x := by
    rw [Finset.sum_congr rfl (fun t _ => hπ t)]
    exact PAG.Part17.sum_comp_surj π.toAddMonoidHom hsurj H
  -- 組み立て
  set τ := gaussSum χ stdAddChar
  have hκτ : (κ : ℂ) * τ = χ u₀ * e u₀ * ((κ' : ℂ) * ∑ x, H x) := by
    rw [← hsumh, ← hre, hcount (fun u => χ u * e u), ← hτ]
  have hκ0 : (κ : ℂ) ≠ 0 := by
    have : 0 < κ := Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨mem_univ _, map_zero μ⟩⟩
    exact_mod_cast this.ne'
  have hκ'0 : 0 < κ' := Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨mem_univ _, map_zero _⟩⟩
  have hsp : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)
  have hspC : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsp.ne'
  set ε := χ u₀ * e u₀ * ((∑ x, H x) / ((Real.sqrt p : ℝ) : ℂ))
  set rR : ℝ := (κ' : ℝ) * Real.sqrt p / κ
  have hrR : 0 < rR := by
    apply div_pos (mul_pos (by exact_mod_cast hκ'0) hsp)
    have : 0 < κ := Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨mem_univ _, map_zero μ⟩⟩
    exact_mod_cast this
  have hτε : τ = (rR : ℂ) * ε := by
    apply mul_left_cancel₀ hκ0
    rw [hκτ]; simp only [rR, ε]; push_cast; field_simp
  -- ε^M = 1
  set o := orderOf χ
  have hq := quad_root_all H a ha hH0 hHfe
  set M := o * p ^ c * (4 * p)
  have hMpos : 0 < M := Nat.mul_pos (Nat.mul_pos (orderOf_pos χ) (pow_pos hp.out.pos _)) (by have := hp.out.pos; omega)
  have hεM : ε ^ M = 1 := by
    have h1 : χ u₀ ^ o = 1 := by
      rw [← MulChar.pow_apply' _ (orderOf_pos χ).ne', pow_orderOf_eq_one]; exact MulChar.one_apply hunit
    have h2 : e u₀ ^ (p ^ c) = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    have hA : (χ u₀ * e u₀) ^ (o * p ^ c) = 1 := by
      rw [mul_pow, pow_mul, h1, one_pow, one_mul, mul_comm, pow_mul, h2, one_pow]
    simp only [ε, M]
    rw [mul_pow, pow_mul, hA, one_pow, one_mul, mul_comm (o * p ^ c), pow_mul, hq, one_pow]
  have hεn : Complex.normSq ε = 1 := by
    have h := congrArg Complex.normSq hεM
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg ε) hMpos.ne').mp h
  -- r = √(p^c)
  have hpc : (0 : ℝ) < (p : ℝ) ^ c := pow_pos (by exact_mod_cast hp.out.pos) _
  have hr2 : rR ^ 2 = (p : ℝ) ^ c := by
    have h : Complex.normSq τ = ((p ^ c : ℕ) : ℝ) := PAG.Part16.normSq_gaussSum hχ
    rw [hτε, map_mul, hεn, mul_one, Complex.normSq_ofReal] at h
    rw [sq, h]; push_cast; ring
  have hr : rR = Real.sqrt ((p : ℝ) ^ c) := by
    rw [← hr2, Real.sqrt_sq hrR.le]
  obtain ⟨κ0, hk⟩ := quad_explicit hp2 H a ha hH0 hHfe
  refine ⟨κ0, ?_⟩
  have hr0 : (rR : ℂ) ≠ 0 := by exact_mod_cast hrR.ne'
  rw [hτε, ← hr, mul_div_cancel_left₀ _ hr0]
  simp only [ε]
  rw [hk]
  simp only [a, π, ZMod.castHom_apply]

end Odd

theorem pow_odd_of_sq_one (x : ℂ) (hx : x ^ 2 = 1) (k : ℕ) (hk : Odd k) : x ^ k = x := by
  obtain ⟨j, rfl⟩ := hk; rw [pow_succ, pow_mul, hx, one_pow, one_mul]

/-- **3. Q = q^{p^n} = L(A) ε^{p^n}**（n ≥ 1）。 -/
theorem Q_explicit (hp2 : p ≠ 2) (n : ℕ) (hn : 1 ≤ n) (κ A : ZMod p) (hA : A ≠ 0) :
    (stdAddChar κ * Lc p A * epsG p) ^ (p ^ n) = Lc p A * epsG p ^ (p ^ n) := by
  have hψ : (stdAddChar κ : ℂ) ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  have hψn : (stdAddChar κ : ℂ) ^ (p ^ n) = 1 := by
    rw [show p ^ n = p * p ^ (n - 1) by rw [← pow_succ']; congr 1; omega, pow_mul, hψ, one_pow]
  have hodd : Odd (p ^ n) := (hp.out.odd_of_ne_two hp2).pow
  rw [mul_pow, mul_pow, hψn, one_mul, pow_odd_of_sq_one _ (Lc_sq A hA) _ hodd]
/-- **4. ζ^p = (q^{p^{n+1}})^{s'}**。 -/
theorem zeta_pow_p (n : ℕ) (χ : DirichletCharacter ℂ (p ^ (n + 1))) (u₀ : ZMod (p ^ (n + 1))) (hu : IsUnit u₀)
    (q : ℂ) (s' : ℕ) (hs : orderOf χ = p ^ n * s') :
    ((χ u₀ * stdAddChar u₀ * q) ^ orderOf χ) ^ p = (q ^ (p ^ (n + 1))) ^ s' := by
  have h1 : χ u₀ ^ orderOf χ = 1 := by
    rw [← MulChar.pow_apply' _ (orderOf_pos χ).ne', pow_orderOf_eq_one]; exact MulChar.one_apply hu
  have h2 : (stdAddChar u₀ : ℂ) ^ (p ^ (n + 1)) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  rw [← pow_mul, mul_pow, mul_pow, pow_mul (χ u₀), h1, one_pow, one_mul,
    show orderOf χ * p = p ^ (n + 1) * s' by rw [hs]; ring, pow_mul, h2, one_pow, one_mul, pow_mul]

/-- **5. p ≡ 1、導手 p^{2m+1}、ord χ 奇数：ζ^p = L(−δ/2) ε、ε² = 1**。 -/
theorem zeta_p_one_odd (h4 : p % 4 = 1) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (δ : ZMod (p ^ (n + 1)))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ (n + 1))) ^ (m + 1) * y) = stdAddChar ((p : ZMod (p ^ (n + 1))) ^ (m + 1) * δ * y))
    (hodd : ¬ 2 ∣ orderOf χ) :
    ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ^ p
      = Lc p (((-δ : ZMod (p ^ (n + 1))).cast : ZMod p) * 2⁻¹) * epsG p ∧ epsG p ^ 2 = 1 := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  have hn : 1 ≤ n := by omega
  have hε : epsG p ^ 2 = 1 := by rw [epsG_sq hp2, PAG.Part129.Lc_neg_one_of_one h4]
  refine ⟨?_, hε⟩
  obtain ⟨u₀, hu, hS₀⟩ := PAG.Part139.exists_unit_SP (p := p) (k := m + 1) (by omega) χ hχ
  obtain ⟨κ, hz⟩ := phase_explicit hnm hm hp2 χ hχ u₀ hu hS₀
  have hcast := PAG.Part142.stationary_cast (p := p) (k := m + 1) (by omega) χ δ hδ u₀ hS₀
  obtain ⟨s', hs, -, -⟩ := PAG.Part157.order_chi_split hp2 n hn χ hχ
  have hs'odd : Odd s' := by
    rw [Nat.odd_iff]; rcases Nat.mod_two_eq_zero_or_one s' with h | h
    · exact absurd (hs ▸ Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) _) hodd
    · exact h
  have hdvd : p ∣ p ^ (n + 1) := dvd_pow_self p (by omega)
  have hu0 : ((u₀.cast : ZMod p)) ≠ 0 := by
    have := (hu.map (ZMod.castHom hdvd (ZMod p))).ne_zero
    simpa [ZMod.castHom_apply] using this
  have hA : (u₀.cast : ZMod p) * 2⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero (two_ne_zero' hp2))
  have hX : (Lc p ((u₀.cast : ZMod p) * 2⁻¹) * epsG p) ^ 2 = 1 := by
    rw [mul_pow, Lc_sq _ hA, hε, one_mul]
  have hpo : Odd (p ^ n) := (hp.out.odd_of_ne_two hp2).pow
  rw [hz, zeta_pow_p n χ u₀ hu _ s' hs,
    show ∀ x : ℂ, x ^ (p ^ (n + 1)) = (x ^ (p ^ n)) ^ p from fun x => by rw [pow_succ, pow_mul], Q_explicit hp2 n hn κ _ hA,
    pow_odd_of_sq_one _ hε _ hpo, pow_odd_of_sq_one _ hX _ (hp.out.odd_of_ne_two hp2),
    pow_odd_of_sq_one _ hX _ hs'odd, hcast]

/-- **6. p ≡ 1、ord χ 奇数：ord ζ = p ⇔ L(−δ/2) = ε**。 -/
theorem zeta_order_one_odd_iff (h4 : p % 4 = 1) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (δ : ZMod (p ^ (n + 1)))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ (n + 1))) ^ (m + 1) * y) = stdAddChar ((p : ZMod (p ^ (n + 1))) ^ (m + 1) * δ * y))
    (hodd : ¬ 2 ∣ orderOf χ) :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = p ↔
      Lc p (((-δ : ZMod (p ^ (n + 1))).cast : ZMod p) * 2⁻¹) = epsG p := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  obtain ⟨hzp, hε⟩ := zeta_p_one_odd h4 n m hnm hm χ hχ δ hδ hodd
  obtain ⟨-, hpd, -⟩ := PAG.Part157.zeta_order_odd hp2 n m hnm hm χ hχ
  set ζ := (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ
  set L := Lc p (((-δ : ZMod (p ^ (n + 1))).cast : ZMod p) * 2⁻¹)
  have key : L * epsG p = 1 ↔ L = epsG p := by
    constructor
    · intro h
      calc L = L * epsG p * epsG p := by rw [mul_assoc, ← sq, hε, mul_one]
        _ = epsG p := by rw [h, one_mul]
    · intro h; rw [h, ← sq, hε]
  rw [← key, ← hzp]
  constructor
  · intro h; rw [← h]; exact pow_orderOf_eq_one ζ
  · intro h; exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h) hpd

end PAG.Part160

#print axioms PAG.Part160.epsG_sq
#print axioms PAG.Part160.quad_explicit
#print axioms PAG.Part160.phase_explicit
#print axioms PAG.Part160.Q_explicit
#print axioms PAG.Part160.zeta_pow_p
#print axioms PAG.Part160.zeta_p_one_odd
#print axioms PAG.Part160.zeta_order_one_odd_iff
#print axioms PAG.Part160.pow_odd_of_sq_one
