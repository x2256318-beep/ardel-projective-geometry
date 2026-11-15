/-
  PAG 2.0 Part 125（2026-10-21）— 2 次ガウス和の位相の平方と、4 の因子の精密化
  p 奇素数について
  1. F が 2 次の関数等式をみたせば ((Σ F)/√p)^{2p} = L(−1)
  2. L(−1) = 1（p ≡ 1 mod 4）、= −1（p ≡ 3 mod 4）
  3. 導手 p^{2m+1}（m ≥ 1）: z = χ(u₀)e(u₀)q、q^{2p} = L(−1)
  4. p ≡ 1 (mod 4): ord z ∣ lcm(ord χ, p^c, 2)
  5. p ≡ 3 (mod 4): 4 ∣ ord z
-/
import PAG128

namespace PAG.Part129

open ZMod Finset PAG.Part118 PAG.Part119 PAG.Part120 PAG.Part127 PAG.Part128

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. ((Σ F)/√p)^{2p} = L(−1)**。 -/
theorem quad_pow_2p (hp2 : p ≠ 2) (F : ZMod p → ℂ) (a : ZMod p) (ha : a ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    ((∑ t, F t) / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * p) = Lc p (-1) := by
  obtain ⟨b, hb⟩ := quad_closed hp2 F a hF0 hF
  have h2 := two_ne_zero' (p := p) hp2
  set A := a * 2⁻¹
  have hA : A ≠ 0 := mul_ne_zero ha (inv_ne_zero h2)
  set κ := -(A * (b * (2 * A)⁻¹) ^ 2)
  have hsum : ∑ t, F t = stdAddChar κ * (Lc p A * gaussSum (Lc p) stdAddChar) := by
    rw [Finset.sum_congr rfl (fun t _ => hb t), complete_square A b hA h2, sum_sq_char hp2 A hA]
  have hsq : gaussSum (Lc p) stdAddChar ^ 2 = Lc p (-1) * p := by
    have := gaussSum_sq (χ := Lc p) (Lc_ne_one hp2) Lc_isQuadratic (ZMod.isPrimitive_stdAddChar p)
    rw [ZMod.card] at this; exact this
  have hψ : stdAddChar κ ^ (2 * p) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    push_cast
    rw [ZMod.natCast_self]; simp
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hL : Lc p (-1) ^ p = Lc p (-1) := by
    obtain ⟨k, hk⟩ := hodd
    have key : ∀ x : ℂ, x ^ 2 = 1 → x ^ p = x := fun x hx => by
      rw [hk, pow_succ, pow_mul, hx, one_pow, one_mul]
    exact key _ (Lc_sq (-1) (neg_ne_zero.mpr one_ne_zero))
  have hs : ((Real.sqrt p : ℝ) : ℂ) ^ (2 * p) = (p : ℂ) ^ p := by
    rw [pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hp.out.pos.le)]
    push_cast; ring
  have hp0 : (p : ℂ) ^ p ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [div_pow, hs, hsum, mul_pow, mul_pow, hψ, one_mul, pow_mul (Lc p A), Lc_sq A hA, one_pow, one_mul,
    pow_mul, hsq, mul_pow, hL, mul_div_assoc, div_self hp0, mul_one]

/-- **2a. p ≡ 1 (mod 4) なら L(−1) = 1**。 -/
theorem Lc_neg_one_of_one (h : p % 4 = 1) : Lc p (-1) = 1 := by
  have hp2 : p ≠ 2 := by intro h2; subst h2; norm_num at h
  rw [Lc_apply, quadraticChar_neg_one (ringChar_ne_two hp2), ZMod.card, ZMod.χ₄_nat_one_mod_four h]
  simp

/-- **2b. p ≡ 3 (mod 4) なら L(−1) = −1**。 -/
theorem Lc_neg_one_of_three (h : p % 4 = 3) : Lc p (-1) = -1 := by
  have hp2 : p ≠ 2 := by intro h2; subst h2; norm_num at h
  rw [Lc_apply, quadraticChar_neg_one (ringChar_ne_two hp2), ZMod.card, ZMod.χ₄_nat_three_mod_four h]
  simp

section Odd

variable {c m : ℕ} (hc : c = 2 * m + 1) (hm : 1 ≤ m)

include hc hm in
/-- **3. 位相の明示形（q^{2p} = L(−1) つき）**。 -/
theorem gauss_odd_phase2 (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧ ∃ q : ℂ, q ^ (4 * p) = 1 ∧ (p ≠ 2 → q ^ (2 * p) = Lc p (-1)) ∧
      gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ) = χ u₀ * stdAddChar u₀ * q := by
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
  have hτ0 := PAG.Part16.gaussSum_ne_zero hχ
  rw [hτ] at hτ0
  obtain ⟨u₀, hu₀S, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ0
  have hχu₀ : χ u₀ ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have hunit : IsUnit u₀ := by by_contra hn; exact hχu₀ (MulChar.map_nonunit χ hn)
  have hS₀ : ∀ y, phiP χ P y * e (P * u₀ * y) = 1 := (Finset.mem_filter.mp hu₀S).2
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
  refine ⟨u₀, hunit, (∑ x, H x) / ((Real.sqrt p : ℝ) : ℂ), hq, fun hp2 => quad_pow_2p hp2 H a ha hH0 hHfe, ?_⟩
  have hr0 : (rR : ℂ) ≠ 0 := by exact_mod_cast hrR.ne'
  rw [hτε, ← hr, mul_div_cancel_left₀ _ hr0]



include hc hm in
/-- **4. p ≡ 1 (mod 4)**: ord z ∣ lcm(lcm(ord χ, p^c), 2)。 -/
theorem orderOf_gauss_odd_one_mod_four (h4 : p % 4 = 1) (χ : DirichletCharacter ℂ (p ^ c))
    (hχ : χ.IsPrimitive) :
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ))
      ∣ Nat.lcm (Nat.lcm (orderOf χ) (p ^ c)) 2 := by
  have hp2 : p ≠ 2 := by intro h2; subst h2; norm_num at h4
  obtain ⟨u₀, hu, q, -, hq2, hz⟩ := gauss_odd_phase2 hc hm χ hχ
  have hq : q ^ (2 * p) = 1 := by rw [hq2 hp2, Lc_neg_one_of_one h4]
  rw [hz]
  apply orderOf_dvd_of_pow_eq_one
  set L := Nat.lcm (Nat.lcm (orderOf χ) (p ^ c)) 2
  have h1 : χ u₀ ^ L = 1 := by
    obtain ⟨k, hk⟩ := (Nat.dvd_lcm_left (orderOf χ) (p ^ c)).trans (Nat.dvd_lcm_left _ 2)
    rw [show L = orderOf χ * k from hk, pow_mul, ← MulChar.pow_apply' _ (orderOf_pos χ).ne',
      pow_orderOf_eq_one, MulChar.one_apply hu, one_pow]
  have h2 : stdAddChar u₀ ^ L = 1 :=
    (stdAddChar_pow_eq_one_iff (p := p) u₀ hu L).mpr
      ((Nat.dvd_lcm_right (orderOf χ) (p ^ c)).trans (Nat.dvd_lcm_left _ 2))
  have h3 : 2 * p ∣ L := by
    have hpL : p ∣ L := (dvd_pow_self p (by omega)).trans ((Nat.dvd_lcm_right (orderOf χ) (p ^ c)).trans
      (Nat.dvd_lcm_left _ 2))
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2)
    exact hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_right _ 2) hpL
  obtain ⟨k, hk⟩ := h3
  rw [mul_pow, mul_pow, h1, h2, one_mul, one_mul, hk, pow_mul, hq, one_pow]

include hc hm in
/-- **5. p ≡ 3 (mod 4)**: 4 ∣ ord z。 -/
theorem four_dvd_orderOf_gauss_odd (h4 : p % 4 = 3) (χ : DirichletCharacter ℂ (p ^ c))
    (hχ : χ.IsPrimitive) :
    4 ∣ orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) := by
  have hp2 : p ≠ 2 := by intro h2; subst h2; norm_num at h4
  obtain ⟨u₀, hu, q, -, hq2, hz⟩ := gauss_odd_phase2 hc hm χ hχ
  have hq : q ^ (2 * p) = -1 := by rw [hq2 hp2, Lc_neg_one_of_three h4]
  set z := gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)
  -- s = p^{c-1}·((p-1)/2) は奇数、z^{2ps} = −1
  set s := p ^ (c - 1) * ((p - 1) / 2)
  have hs_odd : Odd s := by
    apply Odd.mul (Odd.pow (hp.out.odd_of_ne_two hp2))
    refine ⟨(p - 3) / 4, by omega⟩
  have hφ : 2 * p * s = p ^ c * (p - 1) := by
    have h2 : 2 * ((p - 1) / 2) = p - 1 := by omega
    have hpc : p * p ^ (c - 1) = p ^ c := by rw [← pow_succ']; congr 1; omega
    calc 2 * p * s = p * p ^ (c - 1) * (2 * ((p - 1) / 2)) := by simp only [s]; ring
      _ = _ := by rw [h2, hpc]
  have hz2 : z ^ (2 * p * s) = -1 := by
    rw [hz]
    have h1 : χ u₀ ^ (2 * p * s) = 1 := by
      rw [hφ, show p ^ c * (p - 1) = p * (p ^ (c - 1) * (p - 1)) by
        rw [← mul_assoc, ← pow_succ']; congr 2; omega, pow_mul',
        ← Nat.totient_prime_pow hp.out (by omega : 0 < c), chi_pow_totient χ u₀ hu, one_pow]
    have h2 : stdAddChar u₀ ^ (2 * p * s) = 1 :=
      (stdAddChar_pow_eq_one_iff (p := p) u₀ hu _).mpr ⟨p - 1, hφ⟩
    rw [mul_pow, mul_pow, h1, h2, one_mul, one_mul, pow_mul, hq, hs_odd.neg_one_pow]
  -- ord z が 4 で割れなければ矛盾
  by_contra hn
  set o := orderOf z
  obtain ⟨t, ht_odd, hot⟩ : ∃ t, Odd t ∧ o ∣ 2 * t := by
    rcases Nat.even_or_odd o with ⟨k, hk⟩ | hodd
    · refine ⟨k, ?_, ⟨1, by omega⟩⟩
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | hk'
      · exact absurd ⟨j, by omega⟩ hn
      · exact hk'
    · exact ⟨o, hodd, dvd_mul_left _ _⟩
  have e1 : z ^ (2 * t * (p * s)) = 1 := by
    obtain ⟨r, hr⟩ := hot
    rw [hr, mul_assoc, pow_mul, pow_orderOf_eq_one, one_pow]
  have e2 : z ^ (2 * t * (p * s)) = -1 := by
    rw [show 2 * t * (p * s) = 2 * p * s * t by ring, pow_mul, hz2, ht_odd.neg_one_pow]
  rw [e1] at e2
  norm_num at e2

end Odd

end PAG.Part129

#print axioms PAG.Part129.quad_pow_2p
#print axioms PAG.Part129.Lc_neg_one_of_one
#print axioms PAG.Part129.Lc_neg_one_of_three
#print axioms PAG.Part129.gauss_odd_phase2
#print axioms PAG.Part129.orderOf_gauss_odd_one_mod_four
#print axioms PAG.Part129.four_dvd_orderOf_gauss_odd
