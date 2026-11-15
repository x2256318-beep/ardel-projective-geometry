/-
  PAG 2.0 Part 116（2026-10-20）— 導手 p^{2m+1} のガウス和と ζ_k の冪根性（すべての素数）
  N = p^c、c = 2m + 1（m ≥ 1）、χ 原始について
  0. p = 2 を含む 2 次の補題: F(t+s) = F(t)F(s)ψ(a t s)、F(0) = 1、a ≠ 0 ⇒ (Σ F/√p)^{4p} = 1
  1. 一般の平均化（P² = 0 をみたす任意の P）: τ = Σ_{u∈S_P} χ(u)e(u)
  2. P = p^{m+1}、Q = p^m として S_P = u₀ + Q·ℤ/N、Σ_t f(u₀ + Q t) = κ Σ_{S_P} f
  3. h(t) = χ(1 + Q t) e(u₀ Q t) は h(t+s) = h(t)h(s) e(u₀ Q² t s)、p 周期 ⇒ ℤ/p 上の 2 次の関数等式
  4. τ/√(p^c) は 1 の冪根
  系: 導手 p^c（c ≥ 2）の原始ケットの ζ_k はすべて 1 の冪根（Part 114 と合わせて）
-/
import PAG119

namespace PAG.Part120

open ZMod Finset PAG.Part118 PAG.Part119

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## 0. p = 2 の 2 次の補題と、すべての素数での統一形 -/

theorem psi_two_one : stdAddChar (1 : ZMod 2) = -1 := by
  rw [show (1 : ZMod 2) = ((1 : ℕ) : ZMod 2) by simp, stdAddChar_apply, toCircle_natCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) / ((2 : ℕ) : ℂ) = Real.pi * Complex.I by push_cast; ring,
    Complex.exp_pi_mul_I]

theorem quad_root_two (F : ZMod 2 → ℂ) (a : ZMod 2) (ha : a ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    ((∑ t, F t) / ((Real.sqrt 2 : ℝ) : ℂ)) ^ (4 * 2) = 1 := by
  have ha1 : a = 1 := by
    fin_cases a
    · exact absurd rfl ha
    · rfl
  subst ha1
  have h11 := hF 1 1
  rw [show (1 : ZMod 2) + 1 = 0 by decide, hF0, mul_one, mul_one, psi_two_one] at h11
  have hsq : F 1 ^ 2 = -1 := by linear_combination h11
  have hsum : ∑ t, F t = 1 + F 1 := by
    rw [Fintype.sum_eq_add 0 1 (by decide) (fun x hx => by fin_cases x; exacts [absurd rfl hx.1, absurd rfl hx.2]), hF0]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num); exact_mod_cast this.ne'
  rw [hsum, div_pow]
  have e1 : (1 + F 1) ^ 2 = 2 * F 1 := by linear_combination hsq
  have e2 : (1 + F 1) ^ (4 * 2) = 16 := by
    rw [show 4 * 2 = 2 * 4 by norm_num, pow_mul, e1, mul_pow, show F 1 ^ 4 = (F 1 ^ 2) ^ 2 by ring, hsq]; norm_num
  have e3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ (4 * 2) = 16 := by
    rw [show 4 * 2 = 2 * 4 by norm_num, pow_mul, hs]; norm_num
  rw [e2, e3]; norm_num

/-- **0. 統一形**（すべての素数）。 -/
theorem quad_root_all (F : ZMod p → ℂ) (a : ZMod p) (ha : a ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    ((∑ t, F t) / ((Real.sqrt p : ℝ) : ℂ)) ^ (4 * p) = 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    exact_mod_cast quad_root_two F a ha hF0 hF
  · exact quad_root' hp2 F a ha hF0 hF

/-! ## 1. 一般の平均化 -/

section Avg

variable {c : ℕ}

/-- φ_P(y) = χ(1 + P y)。 -/
noncomputable def phiP (χ : DirichletCharacter ℂ (p ^ c)) (P y : ZMod (p ^ c)) : ℂ := χ (1 + P * y)

omit hp in
theorem phiP_add (χ : DirichletCharacter ℂ (p ^ c)) (P : ZMod (p ^ c)) (hP : P * P = 0) (y z : ZMod (p ^ c)) :
    phiP χ P (y + z) = phiP χ P y * phiP χ P z := by
  unfold phiP; rw [← map_mul]; congr 1; linear_combination (-(y * z)) * hP

omit hp in
theorem one_add_unit (P : ZMod (p ^ c)) (hP : P * P = 0) (y : ZMod (p ^ c)) : IsUnit (1 + P * y) :=
  isUnit_iff_exists_inv.mpr ⟨1 - P * y, by linear_combination (-(y * y)) * hP⟩

/-- **1. 平均化**（P² = 0）。 -/
theorem gauss_eq_sum_SP (χ : DirichletCharacter ℂ (p ^ c)) (P : ZMod (p ^ c)) (hP : P * P = 0) :
    gaussSum χ stdAddChar = ∑ u ∈ univ.filter (fun u : ZMod (p ^ c) =>
      ∀ y, phiP χ P y * stdAddChar (P * u * y) = 1), χ u * stdAddChar u := by
  classical
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set τ := gaussSum χ stdAddChar
  have hy : ∀ y : ZMod (p ^ c), τ = ∑ u, χ u * stdAddChar u * (phiP χ P y * stdAddChar (P * u * y)) := by
    intro y
    have hv := one_add_unit P hP y
    have hre : ∑ u, χ (u * (1 + P * y)) * stdAddChar (u * (1 + P * y)) = τ :=
      Fintype.sum_equiv (Units.mulRight hv.unit) _ (fun u => χ u * stdAddChar u) (fun u => rfl)
    rw [← hre]
    apply sum_congr rfl; intro u _
    simp only [phiP]
    rw [map_mul, show u * (1 + P * y) = u + P * u * y by ring, AddChar.map_add_eq_mul]
    ring
  have hmult : ∀ u : ZMod (p ^ c), ∀ y z, phiP χ P (y + z) * stdAddChar (P * u * (y + z))
      = (phiP χ P y * stdAddChar (P * u * y)) * (phiP χ P z * stdAddChar (P * u * z)) := by
    intro u y z
    rw [phiP_add χ P hP, mul_add, AddChar.map_add_eq_mul]; ring
  have hinner : ∀ u : ZMod (p ^ c), ∑ y, phiP χ P y * stdAddChar (P * u * y)
      = if (∀ y, phiP χ P y * stdAddChar (P * u * y) = 1) then ((p ^ c : ℕ) : ℂ) else 0 := by
    intro u
    split_ifs with hS
    · simp only [hS, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    · exact sum_mult_eq_zero _ (hmult u) hS
  have hN : ((p ^ c : ℕ) : ℂ) * τ = ((p ^ c : ℕ) : ℂ) * ∑ u ∈ univ.filter (fun u : ZMod (p ^ c) =>
      ∀ y, phiP χ P y * stdAddChar (P * u * y) = 1), χ u * stdAddChar u := by
    calc ((p ^ c : ℕ) : ℂ) * τ = ∑ _y : ZMod (p ^ c), τ := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      _ = ∑ y : ZMod (p ^ c), ∑ u, χ u * stdAddChar u * (phiP χ P y * stdAddChar (P * u * y)) :=
          sum_congr rfl (fun y _ => hy y)
      _ = ∑ u, χ u * stdAddChar u * ∑ y, phiP χ P y * stdAddChar (P * u * y) := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ = _ := by
          simp only [hinner, mul_ite, mul_zero]
          rw [← Finset.sum_filter, Finset.mul_sum]
          apply sum_congr rfl; intro u _; ring
  have hN0 : ((p ^ c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  exact mul_left_cancel₀ hN0 hN

end Avg

/-! ## 2–4. 導手 p^{2m+1} -/

section Odd

variable {c m : ℕ} (hc : c = 2 * m + 1) (hm : 1 ≤ m)

omit hp in
theorem pow_zero_of_le (k : ℕ) (hk : c ≤ k) : (p : ZMod (p ^ c)) ^ k = 0 :=
  pow_eq_zero_of_le hk (by rw [← Nat.cast_pow, ZMod.natCast_self])

include hc in
theorem divQ (w : ZMod (p ^ c)) (h : (p : ZMod (p ^ c)) ^ (m + 1) * w = 0) :
    ∃ z : ZMod (p ^ c), w = (p : ZMod (p ^ c)) ^ m * z := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [← ZMod.natCast_zmod_val w, ← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
  have hc' : p ^ (m + 1) * p ^ m = p ^ c := by rw [← pow_add]; congr 1; omega
  obtain ⟨z, hz⟩ := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos (m + 1)) ((dvd_of_eq hc').trans h)
  refine ⟨(z : ZMod (p ^ c)), ?_⟩
  rw [← ZMod.natCast_zmod_val w, hz]; push_cast; ring

include hc hm in
/-- **導手 p^{2m+1}（m ≥ 1）のガウス和の位相は 1 の冪根**。 -/
theorem gauss_odd_root (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ M : ℕ, 0 < M ∧ (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ M = 1 := by
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
  refine ⟨M, hMpos, ?_⟩
  have hr0 : (rR : ℂ) ≠ 0 := by exact_mod_cast hrR.ne'
  rw [hτε, ← hr, mul_div_cancel_left₀ _ hr0, hεM]

end Odd

/-! ## 系: 導手 p^c（c ≥ 2）のすべての原始ケットで ζ_k は 1 の冪根 -/

theorem gauss_root_ge_two (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ M : ℕ, 0 < M ∧ (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ M = 1 := by
  rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact gauss_even_root (p := p) (m := m) (by omega) χ hχ
  · exact gauss_odd_root (p := p) (m := m) hm (by omega) χ hχ

open PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117 in
/-- **ζ_k は導手 p^c（c ≥ 2）で 1 の冪根**（すべての素数）。 -/
theorem zeta_root_ge_two (K w n : ℕ) (hn : 1 ≤ n) (h : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K))
    (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w)) :
    ∃ N : ℕ, 0 < N ∧ ((cnorm p K (K - (n + 1) - w) * 𝓕 (ket K w (n + 1) h χ) t₀) ^ orderOf χ) ^ N = 1 :=
  (zeta_root_iff K w n h χ hχ t₀ ht₀).mpr (gauss_root_ge_two (n + 1) (by omega) χ hχ)

end PAG.Part120

#print axioms PAG.Part120.psi_two_one
#print axioms PAG.Part120.quad_root_two
#print axioms PAG.Part120.quad_root_all
#print axioms PAG.Part120.phiP_add
#print axioms PAG.Part120.one_add_unit
#print axioms PAG.Part120.gauss_eq_sum_SP
#print axioms PAG.Part120.pow_zero_of_le
#print axioms PAG.Part120.divQ
#print axioms PAG.Part120.gauss_odd_root
#print axioms PAG.Part120.gauss_root_ge_two
#print axioms PAG.Part120.zeta_root_ge_two
