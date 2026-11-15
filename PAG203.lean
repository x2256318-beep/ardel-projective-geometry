/-
  PAG 2.0 Part 199（2026-10-24）— 同じ殻の畳み込みの一般公式（ℤ/N の定理 A と定理 B の統一）
  A, B は法 c の原始指標、AB = Ψ∘π、Ψ は法 d の原始指標（d ∣ c。素因数の条件はない）、uM = N、c ∣ M、
  s = M/c、R(v, Ψ)(x) = [v ∣ x]·Ψ(x/v)（正規化しない押し出し、`rk`）とすると
     |u, A⟩_N ⋆ |u, B⟩_N = (s/φ(M))·(τ(A)τ(B)/τ(Ψ))·Σ_{e ∣ c, (e, d) = 1} (μ(e)Ψ̄(e)/e)·R(u·(c/d)/e, Ψ)
  1. rk_eq_gket、dft_rk：R はケットの定数倍で、フーリエ変換は Part 198 から
  2. dft_conv_gket：フーリエ側では 𝓕(|u, A⟩ ⋆ |u, B⟩)(ξ) = B_A B_B·[s ∣ ξ]·Ā(ξ/s)B̄(ξ/s)
  3. mobius_identity：Σ_{e ∣ c, (e,d)=1, e ∣ t} μ(e)Ψ(e)Ψ(t/e) = [(t, c) = 1]·Ψ(t)
  4. conv_general：一般公式（フーリエ変換の単射性で示す）
  5. 系：c の素因数がすべて d を割るなら項は e = 1 だけ（conv_general_single、Part 196 の定理 A の正規化しない形）。
     thmB_general：B = Ā（d = 1）のとき |u, A⟩ ⋆ |u, Ā⟩ = A(−1)·(M/φ(M))·Σ_{e ∣ c} (μ(e)/e)·1_{(uc/e)ℤ}（球の差）
-/
import PAG202
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace PAG.Part203

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part201 PAG.Part202
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 正規化しない押し出し -/

/-- R(v, Ψ)(x) = [v ∣ x]·Ψ(x/v)（ZMod N 上の関数）。 -/
noncomputable def rk {N : ℕ} (v d : ℕ) (Ψ : ZMod d → ℂ) : ZMod N → ℂ :=
  fun x => if v ∣ x.val then Ψ ((x.val / v : ℕ) : ZMod d) else 0

/-- v·W = N、d ∣ W なら R(v, Ψ) = √φ(W)·|v, Ψ⟩_N。 -/
theorem rk_eq_gket (v W N : ℕ) [NeZero N] (h : v * W = N) (d : ℕ) (hd : d ∣ W) (Ψ : ZMod d → ℂ) :
    rk (N := N) v d Ψ = ((Real.sqrt (Nat.totient W) : ℝ) : ℂ) • gket v W N h d hd Ψ := by
  have hWZ := neZero_of_mul h
  have hφ : (0 : ℝ) < Real.sqrt (Nat.totient W) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne W)))
  have a1 : ((Real.sqrt (Nat.totient W) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  funext x
  rw [Pi.smul_apply, smul_eq_mul, gket_apply]
  unfold rk
  split_ifs
  · push_cast
    field_simp
  · rw [mul_zero]

/-- R のフーリエ変換：𝓕R(v, Ψ)(ξ) = [W/d ∣ ξ]·(W/d)·Ψ̄(−1)τ(Ψ)·Ψ̄(ξ/(W/d))（Ψ 原始的）。 -/
theorem dft_rk (v W N : ℕ) [NeZero N] (h : v * W = N) (d : ℕ) [NeZero d] (hd : d ∣ W)
    (Ψ : DirichletCharacter ℂ d) (hΨ : Ψ.IsPrimitive) (ξ : ZMod N) :
    𝓕 (rk (N := N) v d Ψ) ξ =
      if W / d ∣ ξ.val then
        ((W / d : ℕ) : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar * Ψ⁻¹ ((ξ.val / (W / d) : ℕ) : ZMod d)
      else 0 := by
  have hWZ := neZero_of_mul h
  have hφ : (0 : ℝ) < Real.sqrt (Nat.totient W) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne W)))
  have a1 : ((Real.sqrt (Nat.totient W) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  rw [rk_eq_gket v W N h d hd Ψ, ZMod.dft_const_smul, Pi.smul_apply, smul_eq_mul,
    dft_gket_apply v W N h d hd Ψ hΨ ξ]
  split_ifs
  · push_cast
    field_simp
  · rw [mul_zero]

/-! ### 2. フーリエ側の積 -/

/-- **2.** 𝓕(|u, A⟩ ⋆ |u, B⟩)(ξ) = [s ∣ ξ]·B_A B_B·Ā(ξ/s)B̄(ξ/s)（s = M/c、B_X = φ(M)^(−1/2)·s·X̄(−1)τ(X)）。 -/
theorem dft_conv_gket (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (A B : DirichletCharacter ℂ c) (hA : A.IsPrimitive) (hB : B.IsPrimitive) (ξ : ZMod N) :
    𝓕 (PAG.Part15.conv (gket u M N h c hc A) (gket u M N h c hc B)) ξ =
      if M / c ∣ ξ.val then
        ((((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * ((M / c : ℕ) : ℂ) * A⁻¹ (-1) * gaussSum A stdAddChar) *
        ((((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * ((M / c : ℕ) : ℂ) * B⁻¹ (-1) * gaussSum B stdAddChar) *
          (A⁻¹ ((ξ.val / (M / c) : ℕ) : ZMod c) * B⁻¹ ((ξ.val / (M / c) : ℕ) : ZMod c))
      else 0 := by
  have hMZ := neZero_of_mul h
  rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_gket_apply u M N h c hc A hA, dft_gket_apply u M N h c hc B hB]
  split_ifs <;> ring

/-! ### 3. メビウスの恒等式 -/

/-- Σ_{e ∣ n} μ(e) = [n = 1]。 -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ e ∈ n.divisors, (ArithmeticFunction.moebius e : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have h' : ((∑ e ∈ n.divisors, ArithmeticFunction.moebius e : ℤ) : ℂ) = ((if n = 1 then 1 else 0 : ℤ) : ℂ) := by
    rw [h]
  push_cast at h'
  rw [h']

/-- **3. メビウスの恒等式**：Σ_{e ∣ c, (e,d)=1} [e ∣ t]·μ(e)Ψ(e)Ψ(t/e) = [(t, c) = 1]·Ψ(t)（d ∣ c）。 -/
theorem mobius_identity (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c) (Ψ : DirichletCharacter ℂ d) (t : ℕ) :
    ∑ e ∈ c.divisors.filter (fun e => e.Coprime d),
        (if e ∣ t then (ArithmeticFunction.moebius e : ℂ) * (Ψ (e : ZMod d) * Ψ ((t / e : ℕ) : ZMod d)) else 0)
      = if t.Coprime c then Ψ (t : ZMod d) else 0 := by
  classical
  have hsplit : ∀ e, e ∣ t → Ψ (e : ZMod d) * Ψ ((t / e : ℕ) : ZMod d) = Ψ (t : ZMod d) := by
    intro e he
    rw [← map_mul, ← Nat.cast_mul, Nat.mul_div_cancel' he]
  have e1 : ∑ e ∈ c.divisors.filter (fun e => e.Coprime d),
        (if e ∣ t then (ArithmeticFunction.moebius e : ℂ) * (Ψ (e : ZMod d) * Ψ ((t / e : ℕ) : ZMod d)) else 0)
      = ∑ e ∈ c.divisors.filter (fun e => e.Coprime d),
        (if e ∣ t then (ArithmeticFunction.moebius e : ℂ) * Ψ (t : ZMod d) else 0) := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    split_ifs with he
    · rw [hsplit e he]
    · rfl
  rw [e1, ← Finset.sum_filter, ← Finset.sum_mul]
  by_cases hcop : t.Coprime d
  · have hset : (c.divisors.filter (fun e => e.Coprime d)).filter (fun e => e ∣ t) = (Nat.gcd t c).divisors := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨⟨hec, hc0⟩, _⟩, het⟩
        exact ⟨Nat.dvd_gcd het hec, Nat.gcd_ne_zero_right hc0⟩
      · rintro ⟨heg, _⟩
        have het : e ∣ t := heg.trans (Nat.gcd_dvd_left t c)
        have hec : e ∣ c := heg.trans (Nat.gcd_dvd_right t c)
        exact ⟨⟨⟨hec, NeZero.ne c⟩, hcop.coprime_dvd_left het⟩, het⟩
    rw [hset, sum_moebius_divisors]
    by_cases htc : t.Coprime c
    · rw [ite_eq_left htc, ite_eq_left (Nat.Coprime.gcd_eq_one htc), one_mul]
    · rw [ite_eq_right htc, ite_eq_right (fun hg => htc hg), zero_mul]
  · have h0 : Ψ (t : ZMod d) = 0 :=
      MulChar.map_nonunit _ (fun hu => hcop ((ZMod.isUnit_iff_coprime t d).mp hu))
    rw [h0, mul_zero, ite_eq_right (fun htc => hcop (htc.coprime_dvd_right hdc))]

/-! ### 4. 一般公式 -/

/-- 積の関係の言い換え：Ā(x)B̄(x) = (Ψ̄∘π)(x)。 -/
theorem inv_mul_inv_apply {c d : ℕ} (hdc : d ∣ c) (A B : DirichletCharacter ℂ c)
    (Ψ : DirichletCharacter ℂ d) (hprod : A * B = Ψ.changeLevel hdc) (x : ZMod c) :
    A⁻¹ x * B⁻¹ x = (Ψ⁻¹).changeLevel hdc x := by
  rw [← MulChar.mul_apply, ← mul_inv, hprod, ← map_inv]

/-- **4. 同じ殻の畳み込みの一般公式**（ℤ/N の定理 A と定理 B の統一）。 -/
theorem conv_general (u M N : ℕ) [NeZero N] (h : u * M = N) (c d : ℕ) [NeZero c] [NeZero d]
    (hc : c ∣ M) (hdc : d ∣ c) (A B : DirichletCharacter ℂ c) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive) (hprod : A * B = Ψ.changeLevel hdc) :
    PAG.Part15.conv (gket u M N h c hc A) (gket u M N h c hc B) =
      (((M / c : ℕ) : ℂ) / (Nat.totient M : ℂ) *
          (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar)) •
        ∑ e ∈ c.divisors.filter (fun e => e.Coprime d),
          ((ArithmeticFunction.moebius e : ℂ) * Ψ⁻¹ (e : ZMod d) / (e : ℂ)) •
            rk (N := N) (u * (c / d) / e) d Ψ := by
  classical
  have hMZ := neZero_of_mul h
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hu0 : 0 < u := pos_of_mul h
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc) hc0
  set s := M / c with hs
  have hsc : s * c = M := Nat.div_mul_cancel hc
  have hcd : d * (c / d) = c := Nat.mul_div_cancel' hdc
  have hφM : (0 : ℝ) < Nat.totient M := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hτΨ : gaussSum Ψ stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero hΨ
  -- 各 e での殻の等式
  have hshell : ∀ e ∈ c.divisors.filter (fun e => e.Coprime d),
      u * (c / d) / e * (s * d * e) = N ∧ d ∣ s * d * e ∧ s * d * e / d = s * e := by
    intro e he
    rw [Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨hec, _⟩, hed⟩ := he
    have hecd : e ∣ c / d := by
      have : e ∣ d * (c / d) := by rw [hcd]; exact hec
      exact hed.dvd_of_dvd_mul_left this
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hec hc0
    obtain ⟨k, hk⟩ := hecd
    refine ⟨?_, Dvd.intro (s * e) (by ring), ?_⟩
    · rw [hk, show u * (e * k) = e * (u * k) by ring, Nat.mul_div_cancel_left _ he0, ← h, ← hsc, ← hcd, hk]
      ring
    · rw [show s * d * e = d * (s * e) by ring, Nat.mul_div_cancel_left _ hd0]
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [dft_conv_gket u M N h c hc A B hA hB ξ, map_smul, Pi.smul_apply, map_sum, Finset.sum_apply]
  have hterm : ∀ e ∈ c.divisors.filter (fun e => e.Coprime d),
      𝓕 (((ArithmeticFunction.moebius e : ℂ) * Ψ⁻¹ (e : ZMod d) / (e : ℂ)) •
          rk (N := N) (u * (c / d) / e) d Ψ) ξ
        = ((ArithmeticFunction.moebius e : ℂ) * Ψ⁻¹ (e : ZMod d) / (e : ℂ)) *
          (if s * e ∣ ξ.val then ((s * e : ℕ) : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar *
            Ψ⁻¹ ((ξ.val / (s * e) : ℕ) : ZMod d) else 0) := by
    intro e he
    obtain ⟨h1, h2, h3⟩ := hshell e he
    rw [map_smul, Pi.smul_apply, smul_eq_mul, dft_rk (u * (c / d) / e) (s * d * e) N h1 d h2 Ψ hΨ ξ, h3]
  rw [Finset.sum_congr rfl hterm]
  -- [s ∣ ξ] で場合分け
  by_cases hsξ : s ∣ ξ.val
  · obtain ⟨t, ht⟩ := hsξ
    rw [ite_eq_left ⟨t, ht⟩, ht, Nat.mul_div_cancel_left t hs0, inv_mul_inv_apply hdc A B Ψ hprod]
    -- 右辺の各項：[se ∣ st] = [e ∣ t]、st/(se) = t/e
    have hterm2 : ∀ e ∈ c.divisors.filter (fun e => e.Coprime d),
        ((ArithmeticFunction.moebius e : ℂ) * Ψ⁻¹ (e : ZMod d) / (e : ℂ)) *
          (if s * e ∣ s * t then ((s * e : ℕ) : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar *
            Ψ⁻¹ ((s * t / (s * e) : ℕ) : ZMod d) else 0)
        = ((s : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar) *
          (if e ∣ t then (ArithmeticFunction.moebius e : ℂ) * (Ψ⁻¹ (e : ZMod d) * Ψ⁻¹ ((t / e : ℕ) : ZMod d))
            else 0) := by
      intro e he
      have he0 : (e : ℂ) ≠ 0 := by
        rw [Finset.mem_filter, Nat.mem_divisors] at he
        exact_mod_cast (Nat.pos_of_dvd_of_pos he.1.1 hc0).ne'
      by_cases het : e ∣ t
      · rw [ite_eq_left ((Nat.mul_dvd_mul_iff_left hs0).mpr het), ite_eq_left het,
          Nat.mul_div_mul_left t e hs0]
        push_cast
        field_simp
      · rw [ite_eq_right (fun hd' => het ((Nat.mul_dvd_mul_iff_left hs0).mp hd')), ite_eq_right het,
          mul_zero, mul_zero]
    rw [Finset.sum_congr rfl hterm2, ← Finset.mul_sum, mobius_identity c d hdc Ψ⁻¹ t]
    -- (Ψ⁻¹)′(t) = [(t, c) = 1]·Ψ⁻¹(t)
    have hcl : (Ψ⁻¹).changeLevel hdc (t : ZMod c) = if t.Coprime c then Ψ⁻¹ (t : ZMod d) else 0 := by
      by_cases htc : t.Coprime c
      · rw [ite_eq_left htc, changeLevel_natCast hdc Ψ⁻¹ t htc]
      · rw [ite_eq_right htc]
        exact MulChar.map_nonunit _ (fun hu => htc ((ZMod.isUnit_iff_coprime t c).mp hu))
    rw [hcl]
    -- Ā(−1)B̄(−1) = Ψ̄(−1)
    have hm1 : A⁻¹ (-1) * B⁻¹ (-1) = Ψ⁻¹ (-1) := by
      rw [inv_mul_inv_apply hdc A B Ψ hprod]
      have : ((-1 : (ZMod c)ˣ) : ZMod c) = -1 := by simp
      rw [← this, DirichletCharacter.changeLevel_eq_cast_of_dvd, this, ZMod.cast_neg_one,
        (ZMod.natCast_eq_zero_iff c d).mpr hdc, zero_sub]
    have hs1 : (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ)
        = ((Nat.totient M : ℝ) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_inv]
    have hφMC : ((Nat.totient M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφM.ne'
    calc (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * ((s : ℕ) : ℂ) * A⁻¹ (-1) * gaussSum A stdAddChar *
          ((((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * ((s : ℕ) : ℂ) * B⁻¹ (-1) * gaussSum B stdAddChar) *
          (if t.Coprime c then Ψ⁻¹ (t : ZMod d) else 0)
        = ((((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ)) *
            ((s : ℂ) * (s : ℂ)) * (A⁻¹ (-1) * B⁻¹ (-1)) * (gaussSum A stdAddChar * gaussSum B stdAddChar) *
            (if t.Coprime c then Ψ⁻¹ (t : ZMod d) else 0) := by ring
      _ = ((s : ℂ) / (Nat.totient M : ℂ) *
            (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar)) *
          (((s : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar) *
            (if t.Coprime c then Ψ⁻¹ (t : ZMod d) else 0)) := by
        rw [hs1, hm1]
        push_cast
        field_simp
  · rw [ite_eq_right hsξ, smul_eq_mul]
    symm
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro e he
    rw [ite_eq_right (fun hd' => hsξ ((Dvd.intro e rfl).trans hd')), mul_zero]

/-! ### 5. 系：定理 A（一つの殻）と定理 B（球の差） -/

/-- c の素因数がすべて d を割るなら、{e ∣ c : (e, d) = 1} = {1}。 -/
theorem filter_coprime_eq_one (c d : ℕ) [NeZero c] (hrad : ∀ q : ℕ, q.Prime → q ∣ c → q ∣ d) :
    c.divisors.filter (fun e => e.Coprime d) = {1} := by
  ext e
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hec, _⟩, hed⟩
    by_contra he1
    obtain ⟨q, hq, hqe⟩ := Nat.exists_prime_and_dvd he1
    have hqd : q ∣ d := hrad q hq (hqe.trans hec)
    have : q ∣ Nat.gcd e d := Nat.dvd_gcd hqe hqd
    rw [Nat.Coprime.gcd_eq_one hed] at this
    exact hq.not_dvd_one this
  · rintro rfl
    exact ⟨⟨one_dvd c, NeZero.ne c⟩, Nat.coprime_one_left d⟩

/-- **5a. 一つの殻**：c の素因数がすべて d を割るなら、一般公式の項は e = 1 だけで
|u, A⟩ ⋆ |u, B⟩ = (s/φ(M))·(τ(A)τ(B)/τ(Ψ))·R(u·c/d, Ψ)（Part 196 の定理 A の、正規化しない形）。 -/
theorem conv_general_single (u M N : ℕ) [NeZero N] (h : u * M = N) (c d : ℕ) [NeZero c] [NeZero d]
    (hc : c ∣ M) (hdc : d ∣ c) (A B : DirichletCharacter ℂ c) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive) (hprod : A * B = Ψ.changeLevel hdc)
    (hrad : ∀ q : ℕ, q.Prime → q ∣ c → q ∣ d) :
    PAG.Part15.conv (gket u M N h c hc A) (gket u M N h c hc B) =
      (((M / c : ℕ) : ℂ) / (Nat.totient M : ℂ) *
          (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar)) •
        rk (N := N) (u * (c / d)) d Ψ := by
  rw [conv_general u M N h c d hc hdc A B Ψ hA hB hΨ hprod, filter_coprime_eq_one c d hrad,
    Finset.sum_singleton]
  congr 1
  rw [ArithmeticFunction.moebius_apply_one, Nat.cast_one, map_one, Nat.cast_one, Nat.div_one]
  simp

/-- 法 1 の自明な指標のガウス和は 1。 -/
theorem gaussSum_level_one (χ : DirichletCharacter ℂ 1) : gaussSum χ stdAddChar = 1 := by
  rw [gaussSum, Fintype.sum_subsingleton _ (0 : ZMod 1), chi_level_one, AddChar.map_zero_eq_one, mul_one]

/-- **5b. 定理 B（球の差）**：B = Ā のとき
|u, A⟩ ⋆ |u, Ā⟩ = A(−1)·(M/φ(M))·Σ_{e ∣ c} (μ(e)/e)·1_{(uc/e)ℤ}（1_v(x) = [v ∣ x]、μ(e) = 0 の項は消える）。 -/
theorem thmB_general (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (A : DirichletCharacter ℂ c) (hA : A.IsPrimitive) :
    PAG.Part15.conv (gket u M N h c hc A) (gket u M N h c hc (A⁻¹ : DirichletCharacter ℂ c)) =
      (A (-1) * ((M : ℂ) / (Nat.totient M : ℂ))) •
        ∑ e ∈ c.divisors, ((ArithmeticFunction.moebius e : ℂ) / (e : ℂ)) •
          rk (N := N) (u * c / e) 1 (fun _ => 1) := by
  have hMZ := neZero_of_mul h
  have hc0 : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  have hprod : A * A⁻¹ = (1 : DirichletCharacter ℂ 1).changeLevel (one_dvd c) := by
    rw [mul_inv_cancel, map_one]
  rw [conv_general u M N h c 1 hc (one_dvd c) A A⁻¹ 1 hA (PAG.Part16.isPrimitive_inv hA)
    DirichletCharacter.isPrimitive_one_level_one hprod]
  have hfilt : c.divisors.filter (fun e => e.Coprime 1) = c.divisors :=
    Finset.filter_true_of_mem (fun e _ => Nat.coprime_one_right e)
  have hone : ((1 : DirichletCharacter ℂ 1) : ZMod 1 → ℂ) = fun _ => 1 := by
    funext x; exact chi_level_one 1 x
  rw [hfilt, hone, gaussSum_level_one, PAG.Part16.gauss_mul_gauss_inv_eq hA, Nat.div_one]
  congr 1
  · have hcM : ((M / c : ℕ) : ℂ) * c = M := by exact_mod_cast Nat.div_mul_cancel hc
    rw [div_one, ← hcM]
    ring
  · refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [chi_level_one, mul_one]

end PAG.Part203

#print axioms PAG.Part203.rk_eq_gket
#print axioms PAG.Part203.dft_rk
#print axioms PAG.Part203.dft_conv_gket
#print axioms PAG.Part203.sum_moebius_divisors
#print axioms PAG.Part203.mobius_identity
#print axioms PAG.Part203.inv_mul_inv_apply
#print axioms PAG.Part203.conv_general
#print axioms PAG.Part203.filter_coprime_eq_one
#print axioms PAG.Part203.conv_general_single
#print axioms PAG.Part203.gaussSum_level_one
#print axioms PAG.Part203.thmB_general
