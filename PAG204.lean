/-
  PAG 2.0 Part 200（2026-10-24）— 異なる殻の畳み込み（ℤ/N の混合公式と、0 になる条件）
  A は法 c₁、B は法 c₂ の原始指標、u_i M_i = N、c_i ∣ M_i、双対の殻 s_i = M_i/c_i、
  S = lcm(s₁, s₂)、g = gcd(s₁, s₂)、L = lcm(c₁, c₂)、A′B′（法 L）= Ψ∘π（Ψ は法 d の原始指標）、
  R(v, Ψ)(x) = [v ∣ x]·Ψ(x/v)（Part 199 の rk）とすると
     |u₁, A⟩_N ⋆ |u₂, B⟩_N = (g/√(φ(M₁)φ(M₂)))·Ā(S/s₁)B̄(S/s₂)·(τ(A)τ(B)/τ(Ψ))
                              ·Σ_{e ∣ L, (e, d) = 1} (μ(e)Ψ̄(e)/e)·R(N/(Sde), Ψ)
  1. 算術：(S/s₁, c₁) = (S/s₂, c₂) = 1 なら S·L ∣ N（lcm_mul_lcm_dvd）
  2. フーリエ側：𝓕(|u₁, A⟩ ⋆ |u₂, B⟩)(ξ) = [S ∣ ξ]·β₁β₂·Ā(S/s₁)B̄(S/s₂)·Ā(ξ/S)B̄(ξ/S)（dft_conv_mixed）
  3. 積の指標：Ā(−1)B̄(−1) = Ψ̄(−1)、Ā(t)B̄(t) = [(t, L) = 1]·Ψ̄(t)
  4. 0 になる条件：|u₁, A⟩ ⋆ |u₂, B⟩ = 0 ⇔ (S/s₁, c₁) ≠ 1 または (S/s₂, c₂) ≠ 1（conv_mixed_eq_zero_iff）
  5. 一般公式（conv_mixed）
  6. 系：N の素因数がすべて c₁, c₂ を割るなら、双対の殻が違えば 0（conv_ne_dual_zero）。
     同じ双対の殻（conv_same_dual）。L の素因数がすべて d を割るなら項は 1 つで、ケット 1 つの定数倍
     （conv_mixed_single、conv_mixed_ket：Part 38 の混合定理 A の ℤ/N 版）、その定数の大きさ（normSq_mixed_coef）
-/
import PAG203

namespace PAG.Part204

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part201 PAG.Part202 PAG.Part203
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 算術 -/

/-- **1.** s_i c_i ∣ N、S = lcm(s₁, s₂)、(S/s₁, c₁) = (S/s₂, c₂) = 1 なら S·lcm(c₁, c₂) ∣ N。 -/
theorem lcm_mul_lcm_dvd {N s₁ s₂ c₁ c₂ : ℕ} (h₁ : s₁ * c₁ ∣ N) (h₂ : s₂ * c₂ ∣ N)
    (hcop₁ : (Nat.lcm s₁ s₂ / s₁).Coprime c₁) (hcop₂ : (Nat.lcm s₁ s₂ / s₂).Coprime c₂) :
    Nat.lcm s₁ s₂ * Nat.lcm c₁ c₂ ∣ N := by
  have hS : Nat.lcm s₁ s₂ ∣ N :=
    Nat.lcm_dvd ((dvd_mul_right s₁ c₁).trans h₁) ((dvd_mul_right s₂ c₂).trans h₂)
  have e1 : s₁ * (Nat.lcm s₁ s₂ / s₁) = Nat.lcm s₁ s₂ := Nat.mul_div_cancel' (Nat.dvd_lcm_left s₁ s₂)
  have e2 : s₂ * (Nat.lcm s₁ s₂ / s₂) = Nat.lcm s₁ s₂ := Nat.mul_div_cancel' (Nat.dvd_lcm_right s₁ s₂)
  have k₁ : Nat.lcm s₁ s₂ * c₁ ∣ N := by
    have h : Nat.lcm (s₁ * c₁) (s₁ * (Nat.lcm s₁ s₂ / s₁)) ∣ N := Nat.lcm_dvd h₁ (by rw [e1]; exact hS)
    rw [Nat.lcm_mul_left, Nat.Coprime.lcm_eq_mul hcop₁.symm] at h
    calc Nat.lcm s₁ s₂ * c₁ = s₁ * (Nat.lcm s₁ s₂ / s₁) * c₁ := by rw [e1]
      _ = s₁ * (c₁ * (Nat.lcm s₁ s₂ / s₁)) := by ring
      _ ∣ N := h
  have k₂ : Nat.lcm s₁ s₂ * c₂ ∣ N := by
    have h : Nat.lcm (s₂ * c₂) (s₂ * (Nat.lcm s₁ s₂ / s₂)) ∣ N := Nat.lcm_dvd h₂ (by rw [e2]; exact hS)
    rw [Nat.lcm_mul_left, Nat.Coprime.lcm_eq_mul hcop₂.symm] at h
    calc Nat.lcm s₁ s₂ * c₂ = s₂ * (Nat.lcm s₁ s₂ / s₂) * c₂ := by rw [e2]
      _ = s₂ * (c₂ * (Nat.lcm s₁ s₂ / s₂)) := by ring
      _ ∣ N := h
  have h := Nat.lcm_dvd k₁ k₂
  rwa [Nat.lcm_mul_left] at h

/-- 補題：s ∣ S なら (S·t)/s = (S/s)·t。 -/
theorem div_mul_aux {s S : ℕ} (hs : 0 < s) (hsS : s ∣ S) (t : ℕ) : S * t / s = S / s * t := by
  obtain ⟨b, rfl⟩ := hsS
  rw [Nat.mul_div_cancel_left b hs, mul_assoc, Nat.mul_div_cancel_left _ hs]

/-! ### 2. フーリエ側 -/

/-- **2.** 𝓕(|u₁, A⟩ ⋆ |u₂, B⟩)(ξ) = [S ∣ ξ]·β₁β₂·Ā(S/s₁)B̄(S/s₂)·Ā(ξ/S)B̄(ξ/S)、
β₁β₂ = φ(M₁)^(−1/2)φ(M₂)^(−1/2)·s₁s₂·Ā(−1)B̄(−1)·τ(A)τ(B)（s_i = M_i/c_i、S = lcm(s₁, s₂)）。 -/
theorem dft_conv_mixed (u₁ M₁ u₂ M₂ N : ℕ) [NeZero N] (h₁ : u₁ * M₁ = N) (h₂ : u₂ * M₂ = N)
    (c₁ c₂ : ℕ) [NeZero c₁] [NeZero c₂] (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (ξ : ZMod N) :
    𝓕 (PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ A) (gket u₂ M₂ N h₂ c₂ hc₂ B)) ξ =
      if Nat.lcm (M₁ / c₁) (M₂ / c₂) ∣ ξ.val then
        ((((Real.sqrt (Nat.totient M₁))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (Nat.totient M₂))⁻¹ : ℝ) : ℂ)) *
          (((M₁ / c₁ : ℕ) : ℂ) * ((M₂ / c₂ : ℕ) : ℂ)) * (A⁻¹ (-1) * B⁻¹ (-1)) *
          (gaussSum A stdAddChar * gaussSum B stdAddChar) *
          (A⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁) : ℕ) : ZMod c₁) *
            B⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂) : ℕ) : ZMod c₂)) *
          (A⁻¹ ((ξ.val / Nat.lcm (M₁ / c₁) (M₂ / c₂) : ℕ) : ZMod c₁) *
            B⁻¹ ((ξ.val / Nat.lcm (M₁ / c₁) (M₂ / c₂) : ℕ) : ZMod c₂))
      else 0 := by
  have hM₁ := neZero_of_mul h₁
  have hM₂ := neZero_of_mul h₂
  have hs₁ : 0 < M₁ / c₁ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M₁)) hc₁)
    (Nat.pos_of_ne_zero (NeZero.ne c₁))
  have hs₂ : 0 < M₂ / c₂ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M₂)) hc₂)
    (Nat.pos_of_ne_zero (NeZero.ne c₂))
  have hS0 : 0 < Nat.lcm (M₁ / c₁) (M₂ / c₂) := Nat.lcm_pos hs₁ hs₂
  rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_gket_apply u₁ M₁ N h₁ c₁ hc₁ A hA,
    dft_gket_apply u₂ M₂ N h₂ c₂ hc₂ B hB]
  by_cases hS : Nat.lcm (M₁ / c₁) (M₂ / c₂) ∣ ξ.val
  · obtain ⟨t, ht⟩ := hS
    have hd₁ : M₁ / c₁ ∣ ξ.val := by
      rw [ht]; exact (Nat.dvd_lcm_left _ _).trans (dvd_mul_right _ t)
    have hd₂ : M₂ / c₂ ∣ ξ.val := by
      rw [ht]; exact (Nat.dvd_lcm_right _ _).trans (dvd_mul_right _ t)
    rw [ite_eq_left hd₁, ite_eq_left hd₂, ite_eq_left ⟨t, ht⟩, ht,
      div_mul_aux hs₁ (Nat.dvd_lcm_left _ _) t, div_mul_aux hs₂ (Nat.dvd_lcm_right _ _) t,
      Nat.mul_div_cancel_left t hS0]
    simp only [Nat.cast_mul, map_mul]
    ring
  · rw [ite_eq_right hS]
    by_cases hd₁ : M₁ / c₁ ∣ ξ.val
    · have hd₂ : ¬ M₂ / c₂ ∣ ξ.val := fun hd₂ => hS (Nat.lcm_dvd hd₁ hd₂)
      rw [ite_eq_right hd₂, mul_zero]
    · rw [ite_eq_right hd₁, zero_mul]

/-! ### 3. 積の指標 -/

/-- 持ち上げた指標の −1 での値：Ψ′(−1) = Ψ(−1)。 -/
theorem changeLevel_neg_one {d c : ℕ} (hd : d ∣ c) (Ψ : DirichletCharacter ℂ d) :
    Ψ.changeLevel hd (-1) = Ψ (-1) := by
  have : ((-1 : (ZMod c)ˣ) : ZMod c) = -1 := by simp
  rw [← this, DirichletCharacter.changeLevel_eq_cast_of_dvd, this, ZMod.cast_neg_one,
    (ZMod.natCast_eq_zero_iff c d).mpr hd, zero_sub]

/-- **3a.** Ā(−1)B̄(−1) = Ψ̄(−1)（A′B′ = Ψ′、法 L = lcm(c₁, c₂)）。 -/
theorem inv_mul_inv_neg_one {c₁ c₂ d : ℕ} (hdL : d ∣ Nat.lcm c₁ c₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (Ψ : DirichletCharacter ℂ d)
    (hprod : A.changeLevel (Nat.dvd_lcm_left c₁ c₂) * B.changeLevel (Nat.dvd_lcm_right c₁ c₂) =
      Ψ.changeLevel hdL) :
    A⁻¹ (-1) * B⁻¹ (-1) = Ψ⁻¹ (-1) := by
  rw [← changeLevel_neg_one (Nat.dvd_lcm_left c₁ c₂) A⁻¹,
    ← changeLevel_neg_one (Nat.dvd_lcm_right c₁ c₂) B⁻¹, ← changeLevel_neg_one hdL Ψ⁻¹,
    map_inv, map_inv, map_inv, ← MulChar.mul_apply, ← mul_inv, hprod]

/-- **3b.** Ā(t)B̄(t) = [(t, L) = 1]·Ψ̄(t)（L = lcm(c₁, c₂)）。 -/
theorem inv_mul_inv_mixed {c₁ c₂ d : ℕ} (hdL : d ∣ Nat.lcm c₁ c₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (Ψ : DirichletCharacter ℂ d)
    (hprod : A.changeLevel (Nat.dvd_lcm_left c₁ c₂) * B.changeLevel (Nat.dvd_lcm_right c₁ c₂) =
      Ψ.changeLevel hdL) (t : ℕ) :
    A⁻¹ (t : ZMod c₁) * B⁻¹ (t : ZMod c₂) =
      if t.Coprime (Nat.lcm c₁ c₂) then Ψ⁻¹ (t : ZMod d) else 0 := by
  by_cases htL : t.Coprime (Nat.lcm c₁ c₂)
  · rw [ite_eq_left htL, ← changeLevel_natCast (Nat.dvd_lcm_left c₁ c₂) A⁻¹ t htL,
      ← changeLevel_natCast (Nat.dvd_lcm_right c₁ c₂) B⁻¹ t htL, ← changeLevel_natCast hdL Ψ⁻¹ t htL,
      map_inv, map_inv, map_inv, ← MulChar.mul_apply, ← mul_inv, hprod]
  · rw [ite_eq_right htL]
    by_cases h1 : t.Coprime c₁
    · have h2 : ¬ t.Coprime c₂ := fun h2 =>
        htL ((Nat.Coprime.mul_right h1 h2).coprime_dvd_right (Nat.lcm_dvd_mul c₁ c₂))
      rw [MulChar.map_nonunit B⁻¹ (fun hu => h2 ((ZMod.isUnit_iff_coprime t c₂).mp hu)), mul_zero]
    · rw [MulChar.map_nonunit A⁻¹ (fun hu => h1 ((ZMod.isUnit_iff_coprime t c₁).mp hu)), zero_mul]

/-! ### 4. 0 になる条件 -/

/-- (a, c₁) ≠ 1 または (b, c₂) ≠ 1 なら Ā(a)B̄(b) = 0。 -/
theorem mixed_unit_factor_eq_zero {c₁ c₂ : ℕ} (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂)
    (a b : ℕ) (hnc : ¬ (a.Coprime c₁ ∧ b.Coprime c₂)) : A⁻¹ (a : ZMod c₁) * B⁻¹ (b : ZMod c₂) = 0 := by
  by_cases h1 : a.Coprime c₁
  · have h2 : ¬ b.Coprime c₂ := fun h2 => hnc ⟨h1, h2⟩
    rw [MulChar.map_nonunit B⁻¹ (fun hu => h2 ((ZMod.isUnit_iff_coprime b c₂).mp hu)), mul_zero]
  · rw [MulChar.map_nonunit A⁻¹ (fun hu => h1 ((ZMod.isUnit_iff_coprime a c₁).mp hu)), zero_mul]

/-- **4a. 0 になる条件（十分性）**：(S/s₁, c₁) ≠ 1 または (S/s₂, c₂) ≠ 1 なら |u₁, A⟩ ⋆ |u₂, B⟩ = 0。 -/
theorem conv_mixed_eq_zero (u₁ M₁ u₂ M₂ N : ℕ) [NeZero N] (h₁ : u₁ * M₁ = N) (h₂ : u₂ * M₂ = N)
    (c₁ c₂ : ℕ) [NeZero c₁] [NeZero c₂] (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (hnc : ¬ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁)).Coprime c₁ ∧
      (Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂)).Coprime c₂)) :
    PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ A) (gket u₂ M₂ N h₂ c₂ hc₂ B) = 0 := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [dft_conv_mixed u₁ M₁ u₂ M₂ N h₁ h₂ c₁ c₂ hc₁ hc₂ A B hA hB ξ, map_zero, Pi.zero_apply,
    mixed_unit_factor_eq_zero A B _ _ hnc]
  split_ifs <;> simp

/-- **4b. 0 になる条件（必要性）**：(S/s₁, c₁) = (S/s₂, c₂) = 1 なら |u₁, A⟩ ⋆ |u₂, B⟩ ≠ 0
（フーリエ変換が ξ = S で 0 でない）。 -/
theorem conv_mixed_ne_zero (u₁ M₁ u₂ M₂ N : ℕ) [NeZero N] (h₁ : u₁ * M₁ = N) (h₂ : u₂ * M₂ = N)
    (c₁ c₂ : ℕ) [NeZero c₁] [NeZero c₂] (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (hcop₁ : (Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁)).Coprime c₁)
    (hcop₂ : (Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂)).Coprime c₂) :
    PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ A) (gket u₂ M₂ N h₂ c₂ hc₂ B) ≠ 0 := by
  intro hzero
  have hM₁ := neZero_of_mul h₁
  have hM₂ := neZero_of_mul h₂
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hs₁ : 0 < M₁ / c₁ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M₁)) hc₁)
    (Nat.pos_of_ne_zero (NeZero.ne c₁))
  have hs₂ : 0 < M₂ / c₂ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M₂)) hc₂)
    (Nat.pos_of_ne_zero (NeZero.ne c₂))
  have hS0 : 0 < Nat.lcm (M₁ / c₁) (M₂ / c₂) := Nat.lcm_pos hs₁ hs₂
  have hSL : Nat.lcm (M₁ / c₁) (M₂ / c₂) * Nat.lcm c₁ c₂ ∣ N :=
    lcm_mul_lcm_dvd (by rw [Nat.div_mul_cancel hc₁]; exact Dvd.intro_left u₁ h₁)
      (by rw [Nat.div_mul_cancel hc₂]; exact Dvd.intro_left u₂ h₂) hcop₁ hcop₂
  have hSN : Nat.lcm (M₁ / c₁) (M₂ / c₂) ∣ N := (dvd_mul_right _ _).trans hSL
  have key : 𝓕 (PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ A) (gket u₂ M₂ N h₂ c₂ hc₂ B))
      ((Nat.lcm (M₁ / c₁) (M₂ / c₂) : ℕ) : ZMod N) = 0 := by
    rw [hzero, map_zero, Pi.zero_apply]
  rw [dft_conv_mixed u₁ M₁ u₂ M₂ N h₁ h₂ c₁ c₂ hc₁ hc₂ A B hA hB, ZMod.val_natCast] at key
  have hdvd : Nat.lcm (M₁ / c₁) (M₂ / c₂) ∣ Nat.lcm (M₁ / c₁) (M₂ / c₂) % N :=
    (Nat.dvd_mod_iff hSN).mpr dvd_rfl
  rw [ite_eq_left hdvd] at key
  -- (S mod N)/S は L と互いに素（S < N なら 1、S = N なら L = 1）
  have hcopL : (Nat.lcm (M₁ / c₁) (M₂ / c₂) % N / Nat.lcm (M₁ / c₁) (M₂ / c₂)).Coprime
      (Nat.lcm c₁ c₂) := by
    rcases Nat.lt_or_ge (Nat.lcm (M₁ / c₁) (M₂ / c₂)) N with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt, Nat.div_self hS0]
      exact Nat.coprime_one_left _
    · have hSeq : Nat.lcm (M₁ / c₁) (M₂ / c₂) = N := le_antisymm (Nat.le_of_dvd hN0 hSN) hge
      have hSL' := hSL
      rw [← hSeq] at hSL'
      have hL1 : Nat.lcm c₁ c₂ = 1 :=
        Nat.dvd_one.mp (Nat.dvd_of_mul_dvd_mul_left hS0 (by rwa [mul_one]))
      rw [hL1]
      exact Nat.coprime_one_right _
  have hc₁' := hcopL.coprime_dvd_right (Nat.dvd_lcm_left c₁ c₂)
  have hc₂' := hcopL.coprime_dvd_right (Nat.dvd_lcm_right c₁ c₂)
  have hnegA : A⁻¹ (-1) ≠ 0 := ((isUnit_one.neg : IsUnit (-1 : ZMod c₁)).map A⁻¹).ne_zero
  have hnegB : B⁻¹ (-1) ≠ 0 := ((isUnit_one.neg : IsUnit (-1 : ZMod c₂)).map B⁻¹).ne_zero
  have hφ₁ : (((Real.sqrt (Nat.totient M₁))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (Nat.totient M₁) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M₁)))
    exact_mod_cast (inv_pos.mpr this).ne'
  have hφ₂ : (((Real.sqrt (Nat.totient M₂))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (Nat.totient M₂) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M₂)))
    exact_mod_cast (inv_pos.mpr this).ne'
  have hs₁C : ((M₁ / c₁ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hs₁.ne'
  have hs₂C : ((M₂ / c₂ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hs₂.ne'
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero hφ₁ hφ₂) (mul_ne_zero hs₁C hs₂C)) (mul_ne_zero hnegA hnegB))
    (mul_ne_zero (PAG.Part16.gaussSum_ne_zero hA) (PAG.Part16.gaussSum_ne_zero hB)))
    (mul_ne_zero (chi_natCast_ne_zero A⁻¹ _ hcop₁) (chi_natCast_ne_zero B⁻¹ _ hcop₂)))
    (mul_ne_zero (chi_natCast_ne_zero A⁻¹ _ hc₁') (chi_natCast_ne_zero B⁻¹ _ hc₂'))) key

/-- **4c. 0 になる条件**：|u₁, A⟩ ⋆ |u₂, B⟩ = 0 ⇔ (S/s₁, c₁) ≠ 1 または (S/s₂, c₂) ≠ 1。 -/
theorem conv_mixed_eq_zero_iff (u₁ M₁ u₂ M₂ N : ℕ) [NeZero N] (h₁ : u₁ * M₁ = N) (h₂ : u₂ * M₂ = N)
    (c₁ c₂ : ℕ) [NeZero c₁] [NeZero c₂] (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (hA : A.IsPrimitive) (hB : B.IsPrimitive) :
    PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ A) (gket u₂ M₂ N h₂ c₂ hc₂ B) = 0 ↔
      ¬ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁)).Coprime c₁ ∧
        (Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂)).Coprime c₂) :=
  ⟨fun h0 hc => conv_mixed_ne_zero u₁ M₁ u₂ M₂ N h₁ h₂ c₁ c₂ hc₁ hc₂ A B hA hB hc.1 hc.2 h0,
    conv_mixed_eq_zero u₁ M₁ u₂ M₂ N h₁ h₂ c₁ c₂ hc₁ hc₂ A B hA hB⟩

/-! ### 5. 一般公式 -/

/-- **5. 異なる殻の畳み込みの一般公式**：
|u₁, A⟩ ⋆ |u₂, B⟩ = (g/√(φ(M₁)φ(M₂)))·Ā(S/s₁)B̄(S/s₂)·(τ(A)τ(B)/τ(Ψ))·Σ_{e ∣ L, (e, d) = 1} (μ(e)Ψ̄(e)/e)·R(N/(Sde), Ψ)。 -/
theorem conv_mixed (u₁ M₁ u₂ M₂ N : ℕ) [NeZero N] (h₁ : u₁ * M₁ = N) (h₂ : u₂ * M₂ = N)
    (c₁ c₂ d : ℕ) [NeZero c₁] [NeZero c₂] [NeZero d] (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (hdL : d ∣ Nat.lcm c₁ c₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive)
    (hprod : A.changeLevel (Nat.dvd_lcm_left c₁ c₂) * B.changeLevel (Nat.dvd_lcm_right c₁ c₂) =
      Ψ.changeLevel hdL) :
    PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ A) (gket u₂ M₂ N h₂ c₂ hc₂ B) =
      (((Nat.gcd (M₁ / c₁) (M₂ / c₂) : ℕ) : ℂ) /
          ((Real.sqrt ((Nat.totient M₁ : ℝ) * (Nat.totient M₂ : ℝ)) : ℝ) : ℂ) *
        (A⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁) : ℕ) : ZMod c₁) *
          B⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂) : ℕ) : ZMod c₂)) *
        (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar)) •
      ∑ e ∈ (Nat.lcm c₁ c₂).divisors.filter (fun e => e.Coprime d),
        ((ArithmeticFunction.moebius e : ℂ) * Ψ⁻¹ (e : ZMod d) / (e : ℂ)) •
          rk (N := N) (N / (Nat.lcm (M₁ / c₁) (M₂ / c₂) * d * e)) d Ψ := by
  classical
  have : NeZero (Nat.lcm c₁ c₂) := ⟨Nat.lcm_ne_zero (NeZero.ne c₁) (NeZero.ne c₂)⟩
  by_cases hcop : (Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁)).Coprime c₁ ∧
      (Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂)).Coprime c₂
  swap
  · -- 両辺とも 0
    rw [conv_mixed_eq_zero u₁ M₁ u₂ M₂ N h₁ h₂ c₁ c₂ hc₁ hc₂ A B hA hB hcop,
      mixed_unit_factor_eq_zero A B _ _ hcop, mul_zero, zero_mul, zero_smul]
  obtain ⟨hcop₁, hcop₂⟩ := hcop
  have hM₁ := neZero_of_mul h₁
  have hM₂ := neZero_of_mul h₂
  have hs₁0 : 0 < M₁ / c₁ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M₁)) hc₁)
    (Nat.pos_of_ne_zero (NeZero.ne c₁))
  have hs₂0 : 0 < M₂ / c₂ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M₂)) hc₂)
    (Nat.pos_of_ne_zero (NeZero.ne c₂))
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hSLN : Nat.lcm (M₁ / c₁) (M₂ / c₂) * Nat.lcm c₁ c₂ ∣ N :=
    lcm_mul_lcm_dvd (by rw [Nat.div_mul_cancel hc₁]; exact Dvd.intro_left u₁ h₁)
      (by rw [Nat.div_mul_cancel hc₂]; exact Dvd.intro_left u₂ h₂) hcop₁ hcop₂
  have hτΨ : gaussSum Ψ stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero hΨ
  have hφ₁ : (0 : ℝ) < Real.sqrt (Nat.totient M₁) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M₁)))
  have hφ₂ : (0 : ℝ) < Real.sqrt (Nat.totient M₂) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M₂)))
  have hgS : ((Nat.gcd (M₁ / c₁) (M₂ / c₂) : ℕ) : ℂ) * ((Nat.lcm (M₁ / c₁) (M₂ / c₂) : ℕ) : ℂ) =
      ((M₁ / c₁ : ℕ) : ℂ) * ((M₂ / c₂ : ℕ) : ℂ) := by
    exact_mod_cast Nat.gcd_mul_lcm (M₁ / c₁) (M₂ / c₂)
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [dft_conv_mixed u₁ M₁ u₂ M₂ N h₁ h₂ c₁ c₂ hc₁ hc₂ A B hA hB ξ, map_smul, Pi.smul_apply, smul_eq_mul,
    map_sum, Finset.sum_apply]
  set s₁ := M₁ / c₁ with hs₁def
  set s₂ := M₂ / c₂ with hs₂def
  set S := Nat.lcm s₁ s₂ with hSdef
  have hS0 : 0 < S := Nat.lcm_pos hs₁0 hs₂0
  -- 各 e での殻の等式
  have hshell : ∀ e ∈ (Nat.lcm c₁ c₂).divisors.filter (fun e => e.Coprime d),
      N / (S * d * e) * (S * d * e) = N ∧ d ∣ S * d * e ∧ S * d * e / d = S * e := by
    intro e he
    rw [Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨heL, _⟩, hed⟩ := he
    have hde : d * e ∣ Nat.lcm c₁ c₂ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hed.symm hdL heL
    have hSde : S * d * e ∣ N := by
      rw [mul_assoc]; exact (mul_dvd_mul_left S hde).trans hSLN
    refine ⟨Nat.div_mul_cancel hSde, Dvd.intro (S * e) (by ring), ?_⟩
    rw [show S * d * e = d * (S * e) by ring, Nat.mul_div_cancel_left _ hd0]
  have hterm : ∀ e ∈ (Nat.lcm c₁ c₂).divisors.filter (fun e => e.Coprime d),
      𝓕 (((ArithmeticFunction.moebius e : ℂ) * Ψ⁻¹ (e : ZMod d) / (e : ℂ)) •
          rk (N := N) (N / (S * d * e)) d Ψ) ξ
        = ((ArithmeticFunction.moebius e : ℂ) * Ψ⁻¹ (e : ZMod d) / (e : ℂ)) *
          (if S * e ∣ ξ.val then ((S * e : ℕ) : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar *
            Ψ⁻¹ ((ξ.val / (S * e) : ℕ) : ZMod d) else 0) := by
    intro e he
    obtain ⟨h1, h2, h3⟩ := hshell e he
    rw [map_smul, Pi.smul_apply, smul_eq_mul, dft_rk (N / (S * d * e)) (S * d * e) N h1 d h2 Ψ hΨ ξ, h3]
  rw [Finset.sum_congr rfl hterm]
  by_cases hSξ : S ∣ ξ.val
  · obtain ⟨t, ht⟩ := hSξ
    rw [ite_eq_left ⟨t, ht⟩, ht, Nat.mul_div_cancel_left t hS0, inv_mul_inv_mixed hdL A B Ψ hprod t,
      inv_mul_inv_neg_one hdL A B Ψ hprod]
    -- 右辺の各項：[Se ∣ St] = [e ∣ t]、St/(Se) = t/e
    have hterm2 : ∀ e ∈ (Nat.lcm c₁ c₂).divisors.filter (fun e => e.Coprime d),
        ((ArithmeticFunction.moebius e : ℂ) * Ψ⁻¹ (e : ZMod d) / (e : ℂ)) *
          (if S * e ∣ S * t then ((S * e : ℕ) : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar *
            Ψ⁻¹ ((S * t / (S * e) : ℕ) : ZMod d) else 0)
        = ((S : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar) *
          (if e ∣ t then (ArithmeticFunction.moebius e : ℂ) * (Ψ⁻¹ (e : ZMod d) * Ψ⁻¹ ((t / e : ℕ) : ZMod d))
            else 0) := by
      intro e he
      have he0 : (e : ℂ) ≠ 0 := by
        rw [Finset.mem_filter, Nat.mem_divisors] at he
        exact_mod_cast (Nat.pos_of_dvd_of_pos he.1.1 (Nat.pos_of_ne_zero he.1.2)).ne'
      by_cases het : e ∣ t
      · rw [ite_eq_left ((Nat.mul_dvd_mul_iff_left hS0).mpr het), ite_eq_left het,
          Nat.mul_div_mul_left t e hS0]
        push_cast
        field_simp
      · rw [ite_eq_right (fun hd' => het ((Nat.mul_dvd_mul_iff_left hS0).mp hd')), ite_eq_right het,
          mul_zero, mul_zero]
    rw [Finset.sum_congr rfl hterm2, ← Finset.mul_sum, mobius_identity (Nat.lcm c₁ c₂) d hdL Ψ⁻¹ t,
      Real.sqrt_mul (Nat.cast_nonneg _), ← hgS]
    have a1 : ((Real.sqrt (Nat.totient M₁) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφ₁.ne'
    have a2 : ((Real.sqrt (Nat.totient M₂) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφ₂.ne'
    push_cast
    field_simp
  · rw [ite_eq_right hSξ]
    symm
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro e he
    rw [ite_eq_right (fun hd' => hSξ ((Dvd.intro e rfl).trans hd')), mul_zero]

/-! ### 6. 系 -/

/-- **6a. 双対の殻の選択**：N の素因数がすべて c₁ と c₂ を割るなら、s₁ ≠ s₂ のとき |u₁, A⟩ ⋆ |u₂, B⟩ = 0。 -/
theorem conv_ne_dual_zero (u₁ M₁ u₂ M₂ N : ℕ) [NeZero N] (h₁ : u₁ * M₁ = N) (h₂ : u₂ * M₂ = N)
    (c₁ c₂ : ℕ) [NeZero c₁] [NeZero c₂] (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ N → q ∣ c₁ ∧ q ∣ c₂) (hne : M₁ / c₁ ≠ M₂ / c₂) :
    PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ A) (gket u₂ M₂ N h₂ c₂ hc₂ B) = 0 := by
  apply conv_mixed_eq_zero u₁ M₁ u₂ M₂ N h₁ h₂ c₁ c₂ hc₁ hc₂ A B hA hB
  rintro ⟨hcop₁, hcop₂⟩
  have hSN : Nat.lcm (M₁ / c₁) (M₂ / c₂) ∣ N :=
    Nat.lcm_dvd ((Nat.div_dvd_of_dvd hc₁).trans (Dvd.intro_left u₁ h₁))
      ((Nat.div_dvd_of_dvd hc₂).trans (Dvd.intro_left u₂ h₂))
  have key : ∀ s c : ℕ, s ∣ Nat.lcm (M₁ / c₁) (M₂ / c₂) →
      (Nat.lcm (M₁ / c₁) (M₂ / c₂) / s).Coprime c → (∀ q : ℕ, q.Prime → q ∣ N → q ∣ c) →
      Nat.lcm (M₁ / c₁) (M₂ / c₂) = s := by
    intro s c hsS hcop hq
    have hone : Nat.lcm (M₁ / c₁) (M₂ / c₂) / s = 1 := by
      by_contra hne1
      obtain ⟨q, hq', hqd⟩ := Nat.exists_prime_and_dvd hne1
      have hqc : q ∣ c := hq q hq' (hqd.trans ((Nat.div_dvd_of_dvd hsS).trans hSN))
      have h := Nat.dvd_gcd hqd hqc
      rw [Nat.Coprime.gcd_eq_one hcop] at h
      exact hq'.not_dvd_one h
    have h := Nat.div_mul_cancel hsS
    rw [hone, one_mul] at h
    exact h.symm
  exact hne ((key _ c₁ (Nat.dvd_lcm_left _ _) hcop₁ (fun q hq hqN => (hprimes q hq hqN).1)).symm.trans
    (key _ c₂ (Nat.dvd_lcm_right _ _) hcop₂ (fun q hq hqN => (hprimes q hq hqN).2)))

/-- **6b. 同じ双対の殻**（s₁ = s₂ = s）：
|u₁, A⟩ ⋆ |u₂, B⟩ = (s/√(φ(M₁)φ(M₂)))·(τ(A)τ(B)/τ(Ψ))·Σ_{e ∣ L, (e, d) = 1} (μ(e)Ψ̄(e)/e)·R(N/(sde), Ψ)。 -/
theorem conv_same_dual (u₁ M₁ u₂ M₂ N : ℕ) [NeZero N] (h₁ : u₁ * M₁ = N) (h₂ : u₂ * M₂ = N)
    (c₁ c₂ d : ℕ) [NeZero c₁] [NeZero c₂] [NeZero d] (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (hdL : d ∣ Nat.lcm c₁ c₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive)
    (hprod : A.changeLevel (Nat.dvd_lcm_left c₁ c₂) * B.changeLevel (Nat.dvd_lcm_right c₁ c₂) =
      Ψ.changeLevel hdL) (hs : M₁ / c₁ = M₂ / c₂) :
    PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ A) (gket u₂ M₂ N h₂ c₂ hc₂ B) =
      (((M₁ / c₁ : ℕ) : ℂ) / ((Real.sqrt ((Nat.totient M₁ : ℝ) * (Nat.totient M₂ : ℝ)) : ℝ) : ℂ) *
        (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar)) •
      ∑ e ∈ (Nat.lcm c₁ c₂).divisors.filter (fun e => e.Coprime d),
        ((ArithmeticFunction.moebius e : ℂ) * Ψ⁻¹ (e : ZMod d) / (e : ℂ)) •
          rk (N := N) (N / (M₁ / c₁ * d * e)) d Ψ := by
  have hM₁ := neZero_of_mul h₁
  have hs0 : 0 < M₁ / c₁ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M₁)) hc₁)
    (Nat.pos_of_ne_zero (NeZero.ne c₁))
  rw [conv_mixed u₁ M₁ u₂ M₂ N h₁ h₂ c₁ c₂ d hc₁ hc₂ hdL A B Ψ hA hB hΨ hprod, ← hs, Nat.lcm_self,
    Nat.gcd_self, Nat.div_self hs0]
  simp

/-- **6c. 項が 1 つの場合**：L の素因数がすべて d を割るなら
|u₁, A⟩ ⋆ |u₂, B⟩ = (g/√(φ(M₁)φ(M₂)))·Ā(S/s₁)B̄(S/s₂)·(τ(A)τ(B)/τ(Ψ))·R(N/(Sd), Ψ)。 -/
theorem conv_mixed_single (u₁ M₁ u₂ M₂ N : ℕ) [NeZero N] (h₁ : u₁ * M₁ = N) (h₂ : u₂ * M₂ = N)
    (c₁ c₂ d : ℕ) [NeZero c₁] [NeZero c₂] [NeZero d] (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (hdL : d ∣ Nat.lcm c₁ c₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive)
    (hprod : A.changeLevel (Nat.dvd_lcm_left c₁ c₂) * B.changeLevel (Nat.dvd_lcm_right c₁ c₂) =
      Ψ.changeLevel hdL) (hrad : ∀ q : ℕ, q.Prime → q ∣ Nat.lcm c₁ c₂ → q ∣ d) :
    PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ A) (gket u₂ M₂ N h₂ c₂ hc₂ B) =
      (((Nat.gcd (M₁ / c₁) (M₂ / c₂) : ℕ) : ℂ) /
          ((Real.sqrt ((Nat.totient M₁ : ℝ) * (Nat.totient M₂ : ℝ)) : ℝ) : ℂ) *
        (A⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁) : ℕ) : ZMod c₁) *
          B⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂) : ℕ) : ZMod c₂)) *
        (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar)) •
      rk (N := N) (N / (Nat.lcm (M₁ / c₁) (M₂ / c₂) * d)) d Ψ := by
  have : NeZero (Nat.lcm c₁ c₂) := ⟨Nat.lcm_ne_zero (NeZero.ne c₁) (NeZero.ne c₂)⟩
  rw [conv_mixed u₁ M₁ u₂ M₂ N h₁ h₂ c₁ c₂ d hc₁ hc₂ hdL A B Ψ hA hB hΨ hprod,
    filter_coprime_eq_one (Nat.lcm c₁ c₂) d hrad, Finset.sum_singleton]
  congr 1
  simp

/-- **6d. 混合定理 A（ℤ/N）**：L の素因数がすべて d を割り、u′·(S·d) = N なら
|u₁, A⟩ ⋆ |u₂, B⟩ = C·|u′, Ψ⟩_N、C = (g·√φ(Sd)/√(φ(M₁)φ(M₂)))·Ā(S/s₁)B̄(S/s₂)·τ(A)τ(B)/τ(Ψ)。 -/
theorem conv_mixed_ket (u₁ M₁ u₂ M₂ N : ℕ) [NeZero N] (h₁ : u₁ * M₁ = N) (h₂ : u₂ * M₂ = N)
    (c₁ c₂ d : ℕ) [NeZero c₁] [NeZero c₂] [NeZero d] (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (hdL : d ∣ Nat.lcm c₁ c₂)
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive)
    (hprod : A.changeLevel (Nat.dvd_lcm_left c₁ c₂) * B.changeLevel (Nat.dvd_lcm_right c₁ c₂) =
      Ψ.changeLevel hdL) (hrad : ∀ q : ℕ, q.Prime → q ∣ Nat.lcm c₁ c₂ → q ∣ d)
    (u' : ℕ) (h' : u' * (Nat.lcm (M₁ / c₁) (M₂ / c₂) * d) = N) :
    PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ A) (gket u₂ M₂ N h₂ c₂ hc₂ B) =
      (((Nat.gcd (M₁ / c₁) (M₂ / c₂) : ℕ) : ℂ) *
          ((Real.sqrt (Nat.totient (Nat.lcm (M₁ / c₁) (M₂ / c₂) * d)) : ℝ) : ℂ) /
          ((Real.sqrt ((Nat.totient M₁ : ℝ) * (Nat.totient M₂ : ℝ)) : ℝ) : ℂ) *
        (A⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁) : ℕ) : ZMod c₁) *
          B⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂) : ℕ) : ZMod c₂)) *
        (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar)) •
      gket u' (Nat.lcm (M₁ / c₁) (M₂ / c₂) * d) N h' d (dvd_mul_left d _) Ψ := by
  have hW : 0 < Nat.lcm (M₁ / c₁) (M₂ / c₂) * d := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, mul_zero] at h'
    exact NeZero.ne N h'.symm
  have hv : N / (Nat.lcm (M₁ / c₁) (M₂ / c₂) * d) = u' := Nat.div_eq_of_eq_mul_left hW h'.symm
  rw [conv_mixed_single u₁ M₁ u₂ M₂ N h₁ h₂ c₁ c₂ d hc₁ hc₂ hdL A B Ψ hA hB hΨ hprod hrad, hv,
    rk_eq_gket u' _ N h' d (dvd_mul_left d _) Ψ, smul_smul]
  congr 1
  ring

/-- **6e. 定数の大きさ**：(S/s₁, c₁) = (S/s₂, c₂) = 1 なら |C|² = g²·φ(Sd)·c₁c₂/(φ(M₁)φ(M₂)·d)。 -/
theorem normSq_mixed_coef (M₁ M₂ c₁ c₂ d : ℕ) [NeZero M₁] [NeZero M₂] [NeZero c₁] [NeZero c₂] [NeZero d]
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive)
    (hcop₁ : (Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁)).Coprime c₁)
    (hcop₂ : (Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂)).Coprime c₂) :
    Complex.normSq ((((Nat.gcd (M₁ / c₁) (M₂ / c₂) : ℕ) : ℂ) *
          ((Real.sqrt (Nat.totient (Nat.lcm (M₁ / c₁) (M₂ / c₂) * d)) : ℝ) : ℂ) /
          ((Real.sqrt ((Nat.totient M₁ : ℝ) * (Nat.totient M₂ : ℝ)) : ℝ) : ℂ) *
        (A⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁) : ℕ) : ZMod c₁) *
          B⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂) : ℕ) : ZMod c₂)) *
        (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar))) =
      (Nat.gcd (M₁ / c₁) (M₂ / c₂) : ℝ) ^ 2 * (Nat.totient (Nat.lcm (M₁ / c₁) (M₂ / c₂) * d) : ℝ) *
          ((c₁ : ℝ) * c₂) / ((Nat.totient M₁ : ℝ) * Nat.totient M₂ * d) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hφ₁ : (Nat.totient M₁ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M₁))).ne'
  have hφ₂ : (Nat.totient M₂ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M₂))).ne'
  simp only [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_natCast]
  rw [normSq_chi_natCast A⁻¹ _ hcop₁, normSq_chi_natCast B⁻¹ _ hcop₂, PAG.Part16.normSq_gaussSum hA,
    PAG.Part16.normSq_gaussSum hB, PAG.Part16.normSq_gaussSum hΨ, Real.mul_self_sqrt (Nat.cast_nonneg _),
    Real.mul_self_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  field_simp

end PAG.Part204

#print axioms PAG.Part204.lcm_mul_lcm_dvd
#print axioms PAG.Part204.div_mul_aux
#print axioms PAG.Part204.dft_conv_mixed
#print axioms PAG.Part204.changeLevel_neg_one
#print axioms PAG.Part204.inv_mul_inv_neg_one
#print axioms PAG.Part204.inv_mul_inv_mixed
#print axioms PAG.Part204.mixed_unit_factor_eq_zero
#print axioms PAG.Part204.conv_mixed_eq_zero
#print axioms PAG.Part204.conv_mixed_ne_zero
#print axioms PAG.Part204.conv_mixed_eq_zero_iff
#print axioms PAG.Part204.conv_mixed
#print axioms PAG.Part204.conv_ne_dual_zero
#print axioms PAG.Part204.conv_same_dual
#print axioms PAG.Part204.conv_mixed_single
#print axioms PAG.Part204.conv_mixed_ket
#print axioms PAG.Part204.normSq_mixed_coef
