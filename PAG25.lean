/-
  PAG 2.0 Part 21（2026-10-18）— |J|² = p^c と赤道係数 conj(Ĵ)²、P¹ 上の定理 B と鏡像定理 B
  1. χ₁, χ₂, χ₁χ₂ 原始的なら |J(χ₁,χ₂)|² = p^c、conj J / J = conj(Ĵ)²（Ĵ = J/√p^c）
  2. 赤道での絡み合い B_N = conj(Ĵ)² B_S
  3. 南の定理 B（P¹ 版）と北の鏡像定理 B
  4. 赤道残留（w = 0, c = 1）: 南北の像はどちらも −χ(−1)/(p−1) · 1_赤道 を共有する
-/
import PAG24

namespace PAG.Part25

open ZMod Finset PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part23 PAG.Part24

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## 1. |J|² = p^c と conj J / J = conj(Ĵ)² -/

section Jacobi

variable {n : ℕ}

/-- **|J(χ₁,χ₂)|² = p^c**（χ₁, χ₂, χ₁χ₂ 原始的）。τ₁τ₂ = J τ₁₂ と |τ|² = p^c から。 -/
theorem normSq_J (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    Complex.normSq (PAG.Part7.J χ₁ χ₂) = ((p ^ (n + 1) : ℕ) : ℝ) := by
  have := PAG.Part8.gauss_mul_gauss_eq_jacobi_mul_primitive χ₁ χ₂ h₁₂ stdAddChar
  have e := congrArg Complex.normSq this
  rw [map_mul, map_mul, PAG.Part16.normSq_gaussSum h₁, PAG.Part16.normSq_gaussSum h₂,
    PAG.Part16.normSq_gaussSum h₁₂] at e
  have hq : ((p ^ (n + 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  exact (mul_right_cancel₀ hq e).symm

/-- 規格化ヤコビ和 Ĵ = J / √p^c。 -/
noncomputable def Jhat (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) : ℂ :=
  PAG.Part7.J χ₁ χ₂ / ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ)

theorem normSq_Jhat (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    Complex.normSq (Jhat χ₁ χ₂) = 1 := by
  have hq : (0 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.out.pos _
  rw [Jhat, map_div₀, normSq_J χ₁ χ₂ h₁ h₂ h₁₂, Complex.normSq_ofReal,
    Real.mul_self_sqrt hq.le, div_self hq.ne']

/-- **conj J / J = conj(Ĵ)²**。 -/
theorem conjJ_div_J (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    starRingEnd ℂ (PAG.Part7.J χ₁ χ₂) / PAG.Part7.J χ₁ χ₂ = (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2 := by
  have hN := normSq_J χ₁ χ₂ h₁ h₂ h₁₂
  have hq : (0 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.out.pos _
  have hJ : PAG.Part7.J χ₁ χ₂ ≠ 0 := by
    intro h; rw [h, map_zero] at hN; exact hq.ne' hN.symm
  have hs : ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have hmc : PAG.Part7.J χ₁ χ₂ * starRingEnd ℂ (PAG.Part7.J χ₁ χ₂) = ((p ^ (n + 1) : ℕ) : ℂ) := by
    rw [Complex.mul_conj, hN]; push_cast; rfl
  have hss : ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) ^ 2 = ((p ^ (n + 1) : ℕ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq.le]; push_cast; rfl
  rw [Jhat, map_div₀, Complex.conj_ofReal, div_pow, hss, ← hmc]
  field_simp

/-- **赤道での絡み合い（Ĵ 形）**: B_N(|0,χ₁⟩,|0,χ₂⟩) = conj(Ĵ)² · B_S(|0,χ₁⟩,|0,χ₂⟩)。 -/
theorem equator_intertwine_hat (K : ℕ) (h : 0 + (n + 1) ≤ K) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    BN (kS K 0 (n + 1) h χ₁) (kS K 0 (n + 1) h χ₂)
      = (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2 • BS (kS K 0 (n + 1) h χ₁) (kS K 0 (n + 1) h χ₂) := by
  rw [equator_intertwine K h χ₁ χ₂ h₁ h₂ h₁₂, conjJ_div_J χ₁ χ₂ h₁ h₂ h₁₂]

end Jacobi

/-! ## 2. P¹ 上の定理 B と鏡像定理 B -/

section ThmB

omit hp in
theorem chi_inv_neg_one {N : ℕ} (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply_eq_inv']
  exact (eq_inv_of_mul_eq_one_left (PAG.Part9.chi_neg_one_sq χ)).symm

/-- 定理 B の像（チャート上の関数）: 1_{p^(w+c)} − (p−1)⁻¹ 1_{S_(w+c−1)}。 -/
noncomputable def cascade (K w n : ℕ) : ZMod (p ^ K) → ℂ :=
  ball (p := p) K (w + (n + 1)) - ((p : ℂ) - 1)⁻¹ • (ball (p := p) K (w + n) - ball (p := p) K (w + (n + 1)))

/-- **定理 B（P¹ 版、南）**: B_S(|w,χ⟩, |w,χ̄⟩) = χ(−1) · extS(cascade)。 -/
theorem thmB_south (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    BS (kS K w (n + 1) hK χ) (kS K w (n + 1) hK χ⁻¹) = χ (-1) • extS (cascade (p := p) K w n) := by
  unfold BS kS
  show extS (PAG.Part15.conv (ket K w (n + 1) hK χ)
    (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))) = _
  rw [thmB_closed K w n hK χ hχ, extS_smul]
  rfl

/-- **鏡像定理 B（北）**: B_N(|−w,χ⟩, |−w,χ̄⟩) = χ(−1) · extN(cascade)。 -/
theorem mirror_thmB (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    BN (kN K w (n + 1) hK χ) (kN K w (n + 1) hK χ⁻¹) = χ (-1) • extN (cascade (p := p) K w n) := by
  rw [BN_eq]
  unfold kN
  show extN (PAG.Part15.conv (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))
    (ket K w (n + 1) hK (((χ⁻¹)⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))) = _
  rw [thmB_closed K w n hK χ⁻¹ (PAG.Part16.isPrimitive_inv hχ), chi_inv_neg_one, extN_smul]
  rfl

/-- 鏡像定理 B は南の定理 B の W 像: B_N(W·, W·) = W B_S(·, ·)。 -/
theorem mirror_thmB_eq_W (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    BN (W (kS K w (n + 1) hK χ⁻¹)) (W (kS K w (n + 1) hK χ))
      = W (χ (-1) • extS (cascade (p := p) K w n)) := by
  rw [← chi_inv_neg_one χ, ← thmB_south K w n hK χ⁻¹ (PAG.Part16.isPrimitive_inv hχ), inv_inv]
  rfl

end ThmB

/-! ## 3. 赤道残留（w = 0, c = 1） -/

section Residue

/-- 単数 ⇔ p ∤ val（K ≥ 1）。 -/
theorem isUnit_iff_not_dvd {K : ℕ} (hK : 1 ≤ K) (x : ZMod (p ^ K)) : IsUnit x ↔ ¬ p ∣ x.val := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have e := ZMod.isUnit_iff_coprime x.val (p ^ K)
  rw [ZMod.natCast_zmod_val, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd hp.out] at e
  exact e

open Classical in
/-- 赤道（単数）の指示関数を P¹ 上の関数として（南北とも同じ）。 -/
noncomputable def Eq1 (N : ℕ) : P1F N := (fun x => if IsUnit x then 1 else 0, fun y => if IsUnit y then 1 else 0)

/-- c = 1, w = 0 の cascade の extS: extS(1_{pZ}) − (p−1)⁻¹ · 1_赤道。 -/
theorem extS_cascade00 (K : ℕ) (hK : 1 ≤ K) :
    extS (cascade (p := p) K 0 0) = extS (ball (p := p) K 1) - ((p : ℂ) - 1)⁻¹ • Eq1 (p ^ K) := by
  have hb0 : ∀ x : ZMod (p ^ K), ball (p := p) K 0 x = 1 := fun x => by simp [ball]
  have hb1 : ∀ x : ZMod (p ^ K), ball (p := p) K 1 x = if IsUnit x then 0 else 1 := fun x => by
    simp only [ball, isUnit_iff_not_dvd hK, pow_one]; split_ifs <;> simp_all
  ext x
  · simp only [extS, cascade, Eq1, Prod.fst_sub, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      zero_add, hb0, hb1]
    split_ifs <;> ring
  · by_cases h1 : IsUnit x
    · have hu := (inv_inv_of_unit h1).1
      simp only [extS, cascade, Eq1, Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        zero_add, hb0, hb1, h1, hu, ite_true]
      ring
    · simp only [extS, cascade, Eq1, Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        h1, ite_false]
      ring

/-- c = 1, w = 0 の cascade の extN: extN(1_{pZ}) − (p−1)⁻¹ · 1_赤道。 -/
theorem extN_cascade00 (K : ℕ) (hK : 1 ≤ K) :
    extN (cascade (p := p) K 0 0) = extN (ball (p := p) K 1) - ((p : ℂ) - 1)⁻¹ • Eq1 (p ^ K) := by
  have h := congrArg W (extS_cascade00 (p := p) K hK)
  rw [W_extS] at h
  rw [h]
  rfl

/-- **赤道残留の共有**（c = 1, w = 0）: 南の定理 B と北の鏡像定理 B の像は、
それぞれの球 1_{pZ} の持ち上げを除くと、同じ赤道残留 −χ(−1)/(p−1) · 1_赤道 になる。 -/
theorem equator_residue (K : ℕ) (hK : 0 + (0 + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (0 + 1))) (hχ : χ.IsPrimitive) :
    BS (kS K 0 (0 + 1) hK χ) (kS K 0 (0 + 1) hK χ⁻¹) - χ (-1) • extS (ball (p := p) K 1)
      = -(χ (-1) * ((p : ℂ) - 1)⁻¹) • Eq1 (p ^ K) ∧
    BN (kN K 0 (0 + 1) hK χ) (kN K 0 (0 + 1) hK χ⁻¹) - χ (-1) • extN (ball (p := p) K 1)
      = -(χ (-1) * ((p : ℂ) - 1)⁻¹) • Eq1 (p ^ K) := by
  refine ⟨?_, ?_⟩
  · rw [thmB_south K 0 0 hK χ hχ, extS_cascade00 K (by omega), smul_sub, smul_smul]
    rw [neg_smul]; abel
  · rw [mirror_thmB K 0 0 hK χ hχ, extN_cascade00 K (by omega), smul_sub, smul_smul]
    rw [neg_smul]; abel

end Residue

end PAG.Part25

#print axioms PAG.Part25.normSq_J
#print axioms PAG.Part25.normSq_Jhat
#print axioms PAG.Part25.conjJ_div_J
#print axioms PAG.Part25.equator_intertwine_hat
#print axioms PAG.Part25.chi_inv_neg_one
#print axioms PAG.Part25.thmB_south
#print axioms PAG.Part25.mirror_thmB
#print axioms PAG.Part25.mirror_thmB_eq_W
#print axioms PAG.Part25.isUnit_iff_not_dvd
#print axioms PAG.Part25.extS_cascade00
#print axioms PAG.Part25.extN_cascade00
#print axioms PAG.Part25.equator_residue
