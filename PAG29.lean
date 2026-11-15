/-
  PAG 2.0 Part 25（2026-10-19）
  1. 本来の射影直線 ProjLine(p^K) 上のケット・べき等元と、定理 A・鏡像定理 A・赤道絡み合いの直接表示
  2. 定理 B の像 = べき等元 ε_{w0} の単項、ε による選別と自己畳み込み
     （注意: 自己畳み込みの固有値は χ(−1)·p^K/|S_{w0}|。χ(−1) = 1 のときに限り p^K/|S_{w0}|）
-/
import PAG28

namespace PAG.Part29

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part23 PAG.Part24
  PAG.Part25 PAG.Part26 PAG.Part27 PAG.Part28

open Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## 1. ProjLine 上のケット・べき等元と定理 A -/

section ProjKets

variable (K : ℕ) (hK : 1 ≤ K)

/-- 射影直線上の南ケット。 -/
noncomputable def ketS_proj (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm ⟨kS K w c h χ, compat_extS _⟩

/-- 射影直線上の北ケット。 -/
noncomputable def ketN_proj (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm ⟨kN K w c h χ, compat_extN _⟩

/-- 射影直線上のべき等元 ε_a の南拡張。 -/
noncomputable def epsS_proj (a : ℕ) : ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm ⟨extS (PAG.Part14.epsBall (Pavg (p := p) K) K a), compat_extS _⟩

/-- 射影直線上のべき等元 ε_a の北拡張。 -/
noncomputable def epsN_proj (a : ℕ) : ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm ⟨extN (PAG.Part14.epsBall (Pavg (p := p) K) K a), compat_extN _⟩

theorem BSproj_symm {F G : P1F (p ^ K)} (hF : Compat F) (hG : Compat G) :
    BSproj K hK ((projFunEquiv K hK).symm ⟨F, hF⟩) ((projFunEquiv K hK).symm ⟨G, hG⟩)
      = (projFunEquiv K hK).symm ⟨BS F G, compat_extS _⟩ := by
  unfold BSproj
  simp only [LinearEquiv.apply_symm_apply]

theorem BNproj_symm {F G : P1F (p ^ K)} (hF : Compat F) (hG : Compat G) :
    BNproj K hK ((projFunEquiv K hK).symm ⟨F, hF⟩) ((projFunEquiv K hK).symm ⟨G, hG⟩)
      = (projFunEquiv K hK).symm ⟨BN F G, compat_extN _⟩ := by
  unfold BNproj
  simp only [LinearEquiv.apply_symm_apply]

/-- 逆同型のスカラー倍: symm ⟨a • F⟩ = a • symm ⟨F⟩。 -/
theorem symm_smul (a : ℂ) {F : P1F (p ^ K)} (hF : Compat F) (haF : Compat (a • F)) :
    (projFunEquiv K hK).symm ⟨a • F, haF⟩ = a • (projFunEquiv K hK).symm ⟨F, hF⟩ := by
  rw [← LinearEquiv.map_smul]
  rfl

theorem projFun_BSproj (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    (projFunEquiv K hK (BSproj K hK Φ Ψ)).1 = BS (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1 := by
  unfold BSproj; rw [LinearEquiv.apply_symm_apply]

theorem projFun_BNproj (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    (projFunEquiv K hK (BNproj K hK Φ Ψ)).1 = BN (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1 := by
  unfold BNproj; rw [LinearEquiv.apply_symm_apply]

theorem projFun_ketS (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    (projFunEquiv K hK (ketS_proj K hK w c h χ)).1 = kS K w c h χ := by
  unfold ketS_proj; rw [LinearEquiv.apply_symm_apply]

theorem projFun_ketN (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    (projFunEquiv K hK (ketN_proj K hK w c h χ)).1 = kN K w c h χ := by
  unfold ketN_proj; rw [LinearEquiv.apply_symm_apply]

theorem projFun_epsS (a : ℕ) :
    (projFunEquiv K hK (epsS_proj K hK a)).1 = extS (PAG.Part14.epsBall (Pavg (p := p) K) K a) := by
  unfold epsS_proj; rw [LinearEquiv.apply_symm_apply]

theorem projFun_epsN (a : ℕ) :
    (projFunEquiv K hK (epsN_proj K hK a)).1 = extN (PAG.Part14.epsBall (Pavg (p := p) K) K a) := by
  unfold epsN_proj; rw [LinearEquiv.apply_symm_apply]

/-- **W_proj |w,χ⟩ = |−w,χ̄⟩**（射影直線上）。 -/
theorem Wpull_ketS_proj (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    Wpull (ketS_proj K hK w c h χ) = ketN_proj K hK w c h χ⁻¹ := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  rw [projFun_Wpull, ketS_proj, ketN_proj, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact W_kS K w c h χ

/-- **赤道ケットの南北一致**（射影直線上、c ≥ 1）。 -/
theorem ketS0_eq_ketN0_proj (c : ℕ) (hc : 1 ≤ c) (h : 0 + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    ketS_proj K hK 0 c h χ = ketN_proj K hK 0 c h χ := by
  unfold ketS_proj ketN_proj
  congr 1
  exact Subtype.ext (kS0_eq_kN0 K c hc h χ)

/-- **定理 A（射影直線上、南）**。 -/
theorem thmA_BSproj (w n v : ℕ) (hv : v ≤ n) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    BSproj K hK (ketS_proj K hK w (n + 1) h χ₁) (ketS_proj K hK w (n + 1) h χ₂)
      = ((Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) : ℝ) *
          (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
            (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))) : ℂ) •
        ketS_proj K hK (w + v) (n + 1 - v) (by omega) ψ := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  simp only [LinearEquiv.map_smul, Submodule.coe_smul, projFun_BSproj, projFun_ketS]
  exact thmA_south K w n v hv h χ₁ χ₂ h₁ h₂ ψ hψ hprod

/-- **鏡像定理 A（射影直線上、北）**。 -/
theorem mirror_thmA_BNproj (w n v : ℕ) (hv : v ≤ n) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    BNproj K hK (ketN_proj K hK w (n + 1) h χ₁) (ketN_proj K hK w (n + 1) h χ₂)
      = ((Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) : ℝ) *
          starRingEnd ℂ (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
            (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))) : ℂ) •
        ketN_proj K hK (w + v) (n + 1 - v) (by omega) ψ := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  simp only [LinearEquiv.map_smul, Submodule.coe_smul, projFun_BNproj, projFun_ketN]
  exact mirror_thmA K w n v hv h χ₁ χ₂ h₁ h₂ ψ hψ hprod

/-- **赤道での絡み合い（射影直線上）**: B_N^proj = conj(Ĵ)² B_S^proj。 -/
theorem equator_intertwine_proj {n : ℕ} (h : 0 + (n + 1) ≤ K) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    BNproj K hK (ketS_proj K hK 0 (n + 1) h χ₁) (ketS_proj K hK 0 (n + 1) h χ₂)
      = (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2 •
          BSproj K hK (ketS_proj K hK 0 (n + 1) h χ₁) (ketS_proj K hK 0 (n + 1) h χ₂) := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  simp only [LinearEquiv.map_smul, Submodule.coe_smul, projFun_BNproj, projFun_BSproj, projFun_ketS]
  exact equator_intertwine_hat K h χ₁ χ₂ h₁ h₂ h₁₂

end ProjKets

/-! ## 2. 球平均の部分群表示、吸収律、ε の直交べき等性 -/

section Absorb

/-- 球 p^(K−u) Z/p^K を部分群として（= ι_{K−u} の像、位数 p^u）。 -/
noncomputable def Hs (K u : ℕ) : AddSubgroup (ZMod (p ^ K)) :=
  (shellEmb (p := p) K (K - u) (Nat.sub_le K u)).range

theorem mem_Hs (K u : ℕ) (x : ZMod (p ^ K)) : x ∈ Hs (p := p) K u ↔ p ^ (K - u) ∣ x.val := by
  rw [Hs, AddMonoidHom.mem_range]
  exact mem_range_iff K (K - u) (Nat.sub_le K u) x

theorem indH_Hs (K u : ℕ) : indH (K := ℂ) (Hs (p := p) K u) = ball (p := p) K (K - u) := by
  funext x
  simp only [indH, ball, mem_Hs]

theorem cardH_Hs (K u : ℕ) (hu : u ≤ K) : cardH (Hs (p := p) K u) = p ^ u := by
  have e : (univ.filter (fun y => y ∈ Hs (p := p) K u))
      = univ.image (shellEmb (p := p) K (K - u) (Nat.sub_le K u)) := by
    ext x
    simp [Hs, AddMonoidHom.mem_range]
  unfold cardH
  rw [e, card_image_of_injective _ (shellEmb_injective K (K - u) (Nat.sub_le K u)), card_univ, ZMod.card,
    Nat.sub_sub_self hu]

theorem ballAvg_Hs (K u : ℕ) (hu : u ≤ K) : ballAvg (K := ℂ) (Hs (p := p) K u) = Pavg (p := p) K u := by
  rw [ballAvg, indH_Hs, cardH_Hs K u hu, Pavg]
  push_cast
  rfl

theorem Hs_mono (K : ℕ) : Monotone (Hs (p := p) K) := by
  intro u u' huu x hx
  rw [mem_Hs] at hx ⊢
  exact (pow_dvd_pow p (by omega)).trans hx

/-- **球平均の吸収律** P(a) ⋆ P(b) = P(b)（a ≤ b ≤ K）。 -/
theorem Pavg_absorb (K a b : ℕ) (hab : a ≤ b) (hb : b ≤ K) :
    conv (Pavg (p := p) K a) (Pavg (p := p) K b) = Pavg (p := p) K b := by
  rw [← ballAvg_Hs K a (by omega), ← ballAvg_Hs K b hb]
  exact ball_avg_absorb (Hs_mono K hab)

theorem epsBall_Pavg_eq (K a : ℕ) (ha : a ≤ K) :
    PAG.Part14.epsBall (Pavg (p := p) K) K a
      = PAG.Part14.epsBall (fun w => ballAvg (K := ℂ) (Hs (p := p) K w)) K a := by
  unfold PAG.Part14.epsBall
  split_ifs with h
  · dsimp only
    rw [ballAvg_Hs K a ha, ballAvg_Hs K (a + 1) (by omega)]
  · dsimp only
    rw [ballAvg_Hs K K le_rfl]

/-- **ε の直交べき等性**: ε_a ⋆ ε_b = δ_ab ε_a（a, b ≤ K）。 -/
theorem eps_conv (K a b : ℕ) (ha : a ≤ K) (hb : b ≤ K) :
    conv (PAG.Part14.epsBall (Pavg (p := p) K) K a) (PAG.Part14.epsBall (Pavg (p := p) K) K b)
      = if a = b then PAG.Part14.epsBall (Pavg (p := p) K) K a else 0 := by
  rw [epsBall_Pavg_eq K a ha, epsBall_Pavg_eq K b hb]
  exact ballEps_conv (Hs (p := p) K) (Hs_mono K) K ha hb

end Absorb

/-! ## 3. 定理 B のべき等元表示 -/

section ThmBEps

/-- 定理 B の係数 χ(−1)·p^K/|S_{w0}|。 -/
noncomputable def cB (K w n : ℕ) (χ : DirichletCharacter ℂ (p ^ (n + 1))) : ℂ :=
  χ (-1) * ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ))

/-- **定理 B = べき等元の単項**: B_cv(|w,χ⟩,|w,χ̄⟩) = χ(−1)(p^K/|S_{w0}|) ε_{w0}。 -/
theorem thmB_eps (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))
      = cB K w n χ • PAG.Part14.epsBall (Pavg (p := p) K) K (K - (n + 1) - w) := by
  rw [thmB_closed K w n hK χ hχ]
  show χ (-1) • cascade K w n = _
  rw [cascade_eps K w n hK, smul_smul, cB]

/-- **ε による選別**: H ⋆ ε_u = H（u = w0）、0（u ≠ w0）。 -/
theorem thmB_select (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (u : ℕ) (hu : u ≤ K) :
    conv (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
        (PAG.Part14.epsBall (Pavg (p := p) K) K u)
      = if u = K - (n + 1) - w then
          conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))
        else 0 := by
  rw [thmB_eps K w n hK χ hχ]
  have e := conv_smul_smul (cB K w n χ) 1 (PAG.Part14.epsBall (Pavg (p := p) K) K (K - (n + 1) - w))
    (PAG.Part14.epsBall (Pavg (p := p) K) K u)
  rw [one_smul, mul_one] at e
  rw [e, eps_conv K _ u (by omega) hu]
  by_cases h : u = K - (n + 1) - w
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h.symm), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm h)), ite_eq_right_of_eq_false _ _ (eq_false h), smul_zero]

theorem chi_neg_one_sq' {N : ℕ} (χ : DirichletCharacter ℂ N) : χ (-1) * χ (-1) = 1 :=
  PAG.Part9.chi_neg_one_sq χ

/-- **自己畳み込み（正しい形）**: H ⋆ H = χ(−1)(p^K/|S_{w0}|) · H。 -/
theorem thmB_self (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    conv (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
        (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
      = cB K w n χ • conv (ket K w (n + 1) hK χ)
          (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)) := by
  rw [thmB_eps K w n hK χ hχ, conv_smul_smul, eps_conv K _ _ (by omega) (by omega), ite_eq_left_of_eq_true _ _ (eq_true rfl), smul_smul]

/-- 自己畳み込みの χ によらない形: H ⋆ H = (p^K/|S_{w0}|)² ε_{w0}。 -/
theorem thmB_self_sq (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    conv (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
        (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
      = ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ)) ^ 2 •
          PAG.Part14.epsBall (Pavg (p := p) K) K (K - (n + 1) - w) := by
  rw [thmB_self K w n hK χ hχ, thmB_eps K w n hK χ hχ, smul_smul, cB]
  congr 1
  have := chi_neg_one_sq' χ
  linear_combination ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ)) ^ 2 * this

/-- 指示書の形 H ⋆ H = (p^K/|S_{w0}|) H は χ(−1) = 1（偶指標）のときに限り成り立つ。 -/
theorem thmB_self_even (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (heven : χ (-1) = 1) :
    conv (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
        (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
      = ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ)) •
          conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)) := by
  rw [thmB_self K w n hK χ hχ, cB, heven, one_mul]

/-- 奇指標（χ(−1) = −1）では H ⋆ H = −(p^K/|S_{w0}|) H（指示書の形は偽）。 -/
theorem thmB_self_odd (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (hodd : χ (-1) = -1) :
    conv (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
        (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
      = (-((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ))) •
          conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)) := by
  rw [thmB_self K w n hK χ hχ, cB, hodd, neg_one_mul]

variable (K : ℕ) (hK1 : 1 ≤ K)

/-- **定理 B（射影直線上、南）**: B_S^proj(|w,χ⟩,|w,χ̄⟩) = χ(−1)(p^K/|S_{w0}|) ε_{w0}^S。 -/
theorem thmB_BSproj (w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    BSproj K hK1 (ketS_proj K hK1 w (n + 1) h χ) (ketS_proj K hK1 w (n + 1) h χ⁻¹)
      = cB K w n χ • epsS_proj K hK1 (K - (n + 1) - w) := by
  apply (projFunEquiv K hK1).injective
  apply Subtype.ext
  simp only [LinearEquiv.map_smul, Submodule.coe_smul, projFun_BSproj, projFun_ketS, projFun_epsS]
  rw [thmB_south K w n h χ hχ, cascade_eps K w n h, extS_smul, smul_smul, cB]

/-- **鏡像定理 B（射影直線上、北）**: B_N^proj(|−w,χ⟩,|−w,χ̄⟩) = χ(−1)(p^K/|S_{w0}|) ε_{w0}^N。 -/
theorem mirror_thmB_BNproj (w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    BNproj K hK1 (ketN_proj K hK1 w (n + 1) h χ) (ketN_proj K hK1 w (n + 1) h χ⁻¹)
      = cB K w n χ • epsN_proj K hK1 (K - (n + 1) - w) := by
  apply (projFunEquiv K hK1).injective
  apply Subtype.ext
  simp only [LinearEquiv.map_smul, Submodule.coe_smul, projFun_BNproj, projFun_ketN, projFun_epsN]
  rw [mirror_thmB K w n h χ hχ, cascade_eps K w n h, extN_smul, smul_smul, cB]

end ThmBEps

end PAG.Part29

#print axioms PAG.Part29.ketS_proj
#print axioms PAG.Part29.ketN_proj
#print axioms PAG.Part29.epsS_proj
#print axioms PAG.Part29.epsN_proj
#print axioms PAG.Part29.BSproj_symm
#print axioms PAG.Part29.BNproj_symm
#print axioms PAG.Part29.symm_smul
#print axioms PAG.Part29.projFun_BSproj
#print axioms PAG.Part29.projFun_BNproj
#print axioms PAG.Part29.projFun_ketS
#print axioms PAG.Part29.projFun_ketN
#print axioms PAG.Part29.projFun_epsS
#print axioms PAG.Part29.projFun_epsN
#print axioms PAG.Part29.Wpull_ketS_proj
#print axioms PAG.Part29.ketS0_eq_ketN0_proj
#print axioms PAG.Part29.thmA_BSproj
#print axioms PAG.Part29.mirror_thmA_BNproj
#print axioms PAG.Part29.equator_intertwine_proj
#print axioms PAG.Part29.Hs
#print axioms PAG.Part29.mem_Hs
#print axioms PAG.Part29.indH_Hs
#print axioms PAG.Part29.cardH_Hs
#print axioms PAG.Part29.ballAvg_Hs
#print axioms PAG.Part29.Hs_mono
#print axioms PAG.Part29.Pavg_absorb
#print axioms PAG.Part29.epsBall_Pavg_eq
#print axioms PAG.Part29.eps_conv
#print axioms PAG.Part29.cB
#print axioms PAG.Part29.thmB_eps
#print axioms PAG.Part29.thmB_select
#print axioms PAG.Part29.chi_neg_one_sq'
#print axioms PAG.Part29.thmB_self
#print axioms PAG.Part29.thmB_self_sq
#print axioms PAG.Part29.thmB_self_even
#print axioms PAG.Part29.thmB_self_odd
#print axioms PAG.Part29.thmB_BSproj
#print axioms PAG.Part29.mirror_thmB_BNproj
