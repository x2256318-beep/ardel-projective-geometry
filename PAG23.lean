/-
  PAG 2.0 Part 19（2026-10-18）— P¹(Z/p^K) の 2 チャートモデルと北チャートの鏡像定理
  P¹ 上の関数 = 南チャート座標 x（点 [x:1]）と北チャート座標 y（点 [1:y]）の関数の組 (F_S, F_N) で、
  赤道（単数）上で F_N(y) = F_S(y⁻¹) を満たすもの。反転 W は (F_S, F_N) ↦ (F_N, F_S)。
  南の畳み込み B_S と北の畳み込み B_N := W B_S(W·, W·)。
-/
import PAG22

namespace PAG.Part23

open ZMod Finset PAG.Part17 PAG.Part19 PAG.Part21

/-! ## 1. 2 チャートモデル -/

section Model

variable {N : ℕ}

/-- P¹ 上の関数（南座標の関数と北座標の関数の組）。 -/
abbrev P1F (N : ℕ) := (ZMod N → ℂ) × (ZMod N → ℂ)

/-- 貼り合わせ条件: 赤道（単数）上で F_N(y) = F_S(y⁻¹)。 -/
def Compat (F : P1F N) : Prop := ∀ y : ZMod N, IsUnit y → F.2 y = F.1 y⁻¹

/-- 反転 W: [x:1] ↔ [1:x]、関数では南北の入れ替え。 -/
def W (F : P1F N) : P1F N := (F.2, F.1)

theorem W_W (F : P1F N) : W (W F) = F := rfl

theorem inv_inv_of_unit {y : ZMod N} (hy : IsUnit y) : IsUnit y⁻¹ ∧ (y⁻¹)⁻¹ = y := by
  obtain ⟨u, rfl⟩ := hy
  rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit, inv_inv]
  exact ⟨Units.isUnit _, rfl⟩

/-- W は貼り合わせ条件を保つ。 -/
theorem compat_W {F : P1F N} (hF : Compat F) : Compat (W F) := by
  intro y hy
  obtain ⟨hy', hyy⟩ := inv_inv_of_unit hy
  simp only [W]
  rw [hF y⁻¹ hy', hyy]

open Classical in
/-- 南チャートの関数を P¹ 上へ（北の内部では 0）。 -/
noncomputable def extS (h : ZMod N → ℂ) : P1F N := (h, fun y => if IsUnit y then h y⁻¹ else 0)

open Classical in
/-- 北チャートの関数を P¹ 上へ（南の内部では 0）。 -/
noncomputable def extN (h : ZMod N → ℂ) : P1F N := (fun x => if IsUnit x then h x⁻¹ else 0, h)

theorem compat_extS (h : ZMod N → ℂ) : Compat (extS h) := fun y hy => by simp [extS, hy]

theorem compat_extN (h : ZMod N → ℂ) : Compat (extN h) := fun y hy => by
  obtain ⟨hy', hyy⟩ := inv_inv_of_unit hy
  simp [extN, hy', hyy]

theorem W_extS (h : ZMod N → ℂ) : W (extS h) = extN h := rfl

theorem extS_smul (a : ℂ) (h : ZMod N → ℂ) : extS (a • h) = a • extS h := by
  ext y <;> simp [extS]

theorem extN_smul (a : ℂ) (h : ZMod N → ℂ) : extN (a • h) = a • extN h := by
  ext y <;> simp [extN]

variable [Fintype (ZMod N)]

/-- 南の畳み込み（南チャートで畳み込み、北の内部は 0）。 -/
noncomputable def BS (F G : P1F N) : P1F N := extS (PAG.Part15.conv F.1 G.1)

/-- 北の畳み込み B_N := W B_S(W·, W·)。 -/
noncomputable def BN (F G : P1F N) : P1F N := W (BS (W F) (W G))

/-- B_N は北チャートでの畳み込み。 -/
theorem BN_eq (F G : P1F N) : BN F G = extN (PAG.Part15.conv F.2 G.2) := rfl

end Model

/-! ## 2. 殻ケットと鏡像定理 -/

section Mirror

variable {p : ℕ} [hp : Fact p.Prime]

/-- 南の殻ケット |w, χ⟩（w ≥ 0）。 -/
noncomputable def kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) : P1F (p ^ K) :=
  extS (ket K w c h χ)

/-- 北の殻ケット |−w, χ⟩: 北座標 y = p^w u で値 χ(u⁻¹)（step30 の規約）。 -/
noncomputable def kN (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) : P1F (p ^ K) :=
  extN (ket K w c h ((χ⁻¹ : DirichletCharacter ℂ (p ^ c)) : ZMod (p ^ c) → ℂ))

/-- **W|w, χ⟩ = |−w, χ̄⟩**。 -/
theorem W_kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    W (kS K w c h χ) = kN K w c h χ⁻¹ := by
  rw [kS, W_extS, kN, inv_inv]

/-- 共役指標の J̃: J̃(χ₁⁻¹, χ₂⁻¹; ψ⁻¹) = conj J̃(χ₁, χ₂; ψ)。 -/
theorem Jt_inv (n v : ℕ) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v)))
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    gaussSum χ₁⁻¹ stdAddChar * gaussSum χ₂⁻¹ stdAddChar /
        (gaussSum ψ⁻¹ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))
      = starRingEnd ℂ (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
        (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))) := by
  have hinv : ∀ {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M),
      gaussSum χ⁻¹ stdAddChar = χ (-1) * starRingEnd ℂ (gaussSum χ stdAddChar) := by
    intro M _ χ
    rw [PAG.Part9.conj_gaussSum, ← mul_assoc, PAG.Part9.chi_neg_one_sq, one_mul]
  have : NeZero (p ^ (n + 1 - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hψ : ψ (-1) = χ₁ (-1) * χ₂ (-1) := by
    have h0 := hprod (-1)
    have hπ : ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) (ZMod (p ^ (n + 1 - v))) (-1) = -1 := by
      rw [map_neg, map_one]
    rw [hπ, MulChar.coeToFun_mul, Pi.mul_apply] at h0
    exact h0.symm
  rw [hinv χ₁, hinv χ₂, hinv ψ, hψ, map_div₀, map_mul, map_mul, Complex.conj_ofReal]
  have h1 := PAG.Part9.chi_neg_one_sq χ₁
  have h2 := PAG.Part9.chi_neg_one_sq χ₂
  have hne1 : χ₁ (-1) ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
  have hne2 : χ₂ (-1) ≠ 0 := fun h => by rw [h, zero_mul] at h2; exact zero_ne_one h2
  rw [show χ₁ (-1) * starRingEnd ℂ (gaussSum χ₁ stdAddChar) * (χ₂ (-1) * starRingEnd ℂ (gaussSum χ₂ stdAddChar))
      = (χ₁ (-1) * χ₂ (-1)) * (starRingEnd ℂ (gaussSum χ₁ stdAddChar) * starRingEnd ℂ (gaussSum χ₂ stdAddChar)) by ring,
    mul_assoc (χ₁ (-1) * χ₂ (-1)), mul_div_mul_left _ _ (mul_ne_zero hne1 hne2)]

/-- **鏡像定理 A（北チャート）**: B_N(|−w,χ₁⟩, |−w,χ₂⟩) = √(p^K/|S_{w0}|)·conj(J̃)·|−(w+v), ψ⟩。 -/
theorem mirror_thmA (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    BN (kN K w (n + 1) hK χ₁) (kN K w (n + 1) hK χ₂)
      = ((Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) : ℝ) *
          starRingEnd ℂ (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
            (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))) : ℂ) •
        kN K (w + v) (n + 1 - v) (by omega) ψ := by
  have hprod' : ∀ x, (χ₁⁻¹ * χ₂⁻¹) x = ψ⁻¹ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x) := by
    intro x
    rw [← mul_inv, PAG.Part18.inv_pullback (χ₁ * χ₂) ψ _ hprod]
  have h := thmA_ket K w n v hv hK χ₁⁻¹ χ₂⁻¹ (PAG.Part16.isPrimitive_inv h₁) (PAG.Part16.isPrimitive_inv h₂)
    ψ⁻¹ (PAG.Part16.isPrimitive_inv hψ) hprod'
  rw [Jt_inv n v χ₁ χ₂ ψ hprod] at h
  rw [BN_eq, kN, kN, kN]
  show extN (PAG.Part15.conv (ket K w (n + 1) hK ((χ₁⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))
    (ket K w (n + 1) hK ((χ₂⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))) = _
  rw [h, extN_smul]

end Mirror

end PAG.Part23

#print axioms PAG.Part23.W_W
#print axioms PAG.Part23.inv_inv_of_unit
#print axioms PAG.Part23.compat_W
#print axioms PAG.Part23.compat_extS
#print axioms PAG.Part23.compat_extN
#print axioms PAG.Part23.W_extS
#print axioms PAG.Part23.extS_smul
#print axioms PAG.Part23.extN_smul
#print axioms PAG.Part23.BN_eq
#print axioms PAG.Part23.W_kS
#print axioms PAG.Part23.Jt_inv
#print axioms PAG.Part23.mirror_thmA
