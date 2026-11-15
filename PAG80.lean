/-
  PAG 2.0 Part 76（2026-10-19）— k₁ ⋆ g の展開での 1_{S_v}・δ₀ 成分
  1. 1_{S_v} は tilde で不変（実数値かつ偶）
  2. 畳み込みの結合・交換: (f ⋆ g) ⋆ h = (f ⋆ h) ⋆ g
  3. ⟨1_{S_v}, k₁ ⋆ g⟩ = μ_v·(k₁ ⋆ g)(0) = μ_v·⟨δ₀, k₁ ⋆ g⟩、
     μ_v = [w+c ≤ v]·p^(K−v) − [w+c ≤ v+1]·p^(K−v−1)（PAG58 の固有値）
  4. 系: v + 1 < w + c なら ⟨1_{S_v}, k₁ ⋆ g⟩ = 0
-/
import PAG79

namespace PAG.Part80

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part52 PAG.Part54 PAG.Part55 PAG.Part58

variable {p : ℕ} [hp : Fact p.Prime]

theorem tilde_ball (K j : ℕ) (hj : j ≤ K) : tilde (PAG.Part22.ball (p := p) K j) = PAG.Part22.ball (p := p) K j := by
  funext x
  simp only [tilde]
  rw [PAG.Part31.ball_neg K j hj x]
  unfold PAG.Part22.ball
  split_ifs <;> simp

theorem tilde_shellInd (K v : ℕ) (hv : v < K) : tilde (shellInd (p := p) K v hv) = shellInd (p := p) K v hv := by
  rw [shellInd_eq_ball_sub K v hv, PAG.Part31.tilde_sub, tilde_ball K v hv.le, tilde_ball K (v + 1) hv]

theorem conv_right_comm {N : ℕ} [NeZero N] (f g h : ZMod N → ℂ) : conv (conv f g) h = conv (conv f h) g := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv, PAG.Part16.dft_conv, PAG.Part16.dft_conv, PAG.Part16.dft_conv]
  ring

/-- 1_{S_v} に対する k の固有値。 -/
noncomputable def mu (K w c v : ℕ) : ℂ :=
  (if w + c ≤ v then (p : ℂ) ^ (K - v) else 0) - (if w + c ≤ v + 1 then (p : ℂ) ^ (K - (v + 1)) else 0)

/-- **1_{S_v} 成分は δ₀ 成分の μ_v 倍**。 -/
theorem ip_shellInd_conv (K w n v : ℕ) (hK : w + (n + 1) ≤ K) (hv : v < K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (g : ZMod (p ^ K) → ℂ) :
    ip (shellInd (p := p) K v hv) (conv (ket K w (n + 1) hK χ) g)
      = mu (p := p) K w (n + 1) v * conv (ket K w (n + 1) hK χ) g 0 := by
  rw [ip_eq_conv, tilde_shellInd, conv_right_comm, ket_conv_shellInd K w n v hK hv χ hχ, conv_comm,
    PAG.Part52.conv_smul_right, conv_comm, Pi.smul_apply, smul_eq_mul]
  rfl

/-- δ₀ 成分は原点での値。 -/
theorem ip_delta_conv (K : ℕ) (F : ZMod (p ^ K) → ℂ) : ip (Pi.single (0 : ZMod (p ^ K)) (1 : ℂ)) F = F 0 :=
  ip_delta F

/-- **系**: v + 1 < w + c なら 1_{S_v} 成分は 0。 -/
theorem ip_shellInd_conv_low (K w n v : ℕ) (hK : w + (n + 1) ≤ K) (hv : v < K) (hlow : v + 1 < w + (n + 1))
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (g : ZMod (p ^ K) → ℂ) :
    ip (shellInd (p := p) K v hv) (conv (ket K w (n + 1) hK χ) g) = 0 := by
  rw [ip_shellInd_conv K w n v hK hv χ hχ g]
  unfold mu
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    sub_zero, zero_mul]

/-- **系**: (k₁ ⋆ g)(0) = 0 なら、1_{S_v}・δ₀ 成分はすべて 0（像は原始ケットの張る空間に入る）。 -/
theorem ip_ind_conv_zero (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (g : ZMod (p ^ K) → ℂ)
    (h0 : conv (ket K w (n + 1) hK χ) g 0 = 0) :
    ip (Pi.single (0 : ZMod (p ^ K)) (1 : ℂ)) (conv (ket K w (n + 1) hK χ) g) = 0 ∧
    ∀ v (hv : v < K), ip (shellInd (p := p) K v hv) (conv (ket K w (n + 1) hK χ) g) = 0 := by
  refine ⟨by rw [ip_delta_conv, h0], fun v hv => ?_⟩
  rw [ip_shellInd_conv K w n v hK hv χ hχ g, h0, mul_zero]

end PAG.Part80

#print axioms PAG.Part80.tilde_ball
#print axioms PAG.Part80.tilde_shellInd
#print axioms PAG.Part80.conv_right_comm
#print axioms PAG.Part80.ip_shellInd_conv
#print axioms PAG.Part80.ip_delta_conv
#print axioms PAG.Part80.ip_shellInd_conv_low
#print axioms PAG.Part80.ip_ind_conv_zero
