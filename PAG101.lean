/-
  PAG 2.0 Part 97（2026-10-19）— 2 次指標のスカラー: χ² = 1 なら U_k² = χ(−1)·id（V_a 上）
  任意の素数、k = |w, χ⟩（原始、双対殻 a）、χ * χ = 1 のとき
    t ∈ T_a ⇒ 𝓕k(t)² = χ(−1)·λ
  （Gauss 和の 2 乗の符号公式の、畳み込みの言葉による形）
-/
import PAG100

namespace PAG.Part101

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part95

variable {p : ℕ} [hp : Fact p.Prime]

theorem quad_scalar (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (hq : χ * χ = 1) (t : ZMod (p ^ K))
    (ht : t ∈ Tset (p := p) K (K - (n + 1) - w)) :
    𝓕 (ket K w (n + 1) h χ) t ^ 2 = χ (-1) * ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ)) := by
  have hinv : χ⁻¹ = χ := (eq_inv_of_mul_eq_one_left hq).symm
  have hB := PAG.Part29.thmB_eps K w n h χ hχ
  rw [hinv] at hB
  have e := congrArg (fun f => 𝓕 f t) hB
  simp only [PAG.Part16.dft_conv, Pi.mul_apply, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at e
  have h1 : 𝓕 (eps (p := p) K (K - (n + 1) - w)) t = 1 := by simpa [Tset] using ht
  rw [sq, e]
  unfold PAG.Part29.cB
  have h1' : 𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w)) t = 1 := h1
  rw [h1', mul_one]

end PAG.Part101

#print axioms PAG.Part101.quad_scalar
