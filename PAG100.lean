/-
  PAG 2.0 Part 96（2026-10-19）— 巡回の長さはちょうど ord χ
  k = |w, χ⟩（原始、双対殻 a）、b ∈ B_a（双対殻 a の原始ケット、または ε_a）について
    T_k^(m+1) b = c·b（c ≠ 0）⇒ χ^(m+1) = 1
  証明: T_k^(m+1) b = k^{⋆(m+1)} ⋆ b は χ^(m+1)·β 同変（β は b の同変指標）。
        c·b は β 同変で 0 でないので、単数上で χ^(m+1) = 1。
  系（PAG92・PAG98 と合わせて）: π_k の各巡回の長さは ord χ（U_k^{ord χ} b ∝ b、かつ m < ord χ では ∝ でない）
-/
import PAG99

namespace PAG.Part100

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part93 PAG.Part98

variable {p : ℕ} [hp : Fact p.Prime]

/-- 同変性の比較: F が α 同変、F = c·b（c ≠ 0, b ≠ 0）、b が β 同変 ⇒ 単数上で α = β（β ≠ 0 のとき）。 -/
theorem equivariant_compare (K : ℕ) (α β : (ZMod (p ^ K))ˣ → ℂ) (F b : ZMod (p ^ K) → ℂ)
    (hF : Equivariant (p := p) K α F) (hb : Equivariant (p := p) K β b) (c : ℂ) (hc : c ≠ 0)
    (he : F = c • b) (hb0 : b ≠ 0) (u : (ZMod (p ^ K))ˣ) : α u = β u := by
  obtain ⟨x, hx⟩ : ∃ x, b x ≠ 0 := by
    by_contra H; push Not at H; exact hb0 (funext H)
  have e1 := hF u x
  rw [he, Pi.smul_apply, Pi.smul_apply, hb, smul_eq_mul, smul_eq_mul] at e1
  have : c * b x ≠ 0 := mul_ne_zero hc hx
  have e2 : (β u - α u) * (c * b x) = 0 := by linear_combination e1
  exact (sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right this)).symm

/-- 単数上で自明な指標は自明。 -/
theorem char_eq_one_of_units (K n : ℕ) (h : n + 1 ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n + 1)))
    (H : ∀ u : (ZMod (p ^ K))ˣ, ψ (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ (n + 1))) u) = 1) : ψ = 1 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  apply MulChar.ext
  intro v
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (pow_dvd_pow p h) v
  have hcu : ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ (n + 1))) (u : ZMod (p ^ K)) = v := by
    have e := congrArg (fun z : (ZMod (p ^ (n + 1)))ˣ => (z : ZMod (p ^ (n + 1)))) hu
    simp only [ZMod.unitsMap_val] at e
    rw [ZMod.castHom_apply, e]
  rw [← hcu, H u, MulChar.one_apply ((Units.isUnit u).map _)]

/-- **巡回の長さの下界（ケットの元）**: T_k^(m+1) k' = c·k'（c ≠ 0）⇒ χ^(m+1) = 1。 -/
theorem cycle_ket (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (w' n' : ℕ) (h' : w' + (n' + 1) ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n' + 1))) (hψ : ψ.IsPrimitive)
    (m : ℕ) (c : ℂ) (hc : c ≠ 0)
    (he : conv (prodConv (ket K w (n + 1) h χ) (List.replicate m (ket K w (n + 1) h χ))) (ket K w' (n' + 1) h' ψ)
      = c • ket K w' (n' + 1) h' ψ) :
    χ ^ (m + 1) = 1 := by
  have hk := ket_equivariant K w (n + 1) h χ
  have hP := prodConv_equivariant K _ _ hk m
  have hb := ket_equivariant K w' (n' + 1) h' ψ
  have hF := conv_equivariant K _ _ _ _ hP hb
  have hb0 : ket K w' (n' + 1) h' ψ ≠ 0 := by
    intro h0
    have := PAG.Part39.norm_ket K w' n' h' ψ hψ
    rw [h0] at this; simp at this
  apply char_eq_one_of_units K n (by omega)
  intro u
  have e := equivariant_compare K _ _ _ _ hF hb c hc he hb0 u
  have hψu : ψ (ZMod.castHom (pow_dvd_pow p (by omega : n' + 1 ≤ K)) (ZMod (p ^ (n' + 1))) u) ≠ 0 :=
    ((Units.isUnit u).map _).map ψ |>.ne_zero
  have e2 : χ (ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ K)) (ZMod (p ^ (n + 1))) u) ^ (m + 1) = 1 := by
    have := mul_right_cancel₀ hψu (e.trans (one_mul _).symm)
    exact this
  rw [MulChar.pow_apply' χ (by omega : m + 1 ≠ 0)]
  exact e2

/-- **巡回の長さの下界（ε の元）**: T_k^(m+1) ε_a = c·ε_a（c ≠ 0）⇒ χ^(m+1) = 1。 -/
theorem cycle_eps (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (m : ℕ) (c : ℂ) (hc : c ≠ 0)
    (he : conv (prodConv (ket K w (n + 1) h χ) (List.replicate m (ket K w (n + 1) h χ)))
      (eps (p := p) K (K - (n + 1) - w)) = c • eps (p := p) K (K - (n + 1) - w)) :
    χ ^ (m + 1) = 1 := by
  have hk := ket_equivariant K w (n + 1) h χ
  have hP := prodConv_equivariant K _ _ hk m
  have hb : Equivariant (p := p) K (fun _ => 1) (eps (p := p) K (K - (n + 1) - w)) := by
    intro u x; rw [PAG.Part99.eps_invariant K w n h χ hχ u x, one_mul]
  have hF := conv_equivariant K _ _ _ _ hP hb
  apply char_eq_one_of_units K n (by omega)
  intro u
  have e := equivariant_compare K _ _ _ _ hF hb c hc he (eps_ne_zero K _) u
  simp only [mul_one] at e
  rw [MulChar.pow_apply' χ (by omega : m + 1 ≠ 0)]
  exact e

end PAG.Part100

#print axioms PAG.Part100.equivariant_compare
#print axioms PAG.Part100.char_eq_one_of_units
#print axioms PAG.Part100.cycle_ket
#print axioms PAG.Part100.cycle_eps
