/-
  PAG 2.0 Part 100（2026-10-19）— 構造定理（Part 85–99 の総括を一つの定理に）
  任意の素数 p、原始ケット k = |w, χ⟩（双対殻 a = K − (n+1) − w）、λ = p^K/|S_a| について
  (1) V_a = span B_a（ε_a ⋆ f = f ⟺ f ∈ span B_a）
  (2) finrank V_a = |S_a|
  (3) V_a 上で ‖k ⋆ f‖² = λ‖f‖²
  (4) ε_a ⋆ f = 0 なら k ⋆ f = 0
  (5) U_k^(m+1) がスカラー ⟺ χ^(m+1) = 1（T_a 上で 𝓕k^(m+1) が定数 ⟺ χ^(m+1) = 1）
  (6) 固有値は 𝓕k(t₀)·μ_{ord χ} に一様分布（各根 |T_a|/ord χ 回）
-/
import PAG103

namespace PAG.Part104

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part93 PAG.Part95
  PAG.Part97 PAG.Part98

variable {p : ℕ} [hp : Fact p.Prime]

/-- **構造定理**。 -/
theorem structure_theorem (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) :
    let a := K - (n + 1) - w
    let k := ket K w (n + 1) h χ
    let lam : ℝ := (p : ℝ) ^ K / (sz p K a : ℝ)
    (∀ f, conv (eps (p := p) K a) f = f ↔ f ∈ Submodule.span ℂ (Bset (p := p) K a)) ∧
    Module.finrank ℂ (Va (p := p) K a) = sz p K a ∧
    (∀ f, conv (eps (p := p) K a) f = f → ∑ x, Complex.normSq (conv k f x) = lam * ∑ x, Complex.normSq (f x)) ∧
    (∀ f, conv (eps (p := p) K a) f = 0 → conv k f = 0) ∧
    (∀ m : ℕ, χ ^ (m + 1) = 1 ↔
      ∀ t ∈ Tset (p := p) K a, ∀ t' ∈ Tset (p := p) K a, 𝓕 k t ^ (m + 1) = 𝓕 k t' ^ (m + 1)) ∧
    (∀ t₀ ∈ Tset (p := p) K a, ∀ ξ : ℂ, ξ ^ orderOf χ = 1 →
      (orderOf χ : ℂ) * (((Tset (p := p) K a).filter (fun t => 𝓕 k t = 𝓕 k t₀ * ξ)).card : ℂ)
        = ((Tset (p := p) K a).card : ℂ)) := by
  intro a k lam
  have hkd : KetDual (p := p) K a k := ⟨w, n, h, χ, hχ, rfl, rfl⟩
  refine ⟨fun f => Va_eq_span K a (by omega) f, ?_, fun f hf => norm_conv_eq_of_mem K w n h χ hχ f hf,
    fun f hf => conv_eq_zero_of_perp K w n h χ hχ f hf, fun m => ⟨fun ho t ht t' ht' =>
      pow_eigen_const K w (n + 1) h (by omega) χ hχ m ho t t' ht ht', fun H => ?_⟩,
    fun t₀ ht₀ ξ hξ => PAG.Part103.eigen_multiplicity K w n h χ hχ t₀ ht₀ ξ hξ⟩
  · rw [finrank_Va K a (by omega), card_Tset K a k hkd]
  · by_contra hne
    obtain ⟨t, ht, t', ht', hneq⟩ := PAG.Part99.pow_eigen_nonconst K w n h χ hχ m hne
    exact hneq (H t ht t' ht')

end PAG.Part104

#print axioms PAG.Part104.structure_theorem
