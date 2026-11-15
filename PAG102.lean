/-
  PAG 2.0 Part 98（2026-10-19）— 冪のトレースの消滅: ord χ ∤ m なら tr U_k^m = 0
  任意の素数、k = |w, χ⟩（原始、双対殻 a）について
  1. χ^(m+1) ≠ 1 なら (k^{⋆(m+1)})(0) = 0（同変性: F(0) = F(u·0) = χ^(m+1)(u) F(0)）
  2. 系: χ^(m+1) ≠ 1 なら Σ_{t∈T_a} 𝓕k(t)^(m+1) = 0（tr T_k^(m+1) = 0）
  3. χ^(m+1) = 1 なら Σ_{t∈T_a} 𝓕k(t)^(m+1) = #T_a · 𝓕k(t₀)^(m+1)（任意の t₀ ∈ T_a）
  すなわち U_k の固有値の冪和は ord χ の倍数でのみ消えず、そこでは |S_a|·ζ^{m/ord χ}
-/
import PAG101

namespace PAG.Part102

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part90 PAG.Part95 PAG.Part97 PAG.Part98

variable {p : ℕ} [hp : Fact p.Prime]

/-- **原点での値の消滅**。 -/
theorem prodConv_zero_vanish (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (m : ℕ) (hne : χ ^ (m + 1) ≠ 1) :
    prodConv (ket K w (n + 1) h χ) (List.replicate m (ket K w (n + 1) h χ)) 0 = 0 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨v, hv⟩ : ∃ v : (ZMod (p ^ (n + 1)))ˣ, (χ ^ (m + 1)) v ≠ 1 := by
    by_contra H2; push Not at H2
    exact hne (MulChar.ext (fun v => by rw [H2 v, MulChar.one_apply_coe]))
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (pow_dvd_pow p (by omega : n + 1 ≤ K)) v
  have hcu : ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ K)) (ZMod (p ^ (n + 1))) (u : ZMod (p ^ K)) = v := by
    have e := congrArg (fun z : (ZMod (p ^ (n + 1)))ˣ => (z : ZMod (p ^ (n + 1)))) hu
    simp only [ZMod.unitsMap_val] at e
    rw [ZMod.castHom_apply, e]
  have e1 := prodConv_equivariant K _ _ (ket_equivariant K w (n + 1) h χ) m u 0
  simp only [mul_zero] at e1
  rw [hcu, ← MulChar.pow_apply' χ (by omega : m + 1 ≠ 0)] at e1
  have e3 : ((χ ^ (m + 1)) v - 1) * prodConv (ket K w (n + 1) h χ) (List.replicate m (ket K w (n + 1) h χ)) 0 = 0 := by
    linear_combination -e1
  exact (mul_eq_zero.mp e3).resolve_left (sub_ne_zero.mpr hv)

/-- **冪のトレースの消滅**: χ^(m+1) ≠ 1 なら Σ_{t∈T_a} 𝓕k(t)^(m+1) = 0。 -/
theorem trace_pow_vanish (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (m : ℕ) (hne : χ ^ (m + 1) ≠ 1) :
    ∑ t ∈ Tset (p := p) K (K - (n + 1) - w), 𝓕 (ket K w (n + 1) h χ) t ^ (m + 1) = 0 := by
  rw [trace_pow K _ _ ⟨w, n, h, χ, hχ, rfl, rfl⟩ m, prodConv_zero_vanish K w n h χ m hne, mul_zero]

/-- **χ^(m+1) = 1 の場合**: 冪和は #T_a 倍の定数。 -/
theorem trace_pow_const (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (m : ℕ) (ho : χ ^ (m + 1) = 1) (t₀ : ZMod (p ^ K))
    (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w)) :
    ∑ t ∈ Tset (p := p) K (K - (n + 1) - w), 𝓕 (ket K w (n + 1) h χ) t ^ (m + 1)
      = ((Tset (p := p) K (K - (n + 1) - w)).card : ℂ) * 𝓕 (ket K w (n + 1) h χ) t₀ ^ (m + 1) := by
  rw [Finset.sum_congr rfl (fun t ht => pow_eigen_const K w (n + 1) h (by omega) χ hχ m ho t t₀ ht ht₀),
    Finset.sum_const, nsmul_eq_mul]

end PAG.Part102

#print axioms PAG.Part102.prodConv_zero_vanish
#print axioms PAG.Part102.trace_pow_vanish
#print axioms PAG.Part102.trace_pow_const
