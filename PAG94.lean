/-
  PAG 2.0 Part 90（2026-10-19）— 全空間の直交分解 L²(ℤ/p^K) = ⊕_{a=0}^{K} V_a
  任意の素数で
  1. Σ_{a=0}^{K} ε_a = δ₀（単位の分解）
  2. f = Σ_a ε_a ⋆ f、各成分は V_a に入る
  3. a ≠ b なら ⟨ε_a ⋆ f, ε_b ⋆ g⟩ = 0（直交性）
  4. ‖f‖² = Σ_a ‖ε_a ⋆ f‖²（Pythagoras）
-/
import PAG93

namespace PAG.Part94

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part52 PAG.Part58 PAG.Part59 PAG.Part93

variable {p : ℕ} [hp : Fact p.Prime]

/-- **単位の分解**: Σ_{a ≤ K} ε_a = δ₀。 -/
theorem sum_eps (K : ℕ) : ∑ a ∈ range (K + 1), eps (p := p) K a = Pi.single (0 : ZMod (p ^ K)) (1 : ℂ) := by
  have h := Pavg_eq_sum_eps (p := p) K 0 (Nat.zero_le _)
  rw [delta_eq_ball, ← Nat.Ico_zero_eq_range, ← h]
  unfold PAG.Part28.Pavg
  rw [pow_zero, inv_one, one_smul, Nat.sub_zero]

/-- **分解**: f = Σ_a ε_a ⋆ f。 -/
theorem decomp (K : ℕ) (f : ZMod (p ^ K) → ℂ) : f = ∑ a ∈ range (K + 1), conv (eps (p := p) K a) f := by
  have e : conv (∑ a ∈ range (K + 1), eps (p := p) K a) f = f := by
    rw [sum_eps, PAG.Part57.conv_delta]
  calc f = conv (∑ a ∈ range (K + 1), eps (p := p) K a) f := e.symm
    _ = ∑ a ∈ range (K + 1), conv (eps (p := p) K a) f := by
      rw [show conv (∑ a ∈ range (K + 1), eps (p := p) K a) f = conv f (∑ a ∈ range (K + 1), eps (p := p) K a)
        from conv_comm _ _, conv_sum_right]
      simp_rw [conv_comm f]

/-- 各成分は V_a に入る。 -/
theorem comp_mem (K a : ℕ) (ha : a ≤ K) (f : ZMod (p ^ K) → ℂ) :
    conv (eps (p := p) K a) (conv (eps (p := p) K a) f) = conv (eps (p := p) K a) f := by
  rw [← PAG.Part89.conv_assoc', eps_conv_eps K a a ha ha, ite_eq_left_of_eq_true _ _ (eq_true rfl)]

/-- **直交性**: a ≠ b なら ⟨ε_a ⋆ f, ε_b ⋆ g⟩ = 0。 -/
theorem comp_orth (K a b : ℕ) (ha : a ≤ K) (hb : b ≤ K) (hab : a ≠ b) (f g : ZMod (p ^ K) → ℂ) :
    ip (conv (eps (p := p) K a) f) (conv (eps (p := p) K b) g) = 0 := by
  have hP := PAG.Part39.plancherel (conv (eps (p := p) K a) f) (conv (eps (p := p) K b) g)
  have hz : ∀ t, starRingEnd ℂ (𝓕 (conv (eps (p := p) K a) f) t) * 𝓕 (conv (eps (p := p) K b) g) t = 0 := by
    intro t
    rw [PAG.Part16.dft_conv, PAG.Part16.dft_conv, Pi.mul_apply, Pi.mul_apply]
    rcases PAG.Part31.dft_eps_zero_or_one (p := p) K a ha t with h0 | h1
    · rw [h0, zero_mul, map_zero, zero_mul]
    · have e := PAG.Part41.dft_eps_mul_eq_zero (p := p) K a b ha hb hab t
      rw [h1, one_mul] at e
      rw [e, zero_mul, mul_zero]
  simp only [hz, Finset.sum_const_zero] at hP
  have hN : ((p ^ K : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  exact (mul_eq_zero.mp hP.symm).resolve_left hN

/-- **Pythagoras**: ⟨f, f⟩ = Σ_a ⟨ε_a ⋆ f, ε_a ⋆ f⟩。 -/
theorem pythagoras (K : ℕ) (f : ZMod (p ^ K) → ℂ) :
    ip f f = ∑ a ∈ range (K + 1), ip (conv (eps (p := p) K a) f) (conv (eps (p := p) K a) f) := by
  have hd := decomp (p := p) K f
  conv_lhs => rw [hd]
  have hL : ∀ (s : Finset ℕ) (u : ℕ → ZMod (p ^ K) → ℂ) (g : ZMod (p ^ K) → ℂ),
      ip (∑ i ∈ s, u i) g = ∑ i ∈ s, ip (u i) g := by
    intro s u g
    unfold ip
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_apply, map_sum, Finset.sum_mul]
  have hR : ∀ (s : Finset ℕ) (u : ℕ → ZMod (p ^ K) → ℂ) (g : ZMod (p ^ K) → ℂ),
      ip g (∑ i ∈ s, u i) = ∑ i ∈ s, ip g (u i) := by
    intro s u g
    unfold ip
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_apply, Finset.mul_sum]
  rw [hL]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [hR, Finset.sum_eq_single a]
  · intro b hb hba
    exact comp_orth K a b (by have := mem_range.mp ha; omega) (by have := mem_range.mp hb; omega)
      (Ne.symm hba) f f
  · intro h; exact absurd ha h

end PAG.Part94

#print axioms PAG.Part94.sum_eps
#print axioms PAG.Part94.decomp
#print axioms PAG.Part94.comp_mem
#print axioms PAG.Part94.comp_orth
#print axioms PAG.Part94.pythagoras
