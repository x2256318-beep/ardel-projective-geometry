/-
  PAG 2.0 Part 55（2026-10-19）— IndSpan は ε_0, …, ε_K を基底とする K+1 次元の可換な畳み込み部分代数
  1. IndSpan = span{ε_b : b ≤ K}
  2. IndSpan は畳み込みで閉じる（ε_a ⋆ ε_b = δ_ab ε_a）
  3. ε_0, …, ε_K は一次独立、dim IndSpan = K+1
  4. 原始ケットは IndSpan 全体の同時固有ベクトル: f ∈ IndSpan ⇒ k ⋆ f ∈ ℂ·k
-/
import PAG58

namespace PAG.Part59

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part54 PAG.Part55 PAG.Part57 PAG.Part58

variable {p : ℕ} [hp : Fact p.Prime]

/-- ε_b（b ≤ K）。 -/
noncomputable abbrev eps (K b : ℕ) : ZMod (p ^ K) → ℂ := PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K b

/-- ε の張る空間。 -/
noncomputable def EpsSpan (K : ℕ) : Submodule ℂ (ZMod (p ^ K) → ℂ) :=
  Submodule.span ℂ (Set.range (fun b : Fin (K + 1) => eps (p := p) K b))

theorem Pavg_mem_IndSpan (K u : ℕ) : PAG.Part28.Pavg (p := p) K u ∈ IndSpan (p := p) K :=
  Submodule.smul_mem _ _ (ball_mem K _)

theorem eps_mem_IndSpan (K b : ℕ) : eps (p := p) K b ∈ IndSpan (p := p) K := by
  unfold eps PAG.Part14.epsBall
  split_ifs with h
  · exact Submodule.sub_mem _ (Pavg_mem_IndSpan K b) (Pavg_mem_IndSpan K (b + 1))
  · exact Pavg_mem_IndSpan K K

omit hp in
theorem Pavg_mem_EpsSpan (K u : ℕ) (hu : u ≤ K) : PAG.Part28.Pavg (p := p) K u ∈ EpsSpan (p := p) K := by
  rw [Pavg_eq_sum_eps K u hu]
  refine Submodule.sum_mem _ (fun b hb => Submodule.subset_span ⟨⟨b, by have := (mem_Ico.mp hb).2; omega⟩, rfl⟩)

theorem ball_mem_EpsSpan (K j : ℕ) (hj : j ≤ K) : PAG.Part22.ball (p := p) K j ∈ EpsSpan (p := p) K := by
  rw [ball_eq_Pavg K j hj]
  exact Submodule.smul_mem _ _ (Pavg_mem_EpsSpan K _ (by omega))

theorem delta_eq_ball (K : ℕ) : (Pi.single (0 : ZMod (p ^ K)) (1 : ℂ)) = PAG.Part22.ball (p := p) K K := by
  rw [ball_decomp K K]
  have : shellSum (p := p) K K = 0 := by
    unfold shellSum
    refine Finset.sum_eq_zero (fun w _ => ?_)
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := w.2; omega))]
  rw [this, zero_add]

/-- **IndSpan = span{ε_b}**。 -/
theorem IndSpan_eq_EpsSpan (K : ℕ) : IndSpan (p := p) K = EpsSpan (p := p) K := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f (⟨w, hw, rfl⟩ | rfl)
    · rw [SetLike.mem_coe, shellInd_eq_ball_sub K w hw]
      exact Submodule.sub_mem _ (ball_mem_EpsSpan K w hw.le) (ball_mem_EpsSpan K (w + 1) hw)
    · rw [SetLike.mem_coe, delta_eq_ball]; exact ball_mem_EpsSpan K K le_rfl
  · apply Submodule.span_le.mpr
    rintro f ⟨b, rfl⟩
    exact eps_mem_IndSpan K b

theorem eps_conv_eps (K a b : ℕ) (ha : a ≤ K) (hb : b ≤ K) :
    conv (eps (p := p) K a) (eps (p := p) K b) = if a = b then eps (p := p) K a else 0 :=
  PAG.Part29.eps_conv K a b ha hb

/-- **IndSpan は畳み込みで閉じる**。 -/
theorem conv_mem_IndSpan (K : ℕ) (f g : ZMod (p ^ K) → ℂ) (hf : f ∈ IndSpan (p := p) K)
    (hg : g ∈ IndSpan (p := p) K) : conv f g ∈ IndSpan (p := p) K := by
  rw [IndSpan_eq_EpsSpan] at hf hg ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [eps_conv_eps K a b (by have := a.2; omega) (by have := b.2; omega)]
      split_ifs
      · exact Submodule.subset_span ⟨a, rfl⟩
      · exact Submodule.zero_mem _
    | zero => rw [← convL_apply, map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [← convL_apply, map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [← convL_apply, _root_.map_smul]; exact Submodule.smul_mem _ _ hy
  | zero => rw [← convL_apply, map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [← convL_apply, map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [← convL_apply, _root_.map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ hx

/-- ε_b(0) ≠ 0、とくに ε_b ≠ 0。 -/
theorem eps_ne_zero (K b : ℕ) : eps (p := p) K b ≠ 0 := by
  intro h
  have e := congrFun h 0
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold eps PAG.Part14.epsBall PAG.Part28.Pavg at e
  split_ifs at e with hlt
  · simp only [Pi.sub_apply, Pi.smul_apply, PAG.Part49.ball_apply_zero, smul_eq_mul, mul_one, Pi.zero_apply] at e
    rw [sub_eq_zero, pow_succ, mul_inv] at e
    have : ((p : ℂ) ^ b)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hp0)
    have h2 : (p : ℂ)⁻¹ = 1 := by
      have := mul_left_cancel₀ this (e.symm.trans (mul_one _).symm)
      exact this
    have : (p : ℂ) = 1 := by rw [← inv_inv (p : ℂ), h2, inv_one]
    exact absurd this (by exact_mod_cast hp.out.one_lt.ne')
  · simp only [Pi.smul_apply, PAG.Part49.ball_apply_zero, smul_eq_mul, mul_one, Pi.zero_apply] at e
    exact inv_ne_zero (pow_ne_zero _ hp0) e

/-- **ε_0, …, ε_K は一次独立**。 -/
theorem eps_linearIndependent (K : ℕ) :
    LinearIndependent ℂ (fun b : Fin (K + 1) => eps (p := p) K b) := by
  rw [linearIndependent_iff']
  intro s g hg a ha
  have e := congrArg (fun F => conv (eps (p := p) K a) F) hg
  have hz : conv (eps (p := p) K a) (0 : ZMod (p ^ K) → ℂ) = 0 := by funext x; simp [conv]
  rw [hz, conv_sum_right, Finset.sum_eq_single a] at e
  · rw [conv_smul_right', eps_conv_eps K a a (by have := a.2; omega) (by have := a.2; omega),
      ite_eq_left_of_eq_true _ _ (eq_true rfl)] at e
    exact (smul_eq_zero.mp e).resolve_right (eps_ne_zero K a)
  · intro i _ hia
    rw [conv_smul_right', eps_conv_eps K a i (by have := a.2; omega) (by have := i.2; omega),
      ite_eq_right_of_eq_false _ _ (eq_false (fun h => hia (Fin.ext h).symm)), smul_zero]
  · intro h; exact absurd ha h

/-- **dim IndSpan = K+1**。 -/
theorem finrank_IndSpan (K : ℕ) : Module.finrank ℂ (IndSpan (p := p) K) = K + 1 := by
  rw [IndSpan_eq_EpsSpan, EpsSpan, finrank_span_eq_card (eps_linearIndependent K), Fintype.card_fin]

/-- **原始ケットは IndSpan の同時固有ベクトル**: f ∈ IndSpan ⇒ ∃ c, k ⋆ f = c·k。 -/
theorem ket_conv_IndSpan (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (f : ZMod (p ^ K) → ℂ) (hf : f ∈ IndSpan (p := p) K) :
    ∃ c : ℂ, conv (ket K w (n + 1) hK χ) f = c • ket K w (n + 1) hK χ := by
  rw [IndSpan_eq_EpsSpan] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    by_cases hb : (b : ℕ) = K - (n + 1) - w
    · refine ⟨1, ?_⟩
      rw [one_smul]
      have := ket_conv_eps_self K w n hK χ hχ
      rw [← hb] at this
      exact this
    · exact ⟨0, by rw [zero_smul]; exact ket_conv_eps_ne K w n b hK (by have := b.2; omega) hb χ hχ⟩
  | zero => exact ⟨0, by rw [zero_smul]; funext x; simp [conv]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c₁, h₁⟩ := hx
    obtain ⟨c₂, h₂⟩ := hy
    exact ⟨c₁ + c₂, by rw [← convL_apply, map_add, convL_apply, convL_apply, h₁, h₂, add_smul]⟩
  | smul a x _ hx =>
    obtain ⟨c, h⟩ := hx
    exact ⟨a * c, by rw [conv_smul_right', h, smul_smul]⟩

end PAG.Part59

#print axioms PAG.Part59.eps
#print axioms PAG.Part59.EpsSpan
#print axioms PAG.Part59.Pavg_mem_IndSpan
#print axioms PAG.Part59.eps_mem_IndSpan
#print axioms PAG.Part59.Pavg_mem_EpsSpan
#print axioms PAG.Part59.ball_mem_EpsSpan
#print axioms PAG.Part59.delta_eq_ball
#print axioms PAG.Part59.IndSpan_eq_EpsSpan
#print axioms PAG.Part59.eps_conv_eps
#print axioms PAG.Part59.conv_mem_IndSpan
#print axioms PAG.Part59.eps_ne_zero
#print axioms PAG.Part59.eps_linearIndependent
#print axioms PAG.Part59.finrank_IndSpan
#print axioms PAG.Part59.ket_conv_IndSpan
