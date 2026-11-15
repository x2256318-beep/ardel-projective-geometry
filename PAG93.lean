/-
  PAG 2.0 Part 89（2026-10-19）— B_a の完全性: V_a = span(双対殻 a の原始ケット ∪ {ε_a})
  任意の素数、a ≤ K について
    ε_a ⋆ f = f  ⟺  f ∈ span({双対殻 a の原始ケット} ∪ {ε_a})
  証明: 族 S による展開（PAG56）に ε_a ⋆ を作用させる。双対殻の異なるケットは消え、
        指示関数・δ₀（IndSpan = span{ε_b}）は ε_a の定数倍に落ちる。個数の数え上げは不要
  系: Part 87 の正規直交性と合わせて B_a は V_a の正規直交基底、U_k は V_a 上の単項ユニタリ
-/
import PAG92

namespace PAG.Part93

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part54 PAG.Part56 PAG.Part57 PAG.Part58 PAG.Part59
  PAG.Part90

variable {p : ℕ} [hp : Fact p.Prime]

/-- B_a の台集合。 -/
noncomputable def Bset (K a : ℕ) : Set (ZMod (p ^ K) → ℂ) := {g | KetDual (p := p) K a g} ∪ {eps (p := p) K a}

theorem conv_add_right' {N : ℕ} [NeZero N] (f g h : ZMod N → ℂ) : conv f (g + h) = conv f g + conv f h := by
  rw [← convL_apply, map_add]; rfl

/-- ε_a ⋆ (IndSpan) ⊆ span{ε_a}。 -/
theorem eps_conv_mem (K a : ℕ) (ha : a ≤ K) (g : ZMod (p ^ K) → ℂ) (hg : g ∈ IndSpan (p := p) K) :
    conv (eps (p := p) K a) g ∈ Submodule.span ℂ {eps (p := p) K a} := by
  rw [IndSpan_eq_EpsSpan] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [eps_conv_eps K a b ha (by have := b.2; omega)]
    split_ifs
    · exact Submodule.subset_span rfl
    · exact Submodule.zero_mem _
  | zero =>
    have : conv (eps (p := p) K a) (0 : ZMod (p ^ K) → ℂ) = 0 := by funext x; simp [conv]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [conv_add_right']; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [conv_smul_right']; exact Submodule.smul_mem _ _ hx

/-- **完全性（→）**: ε_a ⋆ f = f なら f ∈ span B_a。 -/
theorem mem_span_of_eps (K a : ℕ) (ha : a ≤ K) (f : ZMod (p ^ K) → ℂ)
    (hf : conv (eps (p := p) K a) f = f) : f ∈ Submodule.span ℂ (Bset (p := p) K a) := by
  have hexp := expand (p := p) K f
  rw [← hf, hexp, conv_sum_right]
  refine Submodule.sum_mem _ (fun b _ => ?_)
  rw [conv_smul_right']
  refine Submodule.smul_mem _ _ ?_
  rcases b with ⟨g, hg⟩
  simp only
  rcases hg with ⟨w, c, h, hc, ψ, hψ, rfl⟩ | ⟨v, hv, rfl⟩ | rfl
  · obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    by_cases hd : K - (n + 1) - w = a
    · subst hd
      rw [conv_comm, ket_conv_eps_self K w n h ψ hψ]
      exact Submodule.subset_span (Or.inl ⟨w, n, h, ψ, hψ, rfl, rfl⟩)
    · rw [conv_comm, ket_conv_eps_ne K w n a h ha (Ne.symm hd) ψ hψ]
      exact Submodule.zero_mem _
  · exact Submodule.span_mono Set.subset_union_right
      (eps_conv_mem K a ha _ (Submodule.subset_span (Or.inl ⟨v, hv, rfl⟩)))
  · exact Submodule.span_mono Set.subset_union_right
      (eps_conv_mem K a ha _ (Submodule.subset_span (Or.inr rfl)))

/-- **完全性（←）**: span B_a の元は ε_a ⋆ で不変。 -/
theorem eps_of_mem_span (K a : ℕ) (ha : a ≤ K) (f : ZMod (p ^ K) → ℂ)
    (hf : f ∈ Submodule.span ℂ (Bset (p := p) K a)) : conv (eps (p := p) K a) f = f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    rcases hx with hx | rfl
    · exact hx.eps
    · rw [eps_conv_eps K a a ha ha, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  | zero => funext x; simp [conv]
  | add x y _ _ hx hy => rw [conv_add_right', hx, hy]
  | smul c x _ hx => rw [conv_smul_right', hx]

/-- **V_a = span B_a**。 -/
theorem Va_eq_span (K a : ℕ) (ha : a ≤ K) (f : ZMod (p ^ K) → ℂ) :
    conv (eps (p := p) K a) f = f ↔ f ∈ Submodule.span ℂ (Bset (p := p) K a) :=
  ⟨mem_span_of_eps K a ha f, eps_of_mem_span K a ha f⟩

end PAG.Part93

#print axioms PAG.Part93.conv_add_right'
#print axioms PAG.Part93.eps_conv_mem
#print axioms PAG.Part93.mem_span_of_eps
#print axioms PAG.Part93.eps_of_mem_span
#print axioms PAG.Part93.Va_eq_span
