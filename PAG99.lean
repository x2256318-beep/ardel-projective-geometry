/-
  PAG 2.0 Part 95（2026-10-19）— 巡回構造の最小性: χ^m ≠ 1 なら U_k^m はスカラーでない
  任意の素数、k = |w, χ⟩（原始、双対殻 a）について
  1. ε_a は単数不変（ε_a ∝ k ⋆ k̄ で、χ·χ⁻¹ = 1 同変）
  2. χ^(n+1) ≠ 1 なら ∃ t, t' ∈ T_a で 𝓕k(t)^(n+1) ≠ 𝓕k(t')^(n+1)
  系（PAG98 と合わせて）: U_k^m が V_a 上のスカラー ⟺ χ^m = 1。
      よって B_a 上の置換 π_k の巡回の長さはすべてちょうど ord χ（U_k が単項であること（PAG92）による）
-/
import PAG98

namespace PAG.Part99

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part95 PAG.Part97
  PAG.Part98

variable {p : ℕ} [hp : Fact p.Prime]

/-- **ε_a は単数不変**（双対殻 a の原始ケットがあるとき）。 -/
theorem eps_invariant (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (u : (ZMod (p ^ K))ˣ) (x : ZMod (p ^ K)) :
    eps (p := p) K (K - (n + 1) - w) (u * x) = eps (p := p) K (K - (n + 1) - w) x := by
  have hB := PAG.Part29.thmB_eps K w n h χ hχ
  have hE := conv_equivariant K _ _ _ _ (ket_equivariant K w (n + 1) h χ)
    (ket_equivariant K w (n + 1) h ((χ⁻¹ : DirichletCharacter ℂ _)))
  have hone : ∀ v : (ZMod (p ^ K))ˣ,
      χ (ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ K)) (ZMod (p ^ (n + 1))) v) *
        (χ⁻¹ : DirichletCharacter ℂ _) (ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ K)) (ZMod (p ^ (n + 1))) v)
        = 1 := by
    intro v
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply ((Units.isUnit v).map _)]
  have e := hE u x
  simp only [] at e
  rw [hone, one_mul, hB, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at e
  have hc : PAG.Part29.cB K w n χ ≠ 0 := by
    unfold PAG.Part29.cB
    exact mul_ne_zero (PAG.Part75.chi_neg_one_ne_zero _) (PAG.Part77.lam_ne_zero K _)
  exact mul_left_cancel₀ hc e

/-- **最小性**: χ^(n+1) ≠ 1 なら T_a 上で 𝓕k^(n+1) は定数でない。 -/
theorem pow_eigen_nonconst (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (m : ℕ) (hne : χ ^ (m + 1) ≠ 1) :
    ∃ t ∈ Tset (p := p) K (K - (n + 1) - w), ∃ t' ∈ Tset (p := p) K (K - (n + 1) - w),
      𝓕 (ket K w (n + 1) h χ) t ^ (m + 1) ≠ 𝓕 (ket K w (n + 1) h χ) t' ^ (m + 1) := by
  set a := K - (n + 1) - w with ha
  set k := ket K w (n + 1) h χ
  have hkd : KetDual (p := p) K a k := ⟨w, n, h, χ, hχ, rfl, rfl⟩
  by_contra H
  push Not at H
  -- T_a は空でない
  have hT : (Tset (p := p) K a).Nonempty := by
    rw [← Finset.card_pos, card_Tset K a k hkd]
    unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
  obtain ⟨t0, ht0⟩ := hT
  set C := 𝓕 k t0 ^ (m + 1)
  set F := prodConv k (List.replicate m k)
  have hdF : ∀ s, 𝓕 F s = 𝓕 k s ^ (m + 1) := by
    intro s; rw [dft_prodConv, ← List.replicate_succ, List.map_replicate, List.prod_replicate]
  -- F = C • ε_a
  have hFe : F = C • eps (p := p) K a := by
    apply (ZMod.dft (N := p ^ K) (E := ℂ)).injective
    funext s
    rw [hdF, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hs : s ∈ Tset (p := p) K a
    · have h1 : 𝓕 (eps (p := p) K a) s = 1 := by simpa [Tset] using hs
      rw [h1, mul_one]; exact H s hs t0 ht0
    · have h0 : 𝓕 (eps (p := p) K a) s = 0 := by
        rcases PAG.Part31.dft_eps_zero_or_one (p := p) K a (by omega) s with h0 | h1
        · exact h0
        · exact absurd (by simp [Tset, h1]) hs
      rw [h0, mul_zero, (eigen_abs K a k hkd s).2 hs, zero_pow (by omega)]
  -- χ^(m+1) ≠ 1 を与える単数
  obtain ⟨v, hv⟩ : ∃ v : (ZMod (p ^ (n + 1)))ˣ, (χ ^ (m + 1)) v ≠ 1 := by
    by_contra H2
    push Not at H2
    apply hne
    apply MulChar.ext
    intro v; rw [H2 v, MulChar.one_apply_coe]
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (pow_dvd_pow p (by omega : n + 1 ≤ K)) v
  have hcu : ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ K)) (ZMod (p ^ (n + 1))) (u : ZMod (p ^ K)) = v := by
    have e := congrArg (fun z : (ZMod (p ^ (n + 1)))ˣ => (z : ZMod (p ^ (n + 1)))) hu
    simp only [ZMod.unitsMap_val] at e
    rw [ZMod.castHom_apply, e]
  -- F は 0
  have hF0 : F = 0 := by
    funext x
    have e1 := prodConv_equivariant K _ k (ket_equivariant K w (n + 1) h χ) m u x
    have e2 : F (u * x) = F x := by
      rw [hFe, Pi.smul_apply, Pi.smul_apply, eps_invariant K w n h χ hχ u x]
    simp only [] at e1
    rw [hcu, ← MulChar.pow_apply' χ (by omega : m + 1 ≠ 0)] at e1
    have e3 : ((χ ^ (m + 1)) v - 1) * F x = 0 := by
      have : F (u * x) = (χ ^ (m + 1)) v * F x := e1
      rw [sub_mul, one_mul, ← this, e2, sub_self]
    exact (mul_eq_zero.mp e3).resolve_left (sub_ne_zero.mpr hv)
  -- ノルムは λ^m ≠ 0
  have hn := (prodConv_same_dual K a k (List.replicate m k) hkd (fun g hg => by
    rw [List.eq_of_mem_replicate hg]; exact hkd)).2
  rw [show prodConv k (List.replicate m k) = F from rfl, hF0] at hn
  simp only [Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero, List.length_replicate] at hn
  have hl : (0 : ℝ) < (p : ℝ) ^ K / (sz p K a : ℝ) := by
    have : 0 < sz p K a := by
      unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
    exact div_pos (pow_pos (by exact_mod_cast hp.out.pos) _) (by exact_mod_cast this)
  exact absurd hn.symm (pow_ne_zero _ hl.ne')

end PAG.Part99

#print axioms PAG.Part99.eps_invariant
#print axioms PAG.Part99.pow_eigen_nonconst
