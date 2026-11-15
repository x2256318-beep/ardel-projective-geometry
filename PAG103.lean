/-
  PAG 2.0 Part 99（2026-10-19）— 固有値の重複度は一様: 各 o 乗根が |T_a|/o 回ずつ
  任意の素数、k = |w, χ⟩（原始、双対殻 a）、o = ord χ、t₀ ∈ T_a、w₀ = 𝓕k(t₀) とすると
    ξ^o = 1 ⇒ o · #{t ∈ T_a | 𝓕k(t) = w₀ ξ} = #T_a
  （固有値は w₀·μ_o に一様に分布する。証明は冪和の消滅（PAG102）と根の直交性）
-/
import PAG102

namespace PAG.Part103

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part90 PAG.Part95 PAG.Part97 PAG.Part98
  PAG.Part102

variable {p : ℕ} [hp : Fact p.Prime]

/-- 1 の冪根の指示関数: y^o = 1 なら Σ_{j<o} y^j = o·[y = 1]。 -/
theorem geom_indicator (o : ℕ) (y : ℂ) (hy : y ^ o = 1) :
    ∑ j ∈ range o, y ^ j = if y = 1 then (o : ℂ) else 0 := by
  split_ifs with h1
  · subst h1; simp
  · have e := geom_sum_mul y o
    rw [hy, sub_self] at e
    exact (mul_eq_zero.mp e).resolve_right (sub_ne_zero.mpr h1)

/-- **固有値の重複度**。 -/
theorem eigen_multiplicity (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K)) (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w))
    (ξ : ℂ) (hξ : ξ ^ orderOf χ = 1) :
    (orderOf χ : ℂ) * (((Tset (p := p) K (K - (n + 1) - w)).filter
        (fun t => 𝓕 (ket K w (n + 1) h χ) t = 𝓕 (ket K w (n + 1) h χ) t₀ * ξ)).card : ℂ)
      = ((Tset (p := p) K (K - (n + 1) - w)).card : ℂ) := by
  classical
  set T := Tset (p := p) K (K - (n + 1) - w)
  set F := fun t => 𝓕 (ket K w (n + 1) h χ) t
  set o := orderOf χ
  have ho : 0 < o := orderOf_pos χ
  have hχo : χ ^ o = 1 := pow_orderOf_eq_one χ
  have hkd : KetDual (p := p) K (K - (n + 1) - w) (ket K w (n + 1) h χ) := ⟨w, n, h, χ, hχ, rfl, rfl⟩
  have hw0 : F t₀ ≠ 0 := by
    intro h0
    have := (eigen_abs K _ _ hkd t₀).1 ht₀
    simp only [F] at h0
    rw [h0, Complex.normSq_zero] at this
    have hs : 0 < sz p K (K - (n + 1) - w) := by
      unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
    have : (0 : ℝ) < (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) :=
      div_pos (pow_pos (by exact_mod_cast hp.out.pos) _) (by exact_mod_cast hs)
    linarith
  have hξ0 : ξ ≠ 0 := by intro h0; rw [h0, zero_pow ho.ne'] at hξ; exact zero_ne_one hξ
  set c := F t₀ * ξ
  have hc : c ≠ 0 := mul_ne_zero hw0 hξ0
  -- 各 t ∈ T で (F t / c)^o = 1
  obtain ⟨m, hm⟩ : ∃ m, o = m + 1 := ⟨o - 1, by omega⟩
  have hy : ∀ t ∈ T, (F t / c) ^ o = 1 := by
    intro t ht
    have e := pow_eigen_const K w (n + 1) h (by omega) χ hχ m (by rw [← hm]; exact hχo) t t₀ ht ht₀
    rw [div_pow, mul_pow, hξ, mul_one, hm]
    have e' : F t ^ (m + 1) = F t₀ ^ (m + 1) := e
    rw [e']
    exact div_self (pow_ne_zero _ hw0)
  -- 二重和
  have key : (o : ℂ) * ((T.filter (fun t => F t = c)).card : ℂ)
      = ∑ j ∈ range o, c⁻¹ ^ j * ∑ t ∈ T, F t ^ j := by
    have h1 : (o : ℂ) * ((T.filter (fun t => F t = c)).card : ℂ) = ∑ t ∈ T, ∑ j ∈ range o, (F t / c) ^ j := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [geom_indicator o _ (hy t ht)]
      by_cases hFt : F t = c
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hFt), ite_eq_left_of_eq_true _ _ (eq_true (by rw [hFt, div_self hc]))]; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hFt), ite_eq_right_of_eq_false _ _ (eq_false (fun e => hFt (by rwa [div_eq_one_iff_eq hc] at e)))]; simp
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [div_pow, div_eq_mul_inv, ← inv_pow, mul_comm]
  have hEq : ((T.filter (fun t => 𝓕 (ket K w (n + 1) h χ) t = 𝓕 (ket K w (n + 1) h χ) t₀ * ξ)).card : ℂ)
      = ((T.filter (fun t => F t = c)).card : ℂ) := by congr
  rw [hEq, key, Finset.sum_eq_single 0]
  · simp [T]
  · intro j hj hj0
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hne : χ ^ (j' + 1) ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by have := mem_range.mp hj; omega)
    rw [show ∑ t ∈ T, F t ^ (j' + 1) = 0 from trace_pow_vanish K w n h χ hχ j' hne, mul_zero]
  · intro h0; exact absurd (mem_range.mpr ho) h0

end PAG.Part103

#print axioms PAG.Part103.geom_indicator
#print axioms PAG.Part103.eigen_multiplicity
