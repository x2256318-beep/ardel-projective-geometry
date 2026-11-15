/-
  PAG 2.0 Part 112（2026-10-19）— 正規化した作用素 U_k = λ^{-1/2} T_k の特性多項式
  1. 一般の補題: 根 F(t) が F(t₀)·μ_o に一様に分布していれば ∏(X − F(t)) = (X^o − F(t₀)^o)^{|T|/o}
  2. ケットの根の性質（F(t₀) ≠ 0、(F t / F t₀)^o = 1、各ファイバーの大きさ |T|/o）を補題として切り出す
  3. charpoly U_k = (X^o − ζ_k)^{|S_a|/o}、ζ_k = (𝓕k(t₀)/√λ)^o（Part 100 の予想の形）
  4. |ζ_k| = 1
-/
import PAG115

namespace PAG.Part116

open ZMod Finset Polynomial PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part93 PAG.Part95
  PAG.Part115

/-- **1. 一般の補題**。 -/
theorem prod_closed {α : Type*} [DecidableEq α] (T : Finset α) (F : α → ℂ) (t₀ : α) (o : ℕ) (ho : 0 < o)
    (hF0 : F t₀ ≠ 0) (hpow : ∀ t ∈ T, (F t / F t₀) ^ o = 1)
    (hfib : ∀ ξ : ℂ, ξ ^ o = 1 → o * (T.filter (fun t => F t = F t₀ * ξ)).card = T.card) :
    ∏ t ∈ T, (X - C (F t)) = (X ^ o - C (F t₀ ^ o)) ^ (T.card / o) := by
  classical
  have : NeZero o := ⟨ho.ne'⟩
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / o)
  have hω : IsPrimitiveRoot ω o := Complex.isPrimitiveRoot_exp o ho.ne'
  have hex : ∀ t ∈ T, ∃ j < o, ω ^ j = F t / F t₀ := fun t ht => hω.eq_pow_of_pow_eq_one (hpow t ht)
  let g : α → ℕ := fun t => if ht : t ∈ T then Classical.choose (hex t ht) else 0
  have hg : ∀ t ∈ T, g t < o ∧ F t = F t₀ * ω ^ g t := by
    intro t ht
    have hs := Classical.choose_spec (hex t ht)
    simp only [g, ht, ↓reduceDIte]
    refine ⟨hs.1, ?_⟩
    rw [hs.2]; field_simp
  have hmaps : ∀ t ∈ T, g t ∈ range o := fun t ht => mem_range.mpr (hg t ht).1
  have hfib' : ∀ j ∈ range o, (T.filter (fun t => g t = j)).card = T.card / o := by
    intro j hj
    have hfilt : T.filter (fun t => g t = j) = T.filter (fun t => F t = F t₀ * ω ^ j) := by
      apply Finset.filter_congr
      intro t ht
      constructor
      · intro e; rw [← e]; exact (hg t ht).2
      · intro e
        have e2 : ω ^ g t = ω ^ j := by
          have := (hg t ht).2
          rw [this] at e
          exact mul_left_cancel₀ hF0 e
        exact hω.pow_inj (hg t ht).1 (mem_range.mp hj) e2
    rw [hfilt]
    have hm := hfib (ω ^ j) (by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow])
    rw [← hm, Nat.mul_div_cancel_left _ ho]
  have e1 : ∏ t ∈ T, (X - C (F t)) = ∏ t ∈ T, (fun j => X - C (ω ^ j * F t₀)) (g t) := by
    apply Finset.prod_congr rfl; intro t ht
    simp only
    rw [(hg t ht).2, mul_comm]
  rw [e1, ← Finset.prod_fiberwise_of_maps_to' hmaps (fun j => X - C (ω ^ j * F t₀))]
  simp only [Finset.prod_const]
  rw [Finset.prod_congr rfl (fun j hj => by rw [hfib' j hj]), Finset.prod_pow,
    ← X_pow_sub_C_eq_prod hω ho rfl]

variable {p : ℕ} [hp : Fact p.Prime]

theorem lam_pos (K a : ℕ) : (0 : ℝ) < (p : ℝ) ^ K / (sz p K a : ℝ) := by
  apply div_pos (pow_pos (by exact_mod_cast hp.out.pos) _)
  have : 0 < sz p K a := by
    unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
  exact_mod_cast this

/-- **2. ケットの根の性質**。 -/
theorem ket_root_facts (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K)) (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w)) :
    𝓕 (ket K w (n + 1) h χ) t₀ ≠ 0 ∧
    (∀ t ∈ Tset (p := p) K (K - (n + 1) - w),
      (𝓕 (ket K w (n + 1) h χ) t / 𝓕 (ket K w (n + 1) h χ) t₀) ^ orderOf χ = 1) ∧
    (∀ ξ : ℂ, ξ ^ orderOf χ = 1 → orderOf χ * ((Tset (p := p) K (K - (n + 1) - w)).filter
        (fun t => 𝓕 (ket K w (n + 1) h χ) t = 𝓕 (ket K w (n + 1) h χ) t₀ * ξ)).card
        = (Tset (p := p) K (K - (n + 1) - w)).card) := by
  have hkd : KetDual (p := p) K (K - (n + 1) - w) (ket K w (n + 1) h χ) := ⟨w, n, h, χ, hχ, rfl, rfl⟩
  have hF0 : 𝓕 (ket K w (n + 1) h χ) t₀ ≠ 0 := by
    intro h0
    have := (PAG.Part97.eigen_abs K _ _ hkd t₀).1 ht₀
    rw [h0, map_zero] at this
    linarith [lam_pos (p := p) K (K - (n + 1) - w)]
  refine ⟨hF0, fun t ht => ?_, fun ξ hξ => ?_⟩
  · obtain ⟨m, hm⟩ : ∃ m, orderOf χ = m + 1 := ⟨orderOf χ - 1, by have := orderOf_pos χ; omega⟩
    have hχo : χ ^ (m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one χ
    have := PAG.Part98.pow_eigen_const K w (n + 1) h (by omega) χ hχ m hχo t t₀ ht ht₀
    rw [div_pow, hm, this, div_self (pow_ne_zero _ hF0)]
  · exact_mod_cast PAG.Part103.eigen_multiplicity K w n h χ hχ t₀ ht₀ ξ hξ

/-- 正規化の係数 c = λ^{-1/2}。 -/
noncomputable def cnorm (p K a : ℕ) : ℂ := (((Real.sqrt ((p : ℝ) ^ K / (sz p K a : ℝ)))⁻¹ : ℝ) : ℂ)

theorem cnorm_ne_zero (K a : ℕ) : cnorm p K a ≠ 0 := by
  unfold cnorm
  have : (0 : ℝ) < (Real.sqrt ((p : ℝ) ^ K / (sz p K a : ℝ)))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (lam_pos (p := p) K a))
  exact_mod_cast this.ne'

/-- U_k = λ^{-1/2} T_k。 -/
noncomputable def Uk (K a : ℕ) (ha : a ≤ K) (k : ZMod (p ^ K) → ℂ) : Module.End ℂ (Va (p := p) K a) :=
  cnorm p K a • Tk K a ha k

theorem conj_Uk (K a : ℕ) (ha : a ≤ K) (k : ZMod (p ^ K) → ℂ) :
    (PhiE (p := p) K a ha).conj (Uk K a ha k)
      = Matrix.toLin' (Matrix.diagonal (fun t : Tset (p := p) K a => cnorm p K a * 𝓕 k (t : ZMod (p ^ K)))) := by
  apply LinearMap.ext; intro g
  obtain ⟨f, rfl⟩ := (PhiE (p := p) K a ha).surjective g
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply]
  funext t
  rw [Matrix.mulVec_diagonal]
  show 𝓕 (cnorm p K a • conv k (f : ZMod (p ^ K) → ℂ)) (t : ZMod (p ^ K))
    = cnorm p K a * 𝓕 k t * 𝓕 (f : ZMod (p ^ K) → ℂ) t
  rw [_root_.map_smul, Pi.smul_apply, smul_eq_mul, PAG.Part16.dft_conv, Pi.mul_apply, mul_assoc]

theorem charpoly_Uk (K a : ℕ) (ha : a ≤ K) (k : ZMod (p ^ K) → ℂ) :
    (Uk (p := p) K a ha k).charpoly = ∏ t ∈ Tset (p := p) K a, (X - C (cnorm p K a * 𝓕 k t)) := by
  rw [← LinearEquiv.charpoly_conj (PhiE (p := p) K a ha), conj_Uk, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]
  exact Finset.prod_coe_sort (Tset (p := p) K a) (fun t => X - C (cnorm p K a * 𝓕 k t))

/-- **3. charpoly U_k = (X^o − ζ_k)^{|S_a|/o}**、ζ_k = (λ^{-1/2} 𝓕k(t₀))^o。 -/
theorem charpoly_Uk_closed (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K)) (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w)) :
    (Uk (p := p) K (K - (n + 1) - w) (by omega) (ket K w (n + 1) h χ)).charpoly
      = (X ^ orderOf χ - C ((cnorm p K (K - (n + 1) - w) * 𝓕 (ket K w (n + 1) h χ) t₀) ^ orderOf χ))
          ^ (sz p K (K - (n + 1) - w) / orderOf χ) := by
  classical
  obtain ⟨hF0, hpow, hfib⟩ := ket_root_facts K w n h χ hχ t₀ ht₀
  have hc := cnorm_ne_zero (p := p) K (K - (n + 1) - w)
  rw [charpoly_Uk, ← card_Tset K _ _ ⟨w, n, h, χ, hχ, rfl, rfl⟩]
  apply prod_closed _ _ t₀ _ (orderOf_pos χ) (mul_ne_zero hc hF0)
  · intro t ht
    rw [mul_div_mul_left _ _ hc]; exact hpow t ht
  · intro ξ hξ
    rw [← hfib ξ hξ]
    congr 2
    apply Finset.filter_congr
    intro t _
    rw [mul_assoc]
    exact ⟨fun e => mul_left_cancel₀ hc e, fun e => by rw [e]⟩

/-- **4. |ζ_k| = 1**。 -/
theorem norm_zeta (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K)) (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w)) :
    Complex.normSq ((cnorm p K (K - (n + 1) - w) * 𝓕 (ket K w (n + 1) h χ) t₀) ^ orderOf χ) = 1 := by
  have hkd : KetDual (p := p) K (K - (n + 1) - w) (ket K w (n + 1) h χ) := ⟨w, n, h, χ, hχ, rfl, rfl⟩
  have e := (PAG.Part97.eigen_abs K _ _ hkd t₀).1 ht₀
  rw [map_pow, map_mul, e]
  unfold cnorm
  rw [Complex.normSq_ofReal]
  have hl := lam_pos (p := p) K (K - (n + 1) - w)
  have : (Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)))⁻¹ *
      (Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)))⁻¹
      * ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hl.le, inv_mul_cancel₀ hl.ne']
  rw [this, one_pow]

end PAG.Part116

#print axioms PAG.Part116.prod_closed
#print axioms PAG.Part116.lam_pos
#print axioms PAG.Part116.ket_root_facts
#print axioms PAG.Part116.cnorm_ne_zero
#print axioms PAG.Part116.conj_Uk
#print axioms PAG.Part116.charpoly_Uk
#print axioms PAG.Part116.charpoly_Uk_closed
#print axioms PAG.Part116.norm_zeta
