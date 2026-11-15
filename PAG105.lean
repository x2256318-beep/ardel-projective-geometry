/-
  PAG 2.0 Part 101（2026-10-19）— レベル K → K+1 の引き戻しと構造の整合性
  π : ℤ/p^{K+1} → ℤ/p^K、π^* f = f ∘ π とすると、任意の素数で
  1. π^* f ⋆ π^* g = p · π^*(f ⋆ g)
  2. ‖π^* f‖² = p ‖f‖²
  3. π^* ε_a^{(K)} = p · ε_{a+1}^{(K+1)}（双対殻が 1 ずれる）
  4. π^* V_a^{(K)} ⊆ V_{a+1}^{(K+1)}
  （ケットの引き戻し π^*|w,χ⟩_K = √p |w,χ⟩_{K+1} は数値で確認、Lean は次回）
-/
import PAG104

namespace PAG.Part105

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part59

variable {p : ℕ} [hp : Fact p.Prime]

/-- 射影 π。 -/
noncomputable def proj (K : ℕ) : ZMod (p ^ (K + 1)) →+ ZMod (p ^ K) :=
  (ZMod.castHom (pow_dvd_pow p (Nat.le_succ K)) (ZMod (p ^ K))).toAddMonoidHom

omit hp in
theorem proj_apply (K : ℕ) (x : ZMod (p ^ (K + 1))) :
    proj (p := p) K x = ZMod.castHom (pow_dvd_pow p (Nat.le_succ K)) (ZMod (p ^ K)) x := rfl

theorem proj_surjective (K : ℕ) : Function.Surjective (proj (p := p) K) := by
  have : NeZero (p ^ (K + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact ZMod.ringHom_surjective _

/-- 引き戻し。 -/
noncomputable def pull (K : ℕ) (f : ZMod (p ^ K) → ℂ) : ZMod (p ^ (K + 1)) → ℂ := f ∘ proj (p := p) K

/-- 核の大きさは p。 -/
theorem card_ker (K : ℕ) :
    ((univ.filter (fun z : ZMod (p ^ (K + 1)) => proj (p := p) K z = 0)).card : ℂ) = p := by
  classical
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (K + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have e := sum_comp_surj (proj (p := p) K) (proj_surjective K) (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at e
  have hK : ((p ^ K : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  push_cast at e hK
  rw [pow_succ] at e
  have := mul_right_cancel₀ hK (e.symm.trans (by ring))
  rw [← this]

/-- **1. 畳み込みとの整合**: π^* f ⋆ π^* g = p · π^*(f ⋆ g)。 -/
theorem conv_pull (K : ℕ) (f g : ZMod (p ^ K) → ℂ) :
    conv (pull (p := p) K f) (pull (p := p) K g) = (p : ℂ) • pull (p := p) K (conv f g) := by
  classical
  have := conv_pullback (proj (p := p) K) (proj_surjective K) f g
  rw [card_ker] at this
  exact this

/-- **2. ノルム**: ‖π^* f‖² = p‖f‖²。 -/
theorem norm_pull (K : ℕ) (f : ZMod (p ^ K) → ℂ) :
    ∑ x, Complex.normSq (pull (p := p) K f x) = p * ∑ x, Complex.normSq (f x) := by
  classical
  have e := sum_comp_surj (proj (p := p) K) (proj_surjective K) (fun h => ((Complex.normSq (f h) : ℝ) : ℂ))
  rw [card_ker] at e
  apply Complex.ofReal_injective
  push_cast
  exact e

/-- 球の引き戻し。 -/
theorem pull_ball (K j : ℕ) (hj : j ≤ K) :
    pull (p := p) K (PAG.Part22.ball (p := p) K j) = PAG.Part22.ball (p := p) (K + 1) j := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (K + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  funext x
  simp only [pull, Function.comp, proj_apply, PAG.Part22.ball, ZMod.castHom_apply]
  have hv : (x.cast : ZMod (p ^ K)).val = x.val % p ^ K := by
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
  have hdvd : p ^ j ∣ p ^ K := pow_dvd_pow p hj
  have hiff : p ^ j ∣ (x.cast : ZMod (p ^ K)).val ↔ p ^ j ∣ x.val := by
    rw [hv]
    constructor
    · intro h; have := Nat.mod_add_div x.val (p ^ K)
      rw [← this]; exact dvd_add h (dvd_mul_of_dvd_left hdvd _)
    · intro h; exact (Nat.dvd_mod_iff hdvd).mpr h
  simp only [hiff]

theorem pull_Pavg (K u : ℕ) (hu : u ≤ K) :
    pull (p := p) K (PAG.Part28.Pavg (p := p) K u) = (p : ℂ) • PAG.Part28.Pavg (p := p) (K + 1) (u + 1) := by
  unfold PAG.Part28.Pavg
  have e : pull (p := p) K (((p : ℂ) ^ u)⁻¹ • PAG.Part22.ball (p := p) K (K - u))
      = ((p : ℂ) ^ u)⁻¹ • pull (p := p) K (PAG.Part22.ball (p := p) K (K - u)) := rfl
  rw [e, pull_ball K (K - u) (by omega), show K + 1 - (u + 1) = K - u by omega, smul_smul]
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [pow_succ, mul_inv, ← mul_assoc, mul_comm (p : ℂ), mul_assoc, mul_inv_cancel₀ hp0, mul_one]

/-- **3. ε の引き戻し**: π^* ε_a = p · ε_{a+1}^{(K+1)}。 -/
theorem pull_eps (K a : ℕ) (ha : a ≤ K) :
    pull (p := p) K (eps (p := p) K a) = (p : ℂ) • eps (p := p) (K + 1) (a + 1) := by
  unfold eps PAG.Part14.epsBall
  by_cases h : a < K
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by omega : a + 1 < K + 1))]
    have e : pull (p := p) K (PAG.Part28.Pavg (p := p) K a - PAG.Part28.Pavg (p := p) K (a + 1))
        = pull (p := p) K (PAG.Part28.Pavg (p := p) K a) - pull (p := p) K (PAG.Part28.Pavg (p := p) K (a + 1)) := rfl
    rw [e, pull_Pavg K a ha, pull_Pavg K (a + 1) h, smul_sub]
  · obtain rfl : a = K := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl _)), ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl _)),
      pull_Pavg a a le_rfl]

/-- **4. V_a の引き戻し**: ε_a ⋆ f = f なら ε_{a+1} ⋆ π^* f = π^* f。 -/
theorem pull_Va (K a : ℕ) (ha : a ≤ K) (f : ZMod (p ^ K) → ℂ) (hf : conv (eps (p := p) K a) f = f) :
    conv (eps (p := p) (K + 1) (a + 1)) (pull (p := p) K f) = pull (p := p) K f := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have e := conv_pull (p := p) K (eps (p := p) K a) f
  rw [hf, pull_eps K a ha] at e
  rw [show conv ((p : ℂ) • eps (p := p) (K + 1) (a + 1)) (pull (p := p) K f)
      = (p : ℂ) • conv (eps (p := p) (K + 1) (a + 1)) (pull (p := p) K f) by
    rw [conv_comm, PAG.Part58.conv_smul_right', conv_comm]] at e
  exact smul_right_injective _ hp0 e

end PAG.Part105

#print axioms PAG.Part105.proj_surjective
#print axioms PAG.Part105.card_ker
#print axioms PAG.Part105.conv_pull
#print axioms PAG.Part105.norm_pull
#print axioms PAG.Part105.pull_ball
#print axioms PAG.Part105.pull_Pavg
#print axioms PAG.Part105.pull_eps
#print axioms PAG.Part105.pull_Va
