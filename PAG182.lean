/-
  PAG 2.0 Part 178（2026-10-22）— ハッセ・ダベンポート関係（m = 2）と 6 次の指標
  1. count_fiber: #{x | x(1 − x) = t} = 1 + L(1 − 4t)
  2. jacobi_dh: J(χ, χ) = χ(4)⁻¹ J(χ, L)（χ ≠ 1）
  3. hasse_davenport2: τ(χ) τ(χL) = χ(4)⁻¹ τ(χ²) τ(L)（χ, χ², χL ≠ 1）
  4. sextic: 位数 6 の指標 χ = ψL（ψ = χ⁴ は 3 次）で z(χ) = ψ(4)⁻¹ ε / z(ψ)²、したがって 1 の冪根でない
-/
import PAG181

namespace PAG.Part182

open Complex Finset PAG.Part119 PAG.Part160 PAG.Part171 PAG.Part173
open ZMod (stdAddChar)

variable {p : ℕ} [hp : Fact p.Prime]

open Classical in
/-- **1. #{x | x(1 − x) = t} = 1 + L(1 − 4t)**。 -/
theorem count_fiber (hp2 : p ≠ 2) (t : ZMod p) :
    ((#{x : ZMod p | x * (1 - x) = t} : ℕ) : ℤ) = quadraticChar (ZMod p) (1 - 4 * t) + 1 := by
  rw [← quadraticChar_card_sqrts (ringChar_ne_two hp2), Set.toFinset_ofPred]
  have h2 := two_ne_zero' (p := p) hp2
  congr 1
  apply Finset.card_nbij' (fun x => 1 - 2 * x) (fun y => (1 - y) / 2)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    rw [← hx]; ring
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    field_simp; linear_combination (-1 : ZMod p) * hy
  · intro x _; field_simp; ring
  · intro y _; field_simp; ring

/-- **2. J(χ, χ) = χ(4)⁻¹ J(χ, L)**。 -/
theorem jacobi_dh (hp2 : p ≠ 2) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    jacobiSum χ χ = (χ 4)⁻¹ * jacobiSum χ (Lc p) := by
  classical
  have h2 := two_ne_zero' (p := p) hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hχ4 : χ 4 * χ 4⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h4, map_one]
  have hχ40 : χ 4 ≠ 0 := left_ne_zero_of_mul_eq_one hχ4
  unfold jacobiSum
  -- J(χ, χ) = Σ_t #fiber(t) χ(t)
  have e1 : ∑ x : ZMod p, χ x * χ (1 - x) = ∑ t : ZMod p, ((Lc p (1 - 4 * t)) + 1) * χ t := by
    simp_rw [← map_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : ZMod p => x * (1 - x)) (t := univ) (fun _ _ => mem_univ _)]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hc := count_fiber hp2 t
    rw [Lc_apply]
    exact_mod_cast hc
  rw [e1]
  simp_rw [add_mul, one_mul]
  rw [Finset.sum_add_distrib, MulChar.sum_eq_zero_of_ne_one hχ, add_zero]
  -- s = 4t
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Units.mulLeft (Ne.isUnit h4).unit) _ _ (fun t => by
    simp only [Units.mulLeft_apply, IsUnit.unit_spec]; rw [map_mul]; field_simp)

/-- **3. ハッセ・ダベンポート関係（m = 2）**：τ(χ) τ(χL) = χ(4)⁻¹ τ(χ²) τ(L)。 -/
theorem hasse_davenport2 (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (hχ2 : χ * χ ≠ 1)
    (hχL : χ * Lc p ≠ 1) :
    gaussSum χ stdAddChar * gaussSum (χ * Lc p) stdAddChar
      = (χ 4)⁻¹ * gaussSum (χ * χ) stdAddChar * gaussSum (Lc p) stdAddChar := by
  have hp0 : ((Fintype.card (ZMod p) : ℕ) : ℂ) ≠ 0 := by rw [ZMod.card]; exact_mod_cast hp.out.ne_zero
  have hJ1 := jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hp0 hχ2 (ZMod.isPrimitive_stdAddChar p)
  have hJ2 := jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hp0 hχL (ZMod.isPrimitive_stdAddChar p)
  have hdh := jacobi_dh hp2 χ hχ
  rw [hJ1, hJ2] at hdh
  have h1 : gaussSum (χ * χ) stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero (primitive_of_ne_one _ hχ2)
  have h2 : gaussSum (χ * Lc p) stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero (primitive_of_ne_one _ hχL)
  have h3 : gaussSum χ stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero (primitive_of_ne_one _ hχ)
  field_simp at hdh
  rw [hdh]; ring

theorem Lc_mul_self : Lc p * Lc p = 1 := by
  apply MulChar.ext
  intro a
  rw [MulChar.coeToFun_mul, Pi.mul_apply, MulChar.one_apply a.isUnit, ← sq]
  exact Lc_sq _ a.ne_zero

/-- **4. 6 次の指標 ψL（ψ は 3 次）：z(ψL) · z(ψ)² = ψ(4)⁻¹ ε**。 -/
theorem sextic_relation (h3p : p % 3 = 1) (ψ : DirichletCharacter ℂ p) (h3 : orderOf ψ = 3) :
    (gaussSum (ψ * Lc p) stdAddChar / ((Real.sqrt p : ℝ) : ℂ))
        * (gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 2 = (ψ 4)⁻¹ * epsG p := by
  have hp2 : p ≠ 2 := by intro h; rw [h] at h3p; norm_num at h3p
  have hne : ψ ≠ 1 := by intro h; rw [h, orderOf_one] at h3; norm_num at h3
  have hψ3 : ψ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one ψ
  have hne2 : ψ * ψ ≠ 1 := by
    intro h
    have : orderOf ψ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [h3] at this; norm_num at this
  have hneL : ψ * Lc p ≠ 1 := by
    intro h
    have : ψ = (Lc p)⁻¹ := eq_inv_of_mul_eq_one_left h
    apply hne2
    rw [this, ← mul_inv, Lc_mul_self, inv_one]
  have hinv : ψ * ψ = ψ⁻¹ := by
    symm; apply inv_eq_of_mul_eq_one_right; rw [← mul_assoc, ← sq, ← pow_succ]; exact hψ3
  have hdh := hasse_davenport2 hp2 ψ hne hne2 hneL
  have hpair := gauss_inv_pair (N := p) ψ (primitive_of_ne_one ψ hne)
  rw [chi_neg_one ψ h3] at hpair
  have hs : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = p := by
    rw [← ofReal_pow, Real.sq_sqrt (by exact_mod_cast hp.out.pos.le)]; push_cast; ring
  have hs0 : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)
    exact_mod_cast this.ne'
  rw [hinv] at hdh
  set τ := gaussSum ψ stdAddChar
  set τL := gaussSum (ψ * Lc p) stdAddChar
  set τi := gaussSum ψ⁻¹ stdAddChar
  set s := ((Real.sqrt p : ℝ) : ℂ)
  have hτ0 : τ ≠ 0 := PAG.Part16.gaussSum_ne_zero (primitive_of_ne_one _ hne)
  -- τ τ⁻¹ = p、τ τL = ψ(4)⁻¹ τi τ(L)
  have hτi : τ * τi = s ^ 2 := by
    rw [hs]
    have := hpair
    field_simp at this
    rw [hs] at this
    linear_combination this
  unfold epsG
  rw [show ((Real.sqrt (p : ℕ) : ℝ) : ℂ) = s from rfl]
  field_simp
  linear_combination τ * hdh + (ψ 4)⁻¹ * gaussSum (Lc p) stdAddChar * hτi

/-- **4'. 6 次の指標 ψL のガウス和の位相は 1 の冪根でない**。 -/
theorem sextic_not_root (h3p : p % 3 = 1) (ψ : DirichletCharacter ℂ p) (h3 : orderOf ψ = 3) :
    ∀ N : ℕ, 0 < N → (gaussSum (ψ * Lc p) stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ N ≠ 1 := by
  have hp2 : p ≠ 2 := by intro h; rw [h] at h3p; norm_num at h3p
  have hψ3 : ψ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one ψ
  have h4 : (4 : ZMod p) ≠ 0 := by
    have h2 := two_ne_zero' (p := p) hp2
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hc3 : (ψ 4) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' ψ (by norm_num), hψ3, MulChar.one_apply (Ne.isUnit h4)]
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hε4 : epsG p ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, epsG_sq hp2]
    rcases Nat.even_or_odd ((p - 1) / 2) with _ | _
    · have := PAG.Part167.Lc_neg_one_pow p ((p - 1) / 2) (by omega)
      rw [this]; rw [← pow_mul]; exact (show Even ((p - 1) / 2 * 2) from ⟨(p - 1) / 2, by ring⟩).neg_one_pow
    · have := PAG.Part167.Lc_neg_one_pow p ((p - 1) / 2) (by omega)
      rw [this]; rw [← pow_mul]; exact (show Even ((p - 1) / 2 * 2) from ⟨(p - 1) / 2, by ring⟩).neg_one_pow
  have hc12 : ((ψ 4)⁻¹ * epsG p) ^ 12 = 1 := by
    rw [mul_pow, inv_pow, show (12 : ℕ) = 3 * 4 by rfl, pow_mul, hc3, one_pow, inv_one, one_mul,
      show (3 * 4 : ℕ) = 4 * 3 by rfl, pow_mul, hε4, one_pow]
  intro N hN hX
  have hrel := sextic_relation h3p ψ h3
  have : (gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ (24 * N) = 1 := by
    have e := congrArg (· ^ (12 * N)) hrel
    simp only [mul_pow, ← pow_mul] at e
    have e1 : (gaussSum (ψ * Lc p) stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ (12 * N) = 1 := by
      rw [show 12 * N = N * 12 by ring, pow_mul, hX, one_pow]
    have e2 : ((ψ 4)⁻¹ * epsG p) ^ (12 * N) = 1 := by rw [pow_mul, hc12, one_pow]
    rw [← mul_pow, e2] at e
    rw [e1, one_mul, show 2 * (12 * N) = 24 * N by ring] at e
    exact e
  exact gauss_cubic_not_root h3p ψ h3 (24 * N) (by omega) this

open Classical in
/-- 2 乗して 1 になる指標は 1 か L。 -/
theorem sq_one_cases (hp2 : p ≠ 2) (φ : DirichletCharacter ℂ p) (h : φ ^ 2 = 1) : φ = 1 ∨ φ = Lc p := by
  have hcyc : IsCyclic (DirichletCharacter ℂ p) := by
    have : IsCyclic (ZMod p)ˣ := inferInstance
    exact isCyclic_of_surjective (MulChar.equiv_rootsOfUnity (ZMod p) ℂ).symm
      (MulChar.equiv_rootsOfUnity (ZMod p) ℂ).symm.surjective
  by_contra hc
  push Not at hc
  have hL1 : Lc p ≠ 1 := Lc_ne_one hp2
  have hsub : ({1, Lc p, φ} : Finset (DirichletCharacter ℂ p)) ⊆ univ.filter (fun x => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · rw [sq]; exact Lc_mul_self
    · exact h
  have hcard := Finset.card_le_card hsub
  have h3 : ({1, Lc p, φ} : Finset (DirichletCharacter ℂ p)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact fun h' => hc.2 h'.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
      exact ⟨hL1.symm, fun h' => hc.1 h'.symm⟩
  have hle := IsCyclic.card_pow_eq_one_le (α := DirichletCharacter ℂ p) (n := 2) (by norm_num)
  omega

/-- **4''. 位数 6 の指標はすべて ψL の形（ψ = χ⁴ は 3 次）で、位相は 1 の冪根でない**。 -/
theorem sextic_general (χ : DirichletCharacter ℂ p) (h6 : orderOf χ = 6) :
    ∀ N : ℕ, 0 < N → (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ N ≠ 1 := by
  have hd := orderOf_dvd_natCard χ
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime hp.out, h6] at hd
  have := hp.out.two_le
  have h3p : p % 3 = 1 := by omega
  have hp2 : p ≠ 2 := by omega
  have hχ6 : χ ^ 6 = 1 := by rw [← h6]; exact pow_orderOf_eq_one χ
  have hψ : orderOf (χ ^ 4) = 3 := by rw [orderOf_pow' _ (by norm_num), h6]; rfl
  have hL : χ ^ 3 = Lc p := by
    rcases sq_one_cases hp2 (χ ^ 3) (by rw [← pow_mul]; exact hχ6) with h | h
    · exfalso
      have : orderOf χ ∣ 3 := orderOf_dvd_of_pow_eq_one h
      rw [h6] at this; norm_num at this
    · exact h
  have hχ : χ = χ ^ 4 * Lc p := by
    rw [← hL, ← pow_add, show 4 + 3 = 6 + 1 by rfl, pow_add, hχ6, one_mul, pow_one]
  rw [hχ]
  exact sextic_not_root h3p (χ ^ 4) hψ

end PAG.Part182

#print axioms PAG.Part182.count_fiber
#print axioms PAG.Part182.jacobi_dh
#print axioms PAG.Part182.hasse_davenport2
#print axioms PAG.Part182.Lc_mul_self
#print axioms PAG.Part182.sextic_relation
#print axioms PAG.Part182.sextic_not_root
#print axioms PAG.Part182.sq_one_cases
#print axioms PAG.Part182.sextic_general
