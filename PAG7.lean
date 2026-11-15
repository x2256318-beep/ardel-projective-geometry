/-
  Projective Adelic Geometry 2.0, Part 3 — formalization（PAG7.lean）
    (a) 赤道ブロック: M = [[0,1,0],[1,0,1],[0,1,0]] の M³ = 2M と、
        2 つの鏡映の和 A = H_0 + H_∞ が e_0, u_+ = H_0 e_0, u_- = H_∞ e_0 の上で
        A³ = (2 + κ²)A + 2κ（κ = 赤道対角成分）を満たすこと。κ = 0 なら A³ = 2A。
    (b) ヤコビ和: τ(χ₁)τ(χ₂) の二重和展開、s = x + y ごとのファイバー分解、
        単数 s のファイバー = (χ₁χ₂)(s)·J(χ₁,χ₂)、非単数ファイバーが 0 なら τ(χ₁)τ(χ₂) = J·τ(χ₁χ₂)。
        素数法では Mathlib の jacobiSum_mul_nontrivial と一致（定義も同じ）。
    (c) ルート数の 2 乗の恒等式 W(χ)² = (−1)^a Ĵ W(χ²)（(b) の帰結としての代数）。
    (d) 押し出しと DFT の絡み合い F ∘ P = Q ∘ F（P: p 倍写像による押し出し、Q: 引き戻し）。
-/
import PAG4
import Mathlib.NumberTheory.JacobiSum.Basic

open Complex Finset

namespace PAG.Part7

/-! ## (a) 赤道ブロック -/

/-- 赤道ブロック行列。 -/
def Meq : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 1, 0, 1; 0, 1, 0]

/-- M³ = 2M（最小多項式 λ(λ² − 2)、固有値 0, ±√2）。 -/
theorem Meq_cube : Meq * Meq * Meq = 2 • Meq := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Meq, Matrix.mul_apply, Fin.sum_univ_three]

section Abstract

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- 2 つの鏡映 H_0, H_∞ と赤道ベクトル e_0。
仮定: H_0² e_0 = e_0、H_∞² e_0 = e_0（鏡映）、
H_0 は u_- = H_∞ e_0 のうち赤道成分 κ e_0 だけを見る（H_0 u_- = κ u_+）、H_∞ u_+ = κ u_- も同様。 -/
structure EqData (H0 Hi : V →ₗ[R] V) (e0 : V) (κ : R) : Prop where
  h0sq : H0 (H0 e0) = e0
  hisq : Hi (Hi e0) = e0
  h0_on_um : H0 (Hi e0) = κ • H0 e0
  hi_on_up : Hi (H0 e0) = κ • Hi e0

variable {H0 Hi : V →ₗ[R] V} {e0 : V} {κ : R}

/-- A = H_0 + H_∞ について A³ e_0 = (2 + κ²) A e_0 + 2κ e_0。κ がちょうど障害になる。 -/
theorem cube_e0 (h : EqData H0 Hi e0 κ) :
    (H0 + Hi) ((H0 + Hi) ((H0 + Hi) e0)) = (2 + κ ^ 2) • (H0 + Hi) e0 + (2 * κ) • e0 := by
  simp only [LinearMap.add_apply, map_add, map_smul, h.h0sq, h.hisq, h.h0_on_um, h.hi_on_up]
  module

/-- **赤道直交条件 κ = ⟨e_0|H_0|e_0⟩ = 0 なら**、e_0, u_+, u_- の上で A³ = 2A。 -/
theorem cube_eq_two_of_kappa_zero (h : EqData H0 Hi e0 0) :
    (H0 + Hi) ((H0 + Hi) ((H0 + Hi) e0)) = (2 : R) • (H0 + Hi) e0 ∧
    (H0 + Hi) ((H0 + Hi) ((H0 + Hi) (H0 e0))) = (2 : R) • (H0 + Hi) (H0 e0) ∧
    (H0 + Hi) ((H0 + Hi) ((H0 + Hi) (Hi e0))) = (2 : R) • (H0 + Hi) (Hi e0) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [LinearMap.add_apply, map_add, h.h0sq, h.hisq, h.h0_on_um, h.hi_on_up,
    zero_smul, add_zero, zero_add] <;> module

/-- 赤道ブロックの作用: A e_0 = u_+ + u_-、A u_+ = e_0、A u_- = e_0（κ = 0）。これが行列 M_eq。 -/
theorem block_action (h : EqData H0 Hi e0 0) :
    (H0 + Hi) e0 = H0 e0 + Hi e0 ∧ (H0 + Hi) (H0 e0) = e0 ∧ (H0 + Hi) (Hi e0) = e0 := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [h.h0sq, h.hi_on_up]
  · simp [h.hisq, h.h0_on_um]

end Abstract

/-! ## (b) ヤコビ和とガウス和 -/

section Jacobi

variable {N : ℕ} [NeZero N]

/-- ヤコビ和 J(χ₁,χ₂) = Σ_x χ₁(x) χ₂(1 − x)。 -/
noncomputable def J (χ₁ χ₂ : MulChar (ZMod N) ℂ) : ℂ := ∑ x, χ₁ x * χ₂ (1 - x)

/-- Mathlib の jacobiSum と同じ定義。 -/
theorem J_eq_jacobiSum (χ₁ χ₂ : MulChar (ZMod N) ℂ) : J χ₁ χ₂ = jacobiSum χ₁ χ₂ := rfl

/-- ファイバー和 F(s) = Σ_{x+y=s} χ₁(x)χ₂(y) = Σ_x χ₁(x)χ₂(s − x)。 -/
noncomputable def fiber (χ₁ χ₂ : MulChar (ZMod N) ℂ) (s : ZMod N) : ℂ := ∑ x, χ₁ x * χ₂ (s - x)

/-- 二重和展開と s ごとの束ね: τ(χ₁)τ(χ₂) = Σ_s ψ(s) F(s)。 -/
theorem gauss_mul_gauss_eq_sum_fiber (χ₁ χ₂ : MulChar (ZMod N) ℂ) (ψ : AddChar (ZMod N) ℂ) :
    gaussSum χ₁ ψ * gaussSum χ₂ ψ = ∑ s, ψ s * fiber χ₁ χ₂ s := by
  unfold gaussSum fiber
  rw [sum_mul_sum]
  -- Σ_x Σ_y χ₁x ψx χ₂y ψy = Σ_x Σ_s χ₁x χ₂(s−x) ψ s（y = s − x）
  have : ∀ x : ZMod N, ∑ y, χ₁ x * ψ x * (χ₂ y * ψ y) = ∑ s, ψ s * (χ₁ x * χ₂ (s - x)) := by
    intro x
    refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y => ?_
    simp only [Equiv.coe_addLeft, add_sub_cancel_left, AddChar.map_add_eq_mul]
    ring
  simp_rw [this, mul_sum]
  rw [sum_comm]

/-- **s = 1 のファイバーがヤコビ和**。 -/
theorem fiber_one (χ₁ χ₂ : MulChar (ZMod N) ℂ) : fiber χ₁ χ₂ 1 = J χ₁ χ₂ := rfl

/-- **単数 s のファイバー**: x = s u と置き換えて F(s) = (χ₁χ₂)(s) J(χ₁,χ₂)。 -/
theorem fiber_unit (χ₁ χ₂ : MulChar (ZMod N) ℂ) (s : (ZMod N)ˣ) :
    fiber χ₁ χ₂ s = (χ₁ * χ₂) s * J χ₁ χ₂ := by
  unfold fiber J
  rw [mul_sum, ← Equiv.sum_comp (Units.mulLeft s)]
  refine sum_congr rfl fun u _ => ?_
  simp only [Units.mulLeft_apply]
  rw [show (s : ZMod N) - s * u = s * (1 - u) by ring, map_mul, map_mul, MulChar.coeToFun_mul,
    Pi.mul_apply]
  ring

/-- **ガウス和の積 = ヤコビ和 × ガウス和**（非単数のファイバーが 0 のとき）。
素数法で χ₁χ₂ ≠ 1 のとき、また原始指標の積が原始的な素数べき法のとき、この仮定が成り立つ。 -/
theorem gauss_mul_gauss_eq_jacobi_mul (χ₁ χ₂ : MulChar (ZMod N) ℂ) (ψ : AddChar (ZMod N) ℂ)
    (hnon : ∀ s : ZMod N, ¬ IsUnit s → fiber χ₁ χ₂ s = 0) :
    gaussSum χ₁ ψ * gaussSum χ₂ ψ = J χ₁ χ₂ * gaussSum (χ₁ * χ₂) ψ := by
  rw [gauss_mul_gauss_eq_sum_fiber, gaussSum, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  by_cases hs : IsUnit s
  · obtain ⟨u, rfl⟩ := hs
    rw [fiber_unit]; ring
  · rw [hnon s hs, MulChar.map_nonunit _ hs]; ring

/-- 素数法での確認（Mathlib）: χ² ≠ 1 なら τ(χ)² = J(χ,χ) τ(χ²)。 -/
theorem gauss_sq_prime {p : ℕ} [Fact p.Prime] (χ : MulChar (ZMod p) ℂ) (hχ : χ * χ ≠ 1)
    (ψ : AddChar (ZMod p) ℂ) :
    gaussSum χ ψ ^ 2 = J χ χ * gaussSum (χ * χ) ψ := by
  rw [sq, ← jacobiSum_mul_nontrivial hχ ψ, J_eq_jacobiSum]; ring

end Jacobi

/-! ## (c) ルート数の 2 乗 -/

/-- τ² = J τ₂ なら、W = τ/(i^a √q)、W₂ = τ₂/√q（χ² は偶）について W² = (−1)^a (J/√q) W₂。 -/
theorem W_sq (τ τ₂ Jv : ℂ) (q : ℝ) (hq : 0 < q) (a : ℕ) (h : τ ^ 2 = Jv * τ₂) :
    (τ / (I ^ a * (Real.sqrt q : ℂ))) ^ 2 = (-1) ^ a * (Jv / (Real.sqrt q : ℂ)) * (τ₂ / (Real.sqrt q : ℂ)) := by
  have hs : (Real.sqrt q : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have hI : (I ^ a) ^ 2 = (-1 : ℂ) ^ a := by rw [← pow_mul, mul_comm, pow_mul, I_sq]
  have hIa : I ^ a ≠ 0 := pow_ne_zero _ I_ne_zero
  rw [div_pow, mul_pow, hI, h]
  have h1 : ((-1 : ℂ) ^ a) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  field_simp
  rw [show ((-1 : ℂ) ^ a) ^ 2 = 1 from h1]
  ring

/-! ## (d) 押し出しと DFT -/

section Intertwine

variable {N : ℕ} [NeZero N]

/-- p 倍写像 z ↦ p z による押し出し（正規化前）(P f)(w) = Σ_{pz = w} f(z)。 -/
noncomputable def push (p : ZMod N) (f : ZMod N → ℂ) (w : ZMod N) : ℂ :=
  ∑ z, if p * z = w then f z else 0

/-- 引き戻し (Q g)(z) = g(p z)。 -/
def pull (p : ZMod N) (g : ZMod N → ℂ) (z : ZMod N) : ℂ := g (p * z)

/-- **F ∘ P = Q ∘ F**（正規化すると F S_p = S_p^* F）。 -/
theorem F_push (p : ZMod N) (f : ZMod N → ℂ) :
    PAG.Part4.F (push p f) = pull p (PAG.Part4.F f) := by
  funext y
  simp only [PAG.Part4.F, LinearMap.coe_mk, AddHom.coe_mk, push, pull, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [sum_eq_single (p * z)]
  · simp only [ite_true]; congr 2; ring
  · intro w _ hw; rw [ite_eq_right (Ne.symm hw)]; ring
  · intro h; exact absurd (mem_univ _) h

end Intertwine

end PAG.Part7

#print axioms PAG.Part7.Meq_cube
#print axioms PAG.Part7.cube_e0
#print axioms PAG.Part7.cube_eq_two_of_kappa_zero
#print axioms PAG.Part7.block_action
#print axioms PAG.Part7.J_eq_jacobiSum
#print axioms PAG.Part7.gauss_mul_gauss_eq_sum_fiber
#print axioms PAG.Part7.fiber_one
#print axioms PAG.Part7.fiber_unit
#print axioms PAG.Part7.gauss_mul_gauss_eq_jacobi_mul
#print axioms PAG.Part7.gauss_sq_prime
#print axioms PAG.Part7.W_sq
#print axioms PAG.Part7.F_push
