/-
  Projective Adelic Geometry — formalization Part 4
  対象: 公理 A1 の「より基本的な原理」の有限レベル版
    平行移動 T_a と加法的指標の掛け算 M_b を入れ替える線形写像は、
    （正規化していない）離散フーリエ変換のスカラー倍に限られる
    （Heisenberg 群の Schrödinger 表現の一意性の有限版）。
-/
import PAG2

open Complex Finset

namespace PAG.Part4

variable {N : ℕ} [NeZero N]

/-- 平行移動 (T_a f)(x) = f(x + a)。 -/
def T (a : ZMod N) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun f x := f (x + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 加法的指標の掛け算 (M_b f)(x) = e(bx/N) f(x)。 -/
noncomputable def M (b : ZMod N) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun f x := ZMod.stdAddChar (b * x) * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by funext x; simp; ring

/-- 正規化していない DFT (F f)(y) = Σ_x e(xy/N) f(x)。 -/
noncomputable def F : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun f y := ∑ x, ZMod.stdAddChar (x * y) * f x
  map_add' f g := by funext y; simp [mul_add, sum_add_distrib]
  map_smul' c f := by funext y; simp [mul_sum]; refine sum_congr rfl fun _ _ => by ring

/-- F 自身が入れ替え関係を満たすこと: F T_a = M_{−a} F。 -/
theorem F_comm_T (a : ZMod N) : F ∘ₗ T a = M (-a) ∘ₗ F := by
  apply LinearMap.ext; intro f; funext y
  simp only [LinearMap.comp_apply, F, T, M, LinearMap.coe_mk, AddHom.coe_mk, mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun x => ?_
  simp only [Equiv.coe_addRight]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- F 自身が入れ替え関係を満たすこと: F M_b = T_b F。 -/
theorem F_comm_M (b : ZMod N) : F ∘ₗ M b = T b ∘ₗ F := by
  apply LinearMap.ext; intro f; funext y
  simp only [LinearMap.comp_apply, F, T, M, LinearMap.coe_mk, AddHom.coe_mk]
  refine sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- **一意性**: U T_a = M_{−a} U と U M_b = T_b U をすべての a, b で満たす線形写像 U は
F のスカラー倍である。 -/
theorem heisenberg_unique (U : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ))
    (h1 : ∀ a, U ∘ₗ T a = M (-a) ∘ₗ U) (h2 : ∀ b, U ∘ₗ M b = T b ∘ₗ U) :
    ∃ c : ℂ, U = c • F := by
  classical
  set δ : ZMod N → ℂ := Pi.single 0 1 with hδ
  refine ⟨U δ 0, ?_⟩
  -- U δ は定数関数
  have hMδ : ∀ b, M b δ = δ := by
    intro b; funext x
    simp only [M, LinearMap.coe_mk, AddHom.coe_mk, hδ]
    by_cases hx : x = 0
    · subst hx; simp
    · simp [hx]
  have hconst : ∀ y, U δ y = U δ 0 := by
    intro y
    have := congrArg (fun G => G δ) (h2 y)
    simp only [LinearMap.comp_apply, hMδ] at this
    have h := congrFun this 0
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, zero_add] at h
    exact h.symm
  -- δ_x = T_{−x} δ
  have hshift : ∀ x : ZMod N, T (-x) δ = Pi.single x 1 := by
    intro x; funext y
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, hδ, Pi.single_apply, sub_eq_zero,
      ← sub_eq_add_neg]
  -- U δ_x = c · e(x · /N)
  have hUx : ∀ x y : ZMod N, U (Pi.single x 1) y = U δ 0 * ZMod.stdAddChar (x * y) := by
    intro x y
    rw [← hshift x]
    have := congrArg (fun G => G δ) (h1 (-x))
    simp only [LinearMap.comp_apply, neg_neg] at this
    rw [this]
    simp only [M, LinearMap.coe_mk, AddHom.coe_mk, hconst]
    ring
  apply LinearMap.ext; intro f; funext y
  have hf : f = ∑ x, f x • (Pi.single x 1 : ZMod N → ℂ) := by
    funext z; simp [Finset.sum_apply, Pi.single_apply]
  rw [hf, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hUx, LinearMap.smul_apply,
    F, LinearMap.coe_mk, AddHom.coe_mk, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp [Pi.single_apply]
  ring

end PAG.Part4

#print axioms PAG.Part4.F_comm_T
#print axioms PAG.Part4.F_comm_M
#print axioms PAG.Part4.heisenberg_unique
