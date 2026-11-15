/-
  PAG 2.0 Part 229（2026-10-30）— 可換子 A′ と中心 Z の中国剰余定理による分解、番号の集合 S の分解
  A_N = ⟨E_s, D_s⟩（Part 214 の shellAlg）、A′_N（Part 220 の fullComm、Part 222 の fullCommAlg）、
  Z_N = A_N ∩ A′_N（Part 222 の fullCommCenter・centerAlg、Part 225 の mem_fullCommCenter_iff）、
  中国剰余定理の座標の付け替え C（Part 228 の crtConj）、L(S) = S ⊗ 1・R(T) = 1 ⊗ T（Part 228 の leftOp・rightOp）
  0. 一般の補題（a, b ≥ 1。互いに素でなくてよい）：u_i・v_j がそれぞれ一次独立なら L(u_i)R(v_j) も一次独立。
     部分代数 B ⊆ End(ℂ^{ℤ/a})、B′ ⊆ End(ℂ^{ℤ/b}) について B ⊗ B′ ≅ L(B) ⊔ R(B′)（def tensorSupEquiv、代数同型）、
     dim (L(B) ⊔ R(B′)) = dim B·dim B′。gcd(a, b) = 1 で C(X) = L(B) ⊔ R(B′) なら B ⊗ B′ ≅ X（def crtTensorEquiv）
  1. Part 226 によらない次元の乗法性：dim A_{ab} = dim A_a·dim A_b（Part 228 の C(A_{ab}) = L(A_a) ⊔ R(A_b) と 0 から）。
     Part 228 の tensLift の単射性も、Part 226 の数え上げを使わずに出る
  2. 可換子：C(A′_{ab}) = L(A′_a) ⊔ R(A′_b)、A′_a ⊗ A′_b ≅ A′_{ab}（def fullCommTensorEquiv）。
     ⊇ は可換性から、= は次元（Part 226 の finrank_fullComm_mul と 0）から
  3. 中心：C(Z_{ab}) = L(Z_a) ⊔ R(Z_b)、Z_a ⊗ Z_b ≅ Z_{ab}（def centerTensorEquiv。次元は Part 226 の finrank_fullCommCenter_mul）
  4. 番号の集合：(c_a, d_a)·(c_b, d_b) = (c_a c_b, d_a d_b)（def idxMul）は S(a) × S(b) → S(ab) の全単射で、
     逆は (c, d) ↦ ((gcd(c, a), gcd(d, a)), (gcd(c, b), gcd(d, b)))（def idxSplit）。#S(ab) = #S(a)·#S(b)、
     m(c_a c_b) = m(c_a)m(c_b)、n_(c_a c_b, d_a d_b) = n_(c_a, d_a)·n_(c_b, d_b)
-/
import PAG232

namespace PAG.Part233

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part231 PAG.Part232
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 一般の補題：B ⊗ B′ ≅ L(B) ⊔ R(B′) -/

/-- **0a.** L(S)R(T) を積の形の関数 F(x, y) = f(x)h(y) に作用させると S f(x)·T h(y)。 -/
theorem leftOp_mul_rightOp_apply_prod {a b : ℕ} (S : Module.End ℂ (ZMod a → ℂ)) (T : Module.End ℂ (ZMod b → ℂ))
    (f : ZMod a → ℂ) (h : ZMod b → ℂ) (x : ZMod a) (y : ZMod b) :
    (leftOp b S * rightOp a T) (fun q => f q.1 * h q.2) (x, y) = S f x * T h y := by
  have h1 : ∀ x' : ZMod a, (fun y' : ZMod b => f x' * h y') = f x' • h := fun x' => by
    funext y'
    rw [Pi.smul_apply, smul_eq_mul]
  have h2 : (fun x' : ZMod a => T (fun y' => f x' * h y') y) = T h y • f := by
    funext x'
    rw [h1 x', map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  show S (fun x' => T (fun y' => f x' * h y') y) x = S f x * T h y
  rw [h2, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **0b. 一次独立性**：u_i（End(ℂ^{ℤ/a})）と v_j（End(ℂ^{ℤ/b})）がそれぞれ一次独立なら、L(u_i)R(v_j) も一次独立（0a の式で F = f ⊗ h に作用させ、まず v_j、次に u_i の一次独立を使う）。 -/
theorem linearIndependent_leftOp_mul_rightOp {a b : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {u : ι → Module.End ℂ (ZMod a → ℂ)} {v : κ → Module.End ℂ (ZMod b → ℂ)}
    (hu : LinearIndependent ℂ u) (hv : LinearIndependent ℂ v) :
    LinearIndependent ℂ (fun p : ι × κ => leftOp b (u p.1) * rightOp a (v p.2)) := by
  rw [Fintype.linearIndependent_iff] at hu hv ⊢
  intro g hg
  have key : ∀ (f : ZMod a → ℂ) (h : ZMod b → ℂ) (x : ZMod a) (y : ZMod b),
      ∑ j : κ, (∑ i : ι, g (i, j) * u i f x) * v j h y = 0 := by
    intro f h x y
    have hx := congrArg
      (fun X : Module.End ℂ (ZMod a × ZMod b → ℂ) => X (fun q => f q.1 * h q.2) (x, y)) hg
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      LinearMap.zero_apply, Pi.zero_apply] at hx
    simp only [leftOp_mul_rightOp_apply_prod] at hx
    rw [Fintype.sum_prod_type, Finset.sum_comm] at hx
    rw [← hx]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have step1 : ∀ (f : ZMod a → ℂ) (x : ZMod a) (j : κ), ∑ i : ι, g (i, j) * u i f x = 0 := by
    intro f x
    apply hv (fun j => ∑ i : ι, g (i, j) * u i f x)
    apply LinearMap.ext
    intro h
    funext y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      LinearMap.zero_apply, Pi.zero_apply]
    exact key f h x y
  intro p
  obtain ⟨i, j⟩ := p
  refine hu (fun i => g (i, j)) ?_ i
  apply LinearMap.ext
  intro f
  funext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.zero_apply, Pi.zero_apply]
  exact step1 f x j

/-- 一般の部分代数 B、B′ について B ⊗ B′ → End(ℂ^{ℤ/a × ℤ/b})、S ⊗ T ↦ L(S)R(T)（代数準同型）。 -/
noncomputable def tensLiftGen {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    TensorProduct ℂ B B' →ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  Algebra.TensorProduct.lift ((leftHom a b).comp B.val) ((rightHom a b).comp B'.val)
    (fun x y => leftOp_commute_rightOp (x : Module.End ℂ (ZMod a → ℂ)) (y : Module.End ℂ (ZMod b → ℂ)))

/-- **0c.** S ⊗ T ↦ L(S)·R(T)。 -/
theorem tensLiftGen_tmul {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) (S : B) (T : B') :
    tensLiftGen B B' (S ⊗ₜ[ℂ] T) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) * rightOp a (T : Module.End ℂ (ZMod b → ℂ)) :=
  Algebra.TensorProduct.lift_tmul _ _ _ S T

/-- **0d.** 像 = L(B) ⊔ R(B′)。 -/
theorem range_tensLiftGen {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    (tensLiftGen B B').range = B.map (leftHom a b) ⊔ B'.map (rightHom a b) := by
  apply le_antisymm
  · intro y hmem
    obtain ⟨z, rfl⟩ := (AlgHom.mem_range _).mp hmem
    clear hmem
    induction z using TensorProduct.inductionOn with
    | tmul S T =>
      rw [tensLiftGen_tmul]
      exact Subalgebra.mul_mem _
        ((le_sup_left : B.map (leftHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨S.1, S.2, rfl⟩))
        ((le_sup_right : B'.map (rightHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨T.1, T.2, rfl⟩))
    | add x y hx hy =>
      rw [map_add]
      exact Subalgebra.add_mem _ hx hy
  · refine sup_le ?_ ?_
    · intro y hmem
      obtain ⟨S, hS, rfl⟩ := Subalgebra.mem_map.mp hmem
      refine (AlgHom.mem_range _).mpr ⟨⟨S, hS⟩ ⊗ₜ[ℂ] 1, ?_⟩
      rw [tensLiftGen_tmul]
      show leftOp b S * rightHom a b 1 = leftHom a b S
      rw [map_one, mul_one]
      rfl
    · intro y hmem
      obtain ⟨T, hT, rfl⟩ := Subalgebra.mem_map.mp hmem
      refine (AlgHom.mem_range _).mpr ⟨1 ⊗ₜ[ℂ] ⟨T, hT⟩, ?_⟩
      rw [tensLiftGen_tmul]
      show leftHom a b 1 * rightOp a T = rightHom a b T
      rw [map_one, one_mul]
      rfl

/-- **0e.** dim B ⊗ B′ = dim B·dim B′。 -/
theorem finrank_tensorGen {a b : ℕ} (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    Module.finrank ℂ (TensorProduct ℂ B B') = Module.finrank ℂ B * Module.finrank ℂ B' := by
  have h1 : @Module.Free ℂ ↥B _ (AddSubmonoidClass.toAddCommMonoid B) Algebra.toModule :=
    Module.Free.of_divisionRing ℂ ↥B
  have h2 : @Module.Free ℂ ↥B' _ (AddSubmonoidClass.toAddCommMonoid B') Algebra.toModule :=
    Module.Free.of_divisionRing ℂ ↥B'
  rw [Module.finrank_tensorProduct]

/-- 部分代数 B を（Mathlib の既定のインスタンスの）部分空間として見たもの。 -/
noncomputable def subalgSpan {X : Type*} (B : Subalgebra ℂ (Module.End ℂ (X → ℂ))) :
    Submodule ℂ (Module.End ℂ (X → ℂ)) where
  carrier := B
  add_mem' hx hy := B.add_mem hx hy
  zero_mem' := B.zero_mem
  smul_mem' c _ hx := B.smul_mem hx c

/-- **0f.** subalgSpan B の元は B の元。 -/
theorem mem_subalgSpan {X : Type*} (B : Subalgebra ℂ (Module.End ℂ (X → ℂ))) (T : Module.End ℂ (X → ℂ)) :
    T ∈ subalgSpan B ↔ T ∈ B := Iff.rfl

/-- subalgSpan B ≅ B（線形同型、元はそのまま）。 -/
noncomputable def subalgSpanEquiv {X : Type*} (B : Subalgebra ℂ (Module.End ℂ (X → ℂ))) :
    subalgSpan B ≃ₗ[ℂ] B where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **0g.** dim subalgSpan B = dim B。 -/
theorem finrank_subalgSpan {X : Type*} (B : Subalgebra ℂ (Module.End ℂ (X → ℂ))) :
    Module.finrank ℂ (subalgSpan B) = Module.finrank ℂ B :=
  (subalgSpanEquiv B).finrank_eq

/-- **0h.** B の中に、一次独立な dim B 個の元がある（subalgSpan B の基底）。 -/
theorem exists_linearIndependent_subalg {X : Type*} [Fintype X] (B : Subalgebra ℂ (Module.End ℂ (X → ℂ))) :
    ∃ u : Fin (Module.finrank ℂ B) → Module.End ℂ (X → ℂ), LinearIndependent ℂ u ∧ ∀ i, u i ∈ B := by
  let P := subalgSpan B
  let _ : AddCommGroup ↥P := Module.addCommMonoidToAddCommGroup ℂ
  have hF : Module.Free ℂ ↥P := Module.Free.of_divisionRing ℂ ↥P
  have hFin : Module.Finite ℂ ↥P := Module.Finite.equiv (subalgSpanEquiv B).symm
  let bB := Module.finBasis ℂ ↥P
  have hu : LinearIndependent ℂ (fun i => (bB i : Module.End ℂ (X → ℂ))) :=
    bB.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  rw [← finrank_subalgSpan B]
  exact ⟨fun i => (bB i : Module.End ℂ (X → ℂ)), hu, fun i => (bB i).2⟩

/-- **0i.** dim B·dim B′ ≤ dim (L(B) ⊔ R(B′))（0b と 0h）。 -/
theorem finrank_mul_le_finrank_sup {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    Module.finrank ℂ B * Module.finrank ℂ B' ≤
      Module.finrank ℂ ↥(B.map (leftHom a b) ⊔ B'.map (rightHom a b)) := by
  obtain ⟨u, hu, huB⟩ := exists_linearIndependent_subalg B
  obtain ⟨v, hv, hvB⟩ := exists_linearIndependent_subalg B'
  have hw := linearIndependent_leftOp_mul_rightOp hu hv
  have hspan : Submodule.span ℂ (Set.range (fun p : Fin (Module.finrank ℂ B) × Fin (Module.finrank ℂ B') =>
      leftOp b (u p.1) * rightOp a (v p.2))) ≤ subalgSpan (B.map (leftHom a b) ⊔ B'.map (rightHom a b)) := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact Subalgebra.mul_mem _
      ((le_sup_left : B.map (leftHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨u p.1, huB p.1, rfl⟩))
      ((le_sup_right : B'.map (rightHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨v p.2, hvB p.2, rfl⟩))
  have h1 := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hw, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, finrank_subalgSpan] at h1
  exact h1

/-- **0j.** dim (L(B) ⊔ R(B′)) = dim B·dim B′（≥ は 0i、≤ は 0d と 0e）。 -/
theorem finrank_sup_map {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    Module.finrank ℂ ↥(B.map (leftHom a b) ⊔ B'.map (rightHom a b)) = Module.finrank ℂ B * Module.finrank ℂ B' := by
  refine le_antisymm ?_ (finrank_mul_le_finrank_sup B B')
  let _ : AddCommGroup (TensorProduct ℂ B B') := Module.addCommMonoidToAddCommGroup ℂ
  rw [← range_tensLiftGen B B', ← finrank_tensorGen B B']
  exact LinearMap.finrank_le_finrank_of_surjective (f := (tensLiftGen B B').rangeRestrict.toLinearMap)
    (AlgHom.rangeRestrict_surjective _)

/-- **0k.** S ⊗ T ↦ L(S)R(T) は単射（像の次元 = 定義域の次元）。 -/
theorem tensLiftGen_injective {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) : Function.Injective (tensLiftGen B B') := by
  let _ : AddCommGroup (TensorProduct ℂ B B') := Module.addCommMonoidToAddCommGroup ℂ
  have hsurj : Function.Surjective (tensLiftGen B B').rangeRestrict := AlgHom.rangeRestrict_surjective _
  have hfin : Module.finrank ℂ (TensorProduct ℂ B B') = Module.finrank ℂ (tensLiftGen B B').range := by
    rw [finrank_tensorGen, range_tensLiftGen, finrank_sup_map]
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℂ)
    (V := TensorProduct ℂ B B') (V₂ := (tensLiftGen B B').range) hfin
    (f := (tensLiftGen B B').rangeRestrict.toLinearMap)).mpr hsurj
  intro x y h
  exact hinj (Subtype.ext h)

/-- **代数同型** B ⊗ B′ ≅ L(B) ⊔ R(B′)。 -/
noncomputable def tensorSupEquiv {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    TensorProduct ℂ B B' ≃ₐ[ℂ] ↥(B.map (leftHom a b) ⊔ B'.map (rightHom a b)) :=
  (AlgEquiv.ofInjective (tensLiftGen B B') (tensLiftGen_injective B B')).trans
    (Subalgebra.equivOfEq _ _ (range_tensLiftGen B B'))

/-- **0l.** その値：S ⊗ T ↦ L(S)·R(T)。 -/
theorem tensorSupEquiv_tmul {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) (S : B) (T : B') :
    (tensorSupEquiv B B' (S ⊗ₜ[ℂ] T) : Module.End ℂ (ZMod a × ZMod b → ℂ)) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) * rightOp a (T : Module.End ℂ (ZMod b → ℂ)) := by
  simp only [tensorSupEquiv, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply, AlgEquiv.ofInjective_apply]
  exact tensLiftGen_tmul B B' S T

/-- **0m.** dim C(X) = dim X（X は End(ℂ^{ℤ/ab}) の任意の部分代数）。 -/
theorem finrank_map_crtConj_gen {a b : ℕ} (hab : Nat.Coprime a b)
    (X : Subalgebra ℂ (Module.End ℂ (ZMod (a * b) → ℂ))) :
    Module.finrank ℂ ↥(X.map (crtConj hab).toAlgHom) = Module.finrank ℂ X :=
  ((Subalgebra.equivMapOfInjective X (crtConj hab).toAlgHom (crtConj hab).injective).toLinearEquiv.finrank_eq).symm

/-- **0n.** C(T) ∈ C(X) ⇔ T ∈ X。 -/
theorem mem_map_crtConj_iff {a b : ℕ} (hab : Nat.Coprime a b) (X : Subalgebra ℂ (Module.End ℂ (ZMod (a * b) → ℂ)))
    (T : Module.End ℂ (ZMod (a * b) → ℂ)) : crtConj hab T ∈ X.map (crtConj hab).toAlgHom ↔ T ∈ X := by
  constructor
  · intro h
    obtain ⟨T', hT', he⟩ := Subalgebra.mem_map.mp h
    have hTT : T' = T := (crtConj hab).injective he
    rw [← hTT]
    exact hT'
  · intro h
    exact Subalgebra.mem_map.mpr ⟨T, h, rfl⟩

/-- **代数同型** B ⊗ B′ ≅ X（gcd(a, b) = 1、C(X) = L(B) ⊔ R(B′) のとき）。 -/
noncomputable def crtTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ))) (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ)))
    (X : Subalgebra ℂ (Module.End ℂ (ZMod (a * b) → ℂ)))
    (h : X.map (crtConj hab).toAlgHom = B.map (leftHom a b) ⊔ B'.map (rightHom a b)) :
    TensorProduct ℂ B B' ≃ₐ[ℂ] X :=
  ((tensorSupEquiv B B').trans (Subalgebra.equivOfEq _ _ h.symm)).trans
    (Subalgebra.equivMapOfInjective X (crtConj hab).toAlgHom (crtConj hab).injective).symm

/-- **0o.** その値：C(Θ(S ⊗ T)) = L(S)·R(T)。 -/
theorem crtConj_crtTensorEquiv_tmul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ))) (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ)))
    (X : Subalgebra ℂ (Module.End ℂ (ZMod (a * b) → ℂ)))
    (h : X.map (crtConj hab).toAlgHom = B.map (leftHom a b) ⊔ B'.map (rightHom a b)) (S : B) (T : B') :
    crtConj hab (crtTensorEquiv hab B B' X h (S ⊗ₜ[ℂ] T) : Module.End ℂ (ZMod (a * b) → ℂ)) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) * rightOp a (T : Module.End ℂ (ZMod b → ℂ)) := by
  set e := Subalgebra.equivMapOfInjective X (crtConj hab).toAlgHom (crtConj hab).injective
  set w := ((tensorSupEquiv B B').trans (Subalgebra.equivOfEq _ _ h.symm)) (S ⊗ₜ[ℂ] T)
  have h1 : ((e (e.symm w)) : Module.End ℂ (ZMod a × ZMod b → ℂ)) =
      (crtConj hab).toAlgHom (e.symm w : Module.End ℂ (ZMod (a * b) → ℂ)) :=
    Subalgebra.coe_equivMapOfInjective_apply _ _ _ _
  rw [AlgEquiv.apply_symm_apply] at h1
  have h2 : (w : Module.End ℂ (ZMod a × ZMod b → ℂ)) = leftOp b S * rightOp a T := by
    simp only [w, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply]
    exact tensorSupEquiv_tmul B B' S T
  show crtConj hab ((e.symm w : X) : Module.End ℂ (ZMod (a * b) → ℂ)) = _
  rw [← h2, h1]
  rfl

/-! ### 1. Part 226 によらない次元の乗法性 -/

/-- **1a.** Part 228 の tensLift は tensLiftGen の特別な場合（定義から）。 -/
theorem tensLift_eq_tensLiftGen (a b : ℕ) [NeZero a] [NeZero b] :
    tensLift a b = tensLiftGen (shellAlg a) (shellAlg b) := rfl

/-- **1b.** Part 228 の tensLift の単射性を、Part 226 の次元の式を使わずに示したもの（0k）。 -/
theorem tensLift_injective_gen {a b : ℕ} [NeZero a] [NeZero b] : Function.Injective (tensLift a b) :=
  tensLiftGen_injective (shellAlg a) (shellAlg b)

/-- **1c. dim A_{ab} = dim A_a·dim A_b**（gcd(a, b) = 1。Part 228 の map_crtConj_shellAlg と 0j・0m から。Part 226 の finrank_shellAlg_mul と別の証明）。 -/
theorem finrank_shellAlg_mul_of_crt {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ (shellAlg (a * b)) = Module.finrank ℂ (shellAlg a) * Module.finrank ℂ (shellAlg b) := by
  rw [← finrank_map_crtConj_gen hab (shellAlg (a * b)), map_crtConj_shellAlg hab, finrank_sup_map]

/-! ### 2. 可換子 A′ の分解 -/

/-- **2a.** X が部分代数 B₁ と B₂ のすべての元と可換なら、B₁ ⊔ B₂ のすべての元と可換（中心化代数による）。 -/
theorem commute_of_mem_sup {A : Type*} [Ring A] [Algebra ℂ A] (X : A) {B₁ B₂ : Subalgebra ℂ A}
    (h₁ : ∀ Y ∈ B₁, Commute X Y) (h₂ : ∀ Y ∈ B₂, Commute X Y) : ∀ Y ∈ B₁ ⊔ B₂, Commute X Y := by
  have hle : B₁ ⊔ B₂ ≤ Subalgebra.centralizer ℂ {X} := by
    refine sup_le (fun Y hY => ?_) (fun Y hY => ?_)
    · rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact (h₁ Y hY).eq
    · rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact (h₂ Y hY).eq
  intro Y hY
  exact (Subalgebra.mem_centralizer_iff ℂ).mp (hle hY) X (Set.mem_singleton X)

/-- **2b.** C(T) と C(S) が可換 ⇔ T と S が可換。 -/
theorem crtConj_commute_iff {a b : ℕ} (hab : Nat.Coprime a b) (T S : Module.End ℂ (ZMod (a * b) → ℂ)) :
    Commute (crtConj hab T) (crtConj hab S) ↔ Commute T S := by
  constructor
  · intro h
    have h' := h.map (crtConj hab).symm
    rwa [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply] at h'
  · intro h
    exact h.map (crtConj hab)

/-- **2c.** T ∈ A′_{ab} ⇔ C(T) が L(A_a) ⊔ R(A_b) のすべての元と可換（Part 228 の C(A_{ab}) = L(A_a) ⊔ R(A_b)）。 -/
theorem mem_fullComm_mul_iff {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (T : Module.End ℂ (ZMod (a * b) → ℂ)) :
    T ∈ fullComm (a * b) ↔ ∀ Y ∈ (shellAlg a).map (leftHom a b) ⊔ (shellAlg b).map (rightHom a b),
      Commute (crtConj hab T) Y := by
  rw [mem_fullComm_iff_commute]
  constructor
  · intro h Y hY
    rw [← map_crtConj_shellAlg hab] at hY
    obtain ⟨S, hS, rfl⟩ := Subalgebra.mem_map.mp hY
    exact (crtConj_commute_iff hab T S).mpr (h S hS)
  · intro h S hS
    exact (crtConj_commute_iff hab T S).mp (h _ ((mem_shellAlg_mul_iff hab S).mp hS))

/-- **2d.** S ∈ A′_a なら C⁻¹(L(S)) ∈ A′_{ab}（L(S) は L(A_a) とも R(A_b) とも可換）。 -/
theorem symm_leftOp_mem_fullComm {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    {S : Module.End ℂ (ZMod a → ℂ)} (hS : S ∈ fullComm a) :
    (crtConj hab).symm (leftOp b S) ∈ fullComm (a * b) := by
  rw [mem_fullComm_mul_iff hab, AlgEquiv.apply_symm_apply]
  refine commute_of_mem_sup _ (fun Y hY => ?_) (fun Y hY => ?_)
  · obtain ⟨S', hS', rfl⟩ := Subalgebra.mem_map.mp hY
    exact ((mem_fullComm_iff_commute a S).mp hS S' hS').map (leftHom a b)
  · obtain ⟨T', -, rfl⟩ := Subalgebra.mem_map.mp hY
    exact leftOp_commute_rightOp S T'

/-- **2e.** T ∈ A′_b なら C⁻¹(R(T)) ∈ A′_{ab}。 -/
theorem symm_rightOp_mem_fullComm {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    {T : Module.End ℂ (ZMod b → ℂ)} (hT : T ∈ fullComm b) :
    (crtConj hab).symm (rightOp a T) ∈ fullComm (a * b) := by
  rw [mem_fullComm_mul_iff hab, AlgEquiv.apply_symm_apply]
  refine commute_of_mem_sup _ (fun Y hY => ?_) (fun Y hY => ?_)
  · obtain ⟨S', -, rfl⟩ := Subalgebra.mem_map.mp hY
    exact (leftOp_commute_rightOp S' T).symm
  · obtain ⟨T', hT', rfl⟩ := Subalgebra.mem_map.mp hY
    exact ((mem_fullComm_iff_commute b T).mp hT T' hT').map (rightHom a b)

/-- **2f.** L(A′_a) ⊆ C(A′_{ab})。 -/
theorem map_leftHom_fullComm_le {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (fullCommAlg a).map (leftHom a b) ≤ (fullCommAlg (a * b)).map (crtConj hab).toAlgHom := by
  intro Y hY
  obtain ⟨S, hS, rfl⟩ := Subalgebra.mem_map.mp hY
  refine Subalgebra.mem_map.mpr ⟨(crtConj hab).symm (leftOp b S),
    (mem_fullCommAlg _ _).mpr (symm_leftOp_mem_fullComm hab ((mem_fullCommAlg a S).mp hS)), ?_⟩
  show crtConj hab ((crtConj hab).symm (leftOp b S)) = leftHom a b S
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- **2g.** R(A′_b) ⊆ C(A′_{ab})。 -/
theorem map_rightHom_fullComm_le {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (fullCommAlg b).map (rightHom a b) ≤ (fullCommAlg (a * b)).map (crtConj hab).toAlgHom := by
  intro Y hY
  obtain ⟨T, hT, rfl⟩ := Subalgebra.mem_map.mp hY
  refine Subalgebra.mem_map.mpr ⟨(crtConj hab).symm (rightOp a T),
    (mem_fullCommAlg _ _).mpr (symm_rightOp_mem_fullComm hab ((mem_fullCommAlg b T).mp hT)), ?_⟩
  show crtConj hab ((crtConj hab).symm (rightOp a T)) = rightHom a b T
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- **2h.** dim fullCommAlg N = dim fullComm N。 -/
theorem finrank_fullCommAlg_eq (N : ℕ) [NeZero N] :
    Module.finrank ℂ (fullCommAlg N) = Module.finrank ℂ (fullComm N) :=
  (fullCommAlgLinearEquiv N).finrank_eq

/-- **2i. C(A′_{ab}) = L(A′_a) ⊔ R(A′_b)**（⊇ は 2f・2g、次元は 0j と Part 226 の finrank_fullComm_mul）。 -/
theorem map_crtConj_fullComm {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (fullCommAlg (a * b)).map (crtConj hab).toAlgHom =
      (fullCommAlg a).map (leftHom a b) ⊔ (fullCommAlg b).map (rightHom a b) := by
  symm
  refine Subalgebra.eq_of_le_of_finrank_eq (sup_le (map_leftHom_fullComm_le hab) (map_rightHom_fullComm_le hab)) ?_
  rw [finrank_sup_map, finrank_map_crtConj_gen, finrank_fullCommAlg_eq, finrank_fullCommAlg_eq,
    finrank_fullCommAlg_eq, PAG.Part230.finrank_fullComm_mul hab]

/-- **2j.** T ∈ A′_{ab} ⇔ C(T) ∈ L(A′_a) ⊔ R(A′_b)。 -/
theorem mem_fullComm_mul_iff_sup {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (T : Module.End ℂ (ZMod (a * b) → ℂ)) :
    T ∈ fullComm (a * b) ↔ crtConj hab T ∈ (fullCommAlg a).map (leftHom a b) ⊔ (fullCommAlg b).map (rightHom a b) := by
  rw [← map_crtConj_fullComm hab, mem_map_crtConj_iff, mem_fullCommAlg]

/-- **代数同型** A′_a ⊗ A′_b ≅ A′_{ab}（gcd(a, b) = 1）。 -/
noncomputable def fullCommTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    TensorProduct ℂ (fullCommAlg a) (fullCommAlg b) ≃ₐ[ℂ] fullCommAlg (a * b) :=
  crtTensorEquiv hab _ _ _ (map_crtConj_fullComm hab)

/-- **2k.** その値：C(Θ′(S ⊗ T)) = L(S)·R(T)。 -/
theorem crtConj_fullCommTensorEquiv_tmul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (S : fullCommAlg a) (T : fullCommAlg b) :
    crtConj hab (fullCommTensorEquiv hab (S ⊗ₜ[ℂ] T) : Module.End ℂ (ZMod (a * b) → ℂ)) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) * rightOp a (T : Module.End ℂ (ZMod b → ℂ)) :=
  crtConj_crtTensorEquiv_tmul hab _ _ _ _ S T

/-! ### 3. 中心 Z の分解 -/

/-- **3a.** Z ∈ Z_N ⇔ Z ∈ A_N かつ Z ∈ A′_N（Part 225 の mem_fullCommCenter_iff）。 -/
theorem mem_centerAlg_iff_and (N : ℕ) [NeZero N] (Z : Module.End ℂ (ZMod N → ℂ)) :
    Z ∈ centerAlg N ↔ Z ∈ shellAlg N ∧ Z ∈ fullComm N := by
  rw [mem_centerAlg, mem_fullCommCenter_iff]

/-- **3b.** Z ∈ Z_a なら C⁻¹(L(Z)) ∈ Z_{ab}。 -/
theorem symm_leftOp_mem_center {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    {Z : Module.End ℂ (ZMod a → ℂ)} (hZ : Z ∈ centerAlg a) :
    (crtConj hab).symm (leftOp b Z) ∈ centerAlg (a * b) := by
  rw [mem_centerAlg_iff_and] at hZ ⊢
  refine ⟨(mem_shellAlg_mul_iff hab _).mpr ?_, symm_leftOp_mem_fullComm hab hZ.2⟩
  rw [AlgEquiv.apply_symm_apply]
  exact (le_sup_left : (shellAlg a).map (leftHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨Z, hZ.1, rfl⟩)

/-- **3c.** Z ∈ Z_b なら C⁻¹(R(Z)) ∈ Z_{ab}。 -/
theorem symm_rightOp_mem_center {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    {Z : Module.End ℂ (ZMod b → ℂ)} (hZ : Z ∈ centerAlg b) :
    (crtConj hab).symm (rightOp a Z) ∈ centerAlg (a * b) := by
  rw [mem_centerAlg_iff_and] at hZ ⊢
  refine ⟨(mem_shellAlg_mul_iff hab _).mpr ?_, symm_rightOp_mem_fullComm hab hZ.2⟩
  rw [AlgEquiv.apply_symm_apply]
  exact (le_sup_right : (shellAlg b).map (rightHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨Z, hZ.1, rfl⟩)

/-- **3d.** L(Z_a) ⊆ C(Z_{ab})。 -/
theorem map_leftHom_center_le {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (centerAlg a).map (leftHom a b) ≤ (centerAlg (a * b)).map (crtConj hab).toAlgHom := by
  intro Y hY
  obtain ⟨Z, hZ, rfl⟩ := Subalgebra.mem_map.mp hY
  refine Subalgebra.mem_map.mpr ⟨(crtConj hab).symm (leftOp b Z), symm_leftOp_mem_center hab hZ, ?_⟩
  show crtConj hab ((crtConj hab).symm (leftOp b Z)) = leftHom a b Z
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- **3e.** R(Z_b) ⊆ C(Z_{ab})。 -/
theorem map_rightHom_center_le {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (centerAlg b).map (rightHom a b) ≤ (centerAlg (a * b)).map (crtConj hab).toAlgHom := by
  intro Y hY
  obtain ⟨Z, hZ, rfl⟩ := Subalgebra.mem_map.mp hY
  refine Subalgebra.mem_map.mpr ⟨(crtConj hab).symm (rightOp a Z), symm_rightOp_mem_center hab hZ, ?_⟩
  show crtConj hab ((crtConj hab).symm (rightOp a Z)) = rightHom a b Z
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- **3f.** dim centerAlg N = dim fullCommCenter N。 -/
theorem finrank_centerAlg_eq (N : ℕ) [NeZero N] :
    Module.finrank ℂ (centerAlg N) = Module.finrank ℂ (fullCommCenter N) := by
  rw [← Subalgebra.finrank_toSubmodule]
  unfold centerAlg
  rw [Submodule.toSubalgebra_toSubmodule]

/-- **3g. C(Z_{ab}) = L(Z_a) ⊔ R(Z_b)**（次元は 0j と Part 226 の finrank_fullCommCenter_mul）。 -/
theorem map_crtConj_center {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (centerAlg (a * b)).map (crtConj hab).toAlgHom =
      (centerAlg a).map (leftHom a b) ⊔ (centerAlg b).map (rightHom a b) := by
  symm
  refine Subalgebra.eq_of_le_of_finrank_eq (sup_le (map_leftHom_center_le hab) (map_rightHom_center_le hab)) ?_
  rw [finrank_sup_map, finrank_map_crtConj_gen, finrank_centerAlg_eq, finrank_centerAlg_eq,
    finrank_centerAlg_eq, PAG.Part230.finrank_fullCommCenter_mul hab]

/-- **3h.** Z ∈ Z_{ab} ⇔ C(Z) ∈ L(Z_a) ⊔ R(Z_b)。 -/
theorem mem_center_mul_iff {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (Z : Module.End ℂ (ZMod (a * b) → ℂ)) :
    Z ∈ centerAlg (a * b) ↔ crtConj hab Z ∈ (centerAlg a).map (leftHom a b) ⊔ (centerAlg b).map (rightHom a b) := by
  rw [← map_crtConj_center hab, mem_map_crtConj_iff]

/-- **代数同型** Z_a ⊗ Z_b ≅ Z_{ab}（gcd(a, b) = 1）。 -/
noncomputable def centerTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    TensorProduct ℂ (centerAlg a) (centerAlg b) ≃ₐ[ℂ] centerAlg (a * b) :=
  crtTensorEquiv hab _ _ _ (map_crtConj_center hab)

/-- **3i.** その値：C(Θ_Z(S ⊗ T)) = L(S)·R(T)。 -/
theorem crtConj_centerTensorEquiv_tmul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (S : centerAlg a) (T : centerAlg b) :
    crtConj hab (centerTensorEquiv hab (S ⊗ₜ[ℂ] T) : Module.End ℂ (ZMod (a * b) → ℂ)) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) * rightOp a (T : Module.End ℂ (ZMod b → ℂ)) :=
  crtConj_crtTensorEquiv_tmul hab _ _ _ _ S T

/-! ### 4. 番号の集合 S の分解 -/

/-- **4a.** rad(d₁) ∣ c₁、rad(d₂) ∣ c₂ なら rad(d₁d₂) ∣ c₁c₂。 -/
theorem radDvd_mul {d₁ c₁ d₂ c₂ : ℕ} (h₁ : RadDvd d₁ c₁) (h₂ : RadDvd d₂ c₂) : RadDvd (d₁ * d₂) (c₁ * c₂) := by
  intro q hq hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · exact dvd_mul_of_dvd_left (h₁ q hq h) c₂
  · exact dvd_mul_of_dvd_right (h₂ q hq h) c₁

/-- **4b.** rad(d) ∣ c なら rad(gcd(d, a)) ∣ gcd(c, a)。 -/
theorem radDvd_gcd {d c : ℕ} (h : RadDvd d c) (a : ℕ) : RadDvd (Nat.gcd d a) (Nat.gcd c a) := by
  intro q hq hqd
  exact Nat.dvd_gcd (h q hq (dvd_trans hqd (Nat.gcd_dvd_left d a))) (dvd_trans hqd (Nat.gcd_dvd_right d a))

/-- **4c.** (c, d) ∈ S(N) ⇔ c ∣ N、N ≠ 0、m(c) > 0、d ∣ N/c、rad(d) ∣ c。 -/
theorem mem_centerIdx_iff_dvd (N c d : ℕ) : (⟨c, d⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx N ↔
    c ∣ N ∧ N ≠ 0 ∧ 0 < primCount c ∧ d ∣ N / c ∧ RadDvd d c := by
  rw [mem_centerIdx, Nat.mem_divisors, mem_layerIdx, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, ⟨h4, -⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨h1, h2⟩, h3, ⟨h4, ?_⟩, h5⟩
    have hNpos : 0 < N := Nat.pos_of_ne_zero h2
    exact (Nat.div_pos (Nat.le_of_dvd hNpos h1) (Nat.pos_of_dvd_of_pos h1 hNpos)).ne'

/-- 番号の積 (c_a, d_a)·(c_b, d_b) = (c_a c_b, d_a d_b)。 -/
def idxMul (p q : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨p.1 * q.1, p.2 * q.2⟩

/-- 番号の分解 (c, d) ↦ ((gcd(c, a), gcd(d, a)), (gcd(c, b), gcd(d, b)))。 -/
def idxSplit (a b : ℕ) (r : Σ _ : ℕ, ℕ) : (Σ _ : ℕ, ℕ) × (Σ _ : ℕ, ℕ) :=
  (⟨Nat.gcd r.1 a, Nat.gcd r.2 a⟩, ⟨Nat.gcd r.1 b, Nat.gcd r.2 b⟩)

/-- **4d.** gcd(a, b) = 1、x ∣ a、y ∣ b なら gcd(xy, a) = x。 -/
theorem gcd_mul_left_of_dvd {a b x y : ℕ} (hab : Nat.Coprime a b) (hx : x ∣ a) (hy : y ∣ b) :
    Nat.gcd (x * y) a = x := by
  rw [Nat.Coprime.gcd_mul_right_cancel x (Nat.Coprime.coprime_dvd_left hy hab.symm), Nat.gcd_eq_left hx]

/-- **4e.** 同じく gcd(xy, b) = y。 -/
theorem gcd_mul_right_of_dvd {a b x y : ℕ} (hab : Nat.Coprime a b) (hx : x ∣ a) (hy : y ∣ b) :
    Nat.gcd (x * y) b = y := by
  rw [mul_comm, Nat.Coprime.gcd_mul_right_cancel y (Nat.Coprime.coprime_dvd_left hx hab), Nat.gcd_eq_left hy]

/-- **4f.** n ∣ ab（gcd(a, b) = 1）なら n = gcd(n, a)·gcd(n, b)。 -/
theorem eq_gcd_mul_gcd {a b n : ℕ} (hab : Nat.Coprime a b) (hn : n ∣ a * b) : n = Nat.gcd n a * Nat.gcd n b := by
  rw [← Nat.Coprime.gcd_mul n hab, Nat.gcd_eq_left hn]

/-- **4g.** p ∈ S(a)、q ∈ S(b) なら p·q ∈ S(ab)（m の乗法性は Part 226 の primCount_mul）。 -/
theorem idxMul_mem_centerIdx {a b : ℕ} (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b) :
    idxMul ⟨ca, da⟩ ⟨cb, db⟩ ∈ centerIdx (a * b) := by
  rw [mem_centerIdx_iff_dvd] at hp hq
  obtain ⟨hca, ha0, hma, hda, hra⟩ := hp
  obtain ⟨hcb, hb0, hmb, hdb, hrb⟩ := hq
  show (⟨ca * cb, da * db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx (a * b)
  rw [mem_centerIdx_iff_dvd]
  have hcop : Nat.Coprime ca cb := Nat.Coprime.coprime_dvd_right hcb (Nat.Coprime.coprime_dvd_left hca hab)
  refine ⟨Nat.mul_dvd_mul hca hcb, mul_ne_zero ha0 hb0, ?_, ?_, radDvd_mul hra hrb⟩
  · rw [primCount_mul hcop]
    exact Nat.mul_pos hma hmb
  · rw [← Nat.div_mul_div_comm hca hcb]
    exact Nat.mul_dvd_mul hda hdb

/-- **4h.** 分解は積の逆：idxSplit(p·q) = (p, q)。 -/
theorem idxSplit_idxMul {a b : ℕ} (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b) :
    idxSplit a b (idxMul ⟨ca, da⟩ ⟨cb, db⟩) = (⟨ca, da⟩, ⟨cb, db⟩) := by
  rw [mem_centerIdx_iff_dvd] at hp hq
  obtain ⟨hca, -, -, hda, -⟩ := hp
  obtain ⟨hcb, -, -, hdb, -⟩ := hq
  have hda' : da ∣ a := dvd_trans hda (Nat.div_dvd_of_dvd hca)
  have hdb' : db ∣ b := dvd_trans hdb (Nat.div_dvd_of_dvd hcb)
  show ((⟨Nat.gcd (ca * cb) a, Nat.gcd (da * db) a⟩ : Σ _ : ℕ, ℕ),
      (⟨Nat.gcd (ca * cb) b, Nat.gcd (da * db) b⟩ : Σ _ : ℕ, ℕ)) = (⟨ca, da⟩, ⟨cb, db⟩)
  rw [gcd_mul_left_of_dvd hab hca hcb, gcd_mul_left_of_dvd hab hda' hdb', gcd_mul_right_of_dvd hab hca hcb,
    gcd_mul_right_of_dvd hab hda' hdb']

/-- **4i.** (c, d) ∈ S(ab) なら (gcd(c, a), gcd(d, a)) ∈ S(a)、(gcd(c, b), gcd(d, b)) ∈ S(b)。 -/
theorem idxSplit_mem {a b : ℕ} (hab : Nat.Coprime a b) {c d : ℕ} (hr : (⟨c, d⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx (a * b)) :
    (idxSplit a b ⟨c, d⟩).1 ∈ centerIdx a ∧ (idxSplit a b ⟨c, d⟩).2 ∈ centerIdx b := by
  rw [mem_centerIdx_iff_dvd] at hr
  obtain ⟨hc, hN, hm, hd, hrad⟩ := hr
  have ha0 : a ≠ 0 := fun h => hN (by rw [h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hN (by rw [h, mul_zero])
  have hceq := eq_gcd_mul_gcd hab hc
  have hcop : Nat.Coprime (Nat.gcd c a) (Nat.gcd c b) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right c b) (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right c a) hab)
  have hm' : 0 < primCount (Nat.gcd c a) * primCount (Nat.gcd c b) := by
    rw [← primCount_mul hcop, ← hceq]
    exact hm
  have hma : 0 < primCount (Nat.gcd c a) := Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hm'; exact lt_irrefl 0 hm')
  have hmb : 0 < primCount (Nat.gcd c b) := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hm'; exact lt_irrefl 0 hm')
  have hL : a * b / c = (a / Nat.gcd c a) * (b / Nat.gcd c b) := by
    conv_lhs => rw [hceq]
    exact (Nat.div_mul_div_comm (Nat.gcd_dvd_right c a) (Nat.gcd_dvd_right c b)).symm
  have hcopa : Nat.Coprime (b / Nat.gcd c b) a :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right c b)) hab.symm
  have hcopb : Nat.Coprime (a / Nat.gcd c a) b :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right c a)) hab
  refine ⟨?_, ?_⟩
  · show (⟨Nat.gcd c a, Nat.gcd d a⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a
    rw [mem_centerIdx_iff_dvd]
    refine ⟨Nat.gcd_dvd_right c a, ha0, hma, ?_, radDvd_gcd hrad a⟩
    have h1 : Nat.gcd d a ∣ Nat.gcd (a * b / c) a := Nat.gcd_dvd_gcd_of_dvd_left a hd
    rwa [hL, Nat.Coprime.gcd_mul_right_cancel _ hcopa,
      Nat.gcd_eq_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right c a))] at h1
  · show (⟨Nat.gcd c b, Nat.gcd d b⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b
    rw [mem_centerIdx_iff_dvd]
    refine ⟨Nat.gcd_dvd_right c b, hb0, hmb, ?_, radDvd_gcd hrad b⟩
    have h1 : Nat.gcd d b ∣ Nat.gcd (a * b / c) b := Nat.gcd_dvd_gcd_of_dvd_left b hd
    rwa [hL, mul_comm, Nat.Coprime.gcd_mul_right_cancel _ hcopb,
      Nat.gcd_eq_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right c b))] at h1

/-- **4j.** 積は分解の逆：(c, d) ∈ S(ab) なら idxSplit の 2 つの積は (c, d)。 -/
theorem idxMul_idxSplit {a b : ℕ} (hab : Nat.Coprime a b) {c d : ℕ}
    (hr : (⟨c, d⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx (a * b)) :
    idxMul (idxSplit a b ⟨c, d⟩).1 (idxSplit a b ⟨c, d⟩).2 = ⟨c, d⟩ := by
  rw [mem_centerIdx_iff_dvd] at hr
  obtain ⟨hc, -, -, hd, -⟩ := hr
  have hd' : d ∣ a * b := dvd_trans hd (Nat.div_dvd_of_dvd hc)
  show (⟨Nat.gcd c a * Nat.gcd c b, Nat.gcd d a * Nat.gcd d b⟩ : Σ _ : ℕ, ℕ) = ⟨c, d⟩
  rw [← eq_gcd_mul_gcd hab hc, ← eq_gcd_mul_gcd hab hd']

/-- **4k. #S(ab) = #S(a)·#S(b)**（4g〜4j の全単射）。 -/
theorem card_centerIdx_mul {a b : ℕ} (hab : Nat.Coprime a b) :
    (centerIdx (a * b)).card = (centerIdx a).card * (centerIdx b).card := by
  rw [← Finset.card_product]
  symm
  refine Finset.card_nbij' (fun pq => idxMul pq.1 pq.2) (idxSplit a b) ?_ ?_ ?_ ?_
  · rintro ⟨⟨ca, da⟩, ⟨cb, db⟩⟩ h
    rw [Finset.mem_coe, Finset.mem_product] at h
    exact idxMul_mem_centerIdx hab h.1 h.2
  · rintro ⟨c, d⟩ h
    rw [Finset.mem_coe] at h
    rw [Finset.mem_coe, Finset.mem_product]
    exact idxSplit_mem hab h
  · rintro ⟨⟨ca, da⟩, ⟨cb, db⟩⟩ h
    rw [Finset.mem_coe, Finset.mem_product] at h
    exact idxSplit_idxMul hab h.1 h.2
  · rintro ⟨c, d⟩ h
    rw [Finset.mem_coe] at h
    exact idxMul_idxSplit hab h

/-- **4l.** r ∈ S(ab) ⇔ r = p·q（p ∈ S(a)、q ∈ S(b)）。 -/
theorem mem_centerIdx_mul_iff {a b : ℕ} (hab : Nat.Coprime a b) (r : Σ _ : ℕ, ℕ) :
    r ∈ centerIdx (a * b) ↔ ∃ p ∈ centerIdx a, ∃ q ∈ centerIdx b, idxMul p q = r := by
  constructor
  · intro hr
    obtain ⟨c, d⟩ := r
    exact ⟨_, (idxSplit_mem hab hr).1, _, (idxSplit_mem hab hr).2, idxMul_idxSplit hab hr⟩
  · rintro ⟨⟨ca, da⟩, hp, ⟨cb, db⟩, hq, rfl⟩
    exact idxMul_mem_centerIdx hab hp hq

/-- **4m.** m(c_a c_b) = m(c_a)·m(c_b)。 -/
theorem primCount_idxMul {a b : ℕ} (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b) :
    primCount (ca * cb) = primCount ca * primCount cb := by
  rw [mem_centerIdx_iff_dvd] at hp hq
  exact primCount_mul (Nat.Coprime.coprime_dvd_right hq.1 (Nat.Coprime.coprime_dvd_left hp.1 hab))

/-- **4n.** n_(c_a c_b, d_a d_b) = n_(c_a, d_a)·n_(c_b, d_b)（Part 226 の card_layerDivs と prod_primeFactors_mul_of_coprime）。 -/
theorem card_layerDivs_idxMul {a b : ℕ} (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b) :
    (layerDivs (ca * cb) (da * db) (a * b / (ca * cb))).card =
      (layerDivs ca da (a / ca)).card * (layerDivs cb db (b / cb)).card := by
  have hmem : da * db ∈ layerIdx (ca * cb) (a * b / (ca * cb)) :=
    ((mem_centerIdx _ _).mp (idxMul_mem_centerIdx hab hp hq)).2.2
  have hmemA : da ∈ layerIdx ca (a / ca) := ((mem_centerIdx _ _).mp hp).2.2
  have hmemB : db ∈ layerIdx cb (b / cb) := ((mem_centerIdx _ _).mp hq).2.2
  rw [mem_centerIdx_iff_dvd] at hp hq
  obtain ⟨hca, ha0, -, -, -⟩ := hp
  obtain ⟨hcb, hb0, -, -, -⟩ := hq
  have hLa : a / ca ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hca) (Nat.pos_of_dvd_of_pos hca (Nat.pos_of_ne_zero ha0))).ne'
  have hLb : b / cb ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hcb) (Nat.pos_of_dvd_of_pos hcb (Nat.pos_of_ne_zero hb0))).ne'
  have hL : a * b / (ca * cb) = (a / ca) * (b / cb) := (Nat.div_mul_div_comm hca hcb).symm
  have hLcop : Nat.Coprime (a / ca) (b / cb) :=
    Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hcb) (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hca) hab)
  rw [card_layerDivs (by rw [hL]; exact mul_ne_zero hLa hLb) hmem, card_layerDivs hLa hmemA,
    card_layerDivs hLb hmemB, hL, Finset.prod_filter, Finset.prod_filter, Finset.prod_filter]
  have key := prod_primeFactors_mul_of_coprime hLa hLb hLcop (fun q k => if ¬ q ∣ ca * cb then k + 1 else 1)
  rw [key]
  congr 1
  · refine Finset.prod_congr rfl (fun q hq => ?_)
    have hqp := (Nat.mem_primeFactors.mp hq).1
    have hqa : q ∣ a := dvd_trans (Nat.mem_primeFactors.mp hq).2.1 (Nat.div_dvd_of_dvd hca)
    have hqcb : ¬ q ∣ cb := fun h => by
      have h1 := Nat.dvd_gcd hqa (dvd_trans h hcb)
      rw [Nat.Coprime.gcd_eq_one hab] at h1
      exact hqp.one_lt.ne' (Nat.dvd_one.mp h1)
    have hiff : q ∣ ca * cb ↔ q ∣ ca :=
      ⟨fun h => ((Nat.Prime.dvd_mul hqp).mp h).resolve_right hqcb, fun h => dvd_mul_of_dvd_left h cb⟩
    simp only [hiff]
  · refine Finset.prod_congr rfl (fun q hq => ?_)
    have hqp := (Nat.mem_primeFactors.mp hq).1
    have hqb : q ∣ b := dvd_trans (Nat.mem_primeFactors.mp hq).2.1 (Nat.div_dvd_of_dvd hcb)
    have hqca : ¬ q ∣ ca := fun h => by
      have h1 := Nat.dvd_gcd (dvd_trans h hca) hqb
      rw [Nat.Coprime.gcd_eq_one hab] at h1
      exact hqp.one_lt.ne' (Nat.dvd_one.mp h1)
    have hiff : q ∣ ca * cb ↔ q ∣ cb :=
      ⟨fun h => ((Nat.Prime.dvd_mul hqp).mp h).resolve_left hqca, fun h => dvd_mul_of_dvd_right h ca⟩
    simp only [hiff]

end PAG.Part233

#print axioms PAG.Part233.leftOp_mul_rightOp_apply_prod
#print axioms PAG.Part233.linearIndependent_leftOp_mul_rightOp
#print axioms PAG.Part233.tensLiftGen
#print axioms PAG.Part233.tensLiftGen_tmul
#print axioms PAG.Part233.range_tensLiftGen
#print axioms PAG.Part233.finrank_tensorGen
#print axioms PAG.Part233.subalgSpan
#print axioms PAG.Part233.mem_subalgSpan
#print axioms PAG.Part233.subalgSpanEquiv
#print axioms PAG.Part233.finrank_subalgSpan
#print axioms PAG.Part233.exists_linearIndependent_subalg
#print axioms PAG.Part233.finrank_mul_le_finrank_sup
#print axioms PAG.Part233.finrank_sup_map
#print axioms PAG.Part233.tensLiftGen_injective
#print axioms PAG.Part233.tensorSupEquiv
#print axioms PAG.Part233.tensorSupEquiv_tmul
#print axioms PAG.Part233.finrank_map_crtConj_gen
#print axioms PAG.Part233.mem_map_crtConj_iff
#print axioms PAG.Part233.crtTensorEquiv
#print axioms PAG.Part233.crtConj_crtTensorEquiv_tmul
#print axioms PAG.Part233.tensLift_eq_tensLiftGen
#print axioms PAG.Part233.tensLift_injective_gen
#print axioms PAG.Part233.finrank_shellAlg_mul_of_crt
#print axioms PAG.Part233.commute_of_mem_sup
#print axioms PAG.Part233.crtConj_commute_iff
#print axioms PAG.Part233.mem_fullComm_mul_iff
#print axioms PAG.Part233.symm_leftOp_mem_fullComm
#print axioms PAG.Part233.symm_rightOp_mem_fullComm
#print axioms PAG.Part233.map_leftHom_fullComm_le
#print axioms PAG.Part233.map_rightHom_fullComm_le
#print axioms PAG.Part233.finrank_fullCommAlg_eq
#print axioms PAG.Part233.map_crtConj_fullComm
#print axioms PAG.Part233.mem_fullComm_mul_iff_sup
#print axioms PAG.Part233.fullCommTensorEquiv
#print axioms PAG.Part233.crtConj_fullCommTensorEquiv_tmul
#print axioms PAG.Part233.mem_centerAlg_iff_and
#print axioms PAG.Part233.symm_leftOp_mem_center
#print axioms PAG.Part233.symm_rightOp_mem_center
#print axioms PAG.Part233.map_leftHom_center_le
#print axioms PAG.Part233.map_rightHom_center_le
#print axioms PAG.Part233.finrank_centerAlg_eq
#print axioms PAG.Part233.map_crtConj_center
#print axioms PAG.Part233.mem_center_mul_iff
#print axioms PAG.Part233.centerTensorEquiv
#print axioms PAG.Part233.crtConj_centerTensorEquiv_tmul
#print axioms PAG.Part233.radDvd_mul
#print axioms PAG.Part233.radDvd_gcd
#print axioms PAG.Part233.mem_centerIdx_iff_dvd
#print axioms PAG.Part233.idxMul
#print axioms PAG.Part233.idxSplit
#print axioms PAG.Part233.gcd_mul_left_of_dvd
#print axioms PAG.Part233.gcd_mul_right_of_dvd
#print axioms PAG.Part233.eq_gcd_mul_gcd
#print axioms PAG.Part233.idxMul_mem_centerIdx
#print axioms PAG.Part233.idxSplit_idxMul
#print axioms PAG.Part233.idxSplit_mem
#print axioms PAG.Part233.idxMul_idxSplit
#print axioms PAG.Part233.card_centerIdx_mul
#print axioms PAG.Part233.mem_centerIdx_mul_iff
#print axioms PAG.Part233.primCount_idxMul
#print axioms PAG.Part233.card_layerDivs_idxMul
