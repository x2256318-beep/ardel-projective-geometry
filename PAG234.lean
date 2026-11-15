/-
  PAG 2.0 Part 230（2026-10-30）— 可換子の一般の分解：(L(B) ⊔ R(B′))^c = L(B^c) ⊔ R(B′^c)
  L(S) = S ⊗ 1・R(T) = 1 ⊗ T（Part 228 の leftOp・rightOp）、^c は可換子（Mathlib の Subalgebra.centralizer）、
  A_N（Part 214 の shellAlg）、A′_N（Part 222 の fullCommAlg）、Z_N（Part 222 の centerAlg）、C（Part 228 の crtConj）
  0. 行列単位 e_{y,y′}（def matE）と成分 Φ_{y,y′}（def blockEnt：f ↦ (x ↦ Φ(f ⊗ δ_{y′})(x, y))）。
     Φ = Σ_{y,y′} L(Φ_{y,y′})·R(e_{y,y′})。Φ が L(S) と可換なら Φ_{y,y′} はすべて S と可換
  1. 補助：u_i が一次独立で Σ_i L(u_i)R(w_i) = 0 なら w_i = 0。部分代数の基底（一次独立で、B のすべての元を張る）
  2. 可換子の一般の分解（a, b ≥ 1。互いに素でなくてよく、部分代数は半単純でなくてよい）：
     (L(B) ⊔ R(B′))^c = L(B^c) ⊔ R(B′^c)、二重可換子 (L(B) ⊔ R(B′))″ = L(B″) ⊔ R(B′″)、
     dim (L(B) ⊔ R(B′))^c = dim B^c·dim B′^c、L(B)^c = L(B^c) ⊔ R(End)
  3. 応用（Part 226 の数え上げによらない証明）：A′_N = A_N^c、Z_N = (A_N ⊔ A′_N)^c（Part 225 の A = A″ から）、
     C(X^c) = C(X)^c。C(A′_{ab}) = L(A′_a) ⊔ R(A′_b)、C(Z_{ab}) = L(Z_a) ⊔ R(Z_b)、
     dim A′_{ab} = dim A′_a·dim A′_b、dim Z_{ab} = dim Z_a·dim Z_b（Part 229 は次元の比較に Part 226 を使っていた）
-/
import PAG233

namespace PAG.Part234

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part231 PAG.Part232 PAG.Part233
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 行列単位と成分 -/

/-- End(ℂ^{ℤ/b}) の行列単位 e_{y,y′}（p = (y, y′)、h ↦ (y″ ↦ [y″ = y]·h(y′))）。 -/
noncomputable def matE {b : ℕ} (p : ZMod b × ZMod b) : Module.End ℂ (ZMod b → ℂ) where
  toFun h y'' := if y'' = p.1 then h p.2 else 0
  map_add' h k := by
    funext y''
    by_cases hy : y'' = p.1 <;> simp [hy]
  map_smul' c h := by
    funext y''
    by_cases hy : y'' = p.1 <;> simp [hy]

/-- **0a.** e_{y,y′} の値。 -/
theorem matE_apply {b : ℕ} (p : ZMod b × ZMod b) (h : ZMod b → ℂ) (y'' : ZMod b) :
    matE p h y'' = if y'' = p.1 then h p.2 else 0 := rfl

/-- 埋め込み ι_{y′}：f ↦ f ⊗ δ_{y′}（(x, y″) ↦ [y″ = y′]·f(x)）。 -/
noncomputable def inclY {a b : ℕ} (y' : ZMod b) : (ZMod a → ℂ) →ₗ[ℂ] (ZMod a × ZMod b → ℂ) where
  toFun f q := if q.2 = y' then f q.1 else 0
  map_add' f g := by
    funext q
    by_cases hq : q.2 = y' <;> simp [hq]
  map_smul' c f := by
    funext q
    by_cases hq : q.2 = y' <;> simp [hq]

/-- **0b.** ι_{y′} の値。 -/
theorem inclY_apply {a b : ℕ} (y' : ZMod b) (f : ZMod a → ℂ) (q : ZMod a × ZMod b) :
    inclY y' f q = if q.2 = y' then f q.1 else 0 := rfl

/-- 制限 ρ_y：F ↦ F(·, y)。 -/
noncomputable def restrY {a b : ℕ} (y : ZMod b) : (ZMod a × ZMod b → ℂ) →ₗ[ℂ] (ZMod a → ℂ) where
  toFun F x := F (x, y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **0c.** ρ_y の値。 -/
theorem restrY_apply {a b : ℕ} (y : ZMod b) (F : ZMod a × ZMod b → ℂ) (x : ZMod a) :
    restrY y F x = F (x, y) := rfl

/-- Φ ∈ End(ℂ^{ℤ/a × ℤ/b}) の (y, y′) 成分 Φ_{y,y′} = ρ_y ∘ Φ ∘ ι_{y′} ∈ End(ℂ^{ℤ/a})。 -/
noncomputable def blockEnt {a b : ℕ} (Φ : Module.End ℂ (ZMod a × ZMod b → ℂ)) (p : ZMod b × ZMod b) :
    Module.End ℂ (ZMod a → ℂ) :=
  (restrY p.1).comp (Φ.comp (inclY p.2))

/-- **0d.** Φ_{y,y′} f (x) = Φ(f ⊗ δ_{y′})(x, y)。 -/
theorem blockEnt_apply {a b : ℕ} (Φ : Module.End ℂ (ZMod a × ZMod b → ℂ)) (p : ZMod b × ZMod b)
    (f : ZMod a → ℂ) (x : ZMod a) : blockEnt Φ p f x = Φ (inclY p.2 f) (x, p.1) := rfl

/-- **0e.** Σ_{y′} ι_{y′}(F(·, y′)) = F。 -/
theorem sum_inclY {a b : ℕ} [NeZero b] (F : ZMod a × ZMod b → ℂ) :
    ∑ y' : ZMod b, inclY y' (fun x => F (x, y')) = F := by
  funext q
  rw [Finset.sum_apply]
  show ∑ y' : ZMod b, (if q.2 = y' then F (q.1, y') else 0) = F q
  rw [Finset.sum_ite_eq]
  simp

/-- **0f. 行列単位による展開**：Φ = Σ_{y,y′} L(Φ_{y,y′})·R(e_{y,y′})。 -/
theorem sum_blockEnt {a b : ℕ} [NeZero b] (Φ : Module.End ℂ (ZMod a × ZMod b → ℂ)) :
    ∑ p : ZMod b × ZMod b, leftOp b (blockEnt Φ p) * rightOp a (matE p) = Φ := by
  apply LinearMap.ext
  intro F
  funext q
  obtain ⟨x, y0⟩ := q
  rw [LinearMap.sum_apply, Finset.sum_apply]
  have hterm : ∀ p : ZMod b × ZMod b, (leftOp b (blockEnt Φ p) * rightOp a (matE p)) F (x, y0) =
      if y0 = p.1 then Φ (inclY p.2 (fun x' => F (x', p.2))) (x, y0) else 0 := by
    intro p
    show blockEnt Φ p (fun x' => matE p (fun y'' => F (x', y'')) y0) x = _
    by_cases hy : y0 = p.1
    · have h1 : (fun x' => matE p (fun y'' => F (x', y'')) y0) = fun x' => F (x', p.2) := by
        funext x'
        rw [matE_apply]
        simp [hy]
      rw [h1, blockEnt_apply, hy]
      simp
    · have h1 : (fun x' => matE p (fun y'' => F (x', y'')) y0) = 0 := by
        funext x'
        rw [matE_apply]
        simp [hy]
      rw [h1, map_zero]
      simp [hy]
  have hs : Φ F = ∑ y' : ZMod b, Φ (inclY y' (fun x' => F (x', y'))) := by
    conv_lhs => rw [← sum_inclY F]
    rw [map_sum]
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Fintype.sum_prod_type, Finset.sum_comm, hs, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun y' _ => ?_)
  rw [Finset.sum_ite_eq]
  simp

/-- **0g.** ι_{y′}(S f) = L(S)(ι_{y′} f)。 -/
theorem inclY_leftOp {a b : ℕ} (S : Module.End ℂ (ZMod a → ℂ)) (y' : ZMod b) (f : ZMod a → ℂ) :
    inclY y' (S f) = leftOp b S (inclY y' f) := by
  funext q
  show (if q.2 = y' then S f q.1 else 0) = S (fun x' => inclY y' f (x', q.2)) q.1
  by_cases hq : q.2 = y'
  · have h1 : (fun x' => inclY y' f (x', q.2)) = f := by
      funext x'
      rw [inclY_apply]
      simp [hq]
    rw [h1]
    simp [hq]
  · have h1 : (fun x' => inclY y' f (x', q.2)) = 0 := by
      funext x'
      rw [inclY_apply]
      simp [hq]
    rw [h1, map_zero]
    simp [hq]

/-- **0h.** ρ_y(L(S) F) = S(ρ_y F)。 -/
theorem restrY_leftOp {a b : ℕ} (S : Module.End ℂ (ZMod a → ℂ)) (y : ZMod b) (F : ZMod a × ZMod b → ℂ) :
    restrY y (leftOp b S F) = S (restrY y F) := rfl

/-- **0i.** Φ が L(S) と可換なら、成分 Φ_{y,y′} はすべて S と可換（0g・0h）。 -/
theorem blockEnt_commute {a b : ℕ} {Φ : Module.End ℂ (ZMod a × ZMod b → ℂ)} {S : Module.End ℂ (ZMod a → ℂ)}
    (h : Commute Φ (leftOp b S)) (p : ZMod b × ZMod b) : Commute (blockEnt Φ p) S := by
  apply LinearMap.ext
  intro f
  show restrY p.1 (Φ (inclY p.2 (S f))) = S (restrY p.1 (Φ (inclY p.2 f)))
  rw [inclY_leftOp, ← Module.End.mul_apply, h.eq, Module.End.mul_apply, restrY_leftOp]

/-! ### 1. 補助 -/

/-- **1a.** u_i が一次独立で Σ_i L(u_i)R(w_i) = 0 なら、w_i はすべて 0（Part 229 の 0a の式で f ⊗ h に作用させる）。 -/
theorem eq_zero_of_sum_leftOp_mul_rightOp {a b : ℕ} {ι : Type*} [Fintype ι]
    {u : ι → Module.End ℂ (ZMod a → ℂ)} (hu : LinearIndependent ℂ u) (w : ι → Module.End ℂ (ZMod b → ℂ))
    (h : ∑ i, leftOp b (u i) * rightOp a (w i) = 0) (i : ι) : w i = 0 := by
  rw [Fintype.linearIndependent_iff] at hu
  apply LinearMap.ext
  intro g
  funext y
  have key : ∀ (f : ZMod a → ℂ) (x : ZMod a), ∑ j, w j g y * u j f x = 0 := by
    intro f x
    have hx := congrArg
      (fun X : Module.End ℂ (ZMod a × ZMod b → ℂ) => X (fun q => f q.1 * g q.2) (x, y)) h
    simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.zero_apply, Pi.zero_apply] at hx
    simp only [leftOp_mul_rightOp_apply_prod] at hx
    rw [← hx]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hzero := hu (fun j => w j g y) (by
    apply LinearMap.ext
    intro f
    funext x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      LinearMap.zero_apply, Pi.zero_apply]
    exact key f x) i
  simpa using hzero

/-- **1b.** 部分代数 B の基底：B の中の一次独立な有限族で、B のすべての元がその一次結合になるもの（Part 229 の subalgSpan の基底）。 -/
theorem exists_basis_subalg {X : Type*} [Fintype X] (B : Subalgebra ℂ (Module.End ℂ (X → ℂ))) :
    ∃ (n : ℕ) (u : Fin n → Module.End ℂ (X → ℂ)), LinearIndependent ℂ u ∧ (∀ i, u i ∈ B) ∧
      ∀ T ∈ B, ∃ c : Fin n → ℂ, T = ∑ i, c i • u i := by
  let P := subalgSpan B
  let _ : AddCommGroup ↥P := Module.addCommMonoidToAddCommGroup ℂ
  have hF : Module.Free ℂ ↥P := Module.Free.of_divisionRing ℂ ↥P
  have hFin : Module.Finite ℂ ↥P := Module.Finite.equiv (subalgSpanEquiv B).symm
  let bB := Module.finBasis ℂ ↥P
  refine ⟨_, fun i => (bB i : Module.End ℂ (X → ℂ)),
    bB.linearIndependent.map' P.subtype (Submodule.ker_subtype P), fun i => (bB i).2, ?_⟩
  intro T hT
  refine ⟨fun i => bB.repr ⟨T, hT⟩ i, ?_⟩
  have h2 := congrArg P.subtype (bB.sum_repr ⟨T, hT⟩)
  rw [map_sum] at h2
  simp only [map_smul, Submodule.subtype_apply] at h2
  exact h2.symm

/-- **1c.** L(Σ_i c_i u_i) = Σ_i c_i L(u_i)。 -/
theorem leftOp_sum_smul {a b : ℕ} {ι : Type*} [Fintype ι] (c : ι → ℂ) (u : ι → Module.End ℂ (ZMod a → ℂ)) :
    leftOp b (∑ i, c i • u i) = ∑ i, c i • leftOp b (u i) := by
  show leftHom a b (∑ i, c i • u i) = ∑ i, c i • leftHom a b (u i)
  rw [map_sum]
  simp only [map_smul]

/-- **1d.** R(Σ_i c_i v_i) = Σ_i c_i R(v_i)。 -/
theorem rightOp_sum_smul {a b : ℕ} {ι : Type*} [Fintype ι] (c : ι → ℂ) (v : ι → Module.End ℂ (ZMod b → ℂ)) :
    rightOp a (∑ i, c i • v i) = ∑ i, c i • rightOp a (v i) := by
  show rightHom a b (∑ i, c i • v i) = ∑ i, c i • rightHom a b (v i)
  rw [map_sum]
  simp only [map_smul]

/-! ### 2. 可換子の一般の分解 -/

/-- **2a. 可換子の一般の分解**：(L(B) ⊔ R(B′))^c = L(B^c) ⊔ R(B′^c)。⊆：0f で Φ = Σ L(Φ_{y,y′})R(e_{y,y′})、0i で Φ_{y,y′} ∈ B^c、1b の基底で Φ = Σ_i L(u_i)R(T_i)、R(B′) との可換性と 1a で T_i ∈ B′^c。⊇：Part 229 の commute_of_mem_sup。 -/
theorem centralizer_sup_map {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    Subalgebra.centralizer ℂ ((B.map (leftHom a b) ⊔ B'.map (rightHom a b) :
        Subalgebra ℂ (Module.End ℂ (ZMod a × ZMod b → ℂ))) : Set (Module.End ℂ (ZMod a × ZMod b → ℂ))) =
      (Subalgebra.centralizer ℂ (B : Set (Module.End ℂ (ZMod a → ℂ)))).map (leftHom a b) ⊔
        (Subalgebra.centralizer ℂ (B' : Set (Module.End ℂ (ZMod b → ℂ)))).map (rightHom a b) := by
  apply le_antisymm
  · intro Φ hΦ
    rw [Subalgebra.mem_centralizer_iff] at hΦ
    have hL : ∀ S ∈ B, Commute Φ (leftOp b S) := fun S hS =>
      (hΦ _ ((le_sup_left : B.map (leftHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨S, hS, rfl⟩))).symm
    have hR : ∀ T ∈ B', Commute Φ (rightOp a T) := fun T hT =>
      (hΦ _ ((le_sup_right : B'.map (rightHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨T, hT, rfl⟩))).symm
    have hblk : ∀ p, blockEnt Φ p ∈ Subalgebra.centralizer ℂ (B : Set (Module.End ℂ (ZMod a → ℂ))) := by
      intro p
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      exact (blockEnt_commute (hL g hg) p).eq.symm
    obtain ⟨n, u, hu, huB, hspan⟩ :=
      exists_basis_subalg (Subalgebra.centralizer ℂ (B : Set (Module.End ℂ (ZMod a → ℂ))))
    have hc : ∀ p : ZMod b × ZMod b, ∃ c : Fin n → ℂ, blockEnt Φ p = ∑ i, c i • u i :=
      fun p => hspan _ (hblk p)
    choose c hc using hc
    let T' : Fin n → Module.End ℂ (ZMod b → ℂ) := fun i => ∑ p : ZMod b × ZMod b, c p i • matE p
    have hexp : Φ = ∑ i, leftOp b (u i) * rightOp a (T' i) := by
      have h1 : ∀ p : ZMod b × ZMod b, leftOp b (blockEnt Φ p) * rightOp a (matE p) =
          ∑ i, c p i • (leftOp b (u i) * rightOp a (matE p)) := by
        intro p
        rw [hc p, leftOp_sum_smul, Finset.sum_mul]
        simp only [smul_mul_assoc]
      have h2 : ∀ i, leftOp b (u i) * rightOp a (T' i) =
          ∑ p : ZMod b × ZMod b, c p i • (leftOp b (u i) * rightOp a (matE p)) := by
        intro i
        show leftOp b (u i) * rightOp a (∑ p : ZMod b × ZMod b, c p i • matE p) = _
        rw [rightOp_sum_smul, Finset.mul_sum]
        simp only [mul_smul_comm]
      conv_lhs => rw [← sum_blockEnt Φ]
      rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_congr rfl (fun i _ => h2 i)]
      exact Finset.sum_comm
    have hT : ∀ i, T' i ∈ Subalgebra.centralizer ℂ (B' : Set (Module.End ℂ (ZMod b → ℂ))) := by
      intro i
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      have hcomm := (hR g hg).eq
      have e1 : ∀ j, leftOp b (u j) * rightOp a (T' j) * rightOp a g = leftOp b (u j) * rightOp a (T' j * g) := by
        intro j
        rw [mul_assoc]
        show leftOp b (u j) * (rightHom a b (T' j) * rightHom a b g) = leftOp b (u j) * rightHom a b (T' j * g)
        rw [map_mul]
      have e2 : ∀ j, rightOp a g * (leftOp b (u j) * rightOp a (T' j)) = leftOp b (u j) * rightOp a (g * T' j) := by
        intro j
        rw [← mul_assoc, ← (leftOp_commute_rightOp (u j) g).eq, mul_assoc]
        show leftOp b (u j) * (rightHom a b g * rightHom a b (T' j)) = leftOp b (u j) * rightHom a b (g * T' j)
        rw [map_mul]
      have hdiff : ∑ j, leftOp b (u j) * rightOp a (T' j * g - g * T' j) = 0 := by
        have hsub : ∀ j, leftOp b (u j) * rightOp a (T' j * g - g * T' j) =
            leftOp b (u j) * rightOp a (T' j) * rightOp a g - rightOp a g * (leftOp b (u j) * rightOp a (T' j)) := by
          intro j
          rw [e1, e2, ← mul_sub]
          congr 1
        rw [Finset.sum_congr rfl (fun j _ => hsub j), Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
          ← hexp]
        exact sub_eq_zero.mpr hcomm
      have h0 := eq_zero_of_sum_leftOp_mul_rightOp hu _ hdiff i
      exact (sub_eq_zero.mp h0).symm
    rw [hexp]
    refine Subalgebra.sum_mem _ (fun i _ => Subalgebra.mul_mem _ ?_ ?_)
    · exact (le_sup_left : (Subalgebra.centralizer ℂ (B : Set (Module.End ℂ (ZMod a → ℂ)))).map (leftHom a b) ≤ _)
        (Subalgebra.mem_map.mpr ⟨u i, huB i, rfl⟩)
    · exact (le_sup_right : (Subalgebra.centralizer ℂ (B' : Set (Module.End ℂ (ZMod b → ℂ)))).map (rightHom a b) ≤ _)
        (Subalgebra.mem_map.mpr ⟨T' i, hT i, rfl⟩)
  · refine sup_le ?_ ?_
    · intro Y hY
      obtain ⟨S, hS, rfl⟩ := Subalgebra.mem_map.mp hY
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      have hcomm : Commute (leftOp b S) g := by
        refine commute_of_mem_sup (leftOp b S) (fun Z hZ => ?_) (fun Z hZ => ?_) g hg
        · obtain ⟨S', hS', rfl⟩ := Subalgebra.mem_map.mp hZ
          have h1 := (Subalgebra.mem_centralizer_iff ℂ).mp hS S' hS'
          exact Commute.map (show Commute S S' from h1.symm) (leftHom a b)
        · obtain ⟨T', -, rfl⟩ := Subalgebra.mem_map.mp hZ
          exact leftOp_commute_rightOp S T'
      exact hcomm.eq.symm
    · intro Y hY
      obtain ⟨T, hT, rfl⟩ := Subalgebra.mem_map.mp hY
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      have hcomm : Commute (rightOp a T) g := by
        refine commute_of_mem_sup (rightOp a T) (fun Z hZ => ?_) (fun Z hZ => ?_) g hg
        · obtain ⟨S', -, rfl⟩ := Subalgebra.mem_map.mp hZ
          exact (leftOp_commute_rightOp S' T).symm
        · obtain ⟨T'', hT'', rfl⟩ := Subalgebra.mem_map.mp hZ
          have h1 := (Subalgebra.mem_centralizer_iff ℂ).mp hT T'' hT''
          exact Commute.map (show Commute T T'' from h1.symm) (rightHom a b)
      exact hcomm.eq.symm

/-- **2b.** 二重可換子 (L(B) ⊔ R(B′))″ = L(B″) ⊔ R(B′″)（2a を 2 回）。 -/
theorem centralizer_centralizer_sup_map {a b : ℕ} [NeZero a] [NeZero b]
    (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ))) (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    Subalgebra.centralizer ℂ (Subalgebra.centralizer ℂ ((B.map (leftHom a b) ⊔ B'.map (rightHom a b) :
        Subalgebra ℂ (Module.End ℂ (ZMod a × ZMod b → ℂ))) : Set (Module.End ℂ (ZMod a × ZMod b → ℂ))) :
        Set (Module.End ℂ (ZMod a × ZMod b → ℂ))) =
      (Subalgebra.centralizer ℂ (Subalgebra.centralizer ℂ (B : Set (Module.End ℂ (ZMod a → ℂ))) :
        Set (Module.End ℂ (ZMod a → ℂ)))).map (leftHom a b) ⊔
        (Subalgebra.centralizer ℂ (Subalgebra.centralizer ℂ (B' : Set (Module.End ℂ (ZMod b → ℂ))) :
          Set (Module.End ℂ (ZMod b → ℂ)))).map (rightHom a b) := by
  rw [centralizer_sup_map, centralizer_sup_map]

/-- **2c.** dim (L(B) ⊔ R(B′))^c = dim B^c·dim B′^c（2a と Part 229 の finrank_sup_map）。 -/
theorem finrank_centralizer_sup_map {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ)))
    (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    Module.finrank ℂ (Subalgebra.centralizer ℂ ((B.map (leftHom a b) ⊔ B'.map (rightHom a b) :
        Subalgebra ℂ (Module.End ℂ (ZMod a × ZMod b → ℂ))) : Set (Module.End ℂ (ZMod a × ZMod b → ℂ)))) =
      Module.finrank ℂ (Subalgebra.centralizer ℂ (B : Set (Module.End ℂ (ZMod a → ℂ)))) *
        Module.finrank ℂ (Subalgebra.centralizer ℂ (B' : Set (Module.End ℂ (ZMod b → ℂ)))) := by
  rw [centralizer_sup_map, finrank_sup_map]

/-- **2d.** スカラーの可換子は End 全体。 -/
theorem centralizer_bot_eq_top {X : Type*} :
    Subalgebra.centralizer ℂ ((⊥ : Subalgebra ℂ (Module.End ℂ (X → ℂ))) : Set (Module.End ℂ (X → ℂ))) = ⊤ := by
  ext Y
  simp only [Algebra.mem_top, iff_true]
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp hg
  exact Algebra.commutes c Y

/-- **2e.** L(B)^c = L(B^c) ⊔ R(End(ℂ^{ℤ/b}))（2a で B′ = スカラー）。 -/
theorem centralizer_map_leftHom {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ))) :
    Subalgebra.centralizer ℂ ((B.map (leftHom a b) : Subalgebra ℂ (Module.End ℂ (ZMod a × ZMod b → ℂ))) :
      Set (Module.End ℂ (ZMod a × ZMod b → ℂ))) =
      (Subalgebra.centralizer ℂ (B : Set (Module.End ℂ (ZMod a → ℂ)))).map (leftHom a b) ⊔
        (⊤ : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))).map (rightHom a b) := by
  have h : B.map (leftHom a b) =
      B.map (leftHom a b) ⊔ (⊥ : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))).map (rightHom a b) := by
    rw [Algebra.map_bot, sup_bot_eq]
  rw [h, centralizer_sup_map, centralizer_bot_eq_top]

/-- **2f.** R(B′)^c = L(End(ℂ^{ℤ/a})) ⊔ R(B′^c)。 -/
theorem centralizer_map_rightHom {a b : ℕ} [NeZero a] [NeZero b] (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    Subalgebra.centralizer ℂ ((B'.map (rightHom a b) : Subalgebra ℂ (Module.End ℂ (ZMod a × ZMod b → ℂ))) :
      Set (Module.End ℂ (ZMod a × ZMod b → ℂ))) =
      (⊤ : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ))).map (leftHom a b) ⊔
        (Subalgebra.centralizer ℂ (B' : Set (Module.End ℂ (ZMod b → ℂ)))).map (rightHom a b) := by
  have h : B'.map (rightHom a b) =
      (⊥ : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ))).map (leftHom a b) ⊔ B'.map (rightHom a b) := by
    rw [Algebra.map_bot, bot_sup_eq]
  rw [h, centralizer_sup_map, centralizer_bot_eq_top]

/-! ### 3. 応用：Part 226 の数え上げによらない証明 -/

/-- **3a.** A′_N = A_N^c（Part 220 の mem_fullComm_iff_commute）。 -/
theorem fullCommAlg_eq_centralizer (N : ℕ) [NeZero N] :
    fullCommAlg N = Subalgebra.centralizer ℂ (shellAlg N : Set (Module.End ℂ (ZMod N → ℂ))) := by
  ext T
  rw [mem_fullCommAlg, mem_fullComm_iff_commute, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h g hg
    exact (h g hg).eq.symm
  · intro h S hS
    exact (h S hS).symm

/-- **3b.** Z_N = (A_N ⊔ A′_N)^c（Z = A ∩ A′、Part 225 の A = A″）。 -/
theorem centerAlg_eq_centralizer (N : ℕ) [NeZero N] :
    centerAlg N = Subalgebra.centralizer ℂ ((shellAlg N ⊔ fullCommAlg N : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))) :
      Set (Module.End ℂ (ZMod N → ℂ))) := by
  ext Z
  rw [mem_centerAlg_iff_and, Subalgebra.mem_centralizer_iff]
  constructor
  · rintro ⟨hA, hA'⟩ g hg
    have hc : Commute Z g := commute_of_mem_sup Z
      (fun Y hY => (mem_fullComm_iff_commute N Z).mp hA' Y hY)
      (fun Y hY => (mem_shellAlg_iff_commute N Z).mp hA Y ((mem_fullCommAlg N Y).mp hY)) g hg
    exact hc.eq.symm
  · intro h
    refine ⟨(mem_shellAlg_iff_commute N Z).mpr (fun S hS => (h S ((le_sup_right : fullCommAlg N ≤ _)
      ((mem_fullCommAlg N S).mpr hS))).symm), (mem_fullComm_iff_commute N Z).mpr (fun S hS =>
      (h S ((le_sup_left : shellAlg N ≤ _) hS)).symm)⟩

/-- **3c.** C(X^c) = C(X)^c（C は代数同型）。 -/
theorem map_crtConj_centralizer {a b : ℕ} (hab : Nat.Coprime a b)
    (X : Subalgebra ℂ (Module.End ℂ (ZMod (a * b) → ℂ))) :
    (Subalgebra.centralizer ℂ (X : Set (Module.End ℂ (ZMod (a * b) → ℂ)))).map (crtConj hab).toAlgHom =
      Subalgebra.centralizer ℂ ((X.map (crtConj hab).toAlgHom : Subalgebra ℂ (Module.End ℂ (ZMod a × ZMod b → ℂ))) :
        Set (Module.End ℂ (ZMod a × ZMod b → ℂ))) := by
  ext Y
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro hY g hg
    obtain ⟨Y', hY', rfl⟩ := Subalgebra.mem_map.mp hY
    obtain ⟨g', hg', rfl⟩ := Subalgebra.mem_map.mp hg
    rw [Subalgebra.mem_centralizer_iff] at hY'
    have h1 := congrArg (crtConj hab) (hY' g' hg')
    rw [map_mul, map_mul] at h1
    exact h1
  · intro h
    refine Subalgebra.mem_map.mpr ⟨(crtConj hab).symm Y, ?_, AlgEquiv.apply_symm_apply _ _⟩
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    have h1 := h (crtConj hab g) (Subalgebra.mem_map.mpr ⟨g, hg, rfl⟩)
    have h2 := congrArg (crtConj hab).symm h1
    rw [map_mul, map_mul, AlgEquiv.symm_apply_apply] at h2
    exact h2

/-- **3d. C(A′_{ab}) = L(A′_a) ⊔ R(A′_b)** を Part 226 の数え上げによらずに示したもの（3a・3c、Part 228 の map_crtConj_shellAlg、2a）。 -/
theorem map_crtConj_fullComm_of_centralizer {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (fullCommAlg (a * b)).map (crtConj hab).toAlgHom =
      (fullCommAlg a).map (leftHom a b) ⊔ (fullCommAlg b).map (rightHom a b) := by
  rw [fullCommAlg_eq_centralizer, fullCommAlg_eq_centralizer, fullCommAlg_eq_centralizer, map_crtConj_centralizer,
    map_crtConj_shellAlg hab, centralizer_sup_map]

/-- **3e.** dim A′_{ab} = dim A′_a·dim A′_b（3d と Part 229 の finrank_sup_map。Part 226 の finrank_fullComm_mul と別の証明）。 -/
theorem finrank_fullComm_mul_of_crt {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ (fullComm (a * b)) = Module.finrank ℂ (fullComm a) * Module.finrank ℂ (fullComm b) := by
  rw [← finrank_fullCommAlg_eq, ← finrank_fullCommAlg_eq, ← finrank_fullCommAlg_eq,
    ← finrank_map_crtConj_gen hab (fullCommAlg (a * b)), map_crtConj_fullComm_of_centralizer hab, finrank_sup_map]

/-- **3f. C(Z_{ab}) = L(Z_a) ⊔ R(Z_b)** を数え上げによらずに示したもの（3b・3c・3d、L(B₁) ⊔ L(B₂) = L(B₁ ⊔ B₂)、2a）。 -/
theorem map_crtConj_center_of_centralizer {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (centerAlg (a * b)).map (crtConj hab).toAlgHom =
      (centerAlg a).map (leftHom a b) ⊔ (centerAlg b).map (rightHom a b) := by
  rw [centerAlg_eq_centralizer, centerAlg_eq_centralizer, centerAlg_eq_centralizer, map_crtConj_centralizer,
    Algebra.map_sup, map_crtConj_shellAlg hab, map_crtConj_fullComm_of_centralizer hab, sup_sup_sup_comm,
    ← Algebra.map_sup, ← Algebra.map_sup, centralizer_sup_map]

/-- **3g.** dim Z_{ab} = dim Z_a·dim Z_b（Part 226 の finrank_fullCommCenter_mul と別の証明）。 -/
theorem finrank_center_mul_of_crt {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ (fullCommCenter (a * b)) =
      Module.finrank ℂ (fullCommCenter a) * Module.finrank ℂ (fullCommCenter b) := by
  rw [← finrank_centerAlg_eq, ← finrank_centerAlg_eq, ← finrank_centerAlg_eq,
    ← finrank_map_crtConj_gen hab (centerAlg (a * b)), map_crtConj_center_of_centralizer hab, finrank_sup_map]

end PAG.Part234

#print axioms PAG.Part234.matE
#print axioms PAG.Part234.matE_apply
#print axioms PAG.Part234.inclY
#print axioms PAG.Part234.inclY_apply
#print axioms PAG.Part234.restrY
#print axioms PAG.Part234.restrY_apply
#print axioms PAG.Part234.blockEnt
#print axioms PAG.Part234.blockEnt_apply
#print axioms PAG.Part234.sum_inclY
#print axioms PAG.Part234.sum_blockEnt
#print axioms PAG.Part234.inclY_leftOp
#print axioms PAG.Part234.restrY_leftOp
#print axioms PAG.Part234.blockEnt_commute
#print axioms PAG.Part234.eq_zero_of_sum_leftOp_mul_rightOp
#print axioms PAG.Part234.exists_basis_subalg
#print axioms PAG.Part234.leftOp_sum_smul
#print axioms PAG.Part234.rightOp_sum_smul
#print axioms PAG.Part234.centralizer_sup_map
#print axioms PAG.Part234.centralizer_centralizer_sup_map
#print axioms PAG.Part234.finrank_centralizer_sup_map
#print axioms PAG.Part234.centralizer_bot_eq_top
#print axioms PAG.Part234.centralizer_map_leftHom
#print axioms PAG.Part234.centralizer_map_rightHom
#print axioms PAG.Part234.fullCommAlg_eq_centralizer
#print axioms PAG.Part234.centerAlg_eq_centralizer
#print axioms PAG.Part234.map_crtConj_centralizer
#print axioms PAG.Part234.map_crtConj_fullComm_of_centralizer
#print axioms PAG.Part234.finrank_fullComm_mul_of_crt
#print axioms PAG.Part234.map_crtConj_center_of_centralizer
#print axioms PAG.Part234.finrank_center_mul_of_crt
