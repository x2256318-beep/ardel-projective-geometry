/-
  PAG 2.0 Part 224（2026-10-29）— 二重可換子 A″ = (A′ の可換子) ≅ Π_{p ∈ S} End(W_p)
  A = ⟨E_s, D_s⟩（Part 214 の shellAlg）、A′（Part 220 の fullComm）、行列単位 E^d_{χ→χ′}（Part 223 の matUnit）、
  S = {(c, d)}（Part 222 の centerIdx）、p ∈ S の基準の原始指標 χ₀(p)（def refChar）、
  W_p = W_{c,χ₀(p)}(d)（def refLayer）、e_p = E^d_{χ₀→χ₀}（def refProj）、n_p = dim W_p = #{v ∣ N/c : v の層 = d}
  0. A″ = Mathlib の Subalgebra.centralizer（def doubleComm）。T ∈ A″ ⇔ T は行列単位すべてと可換
     （A′ は行列単位で張られる：Part 223）。A ⊆ A″（Part 220 の mem_fullComm_iff_commute）
  1. e_p の値は W_p に入り、e_p は W_p の上で恒等。A″ の元は W_p を保つ
  2. 制限 ρ(T) = (T|_{W_p})_p（def restrictHom、代数の準同型）。持ち上げ
     L(S) = Σ_p Σ_χ E_p(χ₀→χ)·ext(S_p)·E_p(χ→χ₀)（def extOp・liftOp。ext(S) f = S(e_p f)）は A″ に入り、
     ρ(L(S)) = S、L(ρ(T)) = T
  3. 代数の同型 A″ ≅ Π_{p ∈ S} End(W_p)（def doubleCommEquiv）≅ Π_p M_{n_p}(ℂ)（def doubleCommMatrixEquiv）、
     dim A″ = Σ_{p ∈ S} n_p²、dim A ≤ Σ_{p ∈ S} n_p²
-/
import PAG227

namespace PAG.Part228

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 二重可換子 -/

/-- A″ = A′ の可換子（Mathlib の Subalgebra.centralizer）。 -/
noncomputable def doubleComm (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Subalgebra.centralizer ℂ (fullComm N : Set (Module.End ℂ (ZMod N → ℂ)))

/-- **0a.** T ∈ A″ ⇔ T は A′ のすべての元と可換。 -/
theorem mem_doubleComm (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ doubleComm N ↔ ∀ S ∈ fullComm N, Commute T S := by
  unfold doubleComm
  rw [Subalgebra.mem_centralizer_iff]
  exact ⟨fun h S hS => (h S hS).symm, fun h S hS => (h S hS).symm⟩

/-- **0b.** A ⊆ A″。 -/
theorem shellAlg_le_doubleComm (N : ℕ) [NeZero N] : shellAlg N ≤ doubleComm N := by
  intro T hT
  rw [mem_doubleComm]
  intro S hS
  exact (((mem_fullComm_iff_commute N S).mp hS) T hT).symm

/-- **0c.** T ∈ A″ ⇔ T は行列単位すべてと可換（A′ は行列単位で張られる）。 -/
theorem mem_doubleComm_iff_matUnit (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ doubleComm N ↔ ∀ (p : centerIdx N) (i j : Prim p.1.1), Commute T (matUnit N p.1.1 p.1.2 i.1 j.1) := by
  rw [mem_doubleComm]
  constructor
  · intro h p i j
    obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
    exact h _ (matUnit_mem_fullComm N p.1.1 p.1.2 (Nat.dvd_of_mem_divisors hc) i.1 j.1 i.2 j.2
      ((mem_layerIdx _ _ _).mp hdI).2)
  · intro h S hS
    obtain ⟨M, hM⟩ := (matAlgHom_bijective N).2 ⟨S, (mem_fullCommAlg N S).mpr hS⟩
    have hS' : matSum N M = S := congrArg Subtype.val hM
    rw [← hS']
    unfold matSum
    exact Commute.sum_right _ _ _ (fun p _ => Commute.sum_right _ _ _ (fun i _ =>
      Commute.sum_right _ _ _ (fun j _ => (h p j i).smul_right _)))

/-! ### 1. 基準の成分 W_p と射影 e_p -/

/-- p ∈ S の基準の原始指標 χ₀(p)。 -/
noncomputable def refChar (N : ℕ) (p : centerIdx N) : Prim p.1.1 :=
  Classical.choice (Nat.card_pos_iff.mp ((mem_centerIdx N p.1).mp p.2).2.1).1

/-- 基準の成分 W_p = W_{c,χ₀(p)}(d)。 -/
noncomputable def refLayer (N : ℕ) [NeZero N] (p : centerIdx N) : Submodule ℂ (ZMod N → ℂ) :=
  layerPart N p.1.1 (refChar N p).1 p.1.2

/-- 基準の射影 e_p = E^d_{χ₀→χ₀}。 -/
noncomputable def refProj (N : ℕ) [NeZero N] (p : centerIdx N) : Module.End ℂ (ZMod N → ℂ) :=
  matUnit N p.1.1 p.1.2 (refChar N p).1 (refChar N p).1

/-- **1a.** e_p f ∈ W_p。 -/
theorem refProj_mem (N : ℕ) [NeZero N] (p : centerIdx N) (f : ZMod N → ℂ) : refProj N p f ∈ refLayer N p := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  exact matUnit_mem_layerPart N p.1.1 p.1.2 (Nat.dvd_of_mem_divisors hc) _ _ ((mem_layerIdx _ _ _).mp hdI).2 f

/-- **1b.** g ∈ W_p なら e_p g = g。 -/
theorem refProj_apply_of_mem (N : ℕ) [NeZero N] (p : centerIdx N) {g : ZMod N → ℂ} (hg : g ∈ refLayer N p) :
    refProj N p g = g := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  have hd := ((mem_layerIdx _ _ _).mp hdI).2
  have hg' : g ∈ layerPart N p.1.1 (refChar N p).1 p.1.2 := hg
  have hι : layerInd N p.1.1 p.1.2 * g = g := by
    rw [layerInd_mul_of_mem N p.1.1 (refChar N p).1 hd hd hg', ite_eq_left rfl]
  unfold refProj
  rw [matUnit_apply_of_mem_self N p.1.1 p.1.2 (Nat.dvd_of_mem_divisors hc) _ _ (refChar N p).2
    ((mem_layerPart N p.1.1 (refChar N p).1 p.1.2 g).mp hg').1, ← mul_assoc,
    twistFn_self_mul_layerInd N p.1.1 _ hdI, hι]

/-- **1c.** A″ の元は W_p を保つ。 -/
theorem doubleComm_mapsTo (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ doubleComm N)
    (p : centerIdx N) {g : ZMod N → ℂ} (hg : g ∈ refLayer N p) : T g ∈ refLayer N p := by
  have hc := (mem_doubleComm_iff_matUnit N T).mp hT p (refChar N p) (refChar N p)
  have e : T (refProj N p g) = refProj N p (T g) := LinearMap.congr_fun hc.eq g
  rw [← refProj_apply_of_mem N p hg, e]
  exact refProj_mem N p (T g)

/-! ### 2. 制限と持ち上げ -/

/-- ρ(T) = (T|_{W_p})_p（代数の準同型）。 -/
noncomputable def restrictHom (N : ℕ) [NeZero N] :
    doubleComm N →ₐ[ℂ] Π p : centerIdx N, Module.End ℂ (refLayer N p) :=
  AlgHom.ofLinearMap
    { toFun := fun T p => (T : Module.End ℂ (ZMod N → ℂ)).restrict (fun _ hg => doubleComm_mapsTo N T.2 p hg)
      map_add' := fun _ _ => funext fun _ => LinearMap.ext fun _ => Subtype.ext rfl
      map_smul' := fun _ _ => funext fun _ => LinearMap.ext fun _ => Subtype.ext rfl }
    (funext fun _ => LinearMap.ext fun _ => Subtype.ext rfl)
    (fun _ _ => funext fun _ => LinearMap.ext fun _ => Subtype.ext rfl)

/-- **2a.** ρ(T)_p g = T g。 -/
theorem restrictHom_apply (N : ℕ) [NeZero N] (T : doubleComm N) (p : centerIdx N) (g : refLayer N p) :
    (restrictHom N T p g : ZMod N → ℂ) = (T : Module.End ℂ (ZMod N → ℂ)) g := rfl

/-- W_p の自己準同型 S の延長 ext(S)：f ↦ S(e_p f)。 -/
noncomputable def extOp (N : ℕ) [NeZero N] (p : centerIdx N) (S : Module.End ℂ (refLayer N p)) :
    Module.End ℂ (ZMod N → ℂ) :=
  (refLayer N p).subtype ∘ₗ S ∘ₗ LinearMap.codRestrict (refLayer N p) (refProj N p) (refProj_mem N p)

/-- **2b.** ext(S) f = S(e_p f)。 -/
theorem extOp_apply (N : ℕ) [NeZero N] (p : centerIdx N) (S : Module.End ℂ (refLayer N p)) (f : ZMod N → ℂ) :
    extOp N p S f = (S ⟨refProj N p f, refProj_mem N p f⟩ : ZMod N → ℂ) := rfl

/-- **2c.** ext(ρ(T)_p) = T·e_p。 -/
theorem extOp_restrictHom (N : ℕ) [NeZero N] (T : doubleComm N) (p : centerIdx N) :
    extOp N p (restrictHom N T p) = (T : Module.End ℂ (ZMod N → ℂ)) * refProj N p :=
  LinearMap.ext fun _ => rfl

/-- **2d.** e_p·ext(S) = ext(S)。 -/
theorem refProj_mul_extOp (N : ℕ) [NeZero N] (p : centerIdx N) (S : Module.End ℂ (refLayer N p)) :
    refProj N p * extOp N p S = extOp N p S := by
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply, extOp_apply]
  exact refProj_apply_of_mem N p (S _).2

/-- 持ち上げ L(S) = Σ_p Σ_χ E_p(χ₀→χ)·ext(S_p)·E_p(χ→χ₀)。 -/
noncomputable def liftOp (N : ℕ) [NeZero N] (S : Π p : centerIdx N, Module.End ℂ (refLayer N p)) :
    Module.End ℂ (ZMod N → ℂ) :=
  ∑ p : centerIdx N, ∑ χ : Prim p.1.1,
    matUnit N p.1.1 p.1.2 (refChar N p).1 χ.1 * extOp N p (S p) * matUnit N p.1.1 p.1.2 χ.1 (refChar N p).1

/-- **2e.** E_q(i→j)·L(S) = E_q(χ₀→j)·ext(S_q)·E_q(i→χ₀)。 -/
theorem matUnit_mul_liftOp (N : ℕ) [NeZero N] (S : Π p : centerIdx N, Module.End ℂ (refLayer N p))
    (q : centerIdx N) (i j : Prim q.1.1) :
    matUnit N q.1.1 q.1.2 i.1 j.1 * liftOp N S =
      matUnit N q.1.1 q.1.2 (refChar N q).1 j.1 * extOp N q (S q) * matUnit N q.1.1 q.1.2 i.1 (refChar N q).1 := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N q.1).mp q.2
  have hcN := Nat.dvd_of_mem_divisors hc
  have hd := ((mem_layerIdx _ _ _).mp hdI).2
  unfold liftOp
  rw [Finset.mul_sum, Finset.sum_eq_single q]
  · rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [← mul_assoc, ← mul_assoc, matUnit_mul_self N q.1.1 q.1.2 hcN hd (refChar N q).1 i.1 j.1 i.2]
    · intro χ _ hχi
      rw [← mul_assoc, ← mul_assoc, matUnit_mul_of_ne_char N q.1.1 hcN q.1.2 q.1.2 hd i.1 j.1 (refChar N q).1
        χ.1 i.2 χ.2 (fun h => hχi (Subtype.ext h).symm), zero_mul, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro p _ hpq
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero (fun χ _ => ?_)
    rw [← mul_assoc, ← mul_assoc, matUnit_mul_of_ne_idx N (Ne.symm hpq) j i χ (refChar N p), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **2f.** L(S)·E_q(i→j) = E_q(χ₀→j)·ext(S_q)·E_q(i→χ₀)。 -/
theorem liftOp_mul_matUnit (N : ℕ) [NeZero N] (S : Π p : centerIdx N, Module.End ℂ (refLayer N p))
    (q : centerIdx N) (i j : Prim q.1.1) :
    liftOp N S * matUnit N q.1.1 q.1.2 i.1 j.1 =
      matUnit N q.1.1 q.1.2 (refChar N q).1 j.1 * extOp N q (S q) * matUnit N q.1.1 q.1.2 i.1 (refChar N q).1 := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N q.1).mp q.2
  have hcN := Nat.dvd_of_mem_divisors hc
  have hd := ((mem_layerIdx _ _ _).mp hdI).2
  unfold liftOp
  rw [Finset.sum_mul, Finset.sum_eq_single q]
  · rw [Finset.sum_mul, Finset.sum_eq_single j]
    · rw [mul_assoc _ (matUnit N q.1.1 q.1.2 j.1 (refChar N q).1),
        matUnit_mul_self N q.1.1 q.1.2 hcN hd i.1 j.1 (refChar N q).1 j.2]
    · intro χ _ hχj
      rw [mul_assoc _ (matUnit N q.1.1 q.1.2 χ.1 (refChar N q).1),
        matUnit_mul_of_ne_char N q.1.1 hcN q.1.2 q.1.2 hd χ.1 (refChar N q).1 i.1 j.1 χ.2 j.2
          (fun h => hχj (Subtype.ext h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro p _ hpq
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero (fun χ _ => ?_)
    rw [mul_assoc _ (matUnit N p.1.1 p.1.2 χ.1 (refChar N p).1),
      matUnit_mul_of_ne_idx N hpq (refChar N p) χ j i, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **2g.** L(S) ∈ A″。 -/
theorem liftOp_mem (N : ℕ) [NeZero N] (S : Π p : centerIdx N, Module.End ℂ (refLayer N p)) :
    liftOp N S ∈ doubleComm N :=
  (mem_doubleComm_iff_matUnit N _).mpr (fun q i j =>
    (liftOp_mul_matUnit N S q i j).trans (matUnit_mul_liftOp N S q i j).symm)

/-- **2h.** ρ(L(S)) = S。 -/
theorem restrictHom_liftOp (N : ℕ) [NeZero N] (S : Π p : centerIdx N, Module.End ℂ (refLayer N p)) :
    restrictHom N ⟨liftOp N S, liftOp_mem N S⟩ = S := by
  funext p
  apply LinearMap.ext
  intro g
  apply Subtype.ext
  rw [restrictHom_apply]
  show liftOp N S g = (S p g : ZMod N → ℂ)
  have hg := g.2
  have e1 : liftOp N S g = (liftOp N S * refProj N p) g := by
    rw [Module.End.mul_apply, refProj_apply_of_mem N p hg]
  have e2 : liftOp N S * refProj N p = refProj N p * extOp N p (S p) * refProj N p :=
    liftOp_mul_matUnit N S p (refChar N p) (refChar N p)
  rw [e1, e2, refProj_mul_extOp, Module.End.mul_apply, refProj_apply_of_mem N p hg, extOp_apply,
    show (⟨refProj N p g, refProj_mem N p g⟩ : refLayer N p) = g from Subtype.ext (refProj_apply_of_mem N p hg)]

/-- **2i.** L(ρ(T)) = T（T ∈ A″）。 -/
theorem liftOp_restrictHom (N : ℕ) [NeZero N] (T : doubleComm N) :
    liftOp N (restrictHom N T) = T := by
  have hT := (mem_doubleComm_iff_matUnit N T).mp T.2
  unfold liftOp
  calc ∑ p : centerIdx N, ∑ χ : Prim p.1.1, matUnit N p.1.1 p.1.2 (refChar N p).1 χ.1 *
        extOp N p (restrictHom N T p) * matUnit N p.1.1 p.1.2 χ.1 (refChar N p).1
      = ∑ p : centerIdx N, ∑ χ : Prim p.1.1,
          (T : Module.End ℂ (ZMod N → ℂ)) * matUnit N p.1.1 p.1.2 χ.1 χ.1 := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun χ _ => ?_))
        obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
        have hcN := Nat.dvd_of_mem_divisors hc
        have hd := ((mem_layerIdx _ _ _).mp hdI).2
        rw [extOp_restrictHom, ← mul_assoc, ← (hT p (refChar N p) χ).eq,
          mul_assoc (T : Module.End ℂ (ZMod N → ℂ)), mul_assoc (T : Module.End ℂ (ZMod N → ℂ)),
          show refProj N p = matUnit N p.1.1 p.1.2 (refChar N p).1 (refChar N p).1 from rfl,
          matUnit_mul_self N p.1.1 p.1.2 hcN hd (refChar N p).1 (refChar N p).1 χ.1 (refChar N p).2,
          matUnit_mul_self N p.1.1 p.1.2 hcN hd χ.1 (refChar N p).1 χ.1 (refChar N p).2]
    _ = (T : Module.End ℂ (ZMod N → ℂ)) * 1 := by
        rw [← sum_sum_matUnit_self N]
        simp only [Finset.mul_sum]
    _ = T := mul_one _

/-! ### 3. A″ ≅ Π_{p ∈ S} End(W_p)、次元 -/

/-- **3a.** ρ は単射。 -/
theorem restrictHom_injective (N : ℕ) [NeZero N] : Function.Injective (restrictHom N) := by
  intro T T' h
  apply Subtype.ext
  rw [← liftOp_restrictHom N T, ← liftOp_restrictHom N T', h]

/-- **3b.** ρ は全射。 -/
theorem restrictHom_surjective (N : ℕ) [NeZero N] : Function.Surjective (restrictHom N) :=
  fun S => ⟨⟨liftOp N S, liftOp_mem N S⟩, restrictHom_liftOp N S⟩

/-- **代数の同型** A″ ≅ Π_{p ∈ S} End(W_p)。 -/
noncomputable def doubleCommEquiv (N : ℕ) [NeZero N] :
    doubleComm N ≃ₐ[ℂ] Π p : centerIdx N, Module.End ℂ (refLayer N p) :=
  AlgEquiv.ofBijective (restrictHom N) ⟨restrictHom_injective N, restrictHom_surjective N⟩

/-- **代数の同型** A″ ≅ Π_{p ∈ S} M_{n_p}(ℂ)（W_p の基底で行列に直す）。 -/
noncomputable def doubleCommMatrixEquiv (N : ℕ) [NeZero N] :
    doubleComm N ≃ₐ[ℂ] Π p : centerIdx N,
      Matrix (Fin (Module.finrank ℂ (refLayer N p))) (Fin (Module.finrank ℂ (refLayer N p))) ℂ :=
  (doubleCommEquiv N).trans
    (AlgEquiv.piCongrRight (fun p => LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ (refLayer N p))))

/-- A″ と Π_p End(W_p) の線形同型（既定の加群の構造）。 -/
noncomputable def doubleCommLinearEquiv (N : ℕ) [NeZero N] :
    doubleComm N ≃ₗ[ℂ] Π p : centerIdx N, Module.End ℂ (refLayer N p) where
  toFun T := restrictHom N T
  invFun S := ⟨liftOp N S, liftOp_mem N S⟩
  map_add' T T' := map_add (restrictHom N) T T'
  map_smul' r T := map_smul (restrictHom N) r T
  left_inv T := Subtype.ext (liftOp_restrictHom N T)
  right_inv S := restrictHom_liftOp N S

/-- **3c.** n_p = dim W_p = #{v ∣ N/c : v の層 = d}（χ₀ によらない）。 -/
theorem finrank_refLayer (N : ℕ) [NeZero N] (p : centerIdx N) :
    Module.finrank ℂ (refLayer N p) = (layerDivs p.1.1 p.1.2 (N / p.1.1)).card := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  exact finrank_layerPart N p.1.1 (Nat.dvd_of_mem_divisors hc) (refChar N p).1 (refChar N p).2
    ((mem_layerIdx _ _ _).mp hdI).2

/-- **3d.** dim Π_p End(W_p) = Σ_{p ∈ S} n_p²。 -/
theorem finrank_piEnd (N : ℕ) [NeZero N] :
    Module.finrank ℂ (Π p : centerIdx N, Module.End ℂ (refLayer N p)) =
      ∑ p : centerIdx N, (layerDivs p.1.1 p.1.2 (N / p.1.1)).card ^ 2 := by
  rw [Module.finrank_pi_fintype ℂ]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Module.finrank_linearMap, finrank_refLayer N p, sq]

/-- **3e. dim A″ = Σ_{p ∈ S} n_p²**。 -/
theorem finrank_doubleComm (N : ℕ) [NeZero N] :
    Module.finrank ℂ (doubleComm N) = ∑ p : centerIdx N, (layerDivs p.1.1 p.1.2 (N / p.1.1)).card ^ 2 :=
  (doubleCommLinearEquiv N).finrank_eq.trans (finrank_piEnd N)

/-- **3f.** dim A ≤ Σ_{p ∈ S} n_p²（A ⊆ A″）。 -/
theorem finrank_shellAlg_le (N : ℕ) [NeZero N] :
    Module.finrank ℂ (shellAlg N) ≤ ∑ p : centerIdx N, (layerDivs p.1.1 p.1.2 (N / p.1.1)).card ^ 2 := by
  rw [← finrank_doubleComm N, ← Subalgebra.finrank_toSubmodule, ← Subalgebra.finrank_toSubmodule]
  exact Submodule.finrank_mono (fun T hT => shellAlg_le_doubleComm N hT)

end PAG.Part228

#print axioms PAG.Part228.doubleComm
#print axioms PAG.Part228.mem_doubleComm
#print axioms PAG.Part228.shellAlg_le_doubleComm
#print axioms PAG.Part228.mem_doubleComm_iff_matUnit
#print axioms PAG.Part228.refChar
#print axioms PAG.Part228.refLayer
#print axioms PAG.Part228.refProj
#print axioms PAG.Part228.refProj_mem
#print axioms PAG.Part228.refProj_apply_of_mem
#print axioms PAG.Part228.doubleComm_mapsTo
#print axioms PAG.Part228.restrictHom
#print axioms PAG.Part228.restrictHom_apply
#print axioms PAG.Part228.extOp
#print axioms PAG.Part228.extOp_apply
#print axioms PAG.Part228.extOp_restrictHom
#print axioms PAG.Part228.refProj_mul_extOp
#print axioms PAG.Part228.liftOp
#print axioms PAG.Part228.matUnit_mul_liftOp
#print axioms PAG.Part228.liftOp_mul_matUnit
#print axioms PAG.Part228.liftOp_mem
#print axioms PAG.Part228.restrictHom_liftOp
#print axioms PAG.Part228.liftOp_restrictHom
#print axioms PAG.Part228.restrictHom_injective
#print axioms PAG.Part228.restrictHom_surjective
#print axioms PAG.Part228.doubleCommEquiv
#print axioms PAG.Part228.doubleCommMatrixEquiv
#print axioms PAG.Part228.doubleCommLinearEquiv
#print axioms PAG.Part228.finrank_refLayer
#print axioms PAG.Part228.finrank_piEnd
#print axioms PAG.Part228.finrank_doubleComm
#print axioms PAG.Part228.finrank_shellAlg_le
