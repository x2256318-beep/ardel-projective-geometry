/-
  PAG 2.0 Part 235（2026-10-31）— 族のテンソル積の代数の同型 Ψ と中国剰余定理の図式
  Φ_N：Π_{p ∈ S(N)} M_{m(c_p)}(ℂ) ≅ A′_N（Part 223 の fullCommMatrixEquiv）、Θ′：A′_a ⊗ A′_b ≅ A′_{ab}（Part 229 の
  fullCommTensorEquiv、C(Θ′(S ⊗ T)) = L(S)R(T)）、族のテンソル積 M_a ⊠ M_b（Part 234 の tensorFamily、
  C(Φ_{ab}(M_a ⊠ M_b)) = L(Φ_a M_a)·R(Φ_b M_b)）
  0. Ψ = Φ_{ab}⁻¹ ∘ Θ′ ∘ (Φ_a ⊗ Φ_b)：(Π_p M_{m(c_p)}) ⊗ (Π_q M_{m(c_q)}) ≅ Π_r M_{m(c_r)}（def matTensorEquiv、代数の同型）。
     Ψ(M_a ⊗ M_b) = M_a ⊠ M_b（Part 234 の具体的な式は、この抽象的な同型の値）
  1. よって M_a ⊠ M_b は双線形で、この形の族の一次結合で全体が書ける。次元 Σ_r m(c_r)² = (Σ_p m(c_p)²)(Σ_q m(c_q)²)
  2. 中国剰余定理の図式：C ∘ Φ_{ab} ∘ Ψ = (L ∘ Φ_a) ⊗ (R ∘ Φ_b)（代数の準同型の等式）
  3. 中心の極小べき等元：Ψ(1_p ⊗ 1_q) = 1_r（r ↔ (p, q)）
-/
import PAG238

namespace PAG.Part239

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part231 PAG.Part232 PAG.Part233 PAG.Part234
  PAG.Part235 PAG.Part236 PAG.Part237 PAG.Part238
open ZMod (stdAddChar)
open scoped ZMod TensorProduct

/-! ### 0. 代数の同型 Ψ -/

/-- 族のテンソル積の代数の同型 Ψ：(Π_p M_{m(c_p)}) ⊗ (Π_q M_{m(c_q)}) ≅ Π_r M_{m(c_r)}（Ψ = Φ_{ab}⁻¹ ∘ Θ′ ∘ (Φ_a ⊗ Φ_b)。Part 223 の fullCommMatrixEquiv と Part 229 の fullCommTensorEquiv）。 -/
noncomputable def matTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) ⊗[ℂ]
        (Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) ≃ₐ[ℂ]
      (Π r : centerIdx (a * b), Matrix (Prim r.1.1) (Prim r.1.1) ℂ) :=
  (Algebra.TensorProduct.congr (fullCommMatrixEquiv a) (fullCommMatrixEquiv b)).trans
    ((fullCommTensorEquiv hab).trans (fullCommMatrixEquiv (a * b)).symm)

/-- **0a.** Φ(M) の作用素は matSum M（定義から）。 -/
theorem fullCommMatrixEquiv_coe (N : ℕ) [NeZero N] (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) :
    (fullCommMatrixEquiv N M : Module.End ℂ (ZMod N → ℂ)) = matSum N M := rfl

/-- **0b.** Φ_{ab}(Ψ(x)) = Θ′((Φ_a ⊗ Φ_b)(x))。 -/
theorem fullCommMatrixEquiv_matTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (x : (Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) ⊗[ℂ]
      (Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ)) :
    fullCommMatrixEquiv (a * b) (matTensorEquiv hab x) =
      fullCommTensorEquiv hab (Algebra.TensorProduct.congr (fullCommMatrixEquiv a) (fullCommMatrixEquiv b) x) := by
  simp only [matTensorEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]

/-- **0c. Ψ の値は族のテンソル積** Ψ(M_a ⊗ M_b) = M_a ⊠ M_b（Part 234 の tensorFamily。両辺を Φ_{ab} と C で写すと、Part 229 の crtConj_fullCommTensorEquiv_tmul と Part 234 の crtConj_fullCommMatrixEquiv でどちらも L(Φ_a M_a)·R(Φ_b M_b) になる。C と Φ_{ab} は単射）。 -/
theorem matTensorEquiv_tmul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (Ma : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (Mb : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    matTensorEquiv hab (Ma ⊗ₜ[ℂ] Mb) = tensorFamily hab Ma Mb := by
  apply (fullCommMatrixEquiv (a * b)).injective
  apply Subtype.ext
  apply (crtConj hab).injective
  rw [fullCommMatrixEquiv_matTensorEquiv, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    crtConj_fullCommTensorEquiv_tmul]
  exact (crtConj_fullCommMatrixEquiv hab Ma Mb).symm

/-! ### 1. 族のテンソル積の性質 -/

/-- **1a.** (M_a + M′_a) ⊠ M_b = M_a ⊠ M_b + M′_a ⊠ M_b（0c と Ψ の線形性）。 -/
theorem tensorFamily_add_left {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (Ma Ma' : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (Mb : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    tensorFamily hab (Ma + Ma') Mb = tensorFamily hab Ma Mb + tensorFamily hab Ma' Mb := by
  rw [← matTensorEquiv_tmul, ← matTensorEquiv_tmul, ← matTensorEquiv_tmul, TensorProduct.add_tmul, map_add]

/-- **1b.** M_a ⊠ (M_b + M′_b) = M_a ⊠ M_b + M_a ⊠ M′_b。 -/
theorem tensorFamily_add_right {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (Ma : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (Mb Mb' : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    tensorFamily hab Ma (Mb + Mb') = tensorFamily hab Ma Mb + tensorFamily hab Ma Mb' := by
  rw [← matTensorEquiv_tmul, ← matTensorEquiv_tmul, ← matTensorEquiv_tmul, TensorProduct.tmul_add, map_add]

/-- **1c.** (c·M_a) ⊠ M_b = c·(M_a ⊠ M_b)。 -/
theorem tensorFamily_smul_left {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (c : ℂ)
    (Ma : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (Mb : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    tensorFamily hab (c • Ma) Mb = c • tensorFamily hab Ma Mb := by
  rw [← matTensorEquiv_tmul, ← matTensorEquiv_tmul, ← TensorProduct.smul_tmul', map_smul]

/-- **1d.** M_a ⊠ (c·M_b) = c·(M_a ⊠ M_b)。 -/
theorem tensorFamily_smul_right {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (c : ℂ)
    (Ma : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (Mb : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    tensorFamily hab Ma (c • Mb) = c • tensorFamily hab Ma Mb := by
  rw [← matTensorEquiv_tmul, ← matTensorEquiv_tmul, TensorProduct.tmul_smul, map_smul]

/-- **1e.** M_a ⊠ M_b の形の族は Π_r M_{m(c_r)} 全体を張る（Ψ は全射で、テンソル積は純テンソルで張られる）。 -/
theorem span_tensorFamily_eq_top {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Submodule.span ℂ (Set.range fun x : (Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) ×
        (Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) => tensorFamily hab x.1 x.2) = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  obtain ⟨x, rfl⟩ := (matTensorEquiv hab).surjective M
  induction x using TensorProduct.inductionOn with
  | tmul Ma Mb => rw [matTensorEquiv_tmul]; exact Submodule.subset_span ⟨(Ma, Mb), rfl⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- **1f.** dim Π_r M_{m(c_r)} = dim Π_p M_{m(c_p)}·dim Π_q M_{m(c_q)}（Ψ は線形同型）。 -/
theorem finrank_matrixPi_mul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ (Π r : centerIdx (a * b), Matrix (Prim r.1.1) (Prim r.1.1) ℂ) =
      Module.finrank ℂ (Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) *
        Module.finrank ℂ (Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) := by
  rw [← (matTensorEquiv hab).toLinearEquiv.finrank_eq, Module.finrank_tensorProduct]

/-- **1g.** Σ_{r ∈ S(ab)} m(c_r)² = (Σ_{p ∈ S(a)} m(c_p)²)·(Σ_{q ∈ S(b)} m(c_q)²)（1f を行列の大きさで書いたもの）。 -/
theorem sum_card_prim_sq_mul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    ∑ r : centerIdx (a * b), Fintype.card (Prim r.1.1) ^ 2 =
      (∑ p : centerIdx a, Fintype.card (Prim p.1.1) ^ 2) * ∑ q : centerIdx b, Fintype.card (Prim q.1.1) ^ 2 := by
  have h := finrank_matrixPi_mul hab
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one] at h
  simpa only [sq] using h

/-! ### 2. 中国剰余定理の図式 -/

/-- L ∘ Φ_a（代数の準同型 Π_p M_{m(c_p)} → End(ℂ^{ℤ/a × ℤ/b})）。 -/
noncomputable def leftMatHom (a b : ℕ) [NeZero a] :
    (Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) →ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  (leftHom a b).comp ((fullCommAlg a).val.comp (fullCommMatrixEquiv a).toAlgHom)

/-- R ∘ Φ_b（代数の準同型 Π_q M_{m(c_q)} → End(ℂ^{ℤ/a × ℤ/b})）。 -/
noncomputable def rightMatHom (a b : ℕ) [NeZero b] :
    (Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) →ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  (rightHom a b).comp ((fullCommAlg b).val.comp (fullCommMatrixEquiv b).toAlgHom)

/-- **2a.** (L ∘ Φ_a)(M_a) = L(Φ_a(M_a))。 -/
theorem leftMatHom_apply (a b : ℕ) [NeZero a] (Ma : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) :
    leftMatHom a b Ma = leftOp b (matSum a Ma) := rfl

/-- **2b.** (R ∘ Φ_b)(M_b) = R(Φ_b(M_b))。 -/
theorem rightMatHom_apply (a b : ℕ) [NeZero b] (Mb : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    rightMatHom a b Mb = rightOp a (matSum b Mb) := rfl

/-- **2c.** L ∘ Φ_a と R ∘ Φ_b の値は可換（Part 228 の leftOp_commute_rightOp）。 -/
theorem leftMatHom_commute_rightMatHom (a b : ℕ) [NeZero a] [NeZero b]
    (Ma : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (Mb : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    Commute (leftMatHom a b Ma) (rightMatHom a b Mb) :=
  leftOp_commute_rightOp _ _

/-- **2d. 中国剰余定理の図式** C ∘ Φ_{ab} ∘ Ψ = (L ∘ Φ_a) ⊗ (R ∘ Φ_b)（代数の準同型の等式。右辺は可換な 2 つの準同型から Mathlib の Algebra.TensorProduct.lift で作ったもの。純テンソルで比べれば 0c と Part 234 の crtConj_matSum_tensorFamily）。 -/
theorem crtConj_matTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (crtConj hab).toAlgHom.comp ((fullCommAlg (a * b)).val.comp
        ((fullCommMatrixEquiv (a * b)).toAlgHom.comp (matTensorEquiv hab).toAlgHom)) =
      Algebra.TensorProduct.lift (leftMatHom a b) (rightMatHom a b) (leftMatHom_commute_rightMatHom a b) := by
  apply Algebra.TensorProduct.ext'
  intro Ma Mb
  rw [Algebra.TensorProduct.lift_tmul, leftMatHom_apply, rightMatHom_apply]
  show crtConj hab (matSum (a * b) (matTensorEquiv hab (Ma ⊗ₜ[ℂ] Mb))) = leftOp b (matSum a Ma) * rightOp a (matSum b Mb)
  rw [matTensorEquiv_tmul]
  exact crtConj_matSum_tensorFamily hab Ma Mb

/-- **2e.** 2d の値の形：C(Φ_{ab}(Ψ(x))) = ((L ∘ Φ_a) ⊗ (R ∘ Φ_b))(x)。 -/
theorem crtConj_matTensorEquiv_apply {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (x : (Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) ⊗[ℂ]
      (Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ)) :
    crtConj hab (matSum (a * b) (matTensorEquiv hab x)) =
      Algebra.TensorProduct.lift (leftMatHom a b) (rightMatHom a b) (leftMatHom_commute_rightMatHom a b) x :=
  congrArg (fun F => F x) (crtConj_matTensorEquiv hab)

/-! ### 3. 中心の極小べき等元 -/

/-- **3a.** Ψ(1_p ⊗ 1_q) = 1_r（r ↔ (p, q)。Part 223 の matSum_single_one で Φ(1_p) = z_p となり、Part 232 の crtConj_centralElt で C(z_r) = L(z_p)R(z_q)）。 -/
theorem matTensorEquiv_single_one {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (p : centerIdx a)
    (q : centerIdx b) :
    matTensorEquiv hab ((Pi.single p 1 : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) ⊗ₜ[ℂ]
        (Pi.single q 1 : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ)) =
      Pi.single ((centerIdxEquiv hab).symm (p, q)) 1 := by
  apply (fullCommMatrixEquiv (a * b)).injective
  apply Subtype.ext
  apply (crtConj hab).injective
  rw [fullCommMatrixEquiv_matTensorEquiv, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    crtConj_fullCommTensorEquiv_tmul]
  show leftOp b (matSum a (Pi.single p 1)) * rightOp a (matSum b (Pi.single q 1)) =
    crtConj hab (matSum (a * b) (Pi.single ((centerIdxEquiv hab).symm (p, q)) 1))
  rw [matSum_single_one, matSum_single_one, matSum_single_one]
  exact (crtConj_centralElt hab (ca := p.1.1) (da := p.1.2) (cb := q.1.1) (db := q.1.2) p.2 q.2).symm

end PAG.Part239

#print axioms PAG.Part239.matTensorEquiv
#print axioms PAG.Part239.fullCommMatrixEquiv_coe
#print axioms PAG.Part239.fullCommMatrixEquiv_matTensorEquiv
#print axioms PAG.Part239.matTensorEquiv_tmul
#print axioms PAG.Part239.tensorFamily_add_left
#print axioms PAG.Part239.tensorFamily_add_right
#print axioms PAG.Part239.tensorFamily_smul_left
#print axioms PAG.Part239.tensorFamily_smul_right
#print axioms PAG.Part239.span_tensorFamily_eq_top
#print axioms PAG.Part239.finrank_matrixPi_mul
#print axioms PAG.Part239.sum_card_prim_sq_mul
#print axioms PAG.Part239.leftMatHom
#print axioms PAG.Part239.rightMatHom
#print axioms PAG.Part239.leftMatHom_apply
#print axioms PAG.Part239.rightMatHom_apply
#print axioms PAG.Part239.leftMatHom_commute_rightMatHom
#print axioms PAG.Part239.crtConj_matTensorEquiv
#print axioms PAG.Part239.crtConj_matTensorEquiv_apply
#print axioms PAG.Part239.matTensorEquiv_single_one
