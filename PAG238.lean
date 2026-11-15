/-
  PAG 2.0 Part 234（2026-10-31）— 行列環の同型 Π_p M_{m(c_p)}(ℂ) ≅ A′ と中国剰余定理の整合（ゲージつきクロネッカー積）
  Φ(M) = Σ_{p ∈ S} Σ_{i,j} M_p(i, j)·E^{d_p}_{χ_j→χ_i}（Part 223 の matSum・fullCommMatrixEquiv）、C・L・R（Part 228）、
  Prim(c_a) × Prim(c_b) ≅ Prim(c_a c_b)（Part 232 の primEquiv）、ゲージ g(χ_a, χ_b) = χ_a(d_b)·χ_b(d_a)（Part 233 の
  gaugeFactor）、ゲージで直した行列単位の分解 C(Ẽ) = L(E)R(E)（Part 233 の crtConj_gaugeUnit）
  0. 1 つのブロックの像 Φ_{(c,d)}(A) = Σ_{i,j} A(i, j)·E^d_{χ_j→χ_i}（def blockSum）。Φ(M) = Σ_p Φ_p(M_p)。
     番号が等しければ（c = c′、d = d′）、行列の番号を付け替えても像は同じ
  1. ゲージつきクロネッカー積 (A ⊠_g B)(χ_i⊠χ_k, χ_j⊠χ_l) = (g(i,k)/g(j,l))·A(i,j)·B(k,l)（def kronG）。
     A ⊠_g B = D·(A ⊗ B を primEquiv で並べ替えたもの)·D⁻¹（D はゲージの対角行列）。積と 1 を保つ
  2. 1 つのブロックの分解：C(Φ^{ab}_{(c_a c_b, d_a d_b)}(A ⊠_g B)) = L(Φ^a_{(c_a,d_a)}(A))·R(Φ^b_{(c_b,d_b)}(B))
  3. 番号の同値 S(ab) ≅ S(a) × S(b)（def centerIdxEquiv、Part 229 の idxSplit・idxMul）と、族のテンソル積
     (M_a ⊠ M_b)_r = M_a(p) ⊠_g M_b(q)（def tensorFamily、r ↔ (p, q)）。C(Φ^{ab}(M_a ⊠ M_b)) = L(Φ^a(M_a))·R(Φ^b(M_b))。
     M_a ⊠ M_b は積と 1 を保つ
-/
import PAG237

namespace PAG.Part238

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part231 PAG.Part232 PAG.Part233 PAG.Part234
  PAG.Part235 PAG.Part236 PAG.Part237
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 1 つのブロックの像 -/

/-- 1 つのブロックの像 Φ_{(c,d)}(A) = Σ_{i,j} A(i, j)·E^d_{χ_j→χ_i}（A は Prim(c) で番号を付けた行列）。 -/
noncomputable def blockSum (N c d : ℕ) [NeZero N] [NeZero c] (A : Matrix (Prim c) (Prim c) ℂ) :
    Module.End ℂ (ZMod N → ℂ) :=
  ∑ i : Prim c, ∑ j : Prim c, A i j • matUnit N c d j.1 i.1

/-- **0a.** Φ(M) = Σ_{p ∈ S} Φ_p(M_p)（Part 223 の matSum の定義）。 -/
theorem matSum_eq_sum_blockSum (N : ℕ) [NeZero N] (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) :
    matSum N M = ∑ p : centerIdx N, blockSum N p.1.1 p.1.2 (M p) := rfl

/-- **0b.** c = c′、d = d′ なら、行列の番号を Prim(c) ≅ Prim(c′) で付け替えた Φ_{(c,d)} は Φ_{(c′,d′)} に等しい。 -/
theorem blockSum_cast {N c c' d d' : ℕ} [NeZero N] [NeZero c] [NeZero c'] (hc : c = c') (hd : d = d')
    (A : Matrix (Prim c') (Prim c') ℂ) :
    blockSum N c d (A.submatrix (Equiv.cast (congrArg Prim hc)) (Equiv.cast (congrArg Prim hc))) =
      blockSum N c' d' A := by
  subst hc hd
  rfl

/-! ### 1. ゲージつきクロネッカー積 -/

/-- 組 (χ_a, χ_b) のゲージ g = χ_a(d_b)·χ_b(d_a)（Part 233 の gaugeFactor）。 -/
noncomputable def gaugeP {ca cb : ℕ} (da db : ℕ) (x : Prim ca × Prim cb) : ℂ := gaugeFactor da db x.1.1 x.2.1

/-- **1a.** primEquiv (χ_a, χ_b) = χ_a ⊠ χ_b（定義から）。 -/
theorem primEquiv_apply_val {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n) (x : Prim m × Prim n) :
    ((primEquiv hmn x : Prim (m * n)) : DirichletCharacter ℂ (m * n)) = charMul x.1.1 x.2.1 := rfl

/-- ゲージつきクロネッカー積 (A ⊠_g B)(χ, χ′) = (g(x)/g(y))·A(x₁, y₁)·B(x₂, y₂)（χ = x₁ ⊠ x₂、χ′ = y₁ ⊠ y₂）。 -/
noncomputable def kronG {ca cb : ℕ} [NeZero ca] [NeZero cb] (hcop : Nat.Coprime ca cb) (da db : ℕ)
    (A : Matrix (Prim ca) (Prim ca) ℂ) (B : Matrix (Prim cb) (Prim cb) ℂ) :
    Matrix (Prim (ca * cb)) (Prim (ca * cb)) ℂ :=
  fun χ χ' => (gaugeP da db ((primEquiv hcop).symm χ) / gaugeP da db ((primEquiv hcop).symm χ')) *
    (A ((primEquiv hcop).symm χ).1 ((primEquiv hcop).symm χ').1 *
      B ((primEquiv hcop).symm χ).2 ((primEquiv hcop).symm χ').2)

/-- **1b.** (A ⊠_g B)(x₁ ⊠ x₂, y₁ ⊠ y₂) = (g(x)/g(y))·A(x₁, y₁)·B(x₂, y₂)。 -/
theorem kronG_apply {ca cb : ℕ} [NeZero ca] [NeZero cb] (hcop : Nat.Coprime ca cb) (da db : ℕ)
    (A : Matrix (Prim ca) (Prim ca) ℂ) (B : Matrix (Prim cb) (Prim cb) ℂ) (x y : Prim ca × Prim cb) :
    kronG hcop da db A B (primEquiv hcop x) (primEquiv hcop y) =
      (gaugeP da db x / gaugeP da db y) * (A x.1 y.1 * B x.2 y.2) := by
  simp only [kronG, Equiv.symm_apply_apply]

/-- **1c.** A ⊠_g B = D·(A ⊗ B を primEquiv で並べ替えたもの)·D⁻¹（D はゲージの対角行列。Mathlib の kroneckerMap・reindex）。 -/
theorem kronG_eq {ca cb : ℕ} [NeZero ca] [NeZero cb] (hcop : Nat.Coprime ca cb) (da db : ℕ)
    (A : Matrix (Prim ca) (Prim ca) ℂ) (B : Matrix (Prim cb) (Prim cb) ℂ) :
    kronG hcop da db A B = Matrix.diagonal (fun χ => gaugeP da db ((primEquiv hcop).symm χ)) *
      Matrix.reindex (primEquiv hcop) (primEquiv hcop) (Matrix.kroneckerMap (· * ·) A B) *
        Matrix.diagonal (fun χ => (gaugeP da db ((primEquiv hcop).symm χ))⁻¹) := by
  ext χ χ'
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  simp only [kronG]
  rw [div_eq_mul_inv]
  ring

/-- **1d.** (c_a, d_a) ∈ S(a)、(c_b, d_b) ∈ S(b) なら g ≠ 0（Part 233 の gaugeFactor_ne_zero）。 -/
theorem gaugeP_ne_zero {a b : ℕ} (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    (x : Prim ca × Prim cb) : gaugeP da db x ≠ 0 := by
  obtain ⟨hca, -, -, hda, -⟩ := (mem_centerIdx_iff_dvd a ca da).mp hp
  obtain ⟨hcb, -, -, hdb, -⟩ := (mem_centerIdx_iff_dvd b cb db).mp hq
  exact gaugeFactor_ne_zero hab hca hcb (Nat.dvd_trans hda (Nat.div_dvd_of_dvd hca))
    (Nat.dvd_trans hdb (Nat.div_dvd_of_dvd hcb)) x.1.1 x.2.1

/-- **1e.** ⊠_g は積を保つ：(A ⊠_g B)(A′ ⊠_g B′) = (AA′) ⊠_g (BB′)（g ≠ 0。中の和を primEquiv で並べ替え、ゲージは打ち消し合う）。 -/
theorem kronG_mul {ca cb : ℕ} [NeZero ca] [NeZero cb] (hcop : Nat.Coprime ca cb) (da db : ℕ)
    (hg : ∀ x : Prim ca × Prim cb, gaugeP da db x ≠ 0)
    (A A' : Matrix (Prim ca) (Prim ca) ℂ) (B B' : Matrix (Prim cb) (Prim cb) ℂ) :
    kronG hcop da db A B * kronG hcop da db A' B' = kronG hcop da db (A * A') (B * B') := by
  ext χ χ''
  obtain ⟨x, rfl⟩ := (primEquiv hcop).surjective χ
  obtain ⟨z, rfl⟩ := (primEquiv hcop).surjective χ''
  rw [kronG_apply, Matrix.mul_apply, ← Equiv.sum_comp (primEquiv hcop)]
  simp only [kronG_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Fintype.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h1 := hg (j, l)
  field_simp

/-- **1f.** 1 ⊠_g 1 = 1。 -/
theorem kronG_one {ca cb : ℕ} [NeZero ca] [NeZero cb] (hcop : Nat.Coprime ca cb) (da db : ℕ)
    (hg : ∀ x : Prim ca × Prim cb, gaugeP da db x ≠ 0) :
    kronG hcop da db (1 : Matrix (Prim ca) (Prim ca) ℂ) (1 : Matrix (Prim cb) (Prim cb) ℂ) = 1 := by
  ext χ χ'
  obtain ⟨x, rfl⟩ := (primEquiv hcop).surjective χ
  obtain ⟨y, rfl⟩ := (primEquiv hcop).surjective χ'
  rw [kronG_apply]
  by_cases h : x = y
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq, div_self (hg x), one_mul, one_mul]
  · rw [Matrix.one_apply_ne (fun e => h ((primEquiv hcop).injective e))]
    by_cases h1 : x.1 = y.1
    · have h2 : x.2 ≠ y.2 := fun h2 => h (Prod.ext h1 h2)
      rw [Matrix.one_apply_ne h2, mul_zero, mul_zero]
    · rw [Matrix.one_apply_ne h1, zero_mul, mul_zero]

/-! ### 2. 1 つのブロックの分解 -/

/-- **2a. 1 つのブロックの分解** C(Φ^{ab}_{(c_a c_b, d_a d_b)}(A ⊠_g B)) = L(Φ^a_{(c_a,d_a)}(A))·R(Φ^b_{(c_b,d_b)}(B))（右辺を行列単位の積の和に展開し、Part 233 の crtConj_gaugeUnit で各項を C の像に直す。左辺の和は primEquiv で並べ替える）。 -/
theorem crtConj_blockSum {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca] [NeZero cb] (hcop : Nat.Coprime ca cb)
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    (A : Matrix (Prim ca) (Prim ca) ℂ) (B : Matrix (Prim cb) (Prim cb) ℂ) :
    crtConj hab (blockSum (a * b) (ca * cb) (da * db) (kronG hcop da db A B)) =
      leftOp b (blockSum a ca da A) * rightOp a (blockSum b cb db B) := by
  have hL : leftOp b (blockSum a ca da A) = ∑ i : Prim ca, ∑ j : Prim ca, A i j • leftOp b (matUnit a ca da j.1 i.1) := by
    show leftHom a b (blockSum a ca da A) = _
    simp only [blockSum, map_sum, map_smul]
    rfl
  have hR : rightOp a (blockSum b cb db B) = ∑ k : Prim cb, ∑ l : Prim cb, B k l • rightOp a (matUnit b cb db l.1 k.1) := by
    show rightHom a b (blockSum b cb db B) = _
    simp only [blockSum, map_sum, map_smul]
    rfl
  rw [hL, hR]
  simp only [Fintype.sum_mul_sum, smul_mul_smul_comm]
  calc crtConj hab (blockSum (a * b) (ca * cb) (da * db) (kronG hcop da db A B))
      = ∑ χ : Prim (ca * cb), ∑ χ' : Prim (ca * cb),
          kronG hcop da db A B χ χ' • crtConj hab (matUnit (a * b) (ca * cb) (da * db) χ'.1 χ.1) := by
        simp only [blockSum, map_sum, map_smul]
    _ = ∑ x : Prim ca × Prim cb, ∑ y : Prim ca × Prim cb,
          kronG hcop da db A B (primEquiv hcop x) (primEquiv hcop y) •
            crtConj hab (matUnit (a * b) (ca * cb) (da * db) (primEquiv hcop y).1 (primEquiv hcop x).1) := by
        rw [← Equiv.sum_comp (primEquiv hcop)]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Equiv.sum_comp (primEquiv hcop)]
    _ = ∑ i : Prim ca, ∑ k : Prim cb, ∑ j : Prim ca, ∑ l : Prim cb,
          ((gaugeP da db (i, k) / gaugeP da db (j, l)) * (A i j * B k l)) •
            crtConj hab (matUnit (a * b) (ca * cb) (da * db) (charMul j.1 l.1) (charMul i.1 k.1)) := by
        simp only [Fintype.sum_prod_type, kronG_apply, primEquiv_apply_val]
    _ = ∑ i : Prim ca, ∑ k : Prim cb, ∑ j : Prim ca, ∑ l : Prim cb,
          (A i j * B k l) • (leftOp b (matUnit a ca da j.1 i.1) * rightOp a (matUnit b cb db l.1 k.1)) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ =>
          Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))))
        rw [← crtConj_gaugeUnit hab hp hq j.2 l.2 i.1 k.1, gaugeUnit, map_smul, smul_smul, mul_comm]
        rfl

/-! ### 3. 行列の族と番号の同値 -/

/-- **3a.** p ∈ S(a)、q ∈ S(b)、gcd(a, b) = 1 なら gcd(c_p, c_q) = 1。 -/
theorem coprime_of_mem_centerIdx {a b : ℕ} (hab : Nat.Coprime a b) {p q : Σ _ : ℕ, ℕ} (hp : p ∈ centerIdx a)
    (hq : q ∈ centerIdx b) : Nat.Coprime p.1 q.1 :=
  Nat.Coprime.coprime_dvd_right ((mem_centerIdx_iff_dvd b q.1 q.2).mp hq).1
    (Nat.Coprime.coprime_dvd_left ((mem_centerIdx_iff_dvd a p.1 p.2).mp hp).1 hab)

/-- 番号の同値 S(ab) ≅ S(a) × S(b)：(c, d) ↦ ((gcd(c,a), gcd(d,a)), (gcd(c,b), gcd(d,b)))、逆は (p, q) ↦ (c_p c_q, d_p d_q)（Part 229 の idxSplit・idxMul）。 -/
noncomputable def centerIdxEquiv {a b : ℕ} (hab : Nat.Coprime a b) : centerIdx (a * b) ≃ centerIdx a × centerIdx b where
  toFun r := (⟨(idxSplit a b r.1).1, (idxSplit_mem hab (c := r.1.1) (d := r.1.2) r.2).1⟩,
    ⟨(idxSplit a b r.1).2, (idxSplit_mem hab (c := r.1.1) (d := r.1.2) r.2).2⟩)
  invFun pq := ⟨idxMul pq.1.1 pq.2.1,
    idxMul_mem_centerIdx hab (ca := pq.1.1.1) (da := pq.1.1.2) (cb := pq.2.1.1) (db := pq.2.1.2) pq.1.2 pq.2.2⟩
  left_inv r := Subtype.ext (idxMul_idxSplit hab (c := r.1.1) (d := r.1.2) r.2)
  right_inv pq := by
    obtain ⟨⟨⟨ca, da⟩, hp⟩, ⟨⟨cb, db⟩, hq⟩⟩ := pq
    have h := idxSplit_idxMul hab hp hq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- **3b.** 第 1 成分は (gcd(c, a), gcd(d, a))。 -/
theorem centerIdxEquiv_apply_fst {a b : ℕ} (hab : Nat.Coprime a b) (r : centerIdx (a * b)) :
    ((centerIdxEquiv hab r).1 : Σ _ : ℕ, ℕ) = ⟨Nat.gcd r.1.1 a, Nat.gcd r.1.2 a⟩ := rfl

/-- **3c.** 第 2 成分は (gcd(c, b), gcd(d, b))。 -/
theorem centerIdxEquiv_apply_snd {a b : ℕ} (hab : Nat.Coprime a b) (r : centerIdx (a * b)) :
    ((centerIdxEquiv hab r).2 : Σ _ : ℕ, ℕ) = ⟨Nat.gcd r.1.1 b, Nat.gcd r.1.2 b⟩ := rfl

/-- **3d.** 逆の値は (c_p c_q, d_p d_q)。 -/
theorem centerIdxEquiv_symm_apply {a b : ℕ} (hab : Nat.Coprime a b) (pq : centerIdx a × centerIdx b) :
    (((centerIdxEquiv hab).symm pq : centerIdx (a * b)) : Σ _ : ℕ, ℕ) = idxMul pq.1.1 pq.2.1 := rfl

/-- **3e.** r = (c, d) ↔ (p, q) なら c = c_p·c_q。 -/
theorem centerIdxEquiv_fst_mul {a b : ℕ} (hab : Nat.Coprime a b) (r : centerIdx (a * b)) :
    r.1.1 = (centerIdxEquiv hab r).1.1.1 * (centerIdxEquiv hab r).2.1.1 :=
  (congrArg (fun s : Σ _ : ℕ, ℕ => s.1) (congrArg Subtype.val ((centerIdxEquiv hab).symm_apply_apply r))).symm

/-- **3f.** 同じく d = d_p·d_q。 -/
theorem centerIdxEquiv_snd_mul {a b : ℕ} (hab : Nat.Coprime a b) (r : centerIdx (a * b)) :
    r.1.2 = (centerIdxEquiv hab r).1.1.2 * (centerIdxEquiv hab r).2.1.2 :=
  (congrArg (fun s : Σ _ : ℕ, ℕ => s.2) (congrArg Subtype.val ((centerIdxEquiv hab).symm_apply_apply r))).symm

/-- 族のテンソル積 (M_a ⊠ M_b)_r = M_a(p) ⊠_g M_b(q)（r ↔ (p, q)。法 c_r と c_p c_q の番号の付け替えは 3e による）。 -/
noncomputable def tensorFamily {a b : ℕ} (hab : Nat.Coprime a b)
    (Ma : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (Mb : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    Π r : centerIdx (a * b), Matrix (Prim r.1.1) (Prim r.1.1) ℂ :=
  fun r => (kronG (coprime_of_mem_centerIdx hab (centerIdxEquiv hab r).1.2 (centerIdxEquiv hab r).2.2)
      (centerIdxEquiv hab r).1.1.2 (centerIdxEquiv hab r).2.1.2
      (Ma (centerIdxEquiv hab r).1) (Mb (centerIdxEquiv hab r).2)).submatrix
    (Equiv.cast (congrArg Prim (centerIdxEquiv_fst_mul hab r)))
    (Equiv.cast (congrArg Prim (centerIdxEquiv_fst_mul hab r)))

/-- **3g.** M_a ⊠ M_b は積を保つ：(M_a M′_a) ⊠ (M_b M′_b) = (M_a ⊠ M_b)(M′_a ⊠ M′_b)（1e と Mathlib の submatrix_mul_equiv）。 -/
theorem tensorFamily_mul {a b : ℕ} (hab : Nat.Coprime a b)
    (Ma Ma' : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (Mb Mb' : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    tensorFamily hab (Ma * Ma') (Mb * Mb') = tensorFamily hab Ma Mb * tensorFamily hab Ma' Mb' := by
  funext r
  simp only [tensorFamily, Pi.mul_apply]
  rw [Matrix.submatrix_mul_equiv, kronG_mul _ _ _
    (gaugeP_ne_zero hab (ca := (centerIdxEquiv hab r).1.1.1) (da := (centerIdxEquiv hab r).1.1.2)
      (cb := (centerIdxEquiv hab r).2.1.1) (db := (centerIdxEquiv hab r).2.1.2)
      (centerIdxEquiv hab r).1.2 (centerIdxEquiv hab r).2.2)]

/-- **3h.** 1 ⊠ 1 = 1。 -/
theorem tensorFamily_one {a b : ℕ} (hab : Nat.Coprime a b) :
    tensorFamily hab (1 : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
      (1 : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) = 1 := by
  funext r
  simp only [tensorFamily, Pi.one_apply]
  rw [kronG_one _ _ _
    (gaugeP_ne_zero hab (ca := (centerIdxEquiv hab r).1.1.1) (da := (centerIdxEquiv hab r).1.1.2)
      (cb := (centerIdxEquiv hab r).2.1.1) (db := (centerIdxEquiv hab r).2.1.2)
      (centerIdxEquiv hab r).1.2 (centerIdxEquiv hab r).2.2), Matrix.submatrix_one_equiv]

/-- **3i. 行列環の同型と中国剰余定理の整合** C(Φ^{ab}(M_a ⊠ M_b)) = L(Φ^a(M_a))·R(Φ^b(M_b))（0a・0b・2a と、S(ab) ≅ S(a) × S(b) による和の並べ替え）。 -/
theorem crtConj_matSum_tensorFamily {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    (hab : Nat.Coprime a b) (Ma : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (Mb : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    crtConj hab (matSum (a * b) (tensorFamily hab Ma Mb)) = leftOp b (matSum a Ma) * rightOp a (matSum b Mb) := by
  rw [matSum_eq_sum_blockSum, matSum_eq_sum_blockSum, matSum_eq_sum_blockSum, map_sum]
  have hL : leftOp b (∑ p : centerIdx a, blockSum a p.1.1 p.1.2 (Ma p)) =
      ∑ p : centerIdx a, leftOp b (blockSum a p.1.1 p.1.2 (Ma p)) := map_sum (leftHom a b) _ _
  have hR : rightOp a (∑ q : centerIdx b, blockSum b q.1.1 q.1.2 (Mb q)) =
      ∑ q : centerIdx b, rightOp a (blockSum b q.1.1 q.1.2 (Mb q)) := map_sum (rightHom a b) _ _
  rw [hL, hR, Fintype.sum_mul_sum, ← Fintype.sum_prod_type', ← Equiv.sum_comp (centerIdxEquiv hab)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [tensorFamily, blockSum_cast (centerIdxEquiv_fst_mul hab r) (centerIdxEquiv_snd_mul hab r)]
  exact crtConj_blockSum hab (ca := (centerIdxEquiv hab r).1.1.1) (da := (centerIdxEquiv hab r).1.1.2)
    (cb := (centerIdxEquiv hab r).2.1.1) (db := (centerIdxEquiv hab r).2.1.2) _
    (centerIdxEquiv hab r).1.2 (centerIdxEquiv hab r).2.2 _ _

/-- **3j.** 代数の同型 Π_p M_{m(c_p)}(ℂ) ≅ A′（Part 223 の fullCommMatrixEquiv）で書いても同じ：C(Φ_{ab}(M_a ⊠ M_b)) = L(Φ_a(M_a))·R(Φ_b(M_b))。 -/
theorem crtConj_fullCommMatrixEquiv {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)]
    [Fintype (BlockIdx b)] (hab : Nat.Coprime a b) (Ma : Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (Mb : Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) :
    crtConj hab (fullCommMatrixEquiv (a * b) (tensorFamily hab Ma Mb) : Module.End ℂ (ZMod (a * b) → ℂ)) =
      leftOp b (fullCommMatrixEquiv a Ma : Module.End ℂ (ZMod a → ℂ)) *
        rightOp a (fullCommMatrixEquiv b Mb : Module.End ℂ (ZMod b → ℂ)) :=
  crtConj_matSum_tensorFamily hab Ma Mb

end PAG.Part238

#print axioms PAG.Part238.blockSum
#print axioms PAG.Part238.matSum_eq_sum_blockSum
#print axioms PAG.Part238.blockSum_cast
#print axioms PAG.Part238.gaugeP
#print axioms PAG.Part238.primEquiv_apply_val
#print axioms PAG.Part238.kronG
#print axioms PAG.Part238.kronG_apply
#print axioms PAG.Part238.kronG_eq
#print axioms PAG.Part238.gaugeP_ne_zero
#print axioms PAG.Part238.kronG_mul
#print axioms PAG.Part238.kronG_one
#print axioms PAG.Part238.crtConj_blockSum
#print axioms PAG.Part238.coprime_of_mem_centerIdx
#print axioms PAG.Part238.centerIdxEquiv
#print axioms PAG.Part238.centerIdxEquiv_apply_fst
#print axioms PAG.Part238.centerIdxEquiv_apply_snd
#print axioms PAG.Part238.centerIdxEquiv_symm_apply
#print axioms PAG.Part238.centerIdxEquiv_fst_mul
#print axioms PAG.Part238.centerIdxEquiv_snd_mul
#print axioms PAG.Part238.tensorFamily
#print axioms PAG.Part238.tensorFamily_mul
#print axioms PAG.Part238.tensorFamily_one
#print axioms PAG.Part238.crtConj_matSum_tensorFamily
#print axioms PAG.Part238.crtConj_fullCommMatrixEquiv
