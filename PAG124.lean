/-
  PAG 2.0 Part 120（2026-10-20）— n 個の素数の積のケットの特性多項式
  （4 は任意の関数 k_i について成り立つ。原始ケットの場合が主な応用）
  1. n 重の指標 Ψ_v = ⊗ ψ_{v_i} は畳み込み ⊗k_i の固有ベクトル（固有値 ∏ 𝓕k_i(v_i)）
  2. 直交性 Σ Ψ_v Ψ_{−w} = (∏ N_i)[v = w] ⇒ 線形独立
  3. {Ψ_v : v ∈ ∏ T_{a_i}} は V_𝐚 = range((⊗ε_{a_i})⋆) の基底（次元は Part 109）
  4. charpoly((⊗k_i)⋆|V_𝐚) = ∏_{v ∈ ∏T_{a_i}} (X − ∏_i 𝓕k_i(v_i))
-/
import PAG123

namespace PAG.Part124

open ZMod Finset Polynomial PAG.Part15 PAG.Part109 PAG.Part110 PAG.Part113 PAG.Part121

section Gen

variable {n : ℕ} {N : Fin n → ℕ} [∀ i, NeZero (N i)]

/-- n 重の指標。 -/
noncomputable def pchr (v : ∀ i, ZMod (N i)) : (∀ i, ZMod (N i)) → ℂ := ptens (fun i => chr (v i))

omit [∀ i, NeZero (N i)] in
theorem ptens_smul (c : Fin n → ℂ) (f : ∀ i, ZMod (N i) → ℂ) :
    ptens (fun i => c i • f i) = (∏ i, c i) • ptens f := by
  funext x; simp only [ptens, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- **1. 固有ベクトル**。 -/
theorem conv_ptens_pchr (k : ∀ i, ZMod (N i) → ℂ) (v : ∀ i, ZMod (N i)) :
    conv (ptens k) (pchr v) = (∏ i, 𝓕 (k i) (v i)) • pchr v := by
  rw [pchr, conv_ptens]
  simp only [conv_chr]
  exact ptens_smul _ _

/-- **2a. 直交性**。 -/
theorem sum_pchr_mul (v w : ∀ i, ZMod (N i)) :
    ∑ x, pchr v x * pchr (-w) x = if v = w then ((∏ i, N i : ℕ) : ℂ) else 0 := by
  have e : ∀ x : (∀ i, ZMod (N i)), pchr v x * pchr (-w) x = ∏ i, (chr (v i) (x i) * chr (-(w i)) (x i)) := by
    intro x; simp only [pchr, ptens, Pi.neg_apply, Finset.prod_mul_distrib]
  simp only [e]
  rw [← Fintype.prod_sum (fun i y => chr (v i) y * chr (-(w i)) y)]
  simp only [sum_chr_mul]
  by_cases h : v = w
  · subst h; simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ w i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [ite_eq_right_of_eq_false _ _ (eq_false hi)])

/-- **2b. 線形独立**。 -/
theorem pchr_linearIndependent {ι : Type*} [Fintype ι] (u : ι → ∀ i, ZMod (N i)) (hu : Function.Injective u) :
    LinearIndependent ℂ (fun j => pchr (u j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun F => ∑ z, F z * pchr (-(u j)) z) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
  simp only [Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  simp only [mul_assoc, ← Finset.mul_sum, sum_pchr_mul, hu.eq_iff, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  have hN : ((∏ i, N i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (N i)
  exact (mul_eq_zero.mp h).resolve_right hN

end Gen

/-! ## 3–4. 素数の族 -/

section Ket

open PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part95

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K a : Fin n → ℕ)

/-- V_𝐚。 -/
noncomputable abbrev Vn : Submodule ℂ ((∀ i, ZMod (p i ^ K i)) → ℂ) :=
  LinearMap.range (convL (ptens (fun i => eps (p := p i) (K i) (a i))))

/-- 添字 ∏ T_{a_i}。 -/
abbrev Idxn := ∀ i, (Tset (p := p i) (K i) (a i))

theorem pchr_mem (ha : ∀ i, a i ≤ K i) (v : Idxn p K a) :
    pchr (N := fun i => p i ^ K i) (fun i => (v i : ZMod (p i ^ K i))) ∈ Vn p K a := by
  have hidem : conv (ptens (fun i => eps (p := p i) (K i) (a i))) (ptens (fun i => eps (p := p i) (K i) (a i)))
      = ptens (fun i => eps (p := p i) (K i) (a i)) := by
    rw [conv_ptens]; simp only [fun i => eps_idem (p := p i) (K i) (a i) (ha i)]
  rw [mem_range_convL _ hidem, conv_ptens_pchr]
  have h1 : ∀ i, 𝓕 (eps (p := p i) (K i) (a i)) (v i : ZMod (p i ^ K i)) = 1 :=
    fun i => (Finset.mem_filter.mp (v i).2).2
  simp only [h1, Finset.prod_const_one, one_smul]

/-- 次元の一致。 -/
theorem card_Idxn (ha : ∀ i, a i ≤ K i) :
    Fintype.card (Idxn p K a) = Module.finrank ℂ (Vn p K a) := by
  rw [Fintype.card_pi, Vn, finrank_ptens (G := fun i => ZMod (p i ^ K i)) _
    (fun i => eps_idem (p := p i) (K i) (a i) (ha i))]
  apply Finset.prod_congr rfl; intro i _
  rw [Fintype.card_coe, range_convL_eps (K i) (a i) (ha i), finrank_Va (K i) (a i) (ha i)]

/-- 基底。 -/
noncomputable def basisN (ha : ∀ i, a i ≤ K i)
    (hcard : Fintype.card (Idxn p K a) = Module.finrank ℂ (Vn p K a)) :
    Module.Basis (Idxn p K a) ℂ (Vn p K a) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun v => ⟨pchr (N := fun i => p i ^ K i) (fun i => (v i : ZMod (p i ^ K i))), pchr_mem p K a ha v⟩)
    (by
      apply LinearIndependent.of_comp (Vn p K a).subtype
      exact pchr_linearIndependent (N := fun i => p i ^ K i)
        (fun v : Idxn p K a => fun i => (v i : ZMod (p i ^ K i)))
        (fun v v' hv => funext fun i => Subtype.ext (congrFun hv i)))
    hcard

/-- 積の作用素の制限。 -/
noncomputable def Tn (ha : ∀ i, a i ≤ K i) (k : ∀ i, ZMod (p i ^ K i) → ℂ) : Module.End ℂ (Vn p K a) :=
  (convL (ptens k)).restrict (fun f hf => by
    have hidem : conv (ptens (fun i => eps (p := p i) (K i) (a i))) (ptens (fun i => eps (p := p i) (K i) (a i)))
        = ptens (fun i => eps (p := p i) (K i) (a i)) := by
      rw [conv_ptens]; simp only [fun i => eps_idem (p := p i) (K i) (a i) (ha i)]
    exact (mem_range_convL _ hidem _).mpr (PAG.Part111.fix_conv _ _ f ((mem_range_convL _ hidem f).mp hf)))

/-- **4. n 個の素数の積の作用素の特性多項式**（k_i は任意の関数。原始ケットに限らない）。 -/
theorem charpoly_Tn (haK : ∀ i, a i ≤ K i) (k : ∀ i, ZMod (p i ^ K i) → ℂ) :
    (Tn p K a haK k).charpoly = ∏ v : Idxn p K a, (X - C (∏ i, 𝓕 (k i) (v i : ZMod (p i ^ K i)))) := by
  classical
  set B := basisN p K a haK (card_Idxn p K a haK)
  set lam : Idxn p K a → ℂ := fun v => ∏ i, 𝓕 (k i) (v i : ZMod (p i ^ K i))
  have hB : ∀ v, (B v : (∀ i, ZMod (p i ^ K i)) → ℂ)
      = pchr (N := fun i => p i ^ K i) (fun i => (v i : ZMod (p i ^ K i))) := by
    intro v; simp [B, basisN]
  have hT : ∀ v, Tn p K a haK k (B v) = lam v • B v := by
    intro v
    apply Subtype.ext
    show conv (ptens k) (B v : (∀ i, ZMod (p i ^ K i)) → ℂ) = lam v • (B v : (∀ i, ZMod (p i ^ K i)) → ℂ)
    rw [hB, conv_ptens_pchr]
  have hmat : LinearMap.toMatrix B B (Tn p K a haK k) = Matrix.diagonal lam := by
    ext v v'
    rw [LinearMap.toMatrix_apply, hT, _root_.map_smul, B.repr_self, Finsupp.smul_apply, Matrix.diagonal_apply,
      Finsupp.single_apply]
    by_cases hvv : v' = v
    · subst hvv; simp
    · simp [hvv, Ne.symm hvv]
  rw [← LinearMap.charpoly_toMatrix _ B, hmat, Matrix.charpoly_diagonal]

end Ket

end PAG.Part124

#print axioms PAG.Part124.ptens_smul
#print axioms PAG.Part124.conv_ptens_pchr
#print axioms PAG.Part124.sum_pchr_mul
#print axioms PAG.Part124.pchr_linearIndependent
#print axioms PAG.Part124.pchr_mem
#print axioms PAG.Part124.card_Idxn
#print axioms PAG.Part124.charpoly_Tn
