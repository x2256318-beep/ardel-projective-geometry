/-
  PAG 2.0 Part 108（2026-10-19）— n 個の素数での巡回構造: (⊗k_i)^{⋆m} がスカラー ⟺ lcm_i ord χ_i ∣ m
  1. Scalar は加法同型で不変
  2. 正の倍率の等長は単射
  3. n 重の積のスカラー性: Scalar (⊗e_i) (⊗A_i) ⟺ ∀ i, Scalar e_i A_i（A_i は V_i 上で正の倍率の等長、V_i ≠ 0）
  4. (⊗k_i)^{⋆m} = ⊗ k_i^{⋆m}
  5. 系: 原始ケットの n 重の積の巡回の長さは lcm_i ord χ_i
-/
import PAG111

namespace PAG.Part112

open ZMod Finset PAG.Part15 PAG.Part108 PAG.Part109 PAG.Part110 PAG.Part111

section Generic

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]

/-- **1. Scalar の同型不変性**。 -/
theorem scalar_comp_equiv (φ : G ≃+ H) (e k : H → ℂ) : Scalar (e ∘ φ) (k ∘ φ) ↔ Scalar e k := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun F hF => ?_⟩
    have h1 : conv (e ∘ φ) (F ∘ φ) = F ∘ φ := by rw [conv_comp_equiv, hF]
    have h2 := hc _ h1
    rw [conv_comp_equiv] at h2
    funext y
    have := congrFun h2 (φ.symm y)
    simpa using this
  · rintro ⟨c, hc⟩
    refine ⟨c, fun f hf => ?_⟩
    obtain ⟨F, rfl⟩ : ∃ F, f = F ∘ φ := ⟨f ∘ φ.symm, by funext x; simp⟩
    rw [conv_comp_equiv] at hf
    have hF : conv e F = F := by
      funext y
      have := congrFun hf (φ.symm y)
      simpa using this
    rw [conv_comp_equiv, hc F hF]
    rfl

/-- **2. 正の倍率の等長は単射**。 -/
theorem inj_of_isoOn (e k : G → ℂ) (l : ℝ) (hl : 0 < l) (hk : IsoOn e k l) (f : G → ℂ)
    (hf : conv e f = f) (h0 : conv k f = 0) : f = 0 := by
  have hiso := hk f hf
  rw [h0] at hiso
  simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero] at hiso
  have hs : ∑ x, Complex.normSq (f x) = 0 := by
    rcases mul_eq_zero.mp hiso.symm with h' | h'
    · exact absurd h' hl.ne'
    · exact h'
  funext x
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => Complex.normSq_nonneg (f y))).mp hs x (mem_univ x)
  simpa using this

end Generic


theorem ptens_ne_zero {n : ℕ} {G : Fin n → Type} (f : ∀ i, G i → ℂ) (hf : ∀ i, f i ≠ 0) : ptens f ≠ 0 := by
  have hx : ∀ i, ∃ x, f i x ≠ 0 := by
    intro i; by_contra H; push Not at H; exact hf i (funext H)
  choose x hx using hx
  intro h0
  have := congrFun h0 x
  simp only [ptens, Pi.zero_apply] at this
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => hx i) this

/-- **3. n 重の積のスカラー性**（因子の個数についての帰納法）。 -/
theorem scalar_ptens_iff : ∀ (n : ℕ) (G : Fin n → Type) [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)]
    (e A : ∀ i, G i → ℂ) (l : Fin n → ℝ), (∀ i, conv (e i) (e i) = e i) → (∀ i, 0 < l i) →
      (∀ i, IsoOn (e i) (A i) (l i)) → (f : ∀ i, G i → ℂ) → (∀ i, conv (e i) (f i) = f i) → (∀ i, f i ≠ 0) →
      (Scalar (ptens e) (ptens A) ↔ ∀ i, Scalar (e i) (A i)) := by
  intro n
  induction n with
  | zero =>
    intro G _ _ e A l _ _ _ _ _ _
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _
      refine ⟨1, fun f _ => ?_⟩
      funext x
      simp only [conv, ptens, Fin.prod_univ_zero, one_mul, one_smul]
      rw [Fintype.sum_unique]
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
    intro G _ _ e A l he hl hA f hf hf0
    rw [ptens_succ e, ptens_succ A, scalar_comp_equiv]
    have hidem : conv (ptens (fun i : Fin n => e i.succ)) (ptens (fun i : Fin n => e i.succ))
        = ptens (fun i : Fin n => e i.succ) := by
      rw [conv_ptens]; simp only [he]
    have htail_iso := isoOn_ptens n (fun i => G i.succ) (fun i => e i.succ) (fun i => A i.succ)
      (fun i => l i.succ) (fun i => he _) (fun i => hA _)
    have hpos : 0 < ∏ i : Fin n, l i.succ := Finset.prod_pos fun i _ => hl _
    have htail_fix : conv (ptens (fun i : Fin n => e i.succ)) (ptens (fun i : Fin n => f i.succ))
        = ptens (fun i : Fin n => f i.succ) := by
      rw [conv_ptens]; simp only [hf]
    rw [scalar_tens_iff _ _ _ _ (he 0) hidem (inj_of_isoOn _ _ _ (hl 0) (hA 0))
      (inj_of_isoOn _ _ _ hpos htail_iso) (f 0) (hf 0) (hf0 0) _ htail_fix
      (ptens_ne_zero _ (fun i => hf0 _)),
      ih (fun i => G i.succ) (fun i => e i.succ) (fun i => A i.succ) (fun i => l i.succ)
        (fun i => he _) (fun i => hl _) (fun i => hA _) (fun i => f i.succ) (fun i => hf _) (fun i => hf0 _),
      Fin.forall_fin_succ]

/-- **4. 冪のテンソル分解**。 -/
theorem cpow_ptens {n : ℕ} {G : Fin n → Type} [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)]
    [∀ i, DecidableEq (G i)] (k : ∀ i, G i → ℂ) (m : ℕ) :
    cpow (ptens k) m = ptens (fun i => cpow (k i) m) := by
  induction m with
  | zero => exact ptens_single.symm
  | succ m ih => simp only [cpow]; rw [ih, conv_ptens]

/-! ## 5. 系: n 個の素数での巡回の長さ -/

section Primes

open PAG.Part21 PAG.Part59

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K : Fin n → ℕ)

theorem scalar_ptens_lcm (w c : Fin n → ℕ) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive) (m : ℕ) :
    Scalar (ptens (fun i => eps (p := p i) (K i) (K i - (c i + 1) - w i)))
        (cpow (ptens (fun i => ket (K i) (w i) (c i + 1) (h i) (χ i))) (m + 1))
      ↔ (Finset.univ.lcm fun i => orderOf (χ i)) ∣ m + 1 := by
  have hl : ∀ i, (0 : ℝ) < ((p i : ℝ) ^ K i / (PAG.Part19.sz (p i) (K i) (K i - (c i + 1) - w i) : ℝ)) ^ (m + 1) := by
    intro i
    apply pow_pos
    apply div_pos (pow_pos (by exact_mod_cast (hp i).out.pos) _)
    have : 0 < PAG.Part19.sz (p i) (K i) (K i - (c i + 1) - w i) := by
      unfold PAG.Part19.sz
      exact Nat.mul_pos (pow_pos (hp i).out.pos _) (Nat.sub_pos_of_lt (hp i).out.one_lt)
    exact_mod_cast this
  rw [cpow_ptens, scalar_ptens_iff n (fun i => ZMod (p i ^ K i)) _ _ _ (fun i => eps_idem (K i) _ (by omega)) hl
      (fun i => isoOn_cpow _ _ _ (isoOn_ket (K i) (w i) (c i) (h i) (χ i) (hχ i)) (m + 1))
      _ (fun i => eps_idem (K i) _ (by omega)) (fun i => eps_ne_zero (K i) (w i) (c i) (h i) (χ i) (hχ i)),
    Finset.lcm_dvd_iff]
  simp only [Finset.mem_univ, true_implies, orderOf_dvd_iff_pow_eq_one]
  exact forall_congr' fun i => scalar_cpow_iff (K i) (w i) (c i) (h i) (χ i) (hχ i) m

end Primes

end PAG.Part112

#print axioms PAG.Part112.scalar_comp_equiv
#print axioms PAG.Part112.inj_of_isoOn
#print axioms PAG.Part112.ptens_ne_zero
#print axioms PAG.Part112.scalar_ptens_iff
#print axioms PAG.Part112.cpow_ptens
#print axioms PAG.Part112.scalar_ptens_lcm
