/-
  PAG 2.0 Part 106（2026-10-19）— 任意個の素数での積構造と、J の LinearEquiv 化
  1. n 個の有限加法群の積 ∏ G_i 上のテンソル ⊗_i f_i について
     (⊗ f_i) ⋆ (⊗ g_i) = ⊗ (f_i ⋆ g_i)、‖⊗ f_i‖² = ∏ ‖f_i‖²、⊗ δ = δ
  2. 等長性の積（n についての帰納法）: IsoOn e_i k_i λ_i ⇒ IsoOn (⊗ e_i) (⊗ k_i) (∏ λ_i)
  3. 素数の族 p_i での具体化: δ = Σ_𝐚 ⊗ ε_{a_i}（直交べき等）、原始ケットの積は V_𝐚 上で ∏ λ_i 倍の等長
  4. J : V_a^{(K)} ≃ₗ V_{a+1}^{(K+1)}（LinearEquiv）、finrank の一致
-/
import PAG109

namespace PAG.Part110

open Finset PAG.Part15 PAG.Part108 PAG.Part109

section Pi

variable {n : ℕ} {G : Fin n → Type} [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)]

/-- n 重テンソル (⊗ f_i)(x) = ∏ f_i (x_i)。 -/
def ptens (f : ∀ i, G i → ℂ) : (∀ i, G i) → ℂ := fun x => ∏ i, f i (x i)

/-- **1a. 畳み込みの分解**。 -/
theorem conv_ptens (f g : ∀ i, G i → ℂ) :
    conv (ptens f) (ptens g) = ptens (fun i => conv (f i) (g i)) := by
  funext x
  simp only [conv, ptens]
  rw [Fintype.prod_sum]
  apply sum_congr rfl; intro y _
  rw [← Finset.prod_mul_distrib]
  rfl

omit [∀ i, AddCommGroup (G i)] in
/-- **1b. ノルムの積**。 -/
theorem normSq_ptens (f : ∀ i, G i → ℂ) :
    ∑ x, Complex.normSq (ptens f x) = ∏ i, ∑ y, Complex.normSq (f i y) := by
  simp only [ptens, map_prod]
  rw [Fintype.prod_sum]

omit [∀ i, Fintype (G i)] in
/-- **1c. ⊗ δ = δ**。 -/
theorem ptens_single [∀ i, DecidableEq (G i)] :
    ptens (fun i => Pi.single (0 : G i) (1 : ℂ)) = Pi.single 0 1 := by
  funext x
  simp only [ptens, Pi.single_apply, Fintype.prod_boole, funext_iff, Pi.zero_apply]
  congr

/-- 先頭の因子を切り離す加法同型。 -/
def consAdd (G : Fin (n + 1) → Type) [∀ i, AddCommGroup (G i)] :
    (∀ i, G i) ≃+ G 0 × (∀ i : Fin n, G i.succ) where
  toEquiv := (Fin.consEquiv G).symm
  map_add' _ _ := rfl

omit [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)] in
theorem ptens_succ {G : Fin (n + 1) → Type} [∀ i, AddCommGroup (G i)] (f : ∀ i, G i → ℂ) :
    ptens f = tens (f 0) (ptens (fun i => f i.succ)) ∘ consAdd G := by
  funext x
  simp only [ptens, tens, Function.comp, Fin.prod_univ_succ]
  rfl

end Pi

/-- **2. 等長性の積**（因子の個数についての帰納法）。 -/
theorem isoOn_ptens : ∀ (n : ℕ) (G : Fin n → Type) [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)]
    (e k : ∀ i, G i → ℂ) (l : Fin n → ℝ), (∀ i, conv (e i) (e i) = e i) →
      (∀ i, IsoOn (e i) (k i) (l i)) → IsoOn (ptens e) (ptens k) (∏ i, l i) := by
  intro n
  induction n with
  | zero =>
    intro G _ _ e k l _ _ f _
    have hk : conv (ptens k) f = f := by
      funext x
      simp only [conv, ptens, Fin.prod_univ_zero, one_mul]
      rw [Fintype.sum_unique]
      congr 1
      exact Subsingleton.elim _ _
    rw [hk, Fin.prod_univ_zero, one_mul]
  | succ n ih =>
    intro G _ _ e k l he hk
    rw [ptens_succ e, ptens_succ k, Fin.prod_univ_succ]
    apply isoOn_comp_equiv
    have hidem : conv (ptens (fun i : Fin n => e i.succ)) (ptens (fun i : Fin n => e i.succ))
        = ptens (fun i : Fin n => e i.succ) := by
      rw [conv_ptens]; simp only [he]
    exact isoOn_tens _ _ _ _ _ _ (he 0) hidem (hk 0)
      (ih (fun i => G i.succ) (fun i => e i.succ) (fun i => k i.succ) (fun i => l i.succ)
        (fun i => he _) (fun i => hk _))

/-! ## 3. 素数の族での具体化 -/

section Primes

open PAG.Part59 PAG.Part89

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K : Fin n → ℕ)

/-- **3a. 双対殻の組による分解**: Σ_𝐚 ⊗ ε_{a_i} = δ。 -/
theorem sum_ptens_eps :
    ∑ a : ∀ i, Fin (K i + 1), ptens (fun i => eps (p := p i) (K i) (a i)) = Pi.single 0 1 := by
  have e : ∑ a : ∀ i, Fin (K i + 1), ptens (fun i => eps (p := p i) (K i) (a i))
      = ptens (fun i => ∑ b : Fin (K i + 1), eps (p := p i) (K i) b) := by
    funext x
    simp only [ptens, Finset.sum_apply]
    rw [Fintype.prod_sum]
  rw [e]
  have e2 : ∀ i, ∑ b : Fin (K i + 1), eps (p := p i) (K i) b = Pi.single 0 1 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun b => eps (p := p i) (K i) b), PAG.Part94.sum_eps]
  simp only [e2]
  exact ptens_single

/-- **3b. 直交べき等性**。 -/
theorem ptens_eps_conv (a b : ∀ i, Fin (K i + 1)) :
    conv (ptens (fun i => eps (p := p i) (K i) (a i))) (ptens (fun i => eps (p := p i) (K i) (b i)))
      = if a = b then ptens (fun i => eps (p := p i) (K i) (a i)) else 0 := by
  rw [conv_ptens]
  have h : ∀ i, conv (eps (p := p i) (K i) (a i)) (eps (p := p i) (K i) (b i))
      = if a i = b i then eps (p := p i) (K i) (a i) else 0 := by
    intro i
    rw [eps_conv_eps (K i) (a i) (b i) (by omega) (by omega)]
    simp only [Fin.val_inj]
  simp only [h]
  by_cases hab : a = b
  · subst hab; simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hab)]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra hc; push Not at hc; exact hab (funext hc)
    funext x
    simp only [ptens, Pi.zero_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hi)]
    rfl

/-- **3c. 原始ケットの積の等長性**（任意個の素数）。 -/
theorem isoOn_ptens_ket (w c : Fin n → ℕ) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive) :
    IsoOn (ptens (fun i => eps (p := p i) (K i) (K i - (c i + 1) - w i)))
      (ptens (fun i => PAG.Part21.ket (K i) (w i) (c i + 1) (h i) (χ i)))
      (∏ i, (p i : ℝ) ^ K i / (PAG.Part19.sz (p i) (K i) (K i - (c i + 1) - w i) : ℝ)) :=
  isoOn_ptens n (fun i => ZMod (p i ^ K i)) _ _ _ (fun i => eps_idem (K i) _ (by omega))
    (fun i => isoOn_ket (K i) (w i) (c i) (h i) (χ i) (hχ i))

instance instNeZeroProd : NeZero (∏ i, p i ^ K i) :=
  ⟨Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hp i).out.ne_zero⟩

/-- **3d. 法 N = ∏ p_i^{K_i} への持ち上げ**（p_i は相異なる素数、中国剰余定理）。 -/
noncomputable def crtPi (hinj : Function.Injective p) : ZMod (∏ i, p i ^ K i) ≃+ ∀ i, ZMod (p i ^ K i) :=
  (ZMod.prodEquivPi (fun i => p i ^ K i) (fun i j hij =>
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (hp i).out (hp j).out).mpr (hinj.ne hij)))).toAddEquiv

theorem isoOn_crtPi_ket (hinj : Function.Injective p) (w c : Fin n → ℕ) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive) :
    IsoOn (ptens (fun i => eps (p := p i) (K i) (K i - (c i + 1) - w i)) ∘ crtPi p K hinj)
      (ptens (fun i => PAG.Part21.ket (K i) (w i) (c i + 1) (h i) (χ i)) ∘ crtPi p K hinj)
      (∏ i, (p i : ℝ) ^ K i / (PAG.Part19.sz (p i) (K i) (K i - (c i + 1) - w i) : ℝ)) :=
  isoOn_comp_equiv _ _ _ _ (isoOn_ptens_ket p K w c h χ hχ)

end Primes

/-! ## 4. J の LinearEquiv 化 -/

section J

open PAG.Part59 PAG.Part93 PAG.Part95 PAG.Part105 PAG.Part107

variable {p : ℕ} [hp : Fact p.Prime]

/-- 引き戻し π^* : V_a^{(K)} ≃ₗ V_{a+1}^{(K+1)}（J = p^{-1/2} π^* はこれのスカラー倍で等長）。 -/
noncomputable def pullEquiv (K a : ℕ) (hK : 1 ≤ K) (ha : a ≤ K) :
    Va (p := p) K a ≃ₗ[ℂ] Va (p := p) (K + 1) (a + 1) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (Va (p := p) (K + 1) (a + 1)) ((pullL (p := p) K).domRestrict (Va (p := p) K a))
      (fun f => (Va_eq_span (K + 1) (a + 1) (by omega) (pull K (f : ZMod (p ^ K) → ℂ))).mp
        (PAG.Part105.pull_Va K a ha (f : ZMod (p ^ K) → ℂ) ((Va_eq_span K a ha (f : ZMod (p ^ K) → ℂ)).mpr f.2))))
    ⟨fun x y hxy => Subtype.ext (pull_injective K (congrArg Subtype.val hxy)), fun g => by
      obtain ⟨f, hf, hfg⟩ := (Va_succ_eq_pull K a hK ha (g : ZMod (p ^ (K + 1)) → ℂ)).mp
        ((Va_eq_span (K + 1) (a + 1) (by omega) (g : ZMod (p ^ (K + 1)) → ℂ)).mpr g.2)
      exact ⟨⟨f, (Va_eq_span K a ha f).mp hf⟩, Subtype.ext hfg⟩⟩

theorem pullEquiv_apply (K a : ℕ) (hK : 1 ≤ K) (ha : a ≤ K) (f : Va (p := p) K a) :
    ((pullEquiv K a hK ha f : Va (p := p) (K + 1) (a + 1)) : ZMod (p ^ (K + 1)) → ℂ) = pull K (f : ZMod (p ^ K) → ℂ) := by
  rfl

theorem finrank_Va_succ (K a : ℕ) (hK : 1 ≤ K) (ha : a ≤ K) :
    Module.finrank ℂ (Va (p := p) K a) = Module.finrank ℂ (Va (p := p) (K + 1) (a + 1)) :=
  (pullEquiv K a hK ha).finrank_eq

end J

end PAG.Part110

#print axioms PAG.Part110.conv_ptens
#print axioms PAG.Part110.normSq_ptens
#print axioms PAG.Part110.ptens_single
#print axioms PAG.Part110.ptens_succ
#print axioms PAG.Part110.isoOn_ptens
#print axioms PAG.Part110.sum_ptens_eps
#print axioms PAG.Part110.ptens_eps_conv
#print axioms PAG.Part110.isoOn_ptens_ket
#print axioms PAG.Part110.isoOn_crtPi_ket
#print axioms PAG.Part110.pullEquiv
#print axioms PAG.Part110.pullEquiv_apply
#print axioms PAG.Part110.finrank_Va_succ
