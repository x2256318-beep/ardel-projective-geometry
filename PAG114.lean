/-
  PAG 2.0 Part 110（2026-10-19）— 帰納系と積の両立、積のケットの単数同変性
  A. 一つの素数の因子だけレベルを上げる引き戻し π₁^*（他の因子 H はそのまま）について
     1. π₁^*F ⋆ π₁^*G = p · π₁^*(F ⋆ G)
     2. (π^*f) ⊗ g = π₁^*(f ⊗ g)、π₁^*(ε_a ⊗ e) = p · ε_{a+1} ⊗ e
     3. V_{a+1}^{(K+1)} ⊗ V(e) = π₁^*(V_a^{(K)} ⊗ V(e))（K ≥ 1、e は任意のべき等元）
  B. 積のケット (⊗k_i) ∘ φ（φ は中国剰余の環同型）は ℤ/N の単数について
     F(u x) = (∏_i χ_i(u mod p_i^{c_i})) F(x)
-/
import PAG113

namespace PAG.Part114

open ZMod Finset PAG.Part15 PAG.Part105 PAG.Part107 PAG.Part108 PAG.Part109 PAG.Part110 PAG.Part113

section Level

open PAG.Part59 PAG.Part93 PAG.Part95

variable {p : ℕ} [hp : Fact p.Prime] {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- 第一因子の射影 π × id。 -/
noncomputable def proj1 (K : ℕ) : ZMod (p ^ (K + 1)) × H →+ ZMod (p ^ K) × H :=
  (proj (p := p) K).prodMap (AddMonoidHom.id H)

/-- 第一因子の引き戻し。 -/
noncomputable def pull1 (K : ℕ) (F : ZMod (p ^ K) × H → ℂ) : ZMod (p ^ (K + 1)) × H → ℂ := F ∘ proj1 (p := p) K

omit [Fintype H] [DecidableEq H] in
theorem proj1_surjective (K : ℕ) : Function.Surjective (proj1 (p := p) (H := H) K) := by
  rintro ⟨x, y⟩
  obtain ⟨x', rfl⟩ := proj_surjective (p := p) K x
  exact ⟨(x', y), rfl⟩

theorem card_ker1 (K : ℕ) :
    ((univ.filter (fun z : ZMod (p ^ (K + 1)) × H => proj1 (p := p) K z = 0)).card : ℂ) = p := by
  classical
  rw [← card_ker (p := p) K]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type]
  apply sum_congr rfl; intro x _
  rw [Finset.sum_eq_single 0]
  · simp [proj1, Prod.ext_iff]
  · intro y _ hy; simp [proj1, Prod.ext_iff, hy]
  · simp

/-- **A1**。 -/
theorem conv_pull1 (K : ℕ) (F G : ZMod (p ^ K) × H → ℂ) :
    conv (pull1 (p := p) K F) (pull1 (p := p) K G) = (p : ℂ) • pull1 (p := p) K (conv F G) := by
  classical
  have := PAG.Part17.conv_pullback (proj1 (p := p) (H := H) K) (proj1_surjective K) F G
  rw [card_ker1] at this
  exact this

omit hp [Fintype H] [DecidableEq H] in
theorem tens_pull (K : ℕ) (f : ZMod (p ^ K) → ℂ) (g : H → ℂ) :
    tens (pull (p := p) K f) g = pull1 (p := p) K (tens f g) := rfl

omit hp [AddCommGroup H] [Fintype H] [DecidableEq H] in
theorem tens_smul_left (c : ℂ) (f : ZMod (p ^ (K + 1)) → ℂ) (g : H → ℂ) :
    tens (c • f) g = c • tens f g := by
  funext z; simp [tens, mul_assoc]

omit [Fintype H] [DecidableEq H] in
/-- **A2**: π₁^*(ε_a ⊗ e) = p · ε_{a+1} ⊗ e。 -/
theorem pull1_tens_eps (K a : ℕ) (ha : a ≤ K) (e : H → ℂ) :
    pull1 (p := p) K (tens (eps (p := p) K a) e) = (p : ℂ) • tens (eps (p := p) (K + 1) (a + 1)) e := by
  rw [← tens_pull, pull_eps K a ha, tens_smul_left]

/-- π₁^* は V_a ⊗ V(e) を V_{a+1} ⊗ V(e) に移す。 -/
theorem pull1_fix (K a : ℕ) (ha : a ≤ K) (e : H → ℂ) (G : ZMod (p ^ K) × H → ℂ)
    (hG : conv (tens (eps (p := p) K a) e) G = G) :
    conv (tens (eps (p := p) (K + 1) (a + 1)) e) (pull1 (p := p) K G) = pull1 (p := p) K G := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h := conv_pull1 (p := p) K (tens (eps (p := p) K a) e) G
  rw [hG, pull1_tens_eps K a ha, conv_comm, PAG.Part111.conv_smul_gen, conv_comm] at h
  exact smul_right_injective _ hp0 h

omit [Fintype H] [DecidableEq H] in
theorem pull1_injective (K : ℕ) : Function.Injective (pull1 (p := p) (H := H) K) := by
  intro F G h
  funext z
  obtain ⟨z', rfl⟩ := proj1_surjective (p := p) (H := H) K z
  exact congrFun h z'

/-- π₁^* の線形写像。 -/
noncomputable def pull1L (K : ℕ) : (ZMod (p ^ K) × H → ℂ) →ₗ[ℂ] (ZMod (p ^ (K + 1)) × H → ℂ) where
  toFun := pull1 (p := p) K
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **A3. V_{a+1}^{(K+1)} ⊗ V(e) = π₁^*(V_a^{(K)} ⊗ V(e))**。 -/
theorem Va_tens_succ (K a : ℕ) (hK : 1 ≤ K) (ha : a ≤ K) (e : H → ℂ) (he : conv e e = e)
    (g : ZMod (p ^ (K + 1)) × H → ℂ) :
    conv (tens (eps (p := p) (K + 1) (a + 1)) e) g = g ↔
      ∃ G, conv (tens (eps (p := p) K a) e) G = G ∧ pull1 (p := p) K G = g := by
  set S0 := LinearMap.range (convL (tens (eps (p := p) K a) e))
  set S1 := LinearMap.range (convL (tens (eps (p := p) (K + 1) (a + 1)) e))
  have hi0 := tens_idem _ _ (eps_idem (p := p) K a ha) he
  have hi1 := tens_idem _ _ (eps_idem (p := p) (K + 1) (a + 1) (by omega)) he
  have hle : S0.map (pull1L (p := p) (H := H) K) ≤ S1 := by
    rintro g ⟨G, hG, rfl⟩
    exact (mem_range_convL _ hi1 _).mpr (pull1_fix K a ha e G ((mem_range_convL _ hi0 G).mp hG))
  have hdim : Module.finrank ℂ (S0.map (pull1L (p := p) (H := H) K)) = Module.finrank ℂ S1 := by
    rw [(Submodule.equivMapOfInjective _ (pull1_injective (p := p) (H := H) K) S0).finrank_eq.symm]
    simp only [S0, S1]
    rw [finrank_tens _ _ (eps_idem K a ha) he, finrank_tens _ _ (eps_idem (K + 1) (a + 1) (by omega)) he,
      range_convL_eps K a ha, range_convL_eps (K + 1) (a + 1) (by omega), finrank_Va_succ K a hK ha]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hdim
  constructor
  · intro hg
    have : g ∈ S0.map (pull1L (p := p) (H := H) K) := by rw [heq]; exact (mem_range_convL _ hi1 g).mpr hg
    obtain ⟨G, hG, rfl⟩ := this
    exact ⟨G, (mem_range_convL _ hi0 G).mp hG, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    exact pull1_fix K a ha e G hG

end Level

/-! ## B. 積のケットの単数同変性 -/

section Equiv

open PAG.Part21 PAG.Part98

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K : Fin n → ℕ)

/-- 中国剰余の環同型。 -/
noncomputable def crtRing (hinj : Function.Injective p) : ZMod (∏ i, p i ^ K i) ≃+* ∀ i, ZMod (p i ^ K i) :=
  ZMod.prodEquivPi (fun i => p i ^ K i) (fun i j hij =>
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (hp i).out (hp j).out).mpr (hinj.ne hij)))

/-- 単数の成分。 -/
noncomputable def unitComp (hinj : Function.Injective p) (i : Fin n) :
    (ZMod (∏ i, p i ^ K i))ˣ →* (ZMod (p i ^ K i))ˣ :=
  Units.map ((Pi.evalRingHom (fun i => ZMod (p i ^ K i)) i).comp (crtRing p K hinj).toRingHom).toMonoidHom

/-- **B. 積のケットの単数同変性**: F(u x) = (∏ χ_i(u_i)) F(x)。 -/
theorem ptens_ket_equivariant (hinj : Function.Injective p) (w c : Fin n → ℕ) (h : ∀ i, w i + c i ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ c i)) (u : (ZMod (∏ i, p i ^ K i))ˣ) (x : ZMod (∏ i, p i ^ K i)) :
    (ptens (fun i => ket (K i) (w i) (c i) (h i) (χ i)) ∘ crtRing p K hinj) (u * x)
      = (∏ i, χ i (ZMod.castHom (pow_dvd_pow (p i) (by have := h i; omega : c i ≤ K i)) (ZMod (p i ^ c i))
            (unitComp p K hinj i u))) *
        (ptens (fun i => ket (K i) (w i) (c i) (h i) (χ i)) ∘ crtRing p K hinj) x := by
  simp only [Function.comp, ptens, map_mul, Pi.mul_apply]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i _
  exact ket_equivariant (K i) (w i) (c i) (h i) (χ i) (unitComp p K hinj i u) (crtRing p K hinj x i)

/-- 指標の積 ψ(u) = ∏ χ_i(u_i) は乗法的。 -/
theorem prodChar_mul (hinj : Function.Injective p) (c : Fin n → ℕ) (hc : ∀ i, c i ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ c i)) (u v : (ZMod (∏ i, p i ^ K i))ˣ) :
    (∏ i, χ i (ZMod.castHom (pow_dvd_pow (p i) (hc i)) (ZMod (p i ^ c i)) (unitComp p K hinj i (u * v))))
      = (∏ i, χ i (ZMod.castHom (pow_dvd_pow (p i) (hc i)) (ZMod (p i ^ c i)) (unitComp p K hinj i u)))
        * ∏ i, χ i (ZMod.castHom (pow_dvd_pow (p i) (hc i)) (ZMod (p i ^ c i)) (unitComp p K hinj i v)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i _
  rw [map_mul, Units.val_mul, map_mul, map_mul]

end Equiv

end PAG.Part114

#print axioms PAG.Part114.proj1_surjective
#print axioms PAG.Part114.card_ker1
#print axioms PAG.Part114.conv_pull1
#print axioms PAG.Part114.tens_pull
#print axioms PAG.Part114.pull1_tens_eps
#print axioms PAG.Part114.pull1_fix
#print axioms PAG.Part114.pull1_injective
#print axioms PAG.Part114.Va_tens_succ
#print axioms PAG.Part114.ptens_ket_equivariant
#print axioms PAG.Part114.prodChar_mul
