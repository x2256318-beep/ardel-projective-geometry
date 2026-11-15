/-
  PAG 2.0 Part 227（2026-10-30）— ℂ^{ℤ/N} ≅ ⊕_{p ∈ S} W_p ⊗ ℂ^{m(c)}（A と A′ の同時の分解）
  A = ⟨E_s, D_s⟩（Part 214 の shellAlg）、A′（Part 220 の fullComm）、A = A″（Part 225）、S = {(c, d)}（Part 222）、
  χ₀(p)・W_p = W_{c,χ₀(p)}(d)・e_p（Part 224 の refChar・refLayer・refProj）、n_p = dim W_p、m(c) = #Prim c、
  行列単位 E_p(χ→χ′)（Part 223 の matUnit）、Φ(M) = Σ_p Σ_{i,j} M_p(i, j)·E_p(j→i)（Part 223 の matSum）
  0. B = Π_{p ∈ S} (Prim c → W_p)（abbrev bimodSpace。W_p ⊗ ℂ^{m(c)} を W_p の m(c) 個の組とみなす）、
     Ψ(w) = Σ_p Σ_χ E_p(χ₀→χ) w_p(χ)（def bimodMap）、Ψ⁻¹(f)_p(χ) = E_p(χ→χ₀) f（def bimodInv）。
     E_q(j→i) Ψ(w) = E_q(χ₀→i) w_q(j)。Ψ は線形同型（def bimodEquiv）。dim B = Σ_p m(c)·n_p = N（Part 226 と別の証明）
  1. A の作用：T ∈ A なら T Ψ(w) = Ψ((ρ_p(T) w_p(χ))_{p,χ})（ρ は Part 225 の shellAlgEquiv）。A は第 1 成分に作用
  2. A′ の作用：Φ(M) Ψ(w) = Ψ((Σ_j M_p(i, j) w_p(j))_{p,i})。A′ は第 2 成分に行列として作用
  3. 単数倍：U_a Ψ(w) = Ψ((χ_N(a) w_p(χ))_{p,χ})、U_a = Φ(diag(χ_N(a)))。Φ(M) が U_a のすべてと可換 ⇔
     M_p はすべて対角。A′ ∩ (U_a と可換)（Part 220 の dilComm）= Φ(対角行列)
  4. テンソル積の形：W ⊗ ℂ^ι ≅ (ι → W)（def tensorFunEquiv）、⊕_p W_p ⊗ ℂ^{Prim c} ≅ ℂ^{ℤ/N}（def bimodTensorEquiv）
-/
import PAG230

namespace PAG.Part231

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. B = Π_p (Prim c → W_p) と Ψ -/

/-- B = Π_{p ∈ S} (Prim c_p → W_p)（W_p ⊗ ℂ^{m(c)} を W_p の m(c) 個の組とみなしたもの）。 -/
abbrev bimodSpace (N : ℕ) [NeZero N] : Type := Π p : centerIdx N, Prim p.1.1 → refLayer N p

/-- **0a.** E_p(χ→χ₀) f ∈ W_p。 -/
theorem matUnit_mem_refLayer (N : ℕ) [NeZero N] (p : centerIdx N) (χ : Prim p.1.1) (f : ZMod N → ℂ) :
    matUnit N p.1.1 p.1.2 χ.1 (refChar N p).1 f ∈ refLayer N p := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  exact matUnit_mem_layerPart N p.1.1 p.1.2 (Nat.dvd_of_mem_divisors hc) _ _ ((mem_layerIdx _ _ _).mp hdI).2 f

/-- Ψ(w) = Σ_p Σ_χ E_p(χ₀→χ) w_p(χ)（線形写像）。 -/
noncomputable def bimodMap (N : ℕ) [NeZero N] : bimodSpace N →ₗ[ℂ] (ZMod N → ℂ) where
  toFun w := ∑ p : centerIdx N, ∑ χ : Prim p.1.1,
    matUnit N p.1.1 p.1.2 (refChar N p).1 χ.1 (w p χ : ZMod N → ℂ)
  map_add' w w' := by
    simp only [Pi.add_apply, Submodule.coe_add, map_add, Finset.sum_add_distrib]
  map_smul' r w := by
    simp only [Pi.smul_apply, Submodule.coe_smul, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- **0b.** Ψ の値。 -/
theorem bimodMap_apply (N : ℕ) [NeZero N] (w : bimodSpace N) :
    bimodMap N w = ∑ p : centerIdx N, ∑ χ : Prim p.1.1,
      matUnit N p.1.1 p.1.2 (refChar N p).1 χ.1 (w p χ : ZMod N → ℂ) := rfl

/-- **0c.** E_q(j→i) Ψ(w) = E_q(χ₀→i) w_q(j)（行列単位の積の規則）。 -/
theorem matUnit_bimodMap (N : ℕ) [NeZero N] (q : centerIdx N) (i j : Prim q.1.1) (w : bimodSpace N) :
    matUnit N q.1.1 q.1.2 j.1 i.1 (bimodMap N w) =
      matUnit N q.1.1 q.1.2 (refChar N q).1 i.1 (w q j : ZMod N → ℂ) := by
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N q.1).mp q.2
  have hcN := Nat.dvd_of_mem_divisors hc
  have hd := ((mem_layerIdx _ _ _).mp hdI).2
  rw [bimodMap_apply, map_sum, Finset.sum_eq_single q]
  · rw [map_sum, Finset.sum_eq_single j]
    · rw [← Module.End.mul_apply, matUnit_mul_self N q.1.1 q.1.2 hcN hd _ _ _ j.2]
    · intro ψ _ hψ
      rw [← Module.End.mul_apply, matUnit_mul_of_ne_char N q.1.1 hcN q.1.2 q.1.2 hd j.1 i.1 _ ψ.1 j.2 ψ.2
        (fun h => hψ (Subtype.ext h.symm)), LinearMap.zero_apply]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro p _ hpq
    rw [map_sum]
    refine Finset.sum_eq_zero (fun ψ _ => ?_)
    rw [← Module.End.mul_apply, matUnit_mul_of_ne_idx N (Ne.symm hpq) i j ψ (refChar N p), LinearMap.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ q) h

/-- Ψ⁻¹(f)_p(χ) = E_p(χ→χ₀) f ∈ W_p（線形写像）。 -/
noncomputable def bimodInv (N : ℕ) [NeZero N] : (ZMod N → ℂ) →ₗ[ℂ] bimodSpace N where
  toFun f p χ := ⟨matUnit N p.1.1 p.1.2 χ.1 (refChar N p).1 f, matUnit_mem_refLayer N p χ f⟩
  map_add' f g := by
    funext p χ
    apply Subtype.ext
    simp only [map_add, Pi.add_apply, Submodule.coe_add]
  map_smul' r f := by
    funext p χ
    apply Subtype.ext
    simp only [map_smul, Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]

/-- **0d.** Ψ⁻¹ の値。 -/
theorem bimodInv_apply (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (p : centerIdx N) (χ : Prim p.1.1) :
    (bimodInv N f p χ : ZMod N → ℂ) = matUnit N p.1.1 p.1.2 χ.1 (refChar N p).1 f := rfl

/-- **0e.** Ψ⁻¹(Ψ(w)) = w（e_p は W_p の上で恒等）。 -/
theorem bimodInv_bimodMap (N : ℕ) [NeZero N] (w : bimodSpace N) : bimodInv N (bimodMap N w) = w := by
  funext p χ
  apply Subtype.ext
  rw [bimodInv_apply, matUnit_bimodMap]
  exact refProj_apply_of_mem N p (w p χ).2

/-- **0f.** Ψ(Ψ⁻¹(f)) = f（Σ_p Σ_χ E_p(χ→χ) = 1）。 -/
theorem bimodMap_bimodInv (N : ℕ) [NeZero N] (f : ZMod N → ℂ) : bimodMap N (bimodInv N f) = f := by
  rw [bimodMap_apply]
  have h : ∀ p : centerIdx N, ∀ χ : Prim p.1.1,
      matUnit N p.1.1 p.1.2 (refChar N p).1 χ.1 (bimodInv N f p χ : ZMod N → ℂ) =
        matUnit N p.1.1 p.1.2 χ.1 χ.1 f := fun p χ => by
    obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
    rw [bimodInv_apply, ← Module.End.mul_apply, matUnit_mul_self N p.1.1 p.1.2 (Nat.dvd_of_mem_divisors hc)
      ((mem_layerIdx _ _ _).mp hdI).2 _ _ _ (refChar N p).2]
  simp only [h]
  have h1 := LinearMap.congr_fun (sum_sum_matUnit_self N) f
  rw [LinearMap.sum_apply] at h1
  simp only [LinearMap.sum_apply] at h1
  rw [h1, Module.End.one_apply]

/-- **線形同型** Ψ：⊕_{p ∈ S} W_p^{m(c)} ≅ ℂ^{ℤ/N}。 -/
noncomputable def bimodEquiv (N : ℕ) [NeZero N] : bimodSpace N ≃ₗ[ℂ] (ZMod N → ℂ) :=
  { bimodMap N with
    invFun := bimodInv N
    left_inv := bimodInv_bimodMap N
    right_inv := bimodMap_bimodInv N }

/-- **0g.** dim B = Σ_{p ∈ S} m(c_p)·n_p。 -/
theorem finrank_bimodSpace (N : ℕ) [NeZero N] :
    Module.finrank ℂ (bimodSpace N) = ∑ p : centerIdx N,
      PAG.Part230.primCount p.1.1 * (layerDivs p.1.1 p.1.2 (N / p.1.1)).card := by
  rw [Module.finrank_pi_fintype ℂ]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Module.finrank_pi_fintype ℂ, Finset.sum_const, Finset.card_univ, smul_eq_mul, finrank_refLayer N p]
  unfold PAG.Part230.primCount
  rw [Nat.card_eq_fintype_card]

/-- **0h.** Σ_{p ∈ S} m(c_p)·n_p = N（Ψ が同型であることから。Part 226 の `sum_centerIdx_card_mul_primCount` と別の証明）。 -/
theorem sum_primCount_mul_card_layerDivs (N : ℕ) [NeZero N] :
    ∑ p : centerIdx N, PAG.Part230.primCount p.1.1 * (layerDivs p.1.1 p.1.2 (N / p.1.1)).card = N := by
  rw [← finrank_bimodSpace, (bimodEquiv N).finrank_eq, Module.finrank_fintype_fun_eq_card, ZMod.card]

/-! ### 1. A の作用（第 1 成分） -/

/-- **1a.** T ∈ A″ なら Ψ((ρ_p(T) w_p(χ))_{p,χ}) = T Ψ(w)（T は行列単位と可換）。 -/
theorem bimodMap_restrictHom (N : ℕ) [NeZero N] (T : doubleComm N) (w : bimodSpace N) :
    bimodMap N (fun p χ => restrictHom N T p (w p χ)) = (T : Module.End ℂ (ZMod N → ℂ)) (bimodMap N w) := by
  rw [bimodMap_apply, bimodMap_apply, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  rw [restrictHom_apply]
  have hc := (mem_doubleComm_iff_matUnit N T).mp T.2 p (refChar N p) χ
  exact (LinearMap.congr_fun hc.eq (w p χ : ZMod N → ℂ)).symm

/-- **1b. A の作用**：T ∈ A なら T Ψ(w) = Ψ((ρ_p(T) w_p(χ))_{p,χ})（ρ = shellAlgEquiv：A ≅ Π_p End(W_p)）。 -/
theorem shellAlg_apply_bimodMap (N : ℕ) [NeZero N] (T : shellAlg N) (w : bimodSpace N) :
    (T : Module.End ℂ (ZMod N → ℂ)) (bimodMap N w) = bimodMap N (fun p χ => shellAlgEquiv N T p (w p χ)) :=
  (bimodMap_restrictHom N ⟨T.1, shellAlg_le_doubleComm N T.2⟩ w).symm

/-! ### 2. A′ の作用（第 2 成分） -/

/-- **2a. A′ の作用**：Φ(M) Ψ(w) = Ψ((Σ_j M_p(i, j) w_p(j))_{p,i})。 -/
theorem matSum_bimodMap (N : ℕ) [NeZero N] (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (w : bimodSpace N) :
    matSum N M (bimodMap N w) = bimodMap N (fun p i => ∑ j : Prim p.1.1, M p i j • w p j) := by
  unfold matSum
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, matUnit_bimodMap]
  rw [bimodMap_apply]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Submodule.coe_smul, map_smul]

/-- **2b.** S ∈ A′ なら、ある M で S Ψ(w) = Ψ((Σ_j M_p(i, j) w_p(j))_{p,i})（Part 223 の Φ は全射）。 -/
theorem fullComm_apply_bimodMap (N : ℕ) [NeZero N] {S : Module.End ℂ (ZMod N → ℂ)} (hS : S ∈ fullComm N) :
    ∃ M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ, ∀ w : bimodSpace N,
      S (bimodMap N w) = bimodMap N (fun p i => ∑ j : Prim p.1.1, M p i j • w p j) := by
  obtain ⟨M, hM⟩ := (matAlgHom_bijective N).2 ⟨S, (mem_fullCommAlg N S).mpr hS⟩
  have hS' : matSum N M = S := congrArg Subtype.val hM
  exact ⟨M, fun w => by rw [← hS', matSum_bimodMap]⟩

/-- **2c.** Ψ⁻¹(T f)_p(χ) = ρ_p(T)(Ψ⁻¹(f)_p(χ))（T ∈ A。A の作用を Ψ⁻¹ の側で見たもの）。 -/
theorem bimodInv_shellAlg_apply (N : ℕ) [NeZero N] (T : shellAlg N) (f : ZMod N → ℂ) :
    bimodInv N ((T : Module.End ℂ (ZMod N → ℂ)) f) = fun p χ => shellAlgEquiv N T p (bimodInv N f p χ) := by
  conv_lhs => rw [← bimodMap_bimodInv N f, shellAlg_apply_bimodMap]
  rw [bimodInv_bimodMap]

/-- **2d.** Ψ⁻¹(Φ(M) f)_p(i) = Σ_j M_p(i, j)·Ψ⁻¹(f)_p(j)。 -/
theorem bimodInv_matSum_apply (N : ℕ) [NeZero N] (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ)
    (f : ZMod N → ℂ) :
    bimodInv N (matSum N M f) = fun p i => ∑ j : Prim p.1.1, M p i j • bimodInv N f p j := by
  conv_lhs => rw [← bimodMap_bimodInv N f, matSum_bimodMap]
  rw [bimodInv_bimodMap]

/-! ### 3. 単数倍 U_a と、U_a とも可換な変換 -/

/-- **3a.** U_a Ψ(w) = Ψ((χ_N(a)·w_p(χ))_{p,χ})（U_a は V_{c,χ} の上でスカラー χ_N(a)）。 -/
theorem dil_bimodMap (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (w : bimodSpace N) :
    dil a (bimodMap N w) = bimodMap N (fun p χ => liftc χ.1 N (a : ZMod N) • w p χ) := by
  rw [bimodMap_apply, bimodMap_apply, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  obtain ⟨hc, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
  rw [dil_of_mem_span N p.1.1 χ.1 a (matUnit_mem_blockSpan N p.1.1 p.1.2 (Nat.dvd_of_mem_divisors hc) _ _
    ((mem_layerIdx _ _ _).mp hdI).2 _), Submodule.coe_smul, map_smul]

/-- **3b.** U_a = Φ(diag(χ_N(a)))：U_a = Σ_p Σ_χ χ_N(a)·E_p(χ→χ)。 -/
theorem dil_eq_matSum (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    dil a = matSum N (fun p => Matrix.diagonal (fun χ : Prim p.1.1 => liftc χ.1 N (a : ZMod N))) := by
  apply LinearMap.ext
  intro f
  rw [← bimodMap_bimodInv N f, dil_bimodMap, matSum_bimodMap]
  congr 1
  funext p i
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hji), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **3c.** 法 c の指標 χ ≠ χ′（c ∣ N）なら、ある法 N の単数 a で χ_N(a) ≠ χ′_N(a)。 -/
theorem exists_unit_liftc_ne (N c : ℕ) [NeZero N] (hcN : c ∣ N) {χ χ' : DirichletCharacter ℂ c} (h : χ ≠ χ') :
    ∃ a : (ZMod N)ˣ, liftc χ N (a : ZMod N) ≠ liftc χ' N (a : ZMod N) := by
  have hne : liftc χ N ≠ liftc χ' N := by
    rw [liftc_of_dvd χ hcN, liftc_of_dvd χ' hcN]
    exact fun e => h (DirichletCharacter.changeLevel_injective hcN e)
  by_contra hall
  exact hne (MulChar.ext (fun a => not_not.mp (fun hn => hall ⟨a, hn⟩)))

/-- **3d.** W_p ≠ 0（d 自身が d の層に入る）。 -/
theorem exists_ne_zero_refLayer (N : ℕ) [NeZero N] (p : centerIdx N) : ∃ w : refLayer N p, w ≠ 0 := by
  have hpos : 0 < Module.finrank ℂ (refLayer N p) := by
    rw [finrank_refLayer N p]
    obtain ⟨-, -, hdI⟩ := (mem_centerIdx N p.1).mp p.2
    obtain ⟨hdL, -⟩ := (mem_layerIdx _ _ _).mp hdI
    exact Finset.card_pos.mpr ⟨p.1.2, (mem_layerDivs _ _ _ _).mpr
      ⟨hdL, 1, (mul_one _).symm, Nat.coprime_one_left _⟩⟩
  exact Module.finrank_pos_iff_exists_ne_zero.mp hpos

/-- **3e.** Φ(M) が U_a のすべてと可換 ⇔ M_p はすべて対角。 -/
theorem matSum_mem_dilCommute_iff (N : ℕ) [NeZero N]
    (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) :
    matSum N M ∈ dilCommute N ↔ ∀ (p : centerIdx N) (i j : Prim p.1.1), i ≠ j → M p i j = 0 := by
  classical
  rw [mem_dilCommute]
  constructor
  · intro h p i j hij
    obtain ⟨hc, -, -⟩ := (mem_centerIdx N p.1).mp p.2
    obtain ⟨a, ha⟩ := exists_unit_liftc_ne N p.1.1 (Nat.dvd_of_mem_divisors hc) (fun e => hij (Subtype.ext e))
    obtain ⟨w₀, hw₀⟩ := exists_ne_zero_refLayer N p
    have hv := h a (bimodMap N (Pi.single p (Pi.single j w₀)))
    rw [dil_bimodMap, matSum_bimodMap, matSum_bimodMap, dil_bimodMap] at hv
    have hv' := congrArg (bimodInv N) hv
    rw [bimodInv_bimodMap, bimodInv_bimodMap] at hv'
    have h2 := congrFun (congrFun hv' p) i
    simp only [Pi.single_eq_same] at h2
    have e1 : ∑ k : Prim p.1.1, M p i k • (liftc k.1 N (a : ZMod N) • (Pi.single j w₀ : Prim p.1.1 → refLayer N p) k) =
        M p i j • (liftc j.1 N (a : ZMod N) • w₀) := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]
      · intro k _ hkj
        rw [Pi.single_eq_of_ne hkj, smul_zero, smul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have e2 : ∑ k : Prim p.1.1, M p i k • (Pi.single j w₀ : Prim p.1.1 → refLayer N p) k = M p i j • w₀ := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]
      · intro k _ hkj
        rw [Pi.single_eq_of_ne hkj, smul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [e1, e2, smul_smul, smul_smul] at h2
    generalize M p i j = x at h2 ⊢
    have h2' : (x * liftc j.1 N (a : ZMod N)) • (w₀ : ZMod N → ℂ) =
        (liftc i.1 N (a : ZMod N) * x) • (w₀ : ZMod N → ℂ) := by
      have := congrArg Subtype.val h2
      simpa only [Submodule.coe_smul] using this
    have hw₀' : (w₀ : ZMod N → ℂ) ≠ 0 := fun h0 => hw₀ ((Submodule.coe_eq_zero).mp h0)
    have h3 : (x * liftc j.1 N (a : ZMod N) - liftc i.1 N (a : ZMod N) * x) • (w₀ : ZMod N → ℂ) = 0 := by
      rw [sub_smul, h2', sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · have h5 : x * (liftc j.1 N (a : ZMod N) - liftc i.1 N (a : ZMod N)) = 0 := by
        rw [← h4]
        ring
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact h6
      · exact absurd (sub_eq_zero.mp h6).symm ha
    · exact absurd h4 hw₀'
  · intro h a f
    rw [← bimodMap_bimodInv N f, dil_bimodMap, matSum_bimodMap, matSum_bimodMap, dil_bimodMap]
    congr 1
    funext p i
    have e1 : ∑ k : Prim p.1.1, M p i k • (liftc k.1 N (a : ZMod N) • bimodInv N f p k) =
        M p i i • (liftc i.1 N (a : ZMod N) • bimodInv N f p i) :=
      Finset.sum_eq_single i (fun k _ hki => by rw [h p i k (Ne.symm hki), zero_smul])
        (fun hi => absurd (Finset.mem_univ i) hi)
    have e2 : ∑ k : Prim p.1.1, M p i k • bimodInv N f p k = M p i i • bimodInv N f p i :=
      Finset.sum_eq_single i (fun k _ hki => by rw [h p i k (Ne.symm hki), zero_smul])
        (fun hi => absurd (Finset.mem_univ i) hi)
    rw [e1, e2, smul_comm]

/-- **3f. A′ ∩ (U_a と可換) = Φ(対角行列)**（Part 220 の dilComm。引き継ぎメモの 1j）。 -/
theorem mem_dilComm_iff_matSum (N : ℕ) [NeZero N] (S : Module.End ℂ (ZMod N → ℂ)) :
    S ∈ dilComm N ↔ ∃ M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ,
      matSum N M = S ∧ ∀ (p : centerIdx N) (i j : Prim p.1.1), i ≠ j → M p i j = 0 := by
  rw [mem_dilComm]
  constructor
  · rintro ⟨hS, hD⟩
    obtain ⟨M, hM⟩ := (matAlgHom_bijective N).2 ⟨S, (mem_fullCommAlg N S).mpr hS⟩
    have hS' : matSum N M = S := congrArg Subtype.val hM
    refine ⟨M, hS', (matSum_mem_dilCommute_iff N M).mp ?_⟩
    rw [hS']
    exact hD
  · rintro ⟨M, rfl, hM⟩
    exact ⟨matSum_mem_fullComm N M, (matSum_mem_dilCommute_iff N M).mpr hM⟩

/-- **3g.** Ψ⁻¹(U_a f)_p(χ) = χ_N(a)·Ψ⁻¹(f)_p(χ)。 -/
theorem bimodInv_dil_apply (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (f : ZMod N → ℂ) :
    bimodInv N (dil a f) = fun p χ => liftc χ.1 N (a : ZMod N) • bimodInv N f p χ := by
  conv_lhs => rw [← bimodMap_bimodInv N f, dil_bimodMap]
  rw [bimodInv_bimodMap]

/-! ### 4. テンソル積の形 -/

/-- W ⊗ ℂ^ι ≅ (ι → W)（ι は有限。Mathlib の TensorProduct.finsuppScalarRight を経由）。 -/
noncomputable def tensorFunEquiv (W : Type*) [AddCommGroup W] [Module ℂ W] (ι : Type*) [Fintype ι]
    [DecidableEq ι] : TensorProduct ℂ W (ι → ℂ) ≃ₗ[ℂ] (ι → W) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ W) (Finsupp.linearEquivFunOnFinite ℂ ℂ ι).symm) ≪≫ₗ
    TensorProduct.finsuppScalarRight ℂ ℂ W ι ≪≫ₗ Finsupp.linearEquivFunOnFinite ℂ W ι

/-- **4a.** (w ⊗ v)(i) = v(i)·w。 -/
theorem tensorFunEquiv_tmul (W : Type*) [AddCommGroup W] [Module ℂ W] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (w : W) (v : ι → ℂ) (i : ι) :
    tensorFunEquiv W ι (w ⊗ₜ[ℂ] v) i = v i • w := by
  simp [tensorFunEquiv, TensorProduct.congr_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply]

/-- **線形同型** ⊕_{p ∈ S} W_p ⊗ ℂ^{Prim c} ≅ ℂ^{ℤ/N}。 -/
noncomputable def bimodTensorEquiv (N : ℕ) [NeZero N] :
    (Π p : centerIdx N, TensorProduct ℂ (refLayer N p) (Prim p.1.1 → ℂ)) ≃ₗ[ℂ] (ZMod N → ℂ) :=
  LinearEquiv.piCongrRight (fun p => tensorFunEquiv (refLayer N p) (Prim p.1.1)) ≪≫ₗ bimodEquiv N

/-- **4b.** その値：t ↦ Σ_p Σ_χ E_p(χ₀→χ)(t_p(χ))。 -/
theorem bimodTensorEquiv_apply (N : ℕ) [NeZero N] (t : Π p : centerIdx N, TensorProduct ℂ (refLayer N p) (Prim p.1.1 → ℂ)) :
    bimodTensorEquiv N t = ∑ p : centerIdx N, ∑ χ : Prim p.1.1,
      matUnit N p.1.1 p.1.2 (refChar N p).1 χ.1 (tensorFunEquiv (refLayer N p) (Prim p.1.1) (t p) χ : ZMod N → ℂ) :=
  rfl

/-- **4c.** 純テンソルの組 (w_p ⊗ v_p)_p ↦ Σ_p Σ_χ v_p(χ)·E_p(χ₀→χ) w_p。 -/
theorem bimodTensorEquiv_tmul (N : ℕ) [NeZero N] (w : Π p : centerIdx N, refLayer N p)
    (v : Π p : centerIdx N, Prim p.1.1 → ℂ) :
    bimodTensorEquiv N (fun p => w p ⊗ₜ[ℂ] v p) = ∑ p : centerIdx N, ∑ χ : Prim p.1.1,
      v p χ • matUnit N p.1.1 p.1.2 (refChar N p).1 χ.1 (w p : ZMod N → ℂ) := by
  rw [bimodTensorEquiv_apply]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun χ _ => ?_))
  rw [tensorFunEquiv_tmul, Submodule.coe_smul, map_smul]

/-- **4d.** dim ⊕_p W_p ⊗ ℂ^{Prim c} = N。 -/
theorem finrank_bimodTensor (N : ℕ) [NeZero N] :
    Module.finrank ℂ (Π p : centerIdx N, TensorProduct ℂ (refLayer N p) (Prim p.1.1 → ℂ)) = N := by
  rw [(bimodTensorEquiv N).finrank_eq, Module.finrank_fintype_fun_eq_card, ZMod.card]

end PAG.Part231

#print axioms PAG.Part231.bimodSpace
#print axioms PAG.Part231.matUnit_mem_refLayer
#print axioms PAG.Part231.bimodMap
#print axioms PAG.Part231.bimodMap_apply
#print axioms PAG.Part231.matUnit_bimodMap
#print axioms PAG.Part231.bimodInv
#print axioms PAG.Part231.bimodInv_apply
#print axioms PAG.Part231.bimodInv_bimodMap
#print axioms PAG.Part231.bimodMap_bimodInv
#print axioms PAG.Part231.bimodEquiv
#print axioms PAG.Part231.finrank_bimodSpace
#print axioms PAG.Part231.sum_primCount_mul_card_layerDivs
#print axioms PAG.Part231.bimodMap_restrictHom
#print axioms PAG.Part231.shellAlg_apply_bimodMap
#print axioms PAG.Part231.matSum_bimodMap
#print axioms PAG.Part231.fullComm_apply_bimodMap
#print axioms PAG.Part231.bimodInv_shellAlg_apply
#print axioms PAG.Part231.bimodInv_matSum_apply
#print axioms PAG.Part231.dil_bimodMap
#print axioms PAG.Part231.dil_eq_matSum
#print axioms PAG.Part231.exists_unit_liftc_ne
#print axioms PAG.Part231.exists_ne_zero_refLayer
#print axioms PAG.Part231.matSum_mem_dilCommute_iff
#print axioms PAG.Part231.mem_dilComm_iff_matSum
#print axioms PAG.Part231.bimodInv_dil_apply
#print axioms PAG.Part231.tensorFunEquiv
#print axioms PAG.Part231.tensorFunEquiv_tmul
#print axioms PAG.Part231.bimodTensorEquiv
#print axioms PAG.Part231.bimodTensorEquiv_apply
#print axioms PAG.Part231.bimodTensorEquiv_tmul
#print axioms PAG.Part231.finrank_bimodTensor
