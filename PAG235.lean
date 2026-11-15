/-
  PAG 2.0 Part 231（2026-10-30）— 単数倍 U_u と、単数倍とも可換な変換の代数 dilComm の中国剰余定理による分解、層の指示関数の分解
  U_u f(x) = f(u·x)（Part 214 の dil）、dilComm = A′ ∩ (U_u と可換)（Part 220）、C・L・R（Part 228）、
  可換子の一般の分解 (L(B) ⊔ R(B′))^c = L(B^c) ⊔ R(B′^c)（Part 230 の centralizer_sup_map）
  0. 掛け算による引き戻し M_r f(x) = f(r·x)（def mulPull、r は任意）。C(M_r) = L(M_{r mod a})·R(M_{r mod b})
  1. 単数の分解：u ↦ (u mod a, u mod b)（def unitFst・unitSnd）、(v, 1)・(1, w) に当たる単数（def unitLeft・unitRight）。
     C(U_u) = L(U_{u mod a})·R(U_{u mod b})、C(U_{(v,1)}) = L(U_v)、C(U_{(1,w)}) = R(U_w)
  2. 単数倍の代数 ⟨U_u⟩（def dilAlg）：C(⟨U_u⟩_{ab}) = L(⟨U_u⟩_a) ⊔ R(⟨U_u⟩_b)、A ⊔ ⟨U_u⟩ も同様、⟨U_u⟩ の可換子も同様
  3. dilComm = (A ⊔ ⟨U_u⟩)^c（def dilCommAlg、Part 220 の dilComm と同じ元）。C(dilComm_{ab}) = L(dilComm_a) ⊔ R(dilComm_b)、
     dim dilComm_{ab} = dim dilComm_a·dim dilComm_b、代数同型 dilComm_a ⊗ dilComm_b ≅ dilComm_{ab}（def dilCommTensorEquiv）
  4. 層：c_a d_a ∣ a、c_b d_b ∣ b なら「n は c_a c_b について d_a d_b の層」⇔「n mod a は c_a について d_a の層」かつ
     「n mod b は c_b について d_b の層」。(c_a, d_a) ∈ S(a)、(c_b, d_b) ∈ S(b) なら 1_{層} も C(ι) = L(ι)·R(ι) と分かれる
-/
import PAG234

namespace PAG.Part235

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part231 PAG.Part232 PAG.Part233 PAG.Part234
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 掛け算による引き戻し -/

/-- 掛け算による引き戻し M_r f(x) = f(r·x)（r ∈ ℤ/N は任意）。 -/
def mulPull {N : ℕ} (r : ZMod N) : Module.End ℂ (ZMod N → ℂ) := LinearMap.funLeft ℂ ℂ (fun x => r * x)

/-- **0a.** M_r の値。 -/
theorem mulPull_apply {N : ℕ} (r : ZMod N) (f : ZMod N → ℂ) (x : ZMod N) : mulPull r f x = f (r * x) := rfl

/-- **0b.** 単数倍 U_u は M_u（定義から）。 -/
theorem dil_eq_mulPull {N : ℕ} (u : (ZMod N)ˣ) : (dil u : Module.End ℂ (ZMod N → ℂ)) = mulPull (u : ZMod N) := rfl

/-- **0c.** M_1 = 1。 -/
theorem mulPull_one {N : ℕ} : (mulPull (1 : ZMod N) : Module.End ℂ (ZMod N → ℂ)) = 1 := by
  apply LinearMap.ext
  intro f
  funext x
  show f (1 * x) = f x
  rw [one_mul]

/-- **0d.** C(M_r) = L(M_{r mod a})·R(M_{r mod b})（中国剰余定理は環同型なので r·x も成分ごと）。 -/
theorem crtConj_mulPull {a b : ℕ} (hab : Nat.Coprime a b) (r : ZMod (a * b)) :
    crtConj hab (mulPull r) = leftOp b (mulPull (ZMod.chineseRemainder hab r).1) *
      rightOp a (mulPull (ZMod.chineseRemainder hab r).2) := by
  apply LinearMap.ext
  intro F
  funext p
  show F (ZMod.chineseRemainder hab (r * (ZMod.chineseRemainder hab).symm p)) =
    F ((ZMod.chineseRemainder hab r).1 * p.1, (ZMod.chineseRemainder hab r).2 * p.2)
  rw [map_mul, RingEquiv.apply_symm_apply]
  rfl

/-! ### 1. 単数の分解 -/

/-- 単数 u ∈ (ℤ/ab)ˣ の第 1 成分 u mod a ∈ (ℤ/a)ˣ。 -/
noncomputable def unitFst {a b : ℕ} (hab : Nat.Coprime a b) (u : (ZMod (a * b))ˣ) : (ZMod a)ˣ :=
  Units.map ((RingHom.fst (ZMod a) (ZMod b)).comp (ZMod.chineseRemainder hab).toRingHom).toMonoidHom u

/-- 単数 u の第 2 成分 u mod b ∈ (ℤ/b)ˣ。 -/
noncomputable def unitSnd {a b : ℕ} (hab : Nat.Coprime a b) (u : (ZMod (a * b))ˣ) : (ZMod b)ˣ :=
  Units.map ((RingHom.snd (ZMod a) (ZMod b)).comp (ZMod.chineseRemainder hab).toRingHom).toMonoidHom u

/-- **1a.** unitFst の値。 -/
theorem unitFst_val {a b : ℕ} (hab : Nat.Coprime a b) (u : (ZMod (a * b))ˣ) :
    ((unitFst hab u : (ZMod a)ˣ) : ZMod a) = (ZMod.chineseRemainder hab (u : ZMod (a * b))).1 := rfl

/-- **1b.** unitSnd の値。 -/
theorem unitSnd_val {a b : ℕ} (hab : Nat.Coprime a b) (u : (ZMod (a * b))ˣ) :
    ((unitSnd hab u : (ZMod b)ˣ) : ZMod b) = (ZMod.chineseRemainder hab (u : ZMod (a * b))).2 := rfl

/-- (v, 1) に当たる法 ab の単数（v ∈ (ℤ/a)ˣ）。 -/
noncomputable def unitLeft {a b : ℕ} (hab : Nat.Coprime a b) (v : (ZMod a)ˣ) : (ZMod (a * b))ˣ where
  val := (ZMod.chineseRemainder hab).symm ((v : ZMod a), 1)
  inv := (ZMod.chineseRemainder hab).symm (((v⁻¹ : (ZMod a)ˣ) : ZMod a), 1)
  val_inv := by
    rw [← map_mul, Prod.mk_mul_mk, Units.mul_inv, mul_one]
    exact map_one _
  inv_val := by
    rw [← map_mul, Prod.mk_mul_mk, Units.inv_mul, mul_one]
    exact map_one _

/-- (1, w) に当たる法 ab の単数（w ∈ (ℤ/b)ˣ）。 -/
noncomputable def unitRight {a b : ℕ} (hab : Nat.Coprime a b) (w : (ZMod b)ˣ) : (ZMod (a * b))ˣ where
  val := (ZMod.chineseRemainder hab).symm (1, (w : ZMod b))
  inv := (ZMod.chineseRemainder hab).symm (1, ((w⁻¹ : (ZMod b)ˣ) : ZMod b))
  val_inv := by
    rw [← map_mul, Prod.mk_mul_mk, Units.mul_inv, mul_one]
    exact map_one _
  inv_val := by
    rw [← map_mul, Prod.mk_mul_mk, Units.inv_mul, mul_one]
    exact map_one _

/-- **1c.** unitLeft の中国剰余定理の成分は (v, 1)。 -/
theorem crt_unitLeft {a b : ℕ} (hab : Nat.Coprime a b) (v : (ZMod a)ˣ) :
    ZMod.chineseRemainder hab (unitLeft hab v : ZMod (a * b)) = ((v : ZMod a), 1) :=
  RingEquiv.apply_symm_apply _ _

/-- **1d.** unitRight の成分は (1, w)。 -/
theorem crt_unitRight {a b : ℕ} (hab : Nat.Coprime a b) (w : (ZMod b)ˣ) :
    ZMod.chineseRemainder hab (unitRight hab w : ZMod (a * b)) = (1, (w : ZMod b)) :=
  RingEquiv.apply_symm_apply _ _

/-- **1e.** C(U_u) = L(U_{u mod a})·R(U_{u mod b})。 -/
theorem crtConj_dil {a b : ℕ} (hab : Nat.Coprime a b) (u : (ZMod (a * b))ˣ) :
    crtConj hab (dil u) = leftOp b (dil (unitFst hab u)) * rightOp a (dil (unitSnd hab u)) := by
  rw [dil_eq_mulPull, crtConj_mulPull]
  rfl

/-- **1f.** C(U_{(v,1)}) = L(U_v)。 -/
theorem crtConj_dil_unitLeft {a b : ℕ} (hab : Nat.Coprime a b) (v : (ZMod a)ˣ) :
    crtConj hab (dil (unitLeft hab v)) = leftOp b (dil v) := by
  rw [dil_eq_mulPull, crtConj_mulPull, crt_unitLeft]
  show leftOp b (mulPull (v : ZMod a)) * rightOp a (mulPull (1 : ZMod b)) = leftOp b (dil v)
  rw [mulPull_one]
  show leftOp b (mulPull (v : ZMod a)) * rightHom a b 1 = leftOp b (dil v)
  rw [map_one, mul_one]
  rfl

/-- **1g.** C(U_{(1,w)}) = R(U_w)。 -/
theorem crtConj_dil_unitRight {a b : ℕ} (hab : Nat.Coprime a b) (w : (ZMod b)ˣ) :
    crtConj hab (dil (unitRight hab w)) = rightOp a (dil w) := by
  rw [dil_eq_mulPull, crtConj_mulPull, crt_unitRight]
  show leftOp b (mulPull (1 : ZMod a)) * rightOp a (mulPull (w : ZMod b)) = rightOp a (dil w)
  rw [mulPull_one]
  show leftHom a b 1 * rightOp a (mulPull (w : ZMod b)) = rightOp a (dil w)
  rw [map_one, one_mul]
  rfl

/-! ### 2. 単数倍の代数 -/

/-- 単数倍の代数 ⟨U_u⟩：U_u（u は法 N の単数）の生成する部分代数。 -/
noncomputable def dilAlg (N : ℕ) : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun u : (ZMod N)ˣ => (dil u : Module.End ℂ (ZMod N → ℂ))))

/-- **2a.** U_u ∈ ⟨U_u⟩。 -/
theorem dil_mem_dilAlg (N : ℕ) (u : (ZMod N)ˣ) : (dil u : Module.End ℂ (ZMod N → ℂ)) ∈ dilAlg N :=
  Algebra.subset_adjoin ⟨u, rfl⟩

/-- **2b.** U_u と U_v は可換。 -/
theorem dil_commute {N : ℕ} (u v : (ZMod N)ˣ) :
    Commute (dil u : Module.End ℂ (ZMod N → ℂ)) (dil v : Module.End ℂ (ZMod N → ℂ)) := by
  apply LinearMap.ext
  intro f
  funext x
  show f ((v : ZMod N) * ((u : ZMod N) * x)) = f ((u : ZMod N) * ((v : ZMod N) * x))
  rw [mul_left_comm]

/-- **2c.** C(⟨U_u⟩_{ab}) = L(⟨U_u⟩_a) ⊔ R(⟨U_u⟩_b)（⊆ は 1e、⊇ は 1f・1g）。 -/
theorem map_crtConj_dilAlg {a b : ℕ} (hab : Nat.Coprime a b) :
    (dilAlg (a * b)).map (crtConj hab).toAlgHom = (dilAlg a).map (leftHom a b) ⊔ (dilAlg b).map (rightHom a b) := by
  apply le_antisymm
  · rw [dilAlg, AlgHom.map_adjoin]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨T, ⟨u, rfl⟩, rfl⟩
    show crtConj hab (dil u) ∈ _
    rw [crtConj_dil]
    exact Subalgebra.mul_mem _
      ((le_sup_left : (dilAlg a).map (leftHom a b) ≤ _)
        (Subalgebra.mem_map.mpr ⟨_, dil_mem_dilAlg a (unitFst hab u), rfl⟩))
      ((le_sup_right : (dilAlg b).map (rightHom a b) ≤ _)
        (Subalgebra.mem_map.mpr ⟨_, dil_mem_dilAlg b (unitSnd hab u), rfl⟩))
  · refine sup_le ?_ ?_
    · rw [dilAlg, AlgHom.map_adjoin]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨T, ⟨v, rfl⟩, rfl⟩
      refine Subalgebra.mem_map.mpr ⟨dil (unitLeft hab v), dil_mem_dilAlg _ _, ?_⟩
      show crtConj hab (dil (unitLeft hab v)) = leftHom a b (dil v)
      rw [crtConj_dil_unitLeft]
      rfl
    · rw [dilAlg, AlgHom.map_adjoin]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨T, ⟨w, rfl⟩, rfl⟩
      refine Subalgebra.mem_map.mpr ⟨dil (unitRight hab w), dil_mem_dilAlg _ _, ?_⟩
      show crtConj hab (dil (unitRight hab w)) = rightHom a b (dil w)
      rw [crtConj_dil_unitRight]
      rfl

/-- **2d.** C(A_{ab} ⊔ ⟨U_u⟩_{ab}) = L(A_a ⊔ ⟨U_u⟩_a) ⊔ R(A_b ⊔ ⟨U_u⟩_b)（2c と Part 228）。 -/
theorem map_crtConj_shellDilAlg {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (shellAlg (a * b) ⊔ dilAlg (a * b)).map (crtConj hab).toAlgHom =
      (shellAlg a ⊔ dilAlg a).map (leftHom a b) ⊔ (shellAlg b ⊔ dilAlg b).map (rightHom a b) := by
  rw [Algebra.map_sup, map_crtConj_shellAlg hab, map_crtConj_dilAlg hab, sup_sup_sup_comm,
    ← Algebra.map_sup, ← Algebra.map_sup]

/-- **2e.** 単数倍と可換な変換の代数も分かれる：C(⟨U_u⟩_{ab}^c) = L(⟨U_u⟩_a^c) ⊔ R(⟨U_u⟩_b^c)（Part 230）。 -/
theorem map_crtConj_dilAlg_centralizer {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (Subalgebra.centralizer ℂ (dilAlg (a * b) : Set (Module.End ℂ (ZMod (a * b) → ℂ)))).map (crtConj hab).toAlgHom =
      (Subalgebra.centralizer ℂ (dilAlg a : Set (Module.End ℂ (ZMod a → ℂ)))).map (leftHom a b) ⊔
        (Subalgebra.centralizer ℂ (dilAlg b : Set (Module.End ℂ (ZMod b → ℂ)))).map (rightHom a b) := by
  rw [map_crtConj_centralizer, map_crtConj_dilAlg hab, centralizer_sup_map]

/-! ### 3. 単数倍とも可換な変換の代数 dilComm -/

/-- dilComm の部分代数 (A ⊔ ⟨U_u⟩)^c。 -/
noncomputable def dilCommAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Subalgebra.centralizer ℂ ((shellAlg N ⊔ dilAlg N : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))) :
    Set (Module.End ℂ (ZMod N → ℂ)))

/-- **3a.** T がすべての U_u と可換なら、⟨U_u⟩ のすべての元と可換。 -/
theorem dilAlg_le_centralizer {N : ℕ} {T : Module.End ℂ (ZMod N → ℂ)}
    (h : ∀ u : (ZMod N)ˣ, Commute T (dil u)) : dilAlg N ≤ Subalgebra.centralizer ℂ {T} := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨u, rfl⟩
  rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact (h u).eq

/-- **3b.** T ∈ (A ⊔ ⟨U_u⟩)^c ⇔ T ∈ dilComm（Part 220 の dilComm = A′ ∩ (U_u と可換)）。 -/
theorem mem_dilCommAlg_iff (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ dilCommAlg N ↔ T ∈ dilComm N := by
  rw [mem_dilComm, mem_dilCommute, dilCommAlg, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨(mem_fullComm_iff_commute N T).mpr (fun S hS => (h S ((le_sup_left : shellAlg N ≤ _) hS)).symm),
      fun u f => ?_⟩
    have h1 := h _ ((le_sup_right : dilAlg N ≤ _) (dil_mem_dilAlg N u))
    exact (LinearMap.congr_fun h1 f).symm
  · rintro ⟨hA, hU⟩ g hg
    have hc : Commute T g := commute_of_mem_sup T
      (fun Y hY => (mem_fullComm_iff_commute N T).mp hA Y hY)
      (fun Y hY => (Subalgebra.mem_centralizer_iff ℂ).mp
        (dilAlg_le_centralizer (T := T) (fun u => LinearMap.ext (fun f => hU u f)) hY) T (Set.mem_singleton T)) g hg
    exact hc.eq.symm

/-- dilCommAlg N ≅ dilComm N（線形同型、元はそのまま）。 -/
noncomputable def dilCommAlgLinearEquiv (N : ℕ) [NeZero N] : dilCommAlg N ≃ₗ[ℂ] dilComm N where
  toFun T := ⟨T.1, (mem_dilCommAlg_iff N _).mp T.2⟩
  invFun T := ⟨T.1, (mem_dilCommAlg_iff N _).mpr T.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **3c.** dim dilCommAlg N = dim dilComm N。 -/
theorem finrank_dilCommAlg (N : ℕ) [NeZero N] : Module.finrank ℂ (dilCommAlg N) = Module.finrank ℂ (dilComm N) :=
  (dilCommAlgLinearEquiv N).finrank_eq

/-- **3d. C(dilComm_{ab}) = L(dilComm_a) ⊔ R(dilComm_b)**（3b、2d、Part 230 の可換子の一般の分解）。 -/
theorem map_crtConj_dilComm {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (dilCommAlg (a * b)).map (crtConj hab).toAlgHom =
      (dilCommAlg a).map (leftHom a b) ⊔ (dilCommAlg b).map (rightHom a b) := by
  unfold dilCommAlg
  rw [map_crtConj_centralizer, map_crtConj_shellDilAlg hab, centralizer_sup_map]

/-- **3e.** dim dilComm_{ab} = dim dilComm_a·dim dilComm_b。 -/
theorem finrank_dilComm_mul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ (dilComm (a * b)) = Module.finrank ℂ (dilComm a) * Module.finrank ℂ (dilComm b) := by
  rw [← finrank_dilCommAlg, ← finrank_dilCommAlg, ← finrank_dilCommAlg,
    ← finrank_map_crtConj_gen hab (dilCommAlg (a * b)), map_crtConj_dilComm hab, finrank_sup_map]

/-- **代数同型** dilComm_a ⊗ dilComm_b ≅ dilComm_{ab}（gcd(a, b) = 1）。 -/
noncomputable def dilCommTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    TensorProduct ℂ (dilCommAlg a) (dilCommAlg b) ≃ₐ[ℂ] dilCommAlg (a * b) :=
  crtTensorEquiv hab _ _ _ (map_crtConj_dilComm hab)

/-- **3f.** その値：C(Θ(S ⊗ T)) = L(S)·R(T)。 -/
theorem crtConj_dilCommTensorEquiv_tmul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (S : dilCommAlg a) (T : dilCommAlg b) :
    crtConj hab (dilCommTensorEquiv hab (S ⊗ₜ[ℂ] T) : Module.End ℂ (ZMod (a * b) → ℂ)) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) * rightOp a (T : Module.End ℂ (ZMod b → ℂ)) :=
  crtConj_crtTensorEquiv_tmul hab _ _ _ _ S T

/-- **3g.** 二重可換子も分かれる：C(dilComm_{ab}^c) = L(dilComm_a^c) ⊔ R(dilComm_b^c)。 -/
theorem map_crtConj_dilComm_centralizer {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (Subalgebra.centralizer ℂ (dilCommAlg (a * b) : Set (Module.End ℂ (ZMod (a * b) → ℂ)))).map
        (crtConj hab).toAlgHom =
      (Subalgebra.centralizer ℂ (dilCommAlg a : Set (Module.End ℂ (ZMod a → ℂ)))).map (leftHom a b) ⊔
        (Subalgebra.centralizer ℂ (dilCommAlg b : Set (Module.End ℂ (ZMod b → ℂ)))).map (rightHom a b) := by
  rw [map_crtConj_centralizer, map_crtConj_dilComm hab, centralizer_sup_map]

/-! ### 4. 層の指示関数の分解 -/

/-- **4a.** d > 0 なら「n は c について d の層」⇔ d ∣ n かつ gcd(n/d, c) = 1。 -/
theorem inLayer_iff_dvd {c d n : ℕ} (hd : 0 < d) : InLayer c d n ↔ d ∣ n ∧ Nat.Coprime (n / d) c := by
  constructor
  · rintro ⟨e, rfl, he⟩
    refine ⟨Dvd.intro e rfl, ?_⟩
    rwa [Nat.mul_div_cancel_left e hd]
  · rintro ⟨hdn, hc⟩
    exact ⟨n / d, (Nat.mul_div_cancel' hdn).symm, hc⟩

/-- **4b.** d ∣ a、d ∣ n、c ∣ a/d なら gcd((n mod a)/d, c) = 1 ⇔ gcd(n/d, c) = 1（n/d ≡ (n mod a)/d mod a/d）。 -/
theorem coprime_mod_div_iff {a c d n : ℕ} (hda : d ∣ a) (hdn : d ∣ n) (hc : c ∣ a / d) :
    Nat.Coprime (n % a / d) c ↔ Nat.Coprime (n / d) c := by
  have hdm : d ∣ n % a := (Nat.dvd_mod_iff hda).mpr hdn
  have h1 : n / d = n % a / d + a / d * (n / a) := by
    conv_lhs => rw [← Nat.mod_add_div n a]
    rw [Nat.add_div_of_dvd_right hdm, Nat.mul_div_right_comm hda]
  obtain ⟨t, ht⟩ := hc
  rw [h1, ht, show c * t * (n / a) = t * (n / a) * c by ring, Nat.coprime_add_mul_right_left]

/-- **4c.** gcd(a, b) = 1、c_a d_a ∣ a、c_b d_b ∣ b、d_a, d_b > 0 なら「n は c_a c_b について d_a d_b の層」⇔「n mod a は c_a について d_a の層」かつ「n mod b は c_b について d_b の層」。 -/
theorem inLayer_mul_iff {a b ca da cb db n : ℕ} (hab : Nat.Coprime a b) (ha : ca * da ∣ a) (hb : cb * db ∣ b)
    (hda : 0 < da) (hdb : 0 < db) :
    InLayer (ca * cb) (da * db) n ↔ InLayer ca da (n % a) ∧ InLayer cb db (n % b) := by
  have hdaa : da ∣ a := dvd_trans (Dvd.intro_left ca rfl) ha
  have hdbb : db ∣ b := dvd_trans (Dvd.intro_left cb rfl) hb
  have hcaa : ca ∣ a := dvd_trans (Dvd.intro da rfl) ha
  have hcbb : cb ∣ b := dvd_trans (Dvd.intro db rfl) hb
  have hca : ca ∣ a / da := Nat.dvd_div_of_mul_dvd (by rwa [mul_comm] at ha)
  have hcb : cb ∣ b / db := Nat.dvd_div_of_mul_dvd (by rwa [mul_comm] at hb)
  have hcop_d : Nat.Coprime da db := Nat.Coprime.coprime_dvd_right hdbb (Nat.Coprime.coprime_dvd_left hdaa hab)
  have hcop_db_ca : Nat.Coprime db ca :=
    Nat.Coprime.coprime_dvd_right hcaa (Nat.Coprime.coprime_dvd_left hdbb hab.symm)
  have hcop_da_cb : Nat.Coprime da cb := Nat.Coprime.coprime_dvd_right hcbb (Nat.Coprime.coprime_dvd_left hdaa hab)
  have key : da * db ∣ n → n / da = n / (da * db) * db ∧ n / db = n / (da * db) * da := by
    intro hdiv
    refine ⟨?_, ?_⟩
    · rw [← Nat.div_div_eq_div_mul, Nat.div_mul_cancel (Nat.dvd_div_of_mul_dvd hdiv)]
    · have hdiv' : db * da ∣ n := by rwa [mul_comm] at hdiv
      rw [mul_comm da db, ← Nat.div_div_eq_div_mul, Nat.div_mul_cancel (Nat.dvd_div_of_mul_dvd hdiv')]
  rw [inLayer_iff_dvd (Nat.mul_pos hda hdb), inLayer_iff_dvd hda, inLayer_iff_dvd hdb,
    Nat.dvd_mod_iff hdaa, Nat.dvd_mod_iff hdbb]
  constructor
  · rintro ⟨hdiv, hcop⟩
    have hdan : da ∣ n := dvd_trans (dvd_mul_right da db) hdiv
    have hdbn : db ∣ n := dvd_trans (dvd_mul_left db da) hdiv
    obtain ⟨e1, e2⟩ := key hdiv
    rw [Nat.coprime_mul_iff_right] at hcop
    refine ⟨⟨hdan, ?_⟩, ⟨hdbn, ?_⟩⟩
    · rw [coprime_mod_div_iff hdaa hdan hca, e1, Nat.coprime_mul_iff_left]
      exact ⟨hcop.1, hcop_db_ca⟩
    · rw [coprime_mod_div_iff hdbb hdbn hcb, e2, Nat.coprime_mul_iff_left]
      exact ⟨hcop.2, hcop_da_cb⟩
  · rintro ⟨⟨hdan, hca'⟩, ⟨hdbn, hcb'⟩⟩
    have hdiv : da * db ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop_d hdan hdbn
    obtain ⟨e1, e2⟩ := key hdiv
    rw [coprime_mod_div_iff hdaa hdan hca, e1, Nat.coprime_mul_iff_left] at hca'
    rw [coprime_mod_div_iff hdbb hdbn hcb, e2, Nat.coprime_mul_iff_left] at hcb'
    refine ⟨hdiv, ?_⟩
    rw [Nat.coprime_mul_iff_right]
    exact ⟨hca'.1, hcb'.1⟩

/-- **4d.** (c_a, d_a) ∈ S(a)、(c_b, d_b) ∈ S(b) なら 1_{層}(x) = 1_{層}(x mod a)·1_{層}(x mod b)（Part 217 の layerInd）。 -/
theorem layerInd_crt {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b) (x : ZMod (a * b)) :
    layerInd (a * b) (ca * cb) (da * db) x =
      layerInd a ca da (ZMod.chineseRemainder hab x).1 * layerInd b cb db (ZMod.chineseRemainder hab x).2 := by
  rw [mem_centerIdx_iff_dvd] at hp hq
  obtain ⟨hca, ha0, -, hda, -⟩ := hp
  obtain ⟨hcb, hb0, -, hdb, -⟩ := hq
  have hLa : 0 < a / ca :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hca) (Nat.pos_of_dvd_of_pos hca (Nat.pos_of_ne_zero ha0))
  have hLb : 0 < b / cb :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hcb) (Nat.pos_of_dvd_of_pos hcb (Nat.pos_of_ne_zero hb0))
  have hda0 : 0 < da := Nat.pos_of_dvd_of_pos hda hLa
  have hdb0 : 0 < db := Nat.pos_of_dvd_of_pos hdb hLb
  have hiff := inLayer_mul_iff (n := x.val) hab (Nat.mul_dvd_of_dvd_div hca hda) (Nat.mul_dvd_of_dvd_div hcb hdb)
    hda0 hdb0
  unfold layerInd
  rw [crt_fst_val, crt_snd_val]
  by_cases h1 : InLayer ca da (x.val % a)
  · by_cases h2 : InLayer cb db (x.val % b)
    · rw [ite_eq_left (hiff.mpr ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2, one_mul]
    · rw [ite_eq_right (fun h => h2 (hiff.mp h).2), ite_eq_right h2, mul_zero]
  · rw [ite_eq_right (fun h => h1 (hiff.mp h).1), ite_eq_right h1, zero_mul]

/-- **4e.** C(ι_{(c_a c_b, d_a d_b)}) = L(ι_{(c_a,d_a)})·R(ι_{(c_b,d_b)})（ι は層の指示関数の掛け算）。 -/
theorem crtConj_layerInd {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b) :
    crtConj hab (LinearMap.mulLeft ℂ (layerInd (a * b) (ca * cb) (da * db))) =
      leftOp b (LinearMap.mulLeft ℂ (layerInd a ca da)) * rightOp a (LinearMap.mulLeft ℂ (layerInd b cb db)) := by
  apply LinearMap.ext
  intro F
  funext p
  show layerInd (a * b) (ca * cb) (da * db) ((ZMod.chineseRemainder hab).symm p) *
      F (ZMod.chineseRemainder hab ((ZMod.chineseRemainder hab).symm p)) =
    layerInd a ca da p.1 * (layerInd b cb db p.2 * F (p.1, p.2))
  rw [layerInd_crt hab hp hq, RingEquiv.apply_symm_apply, mul_assoc]

end PAG.Part235

#print axioms PAG.Part235.mulPull
#print axioms PAG.Part235.mulPull_apply
#print axioms PAG.Part235.dil_eq_mulPull
#print axioms PAG.Part235.mulPull_one
#print axioms PAG.Part235.crtConj_mulPull
#print axioms PAG.Part235.unitFst
#print axioms PAG.Part235.unitSnd
#print axioms PAG.Part235.unitFst_val
#print axioms PAG.Part235.unitSnd_val
#print axioms PAG.Part235.unitLeft
#print axioms PAG.Part235.unitRight
#print axioms PAG.Part235.crt_unitLeft
#print axioms PAG.Part235.crt_unitRight
#print axioms PAG.Part235.crtConj_dil
#print axioms PAG.Part235.crtConj_dil_unitLeft
#print axioms PAG.Part235.crtConj_dil_unitRight
#print axioms PAG.Part235.dilAlg
#print axioms PAG.Part235.dil_mem_dilAlg
#print axioms PAG.Part235.dil_commute
#print axioms PAG.Part235.map_crtConj_dilAlg
#print axioms PAG.Part235.map_crtConj_shellDilAlg
#print axioms PAG.Part235.map_crtConj_dilAlg_centralizer
#print axioms PAG.Part235.dilCommAlg
#print axioms PAG.Part235.dilAlg_le_centralizer
#print axioms PAG.Part235.mem_dilCommAlg_iff
#print axioms PAG.Part235.dilCommAlgLinearEquiv
#print axioms PAG.Part235.finrank_dilCommAlg
#print axioms PAG.Part235.map_crtConj_dilComm
#print axioms PAG.Part235.finrank_dilComm_mul
#print axioms PAG.Part235.dilCommTensorEquiv
#print axioms PAG.Part235.crtConj_dilCommTensorEquiv_tmul
#print axioms PAG.Part235.map_crtConj_dilComm_centralizer
#print axioms PAG.Part235.inLayer_iff_dvd
#print axioms PAG.Part235.coprime_mod_div_iff
#print axioms PAG.Part235.inLayer_mul_iff
#print axioms PAG.Part235.layerInd_crt
#print axioms PAG.Part235.crtConj_layerInd
