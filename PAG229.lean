/-
  PAG 2.0 Part 225（2026-10-29）— 二重可換子定理 A = A″、dim A = Σ_{p ∈ S} n_p²、A ≅ Π_p M_{n_p}(ℂ)
  A = ⟨E_s, D_s⟩（Part 214 の shellAlg）、A′（Part 220 の fullComm）、A″（Part 224 の doubleComm）、
  S = {(c, d)}（Part 222 の centerIdx）、W_p（Part 224 の refLayer）、n_p = dim W_p、
  ⟪f, g⟫ = Σ_x conj(f x)·g x（def herm）
  0. ⟪·,·⟫ のエルミート性・和とスカラー倍・正定値性
  1. 双対殻 D_s の指示関数 1_{D_s} は実数値で、ε_s = 𝓕⁻¹(1_{D_s}) は conj(ε_s(x)) = ε_s(−x)。
     E_s = ε_s ⋆ と D_s = 1_{D_s}· は ⟪·,·⟫ について自己共役で、
     A は共役で閉じる（def AdjClosed：各元 T に ⟪T f, g⟫ = ⟪f, T′ g⟫ となる T′ がある）。
     随伴 T*（def adjOp）を具体的に作ると、A′ も共役で閉じる
  2. 共役で閉じた部分代数 B と B で不変な部分空間 K について、直交補空間 K^⊥（def perpSub）も B で不変で
     K ⊕ K^⊥ = ℂ^{ℤ/N}（Mathlib の EuclideanSpace の直交補空間を使う）。ℂ^{ℤ/N} は半単純な B 加群で、
     B → (ℂ^{ℤ/N})^N、T ↦ (T δ_x)_x は単射な B 線形写像なので B は半単純環。B = A、A′ に使う
  3. End_A(ℂ^{ℤ/N}) の元は A′ に入る。ジャコブソンの稠密性定理（Mathlib の
     Module.Finite.toModuleEnd_moduleEnd_surjective）で A″ ⊆ A。よって A = A″（二重可換子定理）、
     dim A = Σ_{p ∈ S} n_p²、代数の同型 A ≅ Π_{p ∈ S} End(W_p) ≅ Π_p M_{n_p}(ℂ)
  4. 系：T ∈ A ⇔ T は A′ のすべての元と可換。A′ の中心 = A ∩ A′ = A の中心、z_{c,d} ∈ A、
     A の中心（Mathlib の Subalgebra.center）≅ ℂ^S、dim = #S
-/
import PAG228

namespace PAG.Part229

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 内積 ⟪f, g⟫ = Σ_x conj(f x)·g x -/

/-- ℂ^{ℤ/N} の標準の内積 ⟪f, g⟫ = Σ_x conj(f x)·g x（左の引数について共役線形）。 -/
noncomputable def herm (N : ℕ) [NeZero N] (f g : ZMod N → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x

/-- **0a.** conj⟪f, g⟫ = ⟪g, f⟫。 -/
theorem herm_conj (N : ℕ) [NeZero N] (f g : ZMod N → ℂ) : starRingEnd ℂ (herm N f g) = herm N g f := by
  unfold herm
  rw [map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [map_mul, Complex.conj_conj, mul_comm]

/-- **0b.** ⟪f + f′, g⟫ = ⟪f, g⟫ + ⟪f′, g⟫。 -/
theorem herm_add_left (N : ℕ) [NeZero N] (f f' g : ZMod N → ℂ) :
    herm N (f + f') g = herm N f g + herm N f' g := by
  unfold herm; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_); rw [Pi.add_apply, map_add, add_mul]

/-- **0c.** ⟪f, g + g′⟫ = ⟪f, g⟫ + ⟪f, g′⟫。 -/
theorem herm_add_right (N : ℕ) [NeZero N] (f g g' : ZMod N → ℂ) :
    herm N f (g + g') = herm N f g + herm N f g' := by
  unfold herm; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_); rw [Pi.add_apply, mul_add]

/-- **0d.** ⟪c·f, g⟫ = conj(c)·⟪f, g⟫。 -/
theorem herm_smul_left (N : ℕ) [NeZero N] (c : ℂ) (f g : ZMod N → ℂ) :
    herm N (c • f) g = starRingEnd ℂ c * herm N f g := by
  unfold herm; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_); rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

/-- **0e.** ⟪f, c·g⟫ = c·⟪f, g⟫。 -/
theorem herm_smul_right (N : ℕ) [NeZero N] (c : ℂ) (f g : ZMod N → ℂ) :
    herm N f (c • g) = c * herm N f g := by
  unfold herm; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_); rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- **0f.** 正定値性：⟪f, f⟫ = 0 なら f = 0。 -/
theorem herm_self_eq_zero (N : ℕ) [NeZero N] {f : ZMod N → ℂ} (h : herm N f f = 0) : f = 0 := by
  unfold herm at h
  have h' : ∑ x, (Complex.normSq (f x) : ℂ) = 0 := by
    rw [← h]; refine Finset.sum_congr rfl (fun x _ => ?_); rw [Complex.normSq_eq_conj_mul_self]
  have h'' : ∑ x, Complex.normSq (f x) = 0 := by exact_mod_cast h'
  funext x
  have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => Complex.normSq_nonneg (f y))).mp h'' x
    (Finset.mem_univ x)
  exact Complex.normSq_eq_zero.mp hx

/-- **0g.** ⟪f, g − g′⟫ = ⟪f, g⟫ − ⟪f, g′⟫。 -/
theorem herm_sub_right (N : ℕ) [NeZero N] (f g g' : ZMod N → ℂ) :
    herm N f (g - g') = herm N f g - herm N f g' := by
  unfold herm; rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_); rw [Pi.sub_apply, mul_sub]

/-- **0h.** 非退化性：すべての f で ⟪f, u⟫ = ⟪f, v⟫ なら u = v。 -/
theorem herm_ext (N : ℕ) [NeZero N] {u v : ZMod N → ℂ} (h : ∀ f, herm N f u = herm N f v) : u = v :=
  sub_eq_zero.mp (herm_self_eq_zero N (by rw [herm_sub_right, h, sub_self]))

/-! ### 1. E_s・D_s の自己共役性、A と A′ は共役で閉じる -/

/-- **1a.** 1_{D_s}（双対殻 D_s = {ξ : gcd(N, ξ) = s} の指示関数）は実数値。 -/
theorem conj_dind (N s : ℕ) (x : ZMod N) : starRingEnd ℂ (dind N s x) = dind N s x := by
  unfold dind; split_ifs <;> simp

/-- **1b.** conj(ε_s(x)) = ε_s(−x)（ε_s = 𝓕⁻¹(1_{D_s})、1_{D_s} は実数値）。 -/
theorem conj_geps (N s : ℕ) [NeZero N] (x : ZMod N) : starRingEnd ℂ (geps N s x) = geps N s (-x) := by
  unfold geps
  rw [ZMod.invDFT_apply, ZMod.invDFT_apply]
  simp only [smul_eq_mul, map_mul, map_sum, map_inv₀, map_natCast, conj_dind]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← AddChar.map_neg_eq_conj, mul_neg]

/-- (x, y) ↦ (x − y, −y)（畳み込みの和の付け替え。自分自身が逆写像）。 -/
def pairEquiv (N : ℕ) : ZMod N × ZMod N ≃ ZMod N × ZMod N where
  toFun p := (p.1 - p.2, -p.2)
  invFun p := (p.1 - p.2, -p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- **1c.** b(y) = conj(a(−y)) なら ⟪a ∗ f, g⟫ = ⟪f, b ∗ g⟫（畳み込みの随伴）。 -/
theorem herm_conv (N : ℕ) [NeZero N] (a b f g : ZMod N → ℂ) (hab : ∀ y, b y = starRingEnd ℂ (a (-y))) :
    herm N (PAG.Part15.conv a f) g = herm N f (PAG.Part15.conv b g) := by
  unfold herm PAG.Part15.conv
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (pairEquiv N) _ _ (fun p => ?_)
  simp only [pairEquiv, Equiv.coe_fn_mk, hab, neg_neg, sub_neg_eq_add, sub_add_cancel]
  ring

/-- **1d.** E_s は自己共役：⟪E_s f, g⟫ = ⟪f, E_s g⟫。 -/
theorem herm_geps_conv (N s : ℕ) [NeZero N] (f g : ZMod N → ℂ) :
    herm N (PAG.Part15.conv (geps N s) f) g = herm N f (PAG.Part15.conv (geps N s) g) :=
  herm_conv N _ _ f g (fun y => by rw [conj_geps, neg_neg])

/-- **1e.** D_s は自己共役：⟪D_s f, g⟫ = ⟪f, D_s g⟫。 -/
theorem herm_dind_mul (N s : ℕ) [NeZero N] (f g : ZMod N → ℂ) :
    herm N (dind N s * f) g = herm N f (dind N s * g) := by
  unfold herm
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Pi.mul_apply, Pi.mul_apply, map_mul, conj_dind]
  ring

/-- 部分代数 B は共役で閉じる：B の各元 T に ⟪T f, g⟫ = ⟪f, T′ g⟫ となる T′ ∈ B がある。 -/
def AdjClosed (N : ℕ) [NeZero N] (B : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))) : Prop :=
  ∀ T ∈ B, ∃ T' ∈ B, ∀ f g, herm N (T f) g = herm N f (T' g)

/-- **1f. A は共役で閉じる**（生成元は自己共役、積の共役は順を逆にした積）。 -/
theorem shellAlg_adjClosed (N : ℕ) [NeZero N] : AdjClosed N (shellAlg N) := by
  intro T hT
  unfold shellAlg at hT ⊢
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact ⟨PAG.Part15.convL (geps N s), Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩),
        fun f g => herm_geps_conv N s f g⟩
    · exact ⟨LinearMap.mulLeft ℂ (dind N s), Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩),
        fun f g => herm_dind_mul N s f g⟩
  | algebraMap r =>
    refine ⟨algebraMap ℂ _ (starRingEnd ℂ r), Subalgebra.algebraMap_mem _ _, fun f g => ?_⟩
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, herm_smul_left, herm_smul_right]
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨x' + y', add_mem hx' hy', fun f g => ?_⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, herm_add_left, herm_add_right, ex, ey]
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨y' * x', mul_mem hy' hx', fun f g => ?_⟩
    rw [Module.End.mul_apply, Module.End.mul_apply, ex, ey]

/-- **1g.** T f (x) = Σ_y f(y)·(T δ_y)(x)（δ_y = Pi.single y 1）。 -/
theorem apply_eq_sum_single (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) (f : ZMod N → ℂ) (x : ZMod N) :
    T f x = ∑ y, f y * T (Pi.single y 1) x := by
  conv_lhs => rw [pi_eq_sum_univ' f]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- 随伴作用素 T* g (y) = Σ_x conj((T δ_y)(x))·g(x)（共役転置行列）。 -/
noncomputable def adjOp (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) : Module.End ℂ (ZMod N → ℂ) where
  toFun g y := ∑ x, starRingEnd ℂ (T (Pi.single y 1) x) * g x
  map_add' g g' := by
    funext y
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring

/-- **1h.** ⟪T f, g⟫ = ⟪f, T* g⟫。 -/
theorem herm_adjOp (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) (f g : ZMod N → ℂ) :
    herm N (T f) g = herm N f (adjOp N T g) := by
  unfold herm
  simp only [apply_eq_sum_single N T f, adjOp, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
  ring

/-- **1i.** A′ の元の随伴は A′ に入る（A は共役で閉じるので）。 -/
theorem adjOp_mem_fullComm (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N) :
    adjOp N T ∈ fullComm N := by
  rw [mem_fullComm_iff_commute]
  intro S hS
  obtain ⟨S', hS', e⟩ := shellAlg_adjClosed N S hS
  have e' : ∀ h k, herm N h (S k) = herm N (S' h) k := fun h k => by
    rw [← herm_conj, e, herm_conj]
  have hc : Commute T S' := (mem_fullComm_iff_commute N T).mp hT S' hS'
  refine LinearMap.ext fun g => herm_ext N fun f => ?_
  show herm N f (adjOp N T (S g)) = herm N f (S (adjOp N T g))
  rw [← herm_adjOp, e', ← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, herm_adjOp, e']

/-- **1j. A′ は共役で閉じる**（随伴 T* が A′ に入る）。 -/
theorem fullCommAlg_adjClosed (N : ℕ) [NeZero N] : AdjClosed N (fullCommAlg N) := fun T hT =>
  ⟨adjOp N T, (mem_fullCommAlg N _).mpr (adjOp_mem_fullComm N ((mem_fullCommAlg N T).mp hT)),
    fun f g => herm_adjOp N T f g⟩

/-! ### 2. 直交補空間、半単純性（共役で閉じた部分代数 B） -/

/-- **2a.** B のスカラー c（= c·恒等写像）の作用は c 倍（加群の構造は Subalgebra.moduleLeft）。 -/
theorem algebraMap_sub_smul (N : ℕ) [NeZero N] (B : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))) (c : ℂ)
    (m : ZMod N → ℂ) : (algebraMap ℂ B c) • m = c • m := by
  rw [Subalgebra.smul_def]
  show (algebraMap ℂ (Module.End ℂ (ZMod N → ℂ)) c) m = c • m
  rw [Module.algebraMap_end_apply]

/-- B で不変な部分空間 K の直交補空間 K^⊥ = {g : ∀ k ∈ K, ⟪k, g⟫ = 0}（B は共役で閉じるので B で不変）。 -/
noncomputable def perpSub (N : ℕ) [NeZero N] {B : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))}
    (hB : AdjClosed N B) (K : Submodule B (ZMod N → ℂ)) : Submodule B (ZMod N → ℂ) where
  carrier := {g | ∀ k ∈ K, herm N k g = 0}
  add_mem' := fun {g g'} hg hg' k hk => by rw [herm_add_right, hg k hk, hg' k hk, add_zero]
  zero_mem' := fun k _ => by unfold herm; simp
  smul_mem' := fun a g hg k hk => by
    obtain ⟨a', ha', e⟩ := hB a.1 a.2
    have hk' : (⟨a', ha'⟩ : B) • k ∈ K := K.smul_mem _ hk
    show herm N k ((a : Module.End ℂ (ZMod N → ℂ)) g) = 0
    rw [← herm_conj, e, herm_conj]
    exact hg _ hk'

/-- **2b.** ⟪f, g⟫ は EuclideanSpace ℂ (ZMod N) の内積と一致。 -/
theorem herm_eq_inner (N : ℕ) [NeZero N] (f g : ZMod N → ℂ) :
    herm N f g = inner ℂ (WithLp.toLp 2 f : EuclideanSpace ℂ (ZMod N)) (WithLp.toLp 2 g) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  unfold herm dotProduct
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Pi.star_apply, Complex.star_def, mul_comm]

/-- B で不変な部分空間 K を EuclideanSpace ℂ (ZMod N) の部分空間とみなしたもの。 -/
noncomputable def toEuclid (N : ℕ) [NeZero N] {B : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))}
    (K : Submodule B (ZMod N → ℂ)) : Submodule ℂ (EuclideanSpace ℂ (ZMod N)) where
  carrier := {x | WithLp.ofLp x ∈ K}
  add_mem' := fun {x y} hx hy => by
    show WithLp.ofLp (x + y) ∈ K
    rw [WithLp.ofLp_add]; exact K.add_mem hx hy
  zero_mem' := by
    show WithLp.ofLp (0 : EuclideanSpace ℂ (ZMod N)) ∈ K
    rw [WithLp.ofLp_zero]; exact K.zero_mem
  smul_mem' := fun c x hx => by
    show WithLp.ofLp (c • x) ∈ K
    rw [WithLp.ofLp_smul, ← algebraMap_sub_smul N B]
    exact K.smul_mem _ hx

/-- **2c.** K と K^⊥ は補い合う：K ∩ K^⊥ = 0（正定値性）、K + K^⊥ = ℂ^{ℤ/N}（EuclideanSpace の直交分解）。 -/
theorem isCompl_perpSub (N : ℕ) [NeZero N] {B : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))}
    (hB : AdjClosed N B) (K : Submodule B (ZMod N → ℂ)) : IsCompl K (perpSub N hB K) := by
  apply IsCompl.of_eq
  · rw [eq_bot_iff]
    intro g hg
    rw [Submodule.mem_inf] at hg
    rw [Submodule.mem_bot]
    exact herm_self_eq_zero N (hg.2 g hg.1)
  · rw [eq_top_iff]
    intro m _
    have htop := Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := toEuclid N K)
    have hm : (WithLp.toLp 2 m : EuclideanSpace ℂ (ZMod N)) ∈ toEuclid N K ⊔ (toEuclid N K)ᗮ := by
      rw [htop]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hm
    rw [Submodule.mem_sup]
    refine ⟨WithLp.ofLp y, hy, WithLp.ofLp z, fun k hk => ?_, ?_⟩
    · have hk' : (WithLp.toLp 2 k : EuclideanSpace ℂ (ZMod N)) ∈ toEuclid N K := hk
      have h0 := (Submodule.mem_orthogonal (toEuclid N K) z).mp hz _ hk'
      rw [herm_eq_inner, WithLp.toLp_ofLp]
      exact h0
    · rw [← WithLp.ofLp_add, hyz]

/-- **2d. ℂ^{ℤ/N} は半単純な B 加群**（B で不変な部分空間はすべて B で不変な補空間をもつ）。 -/
theorem isSemisimpleModule_of_adjClosed (N : ℕ) [NeZero N] {B : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))}
    (hB : AdjClosed N B) : IsSemisimpleModule B (ZMod N → ℂ) :=
  { exists_isCompl := fun K => ⟨perpSub N hB K, isCompl_perpSub N hB K⟩ }

/-- **2e. B は半単純環**（B → (ℂ^{ℤ/N})^N、T ↦ (T δ_x)_x は単射な B 線形写像で、半単純加群の部分加群は半単純）。 -/
theorem isSemisimpleRing_of_adjClosed (N : ℕ) [NeZero N] {B : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))}
    (hB : AdjClosed N B) : IsSemisimpleRing B := by
  have := isSemisimpleModule_of_adjClosed N hB
  let g : B →ₗ[B] (ZMod N → (ZMod N → ℂ)) :=
    LinearMap.pi (fun x => LinearMap.toSpanSingleton B (ZMod N → ℂ) (Pi.single x 1))
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    refine LinearMap.pi_ext' (fun x => LinearMap.ext_ring ?_)
    have h := congrFun hab x
    change (a : Module.End ℂ (ZMod N → ℂ)) (Pi.single x 1) = (b : Module.End ℂ (ZMod N → ℂ)) (Pi.single x 1) at h
    simpa using h
  exact IsSemisimpleModule.of_injective
    ((Finsupp.linearEquivFunOnFinite B (ZMod N → ℂ) (ZMod N)).symm.toLinearMap ∘ₗ g)
    ((Finsupp.linearEquivFunOnFinite B (ZMod N → ℂ) (ZMod N)).symm.injective.comp hg)

/-- **2f. ℂ^{ℤ/N} は半単純な A 加群**。 -/
theorem shellAlg_isSemisimpleModule (N : ℕ) [NeZero N] : IsSemisimpleModule (shellAlg N) (ZMod N → ℂ) :=
  isSemisimpleModule_of_adjClosed N (shellAlg_adjClosed N)

/-- **2g. A は半単純環**。 -/
theorem shellAlg_isSemisimpleRing (N : ℕ) [NeZero N] : IsSemisimpleRing (shellAlg N) :=
  isSemisimpleRing_of_adjClosed N (shellAlg_adjClosed N)

/-- **2h. A′ は半単純環**（ℂ^{ℤ/N} も半単純な A′ 加群）。 -/
theorem fullCommAlg_isSemisimpleRing (N : ℕ) [NeZero N] : IsSemisimpleRing (fullCommAlg N) :=
  isSemisimpleRing_of_adjClosed N (fullCommAlg_adjClosed N)

/-! ### 3. ジャコブソンの稠密性定理、A = A″ -/

/-- A 加群の自己準同型 φ を ℂ 線形写像とみなしたもの（スカラー c は A の元 c·1）。 -/
noncomputable def endToComplex (N : ℕ) [NeZero N] (φ : Module.End (shellAlg N) (ZMod N → ℂ)) :
    Module.End ℂ (ZMod N → ℂ) where
  toFun := φ
  map_add' := φ.map_add
  map_smul' c m := by
    rw [RingHom.id_apply, ← algebraMap_sub_smul N (shellAlg N), φ.map_smul, algebraMap_sub_smul N (shellAlg N)]

/-- **3a.** End_A(ℂ^{ℤ/N}) の元は A′ に入る（E_s・D_s は A の元）。 -/
theorem endToComplex_mem_fullComm (N : ℕ) [NeZero N] (φ : Module.End (shellAlg N) (ZMod N → ℂ)) :
    endToComplex N φ ∈ fullComm N := by
  rw [mem_fullComm]
  intro s f
  have hE : PAG.Part15.convL (geps N s) ∈ shellAlg N := Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)
  have hD : LinearMap.mulLeft ℂ (dind N s) ∈ shellAlg N := Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)
  exact ⟨φ.map_smul ⟨_, hE⟩ f, φ.map_smul ⟨_, hD⟩ f⟩

/-- **3b. A″ ⊆ A**（ジャコブソンの稠密性定理：ℂ^{ℤ/N} は半単純な A 加群で、End_A(ℂ^{ℤ/N}) の上で有限生成なので、
A → End_{End_A}(ℂ^{ℤ/N}) は全射。A″ の元は End_A の元と可換）。 -/
theorem doubleComm_le_shellAlg (N : ℕ) [NeZero N] : doubleComm N ≤ shellAlg N := by
  intro T hT
  have := shellAlg_isSemisimpleModule N
  have : Module.Finite (Module.End (shellAlg N) (ZMod N → ℂ)) (ZMod N → ℂ) :=
    Module.Finite.of_restrictScalars_finite ℂ _ _
  let fT : Module.End (Module.End (shellAlg N) (ZMod N → ℂ)) (ZMod N → ℂ) :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun φ m => by
        have hc := ((mem_doubleComm N T).mp hT) _ (endToComplex_mem_fullComm N φ)
        exact LinearMap.congr_fun hc.eq m }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := shellAlg N) (M := ZMod N → ℂ) fT
  have e : (a : Module.End ℂ (ZMod N → ℂ)) = T := LinearMap.ext fun m => LinearMap.congr_fun ha m
  rw [← e]
  exact a.2

/-- **3c. 二重可換子定理 A = A″**。 -/
theorem shellAlg_eq_doubleComm (N : ℕ) [NeZero N] : shellAlg N = doubleComm N :=
  le_antisymm (shellAlg_le_doubleComm N) (doubleComm_le_shellAlg N)

/-- **3d. dim A = Σ_{p ∈ S} n_p²**（n_p = #{v ∣ N/c : v の層 = d}）。 -/
theorem finrank_shellAlg (N : ℕ) [NeZero N] :
    Module.finrank ℂ (shellAlg N) = ∑ p : centerIdx N, (layerDivs p.1.1 p.1.2 (N / p.1.1)).card ^ 2 := by
  rw [shellAlg_eq_doubleComm]
  exact finrank_doubleComm N

/-- **代数の同型** A ≅ Π_{p ∈ S} End(W_p)（W_p への制限）。 -/
noncomputable def shellAlgEquiv (N : ℕ) [NeZero N] :
    shellAlg N ≃ₐ[ℂ] Π p : centerIdx N, Module.End ℂ (refLayer N p) :=
  (Subalgebra.equivOfEq _ _ (shellAlg_eq_doubleComm N)).trans (doubleCommEquiv N)

/-- **代数の同型** A ≅ Π_{p ∈ S} M_{n_p}(ℂ)（ウェダーバーン分解を具体的に与えたもの）。 -/
noncomputable def shellAlgMatrixEquiv (N : ℕ) [NeZero N] :
    shellAlg N ≃ₐ[ℂ] Π p : centerIdx N,
      Matrix (Fin (Module.finrank ℂ (refLayer N p))) (Fin (Module.finrank ℂ (refLayer N p))) ℂ :=
  (Subalgebra.equivOfEq _ _ (shellAlg_eq_doubleComm N)).trans (doubleCommMatrixEquiv N)

/-! ### 4. 系：A の判定、A の中心 = A ∩ A′ = A′ の中心 -/

/-- **4a.** T ∈ A ⇔ T は A′ のすべての元と可換。 -/
theorem mem_shellAlg_iff_commute (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ shellAlg N ↔ ∀ S ∈ fullComm N, Commute T S := by
  rw [shellAlg_eq_doubleComm, mem_doubleComm]

/-- **4b.** A′ の中心 = A ∩ A′。 -/
theorem mem_fullCommCenter_iff (N : ℕ) [NeZero N] (Z : Module.End ℂ (ZMod N → ℂ)) :
    Z ∈ fullCommCenter N ↔ Z ∈ shellAlg N ∧ Z ∈ fullComm N := by
  rw [mem_fullCommCenter, mem_shellAlg_iff_commute]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **4c.** z_{c,d} ∈ A（rad(d) ∣ c。Part 222 の中心の元）。 -/
theorem centralElt_mem_shellAlg (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (c d : ℕ) (hd : RadDvd d c) :
    centralElt N c d ∈ shellAlg N :=
  ((mem_fullCommCenter_iff N _).mp (centralElt_mem_center N c d hd)).1

/-- **4d.** A の元 Z が A の中心（Mathlib の Subalgebra.center）に入る ⇔ Z は A′ の中心に入る。 -/
theorem mem_center_shellAlg (N : ℕ) [NeZero N] (Z : shellAlg N) :
    Z ∈ Subalgebra.center ℂ (shellAlg N) ↔ (Z : Module.End ℂ (ZMod N → ℂ)) ∈ fullCommCenter N := by
  rw [Subalgebra.mem_center_iff, mem_fullCommCenter]
  constructor
  · intro h
    have hA' : (Z : Module.End ℂ (ZMod N → ℂ)) ∈ fullComm N := by
      rw [mem_fullComm_iff_commute]
      intro S hS
      show (Z : Module.End ℂ (ZMod N → ℂ)) * S = S * Z
      exact (congrArg Subtype.val (h ⟨S, hS⟩)).symm
    exact ⟨hA', fun T hT => (mem_doubleComm N _).mp (shellAlg_le_doubleComm N Z.2) T hT⟩
  · rintro ⟨hA', -⟩ b
    exact Subtype.ext ((mem_fullComm_iff_commute N _).mp hA' b.1 b.2).eq.symm

/-- A の中心（Mathlib の Subalgebra.center）と Part 222 の centerAlg の代数の同型（Z ↦ Z）。 -/
noncomputable def centerShellMathlibEquiv (N : ℕ) [NeZero N] :
    Subalgebra.center ℂ (shellAlg N) ≃ₐ[ℂ] centerAlg N where
  toFun Z := ⟨Z.1.1, (mem_centerAlg N _).mpr ((mem_center_shellAlg N Z.1).mp Z.2)⟩
  invFun Z := ⟨⟨Z.1, ((mem_fullCommCenter_iff N _).mp ((mem_centerAlg N _).mp Z.2)).1⟩,
    (mem_center_shellAlg N _).mpr ((mem_centerAlg N _).mp Z.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- **代数の同型** ℂ^S ≅ A の中心（a ↦ Σ_p a_p·z_p。Part 222 の centerAlgEquiv と合成）。 -/
noncomputable def centerShellEquivPi (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    (centerIdx N → ℂ) ≃ₐ[ℂ] Subalgebra.center ℂ (shellAlg N) :=
  (centerAlgEquiv N).trans (centerShellMathlibEquiv N).symm

/-- A の中心と fullCommCenter の線形同型（Z ↦ Z）。 -/
noncomputable def centerShellLinearEquiv (N : ℕ) [NeZero N] :
    Subalgebra.center ℂ (shellAlg N) ≃ₗ[ℂ] fullCommCenter N where
  toFun Z := ⟨Z.1.1, (mem_center_shellAlg N Z.1).mp Z.2⟩
  invFun Z := ⟨⟨Z.1, ((mem_fullCommCenter_iff N _).mp Z.2).1⟩, (mem_center_shellAlg N _).mpr Z.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **4e. dim Z(A)（Mathlib の Subalgebra.center）= #S** = Σ_{c ∣ N, m(c) > 0} Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)。 -/
theorem finrank_center_shellAlg (N : ℕ) [NeZero N] :
    Module.finrank ℂ (Subalgebra.center ℂ (shellAlg N)) =
      ∑ c ∈ N.divisors.filter (fun c => 0 < Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive}),
        ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1) :=
  (centerShellLinearEquiv N).finrank_eq.trans (finrank_fullCommCenter N)

end PAG.Part229

#print axioms PAG.Part229.herm
#print axioms PAG.Part229.herm_conj
#print axioms PAG.Part229.herm_add_left
#print axioms PAG.Part229.herm_add_right
#print axioms PAG.Part229.herm_smul_left
#print axioms PAG.Part229.herm_smul_right
#print axioms PAG.Part229.herm_self_eq_zero
#print axioms PAG.Part229.herm_sub_right
#print axioms PAG.Part229.herm_ext
#print axioms PAG.Part229.conj_dind
#print axioms PAG.Part229.conj_geps
#print axioms PAG.Part229.pairEquiv
#print axioms PAG.Part229.herm_conv
#print axioms PAG.Part229.herm_geps_conv
#print axioms PAG.Part229.herm_dind_mul
#print axioms PAG.Part229.AdjClosed
#print axioms PAG.Part229.shellAlg_adjClosed
#print axioms PAG.Part229.apply_eq_sum_single
#print axioms PAG.Part229.adjOp
#print axioms PAG.Part229.herm_adjOp
#print axioms PAG.Part229.adjOp_mem_fullComm
#print axioms PAG.Part229.fullCommAlg_adjClosed
#print axioms PAG.Part229.algebraMap_sub_smul
#print axioms PAG.Part229.perpSub
#print axioms PAG.Part229.herm_eq_inner
#print axioms PAG.Part229.toEuclid
#print axioms PAG.Part229.isCompl_perpSub
#print axioms PAG.Part229.isSemisimpleModule_of_adjClosed
#print axioms PAG.Part229.isSemisimpleRing_of_adjClosed
#print axioms PAG.Part229.shellAlg_isSemisimpleModule
#print axioms PAG.Part229.shellAlg_isSemisimpleRing
#print axioms PAG.Part229.fullCommAlg_isSemisimpleRing
#print axioms PAG.Part229.endToComplex
#print axioms PAG.Part229.endToComplex_mem_fullComm
#print axioms PAG.Part229.doubleComm_le_shellAlg
#print axioms PAG.Part229.shellAlg_eq_doubleComm
#print axioms PAG.Part229.finrank_shellAlg
#print axioms PAG.Part229.shellAlgEquiv
#print axioms PAG.Part229.shellAlgMatrixEquiv
#print axioms PAG.Part229.mem_shellAlg_iff_commute
#print axioms PAG.Part229.mem_fullCommCenter_iff
#print axioms PAG.Part229.centralElt_mem_shellAlg
#print axioms PAG.Part229.mem_center_shellAlg
#print axioms PAG.Part229.centerShellMathlibEquiv
#print axioms PAG.Part229.centerShellEquivPi
#print axioms PAG.Part229.centerShellLinearEquiv
#print axioms PAG.Part229.finrank_center_shellAlg
