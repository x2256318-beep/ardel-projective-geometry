/-
  PAG 2.0 Part 220（2026-10-29）— 空間全体の可換子の次元 Σ_c m(c)²π(c)
  A = ⟨E_s, D_s⟩（E_s = ε_s ⋆、D_s = 1_{D_s}·、Part 214 の shellAlg）、
  A′ = 空間全体の可換子：すべての E_s・D_s と可換な ℂ^{ℤ/N} の線形変換（def fullComm）
  ブロックの番号 b = (c, χ)（Part 211 の BlockIdx）、V_b = blockSpan、P_b = blockProj、
  Hom_A(V_b, V_b′) = blockHom（Part 218）、π(c) = Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)、m(c) = 法 c の原始指標の数
  0. 準備：ブロックの番号の法は 0 でない（インスタンス）。番号が違えば (c, χ) の組も違う。
     V_b の元は違うブロックの射影で 0。Σ_b P_b f = f
  1. 成分：T ∈ A′ なら P_b′∘T|_{V_b} ∈ Hom_A(V_b, V_b′)（def commBlock）
  2. 組み立て：X ∈ Hom_A(V_b, V_b′) の延長 f ↦ X(P_b f)（Part 219 の blockHomExt）は A′ に入る。
     族 (X_{b,b′}) から Σ_{(b,b′)} X_{b,b′}∘P_b ∈ A′（def commSum）
  3. 線形同型 A′ ≅ Π_{(b,b′)} Hom_A(V_b, V_b′)（def commEquiv。往復は Σ_b P_b = 1 と P_b′ P_b = [b = b′]P_b から）
  4. 次元：dim A′ = Σ_{(b,b′)} [c_b = c_b′]·π(c_b) = Σ_{c ∣ N} m(c)²·π(c)（Part 219 の finrank_blockHom_eq_ite から）
  5. A′ は A の中心化環：T ∈ A′ ⇔ A のすべての元と可換
-/
import PAG223

namespace PAG.Part224

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

/-- ブロックの番号の法 c（N の約数）は 0 でない。 -/
instance neZero_divisors (N : ℕ) (c : N.divisors) : NeZero (c : ℕ) :=
  ⟨(Nat.pos_of_mem_divisors c.2).ne'⟩

/-- **0a.** 番号が違えば (c, χ) の組も違う。 -/
theorem sigma_ne_of_ne {N : ℕ} {b b' : BlockIdx N} (h : b ≠ b') :
    (⟨(b.1 : ℕ), b.2.1⟩ : Σ c : ℕ, DirichletCharacter ℂ c) ≠ ⟨(b'.1 : ℕ), b'.2.1⟩ := by
  obtain ⟨⟨c, hc⟩, ⟨χ, hχ⟩⟩ := b
  obtain ⟨⟨c', hc'⟩, ⟨χ', hχ'⟩⟩ := b'
  intro e
  apply h
  cases e
  rfl

/-- **0b.** V_{c,χ} の元は、ほかのブロックの射影で 0：(c, χ) ≠ (c′, χ′) なら P_{c′,χ′} f = 0。 -/
theorem blockProj_eq_zero_of_mem (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    (hne : (⟨c, χ⟩ : Σ c : ℕ, DirichletCharacter ℂ c) ≠ ⟨c', χ'⟩) {f : ZMod N → ℂ}
    (hf : f ∈ blockSpan N c χ) : blockProj N c' χ' f = 0 := by
  unfold blockSpan at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    have e := blockProj_ketFam_of_ne N c' hc'N χ' hχ' (blockIdx N c hcN χ hχ w) hne
    rw [ketFam_blockIdx N c hcN χ hχ w] at e
    exact e
  | zero =>
    rw [← blockProjL_apply, map_zero]
  | add x y _ _ hx hy =>
    rw [← blockProjL_apply, map_add, blockProjL_apply, blockProjL_apply, hx, hy, add_zero]
  | smul r x _ hx =>
    rw [← blockProjL_apply, map_smul, blockProjL_apply, hx, smul_zero]

/-- **0c.** 番号の形：b ≠ b′、f ∈ V_b なら P_b′ f = 0。 -/
theorem blockProj_eq_zero_of_mem_idx (N : ℕ) [NeZero N] {b b' : BlockIdx N} (h : b ≠ b') {f : ZMod N → ℂ}
    (hf : f ∈ blockSpan N b.1 b.2.1) : blockProj N b'.1 b'.2.1 f = 0 :=
  blockProj_eq_zero_of_mem N b.1 b'.1 (Nat.dvd_of_mem_divisors b.1.2) (Nat.dvd_of_mem_divisors b'.1.2)
    b.2.1 b'.2.1 b.2.2 b'.2.2 (sigma_ne_of_ne h) hf

/-- **0d.** Σ_b P_b f = f（Part 211 の `sum_blockProjI` を blockProj の形で）。 -/
theorem sum_blockProj (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (f : ZMod N → ℂ) :
    ∑ b : BlockIdx N, blockProj N b.1 b.2.1 f = f :=
  (sum_blockProjI N f).symm

/-- **0e.** 部分空間から部分空間への線形写像：値が等しい元での値は等しい。 -/
theorem linearMap_apply_congr {N : ℕ} {V W : Submodule ℂ (ZMod N → ℂ)} (X : V →ₗ[ℂ] W) {f g : ZMod N → ℂ}
    (hf : f ∈ V) (hg : g ∈ V) (e : f = g) : (X ⟨f, hf⟩ : ZMod N → ℂ) = X ⟨g, hg⟩ := by
  subst e
  rfl

/-- **0f.** 部分空間から部分空間への線形写像：値が 0 の元での値は 0。 -/
theorem linearMap_apply_eq_zero {N : ℕ} {V W : Submodule ℂ (ZMod N → ℂ)} (X : V →ₗ[ℂ] W) {g : ZMod N → ℂ}
    (hg : g ∈ V) (e : g = 0) : (X ⟨g, hg⟩ : ZMod N → ℂ) = 0 := by
  subst e
  rw [show (⟨0, hg⟩ : V) = 0 from rfl, map_zero, Submodule.coe_zero]

/-! ### 1. 空間全体の可換子と、その成分 -/

/-- 空間全体の可換子 A′：すべての E_s = ε_s ⋆ と D_s = 1_{D_s}· と可換な線形変換。 -/
noncomputable def fullComm (N : ℕ) [NeZero N] : Submodule ℂ (Module.End ℂ (ZMod N → ℂ)) where
  carrier := {T | ∀ (s : ℕ) (f : ZMod N → ℂ),
    T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f) ∧ T (dind N s * f) = dind N s * T f}
  add_mem' := by
    intro T₁ T₂ h₁ h₂
    simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
    intro s f
    refine ⟨?_, ?_⟩
    · rw [LinearMap.add_apply, LinearMap.add_apply, (h₁ s f).1, (h₂ s f).1, ← PAG.Part15.convL_apply,
        ← PAG.Part15.convL_apply, ← PAG.Part15.convL_apply, map_add]
    · rw [LinearMap.add_apply, LinearMap.add_apply, (h₁ s f).2, (h₂ s f).2, mul_add]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    intro s f
    refine ⟨?_, ?_⟩
    · rw [LinearMap.zero_apply, LinearMap.zero_apply, ← PAG.Part15.convL_apply, map_zero]
    · rw [LinearMap.zero_apply, LinearMap.zero_apply, mul_zero]
  smul_mem' := by
    intro r T hT
    simp only [Set.mem_ofPred_eq] at hT ⊢
    intro s f
    refine ⟨?_, ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, (hT s f).1, ← PAG.Part15.convL_apply,
        ← PAG.Part15.convL_apply, map_smul]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, (hT s f).2, mul_smul_comm]

/-- **1a.** 可換子の元の判定。 -/
theorem mem_fullComm (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ fullComm N ↔ ∀ (s : ℕ) (f : ZMod N → ℂ),
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f) ∧ T (dind N s * f) = dind N s * T f :=
  Iff.rfl

/-- T の (b, b′) 成分：V_b → V_b′、f ↦ P_b′ (T f)。 -/
noncomputable def commBlock (N : ℕ) [NeZero N] (b b' : BlockIdx N) (T : Module.End ℂ (ZMod N → ℂ)) :
    blockSpan N b.1 b.2.1 →ₗ[ℂ] blockSpan N b'.1 b'.2.1 :=
  LinearMap.codRestrict (blockSpan N b'.1 b'.2.1) (blockProjL N b'.1 b'.2.1 ∘ₗ T ∘ₗ (blockSpan N b.1 b.2.1).subtype)
    (fun _ => blockProjL_mem N b'.1 b'.2.1 _)

/-- **1b.** (T の (b, b′) 成分)(f) = P_b′ (T f)。 -/
theorem commBlock_apply (N : ℕ) [NeZero N] (b b' : BlockIdx N) (T : Module.End ℂ (ZMod N → ℂ))
    (f : blockSpan N b.1 b.2.1) : (commBlock N b b' T f : ZMod N → ℂ) = blockProj N b'.1 b'.2.1 (T f) := rfl

/-- **1c.** T ∈ A′ なら成分 P_b′∘T|_{V_b} は A 準同型（blockHom に入る）。 -/
theorem commBlock_mem (N : ℕ) [NeZero N] (b b' : BlockIdx N) {T : Module.End ℂ (ZMod N → ℂ)}
    (hT : T ∈ fullComm N) : commBlock N b b' T ∈ blockHom N b.1 b'.1 b.2.1 b'.2.1 := by
  have hb' : (b'.1 : ℕ) ∣ N := Nat.dvd_of_mem_divisors b'.1.2
  rw [mem_blockHom]
  intro s f hf
  refine ⟨fun h => ?_, fun h => ?_⟩
  · calc (commBlock N b b' T ⟨PAG.Part15.conv (geps N s) f, h⟩ : ZMod N → ℂ)
        = blockProj N b'.1 b'.2.1 (T (PAG.Part15.conv (geps N s) f)) := rfl
      _ = blockProj N b'.1 b'.2.1 (PAG.Part15.conv (geps N s) (T f)) := by
          rw [((mem_fullComm N T).mp hT s f).1]
      _ = PAG.Part15.conv (geps N s) (blockProj N b'.1 b'.2.1 (T f)) :=
          (geps_conv_blockProj N b'.1 hb' b'.2.1 b'.2.2 s (T f)).symm
      _ = PAG.Part15.conv (geps N s) (commBlock N b b' T ⟨f, hf⟩ : ZMod N → ℂ) := rfl
  · calc (commBlock N b b' T ⟨dind N s * f, h⟩ : ZMod N → ℂ)
        = blockProj N b'.1 b'.2.1 (T (dind N s * f)) := rfl
      _ = blockProj N b'.1 b'.2.1 (dind N s * T f) := by
          rw [((mem_fullComm N T).mp hT s f).2]
      _ = dind N s * blockProj N b'.1 b'.2.1 (T f) :=
          (dind_mul_blockProj N b'.1 hb' b'.2.1 b'.2.2 s (T f)).symm
      _ = dind N s * (commBlock N b b' T ⟨f, hf⟩ : ZMod N → ℂ) := rfl

/-! ### 2. 成分の族からの組み立て -/

/-- **2a.** 延長の値：(X の延長)(g) = X (P g)。 -/
theorem blockHomExt_apply_proj (N c c' : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c)
    (χ' : DirichletCharacter ℂ c') (X : blockSpan N c χ →ₗ[ℂ] blockSpan N c' χ') (g : ZMod N → ℂ) :
    blockHomExt N c c' χ χ' X g = (X ⟨blockProjL N c χ g, blockProjL_mem N c χ g⟩ : ZMod N → ℂ) := rfl

/-- **2b.** X ∈ Hom_A(V_{c,χ}, V_{c′,χ′}) なら、空間全体への延長 f ↦ X(P f) は A′ に入る。 -/
theorem blockHomExt_mem_fullComm (N c c' : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) {X : blockSpan N c χ →ₗ[ℂ] blockSpan N c' χ'}
    (hX : X ∈ blockHom N c c' χ χ') : blockHomExt N c c' χ χ' X ∈ fullComm N := by
  have hinv := blockSpan_shellInvariant N c hcN χ hχ
  rw [mem_fullComm]
  intro s g
  have hPg : blockProj N c χ g ∈ blockSpan N c χ := blockProjL_mem N c χ g
  refine ⟨?_, ?_⟩
  · calc blockHomExt N c c' χ χ' X (PAG.Part15.conv (geps N s) g)
        = (X ⟨blockProjL N c χ (PAG.Part15.conv (geps N s) g), blockProjL_mem N c χ _⟩ : ZMod N → ℂ) := rfl
      _ = (X ⟨PAG.Part15.conv (geps N s) (blockProj N c χ g), (hinv s _ hPg).1⟩ : ZMod N → ℂ) :=
          linearMap_apply_congr X _ _ (geps_conv_blockProj N c hcN χ hχ s g).symm
      _ = PAG.Part15.conv (geps N s) (X ⟨blockProj N c χ g, hPg⟩ : ZMod N → ℂ) :=
          ((mem_blockHom N c c' χ χ' X).mp hX s (blockProj N c χ g) hPg).1 (hinv s _ hPg).1
      _ = PAG.Part15.conv (geps N s) (blockHomExt N c c' χ χ' X g) := rfl
  · calc blockHomExt N c c' χ χ' X (dind N s * g)
        = (X ⟨blockProjL N c χ (dind N s * g), blockProjL_mem N c χ _⟩ : ZMod N → ℂ) := rfl
      _ = (X ⟨dind N s * blockProj N c χ g, (hinv s _ hPg).2⟩ : ZMod N → ℂ) :=
          linearMap_apply_congr X _ _ (dind_mul_blockProj N c hcN χ hχ s g).symm
      _ = dind N s * (X ⟨blockProj N c χ g, hPg⟩ : ZMod N → ℂ) :=
          ((mem_blockHom N c c' χ χ' X).mp hX s (blockProj N c χ g) hPg).2 (hinv s _ hPg).2
      _ = dind N s * blockHomExt N c c' χ χ' X g := rfl

/-- 成分の族 (X_{b,b′}) を組み立てたもの：Σ_{(b,b′)} (f ↦ X_{b,b′}(P_b f))。 -/
noncomputable def commSum (N : ℕ) [NeZero N] [Fintype (BlockIdx N)]
    (X : (p : BlockIdx N × BlockIdx N) → blockHom N p.1.1 p.2.1 p.1.2.1 p.2.2.1) :
    Module.End ℂ (ZMod N → ℂ) :=
  ∑ p : BlockIdx N × BlockIdx N, blockHomExt N p.1.1 p.2.1 p.1.2.1 p.2.2.1 (X p).1

/-- **2c.** 組み立てたものは A′ に入る。 -/
theorem commSum_mem (N : ℕ) [NeZero N] [Fintype (BlockIdx N)]
    (X : (p : BlockIdx N × BlockIdx N) → blockHom N p.1.1 p.2.1 p.1.2.1 p.2.2.1) : commSum N X ∈ fullComm N :=
  Submodule.sum_mem _ (fun p _ => blockHomExt_mem_fullComm N p.1.1 p.2.1 (Nat.dvd_of_mem_divisors p.1.1.2)
    p.1.2.1 p.2.2.1 p.1.2.2 (X p).2)

/-! ### 3. 線形同型 A′ ≅ Π_{(b,b′)} Hom_A(V_b, V_b′) -/

/-- A′ → Π_{(b,b′)} Hom_A(V_b, V_b′)：T ↦ (P_b′∘T|_{V_b})。 -/
noncomputable def commToFamily (N : ℕ) [NeZero N] :
    fullComm N →ₗ[ℂ] ((p : BlockIdx N × BlockIdx N) → blockHom N p.1.1 p.2.1 p.1.2.1 p.2.2.1) where
  toFun T p := ⟨commBlock N p.1 p.2 T, commBlock_mem N p.1 p.2 T.2⟩
  map_add' T₁ T₂ := by
    funext p
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    show blockProjL N p.2.1 p.2.2.1 (((T₁ + T₂ : fullComm N) : Module.End ℂ (ZMod N → ℂ)) f) =
      blockProjL N p.2.1 p.2.2.1 ((T₁ : Module.End ℂ (ZMod N → ℂ)) f) +
        blockProjL N p.2.1 p.2.2.1 ((T₂ : Module.End ℂ (ZMod N → ℂ)) f)
    rw [Submodule.coe_add, LinearMap.add_apply, map_add]
  map_smul' r T := by
    funext p
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    show blockProjL N p.2.1 p.2.2.1 (((r • T : fullComm N) : Module.End ℂ (ZMod N → ℂ)) f) =
      r • blockProjL N p.2.1 p.2.2.1 ((T : Module.End ℂ (ZMod N → ℂ)) f)
    rw [Submodule.coe_smul, LinearMap.smul_apply, map_smul]

/-- Π_{(b,b′)} Hom_A(V_b, V_b′) → A′：(X_{b,b′}) ↦ Σ X_{b,b′}∘P_b。 -/
noncomputable def familyToComm (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    ((p : BlockIdx N × BlockIdx N) → blockHom N p.1.1 p.2.1 p.1.2.1 p.2.2.1) →ₗ[ℂ] fullComm N where
  toFun X := ⟨commSum N X, commSum_mem N X⟩
  map_add' X₁ X₂ := by
    apply Subtype.ext
    show commSum N (X₁ + X₂) = commSum N X₁ + commSum N X₂
    unfold commSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    apply LinearMap.ext
    intro g
    rfl
  map_smul' r X := by
    apply Subtype.ext
    show commSum N (r • X) = r • commSum N X
    unfold commSum
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    apply LinearMap.ext
    intro g
    rfl

/-- **3a.** T ∈ A′ を成分に分けて組み立て直すと T：Σ_{(b,b′)} P_b′ (T (P_b g)) = T g。 -/
theorem commSum_commBlock (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] {T : Module.End ℂ (ZMod N → ℂ)}
    (hT : T ∈ fullComm N) (g : ZMod N → ℂ) :
    commSum N (fun p => ⟨commBlock N p.1 p.2 T, commBlock_mem N p.1 p.2 hT⟩) g = T g := by
  unfold commSum
  rw [LinearMap.sum_apply]
  calc ∑ p : BlockIdx N × BlockIdx N, blockHomExt N p.1.1 p.2.1 p.1.2.1 p.2.2.1 (commBlock N p.1 p.2 T) g
      = ∑ p : BlockIdx N × BlockIdx N, blockProj N p.2.1 p.2.2.1 (T (blockProj N p.1.1 p.1.2.1 g)) := rfl
    _ = ∑ b : BlockIdx N, ∑ b' : BlockIdx N, blockProj N b'.1 b'.2.1 (T (blockProj N b.1 b.2.1 g)) :=
        Fintype.sum_prod_type _
    _ = ∑ b : BlockIdx N, T (blockProj N b.1 b.2.1 g) := by simp only [sum_blockProj]
    _ = T g := by rw [← map_sum, sum_blockProj]

/-- **3b.** 族を組み立ててから (b₀, b₀′) 成分をとると X_{b₀,b₀′}：f ∈ V_{b₀} なら
P_{b₀′}(Σ_{(b,b′)} X_{b,b′}(P_b f)) = X_{b₀,b₀′} f。 -/
theorem commBlock_commSum (N : ℕ) [NeZero N] [Fintype (BlockIdx N)]
    (X : (p : BlockIdx N × BlockIdx N) → blockHom N p.1.1 p.2.1 p.1.2.1 p.2.2.1) (b₀ b₀' : BlockIdx N)
    {f : ZMod N → ℂ} (hf : f ∈ blockSpan N b₀.1 b₀.2.1) :
    blockProj N b₀'.1 b₀'.2.1 (commSum N X f) = ((X (b₀, b₀')).1 ⟨f, hf⟩ : ZMod N → ℂ) := by
  have hb₀ : (b₀.1 : ℕ) ∣ N := Nat.dvd_of_mem_divisors b₀.1.2
  have hb₀' : (b₀'.1 : ℕ) ∣ N := Nat.dvd_of_mem_divisors b₀'.1.2
  unfold commSum
  rw [LinearMap.sum_apply, ← blockProjL_apply, map_sum, Finset.sum_eq_single (b₀, b₀')]
  · show blockProj N b₀'.1 b₀'.2.1
      (((X (b₀, b₀')).1 ⟨blockProjL N b₀.1 b₀.2.1 f, blockProjL_mem N b₀.1 b₀.2.1 f⟩ : ZMod N → ℂ)) = _
    have hy := ((X (b₀, b₀')).1 ⟨blockProjL N b₀.1 b₀.2.1 f, blockProjL_mem N b₀.1 b₀.2.1 f⟩).2
    rw [blockProj_of_mem N b₀'.1 hb₀' b₀'.2.1 b₀'.2.2 hy]
    exact linearMap_apply_congr _ _ _ (blockProj_of_mem N b₀.1 hb₀ b₀.2.1 b₀.2.2 hf)
  · intro p _ hp
    show blockProj N b₀'.1 b₀'.2.1
      (((X p).1 ⟨blockProjL N p.1.1 p.1.2.1 f, blockProjL_mem N p.1.1 p.1.2.1 f⟩ : ZMod N → ℂ)) = 0
    by_cases h2 : p.2 = b₀'
    · have h1 : b₀ ≠ p.1 := fun h1 => hp (Prod.ext h1.symm h2)
      have hz : ((X p).1 ⟨blockProjL N p.1.1 p.1.2.1 f, blockProjL_mem N p.1.1 p.1.2.1 f⟩ : ZMod N → ℂ) = 0 :=
        linearMap_apply_eq_zero _ _ (blockProj_eq_zero_of_mem_idx N h1 hf)
      rw [hz, ← blockProjL_apply, map_zero]
    · exact blockProj_eq_zero_of_mem_idx N h2
        ((X p).1 ⟨blockProjL N p.1.1 p.1.2.1 f, blockProjL_mem N p.1.1 p.1.2.1 f⟩).2
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **3c.** 組み立ててから成分に分けると元の族。 -/
theorem commToFamily_comp_familyToComm (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    (commToFamily N).comp (familyToComm N) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  funext p
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact commBlock_commSum N X p.1 p.2 f.2

/-- **3d.** 成分に分けてから組み立てると元の T。 -/
theorem familyToComm_comp_commToFamily (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    (familyToComm N).comp (commToFamily N) = LinearMap.id := by
  apply LinearMap.ext
  intro T
  apply Subtype.ext
  apply LinearMap.ext
  intro g
  exact commSum_commBlock N T.2 g

/-- **3e. 線形同型** A′ ≅ Π_{(b,b′)} Hom_A(V_b, V_b′)。 -/
noncomputable def commEquiv (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    fullComm N ≃ₗ[ℂ] ((p : BlockIdx N × BlockIdx N) → blockHom N p.1.1 p.2.1 p.1.2.1 p.2.2.1) :=
  LinearEquiv.ofLinearMap (commToFamily N) (familyToComm N) (commToFamily_comp_familyToComm N)
    (familyToComm_comp_commToFamily N)

/-! ### 4. 次元 -/

/-- Hom_A(V_b, V_b′) は自由加群（ℂ 上のベクトル空間。加法群の構造は線形写像の空間の部分空間として明示する）。 -/
instance blockHom_free (N c c' : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') :
    Module.Free ℂ (blockHom N c c' χ χ') :=
  @Module.Free.of_divisionRing ℂ (blockHom N c c' χ χ') _
    (@Submodule.addCommGroup ℂ _ _ LinearMap.addCommGroup LinearMap.module (blockHom N c c' χ χ'))
    (Submodule.module _)

/-- **4a.** dim A′ = Σ_{(b,b′)} dim Hom_A(V_b, V_b′)。 -/
theorem finrank_fullComm_eq_sum_finrank (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    Module.finrank ℂ (fullComm N) =
      ∑ p : BlockIdx N × BlockIdx N, Module.finrank ℂ (blockHom N p.1.1 p.2.1 p.1.2.1 p.2.2.1) := by
  rw [(commEquiv N).finrank_eq, Module.finrank_pi_fintype ℂ]

/-- **4b.** dim A′ = Σ_{(b,b′)} [c_b = c_b′]·π(c_b)。 -/
theorem finrank_fullComm_eq_sum (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    Module.finrank ℂ (fullComm N) = ∑ p : BlockIdx N × BlockIdx N,
      if (p.1.1 : ℕ) = p.2.1 then
        ∏ q ∈ (Nat.gcd p.1.1 (N / p.1.1)).primeFactors, ((N / p.1.1).factorization q + 1) else 0 := by
  rw [finrank_fullComm_eq_sum_finrank]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact finrank_blockHom_eq_ite N p.1.1 p.2.1 (Nat.dvd_of_mem_divisors p.1.1.2) (Nat.dvd_of_mem_divisors p.2.1.2)
    p.1.2.1 p.2.2.1 p.1.2.2 p.2.2.2

/-- **4c.** ブロックの番号の上の和：Σ_b g(c_b) = Σ_{c ∣ N} m(c)·g(c)（m(c) = 法 c の原始指標の数）。 -/
theorem sum_blockIdx (N : ℕ) [∀ c : N.divisors, Fintype {χ : DirichletCharacter ℂ c // χ.IsPrimitive}]
    (g : ℕ → ℕ) :
    ∑ b : BlockIdx N, g b.1 = ∑ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} * g c := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Finset.sum_coe_sort N.divisors]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Nat.card_eq_fintype_card]

/-- **4d. 空間全体の可換子の次元**：dim A′ = Σ_{c ∣ N} m(c)²·Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)
（m(c) = 法 c の原始指標の数。Part 214 で数値だけだった式）。 -/
theorem finrank_fullComm (N : ℕ) [NeZero N] :
    Module.finrank ℂ (fullComm N) = ∑ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} ^ 2 *
      ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1) := by
  classical
  have inner : ∀ b : BlockIdx N, (∑ b' : BlockIdx N, if (b.1 : ℕ) = b'.1 then
      ∏ q ∈ (Nat.gcd b.1 (N / b.1)).primeFactors, ((N / b.1).factorization q + 1) else 0) =
      Nat.card {χ : DirichletCharacter ℂ b.1 // χ.IsPrimitive} *
        ∏ q ∈ (Nat.gcd b.1 (N / b.1)).primeFactors, ((N / b.1).factorization q + 1) := by
    intro b
    refine (sum_blockIdx N (fun c => if (b.1 : ℕ) = c then
      ∏ q ∈ (Nat.gcd b.1 (N / b.1)).primeFactors, ((N / b.1).factorization q + 1) else 0)).trans ?_
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left b.1.2]
  calc Module.finrank ℂ (fullComm N)
      = ∑ b : BlockIdx N, ∑ b' : BlockIdx N, (if (b.1 : ℕ) = b'.1 then
          ∏ q ∈ (Nat.gcd b.1 (N / b.1)).primeFactors, ((N / b.1).factorization q + 1) else 0) := by
        rw [finrank_fullComm_eq_sum N, Fintype.sum_prod_type]
    _ = ∑ b : BlockIdx N, Nat.card {χ : DirichletCharacter ℂ b.1 // χ.IsPrimitive} *
          ∏ q ∈ (Nat.gcd b.1 (N / b.1)).primeFactors, ((N / b.1).factorization q + 1) :=
        Finset.sum_congr rfl (fun b _ => inner b)
    _ = ∑ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} *
          (Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} *
            ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1)) :=
        sum_blockIdx N (fun c => Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} *
          ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1))
    _ = _ := Finset.sum_congr rfl (fun c _ => by ring)

/-! ### 5. A′ は A の中心化環 -/

/-- **5a.** 空間全体は殻の射影で閉じる。 -/
theorem top_shellInvariant (N : ℕ) [NeZero N] : ShellInvariant (⊤ : Submodule ℂ (ZMod N → ℂ)) :=
  fun _ _ _ => ⟨Submodule.mem_top, Submodule.mem_top⟩

/-- **5b.** A′ は A の中心化環：T ∈ A′ ⇔ A のすべての元 S と T S = S T。 -/
theorem mem_fullComm_iff_commute (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ fullComm N ↔ ∀ S ∈ shellAlg N, Commute T S := by
  constructor
  · intro hT S hS
    have h := commute_shellAlg_on N (top_shellInvariant N) T (fun s f _ => ((mem_fullComm N T).mp hT s f).1)
      (fun s f _ => ((mem_fullComm N T).mp hT s f).2) hS
    apply LinearMap.ext
    intro f
    exact h f Submodule.mem_top
  · intro h
    rw [mem_fullComm]
    intro s f
    have hE : PAG.Part15.convL (geps N s) ∈ shellAlg N := Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)
    have hD : LinearMap.mulLeft ℂ (dind N s) ∈ shellAlg N := Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)
    exact ⟨LinearMap.congr_fun (h _ hE).eq f, LinearMap.congr_fun (h _ hD).eq f⟩

/-! ### 6. 単数倍 U_a とも可換な変換 -/

/-- 単数倍 U_a（a は法 N の単数、Part 214 の dil）とすべて可換な線形変換。 -/
noncomputable def dilCommute (N : ℕ) [NeZero N] : Submodule ℂ (Module.End ℂ (ZMod N → ℂ)) where
  carrier := {T | ∀ (a : (ZMod N)ˣ) (f : ZMod N → ℂ), T (dil a f) = dil a (T f)}
  add_mem' := by
    intro T₁ T₂ h₁ h₂
    simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
    intro a f
    rw [LinearMap.add_apply, LinearMap.add_apply, h₁ a f, h₂ a f, map_add]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    intro a f
    rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  smul_mem' := by
    intro r T hT
    simp only [Set.mem_ofPred_eq] at hT ⊢
    intro a f
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hT a f, map_smul]

/-- **6a.** 判定。 -/
theorem mem_dilCommute (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ dilCommute N ↔ ∀ (a : (ZMod N)ˣ) (f : ZMod N → ℂ), T (dil a f) = dil a (T f) := Iff.rfl

/-- E_s・D_s と U_a のすべてと可換な線形変換：A′ ∩ (U_a と可換)。 -/
noncomputable def dilComm (N : ℕ) [NeZero N] : Submodule ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  fullComm N ⊓ dilCommute N

/-- **6b.** 判定。 -/
theorem mem_dilComm (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ dilComm N ↔ T ∈ fullComm N ∧ T ∈ dilCommute N := Submodule.mem_inf

/-- **6c.** Y ∈ Hom(V_b, V_b)（同じブロックの間の線形写像）の延長 f ↦ Y(P_b f) は U_a と可換
（U_a は V_b の上でスカラー χ_N(a)）。 -/
theorem blockHomExt_mem_dilCommute (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (Y : blockSpan N c χ →ₗ[ℂ] blockSpan N c χ) : blockHomExt N c c χ χ Y ∈ dilCommute N := by
  rw [mem_dilCommute]
  intro a g
  have e : (⟨blockProjL N c χ (dil a g), blockProjL_mem N c χ _⟩ : blockSpan N c χ) =
      liftc χ N (a : ZMod N) • ⟨blockProjL N c χ g, blockProjL_mem N c χ g⟩ := by
    apply Subtype.ext
    show blockProj N c χ (dil a g) = liftc χ N (a : ZMod N) • blockProj N c χ g
    rw [blockProj_dil N c hcN χ hχ, dil_blockProj]
  calc blockHomExt N c c χ χ Y (dil a g)
      = (Y ⟨blockProjL N c χ (dil a g), blockProjL_mem N c χ _⟩ : ZMod N → ℂ) := rfl
    _ = liftc χ N (a : ZMod N) • (Y ⟨blockProjL N c χ g, blockProjL_mem N c χ g⟩ : ZMod N → ℂ) := by
        rw [e, map_smul, Submodule.coe_smul]
    _ = dil a (Y ⟨blockProjL N c χ g, blockProjL_mem N c χ g⟩ : ZMod N → ℂ) :=
        (dil_of_mem_span N c χ a (Y ⟨blockProjL N c χ g, blockProjL_mem N c χ g⟩).2).symm
    _ = dil a (blockHomExt N c c χ χ Y g) := rfl

/-- 対角の成分の族 (Y_b) を組み立てたもの：Σ_b (f ↦ Y_b(P_b f))。 -/
noncomputable def diagSum (N : ℕ) [NeZero N] [Fintype (BlockIdx N)]
    (Y : (b : BlockIdx N) → blockHom N b.1 b.1 b.2.1 b.2.1) : Module.End ℂ (ZMod N → ℂ) :=
  ∑ b : BlockIdx N, blockHomExt N b.1 b.1 b.2.1 b.2.1 (Y b).1

/-- **6d.** 組み立てたものは A′ に入り、U_a と可換。 -/
theorem diagSum_mem (N : ℕ) [NeZero N] [Fintype (BlockIdx N)]
    (Y : (b : BlockIdx N) → blockHom N b.1 b.1 b.2.1 b.2.1) : diagSum N Y ∈ dilComm N :=
  (mem_dilComm N _).mpr ⟨Submodule.sum_mem _ (fun b _ => blockHomExt_mem_fullComm N b.1 b.1
    (Nat.dvd_of_mem_divisors b.1.2) b.2.1 b.2.1 b.2.2 (Y b).2),
    Submodule.sum_mem _ (fun b _ => blockHomExt_mem_dilCommute N b.1 (Nat.dvd_of_mem_divisors b.1.2) b.2.1 b.2.2
      (Y b).1)⟩

/-- A′ ∩ (U_a と可換) → Π_b Hom_A(V_b, V_b)：T ↦ (P_b∘T|_{V_b})。 -/
noncomputable def dilCommToFamily (N : ℕ) [NeZero N] :
    dilComm N →ₗ[ℂ] ((b : BlockIdx N) → blockHom N b.1 b.1 b.2.1 b.2.1) where
  toFun T b := ⟨commBlock N b b T, commBlock_mem N b b ((mem_dilComm N T).mp T.2).1⟩
  map_add' T₁ T₂ := by
    funext b
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    show blockProjL N b.1 b.2.1 (((T₁ + T₂ : dilComm N) : Module.End ℂ (ZMod N → ℂ)) f) =
      blockProjL N b.1 b.2.1 ((T₁ : Module.End ℂ (ZMod N → ℂ)) f) +
        blockProjL N b.1 b.2.1 ((T₂ : Module.End ℂ (ZMod N → ℂ)) f)
    rw [Submodule.coe_add, LinearMap.add_apply, map_add]
  map_smul' r T := by
    funext b
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    show blockProjL N b.1 b.2.1 (((r • T : dilComm N) : Module.End ℂ (ZMod N → ℂ)) f) =
      r • blockProjL N b.1 b.2.1 ((T : Module.End ℂ (ZMod N → ℂ)) f)
    rw [Submodule.coe_smul, LinearMap.smul_apply, map_smul]

/-- Π_b Hom_A(V_b, V_b) → A′ ∩ (U_a と可換)：(Y_b) ↦ Σ_b Y_b∘P_b。 -/
noncomputable def familyToDilComm (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    ((b : BlockIdx N) → blockHom N b.1 b.1 b.2.1 b.2.1) →ₗ[ℂ] dilComm N where
  toFun Y := ⟨diagSum N Y, diagSum_mem N Y⟩
  map_add' Y₁ Y₂ := by
    apply Subtype.ext
    show diagSum N (Y₁ + Y₂) = diagSum N Y₁ + diagSum N Y₂
    unfold diagSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    apply LinearMap.ext
    intro g
    rfl
  map_smul' r Y := by
    apply Subtype.ext
    show diagSum N (r • Y) = r • diagSum N Y
    unfold diagSum
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    apply LinearMap.ext
    intro g
    rfl

/-- **6e.** U_a とも可換な T を対角の成分に分けて組み立て直すと T：Σ_b P_b (T (P_b g)) = T g
（T は P_b と可換：Part 214 の `comm_blockProj`）。 -/
theorem diagSum_commBlock (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] {T : Module.End ℂ (ZMod N → ℂ)}
    (hT : T ∈ dilComm N) (g : ZMod N → ℂ) :
    diagSum N (fun b => ⟨commBlock N b b T, commBlock_mem N b b ((mem_dilComm N T).mp hT).1⟩) g = T g := by
  have hTd := ((mem_dilComm N T).mp hT).2
  unfold diagSum
  rw [LinearMap.sum_apply]
  calc ∑ b : BlockIdx N, blockHomExt N b.1 b.1 b.2.1 b.2.1 (commBlock N b b T) g
      = ∑ b : BlockIdx N, blockProj N b.1 b.2.1 (T (blockProj N b.1 b.2.1 g)) := rfl
    _ = ∑ b : BlockIdx N, blockProj N b.1 b.2.1 (T g) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [comm_blockProj N b.1 (Nat.dvd_of_mem_divisors b.1.2) b.2.1 b.2.2 T ((mem_dilCommute N T).mp hTd) g,
          blockProj_blockProj N b.1 (Nat.dvd_of_mem_divisors b.1.2) b.2.1 b.2.2]
    _ = T g := sum_blockProj N (T g)

/-- **6f.** 対角の族を組み立ててから b₀ 成分をとると Y_{b₀}：f ∈ V_{b₀} なら P_{b₀}(Σ_b Y_b(P_b f)) = Y_{b₀} f。 -/
theorem commBlock_diagSum (N : ℕ) [NeZero N] [Fintype (BlockIdx N)]
    (Y : (b : BlockIdx N) → blockHom N b.1 b.1 b.2.1 b.2.1) (b₀ : BlockIdx N) {f : ZMod N → ℂ}
    (hf : f ∈ blockSpan N b₀.1 b₀.2.1) :
    blockProj N b₀.1 b₀.2.1 (diagSum N Y f) = ((Y b₀).1 ⟨f, hf⟩ : ZMod N → ℂ) := by
  have hb₀ : (b₀.1 : ℕ) ∣ N := Nat.dvd_of_mem_divisors b₀.1.2
  unfold diagSum
  rw [LinearMap.sum_apply, ← blockProjL_apply, map_sum, Finset.sum_eq_single b₀]
  · show blockProj N b₀.1 b₀.2.1
      (((Y b₀).1 ⟨blockProjL N b₀.1 b₀.2.1 f, blockProjL_mem N b₀.1 b₀.2.1 f⟩ : ZMod N → ℂ)) = _
    have hy := ((Y b₀).1 ⟨blockProjL N b₀.1 b₀.2.1 f, blockProjL_mem N b₀.1 b₀.2.1 f⟩).2
    rw [blockProj_of_mem N b₀.1 hb₀ b₀.2.1 b₀.2.2 hy]
    exact linearMap_apply_congr _ _ _ (blockProj_of_mem N b₀.1 hb₀ b₀.2.1 b₀.2.2 hf)
  · intro b _ hb
    show blockProj N b₀.1 b₀.2.1
      (((Y b).1 ⟨blockProjL N b.1 b.2.1 f, blockProjL_mem N b.1 b.2.1 f⟩ : ZMod N → ℂ)) = 0
    have hz : ((Y b).1 ⟨blockProjL N b.1 b.2.1 f, blockProjL_mem N b.1 b.2.1 f⟩ : ZMod N → ℂ) = 0 :=
      linearMap_apply_eq_zero _ _ (blockProj_eq_zero_of_mem_idx N (Ne.symm hb) hf)
    rw [hz, ← blockProjL_apply, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **6g.** 組み立ててから成分に分けると元の族。 -/
theorem dilCommToFamily_comp_familyToDilComm (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    (dilCommToFamily N).comp (familyToDilComm N) = LinearMap.id := by
  apply LinearMap.ext
  intro Y
  funext b
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact commBlock_diagSum N Y b f.2

/-- **6h.** 成分に分けてから組み立てると元の T。 -/
theorem familyToDilComm_comp_dilCommToFamily (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    (familyToDilComm N).comp (dilCommToFamily N) = LinearMap.id := by
  apply LinearMap.ext
  intro T
  apply Subtype.ext
  apply LinearMap.ext
  intro g
  exact diagSum_commBlock N T.2 g

/-- **6i. 線形同型** A′ ∩ (U_a と可換) ≅ Π_b Hom_A(V_b, V_b)。 -/
noncomputable def dilCommEquiv (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    dilComm N ≃ₗ[ℂ] ((b : BlockIdx N) → blockHom N b.1 b.1 b.2.1 b.2.1) :=
  LinearEquiv.ofLinearMap (dilCommToFamily N) (familyToDilComm N) (dilCommToFamily_comp_familyToDilComm N)
    (familyToDilComm_comp_dilCommToFamily N)

/-- **6j.** dim (A′ ∩ (U_a と可換)) = Σ_b π(c_b)。 -/
theorem finrank_dilComm_eq_sum (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    Module.finrank ℂ (dilComm N) = ∑ b : BlockIdx N,
      ∏ q ∈ (Nat.gcd b.1 (N / b.1)).primeFactors, ((N / b.1).factorization q + 1) := by
  rw [(dilCommEquiv N).finrank_eq, Module.finrank_pi_fintype ℂ]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [finrank_blockHom_eq_ite N b.1 b.1 (Nat.dvd_of_mem_divisors b.1.2) (Nat.dvd_of_mem_divisors b.1.2) b.2.1 b.2.1
    b.2.2 b.2.2, ite_eq_left rfl]

/-- **6k. 単数倍とも可換な変換の次元**：dim (A′ ∩ (U_a と可換)) = Σ_{c ∣ N} m(c)·Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)
（既約成分の総数。Part 214 で数値だけだった式）。 -/
theorem finrank_dilComm (N : ℕ) [NeZero N] :
    Module.finrank ℂ (dilComm N) = ∑ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} *
      ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1) := by
  classical
  rw [finrank_dilComm_eq_sum N]
  exact sum_blockIdx N (fun c => ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1))

end PAG.Part224

#print axioms PAG.Part224.neZero_divisors
#print axioms PAG.Part224.sigma_ne_of_ne
#print axioms PAG.Part224.blockProj_eq_zero_of_mem
#print axioms PAG.Part224.blockProj_eq_zero_of_mem_idx
#print axioms PAG.Part224.sum_blockProj
#print axioms PAG.Part224.linearMap_apply_congr
#print axioms PAG.Part224.linearMap_apply_eq_zero
#print axioms PAG.Part224.fullComm
#print axioms PAG.Part224.mem_fullComm
#print axioms PAG.Part224.commBlock
#print axioms PAG.Part224.commBlock_apply
#print axioms PAG.Part224.commBlock_mem
#print axioms PAG.Part224.blockHomExt_apply_proj
#print axioms PAG.Part224.blockHomExt_mem_fullComm
#print axioms PAG.Part224.commSum
#print axioms PAG.Part224.commSum_mem
#print axioms PAG.Part224.commToFamily
#print axioms PAG.Part224.familyToComm
#print axioms PAG.Part224.commSum_commBlock
#print axioms PAG.Part224.commBlock_commSum
#print axioms PAG.Part224.commToFamily_comp_familyToComm
#print axioms PAG.Part224.familyToComm_comp_commToFamily
#print axioms PAG.Part224.commEquiv
#print axioms PAG.Part224.blockHom_free
#print axioms PAG.Part224.finrank_fullComm_eq_sum_finrank
#print axioms PAG.Part224.finrank_fullComm_eq_sum
#print axioms PAG.Part224.sum_blockIdx
#print axioms PAG.Part224.finrank_fullComm
#print axioms PAG.Part224.top_shellInvariant
#print axioms PAG.Part224.mem_fullComm_iff_commute
#print axioms PAG.Part224.dilCommute
#print axioms PAG.Part224.mem_dilCommute
#print axioms PAG.Part224.dilComm
#print axioms PAG.Part224.mem_dilComm
#print axioms PAG.Part224.blockHomExt_mem_dilCommute
#print axioms PAG.Part224.diagSum
#print axioms PAG.Part224.diagSum_mem
#print axioms PAG.Part224.dilCommToFamily
#print axioms PAG.Part224.familyToDilComm
#print axioms PAG.Part224.diagSum_commBlock
#print axioms PAG.Part224.commBlock_diagSum
#print axioms PAG.Part224.dilCommToFamily_comp_familyToDilComm
#print axioms PAG.Part224.familyToDilComm_comp_dilCommToFamily
#print axioms PAG.Part224.dilCommEquiv
#print axioms PAG.Part224.finrank_dilComm_eq_sum
#print axioms PAG.Part224.finrank_dilComm
