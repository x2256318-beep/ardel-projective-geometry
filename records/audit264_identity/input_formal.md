# 独立照合の入力（恒等の法則の 3 定理、PAG264。形式文と定義だけ）

## A. 照合の対象（PAG264.lean の 3 定理。docstring とコメントを除いた形式文と証明。節の変数宣言を含む）

```lean
section uniq

variable {N M : ℕ} [NeZero N] [NeZero M]

theorem fsum_self (g : ZMod N → ℂ) : fsum (dvd_refl N) g = g := by
  funext x
  simp [fsum, Finset.sum_filter]

theorem cornerOp_self (S : Module.End ℂ (ZMod N → ℂ)) : cornerOp (dvd_refl N) S = S := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  apply LinearMap.ext; intro g
  rw [cornerOp_apply, fsum_self, PAG.Part263.pull_self, div_self hN, one_smul]

theorem cornerHom_self : cornerHom (dvd_refl N) = NonUnitalAlgHom.id ℂ (shellAlg N) := by
  apply NonUnitalAlgHom.ext; intro S
  apply Subtype.ext
  exact cornerOp_self (S : Module.End ℂ (ZMod N → ℂ))
```

## B. 使う定義と補題の文

### B-1. PAG264 の定義（fsum、pullLin、fsumLin、cornerOp、cornerOp_apply）

```lean
namespace PAG.Part264

open PAG.Part201 PAG.Part205 PAG.Part206 PAG.Part218 PAG.Part232

section general

variable {N M : ℕ} [NeZero N] [NeZero M]

noncomputable def fsum (h : N ∣ M) (g : ZMod M → ℂ) : ZMod N → ℂ :=
  fun x => ∑ y ∈ univ.filter (fun y : ZMod M => ZMod.castHom h (ZMod N) y = x), g y

omit [NeZero N] in
theorem fsum_add (h : N ∣ M) (g g' : ZMod M → ℂ) : fsum h (g + g') = fsum h g + fsum h g' := by
  funext x; simp only [fsum, Pi.add_apply, sum_add_distrib]

omit [NeZero N] in
theorem fsum_smul (h : N ∣ M) (c : ℂ) (g : ZMod M → ℂ) : fsum h (c • g) = c • fsum h g := by
  funext x; simp only [fsum, Pi.smul_apply, smul_eq_mul, mul_sum]

noncomputable def pullLin (h : N ∣ M) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod M → ℂ) where
  toFun := pull h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def fsumLin (h : N ∣ M) : (ZMod M → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun := fsum h
  map_add' := fsum_add h
  map_smul' := fsum_smul h


noncomputable def cornerOp (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) : Module.End ℂ (ZMod M → ℂ) :=
  ((N : ℂ) / M) • (pullLin h ∘ₗ S ∘ₗ fsumLin h)

omit [NeZero N] in
theorem cornerOp_apply (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) (g : ZMod M → ℂ) :
    cornerOp h S g = ((N : ℂ) / M) • pull h (S (fsum h g)) := rfl
```

### B-2. PAG264 の cornerHom と cornerHom_coe（cornerOp_mem・cornerOp_smul などの補題の文は省略）

```lean
noncomputable def cornerHom (h : N ∣ M) : shellAlg N →ₙₐ[ℂ] shellAlg M where
  toFun S := ⟨cornerOp h S, cornerOp_mem h S.2⟩
  map_smul' c S := Subtype.ext (show cornerOp h (c • (S : Module.End ℂ (ZMod N → ℂ))) = c • cornerOp h S from
    cornerOp_smul h c S)
  map_zero' := Subtype.ext (cornerOp_zero h)
  map_add' S T := Subtype.ext (cornerOp_add h S T)
  map_mul' S T := Subtype.ext (cornerOp_mul h S T)

theorem cornerHom_coe (h : N ∣ M) (S : shellAlg N) :
    ((cornerHom h S : shellAlg M) : Module.End ℂ (ZMod M → ℂ)) = cornerOp h S := rfl
```

### B-3. PAG201 の pull（PAG.Part201.pull）

```lean
noncomputable def pull {N N' : ℕ} (h : N ∣ N') (f : ZMod N → ℂ) : ZMod N' → ℂ :=
  f ∘ (ZMod.castHom h (ZMod N)).toAddMonoidHom
```

### B-4. PAG263 の pull_self（文だけ。PAG263 の変数宣言を添える）

```lean
variable {N M L : ℕ} [NeZero N] [NeZero M] [NeZero L]

theorem pull_self (f : ZMod N → ℂ) : PAG.Part201.pull (dvd_refl N) f = f   -- 証明は省略
```

### B-5. PAG218 の shellAlg（geps・dind・convL は殻の指示関数と畳み込みの定義で、ここでは省略）

```lean
noncomputable def shellAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪
    Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)))
```
