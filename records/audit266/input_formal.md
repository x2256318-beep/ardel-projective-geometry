# 独立照合の入力（Part 262、PAG266.lean。形式文と定義だけ）

## A. 照合の対象（PAG266.lean の全文から、docstring とコメントを除いたもの。証明を含む）

```lean
import PAG265
import PAG25
import PAG15
import PAG29

open Finset

namespace PAG.Part266

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

open PAG.Part25 (Jhat)
open PAG.Part256 (rootNum)

theorem conj_Jhat_eq_gauss (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    starRingEnd ℂ (Jhat χ₁ χ₂)
      = (Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℂ) * gaussSum (χ₁ * χ₂) ZMod.stdAddChar
          / (gaussSum χ₁ ZMod.stdAddChar * gaussSum χ₂ ZMod.stdAddChar) := by
  have hq : (0 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.out.pos _
  have hs : ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have hss : ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) ^ 2 = ((p ^ (n + 1) : ℕ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq.le]; push_cast; rfl
  have hN := PAG.Part25.normSq_J χ₁ χ₂ h₁ h₂ h₁₂
  have hJ : PAG.Part7.J χ₁ χ₂ ≠ 0 := by
    intro h; rw [h, map_zero] at hN; exact hq.ne' hN.symm
  have hmc : PAG.Part7.J χ₁ χ₂ * starRingEnd ℂ (PAG.Part7.J χ₁ χ₂) = ((p ^ (n + 1) : ℕ) : ℂ) := by
    rw [Complex.mul_conj, hN]; norm_cast
  have h1 := PAG.Part16.gaussSum_ne_zero h₁
  have h2 := PAG.Part16.gaussSum_ne_zero h₂
  have h12 := PAG.Part16.gaussSum_ne_zero h₁₂
  have hr := PAG.Part15.gauss_ratio_eq_jacobi χ₁ χ₂ h₁₂ ZMod.stdAddChar h12
  have hcJ : starRingEnd ℂ (PAG.Part7.J χ₁ χ₂)
      = ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) ^ 2 / PAG.Part7.J χ₁ χ₂ := by
    rw [hss, ← hmc]; field_simp
  rw [Jhat, map_div₀, Complex.conj_ofReal, hcJ, ← hr]
  field_simp

open Classical in
theorem conj_Jhat_eq_rootNum (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    starRingEnd ℂ (Jhat χ₁ χ₂)
      = (if χ₁.Even ∨ χ₂.Even then (1 : ℂ) else -1)
          * (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) := by
  rw [conj_Jhat_eq_gauss χ₁ χ₂ h₁ h₂ h₁₂]
  have hq : (0 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.out.pos _
  have hs : ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have h1 := PAG.Part16.gaussSum_ne_zero h₁
  have h2 := PAG.Part16.gaussSum_ne_zero h₂
  have h12 := PAG.Part16.gaussSum_ne_zero h₁₂
  have hodd : ∀ χ : DirichletCharacter ℂ (p ^ (n + 1)), χ.Odd → ¬ χ.Even := by
    intro χ ho he
    have e1 : χ (-1) = 1 := he
    have e2 : χ (-1) = -1 := ho
    rw [e1] at e2; norm_num at e2
  unfold rootNum
  rcases χ₁.even_or_odd with e₁ | e₁ <;> rcases χ₂.even_or_odd with e₂ | e₂
  · have e : (χ₁ * χ₂).Even := by
      show (χ₁ * χ₂) (-1) = 1
      rw [MulChar.mul_apply, show χ₁ (-1) = 1 from e₁, show χ₂ (-1) = 1 from e₂, one_mul]
    simp only [e₁, e₂, e, ↓reduceIte, true_or]
    field_simp
  · have e : ¬ (χ₁ * χ₂).Even := hodd _ (by
      show (χ₁ * χ₂) (-1) = -1
      rw [MulChar.mul_apply, show χ₁ (-1) = 1 from e₁, show χ₂ (-1) = -1 from e₂, one_mul])
    simp only [e₁, hodd _ e₂, e, true_or, ↓reduceIte]
    field_simp
  · have e : ¬ (χ₁ * χ₂).Even := hodd _ (by
      show (χ₁ * χ₂) (-1) = -1
      rw [MulChar.mul_apply, show χ₁ (-1) = -1 from e₁, show χ₂ (-1) = 1 from e₂, mul_one])
    simp only [hodd _ e₁, e₂, e, or_true, ↓reduceIte]
    field_simp
  · have e : (χ₁ * χ₂).Even := by
      show (χ₁ * χ₂) (-1) = 1
      rw [MulChar.mul_apply, show χ₁ (-1) = -1 from e₁, show χ₂ (-1) = -1 from e₂]; norm_num
    simp only [hodd _ e₁, hodd _ e₂, e, or_self, ↓reduceIte]
    field_simp
    rw [Complex.I_sq]; ring

theorem conj_Jhat_sq_eq_rootNum (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2
      = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2 := by
  rw [conj_Jhat_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]
  split_ifs <;> ring

theorem equator_intertwine_rootNum (K : ℕ) (h : 0 + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    PAG.Part23.BN (PAG.Part23.kS K 0 (n + 1) h χ₁) (PAG.Part23.kS K 0 (n + 1) h χ₂)
      = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2
          • PAG.Part23.BS (PAG.Part23.kS K 0 (n + 1) h χ₁) (PAG.Part23.kS K 0 (n + 1) h χ₂) := by
  rw [PAG.Part25.equator_intertwine_hat K h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]

theorem equator_intertwine_proj_rootNum (K : ℕ) (hK : 1 ≤ K) (h : 0 + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    PAG.Part28.BNproj K hK (PAG.Part29.ketS_proj K hK 0 (n + 1) h χ₁) (PAG.Part29.ketS_proj K hK 0 (n + 1) h χ₂)
      = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2
          • PAG.Part28.BSproj K hK (PAG.Part29.ketS_proj K hK 0 (n + 1) h χ₁) (PAG.Part29.ketS_proj K hK 0 (n + 1) h χ₂) := by
  rw [PAG.Part29.equator_intertwine_proj K hK h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]

#print axioms conj_Jhat_eq_gauss
#print axioms conj_Jhat_eq_rootNum
#print axioms conj_Jhat_sq_eq_rootNum
#print axioms equator_intertwine_rootNum
#print axioms equator_intertwine_proj_rootNum

end PAG.Part266
```

## B. 使う定義と補題の文（docstring を含む宣言の抜き出し。補題は文だけ）

### PAG.Part7.J（PAG7.lean）
```lean
/-- ヤコビ和 J(χ₁,χ₂) = Σ_x χ₁(x) χ₂(1 − x)。 -/
noncomputable def J (χ₁ χ₂ : MulChar (ZMod N) ℂ) : ℂ := ∑ x, χ₁ x * χ₂ (1 - x)
```

### PAG.Part15.conv（PAG15.lean）
```lean
/-- 加法畳み込み (f ⋆ g)(x) = Σ_y f(y) g(x − y)。 -/
def conv (f g : G → K) : G → K := fun x => ∑ y, f y * g (x - y)
```

### PAG.Part15.gauss_ratio_eq_jacobi（PAG15.lean）
```lean
/-- ガウス和比はヤコビ和: χ₁χ₂ 原始的・τ(χ₁χ₂) ≠ 0 ⇒ τ₁τ₂/τ₁₂ = J(χ₁, χ₂)。 -/
theorem gauss_ratio_eq_jacobi (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hprim : (χ₁ * χ₂).IsPrimitive) (ψ : AddChar (ZMod (p ^ (n + 1))) ℂ)
    (h12 : gaussSum (χ₁ * χ₂) ψ ≠ 0) :
    gaussSum χ₁ ψ * gaussSum χ₂ ψ / gaussSum (χ₁ * χ₂) ψ = PAG.Part7.J χ₁ χ₂ :=
```

### PAG.Part16.gaussSum_ne_zero（PAG16.lean）
```lean
/-- **τ(χ) ≠ 0**（χ 原始的）: 𝓕χ = τ·χ⁻¹(−·) なので τ = 0 なら χ = 0 となり χ(1) = 1 に反する。 -/
theorem gaussSum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar ≠ 0 :=
```

### PAG.Part16.normSq_gaussSum（PAG16.lean）
```lean
/-- **|τ(χ)|² = N**（χ 原始的）。法 p^c なら |τ|² = p^c。 -/
theorem normSq_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ stdAddChar) = N :=
```

### PAG.Part23.BN（PAG23.lean）
```lean
/-- 北の畳み込み B_N := W B_S(W·, W·)。 -/
noncomputable def BN (F G : P1F N) : P1F N := W (BS (W F) (W G))
```

### PAG.Part23.BS（PAG23.lean）
```lean
/-- 南の畳み込み（南チャートで畳み込み、北の内部は 0）。 -/
noncomputable def BS (F G : P1F N) : P1F N := extS (PAG.Part15.conv F.1 G.1)
```

### PAG.Part23.P1F（PAG23.lean）
```lean
/-- P¹ 上の関数（南座標の関数と北座標の関数の組）。 -/
abbrev P1F (N : ℕ) := (ZMod N → ℂ) × (ZMod N → ℂ)
```

### PAG.Part23.W（PAG23.lean）
```lean
/-- 反転 W: [x:1] ↔ [1:x]、関数では南北の入れ替え。 -/
def W (F : P1F N) : P1F N := (F.2, F.1)
```

### PAG.Part23.extN（PAG23.lean）
```lean
/-- 北チャートの関数を P¹ 上へ（南の内部では 0）。 -/
noncomputable def extN (h : ZMod N → ℂ) : P1F N := (fun x => if IsUnit x then h x⁻¹ else 0, h)
```

### PAG.Part23.extS（PAG23.lean）
```lean
/-- 南チャートの関数を P¹ 上へ（北の内部では 0）。 -/
noncomputable def extS (h : ZMod N → ℂ) : P1F N := (h, fun y => if IsUnit y then h y⁻¹ else 0)
```

### PAG.Part23.kS（PAG23.lean）
```lean
/-- 南の殻ケット |w, χ⟩（w ≥ 0）。 -/
noncomputable def kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) : P1F (p ^ K) :=
  extS (ket K w c h χ)
```

### PAG.Part25.Jhat（PAG25.lean）
```lean
/-- 規格化ヤコビ和 Ĵ = J / √p^c。 -/
noncomputable def Jhat (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) : ℂ :=
  PAG.Part7.J χ₁ χ₂ / ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ)
```

### PAG.Part25.equator_intertwine_hat（PAG25.lean）
```lean
/-- **赤道での絡み合い（Ĵ 形）**: B_N(|0,χ₁⟩,|0,χ₂⟩) = conj(Ĵ)² · B_S(|0,χ₁⟩,|0,χ₂⟩)。 -/
theorem equator_intertwine_hat (K : ℕ) (h : 0 + (n + 1) ≤ K) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    BN (kS K 0 (n + 1) h χ₁) (kS K 0 (n + 1) h χ₂)
      = (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2 • BS (kS K 0 (n + 1) h χ₁) (kS K 0 (n + 1) h χ₂) :=
```

### PAG.Part25.normSq_J（PAG25.lean）
```lean
/-- **|J(χ₁,χ₂)|² = p^c**（χ₁, χ₂, χ₁χ₂ 原始的）。τ₁τ₂ = J τ₁₂ と |τ|² = p^c から。 -/
theorem normSq_J (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    Complex.normSq (PAG.Part7.J χ₁ χ₂) = ((p ^ (n + 1) : ℕ) : ℝ) :=
```

### PAG.Part27.ProjLine（PAG27.lean）
```lean
/-- **射影直線** P¹(Z/N)。 -/
def ProjLine (N : ℕ) := Quotient (projSetoid N)
```

### PAG.Part27.Unimod（PAG27.lean）
```lean
/-- 単模ベクトル。 -/
def Unimod (N : ℕ) := {v : ZMod N × ZMod N // ∃ s t : ZMod N, s * v.1 + t * v.2 = 1}
```

### PAG.Part28.BNproj（PAG28.lean）
```lean
/-- ProjLine 上の北の畳み込み。 -/
noncomputable def BNproj (Φ Ψ : ProjLine (p ^ K) → ℂ) : ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm
    ⟨BN (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1, compat_extN _⟩
```

### PAG.Part28.BSproj（PAG28.lean）
```lean
/-- ProjLine 上の南の畳み込み。 -/
noncomputable def BSproj (Φ Ψ : ProjLine (p ^ K) → ℂ) : ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm
    ⟨BS (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1, compat_extS _⟩
```

### PAG.Part29.equator_intertwine_proj（PAG29.lean）
```lean
/-- **赤道での絡み合い（射影直線上）**: B_N^proj = conj(Ĵ)² B_S^proj。 -/
theorem equator_intertwine_proj {n : ℕ} (h : 0 + (n + 1) ≤ K) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    BNproj K hK (ketS_proj K hK 0 (n + 1) h χ₁) (ketS_proj K hK 0 (n + 1) h χ₂)
      = (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2 •
          BSproj K hK (ketS_proj K hK 0 (n + 1) h χ₁) (ketS_proj K hK 0 (n + 1) h χ₂) :=
```

### PAG.Part29.ketS_proj（PAG29.lean）
```lean
/-- 射影直線上の南ケット。 -/
noncomputable def ketS_proj (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm ⟨kS K w c h χ, compat_extS _⟩
```

### PAG.Part256.rootNum（PAG256.lean）
```lean
/-- W(χ) = τ(χ)/(i^a √N)（a = 0 は偶、a = 1 は奇）。χ が原始ならルート数（関数等式との一致は Lean の外）。原始的でない
χ ではルート数ではなく、0 にもなる（法 4 の自明な指標）。
内部照合（2026-11-14）：Part 192（PAG196）の `zN` を Part 194（PAG198）の `gs` で割ったものと同じ値（Lean で確認）。 -/
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))
```

### PAG.Part19.sz（PAG19.lean）
```lean
/-- 殻サイズ |S_u| = p^(K−1−u)(p−1)。 -/
def sz (p K u : ℕ) : ℕ := p ^ (K - 1 - u) * (p - 1)
```

### PAG.Part21.ket（PAG21.lean）
```lean
/-- 殻 u の標準ケット（step30 の `P.ket(u, c, j)` に対応）: |S_u|^(−1/2) ι_{u,*}(χ ∘ π_u)。 -/
noncomputable def ket (K u c : ℕ) (huc : u + c ≤ K) (χ : ZMod (p ^ c) → ℂ) : ZMod (p ^ K) → ℂ :=
  have : NeZero (p ^ (K - u)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  (((Real.sqrt (sz p K u))⁻¹ : ℝ) : ℂ) •
    push (shellEmb (p := p) K u (by omega))
      (χ ∘ (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - u)) (ZMod (p ^ c))).toAddMonoidHom)
```

### PAG.Part27.mk（PAG27.lean）
```lean
/-- 点 [a:b]。 -/
def mk (v : Unimod N) : ProjLine N := Quotient.mk (projSetoid N) v
```

### PAG.Part27.projSetoid（PAG27.lean）
```lean
/-- 単数倍の同値関係。 -/
def projSetoid (N : ℕ) : Setoid (Unimod N) where
  r v w := ∃ u : (ZMod N)ˣ, w.1.1 = u * v.1.1 ∧ w.1.2 = u * v.1.2
  iseqv := {
    refl := fun v => ⟨1, by simp, by simp⟩
    symm := fun {v w} ⟨u, h1, h2⟩ => ⟨u⁻¹, by rw [h1, ← mul_assoc, Units.inv_mul, one_mul],
      by rw [h2, ← mul_assoc, Units.inv_mul, one_mul]⟩
    trans := fun {v w z} ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩ => ⟨u' * u, by rw [h1', h1, Units.val_mul, mul_assoc],
      by rw [h2', h2, Units.val_mul, mul_assoc]⟩ }
```


## C. Mathlib の定義（名前だけ）

- `gaussSum χ ψ` = Σ_{a} χ a * ψ a（Mathlib.NumberTheory.GaussSum）。`ZMod.stdAddChar`：ZMod N の標準の加法指標 x ↦ exp(2πi x.val/N)。
- `DirichletCharacter.Even χ` ：χ (-1) = 1。`DirichletCharacter.Odd χ`：χ (-1) = -1。`DirichletCharacter.IsPrimitive`：導手が法に等しい。
- `starRingEnd ℂ`：複素共役。
