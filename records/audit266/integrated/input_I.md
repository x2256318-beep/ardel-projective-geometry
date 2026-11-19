# 統合照合 I の入力：Part 262（PAG266、短期層）の材料と、尾の台帳 L6（2026-11-20）

照合の対象：§D の散文（Lean の冒頭の説明と docstring、ノート、索引・辞書・xlsx・引き継ぎメモ・台帳の Part 262 の行）と、§F の着手前の文書。§E の差分は再照合の後の直し（台帳 L6）で、照合を受けていない。§A〜§C と §G は根拠。


## §A PAG266.lean の全文（現在の版。docstring と冒頭の説明を含む）

```lean
/-
アーデル射影幾何 — Part 262（PAG266、短期層の小さいノート、2026-11-20）：舞台 P¹ の赤道の絡み合いの係数を 𝔀（`rootNum`）で書く

問いの出所：基礎文書の索引 1.4（舞台は P¹）と 2.4（「射影」の変換）の留保「`JH` は P¹ の上の作用素ではなく、P¹ のモデルと結ぶ Lean の文はない」。
- 推薦案 `pag2_p1_gluing_preregistration.md` §4 を、2026-11-20 06:55 に著者が採用した（「進めてください」）。
- 著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」の読みの材料（読みの地位は変えない）。
- この文書の文に `JH` は現れない。Lean で結んだのは 𝔀（`rootNum`）の値と P¹ の赤道の係数で、留保「`JH` と P¹ のモデルを結ぶ Lean の文はない」はこの文書の後も残る。

記号：
- N = p^(n+1)（p は素数）は指標の法。定理の P¹ のモデルの法は p^K で、N とは別（K > n+1 なら値も違う）。e = stdAddChar、τ(χ) = gaussSum χ e。J = `PAG.Part7.J`（ヤコビ和）、Ĵ = J/√N（`PAG.Part25.Jhat`）。
- 𝔀(χ) = `PAG.Part256.rootNum` χ = τ(χ)/(i^a √N)（偶なら a = 0、奇なら a = 1）。原始指標でルート数であることは Lean の外。
  𝔀 は `rootNum` の docstring で W(χ) と書かれている値。B_N の定義に入る反転 `PAG.Part23.W`（南北の入れ替え）と区別して 𝔀 と書く。
- P¹(ℤ/p^K) の 2 チャートのモデル、南北の畳み込み B_S・B_N、赤道のケット |0, χ⟩ = `PAG.Part23.kS K 0 (n+1) h χ`（Part 19（PAG23））。
- 扱うのは殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ。係数は K によらない。

主な定理（χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標のとき）：
1. conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))（`conj_Jhat_eq_gauss`）。
2. conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))、s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1（`conj_Jhat_eq_rootNum`）。
3. conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²（`conj_Jhat_sq_eq_rootNum`）。
4. n + 1 ≤ K のとき、赤道のケットについて B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)（`equator_intertwine_rootNum`、2 チャートのモデル）。
5. 4 の両辺を `projFunEquiv`（Part 24（PAG28）の ℂ 線形同型：`PAG.Part27.ProjLine (p^K)` 上の関数 ≃ 貼り合わせ条件を満たす組）で移した形（`equator_intertwine_proj_rootNum`、Part 25（PAG29）の `equator_intertwine_proj` から）。
   5 は 4 と同値（`projFun_*` と線形性による手の論証。Lean の文にはしていない）。点 [x:1]・[1:y] での値としての読みは `projEquiv`（Part 23（PAG27））と `ptEquiv`（Part 22（PAG26））による。

読み（Lean の外）：原始指標 χ の成分に、導手 p^(n+1) で計算した 𝔀(χ) を掛ける作用素を U とする（法 p^K の指標として計算すると、K > n+1 では τ = 0 になるため）。
B_S(|0,χ₁⟩, |0,χ₂⟩) が χ₁χ₂ の成分に入ること（この文書の文にはない）と合わせて、4 は赤道のケットの上で B_N(k₁, k₂) = U² B_S(U⁻²k₁, U⁻²k₂) と読める。
この条件を満たす位相は 𝔀 だけではない（少なくとも、単数 u による √χ(u) の分と指標ごとの符号 ±1 の分がある。数値と照合者の手計算、`pag2_p1_gluing_preregistration.md`）。
A1 は導かれない。p = 2（すべての n）と p = 3、n = 0 では原始指標の三つ組がなく、5 つの文は空（独立照合の指摘。p = 2 は Part 26（PAG30）の注意とも合う）。
仮定は必要十分ではない：1〜3 では χ₁χ₂ の原始性は不要に見え、χ₁・χ₂ の原始性が中身を運ぶのは n = 0 だけ（n ≥ 1 では両辺が 0 になる。独立照合の手計算）。
4・5 では χ₁χ₂ の原始性を外すと偽になる（独立照合の反例）。反例は単数でない点（n = 1）にも、単数の点（n = 0、χ₂ = χ̄₁、x = 1）にも出る。
単数の点での比 B_N/B_S は conj(J)/J で、conj(Ĵ)² に等しいのは |J|² = N のとき（Lean の外。再照合者の手計算と数値 `records/audit266/numeric/unit_point_ratio.py`、K = n+1 の場合）。
4・5 は Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換えで、絡み合いの中身はそちらにある（名前空間 `PAG.Part25` は Part 21（PAG25）を指し、Part 25（PAG29）とは別）。

ラベル（見込み、照合の後に確定）：1〜3 は［既知］（積が原始的ならヤコビ和はガウス和の比、|τ|² = N。K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15・3.12。法 m は一般で ℤ/p^(n+1) を覆う（WebFetch の要約で確認））、4・5 は［再導出（小さい）］。新規候補なし。
-/
import PAG265
import PAG25
import PAG15
import PAG29

open Finset

namespace PAG.Part266

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

open PAG.Part25 (Jhat)
open PAG.Part256 (rootNum)

/-- **1. ガウス和による形**：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、conj(Ĵ(χ₁, χ₂)) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))
（N = p^(n+1)、τ(χ) = gaussSum χ e、e = stdAddChar）。
p = 2（すべての n）と p = 3、n = 0 では仮定を満たす指標の組がなく、文は空（独立照合の指摘）。 -/
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
/-- **2. 𝔀 による形（2 乗を外した形）**：χ₁・χ₂・χ₁χ₂ が原始的なら、
conj(Ĵ(χ₁, χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))。符号 s は、χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1
（𝔀 = `PAG.Part256.rootNum`、τ/(i^a √N)）。符号 s は、Ĵ（i^a を含まない）と 𝔀（i^a を含む）の正規化の違いから来る
（加法指標の向きや i^a を (−i)^a に替えても変わらない。独立照合の手計算）。 -/
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

/-- **3. 2 乗の形**：χ₁・χ₂・χ₁χ₂ が原始的なら、conj(Ĵ(χ₁, χ₂))² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²。
2 乗で定理 2 の符号 s は落ちる（4・5 も同じ）。 -/
theorem conj_Jhat_sq_eq_rootNum (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2
      = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2 := by
  rw [conj_Jhat_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]
  split_ifs <;> ring

/-- **4. 赤道の絡み合いの 𝔀 による形**：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標で n + 1 ≤ K なら、
P¹(ℤ/p^K) の 2 チャートのモデルの赤道のケット |0, χ⟩ について、
B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)
（Part 21（PAG25）の `equator_intertwine_hat` と 3 から）。この定理は `equator_intertwine_hat` の係数 conj(Ĵ)² を 3 で書き換えたもので、
絡み合いの中身（単数でない点で両辺が 0 になることを含む）は Part 21（PAG25）にある。 -/
theorem equator_intertwine_rootNum (K : ℕ) (h : 0 + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    PAG.Part23.BN (PAG.Part23.kS K 0 (n + 1) h χ₁) (PAG.Part23.kS K 0 (n + 1) h χ₂)
      = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2
          • PAG.Part23.BS (PAG.Part23.kS K 0 (n + 1) h χ₁) (PAG.Part23.kS K 0 (n + 1) h χ₂) := by
  rw [PAG.Part25.equator_intertwine_hat K h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]

/-- **5. 射影直線の上の関数に移した形**：4 の両辺を `projFunEquiv`（Part 24（PAG28）。`PAG.Part27.ProjLine (p^K)` 上の関数と、
貼り合わせ条件を満たす組との ℂ 線形同型）で移した等式。B_S^proj・B_N^proj は Part 24（PAG28）、ketS_proj は Part 25（PAG29）で、
2 チャートの版をこの同型で移して定義したもの。Part 25（PAG29）の `equator_intertwine_proj` の係数を 3 で書き換えたもの。
5 は 4 と同値（`projFun_*` と線形性による。Lean の文にはしていない）。点 [x:1]・[1:y] での値としての読みは `projEquiv`・`ptEquiv` による。
1 ≤ K は h から出るので、仮定に置かない（独立照合の指摘で外した）。 -/
theorem equator_intertwine_proj_rootNum (K : ℕ) (h : 0 + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    PAG.Part28.BNproj K (by omega) (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₁)
        (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₂)
      = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2
          • PAG.Part28.BSproj K (by omega) (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₁)
            (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₂) := by
  rw [PAG.Part29.equator_intertwine_proj K (by omega) h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]

#print axioms conj_Jhat_eq_gauss
#print axioms conj_Jhat_eq_rootNum
#print axioms conj_Jhat_sq_eq_rootNum
#print axioms equator_intertwine_rootNum
#print axioms equator_intertwine_proj_rootNum

end PAG.Part266
```


## §B ビルドの記録

`lake env lean PAG266.lean` 相当のビルド（2026-11-20 07:36、再照合の後の直しの後）。終了コード 0、出力は次の 5 行だけ（エラー・警告・sorry の行は 0）。

```
'PAG.Part266.conj_Jhat_eq_gauss' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part266.conj_Jhat_eq_rootNum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part266.conj_Jhat_sq_eq_rootNum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part266.equator_intertwine_rootNum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part266.equator_intertwine_proj_rootNum' depends on axioms: [propext, Classical.choice, Quot.sound]
```


## §C 使う定義と補題の文


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

### 追加（独立照合の照合者が入力になかったと申告した定義）

### PAG.Part23.compat_extN（PAG23.lean）
```lean

theorem compat_extN (h : ZMod N → ℂ) : Compat (extN h) :=
```

### PAG.Part23.compat_extS（PAG23.lean）
```lean

theorem compat_extS (h : ZMod N → ℂ) : Compat (extS h) :=
```

### PAG.Part26.compatSub（PAG26.lean）
```lean
/-- 貼り合わせ条件を満たす組の部分空間。 -/
def compatSub (N : ℕ) : Submodule ℂ (P1F N) where
  carrier := {F | Compat F}
  add_mem' := fun {F G} hF hG y hy => by
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, hF y hy, hG y hy]
  zero_mem' := fun y _ => rfl
  smul_mem' := fun a {F} hF y hy => by
    simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, hF y hy]
```

### PAG.Part28.projFunEquiv（PAG28.lean）
```lean
/-- **関数空間の直接同型**: (ProjLine(p^K) → ℂ) ≃ₗ 貼り合わせ条件の部分空間。 -/
noncomputable def projFunEquiv : (ProjLine (p ^ K) → ℂ) ≃ₗ[ℂ] compatSub (p ^ K) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (projEquiv K hK)).trans (ptEquiv (p ^ K))
```

### PAG.Part29.projFun_BNproj（PAG29.lean）
```lean

theorem projFun_BNproj (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    (projFunEquiv K hK (BNproj K hK Φ Ψ)).1 = BN (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1 :=
```

### PAG.Part29.projFun_BSproj（PAG29.lean）
```lean

theorem projFun_BSproj (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    (projFunEquiv K hK (BSproj K hK Φ Ψ)).1 = BS (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1 :=
```

### PAG.Part29.projFun_ketS（PAG29.lean）
```lean

theorem projFun_ketS (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    (projFunEquiv K hK (ketS_proj K hK w c h χ)).1 = kS K w c h χ :=
```

### PAG.Part17.push（PAG17.lean）
```lean
/-- ゼロ拡張（押し出し）ι_* f = Function.extend ι f 0。 -/
noncomputable def push (ι : H →+ G) (f : H → ℂ) : G → ℂ := Function.extend ι f 0
```

### PAG.Part17.shellEmb（PAG17.lean）
```lean
/-- 殻 v への埋め込み ι_v : ZMod p^(K−v) → ZMod p^K、x ↦ p^v x。 -/
noncomputable def shellEmb (K v : ℕ) (hv : v ≤ K) : ZMod (p ^ (K - v)) →+ ZMod (p ^ K) :=
  ZMod.lift (p ^ (K - v)) ⟨(p ^ v : ZMod (p ^ K)) • (Int.castAddHom (ZMod (p ^ K))), by
    simp only [AddMonoidHom.smul_apply, Int.castAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Int.cast_natCast, smul_eq_mul]
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hv, ZMod.natCast_self]⟩
```


### 追加（再照合の照合者が入力になかったと申告した定義）


#### PAG.Part23.P1F（PAG23.lean）

```lean
/-- P¹ 上の関数（南座標の関数と北座標の関数の組）。 -/
abbrev P1F (N : ℕ) := (ZMod N → ℂ) × (ZMod N → ℂ)
```


#### PAG.Part23.Compat（PAG23.lean）

```lean
/-- 貼り合わせ条件: 赤道（単数）上で F_N(y) = F_S(y⁻¹)。 -/
def Compat (F : P1F N) : Prop := ∀ y : ZMod N, IsUnit y → F.2 y = F.1 y⁻¹
```


#### PAG.Part26.Pt（PAG26.lean）

```lean
/-- P¹(Z/N) の点: 南の点 [x:1]（inl x）と北の内部点 [1:y]（inr y、y 非単数）。 -/
abbrev Pt (N : ℕ) := ZMod N ⊕ {y : ZMod N // ¬ IsUnit y}
```


#### PAG.Part26.toP1（PAG26.lean）

```lean
/-- 点の関数 → 2 チャートの組。 -/
noncomputable def toP1 (f : Pt N → ℂ) : P1F N :=
  (fun x => f (Sum.inl x), fun y => if h : IsUnit y then f (Sum.inl y⁻¹) else f (Sum.inr ⟨y, h⟩))
```


#### PAG.Part26.ofP1（PAG26.lean）

```lean
/-- 2 チャートの組 → 点の関数。 -/
def ofP1 (F : P1F N) : Pt N → ℂ
  | Sum.inl x => F.1 x
  | Sum.inr y => F.2 y.1
```


#### PAG.Part26.ptEquiv（PAG26.lean）

```lean
/-- **点モデル ≃ 2 チャートモデル**（線形同型）。 -/
noncomputable def ptEquiv (N : ℕ) : (Pt N → ℂ) ≃ₗ[ℂ] compatSub N where
  toFun f := ⟨toP1 f, compat_toP1 f⟩
  invFun F := ofP1 F.1
  map_add' f g := by
    apply Subtype.ext
    ext y
    · rfl
    · simp only [toP1, Pi.add_apply, Submodule.coe_add, Prod.snd_add]
      split_ifs <;> rfl
  map_smul' a f := by
    apply Subtype.ext
    ext y
    · rfl
    · simp only [toP1, Pi.smul_apply, Submodule.coe_smul, Prod.smul_snd, RingHom.id_apply]
      split_ifs <;> rfl
  left_inv f := ofP1_toP1 f
  right_inv F := Subtype.ext (toP1_ofP1 F.2)
```


#### PAG.Part27.toProj（PAG27.lean）

```lean
/-- 点モデル → 射影直線: [x:1]、[1:y]。 -/
def toProj : Pt (p ^ K) → ProjLine (p ^ K)
  | Sum.inl x => mk ⟨(x, 1), 0, 1, by simp⟩
  | Sum.inr y => mk ⟨(1, y.1), 1, 0, by simp⟩
```


#### PAG.Part27.projEquiv（PAG27.lean）

```lean
/-- **点モデル ≃ 射影直線** Pt(p^K) ≃ P¹(Z/p^K)。 -/
noncomputable def projEquiv : Pt (p ^ K) ≃ ProjLine (p ^ K) where
  toFun := toProj K
  invFun := ofProj K hK
  left_inv := ofProj_toProj K hK
  right_inv := toProj_ofProj K hK
```


#### PAG.Part28.projFun_eq（PAG28.lean）

```lean
/-- 南成分: x ↦ Φ([x:1])。 -/
theorem projFun_eq (Φ : ProjLine (p ^ K) → ℂ) :
    (projFunEquiv K hK Φ).1 = toP1 (Φ ∘ toProj K) := rfl
```


#### PAG.Part28.projFun_south（PAG28.lean）

```lean
theorem projFun_south (Φ : ProjLine (p ^ K) → ℂ) (x : ZMod (p ^ K)) :
    (projFunEquiv K hK Φ).1.1 x = Φ (mk ⟨(x, 1), 0, 1, by simp⟩) := rfl
```


## §D 散文（照合の対象）


### D1 ノート `notes/pag2_pag266_p1_equator_rootnum.md`（全文）

```markdown
# アーデル射影幾何 — Part 262（PAG266、短期層の小さいノート）：舞台 P¹ の赤道の絡み合いの係数を 𝔀（`rootNum`）で書く

（2026-11-20。推薦案 `pag2_p1_gluing_preregistration.md` §4 を、06:55 に著者が採用した。）

## §1 問いの出所

- 基礎文書の索引 1.4（舞台は P¹）と 2.4（「射影」の変換）の留保：`JH` は P¹ の上の作用素ではなく、P¹ のモデルと結ぶ Lean の文がない。
- 著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」の読みの材料。読みの地位は変えない。
- このパートの文に `JH` は現れない。Lean で結んだのは 𝔀（`rootNum`）の値と P¹ の赤道の係数で、留保「`JH` と P¹ のモデルを結ぶ Lean の文はない」はこのパートの後も残る（再照合の指摘）。

## §2 Lean に入った文（PAG266.lean、定理 5、sorry 0・警告 0、#print axioms は標準の 3 つ）

記号：N = p^(n+1)（p は素数）は指標の法。定理の P¹ のモデルの法は p^K で、N とは別（K > n+1 なら値も違う）。τ(χ) = gaussSum χ stdAddChar。J = ヤコビ和 `PAG.Part7.J`、Ĵ = J/√N（`PAG.Part25.Jhat`）。𝔀 = `PAG.Part256.rootNum` = τ/(i^a √N)。𝔀 は `rootNum` の docstring で W(χ) と書かれている値で、B_N の定義に入る反転 `PAG.Part23.W`（南北の入れ替え）と区別して 𝔀 と書く。
扱うのは殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ。係数は K によらない。

χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標のとき：

1. `conj_Jhat_eq_gauss`：conj(Ĵ(χ₁, χ₂)) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))。
2. `conj_Jhat_eq_rootNum`：conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))。s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1。
3. `conj_Jhat_sq_eq_rootNum`：conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²。2 乗で 2 の符号 s は落ちる（4・5 も同じ）。
4. `equator_intertwine_rootNum`：n + 1 ≤ K のとき、P¹(ℤ/p^K) の 2 チャートのモデルの赤道のケット |0, χ⟩ について、B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)。
5. `equator_intertwine_proj_rootNum`：4 の両辺を `projFunEquiv`（Part 24（PAG28）の ℂ 線形同型：`PAG.Part27.ProjLine (p^K)` 上の関数 ≃ 貼り合わせ条件を満たす組）で移した形。B_S^proj・B_N^proj は Part 24（PAG28）、ketS_proj は Part 25（PAG29）で、2 チャートの版をこの同型で移して定義したもの。5 は 4 と同値（`projFun_*` と線形性による手の論証、再照合者が確かめた。Lean の文にはしていない）。点 [x:1]・[1:y] での値としての読みは `projEquiv`（Part 23（PAG27））と `ptEquiv`（Part 22（PAG26））による。

範囲と仮定の効き方（独立照合の指摘）：
- p = 2（すべての n）と p = 3、n = 0 では、仮定を満たす指標の組がなく、5 つの文は空。仮定を満たす例があるのは、p ≥ 5 の n = 0 と、奇素数 p の n ≥ 1。
- 仮定は必要十分ではない。1〜3 では χ₁χ₂ の原始性は不要に見え、χ₁・χ₂ の原始性が中身を運ぶのは n = 0 だけ（n ≥ 1 では両辺が 0 になる。照合者の手計算）。4・5 では χ₁χ₂ の原始性を外すと偽になる（独立照合の反例）。反例は単数でない点（n = 1）にも、単数の点（n = 0、χ₂ = χ̄₁、x = 1）にも出る。単数の点での比 B_N/B_S は conj(J)/J で、conj(Ĵ)² に等しいのは |J|² = N のとき（再照合者の手計算。数値 `records/audit266/numeric/unit_point_ratio.py`：K = n+1、(p, K) = (5,1), (7,1), (3,2), (5,2) で、単数の点の比はすべての組で conj(J)/J、χ₁χ₂ が原始的でない組 8 組では conj(Ĵ)² と一致しない）。
- 4・5 は、Part 21（PAG25）の `equator_intertwine_hat` と Part 25（PAG29）の `equator_intertwine_proj` の係数 conj(Ĵ)² を 3 で書き換えたもの。絡み合いの中身（単数でない点で両辺が 0 になることを含む）はそちらにある。
- 符号 s は、Ĵ（i^a を含まない）と 𝔀（i^a を含む）の正規化の違いから来る。加法指標の向きを変えても、i^a を (−i)^a に替えても変わらない（照合者の手計算）。

## §3 読み（Lean の外）

- 原始指標 χ の成分に、導手 p^(n+1) で計算した 𝔀(χ) を掛ける作用素を U とする（法 p^K の指標として計算すると、K > n+1 では τ = 0 になるため）。B_S(|0,χ₁⟩, |0,χ₂⟩) が χ₁χ₂ の成分に入ること（このパートの文にはない）と合わせて、4 は赤道のケットの上で B_N(k₁, k₂) = U² B_S(U⁻²k₁, U⁻²k₂) と読める。0 の近く（南）の加法の構造が、重なり（赤道）で U² によって ∞ の近く（北）の加法の構造に移される。
- この条件を満たす位相は 𝔀 だけではない（少なくとも次の分がある。推薦案 §3 の盲検の手計算と、構築側の数値 N ≤ 49）：φ(χ) = ε(χ)·𝔀(χ)·√χ(u)（ε は指標ごとの符号、u は単数）、数は φ(N)·2^{原始指標の数}。単数倍 v は u を u·v² に動かすので、単数倍と符号で届くのは u が平方のファイバーだけ。素朴な核の位相 τ/√N は u = −1 の解。
- A1 は導かれない。P¹ の 2 チャートの構造は U を有限個の候補に絞るが、選ばない。「P¹ の構造が A1 を導いた」とは書かない。
- 対照群：関数体 F_p[t]/(t^e) でも代数の部分は同じ形（数値）。ただし関数体の本来のルート数（奇の指標では ∞ の局所因子として F_q 上のガウス和が入る）は、一般にこの条件を満たさない（照合者の文献と、構築側の数値：F_7[t]/(t²) で三つ組 1080 組中 600 組が外れる）。ℚ で 𝔀 が条件を満たすのは、無限素点の比が ±1 で 2 乗すると 1 になるから。小さいが ℚ に固有の観察（確信度：中）。
- P¹(ℤ/N) の 0（南、無限小の側）と ∞（北、無限大の側）を、著者の定義の「無限素点では無限大と無限小が重なり合う」と結ぶ読みは、構築側の候補にとどめる（著者の判断が先）。

## §4 ラベル

- 1〜3：［既知］。積が原始的ならヤコビ和はガウス和の比（K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15）、|τ|² = N（同 定理 3.12）。どちらも法 m は一般で ℤ/p^(n+1) を覆う（定理 3.15 は積の原始性だけを仮定する。WebFetch の要約で確認、2026-11-20）。符号つきの形は Long–Pigno–Pinner（arXiv:1410.6179）の式 (10) と、その出典の Zhang–Yao（Acta Arith. 115, 2004）が挙がっている（盲検の照合者による。原文は構築側で確かめていない）。
- 4・5：［再導出（小さい）］。既存の定理の係数の書き換え。
- 新規候補なし。兆候 4（初等的な部品の組み合わせだけ）は続いている。

## §5 内部照合

- 着手前（推薦案 §0）：P¹ の 2 チャートのモデル（Part 19〜28（PAG23〜PAG32））、赤道の絡み合い（Part 20・21（PAG24・PAG25））、ガウス和の比（Part 11（PAG15））、|τ|²（Part 12（PAG16））、𝔀（Part 252（PAG256））。赤道の絡み合いと 𝔀 を結ぶ文は鎖になかった。
- 閉じる前：機械的な照合（全宣言 4490 件、対象 5 件、候補の組 100、照合 200 回、一致なし。記録 `records/audit266/internal/`）。言葉の検索で、射影直線の上の版 `PAG.Part29.equator_intertwine_proj` を見つけて定理 5 にした。下書きの補助補題（積の χ(−1)）は Mathlib の `MulChar.mul_apply` の特別な場合なので消した。

## §6 照合

- 独立照合（形式文と定義だけ、`records/audit266/outputs/check_output.md`、約 454 秒）：逆翻訳は意図どおり。非空虚性の証人は p ≥ 5 の n = 0 と奇素数の n ≥ 1 にある。除去テストで、原始性（n = 0）・符号の場合分け・2 乗のどれを外しても反例がある。指摘：空になる範囲、仮定の効き方、4・5 は係数の書き換え、定理 5 の 1 ≤ K は冗長、記号 W の衝突、`projFunEquiv` が入力になかった。
- 直したこと：docstring と冒頭の説明に、空になる範囲・仮定の効き方・係数の書き換えであることを書いた。定理 5 から 1 ≤ K の仮定を外した（h から出る）。
- 再照合（独立照合の出力の全文・直した後の PAG266.lean の全文・形式文の差分・定義を入力、`records/audit266/outputs/recheck_output.md`、約 425 秒）：形式文の変更（定理 5 の hK を外した）は意味を変えない（確信度：高）。独立照合の指摘は、直った・一部・直っていないに分けられた。直っていなかったのは、定理 3〜5 で符号 s が落ちることの断り。新しい指摘（重要度順）：定理 5 の「射影直線そのもの」は強い（5 は 4 と同値で、足す内容は `projEquiv`・`ptEquiv` が正しい点の対応であることだけ）、4・5 の原始性の括弧が狭い（単数の点でも反例）、`JH` はこの文書に現れない、題と読みの行（U は導手で計算した 𝔀、B_S が χ₁χ₂ の成分に入る前提）、Part 番号の書き方、𝔀 と W、範囲の明記、Conrad の範囲。
- 再照合の後の直し：上の指摘 1〜9 を、Lean の冒頭の説明と docstring・このノート・xlsx・索引に同じ文面で入れた。形式文は変えていない（差分で確認、ビルドは sorry 0・警告 0）。Conrad の範囲は WebFetch で確かめた。単数の点の比は数値で確かめた。**この直しはまだ照合を受けていないので、台帳に L6 として残し、閉じるときの統合照合の入力に含める。**

## §7 収束アラームの報告

- 辞書：このパートの名前の行を §20 に足す（右列はすべて埋まっている）。Part 257〜259 の行のない名前（6 件以上）は残る。
- 文献照合：推薦案の盲検の問いテストで実施した。
- 兆候 4：続いている。
```


### D2 材料索引 `notes/pag2_founding_material_index.md` の 1.4 と 2.4（節の全文）

```markdown
**1.4 舞台は射影直線 P¹。反転が 0 と ∞ を入れ替える。**
- 地位：
  - 「舞台は P¹」は著者の言葉（2026-11-18 19:01、「射影」の読みの採用のとき）。
  - 「反転が 0 と ∞ を入れ替える」は構築側の読みで、2026-11-16 に著者が確認した。
  - P¹(ℤ/N) そのものは［既知］（モジュラー記号の標準の道具）。
- Lean（Part 19・22・23（PAG23・PAG26・PAG27））：
  - 射影直線 `PAG.Part27.ProjLine`、反転 [a:b] ↦ [b:a] の定義 `PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`（一般の N）。
  - N = p^K（K ≥ 1）では、点モデル `PAG.Part26.Pt` との点集合の全単射 `PAG.Part27.projEquiv` と、点の数 `PAG.Part27.card_ProjLine`。
  - 2 チャートモデルの貼り合わせ条件 `PAG.Part23.Compat` と、その反転 `PAG.Part23.W`。点モデルの関数との線形同型 `PAG.Part26.ptEquiv`（一般の N）。
  - 南北のチャートの畳み込み `PAG.Part23.BS`・`PAG.Part23.BN`（Part 19（PAG23））。赤道（単数）での絡み合い：χ₁・χ₂・χ₁χ₂ が原始的なら、赤道のケットについて B_N = conj(Ĵ)² · B_S（`PAG.Part25.equator_intertwine_hat`、Part 21（PAG25）。射影直線の上の版は `PAG.Part29.equator_intertwine_proj`、Part 25（PAG29））。第 6 版までの索引はこれらを拾っていなかった（2026-11-19 夜の内部照合で見つけた）。係数を貼り合わせの位相 𝔀 で書いた形は 2.4 の Part 262。
- 留保：
  - 「0 と ∞ は別の点で、反転がこの 2 点を入れ替える」という文は Lean にない（N ≥ 2 で正しい）。
  - N が 2 つ以上の素因数を持つとき、点モデルと P¹(ℤ/N) の点の数は一致しない（数え上げ、Lean の外）。
- ノート：`pag2_projection_material.md`（第 6 版）§1・§3。
```

```markdown
**2.4 「射影」の変換と位相：反転（乗法の側）と加法の変換（加法の側）の合成。**
- 地位：
  - 読み（2026-11-18 19:01、著者が留保つきで採用）。
  - 著者の言葉は「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」。「反転と加法の変換の合成」は構築側の読みで、著者が 19:01 に留保つきで材料として採用した。著者の言葉「貼り合わせの合成」の貼り合わせは U（次の項）。
  - 「貼り合わせ」は U（ねじれた貼り合わせ）を指す（2026-11-19 06:36、著者の決定。`PAG.Part23.Compat`（ねじれのない座標の貼り合わせ）ではない）。
  - 標準の核は Hartley 核（著者の決定）。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは照合していない（JH_N の正規化も本文で確かめていない）。
- Lean（Part 252（PAG256）、［再導出］）：
  - 写像 `PAG.Part256.JH`、値 `PAG.Part256.rootNum`（= 𝔀）、偶奇の因子 `PAG.Part256.parFac`。
  - すべての指標で、単数の上の式：`PAG.Part256.JH_eq_rootNum_mul_any`。
  - 原始指標で絶対値 1：`PAG.Part256.normSq_rootNum`。
  - 原始指標で単数の外に漏れない：`PAG.Part256.hartley_eq_zero_of_not_isUnit`。
  - 原始性を外した反例：`PAG.Part256.removal_counterexample`・`PAG.Part256.removal_counterexample_normSq`・`PAG.Part256.removal_counterexample_four`。
- 留保：
  - `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。
  - P¹ のモデルと結ぶ Lean の文（Part 262（PAG266）、2026-11-20、短期層）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、P¹(ℤ/p^K) の赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデル `PAG.Part266.equator_intertwine_rootNum`、射影直線 `PAG.Part266.equator_intertwine_proj_rootNum`）。係数の等式 conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は両方とも奇のときだけ −1）は `PAG.Part266.conj_Jhat_eq_rootNum`、2 乗の形は `PAG.Part266.conj_Jhat_sq_eq_rootNum`、ガウス和の形は `PAG.Part266.conj_Jhat_eq_gauss`。
    - 範囲：殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ（係数は K によらない）。p = 2（すべての n）と p = 3、n = 0 では文は空。作用素の形の 2 つは Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換えで、絡み合いの中身はそちらにある。射影直線の版は 2 チャートの版を `projFunEquiv`（Part 24（PAG28））で移したもので、2 チャートの版と同値（手の論証）。
    - このパートの文に `JH` は現れない。Lean で結んだのは 𝔀 の値と P¹ の赤道の係数で、上の留保（`JH` は P¹ の上の作用素ではない）は残る。
    - 読み（Lean の外）：原始指標 χ の成分に導手で計算した 𝔀 を掛ける作用素を U とすると、B_S(|0,χ₁⟩, |0,χ₂⟩) が χ₁χ₂ の成分に入ることと合わせて、赤道で北の畳み込みは南の畳み込みを U² で移したもの。この条件は U を有限個の候補（少なくとも単数 u と指標ごとの符号の分がある）に絞るが選ばず、A1 は導かれない。関数体では本来のルート数が一般にこの条件を満たさない（ℚ に固有の小さな観察、確信度：中）。P¹(ℤ/N) の 0・∞ を定義の「無限小と無限大」と結ぶ読みは構築側の候補（著者の判断が先）。ノート `pag2_pag266_p1_equator_rootnum.md`。
  - 原始指標で 𝔀 がルート数であることは Lean の外。
  - 素朴なフーリエ核 e(xy) では値が τ(χ)/√N で、奇の指標で i 倍ずれる。このずれは滑らかにしない。
- ノート：`pag2_part252_hartley_gluing.md`、`pag2_projection_material.md`、`pag2_prereg_projection.md`。
```


### D3 辞書 `notes/pag2_terwilliger_dictionary.md` の §19・§20

```markdown
## 19. 無限素点・スケーリング・貼り合わせ U との相互作用の読みで足した名前（2026-11-19 夕方。Lean は足していない）

| 名前・主張 | 文献の言葉 | 出典・注意 |
|---|---|---|
| 素数冪ごとの殻の反転の CRT の積 J（数値、Lean の外） | 基点 0 を固定する、スキームの自己同型（固定群 G_0 の元） | 盲検の手計算。法 N の殻ごとの反転 s·w ↦ s·w⁻¹ は N = 10, 14, … で自己同型でない（数値） |
| `fullComm`（Part 220、PAG224）の群による記述（Lean の外） | 二重可換子定理：A_N = End_{G_0}(V_N) なら A_N' は G_0 の群環の像。T(v) ⊆ End_{G_v} | arXiv:2510.17118 の式 (2)。三重推移性（木のスキーム）の明記は見つからなかった（盲検） |
| Hartley・フーリエによる共役（`fourierConj_*` は Part 242、Hartley 版は Lean の外） | translation scheme の指標による双対性（形式的自己双対性） | Martin–Tanaka の解説 arXiv:0811.2475 §6、Kim–Kim arXiv:1108.4947 |
| 単数の角 D_1 A_N D_1 = 導手ごとの射影（Lean の外。`condPart` は Part 254） | E*_1 T E*_1（双対冪等元の角）。単数群の部分群 ker((ℤ/N)^× → (ℤ/g)^×) の上の平均 | 盲検の手計算 |
| range(D_1) ∩ range(E_1) = V_prim（`Vprim` は Part 253、等式は Lean の外） | E*_1 V ∩ E_1 V。原始指標 ⇔ ガウス和 τ(χ, n) = χ̄(n)τ(χ) がすべての n で成り立つ | Montgomery–Vaughan Thm 9.7・Ex. 9.2.6 |
| F_M ι = V F_N（数値、Lean の外） | Pontryagin 双対の関手性（商 ℤ/M → ℤ/N と包含の双対）。φ と ψ は Bost–Connes の ρ_n の 2 つの見方（平行移動の側と乗法作用素の側） | Shirbisheh arXiv:0808.1767、Arledge–Laca–Raeburn 1997。有限レベルで並べた文は見つからなかった（盲検、検索は浅い） |

- 未記入の件数（この節）：0。

## 20. Part 262（PAG266）の名前（2026-11-20）

| 名前・主張 | 文献の言葉 | 出典・注意 |
|---|---|---|
| `conj_Jhat_eq_gauss`・`conj_Jhat_eq_rootNum`・`conj_Jhat_sq_eq_rootNum` | ヤコビ和はガウス和の比 J = G₁G₂/G₁₂（積が原始的なとき）と |G|² = N。位相 conj(Ĵ) はガウス和の位相の余境界（2 乗で符号が消える） | K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15・3.12（法 m は一般。WebFetch の要約で確認）。符号つきの形は Long–Pigno–Pinner（arXiv:1410.6179）の式 (10)（盲検の照合者による） |
| `equator_intertwine_rootNum`・`equator_intertwine_proj_rootNum` | P¹(ℤ/p^K) の 2 チャートの畳み込みの、重なりでの比較（この設定の文献の名前は見つからなかった） | Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換え。射影直線の版は 2 チャートの版を `projFunEquiv` で移したもので同値。設定そのものは盲検の 1 回の検索では見つからなかった |
| 条件「U'² が赤道で B_S を B_N に移す」の解の集まり（Lean の外） | 部分群の補集合の上で乗法的な関数は準同型に延びる（|X/Y| ≥ 3）、ポントリャーギン双対 | 盲検の照合者の手計算（補題を書いた文献は探していない）。加法指標の取り替えで局所定数が χ(b) 倍になること（Tate、Biswas arXiv:1401.5591 §4.3） |

- 未記入の件数（この節）：0。
```


### D4 xlsx（final84）の行 3719〜3723（列 A〜F）と、メモの末尾、検証手順の行 285

```
行 3719：PAG2.0-262（PAG266、短期層の小さいノート）舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く（推薦案 pag2_p1_gluing_preregistration.md、著者の採用 2026-11-20 06:55。基礎文書の索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める材料）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1）、conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²、n + 1 ≤ K のとき赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと、projFunEquiv で射影直線の上の関数に移した形）。扱うのは殻 0 と導手がちょうど p^(n+1) の指標の組だけ。p = 2 と p = 3、n = 0 では文は空。`JH` と P¹ のモデルを結ぶ文ではない。ラベルは 1〜3 が［既知］、4・5 が［再導出（小さい）］ ｜ conj_Jhat_eq_gauss ｜ χ₁・χ₂・χ₁χ₂ が法 N = p^(n+1) の原始指標なら conj(Ĵ(χ₁, χ₂)) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))（Ĵ = J/√N、τ = gaussSum χ stdAddChar） ｜ J·conj J = N と、ガウス和の比はヤコビ和 ｜ PAG.Part15.gauss_ratio_eq_jacobi ｜ 検証完了（axioms 確認済み）

行 3720：PAG2.0-262（PAG266、短期層の小さいノート）舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く（推薦案 pag2_p1_gluing_preregistration.md、著者の採用 2026-11-20 06:55。基礎文書の索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める材料）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1）、conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²、n + 1 ≤ K のとき赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと、projFunEquiv で射影直線の上の関数に移した形）。扱うのは殻 0 と導手がちょうど p^(n+1) の指標の組だけ。p = 2 と p = 3、n = 0 では文は空。`JH` と P¹ のモデルを結ぶ文ではない。ラベルは 1〜3 が［既知］、4・5 が［再導出（小さい）］ ｜ conj_Jhat_eq_rootNum ｜ 同じ仮定で conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（𝔀 = rootNum = τ/(i^a √N)。s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1） ｜ 1 と rootNum の定義、偶奇の 4 通りの場合分け（積の偶奇は χ(−1) の積） ｜ MulChar.mul_apply ｜ 検証完了（axioms 確認済み）

行 3721：PAG2.0-262（PAG266、短期層の小さいノート）舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く（推薦案 pag2_p1_gluing_preregistration.md、著者の採用 2026-11-20 06:55。基礎文書の索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める材料）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1）、conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²、n + 1 ≤ K のとき赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと、projFunEquiv で射影直線の上の関数に移した形）。扱うのは殻 0 と導手がちょうど p^(n+1) の指標の組だけ。p = 2 と p = 3、n = 0 では文は空。`JH` と P¹ のモデルを結ぶ文ではない。ラベルは 1〜3 が［既知］、4・5 が［再導出（小さい）］ ｜ conj_Jhat_sq_eq_rootNum ｜ 同じ仮定で conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²（2 の符号 s は 2 乗で落ちる。4・5 も同じ） ｜ 2 の 2 乗 ｜ conj_Jhat_eq_rootNum ｜ 検証完了（axioms 確認済み）

行 3722：PAG2.0-262（PAG266、短期層の小さいノート）舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く（推薦案 pag2_p1_gluing_preregistration.md、著者の採用 2026-11-20 06:55。基礎文書の索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める材料）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1）、conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²、n + 1 ≤ K のとき赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと、projFunEquiv で射影直線の上の関数に移した形）。扱うのは殻 0 と導手がちょうど p^(n+1) の指標の組だけ。p = 2 と p = 3、n = 0 では文は空。`JH` と P¹ のモデルを結ぶ文ではない。ラベルは 1〜3 が［既知］、4・5 が［再導出（小さい）］ ｜ equator_intertwine_rootNum ｜ n + 1 ≤ K のとき、P¹(ℤ/p^K) の 2 チャートのモデルの赤道のケット |0, χ⟩ について B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩) ｜ Part 21（PAG25）の equator_intertwine_hat と 3（係数の書き換え） ｜ PAG.Part25.equator_intertwine_hat ｜ 検証完了（axioms 確認済み）

行 3723：PAG2.0-262（PAG266、短期層の小さいノート）舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く（推薦案 pag2_p1_gluing_preregistration.md、著者の採用 2026-11-20 06:55。基礎文書の索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める材料）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1）、conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²、n + 1 ≤ K のとき赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと、projFunEquiv で射影直線の上の関数に移した形）。扱うのは殻 0 と導手がちょうど p^(n+1) の指標の組だけ。p = 2 と p = 3、n = 0 では文は空。`JH` と P¹ のモデルを結ぶ文ではない。ラベルは 1〜3 が［既知］、4・5 が［再導出（小さい）］ ｜ equator_intertwine_proj_rootNum ｜ 4 の両辺を projFunEquiv（Part 24（PAG28）の ℂ 線形同型：ProjLine (p^K) 上の関数 ≃ 貼り合わせ条件を満たす組）で移した形：BN_proj(ketS_proj χ₁, ketS_proj χ₂) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · BS_proj(…)。4 と同値（手の論証、Lean の文にはしていない）。1 ≤ K は h から出るので仮定にない ｜ Part 25（PAG29）の equator_intertwine_proj と 3（係数の書き換え） ｜ PAG.Part29.equator_intertwine_proj ｜ 検証完了（axioms 確認済み）

メモの末尾（600 字）：…下書きの pull_trans（Part 259 の pull_pull と向きが逆の同じ文）と apply_single_two_of_mem_span（Part 258 の exists_mulLeft_of_mem_span から直ちに出る）を消し、単射を Part 259 の pull_injective' から出す形に直した。 2026-11-19 午後、Part 261（PAG265.lean、短期層、角の写像の帰納系と極限）をコンパイルし、行 3709〜3718 を足した（定理 10 個）。索引の型は Part 254 の Lvl を使った（内部照合）。下書きの cornerSys_apply（Part 260 の cornerHom_coe と同じ文）を消した。 2026-11-20 朝、Part 262（PAG266.lean、短期層、舞台 P¹ の赤道の絡み合いを 𝔀 で書く）をコンパイルし、行 3719〜3723 を足した（定理 5 個）。内部照合で、Part 21（PAG25）の equator_intertwine_hat と Part 25（PAG29）の equator_intertwine_proj を使った（言葉の検索）。独立照合・再照合を受けた。再照合の後の直し（文面のみ、形式文は変えていない）は尾の台帳の L6 で、閉じるときの統合照合の対象。

検証手順 行 285：284 ｜ PAG 2.0 Part 262（短期層）: PAG266.lean（舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く：ヤコビ和の共役のガウス和と 𝔀 による形、符号つきの 1 乗と 2 乗の形、2 チャートのモデルと射影直線の上の作用素の形）をコンパイル ｜ 完了 ｜ 2026-11-20 朝、推薦案 pag2_p1_gluing_preregistration.md（著者の採用 06:55）。定理 5 個、sorry 0、警告 0、#print axioms 5 行は標準の公理の範囲。内部照合（言葉の検索で Part 21 の equator_intertwine_hat と Part 25 の equator_intertwine_proj を使った。機械的な照合は全宣言 4490 件、対象 5 件、200 回で一致なし）。独立照合・再照合（記録は records/audit266/outputs/）。再照合の後の直しは尾の台帳の L6。
```


### D5 引き継ぎメモ `handoff/PAG2_handoff_part259.md` の Part 262 の項

```markdown
- **Part 262（PAG266、短期層、2026-11-20）**：20:19 の「構築を進めてください」を受けて、舞台 P¹ の上の貼り合わせを関門にかけ（`notes/pag2_p1_gluing_preregistration.md`）、推薦案を著者が 06:55 に採用した（「進めてください」）。
  - Lean：定理 5 個（sorry 0、警告 0、#print axioms は標準の 3 つ）。χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は両方とも奇のときだけ −1）、2 乗の形、n + 1 ≤ K のとき赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと、`projFunEquiv` で射影直線の上の関数に移した形）。
  - 範囲：殻 0 と導手がちょうど p^(n+1) の指標の組だけ。p = 2 と p = 3、n = 0 では文は空。作用素の形は Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換え。`JH` と P¹ のモデルを結ぶ文ではなく、索引 2.4 の留保は残る。
  - 読み（Lean の外）：B_N = U² B_S U⁻²（U は導手で計算した 𝔀 を掛ける作用素）。条件は U を有限個の候補に絞るが選ばず、A1 は導かれない。関数体の本来のルート数は一般にこの条件を満たさない（ℚ に固有の小さな観察、確信度：中）。P¹ の 0・∞ を定義の「無限小と無限大」と結ぶ読みは著者の判断が先。
  - ラベル：1〜3 が［既知］（Conrad の定理 3.15・3.12、法 m は一般）、4・5 が［再導出（小さい）］。新規候補なし。兆候 4 は続く。
  - 照合：内部照合（機械的 200 回で一致なし、言葉の検索で Part 21・25 の定理を使った）、独立照合（形式文と定義だけ）、再照合（独立照合の出力・直した後の全文・差分・定義）。再照合の後の直しは文面のみ（形式文は変えていない）で、尾の台帳の L6。
  - 件数：鎖全体の定理・補題は 3,695 件（3,690 + 5）。xlsx は final84（行 2〜3723）。
  - 閉じる条件：統合照合（Part 262 の材料と台帳の L1〜L6）。その照合を受けるまで、Part 262 は閉じていない。
```


### D6 尾の台帳 `notes/pag2_tail_ledger.md` の L6

```markdown
### L6：Part 262（PAG266）の再照合の後の直し（2026-11-20 朝）

- 範囲：再照合（`records/audit266/outputs/recheck_output.md`）の指摘 1〜9 を受けた直し。PAG266 の冒頭の説明と docstring（形式文は変えていない）、ノート `pag2_pag266_p1_equator_rootnum.md`（題、§1、§2、§3、§4、§6）、xlsx の Part 262 の行、索引 1.4・2.4 の Part 262 の行、辞書 §20。数値 `records/audit266/numeric/unit_point_ratio.py` を足した。
- 自己申告（根拠にしない）：言い過ぎの狭め（定理 5 の「そのもの」、題）と、前提・範囲・出典の明記。主張は足していないつもりだが、単数の点の比の文（conj(J)/J）は新しく書いた内容である。
- 扱い：Part 262 を閉じるときの統合照合の入力に含める（L1〜L5 と同じ照合）。
```


## §E 再照合の出力（全文）と、その後の直しの差分（台帳 L6）


### E1 再照合の出力 `records/audit266/outputs/recheck_output.md`

# 再照合の成果物：Part 262（PAG266）の独立照合の後の直し

（通知の本文をそのまま写した。）

**前提**
- 判定の根拠は入力ファイル 1 つだけです。計算はすべて手で行い、コードは実行していません。
- プロジェクトの指示書は自動で文脈に入っていましたが、判定の根拠には使っていません。
- 入力にはビルドの記録がありません（sorry 0、警告 0、`#print axioms` の出力）。直した後の版がコンパイルすることは確かめていません。

## 1. §A の指摘ごとの判定

| §A の指摘 | 判定 | 根拠（引用） |
|---|---|---|
| §0 入力になかった定義（push、shellEmb、projFunEquiv、compat_extS、compat_extN） | 一部 | 足された。ただし projFunEquiv の中身の `projEquiv`・`ptEquiv` と、`Compat` の定義はない：「(LinearEquiv.funCongrLeft ℂ ℂ (projEquiv K hK)).trans (ptEquiv (p ^ K))」 |
| §0 殻 0 のケットの読み（確信度：中） | 直す必要なし（読みが確かめられた） | 「x ↦ p^v x」（v = 0 で恒等写像）、「殻サイズ \|S_u\| = p^(K−1−u)(p−1)」。§4 (e) を参照 |
| 4.1 空になる範囲 | 直った | 冒頭：「p = 2（すべての n）と p = 3、n = 0 では…5 つの文は空」。定理 1 の docstring にもある。定理 2〜5 の docstring にはないが、冒頭が 5 つの文すべてを覆っている |
| 4.2 仮定は必要十分ではない | 直った（括弧の説明が狭い。§5 の 2） | 「仮定は必要十分ではない：1〜3 では χ₁χ₂ の原始性は不要に見え」 |
| 4.3 符号 s の頑健さ | 直す必要なし（観察。定理 2 の docstring に入った） | 「加法指標の向きや i^a を (−i)^a に替えても変わらない」 |
| 4.4(a) 定理 2 の名前が符号に触れない | 一部（名前は同じ。docstring の題で補った） | 「**2. 𝔀 による形（2 乗を外した形）**」 |
| 4.4(b) 定理 3〜5 は符号の情報を捨てる | 直っていない（断りがない） | 定理 3 の docstring は「**3. 2 乗の形**」だけ |
| 4.4(c) 4・5 は係数の書き換えで、中身は Part 25・29 にある | 直った | 「係数 conj(Ĵ)² を 3 で書き換えたもので、絡み合いの中身…は Part 21 にある」 |
| 4.5 conj(Ĵ) = 1/Ĵ | 直す必要なし | ― |
| 4.6 √N | 直す必要なし | ― |
| 4.7(a) λ は K によらない | 直す必要なし（観察） | ― |
| 4.7(b) hK が冗長 | 直った | §C で `(hK : 1 ≤ K)` を削除。docstring：「1 ≤ K は h から出るので、仮定に置かない」 |
| 4.7(c) 殻 0 と導手 p^(n+1) だけが対象 | 一部（「赤道」「法 p^(n+1) の原始指標」で暗に示すだけ） | 範囲の外を明記した文はない |
| 4.8(a) P1F には貼り合わせ条件を満たさない組も入る | 直す必要なし | ― |
| 4.8(b) 定理 4 の等式は単数でない点で 0 になることを含む | 直った | 「（単数でない点で両辺が 0 になることを含む）」 |
| 4.8(c) 定理 5 は projFunEquiv に依存する | 一部 | 線形性は §D で確かめられる。点との対応は確かめられない（§4）。docstring には依存の断りがなく、逆に「射影直線そのものの上の形」と書いている |
| 4.9 記号 W の衝突 | 一部 | PAG266 の中では 𝔀 で解消した。PAG256 の docstring は「W(χ) = τ(χ)/(i^a √N)」のままで、𝔀 がこの W(χ) と同じ値だという断りがない |
| 除去テストの表の（*） | 直った | 「≃ₗ[ℂ]」。§4 (b) で、反例は条件なしで定理 5 に移ることが確かめられた |

## 2. §C の形式文の変更で、文の意味は変わったか

**結論：意味は変わっていません（確信度：高）。**

- `hK : 1 ≤ K` は命題の証明です。Lean 4 では同じ命題の証明どうしが定義上等しいので、`BNproj K p₁ …` と `BNproj K p₂ …` は同じ項です。`(by omega)` の 4 か所も同じです。
- 前の文から今の文は、前の文に `h` から作った `1 ≤ K` の証明を渡せば出ます。今の文から前の文は、`hK` を使わなければ出ます。
- 適用範囲も同じです。`h : 0 + (n + 1) ≤ K` から K ≥ 1 なので、K = 0 はどちらの文でも除かれます。
- 変わったのは引数の並びだけです。`hK` を位置引数で渡している呼び出しがほかにあれば壊れます。入力には呼び出しがありません。
- 確かめられないこと：文の中の `by omega` がその場の `h` で閉じるか、証明の `rw` が一致を取れるか。どちらも通るはずですが、ビルドの記録がありません。

## 3. docstring と冒頭の説明の文ごとの照合

| 箇所 | 判定 | 内容 |
|---|---|---|
| 題（254 行）「貼り合わせの位相 𝔀 で書く」 | 形式文より強い（読みを含む） | 形式文に貼り合わせ U は現れず、𝔀 は係数のスカラーとしてだけ出る。U は 272 行で自ら「読み（Lean の外）」と断っている |
| 問いの出所（256 行） | 注意 | 留保は「`JH` と P¹ のモデルを結ぶ文はない」だが、§B の全文に `JH` は一度も出てこない。結んだのは 𝔀 の値と P¹ の係数で、留保そのものはこのファイルの後も変わらない。そのことの断りがない |
| 257〜258 行 | 問題なし | 形式の内容を言っていない |
| 記号 N（261 行） | 一致。軽い注意 | N = p^(n+1) は指標の法。§D の `P1F N`・`ProjLine N` の N は、定理では p^K。K > n+1 のとき同じ字が別の値を指す |
| 𝔀（262 行） | 一致 | `if χ.Even then 1 else I` と合う。「偶でない＝奇」は `even_or_odd` と排他性による |
| 263 行 | 一致 | `kS K 0 (n+1) h χ` は南チャートの版（extS） |
| 主な定理 1〜3 | 一致 | ― |
| 主な定理 4 | 一致。軽い欠け | n + 1 ≤ K が書かれていない（ケットの記号に暗に含まれる） |
| 主な定理 5「射影直線そのもの」 | やや強い | B_S^proj・B_N^proj・ketS_proj は 2 チャートの版を移して定義したもので、5 は 4 と同値（§4）。「そのもの」は内在的に定義された文のように読める |
| 読み（272 行） | 食い違いはないが、足りない前提がある | (i) 4 からこの読みを出すには「B_S(\|0,χ₁⟩,\|0,χ₂⟩) が χ₁χ₂ の成分に入る」という、この文書にない事実が要る。(ii) K > n+1 のとき、法 p^K の指標として計算した 𝔀 は 0 になるので（法 p^k、k ≥ 2 の原始的でない指標では τ = 0）、U⁻² が意味を持つには「導手で計算した 𝔀」と指定する必要がある |
| 273 行「𝔀 だけではない」 | Lean の外、出典つき。確かめられない | 「単数 u と符号の分」が全部なのか少なくともなのかが曖昧 |
| 274 行（A1、空になる範囲） | 一致 | §A と合う。PAG30 の注意とは照合できない |
| 275 行 | 一致 | 「1〜3 では」が後半にもかかるかは曖昧。ただ後半（n ≥ 1 では両辺が 0）は 5 つの定理すべてで成り立つので、食い違いはない |
| 276 行の前半の括弧「単数でない点で両辺が 0 になる部分」 | 狭すぎて §A 自身の反例と合わない | §A の n = 0 の反例は単数 x = 1 で破れる（「x = 1 で 1/2 ≠ 1/6」）。手計算では、単数の点での B_N/B_S の比は conj(J)/J で、これが conj(Ĵ)² に等しいのは \|J\|² = N のとき（確信度：中〜高）。χ₁χ₂ の原始性は単数の点の係数にも効いている |
| 276 行の後半 | 一致。番号の書き方に注意 | 「Part 21・25」に PAG 番号がない。同じ冒頭で名前空間 `PAG.Part25`（＝Part 21）を引いているので、「Part 25」（＝PAG29）と取り違えやすい |
| ラベル（278 行） | 強すぎない（「見込み」と明記） | 参照先（Conrad の定理 3.15・3.12）の番号と範囲は確かめられない。有限体（法 p）だけを扱う文献なら n ≥ 1 を覆わない |
| 定理 1 の docstring | 一致 | ― |
| 定理 2 の docstring | 一致 | 符号の説明は証明の場合分けと合う（両方が奇の場合だけ `I_sq` で −1）。手計算でも s = i^(a₁₂ − a₁ − a₂) で、指数は 0 か ±2。規約を変えても s が変わらないことも手で確かめた。どちらも Lean の外で、出典は書かれている。「χ₁ か χ₂ が偶」は「少なくとも一方」と書くほうが誤読がない（ごく軽い） |
| 定理 3 の docstring | 一致 | 符号の情報が落ちることの断りがない |
| 定理 4 の docstring | 一致 | n + 1 ≤ K は 0 + (n+1) ≤ K と同じ。証明は書き換え 2 回だけ |
| 定理 5 の docstring | やや強い。置き場の書き方が紛らわしい | 「そのもの」は上と同じ問題。B_S^proj・B_N^proj は `PAG.Part28`（PAG28）にあるが、括弧の書き方では PAG29 に属すように読める。1 ≤ K の文は正確 |

## 4. §D の定義で、定理 5 の意味を確かめられるか

**確かめられたこと**
- (a) `projFunEquiv` は ℂ 線形同型（`≃ₗ[ℂ]`）なので、スカラー倍と可換です。§A の「線形か」という留保は解けます。
- (b) 同じ K、h、χ₁、χ₂ ごとに、定理 5 と定理 4 は同値です（原始性の仮定は使いません）。E = `projFunEquiv K hK` と書きます。
  - 5 から 4：両辺に E を当てて `.1` を取ります。`projFun_BNproj`・`projFun_BSproj`・`projFun_ketS` と E の線形性で、4 の両辺になります。
  - 4 から 5：E の単射性と `Subtype.ext` によります。
  - 手で組んだ論証で、Lean の文ではありません。補題は文だけを見ています。
  - この同値には原始性の仮定が要らないので、§A の定理 4 への反例はすべて、条件なしで定理 5 に移ります。
- (c) 定理 5 は `ProjLine (p^K) → ℂ` の関数どうしの等式で、スカラー倍は点ごとです。
- (d) `Unimod`・`projSetoid` から、P¹(ℤ/9) は 12 点だと手計算で出ます。b が単数なら [a/b : 1] で 9 個、b が単数でないなら a が単数で [1 : b/a]（b/a ∈ {0, 3, 6}）が 3 個です。§A と一致します。
- (e) §A の殻 0 のケットの読みは正しいことが分かりました。`shellEmb K 0` は x ↦ x（全単射）なので `push` は恒等で、ket = φ(p^K)^(−1/2)·χ(x mod p^(n+1))、φ(p^K) = `sz p K 0` = p^(K−1)(p−1) です。
- (f) `compat_extS`・`compat_extN` から、BS・BN の出力は `compatSub` に入ります（§A の 8 と一致）。

**確かめられなかったこと**
- (a) E の第 1 成分が点 [x:1] の値、第 2 成分が点 [1:y] の値に当たること。`projEquiv K hK` と `ptEquiv (p^K)` の定義が入力にありません。
- (b) `Compat` の定義。`compatSub` の証明の形から「単数 y で F.2 y = F.1 y⁻¹」の型だと推測はできますが、文はありません。
- (c) したがって、§A の「ψ_i は [x:1] で f_i(x)、単数でない y の [1:y] で 0」も確かめられません。
- (d) 帰結：どんな線形同型で移しても 5 と 4 は同値になります。定理 5 が定理 4 に足す内容は、`projEquiv`・`ptEquiv` が正しい点の対応であることだけです。

## 5. 直すべき点（重要度順）

1. **（中）定理 5 の docstring と冒頭の主な定理 5の「射影直線そのもの」**
   - 直し案：「**5. 射影直線の上の関数に移した形**：4 の両辺を `projFunEquiv`（Part 24（PAG28）。`PAG.Part27.ProjLine (p^K)` 上の関数と、貼り合わせ条件を満たす組との ℂ 線形同型）で移した等式。B_S^proj・B_N^proj は Part 24（PAG28）、ketS_proj は Part 25（PAG29）で、2 チャートの版をこの同型で移して定義したもの。5 は 4 と同値（`projFun_*` と線形性による。Lean の文にはしていない）。点 [x:1]・[1:y] での値としての読みは `projEquiv`・`ptEquiv` による。」
2. **（中）276 行の括弧**
   - 直し案：「4・5 では χ₁χ₂ の原始性を外すと偽になる（独立照合の反例）。反例は単数でない点（n = 1）にも、単数の点（n = 0、χ₂ = χ̄₁、x = 1）にも出る。単数の点での比は conj(J)/J で、conj(Ĵ)² に等しいのは \|J\|² = N のとき（Lean の外、手計算）。」
3. **（中）問いの出所と中身の対応**
   - 直し案（256 行の後に足す）：「この文書の文に `JH` は現れない。Lean で結んだのは 𝔀（`rootNum`）の値と P¹ の赤道の係数で、留保『`JH` と P¹ のモデルを結ぶ Lean の文はない』はこの文書の後も残る。」
4. **（低〜中）題と読みの行**
   - 題の直し案：「舞台 P¹ の赤道の絡み合いの係数を 𝔀（`rootNum`）で書く」。
   - 272 行の直し案：「原始指標 χ の成分に、導手 p^(n+1) で計算した 𝔀(χ) を掛ける作用素を U とすると、B_S(\|0,χ₁⟩,\|0,χ₂⟩) が χ₁χ₂ の成分に入ること（この文書の文にはない）と合わせて、4 は…と読める。」
   - 273 行は「少なくとも」を足す。
5. **（低）Part 番号**：276 行を「Part 21（PAG25）・Part 25（PAG29）」と書く。名前空間 `PAG.Part25` と「Part 25」は別物だと分かるようにする。
6. **（低）𝔀 と W**：記号の段に足す。「𝔀 は `rootNum` の docstring で W(χ) と書かれている値。B_N の定義に入る反転 `PAG.Part23.W` と区別して 𝔀 と書く。」
7. **（低）範囲**：主な定理 4 に「n + 1 ≤ K」を足す。さらに「扱うのは殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ。係数は K によらない」と足す。
8. **（低）符号の欠落**：定理 3 の docstring に「（2 乗で定理 2 の符号 s は落ちる。4・5 も同じ）」と足す。定理 2 の名前は docstring で補えているので、変えなくてもよい。
9. **（低）ラベル行の参照**：Conrad の文献名と、それが ℤ/p^k（n ≥ 1）を覆うかを明記する。有限体だけを扱うなら、素数冪の法の出典を足す。
10. **（記録）次の照合の入力**：`projEquiv`・`ptEquiv`・`Compat` の定義と、ビルドの記録（sorry 0、警告 0、`#print axioms` の出力）を入れる。

## 使ったツールと読んだ範囲

- Read を 1 回使い、`/home/claude/ardel-projective-geometry/records/audit266/input_recheck.md` の全文（1〜708 行）を読みました。
- ほかのファイルは読んでいません。コードの実行とウェブの使用もしていません。


### E2 再照合の後の直しの差分（コミット e669d83 → 5f675ec。xlsx・記録の出力・名前の照合の記録は除く）

```diff
diff --git a/PAG266.lean b/PAG266.lean
index 463d89c..7bbb2fd 100644
--- a/PAG266.lean
+++ b/PAG266.lean
@@ -1,29 +1,36 @@
 /-
-アーデル射影幾何 — Part 262（PAG266、短期層の小さいノート、2026-11-20）：舞台 P¹ の赤道の絡み合いを、貼り合わせの位相 𝔀 で書く
+アーデル射影幾何 — Part 262（PAG266、短期層の小さいノート、2026-11-20）：舞台 P¹ の赤道の絡み合いの係数を 𝔀（`rootNum`）で書く
 
 問いの出所：基礎文書の索引 1.4（舞台は P¹）と 2.4（「射影」の変換）の留保「`JH` は P¹ の上の作用素ではなく、P¹ のモデルと結ぶ Lean の文はない」。
 - 推薦案 `pag2_p1_gluing_preregistration.md` §4 を、2026-11-20 06:55 に著者が採用した（「進めてください」）。
 - 著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」の読みの材料（読みの地位は変えない）。
+- この文書の文に `JH` は現れない。Lean で結んだのは 𝔀（`rootNum`）の値と P¹ の赤道の係数で、留保「`JH` と P¹ のモデルを結ぶ Lean の文はない」はこの文書の後も残る。
 
 記号：
-- N = p^(n+1)（p は素数）。e = stdAddChar、τ(χ) = gaussSum χ e。J = `PAG.Part7.J`（ヤコビ和）、Ĵ = J/√N（`PAG.Part25.Jhat`）。
+- N = p^(n+1)（p は素数）は指標の法。定理の P¹ のモデルの法は p^K で、N とは別（K > n+1 なら値も違う）。e = stdAddChar、τ(χ) = gaussSum χ e。J = `PAG.Part7.J`（ヤコビ和）、Ĵ = J/√N（`PAG.Part25.Jhat`）。
 - 𝔀(χ) = `PAG.Part256.rootNum` χ = τ(χ)/(i^a √N)（偶なら a = 0、奇なら a = 1）。原始指標でルート数であることは Lean の外。
+  𝔀 は `rootNum` の docstring で W(χ) と書かれている値。B_N の定義に入る反転 `PAG.Part23.W`（南北の入れ替え）と区別して 𝔀 と書く。
 - P¹(ℤ/p^K) の 2 チャートのモデル、南北の畳み込み B_S・B_N、赤道のケット |0, χ⟩ = `PAG.Part23.kS K 0 (n+1) h χ`（Part 19（PAG23））。
+- 扱うのは殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ。係数は K によらない。
 
 主な定理（χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標のとき）：
 1. conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))（`conj_Jhat_eq_gauss`）。
-2. conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))、s は χ₁ か χ₂ が偶なら 1、両方とも奇なら −1（`conj_Jhat_eq_rootNum`）。
+2. conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))、s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1（`conj_Jhat_eq_rootNum`）。
 3. conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²（`conj_Jhat_sq_eq_rootNum`）。
-4. 赤道のケットについて B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)（`equator_intertwine_rootNum`、2 チャートのモデル）。
-5. 同じ式を、射影直線そのもの（`PAG.Part27.ProjLine`）の上の関数として（`equator_intertwine_proj_rootNum`、Part 25（PAG29）の `equator_intertwine_proj` から）。
+4. n + 1 ≤ K のとき、赤道のケットについて B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)（`equator_intertwine_rootNum`、2 チャートのモデル）。
+5. 4 の両辺を `projFunEquiv`（Part 24（PAG28）の ℂ 線形同型：`PAG.Part27.ProjLine (p^K)` 上の関数 ≃ 貼り合わせ条件を満たす組）で移した形（`equator_intertwine_proj_rootNum`、Part 25（PAG29）の `equator_intertwine_proj` から）。
+   5 は 4 と同値（`projFun_*` と線形性による手の論証。Lean の文にはしていない）。点 [x:1]・[1:y] での値としての読みは `projEquiv`（Part 23（PAG27））と `ptEquiv`（Part 22（PAG26））による。
 
-読み（Lean の外）：χ の成分に 𝔀(χ) を掛ける作用素を U とすると、4 は赤道のケットの上で B_N(k₁, k₂) = U² B_S(U⁻²k₁, U⁻²k₂) と読める。
-この条件を満たす位相は 𝔀 だけではない（単数 u と指標ごとの符号の分。数値と照合者の手計算、`pag2_p1_gluing_preregistration.md`）。
+読み（Lean の外）：原始指標 χ の成分に、導手 p^(n+1) で計算した 𝔀(χ) を掛ける作用素を U とする（法 p^K の指標として計算すると、K > n+1 では τ = 0 になるため）。
+B_S(|0,χ₁⟩, |0,χ₂⟩) が χ₁χ₂ の成分に入ること（この文書の文にはない）と合わせて、4 は赤道のケットの上で B_N(k₁, k₂) = U² B_S(U⁻²k₁, U⁻²k₂) と読める。
+この条件を満たす位相は 𝔀 だけではない（少なくとも、単数 u による √χ(u) の分と指標ごとの符号 ±1 の分がある。数値と照合者の手計算、`pag2_p1_gluing_preregistration.md`）。
 A1 は導かれない。p = 2（すべての n）と p = 3、n = 0 では原始指標の三つ組がなく、5 つの文は空（独立照合の指摘。p = 2 は Part 26（PAG30）の注意とも合う）。
 仮定は必要十分ではない：1〜3 では χ₁χ₂ の原始性は不要に見え、χ₁・χ₂ の原始性が中身を運ぶのは n = 0 だけ（n ≥ 1 では両辺が 0 になる。独立照合の手計算）。
-4・5 では χ₁χ₂ の原始性が要る（単数でない点で両辺が 0 になる部分）。4・5 は Part 21・25 の定理の係数の書き換えで、絡み合いの中身はそちらにある。
+4・5 では χ₁χ₂ の原始性を外すと偽になる（独立照合の反例）。反例は単数でない点（n = 1）にも、単数の点（n = 0、χ₂ = χ̄₁、x = 1）にも出る。
+単数の点での比 B_N/B_S は conj(J)/J で、conj(Ĵ)² に等しいのは |J|² = N のとき（Lean の外。再照合者の手計算と数値 `records/audit266/numeric/unit_point_ratio.py`、K = n+1 の場合）。
+4・5 は Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換えで、絡み合いの中身はそちらにある（名前空間 `PAG.Part25` は Part 21（PAG25）を指し、Part 25（PAG29）とは別）。
 
-ラベル（見込み、照合の後に確定）：1〜3 は［既知］（積が原始的ならヤコビ和はガウス和の比、|τ|² = N。Conrad の定理 3.15・3.12）、4・5 は［再導出（小さい）］。新規候補なし。
+ラベル（見込み、照合の後に確定）：1〜3 は［既知］（積が原始的ならヤコビ和はガウス和の比、|τ|² = N。K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15・3.12。法 m は一般で ℤ/p^(n+1) を覆う（WebFetch の要約で確認））、4・5 は［再導出（小さい）］。新規候補なし。
 -/
 import PAG265
 import PAG25
@@ -69,7 +76,7 @@ theorem conj_Jhat_eq_gauss (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
 
 open Classical in
 /-- **2. 𝔀 による形（2 乗を外した形）**：χ₁・χ₂・χ₁χ₂ が原始的なら、
-conj(Ĵ(χ₁, χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))。符号 s は、χ₁ か χ₂ が偶なら 1、両方とも奇なら −1
+conj(Ĵ(χ₁, χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))。符号 s は、χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1
 （𝔀 = `PAG.Part256.rootNum`、τ/(i^a √N)）。符号 s は、Ĵ（i^a を含まない）と 𝔀（i^a を含む）の正規化の違いから来る
 （加法指標の向きや i^a を (−i)^a に替えても変わらない。独立照合の手計算）。 -/
 theorem conj_Jhat_eq_rootNum (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
@@ -113,7 +120,8 @@ theorem conj_Jhat_eq_rootNum (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))
     field_simp
     rw [Complex.I_sq]; ring
 
-/-- **3. 2 乗の形**：χ₁・χ₂・χ₁χ₂ が原始的なら、conj(Ĵ(χ₁, χ₂))² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²。 -/
+/-- **3. 2 乗の形**：χ₁・χ₂・χ₁χ₂ が原始的なら、conj(Ĵ(χ₁, χ₂))² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²。
+2 乗で定理 2 の符号 s は落ちる（4・5 も同じ）。 -/
 theorem conj_Jhat_sq_eq_rootNum (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
     (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
     (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2
@@ -125,7 +133,7 @@ theorem conj_Jhat_sq_eq_rootNum (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n +
 P¹(ℤ/p^K) の 2 チャートのモデルの赤道のケット |0, χ⟩ について、
 B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)
 （Part 21（PAG25）の `equator_intertwine_hat` と 3 から）。この定理は `equator_intertwine_hat` の係数 conj(Ĵ)² を 3 で書き換えたもので、
-絡み合いの中身（単数でない点で両辺が 0 になることを含む）は Part 21 にある。 -/
+絡み合いの中身（単数でない点で両辺が 0 になることを含む）は Part 21（PAG25）にある。 -/
 theorem equator_intertwine_rootNum (K : ℕ) (h : 0 + (n + 1) ≤ K)
     (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
     (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
@@ -134,9 +142,11 @@ theorem equator_intertwine_rootNum (K : ℕ) (h : 0 + (n + 1) ≤ K)
           • PAG.Part23.BS (PAG.Part23.kS K 0 (n + 1) h χ₁) (PAG.Part23.kS K 0 (n + 1) h χ₂) := by
   rw [PAG.Part25.equator_intertwine_hat K h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]
 
-/-- **5. 射影直線そのものの上の形**：Part 25（PAG29）の `equator_intertwine_proj`（射影直線 P¹(ℤ/p^K) = `PAG.Part27.ProjLine` の上の
-関数としての南北の畳み込み B_S^proj・B_N^proj と赤道のケット）について、4 と同じ式が成り立つ。`equator_intertwine_proj` の係数を
-3 で書き換えたもの。1 ≤ K は h から出るので、仮定に置かない（独立照合の指摘で外した）。 -/
+/-- **5. 射影直線の上の関数に移した形**：4 の両辺を `projFunEquiv`（Part 24（PAG28）。`PAG.Part27.ProjLine (p^K)` 上の関数と、
+貼り合わせ条件を満たす組との ℂ 線形同型）で移した等式。B_S^proj・B_N^proj は Part 24（PAG28）、ketS_proj は Part 25（PAG29）で、
+2 チャートの版をこの同型で移して定義したもの。Part 25（PAG29）の `equator_intertwine_proj` の係数を 3 で書き換えたもの。
+5 は 4 と同値（`projFun_*` と線形性による。Lean の文にはしていない）。点 [x:1]・[1:y] での値としての読みは `projEquiv`・`ptEquiv` による。
+1 ≤ K は h から出るので、仮定に置かない（独立照合の指摘で外した）。 -/
 theorem equator_intertwine_proj_rootNum (K : ℕ) (h : 0 + (n + 1) ≤ K)
     (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
     (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
index 252dcf6..b1487f0 100644
--- a/handoff/PAG2_handoff_part259.md
+++ b/handoff/PAG2_handoff_part259.md
@@ -1708,3 +1708,11 @@
   - 条件 5 の狭い形：第 5 章が Lean の名前で書けるのは PAG265 が形式化した範囲（`DirectedSystem` の構造と、代数的な帰納極限としての `CornerLim`）まで。像 = 角、Bost–Connes との対応、随伴を保つことは Lean の外の地位で書く（索引 5.5 に書いた）。
   - 台帳 L1〜L5 は開いたまま、次の統合照合の対象として受理された。
 
+- **Part 262（PAG266、短期層、2026-11-20）**：20:19 の「構築を進めてください」を受けて、舞台 P¹ の上の貼り合わせを関門にかけ（`notes/pag2_p1_gluing_preregistration.md`）、推薦案を著者が 06:55 に採用した（「進めてください」）。
+  - Lean：定理 5 個（sorry 0、警告 0、#print axioms は標準の 3 つ）。χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は両方とも奇のときだけ −1）、2 乗の形、n + 1 ≤ K のとき赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと、`projFunEquiv` で射影直線の上の関数に移した形）。
+  - 範囲：殻 0 と導手がちょうど p^(n+1) の指標の組だけ。p = 2 と p = 3、n = 0 では文は空。作用素の形は Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換え。`JH` と P¹ のモデルを結ぶ文ではなく、索引 2.4 の留保は残る。
+  - 読み（Lean の外）：B_N = U² B_S U⁻²（U は導手で計算した 𝔀 を掛ける作用素）。条件は U を有限個の候補に絞るが選ばず、A1 は導かれない。関数体の本来のルート数は一般にこの条件を満たさない（ℚ に固有の小さな観察、確信度：中）。P¹ の 0・∞ を定義の「無限小と無限大」と結ぶ読みは著者の判断が先。
+  - ラベル：1〜3 が［既知］（Conrad の定理 3.15・3.12、法 m は一般）、4・5 が［再導出（小さい）］。新規候補なし。兆候 4 は続く。
+  - 照合：内部照合（機械的 200 回で一致なし、言葉の検索で Part 21・25 の定理を使った）、独立照合（形式文と定義だけ）、再照合（独立照合の出力・直した後の全文・差分・定義）。再照合の後の直しは文面のみ（形式文は変えていない）で、尾の台帳の L6。
+  - 件数：鎖全体の定理・補題は 3,695 件（3,690 + 5）。xlsx は final84（行 2〜3723）。
+  - 閉じる条件：統合照合（Part 262 の材料と台帳の L1〜L6）。その照合を受けるまで、Part 262 は閉じていない。
diff --git a/notes/pag2_founding_material_index.md b/notes/pag2_founding_material_index.md
index 3dc34ae..e0a9086 100644
--- a/notes/pag2_founding_material_index.md
+++ b/notes/pag2_founding_material_index.md
@@ -120,8 +120,9 @@
 - 留保：
   - `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。
   - P¹ のモデルと結ぶ Lean の文（Part 262（PAG266）、2026-11-20、短期層）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、P¹(ℤ/p^K) の赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデル `PAG.Part266.equator_intertwine_rootNum`、射影直線 `PAG.Part266.equator_intertwine_proj_rootNum`）。係数の等式 conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は両方とも奇のときだけ −1）は `PAG.Part266.conj_Jhat_eq_rootNum`、2 乗の形は `PAG.Part266.conj_Jhat_sq_eq_rootNum`、ガウス和の形は `PAG.Part266.conj_Jhat_eq_gauss`。
-    - 範囲：p = 2（すべての n）と p = 3、n = 0 では文は空。4・5（作用素の形）は Part 21・25 の定理の係数の書き換えで、絡み合いの中身はそちらにある。
-    - 読み（Lean の外）：χ の成分に 𝔀 を掛ける作用素を U とすると、北の畳み込みは南の畳み込みを U² で移したもの。この条件は U を有限個の候補（単数 u と指標ごとの符号の分）に絞るが選ばず、A1 は導かれない。関数体では本来のルート数が一般にこの条件を満たさない（ℚ に固有の小さな観察、確信度：中）。P¹(ℤ/N) の 0・∞ を定義の「無限小と無限大」と結ぶ読みは構築側の候補（著者の判断が先）。ノート `pag2_pag266_p1_equator_rootnum.md`。
+    - 範囲：殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ（係数は K によらない）。p = 2（すべての n）と p = 3、n = 0 では文は空。作用素の形の 2 つは Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換えで、絡み合いの中身はそちらにある。射影直線の版は 2 チャートの版を `projFunEquiv`（Part 24（PAG28））で移したもので、2 チャートの版と同値（手の論証）。
+    - このパートの文に `JH` は現れない。Lean で結んだのは 𝔀 の値と P¹ の赤道の係数で、上の留保（`JH` は P¹ の上の作用素ではない）は残る。
+    - 読み（Lean の外）：原始指標 χ の成分に導手で計算した 𝔀 を掛ける作用素を U とすると、B_S(|0,χ₁⟩, |0,χ₂⟩) が χ₁χ₂ の成分に入ることと合わせて、赤道で北の畳み込みは南の畳み込みを U² で移したもの。この条件は U を有限個の候補（少なくとも単数 u と指標ごとの符号の分がある）に絞るが選ばず、A1 は導かれない。関数体では本来のルート数が一般にこの条件を満たさない（ℚ に固有の小さな観察、確信度：中）。P¹(ℤ/N) の 0・∞ を定義の「無限小と無限大」と結ぶ読みは構築側の候補（著者の判断が先）。ノート `pag2_pag266_p1_equator_rootnum.md`。
   - 原始指標で 𝔀 がルート数であることは Lean の外。
   - 素朴なフーリエ核 e(xy) では値が τ(χ)/√N で、奇の指標で i 倍ずれる。このずれは滑らかにしない。
 - ノート：`pag2_part252_hartley_gluing.md`、`pag2_projection_material.md`、`pag2_prereg_projection.md`。
diff --git a/notes/pag2_pag266_p1_equator_rootnum.md b/notes/pag2_pag266_p1_equator_rootnum.md
index 7ec6a64..2f4c0b0 100644
--- a/notes/pag2_pag266_p1_equator_rootnum.md
+++ b/notes/pag2_pag266_p1_equator_rootnum.md
@@ -1,4 +1,4 @@
-# アーデル射影幾何 — Part 262（PAG266、短期層の小さいノート）：舞台 P¹ の赤道の絡み合いを、貼り合わせの位相 𝔀 で書く
+# アーデル射影幾何 — Part 262（PAG266、短期層の小さいノート）：舞台 P¹ の赤道の絡み合いの係数を 𝔀（`rootNum`）で書く
 
 （2026-11-20。推薦案 `pag2_p1_gluing_preregistration.md` §4 を、06:55 に著者が採用した。）
 
@@ -6,36 +6,38 @@
 
 - 基礎文書の索引 1.4（舞台は P¹）と 2.4（「射影」の変換）の留保：`JH` は P¹ の上の作用素ではなく、P¹ のモデルと結ぶ Lean の文がない。
 - 著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」の読みの材料。読みの地位は変えない。
+- このパートの文に `JH` は現れない。Lean で結んだのは 𝔀（`rootNum`）の値と P¹ の赤道の係数で、留保「`JH` と P¹ のモデルを結ぶ Lean の文はない」はこのパートの後も残る（再照合の指摘）。
 
 ## §2 Lean に入った文（PAG266.lean、定理 5、sorry 0・警告 0、#print axioms は標準の 3 つ）
 
-記号：N = p^(n+1)（p は素数）。τ(χ) = gaussSum χ stdAddChar。J = ヤコビ和 `PAG.Part7.J`、Ĵ = J/√N（`PAG.Part25.Jhat`）。𝔀 = `PAG.Part256.rootNum` = τ/(i^a √N)。
+記号：N = p^(n+1)（p は素数）は指標の法。定理の P¹ のモデルの法は p^K で、N とは別（K > n+1 なら値も違う）。τ(χ) = gaussSum χ stdAddChar。J = ヤコビ和 `PAG.Part7.J`、Ĵ = J/√N（`PAG.Part25.Jhat`）。𝔀 = `PAG.Part256.rootNum` = τ/(i^a √N)。𝔀 は `rootNum` の docstring で W(χ) と書かれている値で、B_N の定義に入る反転 `PAG.Part23.W`（南北の入れ替え）と区別して 𝔀 と書く。
+扱うのは殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ。係数は K によらない。
 
 χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標のとき：
 
 1. `conj_Jhat_eq_gauss`：conj(Ĵ(χ₁, χ₂)) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))。
-2. `conj_Jhat_eq_rootNum`：conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))。s は χ₁ か χ₂ が偶なら 1、両方とも奇なら −1。
-3. `conj_Jhat_sq_eq_rootNum`：conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²。
+2. `conj_Jhat_eq_rootNum`：conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))。s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1。
+3. `conj_Jhat_sq_eq_rootNum`：conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²。2 乗で 2 の符号 s は落ちる（4・5 も同じ）。
 4. `equator_intertwine_rootNum`：n + 1 ≤ K のとき、P¹(ℤ/p^K) の 2 チャートのモデルの赤道のケット |0, χ⟩ について、B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)。
-5. `equator_intertwine_proj_rootNum`：同じ式を、射影直線 P¹(ℤ/p^K)（`PAG.Part27.ProjLine`）の上の関数としての南北の畳み込みと赤道のケットについて。
+5. `equator_intertwine_proj_rootNum`：4 の両辺を `projFunEquiv`（Part 24（PAG28）の ℂ 線形同型：`PAG.Part27.ProjLine (p^K)` 上の関数 ≃ 貼り合わせ条件を満たす組）で移した形。B_S^proj・B_N^proj は Part 24（PAG28）、ketS_proj は Part 25（PAG29）で、2 チャートの版をこの同型で移して定義したもの。5 は 4 と同値（`projFun_*` と線形性による手の論証、再照合者が確かめた。Lean の文にはしていない）。点 [x:1]・[1:y] での値としての読みは `projEquiv`（Part 23（PAG27））と `ptEquiv`（Part 22（PAG26））による。
 
 範囲と仮定の効き方（独立照合の指摘）：
 - p = 2（すべての n）と p = 3、n = 0 では、仮定を満たす指標の組がなく、5 つの文は空。仮定を満たす例があるのは、p ≥ 5 の n = 0 と、奇素数 p の n ≥ 1。
-- 仮定は必要十分ではない。1〜3 では χ₁χ₂ の原始性は不要に見え、χ₁・χ₂ の原始性が中身を運ぶのは n = 0 だけ（n ≥ 1 では両辺が 0 になる。照合者の手計算）。4・5 では χ₁χ₂ の原始性が要る（単数でない点で両辺が 0 になる部分）。
+- 仮定は必要十分ではない。1〜3 では χ₁χ₂ の原始性は不要に見え、χ₁・χ₂ の原始性が中身を運ぶのは n = 0 だけ（n ≥ 1 では両辺が 0 になる。照合者の手計算）。4・5 では χ₁χ₂ の原始性を外すと偽になる（独立照合の反例）。反例は単数でない点（n = 1）にも、単数の点（n = 0、χ₂ = χ̄₁、x = 1）にも出る。単数の点での比 B_N/B_S は conj(J)/J で、conj(Ĵ)² に等しいのは |J|² = N のとき（再照合者の手計算。数値 `records/audit266/numeric/unit_point_ratio.py`：K = n+1、(p, K) = (5,1), (7,1), (3,2), (5,2) で、単数の点の比はすべての組で conj(J)/J、χ₁χ₂ が原始的でない組 8 組では conj(Ĵ)² と一致しない）。
 - 4・5 は、Part 21（PAG25）の `equator_intertwine_hat` と Part 25（PAG29）の `equator_intertwine_proj` の係数 conj(Ĵ)² を 3 で書き換えたもの。絡み合いの中身（単数でない点で両辺が 0 になることを含む）はそちらにある。
 - 符号 s は、Ĵ（i^a を含まない）と 𝔀（i^a を含む）の正規化の違いから来る。加法指標の向きを変えても、i^a を (−i)^a に替えても変わらない（照合者の手計算）。
 
 ## §3 読み（Lean の外）
 
-- χ の成分に 𝔀(χ) を掛ける作用素を U とすると、4 は赤道のケットの上で B_N(k₁, k₂) = U² B_S(U⁻²k₁, U⁻²k₂) と読める。0 の近く（南）の加法の構造が、重なり（赤道）で U² によって ∞ の近く（北）の加法の構造に移される。
-- この条件を満たす位相は 𝔀 だけではない（推薦案 §3 の盲検の手計算と、構築側の数値 N ≤ 49）：φ(χ) = ε(χ)·𝔀(χ)·√χ(u)（ε は指標ごとの符号、u は単数）、数は φ(N)·2^{原始指標の数}。単数倍 v は u を u·v² に動かすので、単数倍と符号で届くのは u が平方のファイバーだけ。素朴な核の位相 τ/√N は u = −1 の解。
+- 原始指標 χ の成分に、導手 p^(n+1) で計算した 𝔀(χ) を掛ける作用素を U とする（法 p^K の指標として計算すると、K > n+1 では τ = 0 になるため）。B_S(|0,χ₁⟩, |0,χ₂⟩) が χ₁χ₂ の成分に入ること（このパートの文にはない）と合わせて、4 は赤道のケットの上で B_N(k₁, k₂) = U² B_S(U⁻²k₁, U⁻²k₂) と読める。0 の近く（南）の加法の構造が、重なり（赤道）で U² によって ∞ の近く（北）の加法の構造に移される。
+- この条件を満たす位相は 𝔀 だけではない（少なくとも次の分がある。推薦案 §3 の盲検の手計算と、構築側の数値 N ≤ 49）：φ(χ) = ε(χ)·𝔀(χ)·√χ(u)（ε は指標ごとの符号、u は単数）、数は φ(N)·2^{原始指標の数}。単数倍 v は u を u·v² に動かすので、単数倍と符号で届くのは u が平方のファイバーだけ。素朴な核の位相 τ/√N は u = −1 の解。
 - A1 は導かれない。P¹ の 2 チャートの構造は U を有限個の候補に絞るが、選ばない。「P¹ の構造が A1 を導いた」とは書かない。
 - 対照群：関数体 F_p[t]/(t^e) でも代数の部分は同じ形（数値）。ただし関数体の本来のルート数（奇の指標では ∞ の局所因子として F_q 上のガウス和が入る）は、一般にこの条件を満たさない（照合者の文献と、構築側の数値：F_7[t]/(t²) で三つ組 1080 組中 600 組が外れる）。ℚ で 𝔀 が条件を満たすのは、無限素点の比が ±1 で 2 乗すると 1 になるから。小さいが ℚ に固有の観察（確信度：中）。
 - P¹(ℤ/N) の 0（南、無限小の側）と ∞（北、無限大の側）を、著者の定義の「無限素点では無限大と無限小が重なり合う」と結ぶ読みは、構築側の候補にとどめる（著者の判断が先）。
 
 ## §4 ラベル
 
-- 1〜3：［既知］。積が原始的ならヤコビ和はガウス和の比（K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15）、|τ|² = N（同 定理 3.12）。符号つきの形は Long–Pigno–Pinner（arXiv:1410.6179）の式 (10) と、その出典の Zhang–Yao（Acta Arith. 115, 2004）が挙がっている（盲検の照合者による。原文は構築側で確かめていない）。
+- 1〜3：［既知］。積が原始的ならヤコビ和はガウス和の比（K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15）、|τ|² = N（同 定理 3.12）。どちらも法 m は一般で ℤ/p^(n+1) を覆う（定理 3.15 は積の原始性だけを仮定する。WebFetch の要約で確認、2026-11-20）。符号つきの形は Long–Pigno–Pinner（arXiv:1410.6179）の式 (10) と、その出典の Zhang–Yao（Acta Arith. 115, 2004）が挙がっている（盲検の照合者による。原文は構築側で確かめていない）。
 - 4・5：［再導出（小さい）］。既存の定理の係数の書き換え。
 - 新規候補なし。兆候 4（初等的な部品の組み合わせだけ）は続いている。
 
@@ -48,7 +50,8 @@
 
 - 独立照合（形式文と定義だけ、`records/audit266/outputs/check_output.md`、約 454 秒）：逆翻訳は意図どおり。非空虚性の証人は p ≥ 5 の n = 0 と奇素数の n ≥ 1 にある。除去テストで、原始性（n = 0）・符号の場合分け・2 乗のどれを外しても反例がある。指摘：空になる範囲、仮定の効き方、4・5 は係数の書き換え、定理 5 の 1 ≤ K は冗長、記号 W の衝突、`projFunEquiv` が入力になかった。
 - 直したこと：docstring と冒頭の説明に、空になる範囲・仮定の効き方・係数の書き換えであることを書いた。定理 5 から 1 ≤ K の仮定を外した（h から出る）。
-- 再照合：（結果をここに書く。）
+- 再照合（独立照合の出力の全文・直した後の PAG266.lean の全文・形式文の差分・定義を入力、`records/audit266/outputs/recheck_output.md`、約 425 秒）：形式文の変更（定理 5 の hK を外した）は意味を変えない（確信度：高）。独立照合の指摘は、直った・一部・直っていないに分けられた。直っていなかったのは、定理 3〜5 で符号 s が落ちることの断り。新しい指摘（重要度順）：定理 5 の「射影直線そのもの」は強い（5 は 4 と同値で、足す内容は `projEquiv`・`ptEquiv` が正しい点の対応であることだけ）、4・5 の原始性の括弧が狭い（単数の点でも反例）、`JH` はこの文書に現れない、題と読みの行（U は導手で計算した 𝔀、B_S が χ₁χ₂ の成分に入る前提）、Part 番号の書き方、𝔀 と W、範囲の明記、Conrad の範囲。
+- 再照合の後の直し：上の指摘 1〜9 を、Lean の冒頭の説明と docstring・このノート・xlsx・索引に同じ文面で入れた。形式文は変えていない（差分で確認、ビルドは sorry 0・警告 0）。Conrad の範囲は WebFetch で確かめた。単数の点の比は数値で確かめた。**この直しはまだ照合を受けていないので、台帳に L6 として残し、閉じるときの統合照合の入力に含める。**
 
 ## §7 収束アラームの報告
 
diff --git a/notes/pag2_tail_ledger.md b/notes/pag2_tail_ledger.md
index bade289..08d5b5b 100644
--- a/notes/pag2_tail_ledger.md
+++ b/notes/pag2_tail_ledger.md
@@ -39,6 +39,12 @@
   - 補足 15 との照らし合わせ（2026-11-19 夜）：`files/handoff-to-builder-20261119-supplement15.md` の追加、`notes/pag2_supplement15_check.md`、索引 5.5 の一意性の行（3 条件の形）と照合の行、索引 5.5 の Lean の外の列挙への随伴の追加・第 5 章で Lean の名前で書ける範囲の行・補足 15 との関係の行（20:17 の著者の確定の記録）、Part 260 のノートの §9 の 2 行、Part 261 のノートの 1 行、この台帳の L3〜L5、引き継ぎメモの項。
 - 扱い：次の統合照合の対象。
 
+### L6：Part 262（PAG266）の再照合の後の直し（2026-11-20 朝）
+
+- 範囲：再照合（`records/audit266/outputs/recheck_output.md`）の指摘 1〜9 を受けた直し。PAG266 の冒頭の説明と docstring（形式文は変えていない）、ノート `pag2_pag266_p1_equator_rootnum.md`（題、§1、§2、§3、§4、§6）、xlsx の Part 262 の行、索引 1.4・2.4 の Part 262 の行、辞書 §20。数値 `records/audit266/numeric/unit_point_ratio.py` を足した。
+- 自己申告（根拠にしない）：言い過ぎの狭め（定理 5 の「そのもの」、題）と、前提・範囲・出典の明記。主張は足していないつもりだが、単数の点の比の文（conj(J)/J）は新しく書いた内容である。
+- 扱い：Part 262 を閉じるときの統合照合の入力に含める（L1〜L5 と同じ照合）。
+
 ## 閉じた項目
 
 - 2026-11-19 夕方の索引の尾（第 5 版の後の追加）：統合照合・再照合・2 回目の再照合を受けた（`records/tail_audit4/`）。2 回目の再照合の後の直しは L1 として残る。
diff --git a/notes/pag2_terwilliger_dictionary.md b/notes/pag2_terwilliger_dictionary.md
index f023b34..021f3d0 100644
--- a/notes/pag2_terwilliger_dictionary.md
+++ b/notes/pag2_terwilliger_dictionary.md
@@ -466,8 +466,8 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
 
 | 名前・主張 | 文献の言葉 | 出典・注意 |
 |---|---|---|
-| `conj_Jhat_eq_gauss`・`conj_Jhat_eq_rootNum`・`conj_Jhat_sq_eq_rootNum` | ヤコビ和はガウス和の比 J = G₁G₂/G₁₂（積が原始的なとき）と |G|² = N。位相 conj(Ĵ) はガウス和の位相の余境界（2 乗で符号が消える） | K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15・3.12。符号つきの形は Long–Pigno–Pinner（arXiv:1410.6179）の式 (10)（盲検の照合者による） |
-| `equator_intertwine_rootNum`・`equator_intertwine_proj_rootNum` | P¹(ℤ/p^K) の 2 チャートの畳み込みの、重なりでの比較（この設定の文献の名前は見つからなかった） | Part 21・25 の定理の係数の書き換え。設定そのものは盲検の 1 回の検索では見つからなかった |
+| `conj_Jhat_eq_gauss`・`conj_Jhat_eq_rootNum`・`conj_Jhat_sq_eq_rootNum` | ヤコビ和はガウス和の比 J = G₁G₂/G₁₂（積が原始的なとき）と |G|² = N。位相 conj(Ĵ) はガウス和の位相の余境界（2 乗で符号が消える） | K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15・3.12（法 m は一般。WebFetch の要約で確認）。符号つきの形は Long–Pigno–Pinner（arXiv:1410.6179）の式 (10)（盲検の照合者による） |
+| `equator_intertwine_rootNum`・`equator_intertwine_proj_rootNum` | P¹(ℤ/p^K) の 2 チャートの畳み込みの、重なりでの比較（この設定の文献の名前は見つからなかった） | Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換え。射影直線の版は 2 チャートの版を `projFunEquiv` で移したもので同値。設定そのものは盲検の 1 回の検索では見つからなかった |
 | 条件「U'² が赤道で B_S を B_N に移す」の解の集まり（Lean の外） | 部分群の補集合の上で乗法的な関数は準同型に延びる（|X/Y| ≥ 3）、ポントリャーギン双対 | 盲検の照合者の手計算（補題を書いた文献は探していない）。加法指標の取り替えで局所定数が χ(b) 倍になること（Tate、Biswas arXiv:1401.5591 §4.3） |
 
 - 未記入の件数（この節）：0。
diff --git a/records/audit266/numeric/unit_point_ratio.log b/records/audit266/numeric/unit_point_ratio.log
new file mode 100644
index 0000000..d406c44
--- /dev/null
+++ b/records/audit266/numeric/unit_point_ratio.log
@@ -0,0 +1,4 @@
+p=5 K=1: 組（J≠0）9、単数の点で比 = conj(J)/J：9、比 = conj(Ĵ)²：6、うち χ₁χ₂ が原始的でない組 3（比 = conj(Ĵ)² は 0）
+p=7 K=1: 組（J≠0）25、単数の点で比 = conj(J)/J：25、比 = conj(Ĵ)²：20、うち χ₁χ₂ が原始的でない組 5（比 = conj(Ĵ)² は 0）
+p=3 K=2: 組（J≠0）8、単数の点で比 = conj(J)/J：8、比 = conj(Ĵ)²：8、うち χ₁χ₂ が原始的でない組 0（比 = conj(Ĵ)² は 0）
+p=5 K=2: 組（J≠0）192、単数の点で比 = conj(J)/J：192、比 = conj(Ĵ)²：192、うち χ₁χ₂ が原始的でない組 0（比 = conj(Ĵ)² は 0）
diff --git a/records/audit266/numeric/unit_point_ratio.py b/records/audit266/numeric/unit_point_ratio.py
new file mode 100644
index 0000000..c607dcd
--- /dev/null
+++ b/records/audit266/numeric/unit_point_ratio.py
@@ -0,0 +1,40 @@
+"""再照合の指摘 2 の確認（数値。証明ではない）。2026-11-20。
+PAG23 の定義どおり：BS(F,G) = extS(conv F.1 G.1)、BN(F,G) = extN(conv F.2 G.2)、kS = extS(ket)、殻 0 のケットは χ(x)（正規化は両辺に共通なので省く）。
+単数の点 x での BN.1(x)/BS.1(x) が conj(J)/J に等しいか、conj(Ĵ)² と比べる。χ₁χ₂ が原始的でない組（χ₂ = χ̄₁ など）を含める。
+"""
+import math, cmath, sys
+sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/p1_gluing')
+from equator_U_check import characters, is_primitive, mul, J
+import numpy as np
+
+def run(p, K):
+    N = p ** K
+    U = [x for x in range(N) if math.gcd(x, N) == 1]
+    chars = characters(N); prim = [c for c in chars if is_primitive(N, c, p)]
+    def ev(c, x): return c.get(x % N, 0.0)
+    def inv(x): return pow(x, -1, N)
+    def extS(h): return (h, {y: (h[inv(y)] if y in U else 0.0) for y in range(N)})
+    def extN(h): return ({x: (h[inv(x)] if x in U else 0.0) for x in range(N)}, h)
+    def conv(f, g): return {x: sum(f[y] * g[(x - y) % N] for y in range(N)) for x in range(N)}
+    tot = ok_ratio = eq_sq = 0; nonprim12 = 0; nonprim12_eqsq = 0
+    for c1 in prim:
+        for c2 in prim:
+            k1 = extS({x: ev(c1, x) for x in range(N)}); k2 = extS({x: ev(c2, x) for x in range(N)})
+            BS = extS(conv(k1[0], k2[0])); BN = extN(conv(k1[1], k2[1]))
+            Jv = J(N, c1, c2)
+            if abs(Jv) < 1e-9: continue
+            r = [BN[0][x] / BS[0][x] for x in U if abs(BS[0][x]) > 1e-9]
+            tot += 1
+            ok_ratio += all(np.isclose(t, np.conj(Jv) / Jv) for t in r)
+            sq = (np.conj(Jv) / math.sqrt(N)) ** 2
+            same = all(np.isclose(t, sq) for t in r)
+            eq_sq += same
+            c12 = mul(c1, c2)
+            if not is_primitive(N, c12, p):
+                nonprim12 += 1; nonprim12_eqsq += same
+    print(f"p={p} K={K}: 組（J≠0）{tot}、単数の点で比 = conj(J)/J：{ok_ratio}、比 = conj(Ĵ)²：{eq_sq}、"
+          f"うち χ₁χ₂ が原始的でない組 {nonprim12}（比 = conj(Ĵ)² は {nonprim12_eqsq}）")
+
+if __name__ == '__main__':
+    for (p, K) in [(5, 1), (7, 1), (3, 2), (5, 2)]:
+        run(p, K)
diff --git a/records/audit266/update_xlsx_266.py b/records/audit266/update_xlsx_266.py
index a8e6cbb..32793a4 100644
--- a/records/audit266/update_xlsx_266.py
+++ b/records/audit266/update_xlsx_266.py
@@ -4,20 +4,20 @@ os.makedirs('/home/claude/out/final84', exist_ok=True)
 p = '/home/claude/out/final84/lean_verification_status.xlsx'
 shutil.copy(src, p)
 wb = openpyxl.load_workbook(p); ws = wb['定理と証明']
-LABEL = ('PAG2.0-262（PAG266、短期層の小さいノート）舞台 P¹ の赤道の絡み合いを、貼り合わせの位相 𝔀 で書く（推薦案 pag2_p1_gluing_preregistration.md、著者の採用 2026-11-20 06:55。'
+LABEL = ('PAG2.0-262（PAG266、短期層の小さいノート）舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く（推薦案 pag2_p1_gluing_preregistration.md、著者の採用 2026-11-20 06:55。'
  '基礎文書の索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める材料）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、'
- 'conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は χ₁ か χ₂ が偶なら 1、両方とも奇なら −1）、conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²、'
- '赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと射影直線の上）。ラベルは 1〜3 が［既知］、4・5 が［再導出（小さい）］')
+ 'conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1）、conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²、'
+ 'n + 1 ≤ K のとき赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと、projFunEquiv で射影直線の上の関数に移した形）。扱うのは殻 0 と導手がちょうど p^(n+1) の指標の組だけ。p = 2 と p = 3、n = 0 では文は空。`JH` と P¹ のモデルを結ぶ文ではない。ラベルは 1〜3 が［既知］、4・5 が［再導出（小さい）］')
 R = [
  ('conj_Jhat_eq_gauss', 'χ₁・χ₂・χ₁χ₂ が法 N = p^(n+1) の原始指標なら conj(Ĵ(χ₁, χ₂)) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))（Ĵ = J/√N、τ = gaussSum χ stdAddChar）',
   'J·conj J = N と、ガウス和の比はヤコビ和', 'PAG.Part15.gauss_ratio_eq_jacobi'),
- ('conj_Jhat_eq_rootNum', '同じ仮定で conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（𝔀 = rootNum = τ/(i^a √N)。s は χ₁ か χ₂ が偶なら 1、両方とも奇なら −1）',
+ ('conj_Jhat_eq_rootNum', '同じ仮定で conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（𝔀 = rootNum = τ/(i^a √N)。s は χ₁・χ₂ の少なくとも一方が偶なら 1、両方とも奇なら −1）',
   '1 と rootNum の定義、偶奇の 4 通りの場合分け（積の偶奇は χ(−1) の積）', 'MulChar.mul_apply'),
- ('conj_Jhat_sq_eq_rootNum', '同じ仮定で conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²（符号は 2 乗で消える）', '2 の 2 乗', 'conj_Jhat_eq_rootNum'),
+ ('conj_Jhat_sq_eq_rootNum', '同じ仮定で conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²（2 の符号 s は 2 乗で落ちる。4・5 も同じ）', '2 の 2 乗', 'conj_Jhat_eq_rootNum'),
  ('equator_intertwine_rootNum', 'n + 1 ≤ K のとき、P¹(ℤ/p^K) の 2 チャートのモデルの赤道のケット |0, χ⟩ について B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)',
-  'Part 21 の equator_intertwine_hat と 3', 'PAG.Part25.equator_intertwine_hat'),
- ('equator_intertwine_proj_rootNum', '同じ式を、射影直線 P¹(ℤ/p^K)（ProjLine）の上の関数としての南北の畳み込みと赤道のケットについて（1 ≤ K）',
-  'Part 25 の equator_intertwine_proj と 3', 'PAG.Part29.equator_intertwine_proj'),
+  'Part 21（PAG25）の equator_intertwine_hat と 3（係数の書き換え）', 'PAG.Part25.equator_intertwine_hat'),
+ ('equator_intertwine_proj_rootNum', '4 の両辺を projFunEquiv（Part 24（PAG28）の ℂ 線形同型：ProjLine (p^K) 上の関数 ≃ 貼り合わせ条件を満たす組）で移した形：BN_proj(ketS_proj χ₁, ketS_proj χ₂) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · BS_proj(…)。4 と同値（手の論証、Lean の文にはしていない）。1 ≤ K は h から出るので仮定にない',
+  'Part 25（PAG29）の equator_intertwine_proj と 3（係数の書き換え）', 'PAG.Part29.equator_intertwine_proj'),
 ]
 start = 3719
 ws.insert_rows(start, len(R))
@@ -36,7 +36,8 @@ for r in range(last + 1, ws.max_row + 1):
         old = 'Part 261（行 3709〜3718、PAG265.lean、短期層）'; assert old in v, v[-400:]
         v = v.replace(old, f'Part 261（行 3709〜3718、PAG265.lean、短期層）、Part 262（行 3719〜{last}、PAG266.lean、短期層）', 1)
         v = v.rstrip() + (f' 2026-11-20 朝、Part 262（PAG266.lean、短期層、舞台 P¹ の赤道の絡み合いを 𝔀 で書く）をコンパイルし、行 3719〜{last} を足した（定理 5 個）。'
-         '内部照合で、Part 21（PAG25）の equator_intertwine_hat と Part 25（PAG29）の equator_intertwine_proj を使った（言葉の検索）。')
+         '内部照合で、Part 21（PAG25）の equator_intertwine_hat と Part 25（PAG29）の equator_intertwine_proj を使った（言葉の検索）。'
+         '独立照合・再照合を受けた。再照合の後の直し（文面のみ、形式文は変えていない）は尾の台帳の L6 で、閉じるときの統合照合の対象。')
         ws.cell(r, 1).value = v
 ws2 = wb['検証手順']
 ws2.insert_rows(285, 1)
@@ -45,10 +46,10 @@ for c in range(1, 5):
     if s.has_style:
         d.font = copy.copy(s.font); d.alignment = copy.copy(s.alignment); d.border = copy.copy(s.border); d.fill = copy.copy(s.fill)
 ws2.cell(285, 1).value = 284
-ws2.cell(285, 2).value = 'PAG 2.0 Part 262（短期層）: PAG266.lean（舞台 P¹ の赤道の絡み合いを貼り合わせの位相 𝔀 で書く：ヤコビ和の共役のガウス和と 𝔀 による形、符号つきの 1 乗と 2 乗の形、2 チャートのモデルと射影直線の上の作用素の形）をコンパイル'
+ws2.cell(285, 2).value = 'PAG 2.0 Part 262（短期層）: PAG266.lean（舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く：ヤコビ和の共役のガウス和と 𝔀 による形、符号つきの 1 乗と 2 乗の形、2 チャートのモデルと射影直線の上の作用素の形）をコンパイル'
 ws2.cell(285, 3).value = '完了'
 ws2.cell(285, 4).value = ('2026-11-20 朝、推薦案 pag2_p1_gluing_preregistration.md（著者の採用 06:55）。定理 5 個、sorry 0、警告 0、#print axioms 5 行は標準の公理の範囲。'
- '内部照合（言葉の検索で Part 21 の equator_intertwine_hat と Part 25 の equator_intertwine_proj を使った。機械的な照合は全宣言 4490 件、対象 5 件、200 回で一致なし）。記録は records/audit266/。')
+ '内部照合（言葉の検索で Part 21 の equator_intertwine_hat と Part 25 の equator_intertwine_proj を使った。機械的な照合は全宣言 4490 件、対象 5 件、200 回で一致なし）。独立照合・再照合（記録は records/audit266/outputs/）。再照合の後の直しは尾の台帳の L6。')
 for row in ws2.iter_rows(min_row=286):
     for c in row:
         if isinstance(c.value, str) and 'COUNTIF($C$2:$C$284' in c.value:
```


## §F 着手前の文書 `notes/pag2_p1_gluing_preregistration.md`（全文、照合の対象）

```markdown
# アーデル射影幾何 — 舞台 P¹ の上の貼り合わせ：赤道の絡み合いと U の位相（着手前の 4 点、2026-11-19 夜）

（パートではない。Lean と xlsx は変えていない。数値は `records/p1_gluing/`。数値は証明ではない。）

## §0 問いの出所と内部照合

- **出所**：
  - 2026-11-19 20:19 に著者が「アーデル射影幾何学の構築を進めてください」と言い、構築側が次の一歩を関門に通すことにした（着手の決定ではない）。
  - 基礎文書の索引 1.4（舞台は P¹）と 2.4（「射影」の変換）の留保：`JH` は P¹ の上の作用素ではなく、照合した範囲では P¹ のモデルと結ぶ Lean の文がない。著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」のうち「その上で働く」が立っていない。CLAUDE.md §1 の「射影」の読みに仕える。
- **内部照合**（Lean の全宣言を言葉で検索し、宣言を読んで確かめた）：
  - P¹ の 2 チャートのモデル：`PAG.Part23.P1F`・`PAG.Part23.Compat`・`PAG.Part23.W`・南北の畳み込み `PAG.Part23.BS`・`PAG.Part23.BN`（Part 19（PAG23））。点モデル（Part 22（PAG26））、射影直線そのもの（Part 23（PAG27））。
  - 赤道の絡み合い：`PAG.Part24.equator_intertwine`（Part 20（PAG24）：B_N = (conj J / J) · B_S、赤道のケット、χ1・χ2・χ1χ2 が原始的）と `PAG.Part25.equator_intertwine_hat`（Part 21（PAG25）：= conj(Ĵ)² · B_S）。`PAG.Part25.normSq_J`（|J|² = p^c）。
  - ガウス和の比はヤコビ和：`PAG.Part15.gauss_ratio_eq_jacobi`（Part 11（PAG15））。|τ|² = N：`PAG.Part16.normSq_gaussSum`。𝔀：`PAG.Part256.rootNum`（Part 252（PAG256））。
  - 赤道の絡み合いと 𝔀 を結ぶ文は鎖にない。索引（第 6 版）は Part 20〜28（PAG24〜PAG32）の赤道の定理を拾っていなかった。

## §1 4 点

### (1) 幾何の言葉での問い

- 舞台 P¹ には 2 つのチャートがある：0 の近く（南、無限小の側）と ∞ の近く（北、無限大の側）。重なりは赤道（単数）。それぞれのチャートに加法の構造（畳み込み）がある。
- 問い：貼り合わせ U（「射影」の位相 𝔀）は、重なりで、0 の近くの加法の構造を ∞ の近くの加法の構造に移す作用素として現れるか。この条件は U をどこまで決めるか（A1 の位相は、その中のどれか）。

### (2) 既存分野の言葉への翻訳

- ヤコビ和はガウス和の比（τ1τ2 = J τ12、積が原始的なとき）。赤道の位相 conj J / J は、ガウス和の 2 乗の比（余境界）として書ける。
- 位相の集まりの記述は、原始指標の上の乗法的な関数（巡回群・有限アーベル群の双対、ポントリャーギン双対）。単数倍 R_a は南北の畳み込みの自己同型。

### (3) 残余

数値（`equator_U_check.log`、`equator_solution_count.log`）：

| 項目 | 結果 |
|---|---|
| conj(Ĵ(χ1,χ2))² = (𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)))²（χ1・χ2・χ1χ2 が原始的） | N = 5, 7, 11, 13, 9, 25, 27, 49 のすべての組で成り立つ |
| 2 乗を外した版 | 一般に成り立たない（偶然一致する組はある：N = 49 で 36 組） |
| p = 2（N = 8, 16） | 原始指標 3 つがそろう組がない。赤道の定理そのものが空 |
| 条件「U'² が赤道で B_S を B_N に移す」を満たす位相 φ の数（r = (φ/𝔀)² の解の数、格子の指数） | φ(N) 個（N = 5〜49 のすべて）。r(χ) = χ(a)（a は単数）の数と一致 |

- 手計算：conj J / J = N τ12²/(τ1²τ2²)、τ² = 𝔀² χ(−1) N で、符号は χ1χ2 の符号と打ち消す。よって conj(Ĵ)² = (𝔀12/(𝔀1𝔀2))²。U を χ の成分に 𝔀(χ) を掛ける作用素とすると、赤道のケットについて B_N(k1, k2) = U² B_S(U⁻²k1, U⁻²k2)。
- 読み（候補）：
  - 北の畳み込みは、南の畳み込みを U² で移したもの。
  - この条件は U² を、加法の構造の自己同型（単数倍）の分を除いて決める。U そのものは、指標ごとの符号 ± を除いて決まる。
  - 素朴な核の位相 τ/√N は、単数倍 a = −1 の解（無限素点の因子 i^a は 2 乗で消える）。Hartley 核（a = 1）と素朴な核の違いは、この読みではパリティによる単数倍のひねりに当たる。
  - A1 は、a = 1 と指標ごとの符号を固定する公準のまま。P¹ の構造は U を有限個の候補に絞るが、選ばない。
- **円環の検知（第 2 の型）**：依存表。入力は、ガウス和の比がヤコビ和であることと |τ|² = N だけで、A1 は入っていない。除去テスト：A1 を外しても、条件を満たす U は有限個（φ(N) × 符号）に絞られる。「P¹ の構造が A1 を導いた」とは書かない（導かない。符号と単数倍が残る）。
- **残余の判定（見込み）**：計算の細部（PAG25 と PAG256 を結ぶ短い Lean の文、解の集まりの記述）と読み。§4 の規則では短期層に当たる。読みのうち、P¹(ℤ/N) の 0・∞ を著者の定義の「無限素点の無限小と無限大」と結ぶ部分は、著者の判断が先。

### (4) 対照群テスト

- 関数体 F_p[t]/(t^e)（`control_fqt_equator.log`）：等式は同じ形（p = 5, 7 で e = 1、p = 3, 5 で e = 2、p = 3 で e = 3）、解の数は単数の数と一致。p = 2 で空になるのも同じ。
- 扱い：形式の文で、ℚ に固有の算術はない。ℚ に固有なのは無限素点の因子 i^a だけで、この条件では 2 乗で消える（a = ±1 の単数倍のひねりとしてだけ現れる）。

## §2 予想（盲検の前に書いた）

`records/p1_gluing/expected_note.md`。

## §3 盲検の問いテスト

- **条件**：新しいエージェントに WebSearch・WebFetch だけを使わせた（ツール 27 回、約 620 秒）。依頼文は `records/p1_gluing/prompt_blind.md`、出力の全文は `outputs/blind_output.md`。
- **答え**：
  - Q1：2 乗の等式は既知の関係（Conrad の「Gauss and Jacobi sums on finite fields and ℤ/mℤ」の定理 3.15：積が原始的なら J = G1G2/G12、定理 3.12：|G| = √m）から出る（確信度：高）。2 乗を外すと conj(Ĵ) = (−1)^{a1a2}·𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2))で、符号は χ1・χ2 がともに奇のときだけ −1（無限素点の因子 i^a の比）。素朴な g = τ/√N なら符号は出ない。p = 2 と (p, K) = (3, 1) では三つ組がなく空。
  - Q2：m = 2 で成り立つ（B_N = U² B_S U⁻²）。m = 1 は一般に成り立たない。K ≥ 2 では 𝔀 が 1 の冪根なので、m は位数の最小公倍数を法として決まるだけ（確信度：m = 2 は高、一意性は中）。
  - Q3：条件は (φ/𝔀)² が原始的な三つ組の上で乗法的なこと。補題（照合者の手計算、文献は探していない）：|X/Y| ≥ 3 なら、そのような関数は準同型にただ 1 通りに延びる。解は φ(χ) = ε(χ)·𝔀(χ)·√χ(u)（ε は指標ごとの符号、u は単数）、数は φ(N)·2^{|Prim|}。単数倍 v は u を u·v² に動かすので、単数倍と符号で届くのは u が平方のファイバーだけ。素朴な g は u = −1 のファイバーにあり、p ≡ 3 (mod 4) では 𝔀 から単数倍と符号では届かない（確信度：中〜高）。
  - Q4：代数の部分は関数体でも同じ形。ただし関数体の本来のルート数（奇の指標では ∞ の局所因子として F_q 上のガウス和が入る）は、一般にこの条件を満たさない。ℚ で 𝔀 が条件を満たすのは、無限素点の比が ±1 で、2 乗すると 1 になるから（確信度：代数は中〜高、ルート数の対比は中。David–Florea–Lalín など）。
  - Q5：新しい数学の内容は見つからなかった（確信度：中）。残るのは小さい観察 2 つで、どちらも小さいノートの水準以下：(i) この関係は φ² を指標の捩れを除いてしか決めず、A1 型の内容は導かれない。(ii) ℚ では本来のルート数が関係を満たし、関数体では一般に満たさない。
- **構築側の数値での確かめ**（`blind_claims_check.log`）：(a) 符号つきの 1 乗の等式は、8 つの法の 1560 組すべてで成り立った。(b) F_7[t]/(t²) で、照合者の挙げた本来のルート数について (ω/g)² が乗法的でない三つ組が 1080 組中 600 組あった（加法指標の取り替えは乗法的な因子なので、結論に影響しない）。
- **予想との照合**（`expected_note.md`）：Q1・Q2・Q4 の代数の部分は予想どおり。予想と違ったのは次の 3 点。
  - 予想の読み「U² を単数倍の分を除いて決める」は、U'² = U²·R_u（u は単数）という意味では正しいが、U' そのものについては、単数倍 v の作用が u を u·v² に動かすので、単数倍と符号で届くのは u が平方のファイバーだけ。予想は解の集まりの構造を粗く書いていた。
  - 2 乗を外した形の符号 (−1)^{a1a2}（無限素点の因子）を予想していなかった。
  - 関数体では本来のルート数が条件を満たさない、という対照群の違いを予想していなかった（予想は「対照群でも同じ形」だけを見ていた）。
- 文献の照合の範囲：照合者の WebSearch 8 回・WebFetch 約 15 回。MathSciNet・zbMATH、Berndt–Evans–Williams の本文、Tate 1979 の原文は未実施。

## §4 推薦案（1 つ）

- **著者の決定**：2026-11-20 06:55、著者が「進めてください」と言い、この推薦（短期層の小さいノート Part 262、PAG266）が採られた。

- **推薦**：短期層の小さいノート（Part 262、PAG266）として、舞台 P¹ の赤道の絡み合い（Part 21）と貼り合わせの位相 𝔀（Part 252）を結ぶ短い Lean の文を入れる。新規パートにはしない。
  - Lean にする文（案。題と主張文は形式文が確定してから起こす）：
    1. χ1・χ2・χ1χ2 が法 p^(n+1) の原始指標のとき、conj(Ĵ(χ1, χ2))² = (𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)))²。
    2. 2 乗を外した形：conj(Ĵ(χ1, χ2)) = (−1)^{a1a2}·𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2))（符号は χ1・χ2 がともに奇のときだけ −1）。
    3. 作用素の形：赤道のケットについて B_N(k1, k2) = (𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)))² · B_S(k1, k2)（Part 21 の `equator_intertwine_hat` と 1 から）。これが索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める。
  - Lean の外に置くもの（ノートに数値・手計算・盲検として書く）：解の集まりの記述（φ(N)·2^{|Prim|} 個、単数倍の作用と平方のファイバー）、U² による読み、関数体との違い。
  - ラベル（見込み）：1・2 は［既知］（Conrad の定理 3.15 と |τ|² = N）、3 は［再導出（小さい）］。新規候補にはしない。兆候 4 は続く。
  - 閉じるときの統合照合に、台帳の L1〜L5 を一緒に載せる（台帳を閉じる機会にする）。
- **理由**：
  1. 基礎文書の索引に明記された留保（1.4・2.4）を、短い Lean の文で埋められる。著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」の「その上で働く」に、Lean の名前で引ける文が入る（読みの地位は著者の判断のまま）。
  2. 残余は計算の細部と読みで、§4 の規則では短期層に当たる。円環の検知では、入力はガウス和とヤコビ和の関係だけで A1 は入っていない。「P¹ の構造が A1 を導いた」とは書かない（照合者の観察 (i)：符号と u が残る）。
  3. 対照群で違いが 1 つ見つかった：ℚ では本来のルート数（A1 の位相）がこの条件を満たし、関数体では一般に満たさない。ℚ に固有の内容は無限素点の因子 i^a の比が ±1 であることで、小さいが算術の内容を持つ観察として記録する価値がある（確信度：中。関数体のルート数の式は照合者の文献による）。
  4. 初期の鎖（Part 19〜28）の P¹ の定理が索引に入っていなかったので、この機会に索引 1.4 に入れる。
- **著者の判断が先の点**：P¹(ℤ/N) の 0（南、無限小の側）と ∞（北、無限大の側）を、著者の定義の「無限素点では無限大と無限小が重なり合う」と結ぶ読みは、構築側の候補にとどめる。
```


## §G 数値の記録と盲検の出力（根拠）


### records/audit266/numeric/unit_point_ratio.py

```python
"""再照合の指摘 2 の確認（数値。証明ではない）。2026-11-20。
PAG23 の定義どおり：BS(F,G) = extS(conv F.1 G.1)、BN(F,G) = extN(conv F.2 G.2)、kS = extS(ket)、殻 0 のケットは χ(x)（正規化は両辺に共通なので省く）。
単数の点 x での BN.1(x)/BS.1(x) が conj(J)/J に等しいか、conj(Ĵ)² と比べる。χ₁χ₂ が原始的でない組（χ₂ = χ̄₁ など）を含める。
"""
import math, cmath, sys
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/p1_gluing')
from equator_U_check import characters, is_primitive, mul, J
import numpy as np

def run(p, K):
    N = p ** K
    U = [x for x in range(N) if math.gcd(x, N) == 1]
    chars = characters(N); prim = [c for c in chars if is_primitive(N, c, p)]
    def ev(c, x): return c.get(x % N, 0.0)
    def inv(x): return pow(x, -1, N)
    def extS(h): return (h, {y: (h[inv(y)] if y in U else 0.0) for y in range(N)})
    def extN(h): return ({x: (h[inv(x)] if x in U else 0.0) for x in range(N)}, h)
    def conv(f, g): return {x: sum(f[y] * g[(x - y) % N] for y in range(N)) for x in range(N)}
    tot = ok_ratio = eq_sq = 0; nonprim12 = 0; nonprim12_eqsq = 0
    for c1 in prim:
        for c2 in prim:
            k1 = extS({x: ev(c1, x) for x in range(N)}); k2 = extS({x: ev(c2, x) for x in range(N)})
            BS = extS(conv(k1[0], k2[0])); BN = extN(conv(k1[1], k2[1]))
            Jv = J(N, c1, c2)
            if abs(Jv) < 1e-9: continue
            r = [BN[0][x] / BS[0][x] for x in U if abs(BS[0][x]) > 1e-9]
            tot += 1
            ok_ratio += all(np.isclose(t, np.conj(Jv) / Jv) for t in r)
            sq = (np.conj(Jv) / math.sqrt(N)) ** 2
            same = all(np.isclose(t, sq) for t in r)
            eq_sq += same
            c12 = mul(c1, c2)
            if not is_primitive(N, c12, p):
                nonprim12 += 1; nonprim12_eqsq += same
    print(f"p={p} K={K}: 組（J≠0）{tot}、単数の点で比 = conj(J)/J：{ok_ratio}、比 = conj(Ĵ)²：{eq_sq}、"
          f"うち χ₁χ₂ が原始的でない組 {nonprim12}（比 = conj(Ĵ)² は {nonprim12_eqsq}）")

if __name__ == '__main__':
    for (p, K) in [(5, 1), (7, 1), (3, 2), (5, 2)]:
        run(p, K)
```


### records/audit266/numeric/unit_point_ratio.log

```
p=5 K=1: 組（J≠0）9、単数の点で比 = conj(J)/J：9、比 = conj(Ĵ)²：6、うち χ₁χ₂ が原始的でない組 3（比 = conj(Ĵ)² は 0）
p=7 K=1: 組（J≠0）25、単数の点で比 = conj(J)/J：25、比 = conj(Ĵ)²：20、うち χ₁χ₂ が原始的でない組 5（比 = conj(Ĵ)² は 0）
p=3 K=2: 組（J≠0）8、単数の点で比 = conj(J)/J：8、比 = conj(Ĵ)²：8、うち χ₁χ₂ が原始的でない組 0（比 = conj(Ĵ)² は 0）
p=5 K=2: 組（J≠0）192、単数の点で比 = conj(J)/J：192、比 = conj(Ĵ)²：192、うち χ₁χ₂ が原始的でない組 0（比 = conj(Ĵ)² は 0）
```


### records/p1_gluing/equator_U_check.py

```python
"""舞台 P¹ の赤道の絡み合い（Part 21、PAG25 の equator_intertwine_hat）と、貼り合わせ U の位相（Part 252、PAG256 の rootNum = 𝔀）の関係（数値。証明ではない）。2026-11-19 夜。

規約（PAG7・PAG25・PAG256 に合わせる）：e(t) = exp(2πi t/N)（stdAddChar）、τ(χ) = Σ_x χ(x) e(x)、J(χ1,χ2) = Σ_x χ1(x) χ2(1−x)、Ĵ = J/√N、
𝔀(χ) = τ(χ)/(i^a √N)（a = 0：χ(−1) = 1、a = 1：χ(−1) = −1）。
(1) χ1, χ2, χ1χ2 が法 N = p^K の原始指標のとき、conj(Ĵ)² = (𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)))² か。
(2) 1 乗の版 conj(Ĵ)² = 𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)) は成り立つか（成り立たない見込み）。
(3) 条件「U² が赤道で南の畳み込みを北の畳み込みに移す」を満たす位相 φ の集まり：r = (φ/𝔀)² が、原始指標の上で乗法的（χ1, χ2, χ1χ2 が原始的なとき r(χ1χ2) = r(χ1)r(χ2)）。
    そのような r が「ある単数 a で r(χ) = χ(a)」に限られるかを、線形の方程式（r の偏角）として次元で調べる。
"""
import cmath, math, itertools, sys
import numpy as np

def units(N): return [x for x in range(N) if math.gcd(x, N) == 1]

def characters(N):
    U = units(N); n = len(U); idx = {u: i for i, u in enumerate(U)}
    rng = np.random.default_rng(1); c = rng.normal(size=n) + 1j * rng.normal(size=n)
    M = np.zeros((n, n), dtype=complex)
    for k, a in enumerate(U):
        for u in U: M[idx[u], idx[(a * u) % N]] += c[k]
    w, V = np.linalg.eig(M)
    return [{u: V[idx[u], j] / V[idx[1], j] for u in U} for j in range(n)]

def is_primitive(N, chi, p):
    if N == p: return any(abs(chi[u] - 1) > 1e-8 for u in chi)
    g = 1 + N // p
    return abs(chi[g % N] - 1) > 1e-8

def mul(c1, c2): return {u: c1[u] * c2[u] for u in c1}

def ev(N, chi, x): return chi.get(x % N, 0.0)

def tau(N, chi): return sum(chi[u] * cmath.exp(2j * math.pi * u / N) for u in chi)

def J(N, c1, c2): return sum(ev(N, c1, x) * ev(N, c2, 1 - x) for x in range(N))

def w(N, chi):
    a = 0 if abs(chi[N - 1] - 1) < 1e-8 else 1
    return tau(N, chi) / ((1j) ** a * math.sqrt(N))

def key(N, chi): return tuple(np.round([chi[u] for u in sorted(chi)], 6))

if __name__ == '__main__':
  for (p, K) in [(5, 1), (7, 1), (11, 1), (13, 1), (3, 2), (2, 3), (5, 2), (3, 3), (2, 4), (7, 2)]:
      N = p ** K
      chars = characters(N); prim = [c for c in chars if is_primitive(N, c, p)]
      pk = {key(N, c): i for i, c in enumerate(prim)}
      n1 = n2 = 0; bad1 = bad2 = 0; eqs = []
      for i, c1 in enumerate(prim):
          for j, c2 in enumerate(prim):
              c12 = mul(c1, c2)
              if key(N, c12) not in pk: continue
              k = pk[key(N, c12)]
              Jh = J(N, c1, c2) / math.sqrt(N)
              lhs = np.conj(Jh) ** 2
              rhs2 = (w(N, c12) / (w(N, c1) * w(N, c2))) ** 2
              rhs1 = w(N, c12) / (w(N, c1) * w(N, c2))
              n1 += 1; bad1 += not np.isclose(lhs, rhs2); bad2 += np.isclose(lhs, rhs1)
              eqs.append((i, j, k))
      # (3) r の偏角 θ（r = e^{iθ}）について θ_i + θ_j − θ_k ≡ 0。解の空間の次元（実数の線形代数、2π の整数倍は無視）と、
      #     「θ(χ) = arg χ(a)」の族の次元（= 0：離散）を比べる代わりに、方程式の階数から自由度を出す。
      m = len(prim)
      A = np.zeros((len(eqs), m))
      for r_, (i, j, k) in enumerate(eqs):
          A[r_, i] += 1; A[r_, j] += 1; A[r_, k] -= 1
      rank = np.linalg.matrix_rank(A) if len(eqs) else 0
      print(f'N = {N}：原始指標 {m} 個、組 {n1}、(1) の不一致 {bad1}、(2) の一致 {bad2}、(3) 偏角の方程式の自由度 {m - rank}')
```


### records/p1_gluing/equator_U_check.log

```
N = 5：原始指標 3 個、組 6、(1) の不一致 0、(2) の一致 0、(3) 偏角の方程式の自由度 0
N = 7：原始指標 5 個、組 20、(1) の不一致 0、(2) の一致 0、(3) 偏角の方程式の自由度 0
N = 11：原始指標 9 個、組 72、(1) の不一致 0、(2) の一致 0、(3) 偏角の方程式の自由度 0
N = 13：原始指標 11 個、組 110、(1) の不一致 0、(2) の一致 0、(3) 偏角の方程式の自由度 0
N = 9：原始指標 4 個、組 8、(1) の不一致 0、(2) の一致 0、(3) 偏角の方程式の自由度 0
N = 8：原始指標 2 個、組 0、(1) の不一致 0、(2) の一致 0、(3) 偏角の方程式の自由度 2
N = 25：原始指標 16 個、組 192、(1) の不一致 0、(2) の一致 0、(3) 偏角の方程式の自由度 0
N = 27：原始指標 12 個、組 72、(1) の不一致 0、(2) の一致 0、(3) 偏角の方程式の自由度 0
N = 16：原始指標 4 個、組 0、(1) の不一致 0、(2) の一致 0、(3) 偏角の方程式の自由度 4
N = 49：原始指標 36 個、組 1080、(1) の不一致 0、(2) の一致 36、(3) 偏角の方程式の自由度 0
```


### records/p1_gluing/equator_solution_count.py

```python
"""equator_U_check.py の (3) の続き：r = (φ/𝔀)² の偏角 θ（ℝ/ℤ に正規化）が θ_i + θ_j − θ_k ∈ ℤ（χ_i χ_j = χ_k、3 つとも原始的）を満たす解の数を、
行の張る格子 L ⊂ ℤ^m の指数 [ℤ^m : L] として数える（L が全階数のとき解の数 = 指数）。「r(χ) = χ(a)（a は単数）」の解の数 φ(N) と比べる（数値。証明ではない）。2026-11-19 夜。"""
import math, sys
sys.path.insert(0, '.')
from equator_U_check import characters, is_primitive, mul, key
from fractions import Fraction

def lattice_index(rows, m):
    """整数の行のリストが張る格子の、ℤ^m での指数（全階数でなければ None）。行の整数のガウス消去（エルミート標準形）で。"""
    M = [list(r) for r in rows if any(r)]
    col = 0; piv = []
    r0 = 0
    while col < m and r0 < len(M):
        # col 列で、r0 以降の行の gcd を r0 行に集める
        while True:
            nz = [i for i in range(r0, len(M)) if M[i][col] != 0]
            if not nz: break
            i0 = min(nz, key=lambda i: abs(M[i][col]))
            M[r0], M[i0] = M[i0], M[r0]
            done = True
            for i in range(r0 + 1, len(M)):
                if M[i][col] != 0:
                    q = M[i][col] // M[r0][col]
                    M[i] = [a - q * b for a, b in zip(M[i], M[r0])]
                    if M[i][col] != 0: done = False
            if done: break
        if any(M[i][col] != 0 for i in range(r0, len(M))):
            piv.append(abs(M[r0][col])); r0 += 1
        col += 1
    if len(piv) < m: return None
    return math.prod(piv)

if __name__ == '__main__':
  for (p, K) in [(5, 1), (7, 1), (11, 1), (13, 1), (3, 2), (5, 2), (3, 3), (7, 2)]:
      N = p ** K
      chars = characters(N); prim = [c for c in chars if is_primitive(N, c, p)]
      pk = {key(N, c): i for i, c in enumerate(prim)}
      rows = []
      for i, c1 in enumerate(prim):
          for j, c2 in enumerate(prim):
              k = pk.get(key(N, mul(c1, c2)))
              if k is None: continue
              r = [0] * len(prim); r[i] += 1; r[j] += 1; r[k] -= 1; rows.append(r)
      idx = lattice_index(rows, len(prim))
      phiN = N // p * (p - 1)
      print(f'N = {N}：原始指標 {len(prim)} 個、解の数（格子の指数）{idx}、φ(N) = {phiN}')
```


### records/p1_gluing/equator_solution_count.log

```
N = 5：原始指標 3 個、解の数（格子の指数）4、φ(N) = 4
N = 7：原始指標 5 個、解の数（格子の指数）6、φ(N) = 6
N = 11：原始指標 9 個、解の数（格子の指数）10、φ(N) = 10
N = 13：原始指標 11 個、解の数（格子の指数）12、φ(N) = 12
N = 9：原始指標 4 個、解の数（格子の指数）6、φ(N) = 6
N = 25：原始指標 16 個、解の数（格子の指数）20、φ(N) = 20
N = 27：原始指標 12 個、解の数（格子の指数）18、φ(N) = 18
N = 49：原始指標 36 個、解の数（格子の指数）42、φ(N) = 42
```


### records/p1_gluing/control_fqt_equator.py

```python
"""対照群（関数体）：R = F_p[t]/(t^e) で、赤道の等式 conj(Ĵ)² = (𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)))²（𝔀 = τ/√|R|）と、解の数（格子の指数）＝ |R^×| が同じ形で成り立つか（数値。証明ではない）。2026-11-19 夜。
加法指標 ψ(x) = exp(2πi λ(x)/p)（λ は t^{e−1} の係数）。原始指標：1 + t^{e−1}R の上で自明でない指標（e = 1 では自明でない指標）。"""
import itertools, cmath, math, sys
import numpy as np
sys.path.insert(0, '.')
from equator_solution_count import lattice_index

def ring(p, e):
    els = list(itertools.product(range(p), repeat=e)); idx = {x: i for i, x in enumerate(els)}
    def mul(x, y):
        z = [0] * e
        for i in range(e):
            for j in range(e - i): z[i + j] = (z[i + j] + x[i] * y[j]) % p
        return tuple(z)
    def sub(x, y): return tuple((a - b) % p for a, b in zip(x, y))
    units = [x for x in els if x[0] % p != 0]
    return els, idx, mul, sub, units

if __name__ == '__main__':
  for (p, e) in [(5, 1), (7, 1), (3, 2), (5, 2), (3, 3), (2, 3), (2, 4)]:
      els, idx, mul, sub, units = ring(p, e); n = len(els); one = tuple([1] + [0] * (e - 1))
      ui = {u: i for i, u in enumerate(units)}; m = len(units)
      rng = np.random.default_rng(3); c = rng.normal(size=m) + 1j * rng.normal(size=m)
      M = np.zeros((m, m), dtype=complex)
      for k, a in enumerate(units):
          for u in units: M[ui[u], ui[mul(a, u)]] += c[k]
      w_, V = np.linalg.eig(M)
      chars = [{u: V[ui[u], j] / V[ui[one], j] for u in units} for j in range(m)]
      if e == 1: sub1 = [u for u in units if u != one]
      else: sub1 = [u for u in units if all(u[i] == one[i] for i in range(e - 1))]
      prim = [ch for ch in chars if any(abs(ch[u] - 1) > 1e-8 for u in sub1)]
      key = lambda ch: tuple(np.round([ch[u] for u in units], 6))
      pk = {key(ch): i for i, ch in enumerate(prim)}
      psi = lambda x: cmath.exp(2j * math.pi * x[e - 1] / p)
      tau = lambda ch: sum(ch[u] * psi(u) for u in units)
      ev = lambda ch, x: ch.get(x, 0.0)
      J = lambda c1, c2: sum(ev(c1, x) * ev(c2, sub(one, x)) for x in els)
      wv = lambda ch: tau(ch) / math.sqrt(n)
      bad = cnt = 0; rows = []
      for i, c1 in enumerate(prim):
          for j, c2 in enumerate(prim):
              c12 = {u: c1[u] * c2[u] for u in units}; k = pk.get(key(c12))
              if k is None: continue
              cnt += 1
              lhs = np.conj(J(c1, c2) / math.sqrt(n)) ** 2
              rhs = (wv(c12) / (wv(c1) * wv(c2))) ** 2
              bad += not np.isclose(lhs, rhs)
              r = [0] * len(prim); r[i] += 1; r[j] += 1; r[k] -= 1; rows.append(r)
      idx_ = lattice_index(rows, len(prim)) if rows else None
      print(f'F_{p}[t]/(t^{e})：原始指標 {len(prim)} 個、組 {cnt}、等式の不一致 {bad}、解の数 {idx_}、|R^×| = {m}')
```


### records/p1_gluing/control_fqt_equator.log

```
F_5[t]/(t^1)：原始指標 3 個、組 6、等式の不一致 0、解の数 4、|R^×| = 4
F_7[t]/(t^1)：原始指標 5 個、組 20、等式の不一致 0、解の数 6、|R^×| = 6
F_3[t]/(t^2)：原始指標 4 個、組 8、等式の不一致 0、解の数 6、|R^×| = 6
F_5[t]/(t^2)：原始指標 16 個、組 192、等式の不一致 0、解の数 20、|R^×| = 20
F_3[t]/(t^3)：原始指標 12 個、組 72、等式の不一致 0、解の数 18、|R^×| = 18
F_2[t]/(t^3)：原始指標 2 個、組 0、等式の不一致 0、解の数 None、|R^×| = 4
F_2[t]/(t^4)：原始指標 4 個、組 0、等式の不一致 0、解の数 None、|R^×| = 8
```


### records/p1_gluing/blind_claims_check.py

```python
"""盲検の出力の主張のうち 2 つを数値で確かめる（証明ではない）。2026-11-19 夜。
(a) 2 乗を外した形：conj(Ĵ) = (−1)^{a1 a2}·𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2))（法 p^K、p 奇、3 つとも原始的）。
(b) 関数体 F_7[t]/(t^2) で、盲検の挙げた本来のルート数 ω（η = χ|F_7^× が自明なら g、そうでなければ g·√7/τ_7(η)、g = τ/√|R|）が、
    条件「(φ/g)² が原始指標の上で乗法的」を満たさないこと（加法指標の取り替えは η(b) 倍で乗法的なので、結論に影響しない）。"""
import math, cmath, sys
import numpy as np
sys.path.insert(0, '.')
from equator_U_check import characters, is_primitive, mul, key, J, w, tau
from control_fqt_equator import ring

bad = tot = 0
for (p, K) in [(5, 1), (7, 1), (11, 1), (13, 1), (3, 2), (5, 2), (3, 3), (7, 2)]:
    N = p ** K; prim = [c for c in characters(N) if is_primitive(N, c, p)]
    pk = {key(N, c) for c in prim}
    for c1 in prim:
        for c2 in prim:
            c12 = mul(c1, c2)
            if key(N, c12) not in pk: continue
            a1 = 0 if abs(c1[N - 1] - 1) < 1e-8 else 1; a2 = 0 if abs(c2[N - 1] - 1) < 1e-8 else 1
            lhs = np.conj(J(N, c1, c2) / math.sqrt(N)); rhs = (-1) ** (a1 * a2) * w(N, c12) / (w(N, c1) * w(N, c2))
            tot += 1; bad += not np.isclose(lhs, rhs)
print(f'(a) 法 p^K（8 つの法）の組 {tot}：符号つきの 1 乗の等式の不一致 {bad}')

p, e = 7, 2
els, idx, mul_, sub, units = ring(p, e); n = len(els); one = (1, 0)
ui = {u: i for i, u in enumerate(units)}; m = len(units)
rng = np.random.default_rng(5); c = rng.normal(size=m) + 1j * rng.normal(size=m)
M = np.zeros((m, m), dtype=complex)
for k, a in enumerate(units):
    for u in units: M[ui[u], ui[mul_(a, u)]] += c[k]
_, V = np.linalg.eig(M)
chars = [{u: V[ui[u], j] / V[ui[one], j] for u in units} for j in range(m)]
sub1 = [u for u in units if u[0] == 1]
prim = [ch for ch in chars if any(abs(ch[u] - 1) > 1e-8 for u in sub1)]
kf = lambda ch: tuple(np.round([ch[u] for u in units], 6)); pk = {kf(ch): i for i, ch in enumerate(prim)}
psi = lambda x: cmath.exp(2j * math.pi * x[1] / p)
g = lambda ch: sum(ch[u] * psi(u) for u in units) / math.sqrt(n)
consts = [(cc, 0) for cc in range(1, p)]
def omega(ch):
    eta = {cc: ch[(cc, 0)] for cc in range(1, p)}
    if all(abs(eta[cc] - 1) < 1e-8 for cc in eta): return g(ch)
    t7 = sum(eta[cc] * cmath.exp(2j * math.pi * cc / p) for cc in eta)
    return g(ch) * math.sqrt(p) / t7
fails = trip = 0
for c1 in prim:
    for c2 in prim:
        c12 = {u: c1[u] * c2[u] for u in units}
        if kf(c12) not in pk: continue
        trip += 1
        r = lambda ch: (omega(ch) / g(ch)) ** 2
        fails += not np.isclose(r(c12), r(c1) * r(c2))
print(f'(b) F_7[t]/(t^2)：原始指標の三つ組 {trip}、(ω/g)² が乗法的でない組 {fails}（0 でなければ ω は条件を満たさない）')
```


### records/p1_gluing/blind_claims_check.log

```
(a) 法 p^K（8 つの法）の組 1560：符号つきの 1 乗の等式の不一致 0
(b) F_7[t]/(t^2)：原始指標の三つ組 1080、(ω/g)² が乗法的でない組 600（0 でなければ ω は条件を満たさない）
```


### records/p1_gluing/outputs/blind_meta.txt

```
盲検の問いテスト（2026-11-19 20:25〜20:36）。新しいエージェント（general-purpose、WebSearch・WebFetch だけを使うよう依頼）。依頼文は ../prompt_blind.md の全文。ツール 27 回、約 620 秒。出力の全文は blind_output.md。
```


### records/p1_gluing/outputs/blind_output.md

```
# 文献照合の回答：Q1〜Q5（赤道のケット、𝔀、B_N と B_S）— 盲検の出力の全文（2026-11-19）

依頼どおり WebSearch と WebFetch だけを使い、ファイルの読み書きとコードの実行はしていません。手計算は数値では確かめていません。結論を先に書くと、Q1〜Q4 はすべて既知の結果と初等的な計算で答えが出ます。新しい数学の内容になりそうなものは見つかりませんでした。

## 前提の点検（手計算）

- χ1χ2 が原始的なら、南の畳み込みは非単数の点で 0 になります。単数 v について x ↦ x(1+p^{K−1}v) と置き換えると、χ1χ2 の値だけが自明でない因子を受け取るためです。
- その結果、B_S(k1,k2) = J(χ1,χ2)·k_{χ1χ2}、B_N(k1,k2) = conj(J)·k_{χ1χ2} です。
- |J|² = N なので、比は conj(J)/J = conj(Ĵ)² になり、与えられた事実と合います。畳み込みの正規化にはよりません。

## Q1

**答え**
- Jacobi 和とガウス和の関係と |τ| = √N から、Ĵ = g1·g2/g12 です（g = τ/√N）。
- g = i^a·𝔀 で、a(χ1χ2) ≡ a1 + a2 (mod 2) です。
- **2 乗の形**：conj(Ĵ)² = 𝔀(χ1χ2)² / (𝔀(χ1)²·𝔀(χ2)²) = 𝔀(χ1χ2)²·𝔀(χ̄1)²·𝔀(χ̄2)²。
  - 2 つ目の等号は conj 𝔀(χ) = 𝔀(χ̄) = 𝔀(χ)^{−1} によります。これは τ(χ̄) = χ(−1)·conj τ(χ) から出ます。
- **2 乗を外した形**：conj(Ĵ) = (−1)^{a1·a2}·𝔀(χ1χ2) / (𝔀(χ1)·𝔀(χ2))。
  - 符号 (−1)^{a1a2} = i^{a1+a2−a12} は、χ1 と χ2 がともに奇のときだけ −1 になり、𝔀 だけでは消せません。
  - 素朴な g なら符号は出ず、conj(Ĵ) = g12/(g1·g2) です。
  - 補足（Q3 の補題から）：±1 値の s で (−1)^{a1a2} = s12/(s1·s2) と書けるのは、−1 が法 N の平方のとき、つまり p ≡ 1 (mod 4) のときに限ります。そのときは s = i^a·χ(v)（v² = −1）です。
- **p = 2**：仮定を満たす三つ組は存在せず、主張は空虚に成り立ちます。
  - K = 1 には原始指標がありません。
  - K ≥ 2 では、原始的であることは「1+2^{K−1} での値が −1」と同値です。2 つの原始指標の積はそこで +1 になるので、積は原始的になりません。
- 同じ理由で (p, K) = (3, 1) も空虚です。三つ組が存在するのは、p が奇数で K ≥ 2 のときと、p ≥ 5 で K = 1 のときです。

**確信度**：高（手計算）

**根拠**
- K. Conrad, [Gauss and Jacobi Sums on Finite Fields and Z/mZ](https://kconrad.math.uconn.edu/blurbs/gradnumthy/Gauss-Jacobi-sums.pdf)：定理 3.15（χ1χ2 が原始的なら J = G1G2/G12）、定理 3.12（|G| = √m）、系 2.3 の証明（共役の公式）。
- Long–Pigno–Pinner, [Evaluating Prime Power Gauss and Jacobi Sums](https://ar5iv.arxiv.org/html/1410.6179)（arXiv:1410.6179, 2014）の式 (10)。そこでは、この式の出典として次の 2 本が挙げられています。
  - W. Zhang, W. Yao, Acta Arith. 115 (2004) 225–229
  - W. Zhang, Z. Xu, Acta Arith. 121 (2006) 117–124

## Q2

**答え**
- m = 2 で成り立ちます：B_N(k1,k2) = U²·B_S(U^{−2}k1, U^{−2}k2)。
  - 計算：右辺 = 𝔀12²·𝔀1^{−2}·𝔀2^{−2}·J·k12 = conj(Ĵ)²·J·k12 = 左辺（Q1 を使う）。
- m = 1 では右辺が (−1)^{a1a2}·conj(Ĵ) 倍になり、一般には合いません。
- 整数 m で成り立つのは、すべての三つ組で c^{m−2} = 1 となるときです（c = 𝔀12/(𝔀1𝔀2)）。
  - K = 1, p ≥ 5 では m = 2 だけです。例：p = 5 の 4 次指標では J ∈ ℤ[i]、|J|² = 5 で、Ĵ は 1 の冪根ではありません。
  - K ≥ 2 では 𝔀 が 1 の冪根です（明示的な評価式による）。したがって m は、c の位数の最小公倍数 L を法として m ≡ 2 と決まるだけです。
  - p = 2 と (3, 1) は空虚で、どの m でも成り立ちます。
- 素朴な g も m = 2 で同じ関係を満たします（g² = χ(−1)·𝔀²）。

**確信度**：m = 2 は高、m の一意性は中

**根拠**
- 手計算。
- 1 の冪根であることは [Long–Pigno–Pinner](https://ar5iv.arxiv.org/html/1410.6179) の定理 2.1 によります。原始的な χ mod p^m（m ≥ 2）について、G = p^{m/2}·χ(·)·e(·) にルジャンドル型の符号と ε_{p^m} を掛けた形です。
- 同じ論文が先行として次を挙げています。
  - Odoni, Bull. LMS 5 (1973)
  - Cochrane–Zheng, Acta Arith. 91 (1999)

## Q3

**答え**（Q2 と同じ m = 2 の関係）

条件は、ψ = φ²/𝔀² が原始的な三つ組の上で乗法的であることです。

**補題（手計算）**
- 設定：X は有限アーベル群、Y は部分群で |X/Y| ≥ 3、A = X∖Y。
- 主張：x, y, xy ∈ A のときに乗法的な ψ: A → S¹ は、準同型 X → S¹ にただ 1 通りに延びる。
- 証明の要点：
  - Y の上の値を ψ(xy)/ψ(x) で定めます。x の取り方によらないことは、第 3 の剰余類を経由して示します。
  - x, y ∈ A かつ xy ∈ Y の場合は、剰余類が 0 でも −c でもない w を経由します。ここで |X/Y| ≥ 3 を使います。
- 今の設定では、X は法 N の指標の群、Y は原始的でない指標の群で、X/Y ≅ C_p（K ≥ 2）です。Pontryagin 双対から ψ(χ) = χ(u) となり、u ∈ (ℤ/N)^× は一意に決まります。

**解の集まり**
- 解の形：φ(χ) = ε(χ)·𝔀(χ)·√χ(u)。ε ∈ {±1}^{Prim} は指標ごとの自由な符号です。
- 大きさ：φ(N)·2^{|Prim|}。|Prim| = p^{K−2}(p−1)²（K ≥ 2）、p − 2（K = 1）。
- 構造：φ ↦ u は (ℤ/N)^× への全射で、各ファイバーは {±1}^{Prim} の torsor です。

**単数倍の作用**
- 伸縮 f(x) ↦ f(vx) は 2 つの畳み込みと貼り合わせを保ちます（北のチャートでは v^{−1} 倍）。k_χ には χ(v) で働きます。
- したがって φ ↦ φ·χ(v) は解を解に送り、u を u·v² に動かします。
- これは加法指標の取り替え e(x) → e(bx) で局所定数が χ(b) 倍になることと同じ内容です。
- 伸縮と符号で届くのは、u が平方のファイバーだけです（p が奇数のとき指数 2）。平方でない u のファイバーにも解はありますが、χ について乗法的な形の解はありません。

**素朴な値 τ(χ)/√N**
- g² = χ(−1)·𝔀² なので、g は u = −1 のファイバーにあります。𝔀 は u = 1、ε ≡ 1 の解です。
- p ≡ 1 (mod 4) なら、適当な符号 ε について g = ε·𝔀·χ(v)（v² = −1）です。
- p ≡ 3 (mod 4) では −1 が平方でないので、g には 𝔀 から伸縮と符号では届きません。

**注意（Q5 に関係）**
- この関係が見るのは φ² だけで、指標ごとの符号は決まりません。
- φ(χ)φ(χ̄) = 1 を足すと g は外れます（g(χ)g(χ̄) = χ(−1)）。それでも組 {χ, χ̄} ごとの符号と u は自由に残ります。
- つまり、この関係だけでは 𝔀 は選び出せません。

p = 2 と (3, 1) では制約がなく、絶対値 1 のすべての φ が解です。

**確信度**：中〜高（手計算）

**根拠**
- 補題を述べた文献は探しておらず、見つかってもいません。
- 加法指標への依存 W(χ, bψ) = χ(b)·W(χ, ψ) は S. A. Biswas, [Existence of non-abelian local constants, and their properties](https://arxiv.org/pdf/1401.5591)（arXiv:1401.5591, 2014）の §4.3 にあります（Tate による）。Tate 1979 の原文では確認していません。

## Q4

**答え**：代数の部分は同じ形です。ただし「𝔀 ＝ ルート数」という読みは移りません。

**同じ部分**
- 設定：R = F_q[t]/(P^K)、deg P = d、N = q^{dK}、加法指標は Hayes の e_q(a/P^K)。
- 証明は同じで、J = G1G2/G12（χ1χ2 が原始的なとき）と |G| = √N が成り立ちます。
- 𝔀 を同じ式（χ(−1) を使う）で形式的に定めるか、g を使えば、Q1〜Q3 の形はそのまま成り立ちます。
- 解の数は |R^×|·2^{|Prim|} で、|Prim| = q^{d(K−2)}(q^d − 1)²（K ≥ 2）です。

**違い 1：空虚になる範囲**
- 三つ組が存在するのは、K ≥ 2 なら q^d ≥ 3、K = 1 なら q^d ≥ 4 のときです。
- したがって標数 2 でも一般には空虚になりません（例：F_4[t]/(t²)）。有理数体の p = 2 とはここが違います。
- 標数 2 では −1 = 1 なので a ≡ 0、𝔀 = g となり、Q1 の符号も消えます。

**違い 2：本来のルート数**
- 関数体のルート数 ω は、偶の指標では g、奇の指標では g·√q/τ(η) です（η = χ|F_q^×、τ(η) は F_q 上のガウス和、つまり ∞ の局所因子）。
- 有理数体の i^a の位置に、正規化された F_q 上のガウス和が入ることになります。
- η1, η2, η1η2 がすべて自明でない三つ組では、追加の因子は正規化した F_q 上の Jacobi 和の 2 乗です。これは一般に 1 ではありません。
  - 例：q = 7 の 3 次指標で J = 2+3ω のとき J²/7 ≠ 1。R = F_7[t]/(t²) にはこの型の三つ組があります。
- 有理数体で 𝔀 が解になるのは、無限素点の比が ±1、つまり (−1)^{a1a2} で、2 乗すると 1 になるからです。

**確信度**：代数の部分は中〜高、ルート数の対比は中

**根拠**
- David–Florea–Lalín, [The mean values of cubic L-functions over function fields](https://arxiv.org/pdf/1901.00817)（arXiv:1901.00817, 2019）の系 2.4。抽出した文面が崩れていたので、Goel–Ray, [arXiv:2505.12015](https://arxiv.org/pdf/2505.12015) の式 (2.8) で裏を取りました。
- 偶と奇の定義：Andrade–Yiasemides, [arXiv:1901.06295](https://arxiv.org/pdf/1901.06295)。
- F_q[t]/(P^K) での Jacobi 和とガウス和の関係そのものを書いた文献は見つかりませんでした。近いものとして次があります。
  - Galois 環での類似：D. Xu, [On the Jacobi sums over Galois rings](https://arxiv.org/abs/2001.04028) の補題 4.8
  - J. Wang, On the Jacobi sums mod P^n, J. Number Theory 39 (1991)。[zbMATH の記録](https://portal.mardi4nfdi.de/wiki/Item:Q805663)で確認しただけで、P^n がどの環のものかは未確認です。

## Q5

**答え**：既知の結果の当てはめで済まない、新しい数学の内容は見つかりませんでした。

**材料はすべて既知か初等的**
- Jacobi 和とガウス和の関係（Conrad、Zhang–Yao、Long–Pigno–Pinner）
- |τ| と共役の公式
- 素数冪の法でのガウス和の明示的な評価（Odoni、Cochrane–Zheng）
- 加法指標への依存（Tate、Biswas）
- 関数体のルート数（David–Florea–Lalín）
- 初等的な延長の補題と Pontryagin 双対

**残るのは小さい観察 2 つで、どちらも小さいノートの水準以下**
- (i) この貼り合わせの関係は φ² を指標の捩れを除いてしか決めません。したがって位相、つまり指標ごとの符号と u は外から入れる必要があります。関係から A1 型の内容が導かれることはありません。
- (ii) 有理数体では本来のルート数が関係を満たしますが、関数体では一般に満たしません。

どちらも文献には見つかりませんでしたが、検索は軽いものです。

**確信度**：中

**検索の範囲**
- WebSearch 8 回、WebFetch 約 15 回。
- 実施していないもの：MathSciNet と zbMATH での検索、Berndt–Evans–Williams の本文、Tate 1979 と Wang 1991 の原文。
- P¹(ℤ/N) の 2 チャートの畳み込みという設定そのものは、1 回の検索では見つかりませんでした。
- 「見つからなかった」は、存在しないことの証明ではありません。
```
