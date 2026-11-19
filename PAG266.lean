/-
アーデル射影幾何 — Part 262（PAG266、短期層の小さいノート、2026-11-20）：舞台 P¹ の赤道の絡み合いを、貼り合わせの位相 𝔀 で書く

問いの出所：基礎文書の索引 1.4（舞台は P¹）と 2.4（「射影」の変換）の留保「`JH` は P¹ の上の作用素ではなく、P¹ のモデルと結ぶ Lean の文はない」。
- 推薦案 `pag2_p1_gluing_preregistration.md` §4 を、2026-11-20 06:55 に著者が採用した（「進めてください」）。
- 著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」の読みの材料（読みの地位は変えない）。

記号：
- N = p^(n+1)（p は素数）。e = stdAddChar、τ(χ) = gaussSum χ e。J = `PAG.Part7.J`（ヤコビ和）、Ĵ = J/√N（`PAG.Part25.Jhat`）。
- 𝔀(χ) = `PAG.Part256.rootNum` χ = τ(χ)/(i^a √N)（偶なら a = 0、奇なら a = 1）。原始指標でルート数であることは Lean の外。
- P¹(ℤ/p^K) の 2 チャートのモデル、南北の畳み込み B_S・B_N、赤道のケット |0, χ⟩ = `PAG.Part23.kS K 0 (n+1) h χ`（Part 19（PAG23））。

主な定理（χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標のとき）：
1. conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))（`conj_Jhat_eq_gauss`）。
2. conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))、s は χ₁ か χ₂ が偶なら 1、両方とも奇なら −1（`conj_Jhat_eq_rootNum`）。
3. conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²（`conj_Jhat_sq_eq_rootNum`）。
4. 赤道のケットについて B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)（`equator_intertwine_rootNum`、2 チャートのモデル）。
5. 同じ式を、射影直線そのもの（`PAG.Part27.ProjLine`）の上の関数として（`equator_intertwine_proj_rootNum`、Part 25（PAG29）の `equator_intertwine_proj` から）。

読み（Lean の外）：χ の成分に 𝔀(χ) を掛ける作用素を U とすると、4 は赤道のケットの上で B_N(k₁, k₂) = U² B_S(U⁻²k₁, U⁻²k₂) と読める。
この条件を満たす位相は 𝔀 だけではない（単数 u と指標ごとの符号の分。数値と照合者の手計算、`pag2_p1_gluing_preregistration.md`）。
A1 は導かれない。p = 2（すべての n）と p = 3、n = 0 では原始指標の三つ組がなく、5 つの文は空（独立照合の指摘。p = 2 は Part 26（PAG30）の注意とも合う）。
仮定は必要十分ではない：1〜3 では χ₁χ₂ の原始性は不要に見え、χ₁・χ₂ の原始性が中身を運ぶのは n = 0 だけ（n ≥ 1 では両辺が 0 になる。独立照合の手計算）。
4・5 では χ₁χ₂ の原始性が要る（単数でない点で両辺が 0 になる部分）。4・5 は Part 21・25 の定理の係数の書き換えで、絡み合いの中身はそちらにある。

ラベル（見込み、照合の後に確定）：1〜3 は［既知］（積が原始的ならヤコビ和はガウス和の比、|τ|² = N。Conrad の定理 3.15・3.12）、4・5 は［再導出（小さい）］。新規候補なし。
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
conj(Ĵ(χ₁, χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))。符号 s は、χ₁ か χ₂ が偶なら 1、両方とも奇なら −1
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

/-- **3. 2 乗の形**：χ₁・χ₂・χ₁χ₂ が原始的なら、conj(Ĵ(χ₁, χ₂))² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²。 -/
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
絡み合いの中身（単数でない点で両辺が 0 になることを含む）は Part 21 にある。 -/
theorem equator_intertwine_rootNum (K : ℕ) (h : 0 + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    PAG.Part23.BN (PAG.Part23.kS K 0 (n + 1) h χ₁) (PAG.Part23.kS K 0 (n + 1) h χ₂)
      = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2
          • PAG.Part23.BS (PAG.Part23.kS K 0 (n + 1) h χ₁) (PAG.Part23.kS K 0 (n + 1) h χ₂) := by
  rw [PAG.Part25.equator_intertwine_hat K h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]

/-- **5. 射影直線そのものの上の形**：Part 25（PAG29）の `equator_intertwine_proj`（射影直線 P¹(ℤ/p^K) = `PAG.Part27.ProjLine` の上の
関数としての南北の畳み込み B_S^proj・B_N^proj と赤道のケット）について、4 と同じ式が成り立つ。`equator_intertwine_proj` の係数を
3 で書き換えたもの。1 ≤ K は h から出るので、仮定に置かない（独立照合の指摘で外した）。 -/
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
