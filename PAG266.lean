/-
アーデル射影幾何 — Part 262（PAG266、短期層の小さいノート、2026-11-20）：舞台 P¹ の赤道の絡み合いの係数を 𝔀（`rootNum`）で書く

問いの出所：基礎文書の索引 2.4（「射影」の変換）の留保「`JH` は P¹ の上の作用素ではなく、照合した範囲では P¹ のモデルと結ぶ Lean の文はない」（舞台 P¹ は索引 1.4）。
- 推薦案 `pag2_p1_gluing_preregistration.md` §4 を、2026-11-20 06:55 に著者が採用した（「進めてください」）。
- 著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」の読みの材料（読みの地位は変えない）。
- この文書の文に `JH` は現れない。Lean で結んだのは 𝔀（`rootNum`）の値と P¹ の赤道の係数で、留保「照合した範囲では `JH` と P¹ のモデルを結ぶ Lean の文はない」はこの文書の後も残る。

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
この条件を満たす位相は 𝔀 だけではない（少なくとも、単数 u による √χ(u) の分と指標ごとの符号 ±1 の分がある。盲検の手計算、確信度：中〜高。構築側の数値が確かめたのは r = (φ/𝔀)² の取りうる値の数だけ。`pag2_p1_gluing_preregistration.md`）。
A1 は導かれない。p = 2（すべての n）と p = 3、n = 0 では原始指標の三つ組がなく、5 つの文は空（独立照合の指摘。p = 2 は Part 26（PAG30）の注意とも合う）。
仮定は必要十分ではない：1〜3 では χ₁χ₂ の原始性は不要に見え、χ₁・χ₂ の原始性が中身を運ぶのは n = 0 だけ（n ≥ 1 では両辺が 0 になる。独立照合の手計算）。
4・5 では χ₁χ₂ の原始性を外すと偽になる（独立照合の反例。数値 `records/audit266/numeric/unit_point_ratio.py`：K = n+1、(p, K) = (5,1), (7,1), (3,2), (5,2) の χ₁χ₂ が原始的でない 80 組すべてで、定理 4 の係数では等式が破れる）。
反例は、n ≥ 1 では単数でない点にだけ、n = 0 では単数の点（χ₂ = χ̄₁、x = 1 など）にも出る（統合照合の照合者の数値）。
J ≠ 0 なら、単数の点での比 B_N/B_S は conj(J)/J で、conj(Ĵ)² に等しいのは |J|² = N のとき（Lean の外。再照合者の手計算、確信度：中〜高。数値は同じスクリプトの J ≠ 0 の組。
n ≥ 1 で χ₁χ₂ が原始的でない組は、数値で調べた範囲ではすべて J = 0 で、比は定まらない（構築側は K = n+1 = 2 の p = 3, 5 の 72 組、再照合 R2 の照合者は p = 7, 11 の K = 2 と p = 3 の K = 3, 4 と p = 5 の K = 3 の 3,536 組。一般の場合は見込み））。χ₁・χ₂・χ₁χ₂ が原始的なときの比 conj(J)/J は、関数全体の等式として Part 20（PAG24）の `PAG.Part24.equator_intertwine` にある。
4・5 は Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換えで、絡み合いの中身はそちらにある（名前空間 `PAG.Part25` は Part 21（PAG25）を指し、Part 25（PAG29）とは別）。

ラベル（見込み。Part を閉じるときに確定）：1 は［既知］（積が原始的ならヤコビ和はガウス和の比、|τ|² = N。K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15・3.12。法 m は一般で ℤ/p^(n+1) を覆う（WebFetch の要約で確認））。
2・3 は［再導出（小さい）］（1 と `rootNum` の定義からの直接の帰結。符号 s つきの形・𝔀 による形を書いた文献は見つかっていない。Long–Pigno–Pinner（arXiv:1410.6179）の式 (10) は符号のない比で、すべて原始的なときの J = G₁G₂/G₁₂（WebFetch の要約で確認）。統合照合 I の案は「［既知］の直接の帰結」。このプロジェクトのラベルは［既知／再導出／新規候補］の 3 つで、既知の定理からの直接の帰結でその形を書いた文献が見つかっていないものは［再導出（小さい）］としてきたので、そちらにした）。
4・5 は［再導出（小さい）］。新規候補なし。
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
