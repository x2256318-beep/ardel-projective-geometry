# 依頼：Part 257（PAG261.lean）の独立照合

あなたは、このパートの作成に関わっていない照合者です。この 1 つのファイルだけを Read で読んでください（ほかのツールは使わないでください）。

背景：Lean 4 / Mathlib による形式化の鎖（PAG.lean〜PAG261.lean）。PAG 2.0 の Part n はファイル PAG(n+4).lean、名前空間 PAG.PartNNN の NNN はファイル番号。
「素点」「局所因子」「貼り合わせ」「公準 A1」は著者の解釈の層の言葉で、Lean の文には出てこない。数値の確認は証明ではない。

確かめてほしいこと（形式文の全文と、使った前の鎖の宣言の形式文の全文を下に付けます）：
1. 形式文：各定理の文は（仮定のもとで）偽・空虚・自明すぎる（主張の言葉と別物）ものがないか。仮定が強すぎて中身がなくなっていないか（例：Nodup・互いに素の仮定）。定義 lvl・listChar・cross・oddCount は意図どおりか。
2. 文面と形式文のずれ：Lean の冒頭の説明・docstring・ノートの「結論」「読み」「位置づけ」「検証表」が、形式文の言える範囲を越えていないか（格上げ、範囲の書き落とし、「Lean で確認」「Lean ではつないでいない」の書き分けの誤り）。題は形式文から起こしてあるか。
3. 内部照合：下の前の鎖の宣言と比べて、PAG261 の文が同じ文・直ちに出る・数行で出るものはないか（ノート §7 の記録と食い違わないか）。
4. 数値照合 step280 の項目が、Lean の文（または「Lean にしていない」と書いたもの）と対応しているか。
5. そのほか気づいたこと（言い方、確信度の付け方、収束アラームの書き方など）。

出力の形：
## 1. 形式文の判定（定理ごとに 1 行：問題なし／問題あり（理由））
## 2. 文面の指摘（表：場所｜問題｜直し方の案｜確信度 高・中・低）
## 3. 内部照合の指摘
## 4. 数値照合との対応
## 5. 総評（3 行まで）
見ていないもの・確かめていないものも書いてください。

---
# A. PAG261.lean（全文）
```lean
/-
アーデル射影幾何 — Part 257（PAG 2.0）：互いに素な法の並びの指標の積での、ガウス和と W の分解（すべての成分の局所因子の積）

問いの出所：著者の選択（2026-11-14 20:59、着手前の文書 `pag2_part257_preregistration.md` の候補 P1）。開始条件 2（方向βの
登録ファイルとの突き合わせ）は、著者の判断で保留のまま始めた（登録ファイルは届いていない）。
幾何の言葉での問い（読み）：大域の貼り合わせ（U の固有値 W）は、∞ を含む各点の局所の因子の積に分かれるか。
Lean が答えるのは、互いに素な法の並び N_1, …, N_k の指標の積（法 N_1·…·N_k）の上での、ガウス和 τ と W の式まで。

読みの言葉：「貼り合わせ U」「公準 A1 の位相」は Part 254（PAG258.lean）の `UA1`・`phaseA1`。W は Part 252（PAG256.lean）の
`rootNum`（= τ(χ)/(i^a·√n)。原始のときルート数）、偶奇の因子 `parFac`（偶で 1、奇で −i）。「素点」「局所因子」「重なり」は
著者の解釈の層の言葉で、Lean の文には出てこない。偶奇の因子が無限素点の局所因子にあたる、も読み。

Lean の文（すべて既知の事実の Lean 化。Montgomery–Vaughan の Theorem 9.6 を繰り返したものと、そのルート数版）：
1. 法の並びの積 `lvl`（先頭 × 残り）と指標の積 `listChar`（先頭の指標と残りの積を Part 256 の `prodChar` でつなぐ）。
   値は成分の値の積（`listChar_natCast`：自然数で、`listChar_neg_one`：−1 で）。
2. ガウス和：τ(listChar χ l) = 交差項·∏_i τ(χ_i)（`gaussSum_listChar`。法は互いに素。原始性は要らない）。交差項 `cross` は
   漸化式で定め、閉じた形が 2 つ：形 (I) ∏_i χ_i(∏_{j≠i} N_j)（`cross_eq_formI`）と形 (II) ∏_i ∏_{j≠i} χ_j(N_i)
   （`cross_eq_formII`。成分 i の因子を、ほかの成分を N_i で読んだ値で書く形）。
3. W：W(listChar χ l) = ε_∞·∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)/√N_i（`rootNum_listChar_formI`）、
   = ε_∞·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)（`rootNum_listChar_formII`）。ε_∞ = `parFac`(listChar χ l)。
4. ∞ の因子の符号：ε_∞(listChar χ l) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数 `oddCount`。`parFac_listChar`）。
   したがって W(listChar χ l) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（`rootNum_listChar`。成分 2 つでは Part 256 の `rootNum_prodChar` と
   同じ式になる。Lean ではつないでいない）。
5. 原始性：すべての成分が原始 ⇔ 積が原始（`isPrimitive_listChar_iff`）。原始なら UA1 の固有値 phaseA1 も同じ式
   （`phaseA1_listChar`）。
6. 分解：法 lvl l の指標は、どれも成分の積 listChar χ l の形に書け（`exists_listChar`。並びに重複なし）、成分は一意
   （`listChar_injective`）。
7. すべての素数への分解：法 n の指標 Ψ は、素数冪の法 p^{v_p(n)}（0 でないことは Part 236（PAG240）の instance `neZero_ordProj`）の成分 χ_p で、自然数での値が ∏_p χ_p(x)、
   τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)})（`gaussSum_primeFactors`。形 (II)）。退化例（成分 1 つ）は τ(listChar χ [a]) = τ(χ_a)
   （`gaussSum_listChar_singleton`）。

前の鎖の定理を使い、示し直していないもの：Part 199（PAG203）の `gaussSum_level_one`、Part 236（PAG240）の `neZero_ordProj`、Part 189（PAG193）の `gaussSum_mul_coprime`・`mul_changeLevel_apply`、
Part 190（PAG194）の `decomp`・`isPrimitive_iff`・`comp₁_mul`・`comp₂_mul`、Part 232（PAG236）の `charMul_injective`、
Part 252（PAG256）の `rootNum_eq`・`parFac_of_even`、Part 254（PAG258）の `phaseA1_of_isPrimitive`、Part 256（PAG260）の
`prodChar`・`prodChar_neg_one`・`parFac_prodChar`・`crossSign`。

言い方の注意：文献では、大域の ε 因子は局所の ε 因子の積（Tate、Deligne）。形 (II) の成分 i の因子 (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i) は、
加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}（Tate の学位論文の規約）にとったときのイデール類指標の局所定数と一致し、
∞ の因子は i^{−a}（盲検の問いテストと私の手計算。Lean では示していない）。規約を逆にすると各因子が χ_p(−1) 倍、
∞ の因子が i^{a} になるが、積は変わらない。A1 は公準のまま。ここでの文は τ・W・phaseA1 についての恒等式で、A1 から何かを出すものではない。

範囲：互いに素な法の並び（リスト）の上の式。法 n の任意の指標についての文は 7 のガウス和と分解まで（W の形は、listChar の形の
指標の上で 3・4）。Lean にしていないこと（数値は step280.py の項目番号）：イデール類指標と Tate の局所定数そのもの、
原始でない指標の phaseA1 を導手を割る素点だけで書く形（着手前の数値 (5)）、並べ替えで listChar の値が変わらないこと
（数値 (10)）、対照群 F_q[t]（∞ の因子は √q/τ(η)。盲検の答えで、私は計算していない）。

内部照合（2026-11-14 からの必須の手順）：着手の前に、xlsx の「定理と証明」と Lean の全宣言の文を検索した。成分 2 つの式は
前の鎖にある（Part 189 の `gaussSum_mul_coprime`・`z_mul_coprime`、Part 256 の `rootNum_prodChar`）。任意個の成分の明示の積、
形 (II)、符号 (−1)^{k(k−1)/2} の文は見つからなかった（網羅ではない）。近いもの：Part 192（PAG196）の `z_hall`（ホール成分 2 つ、
ずれは「1 の冪根がある」の形）、Part 193（PAG197）の `LocalCrit`・`prod_root_iff_local`（平方因子のない素数成分での、1 の冪根に
なる条件）、Part 127（PAG131）以降の素数冪の成分の積の位数の定理（積 ∏ τ(χ_i)/√ の位数で、合成した指標の τ ではない）。
閉じる前の照合（全宣言 4310 件の書き出し、候補選び上位 20、`#dupcheck`・`#defeqcheck` を両向きに）：1 回目で、下書きの
`gaussSum_level_one` が Part 199（PAG203）の同名の定理と同じ文、法 p^{v_p(n)} が 0 でないことの instance が Part 236（PAG240）の
`neZero_ordProj` と同じ文だった（どちらも Lean で両向きに確認）。両方を消して前の鎖のものを使い、2 回目（31 件・1132 回）は一致 0。
網羅ではない（候補選びは型に現れる定数の近さで、上位 20 まで）。
-/
import PAG260

open ZMod Complex

namespace PAG.Part261

variable {ι : Type*} (N : ι → ℕ) [hN : ∀ i, NeZero (N i)]

/-- 法の並びの積（先頭 × 残りの積）。 -/
def lvl : List ι → ℕ
  | [] => 1
  | a :: l => N a * lvl l

omit hN in
theorem lvl_cons (a : ι) (l : List ι) : lvl N (a :: l) = N a * lvl N l := rfl

omit hN in
theorem lvl_eq_prod (l : List ι) : lvl N l = (l.map N).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [lvl, ih]

instance lvl_neZero (l : List ι) : NeZero (lvl N l) := ⟨by
  induction l with
  | nil => simp [lvl]
  | cons a l ih => exact mul_ne_zero (NeZero.ne (N a)) ih⟩

variable {N}

/-- 法の並びの指標の積（法 lvl l）。先頭の指標と残りの積を、Part 256 の `prodChar` でつなぐ。 -/
noncomputable def listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) :
    (l : List ι) → DirichletCharacter ℂ (lvl N l)
  | [] => 1
  | a :: l => PAG.Part260.prodChar (χ a) (listChar χ l)

/-- 交差項（漸化式）。 -/
noncomputable def cross (χ : ∀ i, DirichletCharacter ℂ (N i)) : List ι → ℂ
  | [] => 1
  | a :: l => χ a (lvl N l : ZMod (N a)) * listChar χ l (N a : ZMod (lvl N l)) * cross χ l

omit hN in
theorem coprime_lvl {a : ι} {l : List ι} (h : ∀ j ∈ l, (N a).Coprime (N j)) :
    (N a).Coprime (lvl N l) := by
  induction l with
  | nil => simp [lvl]
  | cons b l ih =>
    rw [lvl_cons]
    exact Nat.Coprime.mul_right (h b (by simp)) (ih fun j hj => h j (by simp [hj]))

/-- **ガウス和の分解（漸化式の形）**。 -/
theorem gaussSum_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
    gaussSum (listChar χ l) stdAddChar =
      cross χ l * (l.map fun i => gaussSum (χ i) stdAddChar).prod := by
  induction l with
  | nil =>
    show gaussSum (1 : DirichletCharacter ℂ 1) stdAddChar = 1 * 1
    rw [PAG.Part203.gaussSum_level_one]; ring
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have h : gaussSum (PAG.Part260.prodChar (χ a) (listChar χ l)) stdAddChar = _ :=
      PAG.Part193.gaussSum_mul_coprime (coprime_lvl hl.1) (χ a) (listChar χ l)
    show gaussSum (PAG.Part260.prodChar (χ a) (listChar χ l)) stdAddChar = _
    rw [h, ih hl.2]
    simp only [cross, List.map_cons, List.prod_cons]
    ring

theorem listChar_natCast (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) (n : ℕ) :
    listChar χ l (n : ZMod (lvl N l)) = (l.map fun j => χ j (n : ZMod (N j))).prod := by
  induction l with
  | nil =>
    show (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1
    exact MulChar.one_apply (isUnit_of_subsingleton _)
  | cons a l ih =>
    have h : PAG.Part260.prodChar (χ a) (listChar χ l) (n : ZMod (N a * lvl N l)) = _ :=
      PAG.Part193.mul_changeLevel_apply (χ a) (listChar χ l) (n : ZMod (N a * lvl N l))
    show PAG.Part260.prodChar (χ a) (listChar χ l) (n : ZMod (N a * lvl N l)) = _
    rw [h, ZMod.castHom_apply, ZMod.castHom_apply,
      ZMod.cast_natCast (dvd_mul_right _ _), ZMod.cast_natCast (dvd_mul_left _ _), ih]
    simp

theorem listChar_neg_one (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    listChar χ l (-1) = (l.map fun j => χ j (-1)).prod := by
  induction l with
  | nil =>
    show (1 : DirichletCharacter ℂ 1) (-1) = 1
    exact MulChar.one_apply isUnit_one.neg
  | cons a l ih =>
    show PAG.Part260.prodChar (χ a) (listChar χ l) (-1) = _
    rw [PAG.Part260.prodChar_neg_one, ih]
    simp

variable [DecidableEq ι]

/-- 交差項の形 (I)：∏_i χ_i(∏_{j≠i} N_j)。 -/
theorem cross_eq_formI (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) (hnd : l.Nodup) :
    cross χ l = (l.map fun i => χ i (((l.erase i).map N).prod : ZMod (N i))).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [cross, List.map_cons, List.prod_cons, List.erase_cons_head]
    rw [ih hnd.2, listChar_natCast, lvl_eq_prod]
    have key : (l.map fun i => χ i ((((a :: l).erase i).map N).prod : ZMod (N i))) =
        l.map fun i => χ i (N a : ZMod (N i)) * χ i (((l.erase i).map N).prod : ZMod (N i)) := by
      apply List.map_congr_left
      intro i hi
      have hne : a ≠ i := fun h => hnd.1 (h ▸ hi)
      rw [List.erase_cons_tail (by simpa using hne), List.map_cons, List.prod_cons, Nat.cast_mul,
        map_mul]
    rw [key, List.prod_map_mul]
    ring

/-- 交差項の形 (II)：∏_i ∏_{j≠i} χ_j(N_i)。 -/
theorem cross_eq_formII (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) (hnd : l.Nodup) :
    cross χ l = (l.map fun i => ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [cross, List.map_cons, List.prod_cons, List.erase_cons_head]
    rw [ih hnd.2, listChar_natCast, lvl_eq_prod]
    have key : (l.map fun i => (((a :: l).erase i).map fun j => χ j (N i : ZMod (N j))).prod) =
        l.map fun i => χ a (N i : ZMod (N a)) *
          ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod := by
      apply List.map_congr_left
      intro i hi
      have hne : a ≠ i := fun h => hnd.1 (h ▸ hi)
      rw [List.erase_cons_tail (by simpa using hne), List.map_cons, List.prod_cons]
    have hprod : χ a (((l.map N).prod : ℕ) : ZMod (N a)) =
        (l.map fun i => χ a (N i : ZMod (N a))).prod := by
      rw [Nat.cast_list_prod, map_list_prod, List.map_map, List.map_map]
      rfl
    rw [key, List.prod_map_mul, hprod]
    ring

omit hN [DecidableEq ι] in
theorem sqrt_lvl (l : List ι) :
    ((Real.sqrt (lvl N l) : ℝ) : ℂ) = (l.map fun i => ((Real.sqrt (N i) : ℝ) : ℂ)).prod := by
  induction l with
  | nil => simp [lvl]
  | cons a l ih =>
    rw [lvl_cons, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, ih]
    simp

omit hN [DecidableEq ι] in
theorem prod_map_div' {f g : ι → ℂ} (l : List ι) :
    (l.map fun i => f i / g i).prod = (l.map f).prod / (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, div_mul_div_comm]

/-- **W の分解（形 (II)）**：W(χ) = ε_∞(χ)·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)。 -/
theorem rootNum_listChar_formII (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hnd : l.Nodup) :
    PAG.Part256.rootNum (listChar χ l) = PAG.Part256.parFac (listChar χ l) *
      (l.map fun i => gaussSum (χ i) stdAddChar / ((Real.sqrt (N i) : ℝ) : ℂ) *
        ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod).prod := by
  rw [PAG.Part256.rootNum_eq, gaussSum_listChar χ l hl, cross_eq_formII χ l hnd, sqrt_lvl,
    List.prod_map_mul, prod_map_div']
  ring

/-- **W の分解（形 (I)）**：W(χ) = ε_∞(χ)·∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)/√N_i。 -/
theorem rootNum_listChar_formI (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hnd : l.Nodup) :
    PAG.Part256.rootNum (listChar χ l) = PAG.Part256.parFac (listChar χ l) *
      (l.map fun i => χ i (((l.erase i).map N).prod : ZMod (N i)) *
        (gaussSum (χ i) stdAddChar / ((Real.sqrt (N i) : ℝ) : ℂ))).prod := by
  rw [PAG.Part256.rootNum_eq, gaussSum_listChar χ l hl, cross_eq_formI χ l hnd, sqrt_lvl,
    List.prod_map_mul, prod_map_div']
  ring

omit [DecidableEq ι] in
open Classical in
/-- 奇の成分の個数。 -/
noncomputable def oddCount (χ : ∀ i, DirichletCharacter ℂ (N i)) : List ι → ℕ
  | [] => 0
  | a :: l => (if (χ a).Odd then 1 else 0) + oddCount χ l

omit hN [DecidableEq ι] in
theorem not_odd_of_even {n : ℕ} {ψ : DirichletCharacter ℂ n} (h : ψ.Even) : ¬ψ.Odd := by
  intro h'
  unfold DirichletCharacter.Odd at h'; unfold DirichletCharacter.Even at h
  rw [h] at h'; norm_num at h'

omit [DecidableEq ι] in
theorem listChar_neg_one_pow (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    listChar χ l (-1) = (-1) ^ oddCount χ l := by
  rw [listChar_neg_one]
  induction l with
  | nil => simp [oddCount]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, oddCount, ih, pow_add]
    rcases (χ a).even_or_odd with h | h
    · have hn := not_odd_of_even h
      unfold DirichletCharacter.Even at h
      simp [hn, h]
    · have h' := h
      unfold DirichletCharacter.Odd at h'
      simp [h, h']

omit hN in
theorem tri_succ (k : ℕ) : (1 + k) * (1 + k - 1) / 2 = k * (k - 1) / 2 + k := by
  rcases k with _ | m
  · simp
  · have e : (1 + (m + 1)) * (1 + (m + 1) - 1) = (m + 1) * (m + 1 - 1) + (m + 1) * 2 := by
      simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel]; ring
    rw [e, Nat.add_mul_div_right _ _ (by norm_num)]

omit [DecidableEq ι] in
/-- **∞ の因子の符号**：ε_∞(χ) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数。Part 256 の s の一般化）。 -/
theorem parFac_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    PAG.Part256.parFac (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) *
        (l.map fun i => PAG.Part256.parFac (χ i)).prod := by
  induction l with
  | nil =>
    show PAG.Part256.parFac (1 : DirichletCharacter ℂ 1) = _
    rw [PAG.Part256.parFac_of_even (MulChar.one_apply isUnit_one.neg)]
    simp [oddCount]
  | cons a l ih =>
    show PAG.Part256.parFac (PAG.Part260.prodChar (χ a) (listChar χ l)) = _
    rw [PAG.Part260.parFac_prodChar, ih]
    have hk := listChar_neg_one_pow χ l
    have hodd : (listChar χ l).Odd ↔ _root_.Odd (oddCount χ l) := by
      unfold DirichletCharacter.Odd
      rw [hk]
      exact neg_one_pow_eq_neg_one_iff_odd (by norm_num)
    simp only [oddCount, List.map_cons, List.prod_cons]
    unfold PAG.Part260.crossSign
    rcases (χ a).even_or_odd with h | h
    · have hn := not_odd_of_even h
      simp only [hn, false_and, ↓reduceIte, zero_add]
      ring
    · simp only [h, true_and, ↓reduceIte, hodd]
      rw [tri_succ, pow_add]
      by_cases hk2 : _root_.Odd (oddCount χ l)
      · simp only [hk2, ↓reduceIte, hk2.neg_one_pow]; ring
      · simp only [hk2, ↓reduceIte, (Nat.not_odd_iff_even.mp hk2).neg_one_pow]; ring

omit [DecidableEq ι] in
/-- **W の分解（符号つき）**：W(χ) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（成分 2 つでは Part 256 の `rootNum_prodChar` と同じ式。Lean ではつないでいない）。 -/
theorem rootNum_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
    PAG.Part256.rootNum (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) * cross χ l *
        (l.map fun i => PAG.Part256.rootNum (χ i)).prod := by
  rw [PAG.Part256.rootNum_eq, gaussSum_listChar χ l hl, parFac_listChar, sqrt_lvl]
  simp_rw [PAG.Part256.rootNum_eq]
  rw [prod_map_div', List.prod_map_mul]
  ring

omit [DecidableEq ι] in
/-- 原始性：互いに素な法で、すべての成分が原始 ⇔ 積が原始（Part 190 の `isPrimitive_mul`・`isPrimitive_iff`・`comp₁_mul`・`comp₂_mul` を使う）。 -/
theorem isPrimitive_listChar_iff (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
    (listChar χ l).IsPrimitive ↔ ∀ i ∈ l, (χ i).IsPrimitive := by
  induction l with
  | nil =>
    show (1 : DirichletCharacter ℂ 1).IsPrimitive ↔ _
    simpa using (DirichletCharacter.isPrimitive_one_level_one : (1 : DirichletCharacter ℂ 1).IsPrimitive)
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have hc := coprime_lvl hl.1
    have hiff := PAG.Part194.isPrimitive_iff hc (PAG.Part260.prodChar (χ a) (listChar χ l))
    have h1 : PAG.Part194.comp₁ hc (PAG.Part260.prodChar (χ a) (listChar χ l)) = χ a :=
      PAG.Part194.comp₁_mul hc (χ a) (listChar χ l)
    have h2 : PAG.Part194.comp₂ hc (PAG.Part260.prodChar (χ a) (listChar χ l)) = listChar χ l :=
      PAG.Part194.comp₂_mul hc (χ a) (listChar χ l)
    rw [h1, h2, ih hl.2] at hiff
    show (PAG.Part260.prodChar (χ a) (listChar χ l)).IsPrimitive ↔ _
    rw [hiff]
    simp

omit [DecidableEq ι] in
/-- 原始指標の上では、UA1 の固有値 phaseA1 も同じ式で分かれる。 -/
theorem phaseA1_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hp : ∀ i ∈ l, (χ i).IsPrimitive) :
    PAG.Part258.phaseA1 (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) * cross χ l *
        (l.map fun i => PAG.Part258.phaseA1 (χ i)).prod := by
  rw [PAG.Part258.phaseA1_of_isPrimitive ((isPrimitive_listChar_iff χ l hl).mpr hp),
    rootNum_listChar χ l hl]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  rw [PAG.Part258.phaseA1_of_isPrimitive (hp i hi)]

omit hN [DecidableEq ι] in
theorem listChar_congr {χ χ' : ∀ i, DirichletCharacter ℂ (N i)} (l : List ι)
    (h : ∀ i ∈ l, χ i = χ' i) : listChar χ l = listChar χ' l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show PAG.Part260.prodChar (χ a) (listChar χ l) = PAG.Part260.prodChar (χ' a) (listChar χ' l)
    rw [h a (by simp), ih fun i hi => h i (by simp [hi])]

/-- **分解の存在**：法 lvl l（互いに素な法の積）の指標は、どれも成分の積 listChar χ l の形に書ける（Part 190 の `decomp` を使う）。 -/
theorem exists_listChar (l : List ι) (hnd : l.Nodup)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (Ψ : DirichletCharacter ℂ (lvl N l)) :
    ∃ χ : ∀ i, DirichletCharacter ℂ (N i), listChar χ l = Ψ := by
  induction l with
  | nil =>
    refine ⟨fun _ => 1, ?_⟩
    show (1 : DirichletCharacter ℂ 1) = Ψ
    exact (DirichletCharacter.level_one Ψ).symm
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hl
    have hc := coprime_lvl hl.1
    obtain ⟨χ', hχ'⟩ := ih hnd.2 hl.2 (PAG.Part194.comp₂ hc Ψ)
    refine ⟨Function.update χ' a (PAG.Part194.comp₁ hc Ψ), ?_⟩
    show PAG.Part260.prodChar _ (listChar _ l) = Ψ
    rw [Function.update_self,
      listChar_congr l (fun i hi => Function.update_of_ne (fun h : i = a => hnd.1 (h ▸ hi)) _ _), hχ']
    exact (PAG.Part194.decomp hc Ψ).symm

omit [DecidableEq ι] in
/-- **分解の一意性**：listChar χ l = listChar χ' l なら、l の各成分で χ_i = χ'_i（Part 232 の `charMul_injective` を使う）。 -/
theorem listChar_injective (l : List ι) (hl : l.Pairwise fun i j => (N i).Coprime (N j))
    {χ χ' : ∀ i, DirichletCharacter ℂ (N i)} (h : listChar χ l = listChar χ' l) :
    ∀ i ∈ l, χ i = χ' i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have h' : PAG.Part236.charMul (χ a) (listChar χ l) = PAG.Part236.charMul (χ' a) (listChar χ' l) := h
    obtain ⟨h1, h2⟩ := PAG.Part236.charMul_injective (coprime_lvl hl.1) h'
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact h1
    · exact ih hl.2 h2 i hi

omit [DecidableEq ι] in
/-- 退化例（成分 1 つ）：τ(listChar χ [a]) = τ(χ_a)。 -/
theorem gaussSum_listChar_singleton (χ : ∀ i, DirichletCharacter ℂ (N i)) (a : ι) :
    gaussSum (listChar χ [a]) stdAddChar = gaussSum (χ a) stdAddChar := by
  rw [gaussSum_listChar χ [a] (List.pairwise_singleton _ _)]
  have h1 : listChar χ [] (N a : ZMod (lvl N [])) = 1 := listChar_natCast χ [] (N a)
  have h2 : χ a (lvl N [] : ZMod (N a)) = 1 := by
    show χ a ((1 : ℕ) : ZMod (N a)) = 1
    rw [Nat.cast_one, map_one]
  simp only [cross, h1, h2, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

end PAG.Part261

namespace PAG.Part261

theorem pairwise_primeFactors (n : ℕ) :
    n.primeFactors.toList.Pairwise fun p q => (p ^ n.factorization p).Coprime (q ^ n.factorization q) := by
  refine (Finset.nodup_toList _).imp_of_mem (fun hp hq hne => ?_)
  have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hp)
  have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hq)
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' hq').mpr hne)

theorem lvl_primeFactors (n : ℕ) (hn : n ≠ 0) : lvl (fun p => p ^ n.factorization p) n.primeFactors.toList = n := by
  rw [lvl_eq_prod, Finset.prod_map_toList]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-- **すべての素数への分解**：法 n の指標 Ψ は、素数冪の法 p^{v_p(n)} の成分 χ_p の積で（自然数での値が ∏ χ_p）、
τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)})（形 (II)）。 -/
theorem gaussSum_primeFactors (n : ℕ) [NeZero n] (Ψ : DirichletCharacter ℂ n) :
    ∃ χ : ∀ p, DirichletCharacter ℂ (p ^ n.factorization p),
      (∀ x : ℕ, Ψ x = (n.primeFactors.toList.map fun p => χ p (x : ZMod (p ^ n.factorization p))).prod) ∧
      gaussSum Ψ stdAddChar = (n.primeFactors.toList.map fun p => gaussSum (χ p) stdAddChar *
        ((n.primeFactors.toList.erase p).map fun q => χ q ((p ^ n.factorization p : ℕ) : ZMod (q ^ n.factorization q))).prod).prod := by
  have key : ∀ (m : ℕ) [NeZero m], lvl (fun p => p ^ n.factorization p) n.primeFactors.toList = m →
      ∀ Ψ : DirichletCharacter ℂ m, ∃ χ : ∀ p, DirichletCharacter ℂ (p ^ n.factorization p),
        (∀ x : ℕ, Ψ x = (n.primeFactors.toList.map fun p => χ p (x : ZMod (p ^ n.factorization p))).prod) ∧
        gaussSum Ψ stdAddChar = (n.primeFactors.toList.map fun p => gaussSum (χ p) stdAddChar *
          ((n.primeFactors.toList.erase p).map fun q => χ q ((p ^ n.factorization p : ℕ) : ZMod (q ^ n.factorization q))).prod).prod := by
    intro m _ hm Ψ
    subst hm
    obtain ⟨χ, hχ⟩ := exists_listChar _ (Finset.nodup_toList _) (pairwise_primeFactors n) Ψ
    refine ⟨χ, fun x => ?_, ?_⟩
    · rw [← hχ, listChar_natCast]
    · rw [← hχ, gaussSum_listChar χ _ (pairwise_primeFactors n),
        cross_eq_formII χ _ (Finset.nodup_toList _), List.prod_map_mul, mul_comm]
  exact key n (lvl_primeFactors n (NeZero.ne n)) Ψ

end PAG.Part261

#print axioms PAG.Part261.lvl_cons
#print axioms PAG.Part261.lvl_eq_prod
#print axioms PAG.Part261.coprime_lvl
#print axioms PAG.Part261.gaussSum_listChar
#print axioms PAG.Part261.listChar_natCast
#print axioms PAG.Part261.listChar_neg_one
#print axioms PAG.Part261.cross_eq_formI
#print axioms PAG.Part261.cross_eq_formII
#print axioms PAG.Part261.sqrt_lvl
#print axioms PAG.Part261.prod_map_div'
#print axioms PAG.Part261.rootNum_listChar_formII
#print axioms PAG.Part261.rootNum_listChar_formI
#print axioms PAG.Part261.not_odd_of_even
#print axioms PAG.Part261.listChar_neg_one_pow
#print axioms PAG.Part261.tri_succ
#print axioms PAG.Part261.parFac_listChar
#print axioms PAG.Part261.rootNum_listChar
#print axioms PAG.Part261.isPrimitive_listChar_iff
#print axioms PAG.Part261.phaseA1_listChar
#print axioms PAG.Part261.listChar_congr
#print axioms PAG.Part261.exists_listChar
#print axioms PAG.Part261.listChar_injective
#print axioms PAG.Part261.gaussSum_listChar_singleton
#print axioms PAG.Part261.pairwise_primeFactors
#print axioms PAG.Part261.lvl_primeFactors
#print axioms PAG.Part261.gaussSum_primeFactors

```

# B. PAG261.out（組み立ての出力）
```
'PAG.Part261.lvl_cons' does not depend on any axioms
'PAG.Part261.lvl_eq_prod' depends on axioms: [propext]
'PAG.Part261.coprime_lvl' depends on axioms: [propext, Quot.sound]
'PAG.Part261.gaussSum_listChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.listChar_natCast' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.listChar_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.cross_eq_formI' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.cross_eq_formII' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.sqrt_lvl' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.prod_map_div'' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.rootNum_listChar_formII' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.rootNum_listChar_formI' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.not_odd_of_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.listChar_neg_one_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.tri_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.parFac_listChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.rootNum_listChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.isPrimitive_listChar_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.phaseA1_listChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.listChar_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.exists_listChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.listChar_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.gaussSum_listChar_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.pairwise_primeFactors' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.lvl_primeFactors' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part261.gaussSum_primeFactors' depends on axioms: [propext, Classical.choice, Quot.sound]

```

# C. 使った前の鎖の宣言（形式文の全文）
### PAG193（名前空間 PAG.Part193）::gaussSum_mul_coprime
```lean
theorem gaussSum_mul_coprime (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar
      = χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar
```

### PAG193（名前空間 PAG.Part193）::mul_changeLevel_apply
```lean
theorem mul_changeLevel_apply (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) (x : ZMod (N₁ * N₂)) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) x
      = χ₁ (ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁) x) *
        χ₂ (ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂) x)
```

### PAG193（名前空間 PAG.Part193）::z_mul_coprime
```lean
theorem z_mul_coprime (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar
        / ((Real.sqrt ((N₁ * N₂ : ℕ) : ℝ) : ℝ) : ℂ)
      = χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) *
        ((gaussSum χ₁ stdAddChar / ((Real.sqrt (N₁ : ℝ) : ℝ) : ℂ)) *
          (gaussSum χ₂ stdAddChar / ((Real.sqrt (N₂ : ℝ) : ℝ) : ℂ))) ∧
      ∃ M : ℕ, 0 < M ∧ (χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂)) ^ M = 1
```

### PAG194（名前空間 PAG.Part194）::comp₁
```lean
noncomputable def comp₁ (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) :
    DirichletCharacter ℂ N₁ where
  toFun a := χ ((crt hcop).symm (a, 1))
  map_one' := by
    show χ ((crt hcop).symm 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    show χ ((crt hcop).symm (a * b, 1)) = χ ((crt hcop).symm (a, 1)) * χ ((crt hcop).symm (b, 1))
    rw [show ((a * b, 1) : ZMod N₁ × ZMod N₂) = (a, 1) * (b, 1) by simp, map_mul, map_mul]
  map_nonunit' a ha := by
    apply MulChar.map_nonunit
    intro hu
    apply ha
    have := hu.map (crt hcop)
    rw [RingEquiv.apply_symm_apply] at this
    exact (Prod.isUnit_iff.mp this).1
```

### PAG194（名前空間 PAG.Part194）::comp₂
```lean
noncomputable def comp₂ (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) :
    DirichletCharacter ℂ N₂ where
  toFun b := χ ((crt hcop).symm (1, b))
  map_one' := by
    show χ ((crt hcop).symm 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    show χ ((crt hcop).symm (1, a * b)) = χ ((crt hcop).symm (1, a)) * χ ((crt hcop).symm (1, b))
    rw [show ((1, a * b) : ZMod N₁ × ZMod N₂) = (1, a) * (1, b) by simp, map_mul, map_mul]
  map_nonunit' b hb := by
    apply MulChar.map_nonunit
    intro hu
    apply hb
    have := hu.map (crt hcop)
    rw [RingEquiv.apply_symm_apply] at this
    exact (Prod.isUnit_iff.mp this).2
```

### PAG194（名前空間 PAG.Part194）::decomp
```lean
theorem decomp (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) :
    χ = (comp₁ hcop χ).changeLevel (dvd_mul_right N₁ N₂) *
      (comp₂ hcop χ).changeLevel (dvd_mul_left N₂ N₁)
```

### PAG194（名前空間 PAG.Part194）::isPrimitive_iff
```lean
theorem isPrimitive_iff (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) :
    χ.IsPrimitive ↔ (comp₁ hcop χ).IsPrimitive ∧ (comp₂ hcop χ).IsPrimitive
```

### PAG194（名前空間 PAG.Part194）::comp₁_mul
```lean
theorem comp₁_mul (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    comp₁ hcop (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) = χ₁
```

### PAG194（名前空間 PAG.Part194）::comp₂_mul
```lean
theorem comp₂_mul (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    comp₂ hcop (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) = χ₂
```

### PAG194（名前空間 PAG.Part194）::isPrimitive_mul
```lean
theorem isPrimitive_mul (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).IsPrimitive
```

### PAG236（名前空間 PAG.Part236）::charMul
```lean
noncomputable def charMul {m n : ℕ} (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) :
    DirichletCharacter ℂ (m * n) :=
  DirichletCharacter.changeLevel (dvd_mul_right m n) χ₁ * DirichletCharacter.changeLevel (dvd_mul_left n m) χ₂
```

### PAG236（名前空間 PAG.Part236）::charMul_injective
```lean
theorem charMul_injective {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n)
    {χ₁ χ₁' : DirichletCharacter ℂ m} {χ₂ χ₂' : DirichletCharacter ℂ n}
    (h : charMul χ₁ χ₂ = charMul χ₁' χ₂') : χ₁ = χ₁' ∧ χ₂ = χ₂'
```

### PAG256（名前空間 PAG.Part256）::parFac
```lean
noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2
```

### PAG256（名前空間 PAG.Part256）::parFac_of_even
```lean
omit [NeZero N] in
theorem parFac_of_even {χ : DirichletCharacter ℂ N} (h : χ.Even) : parFac χ = 1
```

### PAG256（名前空間 PAG.Part256）::parFac_of_odd
```lean
omit [NeZero N] in
theorem parFac_of_odd {χ : DirichletCharacter ℂ N} (h : χ.Odd) : parFac χ = -I
```

### PAG256（名前空間 PAG.Part256）::rootNum
```lean
open Classical in
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))
```

### PAG256（名前空間 PAG.Part256）::rootNum_eq
```lean
theorem rootNum_eq (χ : DirichletCharacter ℂ N) :
    rootNum χ = parFac χ * gaussSum χ stdAddChar / (Real.sqrt N : ℂ)
```

### PAG258（名前空間 PAG.Part258）::phaseA1
```lean
noncomputable def phaseA1 (χ : DirichletCharacter ℂ N) : ℂ := rootNum χ.primitiveCharacter
```

### PAG258（名前空間 PAG.Part258）::phaseA1_of_isPrimitive
```lean
theorem phaseA1_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    phaseA1 χ = rootNum χ
```

### PAG260（名前空間 PAG.Part260）::prodChar
```lean
noncomputable def prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ (M * N) :=
  changeLevel (dvd_mul_right M N) χ₁ * changeLevel (dvd_mul_left N M) χ₂
```

### PAG260（名前空間 PAG.Part260）::prodChar_neg_one
```lean
theorem prodChar_neg_one (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    prodChar χ₁ χ₂ (-1) = χ₁ (-1) * χ₂ (-1)
```

### PAG260（名前空間 PAG.Part260）::crossSign
```lean
open Classical in
noncomputable def crossSign (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
  if χ₁.Odd ∧ χ₂.Odd then -1 else 1
```

### PAG260（名前空間 PAG.Part260）::parFac_prodChar
```lean
theorem parFac_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.parFac (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * PAG.Part256.parFac χ₁ * PAG.Part256.parFac χ₂
```

### PAG260（名前空間 PAG.Part260）::rootNum_prodChar
```lean
theorem rootNum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.rootNum (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂)
```

### PAG260（名前空間 PAG.Part260）::gaussSum_prodChar
```lean
theorem gaussSum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    gaussSum (prodChar χ₁ χ₂) stdAddChar =
      χ₁ (N : ZMod M) * χ₂ (M : ZMod N) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar
```

### PAG203（名前空間 PAG.Part203）::gaussSum_level_one
```lean
theorem gaussSum_level_one (χ : DirichletCharacter ℂ 1) : gaussSum χ stdAddChar = 1
```

### PAG240（名前空間 PAG.Part240）::neZero_ordProj
```lean
instance neZero_ordProj (N p : ℕ) : NeZero (p ^ N.factorization p) := ⟨(Nat.ordProj_pos N p).ne'⟩
```

### PAG240（名前空間 PAG.Part240）::ppow
```lean
def ppow (N p : ℕ) : ℕ+ := ⟨p ^ N.factorization p, Nat.ordProj_pos N p⟩
```

### PAG196（名前空間 PAG.Part196）::zN
```lean
noncomputable def zN {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)


```

### PAG196（名前空間 PAG.Part196）::z_hall
```lean
theorem z_hall {N : ℕ} [NeZero N] (A B : ℕ) [NeZero A] [NeZero B] (hAB : A * B = N)
    (hcop : A.Coprime B) (χ : DirichletCharacter ℂ N) :
    ∃ ζ : ℂ, (∃ K : ℕ, 0 < K ∧ ζ ^ K = 1) ∧
      zN χ = ζ * (zN (hall A B hAB hcop χ) * zN (hall B A ((mul_comm B A).trans hAB) hcop.symm χ))
```

### PAG197（名前空間 PAG.Part197）::LocalCrit
```lean
def LocalCrit {ι : Type*} [Fintype ι] (N : ι → ℕ) (χ : ∀ i, DirichletCharacter ℂ (N i))
    (a : ι → ℤ) : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], ∃ K : ℕ, 0 < K ∧
    (∏ i ∈ univ.filter (fun i => q ∣ N i ∧ ¬ q ^ 2 ∣ N i), zN (pcomp q (χ i)) ^ a i) ^ K = 1
```

### PAG197（名前空間 PAG.Part197）::prod_root_iff_local
```lean
theorem prod_root_iff_local {ι : Type*} [Fintype ι] (N : ι → ℕ) [hN : ∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i)) (hχ : ∀ i, (χ i).IsPrimitive) (a : ι → ℤ) :
    (∃ K : ℕ, 0 < K ∧ (∏ i, zN (χ i) ^ a i) ^ K = 1) ↔ LocalCrit N χ a
```


# D. ノート（全文）
# アーデル射影幾何 — Part 257（PAG 2.0）：互いに素な法の並び N_1, …, N_k の指標の積の上で、ガウス和と W はすべての成分の因子の積に分かれる — τ = 交差項·∏τ(χ_i)、W = (−1)^{k(k−1)/2}·交差項·∏W(χ_i)。法 N_1·…·N_k の指標はこの形の積にちょうど 1 通りに書ける。既知の事実の Lean 化

2026-11-14。PAG261.lean（定理 26 個、定義 4 個、instance 1 個）、step280.py（11 項目）。

- **問いの出所。** 著者の選択（2026-11-14 20:59、着手前の文書 `pag2_part257_preregistration.md` の候補 P1、§12）。開始条件 2（方向βの登録ファイルとの突き合わせ）は、**著者の判断で保留のまま**始めました。登録ファイルは届いておらず、突き合わせは済んでいません。
- **問いへの答えの範囲。** 幾何の言葉の問い（読み）は「大域の貼り合わせ（U の固有値 W）は、∞ を含む各点の局所の因子の積に分かれるか」。Lean が答えるのは、互いに素な法の並びの指標の積（Lean では `listChar`）の上でのガウス和 τ と W の式と、法 n の指標の素数冪の成分への分解までです。イデール類指標と Tate の局所定数そのものは Lean にしていません。
- **結論（Lean の文。すべて既知の事実の Lean 化）。**
  1. **ガウス和。** 法が互いに素なら τ(listChar χ l) = 交差項·∏_i τ(χ_i)（`gaussSum_listChar`。原始性は要らない）。交差項は漸化式で定め（`cross`）、閉じた形が 2 つあります。形 (I) は ∏_i χ_i(∏_{j≠i} N_j)（`cross_eq_formI`）、形 (II) は ∏_i ∏_{j≠i} χ_j(N_i)（`cross_eq_formII`）です。形 (II) は、成分 i の因子を「ほかの成分を N_i で読んだ値」で書く形です。
  2. **W。** W(listChar χ l) = ε_∞·∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)/√N_i（`rootNum_listChar_formI`）、= ε_∞·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)（`rootNum_listChar_formII`）。ε_∞ は偶奇の因子 `parFac`（偶で 1、奇で −i）です。
  3. **∞ の因子の符号。** ε_∞(listChar χ l) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数。`parFac_listChar`）。したがって W(listChar χ l) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（`rootNum_listChar`）。成分 2 つでは Part 256 の `rootNum_prodChar` と同じ式です（Lean ではつないでいない）。
  4. **原始性と U の固有値。** すべての成分が原始 ⇔ 積が原始（`isPrimitive_listChar_iff`）。原始なら、phaseA1（読みでは公準 A1 の位相）も同じ式で分かれます（`phaseA1_listChar`）。
  5. **分解の存在と一意性。** 法 N_1·…·N_k の指標はどれも listChar χ l の形に書け（`exists_listChar`。並びに重複なし）、成分は一意です（`listChar_injective`）。Part 256 で「Part 190 の `decomp` と Part 232 の `charMul_injective` を合わせると出る（監査者の読み。Lean ではつないでいない）」と書いた事柄を、ここで Lean にしました（任意個の成分で）。
  6. **すべての素数への分解。** 法 n の指標 Ψ には、素数冪の法 p^{v_p(n)} の成分 χ_p があって、自然数 x での値は Ψ(x) = ∏_p χ_p(x)、τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)}) です（`gaussSum_primeFactors`。形 (II)）。退化例（成分 1 つ）は τ(listChar χ [a]) = τ(χ_a)（`gaussSum_listChar_singleton`）。
  - sorry 0、警告 0。`#print axioms` 26 行（定理と同数）は標準の公理の範囲です（23 行が [propext, Classical.choice, Quot.sound]、1 行が [propext, Quot.sound]、1 行が [propext]、1 行は公理なし）。
- **読み（解釈の言葉。Lean の文ではない）。**
  - 「素点」「局所因子」「貼り合わせ」は著者の言葉です。Lean の文は、指標とガウス和についての恒等式です。偶奇の因子 ε_∞ が無限素点の局所因子にあたる、も読みです。
  - 形 (II) の成分 i の因子 (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i) は、加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}（Tate の学位論文の規約）にとったときの、イデール類指標の p での局所定数と一致し、∞ の局所定数は i^{−a} です（着手前の盲検の問いテストと私の手計算。Lean では示していない）。規約を逆にすると各 p の因子が χ_p(−1) 倍、∞ の因子が i^{a} になり、積は変わりません。
  - Part 256 では「成分の W の積からのずれ」を交差項と符号 s として書きました。成分を任意個にすると、ずれは交差項（形 (I)・(II) のどちらでも書ける）と符号 (−1)^{k(k−1)/2} です。形 (II) で各成分の因子にまとめると、ずれは各点の因子の中に入り、W は各点の因子の積になります（ここまでは Lean の文。それを「局所定数の積」と読むのは上の規約の話で、Lean の外）。
- **公準 A1 との関係。** A1 は公準のままです。ここでの文は τ・W・phaseA1 についての恒等式で、A1 から何かを出すものではありません（CLAUDE.md §7 の第 2 の型）。
- **位置づけ。** 既知の事実の Lean 化です（再導出、確信度：高）。形 (I) は Montgomery–Vaughan の Theorem 9.6 を繰り返したもの、形 (II) と ∞ の因子は Tate の局所定数の積公式の GL(1)/ℚ の場合（規約を除いて）です。新規候補はありません。

## 0. 内容

### 0.0 ハンドシェイク（CLAUDE.md §0）

- (a) 形式化済み：Part 252〜254（PAG256〜258）の `rootNum`・`parFac`・`phaseA1`・`UA1`、Part 256（PAG260）の `prodChar`・`rootNum_prodChar`。前の鎖の Part 189（PAG193）・190（PAG194）・192（PAG196）・193（PAG197）・232（PAG236）の中国剰余定理まわりの定理。
- (b) 著者の解釈の層：§1 の 3 命題。重なりはねじれた貼り合わせ（U）。A1 は公準。解像度は測る素点の集合（L1）。
- (c) 未完の大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象（このパートは ∞ の因子の符号まで）、有限レベルの Bost–Connes。

### 0.1 4 点（着手前の文書 §2 から）

1. 幾何の言葉：大域の貼り合わせ（U の固有値 W）は、∞ を含む各点の局所の因子の積に分かれるか。各点の因子は、どこまでその点だけで決まるか。
2. 既存分野の言葉への最善の翻訳：ガウス和の乗法性の繰り返し（形 (I)）と、Tate の局所定数の積公式の GL(1)/ℚ の場合（形 (II)）。
3. 残余：空（確信度：高）。鎖に対して新しいのは、任意個の成分の明示の積、形 (II)、∞ の因子の符号の整理だけ（§7）。
4. 対照群：F_q[t] でも有限素点の分解は同じ形です（着手前の数値 (8)）。∞ の因子は、偶で 1、奇で √q/τ(η)（盲検の答え。私は計算していない）。一般化素数では指標とガウス和がなく、問いが立ちません。

### 0.2 定義（PAG261.lean）

| 記号 | Lean | 内容 |
|---|---|---|
| N_1·…·N_k | `lvl N l` | 法の並びの積（先頭 × 残り）。`lvl_eq_prod` で (l.map N).prod |
| χ_1·…·χ_k | `listChar χ l` | 先頭の指標と残りの積を Part 256 の `prodChar` でつないだ、法 lvl l の指標 |
| 交差項 | `cross χ l` | 漸化式 cross (a::l) = χ_a(lvl l)·listChar l (N_a)·cross l |
| k | `oddCount χ l` | 奇の成分の数 |

### 0.3 ラベル（CLAUDE.md §7）

| 結果 | ラベル | 根拠 |
|---|---|---|
| ガウス和の分解（形 (I)） | 既知 | Montgomery–Vaughan, Theorem 9.6 の繰り返し |
| 形 (II)、W の形、∞ の因子の符号 | 既知（再導出） | Tate の局所定数の積公式の GL(1)/ℚ の場合（盲検：Rohrlich の講義ノート (2.49)・(2.55)） |
| 原始性、分解の存在と一意性 | 既知 | 中国剰余定理と導手の標準の事実 |
| 「局所因子」「素点」「貼り合わせ」の読み | 著者の解釈の層と読み | — |

- 新規候補：なし。

## 1. 検証表

| 主張 | Lean | 数値（step280） | 新規性 |
|---|---|---|---|
| 積の指標の値（自然数で、−1 で） | `listChar_natCast`・`listChar_neg_one`・`listChar_neg_one_pow` | (6) | 既知 |
| ガウス和の分解（漸化式） | `gaussSum_listChar` | (1)（689 組） | 既知 |
| 交差項の形 (I)・(II) | `cross_eq_formI`・`cross_eq_formII` | (2)・(3) | 既知 |
| W の形 (I)・(II) | `rootNum_listChar_formI`・`rootNum_listChar_formII` | (4) | 既知（再導出） |
| ∞ の因子の符号、W の符号つきの形 | `parFac_listChar`・`rootNum_listChar` | (5) | 既知（再導出） |
| 原始性 ⇔、phaseA1 の形 | `isPrimitive_listChar_iff`・`phaseA1_listChar` | (7) | 既知 |
| 分解の存在と一意性 | `exists_listChar`・`listChar_injective` | (8) | 既知 |
| すべての素数への分解 | `gaussSum_primeFactors`（`pairwise_primeFactors`・`lvl_primeFactors`） | 着手前の (1)(2) | 既知 |
| 退化例（成分 1 つ） | `gaussSum_listChar_singleton` | (9) | 既知 |
| 原始でない成分でも成り立つ | 文に原始性の仮定がない | (11)（522 組） | 既知 |
| 並べ替えで値が変わらない | Lean にしていない | (10) | 既知 |
| 原始でない指標の phaseA1 を導手を割る素点だけで書く形 | Lean にしていない | 着手前の (5)（381 個） | 既知 |
| 対照群 F_q[t] | Lean にしていない | 着手前の (8) | 既知 |

- **文の重み。** 中身があるのは `gaussSum_listChar`（帰納法で Part 189 の `gaussSum_mul_coprime` を繰り返す）、`cross_eq_formI`・`cross_eq_formII`（並べ替えの組み合わせ）、`parFac_listChar`（符号の数え上げ）、`exists_listChar`（Part 190 の `decomp` の繰り返し）、`gaussSum_primeFactors`（法の型の受け渡し）です。ほかは補助（`lvl_cons`・`lvl_eq_prod`・`coprime_lvl`・`sqrt_lvl`・`prod_map_div'`・`not_odd_of_even`・`tri_succ`・`listChar_congr`）か、上からの短い帰結です。

## 2. 数値照合（step280.py、11 項目すべて合格、1 回目で通った）

- 19 の法の並び（素数冪でない法、法 1 の成分、成分 1 つ、4 つを含む）で 689 組の指標。誤差は最大 9.1×10⁻¹⁴。
- (8) 分解の個数：法 12・40・105・180・90・112 で、組の数 = 指標の数、重複なし。
- (10) 並びを逆にしても listChar の値は同じ（Lean にしていない）。
- (11) 原始でない成分を含む組 522 個でも (1)〜(6) が成り立つ。Lean の文にも原始性の仮定はありません。
- 数値の確認は証明ではありません。

## 3. Lean（PAG261.lean）

- import は PAG260（鎖の続き）。名前空間は `PAG.Part261`。
- 置き方：成分の並びをリスト l で持ち、法 `lvl N l` を「先頭 × 残り」で再帰的に定めました。こうすると、法の積が定義のまま Part 189 の `gaussSum_mul_coprime`（法 N₁ * N₂ の形）に合い、型の受け渡しが要りません。法 n の指標についての文（`gaussSum_primeFactors`）だけ、lvl = n を `subst` で受け渡しています。
- 作業の記録：下書き `scratch/t257/T1.lean` で段階的にコンパイルしました。直したもの：
  - `show … = _ from rfl` での書き換えが効かない（定理の型を `have h : … := …` で言い換えてから `rw`）。
  - `if_pos`・`if_neg`・`if_true`・`if_false` は非推奨（`↓reduceIte` に変えた）。
  - `Nat.factorization_prod_pow_eq_self` はこの Mathlib では別の文（`Nat.prod_factorization_pow_eq_self` を使う）。
  - `▸` の向きの推論が止まる（`fun h : i = a => …` と型を書いた）。
  - 使っていない section 変数の警告（`omit hN in` を付けた）。
- 内部照合の 1 回目で、下書きの 2 つの宣言が前の鎖と同じ文だと分かり、消しました（§7）。
- sorry 0、警告 0、`#print axioms` 26 行（定理と同数）。鎖全体（PAG.lean〜PAG261.lean）は theorem/lemma 3,551（Part 256 の後の 3,525 に 26 を足した数）。

## 4. 残る問い（本来の道）

- イデール類指標の局所成分と Tate の局所定数そのものを Lean で書けば、形 (II) の因子が局所定数である、という読みが文になります（Mathlib に局所定数の一般論はない。盲検 Q5）。
- 原始でない指標の phaseA1 を、導手を割る素点と ∞ の因子だけで書く形（着手前の数値 (5)）。
- 残る大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象、有限レベルの Bost–Connes。
- 次のパートは著者の選択を待ちます（Part 258 は始めていません）。開始条件 2 は開いたままです。

## 5. 文献の確認の記録

- 着手前の盲検の問いテスト（2026-11-14 13:02〜13:17、WebSearch・WebFetch 28 回、`prereg257/agent_blind_question_test_output.md`）の結果をそのまま使いました：形 (I) は標準的な演習、形 (II) は Rohrlich の局所公式 (2.55) から符号のずれなしに出る（ψ_∞ = e^{−2πix}、∞ の局所ルート数は i^{−a}、(2.49)）、符号は標準的な演習。Mathlib・Isabelle AFP・Coq に、中国剰余定理によるガウス和の分解は見つからなかった。
- このパートで新しく文献を開いてはいません。Rohrlich の講義ノートは私自身は開いていません（盲検の申告のまま）。

## 6. 収束アラームの状況（CLAUDE.md §7、Part 257 の後）

- **兆候 4（既知の事実だけ）：9 パート連続**（Part 249〜257）。着手前の文書 §8 で「どれを採っても 9 になる」と報告し、著者が P1 を選びました。§7 の規定どおり、監査を提案します（次の作業を選ぶときに）。
- 兆候 1 の内側版：下書きの 2 つの宣言が前の鎖と同じ文でした（§7。閉じる前の照合で見つけて消した）。
- 辞書の未記入の件数：0（新しい読みの言葉はない）。文献照合の未実施の連続パート数：0（着手前の盲検）。
- §6 の表現：A1 は公準のまま。「導いた」「アプローチ」の表現は使っていません。

## 7. 内部照合（2026-11-14 からの必須の手順）

- **着手の前。** xlsx の「定理と証明」を言葉で検索し（「素数冪ごと」「局所因子」「局所定数」「すべての素点」など）、Lean の全宣言の文を正規表現で検索しました（ガウス和と ∏、primeFactors、zN と ∏ など）。成分 2 つの式は前の鎖にありました（Part 189 の `gaussSum_mul_coprime`・`z_mul_coprime`、Part 256 の `rootNum_prodChar`）。任意個の成分の明示の積、形 (II)、符号 (−1)^{k(k−1)/2} の文は見つかりませんでした（網羅ではない）。近いもの：Part 192 の `z_hall`（ホール成分 2 つ、ずれは「1 の冪根がある」の形）、Part 193 の `LocalCrit`・`prod_root_iff_local`（平方因子のない素数成分での、1 の冪根になる条件）、Part 127 以降の素数冪の成分の積 ∏ τ(χ_i)/√ の位数の定理（合成した指標の τ ではない）。
- **閉じる前（1 回目）。** 全宣言を書き出し（4313 件、`audit257/internal/Extract3.lean`）、PAG261 の 34 件それぞれに候補を上位 20 まで選び（`shortlist261.py`）、`#dupcheck`・`#defeqcheck` を両向きに 1230 回（`Dup261_round1.out`）。一致は 2 組：
  - 下書きの `gaussSum_level_one`（法 1 の指標のガウス和は 1）は、Part 199（PAG203）の同名の定理と同じ文（両向き）。
  - 下書きの instance `ppow_neZero`（p^{v_p(n)} ≠ 0）は、Part 236（PAG240）の `neZero_ordProj` と同じ文（両向き）。Part 236 には別の `ppow`（値は ℕ+）もある。
  - 2 つとも消して、前の鎖のものを使いました。
- **閉じる前（2 回目）。** 直した後に同じ手順（4310 件、PAG261 の 31 件、1132 回）。一致は 0。
- 限界：候補選びは型に現れる定数の近さで上位 20 までで、名前や形の違う同じ概念は拾いにくい。「見つからなかった」は「ない」の証明ではありません（確信度：中）。

## 8. 独立照合

（照合の後に書く）


# E. 着手前の文書から（§2 P1、§6 盲検、§12 著者の判断）
## 2. P1：∞ を含むすべての素点の局所因子への W の分解

### 2.1 出所
本来の道の「無限素点を含む大域対象」と「重なり」。Part 256 が残した (iv)「素数冪ごとの分解」にあたります。

### 2.2 幾何の言葉での問い
大域の貼り合わせ（U の固有値 W）は、∞ を含む各点の局所の因子の積に分かれるか。各点の因子は、どこまでその点だけで決まるか。

### 2.3 既存分野の言葉への最善の翻訳
- 原始指標 χ（法 N = ∏ p^{e_p}）を中国剰余定理で χ = ∏ χ_p と分けると、
  - 形 (I)：W(χ) = ε_∞(χ)·∏_p χ_p(N/p^{e_p})·τ(χ_p)/√(p^{e_p})
  - 形 (II)：W(χ) = ε_∞(χ)·∏_p τ(χ_p)/√(p^{e_p})·∏_{q≠p} χ_q(p^{e_p})
  - ε_∞(χ) = i^{−a(χ)}（偶で 1、奇で −i）
- 形 (I) はガウス和の乗法性（Montgomery–Vaughan の Theorem 9.6）を繰り返したもの。形 (II) の因子は、イデール類指標の局所成分の Tate の局所定数に、規約を除いて一致する見込みです（規約は盲検で確かめる、§6）。
- 規約についての私の手計算（確信度：中。盲検の結果を見る前に書いた）：ω を「不分岐な q で ω_q(q) = χ(q)」と正規化すると、ω_p は ℤ_p^× の上で χ_p⁻¹、ω_p(p) = ∏_{q≠p} χ_q(p) です。局所定数を ε(ω_p, ψ_p) = ω_p(p^e)·p^{−e/2}·Σ_u ω_p⁻¹(u)ψ_p(u/p^e) で計算すると：
  - 加法指標 ψ_∞(x) = e^{2πix}、ψ_p(x) = e^{−2πi{x}_p} では、ε_p = χ_p(−1)·ε_p^{(II)}、ε_∞ = i^{a}。
  - 逆向き ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{2πi{x}_p} では、ε_p = ε_p^{(II)}、ε_∞ = i^{−a} で、ちょうど一致します。
  - どちらの規約でも積は W(χ) です（ψ を逆にすると各因子が ω_v(−1) 倍になり、その積は ω(−1) = 1）。
  - 盲検も同じ結論で、後者が Tate の学位論文の規約であることを Rohrlich の講義ノートで確かめました（§6）。
- 符号：ε_∞(χ) = (−1)^{k(k−1)/2}·∏_p ε_∞(χ_p)（k は奇の成分の数）。Part 256 の s の一般化です。

### 2.4 鎖の中にあるもの
- Part 189 `z_mul_coprime`・`gaussSum_mul_coprime`（2 つの法、交差項は明示）。
- Part 192 `z_hall`（ホール成分への分解、ずれは 1 の冪根の存在だけ）、`pcomp`（素数成分）。
- Part 190 `decomp`・`isPrimitive_iff`・`factorsThrough_mul_iff`（指標の分解、原始性、導手）。
- Part 256 `rootNum_prodChar`（W の正規化と符号 s。中身は Part 189 に符号を足したもの）。

### 2.5 残余
空です（確信度：高）。鎖に対して新しいのは、明示の全素点の積、形 (II)、∞ の因子と符号の整理だけです。

### 2.6 対照群テスト
- F_q[t]：有限素点の分解は同じ形で成り立ちます（数値 (8)：法 t(t+1)(t²+1) の指標 32 個、誤差 6.2×10⁻¹⁴、交差項 ≠ 1 が 28 個）。∞ の因子は、偶で 1、奇で √q/τ(η)（η は F_q^× への制限）です（盲検 Q4 (b)、確信度：中。私は計算していない）。ℚ の i^{−a} にあたりますが、η の位数が 3 以上だと 1 の冪根になりません。ℚ で ∞ の因子が 1 の冪根なのは、ℝ^× の符号の群が位数 2 だからです。
- 一般化素数：指標とガウス和がないので、問いが立ちません。

### 2.7 採った場合の Part 257 の中身（予定）
- Lean（PAG261）：素因数の個数の帰納法で形 (I)・(II) と符号。Part 189・190・192 の定理を使い、示し直さない。原始でない指標（導手を割る素点だけの積）と退化例（素点 1 つ）。
- 難しさ：中（素因数分解の上の積と中国剰余定理の扱い）。


## 6. 盲検の問いテスト（2026-11-14 13:02〜13:17）

- 新しいエージェント（文脈なし）に、プロジェクトの言葉を除いた定義と文 Q1〜Q5 を渡しました。使ったのは WebSearch・WebFetch だけです（28 回）。依頼文と、結果の前に書いた予想（12:58）は `prereg257/prompt_blind_question_test.md`、出力はそのまま `prereg257/agent_blind_question_test_output.md`。
- **判定：数学として新しい文はない（確信度：中〜高）。**
  - Q1 (a) 形 (I)：標準的な演習（PSU の講義ノート Thm 4.2 で積公式を確認）。
  - Q1 (b) 形 (II)：既知。L(s, ω) = L(s, χ) となる ω で、Rohrlich の局所公式 (2.55) から ε_p^{(II)} が符号のずれなしに出る。加法指標は ψ_∞ = e^{−2πix}、ψ_p = e^{2πi{x}_p}（Rohrlich (2.69)(2.70)、Tate の学位論文と同じ）、∞ の局所ルート数は i^{−a}（(2.49)）。逆向きの ψ では各 p の因子が χ_p(−1) 倍、∞ が i^{a}。ω を χ̄ に対応させる規約では積が W の共役になる。形 (I) の因子は局所定数ではない。
  - Q1 (c) 符号：標準的な演習。(d) 原始でない指標：既知（交差項は導手の指数と原始成分で評価する）。
  - Q2 (a)：既知（Odoni 1973、Ostergaard–Pigno–Pinner Thm 2.1、Cochrane–Zheng 1999、Mauclaire 1983、Rohrlich の演習 1.3(b)）。(b)：既知（Chowla。arXiv:2011.14523 の引用で確認、原典は未確認）。
  - Q2 (c)：p を固定して e → ∞ とする形の文献は見つからなかった。一様分布は成り立つと判断（Weyl 和が法 p^e の超 Kloosterman 和になる、手計算、中）。素数の法 q → ∞ の場合は Katz 1988。
  - Q3（P4）：既知の結果の短い帰結。交差項を法 N_i で評価すると誤り。
  - Q4 (a)：標準的な演習。(b)：既知。F_q(t) の ∞ の因子は、偶で 1、奇で √q/τ(η)（η = χ|F_q^×。David–Florea–Lalín Cor. 2.4、3 次の指標の場合からの拡張は手計算、中）。ℚ の i^{−a} にあたるが、η の位数が 3 以上だと 1 の冪根でない。
  - Q5：ない。Mathlib には `DirichletCharacter.rootNumber` と関数等式 `IsPrimitive.completedLFunction_one_sub` がある（Part 252 のノートに記録済み）。中国剰余定理によるガウス和の分解と素数冪の法の明示公式は、Mathlib・Isabelle AFP・Coq に見つからなかった。
- **盲検の式を数値で確かめました**（`prereg257/check_blind_q2c.py`。数値の確認は証明ではない）。
  - 法 3^e の偏角の最大の隙間 = 22π/3^e：e = 4〜9 で 6 桁まで一致。e = 8・9 は盲検の挙げていない値（0.010534、0.003511）。e = 2・3 では成り立たない（盲検の条件 e ≥ 4 のとおり）。
  - 原始指標についての W の平均 = p^{1−e/2}(cos θ + sin θ)/(p − 1)、θ = 2π/p^e：p = 3（e = 2〜9）、5（e = 2〜6）、7（e = 2〜5）のすべてで 6 桁まで一致（平均は実数）。
- **予想との照合。**
  - 当たり：P1 は Tate の局所定数の積公式の GL(1)/ℚ の場合で既知。P2 (a)(b) は既知、(c) の形の文献は見つからない。P4 は自明な系。F_q(t) の ∞ の因子は F_q^× への制限のガウス和の形。全体として標準を超えない。Mathlib に局所因子への分解はない。
  - 規約：形 (II) が逆向きの加法指標（ψ_∞ = e^{−2πix}）でちょうど一致することは、§2.3 の私の手計算と同じで、それが Tate の学位論文の規約であることも盲検が確認した（私は Rohrlich を開いていない）。
  - 外れ・予想になかったもの：Q2 (c) の閉じた式（22π/3^e と平均の式）。F_q(t) では ∞ の因子が 1 の冪根でないことがある。挙げた文献（Iwaniec–Kowalski、Tate の Corvallis の論文、Rosen、Weil）は確認されず、代わりに Rohrlich の講義ノートと David–Florea–Lalín が挙がった。
- **盲検に見えないもの。** 盲検は外の文献だけを調べるので、§7 の内部の重複（Part 183・189・190・192・194）は見つけられません。今回の重複は、盲検ではなく自分の鎖の検索で見つかりました。


## 12. 著者の判断（2026-11-14 20:59）

- 次の作業：**P1 で Part 257 を始める。**
- 開始条件 2（方向βの登録ファイルとの突き合わせ）：**著者の判断で、条件 2 を保留のまま Part 257 を始める。** 登録ファイルはまだ届いておらず、突き合わせは済んでいない。届いたら Part 255 の結果と 1 項目ずつ突き合わせる（この判断は、13:2x の「ファイルが届くまで待つ」を置き換える）。
- 内部照合（2026-11-14 からの必須の手順）は、着手の前とパートを閉じる前の 2 回行う。


# F. 数値照合 step280.log
```
OK  (1) 漸化式 τ(listChar (a::l)) = χ_a(lvl l)·listChar l (N_a)·τ(χ_a)·τ(listChar l): 689 組、誤差 5.3e-14
OK  (2) 形 (I)：τ = ∏ χ_i(∏_{j≠i} N_j)·τ(χ_i)。漸化式の交差項 = 形 (I) の交差項: 誤差 5.3e-14
OK  (3) 形 (II)：τ = ∏ τ(χ_i)·∏_{j≠i} χ_j(N_i): 誤差 9.1e-14
OK  (4) W = ε_∞(listChar)·∏ (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i): 誤差 5.1e-15
OK  (5) ε_∞(listChar) = (−1)^{k(k−1)/2}·∏ ε_∞(χ_i)、W(listChar) = (−1)^{k(k−1)/2}·交差項·∏ W(χ_i): 誤差 0.0e+00・5.1e-15
OK  (6) listChar(−1) = ∏ χ_i(−1)、listChar(n) = ∏ χ_i(n)（自然数 n、単数でない n も含む）: 誤差 3.9e-31・9.9e-32
OK  (7) すべて原始 ⇒ listChar も原始。逆向きも数値では成り立つ（Lean は一方向だけの予定）: 順 True、逆 True
OK  (9) 退化例 l = [a]：τ(listChar [a]) = τ(χ_a)、交差項 = 1: 誤差 0.0e+00
OK  (11) 原始でない χ_i を含む組でも (1)〜(6) が成り立つ（原始性は要らない）: 原始でない成分を含む組 522 個
OK  (8) 法 lvl の指標はすべて listChar の形に、ちょうど 1 通りに書ける（組の数 = 指標の数、重複なし）: [3, 4]:4/4、[5, 8]:16/16、[3, 5, 7]:48/48、[4, 9, 5]:48/48、[9, 10]:24/24、[7, 16]:48/48
OK  (10) 並びを逆にしても listChar の値は同じ（法も同じ数）: [3,4,5]・[8,9,7] の各 60 組
合格 11 / 11

```
