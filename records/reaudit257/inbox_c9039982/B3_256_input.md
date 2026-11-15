あなたは独立の照合者です。ある Lean 4（Mathlib）の形式化について、前の照合者（B2）が文面のずれを指摘し、構築者が文面を直しました。直しが正しく入ったかを、形式文と突き合わせて判定してください。

## 守ってほしいこと
- この入力ファイルを Read で読んだあとは、ツールを一切使わないでください（ほかのファイル、シェル、検索、Web、エージェントの起動もしない）。長くて 1 回で読み切れないときは、同じファイルの続き（offset を指定）を読むことだけ許します。
- 定義名・定理名は意味の根拠にしないでください。定義の本文と文の形で判断してください。
- 著者の解釈の言葉（貼り合わせ、素点、重なり、解像度、公準 A1 など）は、「読み」「解釈」と明示されていれば許容です。
- 判断ごとに確信度（高・中・低）を付けてください。回答は日本語で、3,000 字程度までにまとめてください。最後に Read の回数を書いてください。

## 入力 (1)：定義の全文（このファイルと前のファイル。原文のまま。コメントと docstring だけ除いた）
```lean
-- PAG256.lean（文脈：namespace PAG.Part256 / open ZMod Complex Finset / variable {N : ℕ} [NeZero N]）

noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2

open Classical in
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))

-- PAG257.lean（文脈：namespace PAG.Part257 / open ZMod Complex Finset PAG.Part256 / variable {N : ℕ} [NeZero N]）

def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u

noncomputable def ip (f g : (ZMod N)ˣ → ℂ) : ℂ := ∑ u, (starRingEnd ℂ) (f u) * g u

-- PAG258.lean（文脈：namespace PAG.Part258 / open ZMod Complex Finset PAG.Part256 PAG.Part257 DirichletCharacter / variable {N : ℕ} [NeZero N]）

instance conductor_neZero (χ : DirichletCharacter ℂ N) : NeZero χ.conductor :=
  ⟨conductor_ne_zero (χ := χ)⟩

noncomputable def phaseA1 (χ : DirichletCharacter ℂ N) : ℂ := rootNum χ.primitiveCharacter

noncomputable def UA1 : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := ∑ χ : DirichletCharacter ℂ N,
    (phaseA1 χ * ip (charU χ) f / (Nat.totient N : ℂ)) • charU χ
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_add_right, mul_add, add_div, add_smul]
  map_smul' c f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_smul_right, smul_smul]
    congr 1
    ring

-- PAG260.lean（文脈：open DirichletCharacter ZMod Complex / namespace PAG.Part260 / variable {M N : ℕ} [NeZero M] [NeZero N]）

instance : NeZero (M * N) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne N)⟩

noncomputable def prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ (M * N) :=
  changeLevel (dvd_mul_right M N) χ₁ * changeLevel (dvd_mul_left N M) χ₂

def crtMap (M N : ℕ) [NeZero M] [NeZero N] (x : ZMod M × ZMod N) : ZMod (M * N) :=
  ((x.1.val * N + x.2.val * M : ℕ) : ZMod (M * N))

open Classical in
noncomputable def crossSign (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
  if χ₁.Odd ∧ χ₂.Odd then -1 else 1
```

## 入力 (2)：形式文の全文（PAG260.lean の定理 23 個すべて。原文のまま、証明だけ除いた。すべてコンパイル済みで sorry なし、公理は標準の範囲）
```lean
theorem cast_crtMap_fst (x : ZMod M × ZMod N) :
    ((crtMap M N x : ZMod (M * N)).cast : ZMod M) = x.1 * (N : ZMod M)
theorem cast_crtMap_snd (x : ZMod M × ZMod N) :
    ((crtMap M N x : ZMod (M * N)).cast : ZMod N) = x.2 * (M : ZMod N)
theorem crtMap_bijective (h : M.Coprime N) : Function.Bijective (crtMap M N)
theorem stdAddChar_crtMap (x : ZMod M × ZMod N) :
    stdAddChar (crtMap M N x) = stdAddChar x.1 * stdAddChar x.2
theorem prodChar_apply (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (a : ZMod (M * N)) :
    prodChar χ₁ χ₂ a = χ₁ (a.cast : ZMod M) * χ₂ (a.cast : ZMod N)
theorem gaussSum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    gaussSum (prodChar χ₁ χ₂) stdAddChar =
      χ₁ (N : ZMod M) * χ₂ (M : ZMod N) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar
theorem prodChar_neg_one (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    prodChar χ₁ χ₂ (-1) = χ₁ (-1) * χ₂ (-1)
omit [NeZero M] [NeZero N] in
theorem crossSign_of_odd {χ₁ : DirichletCharacter ℂ M} {χ₂ : DirichletCharacter ℂ N}
    (h1 : χ₁.Odd) (h2 : χ₂.Odd) : crossSign χ₁ χ₂ = -1
omit [NeZero M] [NeZero N] in
theorem crossSign_of_even_left {χ₁ : DirichletCharacter ℂ M} (χ₂ : DirichletCharacter ℂ N)
    (h1 : χ₁.Even) : crossSign χ₁ χ₂ = 1
omit [NeZero M] [NeZero N] in
theorem crossSign_of_even_right (χ₁ : DirichletCharacter ℂ M) {χ₂ : DirichletCharacter ℂ N}
    (h2 : χ₂.Even) : crossSign χ₁ χ₂ = 1
theorem parFac_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.parFac (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * PAG.Part256.parFac χ₁ * PAG.Part256.parFac χ₂
theorem rootNum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.rootNum (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂)
theorem isPrimitive_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (prodChar χ₁ χ₂).IsPrimitive
theorem phaseA1_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    PAG.Part258.phaseA1 (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂)
theorem UA1_charU_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    PAG.Part258.UA1 (PAG.Part257.charU (prodChar χ₁ χ₂)) =
      (crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂)) •
        PAG.Part257.charU (prodChar χ₁ χ₂)
theorem cross_eq_sign_of_rootNum_one (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) (w1 : PAG.Part256.rootNum χ₁ = 1)
    (w2 : PAG.Part256.rootNum χ₂ = 1) (w12 : PAG.Part256.rootNum (prodChar χ₁ χ₂) = 1) :
    crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) = 1
theorem exists_primitive_odd_five : ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Odd
-- ★ 
theorem rootNum_prodChar_ne_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      χ₁.Odd ∧ χ₂.Odd ∧
      PAG.Part256.rootNum (prodChar χ₁ χ₂) ≠ PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂
-- ★ 
theorem rootNum_prodChar_eq_neg_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 13), χ₁.IsPrimitive ∧
      χ₂.IsPrimitive ∧ χ₁.Odd ∧ χ₂.Odd ∧ χ₁ ((13 : ℕ) : ZMod 3) * χ₂ ((3 : ℕ) : ZMod 13) = 1 ∧
      PAG.Part256.rootNum (prodChar χ₁ χ₂) =
        -(PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂) ∧
      PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂ ≠ 0
theorem phaseA1_prodChar_ne_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      PAG.Part258.phaseA1 (prodChar χ₁ χ₂) ≠ PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂
theorem norm_char_unit {n : ℕ} (χ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) : ‖χ a‖ = 1
omit [NeZero M] [NeZero N] in
theorem norm_cross (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    ‖χ₁ (N : ZMod M) * χ₂ (M : ZMod N)‖ = 1
theorem charU_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (u : (ZMod (M * N))ˣ) :
    PAG.Part257.charU (prodChar χ₁ χ₂) u =
      PAG.Part257.charU χ₁ (ZMod.unitsMap (dvd_mul_right M N) u) *
        PAG.Part257.charU χ₂ (ZMod.unitsMap (dvd_mul_left N M) u)
```


## 入力 (3)：B2 の出力の全文（原文のまま。行番号はノートの直す前の版のもの）

# 照合結果：PAG260.lean（Part 256）

**要旨**：形式文 23 個に、偽・空虚・別物はありません（高）。★の 2 文は、表でもノートでも主な部分が一致しています（高）。ずれは主に Lean ファイルの冒頭説明と docstring にあり、ノートと表で直した箇所がそちらに反映されていません。いちばん重いのは、`UA1_charU_prodChar` の docstring で符号 s が抜けていることです。

## 1. 表（入力 (5)）

- **★見出し**：式と範囲は `rootNum_prodChar`・`phaseA1_prodChar` と一致します。ただし括弧内の「Tate・Deligne の局所定数の GL(1)/ℚ の場合」の Lean 化という部分は、主張が強いです（中）。Lean ファイル自身が、局所の ε 因子は Lean にしていないと書いています。
- **★`rootNum_prodChar_ne_mul`**：一致（高）。
  - 証明の要点を検算しました。s = −1、χ₁(5) = −1 なので、比は χ₂(3) = ∓i です。
  - 比を言うには W(χ₁)W(χ₂) ≠ 0 が要ります。要点に足すとよいです（低）。
  - 「存在の例 1 つ」は「ちょうど 1 組」とも読めます。A2 によると、条件を満たす 2 組のどちらでも成り立ちます（低）。
- **★`rootNum_prodChar_eq_neg_mul`**：一致（高）。連言 6 つがすべて文面にあります。要点も検算しました。χ₂ = χ³ とすると、χ₂ は奇、χ₂(3) = χ(27) = χ(1) = 1、χ₁(13) = χ₁(1) = 1、s = −1 です。
- **★`charU_prodChar`**：一致（高）。「中国剰余定理の成分」を読みとした扱いは適切です。互いに素でなければ、unitsMap の対は中国剰余定理の同型になりません。
- **他の行**：すべて一致（高）。`prodChar_apply` の「単数でない a では両辺 0」は文にはありませんが、定義と文から従う正しい注記です。

## 2. ノート（入力 (4)）

変わった行の範囲はすべて見ました。

- **食い違いなし**：1・3・6・10・15〜17・20・74・80〜84・89・101〜103・115〜121・127・132〜139・142〜143 行は、形式文と食い違いません（高）。
  - 検証表に出てくる Lean の名前はすべて 23 文にあります。「Lean にしていない」とした行は、23 文にありません。
- **11 行**：「中国剰余定理の 2 つの成分の関数の積（`charU_prodChar`）」を事実として書いています。表の★行は読みとしているので、扱いがそろっていません（中）。
- **13 行**：`phaseA1_prodChar_ne_mul` を「W ≠ …となる奇の組」の根拠に挙げています。しかしこの文は phaseA1 についての文で、「奇」も入っていません（高、重さ小）。
- **14 行**：一致します（高）。ただ、この例では交差項が 1 なので、`gaussSum_prodChar` から τ(χ₁χ₂) = τ(χ₁)τ(χ₂) が出ます。その点が書かれていません。
- **21 行**：「2 次の指標では全体がヒルベルト記号の積公式と同値」は、121 行で未確認とした項目なのに、未確認の印がありません。また「同値」は、23 行の「ここから相互法則が出るのではない」と食い違います（中）。
- **24 行**：「ルート数という量についての恒等式」は、10 行の注意（原始でない指標では W はルート数でない）と合いません（低）。
- **25 行**：「Tate・Deligne の局所定数の GL(1)/ℚ の場合です」は、見出しと同じく強い言い方です（中）。
- **6 行**：
  - 「法 M と法 N の固有値」は、Part 258 の `UA1_charU` と合わせて初めて言えることです。許容範囲です（低）。
  - (iv) の「素数冪ごとの分解（数値だけ）」に対応する数値の項目が、検証表にありません（低）。
- **140〜141 行**：「直したもの／直していないもの」に、次の 3 節で挙げる Lean の文面が載っていません（中）。

## 3. Lean ファイルの文面（入力 (3)）

- **(a) `UA1_charU_prodChar`**：「局所の位相の積に交差項を掛けた値で動かす」と書いています（高）。
  - このファイルでは「交差項」は χ₁(N)·χ₂(M) を指します（`norm_cross` と★`rootNum_prodChar_eq_neg_mul` の docstring）。そのため符号 s が抜けています。
  - 両方が奇のとき、形式文の値と −1 倍だけ違います。法 39 の★例が、まさにこの場合です。
- **(b) `crossSign`**：「交差項の符号」と呼んでいます（高）。しかし定義の本文は Odd ∧ Odd だけで決まり、交差項には関係しません。法 39 の例（交差項 = 1、s = −1）とも矛盾します。
- **(c) 冒頭「答え」4 と `parFac_prodChar`**：「無限素点の因子のずれ」を事実として書いています（高）。ノート 9 行と表は「偶奇の因子」に直していますが、Lean 側は直っていません。
- **(d) `phaseA1_prodChar_ne_mul`**：「U の固有値…が局所の位相の積と違う」と書いています（高）。
  - これは、冒頭の「言い方の注意」が避けると決めた「大域は局所の積ではない」の型の言い方です。
  - また、文は phaseA1 についての文です。U の固有値の文にはなっていません。
- **(e) 冒頭「答え」7**：「等号になる組もあり」が「すべて Lean 化」の一覧の中にありますが、Lean にはしていません（高）。冒頭の「Lean にしていないこと」にも、等号の例と、交差項だけでずれる例が載っていません。
- **(f) 冒頭の位置づけ**：冒頭「答え」の「局所定数の場合」と、「Lean にしていないこと：局所の ε 因子」がかみ合いません（中）。
- **(g) `charU_prodChar`**：中国剰余定理の成分を事実として書いています。表と扱いがそろっていません（中）。
- **(h) ★の docstring**：どちらも主張が弱い側で、それ以外は一致します（高、重さ小）。
  - ★`rootNum_prodChar_ne_mul` には「奇」がありません。文に足した連言が反映されていません。
  - ★`rootNum_prodChar_eq_neg_mul` には「W(χ₁)W(χ₂) ≠ 0」がありません。
- **(i) 冒頭「問いの出所」の「公準 A1 の位相＝ルート数 W」**（中）：
  - phaseA1 χ は W（χ の原始指標）です。W(χ) と等しいのは、χ が原始のときだけです。
  - 冒頭「答え」5、「A1 は公準のまま」の段、`rootNum_prodChar` には、ノート 10 行の注意がありません。
- **(j) 小さい点（低）**：
  - `isPrimitive_prodChar` に「互いに素」がありません（仮定がなければ偽）。
  - 「指標の基底の上の文」は、正確には「原始指標の積の形の指標 1 つの上の文」です。
  - 「3 つの位相」と書いていますが、仮定は rootNum = 1 です。
  - 「貼り合わせ U」「公準 A1 の位相」が解釈の言葉だという宣言がありません。

## 4. A2 と文面の食い違い（★の文）

S18・S23 の訳そのものは、文面と一致します（高）。

1. **法 39 の −1**（中）：
   - A2 の見方：この例ではガウス和は乗法的で、−1 は正規化（i·i）だけから来る。「算術的な破れ」と読むのは過大評価。
   - 文面の書き方：「ずれは実際に起きる」の例として置き、21 行で s をヒルベルト記号に結びつけています。
   - 形式文の誤りではありませんが、重みの付け方が違います。
2. **s の扱い**（高）：A2 は s を「正規化 i^κ の帳尻合わせ」とみています。docstring は「交差項の符号」と呼んでいます。
3. **U の固有値**（中）：A2 は、U の固有値が乗法的でないことは文になっていないとしています。(d) は、文で示したように書いています。
4. **法 15**（低）：A2 は「条件を満たす 2 組すべてで成り立ち、奇と原始の連言は強制される」としています。表の「存在の例 1 つ」とノート 102 行は、これと矛盾はしませんが説明が足りません。
5. **交差項だけのずれ**（低）：A2 は、交差項だけが必要な例は示されていないとし、候補（法 3 と法 7 の 3 次の指標）を挙げています。ノート 15 行はこれと合いますが、Lean の冒頭には書かれていません。

## 5. 直すべき点（重要な順）

1. **`UA1_charU_prodChar`**：「M, N が互いに素で χ₁, χ₂ が原始なら、UA1 は charU(prodChar χ₁ χ₂) を s·χ₁(N)·χ₂(M)·phaseA1(χ₁)·phaseA1(χ₂) 倍する（s = crossSign。固有ベクトル 1 つの上の式）。」
2. **`crossSign`**：「偶奇の符号 s：χ₁, χ₂ がともに奇なら −1、それ以外は +1（交差項とは別の因子）。」
3. **冒頭「答え」4 と `parFac_prodChar`**：「偶奇の因子（偶で 1、奇で −i）のずれ ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)。無限素点の局所因子にあたる、は読み。」
4. **`phaseA1_prodChar_ne_mul`**：「法 3・法 5 の原始指標の組で、phaseA1(χ₁χ₂) ≠ phaseA1(χ₁)·phaseA1(χ₂) となるものがある（Part 258 の UA1_charU と合わせると、U の固有値が成分の位相の積と違う例）。」「局所」は除きます。
5. **冒頭「答え」7**：「等号になる組もある（数値 (13)。Lean にしていない）」と書き、phaseA1 版の文は「奇」を含まないと注記します。「Lean にしていないこと」に、等号の例と交差項だけの例を足します。
6. **見出し・冒頭・ノート 25 行**：「Montgomery–Vaughan の Theorem 9.6 とそのルート数版の Lean 化。文献では、大域の ε 因子が局所の積であることと、不分岐なひねりでの局所 ε 因子の変化から出る形にあたる（局所 ε 因子は Lean にしていない）。」
7. **法 39 の例（ノート 14 行・表・docstring）**：「交差項 = 1 なので τ(χ₁χ₂) = τ(χ₁)τ(χ₂)。−1 は rootNum の正規化（奇×奇で i·i = −1）から来る」を足します。
8. **`charU_prodChar` とノート 11 行**：「(χ₁χ₂)(u) = χ₁(u mod M)·χ₂(u mod N)（互いに素は要らない。中国剰余定理の成分の関数の積、は読み）。」
9. **★の docstring をそろえる**：「奇の原始指標 χ₁（法 3）、χ₂（法 5）で…」と「…かつ W(χ₁)W(χ₂) ≠ 0」にします。
10. **W についての注意**：冒頭「答え」5、`rootNum_prodChar`、ノート 24 行に「W は法で正規化したガウス和。ルート数なのは原始指標のときだけ」を足します。「問いの出所」は「固有値は W（χ の原始指標）」と書きます。
11. **ノート 21 行**：「（C の申告。未確認）」を付け、「同値」を「W = 1 を外から入れると同じ形」に直します。
12. **その他**：(j) の各点を直し、140〜141 行に Lean の文面をどう扱ったかを記録します。

## 6. 全体

- **形式文**：偽・空虚・別物はありません（高）。
  - ★`rootNum_prodChar_eq_neg_mul` は、非零の連言で空虚に成り立つことを防いでいます。
  - `cross_eq_sign_of_rootNum_one` の仮定は満たせます。法 3 と法 5 の 2 次の指標で、3 つの W がすべて 1 になります。
- **標準を超える内容**：ありません（高）。中身は、互いに素な法でのガウス和の乗法性、そのルート数版、原始指標の積が原始であること、その具体例です。
- **文献番号**：Theorem 9.6 などの番号は、この入力だけでは照合できません。

使ったツール：Read のみ（2 回）

## 入力 (4)：Lean ファイルの文面の差分（形式文は変えていない。冒頭の説明と docstring だけ）
```diff
--- PAG260.lean（直す前）
+++ PAG260.lean（直した後）
@@ -1,35 +1,47 @@
 /-
-アーデル射影幾何 — Part 256（PAG 2.0）：互いに素な法の原始指標の積の上での、貼り合わせ U の固有値 — 交差項の法則
-
-問いの出所：著者の選択（2026-11-13 18:15、着手前の文書 `pag2_part256_preregistration.md` の候補 M1）。本来の道の
-「無限素点を含む大域対象」と「重なり」。Part 252〜254 の貼り合わせ U（公準 A1 の位相＝ルート数 W を固有値とする）を、
-Part 255 の L1（測る素点の集合）とつなぐ問い：互いに素な法 M, N の局所の貼り合わせから、法 M·N の貼り合わせは決まるか。
-
-答え（すべて既知の事実の Lean 化。Montgomery–Vaughan の Theorem 9.6、Tate・Deligne の局所定数の GL(1)/ℚ の場合）：
+アーデル射影幾何 — Part 256（PAG 2.0）：互いに素な法 M, N の原始指標の積 χ₁χ₂ の上での、UA1 の固有値の式（交差項の法則）
+
+読みの言葉：「貼り合わせ U」は `PAG.Part258.UA1`、「公準 A1 の位相」は `PAG.Part258.phaseA1`（χ の原始指標の W）。
+これらと「素点」「重なり」は著者の解釈の層の言葉で、Lean の文には出てこない。
+
+問いの出所：著者の選択（2026-11-13 18:15、着手前の文書 `pag2_part256_preregistration.md` の候補 M1）。互いに素な法 M, N の
+貼り合わせから、法 M·N の貼り合わせは決まるか（読み）。Lean が答えるのは、原始指標の積 1 つの上の UA1 の固有値まで。
+
+W について：`rootNum χ` = τ(χ)/(i^a·√n)（n は法、a は偶で 0、奇で 1）。χ が原始ならルート数。原始でない χ では
+ルート数ではなく、0 にもなる。UA1 の固有値は phaseA1 χ = W(χ の原始指標)。
+
+Lean の文（既知の事実の Lean 化。Montgomery–Vaughan の Theorem 9.6 とそのルート数版）：
 1. 中国剰余定理の分解 a = a₁·N + a₂·M（`crtMap`・`crtMap_bijective`）と、加法指標の分解（`stdAddChar_crtMap`）。
-2. 指標の積 `prodChar χ₁ χ₂`（法 M·N）とその値（`prodChar_apply`・`charU_prodChar`・`prodChar_neg_one`）。
-3. ガウス和の乗法性 τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)（`gaussSum_prodChar`。原始性は要らない）。
-4. 無限素点の因子のずれ ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)、s = −1（両方が奇）か +1（`crossSign`・`parFac_prodChar`）。
-5. 交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（`rootNum_prodChar`。原始性は要らない）。交差項の絶対値は 1
-   （`norm_cross`）。
-6. 原始指標の積は原始（`isPrimitive_prodChar`）。したがって公準 A1 の位相と貼り合わせ U でも同じ法則
-   （`phaseA1_prodChar`・`UA1_charU_prodChar`）。
-7. 法 15 = 3·5 で W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組がある（`rootNum_prodChar_ne_mul`・
-   `phaseA1_prodChar_ne_mul`）。法 39 = 3·13 で、交差項は 1 だが符号だけで W(χ₁χ₂) = −W(χ₁)·W(χ₂) となる組がある
-   （`rootNum_prodChar_eq_neg_mul`。独立照合 B の指摘で追加）。等号になる組もあり、ずれは「一般には」起きる。
-8. 3 つの位相がすべて 1 なら交差項は符号で打ち消される（`cross_eq_sign_of_rootNum_one`。条件つきの文。2 次の指標では
-   平方剰余の相互法則と同じ形だが、3 つの仮定は外から入れるもので、ここから相互法則が出るのではない）。
-
-言い方の注意（着手前の盲検の問いテストの指摘）：大域の ε 因子は局所の ε 因子の積である（Tate、Deligne）。ここで言う
-ずれは、ディリクレ指標を中国剰余定理で分けた成分 χ₁, χ₂ のルート数の積と、χ₁χ₂ のルート数との差。交差項は、χ₁ の、
-N を割る素点での局所成分（不分岐だが自明でない）から出る。「大域は局所の積ではない」とは書かない。
-A1 は公準のまま。ここでの文は、ルート数という量についての恒等式で、A1 から何かを出すものではない。
-
-範囲（独立照合 B の指摘）：ここでの文は、互いに素な 2 つの法の、原始指標の積 1 つの上の固有値の式。法 M·N の
-すべての指標が積の形に一意に書けること、作用素全体の式、素数冪ごとの分解は Lean にしていない。互いに素の仮定は、
-ガウス和の法則と交差項の法則では外しても成り立つ（両辺 0）が、仮定つきのまま。
-
-Lean にしていないこと：原始でない指標の位相の法則（導手 d₁, d₂ での交差項 χ₁*(d₂)·χ₂*(d₁)。数値 step279 の (4)）、
-作用素の形（テンソル積と平行移動。指標の基底の上の文 `UA1_charU_prodChar` まで）、3 つ以上の法（数値 (7)）、
-互いに素でない法（両辺が 0 になる。数値 (10)）、対照群 F_q[t]（数値 (5)）、イデール類指標の局所成分と局所の ε 因子。
+2. 指標の積 `prodChar χ₁ χ₂`（法 M·N）の値（`prodChar_apply`・`prodChar_neg_one`）と、単数での値（`charU_prodChar`。
+   「中国剰余定理の 2 つの成分の関数の積」は読み）。
+3. ガウス和の乗法性 τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)（`gaussSum_prodChar`。互いに素。原始性は要らない）。
+4. 偶奇の因子（`parFac`：偶で 1、奇で −i）のずれ ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)。s は両方が奇なら −1、それ以外は +1
+   （`crossSign`・`parFac_prodChar`）。偶奇の因子が無限素点の局所因子にあたる、は読み。
+5. W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（`rootNum_prodChar`。互いに素。原始性は要らないが、W がルート数なのは原始の
+   とき）。交差項 χ₁(N)·χ₂(M) の絶対値は 1（`norm_cross`）。
+6. 互いに素な法の原始指標の積は原始（`isPrimitive_prodChar`）。したがって phaseA1 でも同じ式（`phaseA1_prodChar`）。
+   UA1 は charU(χ₁χ₂) を s·χ₁(N)·χ₂(M)·phaseA1(χ₁)·phaseA1(χ₂) 倍する（`UA1_charU_prodChar`。原始指標の積の形の
+   指標 1 つの上の式。作用素全体の式ではない）。
+7. 存在の例：法 15 = 3·5 で W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組（`rootNum_prodChar_ne_mul`）と、
+   phaseA1 で同じ不等号が成り立つ原始指標の組（`phaseA1_prodChar_ne_mul`。この文には「奇」は入っていない）。
+   法 39 = 3·13 で、交差項 = 1、W(χ₁χ₂) = −W(χ₁)·W(χ₂)、W(χ₁)·W(χ₂) ≠ 0 となる奇の原始指標の組
+   （`rootNum_prodChar_eq_neg_mul`）。この例では交差項 = 1 なので τ(χ₁χ₂) = τ(χ₁)·τ(χ₂) で、−1 は W の正規化
+   （奇×奇で i·i = −1）から来る。
+8. 条件つきの文：W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 なら s·χ₁(N)·χ₂(M) = 1（`cross_eq_sign_of_rootNum_one`。互いに素の
+   仮定は余分だが付けたまま）。2 次の指標では平方剰余の相互法則と同じ形になるが、3 つの仮定は外から入れるもので、
+   ここから相互法則が出るのではない。
+
+言い方の注意：文献では、大域の ε 因子は局所の ε 因子の積である（Tate、Deligne）。ここで言うずれは、ディリクレ指標を
+中国剰余定理で分けた成分 χ₁, χ₂ の W の積と、χ₁χ₂ の W との差。「大域は局所の積ではない」とは書かない。
+A1 は公準のまま。ここでの文は W・phaseA1 についての恒等式で、A1 から何かを出すものではない。
+
+範囲：互いに素な 2 つの法の、原始指標の積 1 つの上の式。法 M·N のすべての指標が積の形に一意に書けること、作用素全体の
+式、素数冪ごとの分解と 3 つ以上の法は Lean にしていない。互いに素の仮定は、ガウス和と W の式では外しても成り立つ
+（両辺 0）が、仮定つきのまま。
+
+Lean にしていないこと：等号になる組（法 15、法 5 の偶の 2 次の指標。数値 (13)）、交差項だけでずれる組（s = 1 で交差項
+≠ 1。例：法 3 の奇の指標と法 7 の 3 次の指標。数値は再照合のときの確認だけ）、原始でない指標の式（導手 d₁, d₂ での
+交差項 χ₁*(d₂)·χ₂*(d₁)。数値 (4)）、作用素の形、3 つ以上の法（数値 (7)）、互いに素でない法（両辺が 0。数値 (10)）、
+対照群 F_q[t]（数値 (5)）、イデール類指標の局所成分と局所の ε 因子（文献では、交差項は不分岐なひねりでの局所 ε 因子の
+変化から出る形にあたる）。
 -/
@@ -46,3 +58,3 @@
 
-/-- 互いに素な法 M, N の指標の積（法 M·N の指標）。 -/
+/-- 法 M, N の指標の積（法 M·N の指標）。定義に互いに素は要らない。 -/
 noncomputable def prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
@@ -153,3 +165,3 @@
 open Classical in
-/-- 交差項の符号：両方が奇のとき −1、それ以外は +1。 -/
+/-- 偶奇の符号 s：χ₁, χ₂ がともに奇なら −1、それ以外は +1（交差項 χ₁(N)·χ₂(M) とは別の因子）。 -/
 noncomputable def crossSign (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
@@ -181,3 +193,3 @@
 
-/-- 無限素点の因子のずれ：ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)（ε = parFac は 偶で 1、奇で −i）。 -/
+/-- 偶奇の因子のずれ：ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)（ε = parFac は偶で 1、奇で −i）。ε が無限素点の局所因子にあたる、は読み。 -/
 theorem parFac_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
@@ -205,3 +217,3 @@
 
-/-- **交差項の法則**：W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)。原始性は要らない。 -/
+/-- **交差項の法則**：互いに素な法で W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)。原始性は要らない（W がルート数なのは原始のとき）。 -/
 theorem rootNum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
@@ -224,3 +236,3 @@
 
-/-- 積の導手：χ₁, χ₂ が原始なら χ₁χ₂ も原始（法 M·N）。 -/
+/-- 積の導手：法 M, N が互いに素で χ₁, χ₂ が原始なら、χ₁χ₂ も原始（法 M·N）。 -/
 theorem isPrimitive_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
@@ -248,3 +260,3 @@
 
-/-- 公準 A1 の位相（Part 254 の `phaseA1`）での交差項の法則（原始指標）。 -/
+/-- phaseA1（Part 254 の `phaseA1`。読みでは公準 A1 の位相）での同じ式（互いに素な法の原始指標）。 -/
 theorem phaseA1_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
@@ -258,3 +270,4 @@
 
-/-- 貼り合わせ U（Part 254 の `UA1`）は、原始指標の積を、局所の位相の積に交差項を掛けた値で動かす。 -/
+/-- 互いに素な法の原始指標 χ₁, χ₂ について、UA1（Part 254。読みでは貼り合わせ U）は charU(χ₁χ₂) を
+s·χ₁(N)·χ₂(M)·phaseA1(χ₁)·phaseA1(χ₂) 倍する（s = crossSign。固有ベクトル 1 つの上の式）。 -/
 theorem UA1_charU_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
@@ -267,4 +280,4 @@
 
-/-- 2 次の指標などで 3 つの位相がすべて 1 なら、交差項は符号で打ち消される（平方剰余の相互法則と同じ形。
-3 つの仮定は外から入れるもので、ここからは出ない）。 -/
+/-- 条件つきの文：W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 なら s·χ₁(N)·χ₂(M) = 1（互いに素の仮定は余分）。2 次の指標では平方剰余の
+相互法則と同じ形になるが、3 つの仮定は外から入れるもので、ここからは出ない。 -/
 theorem cross_eq_sign_of_rootNum_one (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
@@ -291,3 +304,3 @@
 
-/-- **中国剰余定理の成分の積とのずれの例**（法 15 = 3·5）：原始指標 χ₁（法 3）、χ₂（法 5）で
+/-- **中国剰余定理の成分の積とのずれの例**（法 15 = 3·5）：奇の原始指標 χ₁（法 3）、χ₂（法 5）で
 W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となるものがある。 -/
@@ -322,3 +335,4 @@
 /-- **符号だけでずれる例**（法 39 = 3·13。独立照合 B の指摘で追加）：奇の原始指標 χ₁（法 3）、χ₂（法 13）で、
-交差項 χ₁(13)·χ₂(3) = 1 だが W(χ₁χ₂) = −W(χ₁)·W(χ₂) となるものがある。 -/
+交差項 χ₁(13)·χ₂(3) = 1、W(χ₁χ₂) = −W(χ₁)·W(χ₂)、W(χ₁)·W(χ₂) ≠ 0 となるものがある。交差項が 1 なので
+τ(χ₁χ₂) = τ(χ₁)·τ(χ₂) で、−1 は W の正規化（奇×奇で i·i = −1）から来る。 -/
 theorem rootNum_prodChar_eq_neg_mul :
@@ -360,3 +374,4 @@
 
-/-- 同じ例を貼り合わせ U の言葉で：法 15 で、U の固有値（公準 A1 の位相）が局所の位相の積と違う原始指標の組がある。 -/
+/-- 法 3・法 5 の原始指標の組で、phaseA1(χ₁χ₂) ≠ phaseA1(χ₁)·phaseA1(χ₂) となるものがある（この文には「奇」は
+入っていない。Part 254 の `UA1_charU` と合わせると、UA1 の固有値が成分の phaseA1 の積と違う例になる）。 -/
 theorem phaseA1_prodChar_ne_mul :
@@ -385,3 +400,4 @@
 
-/-- 積の指標は、中国剰余定理の 2 つの成分の関数の積：(χ₁χ₂)(u) = χ₁(u mod M)·χ₂(u mod N)。 -/
+/-- 積の指標の単数での値：(χ₁χ₂)(u) = χ₁(u mod M)·χ₂(u mod N)（互いに素は要らない。「中国剰余定理の 2 つの成分の
+関数の積」は読み）。 -/
 theorem charU_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
```

## 入力 (5)：ノートの差分
```diff
--- pag2_part256_gluing_cross_term.md（直す前）
+++ pag2_part256_gluing_cross_term.md（直した後）
@@ -4,4 +4,4 @@
 
-- **問いの出所。** 著者の選択（2026-11-13 18:15、着手前の文書 `pag2_part256_preregistration.md` の候補 M1）。本来の道の「無限素点を含む大域対象」と「重なり」に仕えます。Part 252〜254 の貼り合わせ U（公準 A1 の位相を固有値とする）と、Part 255 の L1（測る素点の集合）をつなぐ問いです：互いに素な法 M, N の貼り合わせから、法 M·N の貼り合わせは決まるか。
-- **問いへの答えの範囲（独立照合 B の指摘）。** Lean の文が答えるのは、互いに素な 2 つの法の、原始指標の積 1 つの上の固有値です：法 M と法 N の固有値と、交差項と符号から決まります。「素点ごとに分かれるか」「決まるか」の全体には答えていません。Lean にしていないのは、(i) 法 M·N のすべての指標が積の形に一意に書けること、(ii) 原始でない成分（数値だけ）、(iii) 作用素全体の式、(iv) 素数冪ごとの分解と 3 つ以上の法（数値だけ）です。題の最初の版「貼り合わせ U は素点ごとに分かれるか」は、この範囲に合わせて直しました。
+- **問いの出所。** 著者の選択（2026-11-13 18:15、着手前の文書 `pag2_part256_preregistration.md` の候補 M1）。本来の道の「無限素点を含む大域対象」と「重なり」に仕えます。Part 252〜254 の貼り合わせ U（読み。Lean では `UA1`。固有値は `phaseA1` χ = W(χ の原始指標)）と、Part 255 の L1（測る素点の集合）をつなぐ問いです：互いに素な法 M, N の貼り合わせから、法 M·N の貼り合わせは決まるか。
+- **問いへの答えの範囲（独立照合 B の指摘）。** Lean の文が答えるのは、互いに素な 2 つの法の、原始指標の積 1 つの上の固有値です：法 M と法 N の固有値と、交差項と符号から決まります（Part 254 の `UA1_charU` と合わせて）。「素点ごとに分かれるか」「決まるか」の全体には答えていません。Lean にしていないのは、(i) 法 M·N のすべての指標が積の形に一意に書けること、(ii) 原始でない成分（数値だけ）、(iii) 作用素全体の式、(iv) 素数冪ごとの分解（数値もない）と 3 つ以上の法（数値 (7) だけ）です。題の最初の版「貼り合わせ U は素点ごとに分かれるか」は、この範囲に合わせて直しました。
 - **結論（Lean の文。すべて既知の事実の Lean 化）。**
@@ -10,7 +10,7 @@
   3. **交差項の法則。** W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（`rootNum_prodChar`。原始性は要らない）。交差項 χ₁(N)·χ₂(M) の絶対値は 1 です（`norm_cross`）。ただし W（`rootNum`）がルート数であるのは原始指標のときだけで、原始でない指標では「法で正規化したガウス和」の恒等式です（A の指摘）。
-  4. **貼り合わせ U での形。** 原始指標の積は原始です（`isPrimitive_prodChar`）。したがって公準 A1 の位相 `phaseA1` でも同じ法則が成り立ち（`phaseA1_prodChar`）、U は関数 χ₁χ₂ をその値で動かします（`UA1_charU_prodChar`）。関数 χ₁χ₂ は、中国剰余定理の 2 つの成分の関数の積です（`charU_prodChar`）。これは原始指標の積 1 つの上の固有値の式で、作用素全体の等式ではありません。原始でない指標では、因子は導手での値 χ₁*(d₂)·χ₂*(d₁) に変わります（数値 (4)。Lean にしていない）。
+  4. **貼り合わせ U での形。** 原始指標の積は原始です（`isPrimitive_prodChar`）。したがって `phaseA1`（読みでは公準 A1 の位相）でも同じ法則が成り立ち（`phaseA1_prodChar`）、`UA1`（読みでは U）は charU(χ₁χ₂) を s·χ₁(N)·χ₂(M)·phaseA1(χ₁)·phaseA1(χ₂) 倍します（`UA1_charU_prodChar`）。単数での値は (χ₁χ₂)(u) = χ₁(u mod M)·χ₂(u mod N) です（`charU_prodChar`。「中国剰余定理の 2 つの成分の関数の積」は読み）。これは原始指標の積 1 つの上の固有値の式で、作用素全体の等式ではありません。原始でない指標では、因子は導手での値 χ₁*(d₂)·χ₂*(d₁) に変わります（数値 (4)。Lean にしていない）。
   5. **ずれは実際に起きる（存在の例）。**
-     - 法 15 = 3·5 に、W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組があります（`rootNum_prodChar_ne_mul`・`phaseA1_prodChar_ne_mul`）。この例では比が ∓i で、交差項と符号 s が混ざっています（A・B の手計算。比の値は Lean の文にない）。
-     - 符号 s だけでずれる例：法 39 = 3·13 に、交差項が 1 で W(χ₁χ₂) = −W(χ₁)·W(χ₂)、W(χ₁)·W(χ₂) ≠ 0 となる奇の原始指標の組があります（`rootNum_prodChar_eq_neg_mul`。B が手計算で示した例を Lean にした。数値 (13)）。
-     - 交差項だけでずれる例（符号 s = 1 で交差項 ≠ 1）と、等号になる例（法 3 の奇の指標と法 5 の偶の 2 次の指標。数値 (13)）は Lean にしていません。ずれは指標の選び方によります。「積ではない」は「一般には積ではない」の意味です。
+     - 法 15 = 3·5 に、W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組があります（`rootNum_prodChar_ne_mul`。phaseA1 の版 `phaseA1_prodChar_ne_mul` は「奇」を含まない形）。この例では比が ∓i で（W(χ₁)·W(χ₂) ≠ 0 なので比が言える）、交差項と符号 s が混ざっています（A・B の手計算。比の値は Lean の文にない）。
+     - 符号 s だけでずれる例：法 39 = 3·13 に、交差項が 1 で W(χ₁χ₂) = −W(χ₁)·W(χ₂)、W(χ₁)·W(χ₂) ≠ 0 となる奇の原始指標の組があります（`rootNum_prodChar_eq_neg_mul`。B が手計算で示した例を Lean にした。数値 (13)）。この例では交差項が 1 なので τ(χ₁χ₂) = τ(χ₁)·τ(χ₂)（`gaussSum_prodChar`）で、−1 は W の正規化（奇×奇で i·i = −1）から来ます（再照合 A2 の指摘）。「算術的な符号の破れ」とは読みません。
+     - 交差項だけでずれる例（符号 s = 1 で交差項 ≠ 1。例：法 3 の奇の指標と法 7 の 3 次の指標。再照合のときに数値で確認）と、等号になる例（法 3 の奇の指標と法 5 の偶の 2 次の指標。数値 (13)）は Lean にしていません。ずれは指標の選び方によります。「積ではない」は「一般には積ではない」の意味です。
   6. **条件つきの文。** W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 なら s·χ₁(N)·χ₂(M) = 1（`cross_eq_sign_of_rootNum_one`）。互いに素の仮定 h は余分です（互いに素でなければ W(χ₁χ₂) = 0 ≠ 1。A の指摘。Lean の文は仮定つきのまま）。
@@ -19,8 +19,8 @@
   - 「素点」「貼り合わせ」「重なり」は著者の言葉です。Lean の文は、指標とガウス和についての恒等式です。
-  - 互いに素な法ごとに見ると、法 M·N の貼り合わせ U の固有値は、一般には、法 M と法 N の固有値の積ではありません。ずれは 2 つです。交差項 χ₁(N)·χ₂(M) は、相手の法を自分の指標で読んだ値です。符号 s は偶奇の因子から出ます。偶奇の因子は、文献では無限素点の局所因子にあたります（Lean では偶奇の因子としてだけ現れます）。
-  - 文献の名前（独立照合 C、§7）：交差項は「不分岐な指標でひねったときの ε 因子の変化」、符号 s は (−1)^{a₁a₂} で、実素点のヒルベルト記号 (−1, −1)_∞ と同じ形。2 次の指標では、全体がヒルベルト記号の積公式と同値。
+  - 互いに素な法ごとに見ると、法 M·N の貼り合わせ U の固有値は、一般には、法 M と法 N の固有値の積ではありません。ずれは 2 つです。交差項 χ₁(N)·χ₂(M) は、相手の法を自分の指標で読んだ値です。符号 s は偶奇の因子（W の正規化の i^a）から出ます。偶奇の因子は、文献では無限素点の局所因子にあたります（Lean では偶奇の因子としてだけ現れます）。
+  - 文献の名前（独立照合 C、§7）：交差項は「不分岐な指標でひねったときの ε 因子の変化」、符号 s は (−1)^{a₁a₂} で、実素点のヒルベルト記号 (−1, −1)_∞ と同じ形。2 次の指標では、W = 1 を外から入れるとヒルベルト記号の積公式と同じ形になる（C の申告。未確認）。
   - **言い方の注意（着手前の盲検の指摘）。** 文献では、大域の ε 因子は局所の ε 因子の積です（Tate、Deligne）。ここで言うずれは、ディリクレ指標を中国剰余定理で分けた成分 χ₁, χ₂ と、イデール類指標の局所成分との違いです。交差項は、χ₁ の、N を割る素点での局所成分（不分岐だが自明でない）から出ます。「大域は局所の積ではない」とは書きません。
 - **2 次の指標と相互法則（観察。主な結果にしない）。** p, q が異なる奇素数で χ₁, χ₂ がルジャンドル記号のとき、数値では W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 で、6 の文は平方剰余の相互法則 (q/p)(p/q) = (−1)^{(p−1)(q−1)/4} と同じ形になります（step279 の (2)：奇素数の 28 組）。ただし、ここから相互法則が出るのではありません。合成の法 pq の 2 次の指標で W = 1 であることは外から入れる事実で、その証明の引き方によっては循環します（着手前の盲検の指摘）。
-- **公準 A1 との関係。** A1 は公準のままです。交差項の法則はルート数という量についての恒等式で、A1 から何かを出すものではありません。A1 を外すと位相は自由に戻り、この法則は位相の選び方への制約ではなくなります（除去テスト。CLAUDE.md §7 の第 2 の型）。
-- **位置づけ。** 既知の事実の Lean 化です（再導出、確信度：高）。Montgomery–Vaughan の Theorem 9.6、Tate・Deligne の局所定数の GL(1)/ℚ の場合です。新規候補はありません。形式化としては、互いに素な法でのガウス和の乗法性は Mathlib と Isabelle AFP に見つかりませんでした（着手前の盲検と、この環境の Mathlib の grep。見落としの可能性あり）。兆候 4（既知の事実だけ）は 8 パート連続です（§6）。
+- **公準 A1 との関係。** A1 は公準のままです。交差項の法則は W（原始指標ではルート数）についての恒等式で、A1 から何かを出すものではありません。A1 を外すと位相は自由に戻り、この法則は位相の選び方への制約ではなくなります（除去テスト。CLAUDE.md §7 の第 2 の型）。
+- **位置づけ。** 既知の事実の Lean 化です（再導出、確信度：高）。Montgomery–Vaughan の Theorem 9.6 とそのルート数版の Lean 化です。文献では、大域の ε 因子が局所の積であることと、不分岐なひねりでの局所 ε 因子の変化から出る形にあたります（局所 ε 因子は Lean にしていない）。新規候補はありません。形式化としては、互いに素な法でのガウス和の乗法性は Mathlib と Isabelle AFP に見つかりませんでした（着手前の盲検と、この環境の Mathlib の grep。見落としの可能性あり）。兆候 4（既知の事実だけ）は 8 パート連続です（§6）。
 
@@ -140,2 +140,3 @@
 - **直したもの。** 題（範囲を「互いに素な法の原始指標の積の上」に）、「一般には積ではない」、「互いに素な法ごと」、問いへの答えの範囲の明記、文の重みの区別（§1）、`rootNum_prodChar_ne_mul` に「両方が奇」、`rootNum_prodChar_eq_neg_mul` の追加、数値 (13)、xlsx の行の言い方。
+- **直し漏れ（再照合で分かった）。** 上の直しはノートと表にだけ入れ、Lean の冒頭の説明と docstring には入れていなかった。§8 で直した。
 - **直していないもの（記録）。** 互いに素の仮定を外した形の Lean 化（`gaussSum_prodChar`・`rootNum_prodChar`・`cross_eq_sign_of_rootNum_one` の h）、交差項だけでずれる例と等号の例の Lean 化、原始でない指標の法則、作用素の式、3 つ以上の法。
@@ -144 +145,10 @@
 
+## 8. 再照合（2026-11-14、著者側の補足3 の開始条件 1）
+
+- **対象。** 照合の後に足した `rootNum_prodChar_eq_neg_mul`、文を強めた `rootNum_prodChar_ne_mul`、B の後に直した文面。
+- **手順。** 新しいエージェント A2（逆翻訳。中立化した名前で S18・S23 を判定）と B2（照合。形式文と定義の全文、Lean の docstring の全文、ノートの全文、表の全行、A2 の出力の全文を渡した）。入力が長いので、照合者は入力ファイルを Read で読む形にした（ツール使用：A2 は 1 回、B2 は 2 回。どちらも入力ファイルの Read だけ）。記録は `pag2_reaudit_252_256.md` と `reaudit257/`。
+- **A2。** S18・S23 は真で、端の場合（証人）。法 39 の −1 は W の正規化から来る（ガウス和は乗法的）。交差項だけが要る例は示されていない（法 3 と法 7 の 3 次の指標が候補）。
+- **B2。** 形式文 23 個に偽・空虚・別物はない。★の 2 文は表とノートで一致。ずれは主に Lean の冒頭の説明と docstring：`UA1_charU_prodChar` の docstring に符号 s が抜けていた（両方が奇のとき −1 倍ずれる）、`crossSign` を「交差項の符号」と呼んでいた、冒頭の「無限素点の因子」が事実として書かれていた、`phaseA1_prodChar_ne_mul` を「局所の位相の積と違う」と書いていた、など。ノートは 11・13・14・21・24・25 行。
+- **直したもの。** Lean の冒頭の説明を形式文から書き直し、docstring 12 個を直した（形式文は変えていない。組み立て直して確認）。ノートの上の行、表の見出しと 2 行（`rootNum_prodChar_ne_mul`・`rootNum_prodChar_eq_neg_mul`）。法 39 の例に「τ は乗法的、−1 は正規化から」を足した。交差項だけでずれる例は、数値で確かめた（`reaudit257/numeric/check_cross_only.py`。Lean にはしていない）。
+- **第 3 の型の検知。** B の後の直しが、ノートと表だけに入り、Lean の文面に入っていなかった（Part 252・254・255 と同じ型）。
+
```

## 入力 (6)：表（xlsx）の差分
```
【見出し（直す前）】PAG2.0-256 互いに素な法の原始指標の積の上での、貼り合わせ U の固有値：交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（著者が 2026-11-13 18:15 に候補 M1 を選んだ。すべて既知の事実の Lean 化：Montgomery–Vaughan の Theorem 9.6、Tate・Deligne の局所定数の GL(1)/ℚ の場合）
【見出し（直した後）】PAG2.0-256 互いに素な法の原始指標の積の上での UA1 の固有値の式（読み：貼り合わせ U の固有値）：交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（著者が 2026-11-13 18:15 に候補 M1 を選んだ。既知の事実の Lean 化：Montgomery–Vaughan の Theorem 9.6 とそのルート数版。文献では、大域の ε 因子が局所の積であることと、不分岐なひねりでの局所 ε 因子の変化から出る形にあたる。局所 ε 因子は Lean にしていない）

【rootNum_prodChar_ne_mul の主張（直す前）】中国剰余定理の成分の積とのずれの例：法 15 = 3·5 に、W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組がある（存在の例 1 つ。比の値 ∓i は文にない）
【rootNum_prodChar_ne_mul の主張（直した後）】中国剰余定理の成分の積とのずれの例：法 15 = 3·5 に、W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組がある（存在の文。条件を満たす 2 組のどちらでも成り立つ。比の値 ∓i は文にない）

【rootNum_prodChar_ne_mul の証明の要点（直す前）】s = −1、χ₁(5) = −1、χ₂(3)² = −1 なので比 χ₂(3) ≠ 1
【rootNum_prodChar_ne_mul の証明の要点（直した後）】s = −1、χ₁(5) = −1 なので W(χ₁χ₂) = χ₂(3)·W(χ₁)W(χ₂)。χ₂(3)² = −1 で χ₂(3) ≠ 1、W(χ₁)W(χ₂) ≠ 0

【rootNum_prodChar_eq_neg_mul の主張（直す前）】符号だけでずれる例：法 39 = 3·13 に、交差項 χ₁(13)·χ₂(3) = 1 で W(χ₁χ₂) = −W(χ₁)·W(χ₂)、W(χ₁)·W(χ₂) ≠ 0 となる奇の原始指標の組がある（独立照合 B の手計算の例を Lean にした）
【rootNum_prodChar_eq_neg_mul の主張（直した後）】符号だけでずれる例：法 39 = 3·13 に、交差項 χ₁(13)·χ₂(3) = 1 で W(χ₁χ₂) = −W(χ₁)·W(χ₂)、W(χ₁)·W(χ₂) ≠ 0 となる奇の原始指標の組がある（独立照合 B の手計算の例を Lean にした）。交差項が 1 なので τ(χ₁χ₂) = τ(χ₁)·τ(χ₂) で、−1 は W の正規化（奇×奇で i·i = −1）から来る
```

## 課題
1. B2 の「直すべき点」の各項目について、直しが「入った／不十分／入っていない／直しが誤り」のどれかを、短い理由とともに書いてください。直していない項目は、その扱いが文面（ノートの記録など）に書かれているかも見てください。
2. 差分の中の新しい文面に、形式文より強い言い方、形式文にないことを事実として書いた箇所、計算や参照の誤りがないかを見てください。あれば、場所と直し方の案を書いてください。
3. 全体の判定を 1 行で：直しで残ったずれ（あれば重要な順に）。
