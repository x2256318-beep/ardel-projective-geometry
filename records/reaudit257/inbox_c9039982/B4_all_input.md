あなたは独立の照合者です。ある Lean 4（Mathlib）の形式化について、照合者 B3 が文面の直しの残りを指摘し、構築者がもう一度文面を直しました（第 2 回の直し）。4 つのファイル（Part 252・254・255・256）について、第 2 回の直しが正しく入ったかを、形式文と突き合わせて判定してください。

## 守ってほしいこと
- この入力ファイルを Read で読んだあとは、ツールを一切使わないでください（ほかのファイル、シェル、検索、Web、エージェントの起動もしない）。長くて 1 回で読み切れないときは、同じファイルの続き（offset を指定）を読むことだけ許します。
- 定義名・定理名は意味の根拠にしないでください。著者の解釈の言葉は「読み」と明示されていれば許容です。
- 判断ごとに確信度（高・中・低）を付けてください。回答は日本語で、各 Part 500 字程度、全体で 2,500 字までにまとめてください。最後に Read の回数を書いてください。

## 課題（各 Part について）
1. B3 が挙げた残りのずれのそれぞれが、第 2 回の直しで「入った／不十分／入っていない」か。直していないものの扱いが記録されているか。
2. 第 2 回の直しの新しい文面に、形式文より強い言い方や新しい誤りがないか。
3. 1 行の判定。


## Part 252

### Part 252 の入力 (1)：定義の全文（このファイルと前のファイル。原文のまま。コメントと docstring だけ除いた）
```lean
-- PAG256.lean（文脈：namespace PAG.Part256 / open ZMod Complex Finset / variable {N : ℕ} [NeZero N]）

noncomputable def casKer (t : ZMod N) : ℂ :=
  ((Real.cos (2 * Real.pi * t.val / N) + Real.sin (2 * Real.pi * t.val / N) : ℝ) : ℂ)

noncomputable def hartley (f : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * casKer (x * y)

noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2

open Classical in
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))

noncomputable def JH (f : ZMod N → ℂ) (u : (ZMod N)ˣ) : ℂ :=
  hartley f ((u⁻¹ : (ZMod N)ˣ) : ZMod N) / (Real.sqrt N : ℂ)
```

### Part 252 の入力 (2)：形式文の全文（PAG256.lean の定理 22 個すべて。原文のまま、証明だけ除いた。すべてコンパイル済みで sorry なし、公理は標準の範囲）
```lean
theorem casKer_eq (t : ZMod N) :
    casKer t = ((1 - I) * stdAddChar t + (1 + I) * stdAddChar (-t)) / 2
omit [NeZero N] in
theorem parFac_of_even {χ : DirichletCharacter ℂ N} (h : χ.Even) : parFac χ = 1
omit [NeZero N] in
theorem parFac_of_odd {χ : DirichletCharacter ℂ N} (h : χ.Odd) : parFac χ = -I
omit [NeZero N] in
theorem inv_apply_neg_one (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1)
theorem sum_mul_stdAddChar (χ : DirichletCharacter ℂ N) (y : ZMod N) :
    ∑ x : ZMod N, χ x * stdAddChar (x * y) = gaussSum χ (stdAddChar.mulShift y)
theorem hartley_eq_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (y : ZMod N) :
    hartley (χ : ZMod N → ℂ) y = parFac χ * gaussSum χ stdAddChar * χ⁻¹ y
theorem hartley_eq_zero_of_not_isUnit {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {y : ZMod N} (hy : ¬IsUnit y) : hartley (χ : ZMod N → ℂ) y = 0
theorem rootNum_eq (χ : DirichletCharacter ℂ N) :
    rootNum χ = parFac χ * gaussSum χ stdAddChar / (Real.sqrt N : ℂ)
omit [NeZero N] in
theorem inv_apply_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ⁻¹ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u
theorem JH_eq_rootNum_mul {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u
theorem normSq_rootNum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (rootNum χ) = 1
theorem hartley_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    hartley (χ : ZMod N → ℂ) ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u * hartley (χ : ZMod N → ℂ) 1
omit [NeZero N] in
theorem neg_one_mul_self (χ : DirichletCharacter ℂ N) : χ (-1) * χ (-1) = 1
theorem sum_mul_stdAddChar_neg (χ : DirichletCharacter ℂ N) :
    ∑ x : ZMod N, χ x * stdAddChar (-x) = χ (-1) * gaussSum χ stdAddChar
theorem hartley_one (χ : DirichletCharacter ℂ N) :
    hartley (χ : ZMod N → ℂ) 1 = parFac χ * gaussSum χ stdAddChar
theorem JH_eq_rootNum_mul_any (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u
theorem isPrimitive_of_prime_of_ne_one {p : ℕ} [hp : Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (h : χ ≠ 1) : χ.IsPrimitive
theorem exists_primitive_odd_three : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Odd
theorem exists_primitive_even_five :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Even ∧ χ ≠ 1
theorem removal_counterexample :
    ¬(1 : DirichletCharacter ℂ 2).IsPrimitive ∧ ¬IsUnit (0 : ZMod 2) ∧
      hartley ((1 : DirichletCharacter ℂ 2) : ZMod 2 → ℂ) 0 = 1
theorem removal_counterexample_normSq :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ 2)) = 1 / 2
-- ★ 
theorem removal_counterexample_four :
    (∃ χ : DirichletCharacter ℂ (2 ^ 2), χ.IsPrimitive) ∧
    ¬(1 : DirichletCharacter ℂ 4).IsPrimitive ∧ ¬IsUnit (2 : ZMod 4) ∧
      hartley ((1 : DirichletCharacter ℂ 4) : ZMod 4 → ℂ) 2 = -2 ∧
      Complex.normSq (rootNum (1 : DirichletCharacter ℂ 4)) = 0
```


### Part 252 の入力 (3)：B3 の出力の全文（原文のまま）

# B2 指摘の直しの照合結果（Part 252）

## 1. B2 の「直すべき点」の各項目

1. **JH_eq_rootNum_mul の docstring**：入った〔高〕
   - B2 の案のとおりに直っています。
   - 式 (H_N χ)(u⁻¹)/√N = W(χ)·χ(u) は、JH の定義の本文と一致します。「主定理」の言い方も消えました。
   - 足された「JH は ℤ/N の上の関数を単数の上の関数に送る写像」も、定義の型のとおりです。
2. **Lean の冒頭説明**：入った〔高〕
   - 題に「読み」が付き、「重なりの読みは」に変わりました。
   - 本文は「構築者が再構成した…（U = J∘H_N/√N）…と読める恒等式（読み。U と A1 は文に出てこない）」になりました。
   - 末段の「ルート数という量」も W（rootNum）に直っています。ただし 2(a) を見てください。
3. **ノート行 26**：入った〔高〕
   - 次の 4 点がそろいました。正規化の直し、（読み）の標示、根拠（数値 (9) と τ の公式。Lean にあるのは法 2・法 4 の例だけ）、「τ = 0 なら固有値は 0」。
4. **ノート行 1（題）**：入った〔高〕
   - /√N、H_N は正規化しないこと、「単数の上で」、W の式、「読み」がすべて入りました。
5. **rootNum の docstring**：入った〔高〕
   - 「0 にもなる（法 4）」は、|rootNum(1₄)|² = 0 と合います。
6. **removal_counterexample_normSq**：入った〔高〕
   - docstring・xlsx・行 90 のどれも、原始的でないことを removal_counterexample の第 1 成分（¬IsPrimitive）に帰すようになりました。
7. **法 2 に原始指標がないことの「Lean の外」**：入った〔高〕
   - 行 18・行 141、冒頭説明の 6、xlsx のすべてに入りました。
   - 法 4 に原始指標があることは Lean の文にあるので、その書き分けも正しいです。
8. **§7 の記録**：不十分〔高〕
   - 行 170・行 172 は直りました。
   - 行 161 は、差分にも §8 の「直した行」の一覧にもありません。扱いも書かれていません。ただ、行 161 の中身は入力にないので、直す必要があるかどうかは〔中〕です。
   - 行 170 の括弧書きは「行 26 と Lean…に入っていなかった」としていますが、ノートの題が抜けています。§8 の B2 の段には題が書かれています〔中〕。
9. **細部**：不十分〔高〕
   - 入ったもの：行 123・158・29・12・31・159・46、行 23 の「整合」、行 26 の τ = 0、xlsx の見出し、ラベルの逆転（S10 を「既知」に）。
   - 入っていないもの：行 68 の「固有値は cas 版のガウス和」です。差分では文脈行のままで、/√N が付いていません。§8 の一覧にもなく、扱いも書かれていません。

## 2. 新しい文面の点検

- **(a) Lean 冒頭の末段**〔中〕
  - 該当箇所は「W（rootNum。原始指標ではルート数）についての恒等式である（A1 は位相をこの値に選ぶ公準）」です。
  - 直した結果、「この値」が、すべての指標についての rootNum を指すようになりました。
  - 一方、行 26 の読みでは、A1 は原始的でない χ に誘導元のルート数を割り当てます。これは rootNum と一致しません（|rootNum| < 1）。
  - さらに、A1 の中身を読みの標示なしに書いています。
  - 直し方の案：「（読み：A1 は原始指標の位相をこの値に選ぶ公準）」。
  - ノート行 24 の「ルート数という量についての恒等式」にも、B2 §3.5 と同じずれが残っています〔低〕。
- **(b) §8 の B2 の段**〔高・軽微〕
  - 「偽・空虚・別物はない」とだけ書いています。
  - B2 は「空虚は全体としてない」としたうえで、注意を 3 点付けていました。
  - そのうち「原始性を仮定する 4 文は N = 2 では空虚に成り立つ」は、§8 のどこにもありません。残りの 2 点は、A2 の段に同じ趣旨が書かれています。
  - 直し方の案：B2 の段にこの注意を足す。
- **(c) 行 26 の「H_N χ は単数でないところに値をもちます（数値 (8)、440/440）」**〔低〕
  - 文は一般の形ですが、根拠は N ≤ 60 の数値だけです。
  - 一般の形も正しいです。|W| < 1 と H_N² = N·I から、Σ_{単数でない y}|H_N χ(y)|² = Nφ(N)(1 − |W|²) > 0 が出ます。ただしこれは Lean の外です。
  - 直し方の案：「一般の形は Lean の外。Lean にあるのは法 2 の 0、法 4 の 2 での値だけ」を足す。
- **(d) 計算と参照**：誤りはありません〔高〕
  - 形式文と合うもの：H_N χ(0) = 1、H_N χ(2) = −2、|W|² = 1/2・0、τ/(i^a√N) = ετ/√N、「hartley_one は y = 1 の場合」、「原始的な χ では反対角」（H_N χ = parFac·τ·χ̄）。
  - 数値も手で検算し、一致しました。
    - N = 2〜60 で Σφ(N) = 1,101（行 89 と一致）。原始指標は 661 個、原始的でない指標は 440 個です。
    - τ の公式から、τ = 0 になるのは 135 個です。|W| の最大は 1/√2 ≈ 0.707 です。
  - 「7,517 個」と、§8 の A2 の段の中身は、入力からは確かめられません〔低〕。
- **(e) rootNum の docstring と xlsx の「原始的でない χ ではルート数ではない」**：一般の形の言い方ですが、用語の注意として許容です〔中〕。

## 3. 全体の判定（1 行）

項目 1〜7 は入り、形式文より強い言い方が新しく増えた箇所はありません。残ったずれ（重要な順）：①行 68 の固有値に /√N がない（直っておらず、記録もない）②行 161 の記録が直っておらず、行 170 には「題」が抜けている ③Lean 冒頭末段の「この値」が行 26 の読みと食い違い、ノート行 24 にも同じずれが残る ④§8 が B2 の空虚さの注意を 1 点落としている ⑤行 26 の一般形の根拠（軽微）〔高〕。

Read の回数：1 回（入力ファイルだけ）

### Part 252 の入力 (4)：第 2 回の直しの差分（Lean の文面とノート。形式文は変えていない）
```diff
--- PAG256.lean（第 1 回の直しの後）
+++ PAG256.lean（第 2 回の直しの後）
@@ -18,4 +18,4 @@
   Hartley の形で書いた文献は、盲検の問いテストでは見つからなかった（書き直しであって新しい内容ではない）。
-  公理 A1 は Lean の公理にしていない。ここでの文は W（`rootNum`。原始指標ではルート数）についての恒等式である（A1 は位相を
-  この値に選ぶ公準）。
+  公理 A1 は Lean の公理にしていない。ここでの文は W（`rootNum`。原始指標ではルート数）についての恒等式である（読み：A1 は原始指標の
+  位相をこの値に選ぶ公準）。
 -/

--- pag2_part252_hartley_gluing.md（第 1 回の直しの後）
+++ pag2_part252_hartley_gluing.md（第 2 回の直しの後）
@@ -23,5 +23,5 @@
   - 意味としては（解釈）、A1 の貼り合わせが「点どうしの同一視」ではなく、フーリエ型の作用素であることと、原始指標の部分で整合します（着手前の文書の Q1）。Lean の文は A1 に触れていません。
-  - A1 は Lean の公理にしていません。ここでの文はルート数という量についての恒等式で、「A1 を導いた」ことにはなりません（CLAUDE.md §6）。A1 は位相をこの値に選ぶ公準のままです。
+  - A1 は Lean の公理にしていません。ここでの文は W（`rootNum`。原始指標ではルート数）についての恒等式で、「A1 を導いた」ことにはなりません（CLAUDE.md §6）。A1 は原始指標の位相をこの値に選ぶ公準のままです（読み）。
 - **Lean にしていないこと。**
-  - (ℤ/N)^× 上の関数の空間全体での作用素の等式。原始的でない指標でも、単数に制限した J∘H_N/√N の固有ベクトルにはなります（τ = 0 なら固有値は 0）。ただし固有値 ε(χ)τ(χ)/√N は絶対値が 1 未満で（N ≤ 60 では最大 0.707、τ = 0 が 440 個中 135 個。数値 (9) と τ の公式による。Lean にあるのは法 2・法 4 の自明な指標で |W|² = 1/2・0 となる例だけ）、H_N χ は単数でないところに値をもちます（数値 (8)、440/440）。（読み）A1 が原始的でない χ に誘導元のルート数を割り当てると読むなら、U = J∘H_N/√N は単数に台をもつ関数の空間全体では成り立たず、原始指標の部分に限られます。
+  - (ℤ/N)^× 上の関数の空間全体での作用素の等式。原始的でない指標でも、単数に制限した J∘H_N/√N の固有ベクトルにはなります（τ = 0 なら固有値は 0）。ただし固有値 ε(χ)τ(χ)/√N は絶対値が 1 未満で（N ≤ 60 では最大 0.707、τ = 0 が 440 個中 135 個。数値 (9) と τ の公式による。Lean にあるのは法 2・法 4 の自明な指標で |W|² = 1/2・0 となる例だけ）、H_N χ は単数でないところに値をもちます（数値 (8)、440/440。一般の形は Lean の外。Lean にあるのは法 2 の 0、法 4 の 2 での値だけ）。（読み）A1 が原始的でない χ に誘導元のルート数を割り当てると読むなら、U = J∘H_N/√N は単数に台をもつ関数の空間全体では成り立たず、原始指標の部分に限られます。
     - 最初の版のこの箇所は「原始的でない指標では J∘H_N/√N の固有ベクトルにならず」と書いていました。誤りです。数値 (8) が破れていたのは単数でない点での値で、単数の上の式ではありませんでした（§7）。
@@ -67,3 +67,3 @@
 | 原始指標の場合の式（`JH_eq_rootNum_mul`。下のすべての指標での式に含まれる）と \|W\| = 1（`normSq_rootNum`） | 既知（\|W\| = 1 は再導出） | 同上と Part 16。素数の法のフーリエ版は Benoist 2024 の式 (3.5) |
-| すべての指標での単数の上の式（`JH_eq_rootNum_mul_any`）と補題（`hartley_units_inv`・`hartley_one`・`sum_mul_stdAddChar_neg`） | 既知 | 平行移動と可換な作用素は指標で対角（定理 2.6 の (a) の型）。固有値は cas 版のガウス和 |
+| すべての指標での単数の上の式（`JH_eq_rootNum_mul_any`）と補題（`hartley_units_inv`・`hartley_one`・`sum_mul_stdAddChar_neg`） | 既知 | 平行移動と可換な作用素は指標で対角（定理 2.6 の (a) の型）。固有値は cas 版のガウス和を √N で割ったもの |
 | 証人と除去テストの反例 | 既知 | 素数の法の自明でない指標は原始的、指標の分離性 |
@@ -160,3 +160,3 @@
 | 6 | Φ4 を L 関数の関数等式に結ぶ補題がない（A。A0・C は Mathlib の rootNumber に言及） | 確かめました：Mathlib の `DirichletCharacter.rootNumber` は同じ式で定義され、関数等式 `IsPrimitive.completedLFunction_one_sub`（Λ(1 − s, χ) = N^{s − 1/2}·rootNumber·Λ(s, χ⁻¹)）に現れます。モジュールがこの環境で未ビルドなので、一致は Lean の文にしていません |
-| 7 | Φ5 は入力（ℤ/N 上の関数）と出力（単数の上の関数）の空間が違い、「固有値」は緩い意味（A） | 受け入れます。ノートでは「単数に制限した J∘H_N/√N」と書きます（単数に台をもつ関数に制限すれば、単数の上の関数の空間の作用素になります） |
+| 7 | Φ5 は入力（ℤ/N 上の関数）と出力（単数の上の関数）の空間が違い、「固有値」は緩い意味（A） | 受け入れます。ノートでは「単数に制限した J∘H_N/√N」と書きます（単数に台をもつ関数に制限すれば、単数の上の関数の空間の作用素になります）。Lean の `JH_eq_rootNum_mul` の docstring には入っていなかった（「固有ベクトル」のまま）。再照合の後に直した |
 | 8 | 規約：e の向き、cos ± sin、J∘H と H∘J、i^a の組み合わせで、奇の指標の符号が変わる（A0・A・C） | 記録しました。今の組み合わせ（e(+)、cos + sin、J∘H、i^a）は互いに整合し、Davenport の W(χ) = τ(χ)/(i^a √q) と Mathlib の rootNumber に一致します。モノグラフの規約との照合は、照合ノート §5 の 4 のまま |
@@ -169,3 +169,3 @@
 |---|---|---|
-| 1 | 「モノグラフ §1.3 の主張 (2) の原始指標の部分」という位置づけは判定不能で過大（U も A1 も形式文にない、本文と未照合）。H_N を正規化なしで定義しているので「U = JH_N」と Lean の J∘H_N/√N が √N ずれる | 受け入れます。結論に「構築者の再構成、本文と未照合、解釈」と書き、正規化を U = J∘H_N/√N にそろえ、記法の注意を足しました。xlsx の見出しも直しました（ただし行 26 と Lean の冒頭の説明・docstring には直しが入っていなかった。再照合 B2 で見つかり、§8 で直した） |
+| 1 | 「モノグラフ §1.3 の主張 (2) の原始指標の部分」という位置づけは判定不能で過大（U も A1 も形式文にない、本文と未照合）。H_N を正規化なしで定義しているので「U = JH_N」と Lean の J∘H_N/√N が √N ずれる | 受け入れます。結論に「構築者の再構成、本文と未照合、解釈」と書き、正規化を U = J∘H_N/√N にそろえ、記法の注意を足しました。xlsx の見出しも直しました（ただしノートの題と行 26、Lean の冒頭の説明・docstring には直しが入っていなかった。再照合 B2 で見つかり、§8 で直した） |
 | 2 | 「原始指標の張る部分の上で、ルート数を掛ける作用素」は、線形性・部分空間・直交性がないので「各原始指標について」に弱めるべき | 受け入れて弱めました。作用素としての文は「Lean の外」と明記しました |
@@ -185,3 +185,3 @@
 - **A2。** 7 文とも真。S16〜S18 は自明、S19・S20 は標準、S21・S22 は端の場合（証人）。S22 の 1 つ目の成分（法 4 に原始指標がある）は、ほかの成分とつながらない非空虚性の証人。S20 から S10（`JH_eq_rootNum_mul`）が直ちに出る。JH は u⁻¹ と 1/√N を定義に組み込んでいて、「固有値方程式」に見えるのは定義による（入力と出力の空間が違う）。
-- **B2。** 形式文 22 個に偽・空虚・別物はない。ずれは、B の後の直し（正規化 U = J∘H_N/√N、「解釈・本文と未照合」の標示、rootNum はルート数とは限らない）がノートの題と行 26、Lean の冒頭の説明と docstring に入っていなかったこと。ラベルの逆転（含まれる S10 が再導出、含む S20 が既知）、`removal_counterexample_normSq` の「原始的でない」の帰属、「原始指標のない法 2」が Lean の外であることの標示漏れなど。
+- **B2。** 形式文 22 個に偽・空虚・別物はない（注意：原始性を仮定する 4 文は N = 2 では空虚に成り立つ。`JH_eq_rootNum_mul` は `JH_eq_rootNum_mul_any` に含まれる。`removal_counterexample_four` の第 1 成分はほかの成分と無関係な証人）。ずれは、B の後の直し（正規化 U = J∘H_N/√N、「解釈・本文と未照合」の標示、rootNum はルート数とは限らない）がノートの題と行 26、Lean の冒頭の説明と docstring に入っていなかったこと。ラベルの逆転（含まれる S10 が再導出、含む S20 が既知）、`removal_counterexample_normSq` の「原始的でない」の帰属、「原始指標のない法 2」が Lean の外であることの標示漏れなど。
 - **直したもの。** Lean の冒頭の説明 3 か所と docstring 3 個（`rootNum`・`JH_eq_rootNum_mul`・`removal_counterexample_normSq`。形式文は変えていない。組み立て直して確認）。ノートの上の行（題、12・18・23・26・29・31・46・67・84・90・123・141・158・159・170・172 行）と、表の見出しと 1 行（`removal_counterexample_normSq`）。
```


## Part 254

### Part 254 の入力 (1)：定義の全文（このファイルと前のファイル。原文のまま。コメントと docstring だけ除いた）
```lean
-- PAG256.lean（文脈：namespace PAG.Part256 / open ZMod Complex Finset / variable {N : ℕ} [NeZero N]）

noncomputable def casKer (t : ZMod N) : ℂ :=
  ((Real.cos (2 * Real.pi * t.val / N) + Real.sin (2 * Real.pi * t.val / N) : ℝ) : ℂ)

noncomputable def hartley (f : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * casKer (x * y)

open Classical in
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))

noncomputable def JH (f : ZMod N → ℂ) (u : (ZMod N)ˣ) : ℂ :=
  hartley f ((u⁻¹ : (ZMod N)ˣ) : ZMod N) / (Real.sqrt N : ℂ)

-- PAG257.lean（文脈：namespace PAG.Part257 / open ZMod Complex Finset PAG.Part256 / variable {N : ℕ} [NeZero N]）

open Classical in
noncomputable def extL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun g x := if h : IsUnit x then g h.unit else 0
  map_add' f g := by
    funext x
    by_cases h : IsUnit x <;> simp [h]
  map_smul' c f := by
    funext x
    by_cases h : IsUnit x <;> simp [h]

noncomputable def JHL : (ZMod N → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := JH f
  map_add' f g := by
    funext u
    show JH (f + g) u = JH f u + JH g u
    unfold JH hartley
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by rw [Pi.add_apply, add_mul])
  map_smul' c f := by
    funext u
    show JH (c • f) u = c * JH f u
    unfold JH hartley
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc])

noncomputable def TopL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) := JHL.comp extL

def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u

noncomputable def ip (f g : (ZMod N)ˣ → ℂ) : ℂ := ∑ u, (starRingEnd ℂ) (f u) * g u

noncomputable def Vprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.IsPrimitive} => charU χ.1)

noncomputable def Vimprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // ¬χ.IsPrimitive} => charU χ.1)

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

noncomputable def pullL {M : ℕ} (hNM : N ∣ M) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod M)ˣ → ℂ) where
  toFun f u := f (ZMod.unitsMap hNM u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

structure Lvl where
  
  val : ℕ
  pos : 0 < val
deriving DecidableEq

instance : Preorder Lvl where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

instance : IsDirectedOrder Lvl :=
  ⟨fun a b => ⟨⟨a.val * b.val, Nat.mul_pos a.pos b.pos⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance : Nonempty Lvl := ⟨⟨1, Nat.one_pos⟩⟩

instance (a : Lvl) : NeZero a.val := ⟨a.pos.ne'⟩

abbrev Gsp (a : Lvl) : Type := (ZMod a.val)ˣ → ℂ

noncomputable def pullSys (a b : Lvl) (h : a ≤ b) : Gsp a →ₗ[ℂ] Gsp b :=
  pullL (N := a.val) (M := b.val) h

instance : DirectedSystem Gsp (fun a b h => (pullSys a b h : Gsp a → Gsp b)) where
  map_self a f := by
    funext u
    show f (ZMod.unitsMap (dvd_refl a.val) u) = f u
    rw [ZMod.unitsMap_self]
    rfl
  map_map c b a hab hbc f := by
    funext u
    show f (ZMod.unitsMap hab (ZMod.unitsMap hbc u)) = f (ZMod.unitsMap (dvd_trans hab hbc) u)
    rw [← ZMod.unitsMap_comp hab hbc]
    rfl

abbrev Lim : Type := Module.DirectLimit Gsp pullSys

noncomputable abbrev ofL (a : Lvl) : Gsp a →ₗ[ℂ] Lim := Module.DirectLimit.of ℂ Lvl Gsp pullSys a

noncomputable def Uinf : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map (fun a => UA1 (N := a.val)) (fun a b h => by
    refine LinearMap.ext (fun f => ?_)
    exact UA1_comp_pullL (N := a.val) (M := b.val) h f)

noncomputable def ipn {a : Lvl} (f g : Gsp a) : ℂ := ip f g / (Nat.totient a.val : ℂ)

noncomputable def ipLim (z w : Lim) : ℂ :=
  ipn (Module.DirectLimit.exists_of₂ z w).choose_spec.choose
    (Module.DirectLimit.exists_of₂ z w).choose_spec.choose_spec.choose

noncomputable def condPart (N : ℕ) [NeZero N] (q : ℕ) : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.conductor = q} => charU χ.1)

noncomputable def ipR (f : (ZMod N)ˣ → ℂ) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ℂ where
  toFun := ip f
  map_add' := ip_add_right f
  map_smul' c g := by rw [ip_smul_right, smul_eq_mul, RingHom.id_apply]
```

### Part 254 の入力 (2)：形式文の全文（PAG258.lean の定理 57 個すべて。原文のまま、証明だけ除いた。すべてコンパイル済みで sorry なし、公理は標準の範囲）
```lean
omit [NeZero N] in
theorem rootNum_congr {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂] (h : d₁ = d₂)
    (χ₁ : DirichletCharacter ℂ d₁) (χ₂ : DirichletCharacter ℂ d₂)
    (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) : rootNum χ₁ = rootNum χ₂
theorem phaseA1_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    phaseA1 χ = rootNum χ
theorem normSq_phaseA1 (χ : DirichletCharacter ℂ N) : Complex.normSq (phaseA1 χ) = 1
theorem phaseA1_changeLevel {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    phaseA1 (changeLevel hNM χ) = phaseA1 χ
omit [NeZero N] in
theorem rootNum_one_of_eq_one {d : ℕ} [NeZero d] (hd : d = 1) :
    rootNum (1 : DirichletCharacter ℂ d) = 1
theorem phaseA1_one : phaseA1 (1 : DirichletCharacter ℂ N) = 1
theorem ip_add_right (f g h : (ZMod N)ˣ → ℂ) : ip f (g + h) = ip f g + ip f h
theorem ip_smul_right (f g : (ZMod N)ˣ → ℂ) (c : ℂ) : ip f (c • g) = c * ip f g
theorem UA1_charU (χ : DirichletCharacter ℂ N) : UA1 (charU χ) = phaseA1 χ • charU χ
theorem ip_UA1 (f g : (ZMod N)ˣ → ℂ) : ip (UA1 f) (UA1 g) = ip f g
theorem UA1_eq_TopL_of_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f = TopL f
omit [NeZero N] in
theorem pullL_charU {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    pullL hNM (charU χ) = charU (changeLevel hNM χ)
theorem UA1_charU_eq_pull_TopL (χ : DirichletCharacter ℂ N) :
    UA1 (charU χ) = pullL χ.conductor_dvd_level (TopL (charU χ.primitiveCharacter))
theorem UA1_unique (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N,
      U (charU χ) = pullL χ.conductor_dvd_level (TopL (charU χ.primitiveCharacter))) :
    U = UA1
theorem UA1_comp_pullL {M : ℕ} [NeZero M] (hNM : N ∣ M) (f : (ZMod N)ˣ → ℂ) :
    UA1 (pullL hNM f) = pullL hNM (UA1 f)
theorem TopL_not_compat :
    ∃ f : (ZMod 1)ˣ → ℂ, TopL (pullL (one_dvd 2) f) ≠ pullL (one_dvd 2) (TopL f)
theorem UA1_ne_TopL_prime (p : ℕ) [hp : Fact p.Prime] :
    charU (1 : DirichletCharacter ℂ p) ∈ Vimprim p ∧
      UA1 (charU (1 : DirichletCharacter ℂ p)) ≠ TopL (charU (1 : DirichletCharacter ℂ p))
theorem UA1_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f ∈ Vprim N
theorem UA1_mem_Vimprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vimprim N) : UA1 f ∈ Vimprim N
theorem UA1_comp_TopL (f : (ZMod N)ˣ → ℂ) : UA1 (TopL f) = TopL (UA1 f)
theorem rootNum_one_prime (p : ℕ) [Fact p.Prime] :
    rootNum (1 : DirichletCharacter ℂ p) = -(((Real.sqrt p)⁻¹ : ℝ) : ℂ)
theorem TopL_not_compat_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ f : (ZMod 1)ˣ → ℂ, TopL (pullL (one_dvd p) f) ≠ pullL (one_dvd p) (TopL f)
theorem gaussSum_inv (χ : DirichletCharacter ℂ N) :
    gaussSum χ⁻¹ (stdAddChar (N := N)) = χ (-1) * (starRingEnd ℂ) (gaussSum χ stdAddChar)
theorem rootNum_inv (χ : DirichletCharacter ℂ N) :
    rootNum χ⁻¹ = (starRingEnd ℂ) (rootNum χ)
theorem primitiveCharacter_inv_apply (χ : DirichletCharacter ℂ N) (a : ℤ) :
    (χ⁻¹).primitiveCharacter a = (χ.primitiveCharacter)⁻¹ a
theorem phaseA1_inv (χ : DirichletCharacter ℂ N) :
    phaseA1 χ⁻¹ = (starRingEnd ℂ) (phaseA1 χ)
theorem UA1_star (f : (ZMod N)ˣ → ℂ) :
    UA1 (fun u => (starRingEnd ℂ) (f u)) = fun u => (starRingEnd ℂ) (UA1 f u)
omit [NeZero N] in
theorem pullL_injective {M : ℕ} [NeZero M] (hNM : N ∣ M) : Function.Injective (pullL hNM)
theorem sum_units_unitsMap {M : ℕ} [NeZero M] (hNM : N ∣ M) (F : (ZMod N)ˣ → ℂ) :
    (Nat.totient N : ℂ) * ∑ u : (ZMod M)ˣ, F (ZMod.unitsMap hNM u) =
      (Nat.totient M : ℂ) * ∑ v : (ZMod N)ˣ, F v
theorem ip_pullL {M : ℕ} [NeZero M] (hNM : N ∣ M) (f g : (ZMod N)ˣ → ℂ) :
    (Nat.totient N : ℂ) * ip (pullL hNM f) (pullL hNM g) = (Nat.totient M : ℂ) * ip f g
theorem UA1_bijective : Function.Bijective (UA1 (N := N))
theorem UA1_family_unique (U : ∀ a : Lvl, Gsp a →ₗ[ℂ] Gsp a)
    (hT : ∀ (a : Lvl) (f : Gsp a), f ∈ Vprim a.val → U a f = TopL f)
    (hc : ∀ (a b : Lvl) (h : a ≤ b) (f : Gsp a), U b (pullSys a b h f) = pullSys a b h (U a f))
    (a : Lvl) : U a = UA1
theorem ofL_injective (a : Lvl) : Function.Injective (ofL a)
theorem Uinf_ofL (a : Lvl) (f : Gsp a) : Uinf (ofL a f) = ofL a (UA1 f)
theorem Uinf_unique (V : Lim →ₗ[ℂ] Lim) (hV : ∀ a (f : Gsp a), V (ofL a f) = ofL a (UA1 f)) :
    V = Uinf
theorem Uinf_bijective : Function.Bijective Uinf
theorem Uinf_ofL_of_mem_Vprim (q : Lvl) {f : Gsp q} (hf : f ∈ Vprim q.val) :
    Uinf (ofL q f) = ofL q (TopL f)
theorem ofL_charU (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
    ofL a (charU χ) =
      ofL ⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩ (charU χ.primitiveCharacter)
theorem span_ofL_Vprim : Submodule.span ℂ (⋃ q : Lvl, ofL q '' (Vprim q.val : Set (Gsp q))) = ⊤
theorem Uinf_unique_TopL (V : Lim →ₗ[ℂ] Lim)
    (hV : ∀ q (f : Gsp q), f ∈ Vprim q.val → V (ofL q f) = ofL q (TopL f)) : V = Uinf
theorem totient_ne_zero' (a : Lvl) : (Nat.totient a.val : ℂ) ≠ 0
theorem ipn_pullSys {a b : Lvl} (h : a ≤ b) (f g : Gsp a) :
    ipn (pullSys a b h f) (pullSys a b h g) = ipn f g
theorem ipn_eq_of_ofL_eq {a b : Lvl} {f g : Gsp a} {f' g' : Gsp b}
    (hf : ofL a f = ofL b f') (hg : ofL a g = ofL b g') : ipn f g = ipn f' g'
theorem ipLim_ofL (a : Lvl) (f g : Gsp a) : ipLim (ofL a f) (ofL a g) = ipn f g
theorem ipLim_Uinf (z w : Lim) : ipLim (Uinf z) (Uinf w) = ipLim z w
theorem ipLim_add_right (z w w' : Lim) : ipLim z (w + w') = ipLim z w + ipLim z w'
theorem ipLim_smul_right (z w : Lim) (r : ℂ) : ipLim z (r • w) = r * ipLim z w
theorem ipLim_conj (z w : Lim) : ipLim w z = (starRingEnd ℂ) (ipLim z w)
theorem eq_zero_of_ipLim_self (z : Lim) (h : ipLim z z = 0) : z = 0
theorem ipLim_self_nonneg (z : Lim) : ∃ r : ℝ, 0 ≤ r ∧ ipLim z z = r
-- ★ 
theorem UA1_pullL_of_mem_Vprim {M : ℕ} [NeZero M] (hNM : N ∣ M) {g : (ZMod N)ˣ → ℂ}
    (hg : g ∈ Vprim N) : UA1 (pullL hNM g) = pullL hNM (TopL g)
-- ★ 
theorem condPart_eq_map {M : ℕ} [NeZero M] (hNM : N ∣ M) :
    condPart M N = (Vprim N).map (pullL hNM)
-- ★ 
theorem ip_condPart {q q' : ℕ} (hqq : q ≠ q') {f g : (ZMod N)ˣ → ℂ}
    (hf : f ∈ condPart N q) (hg : g ∈ condPart N q') : ip f g = 0
-- ★ 
theorem iSup_condPart : ⨆ q, condPart N q = ⊤
-- ★ 
theorem iSupIndep_condPart : iSupIndep (condPart N)
-- ★ 
theorem UA1_mem_condPart {q : ℕ} {f : (ZMod N)ˣ → ℂ} (hf : f ∈ condPart N q) :
    UA1 f ∈ condPart N q
-- ★ 
theorem ipLim_ofL_Vprim {q q' : Lvl} (hqq : q.val ≠ q'.val) {f : Gsp q} {g : Gsp q'}
    (hf : f ∈ Vprim q.val) (hg : g ∈ Vprim q'.val) : ipLim (ofL q f) (ofL q' g) = 0
```


### Part 254 の入力 (3)：B3 の出力の全文（原文のまま）

## B3 照合結果（PAG258 / Part 254 の文面の直し）

形式文は変わっていないので、直した文面を形式文と定義の本文に突き合わせて判定しました。

### 1. B2 の「直すべき点」への対応

1. **直和**：おおむね入った。2 か所が不十分です。
   - ノート 7・14・30・209 行、冒頭 10、表（`iSupIndep_condPart`）は B2 の案どおりです。「添字は ℕ 全体」「q ∤ M の部分が 0 であることは文にない」「1 つの定理にはしていない」が入っています（高）。
   - 題に q ∤ M の但し書きがありません。π(V_prim(q)) は q ∣ M のときしか定義されません（pullL は N ∣ M を要する）。「π(V_prim(q)) は…全体を張る」と言うには、文にない「q ∤ M の部分は 0」が要ります（中）。
   - Lean の冒頭 3 の「直和そのものは 10」（B2 の引用）は差分になく、残っています。10 の「1 つの定理にはしていない」と合いません（中）。
   - Lean で閉じる案は採っていません。その扱いは §8「直していないもの」に理由つきで書かれています（高）。
2. **ラベル**：不十分。
   - 指定の 2 組はそろいました（T の非両立は既知、像の直交は既知）（高）。
   - 75 行の W(χ̄*) = conj W(χ*) は、χ̄* を (χ⁻¹)* と読めば `phaseA1_inv` と同じ文です（高）。
   - ただし、80 行に新しく入った「U_∞ の性質は再導出」が §1 と食い違います。113 行は「U_∞ は各法で U_N・一意・全単射」を既知、115 行は「U_∞ が内積を保つ」を既知としています（高）。
   - 114 行は 2 つに分けた結果、「張る」（`span_ofL_Vprim`）にラベルがなくなりました（低）。
   - 104 行の全文は入力にないので、79 行の「両立と一意性は再導出」と合っているかは確かめられません（低）。
3. **docstring の参照**：入った（高）。
4. **冒頭 5**：入った（高）。
   - 主文は `UA1_ne_TopL_prime` の形（V_imprim に入り、かつ U ≠ T）と一致します。
   - U(1) = 1 は `phaseA1_one` と `UA1_charU` から出ます。
   - Part 253 の 2 定理は入力にないので、確かめられません（中）。
5. **★ の docstring**：入った（高）。左辺の UA1 は pullL の値域なので法 M、右辺の TopL は法 q（文の N）です。
6. **定値性**：入った（高）。docstring・冒頭・ノート 21 行・表の 4 か所に入っています。115 行の「正定値」は 2 つの文を並べた言い方なので、問題ありません。
7. **35 行**：入った（高）。
8. **「Lean にしていないこと」**：一部入った（中）。
   - 冒頭と 31 行には入りました。
   - §1 には 114 行のラベル以外の変更がなく、§8 にも扱いの記録がありません。§1 の全文は入力にないので、確信度は中です。
   - §8「直していないもの」に「U_∞ が各部分を保つこと」が抜けています（低）。
9. **小さいもの**：6 件とも入った（高）。
   - ただし 209 行（B への対応の記録）に「実質的な内容が族の一意性であることを明記した」が残っています。今の 19・31 行の言い方と合いません（低）。

### 2. 新しい文面の問題と直し方

- **80 行**（高）：§1 に合わせて次のように書き分けます。
  - 既知：内積、像の直交、U_∞ の存在と一意（普遍性）、全単射、内積の保存
  - 再導出：原始部分の像の上で T_q であること、その性質での一意
  - あわせて 114 行の「張る」にもラベルを付けます。
- **§8 の A2 の要約**（中）
  - 問題：「`condPart_eq_map` が中身のある文で、ほかは自明か標準の短い帰結」とあります。一方 B2 は、A2 が S57（`ipLim_ofL_Vprim`）を「実質的（標準）」としたと伝えています。
  - 直し方：A2 の出力を確かめ、必要なら「`condPart_eq_map` と `ipLim_ofL_Vprim`」とします。
- **題**（中）：「導手ごとの部分（q ∣ M では π(V_prim(q))。添字は ℕ 全体で、q ∤ M の部分が 0 であることは文にしていない）は…」とします。
- **冒頭 3**（中）：「直和の部品は 10（1 つの定理にはしていない）」とします。
- **軽微なもの**（低）
  - 31 行に足した 2 項目にラベルがありません。どちらも既存の文から数行で出るので、［推論］を付けます。
    - 極限での独立性：直交と定値性から出ます。
    - U_∞ が各部分を保つこと：`Uinf_ofL_of_mem_Vprim`・`UA1_eq_TopL_of_mem_Vprim`・`UA1_mem_Vprim` から出ます。
  - 冒頭 10 の「前ヒルベルト空間」は、ipLim の 5 文（右で線形・エルミート・正値・定値性）から数学として正しいです。ノート 21 行と同じく「Mathlib の構造にはしていない」を添えると、言い方がそろいます。
- 上のほかに、偽の文、形式文より強い言い方、計算や参照の誤りは見つかりませんでした（高）。§8 の件数（定理 7・定義 2・冒頭 4 か所・docstring 5 個・ノートの行番号）は差分と一致します。

### 3. 全体の判定（1 行）

B2 の 9 項目はおおむね入りましたが、ずれが残っています。重要な順に次のとおりです。
1. 80 行の新しいラベルが §1 の 113・115 行と食い違う
2. §8 の A2 要約が S57 の扱いと合わない可能性がある
3. Lean の冒頭 3 に「直和そのものは 10」が残っている
4. 題に q ∤ M の但し書きがない
5. §1 への追記がなく、その扱いの記録もない
6. 軽微なもの（31 行のラベル、209 行の言い方、114 行の「張る」のラベル）

Read の回数：2 回（どちらも入力ファイル。2 回目は offset 442 からの続き）

### Part 254 の入力 (4)：第 2 回の直しの差分（Lean の文面とノート。形式文は変えていない）
```diff
--- PAG258.lean（第 1 回の直しの後）
+++ PAG258.lean（第 2 回の直しの後）
@@ -23,3 +23,3 @@
 3. 指標ごとの式（残る問い 1）：すべての χ で U_N χ = π_{q→N}(T_q χ*)（`UA1_charU_eq_pull_TopL`。位相の定義の
-   言い換え）。U_N はこの性質で一意に決まる（`UA1_unique`。基底の上の値による）。直和そのものは 10。
+   言い換え）。U_N はこの性質で一意に決まる（`UA1_unique`。基底の上の値による）。直和の部品は 10（1 つの定理にはしていない）。
 4. 組み立て（残る問い 2）：法を上げる引き戻しと両立する：U_M ∘ π = π ∘ U_N（`UA1_comp_pullL`）。
@@ -52,3 +52,3 @@
    原始部分の引き戻しの上で π∘T_q（`UA1_pullL_of_mem_Vprim`：q ∣ M、g ∈ V_prim(q) なら U_M(π g) = π(T_q g)）。
-   極限では、導手の違う原始部分の像は直交する（`ipLim_ofL_Vprim`。前ヒルベルト空間での直交。極限での独立性と、
+   極限では、導手の違う原始部分の像は直交する（`ipLim_ofL_Vprim`。前ヒルベルト空間での直交。Mathlib の内積の構造にはしていない。極限での独立性と、
    U_∞ が各部分を保つことは文にしていない）。

--- pag2_part254_full_gluing.md（第 1 回の直しの後）
+++ pag2_part254_full_gluing.md（第 2 回の直しの後）
@@ -1,2 +1,2 @@
-# アーデル射影幾何 — Part 254（PAG 2.0）：法 N の境界ユニタリ U_N 全体と、代数的な帰納極限の上の U_∞ — 単数の上の関数の空間で、導手ごとの部分 π(V_prim(q)) は互いに直交し、独立で、全体を張る（合わせると直交直和。1 つの定理にはしていない）。U_N はその上で T_q を引き戻したもの。原始部分で T と一致し引き戻しと両立する族は U_N だけで、代数的な帰納極限の上の、正規化した内積を保つ 1 つの全単射 U_∞ にまとまる（Part 252 の残る問い。完備化 L²(Ẑ^×) は Lean の外）
+# アーデル射影幾何 — Part 254（PAG 2.0）：法 N の境界ユニタリ U_N 全体と、代数的な帰納極限の上の U_∞ — 単数の上の関数の空間で、導手ごとの部分（q ∣ M では π(V_prim(q))。添字は ℕ 全体で、q ∤ M の部分が 0 であることは文にしていない）は互いに直交し、独立で、全体を張る（合わせると直交直和。1 つの定理にはしていない）。U_N はその上で T_q を引き戻したもの。原始部分で T と一致し引き戻しと両立する族は U_N だけで、代数的な帰納極限の上の、正規化した内積を保つ 1 つの全単射 U_∞ にまとまる（Part 252 の残る問い。完備化 L²(Ẑ^×) は Lean の外）
 
@@ -30,3 +30,3 @@
   - 残る問い (1)：直和の部品の文を Lean で示しました（`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart` と `UA1_pullL_of_mem_Vprim`。直和を 1 つの文にすること、q ∤ M の部分が 0 であることは文にしていない）。ただし中身は、指標を導手で分けることと、各レベルでの Part 253 の結果の組み合わせです。U_N の明示の核（導手とメビウスの式）は数値だけです（step277 の (8)、60/60）。
-  - 残る問い (2)：代数的な帰納極限の上の作用素 U_∞ と、その上の内積を Lean で作り、U_∞ が内積を保つ全単射であることを示しました。定義の言い換えでない内容は族の一意性（`UA1_family_unique`。短い組み合わせ）です。Lean にしていないのは次の 2 つです。どちらも標準の事実です［既知、確信度：高］。ほかに、極限での独立性と、U_∞ が導手ごとの各部分を保つことも Lean にしていません。
+  - 残る問い (2)：代数的な帰納極限の上の作用素 U_∞ と、その上の内積を Lean で作り、U_∞ が内積を保つ全単射であることを示しました。定義の言い換えでない内容は族の一意性（`UA1_family_unique`。短い組み合わせ）です。Lean にしていないのは次の 2 つです。どちらも標準の事実です［既知、確信度：高］。ほかに、極限での独立性（直交と定値性から出る［推論］）と、U_∞ が導手ごとの各部分を保つこと（`Uinf_ofL_of_mem_Vprim`・`UA1_eq_TopL_of_mem_Vprim`・`UA1_mem_Vprim` から出る［推論］）も Lean にしていません。
     - 帰納極限 `Lim` を Ẑ^× = lim (ℤ/N)^× の上の局所定数関数の空間と同一視すること。
@@ -79,3 +79,3 @@
 | 引き戻しとの両立（T は両立しない）と、両立する族の一意性 | 両立と一意性は再導出、T の非両立は既知 | 位相が誘導元から決まること |
-| 帰納極限の上の U_∞ と内積、原始部分の像の直交 | 内積と直交は既知、U_∞ の性質は再導出 | 帰納極限の普遍性、ファイバーの元の数が一定 |
+| 帰納極限の上の U_∞ と内積、原始部分の像の直交 | 内積・像の直交・U_∞ の存在と一意・全単射・内積の保存は既知。原始部分の像の上で T_q であることと、その性質での一意は再導出 | 帰納極限の普遍性、ファイバーの元の数が一定 |
 | 原始的でない部分で U ≠ T（素数の法） | 既知 | 主指標のガウス和 −1（ラマヌジャン和 c_p(1) = μ(p)） |
@@ -113,3 +113,3 @@
 | 極限への写像は単射、U_∞ は各法で U_N、一意、全単射 | `ofL_injective`・`Uinf_ofL`・`Uinf_unique`・`Uinf_bijective` | — | 既知 |
-| 原始部分の像は極限を張り、導手の違う像は直交し、U_∞ はその上で T_q、この性質で一意 | `ofL_charU`・`span_ofL_Vprim`・`ipLim_ofL_Vprim`・`Uinf_ofL_of_mem_Vprim`・`Uinf_unique_TopL` | — | 直交は既知、U_∞ の性質は再導出 |
+| 原始部分の像は極限を張り、導手の違う像は直交し、U_∞ はその上で T_q、この性質で一意 | `ofL_charU`・`span_ofL_Vprim`・`ipLim_ofL_Vprim`・`Uinf_ofL_of_mem_Vprim`・`Uinf_unique_TopL` | — | 張ること・直交は既知、T_q であることとその性質での一意は再導出 |
 | 極限の内積：正規化、代表によらない、右で線形、エルミート、正定値、U_∞ が保つ | `totient_ne_zero'`・`ipn_pullSys`・`ipn_eq_of_ofL_eq`・`ipLim_ofL`・`ipLim_add_right`・`ipLim_smul_right`・`ipLim_conj`・`ipLim_self_nonneg`・`eq_zero_of_ipLim_self`・`ipLim_Uinf` | — | 既知 |
@@ -208,3 +208,3 @@
     1. 極分解の文は一般には偽（法 1・6 で U_N は T_N の極分解のユニタリ因子そのもの）。→ 素数の法に限って直し、反例を本文に書いた。数値 (20) で確認：T_N が可逆な N ≤ 60 では、一致するのは N = 1・6 だけ。
-    2. 「直和の文」「(1) を解決」は、指標ごとの式（定義の言い換え）と基底による一意性だけで、直和分解は Lean にない。→ 有限レベルの直和の部品を Lean にした（直和を 1 つの文にはしていない。`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart`・`UA1_mem_condPart`・`UA1_pullL_of_mem_Vprim`、極限で `ipLim_ofL_Vprim`）。指標ごとの式は「定義の言い換え」と書き直し、実質的な内容が族の一意性であることを明記した。数値 (21) で確認。
+    2. 「直和の文」「(1) を解決」は、指標ごとの式（定義の言い換え）と基底による一意性だけで、直和分解は Lean にない。→ 有限レベルの直和の部品を Lean にした（直和を 1 つの文にはしていない。`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart`・`UA1_mem_condPart`・`UA1_pullL_of_mem_Vprim`、極限で `ipLim_ofL_Vprim`）。指標ごとの式は「定義の言い換え」と書き直し、定義の言い換えでない内容が族の一意性（短い組み合わせ）であることを明記した。数値 (21) で確認。
     3. 「T は両立しない」「原始的でない部分で U ≠ T」を一般の形で書いていた。→ Lean の範囲（法 1 → p、素数の法）に合わせ、一般の場合は Lean の外と書いた。N = 1 では V_imprim = 0。
@@ -220,6 +220,6 @@
 - **手順。** 新しいエージェント A2（逆翻訳。中立化した名前で判定）と B2（照合。形式文と定義の全文、Lean の docstring の全文、ノートの全文、表の全行、A2 の出力の全文を渡した）。照合者は入力ファイルを Read で読む形（A2 は 1 回、B2 は 4 回。1 回はサイズ上限のエラーで、範囲を分けて読み直した。どれも入力ファイルだけ）。記録は `pag2_reaudit_252_256.md` と `reaudit257/`。
-- **A2。** 7 文とも真。`condPart_eq_map` が中身のある文（標準）で、ほかは自明か標準の短い帰結。`ipR` は文に出てこない（証明の補助）。`ipLim_ofL_Vprim` は前ヒルベルト空間での直交で、L²(Ẑ^×) の文ではない。極限での独立性と、U_∞ が各部分を保つことは文にない。
+- **A2。** 7 文とも真。`condPart_eq_map`・`iSupIndep_condPart`・`ipLim_ofL_Vprim` は実質的（標準。`iSupIndep_condPart` は自明との境目）、ほかの 4 文は自明。`ipR` は文に出てこない（証明の補助）。`ipLim_ofL_Vprim` は前ヒルベルト空間での直交で、L²(Ẑ^×) の文ではない。極限での独立性と、U_∞ が各部分を保つことは文にない。
 - **B2。** 形式文 57 個に偽・空虚・別物はない。ずれは「直和の文を Lean で示した」の言い方（添字は ℕ 全体で、⊕_{q∣M} を 1 つにまとめた文はない）、ラベルの食い違い（79 行と 104 行、80 行と 114 行）、75 行の ε、Lean の docstring の参照誤り（「直和そのものは §8」）と法の書き違い（`UA1_pullL_of_mem_Vprim` の「U_N」は U_M）、冒頭の説明 5 の書き方など。
 - **直したもの。** Lean の冒頭の説明 4 か所と docstring 5 個（形式文は変えていない。組み立て直して確認）。ノートの上の行（題、7・10・14・19・21・30・31・35・75・79・80・114・206・209 行）と、表の見出しと 4 行（`TopL_not_compat`・`UA1_star`・`eq_zero_of_ipLim_self`・`iSupIndep_condPart`）。
-- **直していないもの。** 直和を 1 つの文（DirectSum.IsInternal）にすること、q ∤ M の部分が 0 であることの文、極限での独立性（Lean の文を足すと、また照合されていない文が増えるため、文面を形式文に合わせる方で直した）。
+- **直していないもの。** 直和を 1 つの文（DirectSum.IsInternal）にすること、q ∤ M の部分が 0 であることの文、§1 の検証表への「Lean にしていないこと」の追記（31 行と Lean の冒頭の説明に書いた）、U_∞ が各部分を保つこと、極限での独立性（Lean の文を足すと、また照合されていない文が増えるため、文面を形式文に合わせる方で直した）。
 - **第 3 の型の検知。** 「直和の文を Lean で示した」は、部品の文を合わせた読みを、1 つの定理があるかのように書いていた。B の後の直しが Lean の docstring に入っていなかった。
```


## Part 255

### Part 255 の入力 (1)：定義の全文（このファイルと前のファイル。原文のまま。コメントと docstring だけ除いた）
```lean
-- PAG254.lean（文脈：namespace PAG.Part254）

def logSet : Set ℝ := {x | ∃ q : ℚ, 0 < q ∧ x = Real.log q}

-- PAG259.lean（文脈：namespace PAG.Part259）

def imgST (S T : Finset ℕ) : Set (ℝ × (T → ℤ)) :=
  {z | ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) ∧
    z = (Real.log q, fun t : T => padicValRat (t : ℕ) q)}

noncomputable def rho (q : ℚ) : ℝ × (Nat.Primes → ℤ) := (Real.log q, fun p => padicValRat p q)

def BoxCoord : Type := Nat.Primes → ℤ

instance : TopologicalSpace BoxCoord := ⊥

instance : DiscreteTopology BoxCoord := ⟨rfl⟩

noncomputable def rhoBox (q : ℚ) : ℝ × BoxCoord := (Real.log q, fun p => padicValRat p q)
```

### Part 255 の入力 (2)：形式文の全文（PAG259.lean の定理 45 個すべて。原文のまま、証明だけ除いた。すべてコンパイル済みで sorry なし、公理は標準の範囲）
```lean
theorem padicValRat_prime_ne {s p : ℕ} (hs : s.Prime) (hp : p.Prime) (hne : s ≠ p) :
    padicValRat s (p : ℚ) = 0
theorem padicValRat_prime_zpow {s p : ℕ} (hs : s.Prime) (hp : p.Prime) (k : ℤ) :
    padicValRat s ((p : ℚ) ^ k) = if s = p then k else 0
theorem padicValRat_prod_zpow (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (k : ℕ → ℤ) {t : ℕ}
    (ht : t.Prime) :
    padicValRat t (∏ s ∈ S, (s : ℚ) ^ (k s)) = if t ∈ S then k t else 0
theorem eq_of_padicValRat_eq {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (h : ∀ p : ℕ, p.Prime → padicValRat p q = padicValRat p r) : q = r
theorem eq_one_of_padicValRat_eq_zero {q : ℚ} (hq : 0 < q)
    (h : ∀ p : ℕ, p.Prime → padicValRat p q = 0) : q = 1
theorem one_le_abs_intCast_sub {a b : ℤ} (hne : a ≠ b) : (1 : ℝ) ≤ |((a - b : ℤ) : ℝ)|
theorem exists_prime_one_le_abs {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (hne : q ≠ r) :
    ∃ p : ℕ, p.Prime ∧ (1 : ℝ) ≤ |((padicValRat p q - padicValRat p r : ℤ) : ℝ)|
theorem eq_prod_of_support (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) {q : ℚ} (hq : 0 < q)
    (hsupp : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) :
    q = ∏ s ∈ S, (s : ℚ) ^ (padicValRat s q)
theorem log_eq_sum_of_support (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) {q : ℚ} (hq : 0 < q)
    (hsupp : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) :
    Real.log q = ∑ s ∈ S, (padicValRat s q : ℝ) * Real.log s
theorem exists_padicValRat_eq (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (k : ℕ → ℤ) :
    ∃ q : ℚ, 0 < q ∧ (∀ s ∈ S, padicValRat s q = k s) ∧
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
theorem closure_logSet : closure PAG.Part254.logSet = Set.univ
theorem dense_closure_log_primes {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) :
    Dense ((AddSubgroup.closure ({Real.log p, Real.log r} : Set ℝ) : AddSubgroup ℝ) : Set ℝ)
theorem exists_zpow_near {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ a b : ℤ, |(a : ℝ) * Real.log p + (b : ℝ) * Real.log r - x| < ε
theorem irrational_log_div_log {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) :
    Irrational (Real.log r / Real.log p)
theorem padicValRat_mul_zpow_zpow {p r t : ℕ} (hp : p.Prime) (hr : r.Prime) (ht : t.Prime)
    {q₀ : ℚ} (hq₀ : q₀ ≠ 0) (a b : ℤ) :
    padicValRat t (q₀ * (p : ℚ) ^ a * (r : ℚ) ^ b) =
      padicValRat t q₀ + (if t = p then a else 0) + (if t = r then b else 0)
theorem log_mul_zpow_zpow {p r : ℕ} (hp : p.Prime) (hr : r.Prime) {q₀ : ℚ} (hq₀ : 0 < q₀)
    (a b : ℤ) :
    Real.log ((q₀ * (p : ℚ) ^ a * (r : ℚ) ^ b : ℚ) : ℝ) =
      Real.log q₀ + (a : ℝ) * Real.log p + (b : ℝ) * Real.log r
theorem exists_near_of_two_unmeasured {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r)
    {q₀ : ℚ} (hq₀ : 0 < q₀) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ≠ p → t ≠ r → padicValRat t q = padicValRat t q₀) ∧
      |Real.log q - x| < ε
theorem exists_near_measured {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r)
    (M : Finset ℕ) (hpM : p ∉ M) (hrM : r ∉ M) {q₀ : ℚ} (hq₀ : 0 < q₀) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ s ∈ M, s.Prime → padicValRat s q = padicValRat s q₀) ∧
      |Real.log q - x| < ε
theorem eq_mul_zpow_of_agree {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q) (hq' : 0 < q')
    (h : ∀ t : ℕ, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q * (p : ℚ) ^ (padicValRat p q' - padicValRat p q)
theorem log_sep_of_agree {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q) (hq' : 0 < q')
    (h : ∀ t : ℕ, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q ∨ Real.log p ≤ |Real.log q' - Real.log q|
theorem exists_mem_one_le_abs_of_support (S : Finset ℕ) {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (hqS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
    (hrS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t r = 0) (hne : q ≠ r) :
    ∃ p ∈ S, p.Prime ∧ (1 : ℝ) ≤ |((padicValRat p q - padicValRat p r : ℤ) : ℝ)|
theorem sep_of_inf_unmeasured (M : Finset ℕ) {q r : ℚ}
    (hne : ∃ s ∈ M, padicValRat s q ≠ padicValRat s r) :
    ∃ s ∈ M, (1 : ℝ) ≤ |((padicValRat s q - padicValRat s r : ℤ) : ℝ)|
theorem log_sep_one_unmeasured (S : Finset ℕ) {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q)
    (hq' : 0 < q') (hqS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
    (hq'S : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q' = 0)
    (h : ∀ t ∈ S, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q ∨ Real.log p ≤ |Real.log q' - Real.log q|
theorem exists_near_in_subgroup (S : Finset ℕ) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hne : p ≠ r) (hpS : p ∈ S) (hrS : r ∈ S) (T : Finset ℕ) (hpT : p ∉ T) (hrT : r ∉ T)
    {q₀ : ℚ} (hq₀ : 0 < q₀) (hq₀S : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q₀ = 0) (x : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) ∧
      (∀ s ∈ T, s.Prime → padicValRat s q = padicValRat s q₀) ∧ |Real.log q - x| < ε
theorem fiber_sep (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime)
    (h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r) :
    ∃ c : ℝ, 0 < c ∧ ∀ q q' : ℚ, 0 < q → 0 < q' →
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) →
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q' = 0) →
      (∀ t ∈ T, padicValRat t q' = padicValRat t q) →
      q' = q ∨ c ≤ |Real.log q' - Real.log q|
theorem threshold_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    (∃ k : T → ℤ, ∀ x : ℝ, (x, k) ∈ closure (imgST S T)) ↔
      ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T
-- ★ 
theorem isClosed_and_discrete_of_subsingleton {X : Type*} [TopologicalSpace X] [T1Space X]
    {A : Set X} (h : ∀ z : X, ∃ U ∈ nhds z, (U ∩ A).Subsingleton) :
    IsClosed A ∧ DiscreteTopology A
-- ★ 
theorem dense_imgST_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    Dense (imgST S T) ↔ ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T
-- ★ 
theorem isClosed_discrete_imgST (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime)
    (h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r) :
    IsClosed (imgST S T) ∧ DiscreteTopology (imgST S T)
theorem rho_one : rho 1 = (0, 0)
theorem exists_two_primes_not_mem (I : Set Nat.Primes) (hI : I.Finite) :
    ∃ p r : Nat.Primes, p ∉ I ∧ r ∉ I ∧ (p : ℕ) ≠ (r : ℕ)
theorem val_ne_of_mem_of_not_mem {I : Set Nat.Primes} {i p : Nat.Primes} (hi : i ∈ I)
    (hp : p ∉ I) : (i : ℕ) ≠ p
theorem dense_rho_image : Dense (rho '' {q : ℚ | 0 < q})
theorem mem_closure_line_prod (x : ℝ) :
    (x, (0 : Nat.Primes → ℤ)) ∈ closure (rho '' {q : ℚ | 0 < q})
theorem closure_rho_not_image :
    ((1 : ℝ), (0 : Nat.Primes → ℤ)) ∈ closure (rho '' {q : ℚ | 0 < q}) ∧
      ((1 : ℝ), (0 : Nat.Primes → ℤ)) ∉ rho '' {q : ℚ | 0 < q}
theorem rho_one_mem_closure_ne_one :
    rho 1 ∈ closure (rho '' {q : ℚ | 0 < q ∧ q ≠ 1})
theorem rho_sep {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (hne : q ≠ r) :
    ∃ p : Nat.Primes, (1 : ℝ) ≤ |(((rho q).2 p - (rho r).2 p : ℤ) : ℝ)|
-- ★ 
theorem isClosed_discrete_rhoBox_image :
    IsClosed (rhoBox '' {q : ℚ | 0 < q}) ∧ DiscreteTopology (rhoBox '' {q : ℚ | 0 < q})
theorem finite_support_padicValRat {q : ℚ} (hq : 0 < q) :
    {p : ℕ | p.Prime ∧ padicValRat p q ≠ 0}.Finite
theorem eq_prod_support {q : ℚ} (hq : 0 < q) :
    q = ∏ s ∈ (finite_support_padicValRat hq).toFinset, (s : ℚ) ^ (padicValRat s q)
theorem sep_of_mem_zmultiples {c x y : ℝ} (hc : 0 < c) (hx : ∃ m : ℤ, x = m * c)
    (hy : ∃ n : ℤ, y = n * c) (hne : x ≠ y) : c ≤ |x - y|
theorem mem_zmultiples_of_commensurable {L₁ L₂ : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) * L₂ = m * L₁) (a b : ℤ) :
    (a : ℝ) * L₁ + b * L₂ = ((a * n + b * m : ℤ) : ℝ) * (L₁ / n)
theorem sep_of_commensurable {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) * L₂ = m * L₁) (a b a' b' : ℤ)
    (hne : (a : ℝ) * L₁ + b * L₂ ≠ a' * L₁ + b' * L₂) :
    L₁ / n ≤ |((a : ℝ) * L₁ + b * L₂) - (a' * L₁ + b' * L₂)|
theorem zpow_ge_of_one_lt {p : ℕ} (hp : p.Prime) {k : ℤ} (hk : 1 < (p : ℝ) ^ k) :
    (p : ℝ) ≤ (p : ℝ) ^ k
theorem exists_between_one {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) {y : ℝ}
    (hy : 1 < y) :
    ∃ a b : ℤ, 1 < (p : ℝ) ^ a * (r : ℝ) ^ b ∧ (p : ℝ) ^ a * (r : ℝ) ^ b < y
```


### Part 255 の入力 (3)：B3 の出力の全文（原文のまま）

# 照合結果：PAG259.lean（Part 255）の直し

## 1. B2 の「直すべき点」12 項目

1. exists_near_in_subgroup：入った（高）。B2 の案どおりです。反例 S = {2, 3}、T = {5} も正しいです（5 の座標は恒等的に 0）。ただし「T ⊆ S なら」に素数の条件がありません（2 (a)）。
2. exists_near_measured：入った（高）。M の素数の座標を保ったまま ε 近似する、という形式文と一致します。
3. 「読み」の印：入った（高）。closure_logSet の docstring と表、threshold_iff の表、mem_closure_line_prod、ノート 17・65 行に入りました。17 行の「と読み（読み）」は重複ですが、体裁だけの問題です。
4. T ⊆ S：入った（高）。dense_imgST_iff の docstring と、ノートの題・31・87・106 行に入りました。「右辺は真で左辺は偽」も正しいです（像は閉集合 ℝ × {0} に入る）。
5. 133・190 行：入った（高）。挙げた 5 つの docstring は B2 の 3 節と合います。
6. 15 行：入った（高）。ℤ^T が離散なので、余極限の位相も離散です。37 行との食い違いは消えました。
7. 守備範囲：入った（高）。ノート 33 行と冒頭の説明の両方に入りました。
8. S45 と 46・66 行：入った（高）。
9. 間隔の言い方：入った（高）。冒頭の説明、ノート 31 行、表の fiber_sep に入りました。
10. 138 行：入った（高）。「すべての素点」を「有限素点」にしたのは、B2 の案より正確です。
11. Lean にしていないこと：入った（中）。Lean の冒頭の説明に 4 点と格子の分割が入り、ノート 107 行も分割されました。ただしノート 38 行の「Lean の外」は元のままです。4 点のうち「積公式を満たす点の集合と像の一致」はノートにありません（ほかの 3 点はノート 31・33・36・138 行に入っています）。
12. 細部：入った（高）。ただし 39 行の新しい文面に小さな問題があります（2 (d)）。

**直していない項目**
- 12 項目の中にはありません。
- §9 の「直していないもの」（余分な仮定 hS、二分法を 1 つの文にすること）は、B2 が直す点に挙げなかったものです。扱いはノートに書かれています（高）。
- B2 が一覧の外で書いた注記は、扱いがどこにも書かれていません（低）。対象は次の 3 つです。
  - Ξ3：コードのコメント「S42〜S45 で使う」
  - S44：「T ⊄ S のときの逆は述べていない」
  - 表の exists_prime_one_le_abs・isClosed_discrete_rhoBox_image の行の但し書き

## 2. 新しい文面の問題

- **(a) exists_near_in_subgroup の docstring**（確信度 高、重要度 中〜低）
  - 問題：「T ⊆ S なら…閉包は ℝ × ℤ^T 全体」に、S が素数という条件がありません。imgST の定義は S, T に素数を課しません（新しい imgST の docstring もそう書いています）。
  - 反例：S = {2, 3, 4}、T = {4}、p = 2、r = 3 は、定理の仮定も T ⊆ S も満たします。しかし v_4 を固定すると 2 の指数は 2〜3 通りに限られ、閉包は水平な直線を含みません。
  - 「exists_padicValRat_eq と合わせて」がその仮定 hS を前提にしている、と読めば正しい文です。
  - 直し方の案：「S が素数の有限集合で T ⊆ S なら」と書き、dense_imgST_iff の docstring と揃えます。B2 の案にも同じ抜けがありました。
- **(b) ノート 36 行「再照合 A2 は『自明（ほぼ同語反復）』と判定」**（中）
  - B2 が引いた A2 の言葉は「自明（log を使わない）」です。§9 の要約は「位相の選び方でほぼ決まる自明な文」です。引用符の中が、どちらの記録とも合いません。
  - 直し方の案：A2 の原文（この入力にはない）に合わせるか、引用符を外します。
- **(c) 「離散の部分は isClosed_discrete_imgST（T = S ∖ {p}）」（冒頭の説明、ノート 107 行）**（中）
  - これが当てはまるのは、有限素点 p を落とす場合だけです。∞ を落とす場合は imgST の外で、対応するのは分離の文 exists_mem_one_le_abs_of_support です。
  - 直し方の案：「有限素点を落とす場合の離散の部分」と範囲を限ります。
- **(d) ノート 39 行「通約的な 2 つの実数の対数」**（低）
  - 形式文は、任意の実数 L₁, L₂（n·L₂ = m·L₁、n > 0）についての文です。「の対数」は形式文にありません。
  - 直し方の案：「通約的な 2 つの実数 L₁, L₂（対数と読む）」にします。
- **(e) ノート 158 行**（低）
  - 「兆候 1・2：出ていない」の根拠が、「C が名前を付けた」から「C の後に足した定義で、C は名前を知らない」に変わりました。それなのに結論はそのままです。
  - 兆候の定義がこの入力にないので、結論の当否は判定できません。結論を保つ理由を一言足すのがよいです。
- **(f) ノート 31 行「S ⊆ T なら点は 1 つ」**（低）
  - 「各ファイバーの点は高々 1 つ」と書くほうが正確です。
  - 「c = log p」は証明の中身で、この入力では確かめられません。
- **(g) ノート 138 行**（低）
  - 「⟨S⟩ の二分法」を「⟨S⟩ の二分法の 2 つの文」にすると、「1 つの文にした定理はない」と食い違いません。
- **(h) 未確認**（低）
  - 冒頭の説明の threshold_iff の行（今回変更なし）に、T ⊆ S が見えません。23 行より前で仮定していなければ足してください。
  - threshold_iff も T ⊆ S を要ります。S = {2, 3}、T = {4, 9} では、右辺は真で左辺は偽になります。

**計算と参照**：次の点は差分と合います（高）。
- 2 つの反例
- 「Part 250 の dense_logSet」
- §9 の「冒頭の説明 6 か所・docstring 9 個」
- 直したノートの行の一覧
- 表の 3 行

## 3. 全体の判定

B2 の 12 項目はすべて入り、新しく偽の文は入っていません。残るずれは小さく、重要な順に (a) exists_near_in_subgroup の括弧に素数の条件がない、(b) ノートの A2 の引用が記録と合わない、(c) 格子の離散の部分の参照の範囲、あとは言い回しです（d〜h）。

Read の回数：2 回（同じ入力ファイル。1 回目が途中で切れたため、offset を指定して続きを読みました）

### Part 255 の入力 (4)：第 2 回の直しの差分（Lean の文面とノート。形式文は変えていない）
```diff
--- PAG259.lean（第 1 回の直しの後）
+++ PAG259.lean（第 2 回の直しの後）
@@ -21,3 +21,3 @@
    無理数（`irrational_log_div_log`）。
-3. 有限の基礎 ⟨S⟩ での閾値（T ⊆ S、∞ と T の素数を測る。像 `imgST S T` ⊆ ℝ × ℤ^T）：
+3. 有限の基礎 ⟨S⟩ での閾値（S は素数の有限集合、T ⊆ S、∞ と T の素数を測る。像 `imgST S T` ⊆ ℝ × ℤ^T）：
    - 閉包がある水平な直線 ℝ × {k} 全体を含む ⇔ T の外に S の異なる素数が 2 つある（`threshold_iff`）。
@@ -59,3 +59,4 @@
 1 つの文にすること（2 つの場合の排他性）。S ∪ {∞} から 1 つ落としたときの余コンパクト性（格子であること。S 単数定理の
-形。数値 step278 の (9)。離散の部分は `isClosed_discrete_imgST` で T = S ∖ {p} として Lean にある）。⟨S⟩ の大きさの
+形。数値 step278 の (9)。有限素点 p を落とす場合の離散の部分は `isClosed_discrete_imgST` で T = S ∖ {p} として Lean に
+ある。∞ を落とす場合の分離は `exists_mem_one_le_abs_of_support`）。⟨S⟩ の大きさの
 順序の Dedekind 完備化が ℝ であること。F_q(t) そのもの（付値と積公式。数値 (15)）。測らない生成元が無限個の一般化素数の
@@ -432,4 +433,4 @@
 /-- ⟨S⟩ で S の素数 p ≠ r を測らないとき：⟨S⟩ の中にとどまり、T の素数の座標を q₀ と同じに保ったまま、log を任意の x に
-ε 近づけられる（閉包の文は `threshold_iff`・`dense_imgST_iff`。T ⊆ S なら、`exists_padicValRat_eq` と合わせて閉包は
-ℝ × ℤ^T 全体。T ⊆ S がないと閉包の文は偽になりうる：S = {2, 3}、T = {5}）。 -/
+ε 近づけられる（閉包の文は `threshold_iff`・`dense_imgST_iff`。S が素数の有限集合で T ⊆ S なら、`exists_padicValRat_eq` と合わせて
+閉包は ℝ × ℤ^T 全体。T ⊆ S がないと閉包の文は偽になりうる：S = {2, 3}、T = {5}）。 -/
 theorem exists_near_in_subgroup (S : Finset ℕ) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)

--- pag2_part255_resolution_discrete_limit.md（第 1 回の直しの後）
+++ pag2_part255_resolution_discrete_limit.md（第 2 回の直しの後）
@@ -16,3 +16,3 @@
 - **着手前の文書からの直し（08:41 の定義を受けて）。**
-  - 着手前の文書は、L1 の「有効な姿」を「像の閉包」と書き、閉包に直線が現れることを中心に置いていました。数学は同じですが、向きを直しました。閉包に現れる連続体は解像度が落ちた印と読み（読み）、中心は「どこまで離散が保たれるか」です。
+  - 着手前の文書は、L1 の「有効な姿」を「像の閉包」と書き、閉包に直線が現れることを中心に置いていました。数学は同じですが、向きを直しました。閉包に現れる連続体は解像度が落ちた印と読み、中心は「どこまで離散が保たれるか」です。
   - **取り下げ 1。** 着手前の文書 §4 は「完備化（尺度 ε → 0）は解像度を上げる向き」として、完備化を候補から外しました。この理由を取り下げます。著者の定義では、完備化は解像度が落ちる側の操作です。L1 の閉包が、その完備化にあたると読みます。
@@ -30,3 +30,3 @@
     - 閉包がある水平な直線 ℝ × {k} 全体を含む ⇔ T の外に S の異なる素数が 2 つある（`threshold_iff`。独立照合 A の指摘で足した）。
-    - 二分法（独立照合 B の指摘で足した）：その条件のもとで像は稠密です（`dense_imgST_iff`。S は素数の有限集合、T ⊆ S。T ⊆ S は必要：S = {2, 3}、T = {5} では右辺は真で左辺は偽）。条件が成り立たない（測らない素数が高々 1 つ）なら、像は閉かつ離散です（`isClosed_discrete_imgST`）。後者は、T の座標が同じ 2 点が、等しいか、q, q' によらない c > 0 以上離れること（`fiber_sep`。証明では S ∖ T = {p} なら c = log p、S ⊆ T なら点は 1 つ）から出ます。後者には T ⊆ S は要りません。二分法を 1 つの文にした定理はありません（2 つの場合が排他的であることは文にしていない）。
+    - 二分法（独立照合 B の指摘で足した）：その条件のもとで像は稠密です（`dense_imgST_iff`。S は素数の有限集合、T ⊆ S。T ⊆ S は必要：S = {2, 3}、T = {5} では右辺は真で左辺は偽）。条件が成り立たない（測らない素数が高々 1 つ）なら、像は閉かつ離散です（`isClosed_discrete_imgST`）。後者は、T の座標が同じ 2 点が、等しいか、q, q' によらない c > 0 以上離れること（`fiber_sep`。証明では S ∖ T = {p} なら c = log p、S ⊆ T なら各ファイバーの点は高々 1 つ）から出ます。後者には T ⊆ S は要りません。二分法を 1 つの文にした定理はありません（2 つの場合が排他的であることは文にしていない）。
     - 部品：測らない素数 p ≠ r があれば、座標を保ったまま log を任意の x に ε 近づけられる。保つ座標は、`exists_near_of_two_unmeasured` では p, r 以外のすべての素数、`exists_near_measured` では M の素数、`exists_near_in_subgroup` では T の素数（⟨S⟩ の中にとどまる）。p 以外の付値が一致する 2 元は q' = q·p^k で、等しいか log p 以上離れる（`eq_mul_zpow_of_agree`・`log_sep_of_agree`・`log_sep_one_unmeasured`）。S の素数をすべて測れば、異なる元は S のある素数の座標で 1 以上離れる（`exists_mem_one_le_abs_of_support`）。∞ を測らなければ整数の座標で離散（`sep_of_inf_unmeasured`。ほぼ同語反復）。
@@ -35,6 +35,6 @@
     - **直積の位相**（`Nat.Primes → ℤ` の既定の位相。各近傍は有限個の素点しか測らない）：像は稠密です（`dense_rho_image`）。ℝ × {0} の直線全体が閉包に入り（`mem_closure_line_prod`）、ρ(1) は孤立点ではなく（`rho_one_mem_closure_ne_one`）、閉包の点 (1, 0) は像にありません（`closure_rho_not_image`。(1, 0) は積公式の形 x = Σ k_p log p を満たさない点。独立照合 A の指摘）。
-    - **すべての素点を同時に測る位相**（読み。`BoxCoord`：`Nat.Primes → ℤ` に離散位相。写像 `rhoBox` は ρ と同じ。ℤ 値の座標では離散位相が箱・一様の位相と同じことは Lean の外の標準の事実）：像は閉かつ離散です（`isClosed_discrete_rhoBox_image`。独立照合 B の指摘で足した。素因数分解の一意性を離散位相で言い直した文で、log の成分は使わない。再照合 A2 は「自明（ほぼ同語反復）」と判定）。sup 距離では、異なる像は 1 以上離れます（`rho_sep`）。
+    - **すべての素点を同時に測る位相**（読み。`BoxCoord`：`Nat.Primes → ℤ` に離散位相。写像 `rhoBox` は ρ と同じ。ℤ 値の座標では離散位相が箱・一様の位相と同じことは Lean の外の標準の事実）：像は閉かつ離散です（`isClosed_discrete_rhoBox_image`。独立照合 B の指摘で足した。素因数分解の一意性を離散位相で言い直した文で、log の成分は使わない。再照合 A2 は「自明（位相の選び方でほぼ決まり、ほぼ同語反復に近い）」と判定）。sup 距離では、異なる像は 1 以上離れます（`rho_sep`）。
     - 離散になるかどうかは位相の選び方で決まり、有限台では決まりません。付値の組は有限台で（`finite_support_padicValRat`）、各元は台の段 ⟨T⟩ の元ですが（`eq_prod_support`）、`rho_one_mem_closure_ne_one` の近似点も有限台です（独立照合 B の指摘）。
-    - Lean の外：直和 ⊕ℤ の直極限の位相（有限の段 ℤ^T の直極限）が離散であることと、それと `BoxCoord` の位相の同一視（標準の事実）。
-  - **5. 対照群（Lean では自明な文だけ）。** 値が c·ℤ（c > 0）に入れば、異なる値は c 以上離れます（`sep_of_mem_zmultiples`）。Lean にあるのは、通約的な 2 つの実数の対数についての文です（`mem_zmultiples_of_commensurable`・`sep_of_commensurable`。一般化素数の全体には広げていない）。
+    - Lean の外：直和 ⊕ℤ の直極限の位相（有限の段 ℤ^T の直極限）が離散であることと、それと `BoxCoord` の位相の同一視（標準の事実）。積公式を満たす点の集合と像の一致。
+  - **5. 対照群（Lean では自明な文だけ）。** 値が c·ℤ（c > 0）に入れば、異なる値は c 以上離れます（`sep_of_mem_zmultiples`）。Lean にあるのは、通約的な 2 つの実数 L₁, L₂ についての文です（対数と読む）（`mem_zmultiples_of_commensurable`・`sep_of_commensurable`。一般化素数の全体には広げていない）。
   - **6. 順序版（大きさの順序 = 無限素点の絶対値）。** ⟨p⟩ では 1 より大きい最小の元は p です（`zpow_ge_of_one_lt`）。⟨p, r⟩（p ≠ r）では 1 より大きい最小の元がありません（`exists_between_one`）。
@@ -106,3 +106,3 @@
 | 有限の基礎 ⟨S⟩ の閾値と二分法（S は素数の有限集合、T ⊆ S）：`imgST S T` の閉包が水平な直線を含む ⇔ 稠密 ⇔ T の外に S の異なる素数が 2 つ。そうでなければ閉かつ離散（この側は T ⊆ S なしでも成り立つ） | `threshold_iff`・`dense_imgST_iff`・`isClosed_discrete_imgST`・`fiber_sep` | (6)（16 通り）・(8)・(21)（仮定 T ⊆ S の除去テストと証人） | 既知（再導出） |
-| S ∪ {∞} から 1 つ落としても格子 | 離散の部分は `isClosed_discrete_imgST`（T = S ∖ {p}）。余コンパクト性は Lean にしていない | (9) | 既知（S 単数定理の形） |
+| S ∪ {∞} から 1 つ落としても格子 | 有限素点 p を落とす場合の離散の部分は `isClosed_discrete_imgST`（T = S ∖ {p}）、∞ を落とす場合の分離は `exists_mem_one_le_abs_of_support`。余コンパクト性は Lean にしていない | (9) | 既知（S 単数定理の形） |
 | 直積の位相で ρ の像は稠密、直線 ℝ × {0} が閉包に入る、ρ(1) は孤立点でない、閉包の点 (1, 0) は像にない | `dense_rho_image`・`mem_closure_line_prod`・`rho_one_mem_closure_ne_one`・`closure_rho_not_image` | (12)・(13)・(20) | 既知 |
@@ -137,3 +137,3 @@
 
-- L1 の読みの主な数学的内容（⟨S⟩ の二分法と、有限素点の座標での位相の対比）は、既知の事実として Lean にしました（§1 の命題 3 そのものを形式化したのではありません。S 単数定理の形、直極限の位相、ℚ_{>0} の有限の解像度での閉包の文は Lean の外）。残る大域の問いは、Ẑ の上の定理 A、無限素点を含む大域対象、有限レベルの Bost–Connes です。
+- L1 の読みの主な数学的内容（⟨S⟩ の二分法の 2 つの文と、有限素点の座標での位相の対比）は、既知の事実として Lean にしました（§1 の命題 3 そのものを形式化したのではありません。S 単数定理の形、直極限の位相、ℚ_{>0} の有限の解像度での閉包の文は Lean の外）。残る大域の問いは、Ẑ の上の定理 A、無限素点を含む大域対象、有限レベルの Bost–Connes です。
 - 08:41 の方針（極限でも離散構造の観測を維持する）のもとでは、Part 252〜254 の U の極限も、完備化（L²(Ẑ^×)）ではなく直極限の側（すべての素点を同時に測る側）で扱うのが方針に合う、と読めます［推論、確信度：中］。U は有限素点の情報（Ẑ^× の方向）に乗っていて、∞ だけを測る（解像度が落ちた）姿では見えません（自明な指標で位相は 1、`phaseA1_one`）［推論］。
@@ -157,3 +157,3 @@
 - **兆候 4（既知の事実だけ）：7 パート連続**（Part 249〜255）。Part 255 は着手前から「既知の事実の Lean 化」と明記して行いました。
-- 辞書の未記入の件数：0（Part 255 の名前は辞書 §15）。文献照合の未実施の連続パート数：0（着手前の盲検の問いテストと、独立照合 C の名前のウェブでの確認）。兆候 1・2：出ていない（自前の名前 `rho` には C が文献の名前を付けた。`imgST`・`BoxCoord` は C の後に足した定義で、C は三つの場合分けについて「名前は知らない」と答えている。問いは構造・分類・次元の型ではない）。
+- 辞書の未記入の件数：0（Part 255 の名前は辞書 §15）。文献照合の未実施の連続パート数：0（着手前の盲検の問いテストと、独立照合 C の名前のウェブでの確認）。兆候 1・2：出ていない（判定の根拠は、問いが構造・分類・次元の型でないこと。自前の名前 `rho` には C が文献の名前を付けた。`imgST`・`BoxCoord` は C の後に足した定義で、C は三つの場合分けについて「名前は知らない」と答えている。問いは構造・分類・次元の型ではない）。
 - **著者の補足による向きの直し。** 08:41 の定義は着手前の文書の後に届き、ノートの向き（閉包の連続体を中心にしない）と Lean の節 4 を変えました。これは著者の入力による直しで、こちらの発見ではありません。L1 の数学がこの定義を「確かめた」とは書きません。
@@ -203,3 +203,3 @@
 - **直したもの。** Lean の冒頭の説明 6 か所と docstring 9 個（形式文は変えていない。組み立て直して確認）。ノートの上の行（題、15・17・31〜33・36・39・40・46・59・65・66・87・103・106・107・133・138・158・190 行）と、表の 3 行（`closure_logSet`・`threshold_iff`・`fiber_sep`）。
-- **直していないもの。** `isClosed_discrete_imgST`・`fiber_sep` の余分な仮定 hS（Lean の文は変えない）。二分法を 1 つの文にすること。
+- **直していないもの。** `isClosed_discrete_imgST`・`fiber_sep` の余分な仮定 hS（Lean の文は変えない）。二分法を 1 つの文にすること。T ⊄ S のときの `isClosed_discrete_imgST` の逆（述べていない）。表の `exists_prime_one_le_abs`・`isClosed_discrete_rhoBox_image` の行の但し書き（B2 の注記。直していない）。
 - **第 3 の型の検知。** B の後の直しが docstring に一部しか入っていなかった。`exists_near_in_subgroup` の docstring の括弧は、形式文の仮定のもとでは偽になりうる文だった（形式文そのものは真）。
```


## Part 256

### Part 256 の入力 (1)：定義の全文（このファイルと前のファイル。原文のまま。コメントと docstring だけ除いた）
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

### Part 256 の入力 (2)：形式文の全文（PAG260.lean の定理 23 個すべて。原文のまま、証明だけ除いた。すべてコンパイル済みで sorry なし、公理は標準の範囲）
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


### Part 256 の入力 (3)：B3 の出力の全文（原文のまま）

# 照合結果：B2 の指摘への直し（PAG260.lean・Part 256）

**要旨**：B2 の「直すべき点」12 項目は、すべて直しが入っています。直しの誤りもありません（高）。新しい文面には、形式文より強い言い方も計算の誤りも見つかりませんでした（高）。残っているのは、出所の書き方と参照についての小さな点だけです。

## 1. 「直すべき点」12 項目

| # | 判定 | 理由（確信度） |
|---|---|---|
| 1 | 入った | docstring・冒頭の 6・ノートの 4 のどれも「s·χ₁(N)·χ₂(M)·phaseA1(χ₁)·phaseA1(χ₂) 倍」で、形式文の係数と一致します。互いに素と原始の仮定も書かれています（高） |
| 2 | 入った | 定義（両方が Odd なら −1）と一致します。「交差項とは別の因子」とも明記されています（高） |
| 3 | 入った | 定義から計算すると、parFac は偶で 1、奇で −i です。「無限素点」は、冒頭でも docstring でも読みだと明記されています（高） |
| 4 | 入った | 「局所」が消え、「この文に奇は入っていない」という注記が付きました（高）。B2 案の「Part 258」が「Part 254」になっていますが、PAG260＝Part 256 という対応から、同じものを指しています（中） |
| 5 | 入った | 等号の組を Lean の一覧から外し、「Lean にしていないこと」へ移しました。交差項だけでずれる例も足されています。B2 案と形は違いますが、趣旨は満たしています（高） |
| 6 | 入った | 「Tate・Deligne の局所定数の場合」という言い方が、見出し・冒頭・ノート 25 行の 3 か所から消えました。代わりに「文献では…にあたる（局所 ε 因子は Lean にしていない）」になっています（高） |
| 7 | 入った | ノート・表・docstring・冒頭の 7 の 4 か所に入っています。τ の乗法性は、gaussSum_prodChar と★の連言「交差項 = 1」から直接出ます。χ₁χ₂ は偶、χ₁ と χ₂ は奇なので、比は正規化から来る 1/(I·I) = −1 です（検算済み）（高） |
| 8 | 入った | 形式文に互いに素の仮定はないので、「互いに素は要らない」は正しいです（高） |
| 9 | 入った | 法 15 の文に「奇」、法 39 の文に W₁W₂ ≠ 0 が入りました。法 39 の連言 7 つは、すべて文面にあります（高） |
| 10 | 入った | 冒頭に「W について」の段が新しくできました。答え 5、rootNum_prodChar、ノート 24 行、問いの出所にも反映されています（高） |
| 11 | 入った | 「C の申告。未確認」が付き、「W = 1 を外から入れると同じ形」に直っています（高） |
| 12 | 入った | isPrimitive に互いに素が入り、「指標の基底」は削られ、「3 つの位相」は W = 1 に直りました。読みの言葉の宣言もあり、ノート 141 行と §8 に記録されています（高） |

12 項目すべてに直しが入ったので、直していない項目の記録は要りません。ただし、リスト外だった B2 §4-4（ノート 102 行の説明不足）には、直しも記録もありません（低）。

## 2. 新しい文面の点検

**検算して合ったもの**（高）：
- parFac の値
- 法 39 の −1
- 法 15 の比 ∓i（法 5 の奇の原始指標は 2 つあり、どちらでも成り立つ）
- 等号の例（χ₁(5)χ₂(3) = (−1)(−1) = 1、s = 1）
- 交差項だけでずれる例（法 7 の 3 次の指標は偶なので s = 1、χ₁(7) = 1、χ₂(3) は 1 の原始 3 乗根）
- 互いに素でないとき両辺が 0（χ₁(N) = 0 で、τ(χ₁χ₂) = 0）

**小さな点**：
- (a) 冒頭「Lean にしていないこと」の「原始でない指標の式」：旧版にあった「位相の」が落ちました。そのため、原始性の要らない rootNum_prodChar まで Lean にしていないように読めます。→「原始でない指標での phaseA1 の式」に直す案です（低、確信度 中）
- (b) 表の「条件を満たす 2 組のどちらでも成り立つ」：内容は正しいのですが、Lean の文は存在を言うだけです。→「（手計算と A2 による。Lean の文は存在だけ）」を添える案です（低、高）
- (c) 「等号になる組（法 15、法 5 の偶の 2 次の指標）」：組の片方が書かれていません。「法 3 の奇の指標と」を補い、ノート 15 行と同じ形にそろえる案です（低、高）
- (d) 参照：docstring は「Part 254」、冒頭は `PAG.Part258.*` と書いています。初めて出るところで「Part 254＝PAG258.lean」と対応を書く案です。また冒頭から「step279」が消えたので、「数値 (4)」などがどの数値計算を指すのか追えません（低、中）
- (e) Lean にしていないことを事実として書いた箇所：「互いに素の仮定は余分」（cross_eq の docstring）、「外しても成り立つ（両辺 0）」、「原始でない χ では 0 にもなる」の 3 つです。どれも数学的には正しく、冒頭には「仮定つきのまま」とあります。docstring にも「外した形は Lean にしていない」を添える案です（低、高）
- (f) 「Part 254 の UA1_charU」は入力にないので、その文そのものは照合できません。ただ、定義から指標の直交関係で UA1(charU χ) = phaseA1 χ • charU χ が出るので、書いてある内容は合っています（中）

**差分の外**（変更されていない行で、B2 も対象にしていない）：
- (g) ノート 22 行「交差項は、χ₁ の、N を割る素点での局所成分（不分岐だが自明でない）から出ます」：冒頭ではこの文を消しましたが、ノートには残っています。さらに法 39 の例では χ₁(13) = 1 なので、その局所成分は自明です。→「（不分岐。一般には自明でない）」にするか、冒頭と同じ「文献では…にあたる」の形にする案です（低〜中、中）

## 3. 全体の判定

12 項目はすべて正しく入り、直しの誤りもない（高）。残るずれは小さく、重要な順に (g) ノート 22 行の「自明でない」、(a)「原始でない指標の式」のあいまいさ、(b) 表の「2 組のどちらでも」の出所、(c)(d) 参照の補い。

Read の回数：1 回

### Part 256 の入力 (4)：第 2 回の直しの差分（Lean の文面とノート。形式文は変えていない）
```diff
--- PAG260.lean（第 1 回の直しの後）
+++ PAG260.lean（第 2 回の直しの後）
@@ -3,3 +3,3 @@
 
-読みの言葉：「貼り合わせ U」は `PAG.Part258.UA1`、「公準 A1 の位相」は `PAG.Part258.phaseA1`（χ の原始指標の W）。
+読みの言葉：「貼り合わせ U」は `PAG.Part258.UA1`（Part 254 ＝ PAG258.lean）、「公準 A1 の位相」は `PAG.Part258.phaseA1`（χ の原始指標の W）。
 これらと「素点」「重なり」は著者の解釈の層の言葉で、Lean の文には出てこない。
@@ -41,4 +41,4 @@
 
-Lean にしていないこと：等号になる組（法 15、法 5 の偶の 2 次の指標。数値 (13)）、交差項だけでずれる組（s = 1 で交差項
-≠ 1。例：法 3 の奇の指標と法 7 の 3 次の指標。数値は再照合のときの確認だけ）、原始でない指標の式（導手 d₁, d₂ での
+Lean にしていないこと（数値は step279.py の項目番号）：等号になる組（法 15：法 3 の奇の指標と法 5 の偶の 2 次の指標。数値 (13)）、交差項だけでずれる組（s = 1 で交差項
+≠ 1。例：法 3 の奇の指標と法 7 の 3 次の指標。数値は再照合のときの確認だけ）、原始でない指標での phaseA1 の式（導手 d₁, d₂ での
 交差項 χ₁*(d₂)·χ₂*(d₁)。数値 (4)）、作用素の形、3 つ以上の法（数値 (7)）、互いに素でない法（両辺が 0。数値 (10)）、
@@ -280,3 +280,3 @@
 
-/-- 条件つきの文：W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 なら s·χ₁(N)·χ₂(M) = 1（互いに素の仮定は余分）。2 次の指標では平方剰余の
+/-- 条件つきの文：W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 なら s·χ₁(N)·χ₂(M) = 1（互いに素の仮定は余分。外した形は Lean にしていない）。2 次の指標では平方剰余の
 相互法則と同じ形になるが、3 つの仮定は外から入れるもので、ここからは出ない。 -/

--- pag2_part256_gluing_cross_term.md（第 1 回の直しの後）
+++ pag2_part256_gluing_cross_term.md（第 2 回の直しの後）
@@ -21,3 +21,3 @@
   - 文献の名前（独立照合 C、§7）：交差項は「不分岐な指標でひねったときの ε 因子の変化」、符号 s は (−1)^{a₁a₂} で、実素点のヒルベルト記号 (−1, −1)_∞ と同じ形。2 次の指標では、W = 1 を外から入れるとヒルベルト記号の積公式と同じ形になる（C の申告。未確認）。
-  - **言い方の注意（着手前の盲検の指摘）。** 文献では、大域の ε 因子は局所の ε 因子の積です（Tate、Deligne）。ここで言うずれは、ディリクレ指標を中国剰余定理で分けた成分 χ₁, χ₂ と、イデール類指標の局所成分との違いです。交差項は、χ₁ の、N を割る素点での局所成分（不分岐だが自明でない）から出ます。「大域は局所の積ではない」とは書きません。
+  - **言い方の注意（着手前の盲検の指摘）。** 文献では、大域の ε 因子は局所の ε 因子の積です（Tate、Deligne）。ここで言うずれは、ディリクレ指標を中国剰余定理で分けた成分 χ₁, χ₂ と、イデール類指標の局所成分との違いです。交差項は、χ₁ の、N を割る素点での局所成分（不分岐。一般には自明でないが、法 39 の例では χ₁(13) = 1 で自明）から出ます。「大域は局所の積ではない」とは書きません。
 - **2 次の指標と相互法則（観察。主な結果にしない）。** p, q が異なる奇素数で χ₁, χ₂ がルジャンドル記号のとき、数値では W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 で、6 の文は平方剰余の相互法則 (q/p)(p/q) = (−1)^{(p−1)(q−1)/4} と同じ形になります（step279 の (2)：奇素数の 28 組）。ただし、ここから相互法則が出るのではありません。合成の法 pq の 2 次の指標で W = 1 であることは外から入れる事実で、その証明の引き方によっては循環します（着手前の盲検の指摘）。
@@ -101,3 +101,3 @@
   - `Nat.Prime 13` は `norm_num` で示せず、`by decide` で通った。
-- B の後に `rootNum_prodChar_eq_neg_mul` を足し、`rootNum_prodChar_ne_mul` の文に「両方が奇」を入れました（B の「主張がやや強い」への対応）。組み立て直して rc = 0。
+- B の後に `rootNum_prodChar_eq_neg_mul` を足し、`rootNum_prodChar_ne_mul` の文に「両方が奇」を入れました（B の「主張がやや強い」への対応。条件を満たす組は 2 つあり、どちらでも成り立つ：手計算と再照合 A2。Lean の文は存在だけ）。組み立て直して rc = 0。
 - sorry 0、警告 0、`#print axioms` 23 行（定理と同数）。鎖全体（PAG.lean〜PAG260.lean）は theorem/lemma 3525、`#print axioms` 3826。
```

### Part 256 の入力 (5)：表（xlsx）の差分
```
【rootNum_prodChar_ne_mul の主張（第 1 回の後）】…（存在の文。条件を満たす 2 組のどちらでも成り立つ。比の値 ∓i は文にない）
【rootNum_prodChar_ne_mul の主張（第 2 回の後）】…（Lean の文は存在だけ。条件を満たす 2 組のどちらでも成り立つことは手計算と再照合 A2 による。比の値 ∓i は文にない）
```
