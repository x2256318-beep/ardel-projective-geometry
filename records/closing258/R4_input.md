あなたは独立の照合者です。この 1 つのファイルだけを Read で読んでください（ほかのツールは使わないでください）。答えは日本語で。
判定ごとに確信度（高・中・低）を付け、見ていないもの・確かめられないものも書いてください。

# 依頼（閉鎖条件 4）：Part 257 の照合後の直し（14 件）の再照合

背景：Part 257（PAG261.lean）の独立照合者 B の指摘（下の A）を受けて、Lean の冒頭の説明と docstring、ノートを直し、Mathlib と同じ文の補助 `not_odd_of_even` を消した。直す前と後の差分を B、直した後の PAG261.lean の全文を C に付ける（ノートは差分だけ）。
確かめてほしいこと：
1. B の指摘 14 件（§2 の表）と内部照合の指摘（§3）のそれぞれが、差分で直ったか（直った／一部／直っていない）。
2. 直しが新しい誤り（言い過ぎ、食い違い、形式文の言える範囲を越えた文）を入れていないか。とくに、局所定数との一致の条件、問いの後半への「負の答え」の文、確信度の付け方。
3. 形式文の変更が `not_odd_of_even` の削除（と、その使用を Mathlib の `DirichletCharacter.Even.not_odd` に置き換えたこと）だけか。
出力：## 1. 指摘ごとの判定（表）　## 2. 新しい誤り（表）　## 3. 形式文の変更の有無　## 4. 総評（3 行まで）

# A. 照合者 B の出力（全文）
## 1. 形式文の判定

| 定理 | 判定 |
|---|---|
| `lvl_cons`・`lvl_eq_prod`・`lvl_neZero`・`coprime_lvl`・`sqrt_lvl`・`prod_map_div'`・`not_odd_of_even`・`tri_succ`・`listChar_congr` | 問題なし。補助の文で、自明だが偽ではない。`prod_map_div'` と `not_odd_of_even` は Mathlib に同じものがあるかもしれないが、確かめていない（確信度 低） |
| `gaussSum_listChar` | 問題なし。仮定は Pairwise coprime だけで、Nodup は要らない。原始性も仮定していない。漸化式の交差項は、`gaussSum_mul_coprime` で N₁ = N a、N₂ = lvl l とおいた形と一致する |
| `listChar_natCast`・`listChar_neg_one`・`listChar_neg_one_pow` | 問題なし。ZMod の元はどれも自然数の像なので、「自然数で」に限っても内容は欠けない |
| `cross_eq_formI`・`cross_eq_formII` | 問題なし。互いに素の仮定がなく、定義 `cross` についての純粋な恒等式。Nodup の仮定は軽い（List.erase が最初の 1 つだけを消すため、置いてあるのは妥当） |
| `rootNum_listChar_formI`・`rootNum_listChar_formII` | 問題なし（軽い注記）。Pairwise coprime のもとでは、重複できる成分は N_i = 1 のものだけなので、Nodup は外せるはず（手で確かめた。Lean では未確認）。弱すぎる・強すぎる仮定ではない |
| `parFac_listChar` | 問題なし。k = 2, 3, 4 を手で確かめた：(−i)^k と (−i)^{k mod 2} の比が (−1)^{k(k−1)/2} になる |
| `rootNum_listChar` | 問題なし。Nodup を使わず cross のままで書いている |
| `isPrimitive_listChar_iff` | 問題なし。⇔ の両向きを示している（docstring の誤りは §2 に書く） |
| `phaseA1_listChar` | 問題なし。仮定は原始性だけ |
| `exists_listChar` | 問題なし。Nodup は `Function.update` のために要る |
| `listChar_injective` | 問題なし |
| `gaussSum_listChar_singleton` | 問題なし。自明な退化例として書かれていて、その表示どおり。法は N_a·1 |
| `pairwise_primeFactors`・`lvl_primeFactors` | 問題なし |
| `gaussSum_primeFactors` | 問題なし。∃ の中の第 1 項（自然数での値が ∏χ_p）が、primeFactors の上の χ_p を中国剰余定理で決めるので、空虚ではない。一意性は文に入っていない（§2 で扱う） |
| 定義 `lvl`・`listChar`・`cross`・`oddCount` | 意図どおり。cross の漸化式は χ_a(lvl l)·listChar l (N_a)·cross l |

## 2. 文面の指摘

| 場所 | 問題 | 直し方の案 | 確信度 |
|---|---|---|---|
| Lean 冒頭 1 行目の題「W の分解（すべての成分の局所因子の積）」 | 形式文にない解釈の言葉「局所因子」が題に入っている。同じ冒頭で「局所因子…は Lean の文には出てこない」と書いていることと矛盾し、「題は形式文から起こす」規則にも反する | 「…ガウス和と W の分解（成分の τ・W の積と交差項・符号）」のように、形式文の言葉だけにする | 高 |
| Lean 冒頭「言い方の注意」とノート「読み」2 項目目の「形 (II) の成分 i の因子 (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i) は…イデール類指標の局所定数と一致」 | (a) 条件が書き落とされている。読みの根拠（着手前 §2.3）は原始指標で、成分は素数冪の法 p^{e_p} として計算している。一般の互いに素な N_i や、原始でない χ_i では成り立たない。例：法 p の自明指標では τ = −1 なので因子は −1/√p になり、不分岐の局所定数とは別物。(b) ω の正規化の条件（ω_q(q) = χ(q)。盲検によれば χ̄ に対応させると積が共役になる）も書き落とされ、加法指標の規約だけが書いてある | 「原始指標 χ を素数冪の成分に分け、ω を ω_q(q)=χ(q) と正規化し、ψ を Tate の規約にとったとき」と条件を明記する | 高 |
| `isPrimitive_listChar_iff` の docstring「Part 190 の `isPrimitive_mul`・`isPrimitive_iff`・… を使う」 | 証明は `isPrimitive_mul` を使っていない（使っているのは `isPrimitive_iff`・`comp₁_mul`・`comp₂_mul` だけ）。冒頭の「前の鎖の定理」の一覧のほうは正しく、docstring と食い違う | docstring から `isPrimitive_mul` を消す | 高 |
| ノート題「ガウス和と W はすべての成分の因子の積に分かれる」 | `rootNum_listChar` では交差項と大域の符号 (−1)^{k(k−1)/2} が残る。形 (II) でも ε_∞ = parFac(listChar χ l) は大域の指標で決まる 1 つの因子で、成分ごとには分かれていない。「成分の因子の積に分かれる」は形式文より強い | 「…成分の τ・W の積と交差項・符号で書ける」とする | 中 |
| Lean 冒頭 31 行目とノートの「大域の貼り合わせ（U の固有値 W）」 | U の固有値は phaseA1 で、rootNum と一致するのは原始のときだけ（`phaseA1_of_isPrimitive`）。一方、W の式（formI/II、`rootNum_listChar`）は原始でない指標でも成り立つ。原始でない指標では W は U の固有値ではないので、二つが混ざっている | 「U の固有値 phaseA1（原始のとき W = rootNum）」と書き分ける | 中 |
| ノート §0.1 の 1（問い後半「各点の因子は、どこまでその点だけで決まるか」） | 結論のどこにも答えがない。形 (II) では成分 i の因子が、ほかの成分の値 χ_j(N_i) に依存する。これは「その点だけでは決まらない」という負の答えで、読みの「ずれは各点の因子の中に入り」はこれをぼかしている | 「成分 i の因子は χ_i だけでは決まらず、χ_j(N_i)（j≠i）に依存する（Lean の文 `cross_eq_formII` から読める）」と明記する | 中 |
| ノート「位置づけ」の「形 (II) と ∞ の因子は Tate の局所定数の積公式の GL(1)/ℚ の場合（確信度：高）」 | 根拠は盲検（判定は確信度 中〜高）だけで、著者は Rohrlich を開いていない（§5）。確信度「高」はその根拠を越える | 「Lean 化の部分＝高、Tate との同定＝中〜高（盲検の申告のまま、一次文献は未確認）」と分ける | 中 |
| 冒頭とノートの「Montgomery–Vaughan の Theorem 9.6」 | 盲検で確かめたのは PSU の講義ノート Thm 4.2 で、M–V の定理番号を確かめた記録がこのファイルにない | 確認したか未確認かを書く | 中 |
| ノート §0.3・§1 の行「原始性 ⇔、phaseA1 の形」と数値 (7) | step280 (7) は原始性しか見ておらず、phaseA1 の式の数値項目はない。(7) のログには「Lean は一方向だけの予定」と古い記述が残っている（Lean は ⇔） | 表に「phaseA1 は数値なし（`rootNum_listChar` からの直接の帰結）」と書く。ログの文言を更新する | 中 |
| ノート §1 の行「W の形 (I)・(II)」の数値 (4) | (4) は形 (II) だけ。形 (I) の W は (2) と (4) から出るが、直接の項目はない | 「(4)（形 (II)）。形 (I) は (2)(4) から」とする | 低 |
| `rootNum_listChar` の docstring・冒頭 4・結論 3「成分 2 つでは `rootNum_prodChar` と同じ式」 | listChar [a,b] は法 N_a·(N_b·1) の指標で、法 N_a·N_b の `prodChar` とは型が違う（N_b·1 と N_b は変数については rfl で一致しないはず）。「Lean ではつないでいない」と書いてあるのは正しい。そのうえで「式として同じ（法は N_b·1）」と添えるとよい | 括弧に「法は N_a·(N_b·1)」を加える | 低 |
| 冒頭「範囲」 | `gaussSum_primeFactors` は存在と τ の式だけで、法 n での成分の一意性は文に入っていない。ノート題の「ちょうど 1 通り」は lvl の形（`listChar_injective`）の話なので、法 n の一般形と混同されうる | 「一意性は lvl の形で（`listChar_injective`）。法 n の形では文にしていない」と明記する | 低 |
| Lean 冒頭の「閉じる前の照合（全宣言 4310 件…）」とノート §7 | Lean 冒頭は 1 回目の数を 2 回目の 4310 と混ぜて書いている。ノートでは 1 回目が 4313 件・PAG261 は 34 件で、2 回目が 4310・31。差は 3 件なのに、消したと説明されているのは 2 件（`gaussSum_level_one`・`ppow_neZero`）。残る 1 件の説明がない | 3 件目が何か（消したのか、改名したのか）を書く | 中 |
| 着手前の文書 §6「内部の重複（Part 183・189・190・192・194）」 | 「Part 194」はおそらくファイル番号 PAG194（= Part 190）との取り違え。Part 183 はほかのどこにも出てこない | 番号を確かめる | 低 |

## 3. 内部照合の指摘

- **前の鎖の中の重複定義（§7 に記録なし）**：PAG236 の `charMul` と PAG260 の `prodChar` は、本体が同一（changeLevel (dvd_mul_right) χ₁ * changeLevel (dvd_mul_left) χ₂）。`listChar_injective` はこれに頼って、`h' : charMul … = charMul … := h` と型を付け替えている。PAG261 の新しい宣言の重複ではないが、Part 256 で入った重複であり、PAG261 の証明が依存している。§7 か監査のメモに記録しておくべき（確信度 高）。PAG193・194 の文も同じ式を名前なしの形で持っているので、実質 3 重の表現になっている。
- `gaussSum_listChar` の cons の 1 段は、PAG260 の `gaussSum_prodChar` と同じ文（証明では `gaussSum_mul_coprime` を直接使っている）。成分 2 つの場合は、型の違い（N_b·1）を除けば `gaussSum_prodChar` と `rootNum_prodChar` から数行で出る。これはノート §7 の「成分 2 つの式は前の鎖にある」と食い違わない。
- `isPrimitive_listChar_iff` の 1 段は `isPrimitive_iff` と `comp₁_mul`・`comp₂_mul`、`exists_listChar` の 1 段は `decomp`、`listChar_injective` の 1 段は `charMul_injective`。どれも任意個への帰納法で、文の一致ではない。§1 の「文の重み」の書き方と整合している。
- `z_hall`・`prod_root_iff_local` は、形式文を比べた範囲では PAG261 の文と同じではなく、直ちに出るものでもない（前者はずれを 1 の冪根の存在でしか書かない）。
- 任意個の成分、形 (II)、符号 (−1)^{k(k−1)/2} の文は、付けられた宣言の中には見当たらない。ノートの記録と一致する。
- `prod_map_div'`・`not_odd_of_even` が Mathlib の既存補題と重複していないかは、確かめていない。

## 4. 数値照合との対応

- (1)→`gaussSum_listChar`、(2)→`cross_eq_formI`、(3)→`cross_eq_formII`、(4)→`rootNum_listChar_formII`、(5)→`parFac_listChar`・`rootNum_listChar`、(6)→`listChar_natCast`・`listChar_neg_one`、(8)→`exists_listChar`・`listChar_injective`、(9)→`gaussSum_listChar_singleton`。どれも対応している。
- (11) は「文に原始性の仮定がない」ことに対応していて正しい。
- (7) は `isPrimitive_listChar_iff` だけに対応し、`phaseA1_listChar` には数値がない。ログの「一方向だけの予定」は古い。
- (10) は「Lean にしていない」と正しく書かれている。
- `rootNum_listChar_formI` には直接の項目がない。
- `gaussSum_primeFactors` の数値は「着手前の (1)(2)」とされているが、その出力はこのファイルにないので見ていない。
- ノート §2 の「最大誤差 9.1×10⁻¹⁴」「689 組」「522 組」「法 12・40・105・180・90・112」「11/11」はログと一致する。
- `#print axioms` は 26 行で、内訳（23・1・1・1）もノートと一致する。sorryAx は出ていない。

## 5. 総評

- 形式文はすべて偽・空虚ではなく、仮定も過大ではない。前の鎖の既知の結果を任意個に帰納したもので、内容はノートの「既知の Lean 化」という表示どおり。
- 主な問題は文面にある。Lean 冒頭の題に「局所因子」が入っていること、Tate の局所定数との同定から「原始・素数冪の成分・ω の正規化」の条件が落ちていること、`isPrimitive_listChar_iff` の docstring の誤り、U の固有値と W の混同、問いの後半（各点の因子がその点だけで決まるか）への負の答えを書いていないこと。
- 内部照合では、PAG236 の `charMul` と PAG260 の `prodChar` の重複定義を記録すべき。1 回目の照合で消した宣言の数（3 件差で説明は 2 件）も、合わない理由を書いてほしい。

**見ていないもの・確かめていないもの**
- コンパイル（.out の axioms 出力だけを信用した。警告 0 も出力からは確かめられない）。
- 付けられていない前の鎖の宣言と Mathlib の補題名、step280.py のソース。
- 着手前の数値 (1)(2)(5)(8)、xlsx の検索、全宣言の照合（4310 件）、鎖全体の定理数 3,551。
- 文献（M–V Thm 9.6、Rohrlich (2.49)(2.55)、Tate の規約）。
- N_b·1 と N_b が rfl で一致しないこと、Nodup が外せることは手で考えただけで、Lean では確かめていない。
- 盲検の出力ファイル本体。


# B. 差分（直す前 → 直した後）
```diff
--- before/PAG261.lean
+++ after/PAG261.lean
@@ -1,8 +1,9 @@
 /-
-アーデル射影幾何 — Part 257（PAG 2.0）：互いに素な法の並びの指標の積での、ガウス和と W の分解（すべての成分の局所因子の積）
+アーデル射影幾何 — Part 257（PAG 2.0）：互いに素な法の並びの指標の積での、ガウス和と W の分解（成分の τ・W の積と、交差項・符号）
 
 問いの出所：著者の選択（2026-11-14 20:59、着手前の文書 `pag2_part257_preregistration.md` の候補 P1）。開始条件 2（方向βの
 登録ファイルとの突き合わせ）は、著者の判断で保留のまま始めた（登録ファイルは届いていない）。
-幾何の言葉での問い（読み）：大域の貼り合わせ（U の固有値 W）は、∞ を含む各点の局所の因子の積に分かれるか。
+幾何の言葉での問い（読み）：大域の貼り合わせ（U の固有値 phaseA1。原始の指標では W = rootNum）は、∞ を含む各点の局所の因子の積に
+分かれるか。各点の因子は、どこまでその点だけで決まるか。
 Lean が答えるのは、互いに素な法の並び N_1, …, N_k の指標の積（法 N_1·…·N_k）の上での、ガウス和 τ と W の式まで。
 
@@ -11,5 +12,5 @@
 著者の解釈の層の言葉で、Lean の文には出てこない。偶奇の因子が無限素点の局所因子にあたる、も読み。
 
-Lean の文（すべて既知の事実の Lean 化。Montgomery–Vaughan の Theorem 9.6 を繰り返したものと、そのルート数版）：
+Lean の文（すべて既知の事実の Lean 化。互いに素な法でのガウス和の乗法性を繰り返したものと、そのルート数版）：
 1. 法の並びの積 `lvl`（先頭 × 残り）と指標の積 `listChar`（先頭の指標と残りの積を Part 256 の `prodChar` でつなぐ）。
    値は成分の値の積（`listChar_natCast`：自然数で、`listChar_neg_one`：−1 で）。
@@ -20,10 +21,10 @@
    = ε_∞·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)（`rootNum_listChar_formII`）。ε_∞ = `parFac`(listChar χ l)。
 4. ∞ の因子の符号：ε_∞(listChar χ l) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数 `oddCount`。`parFac_listChar`）。
-   したがって W(listChar χ l) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（`rootNum_listChar`。成分 2 つでは Part 256 の `rootNum_prodChar` と
-   同じ式になる。Lean ではつないでいない）。
+   したがって W(listChar χ l) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（`rootNum_listChar`。成分 2 つでは、法 N_a·(N_b·1) の上で
+   Part 256 の `rootNum_prodChar` と同じ式になる。Lean ではつないでいない）。
 5. 原始性：すべての成分が原始 ⇔ 積が原始（`isPrimitive_listChar_iff`）。原始なら UA1 の固有値 phaseA1 も同じ式
    （`phaseA1_listChar`）。
 6. 分解：法 lvl l の指標は、どれも成分の積 listChar χ l の形に書け（`exists_listChar`。並びに重複なし）、成分は一意
-   （`listChar_injective`）。
+   （`listChar_injective`。Part 256 の `prodChar` が Part 232 の `charMul` と同じ定義であることを使って、`charMul_injective` を当てる）。
 7. すべての素数への分解：法 n の指標 Ψ は、素数冪の法 p^{v_p(n)}（0 でないことは Part 236（PAG240）の instance `neZero_ordProj`）の成分 χ_p で、自然数での値が ∏_p χ_p(x)、
    τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)})（`gaussSum_primeFactors`。形 (II)）。退化例（成分 1 つ）は τ(listChar χ [a]) = τ(χ_a)
@@ -35,11 +36,15 @@
 `prodChar`・`prodChar_neg_one`・`parFac_prodChar`・`crossSign`。
 
-言い方の注意：文献では、大域の ε 因子は局所の ε 因子の積（Tate、Deligne）。形 (II) の成分 i の因子 (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i) は、
-加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}（Tate の学位論文の規約）にとったときのイデール類指標の局所定数と一致し、
-∞ の因子は i^{−a}（盲検の問いテストと私の手計算。Lean では示していない）。規約を逆にすると各因子が χ_p(−1) 倍、
-∞ の因子が i^{a} になるが、積は変わらない。A1 は公準のまま。ここでの文は τ・W・phaseA1 についての恒等式で、A1 から何かを出すものではない。
-
-範囲：互いに素な法の並び（リスト）の上の式。法 n の任意の指標についての文は 7 のガウス和と分解まで（W の形は、listChar の形の
-指標の上で 3・4）。Lean にしていないこと（数値は step280.py の項目番号）：イデール類指標と Tate の局所定数そのもの、
+言い方の注意：文献では、大域の ε 因子は局所の ε 因子の積（Tate、Deligne）。原始指標 χ を素数冪の成分 χ_p に分け、
+χ に対応するイデール類指標 ω を ω_q(q) = χ(q)（不分岐な q）と正規化し、加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}
+（Tate の学位論文の規約）にとると、形 (II) の p の因子 (τ(χ_p)/√p^{e_p})·∏_{q≠p} χ_q(p^{e_p}) は ω の p での局所定数と一致し、
+∞ の局所定数は i^{−a}（着手前の盲検の問いテストと私の手計算。確信度 中〜高。Lean では示していない）。原始でない成分や、
+素数冪でない法の成分では、この一致は言えない（例：法 p の自明な指標の因子は −1/√p）。ψ の規約を逆にすると各 p の因子が
+χ_p(−1) 倍、∞ の因子が i^{a} になるが、積は変わらない。ω を χ̄ に対応させる規約では、積が W の共役になる（盲検の申告）。
+問いの後半への答え（Lean の文から読めること）：形 (II) の成分 i の因子は χ_i だけでは決まらず、ほかの成分の N_i での値
+χ_j(N_i)（j ≠ i）に依存する。∞ の因子 ε_∞ も合成した指標の偶奇で決まる 1 つの因子で、成分ごとには (−1)^{k(k−1)/2} だけずれる。A1 は公準のまま。ここでの文は τ・W・phaseA1 についての恒等式で、A1 から何かを出すものではない。
+
+範囲：互いに素な法の並び（リスト）の上の式。法 n の任意の指標についての文は 7 のガウス和と成分の存在まで（W の形は、listChar の形の
+指標の上で 3・4。成分の一意性は listChar の形でだけ言い（`listChar_injective`）、法 n の形では文にしていない）。Lean にしていないこと（数値は step280.py の項目番号）：イデール類指標と Tate の局所定数そのもの、
 原始でない指標の phaseA1 を導手を割る素点だけで書く形（着手前の数値 (5)）、並べ替えで listChar の値が変わらないこと
 （数値 (10)）、対照群 F_q[t]（∞ の因子は √q/τ(η)。盲検の答えで、私は計算していない）。
@@ -50,8 +55,10 @@
 ずれは「1 の冪根がある」の形）、Part 193（PAG197）の `LocalCrit`・`prod_root_iff_local`（平方因子のない素数成分での、1 の冪根に
 なる条件）、Part 127（PAG131）以降の素数冪の成分の積の位数の定理（積 ∏ τ(χ_i)/√ の位数で、合成した指標の τ ではない）。
-閉じる前の照合（全宣言 4310 件の書き出し、候補選び上位 20、`#dupcheck`・`#defeqcheck` を両向きに）：1 回目で、下書きの
-`gaussSum_level_one` が Part 199（PAG203）の同名の定理と同じ文、法 p^{v_p(n)} が 0 でないことの instance が Part 236（PAG240）の
-`neZero_ordProj` と同じ文だった（どちらも Lean で両向きに確認）。両方を消して前の鎖のものを使い、2 回目（31 件・1132 回）は一致 0。
-網羅ではない（候補選びは型に現れる定数の近さで、上位 20 まで）。
+閉じる前の照合（全宣言の書き出し、候補選び上位 20、`#dupcheck`・`#defeqcheck` を両向きに）：1 回目（4313 件、PAG261 の 34 件、
+1230 回）で、下書きの `gaussSum_level_one` が Part 199（PAG203）の同名の定理と同じ文、法 p^{v_p(n)} が 0 でないことの instance
+`ppow_neZero` が Part 236（PAG240）の `neZero_ordProj` と同じ文だった（どちらも Lean で両向きに確認）。この 2 つと、instance の
+ために置いた定義 `ppow`（p^{v_p(n)}。Part 236 にも別の `ppow` がある）を消して前の鎖のものを使った。2 回目（4310 件、31 件、
+1132 回）は一致 0。照合者 B の指摘で、下書きの `not_odd_of_even` も Mathlib の `DirichletCharacter.Even.not_odd` と同じ文なので
+消した（Mathlib との重複はこの手順では探していない）。網羅ではない（候補選びは型に現れる定数の近さで、上位 20 まで）。
 -/
 import PAG260
@@ -234,10 +241,4 @@
   | a :: l => (if (χ a).Odd then 1 else 0) + oddCount χ l
 
-omit hN [DecidableEq ι] in
-theorem not_odd_of_even {n : ℕ} {ψ : DirichletCharacter ℂ n} (h : ψ.Even) : ¬ψ.Odd := by
-  intro h'
-  unfold DirichletCharacter.Odd at h'; unfold DirichletCharacter.Even at h
-  rw [h] at h'; norm_num at h'
-
 omit [DecidableEq ι] in
 theorem listChar_neg_one_pow (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
@@ -249,5 +250,5 @@
     simp only [List.map_cons, List.prod_cons, oddCount, ih, pow_add]
     rcases (χ a).even_or_odd with h | h
-    · have hn := not_odd_of_even h
+    · have hn := h.not_odd
       unfold DirichletCharacter.Even at h
       simp [hn, h]
@@ -286,5 +287,5 @@
     unfold PAG.Part260.crossSign
     rcases (χ a).even_or_odd with h | h
-    · have hn := not_odd_of_even h
+    · have hn := h.not_odd
       simp only [hn, false_and, ↓reduceIte, zero_add]
       ring
@@ -296,5 +297,5 @@
 
 omit [DecidableEq ι] in
-/-- **W の分解（符号つき）**：W(χ) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（成分 2 つでは Part 256 の `rootNum_prodChar` と同じ式。Lean ではつないでいない）。 -/
+/-- **W の分解（符号つき）**：W(χ) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（成分 2 つでは、法 N_a·(N_b·1) の上で Part 256 の `rootNum_prodChar` と同じ式。Lean ではつないでいない）。 -/
 theorem rootNum_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
     (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
@@ -308,5 +309,5 @@
 
 omit [DecidableEq ι] in
-/-- 原始性：互いに素な法で、すべての成分が原始 ⇔ 積が原始（Part 190 の `isPrimitive_mul`・`isPrimitive_iff`・`comp₁_mul`・`comp₂_mul` を使う）。 -/
+/-- 原始性：互いに素な法で、すべての成分が原始 ⇔ 積が原始（Part 190 の `isPrimitive_iff`・`comp₁_mul`・`comp₂_mul` を使う）。 -/
 theorem isPrimitive_listChar_iff (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
     (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
@@ -330,5 +331,5 @@
 
 omit [DecidableEq ι] in
-/-- 原始指標の上では、UA1 の固有値 phaseA1 も同じ式で分かれる。 -/
+/-- 成分がすべて原始なら、UA1 の固有値 phaseA1 も同じ式で分かれる（原始でない指標では phaseA1 は W と違う）。 -/
 theorem phaseA1_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
     (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hp : ∀ i ∈ l, (χ i).IsPrimitive) :
@@ -452,5 +453,4 @@
 #print axioms PAG.Part261.rootNum_listChar_formII
 #print axioms PAG.Part261.rootNum_listChar_formI
-#print axioms PAG.Part261.not_odd_of_even
 #print axioms PAG.Part261.listChar_neg_one_pow
 #print axioms PAG.Part261.tri_succ
--- before/note
+++ after/note
@@ -1,22 +1,23 @@
-# アーデル射影幾何 — Part 257（PAG 2.0）：互いに素な法の並び N_1, …, N_k の指標の積の上で、ガウス和と W はすべての成分の因子の積に分かれる — τ = 交差項·∏τ(χ_i)、W = (−1)^{k(k−1)/2}·交差項·∏W(χ_i)。法 N_1·…·N_k の指標はこの形の積にちょうど 1 通りに書ける。既知の事実の Lean 化
+# アーデル射影幾何 — Part 257（PAG 2.0）：互いに素な法の並び N_1, …, N_k の指標の積の上で、ガウス和と W は成分の τ・W の積と、交差項・符号で書ける — τ = 交差項·∏τ(χ_i)、W = (−1)^{k(k−1)/2}·交差項·∏W(χ_i)。法 N_1·…·N_k の指標はこの形の積にちょうど 1 通りに書ける。既知の事実の Lean 化
 
-2026-11-14。PAG261.lean（定理 26 個、定義 4 個、instance 1 個）、step280.py（11 項目）。
+2026-11-14。PAG261.lean（定理 25 個、定義 4 個、instance 1 個）、step280.py（11 項目）。
 
 - **問いの出所。** 著者の選択（2026-11-14 20:59、着手前の文書 `pag2_part257_preregistration.md` の候補 P1、§12）。開始条件 2（方向βの登録ファイルとの突き合わせ）は、**著者の判断で保留のまま**始めました。登録ファイルは届いておらず、突き合わせは済んでいません。
-- **問いへの答えの範囲。** 幾何の言葉の問い（読み）は「大域の貼り合わせ（U の固有値 W）は、∞ を含む各点の局所の因子の積に分かれるか」。Lean が答えるのは、互いに素な法の並びの指標の積（Lean では `listChar`）の上でのガウス和 τ と W の式と、法 n の指標の素数冪の成分への分解までです。イデール類指標と Tate の局所定数そのものは Lean にしていません。
+- **問いへの答えの範囲。** 幾何の言葉の問い（読み）は「大域の貼り合わせ（U の固有値 phaseA1。原始の指標では W = rootNum）は、∞ を含む各点の局所の因子の積に分かれるか。各点の因子は、どこまでその点だけで決まるか」。Lean が答えるのは、互いに素な法の並びの指標の積（Lean では `listChar`）の上でのガウス和 τ と W の式と、法 n の指標の素数冪の成分への分解までです。イデール類指標と Tate の局所定数そのものは Lean にしていません。W の式（1〜3）は原始でない指標でも成り立つ恒等式で、U の固有値になるのは成分がすべて原始のとき（4）です。
 - **結論（Lean の文。すべて既知の事実の Lean 化）。**
   1. **ガウス和。** 法が互いに素なら τ(listChar χ l) = 交差項·∏_i τ(χ_i)（`gaussSum_listChar`。原始性は要らない）。交差項は漸化式で定め（`cross`）、閉じた形が 2 つあります。形 (I) は ∏_i χ_i(∏_{j≠i} N_j)（`cross_eq_formI`）、形 (II) は ∏_i ∏_{j≠i} χ_j(N_i)（`cross_eq_formII`）です。形 (II) は、成分 i の因子を「ほかの成分を N_i で読んだ値」で書く形です。
   2. **W。** W(listChar χ l) = ε_∞·∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)/√N_i（`rootNum_listChar_formI`）、= ε_∞·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)（`rootNum_listChar_formII`）。ε_∞ は偶奇の因子 `parFac`（偶で 1、奇で −i）です。
-  3. **∞ の因子の符号。** ε_∞(listChar χ l) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数。`parFac_listChar`）。したがって W(listChar χ l) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（`rootNum_listChar`）。成分 2 つでは Part 256 の `rootNum_prodChar` と同じ式です（Lean ではつないでいない）。
+  3. **∞ の因子の符号。** ε_∞(listChar χ l) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数。`parFac_listChar`）。したがって W(listChar χ l) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（`rootNum_listChar`）。成分 2 つでは、法 N_a·(N_b·1) の上で Part 256 の `rootNum_prodChar` と同じ式です（Lean ではつないでいない）。
   4. **原始性と U の固有値。** すべての成分が原始 ⇔ 積が原始（`isPrimitive_listChar_iff`）。原始なら、phaseA1（読みでは公準 A1 の位相）も同じ式で分かれます（`phaseA1_listChar`）。
-  5. **分解の存在と一意性。** 法 N_1·…·N_k の指標はどれも listChar χ l の形に書け（`exists_listChar`。並びに重複なし）、成分は一意です（`listChar_injective`）。Part 256 で「Part 190 の `decomp` と Part 232 の `charMul_injective` を合わせると出る（監査者の読み。Lean ではつないでいない）」と書いた事柄を、ここで Lean にしました（任意個の成分で）。
-  6. **すべての素数への分解。** 法 n の指標 Ψ には、素数冪の法 p^{v_p(n)} の成分 χ_p があって、自然数 x での値は Ψ(x) = ∏_p χ_p(x)、τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)}) です（`gaussSum_primeFactors`。形 (II)）。退化例（成分 1 つ）は τ(listChar χ [a]) = τ(χ_a)（`gaussSum_listChar_singleton`）。
-  - sorry 0、警告 0。`#print axioms` 26 行（定理と同数）は標準の公理の範囲です（23 行が [propext, Classical.choice, Quot.sound]、1 行が [propext, Quot.sound]、1 行が [propext]、1 行は公理なし）。
+  5. **分解の存在と一意性。** 法 N_1·…·N_k の指標はどれも listChar χ l の形に書け（`exists_listChar`。並びに重複なし）、成分は一意です（`listChar_injective`。Part 256 の `prodChar` が Part 232 の `charMul` と同じ定義であることを使って `charMul_injective` を当てる）。Part 256 で「Part 190 の `decomp` と Part 232 の `charMul_injective` を合わせると出る（監査者の読み。Lean ではつないでいない）」と書いた事柄を、ここで Lean にしました（任意個の成分で）。
+  6. **すべての素数への分解。** 法 n の指標 Ψ には、素数冪の法 p^{v_p(n)} の成分 χ_p があって、自然数 x での値は Ψ(x) = ∏_p χ_p(x)、τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)}) です（`gaussSum_primeFactors`。形 (II)）。成分の一意性は listChar の形でだけ言い、法 n の形では文にしていません。退化例（成分 1 つ）は τ(listChar χ [a]) = τ(χ_a)（`gaussSum_listChar_singleton`）。
+  - sorry 0、警告 0。`#print axioms` 25 行（定理と同数）は標準の公理の範囲です（22 行が [propext, Classical.choice, Quot.sound]、1 行が [propext, Quot.sound]、1 行が [propext]、1 行は公理なし）。
 - **読み（解釈の言葉。Lean の文ではない）。**
   - 「素点」「局所因子」「貼り合わせ」は著者の言葉です。Lean の文は、指標とガウス和についての恒等式です。偶奇の因子 ε_∞ が無限素点の局所因子にあたる、も読みです。
-  - 形 (II) の成分 i の因子 (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i) は、加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}（Tate の学位論文の規約）にとったときの、イデール類指標の p での局所定数と一致し、∞ の局所定数は i^{−a} です（着手前の盲検の問いテストと私の手計算。Lean では示していない）。規約を逆にすると各 p の因子が χ_p(−1) 倍、∞ の因子が i^{a} になり、積は変わりません。
-  - Part 256 では「成分の W の積からのずれ」を交差項と符号 s として書きました。成分を任意個にすると、ずれは交差項（形 (I)・(II) のどちらでも書ける）と符号 (−1)^{k(k−1)/2} です。形 (II) で各成分の因子にまとめると、ずれは各点の因子の中に入り、W は各点の因子の積になります（ここまでは Lean の文。それを「局所定数の積」と読むのは上の規約の話で、Lean の外）。
+  - **局所定数との一致（条件つき。確信度：中〜高、Lean の外）。** 原始指標 χ を素数冪の成分 χ_p に分け、χ に対応するイデール類指標 ω を ω_q(q) = χ(q)（不分岐な q）と正規化し、加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}（Tate の学位論文の規約）にとると、形 (II) の p の因子 (τ(χ_p)/√p^{e_p})·∏_{q≠p} χ_q(p^{e_p}) は ω の p での局所定数と一致し、∞ の局所定数は i^{−a} です（着手前の盲検の問いテストと私の手計算。盲検の根拠は Rohrlich の講義ノートで、私は一次文献を開いていない）。原始でない成分や、素数冪でない法の成分では、この一致は言えません（例：法 p の自明な指標の因子は −1/√p で、不分岐の局所定数ではない。照合者 B の指摘）。ψ の規約を逆にすると各 p の因子が χ_p(−1) 倍、∞ の因子が i^{a} になり、積は変わりません。ω を χ̄ に対応させる規約では積が W の共役になります（盲検の申告）。
+  - **問いの後半への答え（負の答え。Lean の文 `cross_eq_formII` から読める）。** 各点の因子は、その点だけでは決まりません。形 (II) の成分 i の因子は χ_i だけでなく、ほかの成分の N_i での値 χ_j(N_i)（j ≠ i）に依存します。∞ の因子 ε_∞ も合成した指標の偶奇で決まる 1 つの因子で、成分ごとの ε_∞(χ_i) の積とは (−1)^{k(k−1)/2} だけずれます。上の条件のもとでは、この依存は「局所定数がイデール類指標 ω の局所成分の値（ω_p(p) = ∏_{q≠p} χ_q(p)）を含む」ことにあたります（読み）。
+  - Part 256 では「成分の W の積からのずれ」を交差項と符号 s として書きました。成分を任意個にすると、ずれは交差項（形 (I)・(II) のどちらでも書ける）と符号 (−1)^{k(k−1)/2} です。
 - **公準 A1 との関係。** A1 は公準のままです。ここでの文は τ・W・phaseA1 についての恒等式で、A1 から何かを出すものではありません（CLAUDE.md §7 の第 2 の型）。
-- **位置づけ。** 既知の事実の Lean 化です（再導出、確信度：高）。形 (I) は Montgomery–Vaughan の Theorem 9.6 を繰り返したもの、形 (II) と ∞ の因子は Tate の局所定数の積公式の GL(1)/ℚ の場合（規約を除いて）です。新規候補はありません。
+- **位置づけ。** 既知の事実の Lean 化です（Lean 化の部分は確信度：高）。形 (I) は互いに素な法でのガウス和の乗法性（Part 256 の着手前の盲検が Montgomery–Vaughan の Theorem 9.6 として挙げた。定理番号を私は確かめていない。着手前の盲検は PSU の講義ノート Thm 4.2 で積公式を確かめた）を繰り返したもの、形 (II) と ∞ の因子は、上の条件のもとで Tate の局所定数の積公式の GL(1)/ℚ の場合です（同定は確信度：中〜高、盲検の申告のまま）。新規候補はありません。
 
 ## 0. 内容
@@ -62,7 +63,8 @@
 | ガウス和の分解（漸化式） | `gaussSum_listChar` | (1)（689 組） | 既知 |
 | 交差項の形 (I)・(II) | `cross_eq_formI`・`cross_eq_formII` | (2)・(3) | 既知 |
-| W の形 (I)・(II) | `rootNum_listChar_formI`・`rootNum_listChar_formII` | (4) | 既知（再導出） |
+| W の形 (I)・(II) | `rootNum_listChar_formI`・`rootNum_listChar_formII` | (4)（形 (II)）。形 (I) は (2)・(4) から | 既知（再導出） |
 | ∞ の因子の符号、W の符号つきの形 | `parFac_listChar`・`rootNum_listChar` | (5) | 既知（再導出） |
-| 原始性 ⇔、phaseA1 の形 | `isPrimitive_listChar_iff`・`phaseA1_listChar` | (7) | 既知 |
+| 原始性 ⇔ | `isPrimitive_listChar_iff` | (7) | 既知 |
+| phaseA1 の形（成分がすべて原始） | `phaseA1_listChar` | 数値の項目なし（`rootNum_listChar` からの帰結） | 既知 |
 | 分解の存在と一意性 | `exists_listChar`・`listChar_injective` | (8) | 既知 |
 | すべての素数への分解 | `gaussSum_primeFactors`（`pairwise_primeFactors`・`lvl_primeFactors`） | 着手前の (1)(2) | 既知 |
@@ -73,7 +75,7 @@
 | 対照群 F_q[t] | Lean にしていない | 着手前の (8) | 既知 |
 
-- **文の重み。** 中身があるのは `gaussSum_listChar`（帰納法で Part 189 の `gaussSum_mul_coprime` を繰り返す）、`cross_eq_formI`・`cross_eq_formII`（並べ替えの組み合わせ）、`parFac_listChar`（符号の数え上げ）、`exists_listChar`（Part 190 の `decomp` の繰り返し）、`gaussSum_primeFactors`（法の型の受け渡し）です。ほかは補助（`lvl_cons`・`lvl_eq_prod`・`coprime_lvl`・`sqrt_lvl`・`prod_map_div'`・`not_odd_of_even`・`tri_succ`・`listChar_congr`）か、上からの短い帰結です。
+- **文の重み。** 中身があるのは `gaussSum_listChar`（帰納法で Part 189 の `gaussSum_mul_coprime` を繰り返す）、`cross_eq_formI`・`cross_eq_formII`（並べ替えの組み合わせ）、`parFac_listChar`（符号の数え上げ）、`exists_listChar`（Part 190 の `decomp` の繰り返し）、`gaussSum_primeFactors`（法の型の受け渡し）です。ほかは補助（`lvl_cons`・`lvl_eq_prod`・`coprime_lvl`・`sqrt_lvl`・`prod_map_div'`・`tri_succ`・`listChar_congr`）か、上からの短い帰結です。
 
-## 2. 数値照合（step280.py、11 項目すべて合格、1 回目で通った）
+## 2. 数値照合（step280.py、11 項目すべて合格、1 回目で通った。照合の後に (7) の文言だけ直して再実行、結果は同じ）
 
 - 19 の法の並び（素数冪でない法、法 1 の成分、成分 1 つ、4 つを含む）で 689 組の指標。誤差は最大 9.1×10⁻¹⁴。
@@ -94,5 +96,6 @@
   - 使っていない section 変数の警告（`omit hN in` を付けた）。
 - 内部照合の 1 回目で、下書きの 2 つの宣言が前の鎖と同じ文だと分かり、消しました（§7）。
-- sorry 0、警告 0、`#print axioms` 26 行（定理と同数）。鎖全体（PAG.lean〜PAG261.lean）は theorem/lemma 3,551（Part 256 の後の 3,525 に 26 を足した数）。
+- 照合者 B の後に、Mathlib の `DirichletCharacter.Even.not_odd` と同じ文だった補助 `not_odd_of_even` を消しました（ほかの文は変えていない。組み立て直して rc = 0）。
+- sorry 0、警告 0、`#print axioms` 25 行（定理と同数）。鎖全体（PAG.lean〜PAG261.lean）は theorem/lemma 3,550（Part 256 の後の 3,525 に 25 を足した数）。
 
 ## 4. 残る問い（本来の道）
@@ -118,12 +121,30 @@
 
 - **着手の前。** xlsx の「定理と証明」を言葉で検索し（「素数冪ごと」「局所因子」「局所定数」「すべての素点」など）、Lean の全宣言の文を正規表現で検索しました（ガウス和と ∏、primeFactors、zN と ∏ など）。成分 2 つの式は前の鎖にありました（Part 189 の `gaussSum_mul_coprime`・`z_mul_coprime`、Part 256 の `rootNum_prodChar`）。任意個の成分の明示の積、形 (II)、符号 (−1)^{k(k−1)/2} の文は見つかりませんでした（網羅ではない）。近いもの：Part 192 の `z_hall`（ホール成分 2 つ、ずれは「1 の冪根がある」の形）、Part 193 の `LocalCrit`・`prod_root_iff_local`（平方因子のない素数成分での、1 の冪根になる条件）、Part 127 以降の素数冪の成分の積 ∏ τ(χ_i)/√ の位数の定理（合成した指標の τ ではない）。
-- **閉じる前（1 回目）。** 全宣言を書き出し（4313 件、`audit257/internal/Extract3.lean`）、PAG261 の 34 件それぞれに候補を上位 20 まで選び（`shortlist261.py`）、`#dupcheck`・`#defeqcheck` を両向きに 1230 回（`Dup261_round1.out`）。一致は 2 組：
+- **閉じる前（1 回目）。** 全宣言を書き出し（4313 件、`audit257/internal/Extract3.lean`）、PAG261 の 34 件それぞれに候補を上位 20 まで選び（`shortlist261.py`）、`#dupcheck`・`#defeqcheck` を両向きに 1230 回（`Dup261_round1.out`）。一致は 2 組（消したのは 3 件。下の 2 つと、instance のために置いた定義 `ppow`）：
   - 下書きの `gaussSum_level_one`（法 1 の指標のガウス和は 1）は、Part 199（PAG203）の同名の定理と同じ文（両向き）。
   - 下書きの instance `ppow_neZero`（p^{v_p(n)} ≠ 0）は、Part 236（PAG240）の `neZero_ordProj` と同じ文（両向き）。Part 236 には別の `ppow`（値は ℕ+）もある。
   - 2 つとも消して、前の鎖のものを使いました。
 - **閉じる前（2 回目）。** 直した後に同じ手順（4310 件、PAG261 の 31 件、1132 回）。一致は 0。
-- 限界：候補選びは型に現れる定数の近さで上位 20 までで、名前や形の違う同じ概念は拾いにくい。「見つからなかった」は「ない」の証明ではありません（確信度：中）。
+- **照合者 B の指摘（§8）。** 補助の `not_odd_of_even` は Mathlib の `DirichletCharacter.Even.not_odd` と同じ文でした（この手順は前の鎖だけを探し、Mathlib は探していない）。消して Mathlib のものを使いました。`prod_map_div'` は、Mathlib の List 版が見つからなかったので残しました（Multiset 版はある）。
+- **前の鎖の中の重複定義（記録）。** Part 256 の `prodChar` と Part 232 の `charMul`（と Part 195 の `cmul`）は同じ定義です（内部照合の監査で記録済み、`pag2_internal_audit_249_256.md`）。`listChar_injective` はこの一致を使って `charMul_injective` を当てています。
+- 限界：候補選びは型に現れる定数の近さで上位 20 までで、名前や形の違う同じ概念は拾いにくい。Mathlib との重複は探していない。「見つからなかった」は「ない」の証明ではありません（確信度：中）。
 
-## 8. 独立照合
+## 8. 独立照合（2026-11-14 夜）
 
-（照合の後に書く）
+- 照合者 B（新しいエージェント、`audit257/inbox_B/inbox.md` の Read だけ、ツール 2 回、約 160 秒）。入力は PAG261.lean の全文と .out、使った前の鎖の宣言の形式文の全文、このノートの全文（照合の前の版）、着手前の文書の §2・§6・§12、step280 のログ。予想は先に書いた（`audit257/expected_before_review.md`）。出力はそのまま `audit257/outputs/B_output.md`。
+- **形式文：すべて偽・空虚・別物なし、仮定も過大ではない**（B の判定）。Nodup は `rootNum_listChar_formI/II` では外せるはず（手計算、Lean では未確認）。
+- **文面の指摘と直したこと（14 件）。**
+  - Lean の題に解釈の言葉「局所因子」が入っていた → 形式文の言葉（成分の τ・W の積と、交差項・符号）に直した。ノートの題の「すべての成分の因子の積に分かれる」も同じく直した（交差項と大域の符号が残るため）。
+  - 局所定数との一致の文から、条件（原始、素数冪の成分、ω の正規化）が落ちていた → 条件を書き、原始でない成分では言えない例（法 p の自明な指標）を書いた。
+  - `isPrimitive_listChar_iff` の docstring が、使っていない `isPrimitive_mul` を挙げていた → 消した。
+  - U の固有値（phaseA1）と W の混同 → 書き分けた（W の式は原始でない指標でも成り立つ恒等式、U の固有値になるのは原始のとき）。
+  - 問いの後半（各点の因子はその点だけで決まるか）に答えていない → 負の答えを書いた（形 (II) の因子はほかの成分の値 χ_j(N_i) に依存する）。
+  - 「Tate の局所定数」の同定の確信度「高」は根拠を越える → Lean 化の部分は高、同定は中〜高に分けた。
+  - Montgomery–Vaughan の定理番号を確かめた記録がない → 確かめていないことを書いた。
+  - 検証表：phaseA1 に数値の項目がない、W の形 (I) の直接の項目がない、(7) のログの古い文言 → 表を直し、step280 の (7) の文言を直して再実行した（結果は同じ）。
+  - 「成分 2 つでは `rootNum_prodChar` と同じ式」に法 N_a·(N_b·1) を添えた。範囲に「成分の一意性は listChar の形でだけ」を書いた。
+  - 内部照合の件数の差（34 → 31 で、説明は 2 件）→ 3 件目は定義 `ppow` だったことを書いた。
+  - 着手前の文書 §6 の「Part 183・194」→ 確かめた結果、正しい（Part 183 の `single_root_iff` は PAG187、Part 194 の `real_reciprocity` は PAG198）。直していない。
+- **内部照合の指摘。** Part 256 の `prodChar` と Part 232 の `charMul` の重複定義を記録すべき → §7 に書いた（監査で記録済み）。`not_odd_of_even`・`prod_map_div'` の Mathlib との重複は B は確かめていない → こちらで確かめ、前者を消した（§7）。
+- **数値照合との対応。** (1)〜(6)・(8)・(9)・(11) は Lean の文と対応、件数と誤差はログと一致（B の確認）。
+- 直した後の照合は受けていません（記録だけの直しと、補助 1 つの削除）。
```

# C. 直した後の PAG261.lean（全文）
```lean
/-
アーデル射影幾何 — Part 257（PAG 2.0）：互いに素な法の並びの指標の積での、ガウス和と W の分解（成分の τ・W の積と、交差項・符号）

問いの出所：著者の選択（2026-11-14 20:59、着手前の文書 `pag2_part257_preregistration.md` の候補 P1）。開始条件 2（方向βの
登録ファイルとの突き合わせ）は、著者の判断で保留のまま始めた（登録ファイルは届いていない）。
幾何の言葉での問い（読み）：大域の貼り合わせ（U の固有値 phaseA1。原始の指標では W = rootNum）は、∞ を含む各点の局所の因子の積に
分かれるか。各点の因子は、どこまでその点だけで決まるか。
Lean が答えるのは、互いに素な法の並び N_1, …, N_k の指標の積（法 N_1·…·N_k）の上での、ガウス和 τ と W の式まで。

読みの言葉：「貼り合わせ U」「公準 A1 の位相」は Part 254（PAG258.lean）の `UA1`・`phaseA1`。W は Part 252（PAG256.lean）の
`rootNum`（= τ(χ)/(i^a·√n)。原始のときルート数）、偶奇の因子 `parFac`（偶で 1、奇で −i）。「素点」「局所因子」「重なり」は
著者の解釈の層の言葉で、Lean の文には出てこない。偶奇の因子が無限素点の局所因子にあたる、も読み。

Lean の文（すべて既知の事実の Lean 化。互いに素な法でのガウス和の乗法性を繰り返したものと、そのルート数版）：
1. 法の並びの積 `lvl`（先頭 × 残り）と指標の積 `listChar`（先頭の指標と残りの積を Part 256 の `prodChar` でつなぐ）。
   値は成分の値の積（`listChar_natCast`：自然数で、`listChar_neg_one`：−1 で）。
2. ガウス和：τ(listChar χ l) = 交差項·∏_i τ(χ_i)（`gaussSum_listChar`。法は互いに素。原始性は要らない）。交差項 `cross` は
   漸化式で定め、閉じた形が 2 つ：形 (I) ∏_i χ_i(∏_{j≠i} N_j)（`cross_eq_formI`）と形 (II) ∏_i ∏_{j≠i} χ_j(N_i)
   （`cross_eq_formII`。成分 i の因子を、ほかの成分を N_i で読んだ値で書く形）。
3. W：W(listChar χ l) = ε_∞·∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)/√N_i（`rootNum_listChar_formI`）、
   = ε_∞·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)（`rootNum_listChar_formII`）。ε_∞ = `parFac`(listChar χ l)。
4. ∞ の因子の符号：ε_∞(listChar χ l) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数 `oddCount`。`parFac_listChar`）。
   したがって W(listChar χ l) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（`rootNum_listChar`。成分 2 つでは、法 N_a·(N_b·1) の上で
   Part 256 の `rootNum_prodChar` と同じ式になる。Lean ではつないでいない）。
5. 原始性：すべての成分が原始 ⇔ 積が原始（`isPrimitive_listChar_iff`）。原始なら UA1 の固有値 phaseA1 も同じ式
   （`phaseA1_listChar`）。
6. 分解：法 lvl l の指標は、どれも成分の積 listChar χ l の形に書け（`exists_listChar`。並びに重複なし）、成分は一意
   （`listChar_injective`。Part 256 の `prodChar` が Part 232 の `charMul` と同じ定義であることを使って、`charMul_injective` を当てる）。
7. すべての素数への分解：法 n の指標 Ψ は、素数冪の法 p^{v_p(n)}（0 でないことは Part 236（PAG240）の instance `neZero_ordProj`）の成分 χ_p で、自然数での値が ∏_p χ_p(x)、
   τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)})（`gaussSum_primeFactors`。形 (II)）。退化例（成分 1 つ）は τ(listChar χ [a]) = τ(χ_a)
   （`gaussSum_listChar_singleton`）。

前の鎖の定理を使い、示し直していないもの：Part 199（PAG203）の `gaussSum_level_one`、Part 236（PAG240）の `neZero_ordProj`、Part 189（PAG193）の `gaussSum_mul_coprime`・`mul_changeLevel_apply`、
Part 190（PAG194）の `decomp`・`isPrimitive_iff`・`comp₁_mul`・`comp₂_mul`、Part 232（PAG236）の `charMul_injective`、
Part 252（PAG256）の `rootNum_eq`・`parFac_of_even`、Part 254（PAG258）の `phaseA1_of_isPrimitive`、Part 256（PAG260）の
`prodChar`・`prodChar_neg_one`・`parFac_prodChar`・`crossSign`。

言い方の注意：文献では、大域の ε 因子は局所の ε 因子の積（Tate、Deligne）。原始指標 χ を素数冪の成分 χ_p に分け、
χ に対応するイデール類指標 ω を ω_q(q) = χ(q)（不分岐な q）と正規化し、加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}
（Tate の学位論文の規約）にとると、形 (II) の p の因子 (τ(χ_p)/√p^{e_p})·∏_{q≠p} χ_q(p^{e_p}) は ω の p での局所定数と一致し、
∞ の局所定数は i^{−a}（着手前の盲検の問いテストと私の手計算。確信度 中〜高。Lean では示していない）。原始でない成分や、
素数冪でない法の成分では、この一致は言えない（例：法 p の自明な指標の因子は −1/√p）。ψ の規約を逆にすると各 p の因子が
χ_p(−1) 倍、∞ の因子が i^{a} になるが、積は変わらない。ω を χ̄ に対応させる規約では、積が W の共役になる（盲検の申告）。
問いの後半への答え（Lean の文から読めること）：形 (II) の成分 i の因子は χ_i だけでは決まらず、ほかの成分の N_i での値
χ_j(N_i)（j ≠ i）に依存する。∞ の因子 ε_∞ も合成した指標の偶奇で決まる 1 つの因子で、成分ごとには (−1)^{k(k−1)/2} だけずれる。A1 は公準のまま。ここでの文は τ・W・phaseA1 についての恒等式で、A1 から何かを出すものではない。

範囲：互いに素な法の並び（リスト）の上の式。法 n の任意の指標についての文は 7 のガウス和と成分の存在まで（W の形は、listChar の形の
指標の上で 3・4。成分の一意性は listChar の形でだけ言い（`listChar_injective`）、法 n の形では文にしていない）。Lean にしていないこと（数値は step280.py の項目番号）：イデール類指標と Tate の局所定数そのもの、
原始でない指標の phaseA1 を導手を割る素点だけで書く形（着手前の数値 (5)）、並べ替えで listChar の値が変わらないこと
（数値 (10)）、対照群 F_q[t]（∞ の因子は √q/τ(η)。盲検の答えで、私は計算していない）。

内部照合（2026-11-14 からの必須の手順）：着手の前に、xlsx の「定理と証明」と Lean の全宣言の文を検索した。成分 2 つの式は
前の鎖にある（Part 189 の `gaussSum_mul_coprime`・`z_mul_coprime`、Part 256 の `rootNum_prodChar`）。任意個の成分の明示の積、
形 (II)、符号 (−1)^{k(k−1)/2} の文は見つからなかった（網羅ではない）。近いもの：Part 192（PAG196）の `z_hall`（ホール成分 2 つ、
ずれは「1 の冪根がある」の形）、Part 193（PAG197）の `LocalCrit`・`prod_root_iff_local`（平方因子のない素数成分での、1 の冪根に
なる条件）、Part 127（PAG131）以降の素数冪の成分の積の位数の定理（積 ∏ τ(χ_i)/√ の位数で、合成した指標の τ ではない）。
閉じる前の照合（全宣言の書き出し、候補選び上位 20、`#dupcheck`・`#defeqcheck` を両向きに）：1 回目（4313 件、PAG261 の 34 件、
1230 回）で、下書きの `gaussSum_level_one` が Part 199（PAG203）の同名の定理と同じ文、法 p^{v_p(n)} が 0 でないことの instance
`ppow_neZero` が Part 236（PAG240）の `neZero_ordProj` と同じ文だった（どちらも Lean で両向きに確認）。この 2 つと、instance の
ために置いた定義 `ppow`（p^{v_p(n)}。Part 236 にも別の `ppow` がある）を消して前の鎖のものを使った。2 回目（4310 件、31 件、
1132 回）は一致 0。照合者 B の指摘で、下書きの `not_odd_of_even` も Mathlib の `DirichletCharacter.Even.not_odd` と同じ文なので
消した（Mathlib との重複はこの手順では探していない）。網羅ではない（候補選びは型に現れる定数の近さで、上位 20 まで）。
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

omit [DecidableEq ι] in
theorem listChar_neg_one_pow (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    listChar χ l (-1) = (-1) ^ oddCount χ l := by
  rw [listChar_neg_one]
  induction l with
  | nil => simp [oddCount]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, oddCount, ih, pow_add]
    rcases (χ a).even_or_odd with h | h
    · have hn := h.not_odd
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
    · have hn := h.not_odd
      simp only [hn, false_and, ↓reduceIte, zero_add]
      ring
    · simp only [h, true_and, ↓reduceIte, hodd]
      rw [tri_succ, pow_add]
      by_cases hk2 : _root_.Odd (oddCount χ l)
      · simp only [hk2, ↓reduceIte, hk2.neg_one_pow]; ring
      · simp only [hk2, ↓reduceIte, (Nat.not_odd_iff_even.mp hk2).neg_one_pow]; ring

omit [DecidableEq ι] in
/-- **W の分解（符号つき）**：W(χ) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（成分 2 つでは、法 N_a·(N_b·1) の上で Part 256 の `rootNum_prodChar` と同じ式。Lean ではつないでいない）。 -/
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
/-- 原始性：互いに素な法で、すべての成分が原始 ⇔ 積が原始（Part 190 の `isPrimitive_iff`・`comp₁_mul`・`comp₂_mul` を使う）。 -/
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
/-- 成分がすべて原始なら、UA1 の固有値 phaseA1 も同じ式で分かれる（原始でない指標では phaseA1 は W と違う）。 -/
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
# C2. PAG261.out
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
