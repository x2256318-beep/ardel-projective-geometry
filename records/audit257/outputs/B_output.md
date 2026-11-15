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
