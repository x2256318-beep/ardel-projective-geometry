# 統合照合 IV の入力：台帳 L17（統合照合 III-a・III-b の後の直し）（2026-11-25）
照合の対象：§4 の差分（コミット 7636624。照合者の出力ファイルと xlsx の実物は除く。xlsx の直しは差分の中のスクリプト `records/audit268/update_xlsx_268b.py`）。直しの根拠は §2 の III-a・III-b の出力。§3 は今の PAG268.lean の全文（形式文との突き合わせ用）。記録の文は後注の形で足す方針。この照合は停止規則の「もう1回だけ統合照合」に当たる。

## §1 台帳 L17
```markdown
### L17：統合照合 III-a・III-b の後の直し（2026-11-25 夜）

- 範囲：III-a（`records/audit268/outputs/integrated_IIIa_output.md`）と III-b（`integrated_IIIb_output.md`）の指摘を受けた直し。
  - PAG268.lean の冒頭の説明と `chiPt_not_compat` の docstring（形式文は変えていない。作り直してエラー・警告 0）：3 を「両立しない場合がある（証人 1 つ）」に、4 の続きの「したがって」の段を Lean の外の読みに分け、一致の条件を「原始指標」から「導手 > 1」に直した（主張の条件と量化の直し）、|S_0| = `sz p K 0`、N ∣ 2 の例外、M = 0 の確信度：中、W V W = U⁻¹。`#print axioms` を 4 定理に足した（14 行）。
  - PAG267.lean の冒頭の説明（コメントだけ）：「resL∘X = Uinf∘resL を満たす作用素 X」、M = 0 の 2 つの補題の名前。
  - Part 264 のノート（§2・§3・§6）、着手前の文書 `pag2_p1_lift_preregistration.md` の後注（§0 の c = 0 の誤り）、引き継ぎメモ（Part 264 の項、Part 263 の確かめる事項 4 の後注、「急がない」の出所、Part 254（PAG258））、xlsx（`records/audit268/update_xlsx_268b.py`）、辞書（§22 の `eqU`・`eqPt` の行を「同じ集合」から「対応する（C）」に、§22 のさらい方の式、§21 の文の同語反復、§20 の後注の出所）、Part 263 のノート（§3・§6 の言い方とパス、閉鎖の行の引用）。
  - 数値：`records/p1_lift/numeric/extchi_check.py`（新しい。奇素数冪 7 つの法の全指標で、chiPt と extChi が一致するのは導手 > 1 のときちょうど）、`retraction_check.py` の表示（無条件の「all checks passed」を直した）、`records/p1_tower/numeric/p1_tower_check.py` のコメント。
  - この台帳：L15・L16 を閉じた項目に移し、L17 を新設。閉じた L11・L12 と L15 の記載に後注。
- 直していないもの：III-b の低・極低の一部（L15 の「直していないもの」の 16:40 の条文の記載の古さ、xlsx の「手計算」の出所）。
- 自己申告（根拠にしない）：主張を強めた直しはない。条件の直し（原始指標 → 導手 > 1）は Lean の外の読みの範囲を正しくする直しで、Lean の外の文を 1 つ（chiPt = extChi、導手 > 1）明示した。
- 扱い：主張（条件・量化）を変える直しがあるので、停止規則の「もう1回だけ統合照合」を行う（統合照合 IV）。
```

## §2 根拠：統合照合 III-a・III-b の出力（全文）

### III-a
# 統合照合 III-a の出力（Part 264 の材料と台帳 L16、2026-11-25）

（照合者の最終報告の全文を写した。）

# 統合照合 III-a の報告：Part 264（PAG268）と台帳 L16

結論を先に書きます。形式文と食い違う文は、2 つの型の書き方に集中していました。

- **(A)** 「`extChi` と一致するのは原始的なとき」。正しい条件は「導手 > 1（主指標でない）」です。
- **(B)** 「原始的でない χ では両立しない」が、すべての χ について言う文として読めます。Lean にあるのは証人 1 つだけです。

どちらも数値で確かめました（詳細は 2・4）。

## 1. 独立照合（§4）の指摘ごとの状態

| 指摘 | 状態 | 根拠 |
|---|---|---|
| 4.1 主指標の `extChi` は 0 と ∞ でも 1、導手 > 1 では 0 | 直った | 冒頭「P¹(ℤ/N) の全点（0 と ∞ を含む）で 1」、ノート §3 |
| 4.4 `extChi` の定義が [NeZero N] を取るか | 直った（記載は正しいと見ます） | 「`extChi` の定義は [NeZero N] を引数に取らない」 |
| 4.4（続き）M = 0 で両立が崩れる | 一部 | 「M = 0 では両立が崩れる見込み」。照合者の確信度「中」が写されていません |
| 3. 1 ≤ K は冗長、1 ≤ c は外せない | 直った | 冒頭の注意の 3 項目、ノート §3・§6 |
| 4.5 ケットと `extChi` の一致の条件 | 直しが誤り | 「`extChi` と一致するのは χ が法 p^c で原始的なとき」。照合者の言い方を写したものですが、2 の (A) のとおり条件が狭すぎます |
| 4.7 `charU` の重複の可能性 | 直った（ただし、鎖を検索して確かめることはしていません） | 「`charU` は鎖に 1 つだけ（Part 257（PAG261）…）」 |
| 3. `chiPt_red_congr` の d₁ = d₂ | 直す必要なし | ノート §6「型のための仮定」 |
| 4.2・4.3・4.6・4.8（χ⁻¹ = χ̄、作用の向き、正規化、resE の範囲） | 直す必要なし | 問題の指摘ではなく所見です |

4.4 の補足：手元の Lean v4.36.0-rc1（Mathlib なし）で試しました。使われない section の instance は、def には入らず、theorem には自動で入りました。したがって `omit [NeZero N] in` があってもビルドが通るという記録と、注意の文は整合します。`extChi_eqPt` と `extChi_torus` の [NeZero N] は、証明で `pullL_charU (N := χ.conductor)` を経由して使われるので、警告 0 とも矛盾しません。

## 2. 形式文と食い違う文・形式文より強い文

### (A) 一致の条件（中〜高）

対象の文は次の 3 つです。

- 冒頭の注意「`extChi` と一致するのは χ が法 p^c で原始的なとき」
- 冒頭 4 の続き「原始指標なら規格化の定数倍で `extChi` そのもの」
- ノート §3「この読みは原始指標のときに限る」

法が素数冪 p^c で導手 f ≥ p のときは、法 p^c で単数であることと法 f で単数であることが同じです。そのため、`chiPt χ` = `chiPt χ*` ∘ red が恒等的に成り立ちます。一致しないのは導手 1（主指標）のときだけです。

数値で確かめた範囲は法 9・25・27 の全指標です。導手 1 だけが「DIFF」で、導手 3・9・5 などの原始的でない指標でもすべて一致しました（`/tmp/indep_int268_IIIa/chk.py`）。

### (B) 両立しない、の読み方（中）

対象の文は次の 4 つです。

- 冒頭 3「原始的でない χ では引き戻しと両立しない」
- `chiPt_not_compat` の docstring
- xlsx の行と引き継ぎメモの同じ文
- ノート §2 の 3

形式文 `chiPt_not_compat` は、法 1 → 2、点 0 の証人 1 つだけです。全称の文として読むと偽になります。

- 反例：法 3 のルジャンドル記号を法 9 に上げた指標は原始的ではありませんが、両立します（不一致の点は 0）。
- 逆向き：原始指標を法 6 に上げると、両立しない点が 4 つあります。

崩れるかどうかを決めるのは、新しい素数が増えるかどうかです。

### (C) 「したがって」の文に Lean の外の段がある（中）

冒頭 4 の続き「したがって、…殻 0 のケットは…`extChi` と同じ形の関数」は、`ketS_proj_zero_eq` から直接は出ません。間に次の 2 段が要りますが、どちらも Lean にありません。

- 原始的な χ（または導手 > 1）で `extChi χ = chiPt χ` であること
- 法 p^K に上げた指標に `extChi_changeLevel` を当てること

### 主定理 3 つの言い方

- **`extChi_changeLevel`**：散文は形式文と合っています（[NeZero M] も含む）。
- **`extChi_torus`**：散文は形式文と合っています。
- **`ketS_proj_zero_eq`**：「|S_0|^(−1/2)」は形式文の `sz p K 0` = φ(p^K) の読み替えです。一度だけ「|S_0| = `sz p K 0`」と書くのが望ましいです（極低）。上の (A)・(C) を除けば合っています。

### 着手前の文書 §0（中〜低）

「c = 0 では…殻 0 のケットは単数の点の指示関数」は誤りです。`ket0_apply` によると、c = 0 では南のチャートの全点（0 を含む）で定数になります。0 になるのは、北のチャートの単数でない点だけです。ノート §3 と照合者の反例（[0:1] ↦ 1）の側が正しいです。

## 3. 盲検の出力から引いた読み・地位・確信度

- **冒頭 Lean の外 2 項目**：「トーラスと両立するものはない」は、盲検の出力の例外「（N | 2 の場合を除く）」を落としています（低）。
- **ノート §3・着手前 §3「W V W = V⁻¹」が強制される**：盲検の出力が強制とするのは「E の上では W V W = U⁻¹」です。WVW = V⁻¹ は、層別の持ち上げに課した条件です（低）。
- **ノート §3・引き継ぎメモの対照群**：「ℚ に固有の算術は運ばない」が確信度なしで断定になっています。盲検の確信度は「中〜高」です（低）。冒頭の説明は「見込み」と書いているので問題ありません。
- **冒頭 4 の続き**：(C) のとおり、Lean の外の段を含むのに主な定理の中に置かれています。
- **日付・出所の名前**：19:13 の指示、`records/p1_lift/`、検索 3 回、Q3・Q5 の参照は、入力の中で互いに一致しています。

## 4. 数値スクリプト（§11）

- §11 は「出力」と題していますが、出力が載っていません。私が実行した結果は「compat failures: 0 / all checks passed」でした。
- 最後の「all checks passed」は `bad` の値によらず表示されます。両立を支えているのは前の行だけです。
- このスクリプトが支える文は、着手前の文書 §3 の最後の項（レトラクションの文：M ≤ 60、赤道で恒等、還元と両立、W と両立）だけです。規則（1 + x、(1 + y)⁻¹）は本文の記述と一致します。
- Part 264 の Lean の文（chiPt・extChi・ケット）を数値で照合したスクリプトは入力にありません。§4 のサイクルの「数値照合」が行われたかは確かめられませんでした。

## 5. 番号・名前・件数の整合

- **整合している**：
  - Part n（PAGm）の対応（Part 254 ↔ PAG258、Part 24 ↔ PAG28、Part 20 ↔ PAG24、Part 25 ↔ PAG29、Part 257 ↔ PAG261、Part 263 ↔ PAG267、Part 28 ↔ PAG32、Part 252 ↔ PAG256）
  - 定理 14
  - xlsx の行 3758〜3771（14 行）
  - 機械照合の対象 18 件（定理 14 ＋定義 4）
- **食い違い（低〜中）**：`#print axioms` は 14 定理のうち 10 にしかありません。`mul_inv_apply_unit`、`chiPt_mk`、`torus_eqPt`、`chiPt_red_congr` の 4 つが抜けています。ところが xlsx は 14 行すべてを「axioms 確認済み」とし、ノートも「#print axioms は標準の 3 つ」と書いています。
- **xlsx の `torus_eqPt` の行**：証明は rfl なのに、主な補題が `Units.val_mul` になっています（極低）。
- **台帳 L16 の範囲の漏れ（低〜中）**：
  - 引き継ぎメモの Part 264 の項は、照合の後の作業（「注意を書き足した（台帳 L16）」）に触れているので、照合の後に書かれた文です。それなのに L16 の範囲にありません。
  - xlsx の `ketS_proj_zero_eq` の行（c = 0 の括弧書き）と、ノート §2 の 4 が照合の後に変わったかどうかは、入力からは判別できませんでした。
- **確かめられなかったもの**：
  - 「全宣言 4409 件、候補の組 144、照合 256 回」
  - 「約 160 秒」
  - `charU` が鎖に 1 つだけであること

## 6. 直すべき点（重要度順）

1. **高**：(A) を直す。冒頭の注意、冒頭 4 の続き、ノート §3 の条件を「導手 > 1（主指標でない）とき」に改めます。法が素数冪なので、単数の集合が法 p^c と法 f で同じであることを理由として添え、Lean の外と明記します。
2. **中**：(B) を直す。冒頭 3、docstring、ノート §2、xlsx、引き継ぎメモを「原始的でない χ で両立しない場合がある（証人：法 1 → 2、点 0）」に改めます。docstring を変えるとビルドの作り直しが要ります。
3. **中**：(C) を直す。冒頭 4 の続きを Lean の外の読みとして分け、「`extChi χ = chiPt χ`（導手 > 1）は形式化していない」と添えます。
4. **中〜低**：抜けている 4 定理の `#print axioms` を足すか、xlsx の状態を直します。
5. **中〜低**：着手前の文書 §0 の c = 0 の記述を訂正します。原文を残す規律があるなら、後注として足します。
6. **低**：台帳 L16 に、引き継ぎメモの Part 264 の項と、照合の後に変えた xlsx の行（あれば）を足します。
7. **低**：盲検の出力の例外と確信度を写します（N | 2、M = 0 の確信度「中」、対照群の「中〜高」）。WVW の記述は「E の上で W V W = U⁻¹ が強制」に直します。
8. **極低**：xlsx の `torus_eqPt` の補題名を直し、|S_0| = `sz p K 0` を一度書きます。§11 に出力を載せ、無条件に出る「all checks passed」を直します。

この照合では台帳 L16 の直しを照らしたので、上の直しを入れたら、停止規則に従ってもう一度照合にかけてください。1〜3 は主張の範囲（条件・量化）に関わる直しです。

## ツールと読んだ範囲

- Read 3 回：`input_IIIa.md` の 1〜918 行（全文）。
- Bash 4 回：見出しの一覧、ツールの有無の確認、Lean の section 変数の挙動の試験、§11 の実行と自作の数値照合。いずれも `/tmp/indep_int268_IIIa/` の中で行いました。
- 計 7 回。ほかのファイルとウェブは使っていません。

### III-b
# 統合照合 III-b の出力（台帳 L15、2026-11-25）

（照合者の最終報告の全文を写した。行番号は入力 `records/audit268/integrated/input_IIIb.md` の行。）

# 統合照合 III-b 報告：台帳 L15（Part 263（PAG267）の統合照合 I-a・I-b の後の直しと、閉鎖の記録）

結論：高の指摘はありません。中は 4 件あります。
- (a) 辞書 §22 の新しい行が、PAG267 の冒頭の内部照合（C＝近い）より強い「同じ集合」を書いている。
- (b) 台帳 L15 の閉鎖の記録が、19:11 より前の作業を「19:11 の後」の項に置き、さらに入力に差分のない xlsx の LABEL の変更を範囲に挙げている。
- (c) 確かめる事項 4 の「I-a・I-b とも…形式文と食い違う散文もなかった」が、形式文が入力になかった I-b について強すぎる。この文は著者の判断の前提になった。
- (d) I-b 低 10（閉じた L11・L12 の「形式文より強い文の指摘はなかった」）が直っておらず、「直していないもの」にも挙がっていない。

Lean、xlsx、数値スクリプトは実行していません（入力に全体がなく、環境の外です）。

## 1. 根拠のある直しの状態

**I-a の指摘**

| 指摘 | 判定 | 根拠の引用 |
|---|---|---|
| 中 1　機械的な照合の件数 | 直った | I-a「全宣言 4391 件・対象 55 件・392→440 組・712 回」。55×8＝440、49×8＝392 で整合 |
| 中 2　L13 の範囲の漏れ | 直った（閉じた項目の後注で、517 行） | I-a「引き継ぎメモの Part 263 の項…新しい docstring」 |
| 中 3　「5 は障害の一つ」 | 直った（PAG267 の冒頭とノート §3） | I-a「`s∘Uinf∘resL + (id − s∘resL)` は resL と可換」 |
| 中 4　後注の「すべて Lean に入った」 | 直った | I-a「型の上で `Uinf : Lim → Lim` であることだけ」 |
| 低 5　xlsx の「Lean の外」 | 直った（スクリプト上。xlsx の実物は未確認） | 1 つ目には、I-a の案にない「手計算」が加わっている（極低） |
| 低 6　「すべての定理」 | 直った | I-a「足した 4 定理には、独立照合の証人はありません」 |
| 低 7　`WL` と `Uinf` | 直った（ノート §6 と冒頭の説明） | ― |
| 低 8　Part 番号の併記 | 一部 | 引き継ぎメモの名指しされた 2 か所と xlsx は直った。引き継ぎメモ 390 行の「（Part 254 の Lim）」とノート §3 の「`Uinf`（Part 254）」は、併記がないまま |
| 低 9　LABEL・引き継ぎメモの但し書き | 直った（引き継ぎメモ。xlsx はスクリプト上） | ― |
| 極低 10　M = 0 | 直った | ただし「素因数の条件のある 2 つ」に名前がなく、4 つの中のどれかが曖昧（極低） |
| 極低 11　死んだ assert | 直った | 新しい検査は法 M の `canon` を使わず、`canon` のスカラー倍に対する整合だけを見る弱い検査。「出力は変わらない」は確かめられなかった |
| 極低 12　行番号 | 直していない（台帳に明記） | ― |

**I-b の指摘**

| 指摘 | 判定 | 根拠の引用 |
|---|---|---|
| 中 1　R4 の後注 | 直った | 台帳 3 か所（554・564・573 行）、ノート 2 か所（447・448 行）、引き継ぎメモ 2 か所（379・380 行）。数は台帳の申告と一致 |
| 中 2　辞書 §20 の F_p | 直った（出所の書き方に低の問題。2 節） | I-b「χ₁ が原始的でなく χ₁χ₂ が原始的な組では、不一致は 0」と整合 |
| 中 3　推薦案・索引の番号 | 直った | 名前で書き、ノート §4 の番号を添えた |
| 中 4　16:40 の条文 | 直った（コミット c7f2796 の条文を引いた） | 逐語かどうかは入力の中で確かめられない |
| 低 5　L11 の注 | 直った（555 行） | ― |
| 低 6　閉鎖の行のラベル | 直った（380 行の末尾） | ― |
| 低 7　「どれも後注の形」 | 直った（517 行） | ― |
| 低 8　「直していないもの」 | 直った | ただし L14 ではなく L15 の欄に入れた |
| 低 9　L14 の範囲 | 直った（517 行） | ― |
| 低 10　II-b の突き合わせ | **直っていない** | 新しい 516 行は I-b について書いた文。I-b が指したのは閉じた L11・L12 の行（546 行「形式文より強い文の指摘はなかった」）で、変わっていない |
| 低 11　扱いの理由 | 一部 | 後段の「主張を変えた直し（F_p の範囲、`fC`）があるか」は書かれていない |
| 低 12 | 直していない（台帳に明記） | ― |
| 低 13 | 一部 | 「この構築側のセッションの会話」までで、日時と場所は特定されていない。鉤括弧の指し方は直った |
| 極低 14・15 | 直った | 15 の結果は「インスタンス（…）はインスタンスなので行にせず」という同語反復の文（極低） |
| 極低 16 | 直っていない | 新しく書いたノート §6 の 478 行でも「`integrated_Ib_output.md`」にパスがない |

## 2. 形式文・記録と食い違う文、より強い文

- **（中）辞書 §22 の `eqU`・`eqPt` の行**：「Part 19（PAG23）の 2 チャートのモデルの赤道と同じ集合」と書いている。
  - PAG267 の冒頭では、Part 23（PAG27）の `toProj`（素数冪の法）との関係は「近いもの（C）」に分類されている。
  - 索引によれば、2 チャートのモデルは P¹(ℤ/p^K) の上にある。PAG267 の `eqPt` は一般の N の P¹(ℤ/N) の上にある。
  - 法の範囲も型も違うので、「同じ集合」は内部照合の判定より強い。根拠の欄も「―」で空。
- **（中）確かめる事項 4（400 行）**：「I-a・I-b とも高はなく、形式文と食い違う散文もなかった」とある。I-b は形式文が入力になく、突き合わせができなかった（I-b の冒頭、台帳 516 行）。著者がこの記載をもとに判断しているので、書き換えず後注で補う必要がある。
- **（低）引き継ぎメモ 395 行**：中の指摘を「記録と件数の側」と書いている。I-a の言い方は「**多くは**記録と件数の側」で、I-a の中 3 は読みの範囲の指摘だった。400 行の「記録・件数・範囲の書き方」とも合わない。
- **（低）辞書 §20 の後注の出所**：「（統合照合 I-b の照合者の数値…）」とあるが、I-b が計算したのは法 9・25・27 だけで、法 49 と「270 個中 8 個」は II-b の照合者の数値（I-b はこれを再現した）。
- **（低）中 3 の直しの括弧**：「（resL と可換な作用素）」の実質は resL∘X = Uinf∘resL（絡み合い）で、「可換」は粗い言い方。数学そのものは手で確かめ、正しかった（resL∘s = id から resL∘X = Uinf∘resL）。切断 s の存在は、resL の全射性（Lean）と線形代数（Lean の外）による。

## 3. 直しが足した主張

- 「5 が妨げるのは…だけで、`resL` の切断を使った持ち上げは妨げない」：I-a の手計算に支えられている。ただし範囲を狭めただけの直しではなく、持ち上げが存在するという肯定の主張を足している。台帳の自己申告「どちらも範囲を狭めた直し」は不正確（低）。
- 辞書 §22（新しい節）：新しい主張を含む。上の「同じ集合」は入力の記録で支えられない。`redU` の文献は、ノート §4 の盲検の申告と整合している。
- 16:40 の条文の逐語、コミット c7f2796、「この構築側のセッションの会話」：入力の中では確かめられない。
- 引き継ぎメモの「xlsx は final85（行 3724〜3757 を足した）」：34 行＝34 定理で、スクリプトの range(3724, 3758) と整合する。ただし台帳 L15 に書かれていない（4 節）。
- 著者の回答の対応づけ（「1、2」→確かめる事項 1・4）：構築側の報告の本文が入力にないので、確かめられない。

## 4. 地位・決定者・日付・判断の記録・台帳の範囲

- **（中）台帳 L15 の時系列**：コミット 2 は、「閉じた L13・L14 の記載に…書き足した」を「閉鎖の記録（2026-11-25 19:11 の後）」の項に移した。しかし書き足し（516・517 行）はコミット 1 にあり、19:11 の判断の前の作業である。元の位置（「この台帳」の項）に戻すのがよい。
- **（中）xlsx の LABEL の閉鎖の直し**：台帳は閉鎖の記録に「xlsx の LABEL」を挙げているが、入力にはそのスクリプトも差分もない（267b はラベルの「見込み」を直していない）。この変更は照合の入力に入っておらず、確かめられない。
- **L15 の範囲の漏れ（低）**：
  - 引き継ぎメモ 390 行の「辞書 §22。xlsx は final85」の追記。
  - 17:29 の項（381 行）の出所の書き換え。台帳は「会話の特定」を閉鎖の行だけに帰している。
- **「直していないもの」の食い違い（低）**：「16:40 の条文そのもの…は、著者に確かめる事項」とあるが、確かめる事項 1〜4 に条文そのものの項はない。条文は引き継ぎメモの後注に残したので、記載が古い。I-b が挙げた「L11・ノートの『CLAUDE.md §7』の参照先が今の条文にない」も挙がっていない。
- **判断の記録**：19:11 の判断の前の文は残され、扱いの行は「この行の後の文は判断の前の記載」として前置きの形にしてある。著者の判断の記録の書き換えは見当たらない。
  - R4・索引・推薦案の 2026-11-25 の後注は、その場で書き換えている。標示はあるが、前の文言は差分の外にしか残らない（極低）。著者の判断の記録ではない。
- **（低）ノート §6 の閉鎖の行**：「確かめる事項 4 への回答『良いです』」は部分の引用。著者の原文は「1、2 とも良いです」で、著者の言う番号は 2。
- **（低）引き継ぎメモの「（急がない）」**：誰の判断かの標示がない。
- 閉鎖の性質：止め方の規則の字義（「低・極低だけ」）は満たしておらず、閉鎖は著者の判断による。記録は「著者の判断による閉鎖」と書いていて、規則を満たしたとは書いていない（整合）。

## 5. Part と PAG の対応、参照、件数

- 対応は、照らしたものがすべて 4 のずれで一致した：263/267、258/262、254/258、24/28、23/27、19/23、21/25、25/29、262/266。
- 定理 34＝30＋4。xlsx は 34 行。機械的な照合の 440＝55×8、392＝49×8。
- Part 番号の併記の欠け（低）：引き継ぎメモ 390 行の「Part 254 の Lim」、ノート §3 の「`Uinf`（Part 254）」。
- 辞書 §22 のさらい方：§21 の grep の式（`inductive`・`class` を含む）を示さず、「def・abbrev・structure・instance」とだけ書いている。インスタンス 1 つの範囲が不明（低）。
- 所要時間（I-a 約 191 秒、I-b 約 188 秒）は、I-a・I-b の出力に記載がなく、確かめられなかった。

## 6. 直すべき点（重要度順）

**中**
1. 辞書 §22：「Part 19（PAG23）の…赤道と同じ集合」を「素数冪の法では、Part 19（PAG23）の 2 チャートのモデルの赤道に対応する（Part 23（PAG27）の `toProj` を通して。PAG267 の内部照合では C＝近い。Lean で結んでいない）」にする。
2. 確かめる事項 4 に後注を足す：「I-b は形式文が入力になく、形式文との突き合わせはできなかった（III-b の指摘）」。本文は書き換えない。
3. 台帳 L15：「閉じた L13・L14 の記載に…書き足した」を、19:11 の前の項に戻す。xlsx の LABEL の閉鎖の直しは、スクリプトか手作業かを書き、次の統合照合の入力に差分を含める。
4. 閉じた L11・L12（546 行）に、「II-b は形式文が入力になく、形式文との突き合わせはできなかった（I-b 低 10）」を後注で添える。

**低**
5. L15 の範囲に、引き継ぎメモ 390 行の「辞書 §22・final85」と 381 行の出所の直しを足す。
6. 「直していないもの」の「16:40 の条文そのもの」を、「条文は引き継ぎメモの後注に残した。CLAUDE.md の文面は変えていない。L11・ノートの §7 の参照先の問題は残る」にする。
7. 自己申告を「範囲を狭めた直しと、照合者の手計算による肯定の文（切断による持ち上げ）1 つ。辞書 §22 は新しい節」にする。
8. 395 行の「記録と件数の側」を「多くは記録と件数の側（I-a の 1 件は読みの範囲）」にする。
9. 辞書 §20 の後注の出所：「法 49 と 270 個中 8 個は II-b の照合者、I-b は法 9・25・27 で再現」とする。
10. ノート §6 の閉鎖の行を、「著者の回答『1、2 とも良いです』の 2（構築側の報告の番号。引き継ぎメモの確かめる事項 4 に当たる）」とする。「急がない」には判断者を書く。
11. 引き継ぎメモ 390 行とノート §3 の「Part 254」に（PAG258）を添える。
12. 辞書 §22 のさらい方に grep の式を書く。
13. 「（resL と可換な作用素）」を「（resL∘X = Uinf∘resL を満たす作用素）」にする。

**極低**
14. 「素因数の条件のある 2 つ」に `isUnit_of_castHom`・`exists_eqPt_of_red` の名前を入れる。
15. 「インスタンスはインスタンスなので行にせず」の同語反復を整える（例：「インスタンス（…）は行にせず、所属する定義の行に書いた」）。
16. ノート §6 の 478 行のパスに `records/audit267/outputs/` を付ける。
17. xlsx の「：Lean の外、手計算」の「手計算」の出所を書くか、外す。
18. 数値スクリプトの新しい検査が弱いこと（法 M の `canon` を使わない）を、コメントに書く。

**確かめられなかったこと**
- Lean の再構築（エラー・警告 0）。
- xlsx の実際のセルの値と、LABEL の閉鎖の直し。
- 数値スクリプトの全体と、出力が変わらないこと。
- 16:40・17:29・19:11 の著者のメッセージの原文と、構築側の報告での番号づけ。
- コミット c7f2796 の条文。
- I-a・I-b の所要時間。
- `mk_inv_eq` と Part 19（PAG23）のモデルの定義。

---
**使ったツールと読んだ範囲**：Bash 1 回（行数の確認と /tmp/indep_int268_IIIb/ の作成）と Read 4 回で、`input_IIIb.md` の 1〜740 行（全文）を読みました。ほかのファイルは読んでおらず、ウェブも計算スクリプトも使っていません。切断による持ち上げの式は手で確かめました。

## §3 今の PAG268.lean の全文
```lean
/-
アーデル射影幾何 — Part 264（PAG268、短期層の小さいノート、2026-11-25）：P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致

問いの出所：基礎文書の索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）と、Part 263（PAG267）で外に残った候補 C2（`Uinf` を P¹ の上の関数の極限に持ち上げる作用素）。
- 推薦案 `notes/pag2_p1_lift_preregistration.md` §4（C2-a）。2026-11-25 19:13 の著者の指示「お勧めで進めてください」を受けて、構築側が選んで着手した（CLAUDE.md §4 の選択の委任）。

記号：`chiPt χ`（法 N の指標 χ）は [a:b] ↦ χ(a)·χ⁻¹(b)。χ⁻¹(b) は単数 b では χ(b) の複素共役、単数でない b では 0。
`torus u` は [a:b] ↦ [u a : b]（u は単数）。`extChi χ` は、χ を誘導する原始指標 χ*（法は導手）の `chiPt` を、導手から法 N への還元で引き戻したもの。

主な定理：
1. `chiPt χ` は P¹(ℤ/N) の上で well-defined（定義）。赤道では χ（`chiPt_eqPt`）、反転 W で χ⁻¹ の関数に移り（`chiPt_Wproj`）、トーラスの作用で χ(u) 倍（`chiPt_torus`）。
2. `extChi χ` の赤道への制限は χ（`extChi_eqPt`、`resE_extChi`）。N ∣ M のとき、χ を法 M に上げた指標の `extChi` は、`extChi χ` の引き戻し（`extChi_changeLevel`、段の言葉で `pullP_extChi`）。トーラスの作用で χ(u) 倍（`extChi_torus`）。
3. 法 N の式 `chiPt χ` をそのまま使うと、原始的でない χ では引き戻しと両立しない場合がある（`chiPt_not_compat`：法 2 の自明な指標と点 0 の証人 1 つ。
   崩れるかどうかは新しい素数が増えるかどうかによる：法 3 の指標を法 9 に上げたものは原始的でないが両立する。統合照合 III-a の照合者の数値、Lean の外）。
4. p が素数で 1 ≤ c ≤ K のとき、Part 25（PAG29）の殻 0 の南ケット `ketS_proj K 0 c` は、法 p^c の `chiPt χ` の引き戻しの |S_0|^(−1/2) 倍（`ketS_proj_zero_eq`）。
   |S_0| = `sz p K 0` = φ(p^K)。
   読み（Lean の外）：素数冪の法では、導手が 1 でない（主指標でない）χ について、法 p^c で単数であることと導手の法で単数であることが同じなので
   `chiPt χ` = `extChi χ` が成り立ち、`extChi_changeLevel` と合わせて、殻 0 のケットは規格化の定数倍で法 p^K の `extChi` に一致する見込み
   （`extChi χ = chiPt χ` は形式化していない。統合照合 III-a の指摘で、条件を「原始指標」から「導手 > 1」に直し、この段を読みとして分けた）。

注意（独立照合の指摘）：
- 導手 1 の指標（主指標）の `extChi` は、法 1 の P¹ が 1 点で 0 も単数なので、P¹(ℤ/N) の全点（0 と ∞ を含む）で 1。導手 > 1 の指標の `extChi` は 0 と ∞ で 0。
- `extChi` の定義は [NeZero N] を引数に取らない（節の変数は使われたときだけ入る）。`extChi_changeLevel` は [NeZero M] だけを仮定する。M = 0 では両立が崩れる見込み（照合者の手計算、照合者の確信度：中、Lean の外）。
- 4 の 1 ≤ K は 1 ≤ c と c ≤ K から出る（`ketS_proj` の型の引数として置いた）。1 ≤ c は外せない（c = 0、p = 2、K = 1 の点 ∞ で 0 ≠ 1。照合者の手計算）。
- 4 の右辺は法 p^c の `chiPt χ` の引き戻し。`extChi` との一致は上の読み（導手 > 1 のとき、Lean の外）。主指標では一致しない（`extChi` は定数 1、ケットは 0 と ∞ の近くで 0）。

Lean の外（盲検の問いテスト `records/p1_lift/outputs/blind_output.md`、照合者の確信度つき）：
- 引き戻しと両立し赤道への制限が恒等な延長の族は多い（導手ごとのアフィン空間、確信度：高）。トーラスとも両立する族は一意で、`extChi` で与えられる（確信度：高、照合者の手の証明と数値）。
- レトラクション（点ごとの写像）の形の延長はあるが、トーラスと両立するものはない（N ∣ 2 を除く。点 0 がトーラスで固定されるため）。N によらない同次形式の比では書けない（確信度：高）。
- `Uinf` の持ち上げ（P¹ の上の関数の作用素で、制限すると `Uinf`、引き戻しと両立）は存在するが、ユニタリ・トーラス・W の条件を全部課しても一意でない（確信度：高、数値の反例）。局所性の条件を足すと一意（確信度：中〜高）。W とは可換にできない（赤道の上で W V W = U⁻¹ が強制される）。
- 答えは F_q[t] でも同じ形の見込み（対照群）で、ℚ に固有の算術は運ばない。

内部照合：Part 254（PAG258）の `pullL_charU`、Part 24（PAG28）の `projFun_south`・`projFun_north`、Part 20（PAG24）の `ket0_apply`・`chi_cast_inv`、Part 25（PAG29）の `projFun_ketS` を使った。
機械的な照合（全宣言 4409 件、対象 18 件、候補の組 144、照合 256 回）で一致なし（網羅ではない）。近いもの（C）：Part 28（PAG32）の `negProj`（トーラスの u = −1 の場合）、Part 252（PAG256）の `inv_apply_units_inv`（`mul_inv_apply_unit` の近く）。

ラベル（見込み、閉鎖で確定）：1〜4 は［再導出（小さい）］。新規候補なし。
-/
import PAG267
import PAG29

namespace PAG.Part268

open ZMod PAG.Part27 PAG.Part258 PAG.Part267 DirichletCharacter

/-! ## 1. P¹ の上の指標の関数 χ(a)·χ̄(b) -/

section chiPt

variable {N : ℕ}

theorem mul_inv_apply_unit (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1 := by
  rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]

/-- P¹(ℤ/N) の上の関数 [a:b] ↦ χ(a)·χ⁻¹(b)。 -/
noncomputable def chiPt (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
  Quotient.lift (fun v : Unimod N => χ v.1.1 * χ⁻¹ v.1.2) (fun v w ⟨u, h1, h2⟩ => by
    show χ v.1.1 * χ⁻¹ v.1.2 = χ w.1.1 * χ⁻¹ w.1.2
    rw [h1, h2, map_mul, map_mul]
    calc χ v.1.1 * χ⁻¹ v.1.2
        = (χ (u : ZMod N) * χ⁻¹ (u : ZMod N)) * (χ v.1.1 * χ⁻¹ v.1.2) := by
          rw [mul_inv_apply_unit, one_mul]
      _ = χ (u : ZMod N) * χ v.1.1 * (χ⁻¹ (u : ZMod N) * χ⁻¹ v.1.2) := by ring)

theorem chiPt_mk (χ : DirichletCharacter ℂ N) (v : Unimod N) :
    chiPt χ (mk v) = χ v.1.1 * χ⁻¹ v.1.2 := rfl

/-- 赤道では χ：χ(x)·χ⁻¹(1) = χ(x)。 -/
theorem chiPt_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : chiPt χ (eqPt x) = χ x := by
  show χ (x : ZMod N) * χ⁻¹ 1 = χ x
  rw [map_one, mul_one]

/-- 反転 W で χ⁻¹ の関数に移る。 -/
theorem chiPt_Wproj (χ : DirichletCharacter ℂ N) (q : ProjLine N) :
    chiPt χ (Wproj q) = chiPt χ⁻¹ q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show χ v.1.2 * χ⁻¹ v.1.1 = χ⁻¹ v.1.1 * χ⁻¹⁻¹ v.1.2
    rw [inv_inv, mul_comm]

/-- トーラスの作用の代表 (a, b) ↦ (u a, b)。 -/
def torusU (u : (ZMod N)ˣ) (v : Unimod N) : Unimod N :=
  ⟨((u : ZMod N) * v.1.1, v.1.2), by
    obtain ⟨s, t, h⟩ := v.2
    refine ⟨s * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), t, ?_⟩
    have hu : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := Units.inv_mul u
    linear_combination h + s * v.1.1 * hu⟩

/-- トーラスの作用 [a:b] ↦ [u a : b]。 -/
def torus (u : (ZMod N)ˣ) : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk (torusU u v)) (fun _v _w ⟨c, h1, h2⟩ =>
    mk_eq_mk c (by change (u : ZMod N) * _ = c * ((u : ZMod N) * _); rw [h1]; ring) h2)

/-- トーラスは赤道の上で掛け算：u·[x:1] = [u x : 1]。 -/
theorem torus_eqPt (u x : (ZMod N)ˣ) : torus u (eqPt x) = eqPt (u * x) := rfl

/-- χ(a)·χ̄(b) はトーラスの作用で χ(u) 倍。 -/
theorem chiPt_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
    chiPt χ (torus u q) = χ u * chiPt χ q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show χ ((u : ZMod N) * v.1.1) * χ⁻¹ v.1.2 = χ u * (χ v.1.1 * χ⁻¹ v.1.2)
    rw [map_mul, mul_assoc]

/-- 型の違う法の間の受け渡し：法が等しく整数での値が等しい 2 つの指標の関数は、還元の後で同じ。 -/
theorem chiPt_red_congr {d₁ d₂ M : ℕ} (hd : d₁ = d₂) (χ₁ : DirichletCharacter ℂ d₁)
    (χ₂ : DirichletCharacter ℂ d₂) (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) (h₁ : d₁ ∣ M) (h₂ : d₂ ∣ M)
    (q : ProjLine M) : chiPt χ₁ (red h₁ q) = chiPt χ₂ (red h₂ q) := by
  subst hd
  have : χ₁ = χ₂ := by
    refine MulChar.ext (fun u => ?_)
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod d₁)
    rw [← ha]
    exact hχ a
  subst this
  rfl

end chiPt

/-! ## 2. 原始指標の関数を引き戻した族 -/

section ext

variable {N : ℕ} [NeZero N]

/-- E_N(χ) = r^*(χ*(a)·χ̄*(b))（χ* は χ を誘導する原始指標、導手から法 N への還元で引き戻す）。 -/
noncomputable def extChi (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
  fun q => chiPt χ.primitiveCharacter (red χ.conductor_dvd_level q)

/-- 赤道への制限は χ。 -/
theorem extChi_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : extChi χ (eqPt x) = χ x := by
  show chiPt χ.primitiveCharacter (red χ.conductor_dvd_level (eqPt x)) = χ x
  rw [red_eqPt, chiPt_eqPt]
  have := congrFun (pullL_charU (N := χ.conductor) χ.conductor_dvd_level χ.primitiveCharacter) x
  rw [changeLevel_primitiveCharacter] at this
  exact this

omit [NeZero N] in
/-- 引き戻しとの両立：E_M(χ を法 M に上げたもの) = r^* E_N(χ)。 -/
theorem extChi_changeLevel {M : ℕ} [NeZero M] (h : N ∣ M) (χ : DirichletCharacter ℂ N)
    (q : ProjLine M) : extChi (changeLevel h χ) q = extChi χ (red h q) := by
  show chiPt (changeLevel h χ).primitiveCharacter (red (changeLevel h χ).conductor_dvd_level q) =
    chiPt χ.primitiveCharacter (red χ.conductor_dvd_level (red h q))
  rw [red_comp]
  exact chiPt_red_congr (conductor_changeLevel χ h) _ _ (primitiveCharacter_changeLevel_apply h χ)
    _ _ q

/-- トーラスとの両立：E_N(χ)(u·q) = χ(u)·E_N(χ)(q)。 -/
theorem extChi_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
    extChi χ (torus u q) = χ u * extChi χ q := by
  have hr : red χ.conductor_dvd_level (torus u q) =
      torus (unitsMap χ.conductor_dvd_level u) (red χ.conductor_dvd_level q) := by
    induction q using Quotient.inductionOn with
    | h v =>
      show mk (redU _ (torusU u v)) = mk (torusU _ (redU _ v))
      congr 1
      apply Subtype.ext
      show (castHom _ (ZMod χ.conductor) ((u : ZMod N) * v.1.1), castHom _ (ZMod χ.conductor) v.1.2) =
        (((unitsMap χ.conductor_dvd_level u : (ZMod χ.conductor)ˣ) : ZMod χ.conductor) *
          castHom _ (ZMod χ.conductor) v.1.1, castHom _ (ZMod χ.conductor) v.1.2)
      rw [map_mul]
      rfl
  show chiPt χ.primitiveCharacter (red _ (torus u q)) = χ u * chiPt χ.primitiveCharacter (red _ q)
  rw [hr, chiPt_torus]
  congr 1
  have := congrFun (pullL_charU (N := χ.conductor) χ.conductor_dvd_level χ.primitiveCharacter) u
  rw [changeLevel_primitiveCharacter] at this
  exact this

end ext

/-- 段の帰納系の言葉で：E は引き戻し `pullP` と両立する。 -/
theorem pullP_extChi (a b : Lvl) (h : a ≤ b) (χ : DirichletCharacter ℂ a.val) :
    pullP a b h (extChi χ) = extChi (changeLevel (n := a.val) (m := b.val) h χ) :=
  funext (fun q => (extChi_changeLevel (N := a.val) (M := b.val) h χ q).symm)

/-- E の赤道への制限は χ（Part 257 の `charU`）。 -/
theorem resE_extChi (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
    resE a (extChi χ) = PAG.Part257.charU χ :=
  funext (fun x => extChi_eqPt χ x)

/-! ## 3. 法 N の式をそのまま使うと両立しない（証人） -/

/-- 法 2 の自明な指標（導手 1）では、法 2 の式 χ(a)·χ⁻¹(b) は点 0 で 0、
法 1 の式を引き戻したものは 1。法 N の式 χ(a)χ̄(b) は、原始的でない χ では引き戻しと両立しない場合がある（証人 1 つ）。 -/
theorem chiPt_not_compat :
    chiPt (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) (zeroPt 2) ≠
      chiPt (1 : DirichletCharacter ℂ 1) (red (one_dvd 2) (zeroPt 2)) := by
  have h0 : ¬ IsUnit (0 : ZMod 2) := not_isUnit_zero
  show (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) 0 *
      (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1))⁻¹ 1 ≠
    (1 : DirichletCharacter ℂ 1) (castHom (one_dvd 2) (ZMod 1) 0) *
      (1 : DirichletCharacter ℂ 1)⁻¹ (castHom (one_dvd 2) (ZMod 1) 1)
  rw [MulChar.map_nonunit _ h0, zero_mul, map_one, inv_one]
  rw [MulChar.one_apply (isUnit_of_subsingleton _), MulChar.one_apply (isUnit_of_subsingleton _)]
  norm_num

/-! ## 4. 素数冪の法では Part 25（PAG29）の殻 0 のケット -/

section ket

variable {p : ℕ} [hp : Fact p.Prime]

/-- **殻 0 のケットとの一致**：1 ≤ c ≤ K のとき、P¹(ℤ/p^K) の殻 0 の南ケット `ketS_proj K 0 c`（Part 25（PAG29））は、
法 p^c の χ(a)·χ̄(b) の引き戻しの |S_0|^(−1/2) 倍。 -/
theorem ketS_proj_zero_eq (K c : ℕ) (hK : 1 ≤ K) (h : 0 + c ≤ K) (hc : 1 ≤ c)
    (χ : DirichletCharacter ℂ (p ^ c)) :
    PAG.Part29.ketS_proj K hK 0 c h χ = fun q =>
      (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
        chiPt χ (red (pow_dvd_pow p (by omega : c ≤ K)) q) := by
  apply (PAG.Part28.projFunEquiv K hK).injective
  apply Subtype.ext
  rw [PAG.Part29.projFun_ketS]
  refine Prod.ext (funext (fun x => ?_)) (funext (fun y => ?_))
  · rw [PAG.Part28.projFun_south]
    show PAG.Part21.ket K 0 c h χ x = (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
      (χ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) x) *
        χ⁻¹ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) 1))
    rw [PAG.Part24.ket0_apply, map_one, map_one, mul_one]
  · rw [PAG.Part28.projFun_north]
    show (PAG.Part23.extS (PAG.Part21.ket K 0 c h χ)).2 y = (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
      (χ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) 1) *
        χ⁻¹ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) y))
    rw [map_one, map_one, one_mul]
    unfold PAG.Part23.extS
    dsimp only
    split_ifs with hy
    · rw [PAG.Part24.ket0_apply, PAG.Part24.chi_cast_inv (by omega) χ hy]
    · have hy' : ¬ IsUnit (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) y) := by
        intro hu
        apply hy
        rw [castHom_apply, ZMod.cast_eq_val, ZMod.isUnit_iff_coprime,
          Nat.coprime_pow_right_iff (by omega)] at hu
        rw [← ZMod.natCast_zmod_val y, ZMod.isUnit_iff_coprime,
          Nat.coprime_pow_right_iff (by omega)]
        exact hu
      rw [MulChar.map_nonunit _ hy', mul_zero]

end ket

end PAG.Part268

#print axioms PAG.Part268.mul_inv_apply_unit
#print axioms PAG.Part268.chiPt_mk
#print axioms PAG.Part268.chiPt_eqPt
#print axioms PAG.Part268.chiPt_Wproj
#print axioms PAG.Part268.torus_eqPt
#print axioms PAG.Part268.chiPt_torus
#print axioms PAG.Part268.chiPt_red_congr
#print axioms PAG.Part268.extChi_eqPt
#print axioms PAG.Part268.extChi_changeLevel
#print axioms PAG.Part268.extChi_torus
#print axioms PAG.Part268.pullP_extChi
#print axioms PAG.Part268.resE_extChi
#print axioms PAG.Part268.chiPt_not_compat
#print axioms PAG.Part268.ketS_proj_zero_eq
```

## §4 差分
```diff
diff --git a/PAG267.lean b/PAG267.lean
index aec3588..3c1c155 100644
--- a/PAG267.lean
+++ b/PAG267.lean
@@ -31,9 +31,9 @@ Lean の外：
 - 極限 `LimP` が P¹(Ẑ) = ∏_p P¹(ℤ_p) の上の局所定数関数の空間と同一視できること、Ẑ^× が P¹(Ẑ) の中で閉だが開でないこと（盲検の照合者の記述）。
 - 読み：すべての素点を測る段では赤道が開集合でないので、局所定数関数の上の作用素として `Uinf` を赤道に閉じ込めることはできない。
   `Uinf` が作用するのは `resL` の行き先 `Lim` の側。`LimP` の上に `Uinf` を持ち上げる作用素（候補 C2）はこの文書の外。5 が妨げるのは各段の 0 延長による持ち上げだけで、
-  `resL` の切断を使った持ち上げ（resL と可換な作用素）は妨げない（統合照合 I-a の照合者の手計算、Lean の外）。`WL` と `Uinf` を結ぶ文はこの文書にない。
+  `resL` の切断を使った持ち上げ（resL∘X = Uinf∘resL を満たす作用素 X）は妨げない（統合照合 I-a の照合者の手計算、Lean の外）。`WL` と `Uinf` を結ぶ文はこの文書にない。
 - `red_surjective`・`exists_redU`・`isUnit_of_castHom`・`exists_eqPt_of_red` の M ≠ 0 は証明の都合で、外しても成り立つ見込み
-  （M = 0 では ℤ からの還元。素因数の条件のある 2 つでは M = 0 なら N = 0 で恒等。独立照合の手計算。Lean にしていない）。
+  （M = 0 では ℤ からの還元。素因数の条件のある `isUnit_of_castHom`・`exists_eqPt_of_red` では M = 0 なら N = 0 で恒等。独立照合の手計算。Lean にしていない）。
 - 0 延長との両立を整除の順序の共終な部分系の段だけに弱めても、5 の不存在は保たれる見込み（共終な部分系は素数を足す段を含む。独立照合の手計算。Lean にしていない）。
 - 5 の判定は数値でも確かめた（`records/p1_tower/numeric`：M ≤ 48 の 198 組すべてで、赤道の逆像が上の段の赤道と一致するのは M の素因数が N を割るときに限る）。
 
diff --git a/PAG268.lean b/PAG268.lean
index 6657740..30e284e 100644
--- a/PAG268.lean
+++ b/PAG268.lean
@@ -10,20 +10,24 @@
 主な定理：
 1. `chiPt χ` は P¹(ℤ/N) の上で well-defined（定義）。赤道では χ（`chiPt_eqPt`）、反転 W で χ⁻¹ の関数に移り（`chiPt_Wproj`）、トーラスの作用で χ(u) 倍（`chiPt_torus`）。
 2. `extChi χ` の赤道への制限は χ（`extChi_eqPt`、`resE_extChi`）。N ∣ M のとき、χ を法 M に上げた指標の `extChi` は、`extChi χ` の引き戻し（`extChi_changeLevel`、段の言葉で `pullP_extChi`）。トーラスの作用で χ(u) 倍（`extChi_torus`）。
-3. 法 N の式 `chiPt χ` をそのまま使うと、原始的でない χ では引き戻しと両立しない（`chiPt_not_compat`：法 2 の自明な指標と点 0）。
+3. 法 N の式 `chiPt χ` をそのまま使うと、原始的でない χ では引き戻しと両立しない場合がある（`chiPt_not_compat`：法 2 の自明な指標と点 0 の証人 1 つ。
+   崩れるかどうかは新しい素数が増えるかどうかによる：法 3 の指標を法 9 に上げたものは原始的でないが両立する。統合照合 III-a の照合者の数値、Lean の外）。
 4. p が素数で 1 ≤ c ≤ K のとき、Part 25（PAG29）の殻 0 の南ケット `ketS_proj K 0 c` は、法 p^c の `chiPt χ` の引き戻しの |S_0|^(−1/2) 倍（`ketS_proj_zero_eq`）。
-   したがって、2 チャートのモデル（Part 19〜25（PAG23〜PAG29））の殻 0 のケットは、素数冪の法では `extChi` と同じ形の関数（原始指標なら規格化の定数倍で `extChi` そのもの）。
+   |S_0| = `sz p K 0` = φ(p^K)。
+   読み（Lean の外）：素数冪の法では、導手が 1 でない（主指標でない）χ について、法 p^c で単数であることと導手の法で単数であることが同じなので
+   `chiPt χ` = `extChi χ` が成り立ち、`extChi_changeLevel` と合わせて、殻 0 のケットは規格化の定数倍で法 p^K の `extChi` に一致する見込み
+   （`extChi χ = chiPt χ` は形式化していない。統合照合 III-a の指摘で、条件を「原始指標」から「導手 > 1」に直し、この段を読みとして分けた）。
 
 注意（独立照合の指摘）：
 - 導手 1 の指標（主指標）の `extChi` は、法 1 の P¹ が 1 点で 0 も単数なので、P¹(ℤ/N) の全点（0 と ∞ を含む）で 1。導手 > 1 の指標の `extChi` は 0 と ∞ で 0。
-- `extChi` の定義は [NeZero N] を引数に取らない（節の変数は使われたときだけ入る）。`extChi_changeLevel` は [NeZero M] だけを仮定する。M = 0 では両立が崩れる見込み（照合者の手計算、Lean の外）。
+- `extChi` の定義は [NeZero N] を引数に取らない（節の変数は使われたときだけ入る）。`extChi_changeLevel` は [NeZero M] だけを仮定する。M = 0 では両立が崩れる見込み（照合者の手計算、照合者の確信度：中、Lean の外）。
 - 4 の 1 ≤ K は 1 ≤ c と c ≤ K から出る（`ketS_proj` の型の引数として置いた）。1 ≤ c は外せない（c = 0、p = 2、K = 1 の点 ∞ で 0 ≠ 1。照合者の手計算）。
-- 4 の右辺は法 p^c の `chiPt χ` の引き戻しで、`extChi` と一致するのは χ が法 p^c で原始的なとき。
+- 4 の右辺は法 p^c の `chiPt χ` の引き戻し。`extChi` との一致は上の読み（導手 > 1 のとき、Lean の外）。主指標では一致しない（`extChi` は定数 1、ケットは 0 と ∞ の近くで 0）。
 
 Lean の外（盲検の問いテスト `records/p1_lift/outputs/blind_output.md`、照合者の確信度つき）：
 - 引き戻しと両立し赤道への制限が恒等な延長の族は多い（導手ごとのアフィン空間、確信度：高）。トーラスとも両立する族は一意で、`extChi` で与えられる（確信度：高、照合者の手の証明と数値）。
-- レトラクション（点ごとの写像）の形の延長はあるが、トーラスと両立するものはない（点 0 がトーラスで固定されるため）。N によらない同次形式の比では書けない（確信度：高）。
-- `Uinf` の持ち上げ（P¹ の上の関数の作用素で、制限すると `Uinf`、引き戻しと両立）は存在するが、ユニタリ・トーラス・W の条件を全部課しても一意でない（確信度：高、数値の反例）。局所性の条件を足すと一意（確信度：中〜高）。W とは可換にできない。
+- レトラクション（点ごとの写像）の形の延長はあるが、トーラスと両立するものはない（N ∣ 2 を除く。点 0 がトーラスで固定されるため）。N によらない同次形式の比では書けない（確信度：高）。
+- `Uinf` の持ち上げ（P¹ の上の関数の作用素で、制限すると `Uinf`、引き戻しと両立）は存在するが、ユニタリ・トーラス・W の条件を全部課しても一意でない（確信度：高、数値の反例）。局所性の条件を足すと一意（確信度：中〜高）。W とは可換にできない（赤道の上で W V W = U⁻¹ が強制される）。
 - 答えは F_q[t] でも同じ形の見込み（対照群）で、ℚ に固有の算術は運ばない。
 
 内部照合：Part 254（PAG258）の `pullL_charU`、Part 24（PAG28）の `projFun_south`・`projFun_north`、Part 20（PAG24）の `ket0_apply`・`chi_cast_inv`、Part 25（PAG29）の `projFun_ketS` を使った。
@@ -178,7 +182,7 @@ theorem resE_extChi (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
 /-! ## 3. 法 N の式をそのまま使うと両立しない（証人） -/
 
 /-- 法 2 の自明な指標（導手 1）では、法 2 の式 χ(a)·χ⁻¹(b) は点 0 で 0、
-法 1 の式を引き戻したものは 1。法 N の式 χ(a)χ̄(b) は、原始的でない χ では引き戻しと両立しない。 -/
+法 1 の式を引き戻したものは 1。法 N の式 χ(a)χ̄(b) は、原始的でない χ では引き戻しと両立しない場合がある（証人 1 つ）。 -/
 theorem chiPt_not_compat :
     chiPt (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) (zeroPt 2) ≠
       chiPt (1 : DirichletCharacter ℂ 1) (red (one_dvd 2) (zeroPt 2)) := by
@@ -236,9 +240,13 @@ end ket
 
 end PAG.Part268
 
+#print axioms PAG.Part268.mul_inv_apply_unit
+#print axioms PAG.Part268.chiPt_mk
 #print axioms PAG.Part268.chiPt_eqPt
 #print axioms PAG.Part268.chiPt_Wproj
+#print axioms PAG.Part268.torus_eqPt
 #print axioms PAG.Part268.chiPt_torus
+#print axioms PAG.Part268.chiPt_red_congr
 #print axioms PAG.Part268.extChi_eqPt
 #print axioms PAG.Part268.extChi_changeLevel
 #print axioms PAG.Part268.extChi_torus
diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
index e674ac1..7826c42 100644
--- a/handoff/PAG2_handoff_part259.md
+++ b/handoff/PAG2_handoff_part259.md
@@ -1737,7 +1737,7 @@
   - 著者の確定（2026-11-20 17:46）：停止規則の「主張を変える直しがあれば、もう1回だけ統合照合を行い、その後はこの規則で閉じる」の一文を、この文で確定。CLAUDE.md（日英）の箇条に確定の時刻を書いた。
 - **Part 263（PAG267、短期層の小さいノート、2026-11-25）：P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限、赤道への制限と赤道からの 0 延長**：
   - 出所：基礎文書の索引の「射影」の空間の水準の問い（索引 1.4・2.4）。推薦案 `notes/pag2_p1_tower_preregistration.md` §4（盲検の指摘で改めた C1）を、2026-11-25 18:27 に著者が採用した（「進めてください」）。
-  - Lean：PAG267.lean、定理 34、sorry 0・警告 0、#print axioms は標準の 3 つ。還元の恒等・合成の法則・反転との可換・全射（M ≠ 0）、0 ≠ ∞（N ≠ 1）、引き戻しの帰納系と極限の上の対合 W_∞、赤道への制限が誘導する `resL : LimP → Lim`（Part 254 の Lim）の全射と resL ∘ W_∞ = invL ∘ resL、0 延長が引き戻しと可換 ⇔ 上の段の法の素因数がすべて下の段の法を割る（証人 (1, 2)）、0 延長は極限に降りない（各段の 0 延長と一致する線形写像がない。`resL` の切断の存在は否定しない）。ノート `notes/pag2_pag267_p1_tower.md`。辞書 §22。xlsx は final85（行 3724〜3757 を足した）。
+  - Lean：PAG267.lean、定理 34、sorry 0・警告 0、#print axioms は標準の 3 つ。還元の恒等・合成の法則・反転との可換・全射（M ≠ 0）、0 ≠ ∞（N ≠ 1）、引き戻しの帰納系と極限の上の対合 W_∞、赤道への制限が誘導する `resL : LimP → Lim`（Part 254（PAG258）の Lim）の全射と resL ∘ W_∞ = invL ∘ resL、0 延長が引き戻しと可換 ⇔ 上の段の法の素因数がすべて下の段の法を割る（証人 (1, 2)）、0 延長は極限に降りない（各段の 0 延長と一致する線形写像がない。`resL` の切断の存在は否定しない）。ノート `notes/pag2_pag267_p1_tower.md`。辞書 §22。xlsx は final85（行 3724〜3757 を足した）。
   - ラベル（2026-11-25 19:11 の閉鎖で確定）：1〜3 は［既知］、4・5 は［再導出（小さい）］、新規候補なし。兆候 4 は続く（Part 249〜263 で 15 パート連続）。
   - 内部照合：Part 258（PAG262）の `mem_ker_iff` と Part 24（PAG28）の `Wpull` を使った（言葉の検索）。機械的な照合 712 回で一致なし。`Wproj_eqPt` は Part 24（PAG28）の `mk_inv_eq` と同じ内容（B）。
   - 照合：独立照合（約 119 秒）。指摘で 4 定理を足した（台帳 L13）。同時に、台帳 L11・L12 と台帳に項目のなかった記録の追記を統合照合 II-a・II-b で照らした（L11・L12 は閉じた）。II-a に「高」1 件：R4 の指摘は「低〜中」2 件を含んでいたのに、記録は「低か極低だけ」と書いていた。直しは後注の形で入れた（台帳 L14）。L13・L14 は閉じるときの統合照合 I（I-a・I-b）で照らした。I-a・I-b とも高はなく、中がそれぞれ 4 件（記録と件数の側）。直しは台帳 L15。閉じるかどうかは著者に確かめる（下の 4）。
@@ -1745,15 +1745,15 @@
     1. 2026-11-20 16:40 の Part 262 の閉鎖の決定は、構築側の「R4 は低・極低だけ」という報告を前提にしていた可能性がある。実際の R4 の出力では、6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K。どちらも記録の側で、L11 で直した）が「低〜中」だった。この 2 件を知ったうえで閉鎖の決定を保つかどうか。
     2. CLAUDE.md §7 の「照合の後に直した文面は、そのパートを閉じる前に再照合する（2026-11-13）」と、止め方の規則（2026-11-20）の関係（止め方の規則が前者の例外であると明記するか）。リポジトリの CLAUDE.md は著者側の版の写しなので、構築側では文面を変えていない。
     3. CLAUDE.md §2 の Part 260 の「3 条件すべてが効く」と「`InLayer` が定義する関係そのもの」の文は著者側の版の写しで、構築側はこの写しのために Lean で確かめていない（II-b の指摘）。
-    4. Part 263 を閉じてよいか。独立照合の後に定理 4 つを足した（主張を足した直し）ので、停止規則の「もう1回だけ統合照合」として I-a・I-b を行った。I-a・I-b とも高はなく、形式文と食い違う散文もなかったが、中がそれぞれ 4 件あった（記録・件数・範囲の書き方）。その直しは台帳 L15 で、主張を強めた直しはない（範囲を狭めた直しが 2 つ）。止め方の規則の「その後はこの規則で閉じる」を、中の指摘が残っていても閉じてよいと読むか、もう 1 回照らすかは、構築側では決めずに著者に確かめる。構築側の推薦は、閉じて L15 を次のパートの統合照合に載せること（理由：形式文の側の指摘がなく、直しは範囲を狭める側だけで、照らすたびに記録の側のずれが生まれる型が L7 以来続いているため）。
+    4. Part 263 を閉じてよいか。独立照合の後に定理 4 つを足した（主張を足した直し）ので、停止規則の「もう1回だけ統合照合」として I-a・I-b を行った。I-a・I-b とも高はなく、形式文と食い違う散文もなかったが、中がそれぞれ 4 件あった（記録・件数・範囲の書き方）。（後注 2026-11-25、統合照合 III-b の指摘：I-b は形式文が入力になく、形式文との突き合わせはできなかった。「形式文と食い違う散文もなかった」は I-a についての文。）その直しは台帳 L15 で、主張を強めた直しはない（範囲を狭めた直しが 2 つ）。止め方の規則の「その後はこの規則で閉じる」を、中の指摘が残っていても閉じてよいと読むか、もう 1 回照らすかは、構築側では決めずに著者に確かめる。構築側の推薦は、閉じて L15 を次のパートの統合照合に載せること（理由：形式文の側の指摘がなく、直しは範囲を狭める側だけで、照らすたびに記録の側のずれが生まれる型が L7 以来続いているため）。
   - 著者の回答（2026-11-25 19:11）：「1、2 とも良いです」。
     - 1（構築側の報告では確かめる事項 1）：2026-11-20 16:40 の Part 262 の閉鎖の決定は、R4 の「低〜中」2 件を踏まえても保つ。
     - 2（確かめる事項 4）：Part 263 を閉じてよい。台帳 L15 は次のパートの統合照合に載せる。ラベル（1〜3 は［既知］、4・5 は［再導出（小さい）］、新規候補なし）はこの閉鎖で確定。
-    - 確かめる事項 2・3（CLAUDE.md §7 の 2 つの規則の関係、§2 の Part 260・`InLayer` の文）は今回の報告では問いにしておらず、開いたまま（急がない）。
+    - 確かめる事項 2・3（CLAUDE.md §7 の 2 つの規則の関係、§2 の Part 260・`InLayer` の文）は今回の報告では問いにしておらず、開いたまま（「急がない」は構築側の報告での言い方）。
 
 - **Part 264（PAG268、短期層の小さいノート、2026-11-25 夜）：P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致**：
   - 出所：索引 2.4 の留保と、Part 263 で外に残った候補 C2。著者の指示「お勧めで進めてください」（2026-11-25 19:13）を受けて、構築側が関門（着手前の 4 点 `notes/pag2_p1_lift_preregistration.md`、盲検の問いテスト `records/p1_lift/`、対照群、内部照合）を通した推薦案 C2-a を選び、着手した（CLAUDE.md §4 の選択の委任）。
   - 盲検の答え：引き戻しと両立する延長の族は多いが、トーラスとも両立する族は一意（χ*(a)χ̄*(b)）。U_∞ の持ち上げは存在するが、ユニタリ・トーラス・W の条件を全部課しても一意でない。答えは F_q[t] でも同じ形。残余は計算だけなので短期層。
-  - Lean：PAG268.lean、定理 14、sorry 0・警告 0。χ(a)χ̄(b) の well-defined 性と赤道・W・トーラス、原始指標の関数の引き戻し `extChi` の赤道での値・引き戻しとの両立・トーラス、法 N の式は原始的でない χ で両立しない（証人）、素数冪の法で殻 0 の南ケット（Part 25（PAG29））は χ(a)χ̄(b) の引き戻しの |S_0|^(−1/2) 倍（1 ≤ c）。ノート `notes/pag2_pag268_p1_char_extension.md`。辞書 §23。xlsx は final86（行 3758〜3771）。
+  - Lean：PAG268.lean、定理 14、sorry 0・警告 0。χ(a)χ̄(b) の well-defined 性と赤道・W・トーラス、原始指標の関数の引き戻し `extChi` の赤道での値・引き戻しとの両立・トーラス、法 N の式は原始的でない χ で両立しない場合がある（証人 1 つ）、素数冪の法で殻 0 の南ケット（Part 25（PAG29））は χ(a)χ̄(b) の引き戻しの |S_0|^(−1/2) 倍（1 ≤ c）。ノート `notes/pag2_pag268_p1_char_extension.md`。辞書 §23。xlsx は final86（行 3758〜3771）。
   - ラベル（見込み、閉鎖で確定）：［再導出（小さい）］、新規候補なし。兆候 4 は Part 249〜264 で 16 パート連続。
-  - 照合：独立照合（約 160 秒）。形式文は変えず、注意を書き足した（台帳 L16）。閉じるときの統合照合に、Part 263 の台帳 L15 と一緒に載せる。
+  - 照合：独立照合（約 160 秒）。形式文は変えず、注意を書き足した（台帳 L16）。統合照合 III-a（Part 264 と L16）・III-b（Part 263 の L15）で照らした。III-a に高 1 件（ケットと `extChi` の一致の条件は「導手 > 1」）、III-a・III-b に中が各 3〜4 件。直しは台帳 L17（条件と量化の直しを含むので、停止規則の「もう1回だけ統合照合」を行う）。
diff --git a/notes/pag2_p1_lift_preregistration.md b/notes/pag2_p1_lift_preregistration.md
index 6d72155..0979381 100644
--- a/notes/pag2_p1_lift_preregistration.md
+++ b/notes/pag2_p1_lift_preregistration.md
@@ -37,3 +37,5 @@
 4. 素数冪の法で、χ(a)χ̄(b)（c ≥ 1）の引き戻しは Part 25（PAG29）の殻 0 のケット `ketS_proj K 0 c` と一致する（Lean で結べなければ Lean の外に残す）。
 - Lean の外に残す見込み：トーラスと両立する族の一意性、持ち上げ V の存在と非一意性、局所性の条件による一意性、同次形式の比で書けないこと。
 - ラベルの見込み：1〜3 は［再導出（小さい）］、4 は［再導出（小さい）］。新規候補なし。兆候 4 は続く。
+
+（後注 2026-11-25 夜、統合照合 III-a の指摘：§0 の「c = 0 では殻 0 のケットは単数の点の指示関数」は誤り。`ket0_apply` によれば c = 0 では南のチャートの全点で定数で、0 になるのは北のチャートの単数でない点だけ（Part 264 のノート §3 の側が正しい）。§4 の 4 の結果は Part 264（PAG268）の `ketS_proj_zero_eq`。）
diff --git a/notes/pag2_pag267_p1_tower.md b/notes/pag2_pag267_p1_tower.md
index ac9ff9f..1a4ed9a 100644
--- a/notes/pag2_pag267_p1_tower.md
+++ b/notes/pag2_pag267_p1_tower.md
@@ -24,8 +24,8 @@
 
 - `LimP` は P¹(Ẑ) = ∏_p P¹(ℤ_p) の上の局所定数関数の空間と同一視できる（盲検の照合者の記述。Lean にしていない）。Ẑ^× は P¹(Ẑ) の中で閉だが開でない。
 - 5 はこの「開でない」の有限レベルの形：素数を足す段（b の素因数が a を割らない段）では、赤道の逆像が上の段の赤道より大きい。整除の順序の共終な部分系はどれも素数を足す段を含む。
-- したがって、すべての素点を測る段では、`Uinf`（Part 254）を局所定数関数の上の作用素として赤道に閉じ込めることはできない。`Uinf` が作用するのは `resL` の行き先 `Lim` の側。`LimP` の上に `Uinf` を持ち上げる作用素（候補 C2）はこの文書の外。5 が妨げるのは各段の 0 延長による持ち上げだけで、`resL` の切断を使った持ち上げ（resL と可換な作用素）は妨げない（統合照合 I-a の照合者の手計算、Lean の外）。これは索引 2.4 の留保の、空間の水準の理由の材料になる（留保そのものは埋まっていない）。
-- `red_surjective`・`exists_redU`・`isUnit_of_castHom`・`exists_eqPt_of_red` の M ≠ 0 は証明の都合で、外しても成り立つ見込み（M = 0 では ℤ からの還元。素因数の条件のある 2 つでは M = 0 なら N = 0 で恒等。独立照合の手計算。Lean にしていない）。
+- したがって、すべての素点を測る段では、`Uinf`（Part 254（PAG258））を局所定数関数の上の作用素として赤道に閉じ込めることはできない。`Uinf` が作用するのは `resL` の行き先 `Lim` の側。`LimP` の上に `Uinf` を持ち上げる作用素（候補 C2）はこの文書の外。5 が妨げるのは各段の 0 延長による持ち上げだけで、`resL` の切断を使った持ち上げ（resL∘X = Uinf∘resL を満たす作用素 X）は妨げない（統合照合 I-a の照合者の手計算、Lean の外）。これは索引 2.4 の留保の、空間の水準の理由の材料になる（留保そのものは埋まっていない）。
+- `red_surjective`・`exists_redU`・`isUnit_of_castHom`・`exists_eqPt_of_red` の M ≠ 0 は証明の都合で、外しても成り立つ見込み（M = 0 では ℤ からの還元。素因数の条件のある `isUnit_of_castHom`・`exists_eqPt_of_red` では M = 0 なら N = 0 で恒等。独立照合の手計算。Lean にしていない）。
 - 0 延長との両立を整除の順序の共終な部分系の段だけに弱めても、5 の不存在は保たれる見込み（独立照合の手計算。Lean にしていない）。
 - 数値：`records/p1_tower/numeric/p1_tower_check.py`（M ≤ 48 の N ∣ M の 198 組）。還元はすべて全射、|P¹(ℤ/M)| の公式はすべて一致、赤道の逆像が上の段の赤道と一致するのは M の素因数が N を割る組とちょうど同じ（5 と合う）。
 - 対照群：1〜5 は F_q[t] の法でも同じ形で成り立つ見込みで（盲検の照合者）、ℚ に固有の算術は運ばない。
@@ -51,9 +51,9 @@
 - 独立照合の指摘 4.7 の後半（`WL` と `Uinf` を結ぶ文がない）は扱っていない（候補 C2 の範囲）。
 - この直し（形式文の追加を含む）は、閉じるときの統合照合 I の入力に含めた（台帳 L13）。
 - 統合照合 I-a（2026-11-25 18:53〜、約 191 秒、`records/audit267/outputs/integrated_Ia_output.md`）：形式文と食い違う散文、形式文の主張を取り違える文はなかった。足した 4 定理の逆翻訳と非空虚性の証人（数値）を照合者が示した。中 4 件（冒頭の説明の機械的な照合の件数、台帳 L13 の範囲の漏れ、「5 は C2 の障害の一つ」が広すぎる、着手前の文書の後注の「すべて Lean に入った」が `Uinf` の文を含む）と低・極低。直した（台帳 L15）。
-- 統合照合 I-b（同時、約 188 秒、`integrated_Ib_output.md`）：台帳 L14 を照らした。高はなし、中 4 件（R4 の後注の「L11 で直した」、辞書 §20 の後注が数値より強い、推薦案・索引の後注の番号、16:40 の条文が残っていない）。直した（台帳 L15）。
+- 統合照合 I-b（同時、約 188 秒、`records/audit267/outputs/integrated_Ib_output.md`）：台帳 L14 を照らした。高はなし、中 4 件（R4 の後注の「L11 で直した」、辞書 §20 の後注が数値より強い、推薦案・索引の後注の番号、16:40 の条文が残っていない）。直した（台帳 L15）。
 
-- 閉鎖（2026-11-25 19:11）：著者が、Part 263 を閉じてよいと判断した（引き継ぎメモの確かめる事項 4 への回答「良いです」）。台帳 L15 は次のパートの統合照合に載せる。ラベルはこの閉鎖で確定した。
+- 閉鎖（2026-11-25 19:11）：著者が、Part 263 を閉じてよいと判断した（著者の回答「1、2 とも良いです」の 2。構築側の報告の番号で、引き継ぎメモの確かめる事項 4 に当たる）。台帳 L15 は次のパートの統合照合に載せる。ラベルはこの閉鎖で確定した。
 
 ## §7 収束アラームの報告
 
diff --git a/notes/pag2_pag268_p1_char_extension.md b/notes/pag2_pag268_p1_char_extension.md
index e28fef2..b56c73c 100644
--- a/notes/pag2_pag268_p1_char_extension.md
+++ b/notes/pag2_pag268_p1_char_extension.md
@@ -12,16 +12,16 @@
 
 1. `chiPt χ`：[a:b] ↦ χ(a)·χ⁻¹(b) は P¹(ℤ/N) の上で well-defined。`chiPt_eqPt`（赤道では χ）、`chiPt_Wproj`（W で χ⁻¹ の関数に）、`chiPt_torus`（トーラスの作用 `torus u`：[a:b] ↦ [u a : b] で χ(u) 倍。`torus_eqPt`：赤道の上では掛け算）。補助：`mul_inv_apply_unit`、`chiPt_mk`、`chiPt_red_congr`（型の違う法の間の受け渡し）。
 2. `extChi χ`（原始指標 χ* の `chiPt` を導手から法 N へ引き戻したもの）：`extChi_eqPt`・`resE_extChi`（赤道への制限は χ）、`extChi_changeLevel`・`pullP_extChi`（引き戻しと両立）、`extChi_torus`（トーラスで χ(u) 倍）。
-3. `chiPt_not_compat`：法 N の式をそのまま使うと、原始的でない χ では両立しない（法 2 の自明な指標、点 0：左辺 0、右辺 1）。
-4. `ketS_proj_zero_eq`：p 素数、1 ≤ c ≤ K のとき、Part 25（PAG29）の殻 0 の南ケット `ketS_proj K 0 c` = |S_0|^(−1/2)·（法 p^c の `chiPt χ` の引き戻し）。
+3. `chiPt_not_compat`：法 N の式をそのまま使うと、原始的でない χ では両立しない場合がある（証人 1 つ：法 2 の自明な指標、点 0：左辺 0、右辺 1。崩れるかどうかは新しい素数が増えるかによる。法 3 の指標を法 9 に上げたものは両立する：統合照合 III-a の照合者の数値、Lean の外）。
+4. `ketS_proj_zero_eq`：p 素数、1 ≤ c ≤ K のとき、Part 25（PAG29）の殻 0 の南ケット `ketS_proj K 0 c` = |S_0|^(−1/2)·（法 p^c の `chiPt χ` の引き戻し）。|S_0| = `sz p K 0` = φ(p^K)。
 
 ## §3 読み（Lean の外）
 
-- 盲検の照合者によれば、引き戻しと両立し赤道で恒等な延長の族は多いが、トーラスとも両立する族は一意で `extChi` で与えられる（確信度：高）。したがって 4 は「2 チャートのモデルの殻 0 のケットは、素数冪の法での一意な等変延長（の規格化の定数倍）」と読める（χ が原始的でない場合は、法 p^c の式と原始指標の式が違うので、この読みは原始指標のときに限る）。
-- `Uinf` の持ち上げは存在するが一意でない（ユニタリ・トーラス・W・引き戻しの条件を全部課しても、素数ごとの ±1 の自由度。照合者の数値の反例）。局所性の条件で一意（照合者の確信度：中〜高）。W とは可換にできない（W V W = V⁻¹）。索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）は、この文書の後も残る。材料としては「P¹ の上の作用素への持ち上げは自然には一意に決まらない」。
+- 盲検の照合者によれば、引き戻しと両立し赤道で恒等な延長の族は多いが、トーラスとも両立する族は一意で `extChi` で与えられる（確信度：高）。素数冪の法では、導手が 1 でない χ について `chiPt χ` = `extChi χ`（法 p^c で単数であることと導手の法で単数であることが同じため。Lean の外、数値 `records/p1_lift/numeric/extchi_check.py`：奇素数冪 7 つの法の全指標で、一致するのは導手 > 1 のときちょうど）。したがって 4 は「2 チャートのモデルの殻 0 のケットは、素数冪の法での一意な等変延長（の規格化の定数倍）」と読める（導手 > 1 のとき。主指標では一致しない。統合照合 III-a の指摘で、条件を「原始指標のとき」から直した）。
+- `Uinf` の持ち上げは存在するが一意でない（ユニタリ・トーラス・W・引き戻しの条件を全部課しても、素数ごとの ±1 の自由度。照合者の数値の反例）。局所性の条件で一意（照合者の確信度：中〜高）。W とは可換にできない（赤道の上で W V W = U⁻¹ が強制される。W V W = V⁻¹ は層別の持ち上げが満たす性質）。索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）は、この文書の後も残る。材料としては「P¹ の上の作用素への持ち上げは自然には一意に決まらない」。
 - 4 の 1 ≤ c：c = 0 では、殻 0 のケットは北のチャートの単数でない点で 0、`chiPt`（法 1）の引き戻しは定数 1 で、等式は破れる（構築側と独立照合の照合者の手計算。Lean にしていない）。
 - 主指標の `extChi` は全点（0 と ∞ を含む）で 1、導手 > 1 の指標の `extChi` は 0 と ∞ で 0（独立照合の指摘）。
-- 対照群：盲検の照合者は、答えは F_q[t] でも同じ形とした。ℚ に固有の算術は運ばない。
+- 対照群：盲検の照合者は、答えは F_q[t] でも同じ形とした（照合者の確信度：中〜高）。ℚ に固有の算術は運ばない見込み。
 
 ## §4 ラベル（見込み。閉鎖で確定）
 
@@ -37,7 +37,8 @@
 
 - 独立照合（形式文と定義だけ、2026-11-25 夜、約 160 秒、`records/audit268/outputs/check_output.md`。依頼文 `records/audit268/request_formal.md`、入力 `records/audit268/input_formal.md`）：逆翻訳は意図どおり。非空虚性の証人はすべての定理にある。除去テスト：1 ≤ c は外すと反例（c = 0、p = 2、K = 1、点 ∞）、原始指標の代わりに χ を使うと引き戻しとの両立だけが崩れる（`chiPt_not_compat`）、1 ≤ K は冗長、[NeZero N] は不要の見込み、[NeZero M] は M = 0 で崩れる見込み、`chiPt_red_congr` の d₁ = d₂ は型のための仮定。
 - 指摘：主指標の `extChi` は 0 と ∞ でも 1（導手 > 1 では 0）、`extChi` の定義の [NeZero N]、4 と `extChi` の一致は原始指標のとき、`charU` の重複の可能性。形式文は変えず、冒頭の説明とこのノートに注意を書いた。`charU` は鎖に 1 つだけ（Part 257（PAG261）、PAG258 はそれを開いて使う）で、重複はない（言葉の検索）。
-- この直しは、閉じるときの統合照合の入力に含める（台帳 L16）。
+- この直しは、閉じるときの統合照合の入力に含めた（台帳 L16）。
+- 統合照合 III-a（2026-11-25 夜、約 189 秒、`records/audit268/outputs/integrated_IIIa_output.md`）：高 1（`extChi` との一致の条件は「原始指標」ではなく「導手 > 1」）、中 3（「両立しない」が全称に読める、「したがって」の段に Lean の外が入る、`#print axioms` が 4 定理に欠けていた）ほか。直した（台帳 L17）。条件は構築側の数値（`extchi_check.py`）でも確かめた。同時に Part 263 の台帳 L15 を III-b で照らした。
 
 ## §7 収束アラームの報告
 
diff --git a/notes/pag2_tail_ledger.md b/notes/pag2_tail_ledger.md
index 2991b67..750f1f1 100644
--- a/notes/pag2_tail_ledger.md
+++ b/notes/pag2_tail_ledger.md
@@ -4,29 +4,44 @@
 
 ## 開いている項目
 
-### L16：Part 264（PAG268）の独立照合の後の直し（2026-11-25 夜）
-
-- 範囲：独立照合（`records/audit268/outputs/check_output.md`）の指摘を受けた直し。形式文は変えていない。
-  - PAG268.lean の冒頭の説明に「注意（独立照合の指摘）」の 4 項（主指標の `extChi` の値、`extChi` の [NeZero N]、1 ≤ K と 1 ≤ c、4 と `extChi` の一致の条件）。作り直してエラー・警告 0。
-  - ノート `notes/pag2_pag268_p1_char_extension.md` の §3・§6。
-- 扱い：閉じるときの統合照合に、L15 と一緒に載せる。
-
-### L15：統合照合 I-a・I-b の後の直し（2026-11-25 夜）
-
-- 範囲：I-a（`records/audit267/outputs/integrated_Ia_output.md`）と I-b（`records/audit267/outputs/integrated_Ib_output.md`）の指摘を受けた直し。
-  - PAG267.lean の冒頭の説明（コメントだけ。作り直してエラー・警告 0）：機械的な照合の件数を今の版に、「5 は C2 の障害の一つ」を「各段の 0 延長による持ち上げだけを妨げ、`resL` の切断を使った持ち上げは妨げない（照合者の手計算、Lean の外）」に狭めた、`WL` と `Uinf` を結ぶ文がないこと、M = 0 の 2 つの補題の書き方。
-  - Part 263 のノート（§3・§6）、着手前の文書の後注（`Uinf` の文は型の上の事実）、引き継ぎメモの Part 263 の項（Part 番号の併記、0 延長の但し書き、I-a・I-b の記録、著者に確かめる事項 4）、xlsx（`records/audit267/update_xlsx_267b.py`：「Lean の外」の標示 2 つ、Part 番号の併記、LABEL の但し書き）、数値スクリプト（何も確かめていなかった行を、還元と反転の可換の検査に置き換えた。出力は変わらない）。
-  - L14 の範囲の直し（後注の形）：R4 の後注の「L11 で直した」を「2 は直した、1 は一部」に（台帳 3 か所、Part 262 のノート 2 か所、引き継ぎメモ 2 か所）、L11 の注にも後注、推薦案・索引のラベルの後注を名前で書いた、引き継ぎメモの閉鎖の行にラベルの書き分けの後注と 16:40 の条文の逐語（コミット c7f2796）と会話の特定、辞書 §20 の F_p の後注を数値の範囲に合わせた、インスタンスの数の範囲、「インスタンスなので」。
-  - 辞書 §22（Part 263 の名前の行）を新設。
-  - ノート §7（収束アラームの報告）を記入。
-  - この台帳：L13・L14 を閉じた項目に移し、L15 を新設。
-  - 閉鎖の記録（2026-11-25 19:11 の後）：PAG267.lean の冒頭のラベルの行（コメントだけ）、ノート §4・§6、引き継ぎメモ、xlsx の LABEL、この台帳の扱いの行。閉じた L13・L14 の記載に、I-a・I-b が挙げた範囲の漏れを書き足した。
-- 直していないもの：CLAUDE.md（日英）の文面（著者側の版の写し。16:40 の条文そのものと、2 つの規則の関係、Part 260・`InLayer` の文の断りは、著者に確かめる事項）。II-a の低 5・7・8・11・12、II-b の K と k の表記、grep の式の拡大（さらい直しはしていない）、新しい文の Part 番号の併記の一部、検証手順の行番号の表記。
-- 自己申告（根拠にしない）：主張を強めた文はない。辞書の F_p の後注と「5 は障害」の文は、どちらも範囲を狭めた直し。
-- 扱い（2026-11-25 19:11 の著者の判断）：Part 263 を閉じ、L15 は次のパートの統合照合に載せる。この行の後の文は判断の前の記載。I-a・I-b に中の指摘があった（高はない）。停止規則の「もう1回だけ統合照合」は I-a・I-b で行ったので、Part 263 を閉じて L15 を次のパートの統合照合に載せるか、もう 1 回照らすかを、著者に確かめる（引き継ぎメモの確かめる事項 4）。
+### L17：統合照合 III-a・III-b の後の直し（2026-11-25 夜）
+
+- 範囲：III-a（`records/audit268/outputs/integrated_IIIa_output.md`）と III-b（`integrated_IIIb_output.md`）の指摘を受けた直し。
+  - PAG268.lean の冒頭の説明と `chiPt_not_compat` の docstring（形式文は変えていない。作り直してエラー・警告 0）：3 を「両立しない場合がある（証人 1 つ）」に、4 の続きの「したがって」の段を Lean の外の読みに分け、一致の条件を「原始指標」から「導手 > 1」に直した（主張の条件と量化の直し）、|S_0| = `sz p K 0`、N ∣ 2 の例外、M = 0 の確信度：中、W V W = U⁻¹。`#print axioms` を 4 定理に足した（14 行）。
+  - PAG267.lean の冒頭の説明（コメントだけ）：「resL∘X = Uinf∘resL を満たす作用素 X」、M = 0 の 2 つの補題の名前。
+  - Part 264 のノート（§2・§3・§6）、着手前の文書 `pag2_p1_lift_preregistration.md` の後注（§0 の c = 0 の誤り）、引き継ぎメモ（Part 264 の項、Part 263 の確かめる事項 4 の後注、「急がない」の出所、Part 254（PAG258））、xlsx（`records/audit268/update_xlsx_268b.py`）、辞書（§22 の `eqU`・`eqPt` の行を「同じ集合」から「対応する（C）」に、§22 のさらい方の式、§21 の文の同語反復、§20 の後注の出所）、Part 263 のノート（§3・§6 の言い方とパス、閉鎖の行の引用）。
+  - 数値：`records/p1_lift/numeric/extchi_check.py`（新しい。奇素数冪 7 つの法の全指標で、chiPt と extChi が一致するのは導手 > 1 のときちょうど）、`retraction_check.py` の表示（無条件の「all checks passed」を直した）、`records/p1_tower/numeric/p1_tower_check.py` のコメント。
+  - この台帳：L15・L16 を閉じた項目に移し、L17 を新設。閉じた L11・L12 と L15 の記載に後注。
+- 直していないもの：III-b の低・極低の一部（L15 の「直していないもの」の 16:40 の条文の記載の古さ、xlsx の「手計算」の出所）。
+- 自己申告（根拠にしない）：主張を強めた直しはない。条件の直し（原始指標 → 導手 > 1）は Lean の外の読みの範囲を正しくする直しで、Lean の外の文を 1 つ（chiPt = extChi、導手 > 1）明示した。
+- 扱い：主張（条件・量化）を変える直しがあるので、停止規則の「もう1回だけ統合照合」を行う（統合照合 IV）。
 
 ## 閉じた項目
 
+- L15・L16（2026-11-25 に閉じた）：統合照合 III-b（L15）・III-a（L16 と Part 264 の材料）を、直しそのものを入力に含めて受けた（`records/audit268/integrated/`）。III-a は形式文と食い違う散文を見つけた（ケットと `extChi` の一致の条件、「両立しない」の量化）。III-b は形式文が入力になかった。高は III-a の 1 件、中は各 3〜4 件。直しは L17。
+  - 範囲の漏れ（III-b の指摘）：L15 は引き継ぎメモの「辞書 §22・final85」の追記と 17:29 の項の出所の直しを書いていなかった。L15 の「閉じた L13・L14 の記載に…書き足した」は 19:11 の判断の前の作業（コミット a529c13）で、「閉鎖の記録（19:11 の後）」の項に置いたのは誤り。19:11 の後の xlsx の LABEL の直し（「見込み、閉鎖で確定」→「2026-11-25 19:11 の閉鎖で確定」、34 セル）は、コミット 5419967 の中の手で書いたスクリプトで行い、III-b の入力にはその差分がなかった。L16 は引き継ぎメモの Part 264 の項を書いていなかった。自己申告「どちらも範囲を狭めた直し」は不正確だった（切断による持ち上げの肯定の文を足していた）。
+  - 閉じた L11・L12 の「形式文より強い文の指摘はなかった」への後注：II-b は形式文が入力になく、形式文との突き合わせはできなかった（I-b 低 10、III-b の指摘）。
+    ### L16：Part 264（PAG268）の独立照合の後の直し（2026-11-25 夜）
+
+    - 範囲：独立照合（`records/audit268/outputs/check_output.md`）の指摘を受けた直し。形式文は変えていない。
+      - PAG268.lean の冒頭の説明に「注意（独立照合の指摘）」の 4 項（主指標の `extChi` の値、`extChi` の [NeZero N]、1 ≤ K と 1 ≤ c、4 と `extChi` の一致の条件）。作り直してエラー・警告 0。
+      - ノート `notes/pag2_pag268_p1_char_extension.md` の §3・§6。
+    - 扱い：閉じるときの統合照合に、L15 と一緒に載せる。
+
+    ### L15：統合照合 I-a・I-b の後の直し（2026-11-25 夜）
+
+    - 範囲：I-a（`records/audit267/outputs/integrated_Ia_output.md`）と I-b（`records/audit267/outputs/integrated_Ib_output.md`）の指摘を受けた直し。
+      - PAG267.lean の冒頭の説明（コメントだけ。作り直してエラー・警告 0）：機械的な照合の件数を今の版に、「5 は C2 の障害の一つ」を「各段の 0 延長による持ち上げだけを妨げ、`resL` の切断を使った持ち上げは妨げない（照合者の手計算、Lean の外）」に狭めた、`WL` と `Uinf` を結ぶ文がないこと、M = 0 の 2 つの補題の書き方。
+      - Part 263 のノート（§3・§6）、着手前の文書の後注（`Uinf` の文は型の上の事実）、引き継ぎメモの Part 263 の項（Part 番号の併記、0 延長の但し書き、I-a・I-b の記録、著者に確かめる事項 4）、xlsx（`records/audit267/update_xlsx_267b.py`：「Lean の外」の標示 2 つ、Part 番号の併記、LABEL の但し書き）、数値スクリプト（何も確かめていなかった行を、還元と反転の可換の検査に置き換えた。出力は変わらない）。
+      - L14 の範囲の直し（後注の形）：R4 の後注の「L11 で直した」を「2 は直した、1 は一部」に（台帳 3 か所、Part 262 のノート 2 か所、引き継ぎメモ 2 か所）、L11 の注にも後注、推薦案・索引のラベルの後注を名前で書いた、引き継ぎメモの閉鎖の行にラベルの書き分けの後注と 16:40 の条文の逐語（コミット c7f2796）と会話の特定、辞書 §20 の F_p の後注を数値の範囲に合わせた、インスタンスの数の範囲、「インスタンスなので」。
+      - 辞書 §22（Part 263 の名前の行）を新設。
+      - ノート §7（収束アラームの報告）を記入。
+      - この台帳：L13・L14 を閉じた項目に移し、L15 を新設。
+      - 閉鎖の記録（2026-11-25 19:11 の後）：PAG267.lean の冒頭のラベルの行（コメントだけ）、ノート §4・§6、引き継ぎメモ、xlsx の LABEL、この台帳の扱いの行。閉じた L13・L14 の記載に、I-a・I-b が挙げた範囲の漏れを書き足した。
+    - 直していないもの：CLAUDE.md（日英）の文面（著者側の版の写し。16:40 の条文そのものと、2 つの規則の関係、Part 260・`InLayer` の文の断りは、著者に確かめる事項）。II-a の低 5・7・8・11・12、II-b の K と k の表記、grep の式の拡大（さらい直しはしていない）、新しい文の Part 番号の併記の一部、検証手順の行番号の表記。
+    - 自己申告（根拠にしない）：主張を強めた文はない。辞書の F_p の後注と「5 は障害」の文は、どちらも範囲を狭めた直し。
+    - 扱い（2026-11-25 19:11 の著者の判断）：Part 263 を閉じ、L15 は次のパートの統合照合に載せる。この行の後の文は判断の前の記載。I-a・I-b に中の指摘があった（高はない）。停止規則の「もう1回だけ統合照合」は I-a・I-b で行ったので、Part 263 を閉じて L15 を次のパートの統合照合に載せるか、もう 1 回照らすかを、著者に確かめる（引き継ぎメモの確かめる事項 4）。
+
 - L13・L14（2026-11-25 に閉じた）：統合照合 I-a（L13 と Part 263 の材料）・I-b（L14）を、直しそのものを入力に含めて受けた（`records/audit267/integrated/input_Ia.md`・`input_Ib.md`）。I-a は形式文と食い違う散文・取り違える文を見つけなかった。I-b は形式文が入力になく、形式文との突き合わせはできなかった。高はなく、中が各 4 件。直しは L15。
   - 閉じたときの L13・L14 の記載は下にそのまま残す。範囲の漏れ（I-a・I-b の指摘）：L13 は引き継ぎメモの Part 263 の項、着手前の文書の後注、冒頭の説明の主な定理 4 の追記、新しい docstring を書いていなかった。L14 は閉じた項目の L11・L12 の記載と台帳の漏れの記録を書いていなかった。L14 の「どれも後注の形」は強すぎた（辞書の `fC` と「名前ではない」、CLAUDE.en.md はその場で直した）。L14 の扱いの理由は、高・中の指摘で閉じる条件を満たさないため、と書くべきだった。
     ### L13：Part 263（PAG267）の独立照合の後の直し（2026-11-25 夜）
diff --git a/notes/pag2_terwilliger_dictionary.md b/notes/pag2_terwilliger_dictionary.md
index 50c6f2b..e5c26fb 100644
--- a/notes/pag2_terwilliger_dictionary.md
+++ b/notes/pag2_terwilliger_dictionary.md
@@ -470,13 +470,13 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
 | `equator_intertwine_rootNum`・`equator_intertwine_proj_rootNum` | 2 チャートの比較そのものは文献用語なし。各チャートの中身は、乗法的指標の畳み込みがヤコビ和倍になること χ₁ ⋆ χ₂ = J(χ₁, χ₂)·χ₁χ₂（有限体 F_p の場合、χ₁χ₂ が自明でないとき）。北のチャートでは χ̄ の畳み込みなので係数は conj(J)。（2026-11-20 に補足 16 の作業で足した） | 畳み込みの式は N. Katz「Exponential Sums」の翻訳 arXiv:2308.11611 の Lemma 1.3.2 と arXiv:2406.11529 の §3（どちらも F_p。検索結果の抜粋で確認、2026-11-20）。ℤ/p^k での形は Part 20（PAG24）の `equator_intertwine` の Lean の文で、文献では確かめていない。2 チャートの比較の文献は、検索 1 回（convolution / inversion / projective line / Jacobi sum / two charts）で見つからなかった（見つからなかったは不存在の証明ではない）。Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換え。射影直線の版は 2 チャートの版を `projFunEquiv` で移したもので同値（手の論証、Lean の文ではない）。設定そのものは盲検の 1 回の検索では見つからなかった |
 | 条件「U'² が赤道で B_S を B_N に移す」の解の集まり（Lean の外） | 部分群の補集合の上で乗法的な関数は準同型に延びる（|X/Y| ≥ 3）、ポントリャーギン双対 | 盲検の照合者の手計算（補題を書いた文献は探していない）。加法指標の取り替えで局所定数が χ(b) 倍になること（Tate、Biswas arXiv:1401.5591 §4.3） |
 
-- 後注（2026-11-25、統合照合 II-b の指摘）：作用素の形の行の比較の設定は P¹(ℤ/p^K) の 2 チャート（補足 16 の作業で文献の欄から設定の記述が落ちた）。F_p の畳み込みの式は、ℤ/p^k では、照合者の数値（法 9・25・27・49）で χ₁・χ₂・χ₁χ₂ がすべて原始的なら不一致 0。制限しないと法 9 で 270 個中 8 個の不一致があり、不一致は χ₁χ₂ が原始的でない組に出た（統合照合 I-b の照合者の数値。一般の証明・文献は確かめていない。I-b の指摘で「原始的な場合に限って成り立つ」を直した）。
+- 後注（2026-11-25、統合照合 II-b の指摘）：作用素の形の行の比較の設定は P¹(ℤ/p^K) の 2 チャート（補足 16 の作業で文献の欄から設定の記述が落ちた）。F_p の畳み込みの式は、ℤ/p^k では、照合者の数値（法 9・25・27・49）で χ₁・χ₂・χ₁χ₂ がすべて原始的なら不一致 0。制限しないと法 9 で 270 個中 8 個の不一致があり、不一致は χ₁χ₂ が原始的でない組に出た（法 49 と「270 個中 8 個」は統合照合 II-b の照合者の数値、I-b の照合者が法 9・25・27 で再現。一般の証明・文献は確かめていない。I-b の指摘で「原始的な場合に限って成り立つ」を直した）。
 - 未記入の件数（この節）：0（2026-11-20 に補足 16 の作業で、作用素の形の行の右列を埋めた：比較そのものは「文献用語なし」、各チャートの畳み込みはヤコビ和倍の式。それまでは 1 と数えていた。統合照合 I の指摘）。
 
 ## 21. 行のなかった名前の追加（補足 16、2026-11-20。Parts 257〜261（PAG261〜PAG265）と parFac）
 
 - 欠落の種類（補足 16 の 5）：辞書の欠落には、右列が空の行だけでなく、**行そのものがない名前**もある。§7 の指標（右列が空の行の数）はこれを拾わないので、未記入の件数を数えるときは、各パートの新しい定義名に行があるかも確かめる。
-- さらった範囲（補足 16 の 4）：2026-11-20 に、PAG261〜PAG265 の `def`・`abbrev`・`structure`・`instance` の宣言を機械的に抜き出した（`grep -nE "^\s*(noncomputable )?(def|abbrev|structure|inductive|class|instance)\s"`）。定理の名前は対象にしていない（後注 2026-11-25、統合照合 II-b の指摘：式には `inductive`・`class` も入っている。`private`・`protected` のつく宣言、同じ行に属性がつく宣言、`irreducible_def` は拾わない式で、完全性の確認としては穴がある）。抜き出した定義名のうち、§17・§18 に行のあったもの（`fsum`、`cornerOp`、`cornerHom`、`CornerLim`、`ofCorner`）を除き、すべて下の表に入れた。インスタンス（`lvl_neZero`、`NeZero (primeProd S)`、`DirectedSystem` の 2 つ（`sqMap`・`cornerSys` の行）の 4 つ（上の grep の式で拾った範囲で）。後注 2026-11-25、統合照合 II-b の指摘で「3 つ」を直した）はインスタンスなので行にせず、所属する定義の行に書いた。補足 16 は `parFac` を Part 257 としていたが、定義は PAG256（Part 252）にある。
+- さらった範囲（補足 16 の 4）：2026-11-20 に、PAG261〜PAG265 の `def`・`abbrev`・`structure`・`instance` の宣言を機械的に抜き出した（`grep -nE "^\s*(noncomputable )?(def|abbrev|structure|inductive|class|instance)\s"`）。定理の名前は対象にしていない（後注 2026-11-25、統合照合 II-b の指摘：式には `inductive`・`class` も入っている。`private`・`protected` のつく宣言、同じ行に属性がつく宣言、`irreducible_def` は拾わない式で、完全性の確認としては穴がある）。抜き出した定義名のうち、§17・§18 に行のあったもの（`fsum`、`cornerOp`、`cornerHom`、`CornerLim`、`ofCorner`）を除き、すべて下の表に入れた。インスタンス（`lvl_neZero`、`NeZero (primeProd S)`、`DirectedSystem` の 2 つ（`sqMap`・`cornerSys` の行）の 4 つ（上の grep の式で拾った範囲で）。後注 2026-11-25、統合照合 II-b の指摘で「3 つ」を直した）は行にせず、所属する定義の行に書いた。補足 16 は `parFac` を Part 257 としていたが、定義は PAG256（Part 252）にある。
 - 書き方（補足 16 の 2・3）：文献の言葉が見つからない場合は「文献用語なし」と書いた。文献の言葉を書く場合は、根拠と確かめ方を添えた。「定義の読み」は、Lean の定義を読んで標準の数学用語と照らしたことを指し、文献の本文は開いていない。
 
 | 名前 | Part（PAG） | 文献の言葉 | 根拠・確かめ方 |
@@ -512,7 +512,7 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
 |---|---|---|
 | `redU`・`red` | 射影直線の還元写像 P¹(ℤ/M) → P¹(ℤ/N)（N ∣ M） | 盲検の照合者の申告（Cremona・Stein の Manin 記号の章、SL₂ の持ち上げは Shimura Lemma 1.38。節番号は照合者の記憶で未確認）。定義の読み。 |
 | `zeroPt`・`infPt` | P¹ の点 0 = [0:1]、∞ = [1:0] | 定義の読み。 |
-| `eqU`・`eqPt` | 文献用語なし（両座標が単数の点 [x:1]。この鎖の言葉で「赤道」。Part 19（PAG23）の 2 チャートのモデルの赤道と同じ集合） | ― |
+| `eqU`・`eqPt` | 文献用語なし（両座標が単数の点 [x:1]。この鎖の言葉で「赤道」。素数冪の法では、Part 19（PAG23）の 2 チャートのモデルの赤道に対応する（Part 23（PAG27）の `toProj` を通して。PAG267 の内部照合では C＝近い。Lean で結んでいない。統合照合 III-b の指摘で「同じ集合」を直した）） | ― |
 | `Fsp`・`pullP`・`LimP`・`ofP` | 引き戻しの帰納系と加群の帰納極限。読み（Lean の外）では P¹(Ẑ) の上の局所定数関数の空間 | Mathlib の `Module.DirectLimit`（定義の読み）。P¹(Ẑ) との同一視は盲検の照合者の記述。 |
 | `Wfun`・`WL` | 反転の引き戻し（Part 24（PAG28）の `Wpull`）と、それが極限に誘導する写像 | 定義の読み。 |
 | `resE`・`resL` | 開でない部分集合（Ẑ^×）への制限写像（読み） | 定義の読み。Ẑ^× が P¹(Ẑ) の中で開でないことは盲検の照合者の記述（Lean の外）。 |
@@ -521,7 +521,7 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
 | `lv1`・`lv2` | 文献用語なし（法 1・法 2 の添字） | ― |
 
 - 未記入の件数（この節）：0。「文献用語なし」の行は 2 つ（`eqU`・`eqPt`、`lv1`・`lv2`）。
-- さらい方：PAG267 の `def`・`abbrev`・`structure`・`instance` を抜き出した（インスタンスは `DirectedSystem Fsp` の 1 つで、`pullP` の行に属する）。
+- さらい方：PAG267 から §21 と同じ grep の式（`^\s*(noncomputable )?(def|abbrev|structure|inductive|class|instance)\s`）で抜き出した（インスタンスは `DirectedSystem Fsp` の 1 つで、`pullP` の行に属する）。
 
 ## 23. Part 264（PAG268、短期層）の名前（2026-11-25）
 
diff --git a/records/audit268/PAG268.out b/records/audit268/PAG268.out
index 02c7146..7652b0a 100644
--- a/records/audit268/PAG268.out
+++ b/records/audit268/PAG268.out
@@ -1,6 +1,10 @@
+'PAG.Part268.mul_inv_apply_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
+'PAG.Part268.chiPt_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
 'PAG.Part268.chiPt_eqPt' depends on axioms: [propext, Classical.choice, Quot.sound]
 'PAG.Part268.chiPt_Wproj' depends on axioms: [propext, Classical.choice, Quot.sound]
+'PAG.Part268.torus_eqPt' depends on axioms: [propext, Quot.sound]
 'PAG.Part268.chiPt_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
+'PAG.Part268.chiPt_red_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
 'PAG.Part268.extChi_eqPt' depends on axioms: [propext, Classical.choice, Quot.sound]
 'PAG.Part268.extChi_changeLevel' depends on axioms: [propext, Classical.choice, Quot.sound]
 'PAG.Part268.extChi_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
diff --git a/records/audit268/integrated/input_IIIa.md b/records/audit268/integrated/input_IIIa.md
new file mode 100644
index 0000000..0a8139e
--- /dev/null
+++ b/records/audit268/integrated/input_IIIa.md
@@ -0,0 +1,918 @@
+# 統合照合 III-a の入力：Part 264（PAG268）の材料と、独立照合の後の直し（台帳 L16）（2026-11-25）
+照合の対象：Part 264 の散文（Lean の冒頭の説明と docstring、ノート、xlsx の行、引き継ぎメモの項、着手前の文書、辞書 §23）が、Lean の形式文（§2 の全文）と食い違わないか、強いことを言っていないか。§4 は独立照合の出力、§5 は独立照合に渡した形式文と前の鎖の定義、§6 は盲検の問いテストの出力（読みの出所）。
+
+## §1 台帳 L16
+```markdown
+### L16：Part 264（PAG268）の独立照合の後の直し（2026-11-25 夜）
+
+- 範囲：独立照合（`records/audit268/outputs/check_output.md`）の指摘を受けた直し。形式文は変えていない。
+  - PAG268.lean の冒頭の説明に「注意（独立照合の指摘）」の 4 項（主指標の `extChi` の値、`extChi` の [NeZero N]、1 ≤ K と 1 ≤ c、4 と `extChi` の一致の条件）。作り直してエラー・警告 0。
+  - ノート `notes/pag2_pag268_p1_char_extension.md` の §3・§6。
+- 扱い：閉じるときの統合照合に、L15 と一緒に載せる。
+```
+
+## §2 PAG268.lean の全文
+```lean
+/-
+アーデル射影幾何 — Part 264（PAG268、短期層の小さいノート、2026-11-25）：P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致
+
+問いの出所：基礎文書の索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）と、Part 263（PAG267）で外に残った候補 C2（`Uinf` を P¹ の上の関数の極限に持ち上げる作用素）。
+- 推薦案 `notes/pag2_p1_lift_preregistration.md` §4（C2-a）。2026-11-25 19:13 の著者の指示「お勧めで進めてください」を受けて、構築側が選んで着手した（CLAUDE.md §4 の選択の委任）。
+
+記号：`chiPt χ`（法 N の指標 χ）は [a:b] ↦ χ(a)·χ⁻¹(b)。χ⁻¹(b) は単数 b では χ(b) の複素共役、単数でない b では 0。
+`torus u` は [a:b] ↦ [u a : b]（u は単数）。`extChi χ` は、χ を誘導する原始指標 χ*（法は導手）の `chiPt` を、導手から法 N への還元で引き戻したもの。
+
+主な定理：
+1. `chiPt χ` は P¹(ℤ/N) の上で well-defined（定義）。赤道では χ（`chiPt_eqPt`）、反転 W で χ⁻¹ の関数に移り（`chiPt_Wproj`）、トーラスの作用で χ(u) 倍（`chiPt_torus`）。
+2. `extChi χ` の赤道への制限は χ（`extChi_eqPt`、`resE_extChi`）。N ∣ M のとき、χ を法 M に上げた指標の `extChi` は、`extChi χ` の引き戻し（`extChi_changeLevel`、段の言葉で `pullP_extChi`）。トーラスの作用で χ(u) 倍（`extChi_torus`）。
+3. 法 N の式 `chiPt χ` をそのまま使うと、原始的でない χ では引き戻しと両立しない（`chiPt_not_compat`：法 2 の自明な指標と点 0）。
+4. p が素数で 1 ≤ c ≤ K のとき、Part 25（PAG29）の殻 0 の南ケット `ketS_proj K 0 c` は、法 p^c の `chiPt χ` の引き戻しの |S_0|^(−1/2) 倍（`ketS_proj_zero_eq`）。
+   したがって、2 チャートのモデル（Part 19〜25（PAG23〜PAG29））の殻 0 のケットは、素数冪の法では `extChi` と同じ形の関数（原始指標なら規格化の定数倍で `extChi` そのもの）。
+
+注意（独立照合の指摘）：
+- 導手 1 の指標（主指標）の `extChi` は、法 1 の P¹ が 1 点で 0 も単数なので、P¹(ℤ/N) の全点（0 と ∞ を含む）で 1。導手 > 1 の指標の `extChi` は 0 と ∞ で 0。
+- `extChi` の定義は [NeZero N] を引数に取らない（節の変数は使われたときだけ入る）。`extChi_changeLevel` は [NeZero M] だけを仮定する。M = 0 では両立が崩れる見込み（照合者の手計算、Lean の外）。
+- 4 の 1 ≤ K は 1 ≤ c と c ≤ K から出る（`ketS_proj` の型の引数として置いた）。1 ≤ c は外せない（c = 0、p = 2、K = 1 の点 ∞ で 0 ≠ 1。照合者の手計算）。
+- 4 の右辺は法 p^c の `chiPt χ` の引き戻しで、`extChi` と一致するのは χ が法 p^c で原始的なとき。
+
+Lean の外（盲検の問いテスト `records/p1_lift/outputs/blind_output.md`、照合者の確信度つき）：
+- 引き戻しと両立し赤道への制限が恒等な延長の族は多い（導手ごとのアフィン空間、確信度：高）。トーラスとも両立する族は一意で、`extChi` で与えられる（確信度：高、照合者の手の証明と数値）。
+- レトラクション（点ごとの写像）の形の延長はあるが、トーラスと両立するものはない（点 0 がトーラスで固定されるため）。N によらない同次形式の比では書けない（確信度：高）。
+- `Uinf` の持ち上げ（P¹ の上の関数の作用素で、制限すると `Uinf`、引き戻しと両立）は存在するが、ユニタリ・トーラス・W の条件を全部課しても一意でない（確信度：高、数値の反例）。局所性の条件を足すと一意（確信度：中〜高）。W とは可換にできない。
+- 答えは F_q[t] でも同じ形の見込み（対照群）で、ℚ に固有の算術は運ばない。
+
+内部照合：Part 254（PAG258）の `pullL_charU`、Part 24（PAG28）の `projFun_south`・`projFun_north`、Part 20（PAG24）の `ket0_apply`・`chi_cast_inv`、Part 25（PAG29）の `projFun_ketS` を使った。
+機械的な照合（全宣言 4409 件、対象 18 件、候補の組 144、照合 256 回）で一致なし（網羅ではない）。近いもの（C）：Part 28（PAG32）の `negProj`（トーラスの u = −1 の場合）、Part 252（PAG256）の `inv_apply_units_inv`（`mul_inv_apply_unit` の近く）。
+
+ラベル（見込み、閉鎖で確定）：1〜4 は［再導出（小さい）］。新規候補なし。
+-/
+import PAG267
+import PAG29
+
+namespace PAG.Part268
+
+open ZMod PAG.Part27 PAG.Part258 PAG.Part267 DirichletCharacter
+
+/-! ## 1. P¹ の上の指標の関数 χ(a)·χ̄(b) -/
+
+section chiPt
+
+variable {N : ℕ}
+
+theorem mul_inv_apply_unit (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
+    χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1 := by
+  rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
+
+/-- P¹(ℤ/N) の上の関数 [a:b] ↦ χ(a)·χ⁻¹(b)。 -/
+noncomputable def chiPt (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
+  Quotient.lift (fun v : Unimod N => χ v.1.1 * χ⁻¹ v.1.2) (fun v w ⟨u, h1, h2⟩ => by
+    show χ v.1.1 * χ⁻¹ v.1.2 = χ w.1.1 * χ⁻¹ w.1.2
+    rw [h1, h2, map_mul, map_mul]
+    calc χ v.1.1 * χ⁻¹ v.1.2
+        = (χ (u : ZMod N) * χ⁻¹ (u : ZMod N)) * (χ v.1.1 * χ⁻¹ v.1.2) := by
+          rw [mul_inv_apply_unit, one_mul]
+      _ = χ (u : ZMod N) * χ v.1.1 * (χ⁻¹ (u : ZMod N) * χ⁻¹ v.1.2) := by ring)
+
+theorem chiPt_mk (χ : DirichletCharacter ℂ N) (v : Unimod N) :
+    chiPt χ (mk v) = χ v.1.1 * χ⁻¹ v.1.2 := rfl
+
+/-- 赤道では χ：χ(x)·χ⁻¹(1) = χ(x)。 -/
+theorem chiPt_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : chiPt χ (eqPt x) = χ x := by
+  show χ (x : ZMod N) * χ⁻¹ 1 = χ x
+  rw [map_one, mul_one]
+
+/-- 反転 W で χ⁻¹ の関数に移る。 -/
+theorem chiPt_Wproj (χ : DirichletCharacter ℂ N) (q : ProjLine N) :
+    chiPt χ (Wproj q) = chiPt χ⁻¹ q := by
+  induction q using Quotient.inductionOn with
+  | h v =>
+    show χ v.1.2 * χ⁻¹ v.1.1 = χ⁻¹ v.1.1 * χ⁻¹⁻¹ v.1.2
+    rw [inv_inv, mul_comm]
+
+/-- トーラスの作用の代表 (a, b) ↦ (u a, b)。 -/
+def torusU (u : (ZMod N)ˣ) (v : Unimod N) : Unimod N :=
+  ⟨((u : ZMod N) * v.1.1, v.1.2), by
+    obtain ⟨s, t, h⟩ := v.2
+    refine ⟨s * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), t, ?_⟩
+    have hu : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := Units.inv_mul u
+    linear_combination h + s * v.1.1 * hu⟩
+
+/-- トーラスの作用 [a:b] ↦ [u a : b]。 -/
+def torus (u : (ZMod N)ˣ) : ProjLine N → ProjLine N :=
+  Quotient.lift (fun v => mk (torusU u v)) (fun _v _w ⟨c, h1, h2⟩ =>
+    mk_eq_mk c (by change (u : ZMod N) * _ = c * ((u : ZMod N) * _); rw [h1]; ring) h2)
+
+/-- トーラスは赤道の上で掛け算：u·[x:1] = [u x : 1]。 -/
+theorem torus_eqPt (u x : (ZMod N)ˣ) : torus u (eqPt x) = eqPt (u * x) := rfl
+
+/-- χ(a)·χ̄(b) はトーラスの作用で χ(u) 倍。 -/
+theorem chiPt_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
+    chiPt χ (torus u q) = χ u * chiPt χ q := by
+  induction q using Quotient.inductionOn with
+  | h v =>
+    show χ ((u : ZMod N) * v.1.1) * χ⁻¹ v.1.2 = χ u * (χ v.1.1 * χ⁻¹ v.1.2)
+    rw [map_mul, mul_assoc]
+
+/-- 型の違う法の間の受け渡し：法が等しく整数での値が等しい 2 つの指標の関数は、還元の後で同じ。 -/
+theorem chiPt_red_congr {d₁ d₂ M : ℕ} (hd : d₁ = d₂) (χ₁ : DirichletCharacter ℂ d₁)
+    (χ₂ : DirichletCharacter ℂ d₂) (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) (h₁ : d₁ ∣ M) (h₂ : d₂ ∣ M)
+    (q : ProjLine M) : chiPt χ₁ (red h₁ q) = chiPt χ₂ (red h₂ q) := by
+  subst hd
+  have : χ₁ = χ₂ := by
+    refine MulChar.ext (fun u => ?_)
+    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod d₁)
+    rw [← ha]
+    exact hχ a
+  subst this
+  rfl
+
+end chiPt
+
+/-! ## 2. 原始指標の関数を引き戻した族 -/
+
+section ext
+
+variable {N : ℕ} [NeZero N]
+
+/-- E_N(χ) = r^*(χ*(a)·χ̄*(b))（χ* は χ を誘導する原始指標、導手から法 N への還元で引き戻す）。 -/
+noncomputable def extChi (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
+  fun q => chiPt χ.primitiveCharacter (red χ.conductor_dvd_level q)
+
+/-- 赤道への制限は χ。 -/
+theorem extChi_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : extChi χ (eqPt x) = χ x := by
+  show chiPt χ.primitiveCharacter (red χ.conductor_dvd_level (eqPt x)) = χ x
+  rw [red_eqPt, chiPt_eqPt]
+  have := congrFun (pullL_charU (N := χ.conductor) χ.conductor_dvd_level χ.primitiveCharacter) x
+  rw [changeLevel_primitiveCharacter] at this
+  exact this
+
+omit [NeZero N] in
+/-- 引き戻しとの両立：E_M(χ を法 M に上げたもの) = r^* E_N(χ)。 -/
+theorem extChi_changeLevel {M : ℕ} [NeZero M] (h : N ∣ M) (χ : DirichletCharacter ℂ N)
+    (q : ProjLine M) : extChi (changeLevel h χ) q = extChi χ (red h q) := by
+  show chiPt (changeLevel h χ).primitiveCharacter (red (changeLevel h χ).conductor_dvd_level q) =
+    chiPt χ.primitiveCharacter (red χ.conductor_dvd_level (red h q))
+  rw [red_comp]
+  exact chiPt_red_congr (conductor_changeLevel χ h) _ _ (primitiveCharacter_changeLevel_apply h χ)
+    _ _ q
+
+/-- トーラスとの両立：E_N(χ)(u·q) = χ(u)·E_N(χ)(q)。 -/
+theorem extChi_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
+    extChi χ (torus u q) = χ u * extChi χ q := by
+  have hr : red χ.conductor_dvd_level (torus u q) =
+      torus (unitsMap χ.conductor_dvd_level u) (red χ.conductor_dvd_level q) := by
+    induction q using Quotient.inductionOn with
+    | h v =>
+      show mk (redU _ (torusU u v)) = mk (torusU _ (redU _ v))
+      congr 1
+      apply Subtype.ext
+      show (castHom _ (ZMod χ.conductor) ((u : ZMod N) * v.1.1), castHom _ (ZMod χ.conductor) v.1.2) =
+        (((unitsMap χ.conductor_dvd_level u : (ZMod χ.conductor)ˣ) : ZMod χ.conductor) *
+          castHom _ (ZMod χ.conductor) v.1.1, castHom _ (ZMod χ.conductor) v.1.2)
+      rw [map_mul]
+      rfl
+  show chiPt χ.primitiveCharacter (red _ (torus u q)) = χ u * chiPt χ.primitiveCharacter (red _ q)
+  rw [hr, chiPt_torus]
+  congr 1
+  have := congrFun (pullL_charU (N := χ.conductor) χ.conductor_dvd_level χ.primitiveCharacter) u
+  rw [changeLevel_primitiveCharacter] at this
+  exact this
+
+end ext
+
+/-- 段の帰納系の言葉で：E は引き戻し `pullP` と両立する。 -/
+theorem pullP_extChi (a b : Lvl) (h : a ≤ b) (χ : DirichletCharacter ℂ a.val) :
+    pullP a b h (extChi χ) = extChi (changeLevel (n := a.val) (m := b.val) h χ) :=
+  funext (fun q => (extChi_changeLevel (N := a.val) (M := b.val) h χ q).symm)
+
+/-- E の赤道への制限は χ（Part 257 の `charU`）。 -/
+theorem resE_extChi (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
+    resE a (extChi χ) = PAG.Part257.charU χ :=
+  funext (fun x => extChi_eqPt χ x)
+
+/-! ## 3. 法 N の式をそのまま使うと両立しない（証人） -/
+
+/-- 法 2 の自明な指標（導手 1）では、法 2 の式 χ(a)·χ⁻¹(b) は点 0 で 0、
+法 1 の式を引き戻したものは 1。法 N の式 χ(a)χ̄(b) は、原始的でない χ では引き戻しと両立しない。 -/
+theorem chiPt_not_compat :
+    chiPt (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) (zeroPt 2) ≠
+      chiPt (1 : DirichletCharacter ℂ 1) (red (one_dvd 2) (zeroPt 2)) := by
+  have h0 : ¬ IsUnit (0 : ZMod 2) := not_isUnit_zero
+  show (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) 0 *
+      (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1))⁻¹ 1 ≠
+    (1 : DirichletCharacter ℂ 1) (castHom (one_dvd 2) (ZMod 1) 0) *
+      (1 : DirichletCharacter ℂ 1)⁻¹ (castHom (one_dvd 2) (ZMod 1) 1)
+  rw [MulChar.map_nonunit _ h0, zero_mul, map_one, inv_one]
+  rw [MulChar.one_apply (isUnit_of_subsingleton _), MulChar.one_apply (isUnit_of_subsingleton _)]
+  norm_num
+
+/-! ## 4. 素数冪の法では Part 25（PAG29）の殻 0 のケット -/
+
+section ket
+
+variable {p : ℕ} [hp : Fact p.Prime]
+
+/-- **殻 0 のケットとの一致**：1 ≤ c ≤ K のとき、P¹(ℤ/p^K) の殻 0 の南ケット `ketS_proj K 0 c`（Part 25（PAG29））は、
+法 p^c の χ(a)·χ̄(b) の引き戻しの |S_0|^(−1/2) 倍。 -/
+theorem ketS_proj_zero_eq (K c : ℕ) (hK : 1 ≤ K) (h : 0 + c ≤ K) (hc : 1 ≤ c)
+    (χ : DirichletCharacter ℂ (p ^ c)) :
+    PAG.Part29.ketS_proj K hK 0 c h χ = fun q =>
+      (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
+        chiPt χ (red (pow_dvd_pow p (by omega : c ≤ K)) q) := by
+  apply (PAG.Part28.projFunEquiv K hK).injective
+  apply Subtype.ext
+  rw [PAG.Part29.projFun_ketS]
+  refine Prod.ext (funext (fun x => ?_)) (funext (fun y => ?_))
+  · rw [PAG.Part28.projFun_south]
+    show PAG.Part21.ket K 0 c h χ x = (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
+      (χ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) x) *
+        χ⁻¹ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) 1))
+    rw [PAG.Part24.ket0_apply, map_one, map_one, mul_one]
+  · rw [PAG.Part28.projFun_north]
+    show (PAG.Part23.extS (PAG.Part21.ket K 0 c h χ)).2 y = (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
+      (χ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) 1) *
+        χ⁻¹ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) y))
+    rw [map_one, map_one, one_mul]
+    unfold PAG.Part23.extS
+    dsimp only
+    split_ifs with hy
+    · rw [PAG.Part24.ket0_apply, PAG.Part24.chi_cast_inv (by omega) χ hy]
+    · have hy' : ¬ IsUnit (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) y) := by
+        intro hu
+        apply hy
+        rw [castHom_apply, ZMod.cast_eq_val, ZMod.isUnit_iff_coprime,
+          Nat.coprime_pow_right_iff (by omega)] at hu
+        rw [← ZMod.natCast_zmod_val y, ZMod.isUnit_iff_coprime,
+          Nat.coprime_pow_right_iff (by omega)]
+        exact hu
+      rw [MulChar.map_nonunit _ hy', mul_zero]
+
+end ket
+
+end PAG.Part268
+
+#print axioms PAG.Part268.chiPt_eqPt
+#print axioms PAG.Part268.chiPt_Wproj
+#print axioms PAG.Part268.chiPt_torus
+#print axioms PAG.Part268.extChi_eqPt
+#print axioms PAG.Part268.extChi_changeLevel
+#print axioms PAG.Part268.extChi_torus
+#print axioms PAG.Part268.pullP_extChi
+#print axioms PAG.Part268.resE_extChi
+#print axioms PAG.Part268.chiPt_not_compat
+#print axioms PAG.Part268.ketS_proj_zero_eq
+```
+
+## §3 ノート（全文）
+```markdown
+# アーデル射影幾何 — Part 264（PAG268、短期層の小さいノート）：P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致
+
+（2026-11-25 夜。題と主張は PAG268.lean の形式文から起こした。）
+
+## §1 問いの出所
+
+- 基礎文書の索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）と、Part 263（PAG267）で外に残った候補 C2（`Uinf` を P¹ の上の関数の極限に持ち上げる作用素）。
+- 推薦案 `notes/pag2_p1_lift_preregistration.md` §4（C2-a）。2026-11-25 19:13 の著者の指示「お勧めで進めてください」を受けて、構築側が選んで着手した（CLAUDE.md §4 の選択の委任）。
+- 盲検の問いテスト（`records/p1_lift/`）の答えで、持ち上げ V そのものは一意でないことが分かったので、Lean にするのは一意に決まる側（トーラスと両立する延長）とその 2 チャートのモデルとの結び目にした。
+
+## §2 Lean に入った文（PAG268.lean、定理 14、sorry 0・警告 0、#print axioms は標準の 3 つ）
+
+1. `chiPt χ`：[a:b] ↦ χ(a)·χ⁻¹(b) は P¹(ℤ/N) の上で well-defined。`chiPt_eqPt`（赤道では χ）、`chiPt_Wproj`（W で χ⁻¹ の関数に）、`chiPt_torus`（トーラスの作用 `torus u`：[a:b] ↦ [u a : b] で χ(u) 倍。`torus_eqPt`：赤道の上では掛け算）。補助：`mul_inv_apply_unit`、`chiPt_mk`、`chiPt_red_congr`（型の違う法の間の受け渡し）。
+2. `extChi χ`（原始指標 χ* の `chiPt` を導手から法 N へ引き戻したもの）：`extChi_eqPt`・`resE_extChi`（赤道への制限は χ）、`extChi_changeLevel`・`pullP_extChi`（引き戻しと両立）、`extChi_torus`（トーラスで χ(u) 倍）。
+3. `chiPt_not_compat`：法 N の式をそのまま使うと、原始的でない χ では両立しない（法 2 の自明な指標、点 0：左辺 0、右辺 1）。
+4. `ketS_proj_zero_eq`：p 素数、1 ≤ c ≤ K のとき、Part 25（PAG29）の殻 0 の南ケット `ketS_proj K 0 c` = |S_0|^(−1/2)·（法 p^c の `chiPt χ` の引き戻し）。
+
+## §3 読み（Lean の外）
+
+- 盲検の照合者によれば、引き戻しと両立し赤道で恒等な延長の族は多いが、トーラスとも両立する族は一意で `extChi` で与えられる（確信度：高）。したがって 4 は「2 チャートのモデルの殻 0 のケットは、素数冪の法での一意な等変延長（の規格化の定数倍）」と読める（χ が原始的でない場合は、法 p^c の式と原始指標の式が違うので、この読みは原始指標のときに限る）。
+- `Uinf` の持ち上げは存在するが一意でない（ユニタリ・トーラス・W・引き戻しの条件を全部課しても、素数ごとの ±1 の自由度。照合者の数値の反例）。局所性の条件で一意（照合者の確信度：中〜高）。W とは可換にできない（W V W = V⁻¹）。索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）は、この文書の後も残る。材料としては「P¹ の上の作用素への持ち上げは自然には一意に決まらない」。
+- 4 の 1 ≤ c：c = 0 では、殻 0 のケットは北のチャートの単数でない点で 0、`chiPt`（法 1）の引き戻しは定数 1 で、等式は破れる（構築側と独立照合の照合者の手計算。Lean にしていない）。
+- 主指標の `extChi` は全点（0 と ∞ を含む）で 1、導手 > 1 の指標の `extChi` は 0 と ∞ で 0（独立照合の指摘）。
+- 対照群：盲検の照合者は、答えは F_q[t] でも同じ形とした。ℚ に固有の算術は運ばない。
+
+## §4 ラベル（見込み。閉鎖で確定）
+
+- 1〜4：［再導出（小さい）］。新規候補なし。兆候 4 は続く（Part 249〜264 で 16 パート連続）。
+
+## §5 内部照合
+
+- 着手前：P¹ の上の指標の関数としては、Part 19（PAG23）の殻ケット `kS` と Part 25（PAG29）の `ketS_proj` があった（推薦案 §0）。4 でそれと結んだ。
+- 使ったもの：Part 254（PAG258）の `pullL_charU`、Part 24（PAG28）の `projFun_south`・`projFun_north`、Part 20（PAG24）の `ket0_apply`・`chi_cast_inv`、Part 25（PAG29）の `projFun_ketS`。
+- 機械的な照合（全宣言 4409 件、対象 18 件、候補の組 144、照合 256 回、一致なし。記録 `records/audit268/internal/`）。網羅ではない。近いもの（C）：Part 28（PAG32）の `negProj`（トーラスの u = −1）、Part 252（PAG256）の `inv_apply_units_inv`。
+
+## §6 照合
+
+- 独立照合（形式文と定義だけ、2026-11-25 夜、約 160 秒、`records/audit268/outputs/check_output.md`。依頼文 `records/audit268/request_formal.md`、入力 `records/audit268/input_formal.md`）：逆翻訳は意図どおり。非空虚性の証人はすべての定理にある。除去テスト：1 ≤ c は外すと反例（c = 0、p = 2、K = 1、点 ∞）、原始指標の代わりに χ を使うと引き戻しとの両立だけが崩れる（`chiPt_not_compat`）、1 ≤ K は冗長、[NeZero N] は不要の見込み、[NeZero M] は M = 0 で崩れる見込み、`chiPt_red_congr` の d₁ = d₂ は型のための仮定。
+- 指摘：主指標の `extChi` は 0 と ∞ でも 1（導手 > 1 では 0）、`extChi` の定義の [NeZero N]、4 と `extChi` の一致は原始指標のとき、`charU` の重複の可能性。形式文は変えず、冒頭の説明とこのノートに注意を書いた。`charU` は鎖に 1 つだけ（Part 257（PAG261）、PAG258 はそれを開いて使う）で、重複はない（言葉の検索）。
+- この直しは、閉じるときの統合照合の入力に含める（台帳 L16）。
+
+## §7 収束アラームの報告
+
+- 辞書：§23 に Part 264 の名前の行を足した。
+- 文献照合：推薦案の盲検の問いテストで実施した（`records/p1_lift/`、検索 3 回）。
+- 兆候 4：続いている。
+```
+
+## §4 独立照合の出力（全文）
+# 独立照合の出力（PAG268、2026-11-25）
+
+（照合者の最終報告の全文を写した。）
+
+# PAG268 照合の成果物（逆翻訳・非空虚性の証人・除去テスト・気づいた点）
+
+ファイルは指示どおり 1 回だけ読みました。計算はすべて手計算で、Mathlib の内部の定義について推測した箇所は、そのつど確信度を付けています。
+
+## 0. 使う定義の言葉による説明
+
+- **Unimod N**：$(\mathbb Z/N)^2$ の組 $(x,y)$ のうち、$sx+ty=1$ となる $s,t$ があるもの（単模な組）。
+- **ProjLine N**：単模な組を、単数倍 $(x,y)\sim(ux,uy)$（$u\in(\mathbb Z/N)^\times$）で割った集合 $\mathbb P^1(\mathbb Z/N)$。類を $[x:y]$ と書きます。$N=1$ では 1 点です。$N=0$ では $\mathbb Z/0=\mathbb Z$ なので $\mathbb P^1(\mathbb Z)$ になります。
+- **Wproj**：$[x:y]\mapsto[y:x]$。
+- **red**（$N\mid M$）：成分ごとに法 $N$ へ落とす写像 $\mathbb P^1(\mathbb Z/M)\to\mathbb P^1(\mathbb Z/N)$。
+- **zeroPt** は $[0:1]$。**eqPt x** は単数 $x$ について $[x:1]$。
+- **Lvl**：正の整数のこと。順序は整除です。
+- **pullP**：$\mathbb P^1(\mathbb Z/a)$ の上の関数 $f$ を $f\circ\mathrm{red}$ に送る、$\mathbb P^1(\mathbb Z/b)$ の上の関数への線形写像（$a\mid b$）。
+- **resE**：関数 $f$ を、単数 $x$ ごとに $f([x:1])$ を返す単数群上の関数に送る写像。
+- **charU χ**：ディリクレ指標 $\chi$ を単数群に制限したもの。
+- **χ⁻¹**：ディリクレ指標の群での逆元です。単数では $\chi(u)^{-1}=\overline{\chi(u)}$、非単数では 0 になります。したがって関数として $\chi^{-1}=\overline\chi$ です（$N=1$ でも成り立ちます）。
+- **chiPt χ**：$[x:y]\mapsto \chi(x)\,\chi^{-1}(y)=\chi(x)\overline{\chi(y)}$。値は単数倍で変わりません（$\chi(u)\chi^{-1}(u)=1$）。0 でない値をとるのは $x,y$ がともに単数のときだけで、そのとき値は $\chi(x/y)$ です。
+- **torusU / torus u**：$[x:y]\mapsto[ux:y]$。南の座標 $z=x/y$ では $z\mapsto uz$、北の座標 $y/x$ では $u^{-1}$ 倍になります。$[0:1]$ と $[1:0]$ は動きません。
+- **extChi χ**：$\chi$ の導手を $f$、$\chi$ を誘導する原始指標（法 $f$）を $\chi^*$ とします。$q\in\mathbb P^1(\mathbb Z/N)$ を法 $f$ に落とした点で $\mathrm{chiPt}\,\chi^*$ を評価した値です。式で書くと $[x:y]\mapsto\chi^*(\bar x)\,\overline{\chi^*(\bar y)}$（バーは法 $f$ での剰余）。
+- **sz p K u** $=p^{K-1-u}(p-1)$（自然数の引き算）。$u=0$、$K\ge1$ では $\varphi(p^K)$ です。
+- **ket K 0 c**（ket0_apply による）：法 $p^c$ の関数 $f$ を、$x\mapsto \varphi(p^K)^{-1/2}\,f(x \bmod p^c)$ という $\mathbb Z/p^K$ の上の関数に送ります。
+- **extS h**：南のチャートの関数 $h$ と、北のチャートの関数「$y$ が単数なら $h(y^{-1})$、そうでなければ 0」の組。
+- **kS** $=\mathrm{extS}(\mathrm{ket}\dots\chi)$。
+- **projFunEquiv**：$\mathbb P^1(\mathbb Z/p^K)$ の上の関数 $\Phi$ と、貼り合わせ条件を満たすチャートの組 $(\Phi([x:1]))_x,\ (\Phi([1:y]))_y$ との線形同型。
+- **ketS_proj w c χ**：チャートの組 kS を projFunEquiv で $\mathbb P^1$ の上の関数に戻したもの。
+
+## 1. 逆翻訳
+
+- **mul_inv_apply_unit**：任意の $N$、法 $N$ のディリクレ指標 $\chi$、単数 $u$ について $\chi(u)\chi^{-1}(u)=1$。
+- **chiPt_mk**：任意の単模な組 $(x,y)$ について $\mathrm{chiPt}\chi([x:y])=\chi(x)\chi^{-1}(y)$。
+- **chiPt_eqPt**：単数 $x$ について $\mathrm{chiPt}\chi([x:1])=\chi(x)$。
+- **chiPt_Wproj**：任意の点 $q$ について $\mathrm{chiPt}\chi(W q)=\mathrm{chiPt}\,\chi^{-1}(q)$。座標で書くと、$[y:x]$ での $\chi$ の値は $[x:y]$ での $\bar\chi$ の値に等しい、ということです。
+- **torus_eqPt**：単数 $u,x$ について、$u$ の作用は $[x:1]$ を $[ux:1]$ に送る。
+- **chiPt_torus**：任意の $u$、$q$ について $\mathrm{chiPt}\chi(u\cdot q)=\chi(u)\,\mathrm{chiPt}\chi(q)$。chiPt χ はトーラスの作用の固有関数で、固有値は $\chi(u)$ です。
+- **chiPt_red_congr**：$d_1=d_2$、$d_1,d_2\mid M$ とし、法 $d_1$ の指標 $\chi_1$ と法 $d_2$ の指標 $\chi_2$ がすべての整数で同じ値をとるとします。このとき $\mathbb P^1(\mathbb Z/M)$ のすべての点 $q$ で $\mathrm{chiPt}\chi_1(\mathrm{red}\,q)=\mathrm{chiPt}\chi_2(\mathrm{red}\,q)$（型を運ぶための補題）。
+- **extChi_eqPt**（$N\ne0$）：単数 $x$ について $\mathrm{extChi}\chi([x:1])=\chi(x)$。
+- **extChi_changeLevel**（$N\mid M$、$M\ne0$）：法 $N$ の $\chi$ を法 $M$ に持ち上げた指標の extChi は、extChi χ を red で引き戻したものに等しい。
+- **extChi_torus**（$N\ne0$）：$\mathrm{extChi}\chi(u\cdot q)=\chi(u)\,\mathrm{extChi}\chi(q)$。
+- **pullP_extChi**：正の整数 $a\mid b$ について、extChi χ の引き戻しは、$\chi$ を法 $b$ に持ち上げた指標の extChi に等しい。
+- **resE_extChi**：正の整数 $a$ について、extChi χ を単数 $x$ の点 $[x:1]$ に制限すると、$\chi$ の単数群への制限に等しい。
+- **chiPt_not_compat**：法 1 の自明指標を法 2 に持ち上げた指標の chiPt の $[0:1]$ での値は、法 1 の自明指標の chiPt の $\mathrm{red}([0:1])$ での値と異なる。
+- **ketS_proj_zero_eq**：$p$ を素数とし、$1\le c\le K$ とします（$1\le K$ も仮定にありますが、他の仮定から出ます）。法 $p^c$ の指標 $\chi$ について、$w=0$ のケット $\mathrm{ketS\_proj}(0,c,\chi)$ は関数 $q\mapsto \varphi(p^K)^{-1/2}\,\mathrm{chiPt}\chi(q \bmod p^c)$ に等しい。
+
+## 2. 非空虚性の証人
+
+- **mul_inv_apply_unit**：$N=5$、$\chi(2)=i$ となる位数 4 の指標、$u=2$ とします。$i\cdot(-i)=1$。
+- **chiPt_eqPt / chiPt_mk**：同じ $\chi$ で $[2:1]$ での値は $\chi(2)=i$ です。$[2:3]$ では $\chi(2)\overline{\chi(3)}=i\cdot\overline{(-i)}=i\cdot i=-1$ で、これは $\chi(2\cdot3^{-1})=\chi(4)=-1$ と合います。
+- **chiPt_Wproj**：同じ $\chi$、$q=[2:1]$ とします。左辺 $\mathrm{chiPt}\chi([1:2])=\chi^{-1}(2)=-i$、右辺 $\chi^{-1}(2)=-i$ で一致します。
+- **torus_eqPt / chiPt_torus**：$N=5$、$\chi$ をルジャンドル記号、$u=2$、$q=[1:1]$ とします。$2\cdot[1:1]=[2:1]$ で、値は $-1=\chi(2)\cdot1$ です。
+- **chiPt_red_congr**：$d_1=d_2=4$、$\chi_1=\chi_2=\chi_4$（法 4 の非自明な指標）、$M=12$、$q=[1:3]$ とします。両辺とも $\chi_4(1)\overline{\chi_4(3)}=-1$ です。
+- **extChi_eqPt / extChi_torus**：$N=12$、$\chi$ を $\chi_4$ が誘導する指標（導手 4）とします。
+  - $\mathrm{extChi}\chi([5:1])=\chi_4(1)=1=\chi(5)$ です。
+  - 内容のある点として $q=[1:3]$ では、extChi は $\chi_4(1)\overline{\chi_4(3)}=-1$ ですが、$\mathrm{chiPt}\chi([1:3])=0$ です（3 は法 12 で単数でない）。extChi が chiPt と本当に違う場所はここです。
+  - torus は $u=5$ で $[5:3]$ に移り、値は $\chi_4(1)\overline{\chi_4(3)}=-1=\chi(5)\cdot(-1)$ と合います。
+- **extChi_changeLevel / pullP_extChi**：$N=4$、$M=12$、$\chi=\chi_4$、$q=[1:3]$ とします。左辺は上の $-1$、右辺は $\mathrm{chiPt}\chi_4([1:3])=-1$ です。
+  - もう一つの例として、$N=1$、$M=2$、$\chi$ を自明指標とします。$\mathbb P^1(\mathbb Z/2)$ の 3 点すべてで両辺は 1 です。
+- **resE_extChi**：$a=5$、$\chi$ をルジャンドル記号とします。$x=2$ で $-1=\chi(2)$ です。
+- **chiPt_not_compat**：左辺は $\chi_2(0)\chi_2^{-1}(1)=0$ です。右辺は $\mathbb P^1(\mathbb Z/1)$ の唯一の点での値で、$\mathbb Z/1$ では $0=1$ なので $1$ です。したがって $0\ne1$。
+- **ketS_proj_zero_eq**：$p=3$、$K=2$、$c=1$、$\chi$ を法 3 のルジャンドル記号とします。$\mathrm{sz}=3\cdot2=6$ です。$\mathbb P^1(\mathbb Z/9)$ の 12 点での値は次のとおりです。
+  - $[1:1],[4:1],[7:1],[1:4],[1:7]$ などで $1/\sqrt6$
+  - $[2:1],[5:1],[8:1]$ で $-1/\sqrt6$
+  - $[0:1],[3:1],[6:1],[1:0],[1:3],[1:6]$ で 0
+  
+  2 乗和は $6/6=1$ です。
+
+## 3. 除去テスト
+
+- **ketS_proj_zero_eq の $1\le c$**：外すと反例があります（反例が作れる）。
+  - $p=2$、$K=1$、$c=0$、$\chi$ を法 1 の自明指標とします。$\mathrm{sz}=1$ です。
+  - 左辺の南のチャートでは $\mathrm{ket}(x)=1$ なので、$[0:1]\mapsto1$、$[1:1]\mapsto1$ です。
+  - 点 $[1:0]$ は北のチャートの $y=0$ です。$0$ は単数でないので、左辺の値は 0 です。
+  - 右辺は $\mathrm{chiPt}$ を $\mathbb P^1(\mathbb Z/1)$ で評価するので恒等的に 1 です。
+  - よって $[1:0]$ で $0\ne1$。この仮定は必要です。
+- **$1\le K$**：$h: c\le K$ と $1\le c$ から出るので、文の制限としては冗長です。ただし ketS_proj の型（projFunEquiv の引数）には必要です。
+- **extChi で $\chi^*$ の代わりに $\chi$ を使う**（つまり extChi を chiPt にする）：
+  - eqPt、torus、resE の版はそのまま成り立ちます（chiPt_eqPt と chiPt_torus がそれ自体です）。
+  - changeLevel と pullP の版は崩れます。反例は chiPt_not_compat そのもので、$N=1$、$M=2$、自明指標、$q=[0:1]$ のとき $0\ne1$ です。$a=1$、$b=2$ として pullP の版でも同じです。
+  - したがって、原始指標が中身を運んでいるのは level change との両立だけです。
+- **extChi_eqPt / extChi_torus の [NeZero N]**：不要に見えます（確信度：中）。
+  - Mathlib の導手は、指標がその法を経由する $d$ の最小値（sInf）です。法 0 では $0\mid0$ なので導手は 0 となり、$\chi^*=\chi$、red は恒等になるはずです。
+  - そうなら $N=0$ でも、両定理は chiPt の版に帰着して成り立ちます。
+- **extChi_changeLevel の [NeZero M]**：外すと反例が作れる見込みです（確信度：中。上と同じ「法 0 の導手は 0」という推測に依存します）。
+  - $N=1$、$M=0$、$\chi$ を自明指標、$q=[0:1]\in\mathbb P^1(\mathbb Z)$ とします。
+  - 左辺は $\mathrm{chiPt}(\text{持ち上げ})([0:1])$ です。0 は $\mathbb Z$ で単数でないので、値は 0 です。
+  - 右辺は 1 です。
+- **chiPt_red_congr の $d_1=d_2$**：不要に見えます。
+  - 整数への持ち上げ $\tilde x,\tilde y$ をとると、両辺はそれぞれ $\chi_i(\tilde x)\chi_i^{-1}(\tilde y)$ です。$\chi_1,\chi_2$ が整数上で一致すれば、逆元も整数上で一致します。
+  - 例えば $d_1=2$、$d_2=4$ の自明指標どうしは整数上で一致し（どちらも $a$ が奇数のとき 1、偶数のとき 0）、結論も成り立ちます。
+  - 型を運ぶために置いた仮定と読めます。
+- **chiPt_red_congr の hχ**：外すと反例があります。$d=M=5$、$\chi_1$ を自明指標、$\chi_2$ をルジャンドル記号、$q=[2:1]$ とすると、$1\ne-1$ です。
+- **ほかの定理**：型以外に仮定がありません（mul_inv_apply_unit、chiPt_*、torus_eqPt、pullP_extChi、resE_extChi）。Lvl は正なので、pullP_extChi と resE_extChi には法 0 が入りません。
+
+## 4. 気づいた点
+
+1. **法 1 の扱い**：$\mathbb P^1(\mathbb Z/1)$ は 1 点で、$\mathbb Z/1$ では $0$ が単数です。そのため $\mathrm{chiPt}\,1=1$ になります。
+   - この帰結として、導手 1 の指標（主指標）の extChi は $\mathbb P^1(\mathbb Z/N)$ の全点（$0$ と $\infty$ を含む）で恒等的に 1 です。
+   - 一方、導手 $>1$ の指標の extChi は、法 $f$ での剰余が単数でない点で 0 です。とくに $[0:1]$ と $[1:0]$ では 0 です。
+   - 「自明か非自明か」で $0$ と $\infty$ での値が 1 から 0 に跳ぶので、この扱いは意図どおりか確認してください。
+2. **χ⁻¹ と複素共役**：関数として $\chi^{-1}=\bar\chi$ です（単数では $|\chi|=1$、非単数ではどちらも 0、$N=1$ では両方 1）。問題はありません。chiPt_Wproj は「$W$ は $\chi$ を $\bar\chi$ に変える」と読めます。
+3. **トーラスの作用の向き**：$[x:y]\mapsto[ux:y]$ で、南の座標を $u$ 倍、北の座標を $u^{-1}$ 倍します。固有値は $\chi(u)$ です（$\chi(u)^{-1}$ ではありません）。$W\circ(u\cdot)\circ W=(u^{-1}\cdot)$ となり、chiPt_Wproj と整合します。可換群なので、作用の左右の問題はありません。
+4. **extChi が well-defined な族か**：$\chi^*$ は Classical.choose で選ばれますが、原始指標は一意なので、関数としては $\chi$ だけで決まります。extChi_changeLevel と pullP_extChi が、整除の系の上での両立を与えています。
+   - ただし法 0（$M=0$）では両立が崩れる見込みです（§3）。
+   - さらに、注記には「節 2 の extChi では [NeZero N] を仮定に入れ、extChi_changeLevel では外した」とあります。def extChi 自体が [NeZero N] を引数に取るなら、extChi_changeLevel の右辺 extChi χ はどうやって $N\ne0$ のインスタンスを得ているのか、入力からは分かりません。extChi の実際の引数の並びの確認を勧めます。
+5. **ketS_proj_zero_eq と extChi の関係**：右辺は chiPt χ（法 $p^c$）の引き戻しで、extChi ではありません。
+   - 原始的でない $\chi$（例：法 $p$ の主指標、$c=1$）では、ketS_proj は $\varphi(p^K)^{-1/2}\,\mathrm{extChi}(\text{持ち上げた}\chi)$ とは異なります。主指標の場合、後者は全点で定数になります。
+   - 両者が一致するのは、$\chi$ が法 $p^c$ で原始的なときです。「ケットは extChi の正規化である」と散文で書く場合は、この条件が要ります。
+6. **正規化の因子**：$\varphi(p^K)^{-1/2}$ です。値が 0 でない点は $[x:1]$（$x$ は単数）のちょうど $\varphi(p^K)$ 個で、数え上げ測度で単位ノルムになります。これは $w=0$ のときだけの文です。
+7. **charU の重複の可能性**：resE_extChi は PAG.Part257.charU を名前空間つきで使っています。一方、前提 3 では pullL_charU（Part258）も charU を使っており、Part257 と Part258 に同じ式の charU が 2 つある可能性があります（第 12 の型：内部の重複）。入力の範囲では、どちらの名前空間の定義かは判別できません。
+8. **resE の範囲**：eqPt は単数にしか定義されていないので、resE_extChi は $[x:1]$（$x$ が単数）以外の点について何も言いません。extChi の内容は、extChi_changeLevel のほうにあります。
+
+## 使ったツールと読んだ範囲
+
+Read を 1 回だけ使い、`/home/claude/ardel-projective-geometry/records/audit268/input_formal.md` の全 207 行を読みました。ほかのファイル、コードの実行、ウェブは使っていません。
+
+## §5 独立照合に渡した形式文と定義（全文）
+# 入力：形式文と定義
+
+Lean 4 / Mathlib。定理の証明は省略し、定義は全文を写した（コメントと docstring は除いた。本体を省略した定義はそう書いた）。検査対象はエラー 0・警告 0 で通っており、`#print axioms` は標準の 3 つだけ。
+
+## 前提 1：PAG27（名前空間 PAG.Part27）
+```lean
+def Unimod (N : ℕ) := {v : ZMod N × ZMod N // ∃ s t : ZMod N, s * v.1 + t * v.2 = 1}
+
+def projSetoid (N : ℕ) : Setoid (Unimod N) where
+  r v w := ∃ u : (ZMod N)ˣ, w.1.1 = u * v.1.1 ∧ w.1.2 = u * v.1.2
+  iseqv := {
+    refl := fun v => ⟨1, by simp, by simp⟩
+    symm := fun {v w} ⟨u, h1, h2⟩ => ⟨u⁻¹, by rw [h1, ← mul_assoc, Units.inv_mul, one_mul],
+      by rw [h2, ← mul_assoc, Units.inv_mul, one_mul]⟩
+    trans := fun {v w z} ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩ => ⟨u' * u, by rw [h1', h1, Units.val_mul, mul_assoc],
+      by rw [h2', h2, Units.val_mul, mul_assoc]⟩ }
+
+def ProjLine (N : ℕ) := Quotient (projSetoid N)
+
+def mk (v : Unimod N) : ProjLine N := Quotient.mk (projSetoid N) v
+
+theorem mk_eq_mk {v w : Unimod N} (u : (ZMod N)ˣ) (h1 : w.1.1 = u * v.1.1) (h2 : w.1.2 = u * v.1.2) :
+    mk v = mk w := …（証明は省略）
+
+def Wproj : ProjLine N → ProjLine N :=
+  Quotient.lift (fun v => mk ⟨(v.1.2, v.1.1), swap_unimod v⟩)
+    (fun _v _w ⟨u, h1, h2⟩ => mk_eq_mk u h2 h1)
+```
+
+## 前提 2：PAG267（名前空間 PAG.Part267）
+```lean
+def redU (h : N ∣ M) (v : Unimod M) : Unimod N :=
+  ⟨(castHom h (ZMod N) v.1.1, castHom h (ZMod N) v.1.2), by
+    obtain ⟨s, t, hst⟩ := v.2
+    exact ⟨castHom h (ZMod N) s, castHom h (ZMod N) t, by
+      rw [← map_mul, ← map_mul, ← map_add, hst, map_one]⟩⟩
+
+def red (h : N ∣ M) : ProjLine M → ProjLine N :=
+  Quotient.lift (fun v => mk (redU h v)) (fun _v _w ⟨u, h1, h2⟩ =>
+    mk_eq_mk (unitsMap h u)
+      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h1, map_mul]; rfl)
+      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h2, map_mul]; rfl))
+
+theorem red_comp (h₁ : N ∣ M) (h₂ : M ∣ L) (q : ProjLine L) :
+    red h₁ (red h₂ q) = red (dvd_trans h₁ h₂) q := …（証明は省略）
+
+def zeroU (N : ℕ) : Unimod N := ⟨(0, 1), ⟨0, 1, by simp⟩⟩
+
+def zeroPt (N : ℕ) : ProjLine N := mk (zeroU N)
+
+def eqU (x : (ZMod N)ˣ) : Unimod N := ⟨((x : ZMod N), 1), ⟨0, 1, by simp⟩⟩
+
+def eqPt (x : (ZMod N)ˣ) : ProjLine N := mk (eqU x)
+
+theorem red_eqPt (h : N ∣ M) (x : (ZMod M)ˣ) : red h (eqPt x) = eqPt (unitsMap h x) := …（証明は省略）
+
+abbrev Fsp (a : Lvl) : Type := ProjLine a.val → ℂ
+
+noncomputable def pullP (a b : Lvl) (h : a ≤ b) : Fsp a →ₗ[ℂ] Fsp b where
+  toFun f q := f (red (N := a.val) (M := b.val) h q)
+  map_add' _ _ := rfl
+  map_smul' _ _ := rfl
+
+noncomputable def resE (a : Lvl) : Fsp a →ₗ[ℂ] Gsp a where
+  toFun f x := f (eqPt x)
+  map_add' _ _ := rfl
+  map_smul' _ _ := rfl
+```
+
+## 前提 3：PAG258・PAG257（名前空間 PAG.Part258・PAG.Part257）
+```lean
+noncomputable def pullL {M : ℕ} (hNM : N ∣ M) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod M)ˣ → ℂ) where
+  toFun f u := f (ZMod.unitsMap hNM u)
+  map_add' _ _ := rfl
+  map_smul' _ _ := rfl
+
+theorem pullL_charU {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
+    pullL hNM (charU χ) = charU (changeLevel hNM χ) := …（証明は省略）
+
+structure Lvl where
+  
+  val : ℕ
+  pos : 0 < val
+deriving DecidableEq
+
+abbrev Gsp (a : Lvl) : Type := (ZMod a.val)ˣ → ℂ
+
+def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u
+```
+（Lvl の順序は a ≤ b ↔ a.val ∣ b.val。各 a に NeZero a.val のインスタンスがある。）
+
+## 前提 4：2 チャートのモデル（PAG19・PAG21・PAG23・PAG24・PAG28・PAG29。p は素数）
+```lean
+def sz (p K u : ℕ) : ℕ := p ^ (K - 1 - u) * (p - 1)
+
+noncomputable def ket (K u c : ℕ) (huc : u + c ≤ K) (χ : ZMod (p ^ c) → ℂ) : ZMod (p ^ K) → ℂ := …（本体は省略）
+
+abbrev P1F (N : ℕ) := (ZMod N → ℂ) × (ZMod N → ℂ)
+
+noncomputable def extS (h : ZMod N → ℂ) : P1F N := (h, fun y => if IsUnit y then h y⁻¹ else 0)
+
+noncomputable def kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) : P1F (p ^ K) :=
+  extS (ket K w c h χ)
+
+theorem ket0_apply (K c : ℕ) (h : 0 + c ≤ K) (f : ZMod (p ^ c) → ℂ) (x : ZMod (p ^ K)) :
+    ket K 0 c h f x = (((Real.sqrt (sz p K 0))⁻¹ : ℝ) : ℂ) *
+      f (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) x) := …（証明は省略）
+
+theorem chi_cast_inv {K c : ℕ} (hcK : c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) {x : ZMod (p ^ K)}
+    (hx : IsUnit x) :
+    χ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x⁻¹)
+      = χ⁻¹ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x) := …（証明は省略）
+
+noncomputable def projFunEquiv : (ProjLine (p ^ K) → ℂ) ≃ₗ[ℂ] compatSub (p ^ K) :=
+  (LinearEquiv.funCongrLeft ℂ ℂ (projEquiv K hK)).trans (ptEquiv (p ^ K))
+
+theorem projFun_south (Φ : ProjLine (p ^ K) → ℂ) (x : ZMod (p ^ K)) :
+    (projFunEquiv K hK Φ).1.1 x = Φ (mk ⟨(x, 1), 0, 1, by simp⟩) := …（証明は省略）
+
+theorem projFun_north (Φ : ProjLine (p ^ K) → ℂ) (y : ZMod (p ^ K)) :
+    (projFunEquiv K hK Φ).1.2 y = Φ (mk ⟨(1, y), 1, 0, by simp⟩) := …（証明は省略）
+
+noncomputable def ketS_proj (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
+    ProjLine (p ^ K) → ℂ :=
+  (projFunEquiv K hK).symm ⟨kS K w c h χ, compat_extS _⟩
+
+theorem projFun_ketS (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
+    (projFunEquiv K hK (ketS_proj K hK w c h χ)).1 = kS K w c h χ := …（証明は省略）
+```
+（P1F N = (ZMod N → ℂ) × (ZMod N → ℂ)：南のチャートの関数と北のチャートの関数の組。projFunEquiv は ProjLine (p^K) の上の関数と、貼り合わせ条件を満たす組の ℂ 線形同型。）
+
+## 検査対象：PAG268（名前空間 PAG.Part268）
+```lean
+namespace PAG.Part268
+open ZMod PAG.Part27 PAG.Part258 PAG.Part267 DirichletCharacter
+variable {N : ℕ}
+-- 節 2（extChi・extChi_eqPt・extChi_torus）では [NeZero N] が仮定に入る（extChi_changeLevel では外した）。
+-- 節 4（ketS_proj_zero_eq）では variable {p : ℕ} [hp : Fact p.Prime]。
+
+theorem mul_inv_apply_unit (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
+    χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1 := …（証明は省略）
+
+noncomputable def chiPt (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
+  Quotient.lift (fun v : Unimod N => χ v.1.1 * χ⁻¹ v.1.2) (fun v w ⟨u, h1, h2⟩ => by
+    show χ v.1.1 * χ⁻¹ v.1.2 = χ w.1.1 * χ⁻¹ w.1.2
+    rw [h1, h2, map_mul, map_mul]
+    calc χ v.1.1 * χ⁻¹ v.1.2
+        = (χ (u : ZMod N) * χ⁻¹ (u : ZMod N)) * (χ v.1.1 * χ⁻¹ v.1.2) := by
+          rw [mul_inv_apply_unit, one_mul]
+      _ = χ (u : ZMod N) * χ v.1.1 * (χ⁻¹ (u : ZMod N) * χ⁻¹ v.1.2) := by ring)
+
+theorem chiPt_mk (χ : DirichletCharacter ℂ N) (v : Unimod N) :
+    chiPt χ (mk v) = χ v.1.1 * χ⁻¹ v.1.2 := …（証明は省略）
+
+theorem chiPt_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : chiPt χ (eqPt x) = χ x := …（証明は省略）
+
+theorem chiPt_Wproj (χ : DirichletCharacter ℂ N) (q : ProjLine N) :
+    chiPt χ (Wproj q) = chiPt χ⁻¹ q := …（証明は省略）
+
+def torusU (u : (ZMod N)ˣ) (v : Unimod N) : Unimod N :=
+  ⟨((u : ZMod N) * v.1.1, v.1.2), by
+    obtain ⟨s, t, h⟩ := v.2
+    refine ⟨s * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), t, ?_⟩
+    have hu : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := Units.inv_mul u
+    linear_combination h + s * v.1.1 * hu⟩
+
+def torus (u : (ZMod N)ˣ) : ProjLine N → ProjLine N :=
+  Quotient.lift (fun v => mk (torusU u v)) (fun _v _w ⟨c, h1, h2⟩ =>
+    mk_eq_mk c (by change (u : ZMod N) * _ = c * ((u : ZMod N) * _); rw [h1]; ring) h2)
+
+theorem torus_eqPt (u x : (ZMod N)ˣ) : torus u (eqPt x) = eqPt (u * x) := …（証明は省略）
+
+theorem chiPt_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
+    chiPt χ (torus u q) = χ u * chiPt χ q := …（証明は省略）
+
+theorem chiPt_red_congr {d₁ d₂ M : ℕ} (hd : d₁ = d₂) (χ₁ : DirichletCharacter ℂ d₁)
+    (χ₂ : DirichletCharacter ℂ d₂) (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) (h₁ : d₁ ∣ M) (h₂ : d₂ ∣ M)
+    (q : ProjLine M) : chiPt χ₁ (red h₁ q) = chiPt χ₂ (red h₂ q) := …（証明は省略）
+
+noncomputable def extChi (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
+  fun q => chiPt χ.primitiveCharacter (red χ.conductor_dvd_level q)
+
+theorem extChi_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : extChi χ (eqPt x) = χ x := …（証明は省略）
+
+theorem extChi_changeLevel {M : ℕ} [NeZero M] (h : N ∣ M) (χ : DirichletCharacter ℂ N)
+    (q : ProjLine M) : extChi (changeLevel h χ) q = extChi χ (red h q) := …（証明は省略）
+
+theorem extChi_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
+    extChi χ (torus u q) = χ u * extChi χ q := …（証明は省略）
+
+theorem pullP_extChi (a b : Lvl) (h : a ≤ b) (χ : DirichletCharacter ℂ a.val) :
+    pullP a b h (extChi χ) = extChi (changeLevel (n := a.val) (m := b.val) h χ) := …（証明は省略）
+
+theorem resE_extChi (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
+    resE a (extChi χ) = PAG.Part257.charU χ := …（証明は省略）
+
+theorem chiPt_not_compat :
+    chiPt (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) (zeroPt 2) ≠
+      chiPt (1 : DirichletCharacter ℂ 1) (red (one_dvd 2) (zeroPt 2)) := …（証明は省略）
+
+theorem ketS_proj_zero_eq (K c : ℕ) (hK : 1 ≤ K) (h : 0 + c ≤ K) (hc : 1 ≤ c)
+    (χ : DirichletCharacter ℂ (p ^ c)) :
+    PAG.Part29.ketS_proj K hK 0 c h χ = fun q =>
+      (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
+        chiPt χ (red (pow_dvd_pow p (by omega : c ≤ K)) q) := …（証明は省略）
+```
+
+## §6 盲検の問いテストの出力（全文）
+# 盲検の問いテストの出力（C2：U_∞ の P¹ への持ち上げ、2026-11-25）
+
+（照合者の最終報告の全文を写した。）
+
+## 結論
+
+Q1〜Q4 はすべて構成できました。ただし一意になるのは一箇所だけで、トーラスと両立する延長の族（Q3 の線形版）です。それは χ*(a)·χ̄*(b) という一つの式で与えられます。持ち上げ V（Q4）はユニタリ性・トーラス・W の条件を全部課しても一意になりません。どの答えも、CRT による素点ごとの分解、P¹(ℤ_p) の剰余円板の構造、U の形式的な性質（引き戻しとの可換、トーラスとの可換、ユニタリ、WUW = U⁻¹）しか使っていません。そのため算術的な内容はなく、関数体でも同じ答えになります。この問いそのものを扱った文献は見つかりませんでした。
+
+以下の記号：p ∤ N なら N_p = 1 とする。X_N = ∏_{p^e‖N} P¹(ℤ/p^e)。各素点 p で P¹(ℤ/p^e) は三つに分かれる：単数の円板（法 p で 0 でも ∞ でもない点）、0 の円板（p | a）、∞ の円板（p | b）。
+
+---
+
+### Q1. 延長の族
+
+**答え：できる。一意ではない。** 族全体は次の直積と1対1に対応します。
+
+∏_{f ≥ 1} ∏_{χ* は導手 f の原始指標} { Φ ∈ F_f : res Φ = χ* }
+
+各因子は次元 |X_f| − φ(f) = f∏_{p|f}(1+1/p) − φ(f) のアフィン空間です。
+
+**根拠：**
+- 法 N の指標 χ は、r^*（f → N）による χ* の引き戻しになっている。
+- そのため両立条件 E_N(χ) = r^* E_f(χ*) によって、族は導手のレベルでの値 Φ_{χ*} := E_f(χ*) で決まる。
+- 逆に、Φ を任意に選んで E_N(χ) := r^*Φ_{χ*} と置けば、res との関係も両立条件も満たされる。
+- f = 1 では Φ = 1 しか取れない。f = 3 では自由度は 2 になる。
+- 0 による延長は「導手のレベルで 0 延長してから引き戻したもの」と一致しない。N が f にない素数を含むと破れるので、問題文の記述と整合する。
+
+**数値：** L = 6, 8, 9, 12, 15, 30 の約数すべての上で連立方程式を解きました。どれも解があり、解空間の次元は 2, 20, 26, 26, 56, 56 で、上の式の予想とすべて一致しました（例：L = 15 では 2 + 3·2 + 3·16 = 56）。
+
+**確信度：** 高（証明 ＋ 数値）。
+
+### Q2. レトラクション
+
+**存在：ある。** 素点ごとに次の写像を作ります。
+- 単数の円板の上では [a:b] ↦ a/b。
+- 0 の円板と ∞ の円板は、単数の円板と法 p の段階ですでに分かれている。だから、そこには「法 p^e ごとに降りる」任意の写像（たとえば定数 1）を置けばよい。
+- これらを CRT で貼り合わせる。法 M から法 N への両立条件は p 成分ごとの条件に分解するので、素点ごとの構成で足りる。
+
+**W との両立：可能。** 0 の円板での値を h とし、∞ の円板では h∘W の逆数を取ればよい。
+
+**N によらない式：**
+- 整数係数の同次形式の比 P/Q として一つの式で与えることは**不可能**です。理由：Q がすべての p ですべての点の上で単数でなければならない。Q(x,1) が定数なら Q = c·y^d で、[1:0] で消える。定数でなければ、Schur の定理により無限個の p で根を持つ。
+- 指数が N に依存する多項式なら書けます：
+  ρ_N([a:b]) = 1 − (ab)^n + a^{n+1} b^{n−1}（n は λ(N) の倍数で、かつ N の素因数の最大の冪指数以上。たとえば n = N!）
+- この式は、単数の円板の上では a/b、それ以外では 1 になります。
+- 数値で次を確かめました（M = 12, 30, 36, 60 とその約数）：類の上で well-defined であること、レトラクションであること、還元と両立すること、ρ∘W = ρ⁻¹。
+
+**確信度：** 存在と W との両立は高。形式の比が不可能なことは高（Schur の定理による）。
+
+### Q3. トーラスとの両立
+
+**線形の族：選べる。しかも一意。** 式は次のとおりです。
+
+E_N(χ)([a:b]) = χ*(a mod f) · χ̄*(b mod f)
+
+**根拠（一意性）：**
+- 族は導手のレベル f の値で決まる（Q1）。
+- 等変な写像は、各軌道 O の上で「χ* が O の固定部分群の上で自明なら 1 つのスカラー、そうでなければ 0」という形しか取れない。
+- p | f で非自由な局所軌道（[p^k v : 1] や [1 : p^k w]、k ≥ 1）の固定部分群は 1 + p^{e−1}ℤ_p を含む。原始指標 χ* はその上で自明でない。
+- X_f の自由な軌道は E_f だけなので、Φ は E_f の外では 0 に決まる。これを引き戻したものが上の式になる。
+- この族は W とも自動的に両立する：E(χ)∘W = E(χ̄)。
+
+**数値：** L = 6, 8, 9, 12, 15, 30 で解空間の次元は 0。L = 12 では、解いた族が上の式と一致することを確認しました。
+
+**レトラクションの型（g∘ρ）：存在しない**（N | 2 の場合を除く）。点 [0:1] はトーラス全体で固定されるので ρ([0:1]) = uρ([0:1]) がすべての u で必要になり、単数群が自明でない限り矛盾します。したがって、等変な延長は「ρ による合成」の形をしていません。
+
+**確信度：** 高。
+
+### Q4. 持ち上げ V
+
+**存在：ある。** たとえば V = E·U·res + (1 − E·res)。
+- 引き戻しとの両立は、E と U がそれぞれ両立することから出る。
+- ただし一般にはユニタリではない。数値では N = 10, 15 で非ユニタリでした。N = 6, 12 でユニタリになるのは、そこに現れる実の 2 次指標で 𝔀 = 1 となるためです。
+
+**ユニタリにすると何が決まるか：**
+- res V = U res から、ブロック形は [[U, 0], [*, *]]。
+- ユニタリ性から左下のブロックは 0。したがって V = U ⊕ C で、C は F(X_N ∖ E_N) 上のユニタリ。
+
+**層別の持ち上げ（自然な選び方の候補）：**
+- 構成：S を「単数の円板にある素点の集合」とする層に X_N を分ける。各層は (ℤ/N_S)^× × Z（Z は残りの素点での 0 の円板または ∞ の円板の点）と書ける。そこで V = U_{N_S} ⊗ id と置く。
+- 数値で確認した性質（L = 12, 18, 20, 30）：ユニタリ、res V = U res、引き戻しと両立、トーラスと可換、WVW = V⁻¹。
+- この持ち上げは Φ_χ = χ*(a)χ̄*(b) を固有値 𝔀(χ*) の固有ベクトルに持つ。
+- 「V が層の指示関数と Z 座標の関数による掛け算と可換」（局所性）という条件を加えると一意になります。引き戻しの条件から、各 z で A_z = U が出るためです。
+
+**一意にならないこと：**
+- ユニタリ、トーラスとの可換、WVW = V⁻¹、引き戻しとの両立を全部課しても、一意ではありません。
+- 反例：v = 1_{p での 0 の円板} − 1_{p での ∞ の円板} として、R_p = 1 − 2P_v を層別の V に合成する。素数ごとに ±1 の自由度が生じる。
+- 数値：(L, p) = (30, 3), (36, 3), (20, 5) で、すべての条件を満たし、かつ層別の V と異なることを確認しました。
+- e ≥ 2 では、トーラス不変な関数がさらに増えるので、自由度はもっと大きくなります。
+
+**W と可換にはできない：**
+- E の上では W V W = U⁻¹ が強制される。
+- 𝔀(χ̄) = 𝔀(χ)^{-1} であり、𝔀 は一般に実数でない（N = 5, 7 で数値確認）。
+
+**SL₂ / PGL₂ との可換：**
+- E_N を保つ PGL₂(ℤ/N) の元は、トーラスと W（正規化群）に限ります。それ以外の元（たとえば冪単元）との可換は、E を保たないので条件として意味を持ちません。
+
+**2 変数フーリエでは作れない（手計算のみ）：**
+- 斉次座標の 2 変数フーリエ変換を Φ_χ に当てると、ガウス和の位相は τ(χ)τ(χ̄) = χ(−1)p のように打ち消し合う。
+- 𝔀 は 1 変数の側の量で、P¹ の上の「幾何的な」フーリエからは出てきません。
+
+**確信度：**
+- 存在と、ユニタリ性からブロック形が出ることは高。
+- 一意にならないことは高（反例を数値で確認）。
+- 局所性の条件で一意になることは中〜高（議論は概略で、数値では確かめていない）。
+- 2 変数フーリエの所見は中（手計算のみ）。
+
+### Q5. 文献
+
+この持ち上げの問題そのもの（Ẑ^× ⊂ P¹(Ẑ) からレベルと両立する延長、ルート数の作用素の持ち上げ）を扱った文献は**見つかりませんでした**。検索は 3 回だけで、MathSciNet と zbMATH は使っていないので、「見つからなかった」は「存在しない」の根拠にはなりません。
+
+部品はどれも標準的です：
+- P¹(ℤ/N) と Γ₀(N) の剰余類、その極限 P¹(Ẑ) は Manin–Marcolli の非可換モジュラー曲線とモジュラー記号の文脈に現れる（arXiv:math/0102006、arXiv:math/0111093）。
+- Connes–Marcolli の GL₂ 系（arXiv:math/0409520、arXiv:math/0507101）。
+- 指標つきのマニン記号（Stein のノート）。
+
+χ*(a)χ̄*(b) の型の関数は、指標つきのモジュラー記号やアイゼンシュタイン級数で使われる型だろうと推測しますが、この同定は未確認です。
+
+答え自体は CRT と剰余円板の初等的な議論で出るので、「既知の結果からの短い帰結」の水準と見ます。
+
+**確信度：** 文献の未発見については低〜中。「既知の道具だけで答えが出る」ことについては高。
+
+### Q6. 関数体 F_q[t]
+
+**答え：同じ形になる。**
+- 議論が使うのは、CRT、局所環上の P¹ の剰余円板への分解、U の形式的な性質だけである。
+- 形式の比が不可能なことは、関数体の Chebotarev の定理で同様に出る。
+- トーラス等変なレトラクションが存在しないことも同様。例外は (F_q[t]/P^e)^× が自明な場合で、q = 2、deg P = 1、e = 1 に限られる。
+- 𝔀 の正規化（i^a √f の部分）は、無限素点での符号と q^{deg f / 2} に置き換わる。しかし答えは 𝔀 の値に依存しない。
+
+§7 の対照群テストの意味で言えば、これらの答えに ℚ に固有の算術はありません。
+
+**確信度：** 中〜高。
+
+---
+
+数値のスクリプト（p1.py, test1.py, test2.py, test3.py）は /tmp/blind_p1lift/ にあります（`records/p1_lift/outputs/blind_scripts/` に写した）。
+
+**ツールの使用回数：** Bash 5 回、Write 4 回、WebSearch 3 回、合計 12 回。/home/claude/ の下のファイルは読んでいません。
+
+## §7 着手前の文書（全文）
+```markdown
+# 着手前の 4 点：候補 C2（U_∞ の P¹ への持ち上げ）（2026-11-25 夜）
+
+（2026-11-25 19:13 の著者の指示「お勧めで進めてください」を受けて、構築側が推薦案を 1 つに絞り、そのまま着手する。選択の委任は CLAUDE.md §4。何を選び、なぜかをここに記録する。）
+
+## §0 問いの出所と内部照合
+
+- 出所：基礎文書の索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）と、Part 263（PAG267）で外に残った候補 C2（`Uinf` を P¹ の上の関数の極限 `LimP` に持ち上げる作用素）。
+- 内部照合（言葉の検索）：Part 263 より前に、レベルの間の `ProjLine` の写像はない。P¹ の上の指標の関数としては、Part 19（PAG23）の殻ケット `kS`（2 チャートのモデル、法 p^K）と、Part 25（PAG29）の射影直線の版 `ketS_proj` がある。殻 0 のケット |0, χ⟩ は、下の §2 の関数 χ(a)·χ̄(b) の素数冪の場合と同じものの見込み（c ≥ 1。c = 0 では違う：殻 0 のケットは単数の点の指示関数、χ(a)·χ̄(b) は定数 1）。
+
+## §1 候補と選択
+
+- C2-a（推薦）：トーラスと両立する、引き戻しと両立する延長 E（赤道の関数 → P¹ の関数）を指標の言葉で書き、Part 19 の殻 0 のケットと結ぶ。持ち上げ V の非一意性は読みとして記録する。
+- C2-b：持ち上げ V そのもの（層別の持ち上げと、局所性の条件による一意性）を Lean にする。CRT による層の分解が重く、残余は計算だけなので、今は採らない。
+- C3：A1 と定理 2.6 を組み合わせた 1 つの Lean の文。局所計算の装置の側で、幾何の問いではないので今は採らない。
+- 選んだ理由：C2-a は、Part 263 の極限の塔（PAG267）と、Part 19〜25 の 2 チャートのモデル（PAG23〜PAG29）を初めて Lean で結ぶ。その結び目（殻 0 のケット = 一意な等変延長）が、索引 1.4・2.4 の材料になる。
+
+## §2 4 点（C2-a）
+
+1. 幾何の言葉の問い：赤道（両座標が単数の点）の上の関数を、すべての素点を測る段で P¹ 全体に延ばすとき、解像度の変更（還元による引き戻し）とトーラスの対称性を保つ延ばし方はあるか、一意か。貼り合わせ U は P¹ 全体の作用素に持ち上がるか。
+2. 既存の言葉への翻訳：P¹(Ẑ) の上の局所定数関数の空間への、開でない部分集合 Ẑ^× からの延長。等変延長は、トーラス軌道の固定部分群の上の指標の自明性で決まる（表現論の初等的な議論）。持ち上げ V は E·U·res + (1 − E·res) の形。
+3. 残余：計算の細部だけ（盲検の照合者は「既知の道具だけで答えが出る、既知の結果からの短い帰結の水準」）。したがって新規パートではなく短期層の小さいノートとして扱う。
+4. 対照群：盲検の照合者は、答えは F_q[t] でも同じ形（CRT・剰余円板・U の形式的な性質だけを使う）とした。ℚ に固有の算術は運ばない。
+
+## §3 盲検の問いテスト（`records/p1_lift/`）
+
+- 延長の族は存在し、一意でない（導手ごとの自由度のアフィン空間）。トーラスと両立する族は一意で、E(χ)[a:b] = χ*(a)·χ̄*(b)（χ* は原始指標）。W とは E(χ)∘W = E(χ̄)。
+- レトラクションの型の延長は存在し W と両立にできるが、N によらない同次形式の比では書けない。トーラスと両立するレトラクションはない（点 0 が固定されるため）。
+- 持ち上げ V は存在するが、ユニタリ・トーラス・W・引き戻しの条件を全部課しても一意でない（素数ごとの ±1 の自由度）。局所性の条件で一意（照合者の確信度：中〜高）。W とは可換にできない（W V W = V⁻¹ が強制される）。
+- 文献：この問いを扱ったものは見つからなかった（検索 3 回）。
+- 構築側の数値（`records/p1_lift/numeric/retraction_check.py`）：素数ごとの規則のレトラクション（単数の円板で a/b、0 の円板で 1 + x、∞ の円板で (1 + y)⁻¹）は、M ≤ 60 で赤道の上で恒等・還元と両立・W と両立。
+
+## §4 推薦と、Lean にする予定の文（短期層、Part 264（PAG268））
+
+1. 法 N の指標 χ について、χ(a)·χ̄(b) は P¹(ℤ/N) の上の関数として well-defined（`chiPt`）。赤道では χ(x)。トーラスの作用で χ(u) 倍。W で χ̄ の関数に移る。
+2. 原始指標の関数を引き戻した族 E_N(χ) = r^*(χ*(a)χ̄*(b)) は、赤道への制限が χ で、引き戻しと両立する。
+3. 法 N の式 χ(a)χ̄(b) をそのまま使うと、原始的でない χ では両立しない（証人）。
+4. 素数冪の法で、χ(a)χ̄(b)（c ≥ 1）の引き戻しは Part 25（PAG29）の殻 0 のケット `ketS_proj K 0 c` と一致する（Lean で結べなければ Lean の外に残す）。
+- Lean の外に残す見込み：トーラスと両立する族の一意性、持ち上げ V の存在と非一意性、局所性の条件による一意性、同次形式の比で書けないこと。
+- ラベルの見込み：1〜3 は［再導出（小さい）］、4 は［再導出（小さい）］。新規候補なし。兆候 4 は続く。
+```
+
+## §8 xlsx の行 3758〜3771（名前 | 主張 | 証明の要点 | 主な補題 | 状態）
+LABEL 列：PAG2.0-264（PAG268、短期層の小さいノート）P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致（推薦案 pag2_p1_lift_preregistration.md、著者の指示「お勧めで進めてください」2026-11-25 19:13。索引 2.4 の留保と Part 263 の候補 C2）：χ(a)·χ⁻¹(b) は P¹ の上で well-defined で、赤道では χ、W で χ⁻¹、トーラスで χ(u) 倍。原始指標の関数の引き戻し extChi は赤道で χ、引き戻しとトーラスと両立。法 N の式をそのまま使うと原始的でない χ では両立しない。素数冪の法で殻 0 の南ケット（Part 25（PAG29））は χ(a)χ̄(b) の引き戻しの |S_0|^(−1/2) 倍（1 ≤ c）。U_∞ の持ち上げの非一意性とトーラス等変な延長の一意性は Lean の外。ラベル（見込み、閉鎖で確定）は［再導出（小さい）］、新規候補なし
+
+```
+mul_inv_apply_unit | 単数 u で χ(u)·χ⁻¹(u) = 1 | χ·χ⁻¹ = 1 | MulChar.one_apply_coe | 検証完了（axioms 確認済み）
+chiPt_mk | chiPt χ [a:b] = χ(a)·χ⁻¹(b) | 定義 | Quotient.lift | 検証完了（axioms 確認済み）
+chiPt_eqPt | 赤道 [x:1] で chiPt χ = χ(x) | χ⁻¹(1) = 1 | map_one | 検証完了（axioms 確認済み）
+chiPt_Wproj | chiPt χ ∘ W = chiPt χ⁻¹ | 積の交換 | inv_inv | 検証完了（axioms 確認済み）
+torus_eqPt | トーラス u·[x:1] = [u x : 1] | rfl | Units.val_mul | 検証完了（axioms 確認済み）
+chiPt_torus | chiPt χ (u·q) = χ(u)·chiPt χ q | 乗法性 | map_mul | 検証完了（axioms 確認済み）
+chiPt_red_congr | 法が等しく整数での値が等しい指標は、還元の後で同じ chiPt | subst と MulChar.ext | ZMod.intCast_surjective | 検証完了（axioms 確認済み）
+extChi_eqPt | extChi χ の赤道での値は χ(x) | 還元は赤道を保つ、指標の引き戻し | PAG.Part258.pullL_charU, changeLevel_primitiveCharacter | 検証完了（axioms 確認済み）
+extChi_changeLevel | N ∣ M のとき extChi(changeLevel χ) = extChi χ ∘ 還元 | 導手と原始指標の不変性 | conductor_changeLevel, primitiveCharacter_changeLevel_apply | 検証完了（axioms 確認済み）
+extChi_torus | extChi χ (u·q) = χ(u)·extChi χ q | 還元とトーラスの可換 | chiPt_torus | 検証完了（axioms 確認済み）
+pullP_extChi | 段の言葉で：pullP (extChi χ) = extChi (changeLevel χ) | extChi_changeLevel | extChi_changeLevel | 検証完了（axioms 確認済み）
+resE_extChi | resE (extChi χ) = charU χ（Part 257（PAG261）） | extChi_eqPt | extChi_eqPt | 検証完了（axioms 確認済み）
+chiPt_not_compat | 法 2 の自明な指標（導手 1）で、法 2 の式は点 0 で 0、法 1 の式の引き戻しは 1（法 N の式は原始的でない χ で両立しない） | 値の計算 | MulChar.map_nonunit | 検証完了（axioms 確認済み）
+ketS_proj_zero_eq | p 素数、1 ≤ c ≤ K：殻 0 の南ケット ketS_proj K 0 c（Part 25（PAG29））= |S_0|^(−1/2)·（法 p^c の chiPt χ の引き戻し）（c = 0 では破れる：Lean の外、手計算） | 南北の成分の比較 | PAG.Part24.ket0_apply, PAG.Part24.chi_cast_inv, PAG.Part29.projFun_ketS | 検証完了（axioms 確認済み）
+```
+
+## §9 引き継ぎメモの Part 264 の項
+```markdown
+- **Part 264（PAG268、短期層の小さいノート、2026-11-25 夜）：P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致**：
+  - 出所：索引 2.4 の留保と、Part 263 で外に残った候補 C2。著者の指示「お勧めで進めてください」（2026-11-25 19:13）を受けて、構築側が関門（着手前の 4 点 `notes/pag2_p1_lift_preregistration.md`、盲検の問いテスト `records/p1_lift/`、対照群、内部照合）を通した推薦案 C2-a を選び、着手した（CLAUDE.md §4 の選択の委任）。
+  - 盲検の答え：引き戻しと両立する延長の族は多いが、トーラスとも両立する族は一意（χ*(a)χ̄*(b)）。U_∞ の持ち上げは存在するが、ユニタリ・トーラス・W の条件を全部課しても一意でない。答えは F_q[t] でも同じ形。残余は計算だけなので短期層。
+  - Lean：PAG268.lean、定理 14、sorry 0・警告 0。χ(a)χ̄(b) の well-defined 性と赤道・W・トーラス、原始指標の関数の引き戻し `extChi` の赤道での値・引き戻しとの両立・トーラス、法 N の式は原始的でない χ で両立しない（証人）、素数冪の法で殻 0 の南ケット（Part 25（PAG29））は χ(a)χ̄(b) の引き戻しの |S_0|^(−1/2) 倍（1 ≤ c）。ノート `notes/pag2_pag268_p1_char_extension.md`。辞書 §23。xlsx は final86（行 3758〜3771）。
+  - ラベル（見込み、閉鎖で確定）：［再導出（小さい）］、新規候補なし。兆候 4 は Part 249〜264 で 16 パート連続。
+  - 照合：独立照合（約 160 秒）。形式文は変えず、注意を書き足した（台帳 L16）。閉じるときの統合照合に、Part 263 の台帳 L15 と一緒に載せる。
+```
+
+## §10 辞書 §23
+```markdown
+ Part 264（PAG268、短期層）の名前（2026-11-25）
+
+| 名前 | 文献の言葉 | 根拠・確かめ方 |
+|---|---|---|
+| `chiPt` | 文献用語なし（P¹(ℤ/N) の上の関数 [a:b] ↦ χ(a)χ̄(b)。盲検の照合者は「指標つきのモジュラー記号やアイゼンシュタイン級数で使われる型だろう」と推測したが、未確認） | 盲検の問いテスト `records/p1_lift/outputs/blind_output.md` の Q5。 |
+| `torusU`・`torus` | 射影直線の上の対角トーラス（diag(u, 1)）の作用 | 定義の読み。 |
+| `extChi` | 文献用語なし（原始指標の `chiPt` を引き戻した族。盲検の照合者によれば、トーラスと両立する延長の族の一意な元） | 同上の Q3（照合者の手の証明と数値、Lean の外）。 |
+| `mul_inv_apply_unit`・`chiPt_red_congr` | 補助（行は定義名の慣行に合わせて足した） | ― |
+
+- 未記入の件数（この節）：0。「文献用語なし」の行は 2 つ（`chiPt`、`extChi`）。
+```
+
+## §11 構築側の数値スクリプトと出力
+```python
+"""C2 の着手前の数値：素数ごとの規則で作った ρ_N : P¹(ℤ/N) → (ℤ/N)^× が、赤道で恒等・還元と両立・W と両立（ρ∘W = ρ⁻¹）になるか（N ∣ M ≤ 60）。"""
+from math import gcd
+def fac(n):
+    f={};p=2
+    while p*p<=n:
+        while n%p==0: f[p]=f.get(p,0)+1; n//=p
+        p+=1
+    if n>1: f[n]=f.get(n,0)+1
+    return f
+def units(N): return [u for u in range(N) if gcd(u,N)==1] if N>1 else [0]
+def canon(a,b,N):
+    return min(((u*a)%N,(u*b)%N) for u in units(N)) if N>1 else (0,0)
+def P1(N):
+    return {canon(a,b,N) for a in range(max(N,1)) for b in range(max(N,1)) if N==1 or gcd(gcd(a,b),N)==1}
+def crt(res):  # res: list of (r, m)
+    x,M=0,1
+    for r,m in res:
+        t=((r-x)*pow(M,-1,m))%m; x+=M*t; M*=m
+    return x%M
+def rho_local(a,b,q):  # q = p^k, (a,b) unimodular mod p
+    p=min(fac(q)) 
+    if b%p:   # [x:1], x = a/b
+        x=(a*pow(b,-1,q))%q
+        return x if x%p else (1+x)%q
+    else:     # a unit, [1:y], y=b/a, p | y
+        y=(b*pow(a,-1,q))%q
+        return pow((1+y)%q,-1,q)
+def rho(a,b,N):
+    if N==1: return 0
+    return crt([(rho_local(a%(p**k),b%(p**k),p**k),p**k) for p,k in fac(N).items()])
+bad=0
+for M in range(1,61):
+    for (a,b) in P1(M):
+        r=rho(a,b,M)
+        assert M==1 or gcd(r,M)==1
+        # equator identity
+        if M>1 and gcd(a,M)==1 and gcd(b,M)==1:
+            assert r==(a*pow(b,-1,M))%M
+        # W
+        if M>1: assert (rho(b,a,M)*r)%M==1, (M,a,b)
+        for N in range(1,M+1):
+            if M%N: continue
+            if N>1 and rho(a%N,b%N,N)!=r%N: bad+=1
+print("compat failures:",bad)
+print("all checks passed")
+```
diff --git a/records/audit268/integrated/input_IIIb.md b/records/audit268/integrated/input_IIIb.md
new file mode 100644
index 0000000..b719c90
--- /dev/null
+++ b/records/audit268/integrated/input_IIIb.md
@@ -0,0 +1,740 @@
+# 統合照合 III-b の入力：台帳 L15（Part 263 の統合照合 I-a・I-b の後の直しと、閉鎖の記録）（2026-11-25）
+照合の対象：§3 の差分（コミット a529c13 と 5419967 のうち、L15 の範囲のファイル）。直しの根拠は §2 の I-a・I-b の出力と、2026-11-25 19:11 の著者の回答「1、2 とも良いです」（1：Part 262 の閉鎖の決定を保つ、2：Part 263 を閉じる）。記録の文は後注の形で足す方針。引き継ぎメモの差分の Part 264 の項は対象外（III-a の対象）。
+
+## §1 台帳 L15
+```markdown
+### L15：統合照合 I-a・I-b の後の直し（2026-11-25 夜）
+
+- 範囲：I-a（`records/audit267/outputs/integrated_Ia_output.md`）と I-b（`records/audit267/outputs/integrated_Ib_output.md`）の指摘を受けた直し。
+  - PAG267.lean の冒頭の説明（コメントだけ。作り直してエラー・警告 0）：機械的な照合の件数を今の版に、「5 は C2 の障害の一つ」を「各段の 0 延長による持ち上げだけを妨げ、`resL` の切断を使った持ち上げは妨げない（照合者の手計算、Lean の外）」に狭めた、`WL` と `Uinf` を結ぶ文がないこと、M = 0 の 2 つの補題の書き方。
+  - Part 263 のノート（§3・§6）、着手前の文書の後注（`Uinf` の文は型の上の事実）、引き継ぎメモの Part 263 の項（Part 番号の併記、0 延長の但し書き、I-a・I-b の記録、著者に確かめる事項 4）、xlsx（`records/audit267/update_xlsx_267b.py`：「Lean の外」の標示 2 つ、Part 番号の併記、LABEL の但し書き）、数値スクリプト（何も確かめていなかった行を、還元と反転の可換の検査に置き換えた。出力は変わらない）。
+  - L14 の範囲の直し（後注の形）：R4 の後注の「L11 で直した」を「2 は直した、1 は一部」に（台帳 3 か所、Part 262 のノート 2 か所、引き継ぎメモ 2 か所）、L11 の注にも後注、推薦案・索引のラベルの後注を名前で書いた、引き継ぎメモの閉鎖の行にラベルの書き分けの後注と 16:40 の条文の逐語（コミット c7f2796）と会話の特定、辞書 §20 の F_p の後注を数値の範囲に合わせた、インスタンスの数の範囲、「インスタンスなので」。
+  - 辞書 §22（Part 263 の名前の行）を新設。
+  - ノート §7（収束アラームの報告）を記入。
+  - この台帳：L13・L14 を閉じた項目に移し、L15 を新設。
+  - 閉鎖の記録（2026-11-25 19:11 の後）：PAG267.lean の冒頭のラベルの行（コメントだけ）、ノート §4・§6、引き継ぎメモ、xlsx の LABEL、この台帳の扱いの行。閉じた L13・L14 の記載に、I-a・I-b が挙げた範囲の漏れを書き足した。
+- 直していないもの：CLAUDE.md（日英）の文面（著者側の版の写し。16:40 の条文そのものと、2 つの規則の関係、Part 260・`InLayer` の文の断りは、著者に確かめる事項）。II-a の低 5・7・8・11・12、II-b の K と k の表記、grep の式の拡大（さらい直しはしていない）、新しい文の Part 番号の併記の一部、検証手順の行番号の表記。
+- 自己申告（根拠にしない）：主張を強めた文はない。辞書の F_p の後注と「5 は障害」の文は、どちらも範囲を狭めた直し。
+- 扱い（2026-11-25 19:11 の著者の判断）：Part 263 を閉じ、L15 は次のパートの統合照合に載せる。この行の後の文は判断の前の記載。I-a・I-b に中の指摘があった（高はない）。停止規則の「もう1回だけ統合照合」は I-a・I-b で行ったので、Part 263 を閉じて L15 を次のパートの統合照合に載せるか、もう 1 回照らすかを、著者に確かめる（引き継ぎメモの確かめる事項 4）。
+```
+
+## §2 根拠：統合照合 I-a・I-b の出力（全文）
+
+### I-a
+# 統合照合 I-a の出力（Part 263 の材料と台帳 L13、2026-11-25）
+
+（照合者の最終報告の全文を写した。）
+
+# 統合照合 I-a 報告：Part 263（PAG267）の散文と L13 の直し
+
+結論として、散文が形式文を偽にする箇所や、形式文の主張を取り違えている箇所は見つかりませんでした。直すべき点は中 4 件と低・極低の数件で、多くは記録と件数の側にあります。中の 4 件は次のとおりです。
+
+- 冒頭の説明の機械的な照合の件数が、独立照合の前の版のまま残っている。
+- 台帳 L13 の直しの範囲に、引き継ぎメモと着手前の文書の後注が書かれていない。
+- 「5 は C2 の障害の一つ」という文が広すぎる。
+- 後注の「予定の 5 つの文はすべて Lean に入った」が、Lean にない `Uinf` の文を含んでいる。
+
+Lean のコンパイルと `#print axioms` は再実行していません（環境の外）。
+
+## 1. 独立照合の指摘ごとの状態
+
+| 指摘 | 状態 | 根拠の引用 |
+|---|---|---|
+| 4.1 法 1 では 3 つの呼び名が区別を失う | 直った | 冒頭「法 1 では P¹ は 1 点で、それが 0 でも ∞ でも赤道でもある」、ノート §2 |
+| 4.2 「赤道の外」は「0 と ∞」と同じではない | 直った | 冒頭「『赤道の外』は『0 と ∞』ではない」、xlsx の `extE_off` 行 |
+| 4.3 `extE` の choose | 直す必要なし | — |
+| 4.4 極限の上の写像の well-defined 性 | 直す必要なし | — |
+| 4.5 `not_exists_extL` は `resL` の切断を否定しない | 直った | docstring「`resL` の ℂ 線形な切断の存在は否定しない」。冒頭・ノート・xlsx の行にもある（xlsx の LABEL 列と引き継ぎメモの「極限に降りない」には但し書きがない。6 の低を参照） |
+| 4.5 共終な部分系でも不存在は保たれる | 直った（見込みとして） | 「共終な部分系の段だけに弱めても…見込み」 |
+| 4.6 Ẑ^× との同一視は読み | 直す必要なし | ノート §3 は読みとして書いている |
+| 4.7 前半：`WL` と `resL` の関係の文がない | 直った | `resL_WL`「resL (WL z) = invL (resL z)」 |
+| 4.7 後半：`WL` と `Uinf` を結ぶ文がない | 直っていない（扱いの記録もない） | ノート §6 の「指摘と直し」の 5 項目に入っていない |
+| 4.8 Lim は ℂ 加群だけ | 直す必要なし | — |
+| 除去テスト：M ≠ 0 は不要に見える | 直った（見込みとして） | 冒頭の「Lean の外」の項「M ≠ 0 は証明の都合で、外しても成り立つ見込み」 |
+
+## 2. 形式文との食い違い、形式文より強い文
+
+**形式文と食い違う文はありませんでした。** 定理は 34 個で、名前を数えて一致しました（独立照合の時点は 30 個で、これも一致）。`#print axioms` の行は 11 行です。
+
+**足した 4 つの定理の逆翻訳と非空虚性の証人**（証人は /tmp で数値で確認し、真になりました）：
+
+- **`invG_comp_pullSys`**
+  - 逆翻訳：a が b を割るとき、法 a の単数の上の関数 g について、「g を単数の逆元で引き戻してから法 b に引き戻す」ことと「法 b に引き戻してから逆元で引き戻す」ことは同じ関数を与える。単数の還元が逆元を保つことの言い換え。
+  - 証人：a = 5、b = 10、x = 3。3 の逆元は法 10 で 7、7 mod 5 = 2。一方 3 の逆元は法 5 で 2。一致する。
+  - 2 ≤ N ∣ M &lt; 60 の全組で確認した。
+- **`invL_ofL`**
+  - 逆翻訳：逆元による引き戻しが極限 Lim に誘導する写像は、各段から来た元に対しては、その段での逆元の引き戻しとして働く。
+  - 証人：a = 5、g = δ₂（2 での指示関数）とすると、像は ofL(δ₃)。`ofL_injective` があるので、δ₂ の像と区別できる。
+- **`Wproj_eqPt`**
+  - 逆翻訳：任意の法 N（0 と 1 を含む）の単数 x について、点 [x:1] の座標を入れ替えた点は [x⁻¹:1] である。
+  - 証人：N = 7、x = 3。[1:3] は 5 倍すると [5:1] になり、3 の逆元は法 7 で 5。一致する。
+  - 2 ≤ N &lt; 60 の全単数で確認した。
+- **`resL_WL`**
+  - 逆翻訳：極限 LimP の任意の元について、座標の入れ替えで引き戻してから赤道に制限したものは、赤道に制限してから単数の逆元で引き戻したものに等しい。
+  - 証人：a = 5、f = [2:1] での指示関数。f∘W の赤道への制限は δ₃ で、δ₂ を逆元で引き戻したものも δ₃。δ₂ と δ₃ は違うので、空虚な一致ではない。
+
+**形式文より強い・広い文：**
+
+- 着手前の文書の後注「予定の 5 つの文はすべて Lean に入った」：予定の 4 は「`Uinf` はその像の側で働く」を含みますが、PAG267 に `Uinf` は出てきません（型の上で `Uinf : Lim → Lim` であることだけ）。
+- 冒頭の説明とノート §3 の「5 はその障害の一つ」（候補 C2 について）：PAG267 の 5 が否定するのは、各段の 0 延長と両立する写像だけです。`resL` の切断 s を使えば `s∘Uinf∘resL + (id − s∘resL)` は `resL` と可換な LimP の上の作用素になるので、持ち上げ一般の存在は妨げていません（手計算。Lean にしていない）。読みの項の中の文ですが、範囲を狭める必要があります。
+
+## 3. 「Lean の外」「見込み」「読み」の扱い、ラベル・出所・日付
+
+- xlsx の `zeroPt_ne_infPt` 行の「（N = 1 では等しい）」と、`extE_off` 行の「（合成数の法では赤道の外は 0・∞ だけではない）」は、どちらも Lean に文がないのに、主張の列に Lean の中の文のように置かれています。
+- 冒頭の「M = 0 では ℤ からの還元」：`isUnit_of_castHom` と `exists_eqPt_of_red` では、M = 0 にすると素因数の条件から N = 0 になり、ℤ → ℤ の恒等写像です（独立照合 3 節）。言い方が粗い（極低）。
+- B の記載：冒頭は B（直ちに出る）の行に「`mk_inv_eq` と同じ内容」と書いており、A（同じ文）とも読めます。ノート §5 の「書き換えが要る」と並べれば B として整合します。`mk_inv_eq` の文は入力にないので、照合できませんでした。
+- ノート §6 の「非空虚性の証人はすべての定理にある」：独立照合の時点の 30 定理についての文です。足した 4 定理には、独立照合の証人はありません。
+- ラベル（1〜3 は［既知］、4・5 は［再導出（小さい）］、新規候補なし）と、著者の採用（18:27）は、冒頭・ノート・xlsx・引き継ぎメモで一致しています。
+- 独立照合の「18:42〜、約 119 秒」は確かめられませんでした。
+
+## 4. 数値スクリプト（§9）
+
+- 組の数 198 と、両立しない組 120 は、再計算して一致しました。
+- 「両立 ⇔ M の素因数が N を割る」が True であることも再現しました。
+- 数えているのは件数ですが、上の段の赤道が赤道の逆像に含まれることを assert しているので、件数の一致は集合の一致と同じです。冒頭・ノートの数値の文は支えられています。
+- スクリプトの「W commute」の行は `... if False else True` で、何も確かめていない死んだコードです。散文はこの数値を主張していないので害はありません。別に計算したところ、W と還元の可換性は真でした。
+
+## 5. 番号・参照・件数の整合と台帳 L13
+
+- Part と PAG の対応（263/267、254/258、258/262、23/27、24/28）は正しいです。
+- 規則 (iv) の「Part n（PAGm）」の併記が欠けている箇所があります。
+  - xlsx：「Part 24 の mk_inv_eq」「Part 24 の Wpull」「（Part 254）」、LABEL 列の「Part 254 の Lim」
+  - 引き継ぎメモ：「PAG262 の `mem_ker_iff`」「PAG28 の `Wpull`」（Part の番号がない）
+- **冒頭の説明 56 行目「機械的な照合（独立照合の前の版、632 組）」**：ノート §5 によれば、632 は照合の回数で、組は 392 です。また、今の版の値（4391 件・55 件・440 組・712 回）に更新されていません。
+- ノート §5 の件数は、宣言 6 つ（定理 4 つと定義 2 つ）の追加分と整合しています（49 から 55、1 件あたり 8 組）。
+- 「検証手順の行 286」に対して、行の中身は「285 | …」で始まります。見出し行のずれと思われますが、確かめられませんでした（極低）。
+- 兆候 4 の「Part 249〜263 で 15 パート連続」は正しいです。
+- **L13 の範囲の漏れ：**
+  - 引き継ぎメモの Part 263 の項（4 定理、`resL_WL`、`mk_inv_eq` の B を含む）
+  - 着手前の文書の後注（`resL_WL` を足したことを述べている）
+  - 冒頭の説明の主な定理 4 の追記（36 行目）
+  - 足した定義・定理の docstring（「定理 4 つを足した」に含まれるとも読めますが、明記されていません）
+
+## 6. 直すべき点（重要度順）
+
+**中**
+1. 冒頭の説明の機械的な照合の文：「独立照合の後の版で全宣言 4391 件・対象 55 件・392→440 組・712 回で一致なし（前の版は 392 組・632 回）」に直す。
+2. L13 の範囲に、引き継ぎメモの項、着手前の文書の後注、冒頭の主な定理 4 の追記、新しい docstring を足す。
+3. 「5 はその障害の一つ」を「5 は、各段の 0 延長による持ち上げの障害であり、`resL` の切断を使った持ち上げは妨げない（手計算、Lean の外）」に狭める。冒頭の説明とノート §3 の両方。
+4. 後注を「予定の文はすべて Lean に入った。ただし 4 の『`Uinf` はその像の側で働く』は型の上の事実で、Lean の文ではない」に直す。
+
+**低**
+5. xlsx の `zeroPt_ne_infPt` 行と `extE_off` 行の括弧書きに「（Lean の外）」を付ける。
+6. ノート §6 の「すべての定理」を「独立照合の時点の 30 定理」とする。
+7. 指摘 4.7 の後半（`WL` と `Uinf`）の扱いを、ノート §6 に記録する（例：「C2 の範囲として扱わない」）。
+8. 「Part n（PAGm）」の併記を、xlsx と引き継ぎメモに入れる。
+9. xlsx の LABEL 列と引き継ぎメモの「0 延長は極限に降りない」に「（各段の 0 延長と一致する線形写像がない。切断の存在は否定しない）」を添える。
+
+**極低**
+10. 「M = 0 では ℤ からの還元」に「（素因数の条件のある 2 つでは N = 0 で恒等）」を添える。
+11. 数値スクリプトの死んだ assert を消すか、本物の検査に置き換える。
+12. 検証手順の行番号 285/286 の表記を揃える。
+
+---
+
+**使ったツールと読んだ範囲**：Read 4 回で `input_Ia.md` の全 1198 行を読みました。Bash 4 回で、入力の大きさの確認と、/tmp/indep_int267_Ia/ での数値の確認（chk.py と chk2.py）を行いました。ほかのファイルは読んでおらず、ウェブは使っていません。Lean は実行していません。
+
+### I-b
+# 統合照合 I-b の出力（台帳 L14、2026-11-25）
+
+（照合者の最終報告の全文を写した。行番号は入力 `records/audit267/integrated/input_Ib.md` の行。）
+
+# 統合照合 I-b の報告：台帳 L14（統合照合 II-a・II-b の後の直し）
+
+**結論**：高の指摘はありません。中が 4 件あります。(a) 一部しか直っていない直しを「直した」と書いた後注、(b) 数値の範囲を超えた辞書の後注、(c) 2 つのファイルで番号の振り方が合わない後注、(d) 16:40 の原文が今も残っていないこと、です。Lean の形式文そのもの（PAG266 の冒頭のコメント以外）は入力にないので、形式文との突き合わせはできませんでした。
+
+## 1. 根拠のある直しは直っているか
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-a 高 1「R4 は低・極低だけ」 | **一部** | II-a「17・18・224・264・318・333…行」 |
+
+- 後注は次の 7 か所に入りました。台帳の L11 の扱い（394 行）、閉じた L10 の 2 か所（403・412 行）、ノート §6 の R4 と閉鎖の行（327・328 行）、引き継ぎメモの R4 と閉鎖の行（260・261 行）。
+- 漏れが 1 か所あります。II-a が名指しした「L11 の注」（395 行「R4 の指摘は低か極低だけになった」）に後注がありません。
+- 後注の文「2 件はどちらも記録の側で、L11 で直した」は II-a と食い違います。II-a は R4 の 1 を「一部」と判定しています。L14 自身も、L9 の「含める→含めた」を「直していないもの」に入れています。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-a 中 2　ラベルの確定の書き分け | **一部** | II-a「398・411・419・430・443・456・505 行を…」 |
+
+- 後注は次の 5 か所に入りました。PAG266（238 行）、ノート §4（315 行）、索引（289 行）、推薦案（302 行）、引き継ぎメモのラベルの行（251 行）。
+- 引き継ぎメモの閉鎖の行（261 行「ラベルは確定（1 は［既知］、2〜5 は…）」。II-a の 419 行に当たる）には、書き分けの後注がありません。
+- 推薦案と索引では、番号が合いません（2 節で詳しく書きます）。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-a 中 3　CLAUDE.md §7 の 2 つの規則の関係 | **直っていない（理由あり）** | 「著者に確かめる事項」2 |
+
+- 著者に確かめる事項に回しました（278 行）。
+- 英語版 §7 も変えていませんが、L14 の「直していないもの」は「日本語版」とだけ書いています。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-a 中 4　台帳の漏れ | **直った** | II-a 4 節の 4 件 |
+
+- 閉じた項目の 382 行に、L11 の漏れ（R2・R3 の行、L10 の「扱い」、xlsx）と、L12 の漏れ（e6cb086・c3efc8d、§20 の欄、P¹(ℤ/p^K) の削除）が入りました。c7f2796・600b7c5 に台帳の項目がなかったことも書かれています。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-a 低 6　R3 の素描の置き場 | **直った（後注で）** | 「R3 の行（263 行）に戻します」 |
+
+- 文を戻すのではなく、後注で「R3 の時点のもの」と書く形を選びました（326 行）。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-a 低 9　17:29 の出所 | **直った** | 「出所…を書きます。…構築側の要約かも区別」 |
+
+- 262 行に入りました。ただし「この会話」がどの会話かは特定されていません。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-a 極低 10　鉤括弧 | **別の形で対処** | 「鉤括弧を外すか、条文と一字一致させます」 |
+
+- 「16:40 の著者のメッセージの逐語」とする後注を足しました（261 行）。逐語かどうかは、入力の中では確かめられません。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-a 低 5（記録より強い文） | **直っていない、記載もない** | 「記録より少し断定的な文 1 件（極低…）」 |
+
+- 「直していないもの」に入っていません。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-a 低 7・8・11・12 | **直していない（台帳に明記）** | ― |
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-b 中 1　L12 の漏れ | **直った** | 「L12 に e6cb086 と c3efc8d の直しを足すか」 |
+
+- 382 行に入りました。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-b 中 2　16:40 の止め方の原文を §7 に残す | **直っていない** | 「CLAUDE.md §7 の段落に、16:40 の止め方の原文を後注として残す」 |
+
+- 引き継ぎメモに残したのは「著者のメッセージ」の文で、II-b が言う §7 の条文（「形式文・記録より強めた文」）とは別の文です（2・4 節）。
+- L11 が「CLAUDE.md §7」を参照している点（394 行）も直っていません。
+- 「直していないもの」にも挙がっていません。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-b 中 3　Part 260・`InLayer` | **一部** | 「または「著者側の版の写し、構築側では Lean で未確認」と断る」 |
+
+- 引き継ぎメモの確かめる事項 3 で断っています。文のある CLAUDE.md の側には断りがありません。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-b 低 4　grep の式 | **一部** | 「`inductive`・`class` を足す…式に広げる」 |
+
+- 穴があることを後注で書きました。さらい直しはしておらず、そのことも書かれていません。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-b 低 5　インスタンスの数、「名前ではない」 | **直った** | 「4 つ（…）に直し、「名前ではないので」を「定義ではないので」」 |
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-b 低 6　§20 の設定と F_p の式 | **一部** | 「設定「P¹(ℤ/p^K)」を戻し、K と k の表記を揃える」 |
+
+- 設定は後注で補いました。K と k の表記の揺れはそのままです。
+- F_p の式の範囲の後注は、数値の範囲より強く書いています（2 節）。
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-b 低 7　`fC` の確信度 | **直った** | 「「確信度：中」（§3 と同じ）を添える」 |
+
+| 指摘 | 判定 | 根拠の引用 |
+|---|---|---|
+| II-b 極低 8（英語） | **直った** | 「Sign 4」→「Signal 4」、「a algebra」→「an algebra」 |
+
+- 機械的な差分で確かめました。225 行で変わったのはこの 2 か所だけです。新しい文の Part 番号の併記は直していません。
+
+## 2. 記録と食い違う文、記録より強い文
+
+- **辞書 §20 の後注（424 行）は数値より強く書いています。**
+  - 後注の文は「ℤ/p^k では指標が原始的な場合に限って成り立つ」です。
+  - /tmp/indep_int267_Ib/conv.py で計算し直しました。法 9 で 270 個中 8 個の不一致が出て、照合者の数値と一致しました。
+  - 不一致が出たのは、法 9・25 では「χ₁・χ₂ は原始的、χ₁χ₂ は原始的でない」場合だけでした。法 27 では、これに「3 つとも原始的でない」場合が 24 個加わります。
+  - χ₁ が原始的でなく χ₁χ₂ が原始的な組では、不一致は 0 でした。
+  - したがって「限って」（原始的でなければ成り立たない、という読み）は、数値と食い違います。「原始的なら成り立つ」のほうも、4 つの法での数値にすぎません。
+- **R4 の後注の「L11 で直した」は II-a の判定と食い違います**（1 節）。
+- **推薦案（302 行）と索引（289 行）の後注は番号が合いません。**
+  - 後注は「1・4・5 は 16:40、2・3 は 17:29」と、Part 262 のノート §4 の番号で書いています。
+  - 推薦案の番号は別の振り方です。298・299 行では「2. 2 乗を外した形」「3. 作用素の形」です。推薦案の番号で読むと、作用素の形（16:40 に確定）が 17:29 に確定したことになってしまいます。
+  - 索引の行は番号を持たず、「ガウス和の形」「ほかの 4 つ」と名前で書いています。番号の後注を、どの項に当てればよいか分かりません。
+- **「16:40 の原文」の取り違えのおそれがあります（261 行）。** II-a・II-b によれば、16:40 に CLAUDE.md §7 に入った条文は「形式文・記録より強めた文」でした。後注の「16:40 の原文はこの後注に残す」は、条文とは字句の違うメッセージの文を指しています。条文そのものは、差分のどこにも残っていません。
+- **閉じた項目の 381 行「形式文より強い文の指摘はなかった」** について。II-b は「形式文との突き合わせはどの項目でもできませんでした」と書いています。突き合わせができなかったことを書かないと、照らした結果のように読めます。
+
+## 3. 直しが足した新しい主張
+
+- **16:40 のメッセージが逐語である、という主張（261 行）。** 出所のファイルや会話の参照がなく、入力の中では確かめられません。
+- **17:29 の出所が「著者のこの会話のメッセージ」であり、理由の文は構築側の要約である、という主張（262 行）。** 入力の中では確かめられません。
+- **F_p の式の範囲（424 行）。** 支えは照合者の数値だけで、文は数値より強く書かれています（2 節）。
+- **インスタンスが「4 つ」（431 行）。** II-b の言い方は「少なくとも 4 つ」でした。grep の結果は入力にありません。
+- **`fC` の「確信度：中」。** CLAUDE.md §3 の「hyper-duality に対応（確信度：中）」と合います。これは入力の外の資料で、II-b が参照しています。
+- **数学の主張を強める直し**：PAG266 の差分はコメントだけで、形式文は変わっていません。
+
+## 4. 地位・決定者・日付・判断の記録・台帳の範囲
+
+- **判断の記録**：元の文は残し、後注を足す形になっていて、書き換えは見当たりません。17:29 の項にも、見出しの後に後注を足しています。
+- **L14 の「どれも後注の形で足し、記録の文は書き換えていない」（369 行）は強すぎます。**
+  - 辞書の「名前ではないので」→「定義ではないので」は、標示のない書き換えです（431 行）。
+  - `fC` の確信度（440 行）と CLAUDE.en.md の 2 か所も、その場で書き換えています。
+  - 辞書と英語版は記録ではないと読むこともできますが、それなら全体を指す言い方を避けるべきです。
+- **台帳の範囲**
+  - 閉じた項目の新しい記載（381・382 行。II-a・II-b の台帳の漏れに対する直しそのもの）は、L14 の範囲にありません。L13 の「閉じた項目への移動」に入ると読むことはできますが、中身は移動ではなく新しい記載です。
+  - 「直していないもの」に、次が挙がっていません。II-a 低 5、II-b 中 2、英語版の §7、K と k の表記、grep の式の拡大、新しい文の Part 番号の併記。
+- **L14 の扱い（376 行）の理由づけ。**
+  - 停止規則が「もう1回だけ統合照合」と言うのは、主張を変える直しがあった場合です（269 行）。高・中の指摘があったことは、それとは別に、閉じる条件（低・極低だけ）を満たさない理由になります。
+  - 今の書き方では、I-b の後は結果によらず閉じられるように読めます。
+
+## 5. Part と PAG の対応、参照、件数
+
+- **Part と PAG の対応**：照らしたものは 4 のずれで一致しました。Part 263（PAG267）、Part 252（PAG256）、Part 20（PAG24）、Part 21（PAG25）、Part 25（PAG29）、Part 24（PAG28）、Parts 257〜261（PAG261〜265）です。
+- **番号の振り方**：後注の「1〜5」は推薦案・索引の番号と合いません（2 節）。
+- **パス**：370 行の `integrated_IIb_output.md` だけに `records/audit267/outputs/` が付いていません（極低）。どのパスも、実在は確かめていません。
+- **件数**：§4 の R4 の 6 節の抜粋で、1・2 が「（低〜中）」であることを確かめました。II-a の高 1 は入力の中で支えられています。II-a の高 1・中 3、II-b の中 3 という数え方は、両方の出力と一致します。
+- **「上の鉤括弧の中」（261 行）**：前の後注にも鉤括弧（「低〜中」「低か極低だけ」）があるので、どの鉤括弧を指すのか曖昧です（低）。
+
+## 6. 直すべき点（重要度順）
+
+**中**
+
+1. **R4 の後注 7 か所の「2 件はどちらも…L11 で直した」を直す。**
+   - 案：「1（L10 の範囲と自己申告）は L11 で一部を直した（閉じた L9 の範囲の「含める→含めた」は直していない。II-a）。2（ノート §2 の K）は L11 で直した」。
+2. **辞書 §20 の後注を数値の範囲に合わせる。**
+   - 案：「ℤ/p^k では、照合者の数値（法 9・25・27・49）で χ₁・χ₂・χ₁χ₂ がすべて原始的なら不一致 0。制限しないと法 9 で 270 個中 8 個の不一致があり、不一致は χ₁χ₂ が原始的でない組に出た（一般の証明・文献は確かめていない）」。
+3. **推薦案と索引の後注を、名前か参照つきの番号で書く。**
+   - 案（推薦案と索引）：「ガウス和の形・作用素の形の 2 つ（2 チャート・射影直線）は 16:40 の閉鎖で確定、符号つきの形・2 乗の形は 17:29 に著者が［再導出（小さい）］で確定（番号は Part 262 のノート §4 の 1〜5）」。
+4. **II-b 中 2 への対処を、直したか直していないかに分けて書く。**
+   - 引き継ぎメモ 261 行の「16:40 の原文はこの後注に残す」を、「16:40 の著者のメッセージの文（CLAUDE.md §7 に 16:40 に入った条文「形式文・記録より強めた文…」とは字句が違う）」に直す。
+   - 条文そのものを残していないことと、L11・ノートの「CLAUDE.md §7」の参照先が今の条文にないことを、「直していないもの」か、確かめる事項に足す。
+
+**低**
+
+5. L11 の注（395 行）に、R4 の後注を足す。
+6. 引き継ぎメモの閉鎖の行（261 行）の「ラベルは確定（…）」にも、書き分けの後注を足す。
+7. L14 の「どれも後注の形」を「記録の文は後注の形。辞書（`fC`、「定義ではない」）と英語版はその場で直した」にする。
+8. L14 の「直していないもの」に足す：II-a 低 5、英語版 §7、K と k の表記、grep の式の拡大（さらい直しはしていない）、Part 番号の併記。
+9. L14 の範囲に「閉じた項目の L11・L12 の記載と、台帳の漏れの記録（381・382 行）」を足す。
+10. 381 行に「II-b は形式文が入力になく、突き合わせはできなかった」を添える。
+11. L14 の扱いの理由を「高・中の指摘があり、閉じる条件（低・極低だけ）を満たさないため、統合照合 I に載せる」にする。そのうえで、主張を変えた直し（辞書の F_p の範囲、`fC`）があるかどうかを書く。
+12. CLAUDE.md の Part 260・`InLayer` の文のそばにも断りを置くか、置かない理由を書く。
+13. 262 行の「この会話」を、会話の日時や場所で特定する。261 行の「上の鉤括弧」は「閉鎖の行の最初の鉤括弧」にする。
+
+**極低**
+
+14. インスタンスの「4 つ」に「grep の式で拾った範囲で」を添える。
+15. 「定義ではないので」は、Lean では `instance` も定義の一種なので、「インスタンスなので」のほうが正確です。
+16. 370 行のパスに `records/audit267/outputs/` を付ける。
+
+**確かめられなかったこと**
+- 著者の 16:40・17:29 のメッセージの原文
+- PAG266 を作り直したときの「エラー・警告 0」
+- grep の実際の出力
+- 各ファイルの実在
+- 差分の外にほかの直しがあるかどうか
+- 引き継ぎメモの 420 行（II-a 時点の「著者の確認待ち」）の今の状態
+
+**使ったツールと読んだ範囲**
+- 計 6 回：Bash 3 回（行数の確認と作業ディレクトリの作成、英語版の差分の機械比較、ℤ/9・25・27 での畳み込みの式の数値確認）、Read 3 回。ウェブは使っていません。
+- 読んだ範囲：`input_Ib.md` の 1〜464 行（全文。1–120、120–249、250–464 に分けて読みました）。ほかのファイルは読んでいません。計算は `/tmp/indep_int267_Ib/` で行いました。
+
+## §3 差分
+```diff
+diff --git a/PAG267.lean b/PAG267.lean
+index a1da4e5..ddf96b0 100644
+--- a/PAG267.lean
++++ b/PAG267.lean
+@@ -30,14 +30,15 @@
+ Lean の外：
+ - 極限 `LimP` が P¹(Ẑ) = ∏_p P¹(ℤ_p) の上の局所定数関数の空間と同一視できること、Ẑ^× が P¹(Ẑ) の中で閉だが開でないこと（盲検の照合者の記述）。
+ - 読み：すべての素点を測る段では赤道が開集合でないので、局所定数関数の上の作用素として `Uinf` を赤道に閉じ込めることはできない。
+-  `Uinf` が作用するのは `resL` の行き先 `Lim` の側で、`LimP` の上に `Uinf` を持ち上げる作用素（候補 C2）はこの文書の外で、5 はその障害の一つ。
++  `Uinf` が作用するのは `resL` の行き先 `Lim` の側。`LimP` の上に `Uinf` を持ち上げる作用素（候補 C2）はこの文書の外。5 が妨げるのは各段の 0 延長による持ち上げだけで、
++  `resL` の切断を使った持ち上げ（resL と可換な作用素）は妨げない（統合照合 I-a の照合者の手計算、Lean の外）。`WL` と `Uinf` を結ぶ文はこの文書にない。
+ - `red_surjective`・`exists_redU`・`isUnit_of_castHom`・`exists_eqPt_of_red` の M ≠ 0 は証明の都合で、外しても成り立つ見込み
+-  （M = 0 では ℤ からの還元。独立照合の手計算。Lean にしていない）。
++  （M = 0 では ℤ からの還元。素因数の条件のある 2 つでは M = 0 なら N = 0 で恒等。独立照合の手計算。Lean にしていない）。
+ - 0 延長との両立を整除の順序の共終な部分系の段だけに弱めても、5 の不存在は保たれる見込み（共終な部分系は素数を足す段を含む。独立照合の手計算。Lean にしていない）。
+ - 5 の判定は数値でも確かめた（`records/p1_tower/numeric`：M ≤ 48 の 198 組すべてで、赤道の逆像が上の段の赤道と一致するのは M の素因数が N を割るときに限る）。
+ 
+ 内部照合：Part 258（PAG262）の `mem_ker_iff`（還元の核）と Part 24（PAG28）の `Wpull`・`Wpull_Wpull` を使い、作り直していない。
+-機械的な照合（独立照合の前の版、632 組）で「同じ文」「定義的に同じ」は見つからなかった（網羅ではない）。
++機械的な照合（独立照合の後の版で、全宣言 4391 件、対象 55 件、候補の組 440、照合 712 回。独立照合の前の版は 392 組・632 回）で「同じ文」「定義的に同じ」は見つからなかった（網羅ではない）。
+ 直ちに出るもの（B）：`Wproj_eqPt` は Part 24（PAG28）の `mk_inv_eq`（ZMod の逆元で書いた [y⁻¹:1] = [1:y]）と同じ内容。
+ 近いもの（C）：Part 23（PAG27）の `toProj`（素数冪の法で x ↦ [x:1]）、Part 24（PAG28）の `projFunEquiv` の [x:1] での値。
+ 
+diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
+index 53547d7..26de234 100644
+--- a/handoff/PAG2_handoff_part259.md
++++ b/handoff/PAG2_handoff_part259.md
+@@ -1719,9 +1719,9 @@
+   - 件数：鎖全体の定理・補題は 3,695 件（3,690 + 5）。xlsx は final84（行 2〜3723）。
+   - 再照合 R2（2026-11-20 15:15〜15:31、`records/audit266/recheck_int/`）：L7・L8 を照らした。形式文より強い文はなし。地位の格上げ（ラベルの「確定」）、留保の範囲の限定の脱落、19:58 の判断の記録の書き換えなどを直した（台帳 L9）。
+   - 照合 R3（2026-11-20 15:37〜15:45、`records/audit266/recheck_L9/`）：L9 を照らした。形式文より強い文はなし。PAG265 の判断の記録の言葉、概要の標示の文、留保の範囲の限定の漏れ、ラベルの理由の文などを直した（台帳 L10）。
+-  - 照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/`）：L10 を照らした。指摘は低か極低だけで、形式文・記録より強い文と判断の記録の書き換えはなかった。直した（台帳 L11）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
+-  - 閉鎖（2026-11-20 16:40）：著者が止め方の規則を決めた（「低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい」、CLAUDE.md §7 に追記）。R4 はこれに当たるので Part 262 は閉じた。台帳 L11 は次のパートの統合照合に載せる。ラベルは確定（1 は［既知］、2〜5 は［再導出（小さい）］、新規候補なし）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）（後注 2026-11-25：上の鉤括弧の中は、2026-11-20 16:40 の著者のメッセージの逐語：「低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい」。CLAUDE.md §7 の条文は、その後に著者側の版の箇条に置き換わり、17:46 に一文が確定した。16:40 の原文はこの後注に残す。）
+-  - 著者の確定（2026-11-20 17:29）：（後注 2026-11-25、統合照合 II-a の指摘：出所は著者のこの会話のメッセージ（2026-11-20 17:29）。下の 2・3 のラベルの理由の文は、構築側の要約。）
++  - 照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/`）：L10 を照らした。指摘は低か極低だけで、形式文・記録より強い文と判断の記録の書き換えはなかった。直した（台帳 L11）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側。2（ノート §2 の K）は L11 で直した。1（L10 の範囲と自己申告）は L11 で一部を直した（閉じた L9 の範囲の「含める→含めた」は直していない。II-a の判定、統合照合 I-b の指摘でこの括弧を直した）。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
++  - 閉鎖（2026-11-20 16:40）：著者が止め方の規則を決めた（「低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい」、CLAUDE.md §7 に追記）。R4 はこれに当たるので Part 262 は閉じた。台帳 L11 は次のパートの統合照合に載せる。ラベルは確定（1 は［既知］、2〜5 は［再導出（小さい）］、新規候補なし）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側。2（ノート §2 の K）は L11 で直した。1（L10 の範囲と自己申告）は L11 で一部を直した（閉じた L9 の範囲の「含める→含めた」は直していない。II-a の判定、統合照合 I-b の指摘でこの括弧を直した）。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）（後注 2026-11-25：この行の最初の鉤括弧の中は、2026-11-20 16:40 の著者のメッセージ（この構築側のセッションの会話）の逐語：「低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい」。この文は、16:40 に構築側が CLAUDE.md §7 に入れた条文とは字句が違う。条文は「直しの照合が低・極低の指摘だけを返し、形式文・記録より強めた文と著者の判断の記録の書き換えがなければ、その照合の後の直しは次のパートの統合照合に載せ、そのパートは閉じてよい」（コミット c7f2796）。条文はその後に著者側の版の箇条に置き換わり、17:46 に一文が確定した。メッセージの文と 16:40 の条文はこの後注に残す（統合照合 I-b の指摘で直した）。）（後注 2026-11-25、統合照合 II-a の指摘：1・4・5 は 16:40 の閉鎖で確定、2・3 は 2026-11-20 17:29 に著者が［再導出（小さい）］で確定。）
++  - 著者の確定（2026-11-20 17:29）：（後注 2026-11-25、統合照合 II-a の指摘：出所は著者のメッセージ（2026-11-20 17:29、この構築側のセッションの会話）。下の 2・3 のラベルの理由の文は、構築側の要約。）
+     - 19:58 の判断の記録：元の文を残し、根拠の内訳を後注で足す形で確定（判断の記録は書き換えない原則。確認なしに書き換えて戻した経緯も含めて確定）。
+     - 2・3 のラベル：構築側の［再導出（小さい）］で確定。照合者の案「［既知］の直接の帰結」は採らない（符号つきの形はその形では文献に見つかっておらず、「既知の直接の帰結」は文献の範囲を広く見せる。LPP の式 (10) の誤帰属と同じ型の言い過ぎになる）。
+     - CLAUDE.md §2 は著者側で更新した：Part 262 の追加（鎖全体 3,695 件、xlsx final84、索引 2.4 の留保が埋まっていないこと）、「非単位的な写像」→「単位元を保たない写像」、「Part 216 の InLayer と同じ概念」→「InLayer が定義する関係そのもの」、Part 260 の一意性を 3 条件の形に。§7 にも止め方の規則を条文化した（著者側）。リポジトリの CLAUDE.md §2 にはまだ届いていない（2026-11-20 17:29 の時点）。
+@@ -1737,11 +1737,12 @@
+   - 著者の確定（2026-11-20 17:46）：停止規則の「主張を変える直しがあれば、もう1回だけ統合照合を行い、その後はこの規則で閉じる」の一文を、この文で確定。CLAUDE.md（日英）の箇条に確定の時刻を書いた。
+ - **Part 263（PAG267、短期層の小さいノート、2026-11-25）：P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限、赤道への制限と赤道からの 0 延長**：
+   - 出所：基礎文書の索引の「射影」の空間の水準の問い（索引 1.4・2.4）。推薦案 `notes/pag2_p1_tower_preregistration.md` §4（盲検の指摘で改めた C1）を、2026-11-25 18:27 に著者が採用した（「進めてください」）。
+-  - Lean：PAG267.lean、定理 34、sorry 0・警告 0、#print axioms は標準の 3 つ。還元の恒等・合成の法則・反転との可換・全射（M ≠ 0）、0 ≠ ∞（N ≠ 1）、引き戻しの帰納系と極限の上の対合 W_∞、赤道への制限が誘導する `resL : LimP → Lim`（Part 254 の Lim）の全射と resL ∘ W_∞ = invL ∘ resL、0 延長が引き戻しと可換 ⇔ 上の段の法の素因数がすべて下の段の法を割る（証人 (1, 2)）、0 延長は極限に降りない。ノート `notes/pag2_pag267_p1_tower.md`。
++  - Lean：PAG267.lean、定理 34、sorry 0・警告 0、#print axioms は標準の 3 つ。還元の恒等・合成の法則・反転との可換・全射（M ≠ 0）、0 ≠ ∞（N ≠ 1）、引き戻しの帰納系と極限の上の対合 W_∞、赤道への制限が誘導する `resL : LimP → Lim`（Part 254 の Lim）の全射と resL ∘ W_∞ = invL ∘ resL、0 延長が引き戻しと可換 ⇔ 上の段の法の素因数がすべて下の段の法を割る（証人 (1, 2)）、0 延長は極限に降りない（各段の 0 延長と一致する線形写像がない。`resL` の切断の存在は否定しない）。ノート `notes/pag2_pag267_p1_tower.md`。辞書 §22。xlsx は final85（行 3724〜3757 を足した）。
+   - ラベル（見込み、閉鎖で確定）：1〜3 は［既知］、4・5 は［再導出（小さい）］、新規候補なし。兆候 4 は続く（Part 249〜263 で 15 パート連続）。
+-  - 内部照合：PAG262 の `mem_ker_iff` と PAG28 の `Wpull` を使った（言葉の検索）。機械的な照合 712 回で一致なし。`Wproj_eqPt` は PAG28 の `mk_inv_eq` と同じ内容（B）。
+-  - 照合：独立照合（約 119 秒）。指摘で 4 定理を足した（台帳 L13）。同時に、台帳 L11・L12 と台帳に項目のなかった記録の追記を統合照合 II-a・II-b で照らした（L11・L12 は閉じた）。II-a に「高」1 件：R4 の指摘は「低〜中」2 件を含んでいたのに、記録は「低か極低だけ」と書いていた。直しは後注の形で入れた（台帳 L14）。L13・L14 は閉じるときの統合照合 I に載せる。
++  - 内部照合：Part 258（PAG262）の `mem_ker_iff` と Part 24（PAG28）の `Wpull` を使った（言葉の検索）。機械的な照合 712 回で一致なし。`Wproj_eqPt` は Part 24（PAG28）の `mk_inv_eq` と同じ内容（B）。
++  - 照合：独立照合（約 119 秒）。指摘で 4 定理を足した（台帳 L13）。同時に、台帳 L11・L12 と台帳に項目のなかった記録の追記を統合照合 II-a・II-b で照らした（L11・L12 は閉じた）。II-a に「高」1 件：R4 の指摘は「低〜中」2 件を含んでいたのに、記録は「低か極低だけ」と書いていた。直しは後注の形で入れた（台帳 L14）。L13・L14 は閉じるときの統合照合 I（I-a・I-b）で照らした。I-a・I-b とも高はなく、中がそれぞれ 4 件（記録と件数の側）。直しは台帳 L15。閉じるかどうかは著者に確かめる（下の 4）。
+   - 著者に確かめる事項（2026-11-25）：
+     1. 2026-11-20 16:40 の Part 262 の閉鎖の決定は、構築側の「R4 は低・極低だけ」という報告を前提にしていた可能性がある。実際の R4 の出力では、6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K。どちらも記録の側で、L11 で直した）が「低〜中」だった。この 2 件を知ったうえで閉鎖の決定を保つかどうか。
+     2. CLAUDE.md §7 の「照合の後に直した文面は、そのパートを閉じる前に再照合する（2026-11-13）」と、止め方の規則（2026-11-20）の関係（止め方の規則が前者の例外であると明記するか）。リポジトリの CLAUDE.md は著者側の版の写しなので、構築側では文面を変えていない。
+     3. CLAUDE.md §2 の Part 260 の「3 条件すべてが効く」と「`InLayer` が定義する関係そのもの」の文は著者側の版の写しで、構築側はこの写しのために Lean で確かめていない（II-b の指摘）。
++    4. Part 263 を閉じてよいか。独立照合の後に定理 4 つを足した（主張を足した直し）ので、停止規則の「もう1回だけ統合照合」として I-a・I-b を行った。I-a・I-b とも高はなく、形式文と食い違う散文もなかったが、中がそれぞれ 4 件あった（記録・件数・範囲の書き方）。その直しは台帳 L15 で、主張を強めた直しはない（範囲を狭めた直しが 2 つ）。止め方の規則の「その後はこの規則で閉じる」を、中の指摘が残っていても閉じてよいと読むか、もう 1 回照らすかは、構築側では決めずに著者に確かめる。構築側の推薦は、閉じて L15 を次のパートの統合照合に載せること（理由：形式文の側の指摘がなく、直しは範囲を狭める側だけで、照らすたびに記録の側のずれが生まれる型が L7 以来続いているため）。
+diff --git a/notes/pag2_founding_material_index.md b/notes/pag2_founding_material_index.md
+index 769c9a2..b65808d 100644
+--- a/notes/pag2_founding_material_index.md
++++ b/notes/pag2_founding_material_index.md
+@@ -121,7 +121,7 @@
+   - `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。
+   - 照合した範囲（PAG23・PAG26・PAG27・PAG256）では、`JH` と P¹ のモデルを結ぶ Lean の文はない。この留保は Part 262 の後も残る。
+   - 𝔀 の値と P¹ のモデルを結ぶ Lean の文（Part 262（PAG266）、2026-11-20、短期層）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、P¹(ℤ/p^K) の赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデル `PAG.Part266.equator_intertwine_rootNum`、射影直線 `PAG.Part266.equator_intertwine_proj_rootNum`）。係数の等式 conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は両方とも奇のときだけ −1）は `PAG.Part266.conj_Jhat_eq_rootNum`、2 乗の形は `PAG.Part266.conj_Jhat_sq_eq_rootNum`、ガウス和の形は `PAG.Part266.conj_Jhat_eq_gauss`。
+-    - 範囲：殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ（係数は K によらない）。p = 2（すべての n）と p = 3、n = 0 では文は空。作用素の形の 2 つは Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換えで、絡み合いの中身はそちらにある。射影直線の版は 2 チャートの版を `projFunEquiv`（Part 24（PAG28））で移したもので、2 チャートの版と同値（手の論証。Lean の文ではない）。ラベル（2026-11-20 16:40 の閉鎖で確定）は、ガウス和の形が［既知］、ほかの 4 つが［再導出（小さい）］（符号つきの形を書いた文献は見つかっていない）。（後注 2026-11-25、統合照合 II-a の指摘：1・4・5 は 16:40 の閉鎖で確定、2・3 は 2026-11-20 17:29 に著者が［再導出（小さい）］で確定。）
++    - 範囲：殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ（係数は K によらない）。p = 2（すべての n）と p = 3、n = 0 では文は空。作用素の形の 2 つは Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換えで、絡み合いの中身はそちらにある。射影直線の版は 2 チャートの版を `projFunEquiv`（Part 24（PAG28））で移したもので、2 チャートの版と同値（手の論証。Lean の文ではない）。ラベル（2026-11-20 16:40 の閉鎖で確定）は、ガウス和の形が［既知］、ほかの 4 つが［再導出（小さい）］（符号つきの形を書いた文献は見つかっていない）。（後注 2026-11-25、統合照合 II-a・I-b の指摘：Part 262 の定理のうち、ガウス和の形と作用素の形の 2 つ（2 チャートのモデルと射影直線の版）は 16:40 の閉鎖で確定、符号つきの形と 2 乗の形は 2026-11-20 17:29 に著者が［再導出（小さい）］で確定。番号で書くと Part 262 のノート §4 の 1・4・5 と 2・3。）
+     - このパートの文に `JH` は現れない。Lean で結んだのは 𝔀 の値と P¹ の赤道の係数で、上の二つの留保（`JH` は P¹ の上の作用素ではない、照合した範囲では `JH` と P¹ のモデルを結ぶ文はない）は残る。
+     - 読み（Lean の外）：原始指標 χ の成分に導手で計算した 𝔀 を掛ける作用素を U とすると、B_S(|0,χ₁⟩, |0,χ₂⟩) が χ₁χ₂ の成分に入ること（Part 262 の文にはない）と合わせて、赤道のケット（殻 0）の組で χ₁・χ₂・χ₁χ₂ が原始的なとき、北の畳み込みは南の畳み込みを U² で移したもの。この条件は U を有限個の候補（少なくとも単数 u と指標ごとの符号の分がある）に絞るが選ばず、A1 は導かれない。関数体では本来のルート数が一般にこの条件を満たさない（ℚ に固有の小さな観察、確信度：中）。P¹(ℤ/N) の 0・∞ を定義の「無限小と無限大」と結ぶ読みは構築側の候補（著者の判断が先）。ノート `pag2_pag266_p1_equator_rootnum.md`。
+   - 原始指標で 𝔀 がルート数であることは Lean の外。
+diff --git a/notes/pag2_p1_gluing_preregistration.md b/notes/pag2_p1_gluing_preregistration.md
+index 59c087e..a77d36e 100644
+--- a/notes/pag2_p1_gluing_preregistration.md
++++ b/notes/pag2_p1_gluing_preregistration.md
+@@ -81,7 +81,7 @@
+     2. 2 乗を外した形：conj(Ĵ(χ1, χ2)) = (−1)^{a1a2}·𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2))（符号は χ1・χ2 がともに奇のときだけ −1）。
+     3. 作用素の形：赤道のケットについて B_N(k1, k2) = (𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)))² · B_S(k1, k2)（Part 21（PAG25）の `equator_intertwine_hat` と 1 から）。これが索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める。（後注、2026-11-20：埋めない。Lean で結んだのは 𝔀 の値と P¹ の赤道の係数で、`JH` と P¹ のモデルを結ぶ文ではないので、索引 2.4 の留保は残る（Part 262 のノート §1）。留保は 2.4 にあり、1.4 ではない。）
+   - Lean の外に置くもの（ノートに数値・手計算・盲検として書く）：解の集まりの記述（φ(N)·2^{|Prim|} 個、単数倍の作用と平方のファイバー）、U² による読み、関数体との違い。
+-  - ラベル（見込み）：1・2 は［既知］（Conrad の定理 3.15 と |τ|² = N）、3 は［再導出（小さい）］。新規候補にはしない。兆候 4 は続く。（後注、2026-11-20：Part 262 のラベル（2026-11-20 16:40 の閉鎖で確定）は Part 262 のノート §4。ガウス和の形は［既知］、符号つきの形・2 乗の形・作用素の形は［再導出（小さい）］。符号つきの形を書いた文献は見つかっていない。）（後注 2026-11-25、統合照合 II-a の指摘：1・4・5 は 16:40 の閉鎖で確定、2・3 は 2026-11-20 17:29 に著者が［再導出（小さい）］で確定。）
++  - ラベル（見込み）：1・2 は［既知］（Conrad の定理 3.15 と |τ|² = N）、3 は［再導出（小さい）］。新規候補にはしない。兆候 4 は続く。（後注、2026-11-20：Part 262 のラベル（2026-11-20 16:40 の閉鎖で確定）は Part 262 のノート §4。ガウス和の形は［既知］、符号つきの形・2 乗の形・作用素の形は［再導出（小さい）］。符号つきの形を書いた文献は見つかっていない。）（後注 2026-11-25、統合照合 II-a・I-b の指摘：Part 262 の定理のうち、ガウス和の形と作用素の形の 2 つ（2 チャートのモデルと射影直線の版）は 16:40 の閉鎖で確定、符号つきの形と 2 乗の形は 2026-11-20 17:29 に著者が［再導出（小さい）］で確定。番号で書くと Part 262 のノート §4 の 1・4・5 と 2・3。）
+   - 閉じるときの統合照合に、台帳の L1〜L5 を一緒に載せる（台帳を閉じる機会にする）。
+ - **理由**：
+   1. 基礎文書の索引に明記された留保（1.4・2.4）を、短い Lean の文で埋められる（後注、2026-11-20：埋めるのではなく、留保に関わる材料が入る。留保は 2.4 にあり、残る）。著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」の「その上で働く」に、Lean の名前で引ける文が入る（読みの地位は著者の判断のまま）。
+diff --git a/notes/pag2_p1_tower_preregistration.md b/notes/pag2_p1_tower_preregistration.md
+index 3236139..397fd10 100644
+--- a/notes/pag2_p1_tower_preregistration.md
++++ b/notes/pag2_p1_tower_preregistration.md
+@@ -50,4 +50,4 @@
+ - 対照群：構造の文はすべて F_q[t] でも成り立つ（形式の文、ℚ に固有の算術なし）。
+ - 閉じるときの統合照合に、台帳の L11・L12 を載せる（停止規則）。
+ 
+-（後注 2026-11-25 夜：著者の採用（18:27）を受けて Part 263（PAG267）として実施した。予定の 5 つの文はすべて Lean に入った。5 は証人 (1, 2) だけでなく、両立の判定（上の段の法の素因数がすべて下の段の法を割るとき、そのときに限る）と、0 延長が極限に降りないことの形になった。独立照合の指摘で、反転と制限の関係 resL ∘ W_∞ = invL ∘ resL を足した。全射性は Lean で示せたので、段の単射性も Lean の中にある。結果はノート `notes/pag2_pag267_p1_tower.md`。）
++（後注 2026-11-25 夜：著者の採用（18:27）を受けて Part 263（PAG267）として実施した。予定の 5 つの文はすべて Lean に入った（ただし 4 の「`Uinf` はその像の側で働く」は型の上の事実で、Lean の文ではない。統合照合 I-a の指摘で書き足した）。5 は証人 (1, 2) だけでなく、両立の判定（上の段の法の素因数がすべて下の段の法を割るとき、そのときに限る）と、0 延長が極限に降りないことの形になった。独立照合の指摘で、反転と制限の関係 resL ∘ W_∞ = invL ∘ resL を足した。全射性は Lean で示せたので、段の単射性も Lean の中にある。結果はノート `notes/pag2_pag267_p1_tower.md`。）
+diff --git a/notes/pag2_pag266_p1_equator_rootnum.md b/notes/pag2_pag266_p1_equator_rootnum.md
+index a5097c1..66a258d 100644
+--- a/notes/pag2_pag266_p1_equator_rootnum.md
++++ b/notes/pag2_pag266_p1_equator_rootnum.md
+@@ -61,8 +61,8 @@
+   - 統合照合の後の直しは、台帳の L7 として次の照合（再照合）の入力に含めた。
+ - 再照合 R2（2026-11-20 15:15〜15:31、`records/audit266/recheck_int/`。1 回目の照合者は朝に利用の上限で止まったので、同じ入力で立て直した。記録 `records/audit266/recheck_int/attempts.txt`）：L7 と L8（台帳の外に見つかった直し）を照らした。形式文より強い文は見つからなかった。指摘の主なもの：ラベルの「統合照合の後に確定」は地位の格上げ（統合照合はラベルを確定していない）、索引 2.4 の留保から「照合した範囲では」が落ちた、引き継ぎメモで 19:58 の著者の判断の記録を著者の確認なしに書き換えた、引き継ぎメモの古い自己申告に注がない、n ≥ 1 の J = 0 を一般形で書いた。直した（台帳 L9）。
+ - 照合 R3（2026-11-20 15:37〜15:45、`records/audit266/recheck_L9/`）：L9 を照らした。形式文より強い文はなし。指摘の主なもの：PAG265 で 19:58 の判断を「確認した」と強め、出所を誤って標示した、概要の標示の文（「決めたのは…だけ」）が事実と違う、留保の範囲の限定の漏れ（ノート §1・索引・xlsx）、ラベルの理由の文の慣行の主張に反例がある。直した（台帳 L10）。R3 の時刻は、起動（コミット 768cb6b の後）から通知まで。計測は約 468 秒（`records/audit266/recheck_L9/outputs/R3_meta.txt`。照合者の目安の申告は約 10〜12 分）。（後注 2026-11-25、統合照合 II-a の指摘：R3 の照合者が示した手の論証の素描（n ≥ 1 で χ₁χ₂ が原始的でないとき J = 0）の文は、閉鎖の行に移っているが、R3 の時点のもの。）
+-- 照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/`）：L10 を照らした。指摘はすべて低か極低で、形式文・記録より強い文と、著者の判断の記録の書き換えはなかった。台帳の範囲の書き漏れ、ノート §2 の K の二つの意味、出所のパスの欠け、12:48 の二つの記述などを直した（台帳 L11）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
+-- 閉鎖（2026-11-20 16:40）：著者が止め方の規則を決めた（低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい。CLAUDE.md §7）。R4 はこれに当たるので、Part 262 は閉じた。台帳 L11 は次のパートの統合照合に載せる。ラベル（1 は［既知］、2〜5 は［再導出（小さい）］、新規候補なし）はこの閉鎖で確定した。2・3 のラベルは 2026-11-20 17:29 に著者が［再導出（小さい）］で確定した（符号つきの形はその形では文献に見つかっておらず、「［既知］の直接の帰結」は文献の範囲を広く見せるため）。R3 の照合者は、n ≥ 1 で χ₁χ₂ が原始的でないとき J = 0 になることの手の論証の素描を示した（Lean の外、照合者の確信度：高）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
++- 照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/`）：L10 を照らした。指摘はすべて低か極低で、形式文・記録より強い文と、著者の判断の記録の書き換えはなかった。台帳の範囲の書き漏れ、ノート §2 の K の二つの意味、出所のパスの欠け、12:48 の二つの記述などを直した（台帳 L11）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側。2（ノート §2 の K）は L11 で直した。1（L10 の範囲と自己申告）は L11 で一部を直した（閉じた L9 の範囲の「含める→含めた」は直していない。II-a の判定、統合照合 I-b の指摘でこの括弧を直した）。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
++- 閉鎖（2026-11-20 16:40）：著者が止め方の規則を決めた（低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい。CLAUDE.md §7）。R4 はこれに当たるので、Part 262 は閉じた。台帳 L11 は次のパートの統合照合に載せる。ラベル（1 は［既知］、2〜5 は［再導出（小さい）］、新規候補なし）はこの閉鎖で確定した。2・3 のラベルは 2026-11-20 17:29 に著者が［再導出（小さい）］で確定した（符号つきの形はその形では文献に見つかっておらず、「［既知］の直接の帰結」は文献の範囲を広く見せるため）。R3 の照合者は、n ≥ 1 で χ₁χ₂ が原始的でないとき J = 0 になることの手の論証の素描を示した（Lean の外、照合者の確信度：高）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側。2（ノート §2 の K）は L11 で直した。1（L10 の範囲と自己申告）は L11 で一部を直した（閉じた L9 の範囲の「含める→含めた」は直していない。II-a の判定、統合照合 I-b の指摘でこの括弧を直した）。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
+ 
+ ## §7 収束アラームの報告
+ 
+diff --git a/notes/pag2_pag267_p1_tower.md b/notes/pag2_pag267_p1_tower.md
+index cfa87cb..a56b28c 100644
+--- a/notes/pag2_pag267_p1_tower.md
++++ b/notes/pag2_pag267_p1_tower.md
+@@ -24,8 +24,8 @@
+ 
+ - `LimP` は P¹(Ẑ) = ∏_p P¹(ℤ_p) の上の局所定数関数の空間と同一視できる（盲検の照合者の記述。Lean にしていない）。Ẑ^× は P¹(Ẑ) の中で閉だが開でない。
+ - 5 はこの「開でない」の有限レベルの形：素数を足す段（b の素因数が a を割らない段）では、赤道の逆像が上の段の赤道より大きい。整除の順序の共終な部分系はどれも素数を足す段を含む。
+-- したがって、すべての素点を測る段では、`Uinf`（Part 254）を局所定数関数の上の作用素として赤道に閉じ込めることはできない。`Uinf` が作用するのは `resL` の行き先 `Lim` の側。`LimP` の上に `Uinf` を持ち上げる作用素（候補 C2）はこの文書の外で、5 はその障害の一つ（障害がすべてかどうかは調べていない）。これは索引 2.4 の留保の、空間の水準の理由の材料になる（留保そのものは埋まっていない）。
+-- `red_surjective`・`exists_redU`・`isUnit_of_castHom`・`exists_eqPt_of_red` の M ≠ 0 は証明の都合で、外しても成り立つ見込み（M = 0 では ℤ からの還元。独立照合の手計算。Lean にしていない）。
++- したがって、すべての素点を測る段では、`Uinf`（Part 254）を局所定数関数の上の作用素として赤道に閉じ込めることはできない。`Uinf` が作用するのは `resL` の行き先 `Lim` の側。`LimP` の上に `Uinf` を持ち上げる作用素（候補 C2）はこの文書の外。5 が妨げるのは各段の 0 延長による持ち上げだけで、`resL` の切断を使った持ち上げ（resL と可換な作用素）は妨げない（統合照合 I-a の照合者の手計算、Lean の外）。これは索引 2.4 の留保の、空間の水準の理由の材料になる（留保そのものは埋まっていない）。
++- `red_surjective`・`exists_redU`・`isUnit_of_castHom`・`exists_eqPt_of_red` の M ≠ 0 は証明の都合で、外しても成り立つ見込み（M = 0 では ℤ からの還元。素因数の条件のある 2 つでは M = 0 なら N = 0 で恒等。独立照合の手計算。Lean にしていない）。
+ - 0 延長との両立を整除の順序の共終な部分系の段だけに弱めても、5 の不存在は保たれる見込み（独立照合の手計算。Lean にしていない）。
+ - 数値：`records/p1_tower/numeric/p1_tower_check.py`（M ≤ 48 の N ∣ M の 198 組）。還元はすべて全射、|P¹(ℤ/M)| の公式はすべて一致、赤道の逆像が上の段の赤道と一致するのは M の素因数が N を割る組とちょうど同じ（5 と合う）。
+ - 対照群：1〜5 は F_q[t] の法でも同じ形で成り立つ見込みで（盲検の照合者）、ℚ に固有の算術は運ばない。
+@@ -46,10 +46,15 @@
+ 
+ ## §6 照合
+ 
+-- 独立照合（形式文と定義だけ、2026-11-25 18:42〜、約 119 秒、`records/audit267/outputs/check_output.md`。依頼文 `records/audit267/request_formal.md`、入力 `records/audit267/input_formal.md`）：逆翻訳は意図どおり。非空虚性の証人はすべての定理にある。除去テスト：N ≠ 1 と素因数の条件は外すと反例がある（N = 1、(2, 6) の [3:1] など）。M ≠ 0 は外しても成り立つ見込み。
++- 独立照合（形式文と定義だけ、2026-11-25 18:42〜、約 119 秒、`records/audit267/outputs/check_output.md`。依頼文 `records/audit267/request_formal.md`、入力 `records/audit267/input_formal.md`）：逆翻訳は意図どおり。非空虚性の証人は独立照合の時点の 30 定理すべてにある（足した 4 定理の証人は統合照合 I-a の照合者が数値で示した）。除去テスト：N ≠ 1 と素因数の条件は外すと反例がある（N = 1、(2, 6) の [3:1] など）。M ≠ 0 は外しても成り立つ見込み。
+ - 指摘と直し：赤道の外は 0・∞ と同じではない（合成数の法）、法 1 では 3 つの呼び名が区別を失う、`not_exists_extL` は `resL` の線形な切断を否定しない、共終な部分系でも不存在は保たれる見込み、反転と制限の関係の文がない。前の 4 つは冒頭の説明・docstring・このノートに書いた。最後の 1 つは `Wproj_eqPt`・`invG`・`invL`・`resL_WL` を足して Lean にした（主張を足した直し）。
+-- この直し（形式文の追加を含む）は、閉じるときの統合照合 I の入力に含める（台帳 L13）。
++- 独立照合の指摘 4.7 の後半（`WL` と `Uinf` を結ぶ文がない）は扱っていない（候補 C2 の範囲）。
++- この直し（形式文の追加を含む）は、閉じるときの統合照合 I の入力に含めた（台帳 L13）。
++- 統合照合 I-a（2026-11-25 18:53〜、約 191 秒、`records/audit267/outputs/integrated_Ia_output.md`）：形式文と食い違う散文、形式文の主張を取り違える文はなかった。足した 4 定理の逆翻訳と非空虚性の証人（数値）を照合者が示した。中 4 件（冒頭の説明の機械的な照合の件数、台帳 L13 の範囲の漏れ、「5 は C2 の障害の一つ」が広すぎる、着手前の文書の後注の「すべて Lean に入った」が `Uinf` の文を含む）と低・極低。直した（台帳 L15）。
++- 統合照合 I-b（同時、約 188 秒、`integrated_Ib_output.md`）：台帳 L14 を照らした。高はなし、中 4 件（R4 の後注の「L11 で直した」、辞書 §20 の後注が数値より強い、推薦案・索引の後注の番号、16:40 の条文が残っていない）。直した（台帳 L15）。
+ 
+ ## §7 収束アラームの報告
+ 
+-（閉鎖時に記入する。）
++- 辞書：Part 263 の名前の行を §22 に足した（右列が空の行 0、行のない名前 0。「文献用語なし」の行 2 つ）。
++- 文献照合：推薦案の盲検の問いテストで実施した（`records/p1_tower/`）。
++- 兆候 4：続いている（Part 249〜263 で 15 パート連続）。
+diff --git a/notes/pag2_tail_ledger.md b/notes/pag2_tail_ledger.md
+index 165e8b3..284adf6 100644
+--- a/notes/pag2_tail_ledger.md
++++ b/notes/pag2_tail_ledger.md
+@@ -4,26 +4,41 @@
+ 
+ ## 開いている項目
+ 
+-### L13：Part 263（PAG267）の独立照合の後の直し（2026-11-25 夜）
++### L15：統合照合 I-a・I-b の後の直し（2026-11-25 夜）
++
++- 範囲：I-a（`records/audit267/outputs/integrated_Ia_output.md`）と I-b（`records/audit267/outputs/integrated_Ib_output.md`）の指摘を受けた直し。
++  - PAG267.lean の冒頭の説明（コメントだけ。作り直してエラー・警告 0）：機械的な照合の件数を今の版に、「5 は C2 の障害の一つ」を「各段の 0 延長による持ち上げだけを妨げ、`resL` の切断を使った持ち上げは妨げない（照合者の手計算、Lean の外）」に狭めた、`WL` と `Uinf` を結ぶ文がないこと、M = 0 の 2 つの補題の書き方。
++  - Part 263 のノート（§3・§6）、着手前の文書の後注（`Uinf` の文は型の上の事実）、引き継ぎメモの Part 263 の項（Part 番号の併記、0 延長の但し書き、I-a・I-b の記録、著者に確かめる事項 4）、xlsx（`records/audit267/update_xlsx_267b.py`：「Lean の外」の標示 2 つ、Part 番号の併記、LABEL の但し書き）、数値スクリプト（何も確かめていなかった行を、還元と反転の可換の検査に置き換えた。出力は変わらない）。
++  - L14 の範囲の直し（後注の形）：R4 の後注の「L11 で直した」を「2 は直した、1 は一部」に（台帳 3 か所、Part 262 のノート 2 か所、引き継ぎメモ 2 か所）、L11 の注にも後注、推薦案・索引のラベルの後注を名前で書いた、引き継ぎメモの閉鎖の行にラベルの書き分けの後注と 16:40 の条文の逐語（コミット c7f2796）と会話の特定、辞書 §20 の F_p の後注を数値の範囲に合わせた、インスタンスの数の範囲、「インスタンスなので」。
++  - 辞書 §22（Part 263 の名前の行）を新設。
++  - ノート §7（収束アラームの報告）を記入。
++  - この台帳：L13・L14 を閉じた項目に移し、L15 を新設。閉じた L13・L14 の記載に、I-a・I-b が挙げた範囲の漏れを書き足した。
++- 直していないもの：CLAUDE.md（日英）の文面（著者側の版の写し。16:40 の条文そのものと、2 つの規則の関係、Part 260・`InLayer` の文の断りは、著者に確かめる事項）。II-a の低 5・7・8・11・12、II-b の K と k の表記、grep の式の拡大（さらい直しはしていない）、新しい文の Part 番号の併記の一部、検証手順の行番号の表記。
++- 自己申告（根拠にしない）：主張を強めた文はない。辞書の F_p の後注と「5 は障害」の文は、どちらも範囲を狭めた直し。
++- 扱い：I-a・I-b に中の指摘があった（高はない）。停止規則の「もう1回だけ統合照合」は I-a・I-b で行ったので、Part 263 を閉じて L15 を次のパートの統合照合に載せるか、もう 1 回照らすかを、著者に確かめる（引き継ぎメモの確かめる事項 4）。
+ 
+-- 範囲：独立照合（`records/audit267/outputs/check_output.md`）の指摘を受けた直し。
+-  - PAG267.lean：定理 4 つを足した（`invG_comp_pullSys`・`invL_ofL`・`Wproj_eqPt`・`resL_WL`。定義 `invG`・`invL`。主張を足した直し）。冒頭の説明（赤道の外は 0・∞ と同じでない、法 1、`not_exists_extL` は `resL` の線形な切断を否定しない、M ≠ 0 は外しても成り立つ見込み、共終な部分系の見込み、内部照合の B の行）と `not_exists_extL` の docstring。
+-  - ノート `notes/pag2_pag267_p1_tower.md`（§2・§3・§5・§6）、xlsx（行 3724〜3757、メモ、検証手順の行 286。`records/audit267/update_xlsx_267.py`）、この台帳の L13〜L14 と閉じた項目への移動。
+-- 自己申告（根拠にしない）：足した定理は sorry 0・警告 0、#print axioms は標準の 3 つ。機械的な照合をやり直した（712 回、一致なし）。
+-- 扱い：閉じるときの統合照合 I に載せる。
++## 閉じた項目
+ 
+-### L14：統合照合 II-a・II-b の後の直し（2026-11-25 夜）
++- L13・L14（2026-11-25 に閉じた）：統合照合 I-a（L13 と Part 263 の材料）・I-b（L14）を、直しそのものを入力に含めて受けた（`records/audit267/integrated/input_Ia.md`・`input_Ib.md`）。I-a は形式文と食い違う散文・取り違える文を見つけなかった。I-b は形式文が入力になく、形式文との突き合わせはできなかった。高はなく、中が各 4 件。直しは L15。
++  - 閉じたときの L13・L14 の記載は下にそのまま残す。範囲の漏れ（I-a・I-b の指摘）：L13 は引き継ぎメモの Part 263 の項、着手前の文書の後注、冒頭の説明の主な定理 4 の追記、新しい docstring を書いていなかった。L14 は閉じた項目の L11・L12 の記載と台帳の漏れの記録を書いていなかった。L14 の「どれも後注の形」は強すぎた（辞書の `fC` と「名前ではない」、CLAUDE.en.md はその場で直した）。L14 の扱いの理由は、高・中の指摘で閉じる条件を満たさないため、と書くべきだった。
++    ### L13：Part 263（PAG267）の独立照合の後の直し（2026-11-25 夜）
+ 
+-- 範囲：II-a（`records/audit267/outputs/integrated_IIa_output.md`）と II-b（`integrated_IIb_output.md`）の指摘を受けた直し。どれも後注の形で足し、記録の文は書き換えていない。
+-  - 「R4 は低・極低だけ」の後注（R4 の 6 節の 1・2 は「低〜中」だった。16:40 の著者の決定がこれを知ったうえでのものかを著者に確かめる）：この台帳（L11 の扱い、閉じた L10 の 2 か所）、Part 262 のノート §6（R4 と閉鎖の行）、引き継ぎメモ（R4 と閉鎖の行）。
+-  - ラベルの確定の書き分けの後注（1・4・5 は 16:40、2・3 は 17:29 に著者が確定）：PAG266.lean の冒頭の説明（コメントだけ。作り直してエラー・警告 0）、Part 262 のノート §4、索引（1 か所）、推薦案 `pag2_p1_gluing_preregistration.md`（1 か所）、引き継ぎメモ（ラベルの行）。
+-  - Part 262 のノート §6 の R3 の行に、素描の文が R3 の時点のものという後注。引き継ぎメモの 17:29 の項に出所（著者の会話のメッセージ）と、理由の文は構築側の要約という後注。引き継ぎメモの閉鎖の行に、16:40 の著者のメッセージの逐語の後注。
+-  - 辞書：§21 のさらい方の式の穴の後注、インスタンスの数（3 → 4）、「名前ではない」→「定義ではない」、`fC` の確信度：中、§20 の設定と F_p の式の範囲の後注。CLAUDE.en.md の英語の誤り 2 つ（an algebra、Signal 4）。
+-  - 引き継ぎメモに、著者に確かめる事項（16:40 の決定の前提、CLAUDE.md §7 の 2 つの規則の関係、CLAUDE.md §2 の Part 260 の 3 条件・`InLayer` の文は著者側の版の写しで構築側は Lean で未確認）を書いた。
+-- 直していないもの：CLAUDE.md（日本語版）の文面（著者側の版の写しなので、著者に確かめる事項にした）。II-a の低・極低の一部（L9 の範囲の「含める→含めた」、R3・R4 の時刻の出所の書き足し、「1406 行」の指し方、検索語の書き足し）。
+-- 扱い：閉じるときの統合照合 I に載せる（II-a に「高」1 件・「中」3 件、II-b に「中」3 件があったので、停止規則の「もう1回だけ統合照合」に当たる）。
++    - 範囲：独立照合（`records/audit267/outputs/check_output.md`）の指摘を受けた直し。
++      - PAG267.lean：定理 4 つを足した（`invG_comp_pullSys`・`invL_ofL`・`Wproj_eqPt`・`resL_WL`。定義 `invG`・`invL`。主張を足した直し）。冒頭の説明（赤道の外は 0・∞ と同じでない、法 1、`not_exists_extL` は `resL` の線形な切断を否定しない、M ≠ 0 は外しても成り立つ見込み、共終な部分系の見込み、内部照合の B の行）と `not_exists_extL` の docstring。
++      - ノート `notes/pag2_pag267_p1_tower.md`（§2・§3・§5・§6）、xlsx（行 3724〜3757、メモ、検証手順の行 286。`records/audit267/update_xlsx_267.py`）、この台帳の L13〜L14 と閉じた項目への移動。
++    - 自己申告（根拠にしない）：足した定理は sorry 0・警告 0、#print axioms は標準の 3 つ。機械的な照合をやり直した（712 回、一致なし）。
++    - 扱い：閉じるときの統合照合 I に載せる。
+ 
+-## 閉じた項目
++    ### L14：統合照合 II-a・II-b の後の直し（2026-11-25 夜）
++
++    - 範囲：II-a（`records/audit267/outputs/integrated_IIa_output.md`）と II-b（`integrated_IIb_output.md`）の指摘を受けた直し。どれも後注の形で足し、記録の文は書き換えていない。
++      - 「R4 は低・極低だけ」の後注（R4 の 6 節の 1・2 は「低〜中」だった。16:40 の著者の決定がこれを知ったうえでのものかを著者に確かめる）：この台帳（L11 の扱い、閉じた L10 の 2 か所）、Part 262 のノート §6（R4 と閉鎖の行）、引き継ぎメモ（R4 と閉鎖の行）。
++      - ラベルの確定の書き分けの後注（1・4・5 は 16:40、2・3 は 17:29 に著者が確定）：PAG266.lean の冒頭の説明（コメントだけ。作り直してエラー・警告 0）、Part 262 のノート §4、索引（1 か所）、推薦案 `pag2_p1_gluing_preregistration.md`（1 か所）、引き継ぎメモ（ラベルの行）。
++      - Part 262 のノート §6 の R3 の行に、素描の文が R3 の時点のものという後注。引き継ぎメモの 17:29 の項に出所（著者の会話のメッセージ）と、理由の文は構築側の要約という後注。引き継ぎメモの閉鎖の行に、16:40 の著者のメッセージの逐語の後注。
++      - 辞書：§21 のさらい方の式の穴の後注、インスタンスの数（3 → 4）、「名前ではない」→「定義ではない」、`fC` の確信度：中、§20 の設定と F_p の式の範囲の後注。CLAUDE.en.md の英語の誤り 2 つ（an algebra、Signal 4）。
++      - 引き継ぎメモに、著者に確かめる事項（16:40 の決定の前提、CLAUDE.md §7 の 2 つの規則の関係、CLAUDE.md §2 の Part 260 の 3 条件・`InLayer` の文は著者側の版の写しで構築側は Lean で未確認）を書いた。
++    - 直していないもの：CLAUDE.md（日本語版）の文面（著者側の版の写しなので、著者に確かめる事項にした）。II-a の低・極低の一部（L9 の範囲の「含める→含めた」、R3・R4 の時刻の出所の書き足し、「1406 行」の指し方、検索語の書き足し）。
++    - 扱い：閉じるときの統合照合 I に載せる（II-a に「高」1 件・「中」3 件、II-b に「中」3 件があったので、停止規則の「もう1回だけ統合照合」に当たる）。
+ 
+ - L11・L12 と、台帳に項目のなかった記録の追記（コミット c7f2796・600b7c5・e6cb086・c3efc8d）（2026-11-25 に閉じた）：統合照合 II-a（L11 と c7f2796・600b7c5）・II-b（L12 と e6cb086・c3efc8d）を、直しそのもの（各コミットの差分）を入力に含めて受けた（`records/audit267/integrated/`、`records/audit267/outputs/`）。形式文より強い文の指摘はなかった。記録の側の指摘（II-a の高 1・中 3、II-b の中 3）の直しは L14。
+   - 閉じたときの L11・L12 の記載は、下にそのまま残す。台帳の漏れ（II-a の 4 節・II-b の 4 節）：L11 はノート §6 の R2・R3 の行の直し、閉じた L10 の「扱い」の行、`update_xlsx_266d.py` の追記と xlsx のメモの手での置き換えを書いていなかった。L12 は e6cb086・c3efc8d と、§20 の行の出典・注意の欄の書き換えと P¹(ℤ/p^K) の削除を書いていなかった。c7f2796・600b7c5 は台帳に項目がなかった。どれも II-a・II-b の入力の差分には入っていた。
+@@ -38,8 +53,8 @@
+       - この台帳：閉じた L10 の範囲と自己申告の書き足し、閉じた根拠の補足の出所のパス、L11 の新設。
+       - 確かめたこと：PAG265 のノートに「確認した」はない（検索）。Part 262 のノート §3 の確信度に出所を足した。着手前の文書の Q3 の行は盲検の答えの要約で、確信度は書いていない。
+     - 自己申告（根拠にしない）：出所・範囲の書き足しと、12:48 の記述の訂正。
+-    - 扱い：2026-11-20 16:40 の著者の決定（止め方の規則、CLAUDE.md §7）により、次のパートの統合照合に載せる。R4 は低・極低だけで、強めた文と判断の記録の書き換えはなかったので、Part 262 は閉じた。著者側の記録（2026-11-20 17:29）も、L1〜L10 は閉じ、L11 は次の統合照合に載る、で一致。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
+-    - 注：L7 から L11 まで、直しを照らすたびに、直しが生む小さなずれ（とくに台帳が自分の変更を書き漏らすこと）が見つかっている。R4 の指摘は低か極低だけになった。著者は 2026-11-20 16:40 に止め方の規則を決めた（上の扱い）。
++    - 扱い：2026-11-20 16:40 の著者の決定（止め方の規則、CLAUDE.md §7）により、次のパートの統合照合に載せる。R4 は低・極低だけで、強めた文と判断の記録の書き換えはなかったので、Part 262 は閉じた。著者側の記録（2026-11-20 17:29）も、L1〜L10 は閉じ、L11 は次の統合照合に載る、で一致。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側。2（ノート §2 の K）は L11 で直した。1（L10 の範囲と自己申告）は L11 で一部を直した（閉じた L9 の範囲の「含める→含めた」は直していない。II-a の判定、統合照合 I-b の指摘でこの括弧を直した）。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
++    - 注：L7 から L11 まで、直しを照らすたびに、直しが生む小さなずれ（とくに台帳が自分の変更を書き漏らすこと）が見つかっている。R4 の指摘は低か極低だけになった。著者は 2026-11-20 16:40 に止め方の規則を決めた（上の扱い）。（後注 2026-11-25、統合照合 I-b の指摘：「R4 の指摘は低か極低だけになった」は R4 の出力と合わない。R4 の 6 節の 1・2 は「低〜中」だった。）
+ 
+     ### L12：辞書の欠落行の追加と CLAUDE.md の写し（2026-11-20 夕方、補足 16）
+ 
+@@ -47,7 +62,7 @@
+     - 自己申告（根拠にしない）：文献の言葉は根拠つきで書いた。`canon` と `shellLift` の一致は見込みで、Lean で確かめていない。
+     - 扱い：L11 と一緒に、次のパートの統合照合に載せる。
+ 
+-- L10（2026-11-20 に閉じた）：照合 R4 を、直しそのものを入力に含めて受けた。指摘は低か極低だけで、直しは L11。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
++- L10（2026-11-20 に閉じた）：照合 R4 を、直しそのものを入力に含めて受けた。指摘は低か極低だけで、直しは L11。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側。2（ノート §2 の K）は L11 で直した。1（L10 の範囲と自己申告）は L11 で一部を直した（閉じた L9 の範囲の「含める→含めた」は直していない。II-a の判定、統合照合 I-b の指摘でこの括弧を直した）。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
+   - 閉じたときの記載：
+     - 旧項目 L10：照合 R3 の後の直し（2026-11-20 夕方）
+ 
+@@ -62,7 +77,7 @@
+       - この台帳：L7・L8・L9 を閉じた項目に移し、L10 を新設。閉じた L9 の記載に、範囲の 2 行・自己申告の追記・扱いの行を書き足し、閉鎖の要約の行を足した。
+       - 範囲の書き足し（照合 R4 の指摘）：引き継ぎメモの「閉じる条件」の行の書き換え、Part 262 のノート §6 の R2 の記録の行（「次の照合の対象」を外した）。
+     - 自己申告（根拠にしない）：記録の言葉に揃える直し、範囲の限定、出所の書き足し。新しい文として、R3 の照合者の手の論証の素描を出所つきで引いた。R4 の指摘のとおり、ほかに新しい文として「J は K によらない」、確信度の出所（blind_output の Q3）、補足 15 のノートの記述、crt_output.md のパス、R3 の時刻、閉鎖の要約の内容も足していた。
+-    - 扱い：照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/outputs/R4_output.md`）で照らした。指摘は低か極低だけ。直しは L11。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
++    - 扱い：照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/outputs/R4_output.md`）で照らした。指摘は低か極低だけ。直しは L11。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側。2（ノート §2 の K）は L11 で直した。1（L10 の範囲と自己申告）は L11 で一部を直した（閉じた L9 の範囲の「含める→含めた」は直していない。II-a の判定、統合照合 I-b の指摘でこの括弧を直した）。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
+ 
+ - L7・L8・L9（2026-11-20 に閉じた）：L7・L8 は再照合 R2（`records/audit266/recheck_int/outputs/R2_output.md`）、L9 は照合 R3（`records/audit266/recheck_L9/outputs/R3_output.md`）を、直しそのものを入力に含めて受けた。どちらも形式文より強い文の指摘はなかった。R2 の指摘の直しは L9、R3 の指摘の直しは L10。
+   - 閉じたときの各項目の記載（記録として残す）：
+diff --git a/notes/pag2_terwilliger_dictionary.md b/notes/pag2_terwilliger_dictionary.md
+index 930e9e0..15615d1 100644
+--- a/notes/pag2_terwilliger_dictionary.md
++++ b/notes/pag2_terwilliger_dictionary.md
+@@ -470,13 +470,13 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
+ | `equator_intertwine_rootNum`・`equator_intertwine_proj_rootNum` | 2 チャートの比較そのものは文献用語なし。各チャートの中身は、乗法的指標の畳み込みがヤコビ和倍になること χ₁ ⋆ χ₂ = J(χ₁, χ₂)·χ₁χ₂（有限体 F_p の場合、χ₁χ₂ が自明でないとき）。北のチャートでは χ̄ の畳み込みなので係数は conj(J)。（2026-11-20 に補足 16 の作業で足した） | 畳み込みの式は N. Katz「Exponential Sums」の翻訳 arXiv:2308.11611 の Lemma 1.3.2 と arXiv:2406.11529 の §3（どちらも F_p。検索結果の抜粋で確認、2026-11-20）。ℤ/p^k での形は Part 20（PAG24）の `equator_intertwine` の Lean の文で、文献では確かめていない。2 チャートの比較の文献は、検索 1 回（convolution / inversion / projective line / Jacobi sum / two charts）で見つからなかった（見つからなかったは不存在の証明ではない）。Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換え。射影直線の版は 2 チャートの版を `projFunEquiv` で移したもので同値（手の論証、Lean の文ではない）。設定そのものは盲検の 1 回の検索では見つからなかった |
+ | 条件「U'² が赤道で B_S を B_N に移す」の解の集まり（Lean の外） | 部分群の補集合の上で乗法的な関数は準同型に延びる（|X/Y| ≥ 3）、ポントリャーギン双対 | 盲検の照合者の手計算（補題を書いた文献は探していない）。加法指標の取り替えで局所定数が χ(b) 倍になること（Tate、Biswas arXiv:1401.5591 §4.3） |
+ 
+-- 後注（2026-11-25、統合照合 II-b の指摘）：作用素の形の行の比較の設定は P¹(ℤ/p^K) の 2 チャート（補足 16 の作業で文献の欄から設定の記述が落ちた）。F_p の畳み込みの式は、ℤ/p^k では指標が原始的な場合に限って成り立つ（照合者の数値：原始的なら法 9・25・27・49 で不一致 0、限らないと法 9 で 270 個中 8 個の不一致）。
++- 後注（2026-11-25、統合照合 II-b の指摘）：作用素の形の行の比較の設定は P¹(ℤ/p^K) の 2 チャート（補足 16 の作業で文献の欄から設定の記述が落ちた）。F_p の畳み込みの式は、ℤ/p^k では、照合者の数値（法 9・25・27・49）で χ₁・χ₂・χ₁χ₂ がすべて原始的なら不一致 0。制限しないと法 9 で 270 個中 8 個の不一致があり、不一致は χ₁χ₂ が原始的でない組に出た（統合照合 I-b の照合者の数値。一般の証明・文献は確かめていない。I-b の指摘で「原始的な場合に限って成り立つ」を直した）。
+ - 未記入の件数（この節）：0（2026-11-20 に補足 16 の作業で、作用素の形の行の右列を埋めた：比較そのものは「文献用語なし」、各チャートの畳み込みはヤコビ和倍の式。それまでは 1 と数えていた。統合照合 I の指摘）。
+ 
+ ## 21. 行のなかった名前の追加（補足 16、2026-11-20。Parts 257〜261（PAG261〜PAG265）と parFac）
+ 
+ - 欠落の種類（補足 16 の 5）：辞書の欠落には、右列が空の行だけでなく、**行そのものがない名前**もある。§7 の指標（右列が空の行の数）はこれを拾わないので、未記入の件数を数えるときは、各パートの新しい定義名に行があるかも確かめる。
+-- さらった範囲（補足 16 の 4）：2026-11-20 に、PAG261〜PAG265 の `def`・`abbrev`・`structure`・`instance` の宣言を機械的に抜き出した（`grep -nE "^\s*(noncomputable )?(def|abbrev|structure|inductive|class|instance)\s"`）。定理の名前は対象にしていない（後注 2026-11-25、統合照合 II-b の指摘：式には `inductive`・`class` も入っている。`private`・`protected` のつく宣言、同じ行に属性がつく宣言、`irreducible_def` は拾わない式で、完全性の確認としては穴がある）。抜き出した定義名のうち、§17・§18 に行のあったもの（`fsum`、`cornerOp`、`cornerHom`、`CornerLim`、`ofCorner`）を除き、すべて下の表に入れた。インスタンス（`lvl_neZero`、`NeZero (primeProd S)`、`DirectedSystem` の 2 つ（`sqMap`・`cornerSys` の行）の 4 つ。後注 2026-11-25、統合照合 II-b の指摘で「3 つ」を直した）は定義ではないので行にせず、所属する定義の行に書いた。補足 16 は `parFac` を Part 257 としていたが、定義は PAG256（Part 252）にある。
++- さらった範囲（補足 16 の 4）：2026-11-20 に、PAG261〜PAG265 の `def`・`abbrev`・`structure`・`instance` の宣言を機械的に抜き出した（`grep -nE "^\s*(noncomputable )?(def|abbrev|structure|inductive|class|instance)\s"`）。定理の名前は対象にしていない（後注 2026-11-25、統合照合 II-b の指摘：式には `inductive`・`class` も入っている。`private`・`protected` のつく宣言、同じ行に属性がつく宣言、`irreducible_def` は拾わない式で、完全性の確認としては穴がある）。抜き出した定義名のうち、§17・§18 に行のあったもの（`fsum`、`cornerOp`、`cornerHom`、`CornerLim`、`ofCorner`）を除き、すべて下の表に入れた。インスタンス（`lvl_neZero`、`NeZero (primeProd S)`、`DirectedSystem` の 2 つ（`sqMap`・`cornerSys` の行）の 4 つ（上の grep の式で拾った範囲で）。後注 2026-11-25、統合照合 II-b の指摘で「3 つ」を直した）はインスタンスなので行にせず、所属する定義の行に書いた。補足 16 は `parFac` を Part 257 としていたが、定義は PAG256（Part 252）にある。
+ - 書き方（補足 16 の 2・3）：文献の言葉が見つからない場合は「文献用語なし」と書いた。文献の言葉を書く場合は、根拠と確かめ方を添えた。「定義の読み」は、Lean の定義を読んで標準の数学用語と照らしたことを指し、文献の本文は開いていない。
+ 
+ | 名前 | Part（PAG） | 文献の言葉 | 根拠・確かめ方 |
+@@ -505,3 +505,20 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
+ 
+ - 未記入の件数（この節）：0（すべての行に文献の言葉か「文献用語なし」がある）。「文献用語なし」の行は 7 つ（`lvl`、`oddCount`、`Compat`、`CompatF`、捩れの 6 つをまとめた行、`primeProd`、`sqMap`）。
+ - 次の統合照合で完全性を確かめるときは、上のさらい方で同じ範囲を抜き出し、この表と突き合わせる。
++
++## 22. Part 263（PAG267、短期層）の名前（2026-11-25）
++
++| 名前 | 文献の言葉 | 根拠・確かめ方 |
++|---|---|---|
++| `redU`・`red` | 射影直線の還元写像 P¹(ℤ/M) → P¹(ℤ/N)（N ∣ M） | 盲検の照合者の申告（Cremona・Stein の Manin 記号の章、SL₂ の持ち上げは Shimura Lemma 1.38。節番号は照合者の記憶で未確認）。定義の読み。 |
++| `zeroPt`・`infPt` | P¹ の点 0 = [0:1]、∞ = [1:0] | 定義の読み。 |
++| `eqU`・`eqPt` | 文献用語なし（両座標が単数の点 [x:1]。この鎖の言葉で「赤道」。Part 19（PAG23）の 2 チャートのモデルの赤道と同じ集合） | ― |
++| `Fsp`・`pullP`・`LimP`・`ofP` | 引き戻しの帰納系と加群の帰納極限。読み（Lean の外）では P¹(Ẑ) の上の局所定数関数の空間 | Mathlib の `Module.DirectLimit`（定義の読み）。P¹(Ẑ) との同一視は盲検の照合者の記述。 |
++| `Wfun`・`WL` | 反転の引き戻し（Part 24（PAG28）の `Wpull`）と、それが極限に誘導する写像 | 定義の読み。 |
++| `resE`・`resL` | 開でない部分集合（Ẑ^×）への制限写像（読み） | 定義の読み。Ẑ^× が P¹(Ẑ) の中で開でないことは盲検の照合者の記述（Lean の外）。 |
++| `invG`・`invL` | 単数群の逆元による引き戻し（反転 x ↦ x⁻¹） | 定義の読み。 |
++| `extE` | 0 による延長（extension by zero） | 定義の読み。極限に降りないこと（`not_exists_extL`）は、開でない部分集合からの 0 延長が局所定数性を保たないことの有限レベルの形（読み）。 |
++| `lv1`・`lv2` | 文献用語なし（法 1・法 2 の添字） | ― |
++
++- 未記入の件数（この節）：0。「文献用語なし」の行は 2 つ（`eqU`・`eqPt`、`lv1`・`lv2`）。
++- さらい方：PAG267 の `def`・`abbrev`・`structure`・`instance` を抜き出した（インスタンスは `DirectedSystem Fsp` の 1 つで、`pullP` の行に属する）。
+diff --git a/records/audit267/update_xlsx_267b.py b/records/audit267/update_xlsx_267b.py
+new file mode 100644
+index 0000000..48289eb
+--- /dev/null
++++ b/records/audit267/update_xlsx_267b.py
+@@ -0,0 +1,23 @@
++"""統合照合 I-a の指摘による xlsx の直し（2026-11-25）。"""
++import openpyxl, shutil
++R = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
++wb = openpyxl.load_workbook(R); ws = wb['定理と証明']
++reps = {
++ '（N = 1 では等しい）': '（N = 1 では等しい：Lean の外、手計算）',
++ '（合成数の法では赤道の外は 0・∞ だけではない）': '（合成数の法では赤道の外は 0・∞ だけではない：Lean の外）',
++ 'Part 24 の mk_inv_eq': 'Part 24（PAG28）の mk_inv_eq',
++ 'Part 24 の Wpull': 'Part 24（PAG28）の Wpull',
++ 'Lim（Part 254）': 'Lim（Part 254（PAG258））',
++ 'Part 254 の Lim': 'Part 254（PAG258）の Lim',
++ '0 延長は極限に降りない。': '0 延長は極限に降りない（各段の 0 延長と一致する線形写像がない。resL の切断の存在は否定しない）。',
++}
++n = 0
++for r in range(3724, 3758):
++    for c in range(1, 6):
++        v = ws.cell(r, c).value
++        if isinstance(v, str):
++            w = v
++            for a, b in reps.items():
++                if a in w and b not in w: w = w.replace(a, b)
++            if w != v: ws.cell(r, c).value = w; n += 1
++wb.save(R); shutil.copy(R, '/home/claude/out/final85/lean_verification_status.xlsx'); print('cells changed', n)
+diff --git a/records/p1_tower/numeric/p1_tower_check.py b/records/p1_tower/numeric/p1_tower_check.py
+index c369f23..562fbee 100644
+--- a/records/p1_tower/numeric/p1_tower_check.py
++++ b/records/p1_tower/numeric/p1_tower_check.py
+@@ -1,3 +1,4 @@
++"""P¹(ℤ/N) の還元の数値照合（Part 263（PAG267）、2026-11-25）：全射性、点の数の公式、反転との可換、赤道の逆像と上の段の赤道の一致の判定。"""
+ from math import gcd
+ def P1(N):
+     pts=set()
+@@ -31,7 +32,8 @@ for M in range(1,49):
+         if img!=PN: bad+=1; print("not surj",N,M)
+         # W commute
+         for (a,b) in PM:
+-            assert canon(b%N,a%N,N)==canon(*canon(b,a,M),N) if False else True
++            c=canon(a%N,b%N,N)
++            assert canon(b%N,a%N,N)==canon(c[1],c[0],N)   # red(W q) = W(red q)（統合照合 I-a の指摘で、何も確かめていなかった行を置き換えた）
+         # equator preimage vs upper equator: zero-extension compat?
+         # f on equator(N) indicator of one point; zero-extend then pull vs pull then zero-extend
+         eqN=[x for x in PN if isEq(*x,N)]
+diff --git a/PAG267.lean b/PAG267.lean
+index ddf96b0..aec3588 100644
+--- a/PAG267.lean
++++ b/PAG267.lean
+@@ -42,7 +42,7 @@ Lean の外：
+ 直ちに出るもの（B）：`Wproj_eqPt` は Part 24（PAG28）の `mk_inv_eq`（ZMod の逆元で書いた [y⁻¹:1] = [1:y]）と同じ内容。
+ 近いもの（C）：Part 23（PAG27）の `toProj`（素数冪の法で x ↦ [x:1]）、Part 24（PAG28）の `projFunEquiv` の [x:1] での値。
+ 
+-ラベル（見込み、閉鎖で確定）：1〜3 は［既知］（射影直線の還元、有限集合の全射の逆系の上の局所定数関数）。4・5 は［再導出（小さい）］。新規候補なし。
++ラベル（2026-11-25 19:11 の著者の判断による閉鎖で確定）：1〜3 は［既知］（射影直線の還元、有限集合の全射の逆系の上の局所定数関数）。4・5 は［再導出（小さい）］。新規候補なし。
+ 対照群：1〜5 の文は F_q[t] の法でも同じ形で成り立つ見込みで、ℚ に固有の算術は運ばない。
+ -/
+ import PAG258
+diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
+index 26de234..0996eb5 100644
+--- a/handoff/PAG2_handoff_part259.md
++++ b/handoff/PAG2_handoff_part259.md
+@@ -1738,7 +1738,7 @@
+ - **Part 263（PAG267、短期層の小さいノート、2026-11-25）：P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限、赤道への制限と赤道からの 0 延長**：
+   - 出所：基礎文書の索引の「射影」の空間の水準の問い（索引 1.4・2.4）。推薦案 `notes/pag2_p1_tower_preregistration.md` §4（盲検の指摘で改めた C1）を、2026-11-25 18:27 に著者が採用した（「進めてください」）。
+   - Lean：PAG267.lean、定理 34、sorry 0・警告 0、#print axioms は標準の 3 つ。還元の恒等・合成の法則・反転との可換・全射（M ≠ 0）、0 ≠ ∞（N ≠ 1）、引き戻しの帰納系と極限の上の対合 W_∞、赤道への制限が誘導する `resL : LimP → Lim`（Part 254 の Lim）の全射と resL ∘ W_∞ = invL ∘ resL、0 延長が引き戻しと可換 ⇔ 上の段の法の素因数がすべて下の段の法を割る（証人 (1, 2)）、0 延長は極限に降りない（各段の 0 延長と一致する線形写像がない。`resL` の切断の存在は否定しない）。ノート `notes/pag2_pag267_p1_tower.md`。辞書 §22。xlsx は final85（行 3724〜3757 を足した）。
+-  - ラベル（見込み、閉鎖で確定）：1〜3 は［既知］、4・5 は［再導出（小さい）］、新規候補なし。兆候 4 は続く（Part 249〜263 で 15 パート連続）。
++  - ラベル（2026-11-25 19:11 の閉鎖で確定）：1〜3 は［既知］、4・5 は［再導出（小さい）］、新規候補なし。兆候 4 は続く（Part 249〜263 で 15 パート連続）。
+   - 内部照合：Part 258（PAG262）の `mem_ker_iff` と Part 24（PAG28）の `Wpull` を使った（言葉の検索）。機械的な照合 712 回で一致なし。`Wproj_eqPt` は Part 24（PAG28）の `mk_inv_eq` と同じ内容（B）。
+   - 照合：独立照合（約 119 秒）。指摘で 4 定理を足した（台帳 L13）。同時に、台帳 L11・L12 と台帳に項目のなかった記録の追記を統合照合 II-a・II-b で照らした（L11・L12 は閉じた）。II-a に「高」1 件：R4 の指摘は「低〜中」2 件を含んでいたのに、記録は「低か極低だけ」と書いていた。直しは後注の形で入れた（台帳 L14）。L13・L14 は閉じるときの統合照合 I（I-a・I-b）で照らした。I-a・I-b とも高はなく、中がそれぞれ 4 件（記録と件数の側）。直しは台帳 L15。閉じるかどうかは著者に確かめる（下の 4）。
+   - 著者に確かめる事項（2026-11-25）：
+@@ -1746,3 +1746,8 @@
+     2. CLAUDE.md §7 の「照合の後に直した文面は、そのパートを閉じる前に再照合する（2026-11-13）」と、止め方の規則（2026-11-20）の関係（止め方の規則が前者の例外であると明記するか）。リポジトリの CLAUDE.md は著者側の版の写しなので、構築側では文面を変えていない。
+     3. CLAUDE.md §2 の Part 260 の「3 条件すべてが効く」と「`InLayer` が定義する関係そのもの」の文は著者側の版の写しで、構築側はこの写しのために Lean で確かめていない（II-b の指摘）。
+     4. Part 263 を閉じてよいか。独立照合の後に定理 4 つを足した（主張を足した直し）ので、停止規則の「もう1回だけ統合照合」として I-a・I-b を行った。I-a・I-b とも高はなく、形式文と食い違う散文もなかったが、中がそれぞれ 4 件あった（記録・件数・範囲の書き方）。その直しは台帳 L15 で、主張を強めた直しはない（範囲を狭めた直しが 2 つ）。止め方の規則の「その後はこの規則で閉じる」を、中の指摘が残っていても閉じてよいと読むか、もう 1 回照らすかは、構築側では決めずに著者に確かめる。構築側の推薦は、閉じて L15 を次のパートの統合照合に載せること（理由：形式文の側の指摘がなく、直しは範囲を狭める側だけで、照らすたびに記録の側のずれが生まれる型が L7 以来続いているため）。
++  - 著者の回答（2026-11-25 19:11）：「1、2 とも良いです」。
++    - 1（構築側の報告では確かめる事項 1）：2026-11-20 16:40 の Part 262 の閉鎖の決定は、R4 の「低〜中」2 件を踏まえても保つ。
++    - 2（確かめる事項 4）：Part 263 を閉じてよい。台帳 L15 は次のパートの統合照合に載せる。ラベル（1〜3 は［既知］、4・5 は［再導出（小さい）］、新規候補なし）はこの閉鎖で確定。
++    - 確かめる事項 2・3（CLAUDE.md §7 の 2 つの規則の関係、§2 の Part 260・`InLayer` の文）は今回の報告では問いにしておらず、開いたまま（急がない）。
++
+diff --git a/notes/pag2_pag267_p1_tower.md b/notes/pag2_pag267_p1_tower.md
+index a56b28c..ac9ff9f 100644
+--- a/notes/pag2_pag267_p1_tower.md
++++ b/notes/pag2_pag267_p1_tower.md
+@@ -30,7 +30,7 @@
+ - 数値：`records/p1_tower/numeric/p1_tower_check.py`（M ≤ 48 の N ∣ M の 198 組）。還元はすべて全射、|P¹(ℤ/M)| の公式はすべて一致、赤道の逆像が上の段の赤道と一致するのは M の素因数が N を割る組とちょうど同じ（5 と合う）。
+ - 対照群：1〜5 は F_q[t] の法でも同じ形で成り立つ見込みで（盲検の照合者）、ℚ に固有の算術は運ばない。
+ 
+-## §4 ラベル（見込み。閉鎖で確定）
++## §4 ラベル（2026-11-25 19:11 の著者の判断による閉鎖で確定）
+ 
+ - 1〜3：［既知］。射影直線の還元と、全射の逆系の上の局所定数関数（盲検の照合者は Cremona・Stein の Manin 記号の章、SL₂ の持ち上げは Shimura Lemma 1.38 を挙げた。節番号は照合者の記憶で未確認）。
+ - 4・5：［再導出（小さい）］。
+@@ -53,6 +53,8 @@
+ - 統合照合 I-a（2026-11-25 18:53〜、約 191 秒、`records/audit267/outputs/integrated_Ia_output.md`）：形式文と食い違う散文、形式文の主張を取り違える文はなかった。足した 4 定理の逆翻訳と非空虚性の証人（数値）を照合者が示した。中 4 件（冒頭の説明の機械的な照合の件数、台帳 L13 の範囲の漏れ、「5 は C2 の障害の一つ」が広すぎる、着手前の文書の後注の「すべて Lean に入った」が `Uinf` の文を含む）と低・極低。直した（台帳 L15）。
+ - 統合照合 I-b（同時、約 188 秒、`integrated_Ib_output.md`）：台帳 L14 を照らした。高はなし、中 4 件（R4 の後注の「L11 で直した」、辞書 §20 の後注が数値より強い、推薦案・索引の後注の番号、16:40 の条文が残っていない）。直した（台帳 L15）。
+ 
++- 閉鎖（2026-11-25 19:11）：著者が、Part 263 を閉じてよいと判断した（引き継ぎメモの確かめる事項 4 への回答「良いです」）。台帳 L15 は次のパートの統合照合に載せる。ラベルはこの閉鎖で確定した。
++
+ ## §7 収束アラームの報告
+ 
+ - 辞書：Part 263 の名前の行を §22 に足した（右列が空の行 0、行のない名前 0。「文献用語なし」の行 2 つ）。
+diff --git a/notes/pag2_tail_ledger.md b/notes/pag2_tail_ledger.md
+index 284adf6..7b663b8 100644
+--- a/notes/pag2_tail_ledger.md
++++ b/notes/pag2_tail_ledger.md
+@@ -12,10 +12,11 @@
+   - L14 の範囲の直し（後注の形）：R4 の後注の「L11 で直した」を「2 は直した、1 は一部」に（台帳 3 か所、Part 262 のノート 2 か所、引き継ぎメモ 2 か所）、L11 の注にも後注、推薦案・索引のラベルの後注を名前で書いた、引き継ぎメモの閉鎖の行にラベルの書き分けの後注と 16:40 の条文の逐語（コミット c7f2796）と会話の特定、辞書 §20 の F_p の後注を数値の範囲に合わせた、インスタンスの数の範囲、「インスタンスなので」。
+   - 辞書 §22（Part 263 の名前の行）を新設。
+   - ノート §7（収束アラームの報告）を記入。
+-  - この台帳：L13・L14 を閉じた項目に移し、L15 を新設。閉じた L13・L14 の記載に、I-a・I-b が挙げた範囲の漏れを書き足した。
++  - この台帳：L13・L14 を閉じた項目に移し、L15 を新設。
++  - 閉鎖の記録（2026-11-25 19:11 の後）：PAG267.lean の冒頭のラベルの行（コメントだけ）、ノート §4・§6、引き継ぎメモ、xlsx の LABEL、この台帳の扱いの行。閉じた L13・L14 の記載に、I-a・I-b が挙げた範囲の漏れを書き足した。
+ - 直していないもの：CLAUDE.md（日英）の文面（著者側の版の写し。16:40 の条文そのものと、2 つの規則の関係、Part 260・`InLayer` の文の断りは、著者に確かめる事項）。II-a の低 5・7・8・11・12、II-b の K と k の表記、grep の式の拡大（さらい直しはしていない）、新しい文の Part 番号の併記の一部、検証手順の行番号の表記。
+ - 自己申告（根拠にしない）：主張を強めた文はない。辞書の F_p の後注と「5 は障害」の文は、どちらも範囲を狭めた直し。
+-- 扱い：I-a・I-b に中の指摘があった（高はない）。停止規則の「もう1回だけ統合照合」は I-a・I-b で行ったので、Part 263 を閉じて L15 を次のパートの統合照合に載せるか、もう 1 回照らすかを、著者に確かめる（引き継ぎメモの確かめる事項 4）。
++- 扱い（2026-11-25 19:11 の著者の判断）：Part 263 を閉じ、L15 は次のパートの統合照合に載せる。この行の後の文は判断の前の記載。I-a・I-b に中の指摘があった（高はない）。停止規則の「もう1回だけ統合照合」は I-a・I-b で行ったので、Part 263 を閉じて L15 を次のパートの統合照合に載せるか、もう 1 回照らすかを、著者に確かめる（引き継ぎメモの確かめる事項 4）。
+ 
+ ## 閉じた項目
+```
diff --git a/records/audit268/integrated/request_IIIa.md b/records/audit268/integrated/request_IIIa.md
new file mode 100644
index 0000000..32176e2
--- /dev/null
+++ b/records/audit268/integrated/request_IIIa.md
@@ -0,0 +1,16 @@
+# 依頼文（統合照合 III-a・定型）
+
+あなたは、研究記録の文面と Lean の形式文を照らす独立の照合者です。入力は 1 つのファイル `/home/claude/ardel-projective-geometry/records/audit268/integrated/input_IIIa.md` だけです。Read で読んでください（長いので範囲を分けて読んでかまいません）。/home/claude/ の下のほかのファイルは読まないでください。計算が必要なら /tmp/indep_int268_IIIa/ の中で行ってください（パッケージのインストールはできません）。ウェブ検索は使ってかまいませんが、必須ではありません。
+
+照合の対象は、Part 264 の散文（Lean の冒頭の説明と docstring、ノート、xlsx の行、引き継ぎメモの項、着手前の文書、辞書 §23）と、独立照合の後の直し（形式文は変えていない）です。
+
+「正しいか」の判定だけを書くのではなく、次の成果物を出してください。
+
+1. 独立照合の出力（§4）の指摘ごとに、今の版で直っているか（直った／一部／直っていない／直しが誤り／直す必要なし）と、根拠になる文の引用（15 語程度まで）。
+2. 散文のうち、Lean の形式文（§2）と食い違う文、形式文より強いことを言っている文。文の引用と、根拠になる宣言名。とくに、主定理 extChi_changeLevel・extChi_torus・ketS_proj_zero_eq について、散文（冒頭の説明・ノート・xlsx）の言い方が形式文と合っているかを見てください。
+3. 盲検の問いテストの出力（§6）から引いた読みが、出力より強く書かれていないか。「Lean の外」「見込み」「読み」と書かれた文が、Lean の中の文のように読める箇所。ラベル・確信度・出所・日付の食い違い。
+4. 数値スクリプト（§11）が散文の数値の文を支えているか。
+5. 「Part n（PAGm）」の対応、宣言名・ファイル名・節の参照、件数（定理の数、行番号、照合の回数）の整合。台帳 L16 の記載が直しの範囲を漏れなく書いているか。
+6. 直すべき点を重要度順に（高・中・低・極低）、直し案つきで。
+
+確かめられなかったことは、確かめられなかったと書いてください。最終報告は日本語で、上の 1〜6 の順に並べてください。最後に、使ったツールの回数と読んだ範囲を書いてください。所要時間の目安は 15 分です。
diff --git a/records/audit268/integrated/request_IIIb.md b/records/audit268/integrated/request_IIIb.md
new file mode 100644
index 0000000..3ecac9d
--- /dev/null
+++ b/records/audit268/integrated/request_IIIb.md
@@ -0,0 +1,16 @@
+# 依頼文（統合照合 III-b・定型）
+
+あなたは、研究記録の文面を照らす独立の照合者です。入力は 1 つのファイル `/home/claude/ardel-projective-geometry/records/audit268/integrated/input_IIIb.md` だけです。Read で読んでください（長いので範囲を分けて読んでかまいません）。/home/claude/ の下のほかのファイルは読まないでください。計算が必要なら /tmp/indep_int268_IIIb/ の中で行ってください（パッケージのインストールはできません）。ウェブ検索は使ってかまいませんが、必須ではありません。
+
+照合の対象は、前の照合の後に直した文面と、その後に足した記録です（入力の冒頭の説明を参照）。差分の - の行（直す前）と + の行（直した後）を比べてください。
+
+「正しいか」の判定だけを書くのではなく、次の成果物を出してください。
+
+1. 直しの根拠（前の照合の出力・補足・著者の決定の記録）がある直しについて、直っているか（直った／一部／直っていない／直しが誤り／直す必要なし）と、根拠になる文の引用（15 語程度まで）。
+2. 直した後の文面のうち、Lean の形式文や記録と食い違う文、それより強いことを言っている文（入力の中で確かめられる範囲で）。
+3. 直しが新しい主張を足していないか。足した主張があれば、それが入力の中の記録で支えられているか。
+4. 地位・ラベル・確信度・決定者・日付・出所が、ほかの記載と食い違う文、または強められている文。著者の判断の記録が書き換えられていないか（足すのは後注の形か）。台帳の記載が、差分の範囲を漏れなく書いているか。
+5. 「Part n（PAGm）」の対応、ファイル名・節の参照、件数の整合。
+6. 直すべき点を重要度順に（高・中・低・極低）、直し案つきで。
+
+確かめられなかったことは、確かめられなかったと書いてください。最終報告は日本語で、上の 1〜6 の順に並べてください。最後に、使ったツールの回数と読んだ範囲を書いてください。所要時間の目安は 15 分です。
diff --git a/records/audit268/update_xlsx_268b.py b/records/audit268/update_xlsx_268b.py
new file mode 100644
index 0000000..4055995
--- /dev/null
+++ b/records/audit268/update_xlsx_268b.py
@@ -0,0 +1,19 @@
+"""統合照合 III-a の指摘による xlsx の直し（2026-11-25）。"""
+import openpyxl, shutil
+R = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
+wb = openpyxl.load_workbook(R); ws = wb['定理と証明']
+reps = {
+ '法 N の式をそのまま使うと原始的でない χ では両立しない。': '法 N の式をそのまま使うと原始的でない χ では両立しない場合がある（証人 1 つ）。',
+ '（法 N の式は原始的でない χ で両立しない）': '（法 N の式は原始的でない χ で両立しない場合がある。法 3 → 9 のように両立する例もある：Lean の外）',
+}
+n = 0
+for r in range(3758, 3772):
+    for c in range(1, 6):
+        v = ws.cell(r, c).value
+        if isinstance(v, str):
+            w = v
+            for a, b in reps.items():
+                if a in w and b not in w: w = w.replace(a, b)
+            if w != v: ws.cell(r, c).value = w; n += 1
+    if ws.cell(r, 2).value == 'torus_eqPt': ws.cell(r, 5).value = '（rfl、定義どおり）'; n += 1
+wb.save(R); shutil.copy(R, '/home/claude/out/final86/lean_verification_status.xlsx'); print('cells changed', n)
diff --git a/records/p1_lift/numeric/extchi_check.log b/records/p1_lift/numeric/extchi_check.log
new file mode 100644
index 0000000..4d8bece
--- /dev/null
+++ b/records/p1_lift/numeric/extchi_check.log
@@ -0,0 +1,2 @@
+(p, c, 導手の指数, 一致) の数え上げ： {(3, 1): (1, 2), (3, 2): (5, 6), (3, 3): (17, 18), (5, 1): (3, 4), (5, 2): (19, 20), (7, 1): (5, 6), (7, 2): (41, 42)}
+「一致 ⇔ 導手 > 1」の例外： 0
diff --git a/records/p1_lift/numeric/extchi_check.py b/records/p1_lift/numeric/extchi_check.py
new file mode 100644
index 0000000..25290ab
--- /dev/null
+++ b/records/p1_lift/numeric/extchi_check.py
@@ -0,0 +1,40 @@
+"""Part 264（PAG268）の数値（2026-11-25、統合照合 III-a の指摘で追加）：奇素数冪の法 p^c で、
+chiPt χ（法 p^c の式）と extChi χ（導手 f の原始指標の式を引き戻したもの）が P¹(ℤ/p^c) の全点で一致するのは、
+導手が 1 でないとき、そのときに限るか。"""
+import cmath
+from math import gcd
+def prim_root(p):
+    for g in range(2,p):
+        if all(pow(g,(p-1)//q,p)!=1 for q in range(2,p) if (p-1)%q==0 and all(q%r for r in range(2,q))): return g
+def chars(p,c):
+    N=p**c; phi=N-N//p; g=prim_root(p)
+    if pow(g,p-1,p*p)==1: g+=p
+    log={}; x=1
+    for j in range(phi): log[x]=j; x=x*g%N
+    return N,phi,[(lambda k:(lambda a: 0 if a%p==0 else cmath.exp(2j*cmath.pi*k*log[a%N]/phi)))(k) for k in range(phi)]
+def conductor(chi,p,c):
+    for j in range(0,c+1):
+        f=p**j
+        if all(abs(chi(a)-chi(b))<1e-9 for a in range(p**c) for b in range(p**c) if a%p and b%p and (a-b)%f==0): return j
+def P1(N):
+    us=[u for u in range(N) if gcd(u,N)==1]; pts=set()
+    for a in range(N):
+        for b in range(N):
+            if gcd(gcd(a,b),N)==1: pts.add(min(((u*a)%N,(u*b)%N) for u in us))
+    return pts
+bad=0; rows=[]
+for p,c in [(3,1),(3,2),(3,3),(5,1),(5,2),(7,1),(7,2)]:
+    N,phi,X=chars(p,c)
+    for k,chi in enumerate(X):
+        j=conductor(chi,p,c); f=p**j
+        def prim(a): return 1 if f==1 else chi(a if a%p==0 else next(x for x in range(a%f,N,f) if x%p))
+        eq=True
+        for (a,b) in P1(N):
+            v1=chi(a)*chi(b).conjugate() if chi(b)!=0 else 0
+            v2=prim(a)*(prim(b).conjugate() if isinstance(prim(b),complex) else prim(b)) if f>1 else 1
+            if f>1 and (a%p==0 or b%p==0): v2=0
+            if abs(v1-v2)>1e-9: eq=False
+        rows.append((p,c,j,eq))
+        if eq != (j>=1): bad+=1
+print("(p, c, 導手の指数, 一致) の数え上げ：", {(p,c):(sum(1 for r in rows if r[:2]==(p,c) and r[3]), sum(1 for r in rows if r[:2]==(p,c))) for (p,c,_,_) in rows})
+print("「一致 ⇔ 導手 > 1」の例外：", bad)
diff --git a/records/p1_lift/numeric/retraction_check.log b/records/p1_lift/numeric/retraction_check.log
new file mode 100644
index 0000000..bc96c2a
--- /dev/null
+++ b/records/p1_lift/numeric/retraction_check.log
@@ -0,0 +1,2 @@
+compat failures: 0
+all checks passed
diff --git a/records/p1_lift/numeric/retraction_check.py b/records/p1_lift/numeric/retraction_check.py
index 5860c6a..958a2c6 100644
--- a/records/p1_lift/numeric/retraction_check.py
+++ b/records/p1_lift/numeric/retraction_check.py
@@ -42,4 +42,4 @@ for M in range(1,61):
             if M%N: continue
             if N>1 and rho(a%N,b%N,N)!=r%N: bad+=1
 print("compat failures:",bad)
-print("all checks passed")
+print("all checks passed" if bad==0 else "FAILED")  # 統合照合 III-a の指摘で、無条件の表示を直した
diff --git a/records/p1_tower/numeric/p1_tower_check.py b/records/p1_tower/numeric/p1_tower_check.py
index 562fbee..e5f71a9 100644
--- a/records/p1_tower/numeric/p1_tower_check.py
+++ b/records/p1_tower/numeric/p1_tower_check.py
@@ -33,7 +33,7 @@ for M in range(1,49):
         # W commute
         for (a,b) in PM:
             c=canon(a%N,b%N,N)
-            assert canon(b%N,a%N,N)==canon(c[1],c[0],N)   # red(W q) = W(red q)（統合照合 I-a の指摘で、何も確かめていなかった行を置き換えた）
+            assert canon(b%N,a%N,N)==canon(c[1],c[0],N)   # red(W q) = W(red q)（統合照合 I-a の指摘で、何も確かめていなかった行を置き換えた。法 M の canon を経由しない弱い検査：統合照合 III-b の指摘）
         # equator preimage vs upper equator: zero-extension compat?
         # f on equator(N) indicator of one point; zero-extend then pull vs pull then zero-extend
         eqN=[x for x in PN if isEq(*x,N)]
```

## §5 新しい数値スクリプトの出力
```
(p, c, 導手の指数, 一致) の数え上げ： {(3, 1): (1, 2), (3, 2): (5, 6), (3, 3): (17, 18), (5, 1): (3, 4), (5, 2): (19, 20), (7, 1): (5, 6), (7, 2): (41, 42)}
「一致 ⇔ 導手 > 1」の例外： 0
```
