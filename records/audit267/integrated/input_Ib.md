# 統合照合 I-b の入力：統合照合 II-a・II-b の後の直し（台帳 L14）（2026-11-25）
照合の対象：§3 の差分（コミット 1a1ba6f のうち、L14 の範囲のファイル）。直しの根拠は §2 の II-a・II-b の出力。直しは後注の形で足すことにしていて、記録の文は書き換えない方針。引き継ぎメモの差分の末尾の Part 263 の項は I-a の対象なので、ここでは「著者に確かめる事項」の 3 つだけを見ればよい。台帳の差分には L13 も入っているが、L13 は I-a の対象。

## §1 台帳 L14
```markdown
### L14：統合照合 II-a・II-b の後の直し（2026-11-25 夜）

- 範囲：II-a（`records/audit267/outputs/integrated_IIa_output.md`）と II-b（`integrated_IIb_output.md`）の指摘を受けた直し。どれも後注の形で足し、記録の文は書き換えていない。
  - 「R4 は低・極低だけ」の後注（R4 の 6 節の 1・2 は「低〜中」だった。16:40 の著者の決定がこれを知ったうえでのものかを著者に確かめる）：この台帳（L11 の扱い、閉じた L10 の 2 か所）、Part 262 のノート §6（R4 と閉鎖の行）、引き継ぎメモ（R4 と閉鎖の行）。
  - ラベルの確定の書き分けの後注（1・4・5 は 16:40、2・3 は 17:29 に著者が確定）：PAG266.lean の冒頭の説明（コメントだけ。作り直してエラー・警告 0）、Part 262 のノート §4、索引（1 か所）、推薦案 `pag2_p1_gluing_preregistration.md`（1 か所）、引き継ぎメモ（ラベルの行）。
  - Part 262 のノート §6 の R3 の行に、素描の文が R3 の時点のものという後注。引き継ぎメモの 17:29 の項に出所（著者の会話のメッセージ）と、理由の文は構築側の要約という後注。引き継ぎメモの閉鎖の行に、16:40 の著者のメッセージの逐語の後注。
  - 辞書：§21 のさらい方の式の穴の後注、インスタンスの数（3 → 4）、「名前ではない」→「定義ではない」、`fC` の確信度：中、§20 の設定と F_p の式の範囲の後注。CLAUDE.en.md の英語の誤り 2 つ（an algebra、Signal 4）。
  - 引き継ぎメモに、著者に確かめる事項（16:40 の決定の前提、CLAUDE.md §7 の 2 つの規則の関係、CLAUDE.md §2 の Part 260 の 3 条件・`InLayer` の文は著者側の版の写しで構築側は Lean で未確認）を書いた。
- 直していないもの：CLAUDE.md（日本語版）の文面（著者側の版の写しなので、著者に確かめる事項にした）。II-a の低・極低の一部（L9 の範囲の「含める→含めた」、R3・R4 の時刻の出所の書き足し、「1406 行」の指し方、検索語の書き足し）。
- 扱い：閉じるときの統合照合 I に載せる（II-a に「高」1 件・「中」3 件、II-b に「中」3 件があったので、停止規則の「もう1回だけ統合照合」に当たる）。
```

## §2 根拠：統合照合 II-a・II-b の出力（全文）

### II-a
# 統合照合 II-a の出力（台帳 L11 と、コミット c7f2796・600b7c5 の追記、2026-11-25）

（照合者の最終報告の全文を写した。行番号は入力 `records/audit267/integrated/input_IIa.md` の行。）

# 統合照合 IIa の報告：台帳 L11（R4 の後の直し）と、コミット c7f2796・600b7c5 の追記

**前提**
- 判定の根拠は `input_IIa.md` の 1〜539 行（全文）だけです。行番号はすべてこの入力の行です。
- CLAUDE.md は自動で文脈に入っていましたが、判定には使っていません。例外が一つだけあり、6 の中-3 で入力の外の観察としてはっきり断って触れます。
- git、xlsx、`R3_meta.txt`、`blind_output.md` など、入力の外のファイルは確かめていません。

---

### 1. R4 の「直すべき点」1〜8 の状態

| R4 の # | 状態 | 根拠 |
|---|---|---|
| 1 L10 の範囲と自己申告 | 一部 | 範囲は 330・331 行、自己申告は 332 行に入り、R4 の列挙と一致します。ただし二つ残っています。(a) R4 の小項目「閉じた L9 の範囲に…「含める」→「含めた」をはっきり書く」は差分にありません。台帳の hunk は @@ -4 と @@ -55 だけで、L9 の範囲の行は変わっていません。直さない理由も書かれていません。(b) 330 行の書き足し（「閉じた L9 の記載に、範囲の 2 行…を足した」）は、閉じたときの記載の行の中に、後から足したという標示なしで入っています。331・332 行には「照合 R4 の指摘」と標示があります。 |
| 2 ノート §2 の K | 直った | 244 行は R4 の案（121 行）とほぼ一字一致します。 |
| 3 R3 の 11 の残り 3 件 | 直った | PAG242 は 343 行で `input_IIb.md` の §L1-4、§E2 は `input_I.md`、立て直しは 262 行で `attempts.txt` を指すようになりました。どのパスも、実在するかは確かめていません。 |
| 4 12:48 | 直った（一つの読みを選んだ） | 215・277・307 行で「照合はそれより前」に揃っています。根拠は 307 行の「ef021d6 は 12:48 で、…integrated_output.md を含む」で、git は確かめていません。 |
| 5 R3 の時刻の出所 | 一部 | 出所が入ったのはノートだけです（263 行「計測は約 468 秒（…R3_meta.txt）」）。468 秒は 8 分の窓に入ります。引き継ぎメモ（222・416・503 行）と、台帳の閉じた L9（339 行）は出所なしのままです。 |
| 6 確かめていない置き場 | 直った（自己申告） | 311 行「PAG265 のノートに「確認した」はない（検索）」。検索語と範囲は書かれていません。 |
| 7 1406 行の後注 | 直った | 206 行「（台帳 L5・L8 の範囲）」。 |
| 8 細かい点 | 直った | (a) 括弧の引用は外さず、索引 2.4（427 行）の全文に揃えました（158・235 行）。これは別の直し方として妥当です。(b) 英語は読みが一つに絞れました。180 行「is to read the gluing as U」は 207 行の記録「U と読む」と合い、R4 の案より記録に近い書き方です。(c) 参照は「recorded in the handoff memo／引き継ぎメモの記録」と添えられました。(d)「（φ は位相）」は r の後に移りました（167 行）。 |

### 2. 形式文・記録と食い違う文、記録より強い文

- **「R4 は低・極低だけ」は R4 の出力と食い違います。** R4 の 6 節の 1（117 行）と 2（121 行）は**（低〜中）**と付けられています。それでも次の各行が「低か極低だけ」と書いています。
  - 17・480・535 行（L11 の扱い）
  - 18 行（L11 の注）
  - 318・333 行（閉じた L10）
  - 224・417・264・465 行（引き継ぎメモ・ノートの R4 の記録）
  - 466・505 行（閉鎖）

  止め方の規則の条件は「低・極低の指摘だけ」（385 行）です。閉鎖の前提の記述が、R4 の出力と合っていません。
- **「形式文・記録より強い文はなかった」は少し強い言い方です。** R4 の 3 節が「見つかりませんでした」と書いたのは形式文についてです（74 行）。記録については、概要の「決定 (4)」が記録より少し断定的だと、極低として挙げていました（81 行。「新しく強めたとは言いにくい」とも書いています）。
- **ラベルの確定の時刻と決定者が食い違っています。** c7f2796 は次の箇所すべてを「2026-11-20 16:40 の閉鎖で確定」にしました。
  - PAG266（398 行）
  - 索引（430 行）
  - 推薦案の後注（443 行）
  - ノート §4（456 行）
  - 引き継ぎメモ（411・419 行）

  ところが同じコミットの 420 行は「著者の確認待ち（残り）：…2・3 のラベルの選択」と書いています。2・3 は 17:29 に著者が確定しました（509 行）。それを反映したのはノート §6 の 522 行だけで、ほかの置き場はどれも「16:40 で確定」のままです。R2 が指摘した「ラベルの確定」の格上げと同じ型です。
- **R3 の手の論証の素描の文が R4・閉鎖の行に移っています。** R3 の素描の文が、67e1bc2 で R4 の記録の行（264 行）に、c7f2796 で閉鎖の行（466・522 行）に移りました。R3 の行（263 行）からは消えています。今の置き方では、R4 か閉鎖の時点の出来事のように読めます。
- **CLAUDE.md の中で規則どうしが食い違っています。** 385 行の同じ段落に、前からある「照合の後に直した文面…は、そのパートを閉じる前に再照合する（2026-11-13）」と、新しい「その照合の後の直しは次のパートの統合照合に載せ、そのパートは閉じてよい」が並んでいます。どちらが優先するか（例外の関係）が書かれていません。英語版の 372 行も同じです。

### 3. 直しが足した新しい主張と、その支え

- **12:48 の向き**（「照合はそれより前」）：307 行の、コミットに出力が含まれるという記述が支えです。git の記録は入力にありません。
- **「R3 は約 468 秒」**：出所は `R3_meta.txt` で、中身は入力にありません。窓（8 分）とは合います。
- **確信度の出所「盲検の照合者、blind_output の Q3」**（167・252 行）：中身は入力にありません。R4 の 2 節 (c) と同じく、確かめられません。
- **閉じた L10 の 330 行の書き足し**：差分で支えられます（L9 への書き足しは R4 の 110 行が挙げたものです）。
- **c7f2796 と 600b7c5**
  - 止め方の規則、閉鎖、17:29 の確定 3 件、2・3 のラベルの理由（509 行）を足しています。どれも著者側の記録が出所ですが、ファイルのパスや会話の参照は付いていません（511 行の「著者側の記録」も同じです）。
  - 509 行の理由の文（「「既知の直接の帰結」は文献の範囲を広く見せる…LPP…と同じ型の言い過ぎ」）が著者の言葉なのか、構築側の要約なのかは区別されていません。
- **数学の主張を強める直し**：見つかりませんでした。PAG266 の差分は冒頭のコメントだけです。

### 4. 地位・決定者・日付・判断の記録・台帳の範囲

- **判断の記録**：19:58 の元の文（496 行）は変わっていません。後注の見出しが「著者の確認待ち」から「17:29 に著者が確定」に書き換えられています（497→498 行）。後注を足す形ではなく見出しを差し替えた形ですが、判断の記録そのものは書き換えていません（極低）。
- **引用符の中の文が逐語ではありません。** 419・505 行の「「低・極低だけで、強めた文と…閉じてよい」」は、385 行の条文と一字一致しません。条文は「形式文・記録より強めた文」です。著者の言葉の引用に見えます。
- **台帳 L11 に書かれていない、67e1bc2 の直し**（台帳が自分の変更を書き漏らすのは、これで 4 回目です）
  - ノート §6 の R2 の行に `attempts.txt` を足したこと（262 行）
  - ノート §6 の R3 の行から「、次の照合の対象」を外し、素描の文を移したこと（263・264 行）
  - 閉じた L10 の「扱い」の行の書き換え（333 行）
  - `update_xlsx_266d.py` の追記と、xlsx のメモを「手で 1 回」置き換えたこと（355 行）
- **台帳に項目がない c7f2796・600b7c5 の直し**：Lean の docstring、索引、推薦案、ノート、引き継ぎメモのラベル表記、L11 自身の「扱い」と「注」の書き換えです。今回の照合の入力には入っていますが、台帳には L12 などとしての記載がありません。

### 5. Part と PAG の対応、参照、件数

- **Part と PAG の対応**：照らしたものはすべて 4 のずれで一致しました。Part 262（PAG266）、Part 252（PAG256）、Part 257（PAG261）、Part 19〜28（PAG23〜PAG32）、Part 20（PAG24）、Part 21（PAG25）、Part 24（PAG28）、Part 25（PAG29）です。
- **Part 番号が併記されていない箇所**：343 行の「PAG242」と `PAG.Part246.finrank_shellAlg_primePow`、512 行の「PAG261〜PAG265」（Part 257〜261 に当たります）。
- **「1406 行の後注」**（12 行、327 行）は、引き継ぎメモの今の行番号と合いません。差分の hunk @@ -778 によれば、その後注は 781 行目付近にあります。別の入力ファイルの行番号のようです。
- **「Part 262 の §20 の右列」**（512 行）は、Part 262 のノートの §20 とも読めます。R4 の 136 行に従えば、辞書の §20 のことだと思われます。
- **件数**：3,695 件（3,690 + 5）、final84（行 2〜3723）、メモの行が 3724 以降、宣言 5 つ（428 行）。食い違いはありません。
- **括弧と鉤括弧**：差分の + 行のすべてで対応していることを、機械的に確かめました。

### 6. 直すべき点（重要度順、直し案つき）

**高**
1. **「R4 は低・極低だけ」の訂正。** 2 節に挙げた各行（17・18・224・264・318・333・417・465・466・480・505・535 行）を、例えば次の形にします：「R4 の指摘は低〜中 2 件（台帳 L10 の範囲と自己申告、ノート §2 の K。どちらも記録の側）と、低・極低」。そのうえで、16:40 の著者の決定がこの 2 件を知ったうえでのものかを、著者に確かめる事項として記録します。判断の記録は書き換えず、後注の形にします。

**中**
2. **ラベルの確定の書き分け。** 398・411・419・430・443・456・505 行を「1・4・5 は 16:40 の閉鎖で確定、2・3 は 17:29 に著者が確定」にします。
3. **CLAUDE.md §7 の二つの規則の関係を明記する（日英）。** 止め方の文に「（2026-11-13 の『閉じる前に再照合する』の例外として）」と添えます。600b7c5 によれば、著者側でも §7 に規則を条文化しています（510 行）。リポジトリ版（構築側が 16:40 に追記）と著者側版の二重の経路になるので、著者側版が届いたら置き換えると記録します。
   - 入力の外の観察（判定には使っていません）：自動で文脈に入った CLAUDE.md には、「主張を変える直しがあれば、もう1回だけ統合照合」という一文と、「17:46 に著者が確定」という記載がありました。入力の 385 行にはどちらもありません。
4. **台帳に範囲を足す。** L11 に 4 節の漏れ 4 件を足します。c7f2796・600b7c5 の直しは、新しい項目（例：L12「閉鎖と確定の記録の追記」）として書きます。

**低**
5. 「形式文・記録より強い文はなかった」を「形式文より強い文はなし。記録より少し断定的な文 1 件（極低、新しい強めではない）」にします（224・264・417・465 行ほか）。
6. R3 の素描の文を、ノート §6 の R3 の行（263 行）に戻します。
7. R4 の 1 の残り（L9 の範囲の「含める→含めた」）を書くか、書かない理由を書きます。330 行の書き足しには「（照合 R4 の指摘で書き足し）」と標示します。
8. R3・R4 の時刻の出所を、引き継ぎメモと台帳にも書きます。R4 については、照合者の申告「約 10 分」を併記します。
9. 509・511 行の 17:29 の確定の出所（著者側のファイルか会話）を書きます。理由の文が著者の言葉か構築側の要約かも区別します。

**極低**
10. 419・505 行の鉤括弧を外すか、条文と一字一致させます。
11. 「1406 行」を節名で指す形に直します。512 行は「辞書 §20」と書き、Part 番号を併記します（PAG261〜PAG265 = Part 257〜261、PAG242 = Part 238）。
12. 311 行の検索について、検索語と範囲を書きます。

**確かめられなかったこと**
- git のコミット時刻と中身（ef021d6、768cb6b、67e1bc2、c7f2796、600b7c5）
- `R3_meta.txt`、`blind_output.md` の Q3、`attempts.txt`、`input_I.md`、`input_IIb.md`
- xlsx の実際の値、PAG265 のノート、着手前の文書の Q3 の行
- 著者側の 16:40 と 17:29 の記録の原文
- 差分の外にほかの直しがあるかどうか

### 使ったツールと読んだ範囲
- 計 6 回：Bash 2 回（行数の確認と、変更行の括弧の対応の機械チェック）、Read 4 回。ウェブは使っていません。
- 読んだ範囲：`input_IIa.md` の 1〜539 行（全文。1–120、121–250、251–400、401–539 に分けて読みました）。ほかのファイルは読んでいません。計算は `/tmp/indep_int267_IIa/` で行いました。

### II-b
# 統合照合 II-b の出力（台帳 L12、2026-11-25）

（照合者の最終報告の全文を写した。）

# 統合照合 IIb の報告（入力 `input_IIb.md`、全 311 行）

照合の対象は、4357fb4（補足 16 の作業と CLAUDE.md の写し）、e6cb086（数の訂正）、c3efc8d（17:46 の確定の写し）の 3 つのコミットと、台帳 L12、辞書 §20・§21 です。重要度「中」の指摘が 3 件あります。台帳 L12 が e6cb086 と c3efc8d の直しを書いていないこと、§20 の作用素の行の「出典・注意」の欄の書き換えが L12 の範囲の書き方から外れていること、16:40 の止め方の原文が CLAUDE.md §7 から消えたことです。Lean の形式文は入力に含まれていないので、形式文との突き合わせはどの項目でもできませんでした。

## 1. 根拠のある直しは直っているか

| 直し | 判定 | 根拠の引用 |
|---|---|---|
| e6cb086 引き継ぎメモ「定義名 26 個」→「25 個と `parFac` の行」 | **直った**。§21 の表を数えると、捩れの行以外の 19 名と捩れの 6 名で 25 名、これに `parFac` を足して行は 21。直す前の文は 26 に `parFac` を足すように読めた | 引き継ぎメモの元の文「定義名 26 個（行は 21。捩れの 6 つは 1 行）と `parFac` の行」 |
| e6cb086「文献用語なし」9 → 7（引き継ぎメモと辞書 §21） | **直った**。括弧の中に並ぶのは `lvl`、`oddCount`、`Compat`、`CompatF`、捩れの行、`primeProd`、`sqMap` の 7 行 | 同じ行の列挙（7 項目） |
| 辞書 §17 の注 | **直った**。当時の記録を消さずに「以下は当時の記録」として残し、前に文を足す後注の形になっている | 「2026-11-20 に §21 で行を足した（補足 16）。以下は当時の記録」 |
| 辞書 §20 の未記入 1 → 0 | **直った**。前の照合（統合照合 I）の指摘の経緯も残っている | 「それまでは 1 と数えていた。統合照合 I の指摘」 |
| 補足 16 の 1〜6 項（行の追加、「文献用語なし」の明記、根拠の添付、さらった範囲と日付、欠落の種類、パート番号なし） | **おおむね直った**。範囲・日付・欠落の種類の一文は §21 にある。ただし、さらい方の文と grep の式が食い違う（2 の (c)） | 補足 16「辞書の側に、さらった範囲（PAG261–PAG265）と日付を一文で記録」 |
| CLAUDE.md §2 の 4 点（日英） | **写しとしては直った**。差分は引き継ぎメモの 4 点と一致する。著者側の版と字句が同じかどうかは、その版が入力にないので確かめられない | 引き継ぎメモ「§2 の 4 点（Part 262 の追加、「単位元を保たない写像」…）」 |
| CLAUDE.md §7 の停止規則の箇条と、c3efc8d の 17:46 の確定 | **直った**（日英で同じ内容） | 引き継ぎメモ「この文で確定。CLAUDE.md（日英）の箇条に確定の時刻を書いた」 |

## 2. 形式文・記録と食い違う文、それより強い文

- **(a) 3 条件の一意性**（Part 260（PAG264）、CLAUDE.md §2）：前の版は「(a)(b) による一意性」でした。直した後は「3 条件すべてが効く（補足 15 の所見どおり）」です。補足 15 も Lean の文も入力にないので、確かめられませんでした。「すべてが効く」は、各条件を外すと一意性が崩れる反例があるという意味になり、主張としては強い文です。
- **(b) `InLayer`**：「同じ概念」から「`InLayer` が定義する関係そのもの」に直りました。直した後のほうが強い同一視です（規則 (iii) の A の水準）。出所は著者側の版の写しですが、Lean で確かめた記録は入力にありません。
- **(c) さらい方の文と grep の式**：§21 の文は「`def`・`abbrev`・`structure`・`instance`」ですが、grep の式には `inductive|class` も入っています。また、この式は `private def`・`protected def`・同じ行に属性がつく宣言・`irreducible_def` を拾いません。完全性の確認に使う式としては穴があります。
- **(d) インスタンスの数**：§21 は「インスタンス（`lvl_neZero`、`NeZero (primeProd S)`、`DirectedSystem` の 3 つ）」と書いています。しかし表では `sqMap`（PAG263）と `cornerSys`（PAG265）の両方の行が「`DirectedSystem` のインスタンスを含む」となっており、少なくとも 4 つあることになります。また、`lvl_neZero` には名前があるので、「名前ではないので」という理由づけも合いません。
- **(e) §20 の畳み込みの式**：F_p の式「χ₁ ⋆ χ₂ = J·χ₁χ₂（χ₁χ₂ が自明でないとき）」と「北のチャートの係数は conj(J)」は、/tmp で数値で確かめました（p = 3, 5, 7, 11 で不一致 0）。ℤ/p^k では、指標をすべて原始的に限ると不一致 0 でした（9, 25, 27, 49）が、限らないと不一致が出ます（法 9 で 270 個中 8 個）。行は「ℤ/p^k での形は Lean の文で、文献では確かめていない」と書いているので、行の文としては誤りではありません。ただし、F_p の式をそのまま ℤ/p^k に読み移さないよう注意が要ります。
- **(f) §20 の行の設定**：「P¹(ℤ/p^K) の 2 チャート」という設定の記述が文献の欄から消えました。また、`equator_intertwine` は Part 20（PAG24）、書き換えの元は Part 21（PAG25）・Part 25（PAG29）と、同じ行で Part が別々に書かれています。これが誤りかどうかは、Lean がないので確かめられません。K と k の表記の揺れもあります。

## 3. 直しが足した新しい主張

- **§21 の文献の言葉**：根拠はすべて検索結果の抜粋、要約、または「定義の読み」で、そう明記されています。文献の本文を開いていないことも書かれています。強めた文はありません。
- **`canon`**：「`shellLift` との一致は見込みで、Lean では確かめていない」と留保がついており、台帳 L12 の自己申告とも一致します。
- **`fC`**：「hyper-duality にあたる。定義の全条件との照合は未了」と書かれています。CLAUDE.md §3 にある「確信度：中」の付記がないので、地位が少し強く読めます（低）。
- **CLAUDE.md §2 の新しい主張**：上の 2 の (a)(b) が、根拠を入力の中で確かめられない主張です。
- **§7 の箇条の「主張を変える直しがあれば、もう1回だけ統合照合」**：この一文は 16:40 の止め方の文にはない新しい規則です。根拠は 17:46 の著者の確定（c3efc8d）と、§2 の補足 8 の規約（「変える直しはもう1回の統合照合を条件とする」）で、どちらも入力の中にあります。ただし、4357fb4 の時点では確定の前なのに「2026-11-20 著者の決定」と書かれていました。c3efc8d で時刻が付いて解消しています。

## 4. 地位・日付・出所と台帳

- **16:40 の止め方の文【中】**：16:40 の止め方の文は、「上の箇条による」という参照の文に置き換えられ、CLAUDE.md §7 から原文が消えました。食い違いが 2 点あります。
  - 原文の条件「形式文・記録より強めた文」と、新しい箇条の「主張を強める文の追加」は同じ意味ではありません。
  - 台帳の L11 は「2026-11-20 16:40 の著者の決定（止め方の規則、CLAUDE.md §7）」を参照しているのに、§7 にはもう 16:40 の原文がありません。

  これは「判断の記録は書き換えず、後注として足す」の規則に抵触するおそれがあります。
- **確定の時刻の書き方（低）**：c3efc8d は確定の時刻を箇条の見出しの括弧の中に書き足しました。後注の形ではありませんが、元の文は消していません。
- **台帳 L12 の漏れ【中】**：
  - L12 は 4357fb4 の時点の記載のままで、e6cb086（26→25、9→7）と c3efc8d（CLAUDE.md 日英の確定の時刻と、引き継ぎメモの項）が載っていません。「台帳が自分の変更を書き漏らす」と同じ型です。
  - §20 の行で書き換わったのは右列だけではなく、「出典・注意」の欄の全面的な書き換えと、P¹(ℤ/p^K) の削除も含みます。L12 の範囲の「右列」という書き方では、これを含むかどうかがはっきりしません。
  - 新しいファイル `files/handoff-to-builder-20261119-supplement16.md` は L12 の範囲にありません（著者の文の添付なので、直しではないと読むことはできます）。
- **ラベル・確信度**：`parFac` の行の「確信度は 2026-11-19 の著者の判断で高、Lean の外」は、§20 や CLAUDE.md §1 の記述と食い違いません。

## 5. Part と PAG の対応、参照、件数

- **Part と PAG の対応**：Part 257〜261 ＝ PAG261〜265、Part 262 ＝ PAG266、Part 20/21/25 ＝ PAG24/25/29、Part 228 ＝ PAG232 で、4 ずれは整合しています。
- **`parFac` の所属**：§21 は「Part 252（PAG256）」としています。入力の中では辞書の記載しかなく、確かめられませんでした。参考までに、入力の外で私の文脈に入っていたプロジェクトの指示書（CLAUDE.md §1）の記載 `PAG.Part256.parFac`、「Part 252（PAG256）」とは一致します。
- **ファイル番号の併記漏れ（極低）**：新しい文で「Part n（PAGm）」の形になっていない箇所があります。`shellLift` の行の「Part 228 の」、`cross`・`canon`・`Compat` の行、捩れの行の「Part 257 / 258 / 259 の」です。
- **件数**：§2 の「兆候4は Part 249〜262 で14パート連続」は整合しています。Part 262 の 5 定理も、§20 の 5 つの名前と一致します。「3,695 件」「final84（3,722 項目）」は入力の中にほかの数え方がなく、確かめられません。
- **英語版（極低）**：「Signal 4」と「Sign 4」の揺れと、「is a algebra homomorphism」の文法の誤りがあります。

## 6. 直すべき点（重要度順）

**中**
1. 台帳 L12 に e6cb086 と c3efc8d の直しを足すか、L13 として起こす。範囲には「§20 の行の出典・注意の欄の書き換えと、P¹(ℤ/p^K) の削除」を明記する。
2. CLAUDE.md §7 の段落に、16:40 の止め方の原文を後注として残す。例：「2026-11-20 16:40 の原文：…（形式文・記録より強めた文…）。17:36 の著者の版の箇条に置き換え、17:46 に一文を確定」。あわせて、L11 が参照する先を直す。
3. Part 260 の「3 条件すべてが効く」と、`InLayer` の「関係そのもの」について、根拠（補足 15、Lean の宣言名）を一文添える。または「著者側の版の写し、構築側では Lean で未確認」と断る。

**低**
4. §21 のさらい方の文を grep の式に合わせる（`inductive`・`class` を足す）。完全性の確認のために、`private`・`protected`・属性のついた宣言も拾う式に広げる。
5. インスタンスの数を「4 つ（`DirectedSystem` が 2 つ：`sqMap`・`cornerSys`）」に直し、「名前ではないので」を「定義ではないので」にする。
6. §20 の行の文献の欄に設定「P¹(ℤ/p^K)」を戻し、K と k の表記を揃える。F_p の式は、ℤ/p^k では指標が原始的な場合に限って成り立つことを注記する（数値の範囲では、原始的なら一致、そうでなければ不一致があった）。
7. `fC` の行に「確信度：中」（§3 と同じ）を添える。

**極低**
8. 新しい文の Part に PAG の番号を併記する。英語版の「Sign 4」を「Signal 4」に、「a algebra」を「an algebra」に直す。

---

**使ったツールと読んだ範囲**：Read 6 回（うち 1 回はサイズ超過のエラー）で入力の 1〜311 行をすべて読みました。Bash 3 回（行数の確認と /tmp/indep_int267_IIb/ の作成、ヤコビ和の畳み込みの数値確認 2 回）です。ウェブ検索は使っていません。入力以外のファイルは読んでいません。ただし `parFac` の照合では、私の文脈にあらかじめ入っていたプロジェクトの指示書を参考として見ました（5 で断ったとおりです）。

## §3 コミット 1a1ba6f の、L14 の範囲のファイルの差分
```diff
diff --git a/CLAUDE.en.md b/CLAUDE.en.md
index f13c5a8..9bb5d6a 100644
--- a/CLAUDE.en.md
+++ b/CLAUDE.en.md
@@ -31,7 +31,7 @@ The purpose of this procedure is not to avoid mapping to existing mathematics. T
 ## 2. Structure of the project and current position
 
 - Monograph layer (1.0): an operator system on the idele class group $C_{\mathbb Q}$ ($D$, $T_p$, $W$, dihedral relations). The central problem P1 is the compatibility classification of the boundary conditions $U$ of self-adjoint extensions (Theorem 2.6). Axiom A1 is a restatement of the value at $\lambda=0$ of the gluing of Tate's $\gamma$-factors, and is **still treated as an axiom**. Do not write "derived".
-- PAG 2.0 (finite level): Lean formalization. Completed up to design Part 256 = PAG260.lean (2026-11-13. Part 255 is the dense/discrete dichotomy for the image of the subgroup generated by finitely many primes and the choice of topology; Part 256 = candidate M1 is the factorization of Gauss sums and root numbers for coprime moduli and the law of the eigenvalues of the gluing $U$. All known facts, no new candidates. The registration of the premise of direction β (the inductive system of $A_N$), pre-registered by the author side, remained open because its text had not reached the construction side, but on 2026-11-14 it was transmitted by transcribing it in full in Supplement 4). Parts 252, 253 and 254 were carried out not as new Parts but as small notes of the short-term layer (Part 252: Lean formalization of the claim $U = JH_N$. Part 253 = candidate K1: linearization of the operator $T$ and unitarity on $V_{\mathrm{prim}}$. Part 254: the two remaining questions of Part 252 — the orthogonal direct sum decomposition by conductor, and the uniqueness of the family $U_N$ by pullback compatibility and its assembly into the inductive limit $U_\infty$. All labeled [re-derived], no new candidates. $U_N$ is an operator into which the phase of A1 is put as a definition; A1 is not derived and remains a postulate). At the end of Part 256, the xlsx has 3,552 items. The three start conditions of Part 257 were all resolved on 2026-11-14 (handoff Supplement 4): the re-check of Parts 252–256 was completed, and there were no false, vacuous or different statements and no new candidates in the formal statements (all discrepancies were on the wording side, due to the post-check corrections not having been put into the Lean docstrings and opening explanations. As remaining items, the fact that reverse translation A of the 33 statements S18–S50 of Part 254 had not been carried out in any round, and the collation of the record-only corrections after B4 (record §9), are attached as closing conditions of Part 257). Since the text of the direction β registration had not reached the construction side, it was transmitted by full transcription in Supplement 4 (collating it with the result of Part 255 and stating its fate is the job of the construction side's next report). The "08:41 definition" had been sent on the construction side but its original text did not remain on the author side, so it was closed as a start condition (collation with the wording of §1 is remaining work on the author side). For Part 257, it had been decided under the delegation that, if the collation of the registration confirmed that the premise question was unanswered, the premise of β would be asked in the three stages of registration §6 (blind question test + literature check → numerics → Lean); in fact, however, on 2026-11-14 it was closed as candidate P1 (factorization of Gauss sums and root numbers for sequences of coprime moduli, PAG261, 25 theorems), and the collation with the β registration remained undone. Parts 255, 256 and 257 were three Parts in a row in which a question different from the one decided and registered was closed, and the remaining items made closing conditions of Part 257 in Supplement 4 §1 (reverse translation A of S18–S50, collation of record §9, the duplicate-annotation round) also did not appear in the report. The corrections for checker B's 14 wording findings were closed without being checked (disclosed by the construction side). On the other hand, the mechanical duplicate check before closing (new rule) worked as designed for the first time, removing before closing two declarations with identical statements and one lemma with the same statement as Mathlib. Signal 4 reached nine Parts in a row, and under the author's policy (departure from convergence) it was decided not to start Part 258 and to make a direction audit the next task (Supplement 6: β collation, full inventory of unchecked remaining items, audit of the replacement of questions, residue assessment of the next direction). The three files of Part 257 said to have been sent did not reach the author side. Later, at 21:45 the same day, the construction side received the full text of the registration and completed the collation, and start condition 2 was closed (record `pag2_beta_registration_check.md`; the full text also reached the author side): Part 255 was not a β Part (the author chose L1 at 08:38 in a construction-side session), and none of stages 1–3 of the β question had been tried. The start of Part 257 was also due to the author's own judgment at 20:59 on 2026-11-14 (start while keeping condition 2 on hold; this replaced the earlier judgment the same day, "proceed with the audit, wait on Part 257"), and candidate P1 was also chosen by the author. That is, the choice of questions for Parts 255–257 was the author's choice in construction-side sessions, and the double route with the author side's handoffs and registrations was the cause of the discrepancy (the wording of Supplement 6 §2 (a) was corrected in Supplement 7). The handoff memo `PAG2_handoff_part257.md` has been saved on the author side, and the original text of the 08:41 definition was in it (transcribed into §1). β remains open with a split: for coprime steps ($N$ and $M/N$ coprime), the answer is expected to be nearly available through Part 228 (PAG232) `shellAlgTensorEquiv` and `leftHom` (condition 1 is satisfied; conditions 2 and 3 are expected by hand calculation but unconfirmed; confidence: medium), and the statement in registration §2 that "the direct product theorem does not answer this question" is corrected as an overstatement for the coprime case. The residue is the prime-power steps $p^e \to p^{e+1}$ (e.g. $(2,4), (2,8), (3,9)$), for which no corresponding declaration has been found in the chain. The duplicate audit was completed up to F2 (second round of corrections: 22 fixed, 2 partially, 16 new findings, no change to formal statements. The corrections after F2 are record-only and unchecked — added to the remaining items). Part 258 (PAG262, closed 2026-11-15) decided the premise of direction β in the registration's reading (unital algebra homomorphism, compatibility with pullback, the strong reading of not mixing shells): when $N \mid M$, such a map exists if and only if $\gcd(N, M/N) = 1$ (`exists_compatible_hom_iff`, 23 theorems, sorry 0). The existence side is the tensor product (known), and the non-existence side is candidate 3 of §3. As a reading, the path of setting up β as the inductive limit of these maps is closed, because a cofinal system in the divisibility order always contains steps that raise an exponent (weak readings, maps that do not preserve the unit and other compatibility conditions are outside the answer. A system of coprime steps only is a separate matter). The four closing conditions of Supplement 7 (reverse translation A of S18–S50, record §9, the corrections after F2, the corrections to Part 257) were all closed after being checked (F3). The remaining unchecked tail consists of two items, the record-only corrections after F3 and the wording corrections after checker B of Part 258 (including rephrasings concerning the scope of claims), and together with the stop convention of Supplement 8 (after an integrated check, only corrections that do not change claims are allowed; corrections that change claims are conditional on one more integrated check) they were made the object of the next integrated check. Signal 4 was ten Parts in a row for Parts 249–258. However, Part 258 is a complete answer in both directions to a pre-registered question with residue, and "judging the premise" actually changed the direction (paths (1)–(3) of β were closed, and the remaining question moved to the side of reformulation). The total number of theorems and lemmas in the chain is 3,573. Part 259 had not been started, and next the direction round within the scope of Supplement 8 (integrated check of the tail, residue assessment of the reformulations R1–R3 of β, handling of the literature check for γ) was to be carried out and one recommendation for Part 259 given. After that, on 2026-11-15 the author settled the purpose as "making a new geometry", and the main line moved to the foundational document (writing up the definitional layer as one document) (Supplement 9; the outline is `founding-document-outline-20261115.md`). Following the assessment of R1 (maps of coprime steps are not unique under (i)(ii), and for even moduli there is a twist by conjugation with $\chi(x) = (-1)^x$; adding (iii) Fourier compatibility makes it unique as `shellLift`, and the inductive system has the restricted tensor product as its limit over directed subsystems), Part 259 (PAG263, closed 2026-11-15, 67 theorems) was carried out as a Part filling a gap in Chapter 5: a map satisfying (i)(ii)(iii) exists exactly once if and only if $\gcd(N, M/N) = 1$ (`existsUnique_compatF_iff`). Without (iii), for $a = 2$ there is a twisted map `twLift` and the map is not unique (uniqueness in the odd case is numerical only). The order of the index (= the classical unitary divisors, E. Cohen 1960; in the chain it was exactly the relation defined by `InLayer` of Part 216) is not directed; on the square-free subsystem it forms an inductive system and embeds injectively into the $\mathbb{C}$-module limit `sqLim` (the algebra structure and the isomorphism with the restricted tensor product are outside Lean). The labels were fixed as: the properties of the order [known]; the uniqueness, non-uniqueness and inductive system [re-derived (small)] (Supplement 11). The whole chain has 3,640 items, and the xlsx is final80 (3,668 items). The integrated check of the tail, made a closing condition in Supplement 10, was not included in the report of Part 259, and in Supplement 11 it was decided to carry it out once as an independent deliverable and empty the tail ledger. The literature check for γ was split off as work on the author side. Signal 4 is eleven Parts in a row, but Part 259 has changed position as a Part serving a chapter of the foundational document. The remaining pre-registered candidates K2–K4 have residue that is only computation or empty, and are kept as stock in the short-term layer. On 2026-11-19, after the builder-accessible part of the γ literature check (5 searches; no description linking finite-level Bost–Connes with T(0) was found; confidence: low–medium), the author adopted at 09:37 the recommendation for the restated question (`notes/pag2_gamma_corner_preregistration.md`), carried out as Part 260 (PAG264, a small note in the short-term layer, 40 theorems): for N ∣ M, φ(S) = (N/M)·π^* ∘ S ∘ π_* (read as ι S ι^†) is a algebra homomorphism, not preserving the unit, sending A_N into A_M (regardless of gcd(N, M/N); φ(1) ≠ 1 when N < M), with φ(E_s) = E_{(M/N)s}, φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s, compatibility with pullback, uniqueness under three conditions ((a) compatibility with pullback, (b) the value of φ(1), (c) preserving products; as found in Supplement 15, all three are needed), and the composition and identity laws (the two laws of an inductive system over the divisibility order on positive integers). The D side does not land in the span of the shells (outside the strong reading of Part 258; witness (2,4), in general numerically). Outside Lean: packaging as a `DirectedSystem` and the limit, the image being the whole corner (expected to follow from triple regularity), agreement with the Bost–Connes ρ on the group-ring side (numerical). Labels: the E side is [known] (operator form of the corner by the idempotent of a quotient scheme), the rest [re-derivation (small)]; no new candidate (the control group was tried only for the case corresponding to steps of ℤ/p^e). The reservation in chapter 5 "it does not become the algebra version" is reread as a statement about unital maps (index 5.5). The checks were an independent check, a recheck and an integrated check; the tail ledger is empty. The whole chain has 3,680 theorems/lemmas; the xlsx is final82 (rows 2–3708). In the afternoon of the same day, the remainder of R-d of the recommendation was carried out as Part 261 (PAG265, short-term layer, 10 theorems): over the divisibility order on positive integers (`Lvl` of Part 254) the corner maps form a `DirectedSystem`, and the limit `CornerLim` via Mathlib's general `DirectLimit` carries a non-unital ring structure and ℂ-scalar multiplication. Each stage injects, and the limit has local units (a common idempotent for every finite set) but no left identity. The local-unit statements are general facts true for any direct limit whose stages are unital and whose transition maps preserve multiplication; only the absence of a left identity carries the non-unital content (its proof is expected not to need prime-power steps, by hand). Label [re-derivation (small)], no new candidate, the tail ledger is empty. The whole chain has 3,690 theorems/lemmas; the xlsx is final83 (rows 2–3718). Part 262 (PAG266, closed 2026-11-20, 5 theorems, sorry 0, warnings 0) was carried out as a Part serving the material for "projection" (Chapters 1–2): for pairs of primitive characters, the equatorial coefficient is written with 𝔀 (rootNum) — the signed form, the squared form, the two-chart version and the projective-line version (5 theorems together with the Gauss-sum form). Labels: the Gauss-sum form is [known], the other four are [re-derived (small)]; no new candidate. The attribution made before starting, "the signed form is equation (10) of Long–Pigno–Pinner", was wrong (that equation is the unsigned ratio; no literature writing the signed form was found). The caveat of index 2.4 (no Lean statement links JH to the models of P¹) is not filled by Part 262 — what Lean links is only the value of 𝔀 and the coefficient on P¹. The whole chain has 3,695 items; the xlsx is final84 (3,722 items). In the ledger L1–L10 are closed, and L11 (small fixes after R4) goes on the integrated check of the next Part. Sign 4 has continued for 14 Parts (Parts 249–262). In the dictionary, Part 262 added one row with an empty right column, and 6 or more names of Parts 257–259 have no row at all; together they exceed the threshold of 5, so the next step is dictionary work, not a new Part (Supplement 16). With Part 248 the classification of generators was completed, and from Part 249 the work moved to the original path (B-3: the finite-level idele class group $C_{\mathbb Q}/U_N$). Part 250 is the formulation of resolution and emergence (proposals 1 + 2 adopted by the author on 2026-11-11: put the foundation on the group of positive rationals and look at it through the connectivity of ε-chains, chainIn). Honest summary of the result: what could be shown is that "the foundation sits inside ℝ as a dense subset that is totally disconnected but connected by chains at every scale" (the logarithmic-coordinate version of a textbook example; no new candidate). "When the resolution is lowered, the line emerges" has not been shown — taking a quotient collapses it to one point, ℝ appears from the completion (the ε → 0 side), and ℝ is used in the definition from the start. Concerning the operation of "lowering the resolution / emergence", on 2026-11-12 the author chose candidate 3 (looking at all places coarsely at once), but blind identification showed that for finite S it stays a "shadow of the finite places" in which the omitted primes are invisible, and the author decided to proceed from the projective-limit side of Part 249. Part 251 is its implementation: in the group of compatible systems unitSys (a concrete model of $\varprojlim (\mathbb{Z}/N)^\times$) × ℝ, it showed the density of the subgroup generated by the prime classes $\kappa_p$ (the level-N component is the inverse of $w_p(N) = 1 + p^{N!}(p-1)$; for $p \nmid N$ it is $p^{-1}$, and at levels that are powers of $p$ it is 1) (+ uniqueness primeSys_unique). Re-derivation of the known, no new candidate. Not put into Lean: unitSys ≅ Ẑ^×, the universality, compactness and topological-group property of the limit, and the structure theorem $C_{\mathbb Q} \cong \widehat{\mathbb Z}^\times \times \mathbb{R}_{>0}$ ("dense in the idele class group" is a reading under this identification). Signal 4 (only combinations of elementary components) reached nine Parts in a row for Parts 249–257 (Parts 252, 253 and 254 were chosen knowing they were small notes). The inventory audit of remaining questions was completed by the construction side on 2026-11-12 (`pag2_audit_after_part251.md`; the author side's draft is `remaining-questions-inventory.md`): the restatement test over the whole period (Parts 155–251) succeeded in every period, and the breakdown of the 14 remaining questions is: known theorems or their consequences 10 (of which 4 are expectations from knowledge, not searched), the author's judgment comes first 2 (the operation of "lowering the resolution", the reading of the "overlap" at the infinite place), still a new candidate 1 (classification of generators; not checked against MathSciNet or zbMATH), still an axiom 1 (A1). The conclusion was that no question that is not a re-derivation of the known remains on the formalization side. Correspondences found in this search: on the limit side of Theorem 2.6, Burnol (an operator commuting with translations is a multiplication operator even if it is a closed operator); for unitSys, the ZHat of the FLT project (an explicit definition of Ẑ; precedent for the unit-group version unconfirmed); for the finite-level Bost–Connes, the original BC system. After that, the construction side carried out a re-audit with two agents not given the context (a blind one not shown the judgments = web search only, and a critique of the judgments = no tools), and weakened all three conclusions (audit record §8): being restatable shows only that "no new concepts were needed" (it does not show that there is no new content); only 4 of the 14 items were checked in the literature; "no questions remain" becomes "none has been found within the range checked" (confidence: medium or lower). The classification of generators does not contradict candidate 1 of §3, but its scope narrowed (what remains are items 66 and 67–69; a computation "at the level of a small note" that nobody has written). Rewriting §3 will be done after the author's approval. The construction side has proposed introducing pre-registration (writing, before the next Part, the known correspondences and the conditions for statements that are not re-derivations). The author side's answers to the matters for judgment have been compiled in the handoff to the construction side: A1 = a postulate of the interpretive layer (its content is Tate's theorem); the space of U in Theorem 2.6 = functions on $C_{\mathbb Q}$ (the side of the regular representation, with the reservation of the Λ-cutoff); the control-group test is adopted (codified in §7). The strategy (`strategy-nonconvergence.md`) was adopted by the author on 2026-11-12, including the rule changes; pre-registration was codified in §4 as "selection of questions by residue", and the blind question test in §7. On 2026-11-12 the author indicated the policy "proceed toward emergence", decided to review direction α (a ladder of quotients over the limit) without making it the main line in either form (a) or (b), and decided the reading of the "overlap" at the infinite place as "a twisted gluing (boundary unitary $U$)" (§1). Material for judging directions and the progress of the study are in `emergence-next-directions.md`, and the draft pre-registration of the first consequence of δ is in `preregistration-delta-first-consequence.md`.
+- PAG 2.0 (finite level): Lean formalization. Completed up to design Part 256 = PAG260.lean (2026-11-13. Part 255 is the dense/discrete dichotomy for the image of the subgroup generated by finitely many primes and the choice of topology; Part 256 = candidate M1 is the factorization of Gauss sums and root numbers for coprime moduli and the law of the eigenvalues of the gluing $U$. All known facts, no new candidates. The registration of the premise of direction β (the inductive system of $A_N$), pre-registered by the author side, remained open because its text had not reached the construction side, but on 2026-11-14 it was transmitted by transcribing it in full in Supplement 4). Parts 252, 253 and 254 were carried out not as new Parts but as small notes of the short-term layer (Part 252: Lean formalization of the claim $U = JH_N$. Part 253 = candidate K1: linearization of the operator $T$ and unitarity on $V_{\mathrm{prim}}$. Part 254: the two remaining questions of Part 252 — the orthogonal direct sum decomposition by conductor, and the uniqueness of the family $U_N$ by pullback compatibility and its assembly into the inductive limit $U_\infty$. All labeled [re-derived], no new candidates. $U_N$ is an operator into which the phase of A1 is put as a definition; A1 is not derived and remains a postulate). At the end of Part 256, the xlsx has 3,552 items. The three start conditions of Part 257 were all resolved on 2026-11-14 (handoff Supplement 4): the re-check of Parts 252–256 was completed, and there were no false, vacuous or different statements and no new candidates in the formal statements (all discrepancies were on the wording side, due to the post-check corrections not having been put into the Lean docstrings and opening explanations. As remaining items, the fact that reverse translation A of the 33 statements S18–S50 of Part 254 had not been carried out in any round, and the collation of the record-only corrections after B4 (record §9), are attached as closing conditions of Part 257). Since the text of the direction β registration had not reached the construction side, it was transmitted by full transcription in Supplement 4 (collating it with the result of Part 255 and stating its fate is the job of the construction side's next report). The "08:41 definition" had been sent on the construction side but its original text did not remain on the author side, so it was closed as a start condition (collation with the wording of §1 is remaining work on the author side). For Part 257, it had been decided under the delegation that, if the collation of the registration confirmed that the premise question was unanswered, the premise of β would be asked in the three stages of registration §6 (blind question test + literature check → numerics → Lean); in fact, however, on 2026-11-14 it was closed as candidate P1 (factorization of Gauss sums and root numbers for sequences of coprime moduli, PAG261, 25 theorems), and the collation with the β registration remained undone. Parts 255, 256 and 257 were three Parts in a row in which a question different from the one decided and registered was closed, and the remaining items made closing conditions of Part 257 in Supplement 4 §1 (reverse translation A of S18–S50, collation of record §9, the duplicate-annotation round) also did not appear in the report. The corrections for checker B's 14 wording findings were closed without being checked (disclosed by the construction side). On the other hand, the mechanical duplicate check before closing (new rule) worked as designed for the first time, removing before closing two declarations with identical statements and one lemma with the same statement as Mathlib. Signal 4 reached nine Parts in a row, and under the author's policy (departure from convergence) it was decided not to start Part 258 and to make a direction audit the next task (Supplement 6: β collation, full inventory of unchecked remaining items, audit of the replacement of questions, residue assessment of the next direction). The three files of Part 257 said to have been sent did not reach the author side. Later, at 21:45 the same day, the construction side received the full text of the registration and completed the collation, and start condition 2 was closed (record `pag2_beta_registration_check.md`; the full text also reached the author side): Part 255 was not a β Part (the author chose L1 at 08:38 in a construction-side session), and none of stages 1–3 of the β question had been tried. The start of Part 257 was also due to the author's own judgment at 20:59 on 2026-11-14 (start while keeping condition 2 on hold; this replaced the earlier judgment the same day, "proceed with the audit, wait on Part 257"), and candidate P1 was also chosen by the author. That is, the choice of questions for Parts 255–257 was the author's choice in construction-side sessions, and the double route with the author side's handoffs and registrations was the cause of the discrepancy (the wording of Supplement 6 §2 (a) was corrected in Supplement 7). The handoff memo `PAG2_handoff_part257.md` has been saved on the author side, and the original text of the 08:41 definition was in it (transcribed into §1). β remains open with a split: for coprime steps ($N$ and $M/N$ coprime), the answer is expected to be nearly available through Part 228 (PAG232) `shellAlgTensorEquiv` and `leftHom` (condition 1 is satisfied; conditions 2 and 3 are expected by hand calculation but unconfirmed; confidence: medium), and the statement in registration §2 that "the direct product theorem does not answer this question" is corrected as an overstatement for the coprime case. The residue is the prime-power steps $p^e \to p^{e+1}$ (e.g. $(2,4), (2,8), (3,9)$), for which no corresponding declaration has been found in the chain. The duplicate audit was completed up to F2 (second round of corrections: 22 fixed, 2 partially, 16 new findings, no change to formal statements. The corrections after F2 are record-only and unchecked — added to the remaining items). Part 258 (PAG262, closed 2026-11-15) decided the premise of direction β in the registration's reading (unital algebra homomorphism, compatibility with pullback, the strong reading of not mixing shells): when $N \mid M$, such a map exists if and only if $\gcd(N, M/N) = 1$ (`exists_compatible_hom_iff`, 23 theorems, sorry 0). The existence side is the tensor product (known), and the non-existence side is candidate 3 of §3. As a reading, the path of setting up β as the inductive limit of these maps is closed, because a cofinal system in the divisibility order always contains steps that raise an exponent (weak readings, maps that do not preserve the unit and other compatibility conditions are outside the answer. A system of coprime steps only is a separate matter). The four closing conditions of Supplement 7 (reverse translation A of S18–S50, record §9, the corrections after F2, the corrections to Part 257) were all closed after being checked (F3). The remaining unchecked tail consists of two items, the record-only corrections after F3 and the wording corrections after checker B of Part 258 (including rephrasings concerning the scope of claims), and together with the stop convention of Supplement 8 (after an integrated check, only corrections that do not change claims are allowed; corrections that change claims are conditional on one more integrated check) they were made the object of the next integrated check. Signal 4 was ten Parts in a row for Parts 249–258. However, Part 258 is a complete answer in both directions to a pre-registered question with residue, and "judging the premise" actually changed the direction (paths (1)–(3) of β were closed, and the remaining question moved to the side of reformulation). The total number of theorems and lemmas in the chain is 3,573. Part 259 had not been started, and next the direction round within the scope of Supplement 8 (integrated check of the tail, residue assessment of the reformulations R1–R3 of β, handling of the literature check for γ) was to be carried out and one recommendation for Part 259 given. After that, on 2026-11-15 the author settled the purpose as "making a new geometry", and the main line moved to the foundational document (writing up the definitional layer as one document) (Supplement 9; the outline is `founding-document-outline-20261115.md`). Following the assessment of R1 (maps of coprime steps are not unique under (i)(ii), and for even moduli there is a twist by conjugation with $\chi(x) = (-1)^x$; adding (iii) Fourier compatibility makes it unique as `shellLift`, and the inductive system has the restricted tensor product as its limit over directed subsystems), Part 259 (PAG263, closed 2026-11-15, 67 theorems) was carried out as a Part filling a gap in Chapter 5: a map satisfying (i)(ii)(iii) exists exactly once if and only if $\gcd(N, M/N) = 1$ (`existsUnique_compatF_iff`). Without (iii), for $a = 2$ there is a twisted map `twLift` and the map is not unique (uniqueness in the odd case is numerical only). The order of the index (= the classical unitary divisors, E. Cohen 1960; in the chain it was exactly the relation defined by `InLayer` of Part 216) is not directed; on the square-free subsystem it forms an inductive system and embeds injectively into the $\mathbb{C}$-module limit `sqLim` (the algebra structure and the isomorphism with the restricted tensor product are outside Lean). The labels were fixed as: the properties of the order [known]; the uniqueness, non-uniqueness and inductive system [re-derived (small)] (Supplement 11). The whole chain has 3,640 items, and the xlsx is final80 (3,668 items). The integrated check of the tail, made a closing condition in Supplement 10, was not included in the report of Part 259, and in Supplement 11 it was decided to carry it out once as an independent deliverable and empty the tail ledger. The literature check for γ was split off as work on the author side. Signal 4 is eleven Parts in a row, but Part 259 has changed position as a Part serving a chapter of the foundational document. The remaining pre-registered candidates K2–K4 have residue that is only computation or empty, and are kept as stock in the short-term layer. On 2026-11-19, after the builder-accessible part of the γ literature check (5 searches; no description linking finite-level Bost–Connes with T(0) was found; confidence: low–medium), the author adopted at 09:37 the recommendation for the restated question (`notes/pag2_gamma_corner_preregistration.md`), carried out as Part 260 (PAG264, a small note in the short-term layer, 40 theorems): for N ∣ M, φ(S) = (N/M)·π^* ∘ S ∘ π_* (read as ι S ι^†) is an algebra homomorphism, not preserving the unit, sending A_N into A_M (regardless of gcd(N, M/N); φ(1) ≠ 1 when N < M), with φ(E_s) = E_{(M/N)s}, φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s, compatibility with pullback, uniqueness under three conditions ((a) compatibility with pullback, (b) the value of φ(1), (c) preserving products; as found in Supplement 15, all three are needed), and the composition and identity laws (the two laws of an inductive system over the divisibility order on positive integers). The D side does not land in the span of the shells (outside the strong reading of Part 258; witness (2,4), in general numerically). Outside Lean: packaging as a `DirectedSystem` and the limit, the image being the whole corner (expected to follow from triple regularity), agreement with the Bost–Connes ρ on the group-ring side (numerical). Labels: the E side is [known] (operator form of the corner by the idempotent of a quotient scheme), the rest [re-derivation (small)]; no new candidate (the control group was tried only for the case corresponding to steps of ℤ/p^e). The reservation in chapter 5 "it does not become the algebra version" is reread as a statement about unital maps (index 5.5). The checks were an independent check, a recheck and an integrated check; the tail ledger is empty. The whole chain has 3,680 theorems/lemmas; the xlsx is final82 (rows 2–3708). In the afternoon of the same day, the remainder of R-d of the recommendation was carried out as Part 261 (PAG265, short-term layer, 10 theorems): over the divisibility order on positive integers (`Lvl` of Part 254) the corner maps form a `DirectedSystem`, and the limit `CornerLim` via Mathlib's general `DirectLimit` carries a non-unital ring structure and ℂ-scalar multiplication. Each stage injects, and the limit has local units (a common idempotent for every finite set) but no left identity. The local-unit statements are general facts true for any direct limit whose stages are unital and whose transition maps preserve multiplication; only the absence of a left identity carries the non-unital content (its proof is expected not to need prime-power steps, by hand). Label [re-derivation (small)], no new candidate, the tail ledger is empty. The whole chain has 3,690 theorems/lemmas; the xlsx is final83 (rows 2–3718). Part 262 (PAG266, closed 2026-11-20, 5 theorems, sorry 0, warnings 0) was carried out as a Part serving the material for "projection" (Chapters 1–2): for pairs of primitive characters, the equatorial coefficient is written with 𝔀 (rootNum) — the signed form, the squared form, the two-chart version and the projective-line version (5 theorems together with the Gauss-sum form). Labels: the Gauss-sum form is [known], the other four are [re-derived (small)]; no new candidate. The attribution made before starting, "the signed form is equation (10) of Long–Pigno–Pinner", was wrong (that equation is the unsigned ratio; no literature writing the signed form was found). The caveat of index 2.4 (no Lean statement links JH to the models of P¹) is not filled by Part 262 — what Lean links is only the value of 𝔀 and the coefficient on P¹. The whole chain has 3,695 items; the xlsx is final84 (3,722 items). In the ledger L1–L10 are closed, and L11 (small fixes after R4) goes on the integrated check of the next Part. Signal 4 has continued for 14 Parts (Parts 249–262). In the dictionary, Part 262 added one row with an empty right column, and 6 or more names of Parts 257–259 have no row at all; together they exceed the threshold of 5, so the next step is dictionary work, not a new Part (Supplement 16). With Part 248 the classification of generators was completed, and from Part 249 the work moved to the original path (B-3: the finite-level idele class group $C_{\mathbb Q}/U_N$). Part 250 is the formulation of resolution and emergence (proposals 1 + 2 adopted by the author on 2026-11-11: put the foundation on the group of positive rationals and look at it through the connectivity of ε-chains, chainIn). Honest summary of the result: what could be shown is that "the foundation sits inside ℝ as a dense subset that is totally disconnected but connected by chains at every scale" (the logarithmic-coordinate version of a textbook example; no new candidate). "When the resolution is lowered, the line emerges" has not been shown — taking a quotient collapses it to one point, ℝ appears from the completion (the ε → 0 side), and ℝ is used in the definition from the start. Concerning the operation of "lowering the resolution / emergence", on 2026-11-12 the author chose candidate 3 (looking at all places coarsely at once), but blind identification showed that for finite S it stays a "shadow of the finite places" in which the omitted primes are invisible, and the author decided to proceed from the projective-limit side of Part 249. Part 251 is its implementation: in the group of compatible systems unitSys (a concrete model of $\varprojlim (\mathbb{Z}/N)^\times$) × ℝ, it showed the density of the subgroup generated by the prime classes $\kappa_p$ (the level-N component is the inverse of $w_p(N) = 1 + p^{N!}(p-1)$; for $p \nmid N$ it is $p^{-1}$, and at levels that are powers of $p$ it is 1) (+ uniqueness primeSys_unique). Re-derivation of the known, no new candidate. Not put into Lean: unitSys ≅ Ẑ^×, the universality, compactness and topological-group property of the limit, and the structure theorem $C_{\mathbb Q} \cong \widehat{\mathbb Z}^\times \times \mathbb{R}_{>0}$ ("dense in the idele class group" is a reading under this identification). Signal 4 (only combinations of elementary components) reached nine Parts in a row for Parts 249–257 (Parts 252, 253 and 254 were chosen knowing they were small notes). The inventory audit of remaining questions was completed by the construction side on 2026-11-12 (`pag2_audit_after_part251.md`; the author side's draft is `remaining-questions-inventory.md`): the restatement test over the whole period (Parts 155–251) succeeded in every period, and the breakdown of the 14 remaining questions is: known theorems or their consequences 10 (of which 4 are expectations from knowledge, not searched), the author's judgment comes first 2 (the operation of "lowering the resolution", the reading of the "overlap" at the infinite place), still a new candidate 1 (classification of generators; not checked against MathSciNet or zbMATH), still an axiom 1 (A1). The conclusion was that no question that is not a re-derivation of the known remains on the formalization side. Correspondences found in this search: on the limit side of Theorem 2.6, Burnol (an operator commuting with translations is a multiplication operator even if it is a closed operator); for unitSys, the ZHat of the FLT project (an explicit definition of Ẑ; precedent for the unit-group version unconfirmed); for the finite-level Bost–Connes, the original BC system. After that, the construction side carried out a re-audit with two agents not given the context (a blind one not shown the judgments = web search only, and a critique of the judgments = no tools), and weakened all three conclusions (audit record §8): being restatable shows only that "no new concepts were needed" (it does not show that there is no new content); only 4 of the 14 items were checked in the literature; "no questions remain" becomes "none has been found within the range checked" (confidence: medium or lower). The classification of generators does not contradict candidate 1 of §3, but its scope narrowed (what remains are items 66 and 67–69; a computation "at the level of a small note" that nobody has written). Rewriting §3 will be done after the author's approval. The construction side has proposed introducing pre-registration (writing, before the next Part, the known correspondences and the conditions for statements that are not re-derivations). The author side's answers to the matters for judgment have been compiled in the handoff to the construction side: A1 = a postulate of the interpretive layer (its content is Tate's theorem); the space of U in Theorem 2.6 = functions on $C_{\mathbb Q}$ (the side of the regular representation, with the reservation of the Λ-cutoff); the control-group test is adopted (codified in §7). The strategy (`strategy-nonconvergence.md`) was adopted by the author on 2026-11-12, including the rule changes; pre-registration was codified in §4 as "selection of questions by residue", and the blind question test in §7. On 2026-11-12 the author indicated the policy "proceed toward emergence", decided to review direction α (a ladder of quotients over the limit) without making it the main line in either form (a) or (b), and decided the reading of the "overlap" at the infinite place as "a twisted gluing (boundary unitary $U$)" (§1). Material for judging directions and the progress of the study are in `emergence-next-directions.md`, and the draft pre-registration of the first consequence of δ is in `preregistration-delta-first-consequence.md`.
 - Note on numbering: in the third period, the Part numbers of the design memos are 4 smaller than the Lean file numbers. For the correspondence table see `archive-catalog.md`.
 - Counts: 3,344 theorems/lemmas and 3,371 xlsx items (at the end of Part 251, by the author's audit). Do not confuse these with other ways of counting, such as the total number of declarations.
 
diff --git a/PAG266.lean b/PAG266.lean
index 6e0b117..57b83ba 100644
--- a/PAG266.lean
+++ b/PAG266.lean
@@ -33,7 +33,7 @@ n ≥ 1 で χ₁χ₂ が原始的でない組は、数値で調べた範囲で
 一般の場合は照合 R3 の照合者が手の論証の素描を示した（Lean の外、照合者の確信度：高、`records/audit266/recheck_L9/outputs/R3_output.md` の 2 節 (b)）が、構築側では確かめていないので見込みのままにする））。χ₁・χ₂・χ₁χ₂ が原始的なときの比 conj(J)/J は、関数全体の等式として Part 20（PAG24）の `PAG.Part24.equator_intertwine` にある。
 4・5 は Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換えで、絡み合いの中身はそちらにある（名前空間 `PAG.Part25` は Part 21（PAG25）を指し、Part 25（PAG29）とは別）。
 
-ラベル（2026-11-20 16:40 の閉鎖で確定）：1 は［既知］（積が原始的ならヤコビ和はガウス和の比、|τ|² = N。K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15・3.12。法 m は一般で ℤ/p^(n+1) を覆う（WebFetch の要約で確認））。
+ラベル（2026-11-20 16:40 の閉鎖で確定。後注 2026-11-25、統合照合 II-a の指摘：1・4・5 は 16:40 の閉鎖で確定、2・3 は 2026-11-20 17:29 に著者が［再導出（小さい）］で確定）：1 は［既知］（積が原始的ならヤコビ和はガウス和の比、|τ|² = N。K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15・3.12。法 m は一般で ℤ/p^(n+1) を覆う（WebFetch の要約で確認））。
 2・3 は［再導出（小さい）］（1 と `rootNum` の定義からの直接の帰結。符号 s つきの形・𝔀 による形を書いた文献は見つかっていない。Long–Pigno–Pinner（arXiv:1410.6179）の式 (10) は符号のない比で、すべて原始的なときの J = G₁G₂/G₁₂（WebFetch の要約で確認）。統合照合 I の案は「［既知］の直接の帰結」。構築側の判断で［再導出（小さい）］にした（着手前の文書の見込みでは、2・3 に当たる文を Conrad の帰結として［既知］としていた））。
 4・5 は［再導出（小さい）］。新規候補なし。
 -/
diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
index 23976b1..53547d7 100644
--- a/handoff/PAG2_handoff_part259.md
+++ b/handoff/PAG2_handoff_part259.md
@@ -1713,15 +1713,15 @@
   - Lean：定理 5 個（sorry 0、警告 0、#print axioms は標準の 3 つ）。χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は両方とも奇のときだけ −1）、2 乗の形、n + 1 ≤ K のとき赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデルと、`projFunEquiv` で射影直線の上の関数に移した形）。
   - 範囲：殻 0 と導手がちょうど p^(n+1) の指標の組だけ。p = 2 と p = 3、n = 0 では文は空。作用素の形は Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換え。`JH` と P¹ のモデルを結ぶ文ではなく、索引 2.4 の留保は残る。
   - 読み（Lean の外）：赤道のケット（殻 0）の組で χ₁・χ₂・χ₁χ₂ が原始的なとき、B_S(|0,χ₁⟩, |0,χ₂⟩) が χ₁χ₂ の成分に入ることと合わせて、B_N = U² B_S U⁻²（U は導手で計算した 𝔀 を掛ける作用素）。条件は U を有限個の候補に絞るが選ばず、A1 は導かれない。関数体の本来のルート数は一般にこの条件を満たさない（ℚ に固有の小さな観察、確信度：中）。P¹ の 0・∞ を定義の「無限小と無限大」と結ぶ読みは著者の判断が先。
-  - ラベル（2026-11-20 16:40 の閉鎖で確定）：1 が［既知］（Conrad の定理 3.15・3.12、法 m は一般。WebFetch の要約で確認）、2〜5 が［再導出（小さい）］（符号つきの形を書いた文献は見つかっていない。LPP の式 (10) は符号のない比）。新規候補なし。兆候 4 は続く。
+  - ラベル（2026-11-20 16:40 の閉鎖で確定）：1 が［既知］（Conrad の定理 3.15・3.12、法 m は一般。WebFetch の要約で確認）、2〜5 が［再導出（小さい）］（符号つきの形を書いた文献は見つかっていない。LPP の式 (10) は符号のない比）。新規候補なし。兆候 4 は続く。（後注 2026-11-25、統合照合 II-a の指摘：1・4・5 は 16:40 の閉鎖で確定、2・3 は 2026-11-20 17:29 に著者が［再導出（小さい）］で確定。）
   - 照合：内部照合（機械的 200 回で一致なし、言葉の検索で Part 21（PAG25）・Part 25（PAG29）の定理を使った）、独立照合（形式文と定義だけ）、再照合（独立照合の出力・直した後の全文・差分・定義）。再照合の後の直し（形式文は変えていない。Lean の外の新しい文（単数の点の比）と数値を含む）は尾の台帳の L6。
   - 統合照合（2026-11-20 07:43〜07:55、`records/audit266/integrated/`）：台帳 L1〜L6 と Part 262 の材料を照合者 3 人に分けて同時に照らした。形式文が偽・空虚・別物になる文の指摘はなかった。散文・記録の指摘（LPP の帰属の誤り、着手前の文書の表の取り違え、留保の向き、台帳の範囲の穴、自己申告の残り、PAG264・PAG265 の冒頭の「台帳は空」など）を直した。統合照合の後の直しと、台帳の外に見つかった未照合の直し（概要（日英）と引き継ぎメモ、153e91d→deab9f3）は、台帳の L7・L8 として次の照合の対象。
   - 件数：鎖全体の定理・補題は 3,695 件（3,690 + 5）。xlsx は final84（行 2〜3723）。
   - 再照合 R2（2026-11-20 15:15〜15:31、`records/audit266/recheck_int/`）：L7・L8 を照らした。形式文より強い文はなし。地位の格上げ（ラベルの「確定」）、留保の範囲の限定の脱落、19:58 の判断の記録の書き換えなどを直した（台帳 L9）。
   - 照合 R3（2026-11-20 15:37〜15:45、`records/audit266/recheck_L9/`）：L9 を照らした。形式文より強い文はなし。PAG265 の判断の記録の言葉、概要の標示の文、留保の範囲の限定の漏れ、ラベルの理由の文などを直した（台帳 L10）。
-  - 照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/`）：L10 を照らした。指摘は低か極低だけで、形式文・記録より強い文と判断の記録の書き換えはなかった。直した（台帳 L11）。
-  - 閉鎖（2026-11-20 16:40）：著者が止め方の規則を決めた（「低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい」、CLAUDE.md §7 に追記）。R4 はこれに当たるので Part 262 は閉じた。台帳 L11 は次のパートの統合照合に載せる。ラベルは確定（1 は［既知］、2〜5 は［再導出（小さい）］、新規候補なし）。
-  - 著者の確定（2026-11-20 17:29）：
+  - 照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/`）：L10 を照らした。指摘は低か極低だけで、形式文・記録より強い文と判断の記録の書き換えはなかった。直した（台帳 L11）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
+  - 閉鎖（2026-11-20 16:40）：著者が止め方の規則を決めた（「低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい」、CLAUDE.md §7 に追記）。R4 はこれに当たるので Part 262 は閉じた。台帳 L11 は次のパートの統合照合に載せる。ラベルは確定（1 は［既知］、2〜5 は［再導出（小さい）］、新規候補なし）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）（後注 2026-11-25：上の鉤括弧の中は、2026-11-20 16:40 の著者のメッセージの逐語：「低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい」。CLAUDE.md §7 の条文は、その後に著者側の版の箇条に置き換わり、17:46 に一文が確定した。16:40 の原文はこの後注に残す。）
+  - 著者の確定（2026-11-20 17:29）：（後注 2026-11-25、統合照合 II-a の指摘：出所は著者のこの会話のメッセージ（2026-11-20 17:29）。下の 2・3 のラベルの理由の文は、構築側の要約。）
     - 19:58 の判断の記録：元の文を残し、根拠の内訳を後注で足す形で確定（判断の記録は書き換えない原則。確認なしに書き換えて戻した経緯も含めて確定）。
     - 2・3 のラベル：構築側の［再導出（小さい）］で確定。照合者の案「［既知］の直接の帰結」は採らない（符号つきの形はその形では文献に見つかっておらず、「既知の直接の帰結」は文献の範囲を広く見せる。LPP の式 (10) の誤帰属と同じ型の言い過ぎになる）。
     - CLAUDE.md §2 は著者側で更新した：Part 262 の追加（鎖全体 3,695 件、xlsx final84、索引 2.4 の留保が埋まっていないこと）、「非単位的な写像」→「単位元を保たない写像」、「Part 216 の InLayer と同じ概念」→「InLayer が定義する関係そのもの」、Part 260 の一意性を 3 条件の形に。§7 にも止め方の規則を条文化した（著者側）。リポジトリの CLAUDE.md §2 にはまだ届いていない（2026-11-20 17:29 の時点）。
@@ -1735,3 +1735,13 @@
   - 未記入の件数：右列が空の行 0、行のない名前（PAG261〜PAG265 の定義名）0。兆候 4 は続く（新しいパートはない）。
   - この作業は照合を受けていない。止め方の規則により、台帳 L11 と一緒に次のパートの統合照合に載せる（台帳 L12）。
   - 著者の確定（2026-11-20 17:46）：停止規則の「主張を変える直しがあれば、もう1回だけ統合照合を行い、その後はこの規則で閉じる」の一文を、この文で確定。CLAUDE.md（日英）の箇条に確定の時刻を書いた。
+- **Part 263（PAG267、短期層の小さいノート、2026-11-25）：P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限、赤道への制限と赤道からの 0 延長**：
+  - 出所：基礎文書の索引の「射影」の空間の水準の問い（索引 1.4・2.4）。推薦案 `notes/pag2_p1_tower_preregistration.md` §4（盲検の指摘で改めた C1）を、2026-11-25 18:27 に著者が採用した（「進めてください」）。
+  - Lean：PAG267.lean、定理 34、sorry 0・警告 0、#print axioms は標準の 3 つ。還元の恒等・合成の法則・反転との可換・全射（M ≠ 0）、0 ≠ ∞（N ≠ 1）、引き戻しの帰納系と極限の上の対合 W_∞、赤道への制限が誘導する `resL : LimP → Lim`（Part 254 の Lim）の全射と resL ∘ W_∞ = invL ∘ resL、0 延長が引き戻しと可換 ⇔ 上の段の法の素因数がすべて下の段の法を割る（証人 (1, 2)）、0 延長は極限に降りない。ノート `notes/pag2_pag267_p1_tower.md`。
+  - ラベル（見込み、閉鎖で確定）：1〜3 は［既知］、4・5 は［再導出（小さい）］、新規候補なし。兆候 4 は続く（Part 249〜263 で 15 パート連続）。
+  - 内部照合：PAG262 の `mem_ker_iff` と PAG28 の `Wpull` を使った（言葉の検索）。機械的な照合 712 回で一致なし。`Wproj_eqPt` は PAG28 の `mk_inv_eq` と同じ内容（B）。
+  - 照合：独立照合（約 119 秒）。指摘で 4 定理を足した（台帳 L13）。同時に、台帳 L11・L12 と台帳に項目のなかった記録の追記を統合照合 II-a・II-b で照らした（L11・L12 は閉じた）。II-a に「高」1 件：R4 の指摘は「低〜中」2 件を含んでいたのに、記録は「低か極低だけ」と書いていた。直しは後注の形で入れた（台帳 L14）。L13・L14 は閉じるときの統合照合 I に載せる。
+  - 著者に確かめる事項（2026-11-25）：
+    1. 2026-11-20 16:40 の Part 262 の閉鎖の決定は、構築側の「R4 は低・極低だけ」という報告を前提にしていた可能性がある。実際の R4 の出力では、6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K。どちらも記録の側で、L11 で直した）が「低〜中」だった。この 2 件を知ったうえで閉鎖の決定を保つかどうか。
+    2. CLAUDE.md §7 の「照合の後に直した文面は、そのパートを閉じる前に再照合する（2026-11-13）」と、止め方の規則（2026-11-20）の関係（止め方の規則が前者の例外であると明記するか）。リポジトリの CLAUDE.md は著者側の版の写しなので、構築側では文面を変えていない。
+    3. CLAUDE.md §2 の Part 260 の「3 条件すべてが効く」と「`InLayer` が定義する関係そのもの」の文は著者側の版の写しで、構築側はこの写しのために Lean で確かめていない（II-b の指摘）。
diff --git a/notes/pag2_founding_material_index.md b/notes/pag2_founding_material_index.md
index ca0a7f3..769c9a2 100644
--- a/notes/pag2_founding_material_index.md
+++ b/notes/pag2_founding_material_index.md
@@ -121,7 +121,7 @@
   - `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。
   - 照合した範囲（PAG23・PAG26・PAG27・PAG256）では、`JH` と P¹ のモデルを結ぶ Lean の文はない。この留保は Part 262 の後も残る。
   - 𝔀 の値と P¹ のモデルを結ぶ Lean の文（Part 262（PAG266）、2026-11-20、短期層）：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、P¹(ℤ/p^K) の赤道のケットについて B_N = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S（2 チャートのモデル `PAG.Part266.equator_intertwine_rootNum`、射影直線 `PAG.Part266.equator_intertwine_proj_rootNum`）。係数の等式 conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))（s は両方とも奇のときだけ −1）は `PAG.Part266.conj_Jhat_eq_rootNum`、2 乗の形は `PAG.Part266.conj_Jhat_sq_eq_rootNum`、ガウス和の形は `PAG.Part266.conj_Jhat_eq_gauss`。
-    - 範囲：殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ（係数は K によらない）。p = 2（すべての n）と p = 3、n = 0 では文は空。作用素の形の 2 つは Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換えで、絡み合いの中身はそちらにある。射影直線の版は 2 チャートの版を `projFunEquiv`（Part 24（PAG28））で移したもので、2 チャートの版と同値（手の論証。Lean の文ではない）。ラベル（2026-11-20 16:40 の閉鎖で確定）は、ガウス和の形が［既知］、ほかの 4 つが［再導出（小さい）］（符号つきの形を書いた文献は見つかっていない）。
+    - 範囲：殻 0（赤道）と、導手がちょうど p^(n+1) の同じ法の指標の組だけ（係数は K によらない）。p = 2（すべての n）と p = 3、n = 0 では文は空。作用素の形の 2 つは Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換えで、絡み合いの中身はそちらにある。射影直線の版は 2 チャートの版を `projFunEquiv`（Part 24（PAG28））で移したもので、2 チャートの版と同値（手の論証。Lean の文ではない）。ラベル（2026-11-20 16:40 の閉鎖で確定）は、ガウス和の形が［既知］、ほかの 4 つが［再導出（小さい）］（符号つきの形を書いた文献は見つかっていない）。（後注 2026-11-25、統合照合 II-a の指摘：1・4・5 は 16:40 の閉鎖で確定、2・3 は 2026-11-20 17:29 に著者が［再導出（小さい）］で確定。）
     - このパートの文に `JH` は現れない。Lean で結んだのは 𝔀 の値と P¹ の赤道の係数で、上の二つの留保（`JH` は P¹ の上の作用素ではない、照合した範囲では `JH` と P¹ のモデルを結ぶ文はない）は残る。
     - 読み（Lean の外）：原始指標 χ の成分に導手で計算した 𝔀 を掛ける作用素を U とすると、B_S(|0,χ₁⟩, |0,χ₂⟩) が χ₁χ₂ の成分に入ること（Part 262 の文にはない）と合わせて、赤道のケット（殻 0）の組で χ₁・χ₂・χ₁χ₂ が原始的なとき、北の畳み込みは南の畳み込みを U² で移したもの。この条件は U を有限個の候補（少なくとも単数 u と指標ごとの符号の分がある）に絞るが選ばず、A1 は導かれない。関数体では本来のルート数が一般にこの条件を満たさない（ℚ に固有の小さな観察、確信度：中）。P¹(ℤ/N) の 0・∞ を定義の「無限小と無限大」と結ぶ読みは構築側の候補（著者の判断が先）。ノート `pag2_pag266_p1_equator_rootnum.md`。
   - 原始指標で 𝔀 がルート数であることは Lean の外。
diff --git a/notes/pag2_p1_gluing_preregistration.md b/notes/pag2_p1_gluing_preregistration.md
index 016df40..59c087e 100644
--- a/notes/pag2_p1_gluing_preregistration.md
+++ b/notes/pag2_p1_gluing_preregistration.md
@@ -81,7 +81,7 @@
     2. 2 乗を外した形：conj(Ĵ(χ1, χ2)) = (−1)^{a1a2}·𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2))（符号は χ1・χ2 がともに奇のときだけ −1）。
     3. 作用素の形：赤道のケットについて B_N(k1, k2) = (𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)))² · B_S(k1, k2)（Part 21（PAG25）の `equator_intertwine_hat` と 1 から）。これが索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める。（後注、2026-11-20：埋めない。Lean で結んだのは 𝔀 の値と P¹ の赤道の係数で、`JH` と P¹ のモデルを結ぶ文ではないので、索引 2.4 の留保は残る（Part 262 のノート §1）。留保は 2.4 にあり、1.4 ではない。）
   - Lean の外に置くもの（ノートに数値・手計算・盲検として書く）：解の集まりの記述（φ(N)·2^{|Prim|} 個、単数倍の作用と平方のファイバー）、U² による読み、関数体との違い。
-  - ラベル（見込み）：1・2 は［既知］（Conrad の定理 3.15 と |τ|² = N）、3 は［再導出（小さい）］。新規候補にはしない。兆候 4 は続く。（後注、2026-11-20：Part 262 のラベル（2026-11-20 16:40 の閉鎖で確定）は Part 262 のノート §4。ガウス和の形は［既知］、符号つきの形・2 乗の形・作用素の形は［再導出（小さい）］。符号つきの形を書いた文献は見つかっていない。）
+  - ラベル（見込み）：1・2 は［既知］（Conrad の定理 3.15 と |τ|² = N）、3 は［再導出（小さい）］。新規候補にはしない。兆候 4 は続く。（後注、2026-11-20：Part 262 のラベル（2026-11-20 16:40 の閉鎖で確定）は Part 262 のノート §4。ガウス和の形は［既知］、符号つきの形・2 乗の形・作用素の形は［再導出（小さい）］。符号つきの形を書いた文献は見つかっていない。）（後注 2026-11-25、統合照合 II-a の指摘：1・4・5 は 16:40 の閉鎖で確定、2・3 は 2026-11-20 17:29 に著者が［再導出（小さい）］で確定。）
   - 閉じるときの統合照合に、台帳の L1〜L5 を一緒に載せる（台帳を閉じる機会にする）。
 - **理由**：
   1. 基礎文書の索引に明記された留保（1.4・2.4）を、短い Lean の文で埋められる（後注、2026-11-20：埋めるのではなく、留保に関わる材料が入る。留保は 2.4 にあり、残る）。著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」の「その上で働く」に、Lean の名前で引ける文が入る（読みの地位は著者の判断のまま）。
diff --git a/notes/pag2_pag266_p1_equator_rootnum.md b/notes/pag2_pag266_p1_equator_rootnum.md
index 618a044..a5097c1 100644
--- a/notes/pag2_pag266_p1_equator_rootnum.md
+++ b/notes/pag2_pag266_p1_equator_rootnum.md
@@ -38,7 +38,7 @@
 
 ## §4 ラベル
 
-（2026-11-20 16:40 の閉鎖で確定。2・3 は統合照合 I の指摘を受けて［既知］から改めた。統合照合 I の案は「［既知］の直接の帰結」。構築側の判断で［再導出（小さい）］にした（着手前の文書の見込みでは、2・3 に当たる文を Conrad の帰結として［既知］としていた）。）
+（2026-11-20 16:40 の閉鎖で確定。2・3 は統合照合 I の指摘を受けて［既知］から改めた。統合照合 I の案は「［既知］の直接の帰結」。構築側の判断で［再導出（小さい）］にした（着手前の文書の見込みでは、2・3 に当たる文を Conrad の帰結として［既知］としていた）。）（後注 2026-11-25、統合照合 II-a の指摘：1・4・5 は 16:40 の閉鎖で確定、2・3 は 2026-11-20 17:29 に著者が［再導出（小さい）］で確定。）
 - 1：［既知］。積が原始的ならヤコビ和はガウス和の比（K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ の定理 3.15）、|τ|² = N（同 定理 3.12）。どちらも法 m は一般で ℤ/p^(n+1) を覆う（定理 3.15 は積の原始性だけを仮定する。WebFetch の要約で確認、2026-11-20）。
 - 2・3：［再導出（小さい）］。1 と `rootNum` の定義からの直接の帰結。符号 s つきの形・𝔀 による形を書いた文献は見つかっていない（根拠は盲検の手計算と Lean の文）。Long–Pigno–Pinner（arXiv:1410.6179）の式 (10) は符号のない比 J = ∏G(χᵢ)/G(∏χᵢ)（χ₁, …, χ_k とその積がすべて原始的なとき）で、出典は Zhang–Yao の補題 3（k = 2）と Zhang–Xu の補題 1（WebFetch の要約で確認、2026-11-20）。以前この版では「符号つきの形は LPP の式 (10)」と書いていたが、誤りだった（統合照合 I の指摘）。
 - 4・5：［再導出（小さい）］。既存の定理の係数の書き換え。
@@ -60,9 +60,9 @@
   - I の中くらいの指摘：留保が残るか埋まるかの書き方の食い違い（索引 2.4・xlsx・着手前の文書）、索引 1.4 の題の言葉、単数の点の比の文の範囲（J ≠ 0、Lean の外）、読みの文の前提、数値の範囲の書き広げ（N ≤ 49 → 8 つの法）、「文面のみ」の言い方、ラベルの地位の書き分け。
   - 統合照合の後の直しは、台帳の L7 として次の照合（再照合）の入力に含めた。
 - 再照合 R2（2026-11-20 15:15〜15:31、`records/audit266/recheck_int/`。1 回目の照合者は朝に利用の上限で止まったので、同じ入力で立て直した。記録 `records/audit266/recheck_int/attempts.txt`）：L7 と L8（台帳の外に見つかった直し）を照らした。形式文より強い文は見つからなかった。指摘の主なもの：ラベルの「統合照合の後に確定」は地位の格上げ（統合照合はラベルを確定していない）、索引 2.4 の留保から「照合した範囲では」が落ちた、引き継ぎメモで 19:58 の著者の判断の記録を著者の確認なしに書き換えた、引き継ぎメモの古い自己申告に注がない、n ≥ 1 の J = 0 を一般形で書いた。直した（台帳 L9）。
-- 照合 R3（2026-11-20 15:37〜15:45、`records/audit266/recheck_L9/`）：L9 を照らした。形式文より強い文はなし。指摘の主なもの：PAG265 で 19:58 の判断を「確認した」と強め、出所を誤って標示した、概要の標示の文（「決めたのは…だけ」）が事実と違う、留保の範囲の限定の漏れ（ノート §1・索引・xlsx）、ラベルの理由の文の慣行の主張に反例がある。直した（台帳 L10）。R3 の時刻は、起動（コミット 768cb6b の後）から通知まで。計測は約 468 秒（`records/audit266/recheck_L9/outputs/R3_meta.txt`。照合者の目安の申告は約 10〜12 分）。
-- 照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/`）：L10 を照らした。指摘はすべて低か極低で、形式文・記録より強い文と、著者の判断の記録の書き換えはなかった。台帳の範囲の書き漏れ、ノート §2 の K の二つの意味、出所のパスの欠け、12:48 の二つの記述などを直した（台帳 L11）。
-- 閉鎖（2026-11-20 16:40）：著者が止め方の規則を決めた（低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい。CLAUDE.md §7）。R4 はこれに当たるので、Part 262 は閉じた。台帳 L11 は次のパートの統合照合に載せる。ラベル（1 は［既知］、2〜5 は［再導出（小さい）］、新規候補なし）はこの閉鎖で確定した。2・3 のラベルは 2026-11-20 17:29 に著者が［再導出（小さい）］で確定した（符号つきの形はその形では文献に見つかっておらず、「［既知］の直接の帰結」は文献の範囲を広く見せるため）。R3 の照合者は、n ≥ 1 で χ₁χ₂ が原始的でないとき J = 0 になることの手の論証の素描を示した（Lean の外、照合者の確信度：高）。
+- 照合 R3（2026-11-20 15:37〜15:45、`records/audit266/recheck_L9/`）：L9 を照らした。形式文より強い文はなし。指摘の主なもの：PAG265 で 19:58 の判断を「確認した」と強め、出所を誤って標示した、概要の標示の文（「決めたのは…だけ」）が事実と違う、留保の範囲の限定の漏れ（ノート §1・索引・xlsx）、ラベルの理由の文の慣行の主張に反例がある。直した（台帳 L10）。R3 の時刻は、起動（コミット 768cb6b の後）から通知まで。計測は約 468 秒（`records/audit266/recheck_L9/outputs/R3_meta.txt`。照合者の目安の申告は約 10〜12 分）。（後注 2026-11-25、統合照合 II-a の指摘：R3 の照合者が示した手の論証の素描（n ≥ 1 で χ₁χ₂ が原始的でないとき J = 0）の文は、閉鎖の行に移っているが、R3 の時点のもの。）
+- 照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/`）：L10 を照らした。指摘はすべて低か極低で、形式文・記録より強い文と、著者の判断の記録の書き換えはなかった。台帳の範囲の書き漏れ、ノート §2 の K の二つの意味、出所のパスの欠け、12:48 の二つの記述などを直した（台帳 L11）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
+- 閉鎖（2026-11-20 16:40）：著者が止め方の規則を決めた（低・極低だけで、強めた文と判断の記録の書き換えがなければ、次のパートの統合照合に載せて閉じてよい。CLAUDE.md §7）。R4 はこれに当たるので、Part 262 は閉じた。台帳 L11 は次のパートの統合照合に載せる。ラベル（1 は［既知］、2〜5 は［再導出（小さい）］、新規候補なし）はこの閉鎖で確定した。2・3 のラベルは 2026-11-20 17:29 に著者が［再導出（小さい）］で確定した（符号つきの形はその形では文献に見つかっておらず、「［既知］の直接の帰結」は文献の範囲を広く見せるため）。R3 の照合者は、n ≥ 1 で χ₁χ₂ が原始的でないとき J = 0 になることの手の論証の素描を示した（Lean の外、照合者の確信度：高）。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
 
 ## §7 収束アラームの報告
 
diff --git a/notes/pag2_tail_ledger.md b/notes/pag2_tail_ledger.md
index eacf767..165e8b3 100644
--- a/notes/pag2_tail_ledger.md
+++ b/notes/pag2_tail_ledger.md
@@ -4,29 +4,50 @@
 
 ## 開いている項目
 
-### L11：照合 R4 の後の直し（2026-11-20 夕方）
-
-- 範囲：R4 の指摘 1〜8 を受けた直し。
-  - PAG266 の冒頭の説明（形式文は変えていない）：留保の短い引用を索引 2.4 の文に揃えた、「φ は位相」の置き場。
-  - Part 262 のノート：§1 の留保の引用、§2 の K の書き方、§3 の確信度の出所、§6 の R3 の時刻の出所と R4 の記録。
-  - 補足 15 との照らし合わせのノート：「12:48〜の統合照合」を「12:48 のコミットに記録が入った統合照合（照合はそれより前）」に（コミット ef021d6 は 12:48 で、`records/audit264/outputs/integrated_output.md` を含む）。
-  - 引き継ぎメモ：12:48 の注、1406 行の後注の範囲（「台帳 L5・L8 の範囲」だけに）、R4 の記録と閉じる条件。
-  - 概要（日英）：「決定 (4)」に記録の参照、英語の読みを一つに。
-  - この台帳：閉じた L10 の範囲と自己申告の書き足し、閉じた根拠の補足の出所のパス、L11 の新設。
-  - 確かめたこと：PAG265 のノートに「確認した」はない（検索）。Part 262 のノート §3 の確信度に出所を足した。着手前の文書の Q3 の行は盲検の答えの要約で、確信度は書いていない。
-- 自己申告（根拠にしない）：出所・範囲の書き足しと、12:48 の記述の訂正。
-- 扱い：2026-11-20 16:40 の著者の決定（止め方の規則、CLAUDE.md §7）により、次のパートの統合照合に載せる。R4 は低・極低だけで、強めた文と判断の記録の書き換えはなかったので、Part 262 は閉じた。著者側の記録（2026-11-20 17:29）も、L1〜L10 は閉じ、L11 は次の統合照合に載る、で一致。
-- 注：L7 から L11 まで、直しを照らすたびに、直しが生む小さなずれ（とくに台帳が自分の変更を書き漏らすこと）が見つかっている。R4 の指摘は低か極低だけになった。著者は 2026-11-20 16:40 に止め方の規則を決めた（上の扱い）。
-
-### L12：辞書の欠落行の追加と CLAUDE.md の写し（2026-11-20 夕方、補足 16）
-
-- 範囲：辞書 §21 の新設、§17 の注、§20 の作用素の形の行の右列と未記入の件数。CLAUDE.md と英語版の §2（4 点）と §7（停止規則の箇条、段落の止め方の文）。引き継ぎメモの項、この台帳の L12。
-- 自己申告（根拠にしない）：文献の言葉は根拠つきで書いた。`canon` と `shellLift` の一致は見込みで、Lean で確かめていない。
-- 扱い：L11 と一緒に、次のパートの統合照合に載せる。
+### L13：Part 263（PAG267）の独立照合の後の直し（2026-11-25 夜）
+
+- 範囲：独立照合（`records/audit267/outputs/check_output.md`）の指摘を受けた直し。
+  - PAG267.lean：定理 4 つを足した（`invG_comp_pullSys`・`invL_ofL`・`Wproj_eqPt`・`resL_WL`。定義 `invG`・`invL`。主張を足した直し）。冒頭の説明（赤道の外は 0・∞ と同じでない、法 1、`not_exists_extL` は `resL` の線形な切断を否定しない、M ≠ 0 は外しても成り立つ見込み、共終な部分系の見込み、内部照合の B の行）と `not_exists_extL` の docstring。
+  - ノート `notes/pag2_pag267_p1_tower.md`（§2・§3・§5・§6）、xlsx（行 3724〜3757、メモ、検証手順の行 286。`records/audit267/update_xlsx_267.py`）、この台帳の L13〜L14 と閉じた項目への移動。
+- 自己申告（根拠にしない）：足した定理は sorry 0・警告 0、#print axioms は標準の 3 つ。機械的な照合をやり直した（712 回、一致なし）。
+- 扱い：閉じるときの統合照合 I に載せる。
+
+### L14：統合照合 II-a・II-b の後の直し（2026-11-25 夜）
+
+- 範囲：II-a（`records/audit267/outputs/integrated_IIa_output.md`）と II-b（`integrated_IIb_output.md`）の指摘を受けた直し。どれも後注の形で足し、記録の文は書き換えていない。
+  - 「R4 は低・極低だけ」の後注（R4 の 6 節の 1・2 は「低〜中」だった。16:40 の著者の決定がこれを知ったうえでのものかを著者に確かめる）：この台帳（L11 の扱い、閉じた L10 の 2 か所）、Part 262 のノート §6（R4 と閉鎖の行）、引き継ぎメモ（R4 と閉鎖の行）。
+  - ラベルの確定の書き分けの後注（1・4・5 は 16:40、2・3 は 17:29 に著者が確定）：PAG266.lean の冒頭の説明（コメントだけ。作り直してエラー・警告 0）、Part 262 のノート §4、索引（1 か所）、推薦案 `pag2_p1_gluing_preregistration.md`（1 か所）、引き継ぎメモ（ラベルの行）。
+  - Part 262 のノート §6 の R3 の行に、素描の文が R3 の時点のものという後注。引き継ぎメモの 17:29 の項に出所（著者の会話のメッセージ）と、理由の文は構築側の要約という後注。引き継ぎメモの閉鎖の行に、16:40 の著者のメッセージの逐語の後注。
+  - 辞書：§21 のさらい方の式の穴の後注、インスタンスの数（3 → 4）、「名前ではない」→「定義ではない」、`fC` の確信度：中、§20 の設定と F_p の式の範囲の後注。CLAUDE.en.md の英語の誤り 2 つ（an algebra、Signal 4）。
+  - 引き継ぎメモに、著者に確かめる事項（16:40 の決定の前提、CLAUDE.md §7 の 2 つの規則の関係、CLAUDE.md §2 の Part 260 の 3 条件・`InLayer` の文は著者側の版の写しで構築側は Lean で未確認）を書いた。
+- 直していないもの：CLAUDE.md（日本語版）の文面（著者側の版の写しなので、著者に確かめる事項にした）。II-a の低・極低の一部（L9 の範囲の「含める→含めた」、R3・R4 の時刻の出所の書き足し、「1406 行」の指し方、検索語の書き足し）。
+- 扱い：閉じるときの統合照合 I に載せる（II-a に「高」1 件・「中」3 件、II-b に「中」3 件があったので、停止規則の「もう1回だけ統合照合」に当たる）。
 
 ## 閉じた項目
 
-- L10（2026-11-20 に閉じた）：照合 R4 を、直しそのものを入力に含めて受けた。指摘は低か極低だけで、直しは L11。
+- L11・L12 と、台帳に項目のなかった記録の追記（コミット c7f2796・600b7c5・e6cb086・c3efc8d）（2026-11-25 に閉じた）：統合照合 II-a（L11 と c7f2796・600b7c5）・II-b（L12 と e6cb086・c3efc8d）を、直しそのもの（各コミットの差分）を入力に含めて受けた（`records/audit267/integrated/`、`records/audit267/outputs/`）。形式文より強い文の指摘はなかった。記録の側の指摘（II-a の高 1・中 3、II-b の中 3）の直しは L14。
+  - 閉じたときの L11・L12 の記載は、下にそのまま残す。台帳の漏れ（II-a の 4 節・II-b の 4 節）：L11 はノート §6 の R2・R3 の行の直し、閉じた L10 の「扱い」の行、`update_xlsx_266d.py` の追記と xlsx のメモの手での置き換えを書いていなかった。L12 は e6cb086・c3efc8d と、§20 の行の出典・注意の欄の書き換えと P¹(ℤ/p^K) の削除を書いていなかった。c7f2796・600b7c5 は台帳に項目がなかった。どれも II-a・II-b の入力の差分には入っていた。
+    ### L11：照合 R4 の後の直し（2026-11-20 夕方）
+
+    - 範囲：R4 の指摘 1〜8 を受けた直し。
+      - PAG266 の冒頭の説明（形式文は変えていない）：留保の短い引用を索引 2.4 の文に揃えた、「φ は位相」の置き場。
+      - Part 262 のノート：§1 の留保の引用、§2 の K の書き方、§3 の確信度の出所、§6 の R3 の時刻の出所と R4 の記録。
+      - 補足 15 との照らし合わせのノート：「12:48〜の統合照合」を「12:48 のコミットに記録が入った統合照合（照合はそれより前）」に（コミット ef021d6 は 12:48 で、`records/audit264/outputs/integrated_output.md` を含む）。
+      - 引き継ぎメモ：12:48 の注、1406 行の後注の範囲（「台帳 L5・L8 の範囲」だけに）、R4 の記録と閉じる条件。
+      - 概要（日英）：「決定 (4)」に記録の参照、英語の読みを一つに。
+      - この台帳：閉じた L10 の範囲と自己申告の書き足し、閉じた根拠の補足の出所のパス、L11 の新設。
+      - 確かめたこと：PAG265 のノートに「確認した」はない（検索）。Part 262 のノート §3 の確信度に出所を足した。着手前の文書の Q3 の行は盲検の答えの要約で、確信度は書いていない。
+    - 自己申告（根拠にしない）：出所・範囲の書き足しと、12:48 の記述の訂正。
+    - 扱い：2026-11-20 16:40 の著者の決定（止め方の規則、CLAUDE.md §7）により、次のパートの統合照合に載せる。R4 は低・極低だけで、強めた文と判断の記録の書き換えはなかったので、Part 262 は閉じた。著者側の記録（2026-11-20 17:29）も、L1〜L10 は閉じ、L11 は次の統合照合に載る、で一致。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
+    - 注：L7 から L11 まで、直しを照らすたびに、直しが生む小さなずれ（とくに台帳が自分の変更を書き漏らすこと）が見つかっている。R4 の指摘は低か極低だけになった。著者は 2026-11-20 16:40 に止め方の規則を決めた（上の扱い）。
+
+    ### L12：辞書の欠落行の追加と CLAUDE.md の写し（2026-11-20 夕方、補足 16）
+
+    - 範囲：辞書 §21 の新設、§17 の注、§20 の作用素の形の行の右列と未記入の件数。CLAUDE.md と英語版の §2（4 点）と §7（停止規則の箇条、段落の止め方の文）。引き継ぎメモの項、この台帳の L12。
+    - 自己申告（根拠にしない）：文献の言葉は根拠つきで書いた。`canon` と `shellLift` の一致は見込みで、Lean で確かめていない。
+    - 扱い：L11 と一緒に、次のパートの統合照合に載せる。
+
+- L10（2026-11-20 に閉じた）：照合 R4 を、直しそのものを入力に含めて受けた。指摘は低か極低だけで、直しは L11。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
   - 閉じたときの記載：
     - 旧項目 L10：照合 R3 の後の直し（2026-11-20 夕方）
 
@@ -41,7 +62,7 @@
       - この台帳：L7・L8・L9 を閉じた項目に移し、L10 を新設。閉じた L9 の記載に、範囲の 2 行・自己申告の追記・扱いの行を書き足し、閉鎖の要約の行を足した。
       - 範囲の書き足し（照合 R4 の指摘）：引き継ぎメモの「閉じる条件」の行の書き換え、Part 262 のノート §6 の R2 の記録の行（「次の照合の対象」を外した）。
     - 自己申告（根拠にしない）：記録の言葉に揃える直し、範囲の限定、出所の書き足し。新しい文として、R3 の照合者の手の論証の素描を出所つきで引いた。R4 の指摘のとおり、ほかに新しい文として「J は K によらない」、確信度の出所（blind_output の Q3）、補足 15 のノートの記述、crt_output.md のパス、R3 の時刻、閉鎖の要約の内容も足していた。
-    - 扱い：照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/outputs/R4_output.md`）で照らした。指摘は低か極低だけ。直しは L11。
+    - 扱い：照合 R4（2026-11-20 15:49〜15:57、`records/audit266/recheck_L10/outputs/R4_output.md`）で照らした。指摘は低か極低だけ。直しは L11。（後注 2026-11-25、統合照合 II-a の指摘：R4 の出力の 6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K）は「低〜中」と付けられていた。「低か極低だけ」は R4 の出力と合わない。2 件はどちらも記録の側で、L11 で直した。16:40 の著者の決定がこの 2 件を知ったうえでのものかは、著者に確かめる。記録は書き換えず、この後注を足した。）
 
 - L7・L8・L9（2026-11-20 に閉じた）：L7・L8 は再照合 R2（`records/audit266/recheck_int/outputs/R2_output.md`）、L9 は照合 R3（`records/audit266/recheck_L9/outputs/R3_output.md`）を、直しそのものを入力に含めて受けた。どちらも形式文より強い文の指摘はなかった。R2 の指摘の直しは L9、R3 の指摘の直しは L10。
   - 閉じたときの各項目の記載（記録として残す）：
diff --git a/notes/pag2_terwilliger_dictionary.md b/notes/pag2_terwilliger_dictionary.md
index 783bcce..930e9e0 100644
--- a/notes/pag2_terwilliger_dictionary.md
+++ b/notes/pag2_terwilliger_dictionary.md
@@ -470,12 +470,13 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
 | `equator_intertwine_rootNum`・`equator_intertwine_proj_rootNum` | 2 チャートの比較そのものは文献用語なし。各チャートの中身は、乗法的指標の畳み込みがヤコビ和倍になること χ₁ ⋆ χ₂ = J(χ₁, χ₂)·χ₁χ₂（有限体 F_p の場合、χ₁χ₂ が自明でないとき）。北のチャートでは χ̄ の畳み込みなので係数は conj(J)。（2026-11-20 に補足 16 の作業で足した） | 畳み込みの式は N. Katz「Exponential Sums」の翻訳 arXiv:2308.11611 の Lemma 1.3.2 と arXiv:2406.11529 の §3（どちらも F_p。検索結果の抜粋で確認、2026-11-20）。ℤ/p^k での形は Part 20（PAG24）の `equator_intertwine` の Lean の文で、文献では確かめていない。2 チャートの比較の文献は、検索 1 回（convolution / inversion / projective line / Jacobi sum / two charts）で見つからなかった（見つからなかったは不存在の証明ではない）。Part 21（PAG25）・Part 25（PAG29）の定理の係数の書き換え。射影直線の版は 2 チャートの版を `projFunEquiv` で移したもので同値（手の論証、Lean の文ではない）。設定そのものは盲検の 1 回の検索では見つからなかった |
 | 条件「U'² が赤道で B_S を B_N に移す」の解の集まり（Lean の外） | 部分群の補集合の上で乗法的な関数は準同型に延びる（|X/Y| ≥ 3）、ポントリャーギン双対 | 盲検の照合者の手計算（補題を書いた文献は探していない）。加法指標の取り替えで局所定数が χ(b) 倍になること（Tate、Biswas arXiv:1401.5591 §4.3） |
 
+- 後注（2026-11-25、統合照合 II-b の指摘）：作用素の形の行の比較の設定は P¹(ℤ/p^K) の 2 チャート（補足 16 の作業で文献の欄から設定の記述が落ちた）。F_p の畳み込みの式は、ℤ/p^k では指標が原始的な場合に限って成り立つ（照合者の数値：原始的なら法 9・25・27・49 で不一致 0、限らないと法 9 で 270 個中 8 個の不一致）。
 - 未記入の件数（この節）：0（2026-11-20 に補足 16 の作業で、作用素の形の行の右列を埋めた：比較そのものは「文献用語なし」、各チャートの畳み込みはヤコビ和倍の式。それまでは 1 と数えていた。統合照合 I の指摘）。
 
 ## 21. 行のなかった名前の追加（補足 16、2026-11-20。Parts 257〜261（PAG261〜PAG265）と parFac）
 
 - 欠落の種類（補足 16 の 5）：辞書の欠落には、右列が空の行だけでなく、**行そのものがない名前**もある。§7 の指標（右列が空の行の数）はこれを拾わないので、未記入の件数を数えるときは、各パートの新しい定義名に行があるかも確かめる。
-- さらった範囲（補足 16 の 4）：2026-11-20 に、PAG261〜PAG265 の `def`・`abbrev`・`structure`・`instance` の宣言を機械的に抜き出した（`grep -nE "^\s*(noncomputable )?(def|abbrev|structure|inductive|class|instance)\s"`）。定理の名前は対象にしていない。抜き出した定義名のうち、§17・§18 に行のあったもの（`fsum`、`cornerOp`、`cornerHom`、`CornerLim`、`ofCorner`）を除き、すべて下の表に入れた。インスタンス（`lvl_neZero`、`NeZero (primeProd S)`、`DirectedSystem` の 3 つ）は名前ではないので行にせず、所属する定義の行に書いた。補足 16 は `parFac` を Part 257 としていたが、定義は PAG256（Part 252）にある。
+- さらった範囲（補足 16 の 4）：2026-11-20 に、PAG261〜PAG265 の `def`・`abbrev`・`structure`・`instance` の宣言を機械的に抜き出した（`grep -nE "^\s*(noncomputable )?(def|abbrev|structure|inductive|class|instance)\s"`）。定理の名前は対象にしていない（後注 2026-11-25、統合照合 II-b の指摘：式には `inductive`・`class` も入っている。`private`・`protected` のつく宣言、同じ行に属性がつく宣言、`irreducible_def` は拾わない式で、完全性の確認としては穴がある）。抜き出した定義名のうち、§17・§18 に行のあったもの（`fsum`、`cornerOp`、`cornerHom`、`CornerLim`、`ofCorner`）を除き、すべて下の表に入れた。インスタンス（`lvl_neZero`、`NeZero (primeProd S)`、`DirectedSystem` の 2 つ（`sqMap`・`cornerSys` の行）の 4 つ。後注 2026-11-25、統合照合 II-b の指摘で「3 つ」を直した）は定義ではないので行にせず、所属する定義の行に書いた。補足 16 は `parFac` を Part 257 としていたが、定義は PAG256（Part 252）にある。
 - 書き方（補足 16 の 2・3）：文献の言葉が見つからない場合は「文献用語なし」と書いた。文献の言葉を書く場合は、根拠と確かめ方を添えた。「定義の読み」は、Lean の定義を読んで標準の数学用語と照らしたことを指し、文献の本文は開いていない。
 
 | 名前 | Part（PAG） | 文献の言葉 | 根拠・確かめ方 |
@@ -488,7 +489,7 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
 | `dTop` | Part 258（PAG262） | 基点の双対べき等元 E*_0（D_N = δ_0 への射影） | §3 の行「D_t … D_N = δ_0 への射影 ↔ 双対べき等元 E*_t、E*_0」。定義の読み。 |
 | `eTop` | Part 258（PAG262） | 自明な原始べき等元 E_0 = J/\|X\|（定数 1/N の畳み込み） | §3 の行「E_ND_NE_N = (1/N)E_N ↔ \|X\|E_0E*_0E_0 = E_0」。定義の読み。 |
 | `UDvd` | Part 259（PAG263） | ユニタリ約数（unitary divisor、Hall divisor）：d ∣ n かつ gcd(d, n/d) = 1 | E. Cohen, Arithmetical functions associated with the unitary divisors of an integer, Math. Z. 74（1960）66–80（書誌は EuDML で確認、本文は読んでいない）。定義は Wikipedia の Unitary divisor の項で確認（2026-11-20）。 |
-| `fC` | Part 259（PAG263） | M と M* を入れ替える T の自己同型（Curtin–Nomura の hyper-duality にあたる。定義の全条件との照合は未了） | §3 の行 `fourierConj`。`fC` はそれを A_N に制限したもの（定義の読み）。 |
+| `fC` | Part 259（PAG263） | M と M* を入れ替える T の自己同型（Curtin–Nomura の hyper-duality にあたる、確信度：中（CLAUDE.md §3 と同じ）。定義の全条件との照合は未了） | §3 の行 `fourierConj`。`fC` はそれを A_N に制限したもの（定義の読み）。 |
 | `Compat` | Part 259（PAG263） | 文献用語なし（Part 258 の条件 (i) 引き戻しとの両立、(ii) 殻を混ぜない（強い読み）） | ― |
 | `CompatF` | Part 259（PAG263） | 文献用語なし（`Compat` に (iii) フーリエとの両立を足した条件） | ― |
 | `canon` | Part 259（PAG263） | 互いに素な段では `shellLift` と同じ型の埋め込み（直積スキームのテンソル積分解を通した S ↦ S ⊗ 1） | 定義は (i)(ii)(iii) を満たす唯一の写像の選択。`shellLift` との一致は Part 259 の一意性の定理から出る見込みで、この表のために Lean では確かめていない。文献の言葉は `shellLift` の行と同じ根拠。 |
```

## §4 照合 R4 の出力の 6 節（`records/audit266/recheck_L10/outputs/R4_output.md` の 90〜105 行）
```
  - 台帳の閉鎖の要約の行（382 行）。L10 には「移し、新設」としか書かれていない。
- **自己申告（661 行）に入っていない新しい文**：「J は K によらない」、確信度の出所（blind_output の Q3）、補足 15 のノートの記述、crt_output.md、R3 の時刻、閉鎖の要約の内容。自己申告はもともと根拠にしないものですが、記載として不正確です。
- **xlsx**：`update_xlsx_266d.py` は行 3719〜3723 とメモを置き換えます。§D の行 3719 とメモの末尾はその結果と合います。行 3720〜3723 と、スクリプトを実行した出力は確かめられません。

### 6. 直すべき点（重要度順、直し案つき）

1. **（低〜中）L10 の範囲と自己申告**
   - 範囲に次を足す：「引き継ぎメモの「閉じる条件」の行、Part 262 のノート §6 の R2 の記録の行、この台帳の閉じた L9 の記載への書き足し（範囲の 2 行・自己申告の追記・扱いの行）と閉鎖の要約の行」。
   - 閉じた L9 の範囲には「ノート §6 の「含める」→「含めた」」をはっきり書く。
   - 自己申告に「新しい事実（R3 の時刻、確信度の出所、補足 15 のノートの記述、crt_output.md のパス）と「J は K によらない」」を足す。
2. **（低〜中）ノート §2 の K**：「p = 7, 11 の n+1 = 2 と p = 3 の n+1 = 3, 4 と p = 5 の n+1 = 3 の 3,536 組（R2 の報告の K は指標の法の指数 n+1。J は P¹ のモデルの法 p^K によらない）」にする。PAG266 と同じ書き方に揃える。
3. **（低）R3 の 11 の残り 3 件**：701 行（PAG242・「同名」、§E2）と 324 行（立て直し）に記録のパスを書く。書けなければ「記録のパスは示していない（作業経過の申告）」と書く。
4. **（低）12:48**：git のコミット時刻と照合の記録の時刻を確かめて、どちらかに直す。確かめないなら「どちらの記述が正しいかは確かめていない。どちらでも 18:39 より前で、結論は変わらない」と足す。
5. **（低）R3 の時刻**：15:37〜15:45 の出所（起動と通知の時刻など）を書き、照合者の申告「約 10〜12 分（目安）」を併記する。
6. **（低）確かめていない置き場**：PAG265 のノート、Part 262 のノート §3、着手前の文書に同じ文（「確認した」、出所のない「確信度：中〜高」）がないか検索し、その結果を台帳に書く。
7. **（低）1406 行の後注**：「…概要・引き継ぎメモの直し。台帳 L5・L8 の範囲」にするか、列挙をやめて「台帳 L5・L8 の範囲」とだけ書く。
```
