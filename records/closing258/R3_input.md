あなたは独立の照合者です。この 1 つのファイルだけを Read で読んでください（ほかのツールは使わないでください）。答えは日本語で。
判定ごとに確信度（高・中・低）を付け、見ていないもの・確かめられないものも書いてください。

# 依頼（閉鎖条件 3）：内部照合の監査の「F2 の後の直し（3 回目、記録だけ、照合を受けていない）」の照合

背景：内部照合の監査（Part 249〜256）で、直しの照合者 F2 の新しい指摘 16 件（下の A）を受けて 3 回目の直しを入れた。同時に、構築者自身の取り違え（PAG.lean・PAG2・PAG3 をまとめて「付録 A」と呼んでいた。正しくは、PAG 2.0 より前の最初の形式化の Part 1〜3（Part n は PAGn.lean）で、本文の定理 2.6・4.5、命題 2.8 と付録 A.2 の注記などを含む）を直した。直す前と後の差分を B に付ける（Lean は docstring と冒頭の説明だけ。形式文は変えていない）。
確かめてほしいこと：
1. F2 の新しい指摘 16 件のそれぞれが、差分で直ったか（直った／一部／直っていない／該当なし）。
2. 差分が新しい誤り（言い過ぎ、食い違い、番号の取り違え、「付録 A」の残り、文の壊れ）を入れていないか。
3. Lean の差分が docstring・冒頭の説明（/-! … -/ と /-- … -/）の中だけか。
出力：## 1. 新 1〜16 の判定（表）　## 2. 新しい誤り（表：場所｜問題｜直し方の案｜確信度）　## 3. 形式文の変更の有無　## 4. 総評（3 行まで）

# A. 照合者 F2 の出力（全文）
## 1. F の 24 件への対応

行番号の出典：lean_diff は round2_lean_diff.txt、notes_diff は round2_notes_diff.txt、報告は pag2_internal_audit_249_256.md。

| # | 判定 | 根拠（どこで直ったか） |
|---|---|---|
| 1 | 直った（高） | PAG256 冒頭（lean_diff 22–31）を 2 つに分けた。A は inv_apply_neg_one・neg_one_mul_self・isPrimitive_of_prime_of_ne_one・casKer。B は rootNum・inv_apply_units_inv・sum_mul_stdAddChar_neg。ノート 252 の見出し（notes_diff 41–50）と報告 44–52 行も同じく分けた。evidence の判定と合う |
| 2 | 直った（高） | lean_mechanical_summary.md の 21–22 行に 2 組が入った。MechChecks.lean 169–183 行に `type_of% @PAG.Part260.cast_crtMap_fst`・`_snd` の定理がある（axioms 22–23 行、error 0）。表は 30 行（前の鎖 28、範囲の中 2）。前の鎖の対象は 15（A・B 13 と ipG_smul_left・right）、定理は 44 で、報告 111 行と合う |
| 3 | 直った（高） | ManualChecks2.lean には section も variable もない。`type_of% @PAG.Part256.inv_apply_units_inv` を `intro N χ u` で示しており、インスタンスの引数はない。error 0。charU_eq_charFun・crossSign_eq_rs も NeZero を仮定しない。2 ≤ N の 2 件も type_of% で、対象が持つ NeZero だけを受けている |
| 4 | 直った（高） | PAG260 冒頭（lean_diff 114–116）を直した。4（parFac_prodChar）は「C。Lean では未確認」。5（rootNum_prodChar）は「D（C との境目）。監査者の見立ては C 寄り。Lean ではつないでいない」。「新しい」は xlsx D3542 と docstring（128）からも消えた |
| 5 | 直った（指摘した箇所は）（高） | xlsx B279 は「約 1 万 3 千回（組ごとに両向き）」、D279 は「前の鎖との重複が見つからなかった（網羅ではない）」になった。ただし同じ誤りが引き継ぎメモに残っている（新1） |
| 6 | 直った（高） | xlsx D3383 は「Part 12（PAG16）」、D3400 は「Part 214（PAG218）」になった。evidence の PAG16::normSq_gaussSum・PAG218::sum_units_char と合う。docstring 2 か所（lean_diff 45・73）とノート 5 か所（notes_diff 23・32・67・76・85）も直した。D3295 の直しには根拠がない（新2） |
| 7 | 直った（高） | 「照合者 R2 の判定」「C」「2 件は Lean で確認、5 件は確信度 低で未確認」を書き足した。場所はノート 252 §9（notes_diff 54・57）、報告 20・146 行、xlsx A3373、メモ 191 行 |
| 8 | 直った（高） | 「前の鎖に見つからなかったもの（網羅ではない）」に書き換えた。場所は PAG256 冒頭（lean_diff 36）、PAG260 冒頭（119）、ノート 252・253・254・256（notes_diff 56・99・111・149）。PAG255・257・258 の冒頭にも「網羅ではない」を足した |
| 9 | 直った（高） | PAG256 冒頭（lean_diff 32–34）に「5 件とも確信度 低、Lean では未確認」と「casK_even_part・casK_odd_part から」を足した。PAG258 冒頭（88）に「phaseA1_one（確信度 低）」を足した |
| 10 | 直った（高） | docstring（lean_diff 137）を「式と同値になる」「W = 1 の仮定を使わずに（互いに素・原始・実の指標のもとで）」に直した。冒頭 118 行、ノート 256（146）、xlsx D3546、報告 19・95 行、メモ 197 行、Part 257 の着手前の文書（159 行と §11）も同じ。evidence の 5 つの仮定（919–922 行）と合う。小さな残りは新10・新11 |
| 11 | 直った（高） | xlsx D3546 に「数学として。Lean ではつないでいない」を足した。ノート 256（146）には出所（xlsx の gauss_sign_aux の行）と「証明の中身は確かめていない」を書いた。gauss_sign_aux の形式文（evidence 926–930）は、符号の決定と素数冪の実原始指標との相互法則を 1 つの文にまとめたもので、記述と食い違わない。「強い帰納法」は、xlsx の該当行が材料にないので確かめていない |
| 12 | 直った（高） | (a) 報告 134 行で範囲を「前の鎖に対する A・B と範囲の中の ip」に限り、範囲の中の B 8 件は ip_smul_right 以外は未確認と書いた。(b) は 112 行「14 件（定理 8・定義の一致 6）」。表（123–129 行）の A・B 35 件 ＝ 前の鎖 26 ＋ 範囲の中 9 で合う |
| 13 | 直った（高） | 3 ファイルの全 64 定理（44・14・6）に #print axioms がある。*_axioms.txt はすべて propext・Classical.choice・Quot.sound かその一部で、error 0 |
| 14 | 一部だけ（高） | evidence に C 20 件すべて、D の 3 件（rootNum_prodChar・cross_eq_sign_of_rootNum_one・decomp）、parFac_of_even、番号の規約が入った。xlsx 3551・3552 は PAG202＝Part 198、PAG199＝Part 195 で正しいと確かめられる。まだ形式文がないもの：parFac_of_odd、前の鎖への一般化（ipG と Part 48 の ip・Part 225 の herm、kUnit_mul_natCast・unitsMap_kUnit と Part 33、Part 255 の一般化）、範囲の中の B・C（kUnit_congr など）。足さない理由も書かれていない |
| 15 | 一部だけ（中） | PAG260 冒頭に宣言名を書き、A・B と C を分けた（norm_char_unit・norm_cross は C の文に入った）。ただし「つまり上の 1・2・3 と 6 の前半の宣言は、すべて前の鎖にあった」が残っている。項目 1〜3 の本文が材料にないので照合できない（新6） |
| 16 | 直った（高） | PAG257 冒頭（lean_diff 60–61）を「PAG.charFun に MulChar.toUnitHom を通したものと同じ関数」に直した。報告 21–23 行は「同じ定義」と「同じ値」に分けて 7 つとした。ただし報告 135 行に元の書き方が残っている（新7）。「7 つ」には範囲の中の ip が入っている（新4） |
| 17 | 直った（高） | z_mul_coprime を足した。場所は docstring（lean_diff 128）、冒頭（115）、ノート 256（144）、xlsx D3542、報告 94 行。evidence 877–887 行と合う |
| 18 | 直った（高） | 冒頭（lean_diff 116–117）、ノート 256（145）、報告 96 行を「decomp（存在）と charMul_injective（一意性）を合わせると出る（監査者の読み。Lean ではつないでいない）」にした。ノート 256 §1（133）は「§9」を指し、出所は §9 に書いてある |
| 19 | 直った（高） | PAG255 冒頭（lean_diff 9–10）を「PAG.lean〜PAG252.lean と PAG3・PAG5・PAG6」にし、範囲の中の kUnit_congr を分けて書いた。ノート 255（122）も同じ書き方になった |
| 20 | 直った（高） | xlsx A3373 を「付録 A の Part 3 の casK」に直した |
| 21 | 直った（高） | ノート 251（notes_diff 12）とノート 255（123）に「照合者の判定。Lean では未確認」を足した。253（98）と 254（110）も同じ |
| 22 | 直った（高） | xlsx A3561、報告 184–185・194 行、メモ 199 行を「PAG256〜258・260 の docstring と PAG255〜258・260 の冒頭」「Part 251〜254・256 の行」に直した。docstring の数（7・7・1・14）は round1_lean_diff と合う |
| 23 | 直った（高） | PAG258 冒頭（lean_diff 87）を「conj_gaussSum と chi_neg_one_sq から」に直した |
| 24 | 直った（高） | 報告 104–105 行で、ipG が ip・herm を広げたことは「照合者の判定」とし、「Lean で確認」は 2 つの smul 定理だけに限った（MechChecks 9–47 行、表 7–11 行） |

## 2. 新しい指摘

| 場所 | 問題 | 直し方の案 | 確信度 |
|---|---|---|---|
| 新1：引き継ぎメモ（notes_diff 187） | #5(b) と同じ「一方を他方にそのまま当てる確認を約 1 万 3 千組」が残っている。2 回目でこの行を書き換えたのに直っていない。12,776 は試行の回数で、組の数は 30 | 「約 1 万 3 千回（組ごとに両向き・複数の戦術）」 | 高 |
| 新2：xlsx D3295（Part 249 の行） | 「Part 218 の dil_one・dil_dil」を「Part 214（PAG218）」に直したが、evidence に dil_one・dil_dil の形式文も所在もない。check_part_refs.py の出力も材料にない。もとの「Part 218」（＝PAG222）が正しかった場合は、直しで誤りを入れたことになる | evidence に dil_one・dil_dil の名前空間（PAG.PartNNN）を足す | 中（根拠がないことは確か。直しが正しいかは分からない） |
| 新3：報告 §5（152 行）、メモの規則（178 行） | ファイル番号の取り違えを「Part 252・253 の記録に」あったとしている。一方、§7 と xlsx A3561 は「Part 249・252・253 の行」の 3 か所としている（D3295 は Part 249 の行で、宣言も別）。報告の中で食い違う | 「Part 249・252・253 の記録に」とし、D3295 の例も挙げる | 高 |
| 新4：報告 21 行、手順 5（35 行） | 「前の鎖の定義と一致する定義が 7 つ」の中に、同じ箇条で「範囲の中」と書いた ip が入っている。前の鎖に対しては 6。手順 5 の「前の鎖に対する A・B」の 44 定理・14 件も、範囲の中（ip と 2 組）と一般化の 5 定理を含むファイル全体の数 | 「7 つ（前の鎖に対して 6、範囲の中で 1）」とし、手順 5 に内訳を書く | 高（影響は小さい） |
| 新5：報告 §8（209 行） | 「24 件すべてを直すか、直した形で受け入れました」は言い過ぎ。#14・#15 は一部だけで、理由も書かれていない | 「22 件を直し、#14・#15 は一部」と理由つきで書くか、evidence と PAG260 冒頭を直す | 中 |
| 新6：PAG260 冒頭（lean_diff 113） | 「つまり…すべて前の鎖にあった」が直前の A と B を受けており、B（直ちに出る）まで「あった」にまとめている。#1 と同じ型の格上げ。C の norm_char_unit・norm_cross が項目 1〜3 に入っていないかも、項目の本文がないので確かめられない | 「前の鎖にあるか、前の宣言から直ちに出る（A・B）」とし、項目ごとに宣言名を書く | 中（B を含むこと）／低（C を含むか） |
| 新7：報告 §4（135 行） | 「charU は…同じ関数でした」に、#16 で直した「toUnitHom を通したもの」が抜けている。charFun は G →* ℂˣ を受けるので、このままでは同じ関数ではない | 「PAG.charFun に toUnitHom を通したものと同じ関数」 | 中 |
| 新8：ノート 252（notes_diff 57）、報告 146 行 | 「命題 2.8 の再導出にあたる（確信度：中〜高）」。中心 7 件のうち 5 件は照合者の確信度が低く Lean で未確認なのに、中〜高とする理由が書かれていない | 理由を 1 文足すか、「中」にする | 低 |
| 新9：報告 18・115 行 | 「6 件とも判定どおり」としているが、hartley_one の証明は SampleC2 で 23 行あり、C（数行で出る）にあたるかは微妙。標本の選び方も書かれていない（2 回目に足した 2 件は Hartley の主張を支える hartley_one・casKer_eq） | 選び方を書き、結論にも「hartley_one は約 20 行」と添える | 低 |
| 新10：xlsx A3531 | 相互法則の文に「（互いに素・原始・実の指標のもとで）」がない。ほかの箇所には書いてある | 同じ括弧を足す | 低 |
| 新11：docstring（lean_diff 137）、報告 95 行、xlsx D3546 | 同値の理由が「crossSign と rs が同じ値なので」だけになっている。同値には rs = ±1 も要る | 「同じ値で ±1 なので」 | 低 |
| 新12：PAG260 冒頭の A の見出し、xlsx D279 | A の呼び方がそろっていない。PAG260 は「同じ文・同じ定義」の中に crossSign（同じ値）を入れ、D279 は「同じ文・同じ対象」と書く | 「同じ文・同じ値の定義（A）」にそろえる | 低 |
| 新13：引き継ぎメモ 187・191 行 | (a)「type_of% で述べる」は、定義の一致 8 件（HEq 2、値の等式 6）には当たらない。(b)「χ(−1) の補題 3 つ…167」の 3 つ目（primitive_of_ne_one）は χ(−1) の補題ではない。「A・B が 7」の列挙は 5 件で、B の 2 件が抜けている（(b) は 1 回目から） | (a)「定理は type_of% で述べる」 (b) A 4 件・B 3 件を名前で書く | 低 |
| 新14：報告 7 行・メモ 178 行と、evidence 3 行・依頼文 | 番号の対応の書き方がそろっていない（報告とメモは「PAG.lean〜PAG4 は付録 A の Part 1〜4」）。報告の規則では、#20 と同じく「Part 1 の PAG.charFun」（PAG257 冒頭、報告 23・65 行、xlsx A3395、メモ 192 行）が PAG5 とも読める。PAG4 の対応は材料で確かめられない | 対応の文を 1 つにそろえ、「付録 A の Part 1（PAG.lean）」と書く | 低 |
| 新15：MechChecks.lean の A の両向きの組 | 各定理は exact、apply と assumption、apply と simp_all の 3 つの分岐を順に試す形で、どの分岐で通ったかは抜き出しからは分からない。simp_all の分岐で通った組は、「同じ文」の根拠としては弱い | A の組だけ simp_all の分岐を外して組み立て直す | 低（分からない） |
| 新16：Part 257 の着手前の文書（notes_diff 161、2 回目では変えていない行） | 「P1 で鎖に新しいのは」が残っている。#8 と同じ型だが、監査の注記の外 | 「鎖に見つからなかったのは（網羅ではない）」 | 低（範囲外かもしれない） |

見ていないもの・確かめていないもの：
- .out の本体（見たのは抜き出しの *_axioms.txt だけ）と Lean ファイルの全体。
- PAG260 冒頭の項目 1〜8 の本文と、xlsx の gauss_sign_aux の行。
- check_part_refs.py の出力と outputs/F_output.md。
- 報告の「43 か所」と「.out は直す前と同一」。

## 3. 形式文の変更の有無

**変更なし**（確信度：高）。差分は 9 hunk（PAG255 1、PAG256 2、PAG257 2、PAG258 1、PAG260 3）で、変わった行はすべて `/-! … -/` の冒頭の説明か `/-- … -/` の docstring の中にある。宣言の行、omit、open Classical in、証明はどれも文脈行のまま残っている。行のずれ（+1、+1、+1、0、+2）も、足した行の数と合う。ただし、差分がこれで全部であることと、組み立て直した後の結果は材料にないので、確かめていない。

## 4. 総評

24 件のうち 22 件は直り、#14（evidence に parFac_of_odd・一般化・範囲の中の関係の形式文がない）と #15 は一部だけ。
「Lean で確認」はすべて、type_of% の定理か、必要な仮定だけで述べた定義の一致で裏づけられている。件数（26・20・6、44＋14＋6＝64、30／28／15）も合い、形式文の変更もない。
主に直すべきなのは新1（メモの「約 1 万 3 千組」）、新2・新3（根拠のない D3295 の直しと、それに伴う報告内の食い違い）、新4（「7 つ」に ip が入っている）、新5（「24 件すべて」）、新6（B を「あった」にまとめた文）。


# B. 3 回目の直しの差分（直す前 → 現在）
注意：Part 257 の着手前の文書には、3 回目の直しの後に §12（著者の判断）などを追記した。その追記も差分に出るが、照合の対象ではない。引き継ぎメモ final77 には監査の後に「直しの照合」の行も足した。
```diff
--- before/PAG256.lean
+++ after/PAG256.lean
@@ -21,11 +21,11 @@
 
 内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：前の鎖と同じ文・同じ値の定義（A。Lean で確認）は、
-`inv_apply_neg_one`・`neg_one_mul_self`（Part 5・21・25・77）、`isPrimitive_of_prime_of_ne_one`（Part 167）、`casKer`（付録 A の
-Part 3 の `casK` と同じ値）。前の宣言から直ちに出るもの（B。Lean で確認）は、`rootNum`（Part 192 の `zN` ÷ Part 194 の `gs` と同じ値）、
-`inv_apply_units_inv`・`sum_mul_stdAddChar_neg`（付録 A の Part 3）。照合者の判定で数行で出るもの（C）は、`hartley_one`・`casKer_eq`
-（付録 A の Part 3 の命題 2.8 `hartley_char`、`casK_even_part`・`casK_odd_part` から。この 2 件は Lean で確認）、`hartley_eq_of_isPrimitive`・
+`inv_apply_neg_one`・`neg_one_mul_self`（Part 5・21・25・77）、`isPrimitive_of_prime_of_ne_one`（Part 167）、`casKer`（Part 3（PAG3.lean）
+ の `casK` と同じ値）。前の宣言から直ちに出るもの（B。Lean で確認）は、`rootNum`（Part 192 の `zN` ÷ Part 194 の `gs` と同じ値）、
+`inv_apply_units_inv`・`sum_mul_stdAddChar_neg`（Part 3（PAG3.lean））。照合者の判定で数行で出るもの（C）は、`hartley_one`・`casKer_eq`
+（Part 3（PAG3.lean）の命題 2.8 `hartley_char`、`casK_even_part`・`casK_odd_part` から。この 2 件は Lean で確認）、`hartley_eq_of_isPrimitive`・
 `hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`（`hartley_char` などから。5 件とも
 確信度 低、Lean では未確認）、`normSq_rootNum`（Part 12 の `normSq_gaussSum` から。Lean で確認）、`exists_primitive_odd_three`
-（Part 115・163・167 から。Lean で確認）・`exists_primitive_even_five`、`parFac`・`rootNum_eq`（Part 194 の `gs`、付録 A の Part 2 の
+（Part 115・163・167 から。Lean で確認）・`exists_primitive_even_five`、`parFac`・`rootNum_eq`（Part 194 の `gs`、 Part 2（PAG2.lean）の
 `parity_weight`）。前の鎖に見つからなかったもの（網羅ではない）は、変換としての定義（`hartley`・`JH`）と、反例（`removal_counterexample` など）。
 -/
@@ -46,5 +46,5 @@
 
 /-- Hartley の核 cas(2π t/N) = cos(2π t/N) + sin(2π t/N)（t の代表は t.val）。
-内部照合（2026-11-14）：付録 A の Part 3（PAG3.lean）の `casK` と同じ値（式の書き方は違う。Lean で値の一致を確認）。 -/
+内部照合（2026-11-14）：Part 3（PAG3.lean）の `casK` と同じ値（式の書き方は違う。Lean で値の一致を確認）。 -/
 noncomputable def casKer (t : ZMod N) : ℂ :=
   ((Real.cos (2 * Real.pi * t.val / N) + Real.sin (2 * Real.pi * t.val / N) : ℝ) : ℂ)
@@ -163,5 +163,5 @@
 omit [NeZero N] in
 /-- χ⁻¹(u⁻¹) = χ(u)（u は単数）。
-内部照合（2026-11-14）：付録 A の Part 3（PAG3.lean）の `apply_inv_eq_inv_apply` から 1 行で出る（Lean で確認）。 -/
+内部照合（2026-11-14）：Part 3（PAG3.lean）の `apply_inv_eq_inv_apply` から 1 行で出る（Lean で確認）。 -/
 theorem inv_apply_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
     χ⁻¹ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u := by
@@ -217,5 +217,5 @@
 
 /-- Σ_x χ(x)e(−x) = χ(−1)·τ(χ)（x ↦ −x の置換。原始性は要らない）。
-内部照合（2026-11-14）：付録 A の Part 3（PAG3.lean）の `sum_neg_twist` の x = 1 の場合（Lean で確認）。 -/
+内部照合（2026-11-14）：Part 3（PAG3.lean）の `sum_neg_twist` の x = 1 の場合（Lean で確認）。 -/
 theorem sum_mul_stdAddChar_neg (χ : DirichletCharacter ℂ N) :
     ∑ x : ZMod N, χ x * stdAddChar (-x) = χ (-1) * gaussSum χ stdAddChar := by
--- before/PAG257.lean
+++ after/PAG257.lean
@@ -47,8 +47,8 @@
 「長さが保たれるのはちょうど V_prim の上」（Sz.-Nagy–Foiaș の標準分解のユニタリ部分）も同じ理由で数値だけ（(14)）。
 
-内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：`charU` は Part 1 の `PAG.charFun` に `MulChar.toUnitHom` を通したものと
+内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：`charU` は Part 1（PAG.lean）の `PAG.charFun` に `MulChar.toUnitHom` を通したものと
 同じ関数、`ip` は Part 249 の `ipG` と同じ定義（範囲の中）。`eq_one_of_two`（Part 194）、`not_isPrimitive_one_of_two_le`・
 `charU_one_mem_Vimprim`（Part 191）、`not_isPrimitive_one_prime`（Part 28）、`Vprim_two`（Part 26）は前の定理から直ちに出る（Lean で確認）。
-照合者の判定では `ip_charU`（Part 214 の `sum_units_char` と付録 A の Part 3 の `conj_apply_eq_inv`）も数行で出る（Lean では未確認）。
+照合者の判定では `ip_charU`（Part 214 の `sum_units_char` と Part 3（PAG3.lean）の `conj_apply_eq_inv`）も数行で出る（Lean では未確認）。
 作用素 T と V_prim の上のユニタリ性などの主な文は、前の鎖に見つからなかった（網羅ではない）。
 -/
--- before/PAG260.lean
+++ after/PAG260.lean
@@ -47,9 +47,9 @@
 変化から出る形にあたる）。
 
-内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：前の鎖と同じ文・同じ定義（A。Lean で確認）は、`prodChar`（Part 195 の `cmul`・
+内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：前の鎖と同じ文・同じ値の定義（A。Lean で確認）は、`prodChar`（Part 195 の `cmul`・
 Part 232 の `charMul` と同じ定義）、`crtMap`（Part 189 の `param` と同じ式）、`crossSign`（Part 194 の `rs` と同じ値）、`crtMap_bijective`・
 `stdAddChar_crtMap`・`gaussSum_prodChar`・`prodChar_apply`（Part 189 の定理と同じ文）、`isPrimitive_prodChar`（Part 190・232 の定理と同じ文）。
 前の宣言から直ちに出るもの（B。Lean で確認）は、`cast_crtMap_fst`・`cast_crtMap_snd`（Part 189）、`charU_prodChar`（Part 232）、
-`prodChar_neg_one`（Part 200）。つまり上の 1・2・3 と 6 の前半（`isPrimitive_prodChar`）の宣言は、すべて前の鎖にあった。
+`prodChar_neg_one`（Part 200）。つまり上の 1・2・3 と 6 の前半（`isPrimitive_prodChar`）の宣言は、すべて前の鎖にあるか、前の宣言から直ちに出る（A・B）。
 照合者の判定では、`norm_char_unit`・`norm_cross`・`parFac_prodChar`（4。Part 194 の `gs_combine` と同じ形）は数行で出る（C。Lean では
 未確認）。`rootNum_prodChar`（5）は照合者の判定で D（C との境目）で、中身は Part 189 の `z_mul_coprime`・`gaussSum_mul_coprime` に
@@ -306,5 +306,5 @@
 /-- 条件つきの文：W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 なら s·χ₁(N)·χ₂(M) = 1（互いに素の仮定は余分。外した形は Lean にしていない）。2 次の指標では平方剰余の
 相互法則と同じ形になるが、3 つの仮定は外から入れるもので、ここからは出ない。
-内部照合（2026-11-14）：実原始指標では、3 つの仮定は Part 194（PAG198）の `gauss_sign_real` から成り立ち、結論は Part 194 の `real_reciprocity` の式と同値になる（`crossSign` と `rs` が同じ値なので。数学として。Lean ではつないでいない）。相互法則そのものは Part 194 で、W = 1 の仮定を使わずに（互いに素・原始・実の指標のもとで）示してある。 -/
+内部照合（2026-11-14）：実原始指標では、3 つの仮定は Part 194（PAG198）の `gauss_sign_real` から成り立ち、結論は Part 194 の `real_reciprocity` の式と同値になる（`crossSign` と `rs` が同じ値で、どちらも ±1 なので。数学として。Lean ではつないでいない）。相互法則そのものは Part 194 で、W = 1 の仮定を使わずに（互いに素・原始・実の指標のもとで）示してある。 -/
 theorem cross_eq_sign_of_rootNum_one (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
     (χ₂ : DirichletCharacter ℂ N) (w1 : PAG.Part256.rootNum χ₁ = 1)
--- before/pag2_internal_audit_249_256.md
+++ after/pag2_internal_audit_249_256.md
@@ -4,8 +4,8 @@
 
 - 範囲：Part 249〜256（PAG253〜PAG260.lean）の宣言 334 件（定理 271、定義 63。自動で作られる宣言は除く）。
-- 突き合わせた相手（「前の鎖」）：PAG.lean（Part 1）〜PAG252.lean と、鎖に import されていない初めのファイル PAG3・PAG5・PAG6（付録 A の Part 3 と PAG 2.0 の初め）。全部で 4279 宣言。
-- 番号の対応：PAG 2.0 の Part n は PAG(n+4).lean。PAG.lean・PAG2・PAG3・PAG4 は付録 A の Part 1〜4。名前空間 `PAG.PartNNN` の NNN はファイル番号。
+- 突き合わせた相手（「前の鎖」）：PAG.lean（Part 1）〜PAG252.lean と、鎖に import されていない初めのファイル PAG3・PAG5・PAG6（PAG 2.0 より前の最初の形式化の Part 3 と、PAG 2.0 の初め）。全部で 4279 宣言。
+- 番号の対応：PAG 2.0 の Part n は PAG(n+4).lean。PAG.lean・PAG2・PAG3・PAG4 は PAG 2.0 より前の最初の形式化の Part 1〜4（xlsx の検証手順の記載。本文の定理 2.6・4.5、命題 2.8、付録 A.2 の注記などを含む）。名前空間 `PAG.PartNNN` の NNN はファイル番号。
 - Lean の鎖の形式文は変えていません。docstring と冒頭の説明に注記を足し、組み立て直しました（§7）。
-- 第 2 版（17:5x）：直しの照合（照合者 F）の指摘 24 件を受けて、注記の強さと根拠の書き方を直した版です（§8）。
+- 第 3 版（18:4x）：直しの照合（照合者 F の指摘 24 件、照合者 F2 の指摘 16 件）を受けて、注記の強さと根拠の書き方を直した版です。F2 の後の直しは照合を受けていません（§8）。
 
 ## 結論
@@ -18,11 +18,11 @@
 - **前の宣言から数行で出るもの（C）は、照合者の判定で 20 件です。** 6 件を標本として Lean で確かめ、6 件とも判定どおりでした。
 - **Part 256 の前半は、ほぼ全部が示し直しでした（Lean で確認）。** 中国剰余の分解、積の指標、ガウス和の乗法性、原始性が該当し、元は Part 189・190・195・232 です。偶奇の符号 `crossSign` は Part 194 の `rs` と同じ値です。相互法則も Part 194 の `real_reciprocity` にあり、W = 1 の仮定を使わずに（互いに素・原始・実の指標のもとで）示してあります。
-- **照合者 R2 の判定では、Part 252 の Hartley の部分の中心 7 件は、付録 A の Part 3（PAG3.lean、命題 2.8 `hartley_char`）などから数行で出ます。** そのうち `hartley_one` と `casKer_eq` を Lean で確かめました。残り 5 件は照合者の確信度が低く、Lean では確かめていません。PAG3.lean は鎖に import されていないファイルで、初めの機械的な照合からも漏れていました。照合者が見つけました。
-- **前の鎖の定義と一致する定義が 7 つありました。**
+- **照合者 R2 の判定では、Part 252 の Hartley の部分の中心 7 件は、 Part 3（PAG3.lean。命題 2.8 `hartley_char`）などから数行で出ます。** そのうち `hartley_one` と `casKer_eq` を Lean で確かめました。残り 5 件は照合者の確信度が低く、Lean では確かめていません。PAG3.lean は鎖に import されていないファイルで、初めの機械的な照合からも漏れていました。照合者が見つけました。
+- **前の鎖の定義と一致する定義が 6 つ、範囲の中で一致する定義が 1 つありました。**
   - 同じ定義（`rfl`・`HEq rfl`）：`prodChar`（Part 195 の `cmul`・Part 232 の `charMul` に次ぐ 3 つ目の名前）、`crtMap`（Part 189 の `param`）、Part 253 の `ip`（Part 249 の `ipG`。範囲の中）。
-  - 同じ値（式は違う）：`casKer`（付録 A の Part 3 の `casK`）、`rootNum`（Part 192 の `zN` ÷ Part 194 の `gs`）、`crossSign`（Part 194 の `rs`）、`charU`（Part 1 の `PAG.charFun` に `toUnitHom` を通したもの）。
+  - 同じ値（式は違う）：`casKer`（Part 3（PAG3.lean）の `casK`）、`rootNum`（Part 192 の `zN` ÷ Part 194 の `gs`）、`crossSign`（Part 194 の `rs`）、`charU`（Part 1（PAG.lean）の `PAG.charFun` に `toUnitHom` を通したもの）。
 - **Part 249・250・255 には、前の鎖との重複は見つかりませんでした（網羅ではない）。** 範囲の中の系（前のパートから直ちに・数行で出る便利な補題）はありますが、重複には数えていません。
 - **限界があります。** 照合者は Grep が使えず、全宣言の文（約 2 万 2 千行）の 1〜3 割しか読めていません。機械的な候補選びは上位 20 件までです。「見つからなかった」は「ない」の証明ではありません（§8）。
-- **直したもの。** Lean の docstring と冒頭の説明、ノート 8 本と着手前の文書 2 本、xlsx、引き継ぎメモ（final77）です。直した箇所は照合者 F が確かめ、その指摘で 2 回目の直しをしました。2 回目の直しの照合は照合者 F2 です（§8）。
+- **直したもの。** Lean の docstring と冒頭の説明、ノート 8 本と着手前の文書 2 本、xlsx、引き継ぎメモ（final77）です。直した箇所は照合者 F が確かめ、その指摘で 2 回目の直しをしました。2 回目の直しは照合者 F2 が確かめ、F2 の指摘への対応は記録だけで直しました（照合は受けていない。§8）。
 - **規則の追加の条文案は付録に置きました。** 著者の判断は「足す」です。CLAUDE.md への条文化は著者側で行ってください。
 
@@ -33,5 +33,5 @@
 3. **Lean での直接の当てはめ**（`lean/DupCmd.lean`・`DupCmd2.lean` の `#dupcheck`・`#defeqcheck`）：鎖の外のファイルで、候補の組ごとに一方を他方にそのまま当てて（`exact`、`apply` と仮定、`simp_all`）両向きを試しました。定義は `HEq` の `rfl` で比べました。試行は合計 12,776 回です。
 4. **独立の照合者 5 人（R1〜R5）**：新しいセッションに、対象と候補の形式文の全文と、各ファイルの open・variable の行を渡しました。全宣言の文（`statements_all.txt`）も渡しました。判定は A・B・C・D です（A 同じ文、B 直ちに出る、C 数行で出る、D 見つからない）。ほかの照合者の出力と機械的な確認の結果は渡していません。照合者の判定の前に予想を書きました（`expected_before_review.md`）。
-5. **前の鎖に対する A・B を Lean で確かめました。** 直接の当てはめで通った組は、名前つきの定理に書き直しました（`lean/MechChecks.lean`、44 定理）。通らなかった組は、前の宣言だけから手で示しました（`lean/ManualChecks2.lean`、14 件）。どちらも、定理については対象の型そのもの（`type_of%`）を述べています。仮定は足していません。
+5. **前の鎖に対する A・B を Lean で確かめました。** 直接の当てはめで通った組は、名前つきの定理に書き直しました（`lean/MechChecks.lean`、44 定理。前の鎖に対する 28 組と範囲の中の 2 組で、Part 249 の一般化 5 定理を含む）。通らなかった組は、前の宣言だけから手で示しました（`lean/ManualChecks2.lean`、14 件。うち 1 件は範囲の中の `ip`）。どちらも、定理については対象の型そのもの（`type_of%`）を述べています。仮定は足していません。
 6. **C の判定から標本 6 件を Lean で確かめました**（`lean/SampleC2.lean`）。
 
@@ -46,16 +46,16 @@
   - `neg_one_mul_self`：Part 5 の `chi_neg_one_sq`、Part 25 の `chi_neg_one_sq'` と同じ文。
   - `isPrimitive_of_prime_of_ne_one`：Part 167 の `primitive_of_ne_one` と同じ文。
-  - `casKer`（定義）：付録 A の Part 3 の `casK` と同じ値（定義から直接示した。`casKer_eq_casK`）。
+  - `casKer`（定義）：Part 3（PAG3.lean）の `casK` と同じ値（定義から直接示した。`casKer_eq_casK`）。
 - **B（直ちに出る。Lean で確認、3 件）**
   - `rootNum`（定義）：Part 192 の `zN` を Part 194 の `gs` で割ったものと同じ値（`rootNum_eq_zN_div_gs`）。
-  - `inv_apply_units_inv`：付録 A の Part 3 の `apply_inv_eq_inv_apply` から 1 行。
-  - `sum_mul_stdAddChar_neg`：付録 A の Part 3 の `sum_neg_twist` の x = 1 の場合。
+  - `inv_apply_units_inv`：Part 3（PAG3.lean）の `apply_inv_eq_inv_apply` から 1 行。
+  - `sum_mul_stdAddChar_neg`：Part 3（PAG3.lean）の `sum_neg_twist` の x = 1 の場合。
 - **C（照合者 R2 の判定、12 件）**
-  - Hartley の部分の中心 7 件：`hartley_one`・`casKer_eq`（Lean で確認）、`hartley_eq_of_isPrimitive`・`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`（確信度 低、Lean では未確認）。前の宣言は付録 A の Part 3 の `hartley_char`、`casK_even_part`・`casK_odd_part` など。
+  - Hartley の部分の中心 7 件：`hartley_one`・`casKer_eq`（Lean で確認）、`hartley_eq_of_isPrimitive`・`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`（確信度 低、Lean では未確認）。前の宣言は Part 3（PAG3.lean）の `hartley_char`、`casK_even_part`・`casK_odd_part` など。
   - `normSq_rootNum`：Part 12 の `normSq_gaussSum` から。Lean で確認。
   - `exists_primitive_odd_three`：Part 115・163・167 から。Lean で確認。
   - `exists_primitive_even_five`：同じ補題から。
-  - `parFac`・`rootNum_eq`：Part 194 の `gs`、付録 A の Part 2 の `parity_weight` から。
-- **一般化**：`parFac_of_even`・`parFac_of_odd` は、付録 A の Part 2 の `parity_weight`（r = 1）から [NeZero N] を外した形です（照合者の判定）。
+  - `parFac`・`rootNum_eq`：Part 194 の `gs`、 Part 2（PAG2.lean）の `parity_weight` から。
+- **一般化**：`parFac_of_even`・`parFac_of_odd` は、 Part 2（PAG2.lean）の `parity_weight`（r = 1）から [NeZero N] を外した形です（照合者の判定）。
 - **前の鎖に見つからなかったもの（網羅ではない）**：変換としての定義（`hartley`・`JH`）と、原始性を外したときの反例（`removal_counterexample` など 3 件）。
 
@@ -63,5 +63,5 @@
 
 - **A・B（Lean で確認、6 件）**
-  - `charU`（定義）：Part 1 の `PAG.charFun` に `MulChar.toUnitHom` を通したものと同じ関数。照合者は B（推定、確信度 低）としました。
+  - `charU`（定義）：Part 1（PAG.lean）の `PAG.charFun` に `MulChar.toUnitHom` を通したものと同じ関数。照合者は B（推定、確信度 低）としました。
   - `eq_one_of_two`：Part 194 の `level_two_trivial` から。
   - `not_isPrimitive_one_of_two_le`・`charU_one_mem_Vimprim`：Part 191 の `ne_one_of_isPrimitive` から。
@@ -69,5 +69,5 @@
   - `Vprim_two`：Part 26 の `no_prim_mod_two` から。
 - **C（照合者 R3 の判定、2 件。Lean では未確認）**
-  - `ip_charU`：Part 214 の `sum_units_char` と、付録 A の Part 3 の `conj_apply_eq_inv` から。
+  - `ip_charU`：Part 214 の `sum_units_char` と、 Part 3（PAG3.lean）の `conj_apply_eq_inv` から。
   - `Vprim_ne_bot_prime`：確信度 低。
 - **範囲の中**：`ip`（定義）は Part 249 の `ipG` と同じ定義です（`rfl`）。
@@ -93,5 +93,5 @@
 - **C（照合者 R5 の判定、3 件。Lean では未確認）**：`norm_char_unit`、`norm_cross`、`parFac_prodChar`（Part 194 の `gs_combine` と同じ形）。
 - **境目**：`rootNum_prodChar` は照合者の判定で D（C との境目）です。中身は Part 189 の `z_mul_coprime`・`gaussSum_mul_coprime` に偶奇の因子のずれを足したもので、私の見立ては C 寄りです（Lean ではつないでいない）。
-- **関係**：`cross_eq_sign_of_rootNum_one` の 3 つの仮定は、実原始指標なら Part 194 の `gauss_sign_real` から成り立ち、結論は `real_reciprocity` の式と同値です（`crossSign` と `rs` が同じ値なので。数学として。Lean ではつないでいない）。
+- **関係**：`cross_eq_sign_of_rootNum_one` の 3 つの仮定は、実原始指標なら Part 194 の `gauss_sign_real` から成り立ち、結論は `real_reciprocity` の式と同値です（`crossSign` と `rs` が同じ値で、どちらも ±1 なので。数学として。Lean ではつないでいない）。
 - **「Lean にしていない」とした (i) について**：法 M·N のすべての指標が積の形に一意に書けることは、Part 190 の `decomp`（存在）と Part 232 の `charMul_injective`（一意性）を合わせると出ます（監査者の読み。Lean ではつないでいない）。
 - **前の鎖に見つからなかったもの（網羅ではない）**：UA1・phaseA1 の形の式、例 3 件、一般の指標での条件つきの文。
@@ -113,5 +113,6 @@
   - 定義の一致：`casKer_eq_casK`（定義から直接）、`rootNum_eq_zN_div_gs`、`charU_eq_charFun`、`ip_eq_ipG`、`crtMap_eq_param`、`crossSign_eq_rs`
   - 定理：`inv_apply_units_inv_of_PAG3`、`sum_mul_stdAddChar_neg_of_PAG3`、`not_isPrimitive_one_of_two_le_of_PAG195`、`charU_one_mem_Vimprim_of_PAG195`、`gaussSum_inv_of_PAG9`、`not_isPrimitive_one_prime_of_PAG32`、`Vprim_two_of_PAG30`、`prodChar_neg_one_of_PAG204`
-- **C の標本**（`SampleC2.lean`、6 件）：`normSq_rootNum`、`rootNum_one_of_eq_one`、`units_eq_of_coprime_parts`、`exists_primitive_odd_three`、`hartley_one`、`casKer_eq`。どれも前の宣言から数行で示せました（`hartley_one` は約 20 行で、うち半分は偶奇の場合分け）。
+- **C の標本**（`SampleC2.lean`、6 件）：`normSq_rootNum`、`rootNum_one_of_eq_one`、`units_eq_of_coprime_parts`、`exists_primitive_odd_three`、`hartley_one`、`casKer_eq`。標本は無作為ではなく、Lean で確かめやすいものと、主な主張（Hartley の部分、W の正規化）を支えるものを選びました。5 件は 5〜8 行で示せました。`hartley_one` は約 20 行（半分は偶奇の場合分け）で、C と D の境目にあたります。
+- **「同じ文（両向き）」の 14 組は、`simp_all` の分岐を使わずに通ることも確かめました**（`lean/MechChecksA.lean`、28 定理。`exact` か、`apply` と仮定だけ。照合者 F2 の指摘）。
 - いずれも rc 0 です。64 定理すべてに `#print axioms` を付け、公理が propext・Classical.choice・Quot.sound だけであることを確かめました。
 - 1 回目の `ManualChecks.lean`・`SampleC.lean` は、一部の定理で対象にない仮定（NeZero N）を足していました（照合者 F の指摘 #3）。2 回目の版で、対象の型そのものに直しました。
@@ -133,5 +134,5 @@
   - 機械的な確認で通った組は、すべて照合者も挙げていました。
   - 前の鎖に対する照合者の A・B の判定と、範囲の中の `ip` は、すべて Lean で確かめられました。範囲の中の B 8 件は、`ip_smul_right` を除いて Lean では確かめていません。
-  - `charU` は、照合者の判定（B、推定）より強く、同じ関数でした。
+  - `charU` は、照合者の判定（B、推定）より強く、`PAG.charFun` に `toUnitHom` を通したものと同じ関数でした。
 - **機械的な確認の弱点（照合者の指摘）**
   - 鎖に import されていない PAG3 を、初めは対象に含めていませんでした。
@@ -140,9 +141,9 @@
 - **予想との比較**（`expected_before_review.md`）
   - 当たり：A・B は Part 252 と 256 に集中する。Part 256 の前半の 7 宣言、Part 252 の χ(−1) の補題 3 つ、`eq_one_of_two`、`normSq_rootNum`（C）。
-  - 外れ：A・B の件数は「10〜15」と予想しましたが、実際は 26 件でした。Hartley の部分は「D か、前の DFT の結果の C（低）」と予想しましたが、照合者の判定では付録 A の Part 3 の命題 2.8 から数行でした。私の道具は PAG3 を見ていませんでした。Part 253 のユニタリ性（C を予想）と Part 254 の `condPart`（C を予想）は、照合者の判定では D でした。
+  - 外れ：A・B の件数は「10〜15」と予想しましたが、実際は 26 件でした。Hartley の部分は「D か、前の DFT の結果の C（低）」と予想しましたが、照合者の判定では Part 3（PAG3.lean）の命題 2.8 から数行でした。私の道具は PAG3 を見ていませんでした。Part 253 のユニタリ性（C を予想）と Part 254 の `condPart`（C を予想）は、照合者の判定では D でした。
 
 ## 5. 評価の見直し
 
-- **Part 252**：位置づけ「既知の事実の書き直し（再導出）」は変わりません。照合者の判定と Lean で確かめた 2 件から、鎖の中では付録 A の Part 3 の命題 2.8 の再導出にあたると見ます（確信度：中〜高）。
+- **Part 252**：位置づけ「既知の事実の書き直し（再導出）」は変わりません。照合者の判定と Lean で確かめた 2 件から、鎖の中では Part 3（PAG3.lean）の命題 2.8 の再導出にあたると見ます（確信度：中。中心 7 件のうち Lean で確かめたのは 2 件で、残り 5 件は照合者の確信度が低いため）。
 - **Part 256**：位置づけ「既知の事実の Lean 化（再導出）」は変わりません。加えて、前半は鎖の中の定理の示し直しでした（Lean で確認）。Part 256 の着手前の文書の「形式化としては新しい可能性があります」は誤りでした。
 - **Part 253・254**：作用素の文の大半は、前の鎖に見つかりませんでした（網羅ではない）。補題の一部が重複でした。
@@ -150,5 +151,5 @@
 - **兆候 4（初等的な部品だけ）**：8 パート連続のままです。新しいパートは始めていません。
 - **兆候 1 の内側版**：自前の名前の定義が、自分の鎖の既存の定義と一致していました（`prodChar`・`crtMap`・`charU`・`ip` ほか）。
-- **第 8 の型（規約）**：Part 252・253 の記録に、ファイル番号を Part 番号として書いた取り違えがありました（「Part 16」は正しくは Part 12 = PAG16、「Part 218」は正しくは Part 214 = PAG218）。照合者 F の指摘と、参照の機械的な点検（`check_part_refs.py`）で見つけ、直しました。
+- **第 8 の型（規約）**：Part 249・252・253 の記録に、ファイル番号を Part 番号として書いた取り違えがありました（「Part 16」は正しくは Part 12 = PAG16、「Part 218」は正しくは Part 214 = PAG218。Part 249 の行の `dil_one`・`dil_dil` も PAG218 の宣言）。さらに私自身が、PAG.lean・PAG2・PAG3 をまとめて「付録 A」と書いていました。xlsx では、これらのファイルの定理は本文の定理 2.6・4.5、命題 2.8 と付録 A.2 の注記で、「付録 A」は一部だけです。F2 の後に「Part n（PAGn.lean）」に直しました。照合者 F の指摘と、参照の機械的な点検（`check_part_refs.py`）で見つけ、直しました。
 
 ## 6. 前の鎖の中どうしの重複（範囲外、記録だけ。直していない）
@@ -175,5 +176,5 @@
   - `castHom_neg_one`（Part 194）、`changeLevel_neg_one`（Part 200）、`unitsMap_neg_one`（Part 33）
   - `card_units_filter`（Part 141）と `card_isUnit`（Part 210）
-  - `conj_apply_eq_inv`（付録 A の Part 3）と `conj_inv_apply`（Part 209）
+  - `conj_apply_eq_inv`（Part 3（PAG3.lean））と `conj_inv_apply`（Part 209）
   - `sq_isPrimitive`（Part 5）と `sq_isPrimitive'`（Part 6）
   - `no_prim_mod_two`（Part 26）と `no_prim_mod2`（Part 81）
@@ -207,6 +208,11 @@
   - もとからある文のファイル番号の取り違え。
   
-  24 件すべてを直すか、直した形で受け入れました（`outputs/F_output.md` と、2 回目の直しの差分）。
-- **照合者 F2（2 回目の直しの照合）**：これから行います。F2 の後に直したものは、照合を受けていないものとして記録します。
+  2 回目の直しで 22 件が直り、#14・#15 は一部でした（照合者 F2 の判定。下の項目）。
+- **照合者 F2（2 回目の直しの照合）**：F の 24 件のうち 22 件が直り、#14・#15 は一部でした。形式文の変更はありませんでした。新しい指摘は 16 件です（`outputs/F2_output.md`）。
+  - #14 の残り：parFac_of_odd、前の鎖への一般化（`ipG` など）、範囲の中の B・C には、照合者に渡した根拠の文書に形式文を足していません。どれも照合者の判定として記録したもので、Lean の根拠は主張していません。
+  - #15 の残り：PAG260 の冒頭の「すべて前の鎖にあった」は、F2 の後に「前の鎖にあるか、前の宣言から直ちに出る（A・B）」に直しました（新 6）。
+  - 新 2：F2 の後に、Part 249 の行の `dil_one`・`dil_dil` が PAG218（Part 214）の宣言であることを、全宣言の書き出し（`decls_all.jsonl`）で確かめました。直しは正しかった。
+  - 新 15：F2 の後に、「同じ文（両向き）」の 14 組が `simp_all` の分岐なしでも通ることを確かめました（`MechChecksA.lean`、28 定理、error 0）。
+- **F2 の後の直し（記録だけ。照合は受けていない）**：新 1〜16 への対応（件数の書き方、A と B のまとめ方、`charU` の書き方、確信度の理由、標本の選び方など）と、私自身の取り違えの直しです。私は PAG.lean・PAG2・PAG3 をまとめて「付録 A」と呼んでいましたが、xlsx ではこれらの定理は本文の定理 2.6・4.5、命題 2.8 と付録 A.2 の注記で、「付録 A」は一部だけでした。Lean の docstring と冒頭、ノート、報告、引き継ぎメモ、xlsx（69 セル）で「Part n（PAGn.lean）」に直しました。直したあと、形式文が同じこと、組み立て直した .out が同一であること、xlsx の再計算エラーが 0 であることを確かめました。
 - **網羅していません。** 照合者は全宣言の文の 1〜3 割しか読めていません（R1 約 1 割、R2 約 3 割、R3・R5 約 2.5 割、R4 は読んだ範囲を明記）。機械的な候補選びは上位 20 件までで、名前の違う同じ概念を拾いにくい弱点があります。見落としは残っていると考えます（確信度：中）。
 - **確認の強さに差があります。** Lean で確かめたのは、前の鎖に対する A・B の 26 件と、C の標本 6 件です。残りの C 14 件は照合者の判定です。
--- before/pag2_part249_idele_class_density.md
+++ after/pag2_part249_idele_class_density.md
@@ -356,5 +356,5 @@
 ## 8. 内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）
 
-- 前の鎖（PAG.lean〜PAG252.lean と、鎖に import されていない付録 A・PAG 2.0 の初めのファイル PAG3・PAG5・PAG6）に、このパートの宣言と同じ文・直ちに出る文・数行で出る文は見つからなかった（照合者 R1、機械的な照合）。
+- 前の鎖（PAG.lean〜PAG252.lean と、鎖に import されていない、最初の形式化の Part 3（PAG3.lean）と PAG 2.0 の初めのファイル PAG5・PAG6）に、このパートの宣言と同じ文・直ちに出る文・数行で出る文は見つからなかった（照合者 R1、機械的な照合）。
 - 一般化の関係（示し直しではなく、前の文を特別な場合として含む形）：`ipG` は Part 48 の `ip`・Part 225 の `herm`（法 N の上の内積）を任意の有限型に広げた定義。`ipG_smul_left`・`ipG_smul_right` は Part 51 の `ip_smul_left`・`ip_smul_right`、Part 213 の `inner_smul_left'`、Part 225 の `herm_smul_left`・`herm_smul_right` を含む（前の文がこちらから出ることを Lean で確認）。照合者の判定では、`kUnit_mul_natCast`・`unitsMap_kUnit` は Part 33 の `five_val`・`unitsMap_five` の一般化、`mem_dilCommute_of_prime` は Part 220 の `mem_dilCommute` を強めた形。
 - 定理 2.6 の部分は、基本ファイル（Part 1、PAG.lean）の `eigen_of_commute`・`real_sector_sign` を使って組み立てている（示し直しではない）。
--- before/pag2_part252_hartley_gluing.md
+++ after/pag2_part252_hartley_gluing.md
@@ -7,5 +7,5 @@
   - 着手前の 4 点は `pag2_next_question_preregistration.md` の Q1 です。残余は空で、残るのは計算の細部（モノグラフ §1.3 の主張 (2)「A1 のもとで U = JH_N」の確認）だけ、という判定でした。著者はその Lean 化を選びました。
   - **記法の注意。** このノートの H_N は正規化しない離散 Hartley 変換で、Lean で扱ったのは J∘H_N/√N です。モノグラフの「JH_N」の正規化は、本文で確かめる必要があります（本文は手元にありません）。
-  - 盲検の問いテストは済んでいます（同じ文書の §6 の S1：標準的な演習、Hartley の形の文献は見つからず）。自分の鎖には付録 A の Part 3（PAG3.lean）の命題 2.8 があった（内部照合 2026-11-14、§9）。
+  - 盲検の問いテストは済んでいます（同じ文書の §6 の S1：標準的な演習、Hartley の形の文献は見つからず）。自分の鎖には Part 3（PAG3.lean）の命題 2.8 があった（内部照合 2026-11-14、§9）。
 - **問い（幾何の言葉で）。** ねじれた貼り合わせの読みでは、無限大の側と無限小の側（切断した円筒の両端）を境界ユニタリ U で貼り合わせます。A1 のもとで、その貼り合わせの写像は何か。
 - **結論（Lean）。** H_N は離散 Hartley 変換 (H_N f)(y) = Σ_x f(x)(cos + sin)(2π xy/N)、J は単数の上の反転 (Jg)(u) = g(u⁻¹) です。
@@ -195,11 +195,11 @@
   - `neg_one_mul_self`：Part 5 の `chi_neg_one_sq`、Part 25 の `chi_neg_one_sq'` と同じ文。
   - `isPrimitive_of_prime_of_ne_one`：Part 167 の `primitive_of_ne_one` と同じ文。
-  - `casKer`：付録 A の Part 3（PAG3.lean）の `casK` と同じ値（式の書き方は違う）。
+  - `casKer`：Part 3（PAG3.lean）の `casK` と同じ値（式の書き方は違う）。
 - **前の宣言から直ちに出るもの（B。Lean で確認）**：
   - `rootNum`：Part 192 の `zN` を Part 194 の `gs` で割ったものと同じ値。
-  - `inv_apply_units_inv`・`sum_mul_stdAddChar_neg`：付録 A の Part 3 の `apply_inv_eq_inv_apply`・`sum_neg_twist`（x = 1）から 1 行。
-- **Hartley の部分（照合者 R2 の判定）**：付録 A の Part 3（PAG3.lean。鎖に import されていない初めのファイル）には、`casK`（Hartley の核）、`casK_even_part`・`casK_odd_part`、`sum_neg_twist`、`hartley_char`（Σ_y cas(xy)χ(y) = (偶 1／奇 −i)·Σ_y e(xy/N)χ(y)。xlsx では「命題 2.8」）、`apply_inv_eq_inv_apply` がある。照合者 R2 の判定では、このパートの Hartley の部分の中心の 7 件（`hartley_one`・`hartley_eq_of_isPrimitive`・`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`・`casKer_eq`）は、これらから数行で出る（C）。うち `hartley_one` と `casKer_eq` は Lean で確認した（`audit_internal/lean/SampleC2.lean`）。残り 5 件は照合者の確信度が低く、Lean では確かめていない。
-- **そのほかの C（照合者 R2 の判定）**：`normSq_rootNum`（Part 12 の `normSq_gaussSum` から。Lean で確認）、`exists_primitive_odd_three`（Part 115・163・167 から。Lean で確認）・`exists_primitive_even_five`、`parFac`・`rootNum_eq`（Part 194 の `gs`、付録 A の Part 2 の `parity_weight`）。`parFac_of_even`・`parFac_of_odd` は付録 A の Part 2 の `parity_weight`（r = 1）から [NeZero N] を外した形。
+  - `inv_apply_units_inv`・`sum_mul_stdAddChar_neg`：Part 3（PAG3.lean）の `apply_inv_eq_inv_apply`・`sum_neg_twist`（x = 1）から 1 行。
+- **Hartley の部分（照合者 R2 の判定）**：Part 3（PAG3.lean。PAG 2.0 より前の最初の形式化のファイルで、鎖に import されていない）には、`casK`（Hartley の核）、`casK_even_part`・`casK_odd_part`、`sum_neg_twist`、`hartley_char`（Σ_y cas(xy)χ(y) = (偶 1／奇 −i)·Σ_y e(xy/N)χ(y)。xlsx では「命題 2.8」）、`apply_inv_eq_inv_apply` がある。照合者 R2 の判定では、このパートの Hartley の部分の中心の 7 件（`hartley_one`・`hartley_eq_of_isPrimitive`・`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`・`casKer_eq`）は、これらから数行で出る（C）。うち `hartley_one` と `casKer_eq` は Lean で確認した（`audit_internal/lean/SampleC2.lean`）。残り 5 件は照合者の確信度が低く、Lean では確かめていない。
+- **そのほかの C（照合者 R2 の判定）**：`normSq_rootNum`（Part 12 の `normSq_gaussSum` から。Lean で確認）、`exists_primitive_odd_three`（Part 115・163・167 から。Lean で確認）・`exists_primitive_even_five`、`parFac`・`rootNum_eq`（Part 194 の `gs`、 Part 2（PAG2.lean）の `parity_weight`）。`parFac_of_even`・`parFac_of_odd` は Part 2（PAG2.lean）の `parity_weight`（r = 1）から [NeZero N] を外した形。
 - **前の鎖に見つからなかったもの（網羅ではない）**：変換としての定義（`hartley`・`JH`）と、原始性を外したときの反例（`removal_counterexample`・`removal_counterexample_four`・`removal_counterexample_normSq`）。
-- §1 の位置づけ「既知の事実の書き直し（再導出）」は変わらない。照合者の判定と Lean で確かめた 2 件から、鎖の中では付録 A の Part 3 の命題 2.8 の再導出にあたると見る（確信度：中〜高）。冒頭の「Hartley の形の文献は見つからず」は外の文献についての記録で、自分の鎖には命題 2.8 があった。
+- §1 の位置づけ「既知の事実の書き直し（再導出）」は変わらない。照合者の判定と Lean で確かめた 2 件から、鎖の中では Part 3（PAG3.lean）の命題 2.8 の再導出にあたると見る（確信度：中。中心 7 件のうち Lean で確かめたのは 2 件で、残り 5 件は照合者の確信度が低いため）。冒頭の「Hartley の形の文献は見つからず」は外の文献についての記録で、自分の鎖には命題 2.8 があった。
 - 限界：機械的な候補選び（型に現れる定数の近さ、上位 20 件）と Lean での直接の当てはめ、照合者の通読による。照合者は Grep が使えず、全宣言の文（約 2 万 2 千行）の 1〜3 割しか読めていない。「見つからなかった」は「ない」の証明ではない。
--- before/pag2_part253_primitive_operator.md
+++ after/pag2_part253_primitive_operator.md
@@ -190,5 +190,5 @@
 - 前の定義と同じもの（Lean で確認）：`charU` は基本ファイル（Part 1）の `PAG.charFun` に `MulChar.toUnitHom` を通したものと同じ関数、`ip` は Part 249 の `ipG` の G = (ZMod N)ˣ の場合と同じ定義（範囲の中）。このパートはそれらを使わずに定義し直していた。
 - 前の定理から直ちに出るもの（Lean で確認）：`eq_one_of_two`（Part 194 の `level_two_trivial`）、`not_isPrimitive_one_of_two_le`・`charU_one_mem_Vimprim`（Part 191 の `ne_one_of_isPrimitive`）、`not_isPrimitive_one_prime`（Part 28 の `prim_level_p_iff`）、`Vprim_two`（Part 26 の `no_prim_mod_two`）。
-- 照合者 R3 の判定で数行で出るもの（C）：`ip_charU`（Part 214 の `sum_units_char` と付録 A の Part 3 の `conj_apply_eq_inv`）、`Vprim_ne_bot_prime`（確信度 低）。範囲の中の関係（Part 249・252 から。照合者の判定、Lean では未確認）：C は `JHL`・`TopL_charU`・`Vprim_ne_bot_three`・`TopL_charU_one_four`（低）、B は `ip_smul_smul`・`rootNum_ne_zero`。
+- 照合者 R3 の判定で数行で出るもの（C）：`ip_charU`（Part 214 の `sum_units_char` と Part 3（PAG3.lean）の `conj_apply_eq_inv`）、`Vprim_ne_bot_prime`（確信度 低）。範囲の中の関係（Part 249・252 から。照合者の判定、Lean では未確認）：C は `JHL`・`TopL_charU`・`Vprim_ne_bot_three`・`TopL_charU_one_four`（低）、B は `ip_smul_smul`・`rootNum_ne_zero`。
 - 前の鎖に見つからなかったもの（網羅ではない）：単数の上の作用素 T（`TopL`）、V_prim と V_imprim の分解と直交、V_prim の上のユニタリ性と一意性、V_imprim の上で等長でないこと。
 - 限界：機械的な候補選び（型に現れる定数の近さ、上位 20 件）と Lean での直接の当てはめ、照合者の通読による。照合者は Grep が使えず、全宣言の文（約 2 万 2 千行）の 1〜3 割しか読めていない。「見つからなかった」は「ない」の証明ではない。
--- before/pag2_part257_preregistration.md
+++ after/pag2_part257_preregistration.md
@@ -15,5 +15,5 @@
   2. **Part 256 が「観察にとどめる」とした相互法則は、Part 194 で示してありました。** `real_reciprocity`（PAG198）は、互いに素な法の実原始指標で χ₁(N₂)χ₂(N₁) を符号で決める定理で、W = 1 の仮定は使っていません（仮定は互いに素・原始・実の指標）。xlsx の記述では、ガウスの符号決定（`gauss_sign_aux`・`gauss_sign_real`）と同時の帰納法で示されています。Part 256 の `cross_eq_sign_of_rootNum_one` が外から入れた 3 つの仮定（W = 1）は、実原始指標なら Part 194 の定理から出ます（数学として。Lean ではつないでいない）。Part 256 の着手前の盲検が挙げた「循環の危険」には、Part 194 がこの形で答えています（証明の中身は確かめていない）。
   3. **候補 P2 の (a)(b) は Part 183 の定理と同じ内容です。** `single_root_iff`（PAG187）は「法 p^c の原始指標で、τ/√(p^c) が 1 の冪根 ⇔ c ≥ 2 または ord χ = 2」です。W は τ/√(p^c) に 1 の冪根 i^{−a} を掛けたものなので、同じことです。
-  4. **候補 P1 の中身の大半も鎖にあります。** 2 つの法の分解は Part 189 の `z_mul_coprime`、多くの素数への分解は Part 192 の `z_hall`（ずれの因子は「1 の冪根が存在する」形だけ）です。P1 で鎖に新しいのは、交差項を明示した全素点の積の形、形 (II)、∞ の因子と符号の整理だけです。
+  4. **候補 P1 の中身の大半も鎖にあります。** 2 つの法の分解は Part 189 の `z_mul_coprime`、多くの素数への分解は Part 192 の `z_hall`（ずれの因子は「1 の冪根が存在する」形だけ）です。P1 で前の鎖に見つからなかったのは（網羅ではない）、交差項を明示した全素点の積の形、形 (II)、∞ の因子と符号の整理だけです。
   - **原因。** Part 252〜256 の照合（A・B・C、再照合 B2〜B4、盲検）は、どれも外の文献と Mathlib だけを相手にしていました。自分の鎖を検索する手順は、私の着手前の手順にもパートを閉じる手順にもありませんでした。CLAUDE.md §7 の背景（気づかないまま再構築した）と同じことが、自分の過去の結果に対して起きていました。
   - **Part 256 の記録の誤り。** ノートの「互いに素な法でのガウス和の乗法性は Mathlib と Isabelle AFP に見つかりませんでした」は字面どおりには正しいのですが、鎖にあったことを書いていません。Part 256 の着手前の文書の「形式化としては新しい可能性があります」は誤りでした。直し方は §9 で伺います。
@@ -174,2 +174,9 @@
 
 - 結論の 2 の「仮定はありません」は強すぎたので、「W = 1 の仮定は使っていません（仮定は互いに素・原始・実の指標）」に直しました。
+
+## 12. 著者の判断（2026-11-14 20:59）
+
+- 次の作業：**P1 で Part 257 を始める。**
+- 開始条件 2（方向βの登録ファイルとの突き合わせ）：**著者の判断で、条件 2 を保留のまま Part 257 を始める。** 登録ファイルはまだ届いておらず、突き合わせは済んでいない。届いたら Part 255 の結果と 1 項目ずつ突き合わせる（この判断は、13:2x の「ファイルが届くまで待つ」を置き換える）。
+- 内部照合（2026-11-14 からの必須の手順）は、着手の前とパートを閉じる前の 2 回行う。
+- 追記（2026-11-14 21:45）：登録ファイルの全文が届き、突き合わせて開始条件 2 を閉じた（`pag2_beta_registration_check.md`）。
--- before/PAG2_handoff_internal_audit.md
+++ after/PAG2_handoff_internal_audit.md
@@ -3,6 +3,6 @@
 ## 進め方のルール（そのまま継続）
 - **（2026-11-14 著者の判断）内部照合を必須にする**：着手前の 4 点とパートを閉じる条件に、自分の鎖（xlsx の「定理と証明」と Lean の全宣言）の検索と、Lean での一致の確認を足す。CLAUDE.md への条文化は著者側（条文の案は `pag2_internal_audit_249_256.md` の付録）。道具は `audit_internal/`（`lean/Extract2.lean`：全宣言の定数、`shortlist2.py`：候補選び、`lean/DupCmd2.lean`：`#dupcheck`・`#defeqcheck`）。鎖に import されていない初めのファイル（PAG3・PAG5・PAG6）も対象に含める。照合者には Grep の代わりに読める形（ファイルごとの文）を渡すか、読み取り専用の grep を許す（今回は Grep が使えず、照合者は全宣言の文の 1〜3 割しか読めなかった）。
-- **（2026-11-14 内部照合の教訓）Part 番号とファイル番号を取り違えない**：PAG 2.0 の Part n は PAG(n+4).lean。PAG.lean・PAG2・PAG3・PAG4 は付録 A の Part 1〜4。名前空間 `PAG.PartNNN` の NNN はファイル番号。Part 252・253 の記録に「Part 16」（正しくは Part 12 = PAG16）、「Part 218」（正しくは Part 214 = PAG218）の取り違えがあった。
-- **（2026-11-14 内部照合の教訓）新しい定義を作る前に、同じ式の定義が鎖にないか探す。** `prodChar` は Part 195 の `cmul`・Part 232 の `charMul` と同じ定義（3 つ目の名前）、`crtMap` は Part 189 の `param`、`charU` は Part 1 の `PAG.charFun`、Part 253 の `ip` は Part 249 の `ipG` と同じだった。既にある定理（例：Part 189 の `gaussSum_mul_coprime`）は使い、示し直さない。
+- **（2026-11-14 内部照合の教訓）Part 番号とファイル番号を取り違えない**：PAG 2.0 の Part n は PAG(n+4).lean。PAG.lean・PAG2・PAG3・PAG4 は PAG 2.0 より前の最初の形式化の Part 1〜4（本文の定理 2.6・4.5、命題 2.8、付録 A.2 の注記などを含む。「付録 A」とまとめて呼ばない）。名前空間 `PAG.PartNNN` の NNN はファイル番号。Part 249・252・253 の記録に「Part 16」（正しくは Part 12 = PAG16）、「Part 218」（正しくは Part 214 = PAG218）の取り違えがあった。
+- **（2026-11-14 内部照合の教訓）新しい定義を作る前に、同じ式の定義が鎖にないか探す。** `prodChar` は Part 195 の `cmul`・Part 232 の `charMul` と同じ定義（3 つ目の名前）、`crtMap` は Part 189 の `param`、`charU` は Part 1（PAG.lean）の `PAG.charFun`、Part 253 の `ip` は Part 249 の `ipG` と同じだった。既にある定理（例：Part 189 の `gaussSum_mul_coprime`）は使い、示し直さない。
 - **（2026-11-13 著者側の補足3。選択の委任に基づく著者側の決定。「著者の選択待ち」にはしない）Part 257 の開始条件（すべて満たすまで始めない）**：
   1. 未照合残件の再照合（Part 252：照合後の修正文面、追加項目 22（法 4 の反例）。Part 254：照合 B 後の修正文面、追加 7 項目。Part 255：照合 B 後に足した定理 4 個。Part 256：照合の後に足した法 39 の例）。→ **2026-11-14 に済み**（`pag2_reaudit_252_256.md`）。
@@ -1329,12 +1329,13 @@
 
 - きっかけ：Part 257 の着手前の文書（`pag2_part257_preregistration.md`）を書く途中で、Part 256 の `gaussSum_prodChar`・`isPrimitive_prodChar` が Part 189・190 の定理と同じ文だと分かった。著者が監査を選んだ（新しいパートは始めない）。
-- 方法：Part 249〜256 の宣言 334 件について、前の鎖（PAG.lean〜PAG252.lean と PAG3・PAG5・PAG6）の宣言 4279 件から候補を機械的に選び、一方を他方にそのまま当てる確認を約 1 万 3 千組。独立の照合者 5 人（形式文の全文、Read だけ）。前の鎖に対する A・B の 26 件をすべて Lean で確かめ（直接の当てはめの組を名前つきにした `audit_internal/lean/MechChecks.lean` と、手で示した `ManualChecks2.lean`。対象の型そのものを `type_of%` で述べる）、C の判定から 6 件を標本として Lean で確かめた（`SampleC2.lean`、すべて当たり）。
+- 方法：Part 249〜256 の宣言 334 件について、前の鎖（PAG.lean〜PAG252.lean と PAG3・PAG5・PAG6）の宣言 4279 件から候補を機械的に選び、一方を他方にそのまま当てる確認を約 1 万 3 千回（組ごとに両向き）。独立の照合者 5 人（形式文の全文、Read だけ）。前の鎖に対する A・B の 26 件をすべて Lean で確かめ（直接の当てはめの組を名前つきにした `audit_internal/lean/MechChecks.lean` と、手で示した `ManualChecks2.lean`。定理は対象の型そのものを `type_of%` で述べ、定義の一致は値の等式か `HEq rfl` で確かめる）、C の判定から 6 件を標本として Lean で確かめた（`SampleC2.lean`、すべて当たり）。
 - 結果（前の鎖に対して）：
-  - Part 252：A・B が 7（χ(−1) の補題 3 つは Part 5・21・25・77・167 と同じ文、`casKer` は付録 A の Part 3 の `casK` と同じ値、`rootNum` は Part 192 の `zN` ÷ Part 194 の `gs` と同じ値）。C が 12。**照合者の判定では、Hartley の部分の中心の 7 件は付録 A の Part 3（PAG3.lean、命題 2.8 `hartley_char`）などから数行で出る**（`hartley_one`・`casKer_eq` は Lean で確認、5 件は確信度 低）。
-  - Part 253：A・B が 6（`charU` は Part 1 の `PAG.charFun` に `toUnitHom` を通したものと同じ関数、ほかは Part 26・28・191・194 から直ちに出る）。C が 2。範囲の中で `ip` は Part 249 の `ipG` と同じ定義。
+  - Part 252：A が 4（`inv_apply_neg_one`・`neg_one_mul_self` は Part 5・21・25・77 と、`isPrimitive_of_prime_of_ne_one` は Part 167 と同じ文、`casKer` は Part 3（PAG3.lean）の `casK` と同じ値）、B が 3（`rootNum` は Part 192 の `zN` ÷ Part 194 の `gs` と同じ値、`inv_apply_units_inv`・`sum_mul_stdAddChar_neg` は Part 3（PAG3.lean）から 1 行）。C が 12。**照合者の判定では、Hartley の部分の中心の 7 件は Part 3（PAG3.lean。命題 2.8 `hartley_char`）などから数行で出る**（`hartley_one`・`casKer_eq` は Lean で確認、5 件は確信度 低）。
+  - Part 253：A・B が 6（`charU` は Part 1（PAG.lean）の `PAG.charFun` に `toUnitHom` を通したものと同じ関数、ほかは Part 26・28・191・194 から直ちに出る）。C が 2。範囲の中で `ip` は Part 249 の `ipG` と同じ定義。
   - Part 254：B が 1（`gaussSum_inv`）、C が 2。
   - Part 256：A・B が 12（前半はほぼ全部が Part 189・190・195・232 の示し直し。`crossSign` は Part 194 の `rs` と同じ値）。C が 3。相互法則は Part 194 の `real_reciprocity` で、W = 1 の仮定を使わずに（互いに素・原始・実の指標のもとで）示してある。
   - Part 251：C が 1。Part 249・250・255：前の鎖との重複は見つからなかった（網羅ではない）。
 - 直したもの：PAG256〜PAG258・PAG260 の docstring と PAG255〜PAG258・PAG260 の冒頭の説明（形式文は変えていない。PAG255〜PAG260 を組み立て直し、.out は同一）、Part 249〜256 のノート（「内部照合」の節）、Part 256 の着手前の文書の訂正、xlsx（Part 251〜254・256 の行の「証明の方針」43 か所、Part 252・253・256 の見出し、手順 278、メモ）。直しの照合（照合者 F、指摘 24 件）を受けて 2 回目の直しをした（注記の強さ、A と B の書き分け、もとからある文のファイル番号の取り違え：Part 16 → Part 12（PAG16）、Part 218 → Part 214（PAG218））。2 回目の直しの照合は照合者 F2。
+- 直しの照合：照合者 F（1 回目の直し、指摘 24 件）、照合者 F2（2 回目の直し。22 件が直り、#14・#15 は一部、新しい指摘 16 件、形式文の変更なし）。F2 の後の直し（新しい指摘への対応と、PAG.lean・PAG2・PAG3 を「付録 A」とまとめて呼んでいた取り違えの直し）は記録だけで、照合は受けていない。「同じ文（両向き）」の 14 組は `simp_all` の分岐なしでも通る（`lean/MechChecksA.lean`）。出力は `audit_internal/outputs/`。
 - 限界：照合者は Grep が使えず、全宣言の文の 1〜3 割しか読めていない。機械的な候補選びは上位 20 件まで。「見つからなかった」は「ない」の証明ではない。
 - 前の鎖の中どうしの重複（範囲外、記録だけ）：`cmul`（Part 195）と `charMul`（Part 232）、χ(−1) の補題（Part 5・21・25・77）、`lam_pos`（Part 27・42・112）、`ip`（Part 48）と `herm`（Part 225）など。監査の報告の §6。
```
