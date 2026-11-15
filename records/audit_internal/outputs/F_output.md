## 1. 指摘の表

| # | 場所（ファイルと行） | 問題 | 直し方の案 | 確信度 |
|---|---|---|---|---|
| 1 | PAG256.lean 冒頭 22–24 行（fixes_lean_diff.txt 22–24 行）、pag2_part252 ノート 194 行（notes 差分 62 行） | 「前の鎖に同じ文・同じ値の定義がある（Lean で確認）」の中に、evidence で B のものが入っている。`inv_apply_units_inv`（前の宣言から 1 行）、`sum_mul_stdAddChar_neg`（x = 1 にして積を入れ替えたもの）、B（値）の `rootNum`（zN ÷ gs、2 つの定義の組み合わせ）の 3 件で、B を A に格上げしている。ノートは各項目の文（「から 1 行」）は正しく、見出しだけが同じ書き方 | 2 つに分ける。「同じ文・同じ値（A）：inv_apply_neg_one・neg_one_mul_self・isPrimitive_of_prime_of_ne_one・casKer」「直ちに出る（B）：rootNum（zN ÷ gs と同じ値）・inv_apply_units_inv・sum_mul_stdAddChar_neg」 | 高（冒頭）／中（ノート） |
| 2 | PAG260.lean 82・91 行の docstring、同 冒頭 53–54 行、ノート 256 の 161 行、xlsx 3531・3532、報告 11・89 行 | `cast_crtMap_fst`・`cast_crtMap_snd` の「Lean で確認」に、材料の中の根拠がない。evidence は「直接の当てはめ（S⇒T）」とするが、lean_mechanical_summary.md にこの 2 組の行がなく、ManualChecks・SampleC・DupCheck にもない。件数も合わない。報告 109 行は「30 組、前の鎖に対して 28 組、対象 15 件」だが、表は 27 行（前の鎖に対して 26 組、対象 13 件）。差はちょうどこの 2 組と範囲の中の 1 組にあたる | #dupcheck の出力から抜けた 3 行を表に戻す。出力が残っていなければ ManualChecks に 2 件足して組み立てる。それまでは「Lean で確認」を外す | 高（表にないこと）。実際に通ったかは分からない |
| 3 | PAG256.lean 164 行の docstring、同 冒頭 24 行、ノート 252 の 200 行、xlsx 3381、ManualChecks.lean 10–11・28–30 行 | 対象は `omit [NeZero N] in` で、NeZero を仮定しない（evidence 103 行）。一方 `inv_apply_units_inv_of_PAG3` は `variable {N : ℕ} [NeZero N]` の section の中にある。Lean 4 では、文に出る変数だけに依存するインスタンス引数は自動で文に入るので、`[NeZero N]` が仮定に入る。確かめたのは NeZero つきの弱い文で、対象そのものではない。同じ section の charU_eq_charFun なども、対象に NeZero がなければ同じ形になる（2 ≤ N の 2 件は差が 1 行） | section の外で `{N : ℕ}` だけにして組み立て直す。PAG3 の補題が NeZero を要るなら、注記を「NeZero N のもとで 1 行」にする | 中 |
| 4 | PAG260.lean 冒頭 49–50 行 | 「4 は Part 194 の gs_combine…と同じ内容で、5 はそれらから数行」と言い切っている。evidence では 4（parFac_prodChar）は C（照合者 R5、Lean 未確認）、5（rootNum_prodChar）は D（C との境目）。同じ段の 54 行では parFac_prodChar を「照合者の判定では…数行」と書いていて食い違う。括弧の「数行と新しいの境目」も誤りで、D は「見つからない」であって「新しい」ではない（xlsx 3542 も同じ） | 「照合者の判定では、4 は gs_combine と同じ形で数行（C）。5 は D（C との境目）で、監査者の見立ては C 寄り。どちらも Lean では未確認」 | 高 |
| 5 | xlsx 手順 278（fixes_xlsx_rows.md 192 行） | (a)「Part 249・250・255 は前の鎖に重複なし」は言い切り。報告 24・101 行は「見つかりませんでした」。(b)「そのまま当てる確認を約 1 万 3 千組」は誤り。12,776 は試行の回数で、組ごとに両向き・複数の戦術を試している。報告 109 行の「通った 76 回＝30 組」から見ても、回 ≠ 組 | (a)「重複は見つからなかった（網羅ではない）」 (b)「約 1 万 3 千回」 | 高 |
| 6 | xlsx 3383・3400 | 同じセルの中で、もとからある文と書き足した注記の Part 番号が食い違う。3383 はもとの文が「Part 16 の \|τ(χ)\|² = N」、注記が「Part 12 の normSq_gaussSum」。3400 はもとの文が「Part 218 の単数の上の指標の和」、注記が「Part 214 の sum_units_char」。evidence では PAG16（＝Part 12）と PAG218（＝Part 214）なので、もとの文がファイル番号を Part 番号として書いている（注記の側は正しい） | もとの文を「Part 12（PAG16）」「Part 214（PAG218）」に直す | 高 |
| 7 | ノート 252 の 193 行（太字）・203 行、報告 18 行（太字）・147 行、xlsx 252 の見出し | 「Hartley の部分は命題 2.8 とほぼ重なっていた」「鎖の中では命題 2.8 の再導出だった」を地の文で言い切っている。中心の 7 定理（hartley_*・JH_*・casKer_eq）は照合者 R2 の判定 C で、うち 5 件は確信度 低、Lean では未確認。Lean で確かめたのは casKer（値）・inv_apply_units_inv・sum_mul_stdAddChar_neg の補助の 3 件だけ | 出所と強さを付ける：「照合者 R2 の判定では…（中心の 7 件は C、うち 5 件は確信度 低。Lean では未確認）」 | 中 |
| 8 | PAG256.lean 冒頭 29 行、PAG260.lean 冒頭 56–57 行、ノート 252 の 202 行・253 の 193 行・254 の 232 行・256 の 166 行 | 「鎖に新しいもの／鎖に新しいのは」は「前の鎖にない」と言い切るのと同じ。根拠は照合者の判定 D と上位 20 件の候補選びだけで、照合者は全文の 1〜3 割しか読めていない。Lean の冒頭には限界の注意もない | 「前の鎖に見つからなかったもの（網羅ではない）」 | 中 |
| 9 | PAG256.lean 冒頭 25–26 行、PAG258.lean 冒頭 68 行 | 照合者の確信度が抜けている。PAG256 には Hartley の 7 件のうち「5 件は確信度 低」が書かれていない（ノート 201 行・xlsx・報告 53 行にはある）。また casKer_eq の前の宣言は、evidence では casK_even_part・casK_odd_part で、hartley_char ではない（xlsx 3373 は正しい）。PAG258 には phaseA1_one の「確信度 低」がない | 「（うち 5 件は確信度 低。casKer_eq は casK_even_part・casK_odd_part から）」「phaseA1_one（確信度 低）」を足す | 中 |
| 10 | PAG260.lean 306 行の docstring・冒頭 56 行、ノート 256 の 164 行、xlsx 3546、報告 17・94 行 | 「相互法則そのものは Part 194 で、仮定なしに示してある」は強すぎる。real_reciprocity（evidence 660–663 行）には互いに素・原始×2・χ² = 1×2 の 5 つの仮定がある。言えるのは「W = 1 の 3 つの仮定を使わずに」まで。docstring の「real_reciprocity と同じ式」も不正確で、2 つの式は crossSign = rs と rs = ±1 を通して同値になるのであって、同じ式ではない | 「W = 1 の仮定を使わずに（互いに素・原始・χ² = 1 のもとで）」「同値な式になる」 | 中 |
| 11 | xlsx 3546、ノート 256 の 164 行 | Lean の docstring にある「数学として。Lean ではつないでいない」が抜けていて、確かめた事実のように読める（evidence では D、関係の説明）。ノートの「ガウスの符号決定と同時の帰納法」「循環の危険への答えも Part 194 にあった」は証明の中身の話で、渡された形式文からは確かめられない | 「数学として。Lean ではつないでいない」を足す。証明の中身についての記述には出所を書く | 中（抜けていること）／低（証明の中身は分からない） |
| 12 | 報告 135 行（§4） | (a)「照合者の A・B の判定は、すべて Lean で確かめられました」とあるが、直前の表の A・B（計 35）は範囲の中を含む。範囲の中の B 8 件は ManualChecks にも表にもない（Part 250 の dense_logSet_coprime、Part 254 の ip_add_right・ip_smul_right・normSq_phaseA1、Part 255 の closure_logSet・sep_of_inf_unmeasured、Part 253 の 2 件）。(b)「8 件は手で示す必要がありました」は、35・110 行の「ManualChecks 14 件」と合わない | (a)「前の鎖に対する A・B 26 件と ip は」と範囲を書く (b)「定理 8 件・定義 6 件の計 14 件」 | 中 |
| 13 | 報告 118 行 | 「#print axioms は propext・Classical.choice・Quot.sound だけ」は根拠より広い。#print axioms の行は ManualChecks に 3 件（14 件中）、DupCheck に 3 件、SampleC に 0 件しかない。なお 3 ファイルに sorry がないことは読んで確かめた | 全件に #print axioms を足すか、出力のある 6 件に限って書く | 中 |
| 14 | evidence.md 全体（xlsx 3374–3392・3424・3434・3551・3552 などの注記） | 注記を足したのに形式文がないものがある。C の 12 件（hartley_eq_of_isPrimitive〜norm_cross）、一般化の 2 件（parFac_of_even・parFac_of_odd）、範囲の中の関係。前の宣言の名前と Part 番号を照合できない。特に xlsx 3551「Part 198 の normSq_chi_unit」と 3552「Part 195 の normSq_chi_natCast」は、同じ表に #6 の取り違えがあるので確かめたい | evidence に形式文を足す。Part 番号は名前空間（PAG.PartXXX はファイル番号）で確かめる | 高（形式文がないこと）／低（誤りがあるかは分からない） |
| 15 | PAG260.lean 冒頭 49 行 | 「上の 1〜3 と 6 の前半は前の鎖にあった」について、差分に項目 1〜8 の本文がなく、どの宣言を指すか照合できない。1〜3 に C の norm_char_unit・norm_cross が入るなら格上げになる | 宣言名で書き、A・B と C を分ける | 低（分からない） |
| 16 | PAG257.lean 冒頭 49–50 行、報告 19–23 行 | 「charU は PAG.charFun と同じ対象」は不正確。charFun は G →* ℂˣ を受け、charU は指標を受ける。一致するのは toUnitHom を通した関数（ManualChecks は funext と simp で示している）。docstring 101 行と xlsx 253 の見出しは正確。報告の「同じ対象に別の名前の定義が 4 つ」も、同じ値の casKer・crossSign を数えず charU を数えていて、基準がそろっていない | 「PAG.charFun に toUnitHom を通したものと同じ関数」 | 低 |
| 17 | PAG260.lean 240 行の docstring、ノート 256 の 162 行、xlsx 3542 | rootNum_prodChar の説明に、より近い前の宣言が挙がっていない。evidence には Part 189 の z_mul_coprime（√ で正規化した形の乗法性）があるのに、gaussSum_mul_coprime だけを挙げている | z_mul_coprime も挙げる | 低 |
| 18 | PAG260.lean 冒頭 55 行、ノート 256 の 6・163 行、報告 95 行 | 「(i) は decomp と charMul_injective・primEquiv で鎖にある」の内容は正しい（形式文から見て、存在は decomp、一意性は charMul_injective）。ただし 1 つの定理ではなく、evidence では監査者の読み（判定「関係」）で、照合者の判定でも Lean の確認でもない | 「2 つの定理を合わせると出る（監査者の読み。Lean ではつないでいない）」 | 低 |
| 19 | PAG255.lean 冒頭 20 行、ノート 255 の 211 行 | 「前の鎖」の範囲の書き方がそろっていない。PAG255 は「PAG.lean〜PAG254.lean」で、報告 6 行・ノート 249 の「〜PAG252.lean」と違う（PAG253・254 は範囲の中で、kUnit_congr は Part 249 から C）。ノート 255 の「Part 248 以前と付録 A」は、PAG5・PAG6 を含むかどうかが読み取りにくい | ノート 249 と同じ書き方にそろえ、範囲の中は分けて書く | 低 |
| 20 | xlsx 252 の見出し（fixes_xlsx_rows.md 9 行） | 「casKer は Part 3 の casK」で「付録 A の」が抜けていて、Part 3 = PAG7 と読める | 「付録 A の Part 3 の casK」 | 低 |
| 21 | ノート 251 の 196 行、ノート 255 の 212 行 | 範囲の中の B・C に、照合者の判定であることが書かれていない（Lean の根拠もない） | 「照合者の判定」を付ける | 低 |
| 22 | xlsx メモの追記（fixes_xlsx_rows.md 189 行の末尾）、報告 192 行 | 「PAG255〜PAG258・PAG260 の docstring」とあるが、PAG255 は冒頭の説明だけで docstring は変えていない。「Part 251〜256 の行」とあるが、Part 255 の行（3486〜3530）は変わっていない | 「PAG255 は冒頭のみ」「Part 251〜254・256 の行」 | 中 |
| 23 | PAG258.lean 冒頭 67 行 | 「conj_gaussSum から直ちに出る」とあるが、chi_neg_one_sq も要る（docstring・ノート・xlsx には書いてある） | 「conj_gaussSum と chi_neg_one_sq から」 | 低 |
| 24 | 報告 103 行 | Lean の根拠（表 3–7 行）は smul の 2 定理だけ。定義 ipG が ip・herm を広げたものであることには Lean の根拠がない | 「Lean で確認」は ipG_smul_left・ipG_smul_right の 2 定理に限る | 低 |

## 2. 抜け（A・B の注記が入っていない場所）

**抜けなし**（与えられた差分の範囲で）。
- Lean の docstring：A・B の 27 件（前の鎖に対する 26 件と、範囲の中の ip）すべてに入っている。PAG256 に 7、PAG257 に 7、PAG258 に 1、PAG260 に 12（このほか D の 2 件にも注記がある）。
- ノート：Part 252・253・254・256 のノートに全件ある。
- 表：行のある定理 20 件（Part 252 の 5、253 の 5、254 の 1、256 の 9）の列 D すべてにある。定義 7 件（casKer・rootNum・charU・ip・prodChar・crtMap・crossSign）は Part 252・253・256 の見出しにある。
- 照合していないもの：引き継ぎメモ（final77 の PAG2_handoff_internal_audit.md）は材料に入っていない。PAG253・PAG254・PAG259 の冒頭には内部照合の段落がないが、A・B がないので必須ではない。

## 3. 形式文の変更の有無

**変更なし**（確信度：高）。5 ファイルの 27 hunk（PAG255 1、PAG256 7、PAG257 5、PAG258 2、PAG260 12）で変わった行は、すべて `/-! … -/` の冒頭の説明か `/-- … -/` の docstring の中にある。宣言の行、`omit … in`、`open Classical in`、証明は文脈行としてそのまま残っている。hunk の位置のずれ（+3・+16・+12・+5・+24）も、足した注記の行数と合う。ただし、差分がこれで全部であることと、組み立て直した .out が前と同一であることは、報告の記述によるもので、自分では確かめていない。

## 4. 総評

A・B の注記 27 件は Lean・ノート・表のすべてに入り、形式文も変わっていない。「同じ文・同じ値・同じ定義」の判断と、照合できた範囲の新しい Part 番号は正しく、照合者の判定だけのものに「Lean で確認」と書いた例もない（xlsx のもとからある文 2 か所は誤り、#6）。
直すべき主な点の一つは Lean の根拠で、cast_crtMap_fst・snd の「Lean で確認」の根拠が表になく、報告の件数とも合わない（#2）。inv_apply_units_inv の確認も、NeZero を仮定した弱い文でしかない（#3）。
もう一つは格上げで、冒頭の説明・ノート・手順 278 が、B を「同じ文」、C・D を「同じ内容・数行」、D を「新しい」、「見つからない」を「重複なし」と書いている（#1・#4・#5・#7・#8）。
