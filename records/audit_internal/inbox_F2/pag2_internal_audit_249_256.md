# 内部照合の監査 — Part 249〜256 の宣言を、前の鎖と突き合わせる（2026-11-14）

2026-11-14。著者の判断（13:2x）：Part 257 の前に内部照合の監査を行う。新しいパートは始めない。きっかけは、Part 257 の着手前の文書を書く途中で、Part 256 の定理 2 つが Part 189・190 の定理と同じ文だと分かったことです（`pag2_part257_preregistration.md` の §7）。

- 範囲：Part 249〜256（PAG253〜PAG260.lean）の宣言 334 件（定理 271、定義 63。自動で作られる宣言は除く）。
- 突き合わせた相手（「前の鎖」）：PAG.lean（Part 1）〜PAG252.lean と、鎖に import されていない初めのファイル PAG3・PAG5・PAG6（付録 A の Part 3 と PAG 2.0 の初め）。全部で 4279 宣言。
- 番号の対応：PAG 2.0 の Part n は PAG(n+4).lean。PAG.lean・PAG2・PAG3・PAG4 は付録 A の Part 1〜4。名前空間 `PAG.PartNNN` の NNN はファイル番号。
- Lean の鎖の形式文は変えていません。docstring と冒頭の説明に注記を足し、組み立て直しました（§7）。
- 第 2 版（17:5x）：直しの照合（照合者 F）の指摘 24 件を受けて、注記の強さと根拠の書き方を直した版です（§8）。

## 結論

- **前の鎖と同じ文・同じ値の定義（A）、または前の宣言から直ちに出るもの（B）が 26 件ありました。すべて Lean で確かめました。** 内訳は次のとおりです。
  - Part 252：7 件
  - Part 253：6 件
  - Part 254：1 件
  - Part 256：12 件（定義 3 件を含む）
- **前の宣言から数行で出るもの（C）は、照合者の判定で 20 件です。** 6 件を標本として Lean で確かめ、6 件とも判定どおりでした。
- **Part 256 の前半は、ほぼ全部が示し直しでした（Lean で確認）。** 中国剰余の分解、積の指標、ガウス和の乗法性、原始性が該当し、元は Part 189・190・195・232 です。偶奇の符号 `crossSign` は Part 194 の `rs` と同じ値です。相互法則も Part 194 の `real_reciprocity` にあり、W = 1 の仮定を使わずに（互いに素・原始・実の指標のもとで）示してあります。
- **照合者 R2 の判定では、Part 252 の Hartley の部分の中心 7 件は、付録 A の Part 3（PAG3.lean、命題 2.8 `hartley_char`）などから数行で出ます。** そのうち `hartley_one` と `casKer_eq` を Lean で確かめました。残り 5 件は照合者の確信度が低く、Lean では確かめていません。PAG3.lean は鎖に import されていないファイルで、初めの機械的な照合からも漏れていました。照合者が見つけました。
- **前の鎖の定義と一致する定義が 7 つありました。**
  - 同じ定義（`rfl`・`HEq rfl`）：`prodChar`（Part 195 の `cmul`・Part 232 の `charMul` に次ぐ 3 つ目の名前）、`crtMap`（Part 189 の `param`）、Part 253 の `ip`（Part 249 の `ipG`。範囲の中）。
  - 同じ値（式は違う）：`casKer`（付録 A の Part 3 の `casK`）、`rootNum`（Part 192 の `zN` ÷ Part 194 の `gs`）、`crossSign`（Part 194 の `rs`）、`charU`（Part 1 の `PAG.charFun` に `toUnitHom` を通したもの）。
- **Part 249・250・255 には、前の鎖との重複は見つかりませんでした（網羅ではない）。** 範囲の中の系（前のパートから直ちに・数行で出る便利な補題）はありますが、重複には数えていません。
- **限界があります。** 照合者は Grep が使えず、全宣言の文（約 2 万 2 千行）の 1〜3 割しか読めていません。機械的な候補選びは上位 20 件までです。「見つからなかった」は「ない」の証明ではありません（§8）。
- **直したもの。** Lean の docstring と冒頭の説明、ノート 8 本と着手前の文書 2 本、xlsx、引き継ぎメモ（final77）です。直した箇所は照合者 F が確かめ、その指摘で 2 回目の直しをしました。2 回目の直しの照合は照合者 F2 です（§8）。
- **規則の追加の条文案は付録に置きました。** 著者の判断は「足す」です。CLAUDE.md への条文化は著者側で行ってください。

## 1. 手順

1. **全宣言の書き出し**（`audit_internal/lean/Extract2.lean`）：Lean のメタプログラムで、各宣言の型（定義なら値も）に現れる定数を書き出しました（4279 件）。
2. **候補選び**（`shortlist2.py`）：プロジェクトの定義を値の定数まで展開し、TF-IDF の近さで、前の宣言から上位 k 件を選びました。1 回目は k = 8、2 回目は k = 20、3 回目は PAG.lean・PAG3・PAG5・PAG6 を足して k = 20 です。
3. **Lean での直接の当てはめ**（`lean/DupCmd.lean`・`DupCmd2.lean` の `#dupcheck`・`#defeqcheck`）：鎖の外のファイルで、候補の組ごとに一方を他方にそのまま当てて（`exact`、`apply` と仮定、`simp_all`）両向きを試しました。定義は `HEq` の `rfl` で比べました。試行は合計 12,776 回です。
4. **独立の照合者 5 人（R1〜R5）**：新しいセッションに、対象と候補の形式文の全文と、各ファイルの open・variable の行を渡しました。全宣言の文（`statements_all.txt`）も渡しました。判定は A・B・C・D です（A 同じ文、B 直ちに出る、C 数行で出る、D 見つからない）。ほかの照合者の出力と機械的な確認の結果は渡していません。照合者の判定の前に予想を書きました（`expected_before_review.md`）。
5. **前の鎖に対する A・B を Lean で確かめました。** 直接の当てはめで通った組は、名前つきの定理に書き直しました（`lean/MechChecks.lean`、44 定理）。通らなかった組は、前の宣言だけから手で示しました（`lean/ManualChecks2.lean`、14 件）。どちらも、定理については対象の型そのもの（`type_of%`）を述べています。仮定は足していません。
6. **C の判定から標本 6 件を Lean で確かめました**（`lean/SampleC2.lean`）。

手順からのずれ：依頼文では照合者に Grep を許しましたが、この環境の照合者には Grep がありませんでした。照合者は Read の行範囲指定で読み、シェルは使っていません（本人の報告）。

## 2. 結果（前の鎖に対して）

### Part 252（PAG256）

- **A（同じ文・同じ値の定義。Lean で確認、4 件）**
  - `inv_apply_neg_one`：Part 5 の `inv_apply_neg_one`、Part 21 の `chi_inv_neg_one`、Part 77 の `inv_neg_one` と同じ文。
  - `neg_one_mul_self`：Part 5 の `chi_neg_one_sq`、Part 25 の `chi_neg_one_sq'` と同じ文。
  - `isPrimitive_of_prime_of_ne_one`：Part 167 の `primitive_of_ne_one` と同じ文。
  - `casKer`（定義）：付録 A の Part 3 の `casK` と同じ値（定義から直接示した。`casKer_eq_casK`）。
- **B（直ちに出る。Lean で確認、3 件）**
  - `rootNum`（定義）：Part 192 の `zN` を Part 194 の `gs` で割ったものと同じ値（`rootNum_eq_zN_div_gs`）。
  - `inv_apply_units_inv`：付録 A の Part 3 の `apply_inv_eq_inv_apply` から 1 行。
  - `sum_mul_stdAddChar_neg`：付録 A の Part 3 の `sum_neg_twist` の x = 1 の場合。
- **C（照合者 R2 の判定、12 件）**
  - Hartley の部分の中心 7 件：`hartley_one`・`casKer_eq`（Lean で確認）、`hartley_eq_of_isPrimitive`・`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`（確信度 低、Lean では未確認）。前の宣言は付録 A の Part 3 の `hartley_char`、`casK_even_part`・`casK_odd_part` など。
  - `normSq_rootNum`：Part 12 の `normSq_gaussSum` から。Lean で確認。
  - `exists_primitive_odd_three`：Part 115・163・167 から。Lean で確認。
  - `exists_primitive_even_five`：同じ補題から。
  - `parFac`・`rootNum_eq`：Part 194 の `gs`、付録 A の Part 2 の `parity_weight` から。
- **一般化**：`parFac_of_even`・`parFac_of_odd` は、付録 A の Part 2 の `parity_weight`（r = 1）から [NeZero N] を外した形です（照合者の判定）。
- **前の鎖に見つからなかったもの（網羅ではない）**：変換としての定義（`hartley`・`JH`）と、原始性を外したときの反例（`removal_counterexample` など 3 件）。

### Part 253（PAG257）

- **A・B（Lean で確認、6 件）**
  - `charU`（定義）：Part 1 の `PAG.charFun` に `MulChar.toUnitHom` を通したものと同じ関数。照合者は B（推定、確信度 低）としました。
  - `eq_one_of_two`：Part 194 の `level_two_trivial` から。
  - `not_isPrimitive_one_of_two_le`・`charU_one_mem_Vimprim`：Part 191 の `ne_one_of_isPrimitive` から。
  - `not_isPrimitive_one_prime`：Part 28 の `prim_level_p_iff` から。
  - `Vprim_two`：Part 26 の `no_prim_mod_two` から。
- **C（照合者 R3 の判定、2 件。Lean では未確認）**
  - `ip_charU`：Part 214 の `sum_units_char` と、付録 A の Part 3 の `conj_apply_eq_inv` から。
  - `Vprim_ne_bot_prime`：確信度 低。
- **範囲の中**：`ip`（定義）は Part 249 の `ipG` と同じ定義です（`rfl`）。
- **前の鎖に見つからなかったもの（網羅ではない）**：単数の上の作用素 T、V_prim と V_imprim の分解と直交、V_prim の上のユニタリ性と一意性、V_imprim の上で等長でないこと。

### Part 254（PAG258）

- **B（Lean で確認、1 件）**：`gaussSum_inv`。Part 5 の `conj_gaussSum` と `chi_neg_one_sq` から 1 行。
- **C（照合者 R4 の判定、2 件）**
  - `rootNum_one_of_eq_one`：Part 192 の `zN_level_one` から。Lean で確認。
  - `phaseA1_one`：確信度 低。
- **前の鎖に見つからなかったもの（網羅ではない）**：全空間の UA1、`condPart`、引き戻しとの両立、帰納極限の上の `Uinf` と内積、族の一意性。

### Part 256（PAG260）

- **A（Lean で確認、8 件）**
  - 定義 3 件：`prodChar`（Part 195 の `cmul`、Part 232 の `charMul`。`HEq rfl`）、`crtMap`（Part 189 の `param`。`rfl`）、`crossSign`（Part 194 の `rs` と同じ値。`crossSign_eq_rs`）。
  - 同じ文 5 件：`gaussSum_prodChar`（Part 189 の `gaussSum_mul_coprime`）、`isPrimitive_prodChar`（Part 190 の `isPrimitive_mul`、Part 232 の `isPrimitive_charMul`）、`prodChar_apply`（Part 189・195・232）、`crtMap_bijective`・`stdAddChar_crtMap`（Part 189）。いずれも両向きに確認。
- **B（Lean で確認、4 件）**
  - `cast_crtMap_fst`・`cast_crtMap_snd`：Part 189 の `param_cast₁`・`param_cast₂` から。
  - `charU_prodChar`：Part 232 の `charMul_apply_unit` から。
  - `prodChar_neg_one`：Part 200 の `changeLevel_neg_one` から。
- **C（照合者 R5 の判定、3 件。Lean では未確認）**：`norm_char_unit`、`norm_cross`、`parFac_prodChar`（Part 194 の `gs_combine` と同じ形）。
- **境目**：`rootNum_prodChar` は照合者の判定で D（C との境目）です。中身は Part 189 の `z_mul_coprime`・`gaussSum_mul_coprime` に偶奇の因子のずれを足したもので、私の見立ては C 寄りです（Lean ではつないでいない）。
- **関係**：`cross_eq_sign_of_rootNum_one` の 3 つの仮定は、実原始指標なら Part 194 の `gauss_sign_real` から成り立ち、結論は `real_reciprocity` の式と同値です（`crossSign` と `rs` が同じ値なので。数学として。Lean ではつないでいない）。
- **「Lean にしていない」とした (i) について**：法 M·N のすべての指標が積の形に一意に書けることは、Part 190 の `decomp`（存在）と Part 232 の `charMul_injective`（一意性）を合わせると出ます（監査者の読み。Lean ではつないでいない）。
- **前の鎖に見つからなかったもの（網羅ではない）**：UA1・phaseA1 の形の式、例 3 件、一般の指標での条件つきの文。

### Part 249・250・251・255

- Part 251：C が 1 件です。`units_eq_of_coprime_parts` は Part 192 の `crt_unique` から数行で、Lean で確認しました。
- Part 249・250・255：前の鎖との重複は見つかりませんでした（網羅ではない）。
- 一般化の関係は次のとおりです。示し直しではありません。
  - Part 249 の `ipG`：Part 48 の `ip`、Part 225 の `herm`（法 N の上）を任意の有限型に広げた定義（照合者の判定）。
  - Part 249 の `ipG_smul_left`・`ipG_smul_right`：Part 51・213・225 の同じ形の定理を含みます。前の文がこちらから出ることを Lean で確認しました（この 2 定理について）。
  - Part 249 の `kUnit_mul_natCast`・`unitsMap_kUnit`：Part 33 の `five_val`・`unitsMap_five` の一般化（照合者の判定）。
  - Part 255 の一部：Part 250 の (2, 3) の場合などの一般化（照合者の判定）。

## 3. Lean での確認

- **直接の当てはめ**（試行 12,776 回）：通ったのは自動生成物を除いて 76 回で、組にすると 30 組です。そのうち前の鎖に対するものは 28 組で、対象は 15 件です（A・B の 13 件と、Part 249 の一般化 2 件）。30 組はすべて `MechChecks.lean` に名前つきの定理（44 定理）として書き直しました。表は `lean_mechanical_summary.md` です。
- **手で示した確認**（`ManualChecks2.lean`、14 件。定理 8 件・定義の一致 6 件）：
  - 定義の一致：`casKer_eq_casK`（定義から直接）、`rootNum_eq_zN_div_gs`、`charU_eq_charFun`、`ip_eq_ipG`、`crtMap_eq_param`、`crossSign_eq_rs`
  - 定理：`inv_apply_units_inv_of_PAG3`、`sum_mul_stdAddChar_neg_of_PAG3`、`not_isPrimitive_one_of_two_le_of_PAG195`、`charU_one_mem_Vimprim_of_PAG195`、`gaussSum_inv_of_PAG9`、`not_isPrimitive_one_prime_of_PAG32`、`Vprim_two_of_PAG30`、`prodChar_neg_one_of_PAG204`
- **C の標本**（`SampleC2.lean`、6 件）：`normSq_rootNum`、`rootNum_one_of_eq_one`、`units_eq_of_coprime_parts`、`exists_primitive_odd_three`、`hartley_one`、`casKer_eq`。どれも前の宣言から数行で示せました（`hartley_one` は約 20 行で、うち半分は偶奇の場合分け）。
- いずれも rc 0 です。64 定理すべてに `#print axioms` を付け、公理が propext・Classical.choice・Quot.sound だけであることを確かめました。
- 1 回目の `ManualChecks.lean`・`SampleC.lean` は、一部の定理で対象にない仮定（NeZero N）を足していました（照合者 F の指摘 #3）。2 回目の版で、対象の型そのものに直しました。

## 4. 照合者の判定と、機械的な確認・予想との突き合わせ

- **照合者の件数**

  | 照合者 | 担当 | A | B | C | D |
  |---|---|---|---|---|---|
  | R1 | Part 249・250 | 0 | 1 | 1 | 87 |
  | R2 | Part 251・252 | 4 | 3 | 14 | 27 |
  | R3 | Part 253 | 1 | 8 | 6 | 26 |
  | R4 | Part 254 | 0 | 4 | 5 | 63 |
  | R5 | Part 255・256 | 8 | 6 | 5 | 56 |

  この件数は範囲の中の系を含みます。前の鎖に対する件数は §2 のとおりです。
- **一致**
  - 機械的な確認で通った組は、すべて照合者も挙げていました。
  - 前の鎖に対する照合者の A・B の判定と、範囲の中の `ip` は、すべて Lean で確かめられました。範囲の中の B 8 件は、`ip_smul_right` を除いて Lean では確かめていません。
  - `charU` は、照合者の判定（B、推定）より強く、同じ関数でした。
- **機械的な確認の弱点（照合者の指摘）**
  - 鎖に import されていない PAG3 を、初めは対象に含めていませんでした。
  - 名前が違う同じ概念を拾えませんでした。例：`ip` と `ipG`、`rootNum` と `zN`・`gs`、`casKer` と `casK`。
  - 存在の補題や初等的な補題を拾えませんでした。
- **予想との比較**（`expected_before_review.md`）
  - 当たり：A・B は Part 252 と 256 に集中する。Part 256 の前半の 7 宣言、Part 252 の χ(−1) の補題 3 つ、`eq_one_of_two`、`normSq_rootNum`（C）。
  - 外れ：A・B の件数は「10〜15」と予想しましたが、実際は 26 件でした。Hartley の部分は「D か、前の DFT の結果の C（低）」と予想しましたが、照合者の判定では付録 A の Part 3 の命題 2.8 から数行でした。私の道具は PAG3 を見ていませんでした。Part 253 のユニタリ性（C を予想）と Part 254 の `condPart`（C を予想）は、照合者の判定では D でした。

## 5. 評価の見直し

- **Part 252**：位置づけ「既知の事実の書き直し（再導出）」は変わりません。照合者の判定と Lean で確かめた 2 件から、鎖の中では付録 A の Part 3 の命題 2.8 の再導出にあたると見ます（確信度：中〜高）。
- **Part 256**：位置づけ「既知の事実の Lean 化（再導出）」は変わりません。加えて、前半は鎖の中の定理の示し直しでした（Lean で確認）。Part 256 の着手前の文書の「形式化としては新しい可能性があります」は誤りでした。
- **Part 253・254**：作用素の文の大半は、前の鎖に見つかりませんでした（網羅ではない）。補題の一部が重複でした。
- **Part 249・250・255**：前の鎖に見つからない内容が大半でした（網羅ではない）。
- **兆候 4（初等的な部品だけ）**：8 パート連続のままです。新しいパートは始めていません。
- **兆候 1 の内側版**：自前の名前の定義が、自分の鎖の既存の定義と一致していました（`prodChar`・`crtMap`・`charU`・`ip` ほか）。
- **第 8 の型（規約）**：Part 252・253 の記録に、ファイル番号を Part 番号として書いた取り違えがありました（「Part 16」は正しくは Part 12 = PAG16、「Part 218」は正しくは Part 214 = PAG218）。照合者 F の指摘と、参照の機械的な点検（`check_part_refs.py`）で見つけ、直しました。

## 6. 前の鎖の中どうしの重複（範囲外、記録だけ。直していない）

照合者が担当の外で見つけたものです（照合者の判定。印のあるものだけ Lean で確かめた）。

- 同じ定義・同じ値：
  - `cmul`（Part 195）と `charMul`（Part 232）［Lean：`prodChar` を通して `HEq rfl`］
  - `ip`（Part 48）と `herm`（Part 225）
  - `shellSize`（Part 11）と `sz`（Part 15）
  - `kk c`（Part 26）と `gp 2 c`（Part 28）
  - `testFn N`（Part 243）、`pairFn N 1`（Part 244）、`twoPt N (−1)`（Part 246）
- 同じ文：
  - `inv_apply_neg_one`（Part 5）、`chi_inv_neg_one`（Part 21）、`inv_neg_one`（Part 77）［Lean：Part 252 の宣言を通して両向き］
  - `chi_neg_one_sq`（Part 5）と `chi_neg_one_sq'`（Part 25）［Lean：同上］
  - `lam_pos`（Part 27・42・112）
  - `conv_single_apply`（Part 243）と `conv_single`（Part 246）
  - `exists_ker_ne_one_of_primitive`（Part 4）と `exists_ker_ne`（Part 129）
  - `charMul_mul`（Part 232）と `cmul_mul_cmul`（Part 196）
  - `herm_smul_left`（Part 225）と `inner_smul_left'`（Part 213）
- 直ちに出る：
  - `z_level_one`（Part 191）、`zN_level_one`（Part 192）、`gaussSum_level_one`（Part 199）
  - `prim_level_p_iff`（Part 28）から `primitive_of_ne_one`（Part 167）
  - `castHom_neg_one`（Part 194）、`changeLevel_neg_one`（Part 200）、`unitsMap_neg_one`（Part 33）
  - `card_units_filter`（Part 141）と `card_isUnit`（Part 210）
  - `conj_apply_eq_inv`（付録 A の Part 3）と `conj_inv_apply`（Part 209）
  - `sq_isPrimitive`（Part 5）と `sq_isPrimitive'`（Part 6）
  - `no_prim_mod_two`（Part 26）と `no_prim_mod2`（Part 81）

## 7. 直したもの

- **Lean**（形式文は変えていない。leanparse で 5 ファイルとも文が同一であることを確認）
  - docstring に注記を足しました。PAG256 に 7 か所、PAG257 に 7 か所、PAG258 に 1 か所、PAG260 に 14 か所です。PAG255 の docstring は変えていません。
  - 冒頭の説明に「内部照合」の段落を足しました（PAG255・256・257・258・260）。
  - もとからある docstring のファイル番号の取り違えを 2 か所直しました（PAG256 の「Part 16」、PAG257 の「Part 218」）。
  - PAG255〜PAG260 を順に組み立て直しました。rc 0 で、.out は直す前と同一です。
- **ノート**
  - Part 249〜256 のノートに「内部照合（2026-11-14）」の節を足しました。
  - Part 252 と 256 のノートでは、誤解を招く箇所に短い追記をしました（盲検の「Hartley の形の文献は見つからず」、位置づけの「Mathlib と Isabelle AFP に見つかりませんでした」、「Lean にしていない (i)」）。
  - もとからある文のファイル番号の取り違えを直しました（Part 252 のノートに 2 か所、Part 253 のノートに 3 か所）。
  - Part 256 の着手前の文書に訂正を足しました。Part 257 の着手前の文書の、相互法則についての言い過ぎ（「仮定はありません」）も直しました。
- **xlsx**（final77）
  - Part 251〜254・256 の行の「証明の方針」に注記を 43 か所足しました。
  - Part 252・253・256 の見出しに 1 文ずつ足しました。xlsx には定義の行がないので、定義の一致は見出しに書きました。
  - もとからある文のファイル番号の取り違えを 3 か所直しました（Part 249・252・253 の行）。
  - 検証手順 278 とメモを足しました。再計算でエラーは 0 です。
- **引き継ぎメモ**：final77 の `PAG2_handoff_internal_audit.md` です。規則（内部照合、Part 番号とファイル番号）、開始条件 2 の判断、監査の節、収束アラームを書き足しました。

## 8. 直しの照合と、限界

- **照合者 F（1 回目の直しの照合）**：直した箇所と、対象・前の宣言の形式文の全文を渡しました（`inbox_F/`）。抜けはなく、形式文の変更もありませんでした。指摘は 24 件で、主なものは次のとおりです。
  - B を「同じ文」に、C・D を「同じ内容」「新しい」に、「見つからない」を「重複なし」に格上げしていた。
  - `cast_crtMap_fst`・`snd` の Lean の根拠が、渡した表から抜けていた。3 回目の当てはめの結果を表に入れていなかったためで、通った出力は残っていました。今回 `MechChecks.lean` に名前つきで書き直しました。
  - 手の確認の一部が、対象にない仮定（NeZero N）を足した弱い文だった。
  - 相互法則について「仮定なし」は言い過ぎ。
  - もとからある文のファイル番号の取り違え。
  
  24 件すべてを直すか、直した形で受け入れました（`outputs/F_output.md` と、2 回目の直しの差分）。
- **照合者 F2（2 回目の直しの照合）**：これから行います。F2 の後に直したものは、照合を受けていないものとして記録します。
- **網羅していません。** 照合者は全宣言の文の 1〜3 割しか読めていません（R1 約 1 割、R2 約 3 割、R3・R5 約 2.5 割、R4 は読んだ範囲を明記）。機械的な候補選びは上位 20 件までで、名前の違う同じ概念を拾いにくい弱点があります。見落としは残っていると考えます（確信度：中）。
- **確認の強さに差があります。** Lean で確かめたのは、前の鎖に対する A・B の 26 件と、C の標本 6 件です。残りの C 14 件は照合者の判定です。
- **範囲の中の系は重複に数えていません。** 例は Part 254 の `normSq_phaseA1`（Part 252 から）などです。
- **気づいたこと**：Part 250 のノートの表に「直線が創発する」という表現があります（2026-11-12 の指示より前の記録）。今回は直していません。直すかどうかは著者の判断です。

## 付録：規則の追加の条文案（CLAUDE.md への条文化は著者が行う）

### 案 1：着手前の 4 点に 5 点目を足す

> 5. **鎖の中の照合（内部照合）**：問いと、予定している主な文について、自分の鎖（xlsx の「定理と証明」と、Lean の全宣言。鎖に import されていないファイルも含む）を検索し、同じ文・より強い文・直ちに出る文・同じ式の定義がないかを調べる。見つかったら、その定理と定義を使う計画にし、示し直さない。見つからなかった場合も、検索した語と範囲を書く。

### 案 2：パートを閉じる条件に足す

> 各主要結果について、［既知／再導出／新規候補］のラベルとは別に、内部照合の結果［鎖にある（Part n の宣言名）／鎖に見つからない］を記録する。鎖にあるものは、Lean の docstring にその宣言名を書く。内部照合は次の 3 段で行う。
> 1. 機械的な候補選び：型に現れる定数（プロジェクトの定義は値の定数まで展開）の近さで、前の宣言から候補を選ぶ。
> 2. Lean での確認：候補の組ごとに、一方を他方にそのまま当てて通るかを、鎖の外のファイルで確かめる。定理は対象の型そのもの（`type_of%`）で述べ、定義は `HEq` の `rfl` か値の等式で確かめる。
> 3. 独立の照合：新しいセッションに、対象と候補の形式文の全文を渡して判定させる。全宣言の文を探せる形（読み取り専用の検索か、ファイルごとの文）も渡す。

### 案 3：兆候 1 の補足

> 自前の名前は、外の文献だけでなく、自分の鎖の名前とも照合する。例：Part 256 の `prodChar` は Part 195 の `cmul`・Part 232 の `charMul` と同じ定義だった。

### 案 4：番号の書き方

> Part を参照するときは「Part n（PAGm）」とファイル番号を添える（PAG 2.0 では m = n + 4）。名前空間 `PAG.PartNNN` の NNN はファイル番号で、Part 番号ではない。

### 道具（`audit_internal/`）

- `lean/Extract2.lean`：全宣言の定数を書き出す（鎖に import されていない PAG3・PAG6 も import する）。
- `shortlist2.py`：候補選び。
- `lean/DupCmd2.lean`：`#dupcheck`（直接の当てはめ）と `#defeqcheck`（定義の一致）。
- `check_part_refs.py`：「Part n の 名前」の参照が、Part n のファイルの宣言を指しているかを点検する。
- `build_statements.py`・`build_review_inputs.py`：照合者に渡す全文の材料。
