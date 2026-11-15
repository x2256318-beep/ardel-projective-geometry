**前提**
- このセッションには Grep ツールがありませんでした。シェルの grep は依頼の制約に従って使っていません。そのため statements_all.txt は Read で約 2,500 行しか読めておらず、全 22,569 行の約 1 割です。読んでいない範囲に重複がある可能性は残ります。
- statements_all.txt には PAG1 の節がありません。先頭が PAG2、末尾が PAG260 で、間は番号順に並んでいます。PAG3 と PAG253 が `PAG.transl`・`PAG.charFun`・`PAG.rev` を `PAG.` 付きで使っているので、これらの定義は PAG1 にあると思われますが、照合できていません。確信度が「低」の行は、PAG1 を見れば判定が変わる可能性があります。

## 1. 表

| 宣言 | 判定 | 前の宣言 | 根拠 | 確信度 |
|---|---|---|---|---|
| PAG253::commSubmonoid（def） | D | — | {g ∣ U∘transl g = transl g∘U} を部分モノイドにした定義。前に同じ定義は見つからない | 中 |
| PAG253::commute_transl_of_prime | D | — | kUnit も「素数の類が単数群を生成する」補題も前にない（同じファイルの commSubmonoid と eq_top_of_prime から出る） | 中 |
| PAG253::conj_eigen_of_adjoint | D | — | 前にある材料は PAG3::rev_charFun だけ。ipG を使った随伴の議論は前にない | 低（PAG1 未照合） |
| PAG253::eigenFun_of_commute_prime | D | — | kUnit を仮定に持つ固有関数の存在。前にない | 中 |
| PAG253::eigen_of_commute_prime | D | — | 上と同じ内容を χ ごとに述べたもの | 中 |
| PAG253::eq_of_euler | D | — | Real.log と Complex.exp を使う (χ, l) の一意性。前に Real.log を型に持つ宣言は見つからない | 高 |
| PAG253::eq_of_prime_invariant | D | — | 連続性と素数ずらし不変性から定数を導く文。前に同種なし | 高 |
| PAG253::eq_of_prime_invariant' | D | — | 上の M = N の場合（同じファイル内）。前にはない | 高 |
| PAG253::eq_top_of_prime | D | — | 素数の類を含む部分モノイドは ⊤。前に Submonoid や生成の補題は見つからない | 中 |
| PAG253::exists_cls_near | D | — | 類を指定した log n − log m の近似。前に Real.log なし | 高 |
| PAG253::exists_cls_near_of_dvd | D | — | 上の N ∣ M 版 | 高 |
| PAG253::exists_kUnit_eq | D | — | 単数を正の n の kUnit で表す。PAG37::units_pm5（2 冪での ±5^b 表示）とは別の文 | 中 |
| PAG253::globalInv（def） | D | — | (ZMod N)ˣ → ℝ → ℂ 上の反転。この関数空間は前に出てこない | 高 |
| PAG253::globalInv_globalInv | D | — | 新しい定義の対合性 | 高 |
| PAG253::globalInv_primeShift_globalInv | D | — | 新しい定義どうしの関係 | 高 |
| PAG253::globalInv_scaleShift_globalInv | D | — | 新しい定義どうしの関係 | 高 |
| PAG253::invariant_cls | D | — | 素数ずらし不変から m·n⁻¹ の類によるずらし不変を導く文。前にない | 高 |
| PAG253::invariant_kUnit | D | — | 素数から一般の n への延長。前にない | 高 |
| PAG253::ipG（def） | D（前の X を一般化） | PAG229::herm、PAG52::ip | 式は同じ ∑ conj(f x)·g x。前の定義は ZMod N（[NeZero N]）上、ipG は任意の有限型 G 上 | 中 |
| PAG253::ipG_charFun_self_ne_zero | D | — | 近いのは PAG229::herm_self_eq_zero（ZMod N 上、f ≠ 0 の形）で、charFun についての文ではない | 低（PAG1 未照合） |
| PAG253::ipG_smul_left | D（一般化） | PAG229::herm_smul_left、PAG217::inner_smul_left' | G = ZMod N にすると herm_smul_left と同じ文 | 中 |
| PAG253::ipG_smul_right | D（一般化） | PAG229::herm_smul_right、PAG208::inner_smul_smul | G = ZMod N にすると herm_smul_right と同じ文（inner_smul_smul の a = 1 の場合） | 中 |
| PAG253::kUnit（def） | D | （参考：PAG37::five） | (unitOfCoprime n h)⁻¹。前に unitOfCoprime を使う定義は PAG37::five（5 だけ、逆元なし）しかなく、別物 | 高 |
| PAG253::kUnit_mem_of_prime | D | — | 素因数分解による帰納。前に同種なし | 中 |
| PAG253::kUnit_mul | D | — | unitOfCoprime の乗法性の補題は前に見つからない | 中 |
| PAG253::kUnit_mul_natCast | D（一般化） | PAG37::five_val | n = 5、N = 2^m にすると five_val と 1〜2 行で同値（逆元の形） | 中 |
| PAG253::kUnit_one | D | — | 前に見つからない | 中 |
| PAG253::mem_dilCommute_of_prime | D（強めた形） | PAG224::mem_dilCommute | ← 向きの仮定「すべての単数 a」を「素数の類 kUnit p」に弱めたもの | 高 |
| PAG253::norm_eq_one_of_isometry | D | — | ipG 等長性から固有値の絶対値が 1 であることを導く文。前にない | 低（PAG1 未照合） |
| PAG253::primeShift（def） | D | — | 新しい関数空間上の作用素 | 高 |
| PAG253::primeShiftInv（def） | D | — | 同上 | 高 |
| PAG253::primeShift_eq | D | — | 新しい定義どうしの分解 | 高 |
| PAG253::primeShift_primeShiftInv | D | — | 新しい定義どうしの関係 | 高 |
| PAG253::primeShift_scaleShift | D | — | 新しい定義どうしの可換性 | 高 |
| PAG253::scaleShift（def） | D | — | 新しい関数空間上の作用素 | 高 |
| PAG253::shift_invariant_of_prime_invariant | D | — | 前にない（同じファイルの eq_of_prime_invariant' 系から出る） | 高 |
| PAG253::signMul（def） | D | — | 単位元で +1、それ以外で −1 を掛ける作用素。前に見つからない | 中 |
| PAG253::signMul_adjoint | D | — | 新しい定義の性質 | 中 |
| PAG253::signMul_apply | D | — | 定義を展開しただけ。前に対応する定義がない | 中 |
| PAG253::signMul_isometry | D | — | 新しい定義の性質 | 中 |
| PAG253::signMul_not_commute | D | — | PAG3::rev_not_commute と同じ趣旨（平行移動と可換でない）だが、作用素も仮定も別 | 中 |
| PAG253::thm26_full | D | — | 同じファイルの thm26_full_of_commute と commute_transl_of_prime から出る。前のファイルからは出ない | 中 |
| PAG253::thm26_full_hyp_transl | D | — | transl の等長性・随伴性は前に見つからない（PAG1 にあれば C になりうる） | 低 |
| PAG253::thm26_full_of_commute | D | — | 元の Theorem 2.6 の形式化は PAG1 にあると推測されるが、材料になく照合できない | 低 |
| PAG253::thm26_needs_adjoint | D | — | I • id による反例。前にない | 中 |
| PAG253::thm26_needs_commute | D | — | signMul による反例。前にない | 中 |
| PAG253::thm26_needs_isometry | D | — | 2 • id による反例。前にない | 中 |
| PAG253::transl_adjoint | D | — | 近いのは PAG36::conv_adjoint と PAG229::herm_conv だが、作用素が別 | 低（PAG1 未照合） |
| PAG253::transl_charFun | D | — | 似ているのは PAG218::dil_gket など（dil の固有方程式）だが、空間が別 | 低（PAG1 未照合） |
| PAG253::transl_isometry | D | — | 似ているのは PAG218::inner_dil（ZMod N 上の dil の等長性）だが、空間が別 | 低（PAG1 未照合） |
| PAG253::transl_mul | D | — | 似ているのは PAG218::dil_dil だが、作用素が別 | 低（PAG1 未照合） |
| PAG253::transl_one | D | — | 似ているのは PAG218::dil_one だが、作用素が別 | 低（PAG1 未照合） |
| PAG253::unitShift（def） | D | — | 新しい関数空間上の作用素 | 高 |
| PAG253::unitShift_scaleShift | D | — | 新しい定義どうしの可換性 | 高 |
| PAG253::unitsMap_kUnit | D（一般化） | PAG37::unitsMap_five | n = 5、N = 2^m、M = 2^c にすると、逆元を取って unitsMap_five と同値 | 中 |
| PAG254::abs_log_sub_log_le | D | — | 前に Real.log を型に持つのは PAG253 だけで、そこにはない | 高 |
| PAG254::chainIn（def） | D | — | ε 鎖の新しい定義。前に同種の定義は見つからない | 中 |
| PAG254::chainIn_dInf | D | — | 新しい定義どうし（同じファイルの abs_log_sub_log_le から出る） | 高 |
| PAG254::chainIn_dP_classification | D | — | 新しい定義どうし | 高 |
| PAG254::chainIn_dP_iff | D | — | 新しい定義どうし | 高 |
| PAG254::chainIn_dP_of_one_lt | D | — | 新しい定義どうし | 高 |
| PAG254::chainIn_invariant | D | — | chainIn の基本性質 | 中 |
| PAG254::chainIn_mono | D | — | 同上 | 中 |
| PAG254::chainIn_of_lt | D | — | 同上 | 中 |
| PAG254::chainIn_refl | D | — | 同上 | 中 |
| PAG254::dInf（def） | D | — | log q − log r の絶対値。前に同じ定義なし | 高 |
| PAG254::dInf_eq_dist | D | — | 新しい定義と dist の一致 | 高 |
| PAG254::dInf_mul_left | D | — | 新しい定義の性質 | 高 |
| PAG254::dInf_zpow | D | — | 新しい定義の性質 | 高 |
| PAG254::dP（def） | D | — | padicValRat の差の絶対値。前に padicValRat を型に持つ宣言は見つからない | 高 |
| PAG254::dP_eq_dist | D | — | 新しい定義の性質 | 高 |
| PAG254::dP_lt_one_iff | D | — | 新しい定義の性質 | 高 |
| PAG254::dP_mul_left | D | — | 新しい定義の性質 | 高 |
| PAG254::dense_closure_log_two_three | D | — | log 2 と log 3 が生成する部分群の稠密性。PAG253::exists_cls_near の m, n は任意の正整数なので、これは出ない | 高 |
| PAG254::dense_logSet | C | PAG253::exists_cls_near | N = 1、a = 1 で m, n を取り q = n/m とおけば、Metric.dense_iff と Real.log_div で数行 | 高 |
| PAG254::dense_logSet_coprime | B | PAG253::exists_cls_near | a = 1 を代入し、kUnit の等式を捨てて ∧ の順を並べ替えるだけ（1〜2 行） | 高 |
| PAG254::emergence_contrast | D | — | 同じファイルの chainIn_dInf と padicValRat_eq_of_chainIn から出る。前のファイルからは出ない | 高 |
| PAG254::eq_of_chainIn_primePow | D | — | 新しい定義どうし | 高 |
| PAG254::exists_padicValRat_eq | D | — | 前に padicValRat の宣言は見つからない | 中 |
| PAG254::half_le_abs_padicValRat_sub_half | D | — | 整数と 1/2 の距離の初等的な評価。前に見つからない | 中 |
| PAG254::logSet（def） | D | — | 正の有理数の log の集合。前に同じ定義なし | 高 |
| PAG254::logSet_countable | D | — | 新しい定義の性質 | 高 |
| PAG254::log_inj | D | — | 正の有理数上での log の単射性。PAG253 にもない | 高 |
| PAG254::not_Icc_subset_logSet | D | — | 新しい定義の性質 | 高 |
| PAG254::not_forall_chainIn_dP | D | — | 新しい定義どうし | 高 |
| PAG254::padicValRat_eq_of_chainIn | D | — | 新しい定義どうし | 高 |
| PAG254::posRat（def） | D | — | {q : ℚ ∣ 0 < q}。前に同じ定義は見つからない | 中 |
| PAG254::primePow（def） | D | — | ℚ の中の {p^k ∣ k ∈ ℤ}。前に同じ定義は見つからない | 中 |
| PAG254::subsingleton_of_isPreconnected | D | — | 新しい定義の性質 | 高 |

## 2. A・B・C の件数と一覧
- **A：0 件**
- **B：1 件**：PAG254::dense_logSet_coprime（← PAG253::exists_cls_near）
- **C：1 件**：PAG254::dense_logSet（← PAG253::exists_cls_near）
- **D：87 件**。そのうち「前の X を一般化」または「強めた形」と添えたものが 6 件あります。
  - PAG253::ipG（PAG229::herm、PAG52::ip）
  - PAG253::ipG_smul_left（PAG229::herm_smul_left）
  - PAG253::ipG_smul_right（PAG229::herm_smul_right）
  - PAG253::kUnit_mul_natCast（PAG37::five_val）
  - PAG253::unitsMap_kUnit（PAG37::unitsMap_five）
  - PAG253::mem_dilCommute_of_prime（PAG224::mem_dilCommute）
- B と C はどちらも、PAG254 が直前の PAG253 から出る例です。PAG253 については A・B・C を見つけられませんでした。ただし確信度「低」の 10 行（transl_one、transl_mul、transl_charFun、transl_isometry、transl_adjoint、ipG_charFun_self_ne_zero、norm_eq_one_of_isometry、conj_eigen_of_adjoint、thm26_full_of_commute、thm26_full_hyp_transl）は、PAG1 の内容しだいで判定が変わりえます。

## 3. 気づいたこと
**材料の欠け**
- PAG3 の Cor26a 節にある 4 定理（rev_charFun、rev_not_eigen、rev_not_commute、rev_charFun_real）が `PAG.transl` などを使う唯一の前の宣言でした。どれも担当の宣言とは別の文です。
- 節名が Cor26a なので、元の Theorem 2.6 は PAG1 にあると推測しています。PAG1 の形式文と定義の全文を渡して再照合することを勧めます。

**候補の選び方の弱点**
- (a) `PAG.` で始まる定数を数えていないようです。PAG3 の rev 系 4 定理は、`PAG.charFun`・`PAG.rev`・`PAG.transl` を共有する対象（transl_charFun、transl_adjoint など）に対して一度も候補に出ていません。
- (b) 定義を展開しないため、同じ式を別の名前で定義した PAG229::herm の上の herm_smul_left・herm_smul_right が、ipG_smul_left・ipG_smul_right の候補に出ていません。
- (c) kUnit の中身（`ZMod.unitOfCoprime`）を見ないため、PAG37::five_val が kUnit_mul_natCast の候補に出ていません。
- (d) PAG254 の候補はほとんど雑音です（InQi 系や lam_pos 系）。前の鎖で Real.log・padicValRat・Dense を型に持つのが PAG253 だけだからだと思われます。

**前の鎖の中どうしの重複（担当外で目についたもの）**
- PAG52::ip と PAG229::herm は同じ式の定義です（N が暗黙か明示かの違いだけ）。
- PAG217::inner_smul_left' と PAG229::herm_smul_left は、herm を展開すれば同じ文です。PAG215::inner_conj_symm と PAG229::herm_conj も展開すれば同値です。
- PAG8::exists_ker_ne_one_of_primitive と PAG133::exists_ker_ne は、変数名以外同じ文です。
- PAG31::lam_pos、PAG46::lam_pos、PAG116::lam_pos は同じ文です（sz が同じ定数を指すと仮定した場合）。
- PAG44::orderOf_five' は PAG37::orderOf_five の m = d+3 の場合です。
- PAG9::sq_isPrimitive と PAG10::sq_isPrimitive' は、χ * χ と χ ^ 2 の書き方が違うだけです。
- PAG8::neZero_pow と PAG9::neZero_pow' は同じインスタンスです。

**担当ファイル内の重なり（判定には数えていない）**
- PAG253::exists_cls_near は exists_cls_near_of_dvd の M = N の場合です。
- PAG253::eq_of_prime_invariant' は eq_of_prime_invariant の M = N の場合です。
- PAG254::emergence_contrast は chainIn_dInf と padicValRat_eq_of_chainIn から出ます。

**後のファイル（判定には使っていない）**
- PAG259 に zmultiples や通約性の補題（sep_of_commensurable、exists_between_one）があり、PAG254::dense_closure_log_two_three の周辺と重なる可能性があります。

**その他**
- 作業ディレクトリの表示が途中で変わりましたが、依頼にある 3 か所の外は読んでいません。

## 4. 使った検索語の一覧
- **Grep**：使っていません（ツールがなかったため）。
- **代わりに Read で読んだ範囲**（statements_all.txt の行番号）：
  - 1–899（PAG2–PAG14）
  - 2880–3079（PAG37 全部）
  - 13700–13859（PAG218 の dil 群）
  - 14940–15069（PAG224 の dilCommute 周辺）
  - 15930–16179（PAG229 の herm 群）
  - 21011–21539（PAG253・PAG254 の全部を含む）
  - 22400–22569（PAG259 末〜PAG260）
  - 位置を確かめるための抜き取り約 20 か所（各 8〜12 行）
  - targets.md と candidates.md は全文を読みました。
- **読んだ範囲で目で探した語**：`PAG.transl`、`PAG.charFun`、`PAG.rev`、`CommGroup`、`G →* ℂˣ`、`unitOfCoprime`、`unitsMap`、`herm`、`ip`、`inner`、`starRingEnd`、`dil`、`dilCommute`、`Submonoid`、`Real.log`、`Dense`、`padicValRat`、`Continuous`、`zmultiples`
