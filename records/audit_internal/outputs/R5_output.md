## 照合者 R5 の報告：PAG259・PAG260（Part 255・256）

**前置き（制約とどこまで調べたか）**
- この環境には Grep ツールがありませんでした。シェルは禁止なので、使ったのは Read だけです。書き込み、シェル、ウェブ、エージェントの起動はしていません。
- そのため statements_all.txt（全 22,569 行）は Read で一部を通読しただけで、全文検索はしていません。読んだのは約 5,700 行（約 25%）で、行範囲は 4. に書きました。
- D の大半は「読んだ範囲と候補には見つからなかった」という意味で、前の鎖に無いことの証明ではありません。Mathlib だけで書ける文の D は、この理由で確信度を「中」にしました。
- targets.md と candidates.md は全部読みました。

### 1. 表

**PAG259（Part 255、49 件）**

| 宣言 | 判定 | 前の宣言 | 根拠（1 行） | 確信度 |
|---|---|---|---|---|
| PAG259::BoxCoord | D | — | `Nat.Primes → ℤ` の型別名（離散位相を載せる用）。同じ型の定義は見当たらない | 中 |
| PAG259::closure_logSet | B | PAG254::dense_logSet | `dense_logSet.closure_eq` の 1 行で出る | 高 |
| PAG259::closure_rho_not_image | D | — | rho（新）についての文。後半は同じファイルの eq_one_of_padicValRat_eq_zero（新）に依存 | 高 |
| PAG259::dense_closure_log_primes | D | （一般化元）PAG254::dense_closure_log_two_three | 前の PAG254::dense_closure_log_two_three（p=2, r=3）を、相異なる素数 p, r に一般化したもの | 高 |
| PAG259::dense_imgST_iff | D | — | imgST（新）の稠密性の判定 | 高 |
| PAG259::dense_rho_image | D | （関連）PAG254::dense_logSet_coprime | rho は新。有限個の素数での付値の指定（同じファイルの一般化版 exists_padicValRat_eq）と積位相の処理が要る | 高 |
| PAG259::eq_mul_zpow_of_agree | D | — | 同じファイルの eq_of_padicValRat_eq（新）に依存 | 中 |
| PAG259::eq_of_padicValRat_eq | D | — | 「正の有理数は全素数での付値で決まる」は前の鎖に見つからない（PAG254 には素数 1 つずつの dP しかない） | 中 |
| PAG259::eq_one_of_padicValRat_eq_zero | D | — | 同じファイルの eq_of_padicValRat_eq で r=1 とした場合 | 中 |
| PAG259::eq_prod_of_support | D | — | 台が有限な有理数の素因数分解。前の鎖に見つからない | 中 |
| PAG259::eq_prod_support | D | — | 同じファイルの eq_prod_of_support と finite_support_padicValRat の組合せ | 中 |
| PAG259::exists_between_one | D | （関連）PAG254::dense_closure_log_two_three | 一般の 2 素数での稠密性（新）に依存。p=2, r=3 なら PAG254 から数行で出る | 中 |
| PAG259::exists_mem_one_le_abs_of_support | D | （関連）PAG254::dP_lt_one_iff | 核心は付値による単射性（新）。それがあれば dP_lt_one_iff で数行 | 中 |
| PAG259::exists_near_in_subgroup | D | （関連）PAG254::dense_closure_log_two_three | 台を S の中に保つため p, r の 2 つだけで近似する必要があり、一般の 2 素数での稠密性（新）が要る | 高 |
| PAG259::exists_near_measured | C | PAG254::dense_logSet_coprime（PAG253::exists_cls_near でも可） | N を M に含まれる素数の積とし q=q₀·n/m とすれば、M の素数での付値は変わらず log も近い。p, r の仮定は不要（付値の計算込みで十数行） | 中 |
| PAG259::exists_near_of_two_unmeasured | D | （一般化元）PAG254::dense_closure_log_two_three | q/q₀ が p^a·r^b に限られる。p=2, r=3 なら PAG254 から数行の系で、これはその一般化 | 高 |
| PAG259::exists_padicValRat_eq | D | （一般化元）PAG254::exists_padicValRat_eq | 前の PAG254::exists_padicValRat_eq（素数 1 つ）を、有限個の素数＋それ以外の素数で付値 0、に一般化（同名、名前空間は別） | 高 |
| PAG259::exists_prime_one_le_abs | D | （関連）PAG254::dP_lt_one_iff | 「q≠r なら付値の違う素数がある」が新しい。結論の形は dP_lt_one_iff の否定 | 中 |
| PAG259::exists_two_primes_not_mem | D | — | 素数の無限性の補題。前の鎖に見つからない | 中 |
| PAG259::exists_zpow_near | D | （一般化元）PAG254::dense_closure_log_two_three | mem_closure_pair により dense_closure_log_primes の言い換え。(2,3) の場合は PAG254 の言い換えで、これはその一般化 | 高 |
| PAG259::fiber_sep | D | — | imgST の各繊維が一様に分離していること。前の鎖に対応なし | 高 |
| PAG259::finite_support_padicValRat | D | — | 付値の台が有限であること。前の鎖に見つからない | 中 |
| PAG259::imgST | D | — | 新しい集合の定義 | 高 |
| PAG259::irrational_log_div_log | D | （関連）PAG254::dense_closure_log_two_three | log r／log p の無理性は文としては見つからない（PAG254 の証明の内部にはあり得る） | 中 |
| PAG259::isClosed_and_discrete_of_subsingleton | D | — | 一般位相の補題。前の鎖に見つからない | 中 |
| PAG259::isClosed_discrete_imgST | D | — | imgST（新）についての文 | 高 |
| PAG259::isClosed_discrete_rhoBox_image | D | — | rhoBox・BoxCoord（新）についての文 | 高 |
| PAG259::log_eq_sum_of_support | D | — | log q を付値と log s の和で表す式。前の鎖に見つからない | 中 |
| PAG259::log_mul_zpow_zpow | D | （関連）PAG254::dInf_zpow | Mathlib の log_mul・log_zpow で出る計算。dInf_zpow は絶対値の式なので、そこからは直ちに出ない | 中 |
| PAG259::log_sep_of_agree | D | （関連）PAG254::dInf_mul_left, PAG254::dInf_zpow | q'=q·p^k（同じファイルの eq_mul_zpow_of_agree、新）が要る。そのあとは dInf の 2 つで数行 | 中 |
| PAG259::log_sep_one_unmeasured | D | （関連）同上 | 上の台つき版。付値による単射性（新）に依存 | 中 |
| PAG259::mem_closure_line_prod | D | （関連）PAG254::dense_logSet_coprime | 核心は dense_logSet_coprime だが、rho（新）と積位相の近傍の扱いが要り、数行では済まない | 中 |
| PAG259::mem_zmultiples_of_commensurable | D | — | 実数の環の恒等式。前の鎖に見つからない | 中 |
| PAG259::one_le_abs_intCast_sub | C | PAG254::dP_lt_one_iff, PAG254::exists_padicValRat_eq | a, b を 2 進付値として実現し（p=2）、dP_lt_one_iff の否定と dP の定義を使えば 4 行ほど（遠回りだが成り立つ） | 中 |
| PAG259::padicValRat_mul_zpow_zpow | D | — | 付値の計算。前の鎖に見つからない | 中 |
| PAG259::padicValRat_prime_ne | D | — | Mathlib から直接出る（異なる素数での付値は 0）。前の鎖に見つからない | 中 |
| PAG259::padicValRat_prime_zpow | D | — | 付値の計算。前の鎖に見つからない | 中 |
| PAG259::padicValRat_prod_zpow | D | — | 付値の計算。前の鎖に見つからない | 中 |
| PAG259::rho | D | — | 新しい写像（PAG194::rho とは同名の別物） | 高 |
| PAG259::rhoBox | D | — | 前の鎖には無い（同じファイルの rho と同じ値で、終域 BoxCoord の位相だけが違う） | 高 |
| PAG259::rho_one | D | — | rho（新）の値。Mathlib だけで自明 | 高 |
| PAG259::rho_one_mem_closure_ne_one | D | — | rho（新）についての文 | 高 |
| PAG259::rho_sep | D | — | 同じファイルの exists_prime_one_le_abs を rho で書き直したもの | 高 |
| PAG259::sep_of_commensurable | D | — | 通約可能な L₁, L₂ の整数結合は L₁/n 以上離れる。前の鎖に見つからない | 中 |
| PAG259::sep_of_inf_unmeasured | B | PAG254::dP_lt_one_iff（PAG254::dP の定義） | dP s q r は v_s q − v_s r の絶対値そのものなので、dP_lt_one_iff の否定がそのまま結論 | 高 |
| PAG259::sep_of_mem_zmultiples | D | （関連）PAG254::dInf_zpow | c の整数倍どうしは c 以上離れる。文としては前の鎖に見つからない | 中 |
| PAG259::threshold_iff | D | — | imgST（新）についての文 | 高 |
| PAG259::val_ne_of_mem_of_not_mem | D | — | Nat.Primes についての自明な補題。前の鎖に見つからない | 中 |
| PAG259::zpow_ge_of_one_lt | D | — | 実数のべきの補題。前の鎖に見つからない | 中 |

**PAG260（Part 256、26 件）**

| 宣言 | 判定 | 前の宣言 | 根拠（1 行） | 確信度 |
|---|---|---|---|---|
| PAG260::UA1_charU_prodChar | D | （関連）PAG258::UA1_charU | 同じファイルの phaseA1_prodChar（新）を UA1_charU に入れれば 1 行 | 中 |
| PAG260::cast_crtMap_fst | B | PAG193::param_cast₁ | crtMap≡param、`castHom h R x`≡`x.cast`（定義を展開すれば同じ） | 高 |
| PAG260::cast_crtMap_snd | B | PAG193::param_cast₂ | 同上 | 高 |
| PAG260::charU_prodChar | B | PAG236::charMul_apply_unit（PAG257::charU の定義） | charU・prodChar・unitsMap を展開すると charMul_apply_unit そのもの | 高 |
| PAG260::crossSign | A | PAG198::rs | `rs ψ χ := if ψ(−1)=1 then 1 else χ(−1)` は、χ(−1)=±1（PAG198::neg_one_sq_eq）より全入力で crossSign と同じ値になる（式は別、定義上の同一ではない） | 中 |
| PAG260::crossSign_of_even_left | D | — | 新しい定義 crossSign から自明（rs の値を計算する補題も前の鎖に無い） | 高 |
| PAG260::crossSign_of_even_right | D | — | 同上 | 高 |
| PAG260::crossSign_of_odd | D | — | 同上 | 高 |
| PAG260::cross_eq_sign_of_rootNum_one | D | （関連）PAG198::real_reciprocity | 同じファイルの rootNum_prodChar から数行。結論 χ₁(N)χ₂(M)=crossSign(=rs) は real_reciprocity と同じ形だが、仮定が違う | 中 |
| PAG260::crtMap | A | PAG193::param | 本体の式 `((x.1.val*N + x.2.val*M : ℕ) : ZMod (M*N))` が同一 | 高 |
| PAG260::crtMap_bijective | A | PAG193::param_bijective | crtMap≡param とみれば同文 | 高 |
| PAG260::exists_primitive_odd_five | D | （関連）PAG256::exists_primitive_even_five, PAG172::exists_quartic, PAG171::primitive_of_ne_one | mod 5 の奇原始指標の存在は前の鎖に見つからない。位数 4 の指標から作ると、奇であることの議論で十数行かかる | 中 |
| PAG260::gaussSum_prodChar | A | PAG193::gaussSum_mul_coprime | prodChar を展開すると同文 | 高 |
| PAG260::isPrimitive_prodChar | A | PAG194::isPrimitive_mul, PAG236::isPrimitive_charMul | prodChar≡changeLevel の積≡charMul とみれば同文 | 高 |
| PAG260::norm_char_unit | C | PAG202::normSq_chi_unit, PAG198::neg_one_sq_eq | n≠0 は normSq を norm に書き換えるだけ（1〜2 行）。NeZero なしで入る n=0（ℤ の単元 ±1）も χ(−1)=±1 で数行 | 高 |
| PAG260::norm_cross | C | PAG199::normSq_chi_natCast, PAG200::chi_level_one | 各因子に normSq_chi_natCast を当てて norm_mul。NeZero なしの退化した場合（M=0 なら N=1）は chi_level_one で済む | 高 |
| PAG260::parFac_prodChar | C | PAG204::changeLevel_neg_one, PAG198::neg_one_sq_eq（PAG256::parFac の定義） | prodChar(−1)=χ₁(−1)χ₂(−1) を出し、χᵢ(−1)=±1 の 4 通りを計算。PAG198::gs_combine（gs 版の同じ分解）と同じ形 | 中 |
| PAG260::phaseA1_prodChar | D | （関連）PAG258::phaseA1_of_isPrimitive, PAG194::isPrimitive_mul | 同じファイルの rootNum_prodChar（新）に依存 | 中 |
| PAG260::phaseA1_prodChar_ne_mul | D | — | 新しい反例（mod 3 × mod 5） | 高 |
| PAG260::prodChar | A | PAG236::charMul, PAG199::cmul | `changeLevel (dvd_mul_right) χ₁ * changeLevel (dvd_mul_left) χ₂` で同じ式 | 高 |
| PAG260::prodChar_apply | A | PAG236::charMul_apply（PAG199::cmul_apply、PAG193::mul_changeLevel_apply も） | prodChar≡charMul とみれば同文（cmul_apply などは castHom で書いた形） | 高 |
| PAG260::prodChar_neg_one | B | PAG204::changeLevel_neg_one | MulChar の積の値に changeLevel_neg_one を 2 回使えば 1 行（PAG193::mul_changeLevel_apply＋PAG198::castHom_neg_one でも出る） | 高 |
| PAG260::rootNum_prodChar | D | （関連）PAG256::rootNum_eq, PAG193::gaussSum_mul_coprime, PAG193::z_mul_coprime, PAG198::gs_combine | rootNum = zN/gs とみれば z_mul_coprime と gs_combine の比。前の宣言 4〜5 個を組み合わせるので C との境界 | 中 |
| PAG260::rootNum_prodChar_eq_neg_mul | D | — | 新しい例（mod 3 × mod 13） | 高 |
| PAG260::rootNum_prodChar_ne_mul | D | — | 新しい例（mod 3 × mod 5） | 高 |
| PAG260::stdAddChar_crtMap | A | PAG193::stdAddChar_param | crtMap≡param とみれば同文 | 高 |

### 2. A・B・C の件数と一覧

- **A：8 件**（すべて PAG260）
  - prodChar、crtMap、crtMap_bijective、stdAddChar_crtMap、prodChar_apply、gaussSum_prodChar、isPrimitive_prodChar
  - crossSign（値として一致するという意味での A）
- **B：6 件**
  - PAG259::closure_logSet、PAG259::sep_of_inf_unmeasured
  - PAG260::cast_crtMap_fst、PAG260::cast_crtMap_snd、PAG260::charU_prodChar、PAG260::prodChar_neg_one
- **C：5 件**
  - PAG259::exists_near_measured、PAG259::one_le_abs_intCast_sub
  - PAG260::norm_char_unit、PAG260::norm_cross、PAG260::parFac_prodChar
- **D：56 件**（PAG259 が 45、PAG260 が 11）
  - うち一般化と添えたもの：PAG259::dense_closure_log_primes、PAG259::exists_padicValRat_eq、PAG259::exists_zpow_near・exists_near_of_two_unmeasured（言い換え込みで PAG254 の (2,3) 版の一般化）。
- **境界にある判定**
  - C と D の境界：exists_near_measured と parFac_prodChar は C、rootNum_prodChar は D にしました。
  - A の解釈：crossSign は定義上の同一ではなく、値の一致です。
- **まとめ**
  - PAG259 はほぼ新しい内容です（A〜C は 49 件中 4 件）。
  - PAG260 は前半（CRT の写像と積の指標の基本性質）が PAG193・194・236 の重複で、26 件中 15 件が A〜C です。
  - Part 256 で新しいのは、crossSign による偶奇の因子と、その反例です。

### 3. 気づいたこと

**前の鎖の中どうしの重複（担当外）**
- 同じ対象が 3 つの名前で定義されています：PAG199::cmul ≡ PAG236::charMul（PAG260::prodChar が 3 つ目）。
  - 付随する重複：cmul_apply ≈ charMul_apply ≈ PAG193::mul_changeLevel_apply。
  - PAG200::cmul_mul_cmul ≈ PAG236::charMul_mul（左右が逆なだけ）。
  - PAG194::isPrimitive_mul ≈ PAG236::isPrimitive_charMul。
- PAG199::normSq_chi_natCast ≈ PAG202::normSq_chi_unit（「互いに素な自然数」と「単元」の言い換え）。PAG193::chi_unit_root も同じ事実です。
- PAG254::dense_logSet_coprime は、PAG253::exists_cls_near で a=1 として類の条件を捨てれば出ます（B）。
- PAG171::primitive_of_ne_one ≡ PAG256::isPrimitive_of_prime_of_ne_one（同文）。
- PAG198::level_two_trivial ≈ PAG257::eq_one_of_two。
- PAG195::ne_one_of_isPrimitive と PAG257::not_isPrimitive_one_of_two_le は、対偶で同値です。
- PAG72::prim4_neg_one ≈ PAG151::neg_one_mod4（違いは 2^2 と 4 の書き方だけ）。
- PAG31・PAG46・PAG116 の lam_pos は同じ文が 3 回出ます。
- PAG198::neg_one_sq_eq と PAG256::neg_one_mul_self は同じ事実です（χ(−1)=±1 と χ(−1)²=1）。

**担当内のこと**
- PAG260 に何度も出る χ₁(N)χ₂(M) は、定義上 PAG237::gaugeFactor M N χ₁ χ₂ そのものです。
- PAG259::rhoBox は rho と同じ値です。exists_prime_one_le_abs と rho_sep も、rho を展開すれば同じです。
- PAG259::exists_near_measured の p, r に関する仮定は、PAG254 経由なら要りません。
- 名前の衝突（名前空間が違うのでエラーにはならない）：PAG259::exists_padicValRat_eq と PAG254 の同名定理、PAG259::rho と PAG194::rho。
- PAG260::rootNum_prodChar は、crossSign=PAG198::rs とみれば「PAG193::z_mul_coprime ÷ PAG198::gs_combine」の形です。
- PAG260::cross_eq_sign_of_rootNum_one の結論は PAG198::real_reciprocity と同じ式です。
  - 実原始指標なら、3 つの rootNum が 1 という仮定は PAG198::gaussSum_real から成り立ちます。
  - したがって real_reciprocity は cross_eq_sign_of_rootNum_one から出る、という関係にあります。ただし深い内容は仮定の側にあります。

**候補の選び方の弱点**
- 定義の展開を見ていないため、答えになる宣言が候補に入っていませんでした。展開が要る対応は次のとおりです。
  - prodChar↔charMul、crtMap↔param、castHom↔cast、norm↔normSq、crossSign↔rs
- 候補から漏れていた宣言（判定に使ったもの）：
  - PAG193::param_cast₁・param_cast₂
  - PAG202::normSq_chi_unit、PAG199::normSq_chi_natCast
  - PAG204::changeLevel_neg_one、PAG198::castHom_neg_one
  - PAG198::rs、PAG198::gs_combine
  - PAG236::charMul_apply_unit
  - PAG172::exists_quartic
  - exists_zpow_near などに対する PAG254::dense_closure_log_two_three

**材料の弱点**
- statements_all.txt では、名前の無い instance が同じ見出し「PAGk::」で上書きされているようです（推測、確信度 中）。
  - 根拠 1：PAG258 の見出しは 505 行目の instance の本文なのに、480 行目と 499 行目の宣言のあいだに置かれている。
  - 根拠 2：pullSys が使う `≤` の instance が載っていない。
  - 根拠 3：PAG259 の `instance : DiscreteTopology BoxCoord := ⟨rfl⟩` が前提にする TopologicalSpace BoxCoord が載っていない。
- PAG170::orderOf_zeta_prod_mixed の文が `let ζi` で途切れています。
- targets.md は instance を対象に含めていないので、PAG259 の DiscreteTopology と PAG260 の `NeZero (M * N)` は判定していません。

### 4. 使った検索語の一覧

Grep ツールが無いため、検索語による全文検索はしていません。代わりに次の行範囲を Read で通読し、下の語を目で探しました。

**読んだ行範囲（statements_all.txt）**
- 1–80、3000–3024、6000–6024、8300–8309
- 8700–9309、9500–11928
- 12900–12924、13000–13011、14500–14539、16000–16011、17200–17211
- 17450–18019、18500–18511、19500–19539
- 20400–20598、21000–22569

**ファイル単位では**
- 全部読んだ：PAG167〜179、PAG185〜204、PAG236〜237、PAG253〜260
- 一部だけ読んだ：PAG166・180・184・205・235・238・250・252
- 数十行の抜き取りだけ：上記以外（PAG3〜165、PAG181〜183、PAG206〜234、PAG239〜249 などは大部分を読んでいない）

**目で探した語**
- padicValRat、padicValNat、Real.log、logSet、dP、dInf、Dense、closure、AddSubgroup.closure、zmultiples、Irrational、Nat.Primes、DiscreteTopology、IsClosed、Subsingleton
- changeLevel（積の形）、charMul、cmul、param、crt、castHom、ZMod.cast、unitsMap、chineseRemainder
- gaussSum、stdAddChar、zN、rootNum、gs、rs
- `χ (-1)`、Odd、Even、normSq、`‖χ`
- IsPrimitive、`ℂ 5`、`orderOf … = 4`
