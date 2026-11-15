# R4 照合報告：PAG258（Part 254）の宣言 72 件の判定

**結果：** A 0 件、B 4 件、C 5 件、D 63 件。

**作業条件について：**
- 依頼文で許された Grep ツールは、この環境では使えませんでした。代わりに Read で行範囲を指定して statements_all.txt を読みました。シェルの grep は制約に従い使っていません。
- 読んでいない範囲が残っています（4 章に記載）。D の多くは「読んだ範囲では見つからなかった」という意味で、「ない」ことの証明ではありません。
- B と C の導出は文面から見積もったもので、Lean でのコンパイル確認はしていません。
- 根拠に出てくる Mathlib の補題名（`primitiveCharacter_isPrimitive`、`conductor_one`、`conductor_ne_zero`、`ZMod.unitsMap_surjective`、`Module.DirectLimit.map_apply_of`、`of_injective`）は記憶によるもので、この環境では確認していません。

## 1. 判定表

確信度は「その判定が正しい」ことへの確信です。D の行では、類例を「前の宣言」欄ではなく根拠欄に書きました。

| 宣言 | 判定 | 前の宣言 | 根拠（1 行） | 確信度 |
|---|---|---|---|---|
| Gsp | D | | Lvl 上の単数群関数空間を表す新しい略記。前の鎖に同じ値の定義はない | 高 |
| Lim | D | | Module.DirectLimit による帰納極限。読んだ範囲に DirectLimit はない。PAG255::unitSys（単数群の射影系、ℕ+ 添字）と双対の構成 | 高 |
| Lvl.pos | D | | 新しい構造体 Lvl の自動生成フィールド。Mathlib の PNat.pos に当たるが、前の鎖の宣言ではない | 高 |
| Lvl.val | D | | 同上（PNat.val に当たる） | 高 |
| TopL_not_compat | D | | 水準 1→2 で引き戻しと TopL が交換しない。PAG256::removal_counterexample_normSq と PAG257::TopL_charU を使うが、議論は十行程度。同ファイルの TopL_not_compat_prime の p=2 の場合 | 高 |
| TopL_not_compat_prime | D | | 上の素数版。PAG257::normSq_rootNum_one_prime と関連する | 高 |
| UA1 | D | | phaseA1 を固有値とする新しい作用素の定義 | 高 |
| UA1_bijective | D | | 全空間での全単射。PAG257::unitary_Vprim（Vprim 上）を全空間へ広げた形 | 高 |
| UA1_charU | C | PAG257::ip_charU | UA1 を展開し、直交性で和を 1 項に潰す（5〜8 行。C と D の境界） | 低 |
| UA1_charU_eq_pull_TopL | D | | 同ファイルの UA1_charU、pullL_charU と、Mathlib の primitiveCharacter の性質が必要 | 中 |
| UA1_comp_TopL | D | | 両者とも charU 基底で対角（PAG257::TopL_charU、span_charU_eq_top）だが、UA1_charU を経由するので数行では済まない | 中 |
| UA1_comp_pullL | D | | 水準変更との可換性。前の鎖に pullL がない | 高 |
| UA1_eq_TopL_of_mem_Vprim | D | | PAG257::TopL_eq_of_A1 を当てはめるだけだが、前提として同ファイルの UA1_charU と phaseA1_of_isPrimitive が要る | 中 |
| UA1_family_unique | D | | 水準の族としての一意性。前の鎖に対応するものはない | 高 |
| UA1_mem_Vimprim | D | | PAG257::TopL_mem_Vimprim の UA1 版（類例） | 中 |
| UA1_mem_Vprim | D | | 同ファイルの UA1_eq_TopL_of_mem_Vprim と PAG257::TopL_mem_Vprim から 1 行。前の鎖だけでは出ない | 中 |
| UA1_mem_condPart | D | | condPart が新しい定義 | 高 |
| UA1_ne_TopL_prime | D | | 前半は PAG257::charU_one_mem_Vimprim（N := p）の特殊化。後半が新しい | 中 |
| UA1_pullL_of_mem_Vprim | D | | pullL も UA1 も新しい | 高 |
| UA1_star | D | | 同ファイルの phaseA1_inv が必要 | 高 |
| UA1_unique | D | | PAG257::TopL_eq_of_A1（Vprim 上の一意性）の全空間版に当たる | 高 |
| Uinf | D | | 帰納極限上の作用素の定義 | 高 |
| Uinf_bijective | D | | 新しい | 高 |
| Uinf_ofL | D | | Mathlib の DirectLimit.map_apply_of から出る。前の鎖は使わない | 高 |
| Uinf_ofL_of_mem_Vprim | D | | 同ファイルの補題の組合せ | 高 |
| Uinf_unique | D | | Mathlib の帰納極限の普遍性による | 高 |
| Uinf_unique_TopL | D | | 同ファイルの span_ofL_Vprim などが必要 | 高 |
| condPart | D | | 前の PAG257::Vprim を一般化したもの（q = N のとき、IsPrimitive の定義により Vprim N と一致） | 高 |
| condPart_eq_map | D | | pullL が新しい定義 | 高 |
| conductor_neZero | D | | Mathlib の conductor_ne_zero から 1 行のインスタンス。読んだ範囲に同種のインスタンスはない | 中 |
| eq_zero_of_ipLim_self | D | | PAG257::eq_zero_of_ip_self、PAG229::herm_self_eq_zero の極限版（類例） | 高 |
| gaussSum_inv | B | PAG9::conj_gaussSum, PAG9::chi_neg_one_sq | conj_gaussSum を χ(-1)² = 1 で解き直すだけ（`rw [conj_gaussSum, ← mul_assoc, chi_neg_one_sq, one_mul]`。B と C の境界） | 高 |
| iSupIndep_condPart | D | | PAG257::linearIndependent_charU から部分族のスパンの独立性を示す議論で、数行では済まない。類例は PAG220::layerPart_iSupIndep | 中 |
| iSup_condPart | C | PAG257::span_charU_eq_top | charU χ が condPart N (conductor χ) に入ることと span_le で 3 行 | 高 |
| ipLim | D | | 帰納極限上の内積の定義 | 高 |
| ipLim_Uinf | D | | 新しい | 高 |
| ipLim_add_right | D | | PAG229::herm_add_right の極限版（類例） | 高 |
| ipLim_conj | D | | PAG229::herm_conj の極限版（類例） | 高 |
| ipLim_ofL | D | | 同ファイルの ipn_eq_of_ofL_eq が必要 | 高 |
| ipLim_ofL_Vprim | D | | 新しい（水準をまたぐ原始部分の直交） | 高 |
| ipLim_self_nonneg | D | | 新しい | 高 |
| ipLim_smul_right | D | | PAG253::ipG_smul_right の極限版（類例） | 高 |
| ipR | D | | ip f を線形汎関数にまとめた定義。読んだ範囲に同じ値の定義はない | 中 |
| ip_UA1 | D | | 全空間での等長性。PAG257::ip_TopL_of_mem_Vprim（Vprim 上）を全空間へ広げた形 | 高 |
| ip_add_right | B | PAG257::ip_sum_right | ip_sum_right の 2 項（Fin 2、係数 1）の場合。ip の定義を展開しても 1 行。ZMod 版は PAG229::herm_add_right | 中 |
| ip_condPart | D | | PAG257::ip_charU からのスパン帰納（PAG257::ip_Vprim_Vimprim と同じ型の議論）で、数行では済まない | 中 |
| ip_pullL | D | | 同ファイルの sum_units_unitsMap に依存する。類例は PAG201::conv_pull（ZMod 版のスケール則） | 中 |
| ip_smul_right | B | PAG253::ipG_smul_right, PAG257::ip_smul_smul | ip は G=(ZMod N)ˣ の ipG と定義上同じ値なので、ipG_smul_right の特殊化（ip_smul_smul で a=1 としても出る） | 高 |
| ipn | D | | Lvl 上の正規化内積の定義 | 高 |
| ipn_eq_of_ofL_eq | D | | 新しい | 高 |
| ipn_pullSys | D | | 同ファイルの ip_pullL に依存する | 中 |
| normSq_phaseA1 | B | PAG256::normSq_rootNum | phaseA1 を展開し、Mathlib の primitiveCharacter_isPrimitive を渡すだけ | 高 |
| ofL | D | | Module.DirectLimit.of の略記 | 高 |
| ofL_charU | D | | 新しい | 高 |
| ofL_injective | D | | Mathlib の DirectLimit.of_injective と同ファイルの pullL_injective から | 高 |
| phaseA1 | D | | rootNum χ.primitiveCharacter の定義。rootNum を扱う前のファイルは PAG256 と PAG257 だけで、そこに同値の定義はない | 高 |
| phaseA1_changeLevel | D | | 同ファイルの rootNum_congr と primitiveCharacter の性質が必要。関連は PAG208::conductor_changeLevel_inv | 中 |
| phaseA1_inv | D | | 同ファイルの rootNum_inv、primitiveCharacter_inv_apply、rootNum_congr が必要 | 中 |
| phaseA1_of_isPrimitive | D | | 水準 conductor = N の移送に同ファイルの rootNum_congr が必要 | 中 |
| phaseA1_one | C | PAG196::zN_level_one | Mathlib の conductor_one で水準 1 に落とし、偶性（ZMod 1 では -1 = 1）を示して zN_level_one を使う（4〜6 行。C と D の境界） | 低 |
| primitiveCharacter_inv_apply | D | | 読んだ範囲に primitiveCharacter を扱う宣言はない。関連は PAG208::exists_primitive_changeLevel | 中 |
| pullL | D | | 単数群上の unitsMap による引き戻し。類例は PAG201::pull（ZMod N → ℂ の castHom による引き戻し） | 中 |
| pullL_charU | D | | 単数での changeLevel の値を述べる補題は見つからない。あるのは自然数版の PAG199::changeLevel_natCast と PAG211::changeLevel_natCast_eq だけ | 中 |
| pullL_injective | D | | Mathlib の unitsMap_surjective から出る。類例は PAG206::pull_injective（ZMod 版、N∣N·t の場合） | 中 |
| pullSys | D | | 同ファイルの pullL の Lvl 版 | 高 |
| rootNum_congr | D | | rootNum の水準移送補題。PAG256、PAG257 にない。類例は PAG196::zN_hall_congr | 高 |
| rootNum_inv | D | | PAG9::conj_gaussSum と inv_apply_neg_one から、偶奇の場合分けで十行程度。抽象版の関連は PAG253::conj_eigen_of_adjoint | 中 |
| rootNum_one_of_eq_one | C | PAG196::zN_level_one | 1 は偶なので rootNum 1 = zN 1。同じ hL : L = 1 の形の zN_level_one で 2〜3 行（PAG203::gaussSum_level_one でも出る） | 高 |
| rootNum_one_prime | C | PAG257::gaussSum_one_prime | rootNum を展開し、gaussSum 1 = -1 と 1 の偶性で 2〜3 行。PAG257::normSq_rootNum_one_prime を強めた形 | 高 |
| span_ofL_Vprim | D | | 新しい | 高 |
| sum_units_unitsMap | D | | unitsMap のファイバーの数え上げ。読んだ範囲にない。類例は PAG201::card_ker_cast（ZMod の castHom の核の個数） | 中 |
| totient_ne_zero' | D | | Mathlib の Nat.totient_pos から 1 行。読んだ範囲に (Nat.totient N : ℂ) ≠ 0 の補題はない | 中 |

## 2. A・B・C の件数と一覧

- **A：0 件**
- **B：4 件**
  - gaussSum_inv
  - ip_add_right
  - ip_smul_right
  - normSq_phaseA1
- **C：5 件**
  - iSup_condPart
  - rootNum_one_of_eq_one
  - rootNum_one_prime
  - UA1_charU（低）
  - phaseA1_one（低）
- D：63 件

## 3. 気づいたこと

**担当外で見つけた、前の鎖どうしの重複**
- PAG257::ip（定義）は PAG253::ipG の G=(ZMod N)ˣ の場合と同じ値です。定義の A 相当（高）。
- PAG229::herm（定義）は PAG52::ip（定義）と同じ値です（どちらも ZMod N 上）。定義の A 相当（高）。
- PAG256::inv_apply_neg_one は PAG9::inv_apply_neg_one と同じ文です。DirichletCharacter ℂ N は MulChar (ZMod N) ℂ の略記だからです。A（高）。
- PAG256::neg_one_mul_self は PAG9::chi_neg_one_sq と同じ文です。A（高）。
- PAG257::eq_one_of_two は PAG198::level_two_trivial で L := 2 とすれば出ます。B（高）。
- PAG257::not_isPrimitive_one_of_two_le は PAG195::ne_one_of_isPrimitive の対偶です。B（高）。
- PAG236::charMul（定義）は PAG199::cmul（定義）と同じ値です。また PAG236::charMul_mul は PAG200::cmul_mul_cmul とほぼ同じです。A 相当（高／中）。
- PAG203::gaussSum_level_one は PAG195::z_level_one から √1 = 1 で出ます。B〜C（中）。
- PAG217::inner_smul_left' は PAG208::inner_smul_smul で b = 1 とすれば出ます。B（中）。

**PAG258 の中での重複・関係**
- TopL_not_compat は同ファイルの TopL_not_compat_prime の p=2 の場合です。
- ip_UA1、UA1_bijective、UA1_unique は、それぞれ PAG257::ip_TopL_of_mem_Vprim、unitary_Vprim、TopL_eq_of_A1 を全空間へ広げた形です。

**担当一覧から漏れている可能性**
- targets.md に次のものが載っていません。
  - 構造体 Lvl そのもの
  - Lvl 上の順序のインスタンス。statements_all.txt の 480〜499 行の間に見当たりませんが、pullSys は h : a ≤ b をそのまま a.val ∣ b.val として使っているので、ソースのどこかにあるはずです。
  - 帰納極限に必要な IsDirected・Nonempty のインスタンス
  - 名前が空欄の DirectedSystem インスタンス（「PAG258::（instance、505 行）」）
- 抽出漏れの可能性があります。

**候補の選び方の弱点**
- 値が同じでも定数名が違う前の宣言を拾えていません。例：
  - ipG と ip
  - zN、gaussSum_level_one と、水準 1 の rootNum
  - ZMod 版の pull・pull_injective・card_ker_cast と、pullL 系
- gaussSum_inv に必要な PAG9::chi_neg_one_sq が候補に入っていません。
- UA1 系・ipLim 系の多くに、同じ汎用の 6 件（ip_charU、rootNum_ne_zero、ip_smul_smul など）が並んでいます。頻出する定数に引きずられているようです。
- conductor_neZero の候補は導手の値に関する補題ばかりで、NeZero とは関係がありません。
- Lvl.val は候補が 0 件でした。

## 4. 使った検索語の一覧

Grep が使えなかったので、以下の語を探しながら該当範囲を Read で読みました。

**探した語**
- gaussSum χ⁻¹ / conj_gaussSum / chi_neg_one_sq / neg_one_mul_self
- rootNum / zN / level_one / ZMod 1 / DirichletCharacter ℂ 1
- primitiveCharacter / conductor / NeZero
- unitsMap / changeLevel（単数版・natCast 版）
- pull / pull_injective / card_ker / fiber
- totient … ≠ 0
- ipG / herm / inner_ / add_right / smul_right / conj / →ₗ[ℂ] ℂ
- DirectLimit / DirectedSystem / structure / ℕ+
- span / iSupIndep / iSup / Vprim / charU / TopL

**読んだ範囲**
- targets.md と candidates.md は全体を読みました。
- statements_all.txt（全 22,204 行）で読んだ行：
  - 1–40
  - 230–269
  - 380–579（PAG7 後半〜PAG10 冒頭）
  - 10560–12787（PAG194 末〜PAG211 前半）
  - 13560–13899（PAG217 後半〜PAG218）
  - 15960–16089（PAG229）
  - 17450–17757（PAG236）
  - 20900–22204（PAG252 末〜PAG258 全体）
  - このほか、位置を確かめるために約 10 箇所を数行ずつ見ました。

**読んでいない範囲**
- PAG1〜PAG193 の大部分
- PAG211 後半〜PAG216
- PAG219〜PAG228
- PAG230〜PAG235
- PAG237〜PAG251

このため、古い概念だけで書かれた宣言の D 判定は「中」にとどめています。対象は conductor_neZero、totient_ne_zero'、sum_units_unitsMap、pullL、pullL_charU、pullL_injective、primitiveCharacter_inv_apply、ipR です。
