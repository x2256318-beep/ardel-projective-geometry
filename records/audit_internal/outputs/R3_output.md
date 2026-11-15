**R3 照合結果：PAG257（Part 253）の宣言 41 件**

**最初に断っておくこと**
- この環境には Grep ツールがありませんでした。制約どおりシェルは使わず、Read（範囲指定）だけで探しています。
- targets.md と candidates.md は全文を読みました。statements_all.txt（22,569 行）で読めたのは約 5,600 行（約 25%）です。
  - 読んだ範囲：行 1–1417（PAG2–22）、5560–5829（PAG95–105）、6560–6899（PAG116–121）、8640–8999（PAG165–173）、10560–11429（PAG194–200）、13640–13908（PAG217 末–218）、15380–16199（PAG226–229）、16725–17004（PAG232–233）、21000–21917（PAG252 末–258 冒頭。PAG253–256 は全文）、22520–22569。
  - ほかに位置合わせのため、約 20 か所を 10 行ずつ読みました。
- このため、D は「読んだ範囲と候補の中に見つからなかった」という意味です。「ない」ことの証明ではありません。
- statements_all.txt は PAG2 から始まっていて、PAG1 が入っていません。PAG3 と PAG253 が使う PAG.charFun・PAG.transl・PAG.rev の定義文は確認できませんでした。

## 1. 表

| 宣言 | 判定 | 前の宣言 | 根拠（1 行） | 確信度 |
|---|---|---|---|---|
| JHL | C | PAG256::JH | toFun は JH そのもの。線形性の証明（各 5 行ほど）を足して線形写像にまとめただけ。PAG256 に JH・hartley の線形性補題はない | 中 |
| TopL | D | | JHL ∘ extL。単数群上の関数に働くハートレー型の作用素は前の鎖に見当たらない | 中 |
| TopL_charU | C | PAG256::JH_eq_rootNum_mul_any | extL (charU χ) = χ（Mathlib の MulChar.map_nonunit）とすれば、JH χ u = rootNum χ * χ u の言い直しになる。4〜5 行 | 中 |
| TopL_charU_one_four | C | PAG256::removal_counterexample_four、PAG256::JH_eq_rootNum_mul_any | normSq(rootNum 1₄) = 0 から rootNum 1₄ = 0 を出し、固有値の式に入れる。≠0 は u = 1 で評価。6〜8 行で D との境目 | 低 |
| TopL_eq_of_A1 | D | | Vprim 上での一意性（span の帰納法）。前の鎖に対応するものがない | 中 |
| TopL_mem_Vimprim | D | | Vimprim は PAG257 の新しい定義。TopL_charU と span の帰納法による | 中 |
| TopL_mem_Vprim | D | | 同上（Vprim） | 中 |
| Vimprim | D | | 非原始指標を単数群に制限して張る部分空間。同じ対象はない（PAG227::Prim は添字の部分型にすぎない） | 中 |
| Vprim | D | | 同上（原始指標） | 中 |
| Vprim_inf_Vimprim | D | | PAG257 内の ip_Vprim_Vimprim と eq_zero_of_ip_self から出る。前の鎖からは出ない | 中 |
| Vprim_ne_bot_prime | C | PAG119::Lc_ne_one（または PAG196::exists_generator）、PAG256::isPrimitive_of_prime_of_ne_one（PAG171::primitive_of_ne_one、PAG32::prim_level_p_iff でも可） | p ≥ 3 では Lc p ≠ 1 が原始指標になり、その charU が Vprim に入って u = 1 で値 1。6〜8 行で境目 | 低 |
| Vprim_ne_bot_three | C | PAG256::exists_primitive_odd_three | 原始指標 χ mod 3 の charU が Vprim 3 に入り、χ 1 = 1 なので 0 でない。5 行ほど | 中 |
| Vprim_sup_Vimprim | D | | PAG257 内の span_charU_eq_top による。前の鎖からは出ない | 中 |
| Vprim_two | B | PAG30::no_prim_mod_two | 法 2 に原始指標がないので張る集合が空になり、span = ⊥。1〜2 行 | 中 |
| charU | B（推定） | PAG.charFun（定義は材料外。PAG1 と推定）＋ Mathlib の MulChar.toUnitHom | charU χ = PAG.charFun χ.toUnitHom になるはず。charFun の型は PAG3・PAG253 の使い方から推定しただけで、定義文は未確認 | 低 |
| charU_one_mem_Vimprim | B | PAG195::ne_one_of_isPrimitive | subset_span ⟨⟨1, fun h => ne_one_of_isPrimitive hN 1 h rfl⟩, rfl⟩ の 1 行 | 中 |
| eq_one_of_two | B | PAG198::level_two_trivial | level_two_trivial rfl χ。仮定 L = 2 に rfl を入れるだけなので、実質 A | 高 |
| eq_zero_of_ip_self | D | 類似：PAG229::herm_self_eq_zero | 同じ形の主張は ZMod N 上だけ。添字型が (ZMod N)ˣ なので特殊化では出ない。ipG にもこの補題はない | 中 |
| extL | D | | 単数群からの零延長（線形写像）。PAG23::extS／extN は P1F 上の別物 | 中 |
| extL_apply | D | | PAG257::extL の定義を書き写しただけの rfl 補題 | 高 |
| extL_charU | D | | Mathlib の MulChar.map_nonunit と定義の展開だけで出る。前の鎖の宣言は要らない | 中 |
| gaussSum_one_prime | D | 関連：PAG19::ram、PAG22::ram_pull、PAG118::sum_mult_eq_zero、PAG119::psi_one_primitive | 同じ文はない。ラマヌジャン和を使えば法 p^(0+1) で同じ値 −1 が出るが、ZMod p への移し替えが要る。後の 2 つを使う証明は 10 行ほど | 中 |
| ip | A | PAG253::ipG（G := (ZMod N)ˣ） | 本体が同じ式 ∑ conj(f x)·g x で、rfl で一致する。同じ式は PAG52::ip と PAG229::herm にもある（ZMod N 上） | 高 |
| ip_TopL_charU_prim | D | | PAG257 内なら数行で出るが、前の鎖だけからだと宣言が 5〜6 個要る | 中 |
| ip_TopL_of_mem_Vprim | D | | 上の主張を span の帰納法で広げたもの | 中 |
| ip_Vprim_Vimprim | D | | 直交性（PAG257::ip_charU）を span に広げたもの | 中 |
| ip_charU | C | PAG218::sum_units_char、PAG3::conj_apply_eq_inv | conj(χ u)·ψ u = (χ⁻¹ψ)(u) とし、sum_units_char を χ⁻¹ψ に使う（χ⁻¹ψ = 1 ↔ χ = ψ）。4 行ほど | 中 |
| ip_smul_smul | B | PAG253::ipG_smul_left、PAG253::ipG_smul_right | ip = ipG（rfl）なので、この 2 つで書き換えるだけ | 高 |
| ip_sum_right | D | 類似：PAG212::inner_sum_smul_right | 同じ形の主張は ZMod N 上だけ。ipG の和の補題は PAG253 にない | 中 |
| ip_sum_sum | D | 類似：PAG212::inner_sum_smul_left、inner_sum_smul_right | 同上 | 中 |
| isCompl_Vprim_Vimprim | D | | PAG257 内の Vprim_sup_Vimprim と Vprim_inf_Vimprim を組み合わせたもの | 中 |
| linearIndependent_charU | D | | 読んだ範囲にも候補にもない（PAG1 は未確認） | 中 |
| map_TopL_Vprim | D | | PAG257 内の TopL_mem_Vprim と rootNum_ne_zero による | 中 |
| normSq_rootNum_one_prime | D（前の PAG256::removal_counterexample_normSq を一般化） | | PAG256 にあるのは p = 2（値 1/2）の場合だけ。一般の p には新しい gaussSum_one_prime が要る | 中 |
| not_isPrimitive_one_of_two_le | B | PAG195::ne_one_of_isPrimitive | fun h => ne_one_of_isPrimitive hN 1 h rfl（対偶を χ = 1 に特殊化） | 高 |
| not_isPrimitive_one_prime | B | PAG32::prim_level_p_iff（PAG195::ne_one_of_isPrimitive でも可） | fun h => (prim_level_p_iff 1).mp h rfl | 高 |
| not_isometry_Vimprim_prime | D | | 新しい normSq_rootNum_one_prime を使う。PAG257 内の not_isometry_Vimprim_two を素数全体に広げたもの | 中 |
| not_isometry_Vimprim_two | D | 関連：PAG256::removal_counterexample、removal_counterexample_normSq、JH_eq_rootNum_mul_any | 数値の中身は PAG256 の値 1/2。ただし作用素の形にするには宣言 4〜5 個と 10 行ほどが要る。C との境目 | 低 |
| rootNum_ne_zero | B | PAG256::normSq_rootNum | normSq = 1 なので 0 でない。1 行 | 高 |
| span_charU_eq_top | D | | 読んだ範囲にも候補にもない（PAG1 は未確認） | 中 |
| unitary_Vprim | D | | PAG257 内の map_TopL_Vprim と ip_TopL_of_mem_Vprim から作る | 中 |

## 2. A・B・C の件数と一覧
- **A：1 件**　ip
- **B：8 件**　ip_smul_smul、rootNum_ne_zero、not_isPrimitive_one_prime、not_isPrimitive_one_of_two_le、charU_one_mem_Vimprim、eq_one_of_two、Vprim_two、charU（推定、確信度 低）
- **C：6 件**　JHL、TopL_charU、ip_charU、Vprim_ne_bot_three、Vprim_ne_bot_prime（低）、TopL_charU_one_four（低）
- 合計は 15 件で、そのうち確信度 低が 3 件です。D は 26 件で、うち 1 件（normSq_rootNum_one_prime）は前の宣言の一般化です。
- 境目にある not_isometry_Vimprim_two を C に入れると 16 件になります。

## 3. 気づいたこと

**PAG253 の既存の道具を使っていない**
- PAG257 は PAG253 の道具立て（ipG、PAG.charFun、単数群上の作用素）を使わずに、ip と charU を新しく定義しています。
- ip は ipG と rfl で一致するので、ipG_smul_left/right はそのまま使えます。

**担当の外で見つけた重複（前の鎖の中どうし）**
- 同じ文（A、確信度 高）：
  - PAG256::inv_apply_neg_one と PAG9::inv_apply_neg_one
  - PAG256::neg_one_mul_self と PAG9::chi_neg_one_sq
  - PAG256::isPrimitive_of_prime_of_ne_one と PAG171::primitive_of_ne_one（引数の暗黙・明示が違うだけ）
- 同じ値を別の定義で書いたもの（C、中）：
  - PAG256::rootNum と PAG2::Wpow χ 1（PAG2::parity_weight と 1/I = −I による）
  - PAG256::rootNum と PAG196::zN χ / PAG198::gs χ（χ.Even は χ(−1) = 1 なので）
  - PAG256::casKer と PAG3::casK
- ほぼ同じ主張（B〜C、中）：
  - PAG256::parFac_of_even/odd は PAG2::parity_weight の r = 1 の場合
  - PAG256::hartley_one は PAG3::hartley_char の x = 1 の場合
  - PAG256::sum_mul_stdAddChar_neg は PAG3::sum_neg_twist の x = 1 の場合
- 同じ式の定義（A、高）：PAG52::ip と PAG229::herm（ZMod N 上）。PAG253::ipG はこれを一般の有限型に広げたものです。
- 実質同じ文（A〜B、高）：
  - PAG229::herm_smul_left と PAG217::inner_smul_left'
  - PAG229::herm_conj と PAG215::inner_conj_symm
- B 型（すぐ出るもの）：
  - PAG145::card_units_filter と PAG214::card_isUnit（高）
  - PAG3::conj_apply_eq_inv と PAG213::conj_inv_apply（高）
  - PAG9::sq_isPrimitive と PAG10::sq_isPrimitive'（高）
  - PAG30::no_prim_mod_two と PAG85::no_prim_mod2（中）
  - PAG195::z_level_one と PAG196::zN_level_one（中）

**候補の選び方の弱点**
- 定義の展開をたどらない。ip = ipG なのに、ip_smul_smul の候補は ZMod N 版（PAG217、PAG208）になっていて、PAG253::ipG_smul_* が出ていません。
- 言い換えを拾えない。gaussSum と ram、rootNum と Wpow／zN／gs、casKer と casK が結びつきません。
- 存在補題や初等的な補題を拾えない。
  - Vprim_ne_bot_three／prime の候補は block・layer 系で、exists_primitive_odd_three、Lc_ne_one、exists_generator が出ていません。
  - Vprim_two の候補に PAG30::no_prim_mod_two がありません。
  - ip_charU の候補に PAG3::conj_apply_eq_inv がありません。
- 定義（Vprim、Vimprim、charU、extL）の候補は、Equivariant や Radial などの汎用の定義に偏っています。
- PAG1 が材料にないので、PAG.charFun 系はそもそも候補に出てきません。

**「数行」の線引き**
- B は証明 1〜2 行、C は前の宣言 1〜3 個に 6 行程度までを足すもの、としました。
- 境目の 3 件（TopL_charU_one_four、Vprim_ne_bot_prime、not_isometry_Vimprim_two）は確信度を 低 にしています。

## 4. 使った検索語
Grep が使えなかったため、以下は Read で読んだ範囲を目で探した語です（候補の全文でも確かめました）。
- **内積・正定値性**：ipG、ipG_smul、herm、herm_self_eq_zero、inner_smul、inner_sum、`= 0) : f = 0`
- **単数群上の関数**：`(ZMod N)ˣ → ℂ`、charFun、transl、rev
- **零延長**：`IsUnit x then`、`h.unit`、extS、extN、VanishNU
- **ハートレー変換と根数**：hartley、cas、casK、casKer、Wpow、parity_weight、rootNum、zN、gs、parFac
- **自明指標のガウス和**：`gaussSum (1`、ram、ram_pull、sum_mult_eq_zero、psi_one_primitive
- **原始性**：`IsPrimitive}`、Prim、Np、no_prim_mod_two、no_prim_mod2、level_two_trivial、ne_one_of_isPrimitive、prim_level_p_iff、primitive_of_ne_one
- **原始指標の存在**：exists_primitive、Lc_ne_one、exists_generator、exists_cubic、exists_quartic
- **一次独立・張る空間・直交性**：`LinearIndependent ℂ (fun χ`、`Submodule.span ℂ (Set.range fun χ`、sum_units_char、conj_apply_eq_inv、sum_apply_mul_apply_inv
- **その他**：removal_counterexample、normSq_rootNum、JH_eq_rootNum_mul、IsCompl、isometry、unitary
