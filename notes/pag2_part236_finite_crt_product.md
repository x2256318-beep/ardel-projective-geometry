# アデール射影幾何 2.0 — Part 236：有限個の互いに素な法の積と、中国剰余定理の繰り返し

2026-10-31〜11-04。引き継ぎメモの次の候補（有限個の積 $A_N\cong\bigotimes_{q^k\parallel N}A_{q^k}$ を Lean の定理にすること）を進めました。

2 つの因子の場合は、Part 228〜235 で揃っていました。今回は、中国剰余定理 $\mathbb Z/aP\cong\mathbb Z/a\times\mathbb Z/P$ をリストの先頭から繰り返して、有限個の因子の場合を組み立てました。

- **一般の形で示しました（Lean）。** 「$\gcd(a,b) = 1$ なら $C(X_{ab}) = L(X_a)\sqcup R(X_b)$」を満たす部分代数の族 $X$（`CRTMul`）について、まとめて示しました。
  - $X_N = \bigsqcup_k\iota_k(X_{a_k})$ です。局所の像 $\iota_k(X_{a_k})$ はたがいに可換です（`eq_iSup_map_locHom`、`locHom_commute`）。
  - $\dim X_N = \prod_k\dim X_{a_k}$ です（`finrank_prodList`）。
  - 繰り返しのテンソル積との代数の同型 $X_{a_1}\otimes(X_{a_2}\otimes(\cdots\otimes\mathbb C))\cong X_N$ があります（`tensEquiv`）。純テンソルは局所作用素の積 $\iota_0(S_0)\iota_1(S_1)\cdots$ に写ります（`tensEquiv_tprodL`）。
- **具体的な族に当てはめました（Lean）。** $A$・$A'$・$Z$・dilComm・End 全体の 5 つが `CRTMul` です。End 全体は Part 230 の可換子の分解から出ます。
- **素冪への分解（Lean）。** 素数の昇順に並べた素冪のリストで、次のことを示しました。
  - $X_N\cong\bigotimes_{q^k\parallel N}X_{q^k}$ です（`ppEquiv`）。End については $\mathrm{End}(\mathbb C^{\mathbb Z/N})\cong\bigotimes\mathrm{End}(\mathbb C^{\mathbb Z/q^k})$ です（`endPPEquiv`）。
  - $\dim X_N = \prod_{q\mid N}\dim X_{q^{v_q(N)}}$ です（$A$・$A'$・$Z$・dilComm のそれぞれ）。
- **局所作用素の中身（Lean）。** $\iota_k(S)$ は、$k$ 番目の座標 $x\bmod a_k$ にだけ $S$ を作用させます。
  - 陽な式は $(\iota_k(S)F)(x) = S(y\mapsto F(\mathrm{lift}_k(x,y)))(x\bmod a_k)$ です（`locHom_apply`）。
  - $\mathrm{lift}_k(x,y)$ は、第 $k$ 座標が $y$ で、ほかの座標が $x$ と同じ点です（`castHom_liftL`、`castHom_liftL_of_ne`）。$\mathbb Z/N$ の元は座標で決まります（`eq_of_castHom_eq`）。
  - 掛け算の作用素については $\iota_k(M_g) = M_{g\circ(\bmod a_k)}$ です（`locHom_mulLeft`）。
- **数値だけのもの。** リストの並べ方を変えても、同じ法の局所の像 $\iota(X_a)$ は同じ部分空間でした（234/234）。Lean では、座標による特徴づけ（上の 3 つの定理）までを示しています。並べ方の違う 2 つのリストを直接比べる主張は書いていません。
- **限界（正直な注記）。**
  - テンソル積は 2 因子のテンソル積を右から重ねたものです。Mathlib の `PiTensorProduct`（$\bigotimes_i$）の形ではありません。
  - 局所作用素はリストの順番に依存して定義されています（中身は上の陽な式のとおり、座標ごとの作用です）。
- **やり直し。** 試しのファイル T1 は 7 回目で通りました。主な原因は、型の添字 `prodList (a :: l)` と `a * prodList l` が `rw` の型の確認の水準で一致しなかったことです。`prodList` に `@[implicit_reducible]` を付けて解消しました。詳しくは §3 にあります。PAG240 のコンパイルは 1 回目で通りました。
- **環境。** このチャットのコンテナは新しかったので、Lean と Mathlib をソースから作り直し（86 分）、PAG.lean〜PAG239.lean をすべてコンパイルし直しました。添付にあった元の出力 5 本（PAG189・PAG236〜239）とは完全に一致しました。

成果物は次のとおりです。
- `PAG240.lean`：39 項目。sorry 0・警告 0 です。
  - 定義・インスタンス・構造体 17 個は項目に数えません。
  - 出力は `PAG240.out`（#print axioms 56 行）。
- 照合用の `step259.py`：ログは `step259.log` です。

xlsx の集計は 2805 項目になりました（手順 256）。

## 0. 結論

**記号**
- 法のリスト $l = [a_1,\dots,a_r]$（$\mathbb N^+$ の元）を使います。すべての組が互いに素であることを `CoprimeList l` と書きます。
- $N$ は `prodList l` $= a_1\cdot(a_2\cdot(\cdots(a_r\cdot1)))$ です。$P = $ `prodList` (残りのリスト) とすると $N = a_1P$ です。
- $C$・$L$・$R$ は Part 228 の `crtConj`・`leftOp`・`rightOp`（$\mathbb Z/a_1P\cong\mathbb Z/a_1\times\mathbb Z/P$）です。
- 局所作用素 $\iota_k$（`locHom`）：$\iota_0(S) = C^{-1}(L(S))$、$\iota_{k+1}(T) = C^{-1}(R(\iota'_k(T)))$（$\iota'$ は残りのリストのもの）。
- `CRTMul X`：$\gcd(a,b) = 1$ なら $C(X_{ab}) = L(X_a)\sqcup R(X_b)$。

| 定理 | 主張 |
|---|---|
| `prodList_nil`, `prodList_cons`, `prodList_pos`, `prodList_eq_prod`, `coprime_prodList`, `CoprimeList.head`, `CoprimeList.tail`, `get_dvd_prodList` | 法のリストの積、先頭と残りの積は互いに素、$a_k\mid N$ |
| `locHom_zero`, `locHom_succ`, **`locHom_injective`**, **`locHom_commute`** | $\iota_k$ は単射な代数の準同型で、$j\ne k$ なら $\iota_j(S)\iota_k(T) = \iota_k(T)\iota_j(S)$ |
| `crt_fst_eq_castHom`, `castHom_crt_snd`, **`locHom_mulLeft`** | $\iota_k(M_g) = M_{g\circ(\bmod a_k)}$ |
| **`locHom_apply`**, `castHom_liftL`, `castHom_liftL_of_ne`, **`eq_of_castHom_eq`** | $(\iota_k(S)F)(x) = S(y\mapsto F(\mathrm{lift}_k(x,y)))(x\bmod a_k)$。$\mathrm{lift}_k(x,y)$ は第 $k$ 座標が $y$、ほかは $x$ と同じ点。$\mathbb Z/N$ の元は座標で決まる |
| `map_symm_map_crtConj`, `eq_bot_of_one`, `map_locHom_le`, **`eq_iSup_map_locHom`**, **`finrank_prodList`** | `CRTMul` なら $\iota_k(X_{a_k})\subseteq X_N$、$X_N = \bigsqcup_k\iota_k(X_{a_k})$、$\dim X_N = \prod_k\dim X_{a_k}$、$X_1 = \bot$ |
| **`tensEquiv_tmul`**, **`tensEquiv_tprodL`** | 代数の同型 $\Theta$（`tensEquiv`）：$X_{a_1}\otimes(\cdots\otimes\mathbb C)\cong X_N$。$\Theta(S_0\otimes(S_1\otimes\cdots)) = \iota_0(S_0)\iota_1(S_1)\cdots\iota_{r-1}(S_{r-1})$ |
| `crtMul_shellAlg`, `crtMul_fullCommAlg`, `crtMul_centerAlg`, `crtMul_dilCommAlg`, **`crtMul_topAlg`** | $A$・$A'$・$Z$・dilComm・End 全体は `CRTMul` |
| `ppow_coe`, `coprimeList_ppList`, `prodList_ppList`, **`finrank_eq_prod_primeFactors`**, `finrank_shellAlg_eq_prod`, `finrank_fullCommAlg_eq_prod`, `finrank_centerAlg_eq_prod`, `finrank_dilCommAlg_eq_prod` | 素冪のリスト（`ppList`）で $X_N\cong\bigotimes_{q^k\parallel N}X_{q^k}$（`ppEquiv`、`endPPEquiv`）、$\dim X_N = \prod_{q\mid N}\dim X_{q^{v_q(N)}}$ |

**証明の筋**
1. **局所作用素。**
   - 単射性と可換性は、Part 228 の $L$・$R$ の単射性と $L(S)R(T) = R(T)L(S)$ を、リストの帰納法で繰り返すだけです。
   - 陽な式は定義を展開すると出ます。そのとき、中国剰余定理の第 1 成分が $x\bmod a$ であること（`crt_fst_eq_castHom`）を使います。第 2 成分を $c\mid b$ でさらに割った値が $x\bmod c$ であること（`castHom_crt_snd`）も使います。
   - どちらも「$\mathbb Z/n$ からの環準同型は 1 つしかない」（Mathlib の `RingHom.ext_zmod`）から出ます。
2. **生成。**
   - $X_{a_1P} = C^{-1}(L(X_{a_1})\sqcup R(X_P))$ です。これは `CRTMul` を $C^{-1}$ で戻したものです。
   - $C^{-1}$ は $\sqcup$ と $\bigsqcup$ を保ちます（像と逆像のガロア接続）。帰納法の仮定 $X_P = \bigsqcup_j\iota'_j(X_{a_j})$ を入れると、$X_{a_1P} = \iota_0(X_{a_1})\sqcup\bigsqcup_j\iota_{j+1}(X_{a_{j+1}})$ になります。
3. **次元。** $\dim X_{a_1P} = \dim C(X_{a_1P}) = \dim(L(X_{a_1})\sqcup R(X_P)) = \dim X_{a_1}\cdot\dim X_P$ です（Part 229 の `finrank_map_crtConj_gen`・`finrank_sup_map`）。空のリストでは、$\mathrm{End}(\mathbb C^{\mathbb Z/1})$ の部分代数はスカラーだけなので（`eq_bot_of_one`）、次元は 1 です。
4. **テンソル積。**
   - $\Theta_{a::l} = \mathrm{crtTensorEquiv}\circ(\mathrm{id}\otimes\Theta_l)$ です（Part 229 の $B\otimes B'\cong X$）。
   - 値は Part 229 の $C(\Theta(S\otimes T)) = L(S)R(T)$ から出ます。純テンソル全体については、$C^{-1}\circ R$ が積を保つこと（Mathlib の `map_list_prod`）を使って帰納法で示します。
5. **End 全体。** Part 230 の $(L(B)\sqcup R(B'))^c = L(B^c)\sqcup R(B'^c)$ に $B = B' = \bot$（スカラー）を入れます。$\bot^c = \top$ なので $L(\top)\sqcup R(\top) = \top = C(\top)$ です。
6. **素冪。**
   - `ppList N` は $N$ の素因数を昇順に並べ、$q^{v_q(N)}$ を並べたリストです。異なる素数の冪は互いに素で、積は $N$ です（Mathlib の `Nat.prod_factorization_pow_eq_self`）。
   - 法が命題として等しいだけなので（`prodList (ppList N) = N`）、`subst` で作った付け替え $X_M\cong X_N$（`substEquiv`）でつなぎます。

**例**
- $N = 60$、$l = [4,3,5]$：$\dim A_{60} = 10\cdot5\cdot5 = 250$、$\dim A'_{60} = 2\cdot2\cdot10 = 40$、$\dim Z_{60} = 2\cdot2\cdot2 = 8$、$\dim\mathrm{dilComm}_{60} = 2\cdot2\cdot4 = 16$ です（数値でも一致）。
- 互いに素でないリストでは成り立ちません（数値の対照）。たとえば $[2,4]$ では $x\mapsto(x\bmod2,x\bmod4)$ が全単射でなく、$\dim A_8 = 19\ne4\cdot10$ です。

**読み取れること**
- 2 因子の分解（Part 228〜231）は、部分代数の族の性質 `CRTMul` 1 つにまとまります。有限個の積への分解（生成、次元、テンソル積との同型）は、この性質だけから出ます。
- 局所作用素は、記号の上ではリストの順番に依存して定義しました。それでも、中身は「第 $k$ 座標にだけ作用し、ほかの座標を動かさない」作用素です（`locHom_apply` と lift の特徴づけ）。数値では、並べ方によらず同じ像になりました。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| 繰り返しの座標は $(x\bmod a_k)_k$ で全単射 | **正しい（`castHom_liftL`・`castHom_liftL_of_ne`・`eq_of_castHom_eq` が座標による特徴づけ）**。数値でも互いに素なリスト 4944 個（$N\le2000$）ですべて成立 |
| $\iota_k$ は単射な代数の準同型、$j\ne k$ で可換 | **正しい（`locHom_injective`、`locHom_commute`）**。数値でも積と 1 は 392/392、可換性は 296/296 |
| 陽な式 $(\iota_k(S)F)(x) = S(y\mapsto F(\mathrm{lift}_k(x,y)))(x\bmod a_k)$、$\iota_k(M_g) = M_{g\circ(\bmod a_k)}$ | **正しい（`locHom_apply`、`locHom_mulLeft`）**。数値でも再帰の定義と陽な式（行列）が 392/392 で一致 |
| `CRTMul` なら $X_N = \bigsqcup_k\iota_k(X_{a_k})$、$\dim X_N = \prod_k\dim X_{a_k}$ | **正しい（`eq_iSup_map_locHom`、`finrank_prodList`）**。数値でも $X\in\{A,A',Z,\mathrm{dilComm},\mathrm{End}\}$ の 57 例ですべて成立 |
| 繰り返しのテンソル積 $\cong X_N$、純テンソル $\mapsto$ 局所作用素の積 | **正しい（`tensEquiv`、`tensEquiv_tmul`、`tensEquiv_tprodL`）**。数値でも、局所の基底の積が $X_N$ の基底になること（一次独立で張る）を 57/57 で確認 |
| $A$・$A'$・$Z$・dilComm・End は `CRTMul` | **正しい（`crtMul_shellAlg` など 5 つ）** |
| 素冪への分解 $X_N\cong\bigotimes_{q^k\parallel N}X_{q^k}$、$\dim X_N = \prod_q\dim X_{q^{v_q(N)}}$ | **正しい（`ppEquiv`、`endPPEquiv`、`finrank_eq_prod_primeFactors` と 4 つの系）**。数値でも $A$ は $N\le72$、$A'$・$Z$・dilComm は $N\le40$ ですべて成立 |
| 並べ方を変えても局所の像は同じ | 数値だけ（234/234）。Lean では座標による特徴づけまで |
| 互いに素でないリスト | 成り立たない（数値の対照）。$[2,4]$・$[2,6]$・$[3,9]$・$[4,6]$・$[2,2,3]$ のどれも、座標の写像が全単射でなく、$\dim A_N\ne\prod\dim A_{a_k}$ |

## 2. 数値照合（step259）

| 項目 | 内容 | 結果 |
|---|---|---|
| (0) | $\varepsilon_s$ のラマヌジャン和の式 $c_{N/s}(x)/N$ と定義の和の一致（$N\le60$） | 261/261（最大誤差 6.5e-15） |
| (1) | 繰り返しの座標が $(x\bmod a_k)_k$ で全単射（互いに素なリスト、$1\le a_k\le15$、長さ $\le4$、$N\le2000$） | 4944/4944 |
| (2) | 再帰の $\iota_k$（置換行列とクロネッカー積で作ったもの）= 陽な式 | 392/392（誤差 0） |
| (3) | $\iota_k$ は積と 1 を保つ／$\iota_k(S)$ から $S$ を読み戻せる | 392/392（5.3e-15）／392/392 |
| (4) | $j\ne k$ で $\iota_j(S)\iota_k(T) = \iota_k(T)\iota_j(S)$ | 296/296 |
| (5) | $\iota_k(M_g) = M_{g\circ(\bmod a_k)}$ | 392/392 |
| (6)(7)(8) | $X_N = \bigsqcup_k\iota_k(X_{a_k})$、$\dim X_N = \prod_k\dim X_{a_k}$、局所の基底の積が基底（$X$ は 5 種類、リスト 14 個） | 57/57・57/57・57/57 |
| (9) | 素冪のリストで次元の積（$A$：$N\le72$、$A'$・$Z$・dilComm：$N\le40$） | 72/72・40/40・40/40・40/40 |
| (10) | 対照：互いに素でないリスト 5 個／並べ方を変えた局所の像 | 5 個とも不成立（期待どおり）／234/234 で同じ |

- 実行は 1 回（236 秒）で、すべて合格しました。
- **書き方。**
  - $A$ は生成元 $E_s$・$D_s$ から積で閉じるまで張り、$A'$ はその可換子、$Z = A\cap A'$、dilComm は $A$ と単数倍 $U_u$ の可換子です。どれも行列の空間の部分空間として数値で求めました。
  - このコンテナでは pypi.org に接続できず、mpmath・sympy を入れられませんでした。そのため numpy だけで書いています。Part 228〜235 の照合も numpy でした。前回までの共通モジュール（step227・step251 など）は添付になかったので、使わずに書き直しています。
- **限界。**
  - (6)〜(8) のリストは 14 個で、$N\le120$（$A'$・$Z$・dilComm・End は $N\le60$）です。
  - 可換子は数値の零空間（特異値の閾値 1e-8）で求めています。

## 3. Lean（`PAG240.lean`、namespace `PAG.Part240`、PAG239 を import）

| 区分 | 項目 |
|---|---|
| 0. 法のリスト | def `prodList`（`@[implicit_reducible]`）・`CoprimeList`, instance `neZero_prodList`, `prodList_nil`, `prodList_cons`, `prodList_pos`, `prodList_eq_prod`, `coprime_prodList`, `CoprimeList.head`, `CoprimeList.tail`, `get_dvd_prodList` |
| 1. 局所作用素 | def `locHom`・`liftL`, `locHom_zero`, `locHom_succ`, `locHom_injective`, `locHom_commute`, `crt_fst_eq_castHom`, `castHom_crt_snd`, `locHom_mulLeft`, `locHom_apply`, `castHom_liftL`, `castHom_liftL_of_ne`, `eq_of_castHom_eq` |
| 2. 中国剰余定理で分かれる族 | def `CRTMul`, `map_symm_map_crtConj`, `eq_bot_of_one`, `map_locHom_le`, `eq_iSup_map_locHom`, `finrank_prodList` |
| 3. 繰り返しのテンソル積 | structure `BundledAlg`, def `tensAlg`・`tensEquiv`・`tprodL`, `tensEquiv_tmul`, `tensEquiv_tprodL` |
| 4. A・A′・Z・dilComm・End | def `topAlg`, `crtMul_shellAlg`, `crtMul_fullCommAlg`, `crtMul_centerAlg`, `crtMul_dilCommAlg`, `crtMul_topAlg` |
| 5. 素冪への分解 | instance `neZero_ordProj`, def `ppow`・`ppList`・`substEquiv`・`ppEquiv`・`endPPEquiv`, `ppow_coe`, `coprimeList_ppList`, `prodList_ppList`, `finrank_eq_prod_primeFactors`, `finrank_shellAlg_eq_prod`, `finrank_fullCommAlg_eq_prod`, `finrank_centerAlg_eq_prod`, `finrank_dilCommAlg_eq_prod` |

**使った PAG の結果**
- Part 214 の `shellAlg`（PAG218）、Part 222 の `fullCommAlg`・`centerAlg`（PAG226）
- Part 228 の `crtConj`・`leftOp`・`rightOp`・`leftHom`・`rightHom`・`leftHom_injective`・`rightHom_injective`・`leftOp_commute_rightOp`・`map_crtConj_shellAlg`（PAG232）
- Part 229 の `crtTensorEquiv`・`crtConj_crtTensorEquiv_tmul`・`finrank_map_crtConj_gen`・`finrank_sup_map`・`map_crtConj_fullComm`・`map_crtConj_center`（PAG233）
- Part 230 の `centralizer_sup_map`・`centralizer_bot_eq_top`（PAG234）、Part 231 の `dilCommAlg`・`map_crtConj_dilComm`（PAG235）

**Mathlib・Lean から使った主なもの**
- `ZMod.chineseRemainder`・`RingHom.ext_zmod`・`ZMod.castHom`・`ZMod.val_injective`・`RingEquiv.symm_apply_apply`・`AlgEquiv.symm_apply_eq`・`Commute.map`
- `Subalgebra.map_map`・`map_id`・`map_mono`・`map_le`・`Algebra.map_sup`・`Algebra.map_bot`・`iSup_le`・`le_iSup_of_le`・`iSup_eq_bot`・`Subalgebra.finrank_bot`・`Algebra.botEquiv`・`Subalgebra.equivOfEq`・`Subalgebra.topEquiv`
- `Algebra.TensorProduct.congr`・`congr_apply`・`map_tmul`・`map_list_prod`・`List.ofFn_succ`・`List.map_ofFn`・`List.pairwise_cons`・`List.pairwise_map`・`List.Nodup.pairwise_of_forall_ne`・`List.prod_toFinset`・`Finset.sort_toFinset`・`Nat.prod_factorization_pow_eq_self`・`Nat.ordProj_pos`

**コンパイル**
- `PAG240` は 1 回目（約 13 秒）で、エラー・警告なしで通りました。公理は標準のもの（propext、Classical.choice、Quot.sound）か、その一部だけです。56 行のうち 7 行は公理なし、4 行は一部だけ（[propext] または [propext, Quot.sound]）で、どれも法のリストの算術の項目です。新しい Mathlib のビルドは要りませんでした。
- 内容は試しのファイル T1 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble240.py`）。
- **新しい書き方：`@[implicit_reducible]`。** Lean 本体の属性で、`List.get` にも付いています。`prodList` は `ZMod (prodList l)` のように型の添字に現れます。`prodList (a :: l)` と `a * prodList l` は定義から等しいのですが、`rw` がゴールの型を確かめる水準（implicit 透明度）では展開されませんでした。この属性を付けると、その水準でも展開されるようになります。公理や証明の正しさには関係しません。
- **PAG240 の前の試しのファイル（置き場所は `/home/claude/leanwork/scratch/t236`）。**
  - T0（Mathlib だけを import、§0・§5 の算術）は 3 回目で通りました。
    - 1 回目：`CoprimeList` の λ に型を書かなかったため、$\mathbb N^+$ のリストがモナドの持ち上げで $\mathbb N$ のリストに変換されました。また、$\mathbb N^+$ の無名コンストラクタが部分型 $\{n\mid0<n\}$ として推論され、`List.map` の型が合いませんでした。
    - 2 回目は λ の型注釈で前者だけが直りました。3 回目に、返り値の型を $\mathbb N^+$ と書いた定義 `ppow` にして通りました。
  - T1 は 7 回目で通りました。
    - 1 回目：`x : ZMod (prodList (a :: l))` を `ZMod (a * prodList l)` の関数に渡した式で `rw` が失敗しました（implicit 透明度で型が合わない）。`castHom` の行き先の環 `_` が決まらない箇所も 2 つあり、`Subalgebra.map_le` の `rw` も同じ理由で失敗しました。`prodList` に `@[implicit_reducible]` を付け、行き先の環を明示しました。
    - 2 回目：`Ring (部分代数 ⊗ 入れ物)` のインスタンスが見つかりませんでした。部分代数の型の加法の構造が `AddSubmonoidClass.toAddCommMonoid` 経由で作られ、`Algebra.TensorProduct.instRing` と照合できないためです（`instSemiring` は見つかります）。入れ物 `BundledAlg` を半環にして解消しました。ほかに、`rw` の後に両辺が同じ表示のまま残ったゴールに `rfl` を足し、使われない束縛変数の警告 1 件は `_` にしました。
    - 3〜6 回目：`tensEquiv_tmul` の主張で、型の字面が違う 2 つの End の積は `HMul` が見つかりませんでした。型注釈では型の字面が変わらないので、`@id` でそろえました。部分代数の元の強制も、ambient の型の字面が違うと入らないので、強制先を明示しました。`tprodL` の `S 0`・`S k.succ` は implicit 透明度で型が合わないので、`⟨0, _⟩`・`⟨k + 1, _⟩` に変え、`Subtype.val` で強制しました。
  - T2 はインスタンスの確かめのための小さなファイルです（`#synth`。2 回）。
- **環境。**
  - このチャットのコンテナは新しく、Lean v4.36.0-rc1（GitHub releases の zip）と Mathlib（commit 2f3c7c8a）をソースからビルドしました（7023 ジョブ、2 コアで 86 分）。続けて、PAG189 が import する Padics.Hensel・Padics.RingHoms を、依存を含めて 6 モジュール（36 秒）ビルドしました。ほかの追加の import（ArithmeticFunction.Moebius・Vandermonde・Matrix.Block・Matrix.Adjugate・RingTheory.FiniteType）は、最初のビルドにすでに含まれていました。
  - PAG.lean〜PAG239.lean をすべてコンパイルし直しました。エラー・警告は 0、#print axioms は 2924 行で、すべて標準の公理かその一部です。添付にあった元の出力 5 本（PAG189・PAG236〜239）とは完全に一致しました。
  - `PAG_axioms_supplement.lean` は添付になかったので、同じ規則で作り直してコンパイルしました（36 行、すべて標準の公理かその一部）。
  - 2026-10-31 21:09 に、チェーンの再コンパイルの途中（PAG183 まで）で作業を中断しました。2026-11-04 の再開時にはコンテナが再起動していましたが、ファイルと .olean は残っていました。PAG184 から続けてコンパイルしました（1 本目は import を含めて 211 秒で、キャッシュが冷えていました）。

## 4. 残る問い

1. **（次の候補）`PiTensorProduct` の形にすること。** 今回のテンソル積は 2 因子を右から重ねたものです。Mathlib の `⨂[ℂ] i, X_{a_i}` と `PiTensorProduct.liftAlgHom`（可換な像の積は多重線形で、積と 1 を保つ）を使えば、番号の付け方によらない形で $X_N\cong\bigotimes_iX_{a_i}$ が書ける見込みです。`Mathlib.RingTheory.PiTensorProduct` は追加のビルドが要ります。
2. **並べ方によらないこと。** 同じ法 $a$ の局所の像 $\iota(X_a)$ がリストの並べ方によらないことは、数値だけです（234/234）。座標による特徴づけ（`castHom_liftL`・`castHom_liftL_of_ne`・`eq_of_castHom_eq`）から示せるはずですが、法の字面が違う 2 つのリストを比べるための付け替えが要ります。
3. **素冪 $q^k$ の場合の具体的な形。** $A_{q^k}$・$A'_{q^k}$ を書くこと（$S(q^k)$、$m(q^j)$、ブロックの大きさ）。今回の分解と合わせると、$A_N$ の構造は素冪の場合に帰着します。
4. 引き継ぎメモのほかの候補（1i・1h・1g・1a・1d・1c、法 $p$ の局所の仮定、Ẑ、数論の問い）はそのままです。
