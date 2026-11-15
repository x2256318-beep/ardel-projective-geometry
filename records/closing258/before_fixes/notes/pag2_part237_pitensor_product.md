# アデール射影幾何 2.0 — Part 237：有限個の積を PiTensorProduct の形で、番号の付け方によらずに

2026-11-04。引き継ぎメモの次の候補（有限個の積を Mathlib の `PiTensorProduct` の形で書くこと）を進めました。

Part 236 の積は、2 因子のテンソル積を右から重ねた形（`tensAlg`）でした。局所作用素もリストの順番に依存して定義していました。今回は Mathlib の $\bigotimes_i$（`PiTensorProduct`）を使い、番号の付け方によらない形に書き直しました。

- **一般論（Lean）。** 異なる番号の像がたがいに可換な代数準同型の族 $\varphi_i : A_i\to B$（`CommFam`）から、準同型 $\bigotimes_iA_i\to B$ を作りました（`tpLift`）。
  - 純テンソルは $\otimes_ix_i\mapsto\prod_i\varphi_i(x_i)$ に写ります。積 $\prod$ は Mathlib の `Finset.noncommProd` で、像が可換なので順序によりません（`tpLift_tprod`）。
  - $A_i$ への制限は $\varphi_i$ で（`tpLift_single`）、この性質で一意に決まります（`eq_tpLift`）。
  - 像は $\varphi_i$ の像が生成する部分代数です（`range_tpLift`）。$\dim\bigotimes_iA_i = \prod_i\dim A_i$ です（`finrank_tp`）。
  - 部分代数 $T$ が $\varphi_i$ の像で生成され、$\dim T = \prod_i\dim A_i$ なら、$\bigotimes_iA_i\cong T$ です（`tpEquiv`）。
- **位置によらない局所作用素（Lean）。** $a\mid N$、$\gcd(a,N/a) = 1$ のとき、$\mathbb Z/N\cong\mathbb Z/a\times\mathbb Z/(N/a)$ で第 1 座標に作用させた作用素 $\iota^N_a$ を定義しました（`locOp`）。
  - 陽な式は $(\iota^N_a(S)F)(x) = S(y\mapsto F(\mathrm{lift}(x,y)))(x\bmod a)$ です（`locOp_apply`）。$\mathrm{lift}(x,y)$ は、$a$ 成分を $y$ に取り替え、$N/a$ 成分は $x$ のままにした点です。
  - Part 236 のリストの局所作用素は、位置によらない作用素と一致します：$\iota_k = \iota^N_{a_k}$（`locHom_eq_locOp`）。
  - そのため、リストの並べ方を変えても、同じ法の局所作用素は同じです（`locHom_congr`、`prodList_perm`）。Part 236 では数値だけだった主張です。
  - 互いに素な $a, b$（どちらも上の条件を満たす $N$ の約数）なら、$\iota^N_a(S)$ と $\iota^N_b(T)$ は可換です（`commute_locOp`）。
- **主定理（Lean）。** 中国剰余定理で分かれる部分代数の族 $X$（Part 236 の `CRTMul`）について、次の 2 つの形を示しました。
  - リストの形：$\bigotimes_kX_{a_k}\cong X_N$ で、純テンソルは局所作用素の積に写ります（`piTensEquiv`）。
  - 素因数で番号をつけた形：$\bigotimes_{p\mid N}X_{p^{v_p(N)}}\cong X_N$ です（`piPrimeEquiv`）。番号は $N$ の素因数の集合（`N.primeFactors`）そのもので、並べ方を使いません。
    - $p$ の位置の $1\otimes\cdots\otimes s\otimes\cdots\otimes1$ は $\iota^N_{p^{v_p}}(s)$ に写ります（`piPrimeEquiv_single`）。この性質を持つ準同型はこれだけです（`piPrimeEquiv_unique`）。
    - $X_{p^{v_p}}$ の基底 $b_p$ から、$X_N$ の基底 $b(q) = \prod_p\iota^N_{p^{v_p}}(b_p(q_p))$ が得られます（`ppBasis`、`ppBasis_apply`）。
  - $A$・$A'$・$Z$・dilComm・End 全体に当てはめました（`shellAlgPiEquiv` ほか 4 つ）。
- **限界（正直な注記）。**
  - End 全体の場合（`endPiEquiv`）の因子は、$\mathrm{End}(\mathbb C^{\mathbb Z/p^{v_p}})$ そのものではなく、その全体の部分代数 $\top$（Part 236 の `topAlg`）の型です。End そのものを因子にした版は、インスタンスの経路の違いで証明が通らず、今回は書いていません（§3）。
  - リストの形の同型 `piTensEquiv` はリスト（番号 `Fin r`）に依存します。番号によらない形は `piPrimeEquiv` です。Part 236 の `tensEquiv`（右から重ねた形）との比較は書いていません。
  - $\gcd(a,N/a) > 1$ の約数 $a$ では $\mathbb Z/N\to\mathbb Z/a\times\mathbb Z/(N/a)$ が全単射になりません。これは数値の対照だけで、Lean では仮定 $\gcd(a,N/a) = 1$ を置いています。
- **やり直し。** 試しのファイル T1〜T10 を 9 回コンパイルしました（T7 はコンパイル前に書き直し）。最初に通ったのは T6 です。追加の定理を入れた T10 も通りました。主な原因は、インスタンスや型の字面の照合でした。
  - `Finset.noncommProd` に渡す可換性の証明の型。
  - 一般論の `Ring` のインスタンスと、部分代数の型の `Semiring` のインスタンスの照合。
  - $\mathbb N^+$ の無名コンストラクタ。

  詳しくは §3 にあります。T11（T10 の docstring の番号を直したもの）から組み立てた PAG241 のコンパイルは、1 回目で通りました。
- **環境。** Mathlib の `PiTensorProduct` の 2 モジュールを追加でビルドしました（依存を含めて 6 モジュール、41 秒）。

成果物は次のとおりです。
- `PAG241.lean`：51 項目。sorry 0・警告 0 です。
  - 定義・インスタンス 21 個は項目に数えません。
  - 出力は `PAG241.out`（#print axioms 72 行）。
- 照合用の `step260.py`：ログは `step260.log` です。

xlsx の集計は 2856 項目になりました（手順 257）。

## 0. 結論

**記号**
- `CommFam φ`：$i\ne j$ なら $\varphi_i(x)\varphi_j(y) = \varphi_j(y)\varphi_i(x)$（代数準同型の族 $\varphi_i : A_i\to B$、番号は有限集合）。
- `tpProd φ hφ x` $= \prod_i\varphi_i(x_i)$（`Finset.noncommProd`）。`tpLift φ hφ` $:\bigotimes_iA_i\to B$ はそれを `PiTensorProduct.liftAlgHom` で延ばした準同型。
- `crtE N a`：$\mathbb Z/N\cong\mathbb Z/a\times\mathbb Z/(N/a)$（$a\mid N$、$\gcd(a,N/a) = 1$。`ZMod.ringEquivCongr` と `ZMod.chineseRemainder` の合成）。
- `liftF N a x y` $=$ `crtE`$^{-1}(y, (\text{crtE}\,x)_2)$。`locOp N a` $=\iota^N_a$：`crtE` で $\mathbb C^{\mathbb Z/N}\cong\mathbb C^{\mathbb Z/a\times\mathbb Z/(N/a)}$ と付け替え、Part 228 の $L$（第 1 座標への作用）で共役したもの。
- `endCongr h`：$M = N$ のときの付け替え $\mathrm{End}(\mathbb C^{\mathbb Z/M})\cong\mathrm{End}(\mathbb C^{\mathbb Z/N})$（`subst` で作る）。
- $X$ は Part 236 の `CRTMul` な族（$\gcd(a,b) = 1$ なら $C(X_{ab}) = L(X_a)\sqcup R(X_b)$）。

| 定理 | 主張 |
|---|---|
| `pwComm`, `tpProd_eq_mul_erase`, `tpProd_update`, `tpProd_one`, `tpProd_mul`, `tpProdML_one`, `tpProdML_mul` | $\prod_i\varphi_i(x_i)$ は各変数について線形で、積と 1 を保つ |
| **`tpLift_tprod`**, **`tpLift_single`**, **`eq_tpLift`**, **`range_tpLift`** | $\otimes_ix_i\mapsto\prod_i\varphi_i(x_i)$、$1\otimes\cdots\otimes a\otimes\cdots\otimes1\mapsto\varphi_i(a)$、この性質で一意、像 $=\bigsqcup_i\mathrm{range}\,\varphi_i$ |
| `finrank_tp`, `tpLift_rangeRestrict_bijective`, **`tpEquiv_tprod`**, `tpEquiv_single` | $\dim\bigotimes_iA_i = \prod_i\dim A_i$。$T = \bigsqcup_i\mathrm{range}\,\varphi_i$、$\dim T = \prod_i\dim A_i$ なら $\bigotimes_iA_i\cong T$（`tpEquiv`） |
| `endCongr_rfl`, `crtE_fst`, `castHom_crtE_snd`, `castHom_liftF`, `castHom_liftF_of_dvd` | `crtE` の第 1 成分は $x\bmod a$、第 2 成分を $c\mid N/a$ で割ると $x\bmod c$。$\mathrm{lift}(x,y)\bmod a = y$、$\bmod c$ は $x$ と同じ |
| **`locOp_apply`**, `endCongr_locOp` | $(\iota^N_a(S)F)(x) = S(y\mapsto F(\mathrm{lift}(x,y)))(x\bmod a)$。法の付け替えと両立 |
| `coprime_get_div`, `coprime_get_get`, `get_dvd_div`, `liftL_eq_liftF`, **`locHom_eq_locOp`** | 互いに素なリストで $\gcd(a_k,N/a_k) = 1$、$j\ne k$ なら $a_j\mid N/a_k$。$\mathrm{lift}_k = \mathrm{lift}$、$\iota_k = \iota^N_{a_k}$ |
| `prodList_perm`, **`locHom_congr`** | 並べ替えたリストの積は同じ。積が等しく同じ因子なら、局所作用素は付け替えで一致 |
| `commFam_locFam`, `range_locFam`, **`piTensEquiv_tprod`**, `piTensEquiv_single` | $\bigotimes_kX_{a_k}\cong X_N$（`piTensEquiv`）、$\otimes_kS_k\mapsto\prod_k\iota_k(S_k)$ |
| `coprime_ordProj`, `mem_ppList`, `exists_of_mem_ppList`, `map_locOp_congr`, `iSup_map_locOp_transport`, `commute_locOp_transport`, `commute_locOp_of_list` | 素冪の性質と、法・因子の付け替え（`subst`） |
| **`commute_locOp`**, `commute_locOp_pp` | 互いに素な $a, b$ で $\iota^N_a(S)\iota^N_b(T) = \iota^N_b(T)\iota^N_a(S)$。特に異なる素数の $p^{v_p}$ と $q^{v_q}$ |
| `commFam_ppFam`, `range_ppFam`, **`eq_iSup_ppFam`**, `finrank_pp` | $X_N = \bigsqcup_{p\mid N}\iota^N_{p^{v_p}}(X_{p^{v_p}})$、$\dim X_N = \prod_{p\mid N}\dim X_{p^{v_p}}$（番号は `N.primeFactors`） |
| **`piPrimeEquiv_tprod`**, `piPrimeEquiv_single`, **`piPrimeEquiv_unique`**, **`ppBasis_apply`** | $\bigotimes_{p\mid N}X_{p^{v_p(N)}}\cong X_N$（`piPrimeEquiv`）、$\otimes_pS_p\mapsto\prod_p\iota^N_{p^{v_p}}(S_p)$、局所作用素で一意、局所の基底の積は基底 |
| `endPiEquiv_tprod` | $\bigotimes_{p\mid N}\top_{p^{v_p}}\cong\mathrm{End}(\mathbb C^{\mathbb Z/N})$（`endPiEquiv`）。$A$・$A'$・$Z$・dilComm も同じ形（`shellAlgPiEquiv`・`fullCommAlgPiEquiv`・`centerAlgPiEquiv`・`dilCommAlgPiEquiv`） |

**証明の筋**
1. **一般論。**
   - 多重線形性：$i$ 番目を取り替えた族の積は $\varphi_i(v)\cdot\prod_{j\ne i}\varphi_j(x_j)$ です（Mathlib の `Finset.mul_noncommProd_erase`）。後ろの因子は $v$ によらないので、$v$ について線形です。
   - 積を保つこと：`Finset.noncommProd_mul_distrib` です。異なる番号の像が可換であることを使います。1 を保つことは、すべての因子が 1 だからです。
   - 一意性は Mathlib の `PiTensorProduct.algHom_ext` です（有限個の積からの準同型は、$1\otimes\cdots\otimes a\otimes\cdots\otimes1$ での値で決まります）。
   - 像：純テンソルの和に分けると（`PiTensorProduct.induction_on`）、各項は $\bigsqcup_i\mathrm{range}\,\varphi_i$ の元の積なので、像は $\bigsqcup$ に入ります（`Submonoid.noncommProd_mem`）。逆の包含は `tpLift_single` から出ます。
   - 同型：次元は積の基底（Mathlib の `Basis.piTensorProduct`）で数えます。像への制限は全射で、次元が等しいので単射です。
2. **位置によらない局所作用素。**
   - `crtE` の成分は、Part 236 と同じく「$\mathbb Z/n$ からの環準同型は 1 つしかない」（`RingHom.ext_zmod`）から出ます。陽な式は定義を展開すると出ます。
   - リストの持ち上げ $\mathrm{lift}_k$（Part 236 の `liftL`）と $\mathrm{lift}$ は、座標ごとに比べると一致します（Part 236 の `eq_of_castHom_eq`）。$k$ 番目の座標はどちらも $y$ です。$j\ne k$ の座標はどちらも $x$ と同じです。後者には $a_j\mid N/a_k$（`get_dvd_div`）を使います。
   - 陽な式どうしが一致するので、$\iota_k = \iota^N_{a_k}$ です。
3. **並べ方によらないこと。** $\iota^N_a$ は $N$ と $a$ だけで決まります。そのため、2 つのリストの積が等しく（並べ替えなら `prodList_perm`）、同じ因子を持つなら、局所作用素は法の付け替え `endCongr` で一致します。付け替えは `subst` で示しました。
4. **可換性。**
   - 3 項のリスト $[a, b, N/(ab)]$ は互いに素で、積は $N$ です。
   - 0 番目と 1 番目の局所作用素は可換です（Part 236 の `locHom_commute`）。$\iota_k = \iota^N_{a_k}$ と法の付け替えで、$\iota^N_a$ と $\iota^N_b$ の可換性になります。
5. **素因数で番号をつけた形。**
   - 生成：素冪のリスト（Part 236 の `ppList`）での生成 $X_{\mathrm{prodList}} = \bigsqcup_k\iota_k(X_{a_k})$ を、$\iota_k = \iota^N_{a_k}$ と $\mathrm{prodList}(\mathrm{ppList}\,N) = N$ で付け替えます。
   - 番号の付け替え：リストの位置 $k$ から素数 $p$ への付け替えでは、両方向の包含を示します。リストの各元は $p^{v_p(N)}$ の形で（`exists_of_mem_ppList`）、各 $p\mid N$ の $p^{v_p(N)}$ はリストにあります（`mem_ppList`）。
   - 次元は Part 236 の `finrank_eq_prod_primeFactors` です。あとは一般論の `tpEquiv` に入れるだけです。

**例**
- $N = 60$：$\bigotimes_{p\in\{2,3,5\}}A_{p^{v_p}} = A_4\otimes A_3\otimes A_5\cong A_{60}$ です（$10\cdot5\cdot5 = 250$ 次元）。同じく $A'_{60}\cong A'_4\otimes A'_3\otimes A'_5$（$2\cdot2\cdot10 = 40$）、$Z_{60}$（$2\cdot2\cdot2 = 8$）、dilComm$_{60}$（$2\cdot2\cdot4 = 16$）です。数値でも、局所の基底の積が基底になりました（§2 の (7)）。
- 対照（数値）：$N = 12$、$a = 2$ では $\gcd(2,6) = 2$ です。$x\mapsto(x\bmod2,x\bmod6)$ は単射でなく、$\iota^{12}_2$ は定義されません。

**読み取れること**
- 有限個の積への分解は、「異なる番号の像が可換な準同型の族」という一般の形にまとまりました。中国剰余定理から入るのは、可換性（`commute_locOp`）、生成（`eq_iSup_ppFam`）、次元（`finrank_pp`）の 3 つだけです。
- 局所作用素は $N$ と因子 $a$ だけで決まります。そのため、素因数で番号をつけた同型 `piPrimeEquiv` は、局所作用素から一意に決まります。順番の選び方は入りません。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| 像が可換な準同型の族から $\bigotimes_iA_i\to B$、$1\otimes\cdots\otimes a\otimes\cdots\otimes1\mapsto\varphi_i(a)$、一意、像 $=\bigsqcup_i\mathrm{range}\,\varphi_i$、$\dim\bigotimes_iA_i = \prod_i\dim A_i$ | **正しい（`tpLift_tprod`、`tpLift_single`、`eq_tpLift`、`range_tpLift`、`finrank_tp`）**。数値でも、局所作用素の積はどの順でも同じで（126/126）、純テンソルの和に延ばしたものは積と 1 を保つ（126/126） |
| 生成と次元から同型 $\bigotimes_iA_i\cong T$ | **正しい（`tpEquiv`、`tpEquiv_tprod`、`tpEquiv_single`）** |
| 位置によらない $\iota^N_a$ の陽な式（$=C_a^{-1}L(S)C_a$） | **正しい（`locOp_apply`。`locOp` は定義で $C_a^{-1}LC_a$）**。数値でも陽な式と共役が 448/448 で一致（誤差 0） |
| リストの $\iota_k$ = $\iota^N_{a_k}$ | **正しい（`locHom_eq_locOp`）**。数値でも 442/442（誤差 0） |
| 並べ方を変えても同じ法の局所作用素は同じ | **正しい（`locHom_congr`、`prodList_perm`）**。Part 236 では数値だけだった。数値でもすべての置換で 2108/2108 |
| 互いに素な $a, b$ で $\iota^N_a$ と $\iota^N_b$ は可換 | **正しい（`commute_locOp`、`commute_locOp_pp`）**。数値でもリストの $j\ne k$ で 374/374、互いに素な約数の組（$N\le120$）で 144/144 |
| $\bigotimes_kX_{a_k}\cong X_N$（リスト） | **正しい（`piTensEquiv`、`piTensEquiv_tprod`、`piTensEquiv_single`）**。数値でも局所の基底の積が基底（End 5/5、$A$ 11/11、$A'$・$Z$・dilComm 9/9） |
| $\bigotimes_{p\mid N}X_{p^{v_p(N)}}\cong X_N$、局所作用素で一意、局所の基底の積が基底 | **正しい（`piPrimeEquiv`、`piPrimeEquiv_tprod`、`piPrimeEquiv_single`、`piPrimeEquiv_unique`、`ppBasis_apply`、`eq_iSup_ppFam`、`finrank_pp`）**。数値でも $A$ は $N\le72$（71/71）、$A'$・$Z$・dilComm は $N\le40$（39/39） |
| $A$・$A'$・$Z$・dilComm・End の場合 | **正しい（`shellAlgPiEquiv` など 5 つ、`endPiEquiv_tprod`）**。End の因子は `topAlg`（$\top$）の型 |
| $\gcd(a,N/a) > 1$ の約数 | 成り立たない（数値の対照）。$N\le120$ の 153 個すべてで $x\mapsto(x\bmod a,x\bmod N/a)$ が単射でない。Lean では仮定を置いただけで、反例は Lean にしていない |

## 2. 数値照合（step260）

| 項目 | 内容 | 結果 |
|---|---|---|
| (0) | $\iota^N_a$ の陽な式 $[z\equiv x\ (\bmod N/a)]\cdot S[x\bmod a, z\bmod a]$ と $C_a^{-1}L(S)C_a$ の一致（$N\le120$、$\gcd(a,N/a) = 1$） | 448/448（誤差 0） |
| (1) | リストの $\iota_k$（Part 236 の再帰の作り方）= $\iota^N_{a_k}$（互いに素なリスト 170 個：$2\le a_k\le12$、長さ 2〜4、$N\le180$） | 442/442（誤差 0） |
| (2) | 並べ方を変えたリスト（すべての置換）で、同じ法の局所作用素が同じ | 2108/2108（誤差 0） |
| (3)／(3b) | リストの $j\ne k$ で可換／互いに素な約数 $a, b$（$N\le120$）で可換 | 374/374／144/144 |
| (4) | 局所作用素の積はどの順でも同じで、クロネッカー積 $S_1\otimes\cdots\otimes S_r$ を座標の付け替えで共役したものに等しい（$N\le120$ の 126 個） | 126/126（3.6e-15） |
| (5) | 純テンソルの和に延ばした $\Phi$ は積と 1 を保つ（乱数のテンソル、各 3 項） | 126/126（9.7e-16） |
| (6) | 局所の基底の積が $X_N$ の基底（リスト 11 個。End は $N\le40$、$A$ は $N\le120$、$A'$・$Z$・dilComm は $N\le60$） | 5/5・11/11・9/9・9/9・9/9 |
| (7) | 素因数で番号をつけた形：局所の基底の積が $X_N$ の基底（$A$：$N\le72$、$A'$・$Z$・dilComm：$N\le40$） | 71/71・39/39・39/39・39/39 |
| (8) | 対照：$\gcd(a,N/a) > 1$ の約数（$N\le120$、153 個）で $x\mapsto(x\bmod a,x\bmod N/a)$ が単射でない | 153/153（期待どおり） |

- 実行は 1 回（286 秒）で、すべて合格しました。
- **書き方。**
  - Part 236 の step259 の関数（族 $X$ の数値の作り方、リストの局所作用素の再帰の作り方）を import して使いました。
  - 位置によらない $\iota^N_a$ は、陽な式と $C_a$ の共役の 2 通りで作りました。
- **限界。**
  - (6) のリストは 11 個です。(4)(5) は $N\le120$ のリストだけです。
  - 可換子は数値の零空間（特異値の閾値 1e-8）で求めています（Part 236 と同じ）。

## 3. Lean（`PAG241.lean`、namespace `PAG.Part241`、PAG240 と Mathlib の `RingTheory.PiTensorProduct`・`LinearAlgebra.PiTensorProduct.Basis` を import）

| 区分 | 項目 |
|---|---|
| 1. 一般論 | def `CommFam`・`tpProd`・`tpProdML`・`tpLift`・`tpEquiv`, instance `finiteDimensional_tp`, `pwComm`, `tpProd_eq_mul_erase`, `tpProd_update`, `tpProd_one`, `tpProd_mul`, `tpProdML_one`, `tpProdML_mul`, `tpLift_tprod`, `tpLift_single`, `eq_tpLift`, `range_tpLift`, `finrank_tp`, `tpLift_rangeRestrict_bijective`, `tpEquiv_tprod`, `tpEquiv_single` |
| 2. 位置によらない局所作用素 | def `endCongr`・`crtE`・`liftF`・`crtLinN`・`locOp`, `endCongr_rfl`, `crtE_fst`, `castHom_crtE_snd`, `castHom_liftF`, `castHom_liftF_of_dvd`, `locOp_apply`, `endCongr_locOp` |
| 3. リストの局所作用素 | `coprime_get_div`, `coprime_get_get`, `get_dvd_div`, `liftL_eq_liftF`, `locHom_eq_locOp`, `prodList_perm`, `locHom_congr` |
| 4. リストの形 | def `locFam`・`piTensEquiv`, `commFam_locFam`, `range_locFam`, `piTensEquiv_tprod`, `piTensEquiv_single` |
| 5. 素因数で番号をつけた形 | def `ppFam`・`piPrimeEquiv`・`ppBasis`, `coprime_ordProj`, `mem_ppList`, `exists_of_mem_ppList`, `map_locOp_congr`, `iSup_map_locOp_transport`, `commute_locOp_transport`, `commute_locOp_of_list`, `commute_locOp`, `commute_locOp_pp`, `commFam_ppFam`, `range_ppFam`, `eq_iSup_ppFam`, `finrank_pp`, `piPrimeEquiv_tprod`, `piPrimeEquiv_single`, `piPrimeEquiv_unique`, `ppBasis_apply` |
| 6. 具体的な族 | def `shellAlgPiEquiv`・`fullCommAlgPiEquiv`・`centerAlgPiEquiv`・`dilCommAlgPiEquiv`・`endPiEquiv`, `endPiEquiv_tprod` |

**使った PAG の結果**
- Part 228 の `leftHom`（PAG232）
- Part 236 の `prodList`・`prodList_eq_prod`・`CoprimeList`・`CoprimeList.head`・`CoprimeList.tail`・`get_dvd_prodList`・`locHom`・`locHom_commute`・`locHom_apply`・`liftL`・`castHom_liftL`・`castHom_liftL_of_ne`・`eq_of_castHom_eq`・`CRTMul`・`eq_iSup_map_locHom`・`finrank_prodList`・`topAlg`・`crtMul_*`（5 つ）・`ppow`・`ppList`・`coprimeList_ppList`・`prodList_ppList`・`finrank_eq_prod_primeFactors`（PAG240）
- Part 214・222・231 の `shellAlg`・`fullCommAlg`・`centerAlg`・`dilCommAlg`（PAG218・PAG226・PAG235）

**Mathlib・Lean から使った主なもの**
- `PiTensorProduct.liftAlgHom`・`liftAlgHom_apply`・`lift.tprod`・`singleAlgHom_apply`・`algHom_ext`・`induction_on`・`Basis.piTensorProduct`・`Basis.piTensorProduct_apply`
- `Finset.noncommProd`・`noncommProd_mul_distrib`・`mul_noncommProd_erase`・`noncommProd_eq_pow_card`・`noncommProd_congr`・`Submonoid.noncommProd_mem`・`MultilinearMap`（構造体を直接作った）
- `AlgHom.rangeRestrict`・`rangeRestrict_surjective`・`AlgHom.range_comp`・`Subalgebra.range_val`・`AlgEquiv.ofBijective`・`Subalgebra.equivOfEq`・`Subalgebra.topEquiv`・`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`・`Module.finrank_eq_card_basis`・`Module.finBasis`・`Fintype.card_pi`
- `ZMod.ringEquivCongr`・`ZMod.chineseRemainder`・`RingHom.ext_zmod`・`LinearEquiv.funCongrLeft`・`LinearEquiv.conjAlgEquiv`・`List.pairwise_iff_getElem`・`List.mem_iff_get`・`List.Perm.prod_eq`・`Nat.coprime_ordCompl`・`Nat.ordProj_dvd`・`Nat.toPNat`・`Finset.prod_coe_sort`

**コンパイル**
- `PAG241` は 1 回目（約 15 秒）で、エラー・警告なしで通りました。公理は標準のもの（propext、Classical.choice、Quot.sound）か、その一部だけです。72 行のうち 4 行は一部だけ（[propext, Quot.sound]）で、どれもリストの算術の項目です。
- 内容は試しのファイル T11 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble241.py`）。T11 は T10 の docstring の番号を直しただけです。
- **新しい書き方。**
  - `Finset.noncommProd` に渡す可換性の証明は、型を `(s : Set κ).Pairwise (Function.onFun Commute f)` の形で書いた補題 `pwComm` を通します。λ で直接書くと、その型（$\forall i\in s,\ \forall j\in s,\ i\ne j\to\cdots$）は `Set.Pairwise` を展開しないと一致しません。そのため、`rw` がゴールの型を確かめる水準（implicit 透明度）で失敗しました。
  - 一般論の準同型の族 `CommFam` は `Semiring` の族で書きました。`Ring` の族で書くと、部分代数に値をとる族を渡すときに失敗しました。期待される型の `Ring.toSemiring ?inst` と、実際の型の `Subalgebra.toSemiring` が、インスタンスの合成前に照合されるためです。
  - 次元と単射性（`Module.finBasis`、`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`）には加法群が要るので、そこだけ `Ring` の節にしました。使う側では、`(A := …) (B := …)` を明示し、可換性の証明は `by exact …` で後回しにしました。
- **PAG241 の前の試しのファイル（置き場所は `/home/claude/leanwork/scratch/t237`）。**
  - W0〜W5 は確かめのための小さなファイルです。
    - W0：import の温め。
    - W1・W2：API の名前と、部分代数の族の `PiTensorProduct` に `Semiring`・`Algebra` が見つかること。
    - W3：`CommFam` の `Ring` 版と `Semiring` 版で、部分代数に値をとる族を渡す実験。`Semiring` 版と、`(A := …)` を明示した `Ring` 版は通りました。
    - W4：`Ring.toSemiring S.toRing = S.toSemiring` などのインスタンスの照合が `rfl` ですぐ通ること。
    - W5：純テンソルの定理を `tpLift_tprod` で直接示すと約 4 秒で通ること。
  - T1（エラー 39 件。後の行の多くは前のエラーの連鎖）には、次の 4 種類がありました。
    - **可換性の証明の型。** 上の `noncommProd` の可換性の証明の型が原因で、`rw` が 2 か所（`tpProd_one`・`tpLift_single`）失敗しました。もう 1 か所（`tpLift_tprod`）は、`liftAlgHom` の引数に `tpProd_one`（主張は `tpProd φ hφ 1 = 1`）を渡したことが原因です。期待される型の `tpProdML φ hφ 1 = 1` と implicit 透明度で照合できませんでした。主張を `tpProdML` で書いた `tpProdML_one`・`tpProdML_mul` を足しました。
    - **API の引数の明示。** `AlgHom.mem_range` は準同型を、`Finset.mem_sort` は順序を明示の引数にとりました。
    - **インスタンスの照合。** `CommFam` を `Ring` で書いていたため、部分代数の族を渡せませんでした（上の注）。
    - **証明の引数が残った。** `rw [← locHom_eq_locOp]` で `CoprimeList` の証明が決まらずに残りました。リストと証明を明示しました。
  - T2：`Module.finBasis` に加法群が要るので、次元の補題を `Ring` の節に移しました。`range_tpLift` では、帰納法の前に所属の仮定を残していたため、帰納法の仮定に余計な前提が付きました。`clear` しました。
  - T3：`piTensEquiv`・`piPrimeEquiv` で `CommFam` の引数を確かめるところが時間切れ（200000 heartbeats）になりました。`Ring` の節のインスタンスがまだ決まっていなかったためです。`(A := …) (B := …)` と `by exact` で直りました。
    - End そのものを因子にした `endPiEquiv` の版は、`simp only [range_ppFam, topAlg, Algebra.map_top] at h` が働きませんでした。次元の `rw` も、インスタンスの経路の違いで失敗しました。因子を `topAlg` にした版に変えました。
  - T4：`:=` の次の行に `by exact …` を置き、項を次の行に続けたため、構文エラーになりました。`:= by` の改行に直しました。
  - T5：純テンソルの定理を `Ring` の節の `tpEquiv_tprod` で示すと時間切れになりました。`tpLift_tprod` で直接示すように変えました（W5）。
  - T6：エラー・警告なしで通りました。
  - T7〜T10：追加の定理（一般の `commute_locOp`、`piPrimeEquiv_unique`、`ppBasis`）を入れました。
    - T7 は、コンパイル前に証明の書き損じに気づき、T8 で書き直しました。
    - T8：3 項のリストを `[⟨a, ha⟩, …]` と書くと、$\mathbb N^+$ の無名コンストラクタが部分型 $\{n\mid0<n\}$ として推論されました（Part 236 と同じ）。`Nat.toPNat` にしました。また、部分代数の型の `Module.finBasis` は `Module.Free` のインスタンスが見つかりませんでした。`ppBasis` は任意の基底をとる形にしました。
    - T9：具体的なリストに対して `locOp` の引数に `get_dvd_prodList`（型は `↑(l.get 0) ∣ prodList l`）を渡すと、`Nat.toPNat` を展開しないと型が合いませんでした。そのため `rw` が失敗しました。一般のリストで述べた補題 `commute_locOp_of_list` を通して解消しました。
    - T10：通りました。
- **環境。**
  - `Mathlib.RingTheory.PiTensorProduct` と `Mathlib.LinearAlgebra.PiTensorProduct.Basis` を、依存を含めて 6 モジュール（Multilinear.TensorProduct・PiTensorProduct.Basic・DFinsupp・Finsupp を含む）、41 秒でビルドしました。
  - Part 236 の納品（21:31）の後、Part 237 の開始（22:05）の前に、コンテナが再起動していました（起動時刻 22:04:38）。ファイルと .olean は残っていて、追加のビルドは上の 6 モジュールだけです。

## 4. 残る問い

1. **（次の候補）素冪 $q^k$ の場合の具体的な形。** $A_{q^k}$・$A'_{q^k}$ を書くこと（$S(q^k)$、$m(q^j)$、ブロックの大きさ、Part 226 の数え上げの式を構造の言葉で）。今回の `piPrimeEquiv` で、$A_N$・$A'_N$・$Z_N$・dilComm$_N$ の構造は、番号の付け方によらずに素冪の場合に帰着しました。
2. **End そのものを因子にした形。** $\bigotimes_{p\mid N}\mathrm{End}(\mathbb C^{\mathbb Z/p^{v_p}})\cong\mathrm{End}(\mathbb C^{\mathbb Z/N})$ を、因子を $\top$ の型でなく End そのもので書くこと。一般論 `tpEquiv` に $\varphi_p = \iota^N_{p^{v_p}}$ を入れればよいはずですが、今回はインスタンスの経路の違いで証明が通りませんでした。
3. **Part 236 の形との比較。** `tensEquiv`（右から重ねた形）と `piTensEquiv` が、Mathlib の $\bigotimes$ の分解で対応することを書くこと（任意）。
4. 引き継ぎメモのほかの候補（1i・1h・1g・1a・1d・1c、法 $p$ の局所の仮定、Ẑ、数論の問い）はそのままです。
