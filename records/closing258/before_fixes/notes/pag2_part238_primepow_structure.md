# アデール射影幾何 2.0 — Part 238：素冪 $q^k$ の場合の $A$・$A'$ の具体的な形と、素冪ごとのテンソル積の形

2026-11-05。引き継ぎメモの次の候補（素冪 $q^k$ の場合の $A_{q^k}$・$A'_{q^k}$ を具体的に書くこと）を進めました。

Part 225・223 の行列環への分解 $A_N\cong\prod_{p\in S}M_{n_p}(\mathbb C)$（`shellAlgMatrixEquiv`）と $A'_N\cong\prod_{p\in S}M_{m(c_p)}(\mathbb C)$（`fullCommMatrixEquiv`）は、番号の集合 $S(N)$、層の大きさ $n_p$、原始指標の数 $m(c)$ を一般の形のまま使っていました。今回は $N = q^k$ でこれらを具体的に書き、行列環の形を具体的にしました。Part 237 の素因数ごとの同型と合わせて、一般の $N$ の $A$・$A'$・$Z$・End を素冪の場合のテンソル積として書きました。

- **基準の番号（Lean、一般の $N$）。** 番号 $p_0 = (1, 1)$（導手 1・層 1）はいつも $S(N)$ に入ります（`baseIdx`）。
  - その層 $W_{p_0}$ は動径関数（単数倍で不変な関数）の空間そのもので、次元は約数の個数 $d(N)$ です（`mem_refLayer_base_iff`、`finrank_refLayer_base`）。
  - 制限 $A_N\to\mathrm{End}(W_{p_0})$ は全射です（`radialHom_surjective`）。つまり、**どの $N$ でも、$A$ は動径関数の空間に全行列環 $M_{d(N)}(\mathbb C)$ として作用します。**
- **素冪の番号と層（Lean）。** $N = q^k$（$q$ は素数）で、次を示しました。
  - $S(q^k) = \{(1,1)\}\cup\{(q^\gamma, q^\delta) : 1\le\gamma,\ \gamma+\delta\le k,\ (q,\gamma)\ne(2,1)\}$（`mem_centerIdx_primePow`）。
  - 層の大きさは $n_{(1,1)} = k+1$、ほかの番号ではすべて $n_p = 1$ です（`card_layerDivs_primePow`、`finrank_refLayer_rest`）。
  - $\#S(q^k) = 1 + k(k+1)/2 - [q=2]\,k$ です（`card_centerIdx_primePow`）。
- **主定理（Lean）。**
  - $A_{q^k}\cong M_{k+1}(\mathbb C)\times\mathbb C^{S'}$（`shellAlgPrimePowEquiv`、$S' = S\setminus\{p_0\}$）。$M_{k+1}(\mathbb C)$ は動径関数への作用で、残りは 1 次元の成分のスカラーです。
  - $A'_N\cong\mathbb C\times\prod_{p\in S'}M_{m(c_p)}(\mathbb C)$（`fullCommSplitEquiv`、任意の $N$）。$N = q^k$ では $S'$ の導手は $q^\gamma$ なので、成分は $M_{m(q^\gamma)}(\mathbb C)$ で、同じ $\gamma$ のものが $k+1-\gamma$ 個あります。
  - 一般の $N$：$A_N\cong\bigotimes_{p\mid N}\bigl(M_{v_p(N)+1}(\mathbb C)\times\mathbb C^{S'(p^{v_p(N)})}\bigr)$（`shellAlgPrimeTensorEquiv`）。$A'_N$・$Z_N$ も同じく素冪の形のテンソル積です（`fullCommPrimeTensorEquiv`・`centerAlgPrimeTensorEquiv`）。
  - $\mathrm{End}(\mathbb C^{\mathbb Z/N})\cong\bigotimes_{p\mid N}\mathrm{End}(\mathbb C^{\mathbb Z/p^{v_p(N)}})$（`endTensorEquiv`）。因子は End そのものです。**Part 237 の限界（因子が $\top$ の型だったこと）を解消しました。**
- **Part 226 の数え上げの式の意味。** Part 226 の積の式（`finrank_shellAlg_eq_prod` など）の各因子は、素冪の代数の次元です。
  - $(k+1)^2$ は動径関数の全行列環、$k(k+1)/2-[q=2]k$ は 1 次元の成分の個数です。
  - $-[q=2]k$ は、法 2 の原始指標がない（$m(2) = 0$）ために、$\gamma = 1$ の $k$ 個の番号が抜けることから来ます。
- **限界（正直な注記）。**
  - テンソル積の同型は、Part 237 の一般論（生成と次元）で作った抽象的なものです。陽な式は純テンソルの行き先だけです（End は順向き、$A$ は逆向き）。
  - 「$A'_{q^k}$ で $M_{m(q^\gamma)}(\mathbb C)$ が $k+1-\gamma$ 個」は、3a（$S(q^k)$ の具体形）と主定理 2 からの読み取りです。個別の Lean の主張にはしていません（次元の形は Part 226 の `finrank_fullComm_eq_prod`）。
  - 一般の $N$ のウェダーバーン成分が「素冪ごとの成分の積」であることは数値だけです。Lean はテンソル積の形までで、$\otimes$ を $\times$ に分配する同型と $M_a\otimes M_b\cong M_{ab}$ は書いていません。
  - dilComm は扱っていません。
- **やり直し。** 試しのファイル T1〜T6 を 6 回コンパイルし、T4 で初めて通りました（T7 は docstring の番号を直しただけ）。主な原因は次の 3 つでした（§3）。
  - `tpLift` に渡す可換性の証明を λ で書いたこと（Part 237 と同じ型の字面の問題）。
  - `layerDivs` が `open Classical in` で定義されていること。
  - λ の変数の型の書き忘れ。これは型の強制の推論の時間切れとして現れ、T2 では原因を見誤りました（T3 で判明）。
- **数値。** 数値照合（step261）はすべて合格しました。ただし、実行は 4 回かかりました。$N = 120$（$\dim A = 475$）で、候補の行列の SVD がメモリを使い切りかけたためです（2 回目はコンテナの再起動で止まりました）。$N$ ごとの結果の保存と、候補の行列を分けた直交化で通しました（§2）。
- **環境。** Mathlib の追加ビルドはありません。

成果物は次のとおりです。
- `PAG242.lean`：24 項目。sorry 0・警告 0 です。
  - 定義・abbrev・インスタンス 13 個は項目に数えません。
  - 出力は `PAG242.out`（#print axioms 37 行）。
- 照合用の `step261.py`：ログは `step261.log` です。

xlsx の集計は 2880 項目になりました（手順 258）。

## 0. 結論

**記号**
- $S(N)$（Part 222 の `centerIdx`）：組 $(c, d)$ で、$c\mid N$、$m(c) > 0$、$d\in D(c) = \{d\mid N/c : \mathrm{rad}(d)\mid c\}$（Part 216 の `layerIdx`）のもの。$Z_N\cong\mathbb C^{S(N)}$ です（Part 222 の `centerAlgEquiv`）。
- $m(c)$（Part 226 の `primCount`）：法 $c$ の原始指標の数。$m(q) = q-2$、$m(q^\gamma) = q^{\gamma-2}(q-1)^2$（$\gamma\ge2$）は Part 226 の `primCount_prime`・`primCount_prime_pow` です。
- $W_p$（Part 224 の `refLayer`）：番号 $p = (c,d)$ の代表の層。$n_p = \dim W_p = \#\{v\mid N/c : v\text{ の層} = d\}$（Part 217 の `layerDivs`、Part 224 の `finrank_refLayer`）。
- $p_0 = (1,1)$（`baseIdx`）、$S' = S\setminus\{p_0\}$（`restIdx`）。
- $A_N$ = `shellAlg N`（殻の射影 $E_s$・$D_s$ が生成する代数）、$A'_N$ = `fullCommAlg N`（その可換子）、$Z_N$ = `centerAlg N`（中心）。
- Part 225 の `shellAlgEquiv`：$A_N\cong\prod_{p\in S}\mathrm{End}(W_p)$、$T\mapsto(T|_{W_p})_p$。Part 223 の `fullCommMatrixEquiv`：$\prod_{p\in S}M_{\mathrm{Prim}(c_p)}(\mathbb C)\cong A'_N$（番号は原始指標の集合）。
- Part 237 の `piPrimeEquiv X N`：$\bigotimes_{p\mid N}X_{p^{v_p(N)}}\cong X_N$。`locOp N a` $=\iota^N_a$（$\mathbb Z/N\cong\mathbb Z/a\times\mathbb Z/(N/a)$ の第 1 座標に作用させた作用素）。
- `tpCongr e`：成分ごとの代数の同型 $e_i : A_i\cong B_i$ から作る $\bigotimes_iA_i\cong\bigotimes_iB_i$。

| 定理 | 主張 |
|---|---|
| `piSplitAlgEquiv_apply`, `matUniqueEquiv_apply` | 成分を切り離す代数の同型 $\prod_iB_i\cong B_{i_0}\times\prod_{i\ne i_0}B_i$（値は $(f(i_0), f|_{i\ne i_0})$）。$1\times1$ 行列 $\cong\mathbb C$（値は唯一の成分） |
| `commute_singleAlgHom`, `commFam_single_equiv`, **`tpCongr_tprod`**, `tpCongr_single` | 異なる位置の $1\otimes\cdots\otimes x\otimes\cdots\otimes1$ は可換。`tpCongr` は $\otimes_ix_i\mapsto\otimes_ie_i(x_i)$、$1\otimes\cdots\otimes a\otimes\cdots\otimes1\mapsto1\otimes\cdots\otimes e_i(a)\otimes\cdots\otimes1$ |
| `one_mem_centerIdx`, `layerDivs_one_one`, `finrank_refLayer_base` | $(1,1)\in S(N)$。導手 1・層 1 の層の約数はすべての約数。$\dim W_{p_0} = d(N)$ |
| `mem_layerPart_one_one`, **`mem_refLayer_base_iff`** | $W_{p_0}$ = 動径関数の空間 |
| `radialHom_apply`, **`radialHom_surjective`** | 制限 $A_N\to\mathrm{End}(W_{p_0})$ は $T\mapsto T|_{W_{p_0}}$ で、全射 |
| **`mem_centerIdx_primePow`**, `snd_eq_one_of_fst_eq_one` | $S(q^k) = \{(1,1)\}\cup\{(q^\gamma,q^\delta) : 1\le\gamma,\ \gamma+\delta\le k,\ (q,\gamma)\ne(2,1)\}$。$c = 1$ なら $d = 1$ |
| **`card_layerDivs_primePow`**, `finrank_refLayer_base_primePow`, `finrank_refLayer_rest` | $n_{(c,d)} = k+1$（$c = 1$）、$1$（$c\ne1$）。$\dim W_{p_0} = k+1$、$p\ne p_0$ なら $\dim W_p = 1$ |
| **`card_centerIdx_primePow`**, `card_restIdx_primePow` | $\#S(q^k) = 1+k(k+1)/2-[q=2]k$、$\#S'(q^k) = k(k+1)/2-[q=2]k$（$k\ge1$） |
| `finrank_shellAlg_primePow`, `finrank_fullComm_split` | $\dim A_{q^k} = (k+1)^2+\#S'$。$\dim A'_N = 1+\sum_{p\in S'}m(c_p)^2$ |
| **`endTensorEquiv_tprod`**, **`shellAlgPrimeTensorEquiv_symm_tprod`** | $\otimes_pS_p\mapsto\prod_p\iota^N_{p^{v_p}}(S_p)$（End）。逆向きで $\otimes_px_p\mapsto\prod_p\iota^N_{p^{v_p}}(\text{主定理 1}^{-1}(x_p))$（$A$） |

主定理は定義（同型）として書きました。

| 定義 | 同型 |
|---|---|
| **主定理 1** `shellAlgPrimePowEquiv` | $A_{q^k}\cong M_{k+1}(\mathbb C)\times\mathbb C^{S'(q^k)}$ |
| **主定理 2** `fullCommSplitEquiv` | $A'_N\cong\mathbb C\times\prod_{p\in S'(N)}M_{\mathrm{Prim}(c_p)}(\mathbb C)$（任意の $N$。instance `uniquePrimOne`：法 1 の原始指標はただ 1 つ） |
| **主定理 3** `shellAlgPrimeTensorEquiv` | $A_N\cong\bigotimes_{p\mid N}\bigl(M_{v_p(N)+1}(\mathbb C)\times\mathbb C^{S'(p^{v_p(N)})}\bigr)$ |
| **主定理 4** `fullCommPrimeTensorEquiv` | $A'_N\cong\bigotimes_{p\mid N}\bigl(\mathbb C\times\prod_{r\in S'(p^{v_p(N)})}M_{\mathrm{Prim}(c_r)}(\mathbb C)\bigr)$ |
| **主定理 5** `centerAlgPrimeTensorEquiv` | $Z_N\cong\bigotimes_{p\mid N}\mathbb C^{S(p^{v_p(N)})}$ |
| **主定理 6** `endTensorEquiv` | $\bigotimes_{p\mid N}\mathrm{End}(\mathbb C^{\mathbb Z/p^{v_p(N)}})\cong\mathrm{End}(\mathbb C^{\mathbb Z/N})$ |

道具の定義は `piSplitAlgEquiv`・`matUniqueEquiv`・`tpCongr`・`baseIdx`・`restIdx`（abbrev）・`radialHom` です。

**証明の筋**
1. **道具。**
   - `piSplitAlgEquiv` は Mathlib の `Equiv.piSplitAt` です。積・和・スカラーを保つことは、どれも定義から（`rfl`）出ます。
   - `matUniqueEquiv` は $M\mapsto M_{\ast\ast}$ を `AlgEquiv.ofLinearEquiv` で同型にしたものです。積を保つことは `Matrix.mul_apply` と `Fintype.sum_unique` です。
   - `tpCongr` は、Part 237 の `tpLift` で両方向の準同型を作り、`PiTensorProduct.algHom_ext` で互いに逆であることを示しました。族 $1\otimes\cdots\otimes e_i(\cdot)\otimes\cdots\otimes1$ の可換性は `commute_singleAlgHom`（Mathlib の `Pi.mulSingle_commute` と `Commute.tprod`）です。
   - 純テンソルの行き先：`tpLift_tprod` で $\prod_i(1\otimes\cdots\otimes e_i(x_i)\otimes\cdots\otimes1)$ になります。これは Mathlib の `PiTensorProduct.tprod_noncommProd` と `Finset.noncommProd_mulSingle` で $\otimes_ie_i(x_i)$ に戻ります。
2. **基準の番号。**
   - $(1,1)\in S(N)$ は $m(1) = 1$（Part 226 の `primCount_one`）と $1\in D(1)$ からです。
   - どの約数 $v$ も層 1 に入ります（$v = 1\cdot v$、$\gcd(v,1) = 1$）。そのため層の約数は $N$ のすべての約数で、$\dim W_{p_0} = d(N)$ です（Part 224 の `finrank_refLayer`）。
   - 法 1 の指標は自明な指標だけです（Mathlib の `DirichletCharacter.level_one`）。層 1 の条件は空なので、$W_{p_0}$ は Part 214 の `radial_iff_mem_span` の空間、つまり動径関数の空間です。
   - `radialHom` は Part 225 の `shellAlgEquiv` の $p_0$ 成分です。`shellAlgEquiv` は全単射なので、$p_0$ 成分だけが $S$ の元（`Pi.single`）を戻せば全射が出ます。
3. **素冪の番号と層。**
   - $q^k$ の約数は $q^\gamma$ だけです（`Nat.dvd_prime_pow`）。$m(q^\gamma) > 0\iff(q,\gamma)\ne(2,1)$ は Part 226 の `primCount_prime_pow_pos_iff` です。
   - $d = q^\delta\mid q^{k-\gamma}$ の条件 $\mathrm{rad}(d)\mid c$ は、$\gamma = 0$ なら $\delta = 0$ を強制し、$\gamma\ge1$ ならいつも成り立ちます。
   - 層の大きさは Part 226 の `card_layerDivs`（$n = \prod_{r\mid L,\ r\nmid c}(v_r(L)+1)$、$L = N/c$）です。$c = 1$ なら $r = q$ だけで $k+1$、$c = q^\gamma$（$\gamma\ge1$）なら条件を満たす $r$ がなく 1 です。
   - $\#S$ は $\dim Z$ に等しい（Part 222 の `center_eq_span`：中心は $S$ で番号をつけた一次独立な元で張られる）ので、Part 226 の `finrank_fullCommCenter_eq_prod` の素冪の場合です。
4. **主定理 1・2。**
   - 主定理 1：Part 225 の `shellAlgMatrixEquiv` を $p_0$ で切り離し、行列の番号を $\mathrm{Fin}(n_{p_0}) = \mathrm{Fin}(k+1)$、$\mathrm{Fin}(n_p) = \mathrm{Fin}\,1$ に付け替え（`Matrix.reindexAlgEquiv`）、$1\times1$ 行列を $\mathbb C$ にしました。
   - 主定理 2：Part 223 の `fullCommMatrixEquiv` の逆を $p_0$ で切り離し、$\mathrm{Prim}(1)$ がただ 1 つなので $M_{\mathrm{Prim}(1)}(\mathbb C)\cong\mathbb C$ としました。
   - 次元の系は Mathlib の `Module.finrank_prod`・`Module.finrank_matrix` などで数えるだけです。
5. **一般の $N$。**
   - 主定理 3〜5：Part 237 の `piPrimeEquiv`（$A$・$A'$・$Z$ は Part 236 の `crtMul_*`）の逆と、素冪の同型の `tpCongr` の合成です。
   - 主定理 6：Part 237 の `endPiEquiv`（因子は $\top$ の型）に、因子ごとの `Subalgebra.topEquiv` の逆の `tpCongr` を合成しました。
   - 純テンソルの行き先は `tpCongr_tprod` と Part 237 の `endPiEquiv_tprod`・`piPrimeEquiv_tprod` から出ます。

**例**
- $N = 16 = 2^4$：$S' = \{(4,1),(4,2),(4,4),(8,1),(8,2),(16,1)\}$ で、$\#S = 7 = 1+10-4$ です。
  - $A_{16}\cong M_5(\mathbb C)\times\mathbb C^6$（$\dim = 25+6 = 31$）。
  - $A'_{16}\cong\mathbb C\times M_1(\mathbb C)^3\times M_2(\mathbb C)^2\times M_4(\mathbb C)$（$m(4) = 1$、$m(8) = 2$、$m(16) = 4$、$\dim = 1+3+8+16 = 28$）。
  - $\mathbb C^{16} = W_{p_0}\oplus\bigoplus_{p\in S'}W_p\otimes\mathbb C^{m(c_p)}$ の次元は $5+3\cdot1+2\cdot2+1\cdot4 = 16$ です。
  - 数値のウェダーバーン成分 $(n, m)$ は $(5,1)$ が 1 個、$(1,1)$ が 3 個、$(1,2)$ が 2 個、$(1,4)$ が 1 個でした（§2 の (1)）。
- $N = 27 = 3^3$：$A_{27}\cong M_4(\mathbb C)\times\mathbb C^6$（$\dim 22$）、$A'_{27}\cong\mathbb C\times M_1(\mathbb C)^3\times M_4(\mathbb C)^2\times M_{12}(\mathbb C)$（$\dim 1+3+32+144 = 180$）。
- $N = 60 = 4\cdot3\cdot5$：$A_{60}\cong(M_3\times\mathbb C)\otimes(M_2\times\mathbb C)\otimes(M_2\times\mathbb C)$（$10\cdot5\cdot5 = 250$ 次元）。
  - 分配すると、成分 $(n,m)$ は $(12,1)$、$(6,3)$、$(6,1)$、$(3,3)$、$(4,1)$、$(2,3)$、$(2,1)$、$(1,3)$ の 8 個です（$m(4) = m(3) = 1$、$m(5) = 3$）。
  - $\sum n^2 = 250$、$\sum nm = 60$ です。数値でも同じ成分が出ました（§2 の (3)。分配は数値だけ）。
  - 最大の成分 $(12,1)$ は動径関数の空間（$d(60) = 12$）への作用 $M_{12}(\mathbb C)$ です。

**読み取れること**
- 素冪 $q^k$ では、$A$ の非可換な部分は動径関数の空間の $M_{k+1}(\mathbb C)$ だけです。ほかの成分では $A$ はスカラーで作用し、自由度は可換子 $A'$ の側（原始指標の数 $m(q^\gamma)$）にあります。
- 一般の $N$ では、番号は素数ごとに「基準の番号」か「それ以外」かを選んだものです。成分の大きさは $n = d(N_1)$（$N_1$ は基準の番号を選んだ素数の部分）、重複度は $m = \prod m(q^{\gamma_q})$（それ以外を選んだ素数の分）になります（数値で確認、§2 の (3)）。これは Part 226 の `card_layerDivs` の式 $\prod_{r\nmid c}(v_r(N/c)+1)$ の意味でもあります。
- Part 226 の積の式は、素冪の代数の次元の積です。$\dim A$ は $(k+1)^2$（動径関数の全行列環）と $\#S'$（1 次元の成分）の和、$\dim Z$ は $1+\#S'$ です。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| $S(q^k) = \{(1,1)\}\cup\{(q^\gamma,q^\delta)\}$ | **正しい（`mem_centerIdx_primePow`）**。数値でも定義から作った集合と一致（50/50） |
| 層の大きさ $n_{(1,1)} = k+1$、ほかは 1 | **正しい（`card_layerDivs_primePow`、`finrank_refLayer_base_primePow`、`finrank_refLayer_rest`）**。数値でも（同じ 50/50 の中で確認） |
| $\#S(q^k) = 1+k(k+1)/2-[q=2]k$ | **正しい（`card_centerIdx_primePow`、`card_restIdx_primePow`）**。Part 226 の積の式の素冪の場合 |
| $m(q) = q-2$、$m(q^\gamma) = q^{\gamma-2}(q-1)^2$ | **正しい（Part 226 の `primCount_prime`・`primCount_prime_pow`）**。数値でも再確認（45/45） |
| $W_{p_0}$ = 動径関数の空間、$\dim = d(N)$ | **正しい（`mem_refLayer_base_iff`、`finrank_refLayer_base`）** |
| $A$ は動径関数の空間に $M_{d(N)}(\mathbb C)$ として作用する | **正しい（`radialHom_surjective`）**。数値でも $N\le120$ で 119/119 |
| $A_{q^k}\cong M_{k+1}(\mathbb C)\times\mathbb C^{S'}$ | **正しい（`shellAlgPrimePowEquiv`、`finrank_shellAlg_primePow`）**。数値でもウェダーバーン成分・$\dim A$・$\dim Z$ が一致（44/44） |
| $A'_N\cong\mathbb C\times\prod_{p\in S'}M_{m(c_p)}(\mathbb C)$ | **正しい（`fullCommSplitEquiv`、`finrank_fullComm_split`）** |
| $A'_{q^k}$ では $M_{m(q^\gamma)}(\mathbb C)$ が $k+1-\gamma$ 個 | 3a と主定理 2 からの読み取り（個別の Lean の主張にはしていない）。次元の形は Part 226 の `finrank_fullComm_eq_prod`。数値でも成分の重複度が一致（(1) の中で確認） |
| $A_N$・$A'_N$・$Z_N\cong\bigotimes_{p\mid N}$（素冪の形） | **正しい（主定理 3〜5、`shellAlgPrimeTensorEquiv_symm_tprod`）** |
| $\mathrm{End}(\mathbb C^{\mathbb Z/N})\cong\bigotimes_{p\mid N}\mathrm{End}(\mathbb C^{\mathbb Z/p^{v_p}})$（因子は End そのもの） | **正しい（`endTensorEquiv`、`endTensorEquiv_tprod`）**。Part 237 の限界を解消 |
| 一般の $N$ のウェダーバーン成分 = 素冪ごとの成分の積 | **数値だけ**（素因数 2 個以上の $N\le120$ で 79/79）。Lean はテンソル積の形まで |
| 互いに素でない分け方 | 積の形にならない（数値の対照 6/6、期待どおり） |

## 2. 数値照合（step261）

$A_N$ のウェダーバーン成分 $p$ を、$A$ の中心の極小べき等元 $e_p$ で求めました：$n_p^2 = \dim e_pA$、$n_p m_p = \mathrm{rank}\,e_p$。中心は $A$ の元で生成元と可換なものです（$A'$ は計算しません）。$e_p$ は、中心の乱数の対称な元の固有空間への直交射影です。

| 項目 | 内容 | 結果 |
|---|---|---|
| (2m) | $m(q^\gamma)$（$\sum_{c\mid n}m(c) = \varphi(n)$ の反転）と閉じた式 $m(q) = q-2$、$m(q^\gamma) = q^{\gamma-2}(q-1)^2$（$q < 60$、$q^\gamma\le3000$） | 45/45 |
| (2) | 定義（$c\mid N$、$m(c) > 0$、$d\in D(c)$）から作った $S(q^k)$ と具体形の一致、層の大きさ（定義から数える）、$\#S$（$q < 60$、$q^k\le3000$） | 50/50 |
| (1) | 素冪（$q^k\le128$、$k\ge2$ と素数 $\le127$）：成分 $= \{(k+1,1)\}\cup\{(1,m(q^\gamma))^{k+1-\gamma}\}$、$\dim A = (k+1)^2+T$、$\dim Z$ = 成分の数 $= 1+T$（$T = k(k+1)/2-[q=2]k$） | 44/44（最大残差 4.5e-13） |
| (3) | 一般の $N$（素因数 2 個以上、$N\le120$）：成分 $(n,m)$ の多重集合 = 素冪ごとの多重集合の積（成分ごとの積）= 定義から作った予想 | 79/79（最大残差 3.0e-12） |
| (4) | 動径関数の空間 $R$（$\dim d(N)$）は $A$ で不変で、制限した生成元が生成する代数の次元は $d(N)^2$（$N\le120$） | 119/119（最大残差 2.5e-16） |
| (5) | 対照：互いに素でない分け方（$4 = 2\cdot2$、$8 = 2\cdot4$、$9 = 3\cdot3$、$27 = 3\cdot9$、$16 = 4\cdot4$、$12 = 2\cdot6$）では積の形にならない | 6/6（期待どおり） |

- 実行は 4 回かかりました（正直な記録）。
  - 1 回目：合成数の部分が長くかかったので、(1)(2) を終えたところで止めました。
  - 2 回目：(1)(2) と合成数 $N\le119$ はすべて一致でしたが、$N = 120$ の途中でコンテナが再起動して止まり、集計は出ませんでした。
  - 3 回目：$N$ ごとの結果をファイル（`step261_cache.json`）に保存する形にして実行しました。$N\le119$ までは 509 秒で通りました。$N = 120$（$\dim A = 475$）では、候補の行列とその SVD でメモリが 4.4 GB を超えて増えたので（コンテナは 8 GB、スワップなし）、止めました。2 回目の停止も、これによるコンテナの再起動と考えられます（確かめてはいません）。
  - 4 回目：候補の行列を分けて直交化する形（`algebra_generated_chunked`、張る空間は同じ）に替え、保存した結果から続けて $N = 120$ だけを計算しました（89 秒、メモリは 1.2 GB 以下）。分けた版は、$N = 24$・$60$ で 50 行ずつに分けても元の版と空間の差が 1e-11 以下でした。
  - ログの数値は、$N\le119$ と素冪は 3 回目（元の生成）、$N = 120$ は 4 回目（分けた生成）のものです。ログの「所要時間」は 4 回目の分だけです。
- **書き方。**
  - 代数の生成は、Part 236 の step259 の `algebra_generated` を使いました（新しく入った基底の塊に生成元を掛け、まとめて SVD で直交化します）。生成した空間が生成元の積で閉じていること（残差）も確かめ、成分の残差の最大値に含めました。
  - 動径関数の空間への制限は、生成元の制限が生成する $d(N)\times d(N)$ の行列の代数で調べました。
- **限界と失敗（正直な記録）。**
  - 速くするために書いた「基底 1 本ずつに生成元を掛けて直交化する」生成（`algebra_generated_fast`）は、数値の誤差の方向が閾値を超えて入り込み、空間が膨らみました（$N = 72$ で 228 次元を超えて 2625 次元、閾値 1e-6 でも $N = 96$ で 230 次元を超えて膨らんだ）。本当の新しい方向の残差も 1e-5 ほどと小さく、閾値で分けにくいためです。本番では使っていません（ファイルには失敗の記録として残しました）。
  - $\dim e_pA$ の数値の階数は、特異値の閾値 1e-6 で数えました。
  - (3) は $N\le120$ の素因数 2 個以上の $N$ だけです。(1) の素冪は $q^k\le128$ です。

## 3. Lean（`PAG242.lean`、namespace `PAG.Part242`、PAG241 を import）

| 区分 | 項目 |
|---|---|
| 1. 道具 | def `piSplitAlgEquiv`・`matUniqueEquiv`・`tpCongr`, `piSplitAlgEquiv_apply`, `matUniqueEquiv_apply`, `commute_singleAlgHom`, `commFam_single_equiv`, `tpCongr_tprod`, `tpCongr_single` |
| 2. 基準の番号と動径関数（一般の $N$） | def `baseIdx`・`radialHom`, abbrev `restIdx`, `one_mem_centerIdx`, `layerDivs_one_one`, `finrank_refLayer_base`, `mem_layerPart_one_one`, `mem_refLayer_base_iff`, `radialHom_apply`, `radialHom_surjective` |
| 3. 素冪の番号と層 | `mem_centerIdx_primePow`, `snd_eq_one_of_fst_eq_one`, `card_layerDivs_primePow`, `card_centerIdx_primePow`, `finrank_refLayer_base_primePow`, `finrank_refLayer_rest`, `card_restIdx_primePow` |
| 4. 素冪の $A$・$A'$ | instance `uniquePrimOne`, def `shellAlgPrimePowEquiv`・`fullCommSplitEquiv`, `finrank_shellAlg_primePow`, `finrank_fullComm_split` |
| 5. 一般の $N$ | def `shellAlgPrimeTensorEquiv`・`fullCommPrimeTensorEquiv`・`centerAlgPrimeTensorEquiv`・`endTensorEquiv`, `endTensorEquiv_tprod`, `shellAlgPrimeTensorEquiv_symm_tprod` |

**使った PAG の結果**
- Part 203 の `Radial`（PAG207）、Part 214 の `shellAlg`・`radial_iff_mem_span`（PAG218）
- Part 216 の `layerPart`・`mem_layerPart`・`layerIdx`・`mem_layerIdx`（PAG220）、Part 217 の `layerDivs`（PAG221）
- Part 222 の `centerIdx`・`mem_centerIdx`・`centerAlg`・`fullCommCenter`・`center_eq_span`・`centralElt_linearIndependent`・`centerAlgEquiv`（PAG226）
- Part 223 の `Prim`・`fullCommMatrixEquiv`（PAG227）、Part 224 の `refLayer`・`finrank_refLayer`（PAG228）、Part 225 の `shellAlgEquiv`・`shellAlgMatrixEquiv`（PAG229）
- Part 226 の `primCount`・`primCount_one`・`primCount_prime_pow_pos_iff`・`card_layerDivs`・`finrank_fullCommCenter_eq_prod`（PAG230）
- Part 236 の `crtMul_shellAlg`・`crtMul_fullCommAlg`・`crtMul_centerAlg`（PAG240）
- Part 237 の `CommFam`・`tpLift`・`tpLift_tprod`・`tpLift_single`・`pwComm`・`piPrimeEquiv`・`piPrimeEquiv_tprod`・`endPiEquiv`・`endPiEquiv_tprod`・`locOp`・`coprime_ordProj`・`commute_locOp_pp`（PAG241）

**Mathlib・Lean から使った主なもの**
- `Equiv.piSplitAt`・`AlgEquiv.ofLinearEquiv`・`AlgEquiv.ofAlgHom`・`AlgEquiv.prodCongr`・`AlgEquiv.piCongrRight`・`Matrix.reindexAlgEquiv`・`finCongr`・`Pi.evalAlgHom`・`Pi.single_eq_same`・`Subalgebra.topEquiv`
- `PiTensorProduct.singleAlgHom_apply`・`PiTensorProduct.algHom_ext`・`PiTensorProduct.tprod_noncommProd`・`Finset.noncommProd_mulSingle`・`Commute.tprod`・`Pi.mulSingle_commute`
- `DirichletCharacter.level_one`・`DirichletCharacter.isPrimitive_one_level_one`・`Nat.dvd_prime_pow`・`Nat.pow_div`・`Nat.divisors_prime_pow`・`Nat.primeFactors_prime_pow`・`Nat.factorization_pow`
- `Module.finrank_prod`・`Module.finrank_matrix`・`Module.finrank_fintype_fun_eq_card`・`Module.finrank_pi_fintype`・`finrank_span_eq_card`・`Fintype.card_subtype_compl`・`Fintype.card_subtype_eq`

**コンパイル**
- `PAG242` は 2 回コンパイルし、どちらもエラー・警告なしで通りました。公理はすべて標準のもの（propext、Classical.choice、Quot.sound）です（37 行）。
  - 1 回目は T5 から組み立てた版（35 個、約 20 秒）です。
  - その後、End そのものを因子にした `endTensorEquiv` と `endTensorEquiv_tprod` を足した T6 が通ったので、T7（T6 の docstring の番号を直したもの）から組み立て直しました（37 個、約 18 秒）。納品はこちらです（`/home/claude/out/assemble242.py`）。
- **新しい書き方。**
  - `tpLift` の `CommFam` の引数を λ（`fun _ _ hij _ _ => …`）で渡すと、その項を含むゴールで `simp only [tpLift_single]` や `rw` が働きませんでした。λ の項の型は `CommFam (…)` の字面ではなく、implicit 透明度で照合できないためです（Part 237 の `pwComm` と同じ問題）。主張を `CommFam (fun i => …)` の字面で書いた補題 `commFam_single_equiv` を通しました。
  - Mathlib の `Finset.noncommProd_mulSingle` の左辺にも λ の可換性の証明が入っています。`conv` で書き換えると同じ問題が起きたので、`calc` の各段を項（`congrArg`・`PiTensorProduct.tprod_noncommProd`・`Finset.noncommProd_congr`）で書きました。
  - λ の変数の型を書かないと、`fun p => … (N.factorization p) … p.2` の p は `N.factorization p` から $\mathbb N$ と推論されました。`p.2` が使えなくなるうえ、テンソル積の番号の型も $\mathbb N$ になり、型の強制（`CoeT`）の推論が時間切れになりました。`fun p : N.primeFactors => …` と書きます。
  - 純テンソルの定理（5a・5b）では、定義を開いた等式を `have h2 : … := rfl` と明示してから `rw [h2]` としました。
- **PAG242 の前の試しのファイル（置き場所は `/home/claude/leanwork/scratch/t238`）。**
  - W0〜W3 は確かめのための小さなファイルです。
    - W0：import の温め（PAG241 を読むだけ）。コンテナの再起動の後でキャッシュが冷えていて、250 秒かかりました。
    - W1：`Matrix.uniqueAlgEquiv` がない（`Mathlib.LinearAlgebra.Matrix.Unique` がビルドされていない）ことがわかりました。1 × 1 行列 ≅ ℂ を手で書くことにしました。
    - W2：`Fintype.card_subtype_ne` はありませんでした（`Fintype.card_subtype_compl` と `Fintype.card_subtype_eq` を使う）。
    - W3：`tpLift_single` で書き換えられない原因が、λ で渡した `CommFam` の証明の型であることを確かめました。
  - T1（エラー 10 件、警告 17 件）には、次の 6 種類がありました。
    - **λ の変数の型（1 件）。** `piSplitAlgEquiv_apply` の値 `(f i₀, fun j => f j)` で、`j : {i // i ≠ i₀}` を書かなかったため、型が合いませんでした。
    - **λ の可換性の証明（3 件）。** `tpCongr` の逆であることの証明で `simp` が `tpLift_single` を使えず（2 件）、`tpCongr_tprod` の `rw [tpLift_tprod]` も失敗しました（上の注）。
    - **`DecidablePred`（1 件）。** `Finset.mem_filter` で `layerDivs` の条件の `DecidablePred` が見つかりませんでした。
    - **`simp` が進まない（1 件）。** `finrank_refLayer_rest` で、番号の等しさを `simp` で示せませんでした。
    - **`noncomputable`（1 件）。** 法 1 の原始指標の `Unique` インスタンスは `MulChar.hasOne` に依存するので、`noncomputable` が要りました。
    - **型を書かない λ（3 件）。** 逆向きの純テンソルの定理（5b）の `fun p => …` で、p : ℕ と推論されました（上の注）。
    - 警告は、非推奨の `AlgEquiv.toAlgHom_eq_coe`・`AlgHom.coe_coe`・`if_pos`・`if_neg`、使われない simp の補題 8 か所、使われない節の変数 `[Fintype ι]`（変数の宣言を後ろに移した）などでした。
  - T2（エラー 7 件、警告 4 件）：λ の変数の型と `tpCongr` の `simp` は直りました（`commFam_single_equiv` を通した）。残ったのは次のものです。
    - `tpCongr_tprod`：`conv` で `Finset.noncommProd_mulSingle` を使って書き換えると、λ の証明が入り込みました。`calc` にしました。
    - `DecidablePred`（`classical` を足した）、`finrank_refLayer_rest`（`Subtype.ext (Sigma.ext …)` にした）、`noncomputable`（足した）。
    - 型を書かない λ の 3 件。このときは原因を `show` の `_` と見誤り、`have h2 : … := rfl` に書き換えましたが、T3 でも同じエラーが残りました。
    - 警告：素冪の $A'$ の同型で仮定（$q$ が素数）を使っていませんでした。一般の $N$ の `fullCommSplitEquiv` にしました。`if_pos`・`if_neg` は `Finset.filter_true_of_mem`・`split_ifs` に変えました。
  - T3（エラー 4 件、警告 1 件）：`layerDivs_one_one` の証明の頭にも `classical` が要りました（1 件）。型を書かない λ の 3 件は、ここで本当の原因（p : ℕ の推論）がわかりました。`fun p : N.primeFactors => …` と書いて直しました。警告は使われない変数 `χ` でした。
  - T4：エラー・警告なしで通りました。T5（主定理 5 を足した版）も通りました（73 秒。数値の実行と重なったため）。ここから PAG242 を 1 回目に組み立てました（約 20 秒）。
  - T6：`endTensorEquiv`・`endTensorEquiv_tprod` を足して通りました（18 秒）。T7 は docstring の番号（5a・5b）を直しただけです。
- **環境。**
  - Mathlib の追加ビルドはありません。
  - Part 237 の納品の後、Part 238 の開始時（05:48）にコンテナが再起動していました（起動時刻 05:48:21）。ファイルと .olean は残っていました。
  - step261 の 2 回目の実行中（07:07）にもコンテナが再起動しました（起動時刻 07:07:37）。ファイルは残っていました。$N = 120$ の計算でメモリを使い切ったためと考えられます（§2）。

## 4. 残る問い

1. **（次の候補）動径関数の空間の上の $A$ の具体的な形。** 今回、$A$ が動径関数の空間（基底は殻 $\{x : \gcd(x,N) = s\}$ の指示関数、$s\mid N$）に $M_{d(N)}(\mathbb C)$ として作用することを示しました（`radialHom_surjective`）。その上での $E_s$・$D_s$ の行列（$D_s$ は対角の射影、$E_s$ はラマヌジャン和の行列）と $\mathcal F$ の行列を具体的に書き、$M_{d(N)}(\mathbb C)$ を生成することを直接示すこと。素冪 $q^k$ では $(k+1)\times(k+1)$ の行列で、テンソル積で一般の $N$ に移ります。
2. **分配した形。** $A_N$ のウェダーバーン成分を Lean で「素冪ごとの成分の積」として書くこと（$\otimes$ を $\times$ に分配する同型と $M_a\otimes M_b\cong M_{ab}$）。今回は数値だけです。
3. **dilComm の素冪の形。** dilComm$_{q^k}$ の具体的な形と、その素冪ごとのテンソル積。
4. **Part 236 の形との比較。** `tensEquiv`（右から重ねた形）と `piTensEquiv` の比較（任意）。
5. 引き継ぎメモのほかの候補（1i・1h・1g・1a・1d・1c、法 $p$ の局所の仮定、Ẑ、数論の問い）はそのままです。
