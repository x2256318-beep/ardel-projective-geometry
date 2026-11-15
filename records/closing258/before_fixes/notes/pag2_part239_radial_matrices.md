# アデール射影幾何 2.0 — Part 239：動径関数の空間の上の $A$ の具体的な形（$E_s$・$D_s$・$\mathcal F$ の行列と、$A$ の中の行列単位）

2026-11-05。引き継ぎメモの次の候補（動径関数の空間の上の $E_s$・$D_s$・$\mathcal F$ の行列を具体的に書き、全行列環 $M_{d(N)}(\mathbb C)$ が出ることを直接示すこと）を進めました。

Part 238 では、$A_N$ が動径関数の空間 $R = W_{p_0}$（次元 $d(N)$）に全行列環として作用することを、Part 225 の同型から抽象的に示しました（`radialHom_surjective`）。今回は殻の指示関数の基底 $(1_{D_t})_{t\mid N}$ をとり、作用を具体的な行列で書きました。さらに、全行列環の行列単位そのものを $A_N$ の中に作りました。

- **基底（Lean）。** 動径関数は殻ごとに一定で、$f = \sum_{t\mid N}f(t)\,1_{D_t}$ です（`radial_eq_sum`）。
  - これで座標の同型 $R\cong\mathbb C^{\{t\mid N\}}$、$f\mapsto(f(t))_t$（`radialCoord`）と基底（`radialBasis`）を作りました。
  - $T\in A_N$ の $R$ の上の行列の $(u,t)$ 成分は $(T1_{D_t})(u)$ です（`toMatrix_radialHom`）。
- **行列（Lean）。**
  - $[D_s]$ は行列単位 $E_{ss}$ です（`toMatrix_D`）。
  - $[E_s](u,t) = N\,\varepsilon_t(s)\,\varepsilon_s(u) = C(s,t)\,C(u,s)/N$ です（`toMatrix_E`・`toMatrix_E_eq_ramMat`）。列と行の積なので階数 1 です。
  - 特に $E_N$ は定数関数への射影で、$[E_N](u,t) = \varphi(N/t)/N$ です。どの成分も 0 ではありません（`toMatrix_E_self`）。
  - $\mathcal F$ の行列はラマヌジャンの行列 $C(u,t) = N\varepsilon_t(u) = c_{N/t}(u)$ です（`toMatrix_radialDFT`）。$C^2 = N\cdot1$（`ramMat_mul_self`）、$C[E_s] = [D_s]C$（`ramMat_mul_toMatrix_E`）が成り立ちます。
- **$A$ の中の行列単位（Lean）。** 殻の移し替え $P_{s,t} = \frac{N}{\varphi(N/t)}D_sE_ND_t\in A_N$（`shellTrans`）を定義しました。
  - 陽な形は「$D_t$ の上の $f$ の平均を $1_{D_s}$ に置く」作用素です（`shellTrans_apply`）。
  - **空間全体の作用素として** $P_{s,t}P_{t',r} = [t = t']\,P_{s,r}$ が成り立ちます（`shellTrans_mul`）。
  - そのため、$M\mapsto\sum_{s,t}M_{st}P_{s,t}$ は単射な非単位的代数準同型 $M_{d(N)}(\mathbb C)\to A_N$ になります（`radialMatHom`、`radialMatHom_injective`）。**$A_N$ の中に $M_{d(N)}(\mathbb C)$ の写しが具体的にあります。**
  - その $R$ への制限は、行列から $\mathrm{End}(R)$ への同型です（`toMatrix_radialHom_radialMatOp`）。これで Part 238 の全射の明示的な原像ができました（`radialSection`、`radialHom_radialSection`）。
  - $P_{s,t}$ は $D_s$・$E_N$・$D_t$ の積なので、**$D_s$ と $E_N$ だけで、$R$ の上の全行列環が出ます**（`radialHom_diagAvg_surjective`）。
- **素冪とクロネッカー積（Lean）。**
  - $N = q^k$：$C(q^i,q^j) = 1$（$j = k$）、$q^{k-j}[k-j\le i]-q^{k-j-1}[k-j-1\le i]$（$j<k$）です（`ramMat_primePow`）。
  - 互いに素な $a, b$ では $C_{ab}(u_au_b,t_at_b) = C_a(u_a,t_a)\,C_b(u_b,t_b)$ です（`ramMat_mul_coprime`）。
- **数値だけの観察（正直な注記）。**
  - $\sum_sP_{s,s}$ は $R$ への直交射影で、単数倍の平均 $\frac1{\varphi(N)}\sum_aU_a$ に等しく、$A$ の生成元のすべてと可換です（$A$ の中心の元）。$N\le120$ で確認しました。
  - 空間全体の $\dim\langle D_s, E_N\rangle = d(N)^2+d(N)-1-[2\mid N]$ です（$N\le60$）。
  - $\{D_u|_R\}\cup\{E_s|_R\}$ が全行列環を生成するのは、$N/s$ が平方因子をもたないときちょうどです（$N\le300$ のすべての $s$）。
- **やり直し。** 試しのファイル T1〜T4 を 4 回コンパイルしました。主要部の T1（36 項目）は 1 回目で通りました。
  - T2 で、行列単位の埋め込みが積を保つことの証明が通りませんでした。二重和の積を `Finset.sum_mul`・`Finset.mul_sum` で展開したため、和の順序が変わったのが原因です。
  - これは Part 234 で記録した注意（`Fintype.sum_mul_sum` を使う）の見落としです。T3 で直しました（§3）。
- **環境。** Mathlib の追加ビルドはありません。作業の開始時（13:58）にコンテナが再起動していました。

成果物は次のとおりです。
- `PAG243.lean`：49 項目。sorry 0・警告 0 です。
  - 定義 9 個は項目に数えません。
  - 出力は `PAG243.out`（#print axioms 58 行）。
- 照合用の `step262.py`：ログは `step262.log` です。

xlsx の集計は 2929 項目になりました（手順 259）。

## 0. 結論

**記号**
- $D_t = \{x\in\mathbb Z/N : \gcd(N,x) = t\}$（殻）、$1_{D_t}$ = `dind N t`。$\varepsilon_s = \mathcal F^{-1}(1_{D_s})$ = `geps N s`（Part 201）。
- $E_s f = \varepsilon_s\star f$、$D_s f = 1_{D_s}\cdot f$。$A_N$ = `shellAlg N` はこれらが生成する代数です（Part 214）。
- $R = W_{p_0}$：動径関数（単数倍で不変な関数）の空間。Part 238 の `refLayer N (baseIdx N)` で、次元は $d(N)$ です。`radialHom N` $: A_N\to\mathrm{End}(R)$ は制限です。
- 行列の番号は $N$ の約数（型 `N.divisors`）。点 $u\mid N$ は $u\bmod N$ です（$u = N$ は 0）。$[T](u,t) = (T1_{D_t})(u)$。
- $C(u,t) = N\varepsilon_t(u)$（`ramMat`）。$C(u,t) = c_{N/t}(u)$（ラマヌジャン和）です。
- $P_{s,t} = \frac N{\varphi(N/t)}D_sE_ND_t$（`shellTrans`）。

| 定理 | 主張 |
|---|---|
| `gcd_val_natCast_of_dvd`, `dind_natCast`, `radial_apply_eq`, **`radial_eq_sum`**, `dind_mem_base` | $u\mid N$ なら $\gcd(N,u) = u$、$1_{D_t}(u) = [u = t]$。動径関数は殻ごとに一定で、$f = \sum_tf(t)1_{D_t}$。$1_{D_t}\in R$ |
| `radialBasis_apply`, `radialBasis_repr`, **`toMatrix_radialHom`** | 基底の元は $1_{D_t}$、座標は値 $f(t)$。$[\mathrm{radialHom}\,T](u,t) = (T1_{D_t})(u)$ |
| `geps_neg`, `dft_dind`, `conv_geps_dind` | $\varepsilon_t(-\xi) = \varepsilon_t(\xi)$。$\mathcal F1_{D_t} = N\varepsilon_t$。$E_s1_{D_t} = N\varepsilon_t(s)\,\varepsilon_s$ |
| **`toMatrix_D`**, **`toMatrix_E`** | $[D_s] = E_{ss}$。$[E_s](u,t) = N\varepsilon_t(s)\varepsilon_s(u)$ |
| `geps_self`, `conv_geps_self`, **`toMatrix_E_self`** | $\varepsilon_N = 1/N$、$E_Ng = \frac1N\sum g$、$[E_N](u,t) = \varphi(N/t)/N$ |
| `shellTrans_mem`, **`shellTrans_apply`**, `sum_dind_mul_dind`, `shellTrans_dind` | $P_{s,t}\in A_N$。$P_{s,t}f = \frac{\sum_y1_{D_t}(y)f(y)}{\varphi(N/t)}1_{D_s}$。$\sum_y1_{D_t}1_{D_r} = [t = r]\varphi(N/t)$。$P_{s,t}1_{D_r} = [t = r]1_{D_s}$ |
| **`shellTrans_mul`**, `toMatrix_shellTrans`, `shellTrans_mul_div` | $P_{s,t}P_{t',r} = [t = t']P_{s,r}$（空間全体）。$[P_{s,t}] = E_{st}$ |
| `radialMatOp_mem`, **`radialMatOp_mul`**, `radialMatOp_one`, **`toMatrix_radialHom_radialMatOp`**, `radialMatOp_injective`, **`radialMatHom_injective`** | $\Phi(M) = \sum M_{st}P_{s,t}\in A_N$、$\Phi(MM') = \Phi(M)\Phi(M')$、$\Phi(1) = \sum_sP_{s,s}$、$[\Phi(M)|_R] = M$、$\Phi$ は単射 |
| **`radialHom_radialSection`** | $\mathrm{radialHom}(\Phi([S])) = S$（明示的な原像） |
| `diagAvgAlg_le`, `radialMatOp_mem_diagAvg`, **`radialHom_diagAvg_surjective`** | $\langle D_s, E_N\rangle\subseteq A_N$、$\Phi(M)\in\langle D_s, E_N\rangle$。$D_s$ と $E_N$ だけで $R$ の上の全行列環が出る |
| `sum_dind_mul_radial`, `shellTrans_self_radial`, `sum_shellTrans_self_radial` | 動径関数 $f$ で $\sum_y1_{D_s}f = \varphi(N/s)f(s)$、$P_{s,s}f = f(s)1_{D_s}$、$\sum_sP_{s,s}f = f$ |
| **`natCast_mul_geps`**, `ramMat_apply` | $C(u,t) = N\varepsilon_t(u) = \sum_{e\mid N/t}\mu(e)\frac N{te}[\frac N{te}\mid u]$ |
| **`toMatrix_radialDFT`**, `radialDFT_mul_self`, **`ramMat_mul_self`** | $[\mathcal F|_R] = C$。$R$ の上で $\mathcal F^2 = N$。$C^2 = N\cdot1$ |
| `dft_conv_geps`, **`ramMat_mul_toMatrix_E`**, `toMatrix_E_eq_ramMat` | $\mathcal FE_s = D_s\mathcal F$。$C[E_s] = [D_s]C$。$[E_s](u,t) = C(s,t)C(u,s)/N$ |
| `ramMat_apply_col_self`, `ramMat_apply_row_self` | $C(u,N) = 1$、$C(N,t) = \varphi(N/t)$ |
| `sum_divisors_primePow_moebius`, **`ramMat_primePow`** | $\sum_{e\mid q^n}\mu(e)g(e) = g(1)-g(q)$（$n\ge1$）。素冪の $C$ の式 |
| **`ramMat_mul_coprime`** | $C_{ab}(u_au_b,t_at_b) = C_a(u_a,t_a)C_b(u_b,t_b)$（$\gcd(a,b) = 1$） |

定義は `radialCoord`・`radialBasis`・`shellTrans`・`radialMatOp`・`radialMatHom`（$M_{d(N)}(\mathbb C)\to_{\text{非単位的}}A_N$）・`radialSection`・`diagAvgAlg`（$\langle D_s, E_N\rangle$）・`ramMat`・`radialDFT`（$\mathcal F|_R$）です。

**証明の筋**
1. **基底。**
   - 動径関数は殻ごとに一定です：$\xi = a\cdot\gcd(N,\xi)$（$a$ は単数、Part 203 の `exists_unit_mul_gcd`）なので $f(\xi) = f(\gcd(N,\xi))$。
   - $u\mid N$ の点 $u$ は殻 $D_u$ にあります（$\gcd(N,u\bmod N) = u$）。そのため $\sum_tf(t)1_{D_t}$ を $\xi$ で評価すると、$t = \gcd(N,\xi)$ の項だけが残ります。
   - 座標の同型を `LinearEquiv` で作り、Mathlib の `Module.Basis.ofEquivFun` で基底にしました。座標は値そのもの（`rfl`）なので、行列の成分は $(T1_{D_t})(u)$ です。
2. **$E_s$ の行列。**
   - $\mathcal F1_{D_t} = \mathcal F\mathcal F\varepsilon_t = N\varepsilon_t(-\cdot) = N\varepsilon_t$（Mathlib の `ZMod.dft_dft` と、単数 $-1$ での不変性）。
   - $\mathcal F(E_s1_{D_t}) = 1_{D_s}\cdot N\varepsilon_t$。$D_s$ の上で $\varepsilon_t$ は一定値 $\varepsilon_t(s)$ なので、これは $N\varepsilon_t(s)\,1_{D_s} = \mathcal F(N\varepsilon_t(s)\varepsilon_s)$ です。$\mathcal F$ の単射性から $E_s1_{D_t} = N\varepsilon_t(s)\varepsilon_s$。
   - $\varepsilon_N = 1/N$ は、Part 228 の `geps_apply_eq_sum` に $s = N$ を入れると出ます（$N/N = 1$）。
3. **行列単位。**
   - $E_Ng = \frac1N\sum g$ なので、$D_sE_ND_tf = \frac1N\bigl(\sum_y1_{D_t}(y)f(y)\bigr)1_{D_s}$ です。
   - $\sum_y1_{D_t}1_{D_r} = [t = r]\,\#D_t = [t = r]\varphi(N/t)$（Part 201 の `card_dsh`）から $P_{s,t}1_{D_r} = [t = r]1_{D_s}$。
   - 積の規則は $P_{s,t}P_{t',r}f = c_f\,P_{s,t}1_{D_{t'}}$（$c_f$ は $D_r$ の上の $f$ の平均）から出ます。
   - $\Phi(MM') = \Phi(M)\Phi(M')$ は二重和の積を `Fintype.sum_mul_sum` で展開し、$[t = t']$ の和を消して出しました。
   - $[\Phi(M)|_R] = \sum_{s,t}M_{st}E_{st} = M$ なので、$\Phi$ は単射で、$\mathrm{radialHom}\circ\Phi$ は行列から $\mathrm{End}(R)$ への同型です。
4. **ラマヌジャンの行列。**
   - $[\mathcal F|_R](u,t) = (\mathcal F1_{D_t})(u) = N\varepsilon_t(u)$。$\varepsilon_t$ の値は Part 228 の式（球の交代和）で、クルイフェルの形 $\sum_{e\mid N/t}\mu(e)\frac N{te}[\frac N{te}\mid u]$ になります。
   - $C^2 = N$ は、$R$ の上で $\mathcal F^2 = N\cdot f(-\cdot) = N f$ を行列にしたものです（`LinearMap.toMatrix_mul`）。これはラマヌジャン和の直交関係 $\sum_rc_{N/r}(u)\,c_{N/t}(r) = N[u = t]$ です。
   - $C[E_s] = [D_s]C$ は $\mathcal F(\varepsilon_s\star f) = 1_{D_s}\mathcal Ff$ の制限です。
5. **素冪とクロネッカー積。**
   - $q^n$ の約数は $q^m$ で、$\mu(q^m) = 0$（$m\ge2$）なので $\sum_{e\mid q^n}\mu(e)g(e) = g(1)-g(q)$ です。これを $C$ の式に入れました。
   - 積は Part 228 の `geps_crt`（$\varepsilon_{s_as_b}(x) = \varepsilon_{s_a}(x\bmod a)\varepsilon_{s_b}(x\bmod b)$）です。$u_au_b\bmod a$ は $u_a$ の単数倍（$u_b$ は $a$ と互いに素）なので、値は $\varepsilon_{t_a}(u_a)$ になります。

**例**
- $N = 12$（約数 1, 2, 3, 4, 6, 12。行が $u$、列が $t$）：
  $$C = \begin{pmatrix}0&1&0&-1&-1&1\\2&-1&-2&-1&1&1\\0&-2&0&2&-1&1\\-2&-1&2&-1&1&1\\-4&2&-2&2&1&1\\4&2&2&2&1&1\end{pmatrix}$$
  - 最後の列は $C(u,12) = c_1(u) = 1$、最後の行は $C(12,t) = \varphi(12/t)$ です。$C^2 = 12\cdot1$ です。
  - $[E_{12}](u,t) = \varphi(12/t)/12 = (4, 2, 2, 2, 1, 1)/12$ で、どの行も同じです。
  - 数値の観察では、$E_s$ だけで（$D_u$ と合わせて）$R$ の上の全行列環が出るのは $s = 12, 6, 4, 2$（$N/s = 1, 2, 3, 6$、平方因子なし）でした。$s = 3, 1$（$N/s = 4, 12$）では出ません。
- $N = 8$（約数 1, 2, 4, 8）：
  $$C = \begin{pmatrix}0&0&-1&1\\0&-2&1&1\\-4&2&1&1\\4&2&1&1\end{pmatrix}$$
  素冪の式（`ramMat_primePow`）のとおりで、$C^2 = 8\cdot1$ です。
- $N = 60 = 4\cdot3\cdot5$ では $C_{60} = C_4\otimes C_3\otimes C_5$（番号 $u = u_4u_3u_5$）です。2 つの因子ずつ `ramMat_mul_coprime` を当てます。

**読み取れること**
- $R$ の上で、$D$ の族は殻の基底の座標の射影で、$E$ の族は直線 $\mathbb C\varepsilon_s$ への階数 1 の射影です（成分は $C(u,s)/N$）。2 つの族は「一般の位置」にあります。すべての $D_s$ と **ただ 1 つの** $E_N$ だけで、もう全行列環が出ます（$[E_N]$ の成分がどれも 0 でないため）。
- $A_N$ のウェダーバーン分解の動径の成分（Part 238 の $(1,1)$ の成分、重複度 $m(1) = 1$）は、$A_N$ の中の行列単位 $P_{s,t}$ で具体的に張られます。$P_{s,t}$ は「殻 $t$ の上で平均して、殻 $s$ に置く」作用素です。
- 𝓕 の行列 $C$ は $C^2 = N$ を満たし、$E_s = \mathcal F^{-1}D_s\mathcal F$ は $R$ の上で $C^{-1}[D_s]C$ です。素冪の $C$ は $(k+1)\times(k+1)$ の具体的な行列で、一般の $N$ ではそのクロネッカー積です。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| 動径関数 $= \sum_tf(t)1_{D_t}$、基底と座標 | **正しい（`radial_eq_sum`、`radialBasis`、`radialBasis_repr`）**。数値でも 300/300 |
| $[D_s] = E_{ss}$ | **正しい（`toMatrix_D`）**。数値でも 1767/1767 |
| $[E_s](u,t) = N\varepsilon_t(s)\varepsilon_s(u) = C(s,t)C(u,s)/N$ | **正しい（`toMatrix_E`、`toMatrix_E_eq_ramMat`）**。数値でも 1767/1767 |
| $[E_s]$ は階数 1 | 式（列と行の積）と $[E_s](N,N) = \varphi(N/s)/N\ne0$ から読める（個別の Lean の主張にはしていない）。数値でも 1767/1767 |
| $[E_N](u,t) = \varphi(N/t)/N$（どれも 0 でない） | **正しい（`toMatrix_E_self`）**。数値でも 300/300 |
| $P_{s,t} = \frac N{\varphi(N/t)}D_sE_ND_t$ は平均を移す作用素、$P_{s,t}P_{t',r} = [t = t']P_{s,r}$ | **正しい（`shellTrans_apply`、`shellTrans_mul`）**。数値でも 4038/4038・109623/109623 |
| $\Phi(M) = \sum M_{st}P_{s,t}$ は単射な非単位的代数準同型、$[\Phi(M)|_R] = M$ | **正しい（`radialMatHom`、`radialMatHom_injective`、`toMatrix_radialHom_radialMatOp`）**。数値でも 120/120 |
| 明示的な原像 $\mathrm{radialHom}(\mathrm{radialSection}\,S) = S$ | **正しい（`radialHom_radialSection`）** |
| $D_s$ と $E_N$ だけで $R$ の上の全行列環 | **正しい（`radialHom_diagAvg_surjective`）**。数値でも $R$ の上の生成した代数の次元 $= d(N)^2$（300/300）。対照：$\langle D_s|_R\rangle$ だけなら $d(N)$ 次元（300/300） |
| $\sum_sP_{s,s}$ は動径関数の上で恒等 | **正しい（`sum_shellTrans_self_radial`）** |
| $\sum_sP_{s,s}$ = $R$ への直交射影 = 単数倍の平均、$A$ の中心の元 | **数値だけ**（$N\le120$ で 120/120） |
| $C = [\mathcal F|_R]$、$C(u,t) = c_{N/t}(u)$（クルイフェルの式）、$C^2 = N$、$C[E_s] = [D_s]C$、$C(u,N) = 1$、$C(N,t) = \varphi(N/t)$ | **正しい（`toMatrix_radialDFT`、`ramMat_apply`、`ramMat_mul_self`、`ramMat_mul_toMatrix_E`、`ramMat_apply_col_self`・`row_self`）**。数値でも 300/300（直接の和 $\sum_be(bu/q)$ とも一致） |
| 素冪の $C$ の式 | **正しい（`ramMat_primePow`）**。数値でも 877/877 |
| クロネッカー積 $C_{ab} = C_a\otimes C_b$ | **正しい（`ramMat_mul_coprime`、2 つの因子）**。数値でも 29477/29477。3 つ以上の因子への繰り返しは個別の主張にしていない |
| 空間全体の $\dim\langle D_s, E_N\rangle = d(N)^2+d(N)-1-[2\mid N]$ | **数値だけ**（$N\le60$ で 60/60） |
| $\langle D_u|_R, E_s|_R\rangle = M_{d(N)}$ ⇔ $N/s$ が平方因子をもたない | **数値だけ**（$N\le300$ のすべての $s$ で 1767/1767） |

## 2. 数値照合（step262）

記号は Lean と同じです：$\mathcal F\Phi(k) = \sum_je(-jk/N)\Phi(j)$、$\varepsilon_s = \mathcal F^{-1}1_{D_s}$、$E_s$ は $\varepsilon_s$ との畳み込み、$D_s$ は対角です。行列 $[T](u,t) = (T1_{D_t})(u)$ は、空間全体の $N\times N$ 行列から直接取り出しました。

| 項目 | 内容 | 結果 |
|---|---|---|
| (1) | $\mathrm{rank}(1_{D_t})_t = d(N)$、動径関数の座標は値（$N\le300$、乱数の係数） | 300/300（誤差 0） |
| (2) | $[D_s] = E_{ss}$（$N\le300$、すべての $s$） | 1767/1767（誤差 0） |
| (3) | $[E_s](u,t) = N\varepsilon_t(s)\varepsilon_s(u) = C(s,t)C(u,s)/N$、階数 1 | 1767/1767（1.7e-13） |
| (4) | $[E_N](u,t) = \varphi(N/t)/N$（どれも 0 でない） | 300/300（2.9e-15） |
| (5) | $P_{s,t}$（積で計算）= 平均を移す作用素（$N\le120$、すべての $s, t$）／$P_{s,t}P_{t',r} = [t = t']P_{s,r}$（$N\le60$ はすべての組、$61\le N\le120$ は乱数の 500 組） | 4038/4038／109623/109623（2.0e-15） |
| (6) | $\sum_sP_{s,s}$ = $R$ への直交射影 = $\frac1{\varphi(N)}\sum_aU_a$、べき等、すべての $E_s$・$D_s$ と可換（$N\le120$） | 120/120（1.4e-14） |
| (7) | $\Phi(MM') = \Phi(M)\Phi(M')$、$\Phi(1) = \sum_sP_{s,s}$、$M\mapsto\Phi(M)$ の階数 $= d(N)^2$、$[\Phi(M)|_R] = M$（$N\le120$、乱数の複素行列） | 120/120（3.5e-14） |
| (8) | $R$ の上の $\langle D_s, E_N\rangle$ の次元 $= d(N)^2$（$N\le300$）／対照 $\langle D_s\rangle$ は $d(N)$／空間全体の $\dim\langle D_s, E_N\rangle = d^2+d-1-[2\mid N]$（$N\le60$） | 300/300／300/300／60/60 |
| (9) | $C = N\varepsilon_t(u)$ = クルイフェルの式 = 直接の和 $c_{N/t}(u)$、$[\mathcal F|_R] = C$、$C^2 = N$、$C[E_s] = [D_s]C$、$C(u,N) = 1$、$C(N,t) = \varphi(N/t)$（$N\le300$） | 300/300（3.7e-11） |
| (10) | 素冪の $C$ の式（$q<50$、$q^k\le2000$、すべての成分） | 877/877（3.2e-11） |
| (11) | $C_{ab}(u_au_b,t_at_b) = C_a(u_a,t_a)C_b(u_b,t_b)$（互いに素、$ab\le300$、すべての成分） | 29477/29477（6.3e-12） |
| (12) | 観察：$\langle D_u|_R, E_s|_R\rangle = M_{d(N)}$ ⇔ $N/s$ が平方因子をもたない（$N\le300$、すべての $s$） | 1767/1767 |

- 実行は 1 回（約 100 秒）で、すべて合格しました。項目ごとの結果を `step262_cache.json` に保存し、コンテナが再起動しても続きから実行できる形にしました（Part 238 の教訓。今回は再起動はありませんでした）。
- **書き方。**
  - 代数の次元は、step259 と同じやり方で数えました（新しく入った基底の塊に生成元を掛け、まとめて SVD）。
  - (6) の単数倍の平均は、すべての単数 $a$ の置換行列 $U_a$ の平均です。
- **(8)・(12) の数値だけの主張の理由（Lean にしていない見通し）。**
  - (8) 空間全体：$\sum_sP_{s,s}$ で $R\oplus R^\perp$ に分かれます。$R$ の上は $M_{d(N)}$、$R^\perp$ の上では $E_N = 0$ です。$D_s$ の制限は、$\#D_s = \varphi(N/s)\ge2$（$N/s\ge3$）のときだけ 0 でない、たがいに直交する射影です。数えると $d^2+d-1-[2\mid N]$ になります。
  - (12)：$[E_s] = C(\cdot,s)C(s,\cdot)/N$ です。$c_q(n) = \mu(q/g)\varphi(q)/\varphi(q/g)$（$g = \gcd(q,n)$）から、成分がすべて 0 でないのは $N/s$ が平方因子をもたないときです。そうでなければ $u = 1$ の行が 0 になり、行列単位 $E_{1t}$（$t\ne1$）が出ません。
- **限界。** (5) の $61\le N\le120$ は乱数で選んだ組だけです。(6)・(8) の空間全体の計算は $N\le120$・$N\le60$ です。

## 3. Lean（`PAG243.lean`、namespace `PAG.Part243`、PAG242 を import）

| 区分 | 項目 |
|---|---|
| 1. 基底 | def `radialCoord`・`radialBasis`, `gcd_val_natCast_of_dvd`, `dind_natCast`, `radial_apply_eq`, `radial_eq_sum`, `dind_mem_base`, `radialBasis_apply`, `radialBasis_repr`, `toMatrix_radialHom` |
| 2. $D_s$・$E_s$ の行列 | `geps_neg`, `dft_dind`, `conv_geps_dind`, `toMatrix_D`, `toMatrix_E`, `geps_self`, `conv_geps_self`, `toMatrix_E_self` |
| 3. 行列単位 | def `shellTrans`・`radialMatOp`・`radialMatHom`・`radialSection`・`diagAvgAlg`, `shellTrans_mem`, `shellTrans_apply`, `sum_dind_mul_dind`, `shellTrans_dind`, `shellTrans_mul`, `toMatrix_shellTrans`, `shellTrans_mul_div`, `radialMatOp_mem`, `radialMatOp_mul`, `radialMatOp_one`, `toMatrix_radialHom_radialMatOp`, `radialMatOp_injective`, `radialMatHom_injective`, `radialHom_radialSection`, `diagAvgAlg_le`, `radialMatOp_mem_diagAvg`, `radialHom_diagAvg_surjective`, `sum_dind_mul_radial`, `shellTrans_self_radial`, `sum_shellTrans_self_radial` |
| 4. $\mathcal F$ の行列 | def `ramMat`・`radialDFT`, `natCast_mul_geps`, `ramMat_apply`, `toMatrix_radialDFT`, `radialDFT_mul_self`, `ramMat_mul_self`, `dft_conv_geps`, `ramMat_mul_toMatrix_E`, `toMatrix_E_eq_ramMat`, `ramMat_apply_col_self`, `ramMat_apply_row_self` |
| 5. 素冪とクロネッカー積 | `sum_divisors_primePow_moebius`, `ramMat_primePow`, `ramMat_mul_coprime` |

**使った PAG の結果**
- Part 16 の `dft_conv`（PAG16）、Part 15 の `conv`・`convL`（PAG15）
- Part 201 の `dind`・`geps`・`dft_geps`・`dind_mul`・`card_dsh`・`geps_apply_zero`（PAG205）
- Part 203 の `Radial`・`exists_unit_mul_gcd`・`dind_radial`・`geps_radial`・`dft_radial`（PAG207）
- Part 214 の `shellAlg`（PAG218）、Part 224 の `refLayer`（PAG228）
- Part 228 の `geps_apply_eq_sum`・`geps_crt`・`convL_geps_mem`・`mulLeft_dind_mem`（PAG232）
- Part 238 の `baseIdx`・`mem_refLayer_base_iff`・`radialHom`・`radialHom_apply`（PAG242）

**Mathlib・Lean から使った主なもの**
- `Module.Basis.ofEquivFun`・`coe_ofEquivFun`・`ofEquivFun_repr_apply`、`LinearMap.toMatrix_apply`・`toMatrix_mul`・`toMatrix_one`、`LinearMap.restrict`、`NonUnitalAlgHom`
- `Matrix.single`・`Matrix.of_apply`・`Matrix.matrix_eq_sum_single`・`Matrix.smul_single`・`Matrix.one_apply`・`Matrix.mul_apply`
- `ZMod.dft_dft`・`ZMod.val_natCast`・`ZMod.natCast_self`・`ZMod.coe_unitOfCoprime`・`ZMod.chineseRemainder`・`map_natCast`
- `Fintype.sum_mul_sum`・`Finset.sum_ite_irrel`・`Finset.sum_ite_eq'`・`Finset.sum_comm`・`Fintype.sum_equiv`・`Equiv.subLeft`・`Finset.sum_boole`・`AddSubmonoidClass.coe_finsetSum`・`Subalgebra.coe_smul`
- `Nat.divisors_prime_pow`・`ArithmeticFunction.moebius_apply_prime_pow`・`moebius_apply_prime`・`moebius_apply_one`・`Nat.pow_div`・`Nat.pow_dvd_pow_iff_le_right`・`Nat.dvd_mod_iff`・`Nat.cast_div`・`Nat.totient_pos`

**コンパイル**
- `PAG243` は 1 回目（約 6 秒）で、エラー・警告なしで通りました。その後、冒頭のコメントの 1 か所（$[E_s]$ の説明の「階数 1」を「列と行の積」に）を直して組み立て直し、もう一度通しました（14 秒、出力は同じ）。公理は標準のもの（propext、Classical.choice、Quot.sound）か、その一部だけです。58 行のうち 1 行（`gcd_val_natCast_of_dvd`）は [propext, Quot.sound] です。
- 内容は試しのファイル T4 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble243.py`）。
- **新しい書き方。**
  - 部分空間の基底は、座標の線形同型から `Module.Basis.ofEquivFun` で作りました。座標写像 $f\mapsto(f(t))_t$ の加法・スカラー倍の保存は `rfl` でした。
  - 非単位的な代数準同型は構造体（`toFun`・`map_smul'`・`map_zero'`・`map_add'`・`map_mul'`）で作りました。`map_smul'` の右辺の `(MonoidHom.id ℂ) c` は `show` で $c$ に書き直せました（定義から等しい）。
  - `Matrix.single` の成分の一般の補題はないので、`rw [Matrix.single, Matrix.of_apply]` で if の形にしてから `split_ifs` を使いました。
- **PAG243 の前の試しのファイル（置き場所は `/home/claude/leanwork/scratch/t239`）。**
  - W0〜W3 は確かめのための小さなファイルです。
    - W0：import の温め（PAG242 を読むだけ）。コンテナの再起動の後でキャッシュが冷えていて、257 秒かかりました。
    - W1・W2：API の名前の確認（W2 で `Subalgebra.coe_sum` がないことがわかり、`AddSubmonoidClass.coe_finsetSum` を使いました）。
    - W3：行列単位の性質だけを仮定した抽象的な例で、二重和の積の展開後のゴールの形を `trace_state` で確かめました（2 回）。
  - T1（36 項目：§1・§2、§3 の行列単位の関係、§4・§5）：1 回目でエラー・警告なしで通りました（11 秒）。
  - T2：行列単位の埋め込み（`radialMatOp`・`radialMatHom`・`radialSection`・`diagAvgAlg` など）を足しました。エラー 1 件、警告 7 件でした。
    - **積を保つことの証明。** $(\sum_s\sum_t a)(\sum_{t'}\sum_r b)$ を `simp only [Finset.sum_mul, Finset.mul_sum]` で展開すると、右の和が外に出て順序が $(t', r, s, t)$ になりました。$[t = t']$ の和を消すはずの `Finset.sum_ite_eq` が当たらず（未使用の simp の引数の警告 5 件）、続く `exact` が whnf の時間切れになりました。Part 234 で記録した注意（`Fintype.sum_mul_sum` なら順序を保つ）を見落としていました。W3 でゴールの形を見て、`Fintype.sum_mul_sum`・`Finset.sum_ite_irrel`・`Finset.sum_ite_eq'` に変えました。
    - 単射性の証明で、使わない λ の変数の警告が 2 件ありました（`fun _ _ h` にしました）。
  - T3：エラー・警告なしで通りました（7 秒）。
  - T4：系 3 つ（`toMatrix_E_eq_ramMat`・`ramMat_apply_col_self`・`ramMat_apply_row_self`）を足して通りました（6 秒）。
- **環境。**
  - Mathlib の追加ビルドはありません。
  - Part 238 の納品（07:36 ごろ）の後、Part 239 の開始時（13:58）にコンテナが再起動していました（起動時刻 13:58:26）。ファイルと .olean は残っていました。

## 4. 残る問い

1. **（次の候補）数値だけの主張を Lean にすること。**
   - $P = \sum_sP_{s,s}$ が $A_N$ の中心のべき等元で、$\frac1{\varphi(N)}\sum_aU_a$（$R$ への直交射影）に等しいこと。さらに $PA_NP = \Phi(M_{d(N)}(\mathbb C))\cong M_{d(N)}(\mathbb C)$ であること（動径のウェダーバーン成分を $A$ の中で切り出す）。
   - $\langle D_u|_R, E_s|_R\rangle = M_{d(N)}$ ⇔ $N/s$ が平方因子をもたないこと（$c_q(n)\ne0$ ⇔ $q/\gcd(q,n)$ が平方因子をもたない）。
   - 空間全体の $\dim\langle D_s, E_N\rangle = d(N)^2+d(N)-1-[2\mid N]$。
2. **クロネッカー積の繰り返し。** $C_N = \bigotimes_{p\mid N}C_{p^{v_p}}$ を、Part 237 の `PiTensorProduct` の形で書くこと（今回は 2 つの因子の成分の等式だけ）。
3. **引き継ぎメモのほかの候補。** dilComm$_{q^k}$ の具体的な形、$A_N$ のウェダーバーン成分の分配の形（Part 238 で数値だけ）、`tensEquiv` と `piTensEquiv` の比較（任意）、1i・1h・1g・1a・1d・1c、法 $p$ の局所の仮定、Ẑ、数論の問い。
