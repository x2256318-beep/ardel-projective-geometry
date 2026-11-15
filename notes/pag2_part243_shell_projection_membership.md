# アデール射影幾何 2.0 — Part 243：どの E_s が ⟨D_u, E_N⟩ に入るか（s ≠ 1 では φ(N/s) = 1 のときだけ、E_1 は N ∈ {1, 4} ∪ 素数 のときだけ）

2026-11-05。引き継ぎメモの次の候補「どの E_s が ⟨D_u, E_N⟩ に入らないか」を Lean で証明しました。Part 242 では、条件の外で入らない E_s が「少なくとも 1 つある」ことを次元から示しただけでした。今回は、どの E_s が入らないかを具体的な証拠の関数で示し、すべての約数 s について判定を完成させました。Part 242 の観察 (4)（数値だけ）は、2 つとも Lean になりました。

- **判定の補題（Lean）。** 殻の平均が 0 の関数（P f = 0）に対して、⟨D_u, E_N⟩ の元 X は殻ごとのスカラーとして働きます。
  - 式で書くと $Xf = \sum_{t\in S′}b_t\cdot1_{D_t}\cdot f$ です（`exists_apply_of_mem_oneEAlg`）。とくに f(z) = 0 なら (Xf)(z) = 0 です（`apply_eq_zero_of_mem_oneEAlg`）。
  - 逆に、A_N の元でこの形に働くものは ⟨D_u, E_N⟩ に入ります。これが ⟨D_u, E_N⟩ の特徴づけです（`mem_oneEAlg_iff`）。
- **証拠（Lean）。** f = δ_1 − δ_{−1} は P f = 0 を満たします（1 と −1 は同じ殻）。
  - s ≠ 1、φ(N/s) ≠ 1 なら、z = 1 + N/s は ±1 と違うので f(z) = 0 です。
  - 一方で $(E_sf)(z) = (\varphi(q) - c_q(2))/N$（q = N/s ≥ 3）です。新しい補題 **c_q(n) = φ(q) ⇔ q ∣ n**（`ramSum_eq_totient_iff`）から、これは 0 ではありません。
  - よって $E_s\notin\langle D_u, E_N\rangle$ です（`convL_geps_not_mem_oneEAlg`）。
- **主定理（Lean）。**
  - **s ∣ N、s ≠ 1 なら $E_s\in\langle D_u, E_N\rangle$ ⇔ φ(N/s) = 1 ⇔ s = N ∨ 2s = N** です（`convL_geps_mem_oneEAlg_iff`・`convL_geps_mem_oneEAlg_iff_eq`）。
  - **$E_1\in\langle D_u, E_N\rangle$ ⇔ N = 1 ∨ N = 4 ∨ N は素数** です（`convL_geps_one_mem_oneEAlg_iff`）。証拠は同じ f と z = 1 + N/p（p = minFac(N)）です。
    - 0 にならないことは、N = p^k M（p ∤ M）としたときの $c_N(N/p) = -p^{k-1}\varphi(M)$ と、$c_N(N/p + 2)$ の大きさの評価で示しました（`ramSum_div_minFac_ne`）。
  - まとめた形は `convL_geps_mem_oneEAlg_iff_all` です。
- **フーリエ双対（Lean）。** Part 242 の共役で写すと、$D_s\in\langle E_u, D_N\rangle$ も同じ条件になります（`mulLeft_dind_mem_dualOneEAlg_iff`、`mulLeft_dind_one_mem_dualOneEAlg_iff`）。
- **限界（正直な注記）。**
  - $(E_sf)(z)$ の値の式 $(\varphi(q) - c_q(2))/N$ は、証明の中で使いましたが、定理としては「0 でない」ことだけを述べています。値そのものは数値で確かめました（304/304）。
  - 特徴づけの空間の次元が G(N) = dim ⟨D_u, E_N⟩ に一致することは、この形では数値だけです（36/36、N ≤ 36）。`mem_oneEAlg_iff` と Part 241 の次元から従います。
  - `step266.log` では項目 (7)（$E_1$ の判定）を「観察（数値だけ）」と書いています。数値照合を先に書いたためで、今回 Lean になりました。ログは書き直していません。
- **やり直し。**
  - 試しのファイル T1 は 1 回目にエラー 1 件、T2 は 1 回目にエラー 2 件で、どちらも直して 2 回目で通りました（§3）。
  - PAG247 は 1 回目のコンパイルで通りました。数値照合は 1 回の実行ですべて合格しました。
- **環境。** Mathlib の追加ビルドはありません。Part 243 の開始時（20:15）にコンテナが再起動していて、import の温めに 220 秒かかりました。

成果物は次のとおりです。
- `PAG247.lean`：27 項目。sorry 0・警告 0 です。
  - 定義 1 個（`testFn`）は項目に数えません。
  - 出力は `PAG247.out`（#print axioms 28 行）。
- 照合用の `step266.py`：ログは `step266.log` です。

xlsx の集計は 3094 項目になりました（手順 263）。

## 0. 結論

**記号**（Part 239〜242 と同じ）
- $D_t = \{x : \gcd(N,x) = t\}$、$1_{D_t}$ = `dind N t`、$\varepsilon_s = \mathcal F^{-1}1_{D_s}$、$E_sf = \varepsilon_s\star f$、$D_sf = 1_{D_s}f$。
- $A_N$ = `shellAlg N`。⟨D_u, E_N⟩ = `oneEAlg N N`。⟨E_u, D_N⟩ = `dualOneEAlg N`。
- P = `shellAvg N`（殻の平均）、$P_{u,v}$ = `shellTrans N u v`、$\Phi(M) = \sum M_{uv}P_{u,v}$、$Q_t = D_t - P_{t,t}$ = `shellDev N t`。
- $S′ = \{t\mid N : \varphi(N/t)\ne1\}$ = `devSet N`。⟨D_u, E_N⟩ の元は $\Psi(M, b) = \Phi(M) + \sum_{t\in S′}b_tQ_t$ と書けます（Part 241）。
- $c_q(n)$ = `ramSum n q`（ラマヌジャン和）。$N\cdot\varepsilon_s(u) = c_{N/s}(u)$（Part 240）。

| 定理 | 主張 |
|---|---|
| **`ramSum_eq_totient_iff`** | c_q(n) = φ(q) ⇔ q ∣ n（q ≠ 0） |
| `sum_dind_mul_eq_zero`, `radialMatOp_apply_eq_zero`, `shellDev_apply_of_shellAvg_eq_zero` | P f = 0 なら各殻の上の和は 0、Φ(M) f = 0、$Q_tf = 1_{D_t}f$ |
| **`exists_apply_of_mem_oneEAlg`**, **`apply_eq_zero_of_mem_oneEAlg`** | X ∈ ⟨D_u, E_N⟩ なら、P f = 0 の f に $Xf = \sum_{t\in S′}b_t1_{D_t}f$。とくに f(z) = 0 ⇒ (Xf)(z) = 0 |
| `mulLeft_dind_mul_shellAvg`, **`mem_oneEAlg_iff`** | $D_tP = P_{t,t}$。特徴づけ：X ∈ ⟨D_u, E_N⟩ ⇔ X ∈ A_N かつ P f = 0 の f に殻ごとのスカラーとして働く |
| `sum_mul_single`, `shellAvg_testFn`, `conv_single_apply`, `conv_geps_testFn_apply` | f = δ_1 − δ_{−1}（def `testFn`）で P f = 0、$(E_sf)(z) = \varepsilon_s(z-1) - \varepsilon_s(z+1)$ |
| `three_le_div`, `conv_geps_testFn_ne_zero`, `testFn_apply_eq_zero` | s ≠ 1、φ(N/s) ≠ 1 なら N/s ≥ 3、z = 1 + N/s で f(z) = 0 かつ $(E_sf)(z)\ne0$ |
| **`convL_geps_not_mem_oneEAlg`** | s ≠ 1、φ(N/s) ≠ 1 なら $E_s\notin\langle D_u, E_N\rangle$ |
| **`convL_geps_mem_oneEAlg_iff`**, `convL_geps_mem_oneEAlg_iff_eq` | s ≠ 1 なら $E_s\in\langle D_u, E_N\rangle$ ⇔ φ(N/s) = 1 ⇔ s = N ∨ 2s = N |
| **`mulLeft_dind_mem_dualOneEAlg_iff`** | s ≠ 1 なら $D_s\in\langle E_u, D_N\rangle$ ⇔ φ(N/s) = 1 |
| `abs_ramSum_primePow_le`, `ramSum_mul_eq`, `ramSum_mul_add_two`, **`ramSum_div_minFac_ne`** | $\lvert c_{p^k}(n)\rvert\le p^k - p^{k-1}$、$c_{p^kM}(p^{k-1}M) = -p^{k-1}\varphi(M)$、$c_{p^kM}(p^{k-1}M + 2) = c_{p^k}(\cdot)c_M(2)$、N ∉ {1, 4} ∪ 素数 なら $c_N(N/p)\ne c_N(N/p + 2)$ |
| **`convL_geps_one_not_mem_oneEAlg`**, **`convL_geps_one_mem_oneEAlg_iff`** | N ∉ {1, 4} ∪ 素数 なら $E_1\notin\langle D_u, E_N\rangle$。$E_1\in\langle D_u, E_N\rangle$ ⇔ N = 1 ∨ N = 4 ∨ N は素数 |
| `convL_geps_mem_oneEAlg_iff_all`, `mulLeft_dind_one_mem_dualOneEAlg_iff` | まとめ：$E_s\in\langle D_u, E_N\rangle$ ⇔ (s ≠ 1 ∧ φ(N/s) = 1) ∨ (s = 1 ∧ N ∈ {1, 4} ∪ 素数)。$D_1\in\langle E_u, D_N\rangle$ ⇔ N ∈ {1, 4} ∪ 素数 |

**証明の筋**
1. **c_q(n) = φ(q) ⇔ q ∣ n。**
   - Part 241 の $c_q(n)\varphi(q/(q,n)) = \mu(q/(q,n))\varphi(q)$ に $c_q(n) = \varphi(q)$ を入れると、$\varphi(q/(q,n)) = \mu(q/(q,n))$ です。
   - φ ≥ 1 と |μ| ≤ 1 から両辺は 1 です。φ(m) = 1 は m = 1, 2 で、m = 2 は μ(2) = −1 なので除かれます。よって q/(q, n) = 1、つまり q ∣ n です。
2. **判定の補題。**
   - P f = 0 なら、各殻の上の和が 0 です（$(Pf)(t) = \sum_{D_t}f/\varphi(N/t)$）。
   - Φ(M) は殻の上の和しか見ないので Φ(M) f = 0、$Q_tf = 1_{D_t}f - P_{t,t}f = 1_{D_t}f$ です。
   - X = Ψ(M, b)（Part 241 の `range_wholeHom`）に当てはめると $Xf = \sum_tb_t1_{D_t}f$ です。
   - 逆向き：X ∈ A_N を X = XP + X(1 − P) と分けます。XP = Φ([X])（Part 240）です。(1 − P)g は P(1 − P)g = 0 を満たすので、仮定から $X(1-P)g = \sum_tb_t1_{D_t}(1-P)g$ です。$D_tP = P_{t,t}$ から、これは $\sum_tb_tQ_tg$ に等しく、X = Ψ([X], b) です。
3. **証拠（s ≠ 1）。**
   - 1 と −1 は同じ殻なので P(δ_1 − δ_{−1}) = 0 です（$1_{D_s}$ は動径関数）。
   - $(E_sf)(z) = \varepsilon_s(z-1) - \varepsilon_s(z+1)$ で、z = 1 + q（q = N/s）では $N(E_sf)(z) = c_q(q) - c_q(q+2) = \varphi(q) - c_q(2)$ です。
   - q ≥ 3 なので q ∤ 2 で、1 の補題から $c_q(2)\ne\varphi(q)$ です。
   - z ≢ ±1：z ≡ 1 なら N ∣ q（0 < q < N に反する）、z ≡ −1 なら N ∣ q + 2 で、q ∣ N から q ∣ 2（q ≥ 3 に反する）です。
4. **$E_1$。** N ∉ {1, 4} ∪ 素数 とし、p = minFac(N)、N = p^k M（p ∤ M、Mathlib の `Nat.ordProj_mul_ordCompl_eq_self`）と書きます。
   - $N/p = p^{k-1}M$ で、$c_N(N/p) = c_{p^k}(p^{k-1}M)\,c_M(p^{k-1}M) = -p^{k-1}\varphi(M)$ です（c は q について乗法的）。
   - M = 1 のとき：N が素数でないので k ≥ 2、N ≠ 4 なので $p^{k-1}\ge3$ です。$p^{k-1}\nmid p^{k-1} + 2$ なので $c_{p^k}(p^{k-1} + 2) = 0\ne-p^{k-1}$ です。
   - M > 1 のとき：M の素因数はどれも p より大きいので M は奇数で、$c_M(2) = \mu(M)$、$\lvert c_M(2)\rvert\le1$ です。φ(M) ≥ φ(minFac M) = minFac M − 1 ≥ p なので、$\lvert c_N(N/p + 2)\rvert\le p^k - p^{k-1} < p^k\le p^{k-1}\varphi(M) = \lvert c_N(N/p)\rvert$ です。
   - z = 1 + N/p は ±1 と違います（N ≥ 6 で 2·(N/p) ≤ N）。3 と同じ議論で $E_1\notin\langle D_u, E_N\rangle$ です。
   - 逆に N ∈ {1, 4} ∪ 素数 なら、Part 242 の主定理で A_N = ⟨D_u, E_N⟩ なので $E_1$ も入ります。
5. **フーリエ双対。** $\mathcal FE_s\mathcal F^{-1} = D_s$、$\mathcal F\langle D_u, E_N\rangle\mathcal F^{-1} = \langle E_u, D_N\rangle$（Part 242）で、共役は単射なので所属の条件がそのまま移ります（`Subalgebra.mem_map`）。

**例**
- 証拠の値 $(E_sf)(1 + N/s) = (\varphi(q) - c_q(2))/N$（数値で確認）：N = 6, s = 2 で (2 − (−1))/6 = 1/2、N = 8, s = 2 で (2 − (−2))/8 = 1/2、N = 9, s = 3 で (2 − (−1))/9 = 1/3、N = 10, s = 2 で (4 − (−1))/10 = 1/2。
- $E_1$ の証拠（step266.py の関数で個別に計算して確認。ログには入っていません）：
  - N = 6（p = 2, M = 3）では $c_6(3) = -2$、$c_6(5) = 1$ で、$(E_1f)(4) = -1/2$ です。
  - N = 9（M = 1）では $c_9(3) = -3$、$c_9(5) = 0$ で、$(E_1f)(4) = -1/3$ です。
  - N = 8（M = 1）では $c_8(4) = -4$、$c_8(6) = 0$ で、$(E_1f)(5) = -1/2$ です。
  - N = 12（p = 2, k = 2, M = 3）では $c_{12}(6) = -4$、$c_{12}(8) = -2$ で、$(E_1f)(7) = -1/6$ です。
- 除外される N = 4：z = 1 + 2 = 3 ≡ −1 なので、この証拠は使えません。実際、$E_1 = 1 - E_2 - E_4\in\langle D_u, E_4\rangle$ です（Part 242）。
- 入る E_s の一覧：s = N（φ(1) = 1）は常に入り、s = N/2 は N が偶数のとき入ります。s = 1 は N ∈ {1, 4} ∪ 素数 のときだけです。それ以外の約数の $E_s$ は入りません。たとえば N = 12 では、約数 1, 2, 3, 4, 6, 12 のうち $E_6$・$E_{12}$ だけが入ります。

**読み取れること**
- ⟨D_u, E_N⟩ の元は、殻の平均が 0 の関数の台を広げません（殻ごとのスカラー倍だけ）。$E_s$ は畳み込みなので、ふつうは台を広げます。広げないのは、$E_s$ の像が動径関数になる場合（φ(N/s) = 1）だけです。
- Part 242 の次元による議論では、入らない $E_s$ があることしかわかりませんでした。この判定の補題を使うと、具体的な関数と点で所属を否定できます。
- Part 242 の主定理と合わせると、**$E_1\in\langle D_u, E_N\rangle$ ⇔ A_N = ⟨D_u, E_N⟩** です（右辺の条件が同じ。この同値は定理としては述べていません）。$E_1$ が入るかどうかだけで、A_N 全体が出るかが決まります。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| c_q(n) = φ(q) ⇔ q ∣ n（q ≠ 0） | **正しい（`ramSum_eq_totient_iff`）**。数値でも 1001000/1001000（q ≤ 1000、0 ≤ n < 2q） |
| X ∈ ⟨D_u, E_N⟩ なら、P f = 0 の f に $Xf = \sum_{t\in S′}b_t1_{D_t}f$ | **正しい（`exists_apply_of_mem_oneEAlg`）**。数値でも 180/180 |
| X ∈ ⟨D_u, E_N⟩ ⇔ X ∈ A_N かつ P f = 0 の f に殻ごとのスカラーとして働く | **正しい（`mem_oneEAlg_iff`）** |
| 上の特徴づけの空間の次元 = G(N) = dim ⟨D_u, E_N⟩ | **数値だけ**（36/36、N ≤ 36）。`mem_oneEAlg_iff` と Part 241 の `finrank_oneEAlg_self_add` から従うが、この形では述べていない |
| f = δ_1 − δ_{−1}、z = 1 + N/s（s ≠ 1、φ(N/s) ≠ 1）で P f = 0、f(z) = 0、$(E_sf)(z)\ne0$ | **正しい（`shellAvg_testFn`、`testFn_apply_eq_zero`、`conv_geps_testFn_ne_zero`）**。数値でも 304/304 |
| その値は $(\varphi(q) - c_q(2))/N$（q = N/s） | **数値だけ**（304/304、最大誤差 8.3e-15）。証明の中では使うが、定理としては「0 でない」だけ |
| s ≠ 1 で $E_s\in\langle D_u, E_N\rangle$ ⇔ φ(N/s) = 1 ⇔ s = N ∨ 2s = N | **正しい（`convL_geps_mem_oneEAlg_iff`、`convL_geps_mem_oneEAlg_iff_eq`）**。数値でも 201/201（Part 242 では ⇒ が数値だけ） |
| $E_1\in\langle D_u, E_N\rangle$ ⇔ N ∈ {1, 4} ∪ 素数 | **正しい（`convL_geps_one_mem_oneEAlg_iff`）**。数値でも 60/60（Part 242 では ⇒ が数値だけ） |
| N ∉ {1, 4} ∪ 素数 では z = 1 + N/minFac(N) が $E_1$ の証拠になる | **正しい（`ramSum_div_minFac_ne`、`convL_geps_one_not_mem_oneEAlg`）**。数値でも 88/88（N ≤ 120） |
| フーリエ双対：$D_s\in\langle E_u, D_N\rangle$ ⇔ φ(N/s) = 1（s ≠ 1）、$D_1$ は N ∈ {1, 4} ∪ 素数 のとき | **正しい（`mulLeft_dind_mem_dualOneEAlg_iff`、`mulLeft_dind_one_mem_dualOneEAlg_iff`）**。数値でも s ≠ 1 の場合 118/118（N ≤ 40） |
| $E_1\in\langle D_u, E_N\rangle$ ⇔ A_N = ⟨D_u, E_N⟩ | 2 つの Lean の定理（今回の `convL_geps_one_mem_oneEAlg_iff` と Part 242 の `shellAlg_eq_oneEAlg_iff`）の右辺が同じことから従う。この形の定理はない |

## 2. 数値照合（step266）

| 項目 | 内容 | 結果 |
|---|---|---|
| (1) | 証拠 f = δ_1 − δ_{−1}、z = 1 + N/s（3 ≤ N ≤ 120、s ≠ 1、φ(N/s) ≠ 1 のすべての s）：P f = 0、f(z) = 0、$(E_sf)(z) = (\varphi(q) - c_q(2))/N\ne0$ | 304/304（8.3e-15） |
| (2) | s ≠ 1 で $E_s\in\langle D_u, E_N\rangle$ ⇔ φ(N/s) = 1 ⇔ s ∈ {N, N/2}（N ≤ 60。所属は Part 241 の基底 $P_{s,t}$・$Q_t$ の張る空間で判定） | 201/201 |
| (3) | 判定の補題：ランダムな Ψ(M, b) と P f = 0 のランダムな f で $Xf = \sum_tb_t1_{D_t}f$（N ≤ 60、各 3 回） | 180/180（2.7e-15） |
| (4) | c_q(n) = φ(q) ⇔ q ∣ n（q ≤ 1000、0 ≤ n < 2q） | 1001000/1001000 |
| (5) | 特徴づけの空間（A_N の元で、P f = 0 の f に殻ごとのスカラーとして働くもの）の次元 = G(N)（N ≤ 36、A_N は生成元から直交化で計算） | 36/36 |
| (6) | フーリエ双対：s ≠ 1 で $D_s\in\langle E_u, D_N\rangle$ ⇔ φ(N/s) = 1（N ≤ 40） | 118/118 |
| (7) | $E_1\in\langle D_u, E_N\rangle$ ⇔ N ∈ {1, 4} ∪ 素数（N ≤ 60）／z = 1 + N/minFac(N) が $E_1$ の証拠になる（3 ≤ N ≤ 120 で条件の外のすべての N） | 60/60／88/88（ならない N はなし） |

- **実行は 1 回です**（11.2 秒、項目ごとの結果は `step266_cache.json`）。すべて合格しました。
- 次元の例（(5)）：N = 4 で 10、6 で 18、8 で 18、12 で 40、30 で 70、36 で 88。どれも G(N) = d² + d − 1 − [2 ∣ N] です。
- ログでは (7) を「観察（数値だけ）」と書きました。照合を書いた時点では $E_1$ の節を Lean にする予定がなかったためで、今回 Lean になりました（§1）。
- **限界。**
  - (2)・(7) の所属の判定は、Part 241 の基底 $P_{s,t}$・$Q_t$ の張る空間への射影の残差（< 1e-8）によります（基底が ⟨D_u, E_N⟩ を張ることは Part 241 の Lean の定理）。生成元から直交化で計算したのは (5) の A_N（N ≤ 36）だけです。
  - (6) は N ≤ 40、(5) は N ≤ 36 です。

## 3. Lean（`PAG247.lean`、namespace `PAG.Part247`、PAG246 を import）

| 区分 | 項目 |
|---|---|
| 1. c_q(n) = φ(q) の条件 | `ramSum_eq_totient_iff` |
| 2. 判定の補題と特徴づけ | `sum_dind_mul_eq_zero`, `radialMatOp_apply_eq_zero`, `shellDev_apply_of_shellAvg_eq_zero`, `exists_apply_of_mem_oneEAlg`, `apply_eq_zero_of_mem_oneEAlg`, `mulLeft_dind_mul_shellAvg`, `mem_oneEAlg_iff` |
| 3. 証拠の関数（s ≠ 1） | def `testFn`, `sum_mul_single`, `shellAvg_testFn`, `conv_single_apply`, `conv_geps_testFn_apply`, `three_le_div`, `conv_geps_testFn_ne_zero`, `testFn_apply_eq_zero`, `convL_geps_not_mem_oneEAlg` |
| 4. s ≠ 1 の判定と双対 | `convL_geps_mem_oneEAlg_iff`, `convL_geps_mem_oneEAlg_iff_eq`, `mulLeft_dind_mem_dualOneEAlg_iff` |
| 5. E_1 | `abs_ramSum_primePow_le`, `ramSum_mul_eq`, `ramSum_mul_add_two`, `ramSum_div_minFac_ne`, `convL_geps_one_not_mem_oneEAlg`, `convL_geps_one_mem_oneEAlg_iff`, `convL_geps_mem_oneEAlg_iff_all`, `mulLeft_dind_one_mem_dualOneEAlg_iff` |

**使った PAG の結果**
- Part 15 の `conv`・`convL`（PAG15）
- Part 201 の `dind`・`geps`（PAG205）、Part 203 の `gcd_natCast_self`・`dind_radial`（PAG207）
- Part 214 の `shellAlg`（PAG218）、Part 228 の `convL_geps_mem`（PAG232）
- Part 238 の `radialHom`（PAG242）、Part 239 の `radialBasis`・`radialMatOp`・`shellTrans_apply`（PAG243）
- Part 240 の `shellAvg`・`shellAvg_apply`・`shellAvg_mul_self`・`mul_shellAvg_eq`・`oneEAlg`・`oneEAlg_le`・`ramSum`・`isMultiplicative_ramSum`・`ramSum_primePow`・`natCast_mul_geps_eq_ramSum`（PAG244）
- Part 241 の `ramSum_mul_totient`・`ramSum_of_dvd`・`ramSum_mod`・`ramSum_of_coprime`・`div_gcd_pos`・`shellDev`・`shellDev_apply`・`devSet`・`dvd_of_mem_devSet`・`mulLeft_dind_mul_shellTrans`・`wholeMap`・`wholeHom`・`range_wholeHom`（PAG245）
- Part 242 の `convL_geps_mem_oneEAlg`・`shellAlg_eq_oneEAlg_iff`・`fourierConj`・`fourierConj_convL_geps`・`dualOneEAlg`・`map_fourierConj_oneEAlg`（PAG246）

**Mathlib・Lean から使った主なもの**
- 自然数：`Nat.totient_eq_one_iff`・`Nat.totient_pos`・`Nat.totient_prime`・`Nat.totient_dvd_of_dvd`・`Nat.eq_of_dvd_of_div_eq_one`・`Nat.minFac_prime`・`Nat.minFac_dvd`・`Nat.minFac_le`・`Nat.minFac_le_of_dvd`・`Nat.ordProj_mul_ordCompl_eq_self`・`Nat.not_dvd_ordCompl`・`Nat.ordCompl_dvd`・`Nat.ordCompl_pos`・`Nat.Prime.factorization_pos_of_dvd`・`Nat.Prime.coprime_iff_not_dvd`・`Nat.Coprime.pow_left`・`Nat.dvd_of_mul_dvd_mul_left`・`Nat.div_le_div_left`・`Nat.div_lt_self`・`Nat.mul_add_mod'`・`Nat.add_mod_left`・`Nat.pow_dvd_pow`・`Nat.pow_le_pow_right`
- 数論関数：`ArithmeticFunction.abs_moebius_le_one`・`ArithmeticFunction.moebius_apply_prime`・`ArithmeticFunction.IsMultiplicative.map_mul_of_coprime`
- 剰余環・和・部分代数：`ZMod.natCast_eq_zero_iff`・`Pi.single_eq_same`・`Pi.single_eq_of_ne`・`Finset.sum_eq_single`・`Finset.sum_ite_eq`・`AlgHom.mem_range`・`Subalgebra.mem_map`・`LinearMap.ext`

**コンパイル**
- `PAG247` は 1 回目のコンパイル（約 14 秒）でエラー・警告なしで通りました。
- 公理は標準のもの（propext、Classical.choice、Quot.sound）だけです（28 行、どれも 3 つすべて）。
- 内容は試しのファイル T2 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble247.py`）。
- **試しのファイル（置き場所は `/home/claude/leanwork/scratch/t243`）。**
  - W0：import の温めと API の名前の確認（220 秒、キャッシュが冷えていた）。`ZMod.natCast_zmod_eq_zero_iff_dvd`・`ZMod.natCast_self_eq_zero`・`Subalgebra.mem_map_equiv` はこの Mathlib になく、`ZMod.natCast_eq_zero_iff`・`Subalgebra.mem_map` を使いました。
  - T1（§1〜4、19 項目と定義 1 個）：1 回目にエラー 1 件です。4b で `rw [mul_comm s 2] at h` と書きましたが、h にあるのは `2 * s` で、`s * 2` を探す書き換えは当たりませんでした（向きの取り違え）。`have : s * k = s * 2 := by rw [← h, mul_comm]` に直して、2 回目で通りました（4 秒）。
  - W1：§5 の API の名前の確認（2 秒）。
  - T2（§5 の $E_1$ を足した 27 項目と定義 1 個）：1 回目にエラー 2 件です。
    - 5d の M = 1 の場合で、2 つの `if`（条件は $p^k\mid\cdot$ と $p^{k-1}\mid\cdot$）に `ite_eq_right hnd'` を 2 回書きました。2 つ目は `hnd` が正しい仮定です。
    - 5d の M > 1 の場合で、`positivity` が $(p : ℤ)^{k-1} > 0$ を示せませんでした（「非負なら示せる」というエラー）。同じ形の 5a では通っていました。
    - どちらも直して、2 回目で通りました（6 秒）。`hpos` は 2 か所とも `pow_pos (by exact_mod_cast hp.pos) _` にしました。
  - W2：`positivity` の確認（9 秒）。文脈に `hp2 : (2 : ℤ) ≤ p` があれば通り、`hp : p.Prime` だけでは通りませんでした。5a では `hp2` が先に置いてあったので通っていたことになります。
- 前回の注意を当てはめた箇所があります。
  - N に依存する式（minFac(N)、N の p 進付値、N/p^k）は、`generalize N.minFac = p at …` などで変数にしてから場合分けしました（Part 242 の注意）。
  - `Pi.single` は `(Pi.single a (1 : ℂ) : ZMod N → ℂ) y` と型を書きました（Part 241 の注意）。
  - `if` の書き換えは、非推奨の `if_pos`・`if_neg` ではなく `ite_eq_left`・`ite_eq_right` で行いました。
- **環境。** Mathlib の追加ビルドはありません。Part 242 の納品（17:57 ごろ）の後、Part 243 の開始時（20:15）にコンテナが再起動していました（起動時刻 20:15:49）。ファイルと .olean は残っていて、最初の import は 220 秒でした（キャッシュが冷えていた）。

## 4. 残る問い

1. **（次の候補）双対との共通部分 ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩。**
   - どちらの代数も、動径関数の部分では Φ(M) の形の作用をすべてもつと思われます（未確認）。違いは、殻の平均が 0 の関数の上での作用です。⟨D_u, E_N⟩ では $1_{D_t}$ の 1 次結合、⟨E_u, D_N⟩ では $E_t$ の 1 次結合になります。
   - そのため、共通部分は「殻の平均が 0 の関数の上で、$1_{D_t}$ の 1 次結合でもあり $E_t$ の 1 次結合でもある作用」で決まりそうです。N = 6 では恒等写像だけ、N = 8 では $\delta_2 - \delta_6$ が両方の固有ベクトルになるなど、N によって違いそうです（手計算の見込みで、数値では確かめていません）。
   - まず数値で次元を求め、形を予想するところから始めます。
2. **1 つ足したときの代数。** s ∈ S′ の $E_s$ を 1 つ足した ⟨D_u, E_N, E_s⟩ の次元と構造です。どの s で A_N 全体が出るかも問えます。
3. **次元の差の閉じた形。** 素因数 2 つ以上のときの dim A_N − dim ⟨D_u, E_N⟩ を、単数群の指標（Part 225 の n_p）の言葉で書くことです。
4. **ほかの殻の組み合わせ。** ⟨D_u, E_s⟩（Part 240）の空間全体の構造と次元を、s ≠ N でも求めることです（Part 241 は s = N）。
5. **引き継ぎメモのほかの候補。** $C_N = \bigotimes_pC_{p^{v_p}}$ の PiTensorProduct の形、dilComm$_{q^k}$、$A_N$ のウェダーバーン成分の分配の形、中心そのものの finrank、P・Q_s の自己共役、ほか。
