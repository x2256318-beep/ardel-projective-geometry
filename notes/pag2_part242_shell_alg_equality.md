# アデール射影幾何 2.0 — Part 242：A_N = ⟨D_u, E_N⟩ ⇔ N ∈ {1, 4} ∪ 素数（殻の射影と定数への射影だけで A_N 全体が出る条件）

2026-11-05。引き継ぎメモの次の候補を Lean で証明しました。候補は、A_N と ⟨D_s, E_N⟩ がいつ一致するかで、Part 241 の観察 (8) では数値だけ（N ≤ 40）でした。フーリエ変換による双対の形も足しました（§0 の 5）。

- **主定理（Lean）。** **A_N = ⟨D_u, E_N⟩ ⇔ N = 1 ∨ N = 4 ∨ N は素数**（`shellAlg_eq_oneEAlg_iff`）。
  - **⇐ は構造から。** φ(N/s) = 1（s = N、N/2）なら殻 $D_s$ は 1 点で、$E_s$ の像は動径関数です。$\mathcal F(E_sf) = 1_{D_s}\cdot\mathcal Ff$ で、1 点の殻の指示関数を掛けたものは動径関数になるためです。
    - よって $E_s = \Phi([E_s])\in\langle D_u, E_N\rangle$ です（`convL_geps_mem_oneEAlg`）。
    - 1 でない約数がすべてこの形なら、$E_1 = 1 - \sum_{s\ne1}E_s$ も入り、A_N ⊆ ⟨D_u, E_N⟩ です。
    - 「1 でない約数 s ではどれも φ(N/s) = 1」は N ∈ {1, 4} ∪ 素数 と同じです（`forall_totient_eq_one_iff`）。
  - **⇒ は次元から。** Part 226 の $\dim A_N = \prod_{p^k\parallel N}((k+1)^2 + k(k+1)/2 - [p = 2]k)$ と、Part 241 の $\dim\langle D_u, E_N\rangle = d(N)^2 + d(N) - 1 - [2\mid N]$ を比べます。
    - 素冪では差がちょうど $k(k-1)/2$（p 奇数）・$(k-1)(k-2)/2$（p = 2）です（`finrank_shellAlg_primePow_odd`・`finrank_shellAlg_two_pow`）。
    - 素因数が 2 つ以上なら N = ab（a は奇数、a, b > 1、互いに素）と分けます。dim A の乗法性と、包含 ⟨D_u, E_N⟩ ⊆ A_N からの下からの評価で、真に小さいことを示しました（`finrank_lt_of_eq_mul`）。
  - **系。**
    - 式だけの形：$\prod((k+1)^2 + k(k+1)/2 - [p = 2]k) = d^2 + d - 1 - [2\mid N]$ ⇔ 同じ条件（`prod_eq_iff`）。
    - この条件のもとで $A_N\cong M_{d(N)}(\mathbb C)\times\mathbb C^{S′}$（`shellAlgEquivOfMem`）。
    - 条件の外では、1 でない約数 s で φ(N/s) ≠ 1 かつ $E_s\notin\langle D_u, E_N\rangle$ となるものがあります（`exists_convL_geps_not_mem`）。たとえば N = 6・8 では s = 2、N = 9 では s = 3 に決まります。
- **フーリエ双対（Lean）。**
  - $\mathrm{conv}(\mathcal Ff, \mathcal Fg) = N\cdot\mathcal F(fg)$ です（`conv_dft_dft`）。
  - 𝓕 による共役（`fourierConj`）で $E_s$ と $D_s$ が入れ替わります。そのため $\mathcal FA_N\mathcal F^{-1} = A_N$、$\mathcal F\langle D_u, E_N\rangle\mathcal F^{-1} = \langle E_u, D_N\rangle$ です（`dualOneEAlg`）。
  - **$A_N = \langle E_u, D_N\rangle$ も同じ条件**で成り立ちます（`shellAlg_eq_dualOneEAlg_iff`）。
- **限界（正直な注記）。**
  - ⇒ の証明は次元によるもので、どの $E_s$ が入らないかは「少なくとも 1 つある」という形でしか示していません。
  - 観察「s ≠ 1 で $E_s\in\langle D_u, E_N\rangle$ ⇔ φ(N/s) = 1」は、⇐ だけが Lean です。⇒ は数値だけです（201/201、N ≤ 60）。
  - 素因数が 2 つ以上のときの次元の差は、Lean では 1 以上であることだけを示しました。具体的な値は 2 つの式から計算できます（例：N = 6 で 2、N = 12 で 10、N = 30 で 30、N = 60 で 96）。
- **やり直し。** 試しのファイル T1〜T3 は、どれもエラー・警告なしで通りました。PAG246 は 2 回コンパイルしました（2 回目はフーリエ双対の節を足したもの）。数値照合も、フーリエ双対の項目を足して 2 回実行しました（§2）。
- **環境。** Mathlib の追加ビルドはありません。Part 242 の開始時（17:35）にコンテナが再起動していて、import の温めに 232 秒かかりました。

成果物は次のとおりです。
- `PAG246.lean`：34 項目。sorry 0・警告 0 です。
  - 定義 3 個は項目に数えません。
  - 出力は `PAG246.out`（#print axioms 37 行）。
- 照合用の `step265.py`：ログは `step265.log` です。

xlsx の集計は 3067 項目になりました（手順 262）。

## 0. 結論

**記号**（Part 239〜241 と同じ）
- $D_t = \{x : \gcd(N,x) = t\}$、$1_{D_t}$ = `dind N t`、$\varepsilon_s = \mathcal F^{-1}1_{D_s}$、$E_sf = \varepsilon_s\star f$、$D_sf = 1_{D_s}f$。
- $A_N$ = `shellAlg N`（すべての $D_s$・$E_s$ が生成）。⟨D_u, E_N⟩ = `oneEAlg N N`。⟨E_u, D_N⟩ = `dualOneEAlg N`。
- $\Phi(M) = \sum M_{st}P_{s,t}$、$[T](u,t) = (T1_{D_t})(u)$（Part 239）。$S′ = \{s\mid N : \varphi(N/s)\ne1\}$（Part 241）。
- F(N) = Π_{p^k ∥ N}((k+1)² + k(k+1)/2 − [p = 2]k)（Part 226 の dim A_N）、G(N) = d(N)² + d(N) − 1 − [2 ∣ N]（Part 241 の dim ⟨D_u, E_N⟩）。

| 定理 | 主張 |
|---|---|
| `eq_of_gcd_eq`, `radial_dind_mul`, `radial_conv_geps` | φ(N/s) = 1 なら $D_s$ は 1 点、$1_{D_s}g$ は動径関数、$E_sf$ は動径関数 |
| `convL_geps_eq_radialMatOp`, **`convL_geps_mem_oneEAlg`**, `convL_geps_half_mem_oneEAlg` | φ(N/s) = 1 なら $E_s = \Phi([E_s])\in\langle D_u, E_N\rangle$。N が偶数なら $E_{N/2}$ も入る |
| `shellAlg_le_oneEAlg_of_forall_mem`, `shellAlg_eq_oneEAlg_of_forall` | 1 でない約数の $E_s$ がすべて入れば A_N ⊆ ⟨D_u, E_N⟩。1 でない約数ですべて φ(N/s) = 1 なら A_N = ⟨D_u, E_N⟩ |
| **`forall_totient_eq_one_iff`** | 1 でない約数 s ですべて φ(N/s) = 1 ⇔ N = 1 ∨ N = 4 ∨ N は素数 |
| `finrank_oneEAlg_le`, `card_divisors_primePow`, `finrank_shellAlg_primePow`, `two_dvd_primePow_iff`, `finrank_oneEAlg_primePow_add`, `half_mul_succ` | dim ⟨D_u, E_N⟩ ≤ dim A_N、d(p^k) = k + 1、dim A_{p^k} の式、dim ⟨D_u, E_{p^k}⟩ の式 |
| **`finrank_shellAlg_primePow_odd`**, **`finrank_shellAlg_two_pow`** | dim A_{p^k} = dim ⟨D_u, E_{p^k}⟩ + k(k−1)/2（p 奇数）、+ (k−1)(k−2)/2（p = 2） |
| `finrank_lt_of_eq_primePow_odd`, `finrank_lt_of_eq_two_pow`, `finrank_lt_of_eq_mul`, **`finrank_oneEAlg_lt_shellAlg`** | N ∉ {1, 4} ∪ 素数 なら dim ⟨D_u, E_N⟩ < dim A_N |
| **`shellAlg_eq_oneEAlg_iff`**, `shellAlg_eq_oneEAlg_iff_forall`, `finrank_shellAlg_eq_iff`, **`prod_eq_iff`** | 主定理とその言い換え（条件・次元・式の形） |
| `shellAlgEquivOfMem_apply`, `exists_convL_geps_not_mem` | 条件のもとで $A_N\cong M_{d(N)}(\mathbb C)\times\mathbb C^{S′}$。条件の外では $E_s\notin\langle D_u, E_N\rangle$ となる s ≠ 1 がある |
| `conv_dft_dft`, `fourierConj_convL_geps`, `fourierConj_mulLeft_dind` | $\mathrm{conv}(\mathcal Ff, \mathcal Fg) = N\mathcal F(fg)$、$\mathcal FE_s\mathcal F^{-1} = D_s$、$\mathcal FD_s\mathcal F^{-1} = E_s$ |
| `map_fourierConj_shellAlg`, `map_fourierConj_oneEAlg`, `finrank_dualOneEAlg`, **`shellAlg_eq_dualOneEAlg_iff`** | $\mathcal FA_N\mathcal F^{-1} = A_N$、$\mathcal F\langle D_u, E_N\rangle\mathcal F^{-1} = \langle E_u, D_N\rangle$、次元は等しい、$A_N = \langle E_u, D_N\rangle$ ⇔ 同じ条件 |

定義は `shellAlgEquivOfMem`・`fourierConj`・`dualOneEAlg` です。

**証明の筋**
1. **1 点の殻と動径関数。**
   - #D_s = φ(N/s)（Part 201 の `card_dsh`）なので、φ(N/s) = 1 なら殻の 2 点は一致します。
   - 単数 a で $1_{D_s}(ax) = 1_{D_s}(x)$ です。x ∈ D_s なら ax ∈ D_s で、1 点なので ax = x です。よって $(1_{D_s}g)(ax) = (1_{D_s}g)(x)$ です。
   - $\mathcal F(E_sf) = 1_{D_s}\mathcal Ff$（Part 239）と「f が動径 ⇔ 𝓕f が動径」（Part 203）から、$E_sf$ は動径関数です。
   - 動径関数の上では P は恒等なので $PE_s = E_s$、Part 240 の角の代数の式から $E_s = PE_s = \Phi([E_s])$ です。
2. **十分条件。** $\sum_{s\mid N}E_s = 1$（Part 228）から $E_1 = 1 - \sum_{s\ne1}E_s$ です。s ∤ N なら $E_s = 0$ です。A_N の生成元 $D_s$・$E_s$ がすべて ⟨D_u, E_N⟩ に入ります。
3. **条件の言い換え。**
   - p = minFac(N) で φ(N/p) = 1 なので、N/p = 1 か 2 です。
   - N/p = 2 なら N = 2p で、s = 2 でも φ(p) = 1 なので p = 2、N = 4 です。
   - 逆は N = 1, 4 と素数の約数を直接見ます。
4. **次元の比較。**
   - 素冪では 2 つの式の差が $k(k+1)/2 - k = k(k-1)/2$（p 奇数）、$k(k+1)/2 - 2k + 1 = (k-1)(k-2)/2$（p = 2）です。
   - N = ab（a は奇数、a, b > 1、互いに素）では次のとおりです。
     - dim A_{ab} = dim A_a·dim A_b（Part 226）です。
     - 包含から dim A_a ≥ d(a)² + d(a) − 1、dim A_b ≥ d(b)² です。
     - x = d(a)、y = d(b) ≥ 2 で $(x^2 + x - 1)y^2\ge(xy)^2 + xy$（$x + y\le xy$ から）なので、dim A_{ab} > G(ab) です。
   - 一般の N は p = minFac(N)、N = p^k·M（Mathlib の `Nat.ordProj_mul_ordCompl_eq_self`）と分けます。
     - M = 1 なら素冪の場合です。p 奇数なら k ≥ 2、p = 2 なら k ≥ 3 で、差が 1 以上です。
     - M > 1 なら、p 奇数のとき a = p^k、p = 2 のとき a = M（奇数）として積の場合になります。
5. **フーリエ双対。**
   - $\mathcal F(\mathrm{conv}(\mathcal Ff, \mathcal Fg)) = \mathcal F\mathcal Ff\cdot\mathcal F\mathcal Fg$ と $\mathcal F\mathcal F\Phi = N\Phi(-\cdot)$（Mathlib の `ZMod.dft_dft`）から、$\mathrm{conv}(\mathcal Ff, \mathcal Fg) = N\mathcal F(fg)$ が出ます。
   - これと $\mathcal F1_{D_s} = N\varepsilon_s$ で $\mathcal FD_s\mathcal F^{-1} = E_s$ です。
   - 部分代数の像は生成元の像で生成されます（`AlgHom.map_adjoin`）。共役は単射なので、2 つの等式は同値です。

**例**
- N = 4：約数は 1, 2, 4 です。4/2 = 2、4/4 = 1 なので $E_2$・$E_4$ は ⟨D_u, E_4⟩ に入ります（$E_4$ は定数への射影、$E_2$ は $(-1)^x$ の方向への射影）。$E_1 = 1 - E_2 - E_4$ も入り、dim A_4 = 10 = 9 + 3 − 1 − 1 です。
- N = 6：s = 2 では 6/2 = 3（φ = 2）です。dim A_6 = 20 > 18 で、`exists_convL_geps_not_mem` から $E_2\notin\langle D_u, E_6\rangle$ です（φ(N/s) ≠ 1 となる s ≠ 1 は s = 2 だけ）。
- 素冪の差：9, 27, 81 で 1, 3, 6、8, 16, 32, 64 で 1, 3, 6, 10 です。
- 条件を満たす N の分解：奇素数 p で $A_p = \langle D_u, E_p\rangle\cong M_2(\mathbb C)\times\mathbb C$（5 次元）、$A_2\cong M_2(\mathbb C)$（4 次元）、$A_4\cong M_3(\mathbb C)\times\mathbb C$（10 次元）です。

**読み取れること**
- ⟨D_u, E_N⟩ の動径関数の外の部分は、各殻の上で平均を引いた部分へのスカラーだけです（Part 241）。A_N はほかの $E_s$ で、そこに大きなブロックをもちます。それがないのは、1 でない約数がすべて s = N, N/2 のとき、つまり N ∈ {1, 4} ∪ 素数 のときだけです。
- この条件のもとで、Part 225 の $A_N\cong\prod_pM_{n_p}(\mathbb C)$ は、大きさ d(N) のブロック 1 つと 1 次元のブロック #S′ 個になります。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| φ(N/s) = 1 なら $E_s$ の像は動径関数で $E_s = \Phi([E_s])\in\langle D_u, E_N\rangle$ | **正しい（`radial_conv_geps`、`convL_geps_eq_radialMatOp`、`convL_geps_mem_oneEAlg`）**。数値でも 180/180 |
| 1 でない約数 s ですべて φ(N/s) = 1 ⇔ N ∈ {1, 4} ∪ 素数 | **正しい（`forall_totient_eq_one_iff`）**。数値でも 20000/20000 |
| dim A_{p^k} − dim ⟨D_u, E_{p^k}⟩ = k(k−1)/2（p 奇数）、(k−1)(k−2)/2（p = 2） | **正しい（`finrank_shellAlg_primePow_odd`、`finrank_shellAlg_two_pow`）**。数値でも式で 9684/9684・16/16、生成元からの計算で 14/14 |
| N = ab（a 奇数、a, b > 1、互いに素）で dim ⟨D_u, E_N⟩ < dim A_N | **正しい（`finrank_lt_of_eq_mul`）**。数値でも F(a)F(b) ≥ G(a)G(b) > G(ab) が 36065/36065 |
| **A_N = ⟨D_u, E_N⟩ ⇔ N ∈ {1, 4} ∪ 素数** | **正しい（`shellAlg_eq_oneEAlg_iff`）**。数値でも式で 100000/100000、生成元からの計算で 48/48（Part 241 では数値だけ、N ≤ 40） |
| F(N) = G(N) ⇔ N ∈ {1, 4} ∪ 素数（式だけの形） | **正しい（`prod_eq_iff`）**。数値でも 100000/100000 |
| 条件の外では $E_s\notin\langle D_u, E_N\rangle$ となる s ≠ 1（φ(N/s) ≠ 1）がある | **正しい（`exists_convL_geps_not_mem`）** |
| s ≠ 1 で $E_s\in\langle D_u, E_N\rangle$ ⇔ φ(N/s) = 1 | ⇐ は正しい（`convL_geps_mem_oneEAlg`）。⇒ は**数値だけ**（201/201、N ≤ 60） |
| $E_1\in\langle D_u, E_N\rangle$ ⇔ N ∈ {1, 4} ∪ 素数 | ⇐ は正しい（主定理から）。⇒ は**数値だけ**（60/60） |
| $\mathcal FE_s\mathcal F^{-1} = D_s$、$\mathcal FD_s\mathcal F^{-1} = E_s$ | **正しい（`fourierConj_convL_geps`、`fourierConj_mulLeft_dind`）**。数値でも 261/261 |
| $\mathcal FA_N\mathcal F^{-1} = A_N$、$\mathcal F\langle D_u, E_N\rangle\mathcal F^{-1} = \langle E_u, D_N\rangle$、$A_N = \langle E_u, D_N\rangle$ ⇔ 同じ条件 | **正しい（`map_fourierConj_shellAlg`、`map_fourierConj_oneEAlg`、`shellAlg_eq_dualOneEAlg_iff`）**。数値でも dim ⟨E_u, D_N⟩ = G(N) と一致の判定 40/40 |
| 素因数 2 つ以上での次元の差の具体的な値 | 2 つの式（Part 226・241）から計算できる。Lean では 1 以上であることだけを示した |

## 2. 数値照合（step265）

| 項目 | 内容 | 結果 |
|---|---|---|
| (1) | 式の水準（N ≤ 100000）：F ≥ G／F = G ⇔ N ∈ {1, 4} ∪ 素数／条件 ⇔ 同じ集合（N ≤ 20000）／素冪の差（p^k ≤ 100000）／F(a)F(b) = F(ab) ≥ G(a)G(b) > G(ab)（奇数の a ≤ 300、b ≤ 300、互いに素） | 100000/100000／100000/100000／20000/20000／9684/9684・16/16／36065/36065 |
| (2) | 生成元から直交化で計算（N ≤ 48）：dim A_N = F(N)、dim ⟨D_s, E_N⟩ = G(N)、一致 ⇔ N ∈ {1, 4} ∪ 素数 | 48/48 |
| (3) | φ(N/s) = 1 なら $PE_s = E_s$ かつ $E_s = \Phi([E_s])$（N ≤ 120） | 180/180（7.2e-16） |
| (4) | 観察（数値だけ、N ≤ 60）：s ≠ 1 で $E_s\in\langle D_s, E_N\rangle$ ⇔ φ(N/s) = 1／$E_1$ ∈ ⇔ N ∈ {1, 4} ∪ 素数 | 201/201／60/60 |
| (5) | 素冪の差を生成元からの計算で（2, 4, 8, 16, 32, 64, 3, 9, 27, 81, 5, 25, 7, 49） | 14/14 |
| (6) | 対照：平方因子なしの判定とは N = 4, 6, 10, 14, … で、d(N) ≤ 2 の判定とは N = 4 で違う | 違うことを確認 |
| (7) | フーリエ双対：$\mathcal FE_s\mathcal F^{-1} = D_s$・$\mathcal FD_s\mathcal F^{-1} = E_s$（N ≤ 60）／生成元から計算した dim ⟨E_u, D_N⟩ = G(N) と一致の判定（N ≤ 40） | 261/261（2.3e-14）／40/40 |

- **実行は 2 回です。**
  - 1 回目（約 36 秒）は項目 (1)〜(6) で、すべて合格しました。
  - その後で Lean にフーリエ双対の節を足したので、項目 (7) を足して 2 回目を実行しました。2 回目は (1)〜(6) を保存済みの結果（`step265_cache.json`）から読み、(7) だけを計算しました（約 1 秒）。
  - `step265.log` は 2 回目のログです。1 回目のログは `step265_run1.log` に残しました。2 つの違いは (7) の行と秒数の行だけです。
- 差 F − G の例：N = 6 で 2、8 で 1、9 で 1、12 で 10、16 で 3、27 で 3、30 で 30、32 で 6、60 で 96。
- **限界。**
  - (2) の生成元からの独立な計算は N ≤ 48 です（(7) の双対は N ≤ 40）。
  - (4) の観察は N ≤ 60 です。

## 3. Lean（`PAG246.lean`、namespace `PAG.Part246`、PAG245 を import）

| 区分 | 項目 |
|---|---|
| 1. φ(N/s) = 1 の E_s | `eq_of_gcd_eq`, `radial_dind_mul`, `radial_conv_geps`, `convL_geps_eq_radialMatOp`, `convL_geps_mem_oneEAlg`, `convL_geps_half_mem_oneEAlg` |
| 2. 十分条件と言い換え | `shellAlg_le_oneEAlg_of_forall_mem`, `shellAlg_eq_oneEAlg_of_forall`, `forall_totient_eq_one_iff` |
| 3. 次元の比較 | `finrank_oneEAlg_le`, `card_divisors_primePow`, `finrank_shellAlg_primePow`, `two_dvd_primePow_iff`, `finrank_oneEAlg_primePow_add`, `half_mul_succ`, `finrank_shellAlg_primePow_odd`, `finrank_shellAlg_two_pow`, `finrank_lt_of_eq_primePow_odd`, `finrank_lt_of_eq_two_pow`, `finrank_lt_of_eq_mul`, `finrank_oneEAlg_lt_shellAlg` |
| 4. 主定理 | def `shellAlgEquivOfMem`, `shellAlg_eq_oneEAlg_iff`, `shellAlg_eq_oneEAlg_iff_forall`, `finrank_shellAlg_eq_iff`, `prod_eq_iff`, `shellAlgEquivOfMem_apply`, `exists_convL_geps_not_mem` |
| 5. フーリエ双対 | def `fourierConj`・`dualOneEAlg`, `conv_dft_dft`, `fourierConj_convL_geps`, `fourierConj_mulLeft_dind`, `map_fourierConj_shellAlg`, `map_fourierConj_oneEAlg`, `finrank_dualOneEAlg`, `shellAlg_eq_dualOneEAlg_iff` |

**使った PAG の結果**
- Part 15・16 の `conv`・`convL`・`dft_conv`（PAG15・PAG16）
- Part 201 の `dind`・`geps`・`card_dsh`（PAG205）、Part 203 の `Radial`・`gcd_val_unit_mul`・`radial_iff_dft`（PAG207）
- Part 214 の `shellAlg`（PAG218）、Part 226 の `finrank_shellAlg_eq_prod`・`finrank_shellAlg_mul`（PAG230）、Part 228 の `convL_geps_mem`・`sum_convL_geps`・`geps_eq_zero_of_not_dvd`・`shellAlg_eq_adjoin`（PAG232）
- Part 238 の `radialHom`（PAG242）、Part 239 の `radialBasis`・`radialMatOp`・`dft_conv_geps`・`dft_dind`（PAG243）
- Part 240 の `oneEAlg`・`oneEAlg_le`・`shellAvg_mul_eq`・`shellAvg_apply_of_radial`（PAG244）
- Part 241 の `radialMatOp_mem_oneEAlg`・`finrank_oneEAlg_self_add`・`finrank_oneEAlg_self_sub`・`devSet`・`wholeMap`・`wholeAlgEquiv`（PAG245）

**Mathlib・Lean から使った主なもの**
- 自然数：`Nat.totient_eq_one_iff`・`Nat.totient_two`・`Nat.minFac_prime`・`Nat.eq_of_dvd_of_div_eq_one`・`Nat.Prime.divisors`・`Nat.divisors_prime_pow`・`Nat.primeFactors_prime_pow`・`Nat.Prime.factorization_pow`・`Nat.Coprime.card_divisors_mul`・`Nat.ordProj_mul_ordCompl_eq_self`・`Nat.coprime_ordCompl`・`Nat.ordCompl_pos`・`Nat.Prime.factorization_pos_of_dvd`・`Nat.one_lt_pow`・`Nat.Prime.odd_of_ne_two`・`Odd.pow`・`Nat.not_even_iff_odd`・`Nat.Prime.coprime_iff_not_dvd`・`Nat.Coprime.coprime_dvd_left`・`Nat.mul_add_div`・`Nat.le_div_iff_mul_le`
- 有限集合と次元：`Finset.card_le_one`・`Finset.one_lt_card`・`Finset.add_sum_erase`・`Submodule.finrank_mono`・`Subalgebra.toSubmodule`（順序の埋め込み）・`Algebra.adjoin_le`・`Subalgebra.equivOfEq`
- フーリエ変換と共役：`ZMod.dft_dft`・`LinearEquiv.conjAlgEquiv`・`AlgHom.map_adjoin`・`AlgEquiv.subalgebraMap`・`Subalgebra.map_injective`・`smul_right_injective`・`Set.range_comp`・`Set.image_union`・`Set.image_singleton`

**コンパイル**
- `PAG246` は 2 回コンパイルし、どちらもエラー・警告なしで通りました。
  - 1 回目（約 13 秒）は T2 の内容（§1〜4、27 項目と定義 1 個）です。
  - 2 回目（約 13 秒）は §5 フーリエ双対を足した T3 の内容（34 項目と定義 3 個）です。
- 公理は標準のもの（propext、Classical.choice、Quot.sound）か、その一部だけです。37 行のうち 1 行が一部だけです（`half_mul_succ` は [propext, Quot.sound]）。
- 内容は試しのファイル T3 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble246.py`）。
- **試しのファイル（置き場所は `/home/claude/leanwork/scratch/t242`）。** どれも 1 回目でエラー・警告なしで通りました。
  - W0：import の温め（232 秒）。W1・W2：API の名前の確認。
  - T1（25 項目と定義 1 個、§1〜4、19 秒）。
  - T2（§2 を「$E_s$ がすべて入れば A_N ⊆ ⟨D_u, E_N⟩」の補題とその系に分け、4f を足した。27 項目、12 秒）。
  - T3（§5 を足した。34 項目と定義 3 個、13 秒）。
- 前回の注意を当てはめた箇所があります。
  - 非線形の項（(k+1)²、k(k−1)/2）は `generalize` で変数にしてから `omega` に渡しました（Part 226 の注意）。
  - 法が式で決まる主張は、変数 n と仮定 n = a·b・n = p^k の形の補題にして中で `subst` しました（Part 236・237 の注意）。
  - 部分代数の次元の比較は `Submodule.finrank_mono` と `Subalgebra.toSubmodule` で行いました（Part 224 の注意）。
- **環境。** Mathlib の追加ビルドはありません。Part 241 の納品（15:53 ごろ）の後、Part 242 の開始時（17:35）にコンテナが再起動していました（起動時刻 17:35:15）。ファイルと .olean は残っていて、最初の import は 232 秒でした（キャッシュが冷えていた）。

## 4. 残る問い

1. **（次の候補）どの E_s が入らないか。** 観察 (4)「s ≠ 1 で $E_s\in\langle D_u, E_N\rangle$ ⇔ φ(N/s) = 1」の ⇒ を Lean にすることです。⇐ は今回、⇒ は「少なくとも 1 つ」の形だけでした。
   - 1 つの殻の上で平均 0 の関数 f に対して、⟨D_u, E_N⟩ の元は f のスカラー倍を返します。そこで、$E_sf\notin\mathbb Cf$ となる f を具体的に作る方針です。N = 6 では s = 2 と $\delta_1$、N = 8 では s = 2 と $\delta_1 - \delta_3$ で確かめました。
2. **次元の差の閉じた形。** 素因数 2 つ以上のときの dim A_N − dim ⟨D_u, E_N⟩ を、単数群の指標（Part 225 の n_p）の言葉で書くことです。
3. **ほかの殻の組み合わせ。** ⟨D_u, E_s⟩（Part 240）の空間全体の構造と次元を、s ≠ N でも求めることです（Part 241 は s = N）。
4. **引き継ぎメモのほかの候補。** $C_N = \bigotimes_pC_{p^{v_p}}$ の PiTensorProduct の形、dilComm$_{q^k}$、$A_N$ のウェダーバーン成分の分配の形、中心そのものの finrank、P・Q_s の自己共役、ほか。
