# アデール射影幾何 2.0 — Part 241：ラマヌジャン和の閉じた式（フォン・シュテルネックの式）と、空間全体の ⟨D_s, E_N⟩ ≅ M_{d(N)}(ℂ) × ℂ^{S′}

2026-11-05。引き継ぎメモの次の候補を 2 つとも Lean にしました。1 つは空間全体の ⟨D_s, E_N⟩ の構造と次元で、Part 239 の (8) では数値だけでした。もう 1 つはフォン・シュテルネックの式で、Part 240 の残る問い 2 でした。中心の次元は、数値照合を書いた時点では数値だけの予定でしたが、Lean にできました（§1）。

- **フォン・シュテルネックの式（Lean）。** g = gcd(q, n) のとき、整数で $c_q(n)\cdot\varphi(q/g) = \mu(q/g)\cdot\varphi(q)$ です（`ramSum_mul_totient`）。
  - 両辺とも q について乗法的なので、素冪で確かめました。左辺は Part 240 の `ramSum` と q ↦ φ(q/gcd(q, n)) の各点の積、右辺は q ↦ μ(q/gcd(q, n)) と φ の各点の積です。
  - 系として次を示しました。
    - 閉じた式 $c_q(n) = \mu(q/g)\varphi(q)/\varphi(q/g)$（`ramSum_eq_div`）
    - $c_q(n)$ は gcd(q, n) だけで決まる（`ramSum_gcd`）
    - $(q, n) = 1$ なら $\mu(q)$、$q\mid n$ なら $\varphi(q)$
    - **$c_q(n)\ne0\iff q/g$ が平方因子をもたない**（`ramSum_ne_zero_iff_squarefree`）。Part 240 の判定（どの素因数 p でも $p^{v_p(q)-1}\mid n$）を言い換えた形です。
    - Part 239 の行列 C(u, t) の閉じた式（`ramMat_eq_closed`）
- **E_N と、殻の上で平均を引く作用素（Lean）。**
  - $E_N$（定数への射影）は角の代数に入り、$E_N = \Phi([E_N])$ です（`convL_geps_self_eq`）。
  - $Q_s = D_s - P_{s,s}$（`shellDev`）は次を満たします。
    - $Q_sP_{u,v} = P_{u,v}Q_s = 0$、$Q_sQ_t = [s = t]\,Q_s$
    - $P + \sum_sQ_s = 1$
    - **$Q_s = 0\iff\varphi(N/s) = 1$**（`shellDev_eq_zero_iff`）。つまり N/s = 1, 2 のときで、殻が 1 点のときです。
- **空間全体の構造（Lean）。** $S′ = \{s\mid N : \varphi(N/s)\ne1\}$ とします。
  - $\Psi(M, b) = \sum M_{st}P_{s,t} + \sum_{s\in S′}b_sQ_s$ は、単射な代数準同型 $M_{d(N)}(\mathbb C)\times\mathbb C^{S′}\to\mathrm{End}(\mathbb C^{\mathbb Z/N})$ です。
  - **その像はちょうど ⟨D_u, E_N⟩** で、代数の同型 `wholeAlgEquiv` を得ました。これが ⟨D_s, E_N⟩ のウェダーバーン分解で、動径関数の上の行列のブロック 1 つと、2 点以上ある殻ごとの 1 次元のブロックに分かれます。
  - **$\dim\langle D_u, E_N\rangle = d(N)^2 + d(N) - 1 - [2\mid N]$**（`finrank_oneEAlg_self_sub`）。$\#S′ = d(N) - 1 - [2\mid N]$ は `Nat.totient_eq_one_iff` から出ます（`card_devSet`）。
- **中心（Lean）。**
  - ⟨D_u, E_N⟩ の元が中心に入るのは、$c\cdot P + \sum_{s\in S′}b_sQ_s$ の形のときちょうどです（`mem_center_oneEAlg_iff`）。証明には Mathlib の `Matrix.center_eq_range` を使いました。
  - その形の作用素の空間は $1 + \#S′ = d(N) - [2\mid N]$ 次元です（`finrank_range_centerMap`・`_add`）。
- **限界（正直な注記）。**
  - 中心の次元は、中心そのもの（`Subalgebra.center` の型）の finrank としては書いていません。「中心の元 ⇔ centerMap の像の元」と「centerMap の像の次元」の 2 つの形で書きました。
  - P・Q_s が直交射影（自己共役）であることは今回も書いていません。
  - 観察 (8) の「A_N = ⟨D_s, E_N⟩ ⇔ N ∈ {1, 2, 4} ∪ 素数」は数値だけ（N ≤ 40）です。
- **やり直し。** 試しのファイル T1〜T3 は T2 でエラー 2 件でした（§3）。
  - T2 の 1 件は、subst の後に 2 つの if が同じ形になったのに `rw [ite_eq_left rfl]` を 2 回書いたものです。
  - もう 1 件は `Pi.single` の型が推論できなかったものです。
  - PAG245 は 2 回コンパイルしました（2 回目は docstring の番号の付け直しだけ）。
- **環境。** Mathlib の追加ビルドはありません。Part 241 の開始時（15:26）にコンテナが再起動していました。

成果物は次のとおりです。
- `PAG245.lean`：63 項目。sorry 0・警告 0 です。
  - 定義 8 個は項目に数えません。
  - 出力は `PAG245.out`（#print axioms 71 行）。
- 照合用の `step264.py`：ログは `step264.log` です。

xlsx の集計は 3033 項目になりました（手順 261）。

## 0. 結論

**記号**（Part 239・240 と同じ）
- $D_t = \{x : \gcd(N,x) = t\}$、$1_{D_t}$ = `dind N t`、$\varepsilon_s = \mathcal F^{-1}1_{D_s}$、$E_sf = \varepsilon_s\star f$、$D_sf = 1_{D_s}f$。$A_N$ = `shellAlg N`（すべての $D_s$・$E_s$ が生成）。
- $[T](u,t) = (T1_{D_t})(u)$、$P_{s,t} = \frac N{\varphi(N/t)}D_sE_ND_t$、$\Phi(M) = \sum M_{st}P_{s,t}$（`radialMatOp`）、$P = \sum_sP_{s,s}$（`shellAvg`）。
- $c_q(n)$ = `ramSum n q`（Part 240）。$g = \gcd(q, n)$。
- $Q_s = D_s - P_{s,s}$（`shellDev`）。$S′ = \{s\mid N : \varphi(N/s)\ne1\}$（`devSet`）。$\Psi(M, b) = \Phi(M) + \sum_{s\in S′}b_sQ_s$（`wholeMap`・`wholeHom`）。
- $\langle D_u, E_N\rangle$ = `oneEAlg N N`（Part 240 の `oneEAlg N s` で s = N）。

| 定理 | 主張 |
|---|---|
| `ramSum_gcd`, `ramSum_mod`, `ramSum_of_coprime` | $c_q(n) = c_q(\gcd(q,n))$、$c_q(n\bmod q) = c_q(n)$、$(q,n) = 1$ なら $c_q(n) = \mu(q)$ |
| `totientDivGcd_apply`, `moebiusDivGcd_apply`, `gcd_mul_of_coprime`, `mul_div_gcd_of_coprime`, `coprime_div_gcd_of_coprime` | 互いに素な a, b で gcd(ab, n) = gcd(a, n)gcd(b, n)、ab/gcd(ab, n) = (a/gcd(a, n))(b/gcd(b, n))、2 つの商は互いに素 |
| `isMultiplicative_totientDivGcd`, `isMultiplicative_moebiusDivGcd` | q ↦ φ(q/gcd(q, n))・μ(q/gcd(q, n)) は乗法的 |
| `ramSum_mul_totient_primePow`, **`ramSum_mul_totient`** | フォン・シュテルネックの式（整数の形）$c_q(n)\varphi(q/g) = \mu(q/g)\varphi(q)$ |
| `div_gcd_pos`, `ramSum_eq_div`, **`ramSum_ne_zero_iff_squarefree`**, `ramSum_of_dvd`, `ramMat_eq_closed` | $c_q(n) = \mu(q/g)\varphi(q)/\varphi(q/g)$、$c_q(n)\ne0\iff q/g$ 平方因子なし、$q\mid n$ なら $\varphi(q)$、C(u, t) の閉じた式 |
| `radialMatOp_add`, `radialMatOp_smul`, `radialMatOp_zero`, `radialMatOp_single`, **`convL_geps_self_eq`** | Φ は線形、$\Phi(c\,E_{st}) = c\,P_{s,t}$、$E_N = \Phi([E_N])$ |
| `shellDev_apply`, `mulLeft_dind_mul_shellTrans`, `shellTrans_mul_mulLeft_dind`, `shellDev_mul_shellTrans`, `shellTrans_mul_shellDev`, `shellDev_mul_shellDev` | $D_sP_{u,v} = [s = u]P_{s,v}$、$P_{u,v}D_s = [v = s]P_{u,v}$、$Q_sP_{u,v} = P_{u,v}Q_s = 0$、$Q_sQ_t = [s = t]Q_s$ |
| `shellDev_single_apply`, **`shellDev_eq_zero_iff`** | $(Q_t\delta_s)(s) = [s = t](1 - 1/\varphi(N/s))$、$Q_s = 0\iff\varphi(N/s) = 1$ |
| `dvd_of_mem_devSet`, `card_filter_totient_eq_one`, `card_devSet`, `sum_devSet_shellDev`, `shellAvg_add_sum_shellDev` | $\#\{s : \varphi(N/s) = 1\} = 1 + [2\mid N]$、$\#S′ + 1 + [2\mid N] = d(N)$、$P + \sum_{s\in S′}Q_s = 1$ |
| `radialMatOp_mul_shellDev`, `shellDev_mul_radialMatOp`, `shellDev_mul_shellDev_devSet`, `wholeMap_apply`, `wholeMap_one`, `wholeMap_mul`, `wholeHom_apply` | Ψ は代数準同型（$\Psi(1,1) = 1$、積を保つ） |
| `shellAvg_mul_wholeMap`, **`wholeMap_injective`** | $P\Psi(M, b) = \Phi(M)$、Ψ は単射 |
| `shellTrans_mem_oneEAlg`, `radialMatOp_mem_oneEAlg`, `shellDev_mem_oneEAlg`, `radialMatOp_mem_range`, `shellDev_mem_range`, `mulLeft_dind_mem_range`, **`range_wholeHom`**, `wholeAlgEquiv_apply` | Ψ の像 = ⟨D_u, E_N⟩、同型 `wholeAlgEquiv` |
| `toSubmodule_oneEAlg_self`, `finrank_oneEAlg_self`, `finrank_oneEAlg_self_add`, **`finrank_oneEAlg_self_sub`** | $\dim\langle D_u, E_N\rangle = d^2 + \#S′ = d^2 + d - 1 - [2\mid N]$ |
| `wholeMap_smul_one`, **`mem_center_oneEAlg_iff`**, `centerMap_apply`, `centerMap_injective`, `mem_center_oneEAlg_iff_range`, **`finrank_range_centerMap`**, `finrank_range_centerMap_add` | 中心の元 ⇔ $cP + \sum_{s\in S′}b_sQ_s$、その空間の次元 $1 + \#S′ = d - [2\mid N]$ |

定義は `totientDivGcd`・`moebiusDivGcd`・`shellDev`・`devSet`・`wholeMap`・`wholeHom`・`wholeAlgEquiv`・`centerMap` です。φ を整数値の数論的関数にしたものは、Part 226 の `totientAF`（PAG230）を使いました。

**証明の筋**
1. **フォン・シュテルネックの式。**
   - 互いに素な a, b で gcd(ab, n) = gcd(a, n)gcd(b, n) なので、q ↦ q/gcd(q, n) は互いに素な積を互いに素な商の積に写します。これで q ↦ φ(q/g)・μ(q/g) は乗法的です。
   - 各点の積も乗法的なので、両辺の一致は素冪 $q = p^i$ で確かめれば足ります（Mathlib の `IsMultiplicative.eq_iff_eq_on_prime_powers`）。
   - 素冪では $\gcd(p^i, n) = p^j$（$j\le i$）とおき、Part 240 の素冪の式 $c_{p^i}(n) = p^i[p^i\mid n] - p^{i-1}[p^{i-1}\mid n]$ と比べます。場合は 3 つです。
     - j = i：両辺 $\varphi(p^i)$
     - j = i − 1：両辺 $-p^{i-1}(p-1)$
     - j ≤ i − 2：両辺 0（$\mu(p^{i-j}) = 0$）
   - 0 にならない条件は、$\varphi(q/g)$・$\varphi(q)$ が 0 でないので $c_q(n)\ne0\iff\mu(q/g)\ne0$ です。
2. **E_N と Q_s。**
   - $E_N f$ は定数関数で動径関数なので、Part 240 の `shellAvg_apply_of_radial` から $PE_N = E_N$ です。Part 240 の `shellAvg_mul_eq` から $PE_N = \Phi([E_N])$ なので、$E_N = \Phi([E_N])$ です。
   - $Q_s$ の積は、$D_sD_t = [s = t]D_s$、$D_sP_{u,v} = [s = u]P_{s,v}$、$P_{u,v}D_s = [v = s]P_{u,v}$ と Part 239 の行列単位の積の規則から出ます。
   - $\varphi(N/s) = 1$ なら $D_s$ は 1 点で $Q_s = 0$ です（Part 201 の `card_dsh`）。$\varphi(N/s)\ne1$ なら $(Q_s\delta_s)(s) = 1 - 1/\varphi(N/s)\ne0$ です。
3. **空間全体。**
   - Ψ が単位元を保つことは、$P + \sum_{s\in S′}Q_s = \sum_s(P_{s,s} + Q_s) = \sum_sD_s = 1$ から出ます。積を保つことは、2 の積の規則（交差の項は 0、$Q_sQ_t = [s = t]Q_s$）から出ます。
   - 単射性：$\Psi(M, b) = 0$ なら、左から P を掛けて $\Phi(M) = 0$、Part 239 の単射性から $M = 0$ です。残りを $\delta_s$ に当てて点 s で見ると $b_s(1 - 1/\varphi(N/s)) = 0$ なので $b_s = 0$ です。
   - 像：⟨D_u, E_N⟩ の生成元はどれも像に入ります。$D_u = P_{u,u} + Q_u$（u ∤ N なら $D_u = 0$）、$E_N = \Phi([E_N])$ です。逆に $P_{s,t}$・$Q_s$ は生成元の積と差です。
   - 次元は単射な線形写像の像の次元（Mathlib の `LinearMap.finrank_range_of_inj`）で $d^2 + \#S′$ です。$\#S′$ は $\varphi(m) = 1\iff m\in\{1, 2\}$（`Nat.totient_eq_one_iff`）で数えます。$\varphi(N/s) = 1$ となる約数は s = N と、N が偶数なら s = N/2 です。
4. **中心。**
   - T = Ψ(M, b) が中心なら、すべての行列 X で Ψ(X, 0) と可換です。Ψ の単射性から XM = MX となり、Mathlib の `Matrix.center_eq_range` で M はスカラー行列 c·1、T = Ψ(c·1, b) = cP + Σ b_s Q_s です。
   - 逆は、Ψ(c·1, b) が Ψ のどの値とも可換なことからです。

**例**
- $c_{12}(n)$（n = 0, …, 12）= 4, 0, 2, 0, −2, 0, −4, 0, −2, 0, 2, 0, 4 です。
  - n = 6：g = 6、q/g = 2 で、$\mu(2)\varphi(12)/\varphi(2) = -4$。
  - n = 3：q/g = 4 は平方因子をもつので 0。
- N = 12（d = 6）：12/s が 1, 2 になる s = 12, 6 の殻は 1 点（{0}・{6}）で、$Q_{12} = Q_6 = 0$ です。S′ = {1, 2, 3, 4}、$\dim\langle D_u, E_{12}\rangle = 36 + 4 = 40$、中心の次元は 1 + 4 = 5 です。
- N = 2：S′ = ∅ で、$\langle D_u, E_2\rangle = M_2(\mathbb C) = \mathrm{End}(\mathbb C^{\mathbb Z/2})$（4 次元）です。奇素数 p では S′ = {1} で 5 次元です。

**読み取れること**
- 殻の射影と定数への射影が生成する代数 ⟨D_s, E_N⟩ のウェダーバーン分解は $M_{d(N)}(\mathbb C)\oplus\mathbb C^{\#S′}$ です。
  - 行列のブロックは動径関数の上にあり、単位元は P です。
  - 1 次元のブロックは 2 点以上ある殻ごとに 1 つで、単位元は $Q_s$（殻の上で平均を引く）です。
  - 次元の式の $-[2\mid N]$ は、1 点の殻 $D_{N/2} = \{N/2\}$ から来ます。
- ラマヌジャン和が 0 にならない条件は、q/gcd(q, n) が平方因子をもたないことに帰着します。Part 240 の「E_s 1 つで足りる ⇔ N/s が平方因子をもたない」は、この形で見ると自然です。u = 1 では gcd(N/s, 1) = 1 なので、$c_{N/s}(1)\ne0\iff N/s$ が平方因子をもたない、となります。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| $c_q(n) = c_q(\gcd(q,n))$、$c_q(n\bmod q) = c_q(n)$ | **正しい（`ramSum_gcd`、`ramSum_mod`）**。数値でも 125750/125750 ずつ（周期性は $c_q(n+q) = c_q(n)$ の形で照合） |
| $c_q(n)\varphi(q/g) = \mu(q/g)\varphi(q)$、$c_q(n) = \mu(q/g)\varphi(q)/\varphi(q/g)$ | **正しい（`ramSum_mul_totient`、`ramSum_eq_div`）**。数値でも整数で 501500/501500（Part 240 では残る問い） |
| $c_q(n)\ne0\iff q/g$ が平方因子をもたない | **正しい（`ramSum_ne_zero_iff_squarefree`）**。数値でも 501500/501500。Part 240 の判定（`ramSum_ne_zero_iff`）との同値は、どちらも Lean にあるので従う（その同値を 1 つの定理としては書いていない。数値では 501500/501500） |
| $(q,n) = 1$ なら $c_q(n) = \mu(q)$、$q\mid n$ なら $\varphi(q)$ | **正しい（`ramSum_of_coprime`、`ramSum_of_dvd`）**。数値でも 304193/304193・2000/2000 |
| C(u, t) = μ(q/g)φ(q)/φ(q/g)（q = N/t、g = gcd(q, u)） | **正しい（`ramMat_eq_closed`）**。数値でも DFT で計算した $N\varepsilon_t(u)$ と 8254/8254 |
| $E_N = \Phi([E_N])$ | **正しい（`convL_geps_self_eq`）**。数値でも 120/120 |
| $Q_s$ の積の規則、$P + \sum Q_s = 1$ | **正しい（`shellDev_mul_shellTrans`・`shellTrans_mul_shellDev`・`shellDev_mul_shellDev`・`shellAvg_add_sum_shellDev`）**。数値でも 33800/33800（4 種）・4038/4038・120/120 |
| $Q_s = 0\iff\varphi(N/s) = 1$、$\#S′ = d(N) - 1 - [2\mid N]$ | **正しい（`shellDev_eq_zero_iff`、`card_devSet`）**。数値でも 602/602・10000/10000 |
| ⟨D_u, E_N⟩ ≅ $M_{d(N)}(\mathbb C)\times\mathbb C^{S′}$（Ψ が同型） | **正しい（`wholeAlgEquiv`：`wholeMap_injective`・`range_wholeHom`）**。数値でも、生成元が span に入る・一次独立 120/120、乱数の積 360/360、積の表 60/60 |
| $\dim\langle D_u, E_N\rangle = d^2 + d - 1 - [2\mid N]$ | **正しい（`finrank_oneEAlg_self_sub`）**。数値でも生成元から独立に計算して 60/60（N ≤ 60。Part 239 では数値だけ） |
| 中心の元 ⇔ $cP + \sum_{s\in S′}b_sQ_s$、その空間の次元 $1 + \#S′ = d - [2\mid N]$ | **正しい（`mem_center_oneEAlg_iff`、`finrank_range_centerMap`・`_add`）**。数値でも 60/60。中心そのもの（`Subalgebra.center` の型）の finrank の形では書いていない |
| P・Q_s は直交射影（自己共役） | 書いていない（内積を使っていない） |
| $A_N = \langle D_s, E_N\rangle\iff N\in\{1, 2, 4\}\cup$ 素数 | **数値だけ**（N ≤ 40、観察 (8)） |

## 2. 数値照合（step264）

| 項目 | 内容 | 結果 |
|---|---|---|
| (1) | フォン・シュテルネックの式（整数、q ≤ 1000、0 ≤ n ≤ q）／$c_q(n) = c_q(\gcd(q,n))$・$c_q(n+q) = c_q(n)$（q ≤ 500）／0 にならない ⇔ q/g 平方因子なし、Part 240 の判定との一致／$(q,n) = 1$ で μ(q)／$q\mid n$ で φ(q)／補助の関数の乗法性（互いに素な $q_1q_2\le300$、n ≤ 300）／C(u, t) の閉じた式（N ≤ 200） | 501500/501500／125750/125750・125750/125750／501500/501500・501500/501500／304193/304193／2000/2000／384979/384979／8254/8254（3.0e-12） |
| (2) | $E_N = (1/N)J = \Phi([E_N])$、$[E_N](u,t) = \varphi(N/t)/N$（N ≤ 120） | 120/120（2.9e-15） |
| (3) | $D_sP_{u,v}$・$P_{u,v}D_s$・$Q_sP_{u,v}$・$P_{u,v}Q_s$／$Q_sQ_t$／$P + \sum Q_s = 1$／$(Q_t\delta_s)(s)$／$Q_s = 0\iff\varphi(N/s) = 1$（N ≤ 120）／$\#\{s : \varphi(N/s) = 1\} = 1 + [2\mid N]$（N ≤ 10000） | 33800/33800（4 種）／4038/4038／120/120／4038/4038／602/602／10000/10000（3.3e-15） |
| (4) | 生成元 $D_u$・$E_N$ が span{P_{s,t}, Q_s (s ∈ S′)} に入る／その d² + #S′ 個が一次独立／Ψ(1, 1) = 1／乱数の (M, b) で積を保つ（各 N で 3 組）（N ≤ 120）／基底どうしの積の表（N ≤ 60） | 120/120／120/120／120/120／360/360（相対 5.4e-14）／60/60 |
| (5) | 生成元から直交化で計算した $\dim\langle D_s, E_N\rangle = d^2 + d - 1 - [2\mid N]$（N ≤ 60） | 60/60 |
| (6) | 中心の次元 = 1 + #S′（N ≤ 60） | 60/60 |
| (7) | 対照：補正のない $d^2 + d - 1$ と (5) が食い違う N は、ちょうど偶数の N | 一致（30 個） |
| (8) | 観察（数値だけ）：$A_N$（すべての $D_s$・$E_s$ が生成）と ⟨D_s, E_N⟩ が一致する N（N ≤ 40） | 1, 2, 4 と素数にちょうど一致 |

- **実行は 2 回です。**
  - 1 回目（約 61 秒）は項目 (1)〜(7) で、すべて合格しました。
  - その後で中心を Lean にしたので、(6) の「数値だけ」の表示を外しました。次の候補のための観察 (8) も足して、2 回目を実行しました。2 回目は (1)〜(7) を保存済みの結果（`step264_cache.json`）から読み、(8) だけを計算しました（約 9 秒）。
  - `step264.log` は 2 回目のログです。1 回目のログは `step264_run1.log` に残しました。2 つの違いは (6) の表示と (8) と秒数の行だけです。
- (8) の次元の例：$\dim A_N$ = 20（N = 6）、19（N = 8）、12（N = 9）、50（N = 12）、25（N = 15）、100（N = 30）。⟨D_s, E_N⟩ はそれぞれ 18・18・11・40・19・70 です。
- **限界。**
  - (4) の積は、N > 60 では乱数の 3 組だけです（積の規則そのものは Lean で示した）。
  - (5) の生成元からの独立な計算は N ≤ 60 です。
  - (7) は式の確認のための対照です。

## 3. Lean（`PAG245.lean`、namespace `PAG.Part245`、PAG244 を import）

| 区分 | 項目 |
|---|---|
| 1. フォン・シュテルネックの式 | def `totientDivGcd`・`moebiusDivGcd`, `ramSum_gcd`, `ramSum_mod`, `ramSum_of_coprime`, `totientDivGcd_apply`, `moebiusDivGcd_apply`, `gcd_mul_of_coprime`, `mul_div_gcd_of_coprime`, `coprime_div_gcd_of_coprime`, `isMultiplicative_totientDivGcd`, `isMultiplicative_moebiusDivGcd`, `ramSum_mul_totient_primePow`, `ramSum_mul_totient`, `div_gcd_pos`, `ramSum_eq_div`, `ramSum_ne_zero_iff_squarefree`, `ramSum_of_dvd`, `ramMat_eq_closed` |
| 2. E_N と Q_s | def `shellDev`, `radialMatOp_add`, `radialMatOp_smul`, `radialMatOp_zero`, `radialMatOp_single`, `convL_geps_self_eq`, `shellDev_apply`, `mulLeft_dind_mul_shellTrans`, `shellTrans_mul_mulLeft_dind`, `shellDev_mul_shellTrans`, `shellTrans_mul_shellDev`, `shellDev_mul_shellDev`, `shellDev_single_apply`, `shellDev_eq_zero_iff` |
| 3. 空間全体の ⟨D_u, E_N⟩ | def `devSet`・`wholeMap`・`wholeHom`・`wholeAlgEquiv`, `dvd_of_mem_devSet`, `card_filter_totient_eq_one`, `card_devSet`, `sum_devSet_shellDev`, `shellAvg_add_sum_shellDev`, `radialMatOp_mul_shellDev`, `shellDev_mul_radialMatOp`, `shellDev_mul_shellDev_devSet`, `wholeMap_apply`, `wholeMap_one`, `wholeMap_mul`, `wholeHom_apply`, `shellAvg_mul_wholeMap`, `wholeMap_injective`, `shellTrans_mem_oneEAlg`, `radialMatOp_mem_oneEAlg`, `shellDev_mem_oneEAlg`, `radialMatOp_mem_range`, `shellDev_mem_range`, `mulLeft_dind_mem_range`, `range_wholeHom`, `wholeAlgEquiv_apply`, `toSubmodule_oneEAlg_self`, `finrank_oneEAlg_self`, `finrank_oneEAlg_self_add`, `finrank_oneEAlg_self_sub` |
| 4. 中心 | def `centerMap`, `wholeMap_smul_one`, `mem_center_oneEAlg_iff`, `centerMap_apply`, `centerMap_injective`, `mem_center_oneEAlg_iff_range`, `finrank_range_centerMap`, `finrank_range_centerMap_add` |

**使った PAG の結果**
- Part 201 の `dind`・`geps`・`dind_mul`・`card_dsh`（PAG205）。Part 203 の `Radial`（PAG207）
- Part 226 の `totientAF`・`totientAF_apply`・`totientAF_isMultiplicative`（PAG230）
- Part 228 の `convL_geps_mem`・`sum_mulLeft_dind`・`dind_eq_zero_of_not_dvd`（PAG232）
- Part 238 の `radialHom`（PAG242）
- Part 239 の `dind_natCast`・`radialBasis`・`conv_geps_self`・`shellTrans`・`shellTrans_apply`・`shellTrans_mul`・`radialMatOp`・`radialMatOp_mul`・`radialMatOp_injective`・`ramMat`（PAG243）
- Part 240 の `ramSum`・`ramSum_apply`・`isMultiplicative_ramSum`・`ramSum_primePow`・`ramSum_one`・`ramMat_eq_ramSum`・`shellAvg`・`radialMatOp_one_eq`・`shellAvg_mul_eq`・`shellAvg_mul_radialMatOp`・`shellAvg_apply_of_radial`・`oneEAlg`（PAG244）

**Mathlib・Lean から使った主なもの**
- 数論の関数：`ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers`・`IsMultiplicative.pmul`・`pmul_apply`・`isMultiplicative_moebius`・`moebius_ne_zero_iff_squarefree`・`moebius_apply_prime`・`moebius_apply_prime_pow`
- 自然数：`Nat.Coprime.gcd_mul`・`Nat.div_mul_div_comm`・`Nat.Coprime.coprime_div_left`・`coprime_div_right`・`Nat.totient_mul`・`Nat.totient_prime`・`Nat.totient_prime_pow`・`Nat.totient_eq_one_iff`・`Nat.dvd_prime_pow`・`Nat.pow_dvd_pow_iff_le_right`・`Nat.pow_div`・`Nat.gcd_rec`・`Nat.dvd_gcd_iff`・`Nat.eq_of_dvd_of_div_eq_one`・`Nat.div_div_self`
- 有限集合：`Finset.card_pair`・`Finset.card_filter_add_card_filter_not`・`Finset.sum_filter_of_ne`・`Finset.card_le_one`・`Fintype.sum_mul_sum`
- 代数と次元：`AlgHom.ofLinearMap`・`AlgEquiv.ofInjective`・`Subalgebra.equivOfEq`・`AlgHom.mem_range`・`Algebra.adjoin_le`・`LinearMap.finrank_range_of_inj`・`Module.finrank_prod`・`Module.finrank_matrix`・`Module.finrank_fintype_fun_eq_card`・`Subalgebra.finrank_toSubmodule`
- 中心と行列：`Matrix.center_eq_range`・`Semigroup.mem_center_iff`・`Matrix.scalar_apply`・`Matrix.smul_one_eq_diagonal`
- 線形写像：`LinearMap.toSpanSingleton`・`LinearMap.prodMap`・`LinearMap.mulLeft_zero_eq_zero`・`injective_iff_map_eq_zero`

**コンパイル**
- `PAG245` は 1 回目（約 6 秒）で、エラー・警告なしで通りました。
- docstring の番号を付け直して、2 回目もエラー・警告なしで通りました（約 6 秒）。付け直したのは、def `wholeAlgEquiv` に付けていた番号「3v」を外して後ろの 3w〜3z′ を 3v〜3z に詰めたことと、2a・4f・4g の文言です。
  - 2 回目の最初の指示は、`/usr/bin/time` がこの環境になかったので実行されていませんでした。.olean の時刻で気づき、bash の `time` でやり直しました。
- 公理は標準のもの（propext、Classical.choice、Quot.sound）か、その一部だけです。71 行のうち 4 行が一部だけです（`gcd_mul_of_coprime`・`mul_div_gcd_of_coprime`・`coprime_div_gcd_of_coprime`・`div_gcd_pos` は [propext, Quot.sound]）。
- 内容は試しのファイル T3 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble245.py`）。
- **試しのファイル（置き場所は `/home/claude/leanwork/scratch/t241`）。**
  - W0：import の温め（17 秒）と API の名前の確認。
  - T1（17 項目と定義 2 個、§1）：1 回目でエラー・警告なし（10 秒）。
  - T2（56 項目と定義 7 個、§1〜3）：エラー 2 件でした。
    - `shellTrans_mul_shellDev`：subst の後で 2 つの if（$P_{u,v}D_s$ と $P_{u,v}P_{s,s}$ の値）がまったく同じ形 `if v = v then P_{u,v} else 0` になりました。そのため 1 つ目の `rw [ite_eq_left rfl]` が両方を書き換え、2 つ目は当たる場所がありませんでした（1 件）。2 つ目を消しました。
    - `shellDev_single_apply`：`Pi.single (s : ZMod N) (1 : ℂ) y` の型が、依存関数の族として推論できませんでした（1 件）。`(Pi.single (s : ZMod N) (1 : ℂ) : ZMod N → ℂ) y` と型を書きました。
    - 直して通りました（5 秒）。
  - T3（63 項目と定義 8 個、§1〜4）：1 回目で通りました（6 秒）。docstring を直して再び通りました（6 秒）。
- **環境。** Mathlib の追加ビルドはありません。Part 240 の納品（15:01 ごろ）の後、Part 241 の開始時（15:26）にコンテナが再起動していました（起動時刻 15:26:02）。ファイルと .olean は残っていました。

## 4. 残る問い

1. **（次の候補）A_N と ⟨D_s, E_N⟩ の比較。**
   - 観察 (8)（数値だけ、N ≤ 40）は、$A_N = \langle D_s, E_N\rangle\iff N\in\{1, 2, 4\}\cup$ 素数 です。
   - Part 225 の $\dim A_N = \sum_pn_p^2$（Part 214 の式の形にしたのは Part 226）と、今回の $d^2 + d - 1 - [2\mid N]$ を比べて Lean にすることです。
   - $A_N$ で増える分の形（例：N = 8 で +1、N = 6 で +2、N = 15 で +6）を、単数群の指標の言葉で書けるかは確かめていません。
2. **中心そのものの次元。** `Subalgebra.center ℂ (oneEAlg N N)` の finrank を直接書くことです（Part 226 の注意のとおり、インスタンスの探索の上限に注意）。
3. **直交性。** P・$Q_s$ が自己共役であること（内積を使う。Part 225 の `EuclideanSpace` の形）。
4. **引き継ぎメモのほかの候補。** $C_N = \bigotimes_pC_{p^{v_p}}$ の PiTensorProduct の形、dilComm$_{q^k}$、$A_N$ のウェダーバーン成分の分配の形（Part 238 で数値だけ）、`tensEquiv` と `piTensEquiv` の比較、ほか。
