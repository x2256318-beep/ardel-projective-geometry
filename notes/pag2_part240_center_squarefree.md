# アデール射影幾何 2.0 — Part 240：中心のべき等元 $P = \sum_sP_{s,s}$ と、$E_s$ 1 つで足りる条件（ラマヌジャン和が 0 にならない条件）

2026-11-05。引き継ぎメモの次の候補（Part 239 で数値だけだった主張を Lean にすること）を進めました。候補の 3 つのうち 2 つ（$P$ の中心性と $E_s$ 1 つの判定）を Lean にしました。残りの 1 つ（空間全体の $\dim\langle D_s, E_N\rangle$）は数値だけのままです（§4）。

- **単数倍の平均（Lean）。** Part 239 の $P = \sum_{s\mid N}P_{s,s}$ は、単数倍の平均 $\frac1{\varphi(N)}\sum_aU_a$ に等しいことを示しました（`shellAvg_eq_unitAvg`）。
  - 鍵は軌道の数え上げです：$\sum_{a}F(ax) = \#\mathrm{Stab}(x)\cdot\sum_{y\in D_g}F(y)$（$g = \gcd(N,x)$、`sum_units_mul`）、$\#\mathrm{Stab}(x)\cdot\varphi(N/g) = \varphi(N)$（`card_stab_mul_totient`）。
- **中心のべき等元（Lean）。** $P$ は $A_N$ の中心のべき等元です（`shellAvg_mem_center`、`shellAvg_mul_self`）。$A_N$ の元は $U_a$ と可換なので、その平均 $P$ とも可換です。
  - $T\in A_N$ なら $PT = TP = \sum_{s,t}[T](s,t)\,P_{s,t}$ です（`shellAvg_mul_eq`）。つまり**角の代数 $PA_NP$ は、Part 239 の行列単位の代数（$\cong M_{d(N)}(\mathbb C)$）そのもの**です。動径のウェダーバーン成分を、$A_N$ の中で中心のべき等元で切り出したことになります。
  - $\mathrm{radialHom}\,T = 0\iff PT = 0$（`radialHom_eq_zero_iff`）。$Pf$ は動径関数で、動径関数 $f$ では $Pf = f$ です。
- **ラマヌジャン和（Lean）。** $c_q(n) = \sum_{e\mid q}\mu(e)\frac qe[\frac qe\mid n]$ を、Mathlib の `ArithmeticFunction` の積 $\mu * (d\mapsto d[d\mid n])$ として定義しました（`ramSum`）。
  - $q$ について乗法的です（`isMultiplicative_ramSum`）。Part 239 の $C(u,t) = c_{N/t}(u)$ です（`ramMat_eq_ramSum`）。
  - $c_{p^k}(n) = p^k[p^k\mid n]-p^{k-1}[p^{k-1}\mid n]$、$c_q(1) = \mu(q)$ です。
  - **$c_q(n)\ne0\iff$ $q$ のどの素因数 $p$ でも $p^{v_p(q)-1}\mid n$** です（`ramSum_ne_zero_iff`）。
- **$E_s$ 1 つの判定（Lean）。** すべての $D_u$ と 1 つの $E_s$（$s\mid N$）だけで動径関数の空間の上の全行列環が出るのは、**$N/s$ が平方因子をもたないときちょうど**です（`radialHom_oneE_surjective_iff`）。
  - 平方因子をもたなければ $[E_s]$ の成分はどれも 0 でなく、$X_{u,t} = [E_s](u,t)^{-1}D_uE_sD_t$ が行列単位になります（`toMatrix_oneETrans`）。
  - 平方因子をもてば $\varepsilon_s(1) = c_{N/s}(1)/N = \mu(N/s)/N = 0$ です。そのため $\langle D_u, E_s\rangle$ のどの元でも、行列の $(1,t)$ 成分（$t\ne1$）は 0 になります（`oneEAlg_apply_one_eq_zero`）。
- **限界（正直な注記）。**
  - $P$ が「直交」射影であることは、$P^2 = P$・像が動径関数・動径関数で恒等、の形で示しました。自己共役であることは書いていません。
  - 空間全体の $\dim\langle D_s, E_N\rangle = d(N)^2+d(N)-1-[2\mid N]$（Part 239 の (8)）は数値だけのままです。
- **やり直し。** 試しのファイル T1〜T3 を 3 回コンパイルしました。T1 でエラー 3 件（集合の内包表記になった所属と、`push_cast` の割り算の書き換え）があり、T2 で通りました（§3）。
- **環境。** Mathlib の追加ビルドはありません。開始時（14:36）にコンテナが再起動していました。

成果物は次のとおりです。
- `PAG244.lean`：41 項目。sorry 0・警告 0 です。
  - 定義 6 個は項目に数えません。
  - 出力は `PAG244.out`（#print axioms 47 行）。
- 照合用の `step263.py`：ログは `step263.log` です。

xlsx の集計は 2970 項目になりました（手順 260）。

## 0. 結論

**記号**（Part 239 と同じ）
- $D_t = \{x : \gcd(N,x) = t\}$、$1_{D_t}$ = `dind N t`、$\varepsilon_s = \mathcal F^{-1}1_{D_s}$、$E_sf = \varepsilon_s\star f$、$D_sf = 1_{D_s}f$。$A_N$ = `shellAlg N`。
- $U_af(x) = f(ax)$（Part 214 の `dil`）。$\mathrm{Stab}(x) = \{a\in(\mathbb Z/N)^\times : ax = x\}$。
- $R$ = 動径関数の空間、$[T](u,t) = (T1_{D_t})(u)$、$P_{s,t} = \frac N{\varphi(N/t)}D_sE_ND_t$、$\Phi(M) = \sum M_{st}P_{s,t}$（Part 239）。
- $P = \sum_{s\mid N}P_{s,s}$（`shellAvg`）、$\frac1{\varphi(N)}\sum_aU_a$（`unitAvg`）。
- $c_q(n)$ = `ramSum n q`。$\langle D_u, E_s\rangle$ = `oneEAlg N s`。

| 定理 | 主張 |
|---|---|
| `card_fiber_eq`, **`sum_units_mul`**, **`card_stab_mul_totient`** | 軌道の上でファイバーの大きさは一定。$\sum_aF(ax) = \#\mathrm{Stab}(x)\sum_{D_g}F$。$\#\mathrm{Stab}(x)\varphi(N/g) = \varphi(N)$ |
| `unitAvg_apply`, `shellAvg_apply`, **`shellAvg_eq_unitAvg`** | どちらの値も $D_{\gcd(N,x)}$ の上の平均。$P = \frac1{\varphi(N)}\sum_aU_a$ |
| `shellAvg_mem`, `radialMatOp_one_eq`, `shellAvg_mul_self` | $P\in A_N$、$P = \Phi(1)$、$P^2 = P$ |
| `radial_apply_of_mem`, `commute_shellAvg`, **`shellAvg_mem_center`** | $A_N$ の元は動径関数を保つ。$P$ は $A_N$ の中心の元 |
| **`shellAvg_mul_eq`**, `mul_shellAvg_eq`, `shellAvg_mul_radialMatOp` | $PT = TP = \Phi([T])$（$T\in A_N$）、$P\Phi(M) = \Phi(M)$ |
| `radialHom_eq_zero_iff`, `radial_shellAvg_apply`, `shellAvg_apply_of_radial` | $\mathrm{radialHom}\,T = 0\iff PT = 0$。$Pf\in R$、$f\in R$ なら $Pf = f$ |
| `dvdWeight_apply`, `isMultiplicative_dvdWeight`, `ramSum_apply`, **`isMultiplicative_ramSum`** | $d\mapsto d[d\mid n]$ は乗法的。$c_q(n) = \sum_{e\mid q}\mu(e)\frac qe[\frac qe\mid n]$ は $q$ について乗法的 |
| `natCast_mul_geps_eq_ramSum`, `ramMat_eq_ramSum` | $N\varepsilon_t(u) = c_{N/t}(u)$、$C(u,t) = c_{N/t}(u)$ |
| `sum_divisors_primePow_moebius_int`, `ramSum_primePow`, `ramSum_one` | 素冪の式、$c_q(1) = \mu(q)$ |
| `ramSum_primePow_ne_zero`, `ramSum_ne_zero`, **`ramSum_ne_zero_iff`** | $c_q(n)\ne0\iff\forall p\mid q,\ p^{v_p(q)-1}\mid n$ |
| `ramSum_ne_zero_of_squarefree`, `ramSum_div_ne_zero`, `toMatrix_E_ne_zero` | $N/s$ が平方因子をもたなければ $c_{N/s}(u)\ne0$、$c_{N/t}(s)\ne0$、$[E_s]$ の成分はどれも 0 でない |
| `oneEAlg_le`, `oneETrans_mem`, `oneETrans_dind`, `toMatrix_oneETrans`, `radialHom_oneE_surjective` | $\langle D_u, E_s\rangle\subseteq A_N$。$X_{u,t}1_{D_r} = [t = r]1_{D_u}$、$[X_{u,t}] = E_{ut}$。平方因子なしなら全射 |
| `oneEAlg_apply_one_eq_zero`, `not_radialHom_oneE_surjective`, **`radialHom_oneE_surjective_iff`** | 平方因子ありなら $(T1_{D_t})(1) = 0$（$t\ne1$）で全射にならない。判定 ⇔ |

定義は `unitAvg`・`shellAvg`・`dvdWeight`・`ramSum`・`oneEAlg`・`oneETrans` です。

**証明の筋**
1. **軌道の数え上げ。**
   - $y$ と $x$ が同じ殻にあれば $y = bx$ となる単数 $b$ があります（Part 203 の `exists_unit_mul_gcd` を 2 回）。$a\mapsto b^{-1}a$ が $\{a : ax = y\}$ と $\{a : ax = x\}$ の対応です（Mathlib の `Finset.card_nbij'`）。違う殻なら $ax = y$ となる $a$ はありません（`gcd_val_unit_mul`）。
   - $\sum_aF(ax) = \sum_y\#\{a : ax = y\}F(y)$ で、和が $\#\mathrm{Stab}(x)\sum_{D_g}F$ になります。$F = 1$ と $\#D_g = \varphi(N/g)$（Part 201 の `card_dsh`）から $\#\mathrm{Stab}(x)\varphi(N/g) = \varphi(N)$。
   - これで単数倍の平均の値は $\frac1{\varphi(N/g)}\sum_{D_g}f$ になり、Part 239 の $P$ の値（$D_g$ の上の平均）と一致します。
2. **中心性と角の代数。**
   - $T\in A_N$ は $U_a$ と可換（Part 214 の `shellAlg_comm_dil`）なので $T$ は $\frac1{\varphi(N)}\sum_aU_a = P$ と可換です。
   - $TP f = T\bigl(\sum_t(\text{平均}_t f)1_{D_t}\bigr) = \sum_t(\text{平均}_tf)\sum_s[T](s,t)1_{D_s} = \Phi([T])f$。$T1_{D_t}$ が動径関数で、Part 239 の `radial_eq_sum` で展開できるためです。
3. **ラマヌジャン和。**
   - $d\mapsto d[d\mid n]$ が乗法的なこと（互いに素なら $ab\mid n\iff a\mid n\wedge b\mid n$）と、$\mu$ の乗法性から、積 $\mu * (\cdot)$ は乗法的です（Mathlib の `IsMultiplicative.mul`）。
   - 素冪では約数 $p^m$ のうち $\mu\ne0$ は $m = 0,1$ だけで、$c_{p^k}(n) = p^k[p^k\mid n]-p^{k-1}[p^{k-1}\mid n]$。これが 0 でない ⇔ $p^{k-1}\mid n$。
   - 一般の $q$ では `multiplicative_factorization` で素冪の積にし、積が 0 でない ⇔ どの因子も 0 でない。
4. **$E_s$ 1 つの判定。**
   - $[E_s](u,t) = C(s,t)C(u,s)/N = c_{N/t}(s)\,c_{N/s}(u)/N$（Part 239）。$N/s$ が平方因子をもたなければ、$c_{N/s}(u)$ は $v_p(N/s)-1 = 0$ から、$c_{N/t}(s)$ は $v_p(N/t)-1\le v_p(N)-1\le v_p(s)$ から 0 でありません。
   - そのとき $X_{u,t}$ の行列は $E_{ut}$ で、$\sum_{u,t}S_{ut}X_{u,t}$ が $S$ の原像です。
   - 平方因子をもてば $\varepsilon_s(1) = \mu(N/s)/N = 0$。生成元はどれも $(T1_{D_t})(1) = 0$（$t\ne1$）を満たし、和・スカラー・積で保たれます（積は $y1_{D_t}$ を動径関数として展開）。行列単位 $E_{1N}$ はこれを満たさないので、全射になりません。

**例**
- $N = 12$、$x = 2$：$g = 2$、$\mathrm{Stab}(2) = \{1, 7\}$（$a\equiv1\pmod 6$）で、$2\cdot\varphi(6) = 4 = \varphi(12)$ です。
- $c_{12}(n)$：$12 = 2^2\cdot3$ なので $c_{12}(n)\ne0\iff2\mid n$ です。$u = 1, 2, 3, 4, 6, 12$ で $c_{12}(u) = 0, 2, 0, -2, -4, 4$ です（$C_{12}$ の $t = 1$ の列 $C(u,1)$）。
- $N = 12$：$E_s$ 1 つで足りるのは $s = 12, 6, 4, 2$（$N/s = 1, 2, 3, 6$）です。$s = 3$（$N/s = 4$）では $C(1,3) = c_4(1) = \mu(4) = 0$ で、$[E_3]$ の 1 行目が 0 になります。$s = 1$（$N/s = 12$）でも $c_{12}(1) = \mu(12) = 0$ で同じです。

**読み取れること**
- 動径のウェダーバーン成分は、$A_N$ の中心のべき等元 $P = \frac1{\varphi(N)}\sum_aU_a$ で切り出され、$PA_N = \Phi(M_{d(N)}(\mathbb C))$ です。$A_N$ の元が動径関数の上で 0 であることと、$P$ で消えることは同じです。
- $E$ の族の 1 つの元 $E_s$ と $D$ の族が「一般の位置」にあるかは、ラマヌジャン和 $c_{N/s}$・$c_{N/t}(s)$ が 0 にならないかで決まり、結局 $N/s$ が平方因子をもたないかで決まります。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| $\#\mathrm{Stab}(x)\cdot\varphi(N/\gcd(N,x)) = \varphi(N)$、軌道の和の式 | **正しい（`card_stab_mul_totient`、`sum_units_mul`）**。数値でも 20100/20100・7260/7260 |
| $P = \frac1{\varphi(N)}\sum_aU_a$ | **正しい（`shellAvg_eq_unitAvg`）**。数値でも 120/120（Part 239 では数値だけ） |
| $P^2 = P$、$Pf\in R$、$f\in R$ で $Pf = f$ | **正しい（`shellAvg_mul_self`、`radial_shellAvg_apply`、`shellAvg_apply_of_radial`）** |
| $P$ は $A_N$ の中心の元 | **正しい（`shellAvg_mem_center`）**。数値でも乱数の元で 180/180（Part 239 では数値だけ） |
| $P$ は直交射影（自己共役） | 書いていない（Part 239 の数値では直交射影と一致） |
| $PT = TP = \Phi([T])$（角の代数）、$\mathrm{radialHom}\,T = 0\iff PT = 0$ | **正しい（`shellAvg_mul_eq`、`mul_shellAvg_eq`、`radialHom_eq_zero_iff`）**。数値でも 180/180 |
| $c_q(n)$ は $q$ について乗法的、素冪の式、$c_q(1) = \mu(q)$ | **正しい（`isMultiplicative_ramSum`、`ramSum_primePow`、`ramSum_one`）**。数値でも 27520/27520・64462/64462・1000/1000 |
| $c_q(n)\ne0\iff\forall p\mid q,\ p^{v_p(q)-1}\mid n$ | **正しい（`ramSum_ne_zero_iff`）**。数値でも 90300/90300 |
| $N\varepsilon_t(u) = c_{N/t}(u)$ | **正しい（`natCast_mul_geps_eq_ramSum`）**。数値でも 120497/120497。直接の和 $\sum_be(bn/q)$ とも 40200/40200 |
| $\langle D_u, E_s\rangle$ の元を $R$ に制限すると全行列環のすべてが出る ⇔ $N/s$ が平方因子をもたない | **正しい（`radialHom_oneE_surjective_iff`）**。数値でも 1767/1767（Part 239 では数値だけ）。$[X_{u,t}] = E_{ut}$ は 20559/20559、平方因子ありの $(1,t)$ 成分 = 0 は 488/488 |
| 空間全体の $\dim\langle D_s, E_N\rangle = d^2+d-1-[2\mid N]$ | **数値だけ**（Part 239 の (8)、$N\le60$ で 60/60） |

## 2. 数値照合（step263）

| 項目 | 内容 | 結果 |
|---|---|---|
| (1) | $\#\mathrm{Stab}(x)\varphi(N/g) = \varphi(N)$（$N\le200$、すべての $x$）／$\sum_aF(ax) = \#\mathrm{Stab}(x)\sum_{D_g}F$（$N\le120$、乱数の $F$） | 20100/20100／7260/7260（7.4e-13） |
| (2) | $P = \frac1{\varphi(N)}\sum_aU_a$、$P^2 = P$、$Pf$ は動径、動径 $f$ で $Pf = f$（$N\le120$） | 120/120（2.7e-15） |
| (3) | $A_N$ の乱数の元 $T$（生成元の長さ 4 までの語の乱数の一次結合、各 $N$ で 3 個）で $PT = TP = \Phi([T])$、$T_0 = T-\Phi([T])$ で $[T_0] = 0$・$PT_0 = 0$（$N\le60$） | 180/180（2.3e-14） |
| (4) | $c_q(n)$：クルイフェルの式 = 直接の和（$q\le200$、$0\le n<2q$）／乗法性（互いに素で $q_1q_2\le300$、$n$ は 0〜300 の 7 おき）／素冪の式（$p^k\le1000$、$n$ は 0〜1000 の 3 おき）／$c_q(1) = \mu(q)$（$q\le1000$）／0 にならない判定（$1\le q\le300$、$0\le n\le300$） | 40200/40200（1.4e-11）／27520/27520／64462/64462／1000/1000／90300/90300 |
| (5) | $N\varepsilon_t(u) = c_{N/t}(u)$（DFT で計算した $\varepsilon$、$N\le200$） | 120497/120497（4.4e-12） |
| (6) | 平方因子なし：$[X_{u,t}] = E_{ut}$（$N\le120$）／平方因子あり：生成した代数の基底のすべての元で $(1,t)$ 成分 = 0（$N\le300$）／判定（$N\le300$、すべての $s$） | 20559/20559（7.2e-12）／488/488／1767/1767 |
| (7) | 対照：$E_s|_R$ だけ（$D_u$ なし）では全行列環にならない（$2\le N\le120$） | 601/601 |

- 実行は 1 回（約 83 秒）で、すべて合格しました。項目ごとの結果を `step263_cache.json` に保存する形です（再起動はありませんでした）。
- **限界。** (3) の $A_N$ の元は乱数で作った 3 個ずつです。(7) は自明な対照です（$E_s|_R$ は階数 1 の射影なので、生成する代数は 2 次元以下）。

## 3. Lean（`PAG244.lean`、namespace `PAG.Part244`、PAG243 を import）

| 区分 | 項目 |
|---|---|
| 1. 軌道と単数倍の平均 | def `unitAvg`・`shellAvg`, `card_fiber_eq`, `sum_units_mul`, `card_stab_mul_totient`, `unitAvg_apply`, `shellAvg_apply`, `shellAvg_eq_unitAvg` |
| 2. 中心のべき等元 | `shellAvg_mem`, `radialMatOp_one_eq`, `shellAvg_mul_self`, `radial_apply_of_mem`, `commute_shellAvg`, `shellAvg_mem_center`, `shellAvg_mul_eq`, `mul_shellAvg_eq`, `shellAvg_mul_radialMatOp`, `radialHom_eq_zero_iff`, `radial_shellAvg_apply`, `shellAvg_apply_of_radial` |
| 3. ラマヌジャン和 | def `dvdWeight`・`ramSum`, `dvdWeight_apply`, `isMultiplicative_dvdWeight`, `ramSum_apply`, `isMultiplicative_ramSum`, `natCast_mul_geps_eq_ramSum`, `ramMat_eq_ramSum`, `sum_divisors_primePow_moebius_int`, `ramSum_primePow`, `ramSum_one`, `ramSum_primePow_ne_zero`, `ramSum_ne_zero`, `ramSum_ne_zero_iff` |
| 4. $E_s$ 1 つの判定 | def `oneEAlg`・`oneETrans`, `ramSum_ne_zero_of_squarefree`, `ramSum_div_ne_zero`, `toMatrix_E_ne_zero`, `oneEAlg_le`, `oneETrans_mem`, `oneETrans_dind`, `toMatrix_oneETrans`, `radialHom_oneE_surjective`, `oneEAlg_apply_one_eq_zero`, `not_radialHom_oneE_surjective`, `radialHom_oneE_surjective_iff` |

**使った PAG の結果**
- Part 201 の `dind`・`geps`・`dind_mul`・`card_dsh`（PAG205）、Part 203 の `Radial`・`exists_unit_mul_gcd`・`gcd_val_unit_mul`・`dind_radial`・`geps_radial`（PAG207）
- Part 214 の `dil`・`dil_apply`・`radial_iff_dil`・`shellAlg`・`shellAlg_comm_dil`（PAG218）、Part 228 の `convL_geps_mem`・`mulLeft_dind_mem`（PAG232）
- Part 238 の `radialHom`（PAG242）
- Part 239 の `dind_natCast`・`radial_apply_eq`・`radial_eq_sum`・`radialBasis`・`toMatrix_radialHom`・`conv_geps_dind`・`toMatrix_E`・`shellTrans`・`shellTrans_apply`・`shellTrans_mem`・`radialMatOp`・`radialMatOp_one`・`radialMatOp_mul`・`radialMatOp_injective`・`sum_shellTrans_self_radial`・`ramMat`・`natCast_mul_geps`・`toMatrix_E_eq_ramMat`（PAG243）

**Mathlib・Lean から使った主なもの**
- `ArithmeticFunction`・`ArithmeticFunction.mul_apply`・`IsMultiplicative`・`IsMultiplicative.mul`・`isMultiplicative_moebius`・`IsMultiplicative.multiplicative_factorization`・`moebius_apply_prime_pow`・`moebius_eq_zero_of_not_squarefree`・`Nat.sum_divisorsAntidiagonal`
- `Finset.card_nbij'`・`Finset.sum_ite`・`Finset.sum_comm`・`Finset.filter_eq_empty_iff`・`ZMod.card_units_eq_totient`・`Subalgebra.mem_center_iff`
- `Squarefree.natFactorization_le_one`・`Nat.factorization_div`・`Finsupp.tsub_apply`・`Nat.ordProj_dvd`・`Nat.support_factorization`・`Finset.prod_ne_zero_iff`・`Nat.pow_lt_pow_right`・`Algebra.adjoin_induction`

**コンパイル**
- `PAG244` は 1 回目（約 6 秒）で、エラー・警告なしで通りました。公理は標準のもの（propext、Classical.choice、Quot.sound）か、その一部だけです。47 行のうち 3 行が一部だけです（`dvdWeight`・`dvdWeight_apply` は [propext]、`isMultiplicative_dvdWeight` は [propext, Quot.sound]）。
- 内容は試しのファイル T3 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble244.py`）。
- **試しのファイル（置き場所は `/home/claude/leanwork/scratch/t240`）。**
  - W0：import の温め（17 秒）。W1：API の名前の確認。
  - T1（38 項目）：エラー 3 件、警告 4 件でした。
    - `card_fiber_eq` の `Set.MapsTo` のゴールで、`simp only` に `Finset.coe_filter` を入れたため所属が集合の内包表記 $\{a\mid\cdots\}$ になり、続く `rw [Units.val_mul]` が当たりませんでした（2 件）。`Finset.mem_coe`・`Finset.mem_filter` だけにしました。
    - `natCast_mul_geps_eq_ramSum` で、`push_cast` が文脈の整除の仮定から `Nat.cast_div` を使い、$\uparrow(N/t/e)$ を $\uparrow N/\uparrow t/\uparrow e$ に書き換えたため、`ring` が閉じませんでした（1 件）。`Int.cast_sum` などの `simp only` にしました。
    - 警告は未使用の simp の引数 4 件でした。
  - T2：エラー・警告なしで通りました（5 秒）。
  - T3：3 項目を足して通りました（5 秒）。判定の逆向きを含む `ramSum_ne_zero_iff`、$Pf$ が動径関数であること（`radial_shellAvg_apply`）、動径関数で $Pf = f$（`shellAvg_apply_of_radial`）です。
- **環境。** Mathlib の追加ビルドはありません。Part 239 の納品（14:30 ごろ）の後、Part 240 の開始時（14:36）にコンテナが再起動していました（起動時刻 14:36:01）。ファイルと .olean は残っていました。

## 4. 残る問い

1. **（次の候補）空間全体の $\langle D_s, E_N\rangle$ の構造。** $\langle D_s, E_N\rangle = \{\Phi(M)+\sum_sb_s(D_s-P_{s,s})\}$ と $\dim = d(N)^2+d(N)-1-[2\mid N]$（Part 239 の数値 (8)）。今回の中心のべき等元 $P$ で空間を $R\oplus\ker P$ に分ければ、$\ker P$ の上では $E_N = 0$ です（$E_N$ は全体の和しか見ないため）。$D_s-P_{s,s}$ は $\#D_s = \varphi(N/s)\ge2$ のときだけ 0 でありません。`Nat.totient_eq_one_iff`（$\varphi(m) = 1\iff m = 1, 2$）が使えます。
2. **ラマヌジャン和の閉じた式。** $c_q(n) = \mu(q/g)\varphi(q)/\varphi(q/g)$（$g = \gcd(q,n)$）を、今回の乗法性と素冪の式から示すこと。
3. **引き継ぎメモのほかの候補。** $C_N = \bigotimes_pC_{p^{v_p}}$ の PiTensorProduct の形、dilComm$_{q^k}$、$A_N$ のウェダーバーン成分の分配の形、`tensEquiv` と `piTensEquiv` の比較、ほか。
