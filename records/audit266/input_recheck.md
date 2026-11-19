# 再照合の入力（Part 262、PAG266.lean。独立照合の後の直し）

§A は独立照合の照合者の出力の全文。§B は直した後の PAG266.lean の全文（docstring と冒頭の説明を含む）。§C は形式文の差分（独立照合の前と後、docstring を除く）。§D は使う定義と補題の文（独立照合の入力と同じものに、照合者が入力になかったと申告した定義を足した）。

## §A 独立照合の出力（全文）

# 照合の成果物：Part 262（PAG266.lean）の形式文 — 独立照合の出力の全文（2026-11-20）

## 0. 前提と読めなかった定義

- 記号：$p$ は素数、$n \ge 0$、$N = p^{n+1}$ とします。$e(t) = \exp(2\pi i t)$ と書きます。
- 入力に定義がなかったもの：`push`、`shellEmb`、`projFunEquiv`、`compat_extS`、`compat_extN`。
  - 殻 0 のケット `ket K 0 c χ` は、docstring の「$|S_u|^{-1/2}\,\iota_{u,*}(\chi\circ\pi_u)$」から、$\mathbb Z/p^K$ 上の関数 $x \mapsto \varphi(p^K)^{-1/2}\,\chi(x \bmod p^{n+1})$（$\varphi(p^K) = p^{K-1}(p-1)$）と読みました。
  - 下の具体計算のうち、定理 4・5 に関わる部分はこの読みに依存します（確信度：中）。
- 計算はすべて手計算です。コードは実行していません。

## 1. 逆翻訳

### 共通の定義

- **ディリクレ指標**：法 $N$ の乗法的な写像 $\chi : \mathbb Z/N \to \mathbb C$ で、$\chi(1) = 1$、単数でない元では 0 になるもの。積 $\chi_1\chi_2$ は値ごとの積です。
  - 原始的：導手がちょうど $N$ であること。
  - 偶：$\chi(-1) = 1$。奇：$\chi(-1) = -1$。
- **ガウス和**：$\tau(\chi) = \sum_{a \bmod N} \chi(a)\, e(a/N)$。
- **$\sqrt N$**：$N$ の正の実数の平方根を複素数とみなしたもの。$\hat J$ と $W$ の両方で同じものを使っています。
- **J（ヤコビ和）**：$J(\chi_1,\chi_2) = \sum_{x \bmod N} \chi_1(x)\,\chi_2(1-x)$。
- **Jhat**：$\hat J = J/\sqrt N$。
- **rootNum**：$W(\chi) = \tau(\chi)/(\varepsilon_\chi\sqrt N)$。$\varepsilon_\chi$ は、$\chi$ が偶なら 1、偶でない（奇の）なら $i$ です。
- **P1F($M$)**：$\mathbb Z/M$ 上の複素数値関数の組 $(f_S, f_N)$。第 1 成分を南座標の関数、第 2 成分を北座標の関数と読みます。
- **反転 W**：$(f_S, f_N) \mapsto (f_N, f_S)$。
- **extS($h$)**：$(h,\ y \mapsto h(y^{-1})$（$y$ が単数のとき）、それ以外は 0$)$。
- **extN($h$)**：$(x \mapsto h(x^{-1})$（$x$ が単数のとき）、それ以外は 0$,\ h)$。
- **畳み込み**：$(f \star g)(x) = \sum_y f(y)\, g(x-y)$。
- **BS**：$B_S(F,G) = \mathrm{extS}(F_S \star G_S)$。南座標で畳み込み、北の内部（単数でない $y$）は 0 にします。
- **BN**：$B_N(F,G) = W(B_S(WF, WG)) = \mathrm{extN}(F_N \star G_N)$。
- **kS**：$\mathrm{kS}(K,0,n+1,\chi) = \mathrm{extS}(\text{上の殻 0 のケット})$。ここで $K \ge n+1$ です。
- **ProjLine($M$)**：$sa + tb = 1$ となる $s, t$ が存在する組 $(a,b) \in (\mathbb Z/M)^2$ を、単数倍 $(a,b) \sim (ua, ub)$ で割った集合。$P^1(\mathbb Z/M)$ に当たります。
- **BSproj、BNproj、ketS_proj**：`projFunEquiv`（$P^1(\mathbb Z/p^K)$ 上の関数と、貼り合わせ条件を満たす組との対応と読みました）で、BS・BN・kS を射影直線上の関数に移したものです。

### 定理 1（conj_Jhat_eq_gauss）

- 仮定：$p$ は素数、$n \ge 0$。$\chi_1, \chi_2$ は法 $N = p^{n+1}$ のディリクレ指標で、$\chi_1$、$\chi_2$、$\chi_1\chi_2$ がいずれも原始的。
- 結論：$\overline{\hat J(\chi_1,\chi_2)} = \sqrt N \cdot \tau(\chi_1\chi_2) / (\tau(\chi_1)\,\tau(\chi_2))$。

### 定理 2（conj_Jhat_eq_rootNum）

- 仮定：定理 1 と同じ。
- 結論：$\overline{\hat J} = s \cdot W(\chi_1\chi_2) / (W(\chi_1)\,W(\chi_2))$。
  - $\chi_1$、$\chi_2$ の少なくとも一方が偶なら $s = 1$、両方が奇なら $s = -1$。

### 定理 3（conj_Jhat_sq_eq_rootNum）

- 仮定：定理 1 と同じ。
- 結論：$\overline{\hat J}^{\,2} = \bigl(W(\chi_1\chi_2) / (W(\chi_1)W(\chi_2))\bigr)^2$。

### 定理 4（equator_intertwine_rootNum）

- 仮定：定理 1 の仮定に加えて、$K \ge n+1$。
- 準備：$F_i = \mathrm{kS}(K,0,n+1,\chi_i)$ とします。これは $\mathbb Z/p^K$ 上の殻 0（単数、赤道）の南ケットで、法 $p^{n+1}$ の指標 $\chi_i$ を $\mathbb Z/p^K$ に引き戻したものです。
- 結論：組（南成分と北成分の両方）として $B_N(F_1,F_2) = \lambda \cdot B_S(F_1,F_2)$。ここで $\lambda = (W(\chi_1\chi_2)/(W(\chi_1)W(\chi_2)))^2$。
- 上の読みのもとで具体的に書くと、$f_i = \varphi^{-1/2}\chi_i\circ\pi$、$F_{i,N} = \varphi^{-1/2}\bar\chi_i\circ\pi$ で、次の 2 つの等式になります。
  - $\mathrm{extN}(F_{1,N} \star F_{2,N}) = \lambda\, \mathrm{extS}(f_1 \star f_2)$ の南成分どうし
  - 同じく北成分どうし

### 定理 5（equator_intertwine_proj_rootNum）

- 仮定：定理 4 の仮定に $1 \le K$ を加えたもの（$K \ge n+1$ から出るので、新しい制約ではありません）。
- 結論：$P^1(\mathbb Z/p^K)$ 上の関数として、定理 4 と同じ等式が成り立つ。
  - 南ケット $\psi_i$ の値は、点 $[x:1]$ で $f_i(x)$、$y$ が単数でない点 $[1:y]$ で 0 です。

## 2. 非空虚性の証人

### 仮定を満たす例があるかどうか

| $p$ | $n = 0$ | $n \ge 1$ |
|---|---|---|
| 2 | なし | なし |
| 3 | なし | あり |
| $\ge 5$ | あり | あり |

- **$p = 2$**：どの $n$ でも、5 定理とも仮定を満たす例がなく、空虚です。
  - 法 2 には原始指標がありません。法 4 の原始指標は $\chi_{-4}$ だけで、その 2 乗は自明です。
  - $k \ge 3$ では $(\mathbb Z/2^k)^\times \cong \{\pm1\}\times\langle 5\rangle$ です。原始的であることは $\chi(5)$ の位数がちょうど $2^{k-2}$ であることと同値です。$\chi(5) = \omega^a$（$a$ は奇数）どうしの積は指数が偶数になるので、原始的になりません。
  - 補足：$p = 2$ では、$x$ と $1-x$ が同時に単数になることがないので、すべての指標で $J = 0$ です。
- **$p = 3$, $n = 0$**：空虚です。非自明な指標は Legendre 記号だけで、その 2 乗は自明です。
- **$p$ が奇数で $n \ge 1$**：$\omega$ を $(\mathbb Z/p^{n+1})^\times$ の生成元 $g$ に原始 $\varphi$ 乗根を当てる指標とします。$\omega^a$ が原始的であることは $p \nmid a$ と同値です。$a = b = 1$ で $p \nmid 2$ なので、常に例があります。
- **$n = 0$**：$\omega^a$ が原始的であることは $(p-1) \nmid a$ と同値です。$a$、$b$、$a+b$ がすべてこれを満たすことは、$p \ge 5$ と同値です。

### 定理 1・2・3：$p = 5$、$n = 0$、$\chi_1 = \chi_2 = \chi$

- 指標：$\chi$ は 4 次の指標で、$\chi(2) = i$、$\chi(4) = -1$、$\chi(3) = -i$。奇です。
- 積：$\chi^2$ は Legendre 記号で、偶かつ原始的です。
- 計算値：
  - $J(\chi,\chi) = (-i) + (-1) + (-i) = -1-2i$。$|J|^2 = 5$。
  - $\overline{\hat J} = (-1+2i)/\sqrt5$。
  - $\tau(\chi^2) = \sqrt5$（$5 \equiv 1 \pmod 4$ なので）。
- 定理 1 の内容：$\tau(\chi)^2 = \sqrt5\,(-1-2i)$。
- 定理 2 の内容：両方が奇なので $s = -1$。$W(\chi^2) = 1$、$W(\chi)^2 = \tau(\chi)^2/(i^2\cdot5) = (1+2i)/\sqrt5$ なので、$-W(\chi^2)/W(\chi)^2 = (-1+2i)/\sqrt5$ となり、左辺と一致します。
- 定理 3 の内容：両辺とも $(-3-4i)/5$。

### 定理 2 の他の場合分けにも例があること

- **一方が偶**：$p = 5$、$\chi_1 = \chi$（奇）、$\chi_2 = \chi^2$（偶）。積 $\chi^3$ は奇で原始的。
  - $J = 1+2i$、$\overline{\hat J} = (1-2i)/\sqrt5$、$s = 1$。
  - 右辺は $-5/\tau(\chi)^2 = (1-2i)/\sqrt5$ で一致します。
- **両方が偶**：
  - 例 1：$p = 7$、$\chi_1 = \chi_2 = $ 3 次の指標（生成元 3 に $\rho = e^{2\pi i/3}$ を当てる）。$J = 2 + 3\rho^2 = (1-3\sqrt3\,i)/2$、$|J|^2 = 7$。
  - 例 2：$p = 3$、$n = 1$、$\chi_1 = \chi_2 = \omega^2$（法 9）。

### $p = 3$、$n = 1$、$\chi_1 = \chi_2 = \omega$（法 9）

- 指標：生成元 2 に $z = e^{i\pi/3}$ を当てます。$\omega$ は奇で、積 $\omega^2$ は偶かつ原始的です。
- $x$ と $1-x$ がともに単数になるのは $x = 2, 5, 8$ で、どの項も $z^4$ です。したがって $J = 3e^{4\pi i/3}$。
- $\overline{\hat J} = e^{2\pi i/3}$、$s = -1$。
- $W(\omega^2)/W(\omega)^2 = -e^{2\pi i/3}$、その 2 乗は $e^{4\pi i/3}$。

### 定理 4：$p = 5$、$n = 0$、$K = 1$、$\chi_1 = \chi_2 = \chi$（上の読みのもとで）

- $\varphi = 4$。
- $B_S$：南成分は $x \mapsto \frac{-1-2i}{4}\chi^2(x)$、北成分は $y \mapsto \frac{-1-2i}{4}\chi^2(y)$。
- $B_N$：南北とも係数が $\frac{-1+2i}{4}$。
- どちらも $x = 0$ では 0 です。比は $\bar J/J = (-3-4i)/5 = \lambda$ です。
- 一般には、両辺が 0 でないことは $|J|^2 = N$ から出ます。したがって 0 = 0 型の空虚さはありません。

### 定理 4：$p = 3$、$n = 1$、$K = 2$、$\omega$

- $B_S$ の南成分は $(J/6)\,\omega^2$、$B_N$ の南成分は $(\bar J/6)\,\omega^2$。
- 比は $e^{-2\pi i/3} = e^{4\pi i/3}$ です。
- $K > n+1$ のときは、どちらの成分にも同じ因子 $p^{K-n-1}/\varphi(p^K)$ がかかるだけです。

### 定理 5

- 定理 4 と同じ例を $P^1(\mathbb Z/9)$ で見ます。点は 12 個あり、内訳は $[x:1]$ が 9 個、$y \in \{0,3,6\}$ の $[1:y]$ が 3 個です。
- 両辺は単数の点だけで 0 でなく、両極の点では 0 です。

## 3. 除去テスト

| 外す仮定 | 定理 1 | 定理 2 | 定理 3 | 定理 4 | 定理 5 |
|---|---|---|---|---|---|
| χ₁ の原始性 | 反例あり（n=0） | 反例あり（n=0） | 反例あり（n=0） | 反例あり（n=0） | 反例が移る（*） |
| χ₂ の原始性 | 対称（同上） | 同上 | 同上 | 同上 | 同上 |
| χ₁χ₂ の原始性 | 不要に見える | 不要に見える | 不要に見える | 反例あり（n=0, n=1） | 反例が移る（*） |
| 符号の場合分け | ― | 反例あり | ― | ― | ― |
| 2 乗 | ― | ― | 反例あり | 反例あり | 反例が移る（*） |

（*）`projFunEquiv` の逆が値ごとの対応で線形だという読みのもとでの話です。

### χ₁ の原始性を外す

反例：$p = 3$、$n = 0$、$\chi_1 = \chi_0$（自明な指標）、$\chi_2 = $ Legendre 記号。積は $\chi_2$ なので原始的です。

- 計算値：$J(\chi_0,\chi_2) = \chi_2(2) = -1$、$\tau(\chi_0) = -1$。
- 定理 1：左辺は $-1/\sqrt3$、右辺は $\sqrt3\,\tau_2/(-\tau_2) = -\sqrt3$ で、一致しません。
- 定理 2：$s = 1$。右辺は $1/W(\chi_0) = -\sqrt3$ で、左辺 $-1/\sqrt3$ と一致しません。
- 定理 3：左辺 $1/3$、右辺 $3$。
- 定理 4（$K = 1$）：
  - $\chi_0 \star \chi_2 = (0, -1, 1) = -\chi_2$ なので、$B_S = ((0,-\tfrac12,\tfrac12), (0,-\tfrac12,\tfrac12))$ です。
  - $B_N$ も同じ値になり、$B_N = B_S \ne 0$ です。
  - 形式文の $\lambda$ は $(-\sqrt3)^2 = 3$ なので、主張は偽になります。

ただし $n \ge 1$ では反例が出ず、両辺が 0 になって成り立ちます。

- 理由 1：法 $p^k$（$k \ge 2$）の原始的でない指標では $\tau = 0$ です。$a \bmod p^{k-1}$ でまとめると $\sum_t e(t/p) = 0$ が出るからです。
- 理由 2：$1 + p^{k-1}\mathbb Z$ の剰余類ごとの和を取る議論で $J = 0$ が出ます。さらに $\chi_1 \star \chi_2 \equiv 0$ です。
- そのため、定理 1〜3 の右辺は Lean の $x/0 = 0$ で 0 になり、定理 4 は $0 = 0\cdot 0$ になります。
- 結論として、この仮定が実際に効いているのは $n = 0$ の場合だけです（確信度：中〜高）。

### χ₂ の原始性を外す

- $J$、ガウス和の積、符号は、どれも $\chi_1 \leftrightarrow \chi_2$ について対称です。
- 反例は、上の例で $\chi_1$ と $\chi_2$ を入れ替えたものです。

### χ₁χ₂ の原始性を外す

**定理 1〜3：反例は作れませんでした。不要に見えます（確信度：中〜高、手計算による一般的な議論）。**

- $n = 0$ では、積が原始的でないのは $\chi_2 = \bar\chi_1$ の場合だけです。
  - このとき $J = -\chi(-1)$、$\tau(\chi)\tau(\bar\chi) = \chi(-1)\,p$、$\tau(\chi_0) = -1$。
  - 定理 1：両辺とも $-\chi(-1)/\sqrt p$。
  - 定理 2：$W(\chi)W(\bar\chi) = 1$、$W(\chi_0) = -1/\sqrt p$、$s = \chi(-1)$ なので、両辺が一致します。
  - 具体例：$p = 3$ で Legendre 記号 2 つ。両辺とも $1/\sqrt3$。
- $n \ge 1$ では、$\tau(\chi_1\chi_2) = 0$ です。また剰余類の議論で $J = 0$ です。
  - 具体例：法 9 の $\omega$ と $\omega^2$ では $J = z + z^5 - 1 = 0$。$\omega$ と $\bar\omega$ では $J = 1 + z^2 + z^4 = 0$。
  - よって両辺とも 0 です。

**定理 4：反例があります。**

- $p = 3$、$n = 0$、$K = 1$、$\chi_1 = \chi_2 = $ Legendre 記号の場合：
  - $\chi \star \chi = (-2, 1, 1)$ です。
  - $B_S = ((-1, \tfrac12, \tfrac12), (0, \tfrac12, \tfrac12))$、$B_N = ((0, \tfrac12, \tfrac12), (-1, \tfrac12, \tfrac12))$。
  - 形式文の $\lambda = (W(\chi_0)/W(\chi)^2)^2 = 1/3$ です。南成分は $x = 1$ で $\tfrac12 \ne \tfrac16$ となり、主張は偽です。
  - そもそも、この 2 つを結ぶスカラーは存在しません。南成分が $x = 0$ では $\lambda = 0$ を、単数では $\lambda = 1$ を要求するからです。
- $p = 3$、$n = 1$、$K = 2$、$\chi_1 = \omega$、$\chi_2 = \bar\omega = \omega^5$ の場合：
  - $W(\chi_0 \bmod 9) = 0$ なので $\lambda = 0$ です。
  - 一方、$B_N$ の北成分は 0 で $(\bar\omega \star \omega)(0)/6 = \omega(-1)\cdot 6/6 = -1 \ne 0$ です。
  - 補足：積が自明でない場合（$\omega$ と $\omega^2$）でも、$x = 3$ での畳み込みが $\overline{3\sqrt3\,i} \ne 0$ となり、反例になります。
- 解釈：この仮定が効く場所は、「単数でない点（両極）で両方の畳み込みが消える」という部分です。

### 符号の場合分けを外す（定理 2）

- 両方が奇の例で偽になります。
- $p = 5$ の 4 次の指標 $\chi$：左辺 $(-1+2i)/\sqrt5$、右辺（符号なし）$(1-2i)/\sqrt5$。
- 法 9 の $\omega$：左辺 $e^{2\pi i/3}$、右辺 $-e^{2\pi i/3}$。

### 2 乗を外す

- 定理 3 で 2 乗を外すと、符号を外した定理 2 と同じ文になります。同じ例で偽です。
- 定理 4 で 2 乗を外した場合：
  - $B_S \ne 0$ なので、スカラーは $\bar J/J = \overline{\hat J}^{\,2}$ に一意に決まります。
  - $p = 5$ の 4 次の指標では $(-3-4i)/5$ です。外した後の主張のスカラーは $(1-2i)/\sqrt5$ で、一致しません。
  - $s = 1$ の例（$p = 7$ の 3 次の指標。$\overline{\hat J} \ne 1$）でも偽になります。

## 4. 気づいた点

1. **空虚な範囲**：$p = 2$（すべての $n$）と $p = 3$、$n = 0$ では、5 定理とも空虚です。
   - これらの $p$ について何かを言っていると読んではいけません。
   - 「法 $p^{n+1}$ で一般に」と散文で書く場合は、この範囲を断る必要があります。
2. **仮定は必要十分ではない**：
   - 定理 1〜3 では、$\chi_1\chi_2$ の原始性は不要に見えます。
   - $\chi_1$、$\chi_2$ の原始性は $n = 0$ でだけ効きます。$n \ge 1$ では、Lean の $x/0 = 0$ と畳み込みの消滅によって 0 = 0 になります。
   - 定理 4・5 では、$\chi_1\chi_2$ の原始性が本当に必要です。
   - 偽の文ではありませんが、どの仮定が中身を運んでいるかは形式文からは読めません。
3. **符号 $s$ の頑健さ**：$s = i^{a_1+a_2-a_{12}}$ で、指数は常に 0 か 2 です。
   - $-1$ になるのは両方が奇のときだけです。形式文の条件の向き（「どちらかが偶」なら $+1$）は、この計算と合っています。
   - 加法指標の符号（$e^{\pm 2\pi i}$）を変えても、比は $\chi_{12}(-1)/(\chi_1(-1)\chi_2(-1)) = 1$ 倍で変わりません。
   - rootNum の $i^a$ を $(-i)^a$ に替えても、比は $(-1)^{\text{偶数}} = 1$ 倍で変わりません。
   - $s$ が消えるのは、rootNum から $i^a$ の因子そのものを外したとき（$\tau/\sqrt N$ にしたとき）だけです。
   - したがって、$s$ は規約の人工物ではなく、Jhat（$i^a$ なし）と rootNum（$i^a$ あり）の正規化の違いそのものから来ています。
4. **定理名と定理の中身**：
   - 定理 2 の名前は符号に触れていません。
   - 定理 3〜5 は符号の情報を捨てています。
   - 定理 4・5 は、Part 25・29 の補題のスカラー $\overline{\hat J}^{\,2}$ を定理 3 で書き換えただけです。絡み合いの中身（両極での消滅を含む）は、すべて Part 25・29 にあります。
5. **$\overline{\hat J} = 1/\hat J$**：$|\hat J| = 1$ なので、定理 1 は「$J = \tau_1\tau_2/\tau_{12}$ かつ $|J|^2 = N$」と同じ内容です。
6. **$\sqrt N$**：Jhat と rootNum は同じ正の実数の平方根（$N = p^{n+1}$ の実数へのキャスト）を使っていて、ずれはありません。
7. **$K$ と $n+1$ の関係**：
   - $\lambda$ は $K$ によりません。
   - `hK : 1 ≤ K` は `h` から出るので冗長です。
   - 扱っているのは殻 0（赤道）だけで、$\chi_1$、$\chi_2$ はどちらも導手がちょうど $p^{n+1}$ の場合だけです。導手の違う組や、ほかの殻は対象外です。
8. **2 チャートのモデルと射影直線の版**：
   - P1F には貼り合わせ条件を満たさない組も入ります。ただし BS・BN の出力は extS・extN なので、条件を満たします。
   - 定理 4 の組としての等式には、単数でない点で両辺が 0 であることが含まれます。これがスカラーの等式以上の中身で、積の原始性が効く場所です。
   - 定理 5 の意味は、入力にない `projFunEquiv` に依存します。それが点 $[x:1]$ と $[1:y]$ での値への正しい対応か、スカラー倍と可換か（線形か）は、この入力からは確かめられません。
9. **記号 W の衝突**：rootNum の docstring の $W(\chi)$（ルート数）と、Part 23 の `W`（反転、南北の入れ替え）が、定理 4 の中に同時に現れます。散文で書くときは取り違えに注意が要ります。

## ツールの使用と読んだ範囲

- Read を 1 回使い、`/home/claude/ardel-projective-geometry/records/audit266/input_formal.md` の全文（1〜319 行）を読みました。
- ほかのファイルは読んでいません。コードの実行とウェブの使用もしていません。

## §B 直した後の PAG266.lean の全文

```lean
/-
アーデル射影幾何 — Part 262（PAG266、短期層の小さいノート、2026-11-20）：舞台 P¹ の赤道の絡み合いを、貼り合わせの位相 𝔀 で書く

問いの出所：基礎文書の索引 1.4（舞台は P¹）と 2.4（「射影」の変換）の留保「`JH` は P¹ の上の作用素ではなく、P¹ のモデルと結ぶ Lean の文はない」。
- 推薦案 `pag2_p1_gluing_preregistration.md` §4 を、2026-11-20 06:55 に著者が採用した（「進めてください」）。
- 著者の言葉「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」の読みの材料（読みの地位は変えない）。

記号：
- N = p^(n+1)（p は素数）。e = stdAddChar、τ(χ) = gaussSum χ e。J = `PAG.Part7.J`（ヤコビ和）、Ĵ = J/√N（`PAG.Part25.Jhat`）。
- 𝔀(χ) = `PAG.Part256.rootNum` χ = τ(χ)/(i^a √N)（偶なら a = 0、奇なら a = 1）。原始指標でルート数であることは Lean の外。
- P¹(ℤ/p^K) の 2 チャートのモデル、南北の畳み込み B_S・B_N、赤道のケット |0, χ⟩ = `PAG.Part23.kS K 0 (n+1) h χ`（Part 19（PAG23））。

主な定理（χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標のとき）：
1. conj(Ĵ) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))（`conj_Jhat_eq_gauss`）。
2. conj(Ĵ) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))、s は χ₁ か χ₂ が偶なら 1、両方とも奇なら −1（`conj_Jhat_eq_rootNum`）。
3. conj(Ĵ)² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²（`conj_Jhat_sq_eq_rootNum`）。
4. 赤道のケットについて B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)（`equator_intertwine_rootNum`、2 チャートのモデル）。
5. 同じ式を、射影直線そのもの（`PAG.Part27.ProjLine`）の上の関数として（`equator_intertwine_proj_rootNum`、Part 25（PAG29）の `equator_intertwine_proj` から）。

読み（Lean の外）：χ の成分に 𝔀(χ) を掛ける作用素を U とすると、4 は赤道のケットの上で B_N(k₁, k₂) = U² B_S(U⁻²k₁, U⁻²k₂) と読める。
この条件を満たす位相は 𝔀 だけではない（単数 u と指標ごとの符号の分。数値と照合者の手計算、`pag2_p1_gluing_preregistration.md`）。
A1 は導かれない。p = 2（すべての n）と p = 3、n = 0 では原始指標の三つ組がなく、5 つの文は空（独立照合の指摘。p = 2 は Part 26（PAG30）の注意とも合う）。
仮定は必要十分ではない：1〜3 では χ₁χ₂ の原始性は不要に見え、χ₁・χ₂ の原始性が中身を運ぶのは n = 0 だけ（n ≥ 1 では両辺が 0 になる。独立照合の手計算）。
4・5 では χ₁χ₂ の原始性が要る（単数でない点で両辺が 0 になる部分）。4・5 は Part 21・25 の定理の係数の書き換えで、絡み合いの中身はそちらにある。

ラベル（見込み、照合の後に確定）：1〜3 は［既知］（積が原始的ならヤコビ和はガウス和の比、|τ|² = N。Conrad の定理 3.15・3.12）、4・5 は［再導出（小さい）］。新規候補なし。
-/
import PAG265
import PAG25
import PAG15
import PAG29

open Finset

namespace PAG.Part266

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

open PAG.Part25 (Jhat)
open PAG.Part256 (rootNum)

/-- **1. ガウス和による形**：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標なら、conj(Ĵ(χ₁, χ₂)) = √N·τ(χ₁χ₂)/(τ(χ₁)τ(χ₂))
（N = p^(n+1)、τ(χ) = gaussSum χ e、e = stdAddChar）。
p = 2（すべての n）と p = 3、n = 0 では仮定を満たす指標の組がなく、文は空（独立照合の指摘）。 -/
theorem conj_Jhat_eq_gauss (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    starRingEnd ℂ (Jhat χ₁ χ₂)
      = (Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℂ) * gaussSum (χ₁ * χ₂) ZMod.stdAddChar
          / (gaussSum χ₁ ZMod.stdAddChar * gaussSum χ₂ ZMod.stdAddChar) := by
  have hq : (0 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.out.pos _
  have hs : ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have hss : ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) ^ 2 = ((p ^ (n + 1) : ℕ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq.le]; push_cast; rfl
  have hN := PAG.Part25.normSq_J χ₁ χ₂ h₁ h₂ h₁₂
  have hJ : PAG.Part7.J χ₁ χ₂ ≠ 0 := by
    intro h; rw [h, map_zero] at hN; exact hq.ne' hN.symm
  have hmc : PAG.Part7.J χ₁ χ₂ * starRingEnd ℂ (PAG.Part7.J χ₁ χ₂) = ((p ^ (n + 1) : ℕ) : ℂ) := by
    rw [Complex.mul_conj, hN]; norm_cast
  have h1 := PAG.Part16.gaussSum_ne_zero h₁
  have h2 := PAG.Part16.gaussSum_ne_zero h₂
  have h12 := PAG.Part16.gaussSum_ne_zero h₁₂
  have hr := PAG.Part15.gauss_ratio_eq_jacobi χ₁ χ₂ h₁₂ ZMod.stdAddChar h12
  have hcJ : starRingEnd ℂ (PAG.Part7.J χ₁ χ₂)
      = ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) ^ 2 / PAG.Part7.J χ₁ χ₂ := by
    rw [hss, ← hmc]; field_simp
  rw [Jhat, map_div₀, Complex.conj_ofReal, hcJ, ← hr]
  field_simp

open Classical in
/-- **2. 𝔀 による形（2 乗を外した形）**：χ₁・χ₂・χ₁χ₂ が原始的なら、
conj(Ĵ(χ₁, χ₂)) = s·𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂))。符号 s は、χ₁ か χ₂ が偶なら 1、両方とも奇なら −1
（𝔀 = `PAG.Part256.rootNum`、τ/(i^a √N)）。符号 s は、Ĵ（i^a を含まない）と 𝔀（i^a を含む）の正規化の違いから来る
（加法指標の向きや i^a を (−i)^a に替えても変わらない。独立照合の手計算）。 -/
theorem conj_Jhat_eq_rootNum (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    starRingEnd ℂ (Jhat χ₁ χ₂)
      = (if χ₁.Even ∨ χ₂.Even then (1 : ℂ) else -1)
          * (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) := by
  rw [conj_Jhat_eq_gauss χ₁ χ₂ h₁ h₂ h₁₂]
  have hq : (0 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.out.pos _
  have hs : ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have h1 := PAG.Part16.gaussSum_ne_zero h₁
  have h2 := PAG.Part16.gaussSum_ne_zero h₂
  have h12 := PAG.Part16.gaussSum_ne_zero h₁₂
  have hodd : ∀ χ : DirichletCharacter ℂ (p ^ (n + 1)), χ.Odd → ¬ χ.Even := by
    intro χ ho he
    have e1 : χ (-1) = 1 := he
    have e2 : χ (-1) = -1 := ho
    rw [e1] at e2; norm_num at e2
  unfold rootNum
  rcases χ₁.even_or_odd with e₁ | e₁ <;> rcases χ₂.even_or_odd with e₂ | e₂
  · have e : (χ₁ * χ₂).Even := by
      show (χ₁ * χ₂) (-1) = 1
      rw [MulChar.mul_apply, show χ₁ (-1) = 1 from e₁, show χ₂ (-1) = 1 from e₂, one_mul]
    simp only [e₁, e₂, e, ↓reduceIte, true_or]
    field_simp
  · have e : ¬ (χ₁ * χ₂).Even := hodd _ (by
      show (χ₁ * χ₂) (-1) = -1
      rw [MulChar.mul_apply, show χ₁ (-1) = 1 from e₁, show χ₂ (-1) = -1 from e₂, one_mul])
    simp only [e₁, hodd _ e₂, e, true_or, ↓reduceIte]
    field_simp
  · have e : ¬ (χ₁ * χ₂).Even := hodd _ (by
      show (χ₁ * χ₂) (-1) = -1
      rw [MulChar.mul_apply, show χ₁ (-1) = -1 from e₁, show χ₂ (-1) = 1 from e₂, mul_one])
    simp only [hodd _ e₁, e₂, e, or_true, ↓reduceIte]
    field_simp
  · have e : (χ₁ * χ₂).Even := by
      show (χ₁ * χ₂) (-1) = 1
      rw [MulChar.mul_apply, show χ₁ (-1) = -1 from e₁, show χ₂ (-1) = -1 from e₂]; norm_num
    simp only [hodd _ e₁, hodd _ e₂, e, or_self, ↓reduceIte]
    field_simp
    rw [Complex.I_sq]; ring

/-- **3. 2 乗の形**：χ₁・χ₂・χ₁χ₂ が原始的なら、conj(Ĵ(χ₁, χ₂))² = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²。 -/
theorem conj_Jhat_sq_eq_rootNum (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2
      = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2 := by
  rw [conj_Jhat_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]
  split_ifs <;> ring

/-- **4. 赤道の絡み合いの 𝔀 による形**：χ₁・χ₂・χ₁χ₂ が法 p^(n+1) の原始指標で n + 1 ≤ K なら、
P¹(ℤ/p^K) の 2 チャートのモデルの赤道のケット |0, χ⟩ について、
B_N(|0,χ₁⟩, |0,χ₂⟩) = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))² · B_S(|0,χ₁⟩, |0,χ₂⟩)
（Part 21（PAG25）の `equator_intertwine_hat` と 3 から）。この定理は `equator_intertwine_hat` の係数 conj(Ĵ)² を 3 で書き換えたもので、
絡み合いの中身（単数でない点で両辺が 0 になることを含む）は Part 21 にある。 -/
theorem equator_intertwine_rootNum (K : ℕ) (h : 0 + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    PAG.Part23.BN (PAG.Part23.kS K 0 (n + 1) h χ₁) (PAG.Part23.kS K 0 (n + 1) h χ₂)
      = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2
          • PAG.Part23.BS (PAG.Part23.kS K 0 (n + 1) h χ₁) (PAG.Part23.kS K 0 (n + 1) h χ₂) := by
  rw [PAG.Part25.equator_intertwine_hat K h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]

/-- **5. 射影直線そのものの上の形**：Part 25（PAG29）の `equator_intertwine_proj`（射影直線 P¹(ℤ/p^K) = `PAG.Part27.ProjLine` の上の
関数としての南北の畳み込み B_S^proj・B_N^proj と赤道のケット）について、4 と同じ式が成り立つ。`equator_intertwine_proj` の係数を
3 で書き換えたもの。1 ≤ K は h から出るので、仮定に置かない（独立照合の指摘で外した）。 -/
theorem equator_intertwine_proj_rootNum (K : ℕ) (h : 0 + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    PAG.Part28.BNproj K (by omega) (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₁)
        (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₂)
      = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2
          • PAG.Part28.BSproj K (by omega) (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₁)
            (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₂) := by
  rw [PAG.Part29.equator_intertwine_proj K (by omega) h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]

#print axioms conj_Jhat_eq_gauss
#print axioms conj_Jhat_eq_rootNum
#print axioms conj_Jhat_sq_eq_rootNum
#print axioms equator_intertwine_rootNum
#print axioms equator_intertwine_proj_rootNum

end PAG.Part266
```

## §C 形式文の差分

```diff
--- PAG266（独立照合の前、形式文）
+++ PAG266（直した後、形式文）
@@ -94,13 +94,15 @@
           • PAG.Part23.BS (PAG.Part23.kS K 0 (n + 1) h χ₁) (PAG.Part23.kS K 0 (n + 1) h χ₂) := by
   rw [PAG.Part25.equator_intertwine_hat K h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]
 
-theorem equator_intertwine_proj_rootNum (K : ℕ) (hK : 1 ≤ K) (h : 0 + (n + 1) ≤ K)
+theorem equator_intertwine_proj_rootNum (K : ℕ) (h : 0 + (n + 1) ≤ K)
     (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
     (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
-    PAG.Part28.BNproj K hK (PAG.Part29.ketS_proj K hK 0 (n + 1) h χ₁) (PAG.Part29.ketS_proj K hK 0 (n + 1) h χ₂)
+    PAG.Part28.BNproj K (by omega) (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₁)
+        (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₂)
       = (rootNum (χ₁ * χ₂) / (rootNum χ₁ * rootNum χ₂)) ^ 2
-          • PAG.Part28.BSproj K hK (PAG.Part29.ketS_proj K hK 0 (n + 1) h χ₁) (PAG.Part29.ketS_proj K hK 0 (n + 1) h χ₂) := by
-  rw [PAG.Part29.equator_intertwine_proj K hK h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]
+          • PAG.Part28.BSproj K (by omega) (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₁)
+            (PAG.Part29.ketS_proj K (by omega) 0 (n + 1) h χ₂) := by
+  rw [PAG.Part29.equator_intertwine_proj K (by omega) h χ₁ χ₂ h₁ h₂ h₁₂, conj_Jhat_sq_eq_rootNum χ₁ χ₂ h₁ h₂ h₁₂]
 
 #print axioms conj_Jhat_eq_gauss
 #print axioms conj_Jhat_eq_rootNum
```

## §D 使う定義と補題の文（docstring を含む宣言の抜き出し。補題は文だけ）

### PAG.Part7.J（PAG7.lean）
```lean
/-- ヤコビ和 J(χ₁,χ₂) = Σ_x χ₁(x) χ₂(1 − x)。 -/
noncomputable def J (χ₁ χ₂ : MulChar (ZMod N) ℂ) : ℂ := ∑ x, χ₁ x * χ₂ (1 - x)
```

### PAG.Part15.conv（PAG15.lean）
```lean
/-- 加法畳み込み (f ⋆ g)(x) = Σ_y f(y) g(x − y)。 -/
def conv (f g : G → K) : G → K := fun x => ∑ y, f y * g (x - y)
```

### PAG.Part15.gauss_ratio_eq_jacobi（PAG15.lean）
```lean
/-- ガウス和比はヤコビ和: χ₁χ₂ 原始的・τ(χ₁χ₂) ≠ 0 ⇒ τ₁τ₂/τ₁₂ = J(χ₁, χ₂)。 -/
theorem gauss_ratio_eq_jacobi (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hprim : (χ₁ * χ₂).IsPrimitive) (ψ : AddChar (ZMod (p ^ (n + 1))) ℂ)
    (h12 : gaussSum (χ₁ * χ₂) ψ ≠ 0) :
    gaussSum χ₁ ψ * gaussSum χ₂ ψ / gaussSum (χ₁ * χ₂) ψ = PAG.Part7.J χ₁ χ₂ :=
```

### PAG.Part16.gaussSum_ne_zero（PAG16.lean）
```lean
/-- **τ(χ) ≠ 0**（χ 原始的）: 𝓕χ = τ·χ⁻¹(−·) なので τ = 0 なら χ = 0 となり χ(1) = 1 に反する。 -/
theorem gaussSum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar ≠ 0 :=
```

### PAG.Part16.normSq_gaussSum（PAG16.lean）
```lean
/-- **|τ(χ)|² = N**（χ 原始的）。法 p^c なら |τ|² = p^c。 -/
theorem normSq_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ stdAddChar) = N :=
```

### PAG.Part23.BN（PAG23.lean）
```lean
/-- 北の畳み込み B_N := W B_S(W·, W·)。 -/
noncomputable def BN (F G : P1F N) : P1F N := W (BS (W F) (W G))
```

### PAG.Part23.BS（PAG23.lean）
```lean
/-- 南の畳み込み（南チャートで畳み込み、北の内部は 0）。 -/
noncomputable def BS (F G : P1F N) : P1F N := extS (PAG.Part15.conv F.1 G.1)
```

### PAG.Part23.P1F（PAG23.lean）
```lean
/-- P¹ 上の関数（南座標の関数と北座標の関数の組）。 -/
abbrev P1F (N : ℕ) := (ZMod N → ℂ) × (ZMod N → ℂ)
```

### PAG.Part23.W（PAG23.lean）
```lean
/-- 反転 W: [x:1] ↔ [1:x]、関数では南北の入れ替え。 -/
def W (F : P1F N) : P1F N := (F.2, F.1)
```

### PAG.Part23.extN（PAG23.lean）
```lean
/-- 北チャートの関数を P¹ 上へ（南の内部では 0）。 -/
noncomputable def extN (h : ZMod N → ℂ) : P1F N := (fun x => if IsUnit x then h x⁻¹ else 0, h)
```

### PAG.Part23.extS（PAG23.lean）
```lean
/-- 南チャートの関数を P¹ 上へ（北の内部では 0）。 -/
noncomputable def extS (h : ZMod N → ℂ) : P1F N := (h, fun y => if IsUnit y then h y⁻¹ else 0)
```

### PAG.Part23.kS（PAG23.lean）
```lean
/-- 南の殻ケット |w, χ⟩（w ≥ 0）。 -/
noncomputable def kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) : P1F (p ^ K) :=
  extS (ket K w c h χ)
```

### PAG.Part25.Jhat（PAG25.lean）
```lean
/-- 規格化ヤコビ和 Ĵ = J / √p^c。 -/
noncomputable def Jhat (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) : ℂ :=
  PAG.Part7.J χ₁ χ₂ / ((Real.sqrt ((p ^ (n + 1) : ℕ) : ℝ) : ℝ) : ℂ)
```

### PAG.Part25.equator_intertwine_hat（PAG25.lean）
```lean
/-- **赤道での絡み合い（Ĵ 形）**: B_N(|0,χ₁⟩,|0,χ₂⟩) = conj(Ĵ)² · B_S(|0,χ₁⟩,|0,χ₂⟩)。 -/
theorem equator_intertwine_hat (K : ℕ) (h : 0 + (n + 1) ≤ K) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    BN (kS K 0 (n + 1) h χ₁) (kS K 0 (n + 1) h χ₂)
      = (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2 • BS (kS K 0 (n + 1) h χ₁) (kS K 0 (n + 1) h χ₂) :=
```

### PAG.Part25.normSq_J（PAG25.lean）
```lean
/-- **|J(χ₁,χ₂)|² = p^c**（χ₁, χ₂, χ₁χ₂ 原始的）。τ₁τ₂ = J τ₁₂ と |τ|² = p^c から。 -/
theorem normSq_J (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    Complex.normSq (PAG.Part7.J χ₁ χ₂) = ((p ^ (n + 1) : ℕ) : ℝ) :=
```

### PAG.Part27.ProjLine（PAG27.lean）
```lean
/-- **射影直線** P¹(Z/N)。 -/
def ProjLine (N : ℕ) := Quotient (projSetoid N)
```

### PAG.Part27.Unimod（PAG27.lean）
```lean
/-- 単模ベクトル。 -/
def Unimod (N : ℕ) := {v : ZMod N × ZMod N // ∃ s t : ZMod N, s * v.1 + t * v.2 = 1}
```

### PAG.Part28.BNproj（PAG28.lean）
```lean
/-- ProjLine 上の北の畳み込み。 -/
noncomputable def BNproj (Φ Ψ : ProjLine (p ^ K) → ℂ) : ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm
    ⟨BN (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1, compat_extN _⟩
```

### PAG.Part28.BSproj（PAG28.lean）
```lean
/-- ProjLine 上の南の畳み込み。 -/
noncomputable def BSproj (Φ Ψ : ProjLine (p ^ K) → ℂ) : ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm
    ⟨BS (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1, compat_extS _⟩
```

### PAG.Part29.equator_intertwine_proj（PAG29.lean）
```lean
/-- **赤道での絡み合い（射影直線上）**: B_N^proj = conj(Ĵ)² B_S^proj。 -/
theorem equator_intertwine_proj {n : ℕ} (h : 0 + (n + 1) ≤ K) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    BNproj K hK (ketS_proj K hK 0 (n + 1) h χ₁) (ketS_proj K hK 0 (n + 1) h χ₂)
      = (starRingEnd ℂ (Jhat χ₁ χ₂)) ^ 2 •
          BSproj K hK (ketS_proj K hK 0 (n + 1) h χ₁) (ketS_proj K hK 0 (n + 1) h χ₂) :=
```

### PAG.Part29.ketS_proj（PAG29.lean）
```lean
/-- 射影直線上の南ケット。 -/
noncomputable def ketS_proj (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm ⟨kS K w c h χ, compat_extS _⟩
```

### PAG.Part256.rootNum（PAG256.lean）
```lean
/-- W(χ) = τ(χ)/(i^a √N)（a = 0 は偶、a = 1 は奇）。χ が原始ならルート数（関数等式との一致は Lean の外）。原始的でない
χ ではルート数ではなく、0 にもなる（法 4 の自明な指標）。
内部照合（2026-11-14）：Part 192（PAG196）の `zN` を Part 194（PAG198）の `gs` で割ったものと同じ値（Lean で確認）。 -/
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))
```

### PAG.Part19.sz（PAG19.lean）
```lean
/-- 殻サイズ |S_u| = p^(K−1−u)(p−1)。 -/
def sz (p K u : ℕ) : ℕ := p ^ (K - 1 - u) * (p - 1)
```

### PAG.Part21.ket（PAG21.lean）
```lean
/-- 殻 u の標準ケット（step30 の `P.ket(u, c, j)` に対応）: |S_u|^(−1/2) ι_{u,*}(χ ∘ π_u)。 -/
noncomputable def ket (K u c : ℕ) (huc : u + c ≤ K) (χ : ZMod (p ^ c) → ℂ) : ZMod (p ^ K) → ℂ :=
  have : NeZero (p ^ (K - u)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  (((Real.sqrt (sz p K u))⁻¹ : ℝ) : ℂ) •
    push (shellEmb (p := p) K u (by omega))
      (χ ∘ (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - u)) (ZMod (p ^ c))).toAddMonoidHom)
```

### PAG.Part27.mk（PAG27.lean）
```lean
/-- 点 [a:b]。 -/
def mk (v : Unimod N) : ProjLine N := Quotient.mk (projSetoid N) v
```

### PAG.Part27.projSetoid（PAG27.lean）
```lean
/-- 単数倍の同値関係。 -/
def projSetoid (N : ℕ) : Setoid (Unimod N) where
  r v w := ∃ u : (ZMod N)ˣ, w.1.1 = u * v.1.1 ∧ w.1.2 = u * v.1.2
  iseqv := {
    refl := fun v => ⟨1, by simp, by simp⟩
    symm := fun {v w} ⟨u, h1, h2⟩ => ⟨u⁻¹, by rw [h1, ← mul_assoc, Units.inv_mul, one_mul],
      by rw [h2, ← mul_assoc, Units.inv_mul, one_mul]⟩
    trans := fun {v w z} ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩ => ⟨u' * u, by rw [h1', h1, Units.val_mul, mul_assoc],
      by rw [h2', h2, Units.val_mul, mul_assoc]⟩ }
```


## C. Mathlib の定義（名前だけ）

- `gaussSum χ ψ` = Σ_{a} χ a * ψ a（Mathlib.NumberTheory.GaussSum）。`ZMod.stdAddChar`：ZMod N の標準の加法指標 x ↦ exp(2πi x.val/N)。
- `DirichletCharacter.Even χ` ：χ (-1) = 1。`DirichletCharacter.Odd χ`：χ (-1) = -1。`DirichletCharacter.IsPrimitive`：導手が法に等しい。
- `starRingEnd ℂ`：複素共役。

### 追加（独立照合の照合者が入力になかったと申告した定義）

### PAG.Part23.compat_extN（PAG23.lean）
```lean

theorem compat_extN (h : ZMod N → ℂ) : Compat (extN h) :=
```

### PAG.Part23.compat_extS（PAG23.lean）
```lean

theorem compat_extS (h : ZMod N → ℂ) : Compat (extS h) :=
```

### PAG.Part26.compatSub（PAG26.lean）
```lean
/-- 貼り合わせ条件を満たす組の部分空間。 -/
def compatSub (N : ℕ) : Submodule ℂ (P1F N) where
  carrier := {F | Compat F}
  add_mem' := fun {F G} hF hG y hy => by
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, hF y hy, hG y hy]
  zero_mem' := fun y _ => rfl
  smul_mem' := fun a {F} hF y hy => by
    simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, hF y hy]
```

### PAG.Part28.projFunEquiv（PAG28.lean）
```lean
/-- **関数空間の直接同型**: (ProjLine(p^K) → ℂ) ≃ₗ 貼り合わせ条件の部分空間。 -/
noncomputable def projFunEquiv : (ProjLine (p ^ K) → ℂ) ≃ₗ[ℂ] compatSub (p ^ K) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (projEquiv K hK)).trans (ptEquiv (p ^ K))
```

### PAG.Part29.projFun_BNproj（PAG29.lean）
```lean

theorem projFun_BNproj (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    (projFunEquiv K hK (BNproj K hK Φ Ψ)).1 = BN (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1 :=
```

### PAG.Part29.projFun_BSproj（PAG29.lean）
```lean

theorem projFun_BSproj (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    (projFunEquiv K hK (BSproj K hK Φ Ψ)).1 = BS (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1 :=
```

### PAG.Part29.projFun_ketS（PAG29.lean）
```lean

theorem projFun_ketS (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    (projFunEquiv K hK (ketS_proj K hK w c h χ)).1 = kS K w c h χ :=
```

### PAG.Part17.push（PAG17.lean）
```lean
/-- ゼロ拡張（押し出し）ι_* f = Function.extend ι f 0。 -/
noncomputable def push (ι : H →+ G) (f : H → ℂ) : G → ℂ := Function.extend ι f 0
```

### PAG.Part17.shellEmb（PAG17.lean）
```lean
/-- 殻 v への埋め込み ι_v : ZMod p^(K−v) → ZMod p^K、x ↦ p^v x。 -/
noncomputable def shellEmb (K v : ℕ) (hv : v ≤ K) : ZMod (p ^ (K - v)) →+ ZMod (p ^ K) :=
  ZMod.lift (p ^ (K - v)) ⟨(p ^ v : ZMod (p ^ K)) • (Int.castAddHom (ZMod (p ^ K))), by
    simp only [AddMonoidHom.smul_apply, Int.castAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Int.cast_natCast, smul_eq_mul]
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hv, ZMod.natCast_self]⟩
```
