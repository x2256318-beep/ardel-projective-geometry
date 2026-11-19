# Q1〜Q7 の文献照合（盲検の出力の全文、2026-11-19）

制約どおり、使ったのは WebSearch と WebFetch だけです。ファイルの読み書きとコードの実行はしていません。数値での確認はしていないので、「手計算」と書いた箇所は数値で裏付けていません。

## 共通の準備（手計算）

- **スキームの同定。** $\mathbb Z/N$ 上で $R_s=\{(x,y):\gcd(x-y,N)=s\}$ とおくと、$(\mathbb Z/N)^\times$ の乗法の軌道から作る translation scheme $\mathfrak X_N$ ができます。$D_s$ は基点 0 に関する双対冪等元、$E_s$ は周波数の殻への射影で原始冪等元です。したがって $A_N$ は $\mathfrak X_N$ の Terwilliger 代数 $T(0)$ です。
- **素数冪への分解。** $N=\prod p^{e}$ とすると、中国剰余定理で $\mathfrak X_N$ は直積スキームになり、$A_N=\bigotimes A_{p^e}$ です（生成元が各因子のテンソル積になるので初等的に出ます）。
- **素数冪の場合。** $\mathfrak X_{p^e}$ は関係 $v_p(x-y)$ で決まる超距離スキームで、$K_p\wr\cdots\wr K_p$（$e$ 個）に当たります（[Bastian–Humphries 2026, Thm 3.7](https://arxiv.org/pdf/2606.19095)）。
- **記号。** $n_c(p)$ は法 $p^c$ の原始指標の個数で、$c=1$ なら $p-2$、$c\ge2$ なら $p^{c-2}(p-1)^2$ です。
- **補題 L（手計算）。** $\chi$ を法 $p^c$（$c\ge1$）の原始指標、$k\le e-c$ とし、$g_{\chi,k}(x)=\chi(x/p^k)$（$v_p(x)=k$ のとき）、それ以外は 0 とおきます。
  - $g_{\chi,k}$ のフーリエ変換の台は、ちょうど殻 $p^{e-k-c}$ にあります。
  - 自明な指標の成分（殻の指示関数）だけは、フーリエ側で複数の殻にまたがります（ラマヌジャン和）。
- **補題 L から出る加群の構造。** 自明でない $\chi$ の等型成分 $V^\chi$ の上では、$A_{p^e}$ は対角的に作用します。$A_{p^e}$ の既約加群は次の 2 種類です。
  - 主加群：次元 $e+1$、重複 1。
  - 1 次元の型 $(k,j)$：$k+j=e-c$、重複 $n_c(p)$。ここで $D_{p^k}=1$、$E_{p^j}=1$ です。
- **次元の照合。** 次元は $p$ が奇数なら $(e+1)^2+e(e+1)/2$、$p=2$ なら $(e+1)^2+e(e-1)/2$ です。これは公表された結果と一致します。
  - Bastian–Humphries の Prop. 3.3：$\tfrac12(3e^2+5e+2)$ と $\tfrac12(3e^2+3e+2)$。
  - Bhattacharyya–Song：$M_{d+1}\oplus M_1^{\oplus d(d+1)/2}$（$n\ge3$）、$M_1^{\oplus d(d-1)/2}$（$n=2$）（[arXiv:0809.1052](https://ar5iv.arxiv.org/html/0809.1052)）。
  - 主加群以外がすべて 1 次元であることは、Bhattacharyya–Song–Tanaka の結果として引用されています（[Song–Xu, arXiv:1008.2228](https://ar5iv.arxiv.org/html/1008.2228)）。

---

## Q1. $R_u$・$P$・$J$ との可換性と、$A_N$ の可換子

**答え**

- **可換性。** $R_u$、$P$、$J$ はすべて $A_N$ と可換です。
  - $R_u$：殻は単数倍で保たれるので $D_s$ と可換です。さらに $FR_u=R_{u^{-1}}F$ なので $E_sR_u=R_uE_s$ が出ます。$P=R_{-1}$ も同じです。
  - $J$：すべての $d\mid N$ について「$x\equiv y \pmod d$ なら $Jx\equiv Jy \pmod d$」が成り立ち、0 を固定します。つまり $J$ はスキームの自己同型で、0 を固定します。
  - 一般に、基点を固定する自己同型群 $G_v$ について $T(v)\subseteq \mathrm{End}_{G_v}(\mathbb C^\Omega)$ が成り立ちます（[arXiv:2510.17118 の式 (2)](https://arxiv.org/pdf/2510.17118)）。
- **可換子。** $A_N'=\bigotimes_{p^e\parallel N}A_{p^e}'$ で、各因子は次の形です。
  $$A_{p^e}'\cong \mathbb C\oplus\bigoplus_{c=1}^{e}M_{n_c(p)}(\mathbb C)^{\oplus(e-c+1)}$$
  - 具体的には、主加群（殻の上で定数の関数）の上ではスカラー、各 $D_{p^k}V\cap E_{p^j}V$（$k+j<e$）の上では任意で、成分どうしの間はゼロ、という作用素の全体です。
  - 同じことを群で言うと、$A_N=\mathrm{End}_{G_0}(V_N)$ です。ここで $G_0=\mathrm{Aut}(\mathfrak X_N)_0$ は、0 を固定しすべての $d\mid N$ で合同関係を保つ置換の群で、$p$ 進の根付き木の葉を 1 つ固定する安定化群の直積になります。
  - 二重可換子定理から $A_N'=\mathrm{span}\{\pi(\sigma):\sigma\in G_0\}$ です。
  - 根拠（手計算）：$G_0$ の点の対への作用の軌道は三つ組 $(v(x),v(x-y),v(y))$ と一致します（木の安定化群が各三つ組で推移的）。軌道の数は Bastian–Humphries が三重正則性で数えた $\dim T$ と一致します。つまり $\mathfrak X_{p^e}$ は triply transitive です。
- **$\mathrm{span}\{R_u\}$ との比較。** $A_N'=\mathrm{span}\{R_u\}$ となるのは $N\mid 12$ のとき、そのときに限ります（重複なしの条件 $n_c\le1$ から）。
  - 例：$N=5$ では $A_5'\cong\mathbb C\oplus M_3(\mathbb C)$ で、単数のどんな置換も $A_5$ と可換です。

**確信度**

- 可換性：高。
- 可換子の構造：高（次元が公表値と一致）。
- $A_N=\mathrm{End}_{G_0}$：中〜高。
- $N\mid12$ の判定：中〜高。

**既知か**

- 包含 $T(v)\subseteq\mathrm{End}_{G_v}$ と加群の構造は既知です。
- 円分スキームが triply transitive であること、可換子を明示した文、$N\mid12$ の判定は、見つかりませんでした。triply transitive は [Bannai–Munemasa 1995（2510.17118 での引用）](https://arxiv.org/pdf/2510.17118) が有限アーベル群の共役類スキームについて示したもので、木のスキームについての記述は見当たりませんでした。

## Q2. $H$ と $J\circ H$ による共役

**答え**

- $H=\tfrac{1+i}{2}F+\tfrac{1-i}{2}F^{-1}=F(\Pi_++i\Pi_-)$ と書けます。$\Pi_\pm$ は $P$ の固有射影で、$\mathrm{span}\{I,P\}\subset A_N'$ に入ります。
- $F^2=P$ は $D_s$ と可換なので、$FD_sF^{-1}=E_s$ と $FE_sF^{-1}=D_s$ が成り立ちます。
- したがって $HD_sH=E_s$、$HE_sH=D_s$、$H^2=I$ で、$H$ による共役は $A_N$ を保ちます。
- $J\in A_N'$ なので、$A_N$ の上では $\mathrm{Ad}(JH)=\mathrm{Ad}(H)=\mathrm{Ad}(F)$ です。3 つとも、$D_s$ と $E_s$ を入れ替える同じ位数 2 の自己同型を与えます。

**確信度**：高。

**根拠**：手計算。translation scheme の指標による双対性は既知です（[Martin–Tanaka の解説 §6](https://ar5iv.arxiv.org/html/0811.2475)）。$(\mathbb Z/\nu)^\times$ の作用から来るスキームの自己双対性もあります（[Kim–Kim, arXiv:1108.4947](https://arxiv.org/abs/1108.4947)）。Hartley 変換の形で書いた文は見つかりませんでしたが、上の式から直ちに出ます。

## Q3. 角 $D_1A_ND_1$ と $U_N$・$P$

**答え**

- **角の代数。** 単数の上の関数に制限すると、
  $$D_1A_ND_1|_{\rm units}=\mathrm{span}\{\Pi_f: f\mid N,\ f\not\equiv2 \ (\mathrm{mod}\ 4)\},\qquad \Pi_f=\sum_{f(\chi)=f}P_\chi$$
  です。
  - 次元は、$N=2^am$（$m$ は奇数）として、$a\le1$ なら $d(m)$、$a\ge2$ なら $a\,d(m)$ です。
  - 同値な基底として、$U_g=\ker\big((\mathbb Z/N)^\times\to(\mathbb Z/g)^\times\big)$ の上での平均（$g\mid N$）が取れます。
  - 根拠：$D_1W$ はどの既約加群でも高々 1 次元で、$D_1\ne0$ となる型は導手と一対一に対応します。
- **$U_N$。** $U_N$ は角の代数と常に可換です（どちらも指標の基底で対角）。
  - 角に属するのは、各導手の類の上で $W(\chi^*)$ が一定のときで、それは $N\mid24$（$N\in\{2,3,4,6,8,12,24\}$）のとき、そのときに限ります。このとき $U_N=I$ です。
  - $N\mid24$ の側：すべての指標が実で、Gauss の符号の決定 $\tau(\chi_d)=\sqrt d$ または $i\sqrt{|d|}$ から $W=1$ になります（[Montgomery–Vaughan 第 9 章, Thm 9.17](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf)）。
  - それ以外の側：$N$ は導手 $p\ge5$、9、16 のどれかを含み、そこで $W$ が一定になりません（手計算）。
    - $p\ge5$：$\sum_{\chi\ne1}\tau(\chi)$ の虚部を比べると、すべて $W=1$ なら $\sin(2\pi/p)=\sqrt p/2$ が必要になり、不可能です。
    - 9：3 次の指標で $W=\zeta_9^{\pm1}$。
    - 16：$W\in\{e^{\pm i\pi/8},e^{\pm3i\pi/8}\}$。
  - 補足：$U_N$ は常に $\mathrm{span}\{R_u|_{\rm units}\}$、つまり可換子の側の角に入ります。$A_N$ の角に入るのは自明な場合（$U_N=I$）だけです。
- **$P$ の単数への制限。** $P|_{\rm units}=\sum\chi(-1)P_\chi$ は常に可換です。角に属するのは $N\mid12$ のとき、そのときに限ります。
  - 導手 8 では $\chi_8$ が偶、$\chi_{-8}$ が奇。$p\ge5$、9、16 でも偶奇が混ざります。

**確信度**

- 角の構造：高。
- $N\mid24$：中〜高（手計算）。
- $N\mid12$：中〜高（手計算）。

**既知か**：判定の文は見つかりませんでした。

## Q4. $F_M\iota$ と $VF_N$、$\varphi$ と $\psi$

**答え**

- **基本の関係。** $F_M\iota=VF_N$ です（手計算：$t$ についての和が $(M/N)\cdot\mathbf 1[(M/N)\mid k]$ になる）。
- **$\varphi$ と $\psi$ の関係。** フーリエ変換で $\psi\circ\mathrm{Ad}F_N=\mathrm{Ad}F_M\circ\varphi$ と結ばれます。$n=M/N$ とおくと、
  - $\psi(D_s)=D_{ns}$、$\varphi(E_s)=E_{ns}$。
  - $\varphi(1)=\iota\iota^*=\tfrac1n\sum_j T_{jN}=\sum_{n\mid t}E_t$、$\psi(1)=VV^*=\sum_{n\mid t}D_t$。
  - $\varphi(D_s)=\big(\sum_{\gcd(t,N)=s}D_t\big)\varphi(1)\in A_M$。
- **Bost–Connes 系での型。** $\psi$ は乗法作用素の側（$C(\widehat{\mathbb Z})$ の像）で、端点写像 $\alpha_n(f)(x)=f(x/n)\mathbf 1_{n\widehat{\mathbb Z}}$ の有限レベル版です。
  - $V$ は、標準表現での等長作用素 $\mu_n$（$\varepsilon_m\mapsto\varepsilon_{nm}$）に当たります。
  - 手計算で $Ve(r)V^*=\tfrac1n\sum_{ns=r}e(s)$ を確かめました。
  - $\varphi$ は平行移動の側（群環 $\mathbb C[(1/N)\mathbb Z/\mathbb Z]$）で、同じ関係 $\varphi(T_a)=\tfrac1n\sum_{b\equiv a\ (N)}T_b$ を満たします。
  - つまり $\varphi$ と $\psi$ は、BC の共変関係 $\rho_n$ をフーリエ変換で入れ替わる 2 つの見方で書いたものです。

**確信度**

- 恒等式：高。
- BC との型の対応：中〜高。

**根拠**

- 商と双対の部分群の対応（Pontryagin 双対）は標準的です。
- BC の関係 $\mu_ne(r)\mu_n^*=\tfrac1n\sum_{ns=r}e(s)$ と $C(R)$ 上の $\alpha_n$ は [Shirbisheh, arXiv:0808.1767](https://arxiv.org/pdf/0808.1767) にあります（Bost–Connes, Selecta Math. 1995 を引用）。
- 半群接合積として実現したのは Laca–Raeburn です（[Arledge–Laca–Raeburn 1997](https://emis.muni.cz/journals/DMJDMV/vol-02/05.html)、[AIM の解説](https://aimath.org/WWN/rh/articles/html/102a)）。
- 有限レベルで 2 つを並べた明示的な文は見つかりませんでした（検索は 1 回だけ）。

## Q5. $D_1V\cap E_1V$

**答え**

- **共通部分。** $D_1V\cap E_1V$ は、法 $N$ の原始指標（単数の外では 0 に延長）が張る空間です。
  $$\dim=\varphi^*(N)=\sum_{d\mid N}\mu(N/d)\varphi(d)=N\prod_{p\parallel N}(1-2/p)\prod_{p^2\mid N}(1-1/p)^2$$
  - $N\equiv2\pmod4$ のとき 0 です。
- **根拠。**
  - $R_u$ の等型成分に分けて考えます。
  - 原始指標なら、すべての $n$ について $\tau(\chi,n)=\bar\chi(n)\tau(\chi)$ が成り立ちます（[Montgomery–Vaughan Thm 9.7](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf)、逆は Ex. 9.2.6）。
  - 原始的でない指標では、どこかの素数での局所因子が、台が $v\ge1$ にあるか、自明な成分のラマヌジャン和で $\xi_p=0$ での値が 0 でないかのどちらかになり、$E_1V$ に入りません。
  - この空間は、$D_1=E_1=1$ となる 1 次元の型 1 つの重複空間で、$A_N$ はそこにスカラーで作用します。
- **$J\circ H$ は保つか。** 保ちます。
  - 構造からの理由：$J$ は $D_1V$ を保ち $E_1$ と可換、$H$ は $D_1V$ と $E_1V$ を入れ替えます。
  - 明示的には $H\chi=W(\chi)\bar\chi$、$J\bar\chi=\chi$ なので、$JH$ の原始指標の上への制限は $\sum_{\chi\ \text{原始}}W(\chi)P_\chi$、つまり $U_N$ の制限と一致します。

**確信度**：高。

**既知か**

- 原始指標のフーリエ変換は古典的です。
- 近いものとして、関数等式から原始指標を特徴づける逆定理（[Hiary–Saraeb, arXiv:2607.00332](https://arxiv.org/abs/2607.00332)）と、乗法的指標の DFT（[arXiv:2104.09295](https://arxiv.org/abs/2104.09295)）があります。
- 「関数とそのフーリエ変換の台がともに単数に入る ⇔ 原始指標の張る空間に入る」を補題として書いた文献と、Hartley 変換の偶奇の因子 $(-i)^a$ を書いた文献は見つかりませんでした。

## Q6. 関数体 $\mathbb F_q(t)$ での対照

$\mathbb Z/N$ の代わりに $\mathbb F_q[t]/(m)$ を使い、加法指標を $\psi_m(x)=\psi_0(\mathrm{Tr}\,\mathrm{res}_\infty(x/m))$ とします（[Chinta–Mohler](https://arxiv.org/pdf/0706.2735) の留数による定義）。各 $P^e\parallel m$ について、スキームは $(K_Q)^{\wr e}$（$Q=q^{\deg P}$）になります。

**答え**

- **Q1・Q2・Q4・Q5：同じ形です。**
  - Q1 は $p$ を $Q$ に替えて成り立ち、$n_1=Q-2$、$n_c=Q^{c-2}(Q-1)^2$ です。
  - 「$A$ が単数群の中心化代数に等しい」条件のリストは変わります。$\mathbb F_2[t]$ では $m\mid t^2(t+1)^2$、$\mathbb F_3[t]$ では $m\mid t^3-t$、$q\ge4$ では $m=1$ だけです。
  - 標数 2 では $P=I$ で、$H=F$ になります。
  - Q4 では $\psi_M((M/N)x)=\psi_N(x)$ なので同じ関係が成り立ちます。関数体版の Bost–Connes 系も存在します（[Jacob, math/0602554](https://arxiv.org/pdf/math/0602554)）。
- **Q3：判定の形は同じですが、どの $m$ で成り立つかとその算術的な意味が変わります。**
  - 判定の形は「各導手の類の上で $W$ が一定」で同じです。
  - 値は違います（手計算）。$\mathbb F_3[t]$ の導手 $t^2$ では $W\in\{1,1,i,-i\}$、$\mathbb F_2[t]$ の導手 $t^3$ では $W=e^{\pm i\pi/4}$ です。
  - $\mathbb Q$ での「$N\mid24$」は、Gauss の符号定理と、$i^a$ を無限素点の因子と読むことに依存しています。$\mathbb F_q(t)$ では $\infty$ が非アルキメデス的で、偶指標とは $\mathbb F_q^\times$ の上で自明な指標を指し、関数等式に $(1-q^{-s})$ の因子が入ります（[Andrade–Miller–Pratt–Trinh, arXiv:1404.2435](https://arxiv.org/pdf/1404.2435)）。そのため、$\mathbb Q$ の式をそのまま移した $W$ は、一般には $L$ 関数のルート数ではありません。

**確信度**

- 構造が同じであること：中〜高。
- 個々の値とルート数との比較：中。

**結論**：Q1・Q2・Q4・Q5 と Q3 の判定の形は、有限環とフーリエ変換の構造しか使っておらず、$\mathbb Q$ に固有の算術を含みません。

## Q7. 既存の結果の当てはめで済まない部分は残るか

**答え**：照合した範囲では、新しい数学の内容は見つかりませんでした。これは不存在の証明ではありません。

**確信度**：中。

**内訳**

- 各問いの核は既知の結果に対応します。
  - $T(0)$ の構造：Bhattacharyya–Song、Bastian–Humphries、Tanaka。
  - $T\subseteq\mathrm{End}_{G_v}$ と二重可換子定理。
  - translation scheme の双対性。
  - 原始指標のガウス和：Montgomery–Vaughan。
  - Pontryagin 双対と Bost–Connes の関係。
- 文献には見つからなかった部分は次の 4 つで、いずれも短い計算です。せいぜい「小さいノートの水準」です。
  1. $\mathfrak X_{p^e}$ が triply transitive であること、可換子の明示、$N\mid12$ の判定。
  2. $U_N\in$ 角 $\Leftrightarrow N\mid24$、$P|_{\rm units}\in$ 角 $\Leftrightarrow N\mid12$。
  3. $F_M\iota=VF_N$ による、$\varphi$ と $\psi$ を BC の $\rho_n$ の 2 つの見方としてまとめる整理。
  4. $D_1V\cap E_1V$ の上で $JH=U_N$ となること（Hartley の偶奇の因子を含む）。
- 2 に含まれる算術は Gauss の古典的な符号定理だけです。
- 注意：$U_N$ は $A_N$ の角には（$U_N=I$ の場合を除いて）入らず、可換子の側（単数群の群環）に属します。したがって「$A_N$ から $U_N$ が出た」と読むと、ルート数を外から入れたものの読み替えになります。

**検索の記録**：WebSearch 約 20 回。主な検索語は、Terwilliger algebra cyclotomic / orbit Schur ring / wreath product / centralizer algebra / triply transitive、Hartley transform Dirichlet character、Fourier transform supported on units primitive characters、Bost–Connes ρ_n、function field Gauss sum root number。WebFetch は約 15 回です。
- MathSciNet と zbMATH は使っていません。
- Hanaki–Kim–Maekawa の本文は取得できませんでした（リダイレクトの期限切れ）。
- Bost–Connes の有限レベルについての検索は浅いです。
