# 独立照合の出力（PAG268、2026-11-25）

（照合者の最終報告の全文を写した。）

# PAG268 照合の成果物（逆翻訳・非空虚性の証人・除去テスト・気づいた点）

ファイルは指示どおり 1 回だけ読みました。計算はすべて手計算で、Mathlib の内部の定義について推測した箇所は、そのつど確信度を付けています。

## 0. 使う定義の言葉による説明

- **Unimod N**：$(\mathbb Z/N)^2$ の組 $(x,y)$ のうち、$sx+ty=1$ となる $s,t$ があるもの（単模な組）。
- **ProjLine N**：単模な組を、単数倍 $(x,y)\sim(ux,uy)$（$u\in(\mathbb Z/N)^\times$）で割った集合 $\mathbb P^1(\mathbb Z/N)$。類を $[x:y]$ と書きます。$N=1$ では 1 点です。$N=0$ では $\mathbb Z/0=\mathbb Z$ なので $\mathbb P^1(\mathbb Z)$ になります。
- **Wproj**：$[x:y]\mapsto[y:x]$。
- **red**（$N\mid M$）：成分ごとに法 $N$ へ落とす写像 $\mathbb P^1(\mathbb Z/M)\to\mathbb P^1(\mathbb Z/N)$。
- **zeroPt** は $[0:1]$。**eqPt x** は単数 $x$ について $[x:1]$。
- **Lvl**：正の整数のこと。順序は整除です。
- **pullP**：$\mathbb P^1(\mathbb Z/a)$ の上の関数 $f$ を $f\circ\mathrm{red}$ に送る、$\mathbb P^1(\mathbb Z/b)$ の上の関数への線形写像（$a\mid b$）。
- **resE**：関数 $f$ を、単数 $x$ ごとに $f([x:1])$ を返す単数群上の関数に送る写像。
- **charU χ**：ディリクレ指標 $\chi$ を単数群に制限したもの。
- **χ⁻¹**：ディリクレ指標の群での逆元です。単数では $\chi(u)^{-1}=\overline{\chi(u)}$、非単数では 0 になります。したがって関数として $\chi^{-1}=\overline\chi$ です（$N=1$ でも成り立ちます）。
- **chiPt χ**：$[x:y]\mapsto \chi(x)\,\chi^{-1}(y)=\chi(x)\overline{\chi(y)}$。値は単数倍で変わりません（$\chi(u)\chi^{-1}(u)=1$）。0 でない値をとるのは $x,y$ がともに単数のときだけで、そのとき値は $\chi(x/y)$ です。
- **torusU / torus u**：$[x:y]\mapsto[ux:y]$。南の座標 $z=x/y$ では $z\mapsto uz$、北の座標 $y/x$ では $u^{-1}$ 倍になります。$[0:1]$ と $[1:0]$ は動きません。
- **extChi χ**：$\chi$ の導手を $f$、$\chi$ を誘導する原始指標（法 $f$）を $\chi^*$ とします。$q\in\mathbb P^1(\mathbb Z/N)$ を法 $f$ に落とした点で $\mathrm{chiPt}\,\chi^*$ を評価した値です。式で書くと $[x:y]\mapsto\chi^*(\bar x)\,\overline{\chi^*(\bar y)}$（バーは法 $f$ での剰余）。
- **sz p K u** $=p^{K-1-u}(p-1)$（自然数の引き算）。$u=0$、$K\ge1$ では $\varphi(p^K)$ です。
- **ket K 0 c**（ket0_apply による）：法 $p^c$ の関数 $f$ を、$x\mapsto \varphi(p^K)^{-1/2}\,f(x \bmod p^c)$ という $\mathbb Z/p^K$ の上の関数に送ります。
- **extS h**：南のチャートの関数 $h$ と、北のチャートの関数「$y$ が単数なら $h(y^{-1})$、そうでなければ 0」の組。
- **kS** $=\mathrm{extS}(\mathrm{ket}\dots\chi)$。
- **projFunEquiv**：$\mathbb P^1(\mathbb Z/p^K)$ の上の関数 $\Phi$ と、貼り合わせ条件を満たすチャートの組 $(\Phi([x:1]))_x,\ (\Phi([1:y]))_y$ との線形同型。
- **ketS_proj w c χ**：チャートの組 kS を projFunEquiv で $\mathbb P^1$ の上の関数に戻したもの。

## 1. 逆翻訳

- **mul_inv_apply_unit**：任意の $N$、法 $N$ のディリクレ指標 $\chi$、単数 $u$ について $\chi(u)\chi^{-1}(u)=1$。
- **chiPt_mk**：任意の単模な組 $(x,y)$ について $\mathrm{chiPt}\chi([x:y])=\chi(x)\chi^{-1}(y)$。
- **chiPt_eqPt**：単数 $x$ について $\mathrm{chiPt}\chi([x:1])=\chi(x)$。
- **chiPt_Wproj**：任意の点 $q$ について $\mathrm{chiPt}\chi(W q)=\mathrm{chiPt}\,\chi^{-1}(q)$。座標で書くと、$[y:x]$ での $\chi$ の値は $[x:y]$ での $\bar\chi$ の値に等しい、ということです。
- **torus_eqPt**：単数 $u,x$ について、$u$ の作用は $[x:1]$ を $[ux:1]$ に送る。
- **chiPt_torus**：任意の $u$、$q$ について $\mathrm{chiPt}\chi(u\cdot q)=\chi(u)\,\mathrm{chiPt}\chi(q)$。chiPt χ はトーラスの作用の固有関数で、固有値は $\chi(u)$ です。
- **chiPt_red_congr**：$d_1=d_2$、$d_1,d_2\mid M$ とし、法 $d_1$ の指標 $\chi_1$ と法 $d_2$ の指標 $\chi_2$ がすべての整数で同じ値をとるとします。このとき $\mathbb P^1(\mathbb Z/M)$ のすべての点 $q$ で $\mathrm{chiPt}\chi_1(\mathrm{red}\,q)=\mathrm{chiPt}\chi_2(\mathrm{red}\,q)$（型を運ぶための補題）。
- **extChi_eqPt**（$N\ne0$）：単数 $x$ について $\mathrm{extChi}\chi([x:1])=\chi(x)$。
- **extChi_changeLevel**（$N\mid M$、$M\ne0$）：法 $N$ の $\chi$ を法 $M$ に持ち上げた指標の extChi は、extChi χ を red で引き戻したものに等しい。
- **extChi_torus**（$N\ne0$）：$\mathrm{extChi}\chi(u\cdot q)=\chi(u)\,\mathrm{extChi}\chi(q)$。
- **pullP_extChi**：正の整数 $a\mid b$ について、extChi χ の引き戻しは、$\chi$ を法 $b$ に持ち上げた指標の extChi に等しい。
- **resE_extChi**：正の整数 $a$ について、extChi χ を単数 $x$ の点 $[x:1]$ に制限すると、$\chi$ の単数群への制限に等しい。
- **chiPt_not_compat**：法 1 の自明指標を法 2 に持ち上げた指標の chiPt の $[0:1]$ での値は、法 1 の自明指標の chiPt の $\mathrm{red}([0:1])$ での値と異なる。
- **ketS_proj_zero_eq**：$p$ を素数とし、$1\le c\le K$ とします（$1\le K$ も仮定にありますが、他の仮定から出ます）。法 $p^c$ の指標 $\chi$ について、$w=0$ のケット $\mathrm{ketS\_proj}(0,c,\chi)$ は関数 $q\mapsto \varphi(p^K)^{-1/2}\,\mathrm{chiPt}\chi(q \bmod p^c)$ に等しい。

## 2. 非空虚性の証人

- **mul_inv_apply_unit**：$N=5$、$\chi(2)=i$ となる位数 4 の指標、$u=2$ とします。$i\cdot(-i)=1$。
- **chiPt_eqPt / chiPt_mk**：同じ $\chi$ で $[2:1]$ での値は $\chi(2)=i$ です。$[2:3]$ では $\chi(2)\overline{\chi(3)}=i\cdot\overline{(-i)}=i\cdot i=-1$ で、これは $\chi(2\cdot3^{-1})=\chi(4)=-1$ と合います。
- **chiPt_Wproj**：同じ $\chi$、$q=[2:1]$ とします。左辺 $\mathrm{chiPt}\chi([1:2])=\chi^{-1}(2)=-i$、右辺 $\chi^{-1}(2)=-i$ で一致します。
- **torus_eqPt / chiPt_torus**：$N=5$、$\chi$ をルジャンドル記号、$u=2$、$q=[1:1]$ とします。$2\cdot[1:1]=[2:1]$ で、値は $-1=\chi(2)\cdot1$ です。
- **chiPt_red_congr**：$d_1=d_2=4$、$\chi_1=\chi_2=\chi_4$（法 4 の非自明な指標）、$M=12$、$q=[1:3]$ とします。両辺とも $\chi_4(1)\overline{\chi_4(3)}=-1$ です。
- **extChi_eqPt / extChi_torus**：$N=12$、$\chi$ を $\chi_4$ が誘導する指標（導手 4）とします。
  - $\mathrm{extChi}\chi([5:1])=\chi_4(1)=1=\chi(5)$ です。
  - 内容のある点として $q=[1:3]$ では、extChi は $\chi_4(1)\overline{\chi_4(3)}=-1$ ですが、$\mathrm{chiPt}\chi([1:3])=0$ です（3 は法 12 で単数でない）。extChi が chiPt と本当に違う場所はここです。
  - torus は $u=5$ で $[5:3]$ に移り、値は $\chi_4(1)\overline{\chi_4(3)}=-1=\chi(5)\cdot(-1)$ と合います。
- **extChi_changeLevel / pullP_extChi**：$N=4$、$M=12$、$\chi=\chi_4$、$q=[1:3]$ とします。左辺は上の $-1$、右辺は $\mathrm{chiPt}\chi_4([1:3])=-1$ です。
  - もう一つの例として、$N=1$、$M=2$、$\chi$ を自明指標とします。$\mathbb P^1(\mathbb Z/2)$ の 3 点すべてで両辺は 1 です。
- **resE_extChi**：$a=5$、$\chi$ をルジャンドル記号とします。$x=2$ で $-1=\chi(2)$ です。
- **chiPt_not_compat**：左辺は $\chi_2(0)\chi_2^{-1}(1)=0$ です。右辺は $\mathbb P^1(\mathbb Z/1)$ の唯一の点での値で、$\mathbb Z/1$ では $0=1$ なので $1$ です。したがって $0\ne1$。
- **ketS_proj_zero_eq**：$p=3$、$K=2$、$c=1$、$\chi$ を法 3 のルジャンドル記号とします。$\mathrm{sz}=3\cdot2=6$ です。$\mathbb P^1(\mathbb Z/9)$ の 12 点での値は次のとおりです。
  - $[1:1],[4:1],[7:1],[1:4],[1:7]$ などで $1/\sqrt6$
  - $[2:1],[5:1],[8:1]$ で $-1/\sqrt6$
  - $[0:1],[3:1],[6:1],[1:0],[1:3],[1:6]$ で 0
  
  2 乗和は $6/6=1$ です。

## 3. 除去テスト

- **ketS_proj_zero_eq の $1\le c$**：外すと反例があります（反例が作れる）。
  - $p=2$、$K=1$、$c=0$、$\chi$ を法 1 の自明指標とします。$\mathrm{sz}=1$ です。
  - 左辺の南のチャートでは $\mathrm{ket}(x)=1$ なので、$[0:1]\mapsto1$、$[1:1]\mapsto1$ です。
  - 点 $[1:0]$ は北のチャートの $y=0$ です。$0$ は単数でないので、左辺の値は 0 です。
  - 右辺は $\mathrm{chiPt}$ を $\mathbb P^1(\mathbb Z/1)$ で評価するので恒等的に 1 です。
  - よって $[1:0]$ で $0\ne1$。この仮定は必要です。
- **$1\le K$**：$h: c\le K$ と $1\le c$ から出るので、文の制限としては冗長です。ただし ketS_proj の型（projFunEquiv の引数）には必要です。
- **extChi で $\chi^*$ の代わりに $\chi$ を使う**（つまり extChi を chiPt にする）：
  - eqPt、torus、resE の版はそのまま成り立ちます（chiPt_eqPt と chiPt_torus がそれ自体です）。
  - changeLevel と pullP の版は崩れます。反例は chiPt_not_compat そのもので、$N=1$、$M=2$、自明指標、$q=[0:1]$ のとき $0\ne1$ です。$a=1$、$b=2$ として pullP の版でも同じです。
  - したがって、原始指標が中身を運んでいるのは level change との両立だけです。
- **extChi_eqPt / extChi_torus の [NeZero N]**：不要に見えます（確信度：中）。
  - Mathlib の導手は、指標がその法を経由する $d$ の最小値（sInf）です。法 0 では $0\mid0$ なので導手は 0 となり、$\chi^*=\chi$、red は恒等になるはずです。
  - そうなら $N=0$ でも、両定理は chiPt の版に帰着して成り立ちます。
- **extChi_changeLevel の [NeZero M]**：外すと反例が作れる見込みです（確信度：中。上と同じ「法 0 の導手は 0」という推測に依存します）。
  - $N=1$、$M=0$、$\chi$ を自明指標、$q=[0:1]\in\mathbb P^1(\mathbb Z)$ とします。
  - 左辺は $\mathrm{chiPt}(\text{持ち上げ})([0:1])$ です。0 は $\mathbb Z$ で単数でないので、値は 0 です。
  - 右辺は 1 です。
- **chiPt_red_congr の $d_1=d_2$**：不要に見えます。
  - 整数への持ち上げ $\tilde x,\tilde y$ をとると、両辺はそれぞれ $\chi_i(\tilde x)\chi_i^{-1}(\tilde y)$ です。$\chi_1,\chi_2$ が整数上で一致すれば、逆元も整数上で一致します。
  - 例えば $d_1=2$、$d_2=4$ の自明指標どうしは整数上で一致し（どちらも $a$ が奇数のとき 1、偶数のとき 0）、結論も成り立ちます。
  - 型を運ぶために置いた仮定と読めます。
- **chiPt_red_congr の hχ**：外すと反例があります。$d=M=5$、$\chi_1$ を自明指標、$\chi_2$ をルジャンドル記号、$q=[2:1]$ とすると、$1\ne-1$ です。
- **ほかの定理**：型以外に仮定がありません（mul_inv_apply_unit、chiPt_*、torus_eqPt、pullP_extChi、resE_extChi）。Lvl は正なので、pullP_extChi と resE_extChi には法 0 が入りません。

## 4. 気づいた点

1. **法 1 の扱い**：$\mathbb P^1(\mathbb Z/1)$ は 1 点で、$\mathbb Z/1$ では $0$ が単数です。そのため $\mathrm{chiPt}\,1=1$ になります。
   - この帰結として、導手 1 の指標（主指標）の extChi は $\mathbb P^1(\mathbb Z/N)$ の全点（$0$ と $\infty$ を含む）で恒等的に 1 です。
   - 一方、導手 $>1$ の指標の extChi は、法 $f$ での剰余が単数でない点で 0 です。とくに $[0:1]$ と $[1:0]$ では 0 です。
   - 「自明か非自明か」で $0$ と $\infty$ での値が 1 から 0 に跳ぶので、この扱いは意図どおりか確認してください。
2. **χ⁻¹ と複素共役**：関数として $\chi^{-1}=\bar\chi$ です（単数では $|\chi|=1$、非単数ではどちらも 0、$N=1$ では両方 1）。問題はありません。chiPt_Wproj は「$W$ は $\chi$ を $\bar\chi$ に変える」と読めます。
3. **トーラスの作用の向き**：$[x:y]\mapsto[ux:y]$ で、南の座標を $u$ 倍、北の座標を $u^{-1}$ 倍します。固有値は $\chi(u)$ です（$\chi(u)^{-1}$ ではありません）。$W\circ(u\cdot)\circ W=(u^{-1}\cdot)$ となり、chiPt_Wproj と整合します。可換群なので、作用の左右の問題はありません。
4. **extChi が well-defined な族か**：$\chi^*$ は Classical.choose で選ばれますが、原始指標は一意なので、関数としては $\chi$ だけで決まります。extChi_changeLevel と pullP_extChi が、整除の系の上での両立を与えています。
   - ただし法 0（$M=0$）では両立が崩れる見込みです（§3）。
   - さらに、注記には「節 2 の extChi では [NeZero N] を仮定に入れ、extChi_changeLevel では外した」とあります。def extChi 自体が [NeZero N] を引数に取るなら、extChi_changeLevel の右辺 extChi χ はどうやって $N\ne0$ のインスタンスを得ているのか、入力からは分かりません。extChi の実際の引数の並びの確認を勧めます。
5. **ketS_proj_zero_eq と extChi の関係**：右辺は chiPt χ（法 $p^c$）の引き戻しで、extChi ではありません。
   - 原始的でない $\chi$（例：法 $p$ の主指標、$c=1$）では、ketS_proj は $\varphi(p^K)^{-1/2}\,\mathrm{extChi}(\text{持ち上げた}\chi)$ とは異なります。主指標の場合、後者は全点で定数になります。
   - 両者が一致するのは、$\chi$ が法 $p^c$ で原始的なときです。「ケットは extChi の正規化である」と散文で書く場合は、この条件が要ります。
6. **正規化の因子**：$\varphi(p^K)^{-1/2}$ です。値が 0 でない点は $[x:1]$（$x$ は単数）のちょうど $\varphi(p^K)$ 個で、数え上げ測度で単位ノルムになります。これは $w=0$ のときだけの文です。
7. **charU の重複の可能性**：resE_extChi は PAG.Part257.charU を名前空間つきで使っています。一方、前提 3 では pullL_charU（Part258）も charU を使っており、Part257 と Part258 に同じ式の charU が 2 つある可能性があります（第 12 の型：内部の重複）。入力の範囲では、どちらの名前空間の定義かは判別できません。
8. **resE の範囲**：eqPt は単数にしか定義されていないので、resE_extChi は $[x:1]$（$x$ が単数）以外の点について何も言いません。extChi の内容は、extChi_changeLevel のほうにあります。

## 使ったツールと読んだ範囲

Read を 1 回だけ使い、`/home/claude/ardel-projective-geometry/records/audit268/input_formal.md` の全 207 行を読みました。ほかのファイル、コードの実行、ウェブは使っていません。
