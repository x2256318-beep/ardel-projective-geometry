# 独立照合の出力（PAG267、2026-11-25）

（照合者の最終報告の全文を写した。）

# PAG267 の形式文の照合結果（逆翻訳・証人・除去テスト・気づいた点）

## 1. 逆翻訳

### 定義

- **Unimod N**：$\mathbb Z/N$ の元の組 $(v_1,v_2)$ のうち、$s v_1 + t v_2 = 1$ となる $s,t\in\mathbb Z/N$ があるもの（単模ベクトル）の集合です。
  - $N=0$ のとき $\mathbb Z/0=\mathbb Z$ なので、互いに素な整数の組になります。
  - $N=1$ のときは自明環なので、組 $(0,0)$ がただ 1 つあります。
- **ProjLine N**：単模ベクトルを、単数 $u\in(\mathbb Z/N)^\times$ によるスカラー倍 $(v_1,v_2)\sim(uv_1,uv_2)$ で割った商です。$\mathbb Z/N$ 上の射影直線 $\mathbb P^1(\mathbb Z/N)$ に当たります。
- **mk**：単模ベクトルの類 $[v_1:v_2]$ です。
- **Wproj**：$[a:b]\mapsto[b:a]$（座標の入れ替え）です。
- **Wpull Φ**：$\Phi\circ \mathrm{Wproj}$ です。
- **redU（$N\mid M$）**：$\mathbb Z/M$ 上の単模ベクトルを、成分ごとに法 $N$ で還元したものです。
- **red**：redU が誘導する写像 $\mathbb P^1(\mathbb Z/M)\to\mathbb P^1(\mathbb Z/N)$ です。
- **zeroPt N**：$[0:1]$ です。
- **infPt N**：$[1:0]$ です。
- **eqPt x**（$x\in(\mathbb Z/N)^\times$）：点 $[x:1]$ です。これを「赤道」の点と呼んでいます。
- **Lvl**：正の整数の集合で、順序は $a\le b \iff a\mid b$（有向）です。
- **Gsp a**：$(\mathbb Z/a)^\times$ 上の複素数値関数の空間です。
- **pullSys a b**（$a\mid b$）：$g\mapsto g\circ(\text{単数の還元 }(\mathbb Z/b)^\times\to(\mathbb Z/a)^\times)$ です。
- **Lim**：Gsp を pullSys でつないだ帰納系の直極限（$\mathbb C$ 加群）です。
- **ofL a**：段 $a$ から Lim への標準写像です。
- **Fsp a**：$\mathbb P^1(\mathbb Z/a)$ 上の複素数値関数の空間です。
- **pullP a b**：$f\mapsto f\circ \mathrm{red}$ です。
- **LimP**：Fsp を pullP でつないだ直極限です。
- **ofP**：段から LimP への標準写像です。
- **Wfun a**：段 $a$ での Wpull です。
- **WL**：Wfun が誘導する LimP 上の線形写像です。
- **resE a**：$f\mapsto (x\mapsto f([x:1]))$（赤道への制限）です。
- **resL**：resE が誘導する写像 LimP → Lim です。
- **extE a**：$g\mapsto$「$q=[x:1]$ となる単数 $x$ があれば $g(x)$、なければ $0$」（赤道の外を 0 で延ばす写像）です。$x$ は選択公理で選びますが、eqPt が単射なので値は一意に決まります。
- **lv1**：段 1 です。
- **lv2**：段 2 です。

### 定理

（$N,M,L$ は 0 を含む任意の自然数です。）

- **red_mk**：$\mathrm{red}[v]=[v \bmod N]$。
- **red_self**：$N\mid N$ に対する red は恒等写像。
- **red_comp**：$N\mid M\mid L$ なら、$L\to M\to N$ と還元したものは $L\to N$ の還元に等しい。
- **red_Wproj**：還元は座標の入れ替えと可換。
- **Wproj_zeroPt / Wproj_infPt**：入れ替えは $[0:1]$ と $[1:0]$ を互いに移す。
- **red_zeroPt / red_infPt**：還元は $[0:1]$ を $[0:1]$ に、$[1:0]$ を $[1:0]$ に移す。
- **zeroPt_ne_infPt**：$N\ne1$ なら $\mathbb P^1(\mathbb Z/N)$ で $[0:1]\ne[1:0]$。
- **exists_redU**：$M\ne0$、$N\mid M$ とする。法 $N$ の任意の単模ベクトル $v$ に対し、法 $M$ の単模ベクトル $w$ で、その還元が $v$ と射影的に同値なものがある。
- **red_surjective**：$M\ne0$、$N\mid M$ なら、$\mathbb P^1(\mathbb Z/M)\to\mathbb P^1(\mathbb Z/N)$ は全射。
- **eqPt_injective**：$x\mapsto[x:1]$ は単射。
- **red_eqPt**：$[x:1]$ の還元は $[x \bmod N:1]$。
- **isUnit_of_castHom**：次の 3 つを仮定する。
  - $M\ne0$ かつ $N\mid M$。
  - $M$ の素因数はすべて $N$ を割る。
  - $c\in\mathbb Z/M$ の法 $N$ での像が単数である。

  このとき $c$ は $\mathbb Z/M$ の単数。
- **exists_eqPt_of_red**：isUnit_of_castHom と同じ仮定のもとで、$q\in\mathbb P^1(\mathbb Z/M)$ の還元が赤道の点 $[x:1]$ に等しいなら、$q$ 自身も赤道の点（ある単数 $y$ で $q=[y:1]$）。
- **pullP_injective**：段の間の引き戻し pullP は単射。
- **ofP_injective**：各段から LimP への標準写像は単射。
- **Wfun_comp_pullP**：入れ替えの引き戻しは、段の間の引き戻しと可換。
- **WL_ofP**：WL は段 $a$ では Wfun として働く。
- **WL_WL**：WL は対合（2 回で恒等）。
- **resE_comp_pullP**：赤道への制限は引き戻しと可換。すなわち $\mathrm{resE}_b(f\circ\mathrm{red})=\mathrm{resE}_a(f)\circ(\text{単数の還元})$。
- **resL_ofP**：resL は段 $a$ では resE として働く。
- **resL_surjective**：resL は全射。
- **extE_eqPt**：$\mathrm{extE}(g)([x:1])=g(x)$。
- **extE_off**：赤道の外では $\mathrm{extE}(g)=0$。
- **resE_extE**：$\mathrm{resE}\circ\mathrm{extE}=\mathrm{id}$。
- **extE_compat_iff**：$a\mid b$ のとき、次の 2 つは同値。
  - すべての $g$ について $\mathrm{extE}_b(g\circ\text{還元})=\mathrm{extE}_a(g)\circ\mathrm{red}$。
  - $b$ の素因数はすべて $a$ を割る（$\mathrm{rad}(b)\mid a$）。
- **lv1_le_lv2**：$1\mid 2$。
- **extE_not_compat**：段 1 のある関数 $g$ について、$\mathrm{extE}_2(g\circ\text{還元})\ne \mathrm{extE}_1(g)\circ\mathrm{red}$。
- **not_exists_extL**：すべての段 $a$ とすべての $g$ で $E(\mathrm{ofL}_a g)=\mathrm{ofP}_a(\mathrm{extE}_a g)$ を満たす $\mathbb C$ 線形写像 $E:\mathrm{Lim}\to\mathrm{LimP}$ は存在しない。

## 2. 非空虚性の証人

- **red 系（red_mk、red_self、red_comp、red_Wproj）**：$N=2,M=4,L=8$、$q=[3:2]\in\mathbb P^1(\mathbb Z/8)$ を取ります。
  - $q$ を法 4 に還元すると $[3:2]$、法 2 に還元すると $[1:0]$ です。
  - 入れ替えてから還元すると、法 2 で $[0:1]$ になり、還元してから入れ替えたものと一致します。
- **zeroPt_ne_infPt**：$N=2$ では $[0:1]\ne[1:0]$ です（スカラー倍は 1 だけなので）。
- **exists_redU、red_surjective**：$N=3,M=6,v=(2,0)$ を取ります。
  - 素朴な持ち上げ $(2,0)$ は法 6 で単模ではありません。
  - $w=(2,3)$（$2\cdot2+3\cdot1=7\equiv1$）は単模で、法 3 に還元すると $(2,0)$ です。
  - したがって、この定理は持ち上げを調整する必要がある場合を含んでいます。
- **eqPt_injective、red_eqPt**：$N=3,M=9,x=4$ を取ると、$[4:1]\mapsto[1:1]$ です。
- **isUnit_of_castHom**：$N=2,M=4,c=3$ を取ります。$3 \bmod 2=1$ は単数で、$3$ は法 4 の単数です。
- **exists_eqPt_of_red**：$N=2,M=4$ を取ります。
  - $q=[1:2]$ の還元は $[1:0]$ で赤道ではないので、この $q$ では仮定が成り立たず、文は空になります。
  - $q=[3:1]$ の還元は $[1:1]$（赤道）で、確かに $q=[3:1]$ も赤道の点です。
- **pullP_injective、ofP_injective**：$a=1,b=2$ を取ります。$f$ を定数 $c$ とすると引き戻しも定数 $c$ なので、$c$ が復元できます。
- **WL 系（Wfun_comp_pullP、WL_ofP、WL_WL）**：$a=3$、$f=$「$[0:1]$ で 1、それ以外で 0」を取ります。
  - Wfun で $[1:0]$ の指示関数に移り、もう 1 回で元に戻ります。
- **resE_comp_pullP、resL_ofP、resL_surjective**：$a=2,b=4$ を取ります。
  - $f$ を法 2 の $\mathbb P^1$ 上の関数とすると、法 4 の赤道 $\{[1:1],[3:1]\}$ 上で $f([1:1])$ の値を取ります。
  - 全射性の証人は $\mathrm{ofL}_a g=\mathrm{resL}(\mathrm{ofP}_a(\mathrm{extE}_a g))$ です。
- **extE_eqPt、extE_off、resE_extE**：$a=4$、$g(1)=5,\ g(3)=7$ を取ります。
  - $\mathrm{extE}(g)$ は $[1:1]\mapsto5$、$[3:1]\mapsto7$ で、$[0:1],[1:0],[2:1],[1:2]$ では 0 です。
- **extE_compat_iff の真の側**：$a=2,b=4$ を取ります。
  - 赤道の外の点 $[0:1],[1:0],[2:1],[1:2]$ は、法 2 でそれぞれ $[0:1],[1:0],[0:1],[1:0]$ に還元され、どれも赤道の外です。
  - したがって両辺とも 0 になり、一致します。
- **extE_compat_iff の偽の側**：$a=2,b=6$ を取ります。
  - $q=[3:1]$ は赤道の外（3 は法 6 で単数でない）ですが、法 2 で $[1:1]$（赤道）に還元されます。
  - $g=1$ とすると左辺は 0、右辺は 1 です。
- **extE_not_compat**：段 1 で $g=1$ を取ります。
  - $\mathbb P^1(\mathbb Z/1)$ は 1 点で、それが赤道なので $\mathrm{extE}_1 g=1$ です。引き戻すと $\mathbb P^1(\mathbb Z/2)=\{[0:1],[1:0],[1:1]\}$ 上の定数 1 になります。
  - 一方 $\mathrm{extE}_2(1)$ は $[1:1]$ でだけ 1 なので、$[0:1]$ で食い違います。
- **not_exists_extL**：上の $g$ で $\mathrm{ofL}_1 g=\mathrm{ofL}_2(\text{引き戻し})$ です。
  - $E$ があれば $\mathrm{ofP}_2(\mathrm{pullP}(\mathrm{extE}_1 g))=\mathrm{ofP}_2(\mathrm{extE}_2(\ldots))$ となります。
  - ofP_injective により extE_not_compat と矛盾します。

## 3. 除去テスト（手計算）

- **zeroPt_ne_infPt の $N\ne1$**：外すと反例があります。$N=1$ では $\mathbb P^1$ は 1 点なので $[0:1]=[1:0]$ です。この仮定は必要です。$N=0$（$\mathbb Z$、単数は $\pm1$）では成り立ちます。
- **exists_redU・red_surjective の [NeZero M]**：$M=0$ のときは $\mathbb P^1(\mathbb Z)\to\mathbb P^1(\mathbb Z/N)$ の全射性を言うことになり、これは成り立ちます（$\mathrm{SL}_2(\mathbb Z)\to\mathrm{SL}_2(\mathbb Z/N)$ が全射、という既知の事実による）。反例は作れないので、**この仮定は不要に見えます**（証明の便宜と思われます）。
- **isUnit_of_castHom・exists_eqPt_of_red の [NeZero M]**：$M=0$ のとき、素因数の条件は「すべての素数が $N$ を割る」となり、$N=0$ を強制します。すると還元は $\mathbb Z\to\mathbb Z$ の恒等写像で、文は自明に成り立ちます。**不要に見えます**。
- **素因数の条件 $\forall p$（isUnit_of_castHom）**：外すと反例があります。$N=1,M=2,c=0$ では、$0 \bmod 1$ は（自明環の）単数ですが、$0$ は法 2 の単数ではありません。$N\neq1$ の例としては $N=2,M=6,c=3$ があります。
- **素因数の条件（exists_eqPt_of_red）**：外すと反例があります。
  - $N=2,M=6,q=[3:1]$ では、還元は $[1:1]=\mathrm{eqPt}(1)$ ですが、$q$ は赤道の点ではありません。$[3:1]=[y:1]$ ならスカラー倍は $u=1$ に限られ、$y=3$ は単数でないからです。
  - $N=1,M=2,q=[0:1]$ も反例です。
- **$N\mid M$**：型の上で必要な仮定なので、外すことはできません。
- **extE_compat_iff の右辺**：右辺を外して「左辺が常に成り立つ」とする文は偽です。反例は $a=1,b=2$（extE_not_compat）と $a=2,b=6$ です。逆向き（左辺 ⇒ 右辺）も上の構成で確認できます。
  - $p\mid b,\ p\nmid a$ なら、中国剰余定理で $x\equiv1\pmod a$、$x\equiv0\pmod p$ を取ります。
  - $q=[x:1]$ は赤道の外（または $[0:1]$ など）で、還元は $[1:1]$ になります。
- **not_exists_extL**：仮定のない否定文なので、除去の対象はありません。

## 4. 気づいた点

1. **法 0 と法 1**：
   - red・ProjLine・zeroPt などは $N=0$（$\mathbb Z$）でも定義され、各文も成り立ちます。一方、Lvl は正の整数だけなので、極限には法 0 は入りません。
   - 法 1 では 1 点が $[0:1]$ でも $[1:0]$ でも $[1:1]$ でもあります。そのため「段 1 の赤道は $\mathbb P^1$ 全体」となり、extE_not_compat はちょうどこの性質を使っています。
   - 「0・∞・赤道」という呼び名は、段 1 では区別を失います。
2. **赤道の定義**：
   - 赤道は $[x:1]$（$x$ は単数）の形の点だけで、これは「両座標がともに単数」の点と同じ集合です。
   - $N$ が素数なら $\mathbb P^1=\{0,\infty\}\cup$ 赤道となります。合成数の $N$ では、どちらにも入らない点（法 4 の $[2:1],[1:2]$、法 6 の $[2:1],[3:1]$ など）があります。
   - したがって「赤道の外」は「0 と ∞」と同じではありません。ノートで「赤道の補集合＝両極」と読まれないように注意が要ります。
3. **extE の choose**：eqPt が単射なので値は選び方によらず、well-defined です。問題はありません。
4. **極限の上の写像の well-defined 性**：
   - WL と resL は Module.DirectLimit.map に、可換性（Wfun_comp_pullP、resE_comp_pullP）を渡して作られています。可換性は形式文として示されているので、well-defined です。
   - extE は可換性を満たさない（extE_compat_iff）ので、極限に降ろす写像は定義されていません。not_exists_extL はそのことを、極限の上の線形写像の不存在として述べています。
5. **not_exists_extL の範囲**：
   - 否定しているのは「すべての段で extE と両立する $E$」だけです。resL は全射なので、ℂ 加群として線形な切断は（選択公理により）存在します。この定理はそれを否定していません。
   - 散文で「resL には切断がない」と読まないようにする必要があります。
   - なお手計算では、両立を共終な部分系の段だけに弱めても不存在は保たれます。共終性から新しい素数を持ち込む段 $a\mid b$ が必ず現れ、そこで extE_compat_iff の偽の側に当たるためです。ただしこれは形式化されていません。
6. **resL の行き先**：Lim は単数の上の関数（Gsp）の極限で、Uinf と同じ空間です。この点は意図どおりです。
   - $\widehat{\mathbb Z}^\times$ 上の局所定数関数との同一視は、この入力には文がありません（読みです）。
7. **未記載の関係**：
   - WL と resL の関係を述べる文がありません。$\mathrm{Wproj}[x:1]=[1:x]=[x^{-1}:1]$ なので、期待される関係は「$\mathrm{resL}\circ\mathrm{WL}=(\text{単数の逆元による引き戻し})\circ\mathrm{resL}$」です。
   - WL と Uinf を結ぶ文もありません。
8. **Lim のスカラー**：Lim には $\mathbb C$ 加群の構造しか与えられていません。積・代数の構造はこの入力にはありません。

## 使ったツールと読んだ範囲

Read を 1 回だけ使い、`/home/claude/ardel-projective-geometry/records/audit267/input_formal.md` の全体（285 行）を読みました。ほかのファイルは読まず、コードの実行とウェブの利用もしていません。上の反例と証人はすべて手計算で、数値や Lean では確かめていません。
