# PAG264 形式文の照合（逆翻訳・非空虚性の証人・除去テスト・気づいた点）

**読んだ範囲とツール**：`input_formal.md` の全文（1〜421 行）を Read で 1 回読んだだけ。コード実行・ウェブ・他ファイルは使っていない。以下の具体例・反例はすべて手計算で、数値での確認はしていない。（独立性の記録：システムが最初から文脈に入れていたプロジェクトの CLAUDE.md とユーザーのメモリには、Part 259 までの経緯（Part 258 の「殻を混ぜない」の読みなど）が書かれている。PAG264 の散文は含まれていない。4 の (b) はこの文脈に触発された指摘。）

## 0. 記号と定義

- N, M は 0 でない自然数で N | M。π: ℤ/M → ℤ/N は還元写像（環準同型）。V_N = ℤ/N 上の複素数値関数。End(V_N) はその線形変換全体で、積は合成。x̃ ∈ {0,…,N−1} は代表元。
- 畳み込み (f*g)(x) = Σ_y f(y) g(x−y)。
- 殻：dind_N(s) は {ξ ∈ ℤ/N : gcd(N, ξ̃) = s} の指示関数。gcd(N, 0) = N なので殻 N は {0}。s ∤ N（s = 0 を含む）なら殻は空で dind_N(s) = 0。
- D^N_s は dind_N(s) を掛ける作用素。geps_N(s) は dind_N(s) の逆離散フーリエ変換で、E^N_s は geps_N(s) との畳み込み作用素。証明に使われている畳み込み定理（文は入力にない）のもとでは、E^N_s は「フーリエ側で殻 s の周波数だけを残す射影」。
- A_N（shellAlg N）は、すべての s の E^N_s と D^N_s が生成する End(V_N) の部分代数（単位元を含む）。
- pull: V_N → V_M、(pull f)(y) = f(π(y))。
- oldP_{N,t}(g) = (1/t)(1_K * g)（M = Nt、K = ker π は t 個の元）で、剰余類 y+K の上での g の平均。
- 非単位的代数準同型とは、ℂ 線形で積を保つ写像のこと。単位元を保つことは要求しない。

**主な定義**
- fsum: V_M → V_N、(fsum g)(x) = Σ_{π(y)=x} g(y)（ファイバーの和、押し出し）。pullLin・fsumLin は pull・fsum を線形写像として束ねたもの。
- cornerOp(S) = (N/M)·pull∘S∘fsum（S ∈ End(V_N)）。行列の (y, y′) 成分は (N/M)·S_{π(y), π(y′)}。P := cornerOp(1) は「π の同じファイバー上での平均」で、像は pull(V_N)。
- cornerHom: A_N → A_M、S ↦ cornerOp(S)。非単位的代数準同型。

## 1. 逆翻訳

- **fsum_add / fsum_smul**：fsum は和とスカラー倍を保つ。
- **card_fiber**：π のどのファイバーもちょうど M/N 個の元を持つ。
- **fsum_pull**：fsum(pull f) = (M/N)·f。
- **cornerOp_apply**：cornerOp(S)g = (N/M)·pull(S(fsum g))。
- **scal_cancel**：N, M ≠ 0 なら複素数として (N/M)(M/N) = 1。
- **cornerOp_pull**：すべての S ∈ End(V_N) と f で cornerOp(S)(pull f) = pull(Sf)。
- **cornerOp_mul / _add / _smul / _zero**：cornerOp は合成・和・スカラー倍・0 を保つ。
- **cornerOp_one_mul / _mul_one**：P·cornerOp(S) = cornerOp(S) = cornerOp(S)·P。
- **cornerOp_injective**：S ↦ cornerOp(S) は End(V_N) 全体で単射。
- **fsum_single**：c δ_{y0}（y0 で c、他で 0）について fsum(c δ_{y0})(x) = [π(y0) = x]·c。
- **cornerOp_one_single**：P(δ_0)(0) = N/M。
- **cornerOp_one_ne_one**：N &lt; M なら P は恒等写像でない。
- **pull_fsum**（M = Nt）：pull∘fsum = t·oldP_{N,t}。
- **cornerOp_one_apply**（M = Nt）：P = oldP_{N,t}。
- **conv_geps_oldP**（M = Nt、任意の s）：E^{Nt}_{ts}∘oldP = E^{Nt}_{ts}。
- **cornerOp_geps_mul**（M = Nt、任意の s）：cornerOp(E^N_s) = E^{Nt}_{ts}。
- **cornerOp_one**：P = Σ_{s | M, (M/N) | s} E^M_s。
- **cornerOp_geps**（任意の s）：cornerOp(E^N_s) = E^M_{(M/N)s}。
- **pull_dind**（任意の s）：pull(dind_N(s)) = Σ_{u | M, gcd(u,N) = s} dind_M(u)。
- **mulLeft_sum**：有限和を掛ける作用素は、各項を掛ける作用素の和。
- **mulLeft_pull_dind_mem**：pull(dind_N(s)) を掛ける作用素は A_M に属する。
- **cornerOp_dind**：cornerOp(D^N_s) =（pull(dind_N(s)) を掛ける作用素）∘P。
- **cornerOp_one_mem**：P ∈ A_M。
- **cornerOp_mem**：S ∈ A_N なら cornerOp(S) ∈ A_M。
- **cornerHom_coe**：cornerHom(S) の中身の作用素は cornerOp(S)。
- **existsUnique_corner**：N | M のとき、非単位的 ℂ 代数準同型 φ: A_N → A_M で、(i) すべての S ∈ A_N と f ∈ V_N について φ(S)(pull f) = pull(Sf)、(ii) φ(恒等写像) = Σ_{s | M, (M/N) | s} E^M_s、を満たすものがちょうど 1 つある（証明項ではそれは cornerHom。これは文の外の情報）。
- **fsum_trans**（N | M | L）：L→N の fsum = （L→M の fsum の後に M→N の fsum）。
- **cornerOp_comp**（N | M | L、すべての S ∈ End(V_N)）：cornerOp_{M→L}(cornerOp_{N→M}(S)) = cornerOp_{N→L}(S)。
- **cornerHom_comp**：A_N → A_M → A_L の合成は A_N → A_L の cornerHom に等しい。
- **cornerHom_injective**：cornerHom は単射。
- **cornerHom_one_ne_one**：N &lt; M なら cornerHom(1) ≠ 1。
- **cornerOp_dind_not_mem_span**：N = 2, M = 4 で、cornerOp(D^2_2)（D^2_2 は ℤ/2 の点 0 の指示関数を掛ける作用素）は D^4_u（u ∈ ℕ）の線形結合ではない。

## 2. 非空虚性の証人

すべての定理で仮定は満たせる。空虚な定理はない。(N, M) = (2, 4) の計算：基底 δ_0, …, δ_3、π は 0, 2 ↦ 0、1, 3 ↦ 1。P g = ((g0+g2)/2, (g1+g3)/2, (g0+g2)/2, (g1+g3)/2)。A_2 = End(V_2)（D^2_2 = diag(1,0) と E^2_2 = (1/2)[[1,1],[1,1]] が M_2 を生成する。確信度：高）。A_4 ≠ End(V_4)（A_4 の元はすべて x ↦ −x の置換と可換。確信度：高）。

- **cornerOp_mem**：(2,4) では A_2 = End なので、仮定は任意の S = [[a,b],[c,d]] で満たされる。主張は、4×4 行列 (1/2)[[a,b,a,b],[c,d,c,d],[a,b,a,b],[c,d,c,d]] が A_4 に入ること。A_4 ≠ End(V_4) なので中身のある主張。例：S = D^2_2 なら g ↦ ((g0+g2)/2, 0, (g0+g2)/2, 0) = (D^4_4 + D^4_2)P。
- **existsUnique_corner**：(2,4) では φ は上の行列の写像、(ii) の右辺は E^4_2 + E^4_4（E^4_4 g は平均の定数関数、E^4_2 g = ((g0−g1+g2−g3)/4)(1,−1,1,−1)、和は P）。(1,2)：A_1 = ℂ で φ(c) = c·（ℤ/2 上の平均）。(2,6)：(ii) の右辺は E^6_3 + E^6_6（周波数 {0, 3} への射影）。
- **cornerOp_comp / cornerHom_comp**：(2, 4, 8)、S = D^2_2 で、両辺とも g ↦ 1_{偶数}(y)·(g0+g2+g4+g6)/4。
- **cornerOp_one**：(2,4)：P = E^4_2 + E^4_4。(2,6)：P = E^6_3 + E^6_6（平行移動 2 で不変な関数への射影）。(1,M)：P = E^M_M（平均）。(N,N)：Σ_s E^N_s = 1（1 の分割）。
- **cornerOp_geps**：(2,4)：E^2_1 ↦ E^4_2、E^2_2 ↦ E^4_4。(2,6)：E^2_1 ↦ E^6_3。s = 0 や s ∤ N では両辺 0 で自明。
- **cornerOp_dind**：(2,4)、s = 2：pull(dind_2(2)) = 1_{0,2} = dind_4(4) + dind_4(2)。作用素は g ↦ ((g0+g2)/2, 0, (g0+g2)/2, 0)。
- **cornerOp_one_ne_one**：(1,2) で P δ_0 = (1/2, 1/2) ≠ δ_0。
- **cornerOp_dind_not_mem_span**：仮定なし。上の作用素が diag(α, β, γ, β) の形でないという主張（δ_0 に作用させると点 2 で値 1/2、対角作用素なら 0）。

## 3. 除去テスト

**existsUnique_corner**
- **(ii) を外すと一意性が崩れる**。反例 1：(1,2)。cornerHom(c) = cP のほかに、φ′(c) = c·1 も (i) を満たす。反例 2：(2,4)。e = P + P·D^4_4·(1−P)（冪等で、pull(V_2) 上で恒等。P·D^4_4·(1−P)δ_0 = (δ_0+δ_2)/4 ≠ 0 なので e ≠ P）とし、φ′(S) = cornerOp(S)∘e。φ′ は (i) を満たし、積を保ち、A_4 に値を取る。反例 2 から、(ii) を「φ(1) は像が pull(V_N) の冪等元」に弱めることもできない。（N = M のときは (ii) は (i) から出る。）
- **(i) を外すと一意性が崩れる**。反例：(2,4)、g = D^2_2 − D^2_1 = diag(1, −1)、φ″(S) = cornerOp(gSg⁻¹)。φ″(1) = P で (ii) は満たすが、φ″(E^2_2) = E^4_2 ≠ E^4_4 = cornerHom(E^2_2)。（(2,2) なら内部自己同型 S ↦ gSg⁻¹ そのものが反例。N = 1 のときは (i) は (ii) から出る。）
- **型に入っている「積を保つ」を外すと一意性が崩れる**。例：(2,4) で φ(S) = cornerOp(S) + (S の (0,1) 成分)·(1−P) は (i)(ii) を満たす。一意性の証明は乗法性に依存している。

**cornerOp_mem**
- S ∈ A_N を外すと偽になる。反例：N = M = 3、S = 1_{1} を掛ける作用素。cornerOp(S) = S は x ↦ −x と可換でないので A_3 に入らない（N = 3, M = 6 でも同じ理由で反例）。(2,4) では A_2 = End なので、この仮定は自動的に成り立ち、除去しても何も変わらない。

**外せる仮定がない定理**
- cornerOp_comp・cornerHom_comp・cornerOp_one・cornerOp_geps の仮定は整除と非零だけで、どれも文を書くのに必要。cornerOp_comp は S ∈ A_N を仮定せず、End(V_N) 全体で成り立つ。cornerOp_dind は dind_N(s) を任意の関数 f に替えても成り立つ。

**cornerOp_one_ne_one / cornerHom_one_ne_one**：N &lt; M を外して N = M（例：(1,1)）にすると P = 1 で偽。この仮定は必要。

**cornerOp_dind_not_mem_span（パラメータを替えた変種）**：(1,2) でも同じ形の文が成り立つ（cornerOp(D^1_1) = P は掛け算作用素でない）。(2,6) でも成り立つ（点 2 で値 1/3）。(N,N) では cornerOp が恒等写像で偽。

## 4. 気づいた点

- **(a)** (2,4) では N = M/N = 2 なので、N と M/N の取り違えを検出できない。例えば cornerOp_one の「M/N | s」を「N | s」に替えても同じ値になる。(1,2) や (2,6) では区別できる（(1,2) で取り違えると和が 1、(2,6) では周波数 {0, 2, 4}）。数値照合には N ≠ M/N の組を必ず入れるべき。
- **(b)** cornerOp_dind_not_mem_span の現象は (2,4) に固有ではない。N &lt; M で殻が空でなければ、いつでも起きる。互いに素な (1,2) や (2,6) でも成り立つ（確信度：高）。この文を「N と M/N が共通の素因数を持つ場合に固有の現象」の証拠として読むと、形式文の内容を超える。
- **(c)** 一意性の中身は短い議論：φ(S) = φ(S)φ(1)、(ii)、(i) の 3 つから出る。(ii) は φ(1) = P を周波数の殻の和で書いたもので、cornerOp_one により φ(1) = cornerOp(1) と同値。「pull との両立だけで一意に決まる」とは読めない。
- **(d)** 文が主張していないこと：cornerHom の像が P·A_M·P 全体に等しいこと（主張から出るのは包含だけ。(2,4) では次元がどちらも 4 なので等しくなる（手計算）が、一般には分からない）。随伴を保つこと（標準内積で cornerOp(S*) = cornerOp(S)*。行列の形から成り立つはず、手計算）。
- **(e)** 退化する場合：N = M では π も cornerOp も恒等。N = 1 では A_1 = ℂ で cornerHom(c) = c·E^M_M。s = 0 や s ∤ N では関係する文が 0 = 0 になる。
- **(f)** 型：`M / N` は自然数の割り算だが、N | M のもとで割り切れるので切り捨ては起きない。cornerOp のスカラー (N:ℂ)/M は複素数の割り算。`omit [NeZero N]` は意味を変えない（N | M かつ M ≠ 0 なら N ≠ 0。ZMod 0 = ℤ の場合は起きない）。`M / N * s` は (M/N)·s と読まれる。`φ 1` の 1 は A_N の単位元（恒等写像）。
- **(g)** 名前の読み違いに注意：D^2_2 は 0 の殻（gcd(2, 0) = 2）を掛ける作用素で、単数の殻は s = 1。E^N_s を周波数の射影として読む根拠は、入力にない畳み込み定理。ただし dind は偶関数なので、フーリエ変換の符号規約には左右されない。
