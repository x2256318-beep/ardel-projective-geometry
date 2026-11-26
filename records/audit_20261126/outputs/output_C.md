# 2026-11-26・盲検の命名テスト C（幾何の層）の出力

（照合者の最終報告の全文を写した。依頼文は `../requests/request_C_naming.md`、時刻は `meta.txt`。）

## 照合結果：(X)(Y)(Z) の文献での名前

**要約**：(X) と (Y) は既知の枠組みの特別な場合・有限レベル版と判定した（(Y) の固有値の主張は数値でも確認）。(Z) は部品はすべて標準的だが、「σ と赤道上の U_∞ を P¹ 全体に延ばす」という組み立てを扱った文献は見つからなかった（見つからなかったことは不存在の証明ではない）。

### 1. 対象ごとの名前の候補

**(X) 点の集合と座標**
- **候補 1：Arakelov のコンパクト化 Spec ℤ̄ = Spec ℤ ∪ {∞} と、その Arakelov 因子（Neukirch の replete divisor）**。一致する範囲：Schoof の定義では、有限素点の係数は整数、無限素点の係数は実数で、主因子は n_p = ord_p(f)、x_∞ = −log|f|（Schoof, *Computing Arakelov class groups*、https://www.mat.uniroma2.it/~schoof/infranew2.pdf、本文、2004 予備版）。q ↦ (v_p(q), log q) は、∞ 成分の符号を除いて主 Arakelov 因子の写像そのもの。食い違う点：Arakelov 理論は因子類群（次数が ℝ）を見るので、「T を選んで像の稠密・離散を問う」問いは中心の問いではない。確信度：高。
- **候補 2：「∞ を一点として加えた対象」としての Spec ℤ̄（F₁ 幾何・Durov・Haran・Takagi の代数的コンパクト化）**。確かめた文献：arXiv:1203.4914 *Compactifying Spec ℤ*（要旨）。凸環スキームの Zariski–Riemann 空間として Spec ℤ ∪ {∞} を作り、Durov・Haran のコンパクト化とほぼ一致すると述べる（著者名 Takagi は私の推定で、取得した要旨では未確認）。食い違う点：構造層を問題にし、座標の像の位相は扱わない。確信度：中。
- **候補 3：「測る点の集合を選ぶ」操作 ＝ 素点の集合への制限（S 進アデール・S イデール、Connes の半局所の設定）**。確かめた文献：Connes, *Trace formula in NCG and the zeros of the Riemann zeta function*（https://ar5iv.labs.arxiv.org/html/math/9811068、本文の冒頭 10 万字）。有限素点集合 S について ∏_{v∈S} k_v を S 単数の群 O_S^* で割った商と、イデール類群 C_S を扱う。稠密・離散の判定は、Dirichlet の S 単数定理（S 単数の log 像は和 0 の超平面の格子）を T の座標へ射影した結果として出る（log p の ℚ 上の一次独立だけを使う初等的事実。私の推論で、この形の記述は文献で確かめていない）。確信度：中。
- **形式文への指摘（独自の計算）**：T∖S に素数があると、像は ℤ^{T_f}×ℝ の真の閉部分群 ℤ^{S∩T}×{0}×ℝ に含まれる。したがって「稠密」は ℤ^{T_f}×ℝ 全体ではなく、この部分群の中での稠密と読む必要がある。

**(Y) 有限レベルの変換 Φ_N と U_∞**
- **候補 1：Fourier 変換と反転の合成 FI（Tate の局所関数等式を作用素として書いたもの）**。確かめた文献：Burnol, *Scattering on the p-adic field and a trace formula*（arXiv:math/9901051、要旨と取得した要約）。FI は伸縮と可換で Tate–Gel'fand–Graev のガンマ関数で対角化され、単数の指標ごとの成分 L²_χ への分解もある。Burnol の math/9811040・math/9902080（要旨のみ）は、Fourier 変換の「乗法の言葉で見たもの」とガンマ関数を結びつける。Φ_N はこの作用素の ℤ/N 版（核は実数値の cas）。有限体の場合の基本の式 F(λ) = g(λ)·λ⁻¹ は Kazhdan–Polishchuk, *Fourier transform over finite field and identities between Gauss sums*（https://ar5iv.arxiv.org/html/math/0003011、本文の冒頭）にあり、これに反転を合成すれば χ が固有値 g(χ) の固有関数になる。確信度：高。
- **候補 2：根数（ε 因子）**。W(χ) = τ(χ)/(i^a√N) は L(s,χ) の根数の標準形（私の知識、Davenport 第 9 章。取得した文献では未確認）。大域 ε が局所 ε の積で、有限素点ではほぼガウス和、無限素点では i の冪であることは Buzzard のノート *Epsilon constants*（https://www.ma.ic.ac.uk/~buzzard/maths/research/notes/epsilon_constants.pdf、本文）で確認（ディリクレ指標の明示式はこのノートにない）。数値確認（/tmp/naming_C/check.py）：N = 3, 4, 5, 7, 8, 9, 12, 15, 16 のすべての原始指標で、Φ_N χ = W(χ)χ が誤差 7×10⁻¹⁵ 以下で成立。
- **候補 3：U_∞ は Ẑ^× = lim← (ℤ/N)^× の上の局所定数関数の空間に作用する、ε 因子による対角ユニタリ（指標 χ を W(χ*) 倍する掛け算作用素）**。大域の対象としては、有限アデールの Fourier 変換と反転の合成を Ẑ^× の指標の成分ごとに見て s = 1/2 で評価し、無限素点の符号因子を掛けたもの（Burnol の局所作用素の積と Tate の大域関数等式から私が組み立てた読み）。固有の名前は見つからなかった。Meyer の math/0311468（Duke 2005）は要旨のみで、指標分解は確かめられなかった。確信度：中（構成は既知の部品から出る）。
- **Weil 表現との関係**：DFT は Weil 表現 ρ(w) のスカラー倍で、対角トーラスは 2 次指標の因子つきの伸縮で作用する（Gurevich–Hadani–Sochen, arXiv:0808.3281、取得した要約で定理 4.1 と §3.2）。反転 u ↦ u⁻¹ は Weil 表現のトーラス作用に含まれないので、Φ_N は Weil 表現の元ではなく「ρ(w) と反転の合成」。

**(Z) 射影直線の上の構造**
- **候補 1：P¹(ℤ/N) の射影系、極限は P¹(Ẑ) = ∏_p P¹(ℤ_p)（＝ P¹(A_f)）**。P¹(ℤ/N) の定義はモジュラー記号での標準の定義と同じ（W. Stein の講義ノート https://williamstein.org/edu/2006/spring/583/notes/2006-04-19/2006-04-19.pdf、本文。Manin 記号の添字集合 Γ₀(N)\SL₂(ℤ)）。食い違う点：Manin 記号の対合は S による (c:d) ↦ (d:−c) で、σ の [a:b] ↦ [b:a] と符号の規約が違う（この S の作用は、ノートが明示していない行列計算から取得の要約が推定したもので未確認）。目的も違い、Manin 記号はカスプ形式のホモロジーのための 3 項関係の商を扱う（この食い違いは確か）。極限 P¹(Ẑ) と L が局所定数関数の空間になることは私の推論で、文献では未確認。確信度：中。
- **候補 2：GL₂(ℤ/N) の主系列 Ind_B^G(1)（＝ P¹ の上の関数）**。σ は Weyl 元、diag(u,1) は分裂トーラス、χ(a)χ̄(b) はトーラスの固有ベクトル。Weyl 元の絡作用素 Σ_u f(J⁻¹ug) の固有値がガウス和の形になることは、GL_{2n} の REU ノート（https://dfoiler.github.io/umich-reu/intertwining.pdf、本文、命題 2.5.6）で確認（特別なベクトルについての結果で、β = 1 では固有値は q の冪）。「赤道上の Φ_N の延長が主系列の絡作用素になる」対応は未確認。確信度：低〜中。
- **候補 3：G_m の同変なコンパクト化（トーリック多様体）としての P¹（σ は反転 t ↦ t⁻¹）**。私の知識で文献未確認。ℤ/N の上では [p:1] のような点があるので、トーラス軌道は 3 つより多い。赤道は単数の軌道 G_m(ℤ/N)。確信度：中。

### 2. 対象ごとの判定
- **(X)：既知の対象の特別な場合。** 点の集合と座標は Arakelov の主因子そのもの。稠密・離散の判定は S 単数の格子の射影についての初等的事実（名前のついた定理としては見つかっていない）。
- **(Y)：既知の対象の有限レベル版。** Φ_N は Tate・Gel'fand–Graev・Burnol の作用素 FI の ℤ/N 版（核は Hartley の cas）で、固有値は古典的な根数。U_∞ は ε 因子による掛け算作用素で、構成は既知の部品から直ちに出る（固有の名前は見つかっていない）。
- **(Z)：近いが違う。** 部品（P¹(ℤ/N)、Weyl 元、トーラス、主系列）はすべて既知。σ と赤道上の U_∞ を組み合わせ、P¹ 全体への延長の一意性を問う設定は文献で見つかっていない。延長が一意にならないことは、Φ_N が GL₂ の幾何的作用から来ていないこと（Fourier の部分は P¹ の上の点の写像ではない）と整合する（私の解釈）。

### 3. 全体として収まる枠組み
全体としては、**Tate の学位論文（局所・大域の関数等式と ε 因子）＋ Connes・Burnol のアデールの作用素論 ＋ Arakelov の Spec ℤ̄** の範囲に収まると判断する。代表文献：Tate の学位論文（1950、未取得）、Connes math/9811068、Burnol math/9901051・math/9902080、Schoof の Arakelov 因子。有限レベルの部分は「有限環の上の Tate の学位論文」（ガウス和を有限体のガンマ関数と見る見方、Kazhdan–Polishchuk）に当たる。

収まらない部分は 3 つ：(Z) で P¹ の射影系を赤道とともに立て、U_∞ の延長を問う設定（文献は見つかっていない）。「解像度 ＝ T の選び方」という呼び方（数学の内容は既知で、名前だけが独自）。Hartley 核を標準の核に選ぶこと（根数の i^a の正規化と符号の置き場所がこれで決まる）。

Connes–Marcolli の GL₂ 系、Connes–Consani の arithmetic site・scaling site は、検索で名前だけ出てきた（arXiv:1609.08727、arXiv:1806.01887）。中身は確かめていないので近いかどうかは判定できない。

### 4. 確かめられなかったこと
- Neukirch の本文（replete divisor）、Tate の学位論文、Davenport の根数の式（いずれも未取得で、私の知識による）。
- Connes 1999 の本文で、半局所の商が稠密か離散かを論じている箇所（取得できたのは冒頭 10 万字だけ）。
- Meyer（Duke 2005）が指標で分解しているか（要旨のみ）。
- 有限 GL₂ の Ind(1) での Weyl 元の絡作用素と Φ_N の延長との関係（Bump・Piatetski-Shapiro の本文は未取得）。
- P¹(Ẑ) の上の局所定数関数の空間を扱った文献。
- cas 核で根数を対角化することを明示した文献（見つかった Hartley 変換の論文 arXiv:2406.19410 は Mehta 型の固有ベクトルの話で、指標と無関係）。
- MathSciNet・zbMATH は使っていない。

**使ったツールの回数**：WebSearch 14 回、WebFetch 13 回、Bash 1 回（数値確認）。

**取得した文献**：本文の一部（Connes math/9811068 の冒頭 10 万字、Kazhdan–Polishchuk math/0003011 の冒頭 10 万字、Schoof *Computing Arakelov class groups* の冒頭 10 万字）。本文（Stein 講義ノート 2006-04-19、dfoiler *intertwining.pdf*、Buzzard *Epsilon constants*）。要旨（Burnol math/9811040・math/9902080、Meyer math/0311468、arXiv:1203.4914、arXiv:2406.19410）。要旨と取得ツールの要約による本文の該当箇所（Burnol math/9901051、Gurevich–Hadani–Sochen arXiv:0808.3281）。検索結果にだけ出たもの：Wikipedia の Arakelov theory、Durov のコンパクト化の解説 arXiv:0908.4059、Wikipedia の Projective line over a ring。所要時間は約 20 分。
