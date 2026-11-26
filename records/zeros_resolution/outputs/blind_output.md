# 盲検の問いテストの出力（零点と解像度、2026-11-26 17:54〜17:58）

依頼文：`../prompt_blind.md`。文脈を渡さない新しいエージェント（general-purpose、ウェブ検索あり）。所要約 4 分 19 秒、ツール使用 14 回。以下は返信の全文。構築側が変えたのは、Z3 の行と Connes の項にあったリンクの URL を省いたことだけ（文献名は残した）。

---

## 照合結果（Z1〜Z6）

| 文 | 区別 | 答えを持つ文献 | 誤り・言い過ぎの場合の正しい形と反例 |
|---|---|---|---|
| **Z1** | 前半は**定義からすぐ出る**。後半は**既存の結果（よく知られたヒューリスティクと、その厳密な形）** | Weil の明示公式の形：Iwaniec–Kowalski『Analytic Number Theory』(2004) 定理 5.12（番号は確信度：中）、Rudnick–Sarnak "Zeros of principal L-functions and random matrix theory", Duke 81 (1996)（節は未確認）。厳密な形：Beurling–Selberg の極値関数。Vaaler "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985)。応用例：Goldston–Gonek, Bull. LMS 39 (2007)、Carneiro–Chandee–Milinovich, Math. Ann. 356 (2013)（S(T) の評価） | 「見分けない」は**言い過ぎ**。g の台が [−L, L]（L = log X）なら、Paley–Wiener により h は指数型 L の整関数になる。そのため、h が変化できる速さは Bernstein の不等式で上から抑えられる。ただし h は L より細かい尺度でも滑らかに変化するので、和は零点の正確な位置に依存し続ける。正確に言えるのは次のこと：区間の指示関数を「型 L の関数」で上と下から挟むと、その誤差は 2π/L 以上になる（Selberg。h の Fourier 台の長さで規格化すると、ちょうど 2π/log X）。2π/log X という定数は規約で変わり、確かなのは 1/log X の桁だけ。高さ T での零点の平均間隔は 2π/log(T/2π) なので、個々の零点を分けるには X ≈ T 程度が要る（Montgomery の α<1 の範囲と同じ構図） |
| **Z2** | 打ち切った明示公式そのものは**既存**。「幅 x/T で均した ψ」は**既存のヒューリスティクで、言い過ぎを含む** | Davenport『Multiplicative Number Theory』第 17 章。Montgomery–Vaughan『Multiplicative Number Theory I』(2007) 第 12 章（定理 12.5 という番号は未確認）。Ingham (1932) 第 IV 章。数値図示：Riesel–Göhl, Math. Comp. 24 (1970) | 正しい形：ψ₀(x) = x − Σ_{\|γ\|≤T} x^ρ/ρ − log 2π − ½log(1 − x⁻²) + O(x log²(xT)/T + …)。言い過ぎは 3 点。(i) 鋭い打ち切りの核は Dirichlet 核型で符号を変えるので、正値の平均ではない（素数冪の跳びでギブス型の振動が出る）。また極の項 x は打ち切られないので、「ψ を核で畳み込んだもの」と厳密には一致しない。厳密な均し方は、Mellin 変換が高さ T で切れる重みを使った平滑化された明示公式で、そのとき主項は x·ŵ(1) の形になる。(ii) T < γ₁ ≈ 14.13 では零点の和が空になる。誤差項は T ≪ log²x で意味を失うので、「幅 x/T」の読みは T が大きい範囲だけのもの。(iii) 零点をすべて外すと残るのは、正確には x − log 2π − ½log(1 − x⁻²)。½log の項は自明零点から来るので、自明零点も外すなら x − log 2π になる。一方 ψ(x) − x = Ω±(x^{1/2} log log log x)（Littlewood 1914）なので、外した零点の寄与は小さくない |
| **Z3** | 前半は**正しいが弱い**（自明な事実）。後半は**定理ではなく、誤解を招く** | Hurwitz の定理（標準）。Gonek–Hughes–Keating "A hybrid Euler–Hadamard product for the Riemann zeta function", Duke Math. J. 136 (2007) no. 3（Project Euclid、arXiv:math/0511182）。K. Conrad "Partial Euler products on the critical line", Canad. J. Math. 57 (2005) 267–297。比較：Montgomery の部分和の零点 (1983, MR 87a:11081) | 正しい形：各因子 (1 − p^{−s})^{−1} は ℂ 全体で零にならない（極は Re s = 0 の上にある）。したがって有限積は Re s > 0 に限らず**ℂ 全体で零点を持たない**。「初めて現れる」については、ζ の零点は部分積の零点の極限ではない。Hurwitz の定理により、零にならない関数の局所一様極限は零を持たない（恒等的に 0 の場合を除く）。だから部分積は、零点を含むどの領域でも ζ に局所一様収束しない。零点はオイラー積の外側、つまり解析接続の側の対象である。定量的な形は GHK の ζ(s) ≈ P_X(s)·Z_X(s) で、素数 ≤ X の部分積 P_X と、s から約 1/log X 以内の零点の積 Z_X に分かれる（P_X の定義は平滑化版）。臨界線上で部分積が収束することは RH より強い条件になる（Conrad）。対比として、部分和 Σ_{n≤N} n^{−s} には零点があり、Re s > 1 にもはみ出す（Montgomery） |
| **Z4** | **一部誤り（言い過ぎ）**。正しい形は既存 | Riemann–von Mangoldt の公式。Titchmarsh『The Theory of the Riemann Zeta-Function』第 2 版 §9.3（確信度：中）、Davenport 第 15 章（確信度：中） | N(T) = θ(T)/π + 1 + S(T)、θ(T) = (T/2)log(T/2π) − T/2 − π/8 + O(1/T)。したがって (T/2π)log(T/2πe) と −1/8 は無限素点の因子 π^{−s/2}Γ(s/2) から来る（π^{−s/2} も無限素点の局所因子の一部）。一方 **+1 は極から来る**（ξ の因子 s(s−1)、Weil の形では h(±i/2) の項）。つまり 7/8 = −1/8（ガンマ因子）+ 1（極）であって、「7/8 は無限素点から」は誤り |
| **Z5** | **既存の結果からの短い帰結**（ほぼ正しい） | IK 定理 5.12（一般の L 関数の明示公式に ε は現れない。番号は確信度：中）。Davenport 第 19 章（ψ(x, χ) の明示公式。定数 b(χ) も、関数等式で書き直すと ε が消える）。Weil 1952 "Sur les « formules explicites » de la théorie des nombres premiers" | 正しい理由：明示公式は対数微分から出るので、定数 ε(χ) は消える。Weil の局所的な定式化でも、局所 ε 因子のうち絶対値（導手）は入るが、位相は入らない。補足として 3 点。(i) 「現れるのは導手とパリティだけ」は、関数等式から入るデータに限った言い方。素数の側には χ(pᵏ) があり、自然な形では χ と χ̄ が対になる。(ii) ε は明示公式の外で効く。自己双対な L 関数で ε = −1 なら中心に零点が強制される（実の原始的なディリクレ指標では ε = 1 なので起きない）。族の 1 準位密度では、ε で SO(even) と SO(odd) が分かれる（Iwaniec–Luo–Sarnak, Publ. IHES 91 (2000)） |
| **Z6** | 種数 g ≥ 1 の曲線については**既存**。**𝔽_q(t) そのもの（種数 0）については誤り** | Weil 1948（曲線の RH）、Weil 1952（大域体の明示公式）。Rosen『Number Theory in Function Fields』GTM 210 (2002) 第 5 章（定理番号は未確認）。Katz–Sarnak『Random Matrices, Frobenius Eigenvalues, and Monodromy』(1999) | 反例：𝔽_q(t)（射影直線）では Z(u) = 1/((1 − u)(1 − qu)) で、**零点がない**（N(T) = 0）。種数 g の曲線では、偏角の周期 2π/log q ごとに 2g 個の零点が並ぶので、N(T) = (g log q/π)·T + O(g)。この線形性は「log の因子がない」の正しい内容で、無限素点（導手が高さとともに増えるガンマ因子）がないことの反映（Z4 と整合）。主項は二つの極（s = 0, 1）から来る：#C(𝔽_{qⁿ}) = qⁿ + 1 − Σαⱼⁿ。周期性があるので、関数体での「台」は次数 n ∈ ℤ の有限集合になり、次数 ≤ N の情報は偏角を約 2π/N の分解能で見る |

## 「解像度」を台や打ち切りの高さとして定義する考え方は文献にあるか

「解像度（resolution）」という語で、こうした操作をひとつの概念として定義した文献は、**今回の検索の範囲では見つからなかった**（存在しないという意味ではない）。ただし、同じ内容は以下の別の名前で広く使われている。

- **Montgomery の対相関**（Proc. Symp. Pure Math. 24, 1973）。F(α) が分かるのは |α| < 1 のときで、Fourier の台を (−1, 1) に限ることは、高さ T で素数 ≤ T^{|α|} しか使わないことに当たる。Rudnick–Sarnak (1996) の n 準位相関、Katz–Sarnak (1999)、Iwaniec–Luo–Sarnak (2000) でも「Fourier の台の制限」として定式化されており、台を延ばすことが細かい尺度を見ることに当たる。
- **Beurling–Selberg 型の極値関数**（Vaaler 1985、Goldston–Gonek 2007、Carneiro–Chandee–Milinovich 2013）。素数の範囲 Δ と、零点を数えるときの誤差 1/Δ の間のトレードオフ。Z1 の厳密な形に当たる。
- **Gonek–Hughes–Keating (2007)**。パラメータ X 一つで、素数 ≤ X と、約 1/log X 以内の零点を明示的に分ける。「台＝素数の範囲」と「零点の分解能」の双対性に最も直接的に当たる。
- **量子カオスの類推**：Berry "Riemann's zeta function: a model for quantum chaos?" (Lecture Notes in Physics 263, 1986)、Berry–Keating, SIAM Rev. 41 (1999)。素数を周期軌道（周期 log p）とみなし、周期 τ までの軌道で 2π/τ の分解能、Heisenberg 時間 log(T/2π) が平均間隔に当たる（節番号は未確認）。
- **Connes の仕事**
  - "Trace formula in noncommutative geometry and the zeros of the Riemann zeta function", Selecta Math. 5 (1999)（arXiv:math/9811068）。有限個の素点の集合 S の上の半局所的な跡公式（定理 4、§VII）がある。カットオフ Λ を使う箇所もあると記憶しているが、今回取得できた抜粋では確認できなかった（未確認）。
  - Connes–Consani "Spectral triples and ζ-cycles"（arXiv:2106.01715）。**台を固定した区間に制限した試験関数**で Weil の二次形式を調べ、長さ L = 2 log S の円の低い固有値が零点に似ること（最初の 31 個の再現）を数値で示している。「台＝測る素数の範囲」を明示的なパラメータにした仕事として、最も近い先行。
  - Connes–Consani "Weil positivity and trace formula, the archimedean place"（arXiv:2006.13771）。無限素点だけが効く場合（カットオフのパラメータ 1）。台の小さい試験関数での Weil 正値性は Yoshida (1992, Adv. Stud. Pure Math. 21) にあると記憶しているが、書誌は未確認。
- **不確定性原理**：Paley–Wiener と Bernstein の不等式による議論は標準的。明示公式と Fourier の符号不確定性原理を結んだものとして Bourgain–Clozel–Kahane (Ann. Inst. Fourier 2010) と Carneiro–Milinovich–Soundararajan (Comment. Math. Helv. 2019) を挙げておくが、明示公式との関係の詳細は未確認。

補足（確信度）：各文の数学的な判定は、標準的な事実と手計算によるもので、確信度は高。定理や節の番号は、上で「未確認」「確信度：中」と書いたものを照合していない。文献の存在は、Connes–Consani の 2 本、GHK、Conrad、Connes 1999、Montgomery (MR 87a:11081) についてはウェブで確かめた。ほかは記憶による。
