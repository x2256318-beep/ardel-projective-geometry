# 盲検の問いテストの出力（2026-11-20 20:45 開始、約 485 秒、ツール 20 回）

- 照合者：文脈を共有しない新しいエージェント（汎用）。使ったのは WebSearch と WebFetch だけ（本人の申告：WebSearch 11 回、WebFetch 8 回）。
- 依頼文：`records/partial_inversion/prompt_blind.md` の全文に、末尾の 1 文（「最後に、全体として『この問いは既存の結果か。どの文献が答えを持っているか。既知の結果の当てはめで済まない部分（残余）があるとすれば何か』を短くまとめてください。」）を足したもの。
- 以下は出力をそのまま転記したもの（文献の URL・番号は照合者の申告で、こちらでは未照合）。

---

# 照合結果（Q1〜Q6）

**前提.** WebSearch（11 回）と WebFetch（8 回）のみを使用。数学的な主張の多くは私の手計算で、コードによる数値確認はしていません（実行禁止のため）。［手計算］＝私の導出、［文献］＝本文または二次文献の引用で確認、［知識］＝本セッションで本文未確認の文献知識。

## Q1（舞台）

**1-1. 部分反転で閉じさせると P¹(ℤ/N) 全体になる。** ［手計算、確信度：高］
|X_N| = N + (N − φ(N)) = 2N − φ(N)、|P¹(ℤ/N)| = ψ(N) = N∏_{p∣N}(1+1/p)。差は「a も b も単数でない単模な組」（CRT で法 p では (1,0)、法 q では (0,1) のような点）で、N が素数冪のときだけ 0（例：N = pq で 2 点足りない）。任意の点の p 成分は [x_p:1] か [1:y_p]（y_p 非単数）のどちらか。後者の型の p を集めて Q とすると w_Q(P) ∈ {[x:1]} ⊂ X_N。よって P¹ = ⋃_Q w_Q(𝔸¹)。構造としては、Q ∥ N は ℤ/N の冪等元（Spec ℤ/N の開かつ閉な部分集合）に対応し、w_Q は GL₂(ℤ/N) ≅ ∏GL₂(ℤ/p^k) の元で、Q 成分が (0 1; 1 0)、残りが単位行列。つまり「積環の上の P¹ と成分ごとの反転のなす群 (ℤ/2)^{ω(N)}」にすぎない。

**1-2. 既知の文脈** ［文献］
- Atkin–Lehner の W_Q（Q ∥ N）は Γ₀(N) を正規化する対合で群 (ℤ/2)^{ω(N)} をなす（[LMFDB: cmf.atkin-lehner](https://www.lmfdb.org/knowledge/show/cmf.atkin-lehner)）。カスプへの作用：W_Q はレベル d = d_Q d_{Q'} のカスプをレベル (Q/d_Q)·d_{Q'} のカスプに送る（F. Brunault, "On the ramification of modular parametrizations at the cusps", [arXiv:1206.2621](https://arxiv.org/pdf/1206.2621), Lemma 2.6）。確信度：高。
- 赤道での作用 u ↦（法 Q で u⁻¹）は、Atkin–Li の W_Q が指標を χ = χ_Qχ_{N/Q} から χ̄_Q χ_{N/Q} に替えることと同じ型（A. O. L. Atkin, W.-C. W. Li, "Twists of newforms and pseudo-eigenvalues of W-operators", Invent. Math. 48 (1978) 221–243。二次文献 "Fourier expansions at cusps", [arXiv:1807.00391](https://arxiv.org/pdf/1807.00391) §5・Thm 5.3 の引用で確認。原論文の本文は未見、著者名も未確認）。確信度：中〜高。
- 注意：P¹(ℤ/N) を Γ₀(N)\SL₂(ℤ)（Manin 記号の (c:d)）と同一視したとき、部分反転 w_Q は Atkin–Lehner の作用では**ない**（W_Q は SL₂(ℤ) に入らず剰余類集合に作用しない。底の行のレベル gcd(c,N) の変化も d_Q ↦ Q/d_Q にならない）。［手計算、確信度：中］ 全体の反転 (c:d) ↦ (d:c) は Manin 記号の σ 関係と ★ 対合 (c:d) ↦ (−c:d) の合成。部分版に名前を付けた文献は見つからなかった（検索語："Manin symbols P^1(Z/NZ) Atkin-Lehner action"、Web 全般・W. Stein の Modular Forms 本の該当ページ）。
- ユニタリ約数 {Q ∥ N} が現れる文脈：E. Cohen, "Arithmetical functions associated with the unitary divisors of an integer", Math. Z. 74 (1960)［知識］、Atkin–Lehner 群、Γ₀(N) のカスプ（上記）、Hall 約数、ℤ/N の冪等元。

## Q2（解の群） ［手計算、確信度：高］

はい。G_p を法 p^{k_p} の原始指標の集合、O_p = G_p/{共役}、n_p = |O_p| とする。(L) の比 g_p は g_p(χ̄_p) = g_p(χ_p)⁻¹ を満たし、実指標の上では 1 なので、g_p = f_p∘c / f_p と書ける（2 元の軌道ごとに選べる）。局所の補正で α は各 c_p で不変になり、S = Loc · Fun(∏O_p)。よって

S/Loc ≅ Fun(∏_p O_p, U(1)) / {∏_p f_p(o_p)}

で、次元 D = ∏n_p − Σn_p + ω − 1 のトーラス。不変量は 2 つの素数 p, q の 2×2 の交差比 α(o,o')α(ō,ō')/(α(o,ō')α(ō,o'))。n_p：奇素数 p、k = 1 で n_p = (p−1)/2。法 3・法 4 で 1、法 8 で 2。2 ∥ N なら P_N は空。例：N = 15 で D = 0（S = Loc）、N = 35 で D = 2。

## Q3（追加条件） ［手計算、確信度：高（G1）・中〜高（G2）］

**(G1) だけでは、パリティの関数までは縮まない。** 条件は S/Loc の中で 2[β] = [c∘ε] と同値。解集合は T[2] ≅ 𝔽₂^{∏O_p}/Σ_p 𝔽₂^{O_p}（𝔽₂ 上の次元 D）の主等質空間で、有限集合。ルート数の型の c(χ) = χ(−1) = ∏χ_p(−1) は Loc に入るので、解は T[2] そのもの。パリティの関数が占めるのは、そのうち次元 2^{ω'} − ω' − 1 以下の部分だけ（ω' は両方のパリティを持つ p の数）。

**(G2) で全レベル・全分解に κ を課すと、S/Loc は 1 点 [∏κ] に潰れる。** κ の χ_a(b)χ_b(a) の部分は素数冪の分解では Loc に入るので、残る類は κ のパリティ項だけで決まる（ルート数なら (−1)^{a_a a_b}）。注意：(G2) は答えの形を外から入れる条件で、CLAUDE.md の円環の第 2 の型で言う「注入」の疑いとして記録すべきだと考える。

## Q4（既知の例） ［手計算、確信度：高。ガウス和の積の公式は文献］

α(χ) = τ(χ)/(i^a√N) は (L) を満たす。ガウス和の積の公式 τ(χ₁χ₂) = χ₁(q₂)χ₂(q₁)τ(χ₁)τ(χ₂)（[Bristol 講義ノート Lemma 13.3](https://people.maths.bris.ac.uk/~madjp/Teaching/lecture_gauss.pdf)）から τ(χ) = ∏_p χ_p(N/p^{k_p})τ(χ_p) で τ(χ)/√N ∈ Loc。i^{a} = i^{m}·(−1)^{⌊m/2⌋}（m = #{p : χ_p 奇}）で、c_p はパリティを保つので (−1)^{⌊m/2⌋} は各 c_p で不変。

S/Loc での類は (−1)^{e₂(a)} = (−1)^{Σ_{p&lt;q} a_p a_q}（𝔽₂ 上の 2 次の基本対称式、まさに「パリティの二次形式」）。自明でないのは、両方のパリティを持つ p が 2 つ以上あるとき（p ≥ 5、または 2^k で k ≥ 3）で、最小例は N = 35。積の公式で書けば W(χ_aχ_b) = χ_a(b)χ_b(a)W(χ_a)W(χ_b)·(−1)^{a_a a_b}。この形をそのまま書いた文献は検索では見つからなかった（検索語："W(χ1χ2)" root number parity）。

**規約によらないか**：はい。有限素点 p の局所定数は ω_p によって決まり、ω_p は χ_p と χ_q(p^{k_p})（q ≠ p）にしかよらないので、局所定数の積は Loc に入る。χ(−1) = ∏χ_p(−1) も Loc に入る。i^{a} と i^{−a} は同じ類を与える（類は ±1 値）。解釈：局所の積に分かれない部分は、無限素点の ε_∞ だけから来る。ε_∞ は大域のパリティ ∏χ_p(−1) を i^{a}（a ∈ {0,1}）で読むので、Σa_p の ℤ/4 での「繰り上がり」が現れる。背景文献［知識、本文未確認］：Davenport, *Multiplicative Number Theory* 9 章（W = τ/(i^a√q)）、Tate の学位論文（1950）、Tate, "Number theoretic background"（Corvallis, 1979）、Deligne, "Les constantes des équations fonctionnelles des fonctions L"（LNM 349, 1973）。

## Q5（関数体） ［形は文献、類の計算は手計算、確信度：中］

Q2 の構造は同じ（純粋に組合せ）。Q4 は違う。パリティに当たる ψ = χ|_{𝔽_q^×} は **∞ の局所定数に入る**。原始指標 χ のルート数は、奇のとき q^{−(deg h−1)/2} G(χ)/τ(χ|_{𝔽_q^×})、偶のとき q^{−(deg h−1)/2} G(χ)/√q（David–Florea–Lalín, "The mean values of cubic L-functions over function fields", [arXiv:1901.00817](https://arxiv.org/pdf/1901.00817), Cor. 2.3。[arXiv:2505.12015](https://arxiv.org/pdf/2505.12015) 式 (2.8) の引用で確認。偶奇の定義は [arXiv:1901.06295](https://arxiv.org/pdf/1901.06295)、Rosen の本の Thm 9.24A）。局所の積に分かれない部分は F(ψ) = ε(ψ)⁻¹（ε(ψ) = τ(ψ)/√q、ε(1) = 1）で、障害は正規化した Jacobi 和 J(ψ₁, ψ₂)/√q と ψ(−1)。違い：
1. q − 1 &gt; 2 で 𝔽_q^× に実でない指標があると、c_P が ψ_P を ψ̄_P に替えるので「パリティの関数」が c_P で不変でない。
2. その結果、**ルート数は (L) を満たさないことがある**。例：q = 5、ψ_P = 四次指標 λ で、他の成分の積 ψ' = 1 のとき比は ε(λ)²/λ(−1) = −J(λ,λ)/√5 ≠ 1、ψ' = λ のとき比は 1（数値未確認の手計算）。
3. q = 3：τ(sgn) = i√3 で ℚ とまったく同じ形 (−1)^{Σa_Pa_Q}。q = 2：すべて偶で類は自明。q = 4：三次指標のガウス和が 2 = √4 なので類は自明と見込む。

## Q6（文献）

この型の問いの直接の文献は**見つからなかった**。最も近い先行：Atkin–Li（1978。部分的な W_Q、ネベンティプスの部分共役、合成の法則（χ_{Q'}(Q) の因子）、擬固有値）、確信度：中。Hilbert モジュラー形式版の Shemanske–Walling, "Twists of Hilbert Modular Forms"（[PDF](https://people.maths.bris.ac.uk/~malhw/twists.pdf)、Prop 2.7 が合成の法則、λ_Q(f)λ_Q(g) = ψ_Q(−1)。後者は (G1) の c に当たる式）。Tate・Deligne の局所定数（「局所の積と、局所に分かれない部分」の概念的な答え）。周辺：Hiary–Saraeb, "Functional Equations Characterize Dirichlet Characters"（[arXiv:2607.00332](https://arxiv.org/abs/2607.00332)、関数等式の逆定理）。関数の群の分類そのもの（Fun(X×Y) を積で割る）は変数分離（Hoeffding/ANOVA 型の分解）の初等的な事実。検索語："partial conjugation" root number factorization obstruction parity cocycle、pseudo-eigenvalue λ_{QQ'} product formula。検索先は Web 全般。MathSciNet と zbMATH は使っていない。

## まとめ

Q1〜Q3 は積環の上の P¹ と変数分離の初等的な帰結で、既知か少なくとも自明な部類（確信度：高）。Q4 の答え（τ/(i^a√N) の類はパリティの二次形式 e₂ で、規約によらない）は、ガウス和の積の公式と Davenport のルート数からの短い帰結。概念的には Tate・Deligne の局所定数が答えを持っていて、無限素点だけが局所に分かれない。この形をそのまま書いた文献は見つからなかった（確信度：中）が、新規性の根拠にはならない。残余の候補は 2 つ：(1) Q5 の対照群の結果 — 𝔽_q(t) では、q に応じてルート数が (L) を満たさない（q = 5 の手計算）か類が自明になり（q = 2、4）、ℚ の i^a の型は q = 3 でだけ再現する。数値での確認が要る。(2) (G2) は答えを注入しているので、(G2) を使う主張は「導いた」ではなく「入れて読み替えた」と書くべき。
