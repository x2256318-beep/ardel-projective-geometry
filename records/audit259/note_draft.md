# アーデル射影幾何 PAG 2.0 — Part 259：互いに素な段の写像の一意性と、帰納系の添字（PAG263.lean）

（2026-11-15。著者の指示「Lean」（07:27）。問いの出所は、基礎文書の骨格（著者側）の第5章と、方向ラウンドの項目 (b) の R1。R1 の査定 `pag2_R1_assessment.md` の主張を Lean にした。）

## §0 結論（Lean の文から）

記号：A_N = `shellAlg N`。Part 258 の条件 (i)(ii) を `Compat` と書く。(i) φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の、φ(E_s) は E_t の線形結合。(iii) フーリエとの両立 φ(𝓕S𝓕⁻¹) = 𝓕φ(S)𝓕⁻¹ を足したものを `CompatF` と書く。

1. **一意な存在の二分法**（`existsUnique_compatF_iff`）：N ∣ M のとき、(i)(ii)(iii) を満たす単位的な代数準同型 A_N → A_M がちょうど 1 つあるのは、gcd(N, M/N) = 1 のとき、かつそのときに限る。互いに素な段では、それは `shellLift`（S ↦ S ⊗ 1）である（`compatF_iff_eq_shellLift`）。
2. **(iii) は外せない**（`not_existsUnique_compat`）：gcd(2, b) = 1、1 < b のとき、(i)(ii) だけを満たす A_2 → A_{2b} は 2 つ以上ある。もう 1 つは χ(x) = (−1)^x による捩れ `twLift`。
3. **帰納系**（`canon_comp`、`canon_self`）：互いに素な段の標準の写像は合成と両立する。
4. **添字は有向でない**（`not_directed_udvd`）：素数 p について、p と p² の両方の上に来る互いに素な段はない。
5. **有向な部分系の例**：素数の有限集合の積（無平方数）の段は、包含の順で帰納系をなし（`DirectedSystem` のインスタンス）、ℂ 加群としての帰納極限 `sqLim` に各段は単射で入る（`sqLim_of_injective`）。

定理 61 個、定義 14 個、インスタンス 3 個。sorry 0、警告 0、公理は標準の範囲。

（以下、照合の後に書く）
