# アデール射影幾何 2.0 — Part 246：E_s を 1 つ足した代数 B_s = ⟨D_u, E_N, E_s⟩（|S′| ≤ 2 なら A_N、2 点の証拠で E_1 ∉ B_s）

2026-11-06。引き継ぎメモの次の候補「E_s を 1 つ足した代数 ⟨D_u, E_N, E_s⟩」を扱いました。まず数値で s ごとの次元を求め、見つかった形の一部を Lean で証明しました。

- **数値で見つかった形（Lean の証明ではない）。** s ∈ S′ のとき、**B_s = A_N ⇔ |S′| ≤ 2 ∨（N が平方因子なし ∧ s ∈ {1, 2}）** です。
  - N ≤ 60 の s ∈ S′ のすべて（171 組。s ∉ S′ の 90 組では dim B_s = dim ⟨D_u, E_N⟩）と、平方因子なしの N = 66, 70, 78, 102, 105, 110 で確かめました。
- **Lean で示したこと。**
  - **基本。** ⟨D_u, E_N⟩ ≤ B_s ≤ A_N、B_s = ⟨D_u, E_N⟩ ⊔ ⟨D_u, E_s⟩ です（`addEAlg_le`、`addEAlg_eq_sup`）。
  - **何も増えない場合。** s ∣ N のとき、B_s = ⟨D_u, E_N⟩ ⇔ s ∉ S′ ∨ (s = 1 ∧ N ∈ {1, 4} ∪ 素数) です（`addEAlg_eq_oneEAlg_iff_all`）。
  - **十分条件。** |S′| ≤ 2 で s ∈ S′ なら B_s = A_N です（`addEAlg_eq_shellAlg_of_card_le_two`）。Σ_{t ∣ N} E_t = 1 から、残りの E_t が出ます。
  - **判定法。** U_s^⊥ = {f : P f = 0、どの u でも E_s(1_{D_u}·f) = 0} の上では、B_s の元は殻ごとのスカラーとして働きます（`exists_apply_of_mem_addEAlg`）。
  - **否定の主定理。** 素数 r ∣ s ∣ N（r ≠ 2 か 4 ∣ N）と、r と異なる素数 q ∣ N があれば、**E_1 ∉ B_s**、とくに B_s ≠ A_N です（`convL_geps_one_not_mem_addEAlg`、`addEAlg_ne_shellAlg`）。
    - 証拠は 2 点の関数 f = δ_1 − δ_{1+m}（m = j·N/r、j ∈ {1, 2}）です。
  - **平方因子なしの系。** N が平方因子なしなら、s ∈ S′ で s ∉ {1, 2} のすべてで B_s ≠ A_N です（`addEAlg_ne_shellAlg_of_squarefree`）。
    - これで平方因子なしの N では「B_s = A_N ⇒ s ∈ {1, 2}」が Lean で示されました。逆向きは数値だけです。
  - **フーリエ双対。** ⟨E_u, D_N, D_s⟩ = 𝓕B_s𝓕⁻¹ についても、次元が等しいこと、A_N との一致が同値なこと、D_1 ∉ ⟨E_u, D_N, D_s⟩ を示しました。
- **限界（正直な注記）。**
  - 十分性（平方因子なしで s ∈ {1, 2} なら B_s = A_N）は、|S′| ≤ 2 の場合を除いて Lean にしていません。
  - 平方因子ありの N の s = 1、素冪、2 ∥ N（平方因子あり）の s = 2 での B_s ≠ A_N は数値だけです（N ≤ 60 で 28 組）。2 点の証拠はこれらには使えません（理由は §0 の 7）。
  - 観察「|S′| ≥ 3 なら B_s = A_N ⇔ U_s^⊥ = 0」は数値だけです。
- **やり直し。**
  - 数値照合の 1 回目は、観察 (2) を |S′| ≥ 3 に限るのを忘れて、8 件が不合格になりました（§2）。
  - Lean を書く前にメモの注意を読み直したのに、非推奨の `if_pos`・`if_neg` と `push_neg` をまた使いました（警告 8 件、§3）。
  - 試しのファイルは T1 が 2 回目、T2 が 3 回目で通りました。PAG250 は 1 回目のコンパイルで通りました。
- **環境。** Mathlib の追加ビルドはありません。Part 246 の開始時（16:55）にコンテナが再起動していて、import の温めは 179 秒でした。

成果物は次のとおりです。
- `PAG250.lean`：37 項目。sorry 0・警告 0 です。
  - 定義 3 個（`addEAlg`・`twoPt`・`dualAddEAlg`）は項目に数えません。
  - 出力は `PAG250.out`（#print axioms 40 行）。
- 照合用の `step269.py`：ログは `step269.log` です。

xlsx の集計は 3188 項目になりました（手順 266）。

## 0. 結論

**記号**（Part 240〜245 と同じ）
- A_N = `shellAlg N`、B1 = ⟨D_u, E_N⟩ = `oneEAlg N N`、B_s = ⟨D_u, E_N, E_s⟩ = `addEAlg N s`、⟨E_u, D_N, D_s⟩ = `dualAddEAlg N s`。
- S′ = {t ∣ N : φ(N/t) ≠ 1} = `devSet N`、|S′| = d − 1 − [2 ∣ N]（Part 241）。P = 殻の平均（`shellAvg N`）。
- F(N) = dim A_N（Part 226）、G(N) = dim B1 = d² + d − 1 − [2 ∣ N]（Part 241）。
- U_s^⊥ = {f : P f = 0、すべての u で E_s(1_{D_u}·f) = 0}。δ_a = `Pi.single a 1`、δ_1 − δ_b = `twoPt N b`。

| 定理 | 主張 |
|---|---|
| `convL_geps_mem_addEAlg`, `oneEAlg_le_addEAlg`, `oneEAlg_le_addEAlg'`, `addEAlg_le`, `addEAlg_self`, **`addEAlg_eq_sup`** | E_s ∈ B_s、⟨D_u, E_N⟩ ≤ B_s、⟨D_u, E_s⟩ ≤ B_s、B_s ≤ A_N、B_N = ⟨D_u, E_N⟩、B_s = ⟨D_u, E_N⟩ ⊔ ⟨D_u, E_s⟩ |
| `dind_of_not_dvd`, `convL_geps_of_not_dvd`, `convL_geps_mem_oneEAlg_of_not_mem` | s ∤ N なら 1_{D_s} = 0・E_s = 0。s ∉ S′ なら E_s ∈ ⟨D_u, E_N⟩ |
| `addEAlg_eq_oneEAlg_iff`, `addEAlg_eq_oneEAlg`, **`addEAlg_eq_oneEAlg_iff_all`** | B_s = ⟨D_u, E_N⟩ ⇔ E_s ∈ ⟨D_u, E_N⟩ ⇔（s ∣ N で）s ∉ S′ ∨ (s = 1 ∧ N ∈ {1, 4} ∪ 素数) |
| `sum_convL_geps`, `addEAlg_eq_shellAlg_iff`, `convL_geps_eq_one_sub` | Σ_{t ∣ N} E_t = 1。B_s = A_N ⇔ すべての t ∣ N で E_t ∈ B_s。E_t = 1 − Σ_{u ≠ t} E_u |
| **`addEAlg_eq_shellAlg_of_card_le_two`**, `card_devSet_le_two_iff` | \|S′\| ≤ 2、s ∈ S′ なら B_s = A_N。\|S′\| ≤ 2 ⇔ d(N) ≤ 3 + [2 ∣ N] |
| `uperp_dind_mul`, `convL_geps_eq_zero_of_uperp`, **`exists_apply_of_mem_addEAlg`**, `exists_apply_eq_smul_of_mem_addEAlg` | U_s^⊥ は 1_{D_t}· で閉じ、E_s で 0 に送られる。判定法：X ∈ B_s は U_s^⊥ の上で Σ_t b_t·1_{D_t}。1 つの殻に載る f では X f = c·f |
| `shellAvg_twoPt`, `dind_one_mul_twoPt`, `conv_single`, **`geps_add_of_dvd`**, `convL_geps_twoPt`, `dft_single`, `dft_twoPt_ne_zero` | b が単数なら P(δ_1 − δ_b) = 0 で単数の殻に載る。(g ⋆ δ_a)(x) = g(x − a)。(N/s) ∣ m なら ε_s(w + m) = ε_s(w)、E_s(δ_1 − δ_{1+m}) = 0。𝓕δ_a(k) = e(−ak)。(b − 1)k ≠ 0 なら 𝓕(δ_1 − δ_b)(k) ≠ 0 |
| `convL_geps_one_not_mem_addEAlg_of_witness`, `exists_witness_coeff`, **`convL_geps_one_not_mem_addEAlg`**, `addEAlg_ne_shellAlg` | 証拠からの結論。j ∈ {1, 2} の選び方。主定理 E_1 ∉ B_s と B_s ≠ A_N |
| **`addEAlg_ne_shellAlg_of_squarefree`** | N が平方因子なし、s ∈ S′、s ∉ {1, 2} なら B_s ≠ A_N |
| `map_fourierConj_addEAlg`, `finrank_dualAddEAlg`, `dualAddEAlg_eq_shellAlg_iff`, `mulLeft_dind_one_not_mem_dualAddEAlg` | 𝓕B_s𝓕⁻¹ = ⟨E_u, D_N, D_s⟩、次元が等しい、A_N との一致が同値、D_1 ∉ ⟨E_u, D_N, D_s⟩ |

**証明の筋**
1. **基本。** 生成元の集合の包含から、⟨D_u, E_N⟩ ≤ B_s ≤ A_N です。B_s の生成元を 1 つずつ確かめて、B_s = ⟨D_u, E_N⟩ ⊔ ⟨D_u, E_s⟩ です。
2. **何も増えない場合。** B_s = ⟨D_u, E_N⟩ ⇔ E_s ∈ ⟨D_u, E_N⟩ です。右辺は Part 243 で決めました（s ≠ 1 では φ(N/s) = 1、s = 1 では N ∈ {1, 4} ∪ 素数）。φ(N/s) = 1 は s ∉ S′ と同じです。s = 1 で φ(N) = 1 なら N ∈ {1, 2} なので、まとめて上の形になります。
3. **|S′| ≤ 2 の十分性。** t ∣ N をとります。
   - t ∉ S′ なら E_t ∈ ⟨D_u, E_N⟩ です。t = s なら生成元です。
   - 残りは t ∈ S′、t ≠ s で、E_t = 1 − Σ_{u ∣ N, u ≠ t} E_u と書きます。右辺の u は S′ の外か u = s です（S′ に s、t 以外の元 u があると |S′| ≥ 3）。
4. **判定法。** 生成元についての帰納法（`Algebra.adjoin_induction`）です。
   - D_u・E_N と定数は ⟨D_u, E_N⟩ に入るので、Part 243 の形（P f = 0 の f に Σ_t b_t·1_{D_t}·f）です。
   - E_s は U_s^⊥ を 0 に送ります（f = Σ_u 1_{D_u}·f）。和では係数を足し、積では係数を掛けます。
   - 積で使うのは、f ∈ U_s^⊥ なら 1_{D_t}·f ∈ U_s^⊥ であることです（P と D_t は可換、1_{D_u}·1_{D_t} = [u = t]·1_{D_u}）。
5. **2 点の証拠。** m = j·N/r、b = 1 + m、f = δ_1 − δ_b とおきます。
   - **(a) P f = 0。** j の選び方（6）から b は単数なので、1 と b は同じ殻（単数の殻 D_1）にあります。f は D_1 に載っています。
   - **(b) E_s f = 0。** N·ε_s(u) = c_{N/s}(u)（Part 240）は u mod N/s だけで決まります（Part 241）。r ∣ s から N/s ∣ N/r ∣ m なので、ε_s は m の平行移動で不変です。(E_s f)(x) = ε_s(x − 1) − ε_s(x − 1 − m) = 0 になります。
   - **(c)** f ∈ U_s^⊥ で、f は 1 つの殻に載るので、E_1 ∈ B_s なら判定法から E_1 f = c·f です。
   - **(d) フーリエ変換。** 𝓕(E_1 f) = 1_{D_1}·𝓕f で、𝓕f(k) = e(−k) − e(−bk) は mk ≢ 0（mod N）なら 0 でありません。
     - k = q：1_{D_1}(q) = 0（gcd(N, q) = q ≠ 1）なので c·𝓕f(q) = 0 です。mq ≢ 0（N ∣ jq·N/r ⇔ r ∣ jq で、r ∤ j、r ≠ q）なので c = 0 です。
     - k = 1：1_{D_1}(1) = 1 なので 𝓕f(1) = c·𝓕f(1) = 0 です。ところが m ≢ 0（r ∤ j）なので矛盾します。
6. **j の選び方。**
   - r ∤ 1 + N/r なら j = 1 です。r 以外の素因数 p ∣ N は N/r を割るので、1 + m を割りません。
   - r ∣ 1 + N/r なら N/r ≡ −1（mod r）で、j = 2 とすると 1 + 2N/r ≡ −1（mod r）です。r ∤ 2 には r ≠ 2 が要ります。
   - r = 2 で 4 ∣ N なら N/2 は偶数で、2 ∤ 1 + N/2 なので j = 1 の場合です。仮定「r ≠ 2 か 4 ∣ N」はここで使いました。
7. **2 点の証拠が使えない場合**（数値では B_s ≠ A_N）。
   - s = 1：N/s = N なので、(b) の条件は m ≡ 0（mod N）になり、f = 0 です。
   - 2 ∥ N で s = 2（N は平方因子あり）：r = 2 しかありません。N/2 は奇数なので、1 + j·N/2 が単数になる j は偶数で、そのとき m ≡ 0 です。
   - 素冪 N = p^k：r と異なる q がありません（(d) の k = q が使えない）。
   - これらでも U_s^⊥ ≠ 0 です（数値。例：N = 12、s = 1 で dim U_s^⊥ = 1）。別の形の証拠が要ります。
8. **平方因子なしの系。** s は平方因子なしで {1, 2} の外なので、奇素因数 r をもちます。N/r ≠ 1 です（N = r なら s = N で、φ(1) = 1 から s ∉ S′）。q = minFac(N/r) は r と異なります（r² ∤ N）。

**例**（step269 の数値）

| N | F | G | \|S′\| | dim B_s（s ∈ S′） |
|---|---|---|---|---|
| 6 | 20 | 18 | 2 | s = 1, 2 → 20 |
| 12 | 50 | 40 | 4 | s = 1 → 46、2 → 47、3 → 43、4 → 47 |
| 15 | 25 | 19 | 3 | s = 1 → 25、3, 5 → 22 |
| 16 | 31 | 28 | 3 | s = 1, 2 → 30、4 → 29 |
| 18 | 48 | 40 | 4 | s = 1, 2 → 46、3, 6 → 44 |
| 27 | 22 | 19 | 3 | s = 1, 3 → 21、9 → 20 |
| 30 | 100 | 70 | 6 | s = 1, 2 → 100、3, 5, 6, 10 → 84 |
| 36 | 120 | 88 | 7 | s = 1 → 99、2, 4 → 104、3 → 101、6, 12 → 97、9 → 96 |
| 60 | 250 | 154 | 10 | s = 1 → 208、2, 4 → 229、3, 5 → 187、6, 10, 12, 20 → 188、15 → 169 |

- 平方因子なしの N = 66, 70, 78, 102, 110（F = 100）では、s = 1, 2 で 100、最小の奇素因数の s で 84 です。N = 105（F = 125）では、s = 1 で 125、s = 3 で 104 です。
- 平方因子ありで |S′| ≥ 3 の N（12、16、18、27、36、60 など）では、どの s でも A_N になりません。

**読み取れること**
- B1 は殻の平均が 0 の関数に、殻ごとのスカラーとして働くだけでした（Part 243）。E_s を足すと殻をまたぐ作用が加わります。それでも U_s^⊥ の上では、殻ごとのスカラーのままです（判定法）。
- s に奇素因数 r があると、ε_s が N/r の倍数の平行移動で不変になり、これが 2 点の証拠を生みます。E_1 にはこの不変性がありません（周期は N）。2 ∥ N での E_2 は N/2 の平行移動で不変ですが、1 + N/2 が偶数で単数にならないので、証拠になりません。平方因子なしの N では、E_1（偶数なら E_2 でも）を足すだけで A_N 全体が出るというのが数値の結論です。
- 平方因子ありの N では、s = 1 でも足りません。2 点とは別の形の障害があるはずです（未解明）。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| ⟨D_u, E_N⟩ ≤ B_s ≤ A_N、B_s = ⟨D_u, E_N⟩ ⊔ ⟨D_u, E_s⟩ | **正しい（`oneEAlg_le_addEAlg`、`addEAlg_le`、`addEAlg_eq_sup`）** |
| s ∣ N で B_s = ⟨D_u, E_N⟩ ⇔ s ∉ S′ ∨ (s = 1 ∧ N ∈ {1, 4} ∪ 素数) | **正しい（`addEAlg_eq_oneEAlg_iff_all`）**。数値でも s ∉ S′ で dim B_s = G（N ≤ 60） |
| \|S′\| ≤ 2、s ∈ S′ なら B_s = A_N | **正しい（`addEAlg_eq_shellAlg_of_card_le_two`）**。数値でも（N ≤ 60） |
| \|S′\| ≤ 2 ⇔ d(N) ≤ 3 + [2 ∣ N] | **正しい（`card_devSet_le_two_iff`）** |
| \|S′\| ≤ 2 ⇔ N ∈ {1, 8} ∪ {p, p²} ∪ {2q : q は奇素数} | **数値だけ**（N ≤ 10^5、100000/100000） |
| 判定法：B_s の元は U_s^⊥ の上で殻ごとのスカラー | **正しい（`exists_apply_of_mem_addEAlg`）**。数値でも乱数の元で 195/195（N ≤ 40） |
| 素数 r ∣ s ∣ N（r ≠ 2 か 4 ∣ N）、q ≠ r の素数 q ∣ N なら E_1 ∉ B_s、B_s ≠ A_N | **正しい（`convL_geps_one_not_mem_addEAlg`、`addEAlg_ne_shellAlg`）**。数値でも証拠の組 1493/1493（N ≤ 200） |
| 平方因子なしの N で、s ∈ S′ \ {1, 2} なら B_s ≠ A_N | **正しい（`addEAlg_ne_shellAlg_of_squarefree`）** |
| フーリエ双対（次元、A_N との一致、D_1 ∉） | **正しい（`finrank_dualAddEAlg`、`dualAddEAlg_eq_shellAlg_iff`、`mulLeft_dind_one_not_mem_dualAddEAlg`）**。数値でも次元 48/48（N ≤ 24） |
| 平方因子なしで s ∈ {1, 2} なら B_s = A_N（十分性） | **数値だけ**（N ≤ 60 と N = 66, 70, 78, 102, 105, 110）。\|S′\| ≤ 2 の N だけ Lean |
| s ∈ S′ で B_s = A_N ⇔ \|S′\| ≤ 2 ∨（平方因子なし ∧ s ∈ {1, 2}） | **数値だけ**（N ≤ 60 の 171 組。(1) の 261/261 に含まれる）。⇐ の \|S′\| ≤ 2 の部分と、平方因子なしの ⇒ だけ Lean |
| 平方因子ありの s = 1・素冪・2 ∥ N の s = 2 で B_s ≠ A_N | **数値だけ**（N ≤ 60 で 28 組） |
| \|S′\| ≥ 3 なら B_s = A_N ⇔ U_s^⊥ = 0 | **数値だけ**（N ≤ 60、128/128）。\|S′\| ≤ 2 では成り立たない（N = 8, 9, 25, 49 で U_s^⊥ ≠ 0 なのに B_s = A_N） |
| 恒等式 E_p = p(1 − E_1)G_p(1 − E_1) − p²·G_p·T_p·G_p ⇔ p ∥ N（G_p = Σ_{p ∣ t} D_t、T_p = Σ_{p ∣ t, t ≠ p} E_t） | **数値だけ（探索）**（12 個の N の素因数すべて、29/29）。フーリエ側での手計算の筋は §4 の 1 |

## 2. 数値照合（step269）

| 項目 | 内容 | 結果 |
|---|---|---|
| (1) | 生成元から（N ≤ 60、s ∣ N すべて）：dim B_s ≤ F、s ∉ S′ で dim B_s = G、s ∈ S′ で dim B_s = F ⇔ \|S′\| ≤ 2 ∨（平方因子なし ∧ s ∈ {1, 2}） | 261/261 |
| (2) | 観察：\|S′\| ≥ 3 で dim B_s = F ⇔ U_s^⊥ = 0（128 組）と、\|S′\| ≤ 2 で U_s^⊥ ≠ 0 となる N が 8 と奇素数の平方（9, 25, 49）であること | 129/129 |
| (3) | 判定法（N ≤ 40、U_s^⊥ ≠ 0 の 65 組に B_s の乱数の元 3 つずつ）：U_s^⊥ の基底に共通の b で X f = Σ_t b_t·1_{D_t}·f。残差の最大 1.8e-14。対照の E_1：残差が大きい 48 組はどれも E_1 ∉ B_s | 196/196 |
| (4) | 2 点の証拠（N ≤ 200）：仮定を満たす組 (N, s, r, q) すべてで gcd(N, b) = 1、r ∤ j、(N/s) ∣ m、P f = 0、E_s f = 0、𝓕f(1) ≠ 0、𝓕f(q) ≠ 0、E_1 f ∉ ℂf。(1) との整合（証拠のある (N, s ∈ S′) では dim B_s < F） | 1493/1493、88/88 |
| (5) | \|S′\| ≤ 2 ⇔ N ∈ {1, 8} ∪ {p, p²} ∪ {2q}（N ≤ 10^5）。N ≤ 2000 では \|S′\| を定義から数えて d − 1 − [2 ∣ N] と照合 | 100000/100000 |
| (6) | 平方因子なしの N = 66, 70, 78, 102, 105, 110：s = 1（と偶数なら 2）で dim B_s = F、最小の奇素因数の s で dim B_s < F | 17/17 |
| (7) | フーリエ双対（N ≤ 24、s ∈ S′）：dim ⟨E_u, D_N, D_s⟩ = dim B_s | 48/48 |
| (8) | 探索（次の Part 用）：恒等式 (I) が成り立つ ⇔ p ∥ N（N = 6, 10, 15, 21, 30, 42, 66, 70, 105, 12, 18, 45）。語の長さ（下） | 29/29 |

- 証拠のない dim B_s < F（N ≤ 60）は、平方因子ありの s = 1 が 15 組（例 (12, 1)、(18, 1)、(20, 1)、(24, 1)、(28, 1)、(36, 1)）、N が素冪が 10 組（例 (16, 1)、(16, 2)、(16, 4)、(27, 1)、(27, 3)、(27, 9)）、2 ∥ N の s = 2 が 3 組（(18, 2)、(50, 2)、(54, 2)）です。
- (8) の語の長さ：B_s の生成元（D_t・E_N・E_s）の長さ k 以下の語が張る空間に、E_t が初めて入る k です。
  - N = 15, 21, 35（s = 1）では、素数 t の E_t が k = 3 で入ります。
  - N = 30, 42（s = 1）では、素数 t の E_t が k = 3、t = 6, 10, 14 の E_t が k = 5 で入ります。N = 30、s = 2 では E_1・E_6・E_10 が 3、E_3・E_5 が 5 です。
- **実行は 3 回です。**
  - 1 回目（約 182 秒）は (2) が 163/171 で不合格でした。観察「dim B_s = F ⇔ U_s^⊥ = 0」を |S′| ≥ 3 に限るのを忘れていました。|S′| ≤ 2 の N = 8, 9, 25, 49 では、B_s = A_N なのに U_s^⊥ ≠ 0 です。
    - 探索の段階（下）では |S′| ≥ 3 に限って書いていたのに、照合のスクリプトに写すときに落としました。1 回目の出力は `step269.run.out` に残しました。
  - 2 回目は (2) を直し、|S′| ≤ 2 の場合は別に記録する形にして、すべて合格しました（保存済みの結果を使い 0.7 秒）。
  - 3 回目は探索 (8) を足しました（1.7 秒）。`step269.log` は 3 回目の出力です。
  - 項目ごとの結果は `step269_cache.json` に保存しました。
- **照合の前の探索**（成果物ではない。置き場所は `/home/claude/explore`）。
  - `ex269.py`・`ex269b.py`：N ≤ 60 の次元と U_s^⊥ の次元。ここで形を見つけました。
  - `ex269c.py`：N = 66, 70, 78, 105。N = 70 では s = 3 を指定していましたが、3 は 70 の約数でなく E_3 = 0 なので、結果 70 は dim ⟨D_u, E_N⟩ でした（指定の誤り）。step269 の (6) では最小の奇素因数を使うように直しました。
  - `ex269d.py`〜`ex269h.py`：語の長さと恒等式 (I) の探索。(8) にまとめました。
- **限界。** 生成元からの計算は N ≤ 60（と (6) の 6 個）です。(4) は作用素の行列で確かめました。(5) は約数の個数の式の照合です。

## 3. Lean（`PAG250.lean`、namespace `PAG.Part250`、PAG249 を import）

| 区分 | 項目 |
|---|---|
| 1. B_s の定義と包含 | def `addEAlg`, `convL_geps_mem_addEAlg`, `oneEAlg_le_addEAlg`, `oneEAlg_le_addEAlg'`, `addEAlg_le`, `addEAlg_self`, `addEAlg_eq_sup` |
| 2. 簡単な場合 | `dind_of_not_dvd`, `convL_geps_of_not_dvd`, `convL_geps_mem_oneEAlg_of_not_mem`, `addEAlg_eq_oneEAlg_iff`, `addEAlg_eq_oneEAlg`, `addEAlg_eq_oneEAlg_iff_all`, `sum_convL_geps`, `addEAlg_eq_shellAlg_iff`, `convL_geps_eq_one_sub`, `addEAlg_eq_shellAlg_of_card_le_two`, `card_devSet_le_two_iff` |
| 3. 判定法 | `uperp_dind_mul`, `convL_geps_eq_zero_of_uperp`, `exists_apply_of_mem_addEAlg`, `exists_apply_eq_smul_of_mem_addEAlg` |
| 4. 2 点の証拠 | def `twoPt`, `shellAvg_twoPt`, `dind_one_mul_twoPt`, `conv_single`, `geps_add_of_dvd`, `convL_geps_twoPt`, `dft_single`, `dft_twoPt_ne_zero`, `convL_geps_one_not_mem_addEAlg_of_witness`, `exists_witness_coeff`, `convL_geps_one_not_mem_addEAlg`, `addEAlg_ne_shellAlg`, `addEAlg_ne_shellAlg_of_squarefree` |
| 5. フーリエ双対 | def `dualAddEAlg`, `map_fourierConj_addEAlg`, `finrank_dualAddEAlg`, `dualAddEAlg_eq_shellAlg_iff`, `mulLeft_dind_one_not_mem_dualAddEAlg` |

**使った PAG の結果**
- Part 201 の `dind`・`geps`・`dind_mul`・`sum_dind`・`sum_geps_conv`（PAG205）、Part 203 の `dind_radial`・`dind_self`・`gcd_natCast_self`（PAG207）
- Part 214 の `shellAlg`（PAG218）、Part 228 の `shellAlg_eq_adjoin`・`convL_geps_mem`・`mulLeft_dind_mem`（PAG232）
- Part 239 の `dft_conv_geps`（PAG243）、Part 240 の `shellAvg`・`shellAvg_apply`・`natCast_mul_geps_eq_ramSum`・`oneEAlg`（PAG244）
- Part 241 の `ramSum_mod`・`devSet`・`card_devSet`（PAG245）、Part 242 の `fourierConj`・`fourierConj_convL_geps`・`fourierConj_mulLeft_dind`・`map_fourierConj_shellAlg`・`convL_geps_mem_oneEAlg`（PAG246）
- Part 243 の `exists_apply_of_mem_oneEAlg`・`sum_mul_single`・`convL_geps_mem_oneEAlg_iff_all`（PAG247）、Part 244 の `shellAvg_dind_mul`（PAG248）

**Mathlib・Lean から使った主なもの**
- 部分代数：`Algebra.adjoin_induction`・`Algebra.adjoin_le`・`Algebra.adjoin_mono`・`Algebra.subset_adjoin`・`Algebra.mem_sup_left`・`AlgHom.map_adjoin`・`Subalgebra.mem_map`・`Subalgebra.map_injective`・`AlgEquiv.subalgebraMap`
- フーリエ変換と ZMod：`ZMod.dft_apply`・`ZMod.injective_stdAddChar`・`ZMod.isUnit_iff_coprime`・`ZMod.natCast_eq_zero_iff`・`ZMod.natCast_zmod_val`・`IsUnit.unit_spec`
- 自然数：`Nat.coprime_of_dvd`・`Nat.dvd_sub`・`Nat.dvd_add_right`・`Nat.prime_dvd_prime_iff_eq`・`Nat.dvd_of_mul_dvd_mul_right`・`Nat.add_mul_mod_self_left`・`Nat.eq_prime_pow_of_unique_prime_dvd`・`Nat.squarefree_iff_prime_squarefree`・`Squarefree.squarefree_of_dvd`・`Nat.minFac_prime`・`Finset.card_eq_three`

**コンパイル**
- `PAG250` は 1 回目のコンパイル（約 5 秒）でエラー・警告なしで通りました。公理は 40 行すべて [propext, Classical.choice, Quot.sound] です。
- 内容は試しのファイル T2 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble250.py`）。
- **試しのファイル（置き場所は `/home/claude/leanwork/scratch/t246`）。**
  - W0：import の温めと API の確認（179 秒、コンテナ再起動の直後）。存在しない名前 `PAG.Part232.convL_geps_mul` を書いていました（使う予定はなくなった）。
  - W1〜W3：API の確認（各 6〜7 秒）。名前の誤りが 5 件ありました。
    - `Nat.exists_mul_emod_eq_one_of_coprime` はありません（逆元を使わずに j ∈ {1, 2} で済ませる形にしました）。
    - `ramSum_mod` は PAG.Part241 ではなく PAG.Part245（Part 241 の PAG245）にあります。
    - `Finset.sum_eq_sum_diff_singleton_add` はありません（`Finset.sum_erase_eq_sub` を使いました）。
    - `ZMod.natCast_self_eq_zero` ではなく `ZMod.natCast_self`、`Nat.dvd_sub'` ではなく `Nat.dvd_sub` です。
  - T1（§1〜3、21 項目と定義 1 個）：1 回目にエラー 1 件と警告 8 件で、2 回目で通りました（3 秒）。
    - エラー：A_N の生成元 `Set.range (fun s => E_s)` から `rintro` すると、ゴールが `(fun s => E_s) t ∈ …` の形のままで `rw` が当たりませんでした。`show E_t ∈ B_s` で書き直しました。
    - 警告：非推奨の `if_pos`・`if_neg`（6 件）と `push_neg`（2 件）です。**メモの「よく出たエラーと対処」に書いてあり、Lean を書く前に読み直したのに、また使いました。** `ite_eq_left`・`ite_eq_right` と `push Not` に直しました。
  - T2（§4〜5 を足した 37 項目と定義 3 個）：1 回目にエラー 2 件、2 回目にエラー 1 件で、3 回目で通りました（5 秒）。
    - `show (if Nat.gcd N (q : ZMod N).val = 1 then 1 else 0) = 0` と書くと、if の Decidable が `Nat.Coprime` のもの（`N.instDecidableCoprime`）になり、`rw [gcd_natCast_self]` が motive エラーになりました。条件の否定を別の `have` で示し、`exact ite_eq_right hg` で閉じました。
    - `Subalgebra.map_injective (fourierConj N).injective` では、AlgEquiv から AlgHom への型の変換を推論できませんでした。`(f := (fourierConj N : … →ₐ[ℂ] …))` を明示しました。
    - `rw [← map_fourierConj_shellAlg]` が ↔ の両辺の A_N を書き換えて、`eq_iff` と形が合わなくなりました。`conv_lhs => rw […]` で左辺だけにしました。
- **前回までの注意を当てはめた箇所。**
  - 部分代数の帰納法は、ゴールの型の def（`addEAlg`）を `unfold` してから `induction hX using Algebra.adjoin_induction with` にしました。
  - 同じ条件の if が 2 か所に出る書き換え（3d）では、2 つ目の if は `dind_mul` で現れた後なので、`ite_eq_right ht` を 2 回書きました（1 回目で両方が書き換わることはありませんでした）。
- **環境。** Mathlib の追加ビルドはありません。Part 245 の納品の後、Part 246 の開始時（2026-11-06 16:55）にコンテナが再起動していました（起動時刻 16:56:27）。ファイルと .olean は残っていて、最初の import は 179 秒でした。

## 4. 残る問い

1. **（次の候補）十分性：平方因子なしの N で ⟨D_u, E_N, E_1⟩ = A_N。** 数値の手がかりとして、恒等式 (I) を見つけました。
   - (I)：p ∥ N なら E_p = p(1 − E_1)G_p(1 − E_1) − p²·G_p·T_p·G_p（G_p = Σ_{p ∣ t} D_t = 1_{pℤ/Nℤ}、T_p = Σ_{p ∣ t, t ≠ p} E_t）。step269 の (8) で 29/29 でした（数値だけ）。
   - **フーリエ側の筋（手計算、未検証）。** 𝓕 で写すと、E_1・E_N は 1_{D_1}・δ_0 の掛け算に、G_p は「k mod p の方向の平均」A になります。ℤ/N = ℤ/p × ℤ/M（M = N/p）の各ファイバー {(a, k_M)} で、
     - k_M が単数なら、単数でない点は (0, k_M) だけです。p(1 − 1_{D_1})A(1 − 1_{D_1}) はそこで 1_{D_p} として働きます。
     - k_M が単数でなければ、ファイバー全体が単数でなく、p·A として働きます。その部分は p²A·1_{T}·A（T = 単数でない k_M をもつ k_p = 0 の点）と等しくなり、引くと消えます。
   - **N = pq の場合。** T_p = E_N なので、(I) から E_p ∈ ⟨D_u, E_N, E_1⟩ がすぐ出ます。E_q も同じで、Σ_t E_t = 1 と合わせて B_1 = A_{pq} です。
     - Lean では、両辺を f に作用させ、𝓕 で 1_{D_t} の掛け算と平均の作用素に移して点ごとに比べる形になる見込みです。N = 2q は今回の |S′| ≤ 2 で済んでいます。
   - **素因数 3 つ以上。** T_p に E_{pq} などが入ります。これらを B_1 で作るには、(I) の E_1 を別の殻の和に替えた形が要りそうです（未確認）。語の長さ（(8)：E_6 などは長さ 5）も、もう 1 段の構成を示しています。
2. **平方因子ありの N の障害。** s = 1 で U_1^⊥ ≠ 0（N = 12 で 1 次元、N = 18 で 2 次元）です。その元を具体的に与えて、判定法で E_t ∉ B_1 となる t を示すことです。2 点の証拠は使えません（§0 の 7）。
3. **観察 (2) の証明。** |S′| ≥ 3 で B_s = A_N ⇔ U_s^⊥ = 0。⇒ の向きは、判定法と「A_N の元で殻ごとのスカラーでないもの」から出るかもしれません。
4. **dim B_s の閉じた形。** 平方因子なしの N = 2·3·q（F = 100）では、奇素因数の s で 84 になりました（N = 30, 42, 66, 78, 102）。N = 70, 110（= 2·5·7、2·5·11）の s = 5 も 84 です。N = 15 で 22、N = 105 で 104 でした。
5. **A_N を生成するのに要る E の個数。** 平方因子ありで |S′| ≥ 3 の N では、E を 1 つ足しても足りません。何個で足りるか、どの組で足りるかを求めることです。
6. **引き継ぎメモのほかの候補。** B1 + B2 の補空間を張る元、dim A_N − dim ⟨D_u, E_N⟩ の閉じた形、⟨D_u, E_s⟩（s ≠ N）の空間全体の構造、C_N の PiTensorProduct の形、ほか。
