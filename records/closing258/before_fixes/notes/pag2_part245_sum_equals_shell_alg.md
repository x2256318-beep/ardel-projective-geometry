# アデール射影幾何 2.0 — Part 245：⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ = A_N ⇔ N ∈ {1, 8} ∪ {p, p²}（2 つの双対な代数の和が A_N 全体になる条件）

2026-11-05。引き継ぎメモの次の候補を Lean で証明しました。候補は、Part 244 の観察 (7)「⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ = A_N ⇔ N ∈ {1, 8} ∪ {p, p²}」で、前回は数値だけでした。ここでの和は部分空間としての和です。代数として生成されるものは、すべての D_s・E_s を含むので常に A_N になります。

- **主定理（Lean）。** **B1 + B2 = A_N ⇔ N = 1 ∨ N = 8 ∨ N = p ∨ N = p²（p は素数）**（`sumSub_eq_shellAlg_iff`）。ここで B1 = ⟨D_u, E_N⟩、B2 = ⟨E_u, D_N⟩ です。
  - **包含と次元。** B2 ≤ A_N（𝓕A_N𝓕⁻¹ = A_N）なので B1 + B2 ≤ A_N で、等号は次元の一致と同じです（`sumSub_eq_iff_finrank`）。
    - 和の次元は Part 244 から dim(B1 + B2) + 3 + 2[2 ∣ N] = d(N)² + 2d(N)（N ≥ 3）です（`finrank_sumSub_add`）。
  - **素冪では差がちょうど求まります。**
    - dim A_{p^k} − dim(B1 + B2) = (k − 1)(k − 2)/2（p 奇数）です（`finrank_shellAlg_primePow_odd_sum`）。
    - p = 2、k ≥ 2 では (k − 2)(k − 3)/2 です（`finrank_shellAlg_two_pow_sum`）。
    - 0 になるのは p、p²、4、8 だけです。
  - **素因数が 2 つ以上なら真に小さくなります。** N = p^k·M（p = minFac N、M > 1 は奇数）と分けます。
    - dim A_N = dim A_{p^k}·dim A_M（Part 226）と、dim A_M ≥ dim ⟨D_u, E_M⟩ = d(M)² + d(M) − 1 を使います。
    - これに x = k + 1、y = d(M) の 2 変数の不等式を合わせて、dim(B1 + B2) < dim A_N を示しました（`finrank_sumSub_lt_of_eq_mul`）。
- **系（Lean）。**
  - 式の形（N ≥ 3）：Π_{p^k ∥ N}((k+1)² + k(k+1)/2 − [p = 2]k) = d² + 2d − 3 − 2[2 ∣ N] ⇔ N = 8 ∨ N = p ∨ N = p²（`prod_eq_sum_iff`）。
  - **和は A_N なのに ⟨D_u, E_N⟩ ≠ A_N となるのは、N = 8 と奇素数の平方 N = p² だけ**です（`sumSub_eq_and_ne_iff`）。どちらの代数だけでも A_N にならないのに、2 つ合わせると A_N 全体を張る N です。
- **限界（正直な注記）。**
  - 素因数が 2 つ以上のときの差 dim A_N − dim(B1 + B2) は、Lean では 1 以上であることだけを示しました。具体的な値は 2 つの式から計算できます（例：N = 6 で 1、N = 12 で 7、N = 36 で 26）。
  - 証明に使った下からの評価 dim A_M ≥ dim ⟨D_u, E_M⟩ は粗いものです。余裕の最小は 1 で、N = 6 で起きました（数値）。N = 2q（q は奇素数）では差がちょうど 1 になります。
- **やり直し。**
  - 試しのファイル T1・T2 は、どちらも 1 回目にエラーがあり、2 回目で通りました（§3）。
  - PAG249 は 1 回目のコンパイルで通りました。数値照合は 1 回の実行ですべて合格しました。
- **環境。** Mathlib の追加ビルドはありません。Part 245 の開始時（21:17）にコンテナが再起動していました。import の温めは 22 秒でした。

成果物は次のとおりです。
- `PAG249.lean`：23 項目。sorry 0・警告 0 です。
  - 定義 1 個（`sumSub`）は項目に数えません。
  - 出力は `PAG249.out`（#print axioms 24 行）。
- 照合用の `step268.py`：ログは `step268.log` です。

xlsx の集計は 3151 項目になりました（手順 265）。

## 0. 結論

**記号**（Part 241〜244 と同じ）
- B1 = ⟨D_u, E_N⟩ = `oneEAlg N N`、B2 = ⟨E_u, D_N⟩ = `dualOneEAlg N`、B1 + B2 = `sumSub N`（部分空間）。
- d = d(N)、S′ = {t ∣ N : φ(N/t) ≠ 1}、|S′| = d − 1 − [2 ∣ N]（Part 241）。
- F(N) = dim A_N = Π_{p^k ∥ N}((k+1)² + k(k+1)/2 − [p = 2]k)（Part 226）。
- G(N) = dim B1 = d² + d − 1 − [2 ∣ N]（Part 241）。H(N) = dim(B1 + B2) = d² + 2|S′| − 1（N ≥ 3、Part 244）。

| 定理 | 主張 |
|---|---|
| `dualOneEAlg_le`, `sumSub_le`, `finrank_sumSub_le`, **`sumSub_eq_iff_finrank`** | B2 ≤ A_N、B1 + B2 ≤ A_N、dim(B1 + B2) ≤ dim A_N、B1 + B2 = A_N ⇔ 次元が等しい |
| **`finrank_sumSub_add`**, `finrank_sumSub_eq_of_shellAlg_eq` | N ≥ 3 で dim(B1 + B2) + 3 + 2[2 ∣ N] = d² + 2d。A_N = B1 なら和 = A_N |
| `half_mul_succ_add_one`, `half_mul_succ_add_three`, `finrank_sumSub_primePow_add` | k(k+1)/2 + 1 = 2k + (k − 1)(k − 2)/2、k(k+1)/2 + 3 = 3k + (k − 2)(k − 3)/2、dim(和_{p^k}) の式 |
| **`finrank_shellAlg_primePow_odd_sum`**, **`finrank_shellAlg_two_pow_sum`** | dim A_{p^k} = dim(和) + (k − 1)(k − 2)/2（p 奇数）、dim A_{2^k} = dim(和) + (k − 2)(k − 3)/2（k ≥ 2） |
| `finrank_sumSub_lt_of_eq_primePow_odd`, `finrank_sumSub_lt_of_eq_two_pow`, `finrank_sumSub_eq_of_eq_sq`, `finrank_sumSub_eq_two_pow_three` | p^k（p 奇数、k ≥ 3）と 2^k（k ≥ 4）で和 < A、p² と 8 で和 = A |
| `ineq_odd`, `ineq_two`, **`finrank_sumSub_lt_of_eq_mul`** | x, y ≥ 2 での 2 つの不等式。N = p^k·M（M > 1 は奇数）で dim(和) < dim A_N |
| `finrank_sumSub_lt_shellAlg`, **`sumSub_eq_shellAlg_iff`**, `finrank_sumSub_eq_iff` | N ∉ {1, 8} ∪ {p, p²} で dim(和) < dim A_N。主定理とその次元の形 |
| **`prod_eq_sum_iff`**, **`sumSub_eq_and_ne_iff`** | 式の形（N ≥ 3）。和 = A_N かつ B1 ≠ A_N ⇔ N = 8 ∨ N = p²（p 奇素数） |

**証明の筋**
1. **包含。** B2 = 𝓕B1𝓕⁻¹ ≤ 𝓕A_N𝓕⁻¹ = A_N（Part 242）なので、B1 + B2 ≤ A_N です。部分空間の包含では、等号は次元の一致と同じです。
2. **和の次元。** Part 244 の dim(B1 + B2) + 1 = d² + 2|S′|（N ≥ 3）と、Part 241 の |S′| + 1 + [2 ∣ N] = d から、dim(B1 + B2) = d² + 2d − 3 − 2[2 ∣ N] です。
3. **素冪。** d(p^k) = k + 1 です。
   - p 奇数では、F − H = (k+1)² + k(k+1)/2 − ((k+1)² + 2k − 1) = k(k+1)/2 − 2k + 1 = (k − 1)(k − 2)/2 です。
   - p = 2 では、F − H = k(k+1)/2 − k − (2k − 3) = (k − 2)(k − 3)/2 です。
   - 自然数の割り算のままで扱うため、k(k+1) = 2(2k − 1) + (k − 1)(k − 2) などの恒等式を、k = m + 1（m + 2）と置いて示しました。
4. **素因数 2 つ以上。** p = minFac N、N = p^k·M です（Mathlib の `Nat.ordProj_mul_ordCompl_eq_self`）。M の素因数はどれも p より大きいので、M は奇数です。
   - x = k + 1 ≥ 2、y = d(M) ≥ 2 と置くと、d(N) = xy です。
   - **p 奇数のとき。** dim A_{p^k} ≥ x² + 1 です。dim(B1 + B2) = x²y² + 2xy − 3 なので、不等式 2xy + x² + 1 < x²y + y² + y + 2 から dim(B1 + B2) < (x² + 1)(y² + y − 1) ≤ dim A_N です。
   - **p = 2 のとき。** dim A_{2^k} ≥ x² です。dim(B1 + B2) = x²y² + 2xy − 5 なので、不等式 2xy + x² ≤ x²y + 4 から dim(B1 + B2) < x²(y² + y − 1) ≤ dim A_N です。
   - 不等式は x = a + 2、y = b + 2 と置くと、差が a²b + a² + 2ab + b² + 5b + 3 と a²b + a² + 2ab になります（係数がすべて非負）。
5. **主定理。**
   - ⇐：N = 1 と素数では、Part 242 の主定理で A_N = B1 です。p² と 8 では、3 の差の式が 0 です。
   - ⇒：条件の外では、M = 1（p^k で、p 奇数なら k ≥ 3、p = 2 なら k ≥ 4）でも M > 1 でも、dim(和) < dim A_N です。
6. **系。** Part 242 の A_N = B1 ⇔ N ∈ {1, 4} ∪ 素数 と比べます。違いは 8 と奇素数の平方です（p² は素数でなく、p² = 4 ⇔ p = 2）。

**例**（数値でも確認）
- N = 8：dim B1 = dim B2 = 18 < 19 = dim A_8 です。dim(B1 ∩ B2) = 17（Part 244）なので、dim(B1 + B2) = 18 + 18 − 17 = 19 = dim A_8 になります。
- N = 9：dim B1 = 11 < 12 = dim A_9 で、dim(B1 + B2) = 12 です。N = 25 も同様です。
- 差 dim A_N − dim(B1 + B2)：
  - 2^k では k = 2, 3 で 0、k = 4, 5, 6, 7 で 1, 3, 6, 10 です。3^k では k = 3, 4 で 1, 3 です。
  - N = 6 で 1（20 − 19）、N = 12 で 7（50 − 43）、N = 36 で 26（120 − 94）、N = 48 で 40（155 − 115）です。

**読み取れること**
- A_N の元は P と可換なので、動径関数の上の部分 Φ(M_d) と、殻の平均が 0 の関数の上の部分に分かれます（Part 240）。B1 は後者に「位置の殻ごとのスカラー」、B2 は「周波数の殻ごとのスカラー」をもちます（Part 243・244）。和が A_N になる N では、この 2 種類で後者がちょうど張れます。
- それ以外の N では、殻の平均が 0 の部分に、2 つの代数の和では張れない成分が残ります。A_N は D_s・E_t の積で張られるので、残りは D_s と E_t を交互に掛けた積から来ると考えられます（読み取り。具体的な補空間は §4 の 2）。
- Part 242 の「B1 だけで A_N」（N ∈ {1, 4} ∪ 素数）と比べると、和で新たに届くのは 8 と奇素数の平方だけです。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| B2 ≤ A_N、B1 + B2 ≤ A_N、等号 ⇔ 次元が等しい | **正しい（`dualOneEAlg_le`、`sumSub_le`、`sumSub_eq_iff_finrank`）**。数値でも包含 48/48（N ≤ 48） |
| dim(B1 + B2) + 3 + 2[2 ∣ N] = d² + 2d（N ≥ 3） | **正しい（`finrank_sumSub_add`）**。数値でも生成元から 48/48 |
| 素冪の差 (k − 1)(k − 2)/2（p 奇数）、(k − 2)(k − 3)/2（p = 2、k ≥ 2） | **正しい（`finrank_shellAlg_primePow_odd_sum`、`finrank_shellAlg_two_pow_sum`）**。数値でも 78733/78733（3 ≤ p^k ≤ 10^6） |
| 素因数 2 つ以上で dim(B1 + B2) < dim A_N | **正しい（`finrank_sumSub_lt_of_eq_mul`）**。数値でも 90299/90299（N ≤ 10^5） |
| **B1 + B2 = A_N ⇔ N ∈ {1, 8} ∪ {p, p²}** | **正しい（`sumSub_eq_shellAlg_iff`）**。数値でも式で 99998/99998、生成元から 48/48（Part 244 では数値だけ） |
| 式の形 F(N) = d² + 2d − 3 − 2[2 ∣ N] ⇔ N ∈ {8} ∪ {p, p²}（N ≥ 3） | **正しい（`prod_eq_sum_iff`）** |
| 和 = A_N かつ B1 ≠ A_N ⇔ N = 8 ∨ N = p²（p 奇素数） | **正しい（`sumSub_eq_and_ne_iff`）** |
| 素因数 2 つ以上での差の具体的な値 | 2 つの式から計算できる。Lean では 1 以上であることだけを示した |
| 下からの評価 F(p^k)·G(M) − H(N) の最小は 1（N = 6） | **数値だけ**（N ≤ 10^5） |

## 2. 数値照合（step268）

| 項目 | 内容 | 結果 |
|---|---|---|
| (1) | 素冪（3 ≤ p^k ≤ 10^6）：|S′| は約数を数えて求め、F − H = (k − 1)(k − 2)/2（p 奇数）・(k − 2)(k − 3)/2（p = 2）。F は閉じた式と Part 226 の積の式の両方で | 78733/78733 |
| (2) | 恒等式 k(k+1)/2 + 1 = 2k + (k − 1)(k − 2)/2（k ≥ 1）、k(k+1)/2 = 3k − 3 + (k − 2)(k − 3)/2（k ≥ 2）（k ≤ 10^5） | 199999/199999 |
| (3) | 素因数 2 つ以上（N ≤ 10^5）：M は奇数かつ p と互いに素、F(N) = F(p^k)F(M)、F(M) ≥ G(M)、F(p^k)G(M) > H(N)、F(N) > H(N) | 90299/90299（余裕の最小は 1、N = 6） |
| (4) | 不等式 2xy + x² + 1 < x²y + y² + y + 2、2xy + x² ≤ x²y + 4（2 ≤ x, y ≤ 300） | 178802/178802 |
| (5) | 式の形（3 ≤ N ≤ 10^5）：F(N) ≥ H(N)、F(N) = H(N) ⇔ N ∈ {8} ∪ {p, p²} | 99998/99998 |
| (6) | 生成元から（N ≤ 48）：A_N を D_s・E_s から直交化で求め、B1 + B2 ⊆ A_N、dim A_N = F(N)、dim(B1 + B2) = H(N)（N ≥ 3、N ≤ 2 では d²）、一致 ⇔ N ∈ {1, 8} ∪ {p, p²} | 48/48 |

- 実行は 1 回です（約 32 秒、そのうち (6) が 31 秒）。項目ごとの結果は `step268_cache.json` に保存しました。
- **限界。** (6) の生成元からの計算は N ≤ 48 です。(3)・(5) は Lean の式（Part 226・241・244）を数値で評価したもので、作用素からの独立な計算ではありません。

## 3. Lean（`PAG249.lean`、namespace `PAG.Part249`、PAG248 を import）

| 区分 | 項目 |
|---|---|
| 1. 包含と次元 | def `sumSub`, `dualOneEAlg_le`, `sumSub_le`, `finrank_sumSub_le`, `sumSub_eq_iff_finrank`, `finrank_sumSub_add`, `finrank_sumSub_eq_of_shellAlg_eq` |
| 2. 素冪 | `half_mul_succ_add_one`, `half_mul_succ_add_three`, `finrank_sumSub_primePow_add`, `finrank_shellAlg_primePow_odd_sum`, `finrank_shellAlg_two_pow_sum`, `finrank_sumSub_lt_of_eq_primePow_odd`, `finrank_sumSub_lt_of_eq_two_pow`, `finrank_sumSub_eq_of_eq_sq`, `finrank_sumSub_eq_two_pow_three` |
| 3. 素因数 2 つ以上 | `ineq_odd`, `ineq_two`, `finrank_sumSub_lt_of_eq_mul` |
| 4. 主定理と系 | `finrank_sumSub_lt_shellAlg`, `sumSub_eq_shellAlg_iff`, `finrank_sumSub_eq_iff`, `prod_eq_sum_iff`, `sumSub_eq_and_ne_iff` |

**使った PAG の結果**
- Part 214 の `shellAlg`（PAG218）、Part 226 の `finrank_shellAlg_eq_prod`・`finrank_shellAlg_mul`（PAG230）
- Part 240 の `oneEAlg`・`oneEAlg_le`（PAG244）、Part 241 の `devSet`・`card_devSet`・`finrank_oneEAlg_self_add`（PAG245）
- Part 242 の `dualOneEAlg`・`map_fourierConj_oneEAlg`・`map_fourierConj_shellAlg`・`finrank_oneEAlg_le`・`card_divisors_primePow`・`finrank_shellAlg_primePow`・`two_dvd_primePow_iff`・`shellAlg_eq_oneEAlg_iff`（PAG246）
- Part 244 の `finrank_sup_add_one`（PAG248）

**Mathlib・Lean から使った主なもの**
- 部分空間と次元：`Subalgebra.map_mono`・`Subalgebra.toSubmodule`（順序の埋め込み）・`sup_le`・`le_sup_left`・`Submodule.finrank_mono`・`Submodule.eq_of_le_of_finrank_eq`
- 自然数：`Nat.mul_add_div`・`Nat.le_div_iff_mul_le`・`Nat.pow_le_pow_right`・`le_self_pow`・`Nat.Coprime.card_divisors_mul`・`Nat.ordProj_mul_ordCompl_eq_self`・`Nat.coprime_ordCompl`・`Nat.ordCompl_pos`・`Nat.not_dvd_ordCompl`・`Nat.ordCompl_dvd`・`Nat.minFac_prime`・`Nat.minFac_le_of_dvd`・`Nat.Prime.factorization_pos_of_dvd`・`Nat.Prime.eq_one_or_self_of_dvd`・`Finset.one_lt_card`
- 不等式：`ring_nf`・`nlinarith`（単項式の非負性 `Nat.zero_le` をヒントに渡す）

**コンパイル**
- `PAG249` は 1 回目のコンパイル（約 14 秒）でエラー・警告なしで通りました。
- 公理は標準のもの（propext、Classical.choice、Quot.sound）か、その一部だけです。24 行のうち 2 行が一部だけです（`half_mul_succ_add_one`・`half_mul_succ_add_three` は [propext, Quot.sound]）。
- 内容は試しのファイル T2 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble249.py`）。
- **試しのファイル（置き場所は `/home/claude/leanwork/scratch/t245`）。**
  - W0：import の温めと API の確認（22 秒）。名前の誤りはありませんでした。
  - T1（§1〜4、22 項目と定義 1 個）：1 回目にエラー 1 件で、2 回目で通りました（13 秒）。
    - M ≠ 2 を `fun h => hM2 (h ▸ dvd_refl 2)` と書いたところ、`▸` が期待される型を `M ∣ M` と推論して合いませんでした。`rintro rfl; exact hM2 (dvd_refl 2)` に直しました。
  - T2（系 4e `sumSub_eq_and_ne_iff` を足した。23 項目と定義 1 個）：1 回目にエラー 2 件で、2 回目で通りました（12 秒）。
    - `norm_num` が `¬ Nat.Prime 8` を示せませんでした。素数を判定する norm_num の拡張が、この import の鎖に入っていないためと思われます（未確認）。
    - `Nat.Prime.pow_not_prime` はこの Mathlib にありませんでした。
    - どちらも `Nat.Prime.eq_one_or_self_of_dvd`（2 ∣ 8、p ∣ p²）で書き直しました。
- 前回の注意を当てはめた箇所があります。
  - 素冪と積の場合の分け方、`generalize` で N に依存する式を変数にする書き方は、Part 242 の `finrank_oneEAlg_lt_shellAlg` と同じ形にしました。
  - 非線形の項（(k+1)²、k(k+1)/2）は `generalize` で変数にしてから `omega` に渡しました。2 変数の不等式は、x = a + 2、y = b + 2 と置いて `ring_nf` の後 `nlinarith` に単項式の非負性を渡しました。
  - 部分空間の次元の比較は `Submodule.finrank_mono` と `Subalgebra.toSubmodule.monotone` で行いました。
- **環境。** Mathlib の追加ビルドはありません。Part 244 の納品（21:13 ごろ）の後、Part 245 の開始時（21:17）にコンテナが再起動していました（起動時刻 21:16:53 ごろ）。ファイルと .olean は残っていて、最初の import は 22 秒でした。

## 4. 残る問い

1. **（次の候補）E_s を 1 つ足した代数。** B1 に E_s（s ∈ S′）を 1 つ足した ⟨D_u, E_N, E_s⟩ の次元と構造を求めることです。どの s で A_N 全体が出るかも問えます。
   - N = p² では S′ = {1, p} で、E_1 = 1 − E_p − E_N なので、どちらを足しても A_N です。
   - 約数の多い N では、1 つでは足りないかもしれません。まず数値で、s ごとの次元を求めます。
2. **和の補空間。** B1 + B2 ≠ A_N の N で、A_N/(B1 + B2) を張る元（D_s E_t D_u のような積）を具体的に与え、次元 F(N) − H(N) を Part 225 の成分 n_p の言葉で書くことです。
3. **次元の差の閉じた形。** 素因数 2 つ以上のときの dim A_N − dim ⟨D_u, E_N⟩ を、単数群の指標の言葉で書くことです。
4. **ほかの殻の組み合わせ。** ⟨D_u, E_s⟩（Part 240）の空間全体の構造と次元を、s ≠ N でも求めることです。
5. **引き継ぎメモのほかの候補。** $C_N = \bigotimes_pC_{p^{v_p}}$ の PiTensorProduct の形、dilComm$_{q^k}$、$A_N$ のウェダーバーン成分の分配の形、中心そのものの finrank、P・Q_s の自己共役、ほか。
