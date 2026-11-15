# アデール射影幾何 2.0 — Part 244：⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩ = Φ(M_d(ℂ)) + ℂ(1 − P) ≅ M_{d(N)}(ℂ) × ℂ（フーリエ双対との共通部分）

2026-11-05。引き継ぎメモの次の候補「双対との共通部分 ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩」を、数値で形を確かめてから Lean で証明しました。共通部分は N によらず同じ形で、動径関数の上の作用 Φ(M) すべてと、殻の平均が 0 の関数の上のスカラー倍だけからなります。

- **主定理（Lean）。**
  - **X ∈ ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩ ⇔ X = Φ(M) + c(1 − P)**（M は d(N) 次の行列、c ∈ ℂ。`mem_inf_iff`）です。
    - 言い換えると X = Φ(M) + c·1 で、共通部分 = Φ(M_d(ℂ)) + ℂ·1 です（`mem_inf_iff_one`）。
  - N ≥ 3 では、(M, c) ↦ Φ(M) + c(1 − P) が代数の同型 **M_{d(N)}(ℂ) × ℂ ≃ 共通部分** です（`interAlgEquiv`）。
  - 次元は **d(N)² + [N ≥ 3]** です（`finrank_inf_eq`）。N ≤ 2 では、共通部分は ⟨D_u, E_N⟩ 全体です（`inf_eq_oneEAlg_of_le_two`）。
- **証明の要（Lean）。**
  - **𝓕 と殻の平均 P は可換**です：𝓕(Pf) = P(𝓕f)（`dft_shellAvg`）、𝓕P𝓕⁻¹ = P（`fourierConj_shellAvg`）。
  - **双対側の判定：** X ∈ ⟨E_u, D_N⟩ なら、殻の平均が 0 の f に $Xf = \sum_{t\in S′}c_tE_tf$ です（`exists_apply_of_mem_dualOneEAlg`）。Part 243 の判定（$Xf = \sum_tb_t1_{D_t}f$）のフーリエ双対です。
  - **証拠：** t ∈ S′ なら $h_t = \delta_t - \delta_{-t}$ は殻の平均が 0 です。さらに $(E_1h_t)(t) = (\varphi(N) - c_N(2t))/N\ne0$ です（`convL_geps_one_pairFn_ne_zero`）。
    - 共通部分の元を $g = E_1h_t$ に作用させます。点 t で比べると、殻ごとのスカラー $b_t$ が双対側の定数 c に等しくなります。
- **系（Lean）。**
  - 和の次元は、N ≥ 3 で dim(⟨D_u, E_N⟩ + ⟨E_u, D_N⟩) + 1 = d(N)² + 2|S′| です（`finrank_sup_add_one`）。
  - 共通部分はフーリエ変換で不変です：𝓕(共通部分)𝓕⁻¹ = 共通部分（`map_fourierConj_inf`）。
- **観察（数値だけ）。** ⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ = A_N となるのは、N ∈ {1, 8} ∪ {p, p²}（p は素数）のときだけでした（式の水準で N ≤ 100000、生成元からの計算で N ≤ 60）。
- **見込み違い（正直な記録）。** 前回のメモには、手計算の見込みとして「共通部分は N によって違いそう（N = 8 では δ_2 − δ_6 がすべての D_t・E_t の固有ベクトル）」と書きました。
  - 固有ベクトルであること自体は正しいですが、共通部分は大きくなりませんでした。どの N でも、殻の平均が 0 の部分ではスカラー倍だけです。
  - 同じメモで未確認としていた「どちらの代数も Φ(M) をすべて含む」は、今回 Lean で示しました（`radialMatOp_mem_dualOneEAlg`）。
- **やり直し。**
  - 試しのファイルは T1 が 3 回目、T3 が 2 回目で通りました。T2 は 1 回目で通りました（§3）。
  - PAG248 は 1 回目のコンパイルで通りました。数値照合は、Lean に合わせて項目 (8) を足して 2 回実行しました（§2）。
- **環境。** Mathlib の追加ビルドはありません。Part 244 の開始時（20:49）にコンテナが再起動していました。import の温めは 19 秒でした。

成果物は次のとおりです。
- `PAG248.lean`：34 項目。sorry 0・警告 0 です。
  - 定義 3 個（`pairFn`・`interHom`・`interAlgEquiv`）は項目に数えません。
  - 出力は `PAG248.out`（#print axioms 37 行）。
- 照合用の `step267.py`：ログは `step267.log` です（1 回目のログは `step267_run1.log`）。

xlsx の集計は 3128 項目になりました（手順 264）。

## 0. 結論

**記号**（Part 239〜243 と同じ）
- $D_t = \{x : \gcd(N,x) = t\}$、$1_{D_t}$ = `dind N t`、$\varepsilon_s = \mathcal F^{-1}1_{D_s}$、$E_sf = \varepsilon_s\star f$、$D_sf = 1_{D_s}f$。
- P = `shellAvg N`（殻の平均）、$\Phi(M) = \sum M_{uv}P_{u,v}$、$Q_t = D_t - P_{t,t}$、$S′ = \{t\mid N : \varphi(N/t)\ne1\}$。
- ⟨D_u, E_N⟩ = `oneEAlg N N` の元は $\Psi(M, b) = \Phi(M) + \sum_{t\in S′}b_tQ_t$ です（Part 241）。⟨E_u, D_N⟩ = `dualOneEAlg N` = $\mathcal F\langle D_u, E_N\rangle\mathcal F^{-1}$ です（Part 242）。
- B1 = ⟨D_u, E_N⟩、B2 = ⟨E_u, D_N⟩、G(N) = dim B1 = d² + |S′|（Part 241）、F(N) = dim A_N（Part 226）。

| 定理 | 主張 |
|---|---|
| `fourierConj_apply`, **`dft_shellAvg`**, `dft_symm_shellAvg`, **`fourierConj_shellAvg`**, `shellAvg_dft_symm_eq_zero` | (𝓕T𝓕⁻¹)h = 𝓕(T(𝓕⁻¹h))、𝓕P = P𝓕、𝓕⁻¹P = P𝓕⁻¹、𝓕P𝓕⁻¹ = P、𝓕⁻¹ は殻の平均が 0 の関数を保つ |
| `shellAvg_dind_mul`, `shellAvg_convL_geps` | P(1_{D_t}g) = 1_{D_t}Pg、P(E_sh) = E_s(Ph) |
| `exists_apply_convL_geps_one`, **`exists_apply_of_mem_dualOneEAlg`** | X ∈ ⟨E_u, D_N⟩ なら、Ph = 0 の h に X(E_1h) = c·E_1h。一般に Pf = 0 の f に $Xf = \sum_{t\in S′}c_tE_tf$ |
| `shellAvg_pairFn`, `convL_geps_pairFn_apply`, `not_dvd_two_mul`, **`convL_geps_one_pairFn_ne_zero`** | $h_a = \delta_a - \delta_{-a}$（def `pairFn`）は Ph_a = 0、$(E_sh_a)(a) = \varepsilon_s(0) - \varepsilon_s(2a)$、t ∈ S′ なら N ∤ 2t、$(E_1h_t)(t)\ne0$ |
| `radialMatOp_mul_shellAvg`, `shellAvg_mem_dualOneEAlg`, **`radialMatOp_mem_dualOneEAlg`**, `radialMatOp_add_smul_mem_inf`, `sum_smul_shellDev` | Φ(M)P = Φ(M)、P ∈ B2、Φ(M) ∈ B2、Φ(M) + c(1 − P) ∈ B1 ∩ B2、$\sum_{s\in S′}cQ_s = c(1-P)$ |
| **`mem_inf_iff`**, **`mem_inf_iff_one`** | X ∈ B1 ∩ B2 ⇔ X = Φ(M) + c(1 − P) ⇔ X = Φ(M) + c·1 |
| `one_mem_devSet`, `interHom_apply`, `range_interHom`, `interHom_injective`, **`interAlgEquiv_apply`**, **`finrank_inf`** | N ≥ 3 で 1 ∈ S′、(M, c) ↦ Φ(M) + c(1 − P)（def `interHom`）の像は B1 ∩ B2 で単射、同型 M_d(ℂ) × ℂ ≃ B1 ∩ B2（def `interAlgEquiv`）、dim = d² + 1 |
| `totient_div_eq_one_of_le_two`, `inf_eq_oneEAlg_of_le_two`, **`finrank_inf_eq`** | N ≤ 2 で S′ = ∅ かつ B1 ∩ B2 = B1。すべての N で dim(B1 ∩ B2) = d(N)² + [N ≥ 3] |
| `toSubmodule_inf`, `finrank_sup_add_finrank_inf`, **`finrank_sup_add_one`** | dim(B1 + B2) + dim(B1 ∩ B2) = 2·dim B1。N ≥ 3 で dim(B1 + B2) + 1 = d² + 2\|S′\| |
| `fourierConj_radialMatOp_mem_inf`, **`map_fourierConj_inf`** | 𝓕Φ(M)𝓕⁻¹ ∈ B1 ∩ B2。𝓕(B1 ∩ B2)𝓕⁻¹ = B1 ∩ B2 |

**証明の筋**
1. **𝓕 と P は可換。**
   - P は単数倍の平均 $(1/\varphi(N))\sum_aU_a$ です（Part 240）。$\mathcal FU_a = U_{a^{-1}}\mathcal F$（Part 214 の `dft_dil`）なので、和の添字を $a\mapsto a^{-1}$ で付け替えて 𝓕P = P𝓕 です。
   - とくに 𝓕 と 𝓕⁻¹ は、殻の平均が 0 の関数の空間 ker P を保ちます。
2. **双対側の判定。**
   - X ∈ B2 なら、ある Y ∈ B1 で X = 𝓕Y𝓕⁻¹ です。Pf = 0 なら P𝓕⁻¹f = 0 なので、Part 243 の判定から $Y\mathcal F^{-1}f = \sum_tb_t1_{D_t}\mathcal F^{-1}f$ です。
   - $\mathcal F(1_{D_t}\cdot\mathcal F^{-1}f) = E_tf$（Part 242 の 𝓕D_t𝓕⁻¹ = E_t）から、$Xf = \sum_tb_tE_tf$ です。
   - f = E_1h（Ph = 0）では、$1_{D_t}1_{D_1} = [t = 1]1_{D_1}$ から X(E_1h) = c·E_1h です。c はある 1 つの係数で、h によりません。
3. **証拠。**
   - t ∈ S′ なら N/t ≥ 3 なので N ∤ 2t、つまり −t ≢ t です。t と −t は同じ殻にあるので、$h_t = \delta_t - \delta_{-t}$ は殻の平均が 0 です。
   - $(E_1h_t)(t) = \varepsilon_1(0) - \varepsilon_1(2t) = (\varphi(N) - c_N(2t))/N$ です（$N\varepsilon_1(u) = c_N(u)$、Part 240）。
   - Part 243 の c_N(n) = φ(N) ⇔ N ∣ n から、これは 0 ではありません。
4. **主定理。**
   - X ∈ B1 ∩ B2 を X = Ψ(M, b) と書きます。$g = E_1h_t$ も殻の平均が 0 です（E_1 は P と可換）。
   - B1 の側から $Xg = \sum_sb_s1_{D_s}g$、B2 の側から Xg = c·g です。点 t で比べると $b_tg(t) = c\,g(t)$ で、g(t) ≠ 0 なので $b_t = c$ です。
   - すべての t ∈ S′ で $b_t = c$ なので、$X = \Phi(M) + c\sum_tQ_t = \Phi(M) + c(1-P)$ です。
   - 逆向き：T = 𝓕⁻¹Φ(M)𝓕 は A_N の元で（Part 242）、TP = T です。Part 240 の TP = Φ([T]) から T ∈ B1、よって Φ(M) = 𝓕T𝓕⁻¹ ∈ B2 です。P ∈ B2 も同様です。
5. **構造と次元。**
   - (M, c) ↦ Ψ(M, (c, …, c)) は、Part 241 の代数の準同型を対角に制限したものです。N ≥ 3 では 1 ∈ S′ なので単射で、像は B1 ∩ B2 です。
   - N ≤ 2 では S′ = ∅ で、Ψ(M, b) = Φ(M) ∈ B2 です。よって B1 ∩ B2 = B1 で、次元は d² です（N = 1 で 1、N = 2 で 4）。
6. **和とフーリエ変換。**
   - 次元の公式 dim(B1 + B2) + dim(B1 ∩ B2) = dim B1 + dim B2 と dim B2 = dim B1（Part 242）から、dim(B1 + B2) = 2(d² + |S′|) − (d² + 1) です。
   - 𝓕(Φ(M) + c(1 − P))𝓕⁻¹ = 𝓕Φ(M)𝓕⁻¹ + c(1 − P) は再び B1 ∩ B2 の元です。包含と次元の一致から等号が出ます。

**例**
- 次元（数値でも確認）：N = 6 で dim B1 = dim B2 = 18、dim(B1 ∩ B2) = 17 = 4² + 1、dim(B1 + B2) = 19。N = 12 で 40・37・43、N = 30 で 70・65・75、N = 60 で 154・145・163。
- 素数 N = p と N = 4 では B1 = B2 = A_N なので、共通部分も A_N です（5 = 2² + 1、10 = 3² + 1）。
- 証拠の値 $(E_1h_t)(t)$（数値で確認）：N = 6, t = 2 で (2 − (−1))/6 = 1/2、N = 8, t = 2 で (4 − (−4))/8 = 1、N = 9, t = 3 で (6 − (−3))/9 = 1、N = 12, t = 2 で (4 − (−2))/12 = 1/2。
- 和と A_N（観察）：N = 8 では dim(B1 + B2) = 19 = F(8) なので B1 + B2 = A_8 です。N = 6 では 19 < F(6) = 20、N = 16 では 30 < 31、N = 12 では 43 < 50 です。

**読み取れること**
- どちらの代数も、動径関数の上では任意の作用 Φ(M) をもちます。動径関数の空間と P は 𝓕 で保たれるので、この部分は自己双対です。
- 違いは、殻の平均が 0 の関数の上での作用です。B1 は位置の殻ごとのスカラー $\sum b_t1_{D_t}$、B2 は周波数の殻ごとのスカラー $\sum c_tE_t$ で働きます。
- 2 つの分解に共通する非自明な部分はありません。証拠 $h_t$ が、位置の殻 $D_t$ と周波数の殻 $D_1$（E_1）を結びつけるためです。そのため、共通部分は最小の形 Φ(M_d) ⊕ ℂ(1 − P) になります。
- 代数としては、Part 241 の ⟨D_u, E_N⟩ ≅ M_d(ℂ) × ℂ^{S′} の中で、ℂ^{S′} を対角の ℂ に縮めたものです。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| 𝓕P = P𝓕（𝓕P𝓕⁻¹ = P） | **正しい（`dft_shellAvg`、`fourierConj_shellAvg`）**。数値でも 60/60 |
| 𝓕Φ(M)𝓕⁻¹ ∈ Φ(M_d) | 証明の中では示して使った（`fourierConj_radialMatOp_mem_inf` の証明で 𝓕Φ(M)𝓕⁻¹ = Φ([·])）が、定理として述べたのは 𝓕Φ(M)𝓕⁻¹ ∈ B1 ∩ B2 だけ。数値でも 60/60 |
| 𝓕Q_t𝓕⁻¹ = E_t(1 − P)（作用素の等式） | **数値だけ**（60/60）。Lean では、関数の水準の判定（次の行）の形で使った |
| X ∈ ⟨E_u, D_N⟩ なら、Pf = 0 の f に $Xf = \sum_{t\in S′}c_tE_tf$ | **正しい（`exists_apply_of_mem_dualOneEAlg`）**。数値でも 180/180 |
| t ∈ S′ で $h_t = \delta_t - \delta_{-t}$ は Ph_t = 0、$(E_1h_t)(t)\ne0$ | **正しい（`shellAvg_pairFn`、`convL_geps_one_pairFn_ne_zero`）**。数値でも 1317/1317（N ≤ 300） |
| その値は (φ(N) − c_N(2t))/N | **数値だけ**（1317/1317）。定理としては「0 でない」だけ |
| **B1 ∩ B2 = {Φ(M) + c(1 − P)} = Φ(M_d) + ℂ·1** | **正しい（`mem_inf_iff`、`mem_inf_iff_one`）**。数値でも 40/40（N ≤ 40） |
| N ≥ 3 で B1 ∩ B2 ≅ M_{d(N)}(ℂ) × ℂ（代数として） | **正しい（`interAlgEquiv`、`interAlgEquiv_apply`）**。積の形は数値でも 40/40 |
| dim(B1 ∩ B2) = d(N)² + [N ≥ 3] | **正しい（`finrank_inf_eq`）**。数値でも 60/60（N ≤ 60） |
| dim(B1 + B2) + 1 = d² + 2\|S′\|（N ≥ 3） | **正しい（`finrank_sup_add_one`）**。数値でも 60/60 |
| 𝓕(B1 ∩ B2)𝓕⁻¹ = B1 ∩ B2 | **正しい（`map_fourierConj_inf`）**。数値でも 40/40 |
| B1 + B2 = A_N ⇔ N ∈ {1, 8} ∪ {p, p²} | **数値だけ（観察）**。式の水準で N ≤ 100000（9659 個すべて一致）、生成元から N ≤ 60 |
| （前回のメモの見込み）共通部分は N によって違いそう | **誤り**。どの N でも Φ(M_d) + ℂ(1 − P)（N ≤ 2 では Φ(M_d)） |

## 2. 数値照合（step267）

| 項目 | 内容 | 結果 |
|---|---|---|
| (1) | 基底（Part 241 の $P_{s,t}$・$Q_t$ とその 𝓕 共役）から：dim B1 = dim B2 = G(N)、dim(B1 ∩ B2) = d² + [N ≥ 3]、dim(B1 + B2) = d² + 2\|S′\| − 1（N ≥ 3）、= d²（N ≤ 2）（N ≤ 60） | 60/60 |
| (2) | 𝓕P = P𝓕、𝓕Q_t𝓕⁻¹ = E_t(1 − P)（t ∈ S′）、乱数の M で 𝓕Φ(M)𝓕⁻¹ ∈ span{P_{s,t}}（N ≤ 60） | 60/60（5.3e-14） |
| (3) | 証拠：t ∈ S′ で −t ≢ t、Ph_t = 0、$(E_1h_t)(t) = (\varphi(N) - c_N(2t))/N\ne0$（c_N は整数で厳密に、3 ≤ N ≤ 300 のすべての t ∈ S′） | 1317/1317（2.3e-14） |
| (4) | 特徴づけ：共通部分の基底が span{P_{s,t}, 1 − P} に入る、乱数の Φ(M) + c(1 − P) が B1 と B2 に入る、基底の個数 = d² + [N ≥ 3]（N ≤ 40） | 40/40（3.3e-14） |
| (5) | 代数の形：(Φ(M) + c(1 − P))(Φ(M′) + c′(1 − P)) = Φ(MM′) + cc′(1 − P)、Φ(1) = P（N ≤ 40） | 40/40（1.1e-14） |
| (6) | 𝓕(B1 ∩ B2)𝓕⁻¹ = B1 ∩ B2（N ≤ 40） | 40/40 |
| (7) | 観察（数値だけ）：dim(B1 + B2) ≤ F(N)（N ≤ 60）と、等号となる N。式の水準（N ≤ 100000）では d² + 2\|S′\| − 1 と F(N) を比べた | ≤ はすべて成立。等号 ⇔ N ∈ {1, 8} ∪ {p, p²}（N ≤ 60 で 23 個、N ≤ 100000 で 9659 個、予想の集合と一致） |
| (8) | 双対側の判定：乱数の Y = Ψ(M, b)、X = 𝓕Y𝓕⁻¹、Pf = 0 の乱数の f で $Xf = \sum_tb_tE_tf$（N ≤ 60、各 3 組） | 180/180（3.6e-13） |

- **実行は 2 回です。**
  - 1 回目（約 10 秒）は項目 (1)〜(7) で、すべて合格しました。
  - その後で Lean に双対側の判定（`exists_apply_of_mem_dualOneEAlg`）を足したので、項目 (8) を足して 2 回目を実行しました。2 回目は (1)〜(7) を保存済みの結果（`step267_cache.json`）から読み、(8) だけを計算しました（0.2 秒）。
  - `step267.log` は 2 回目のログです。1 回目のログは `step267_run1.log` に残しました。違いは「保存済みの結果を使用」の行、(8) の行、秒数の行だけです。
- **限界。**
  - (1) の次元は、基底のベクトルの階数（特異値の相対しきい値 1e-9）で数えました。
  - (7) の式の水準の比較は、d² + 2|S′| − 1（今回 Lean の `finrank_sup_add_one`）と F(N)（Part 226 の Lean の式）を比べたものです。B1 + B2 ⊆ A_N なので、等号は B1 + B2 = A_N と同じです。

## 3. Lean（`PAG248.lean`、namespace `PAG.Part248`、PAG247 を import）

| 区分 | 項目 |
|---|---|
| 1. 𝓕 と P の可換性 | `fourierConj_apply`, `dft_shellAvg`, `dft_symm_shellAvg`, `fourierConj_shellAvg`, `shellAvg_dft_symm_eq_zero` |
| 2. D_t・E_s と P | `shellAvg_dind_mul`, `shellAvg_convL_geps` |
| 3. 双対側の判定 | `exists_apply_convL_geps_one`, `exists_apply_of_mem_dualOneEAlg` |
| 4. 証拠の関数 | def `pairFn`, `shellAvg_pairFn`, `convL_geps_pairFn_apply`, `not_dvd_two_mul`, `convL_geps_one_pairFn_ne_zero` |
| 5. 共通部分 | `radialMatOp_mul_shellAvg`, `shellAvg_mem_dualOneEAlg`, `radialMatOp_mem_dualOneEAlg`, `radialMatOp_add_smul_mem_inf`, `sum_smul_shellDev`, `mem_inf_iff`, `mem_inf_iff_one`, `one_mem_devSet`, def `interHom`, `interHom_apply`, `range_interHom`, `interHom_injective`, def `interAlgEquiv`, `interAlgEquiv_apply`, `finrank_inf`, `totient_div_eq_one_of_le_two`, `inf_eq_oneEAlg_of_le_two`, `finrank_inf_eq` |
| 6. 和の次元と不変性 | `toSubmodule_inf`, `finrank_sup_add_finrank_inf`, `finrank_sup_add_one`, `fourierConj_radialMatOp_mem_inf`, `map_fourierConj_inf` |

**使った PAG の結果**
- Part 15 の `conv`・`convL`（PAG15）
- Part 201 の `dind`・`dind_mul`・`geps`（PAG205）、Part 203 の `gcd_natCast_self`・`dind_radial`・`dind_self`（PAG207）
- Part 214 の `dil`・`dil_apply`・`dft_dil`・`shellAlg`（PAG218）、Part 228 の `convL_geps_mem`・`mulLeft_dind_mem`（PAG232）
- Part 238 の `radialHom`（PAG242）、Part 239 の `radialBasis`・`radialMatOp`・`radialMatOp_mul`（PAG243）
- Part 240 の `unitAvg`・`shellAvg`・`shellAvg_eq_unitAvg`・`shellAvg_apply`・`commute_shellAvg`・`mul_shellAvg_eq`・`radialMatOp_one_eq`・`oneEAlg`・`oneEAlg_le`・`ramSum`・`natCast_mul_geps_eq_ramSum`（PAG244）
- Part 241 の `ramSum_of_dvd`・`shellDev`・`devSet`・`dvd_of_mem_devSet`・`shellAvg_add_sum_shellDev`・`radialMatOp_add`・`radialMatOp_smul`・`radialMatOp_mem_oneEAlg`・`wholeMap`・`wholeHom`・`range_wholeHom`・`wholeMap_injective`・`finrank_oneEAlg_self`（PAG245）
- Part 242 の `fourierConj`・`fourierConj_mulLeft_dind`・`dualOneEAlg`・`map_fourierConj_shellAlg`・`map_fourierConj_oneEAlg`・`finrank_dualOneEAlg`（PAG246）
- Part 243 の `ramSum_eq_totient_iff`・`radialMatOp_apply_eq_zero`・`shellDev_apply_of_shellAvg_eq_zero`・`exists_apply_of_mem_oneEAlg`・`sum_mul_single`・`conv_single_apply`・`three_le_div`（PAG247）

**Mathlib・Lean から使った主なもの**
- フーリエ変換と共役：`LinearEquiv.conjAlgEquiv_apply`・`LinearEquiv.apply_symm_apply`・`LinearEquiv.symm_apply_apply`・`Fintype.sum_equiv`・`Equiv.inv`
- 部分代数と次元：`Algebra.mem_inf`・`Subalgebra.mem_map`・`AlgHom.mem_range`・`AlgHom.prodMap`・`Algebra.ofId`・`AlgEquiv.ofInjective`・`Subalgebra.equivOfEq`・`Submodule.finrank_sup_add_finrank_inf_eq`・`Submodule.eq_of_le_of_finrank_eq`・`Subalgebra.toSubmodule_injective`・`Module.finrank_prod`・`Module.finrank_matrix`
- 自然数：`Nat.totient_eq_one_iff`・`Nat.one_mem_divisors`・`Nat.dvd_of_mul_dvd_mul_left`・`Nat.div_le_self`・`Finset.filter_eq_empty_iff`

**コンパイル**
- `PAG248` は 1 回目のコンパイル（約 8 秒）でエラー・警告なしで通りました。
- 公理は標準のもの（propext、Classical.choice、Quot.sound）だけです（37 行、どれも 3 つすべて）。
- 内容は試しのファイル T3 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble248.py`）。
- **試しのファイル（置き場所は `/home/claude/leanwork/scratch/t244`）。**
  - W0：import の温めと API の名前の確認（19 秒）。`Subalgebra.mem_inf` はなく、`Algebra.mem_inf` を使いました。
  - W1：API の名前の確認（10 秒）。`Subalgebra.inf_toSubmodule`・`AlgHom.prodMap_apply` はありませんでした。部分空間の共通部分は補題 `toSubmodule_inf` を自分で書きました。`Module.finrank_matrix` は card m · card n · finrank R M の形でした。
  - T1（§1〜6、29 項目と定義 3 個）：3 回目で通りました（8 秒）。
    - 1 回目のエラー 1：部分型の元 t の性質 `t.2`（↑t ∈ devSet N）に `rw [devSet]` が当たりませんでした。t の型 ↥(devSet N) の中にも devSet N があるためと思われます（未確認）。型を書いた `have h2 : (t : ℕ) ∈ N.divisors.filter … := t.2` にして解決しました。
    - 1 回目のエラー 2：`Prod.ext (congrArg Prod.fst h) h2` で、期待される型 x.1 = y.1 から `congrArg Prod.fst` の引数が x = y と推論され、h の型と合いませんでした。
    - 2 回目：`have h1 : x.1 = y.1 := congrArg Prod.fst h` でも同じエラーでした。型を書かない `have h1 := congrArg Prod.fst h` の後に、型を付けた `have h1' : x.1 = y.1 := h1` を置いて解決しました。
  - T2（双対側の判定 3b と、N ≤ 2 の場合 5m〜5o を足した。33 項目と定義 3 個）：1 回目で通りました（7 秒）。
  - T3（言い換え Φ(M) + c·1 を足した。34 項目と定義 3 個）：1 回目にエラー 1 件で、2 回目で通りました（7 秒）。
    - `rw [neg_smul]` が、目標に見えている `-c • shellAvg N` をパターン `-?r • ?x` として見つけられませんでした。原因は確かめていません。
    - M − c·1 を選び、`radialMatOp_one_eq`・`radialMatOp_smul`・`radialMatOp_add` を逆向きに使って Φ(M) = Φ(M − c·1) + c·P を示す証明に直しました。
- 前回の注意を当てはめた箇所があります。
  - 部分代数に入らない・入ることを、元の満たす性質（殻ごと・周波数の殻ごとのスカラー）と具体的な関数・点で示しました（Part 243 の注意）。
  - 単射な代数準同型からの部分代数への同型は `(AlgEquiv.ofInjective f hf).trans (Subalgebra.equivOfEq _ _ h)` で作りました（Part 241 の注意）。
  - 非線形の項（d²）は `generalize` で変数にしてから `omega` に渡しました（Part 226 の注意）。
  - `if` の書き換えは `ite_eq_left`・`ite_eq_right` で、条件の違う 2 つの if にそれぞれの仮定を渡しました（Part 243 の注意）。
- docstring の番号は、足した順のまま `5f′` が混じっています（見た目だけの不ぞろい）。
- **環境。** Mathlib の追加ビルドはありません。Part 243 の納品（20:41 ごろ）の後、Part 244 の開始時（20:49）にコンテナが再起動していました（起動時刻 20:48:58 ごろ）。ファイルと .olean は残っていました。最初の import は 19 秒で、Part 243 の開始時（220 秒）より短く済みました。

## 4. 残る問い

1. **（次の候補）B1 + B2 = A_N となる N。** 観察 (7) の「⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ = A_N ⇔ N ∈ {1, 8} ∪ {p, p²}」を Lean にすることです。
   - dim(B1 + B2) は今回の `finrank_sup_add_one`、dim A_N は Part 226 の式で、Part 242 の `prod_eq_iff` と同じ型の算術の比較になります。
   - 2 つの式から手で計算すると、素冪では差 F(p^k) − dim(B1 + B2) が (k − 1)(k − 2)/2（p 奇数）、(k − 2)(k − 3)/2（p = 2、k ≥ 2）になる見込みです。p 奇数では k ≤ 2、p = 2 では k = 2, 3 で 0 です（N = 2 は S′ = ∅ の別扱いで、B1 = A_2）。
2. **生成される代数。** B1 と B2 の和が部分空間として A_N にならない N で、B1 ∪ B2 が生成する代数（A_N そのもの）と和の差を、Part 225 の成分 n_p の言葉で書くことです。
3. **次元の差の閉じた形。** 素因数 2 つ以上のときの dim A_N − dim ⟨D_u, E_N⟩ を、単数群の指標の言葉で書くことです。
4. **ほかの殻の組み合わせ。** ⟨D_u, E_s⟩（Part 240）の空間全体の構造と次元を、s ≠ N でも求めることです。
5. **引き継ぎメモのほかの候補。** $C_N = \bigotimes_pC_{p^{v_p}}$ の PiTensorProduct の形、dilComm$_{q^k}$、$A_N$ のウェダーバーン成分の分配の形、中心そのものの finrank、P・Q_s の自己共役、ほか。
