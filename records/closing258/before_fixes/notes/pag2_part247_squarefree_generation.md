# アデール射影幾何 2.0 — Part 247：平方因子なしの N では ⟨D_u, E_1⟩ = A_N（B_s = A_N の分類を 2 種類の組を除いて完了）

2026-11-06。引き継ぎメモの次の候補「平方因子なしの N で ⟨D_u, E_N, E_1⟩ = A_N（十分性）」を Lean で証明しました。途中で、Part 246 の恒等式 (I) より扱いやすい恒等式 (II) が見つかりました。(II) を使うと十分性は E_N なしでも成り立ちます。逆向きの障害も 2 つ新しく示し、Part 246 で数値だけだった分類を、2 種類の組を除いて定理にしました。

- **新しい恒等式 (II)（Lean）。** 素数 q ∥ N、t ∣ N/q のとき、次が成り立ちます（`convL_geps_prime_mul`）。
  - **E_{qt} = (q²/(q − 1))·(1 − E_t)·G_q·E_t·G_q·(1 − E_t)**。G_q = Σ_{v ∣ N/q} D_{qv} は、q の倍数の指示関数を掛ける作用素です。
  - q = 2 では逆向きの式 E_t = 4·(1 − E_{2t})G_2E_{2t}G_2(1 − E_{2t}) も成り立ちます（`convL_geps_of_two_mul`）。
  - 証明では、中国剰余定理の共役（Part 228）で作用素を「法 q の部分 ⊗ 法 N/q の部分」に分けます。そうすると、法 q だけの式 (1 − E_1)D_qE_1D_q(1 − E_1) = ((q − 1)/q²)E_q に帰着します。
  - Part 246 の (I) には、より高い殻の和 T_p が入っていました。(II) には E_t と G_q しか入らないので、そのまま帰納法に使えます。
- **十分性（Lean）。** N が平方因子なしなら **⟨D_u, E_1⟩ = A_N** です。E_N がなくても成り立ちます（`oneEAlg_one_eq_shellAlg`）。
  - N が偶数なら ⟨D_u, E_2⟩ = A_N も成り立ちます（`oneEAlg_two_eq_shellAlg`）。
  - Part 246 と合わせると、平方因子なしの N と s ∈ S′ について B_s = A_N ⇔ s ∈ {1, 2} です（`addEAlg_eq_shellAlg_iff_of_squarefree`）。
- **逆向き（Lean）。**
  - **⟨D_u, E_1⟩ = A_N ⇔ N は平方因子なし** です（`oneEAlg_one_eq_shellAlg_iff`）。
    - 一般に、N/s が平方因子をもてば E_N ∉ ⟨D_u, E_s⟩ です。⟨D_u, E_s⟩ は指標 ψ(y) = e(y/p)（p² ∣ N/s）の掛け算と可換で、E_N は可換でないからです。
  - **単数の殻の上の新しい証拠**（`convL_geps_primePow_not_mem_addEAlg`）。f = Σ_{c < p^m}(δ_{1+cM} − δ_{−(1+cM)})（M = N/p^m）とおきます。
    - p^{m+1} ∣ N、p^m ∤ s、N ∤ 2p^{m+1}（または N = 2p^{m+1} で p ≠ 2）なら、E_{p^m} ∉ B_s です。
  - **B_1 = A_N ⇔ N は平方因子なし ∨ N = 8 ∨ N = p²**（p は素数）です（`addEAlg_one_eq_shellAlg_iff`）。
  - **主定理**（`addEAlg_eq_shellAlg_iff`）：s ∈ S′ で、(N, s) が (p³, p)（p は奇素数）と (16, 2) のどちらでもなければ、**B_s = A_N ⇔ |S′| ≤ 2 ∨（N は平方因子なし ∧ s ∈ {1, 2}）** です。
    - Part 246 で数値だけだった形が、この 2 種類の組を除いて定理になりました。
  - フーリエ双対 ⟨E_u, D_s⟩・⟨E_u, D_N, D_1⟩ についても、同じ条件を示しました。
- **限界（正直な注記）。**
  - 除いた (p³, p)（p は奇素数）と (16, 2) は数値だけです。N = 27, 125, 343, 16 で dim B_s = F − 1 でした（B_s ≠ A_N）。
  - 今回の証拠では届きません。m = 2 の証拠には、p² の倍数の中に殻が 2 つ必要です。ところが N = p³ や N = 16 では、2k₂ ≢ 0 となる k₂ が見つかりません（§0 の 6）。
- **やり直し。**
  - 試しのファイルは T1 が 4 回目、T2・T3 が 2 回目、T4 が 1 回目で通りました。
  - PAG251 は 1 回目のコンパイルで通りました。その後、docstring の書き損じを直して、もう 1 回コンパイルしました（内容は同じ）。
  - 数値照合は 1 回の実行ですべて合格しました。
  - 今回はコンパイルの前に `if_pos`・`if_neg`・`push_neg`・`dif_pos` を grep で確かめ、0 件でした。
- **環境。** Mathlib の追加ビルドはありません。Part 247 の開始時（17:56）にコンテナが再起動していました。import の温めは 13 秒でした。

成果物は次のとおりです。
- `PAG251.lean`：60 項目。sorry 0・警告 0 です。
  - 定義 3 個（`charP`・`unitWit`・`dualOneEAlgOf`）は項目に数えません。
  - 出力は `PAG251.out`（#print axioms 63 行）。
- 照合用の `step270.py`：ログは `step270.log` です。

xlsx の集計は 3248 項目になりました（手順 267）。

## 0. 結論

**記号**（Part 240〜246 と同じ）
- A_N = `shellAlg N`、⟨D_u, E_s⟩ = `oneEAlg N s`、B_s = ⟨D_u, E_N, E_s⟩ = `addEAlg N s`。
- S′ = {t ∣ N : φ(N/t) ≠ 1} = `devSet N`、P = 殻の平均、U_s^⊥ = {f : P f = 0、すべての u で E_s(1_{D_u}f) = 0}（Part 246）。
- F(N) = dim A_N（Part 226）。G_q = Σ_{v ∣ N/q} D_{qv}。
- 中国剰余定理の共役 C：End(ℂ^{ℤ/qM}) ≅ End(ℂ^{ℤ/q × ℤ/M})。L(S) は第 1 座標への作用、R(T) は第 2 座標への作用です（Part 228 の `crtConj`・`leftOp`・`rightOp`）。

| 定理 | 主張 |
|---|---|
| `geps_self_apply`, `convL_geps_self_apply`, `dind_self_apply`, `mulLeft_dind_mul_self`, `convL_geps_mul_self`, `convL_geps_self_mul_mulLeft_dind_self` | ε_N ≡ 1/N、(E_N f)(x) = Σf/N、1_{D_N} = δ_0、D_s² = D_s、E_s² = E_s、E_ND_NE_N = (1/N)E_N |
| `convL_geps_one_add_self_of_prime`, **`level_identity`**, **`two_level_identity`** | 法 q（素数）で E_1 + E_q = 1、(1 − E_1)D_qE_1D_q(1 − E_1) = ((q − 1)/q²)E_q。法 2 で 4(1 − E_2)D_2E_2D_2(1 − E_2) = 1 − E_2 |
| `leftOp_mul'` ほか 7 個、**`sandwich`**, `crtConj_sum_dind` | L・R は準同型。はさみうちの式 (1 − X)L(P)XL(P)(1 − X) = L((1 − c)PcP(1 − c))R(z)（X = L(c)R(z)、z² = z）。C(G_q) = L(D_q) |
| `convL_geps_prime_mul_aux`, **`convL_geps_prime_mul`**, `convL_geps_of_two_mul_aux`, **`convL_geps_of_two_mul`** | 恒等式 (II) と、q = 2 の逆向きの式 |
| **`convL_geps_mem_of_squarefree`**, **`oneEAlg_one_eq_shellAlg`**, `oneEAlg_two_eq_shellAlg`, `addEAlg_one_eq_shellAlg`, `addEAlg_two_eq_shellAlg`, **`addEAlg_eq_shellAlg_iff_of_squarefree`** | 平方因子なし：D_u と E_1 を含む部分代数はすべての E_t を含む。⟨D_u, E_1⟩ = A_N、偶数なら ⟨D_u, E_2⟩ = A_N。B_s = A_N ⇔ s ∈ {1, 2} |
| `mul_div_eq_zero_of_dvd`, `geps_eq_zero_of_not_dvd_val`, `convL_geps_commute_charP`, `oneEAlg_le_centralizer`, `convL_geps_self_not_commute_charP`, **`convL_geps_self_not_mem_oneEAlg`**, `oneEAlg_ne_shellAlg`, **`oneEAlg_one_eq_shellAlg_iff`** | p² ∣ N/s なら ε_s は p の倍数の上だけ、⟨D_u, E_s⟩ は ψ の掛け算と可換、E_N は可換でない、E_N ∉ ⟨D_u, E_s⟩。⟨D_u, E_1⟩ = A_N ⇔ 平方因子なし |
| `shellAvg_unitWit` ほか 11 個, **`convL_geps_primePow_not_mem_addEAlg`**, `convL_geps_prime_not_mem_addEAlg`, `addEAlg_ne_shellAlg_of_sq` | 単数の殻の上の証拠 f の性質と、E_{p^m} ∉ B_s。m = 1 での B_s ≠ A_N |
| `convL_geps_one_not_mem_addEAlg_primePow` | N = p^k、s = p^j（2 ≤ j < k）なら E_1 ∉ B_s |
| `card_devSet_sq_le`, `card_devSet_eight_le`, **`addEAlg_one_eq_shellAlg_iff`**, **`addEAlg_eq_shellAlg_iff`** | \|S′(p²)\|, \|S′(8)\| ≤ 2。B_1 の分類と、主定理（(p³, p)・(16, 2) を除く） |
| `map_fourierConj_oneEAlg_of`, `dualOneEAlgOf_eq_shellAlg_iff`, `dualOneEAlgOf_one_eq_shellAlg_iff`, `dualAddEAlg_one_eq_shellAlg_iff` | フーリエ双対 ⟨E_u, D_s⟩ と ⟨E_u, D_N, D_1⟩ |

**証明の筋**
1. **法 q の式。** 法 q では E_q = (1/q)·（定数への射影）、D_q = δ_0 です。E_qD_qE_q = (1/q)E_q、D_q² = D_q、E_1 = 1 − E_q から、
   - (1 − E_1)D_qE_1D_q(1 − E_1) = E_qD_q(1 − E_q)D_qE_q = E_qD_qE_q − E_qD_qE_qD_qE_q = (1/q − 1/q²)E_q です。
   - 法 2 の式は ℤ/2 の 2 点で値を比べました（E_1 の階数が 1 である法 2 だけの式です）。
2. **中国剰余定理の共役。** N = qM（gcd(q, M) = 1）で、C(E_{ab}) = L(E_a)R(E_b)、C(D_{ab}) = L(D_a)R(D_b) です（Part 228）。
   - Σ_{v ∣ M} D_v = 1 から C(G_q) = L(D_q) です。
   - z = E_t（法 M）は z² = z を満たし、L(·) は R(z) と可換です。そこで (1 − L(E_1)R(z))L(D_q)·L(E_1)R(z)·L(D_q)(1 − L(E_1)R(z)) = L((1 − E_1)D_qE_1D_q(1 − E_1))R(z) となり、1 から ((q − 1)/q²)·C(E_{qt}) です。
   - q = 2 の逆向きの式は、E_1 と E_2 の役割を入れ替えて法 2 の式を使います。
3. **十分性。** t ∣ N（N は平方因子なし）を、最小素因数 q で t = q·t′ と分けます。q ∤ t′ で t′ ∣ N/q なので、(II) から E_{t′} を含む代数は E_t を含みます。t についての帰納法で、E_1 からすべての E_t が出ます。
   - 偶数 N の E_2 からは、逆向きの式（t = 1）で E_1 が出ます。
4. **指標による障害。** p² ∣ N/s とします。
   - c_{N/s}(y) ≠ 0 には (N/s)/gcd(N/s, y) が平方因子なしであることが必要です（Part 241）。p ∤ y なら p² が商に残るので、ε_s は p の倍数の上にしかありません。
   - そのため E_s と D_u は ψ(y) = e(y·(N/p)/N) の掛け算と可換で、⟨D_u, E_s⟩ 全体も可換です。
   - E_N(ψ·δ_0) = E_Nδ_0 ≡ 1/N ですが、ψ·E_Nδ_0 = ψ/N は定数でありません（ψ(1) ≠ 1）。よって E_N ∉ ⟨D_u, E_s⟩ です。
5. **単数の殻の上の証拠。** M = N/p^m、f = Σ_{c < p^m}(δ_{1+cM} − δ_{−(1+cM)}) とおきます。
   - p^{m+1} ∣ N なので、N のどの素因数も M を割り、1 + cM は単数です。f は単数の殻に載り、各項が δ_a − δ_{−a} なので P f = 0 です（Part 244）。
   - 𝓕f(k) = Σ_c (e(−(1 + cM)k) − e((1 + cM)k)) です。Mk ≢ 0 なら e(Mk) は 1 でない p^m 乗根で、等比数列の和が 0 になり 𝓕f(k) = 0 です。Mk ≡ 0（p^m ∣ k）なら 𝓕f(k) = p^m(e(−k) − e(k)) です。
   - p^m ∤ s なら、p^m ∣ k の k は D_s に入らないので E_s f = 0、つまり f ∈ U_s^⊥ です。
   - E_{p^m} ∈ B_s なら、Part 246 の判定法で E_{p^m}f = c·f です。𝓕 で写すと 1_{D_{p^m}}𝓕f = c·𝓕f です。
     - k = p^m では 𝓕f ≠ 0（2p^m ≢ 0）なので c = 1 です。
     - k₂ = p^{m+1}（N ∤ 2p^{m+1}）または k₂ = 2p^m（N = 2p^{m+1}、p 奇数）は D_{p^m} の外で 𝓕f(k₂) ≠ 0 なので、矛盾します。
6. **2 種類の組が残る理由。** (p³, p)（p 奇数）では、p ∣ s なので m = 1 は使えず、m ≥ 2 が必要です。
   - m = 2 では k₂ は p² の倍数で D_{p²} の外、つまり k₂ = 0 しかなく、𝓕f(0) = 0 です。
   - (16, 2) でも m = 2 で k₂ = 8 となり、2k₂ ≡ 0 です。素冪の j ≥ 2 は Part 246 の 2 点の証拠で済みますが、j = 1 は届きません。
7. **主定理の場合分け。**
   - 平方因子なしは 3 です。
   - 平方因子あり（p² ∣ N）で p ∤ s なら 5（m = 1）です。N ≠ p²、N ≠ 8 は |S′| ≥ 3 から出ます。
   - p ∣ s で、N に p 以外の素因数があれば Part 246 の主定理（r = p）です。N = p^k なら、s = p^j で j ≥ 2 は 6、j = 1 は 5（m = 2、除いた組のほか）です。

**例**（数値）
- ⟨D_u, E_1⟩ の次元：N = 30 で 100 = F、N = 12 で 27 < 50、N = 36 で 35 < 120、N = 60 で 129 < 250 です。
  - ⟨D_u, E_2⟩：N = 12 で 47、N = 60 で 229（どちらも < F）です。
- 恒等式 (II) の例：N = 15、q = 3、t = 5 で E_15 = (9/2)(1 − E_5)G_3E_5G_3(1 − E_5) です。G_3 は 3 の倍数（0, 3, 6, 9, 12）の指示関数です。
- 語の長さ（Part 246 の (8)）：N = 30 では E_2 などが長さ 3、E_6・E_10 が長さ 5 で初めて出ました。(II) による構成（E_1 → E_2 → E_6 のように素因数を 1 つずつ増やす）はこれより長い語になり、最短の表し方ではありません。合成数の t ほど長い語が要る点だけが合っています。
- 除いた組：dim B_3 = 21（N = 27, F = 22）、dim B_5 = 21（N = 125）、dim B_7 = 21（N = 343）、dim B_2 = 30（N = 16, F = 31）です。
  - どれも E_1 と E_{p²}（N = 16 では E_4）が B_s に入りません（探索、E_1 + E_{p²} ∈ B_s）。

**読み取れること**
- 平方因子なしの N では、殻の掛け算 D_u と、単数の周波数への射影 E_1 だけで A_N 全体が出ます。E_1 は「どの素因数でも割れない周波数」を選ぶ作用素です。q の倍数の位置への掛け算 G_q ではさむと、q 成分だけを「割れる側」に切り替えた E_q が出ます。
- 平方因子があると、ε_1 は p の倍数の上にしかなく、⟨D_u, E_1⟩ は ℤ/p の剰余類ごとに分かれます。それをつなぐのが E_N ですが、E_N を足しても、単数の殻の上の証拠 f が残ります（N = p², 8 を除く）。
- B_s = A_N の分類は、残り 2 種類の組を除いて「|S′| ≤ 2 か、平方因子なしで s ∈ {1, 2}」です。

## 1. 検証表

| 主張 | 判定 |
|---|---|
| 法 q・法 2 の式、ε_N ≡ 1/N、E_ND_NE_N = (1/N)E_N | **正しい（`level_identity`、`two_level_identity`、`convL_geps_self_mul_mulLeft_dind_self`）**。数値でも 442/442 |
| 恒等式 (II) と q = 2 の逆向きの式 | **正しい（`convL_geps_prime_mul`、`convL_geps_of_two_mul`）**。数値でも 204/204（N ≤ 60）、q² ∣ N では成り立たない（24 組） |
| 平方因子なしの N で ⟨D_u, E_1⟩ = A_N、偶数なら ⟨D_u, E_2⟩ = A_N | **正しい（`oneEAlg_one_eq_shellAlg`、`oneEAlg_two_eq_shellAlg`）**。数値でも（N ≤ 60） |
| 平方因子なしの N、s ∈ S′ で B_s = A_N ⇔ s ∈ {1, 2} | **正しい（`addEAlg_eq_shellAlg_iff_of_squarefree`）**（Part 246 では ⇒ だけ） |
| N/s が平方因子をもてば E_N ∉ ⟨D_u, E_s⟩、⟨D_u, E_1⟩ = A_N ⇔ 平方因子なし | **正しい（`convL_geps_self_not_mem_oneEAlg`、`oneEAlg_one_eq_shellAlg_iff`）**。数値でも 155/155、72/72 |
| p^{m+1} ∣ N、p^m ∤ s ほかで E_{p^m} ∉ B_s | **正しい（`convL_geps_primePow_not_mem_addEAlg`）**。数値でも証拠の組 425/425（N ≤ 200） |
| N = p^k、s = p^j（2 ≤ j < k）で E_1 ∉ B_s | **正しい（`convL_geps_one_not_mem_addEAlg_primePow`）** |
| B_1 = A_N ⇔ 平方因子なし ∨ N = 8 ∨ N = p² | **正しい（`addEAlg_one_eq_shellAlg_iff`）**。数値でも（N ≤ 60） |
| 主定理（(p³, p)・(16, 2) を除く） | **正しい（`addEAlg_eq_shellAlg_iff`）**。数値でも 229/229（N ≤ 60）（Part 246 では数値だけ） |
| (p³, p)（p 奇素数）・(16, 2) で B_s ≠ A_N | **数値だけ**（N = 27, 125, 343, 16 で dim B_s = F − 1） |
| ⟨E_u, D_1⟩ = A_N ⇔ 平方因子なし、⟨E_u, D_N, D_1⟩ も B_1 と同じ条件 | **正しい（`dualOneEAlgOf_one_eq_shellAlg_iff`、`dualAddEAlg_one_eq_shellAlg_iff`）**。数値でも 30/30（N ≤ 30） |
| 除いた組で B_s に入らないのは E_1 と E_{p²}（N = 16 では E_4） | **数値だけ（探索）**（N = 27, 125, 16） |

## 2. 数値照合（step270）

| 項目 | 内容 | 結果 |
|---|---|---|
| (1) | 恒等式 (II)（素数 q ∥ N、t ∣ N/q）と 2 ∥ N での逆向きの式（N ≤ 60）。対照：q² ∣ N の 24 組では t = 1 の式が成り立たない（差の最小 0.080） | 204/204 |
| (2) | 法 n の式 E_nD_nE_n = (1/n)E_n・D_nE_nD_n = (1/n)D_n・D_n² = D_n・E_s² = E_s（n ≤ 60）と法 2 の式 | 442/442 |
| (3) | 生成元から：dim ⟨D_u, E_1⟩ = F ⇔ 平方因子なし、偶数で平方因子なしなら dim ⟨D_u, E_2⟩ = F（N ≤ 60） | 72/72 |
| (4) | N/s が平方因子をもつ 62 組：D_u・E_s は ψ の掛け算と可換、E_N は可換でない、dim ⟨D_u, E_s⟩ < F（次元は N ≤ 36） | 155/155 |
| (5) | 単数の殻の上の証拠（N ≤ 200）：仮定を満たす組 (N, s, p, m) すべてで P f = 0、f は単数の殻に載る、E_s f = 0、𝓕f(p^m) ≠ 0、𝓕f(k₂) ≠ 0、gcd(N, k₂) ≠ p^m、E_{p^m}f ∉ ℂf | 425/425 |
| (6) | 分類と step269 の次元（N ≤ 60）：B_1 の分類と主定理の形 | 229/229 |
| (7) | 除いた組の次元：(27, 3)・(125, 5)・(343, 7) で 21 < 22、(16, 2) で 30 < 31 | 4/4 |
| (8) | フーリエ双対 dim ⟨E_u, D_1⟩ = dim ⟨D_u, E_1⟩（N ≤ 30） | 30/30 |

- 実行は 1 回で、約 24 秒でした。項目ごとの結果は `step270_cache.json` に保存しました。(6) は step269 の保存済みの次元を使いました。
- **照合の前の探索**（成果物ではない。置き場所は `/home/claude/explore`）。
  - `ex270.py`：恒等式 (II) と ⟨D_u, E_1⟩・⟨D_u, E_2⟩ の次元（N ≤ 48）。ここで (II) と「⟨D_u, E_1⟩ = A_N ⇔ 平方因子なし」を見つけました。
  - `ex270b.py`：平方因子ありの N の U_1^⊥。N = 12 では δ_1 − δ_5 + δ_7 − δ_11（N/2 の平行移動で不変）で、これが §0 の 5 の証拠の形の手がかりになりました。
  - `ex270c.py`：除いた組の U_s^⊥ と、B_s に入らない E_t。
- **限界。** 生成元からの次元は N ≤ 60（(4) は N ≤ 36、(7) は 4 組）です。(6) は分類の式と次元の照合で、作用素から独立に分類を計算したものではありません。

## 3. Lean（`PAG251.lean`、namespace `PAG.Part251`、PAG250 を import）

| 区分 | 項目 |
|---|---|
| 1. 法 N・法 q・法 2 の式 | `geps_self_apply`, `convL_geps_self_apply`, `dind_self_apply`, `mulLeft_dind_mul_self`, `convL_geps_mul_self`, `convL_geps_self_mul_mulLeft_dind_self`, `convL_geps_one_add_self_of_prime`, `level_identity`, `two_level_identity` |
| 2. 中国剰余定理による分解と恒等式 | `leftOp_mul'`, `leftOp_sub'`, `leftOp_one'`, `leftOp_smul'`, `rightOp_mul'`, `rightOp_one'`, `rightOp_sum'`, `sandwich`, `crtConj_sum_dind`, `convL_geps_prime_mul_aux`, `convL_geps_prime_mul`, `convL_geps_of_two_mul_aux`, `convL_geps_of_two_mul` |
| 3. 平方因子なしの十分性 | `convL_geps_mem_of_squarefree`, `oneEAlg_one_eq_shellAlg`, `oneEAlg_two_eq_shellAlg`, `addEAlg_one_eq_shellAlg`, `addEAlg_two_eq_shellAlg`, `addEAlg_eq_shellAlg_iff_of_squarefree` |
| 4. 指標による障害 | def `charP`, `mul_div_eq_zero_of_dvd`, `geps_eq_zero_of_not_dvd_val`, `convL_geps_commute_charP`, `oneEAlg_le_centralizer`, `convL_geps_self_not_commute_charP`, `convL_geps_self_not_mem_oneEAlg`, `oneEAlg_ne_shellAlg`, `oneEAlg_one_eq_shellAlg_iff` |
| 5. 単数の殻の上の証拠 | def `unitWit`, `shellAvg_unitWit`, `dind_one_of_isUnit`, `dind_one_mul_pairFn`, `dft_pairFn`, `geom_sum_eq_zero_of_pow`, `prime_dvd_div_of_dvd`, `isUnit_one_add_mul`, `dind_one_mul_unitWit`, `dvd_val_of_mul_eq_zero`, `dft_unitWit_of_mul_eq_zero`, `dft_unitWit_of_mul_ne_zero`, `convL_geps_unitWit`, `convL_geps_primePow_not_mem_addEAlg`, `convL_geps_prime_not_mem_addEAlg`, `addEAlg_ne_shellAlg_of_sq` |
| 6. 素冪 | `convL_geps_one_not_mem_addEAlg_primePow` |
| 7. 分類 | `card_devSet_sq_le`, `card_devSet_eight_le`, `addEAlg_one_eq_shellAlg_iff`, `addEAlg_eq_shellAlg_iff` |
| 8. フーリエ双対 | def `dualOneEAlgOf`, `map_fourierConj_oneEAlg_of`, `dualOneEAlgOf_eq_shellAlg_iff`, `dualOneEAlgOf_one_eq_shellAlg_iff`, `dualAddEAlg_one_eq_shellAlg_iff` |

**使った PAG の結果**
- Part 201 の `dind`・`geps`・`dind_mul`・`sum_dind`（PAG205）、Part 203 の `dind_radial`・`dind_self`・`gcd_natCast_self`（PAG207）
- Part 214 の `shellAlg`（PAG218）、Part 228 の `crtConj`・`leftOp`・`rightOp`・`leftHom`・`rightHom`・`leftOp_commute_rightOp`・`crtConj_geps`・`crtConj_dind`・`sum_mulLeft_dind`・`shellAlg_eq_adjoin`・`convL_geps_mem`（PAG232）
- Part 239 の `dft_conv_geps`（PAG243）、Part 240 の `natCast_mul_geps_eq_ramSum`・`oneEAlg`・`oneEAlg_le`（PAG244）、Part 241 の `ramSum_of_dvd`・`ramSum_ne_zero_iff_squarefree`・`devSet`（PAG245）
- Part 242 の `fourierConj`・`fourierConj_convL_geps`・`fourierConj_mulLeft_dind`・`map_fourierConj_shellAlg`・`card_divisors_primePow`（PAG246）、Part 244 の `pairFn`・`shellAvg_pairFn`・`one_mem_devSet`（PAG248）
- Part 246 の `addEAlg` まわり（`oneEAlg_le_addEAlg'`・`addEAlg_le`・`convL_geps_of_not_dvd`・`sum_convL_geps`・`exists_apply_eq_smul_of_mem_addEAlg`・`dft_single`・`convL_geps_one_not_mem_addEAlg_of_witness`・`addEAlg_ne_shellAlg`・`addEAlg_ne_shellAlg_of_squarefree`・`addEAlg_eq_shellAlg_of_card_le_two`・`card_devSet_le_two_iff`・`dualAddEAlg`・`dualAddEAlg_eq_shellAlg_iff`）（PAG250）

**Mathlib・Lean から使った主なもの**
- 部分代数：`Algebra.adjoin_le`・`Subalgebra.centralizer`・`Subalgebra.mem_centralizer_iff`・`Subalgebra.sum_mem`・`Subalgebra.smul_mem`・`Subalgebra.map_injective`・`AlgHom.map_adjoin`
- 指標と和：`ZMod.injective_stdAddChar`・`AddChar.map_add_eq_mul`・`AddChar.map_nsmul_eq_pow`・`AddChar.map_zero_eq_one`・`geom_sum_mul`
- 自然数：`Nat.strong_induction_on`・`Nat.minFac_prime`・`Nat.squarefree_iff_prime_squarefree`・`Nat.coprime_mul_iff_left`・`Nat.Coprime.dvd_of_dvd_mul_left`・`Nat.dvd_prime_pow`・`Nat.pow_dvd_pow_iff_le_right`・`Nat.eq_prime_pow_of_unique_prime_dvd`・`Nat.pow_div`・`Nat.coprime_of_dvd`・`ZMod.isUnit_iff_coprime`

**コンパイル**
- `PAG251` は 1 回目のコンパイル（約 7 秒）でエラー・警告なしで通りました。
  - その後、2j の docstring で恒等式を「(1 − E_t)G(1 − ...)」と書き損じていたのに気づいて直し、もう 1 回コンパイルしました（約 6 秒、内容は同じ）。
- 公理は 63 行すべて標準のもの（propext、Classical.choice、Quot.sound）です。内容は試しのファイル T4 と同じで、冒頭のコメントと #print axioms の追加だけをしました（`/home/claude/out/assemble251.py`）。
- **試しのファイル（置き場所は `/home/claude/leanwork/scratch/t247`）。**
  - W0：import の温め（13 秒）。誤りはありませんでした。
  - W1・W2：API の確認。名前の誤りが 2 件ありました（`Nat.not_squarefree_mul_self` と `Nat.Coprime.mul` はこの Mathlib にない）。`Nat.squarefree_iff_prime_squarefree` と `Nat.coprime_mul_iff_left` を使いました。
  - コンパイルの前に `grep -n "if_pos\|if_neg\|push_neg\|dif_pos" T*.lean` で確かめ、0 件でした（メモの注意を守れた）。
  - T1（§1〜2、23 項目）：4 回目で通りました（3〜4 秒）。PAG232 の `sum_mulLeft_dind` と同じ補題を書いていたので、T2 で消して既存のものを使いました。
    - 1 回目のエラー 3 件：
      - `noncomm_ring` が Module.End の中の `-1 •` の形を閉じられませんでした。`rw [mul_sub, mul_one, sub_mul, sub_mul]` で展開しました。
      - `rw [← sub_smul]` が、スカラー倍の型の経路の違いで当たりませんでした（未確認）。2 回目に順向きの `sub_smul` も当たらなかったので、作用素に f を作用させ、点ごとに `field_simp` で比べる形にしました。
      - 法 2 の式で、`fin_cases x` の後の `if 0 = 0` が simp で消えませんでした（Fin の数字が `0 : ZMod 2` と字面で違うためと思われる、未確認）。`by_cases hx : x = 0` と `decide`（x ≠ 0 → x = 1）と `simp only [..., ↓reduceIte]` にしました。
    - 2 回目のエラー 3 件：field_simp の後の `ring` が「No goals」、順向きの `sub_smul`、`if True then 1 else 0` が残りました（simp が先に `0 = 0` を True にしたので、用意した補題 e0 が当たらなかった）。`↓reduceIte` で消えました。
    - 3 回目のエラー 1 件：また field_simp の後の `ring` が「No goals」でした。
  - T2（§3〜5 を足した 48 項目と定義 2 個）：2 回目で通りました（5 秒）。
    - 1 回目は、def `charP` に `[NeZero N]` がなく `stdAddChar` が使えず、連鎖してエラーが 3 件出ました。もう 1 件は `Nat.Coprime.mul` がないことでした。
  - T3（§5〜7 を足した 56 項目と定義 2 個）：2 回目で通りました（6 秒）。
    - 1 回目は `rwa [pow_one] at h2 ⊢` が、h2 に `p ^ 1` がなくて失敗しました。この書き方は非推奨の警告も出ます。`(by rw [pow_one]; exact h2 : p ^ 2 ∣ p ^ 1)` に直しました。
  - T4（§8 を足した 60 項目と定義 3 個）：1 回目で通りました（9 秒）。
- **前回までの注意を当てはめた箇所。**
  - 法が式で決まる主張は、変数 n と仮定 `hn : n = q * M` の補題にして中で `subst` しました（Part 242 の注意）。NeZero q・NeZero M は `have` で作りました。
  - A_N の生成元から `rintro` した後の β 簡約前のゴールには、`rw` ではなく `exact` を使いました（Part 246 の注意）。
  - `Subalgebra.map_injective` には `(f := …)` を明示し、↔ の片側だけの書き換えには `conv_lhs` を使いました（Part 246 の注意）。
- **環境。** Mathlib の追加ビルドはありません。Part 246 の納品（17:41 ごろ）の後、Part 247 の開始時にコンテナが再起動していました（起動時刻 17:56:02）。ファイルと .olean は残っていて、最初の import は 13 秒でした。

## 4. 残る問い

1. **（次の候補）除いた 2 種類の組。** (p³, p)（p は奇素数）と (16, 2) で B_s ≠ A_N を示すことです。
   - 数値では dim B_s = F − 1 で、E_1 と E_{p²}（N = 16 では E_4）が入りません（E_1 + E_{p²} は入る）。
   - U_s^⊥ の元の 𝓕 は双対殻 D_1 と D_{p²} に載っていて、空間では殻 1, p, p² にまたがっています（N = 27, 125, 16）。
   - 1 つの殻に載る証拠を作るには、単数の殻の上で 𝓕 が D_1 と D_{p²} の両方に載り、D_p で消える関数が要ります。例えば 1_{D_1}·(e(b₁x/N) − e(b₂x/N) − 1/(p − 1))（b₁ は単数、v_p(b₂) = 2）の形です（手計算、未検証）。
2. **⟨D_u, E_s⟩ = A_N の分類。** 今回は「N/s が平方因子をもてば ≠」と「平方因子なしで s ∈ {1, 2} なら =」を示しました。
   - それ以外の例：N = 12、s = 2（N/s = 6 は平方因子なし）で 47 < 50、N = 4、s = 2 で A_4 です。全体の分類が問えます。
3. **次元の閉じた形。** 平方因子ありの N での dim ⟨D_u, E_1⟩（N = 12 で 27、N = 36 で 35、N = 60 で 129）と dim B_s を、Part 225 の成分の言葉で書くことです。
4. **A_N を生成するのに要る E の個数。** 平方因子ありで |S′| ≥ 3 の N では、E を 1 つ足しても足りません。何個で足りるかを問えます。
5. **引き継ぎメモのほかの候補。** B1 + B2 の補空間、C_N の PiTensorProduct の形、A_N のウェダーバーン成分の分配、ほか。
