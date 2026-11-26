# 候補 1（生成の分類、項目 66〜69）の照合の仕上げ

2026-11-12 夕方。著者の申し送り（15:43「候補 1（生成の分類の項目 66〜69）と候補 2（定理 2.6 の組み合わせ）の照合の仕上げ」）による。Part の番号は使わず、Lean と xlsx は変えていません。候補 2 は `pag2_thm26_A1_collation.md` の §11・§12 です。

## 結論

- **主張（標準の言葉）。** 記号は次のとおりです。
  - X = ℤ/N、関係 R_t = {(x, y) : gcd(x − y, N) = t}（t ∣ N）。これは巡回群 ℤ/N 上の Aut(ℤ/N) の軌道 Schur 環（円分 Schur 環）のスキームです。
  - T = T(0) は基点 0 の Terwilliger 代数（＝殻代数 A_N）です。
  - M* = 双対 Bose–Mesner 代数（D_t = E*_t）、M = Bose–Mesner 代数（E_s は原始べき等元、E_N = J/N）、E*_N = D_N（δ_0 への射影）です。
  - 主張は次の 3 つです。

  | 項目 | 主張 | Lean |
  |---|---|---|
  | 66 | ⟨M*, J⟩ + ⟨M, E*_N⟩ = T（部分空間の和）⇔ N ∈ {1, 8} ∪ {p, p²} | `sumSub_eq_shellAlg_iff`（PAG249） |
  | 67〜69 | s ∈ S′ = {s ∣ N : φ(N/s) ≠ 1} について、⟨M*, J, E_s⟩ = T ⇔ \|S′\| ≤ 2 ∨（N が平方因子なし ∧ s ∈ {1, 2}） | `addEAlg_eq_shellAlg_iff_all`（PAG252） |
  | 68 | ⟨M*, J, E_1⟩ = T ⇔ N が平方因子なし ∨ N = 8 ∨ N = p² | `addEAlg_one_eq_shellAlg_iff`（PAG251） |

  どれも `#print axioms` は [propext, Classical.choice, Quot.sound] です。
- **文献。**
  - 構造（ほぼ可換であること、輪積、次元、1 次元の加群の番号）は既知です。
  - 照合した範囲には、生成の問いが出てきません。つまり「M* と少数の原始べき等元、または J で T が生成されるか」「2 つの部分代数の和が T か」です。照合した範囲は、本文が Song–Xu 2010、Kim 2011、Bastian–Humphries 2026、要旨が BST 2010、前回の再監査の盲検が Hanaki–Kim–Maekawa のプレプリントです。
  - 文献にある生成の結果は、別の型です。P 多項式かつ Q 多項式のスキームで T = ⟨A, A*⟩、三重正則なスキームで T が三つの積 E*_i A_j E*_k で張られること、主部分代数が F と F* で生成されること、の 3 つです。
- **導出の長さ（私の見立て、確信度：中）。**
  - 項目 66：次元の数え上げです。素冪では 1〜2 行の不等式、合成数では d² の増え方と dim T の積の増え方の比較です。演習の水準です。
  - 項目 67〜69（素冪）：既知の 1 次元加群の番号（Song–Xu の中心べき等元）の上の短い場合分けです。
  - 項目 67〜69（合成数）：既知の構造（テンソル積）の上の追加の計算で、文献の結果から直ちには出ません。**残余はここにあります。**
- **判定（確信度：中）。** 新規候補のまま残ります。ただし範囲は「合成数の N での生成の分類」（項目 66 の合成数の場合と 67〜69）に絞られます。新しい現象ではなく「書かれていない計算」の種類です。著者の新しい規則の「残余が計算の細部だけなら小さいノート」に当たる見込みです。CLAUDE.md §3 の書き換えは著者側で行われます。
- **MathSciNet・zbMATH：未実施。**（後注 2026-11-26 14:25、著者側（Muse）が zbMATH の公開 API で §3 の検索式を実行した結果による。構築側は zbMATH を開けていない。詳細は `pag2_literature_zbmath_20261126.md` §6。zbMATH は済み：2 つの検索（ti:Terwilliger & (cyclic | cyclotomic | "Schur ring") で 2 件、"Terwilliger algebra" & generat* & (cyclic | "Schur ring") で 4 件）の範囲で、生成系の分類は見つからなかった（不存在の証明ではない）。Ishibashi–Ito–Yamada の 3 人目は Yamada, Mieko（Zbl 0944.05101）。未了は MathSciNet。）
  - MathSciNet はこのコンテナからは使えません。
  - zbMATH Open は直接の検索ができません。「zbMATH」を含むウェブ検索でも zbMATH の項目は出てきませんでした。
  - 正式な文献調査は、著者側か専門家への照会でお願いします。

## 1. 文献の照合

| 文献 | 確かめた範囲 | 構造について | 生成について |
|---|---|---|---|
| Bhattacharyya–Song–Tanaka 2010（J. Algebraic Combin. 31） | 要旨（EMIS） | K_n の輪積で、主でない加群はすべて 1 次元 | 要旨には出てこない |
| Song–Xu 2010（arXiv:1008.2228） | 本文（自動の読み取り） | T ≅ M_{d+1}(ℂ) ⊕ M_1(ℂ)^{⊕(d(d+1)/2 − b)}（b は n_i = 2 の個数）、中心べき等元 F_ih（h < i）で 1 次元のイデアルを番号づけ | M* と少数の原始べき等元、J による生成、部分代数の和は扱っていない。T は三つの積で張られる（三重正則） |
| Kim 2011（arXiv:1103.4216） | 本文（自動） | 巡回スキーム C_p の輪積（K_p の輪積とは別の対象）の T の分解 | 扱っていない |
| Hanaki–Kim–Maekawa 2011（J. Algebra 343） | 前回の盲検がプレプリントで確認 | 直積スキームの T はテンソル積 | 前回の盲検の範囲では出てこない |
| Tanaka 2011 | Bastian–Humphries 2026 の引用で確認 | ほぼ可換 ⇔ 1 クラススキームと可換群スキームの輪積 | — |
| Bastian–Humphries 2026（arXiv:2606.19095） | 本文（自動） | Aut の軌道 Schur 環は C_{p^n} でほぼ可換。次元は p = 2 で (3n² + 3n + 2)/2、p が奇数で (3n² + 5n + 2)/2。素冪でない位数では、自明な H だけがほぼ可換 | M* と原始べき等元・J による生成、⟨M*, J⟩ + ⟨M, E*_0⟩ は扱っていない。1 次元加群の番号づけもない |
| Bastian–Humphries 2024・2025（群スキーム、強ゲルファント対） | 要旨 | ほぼ可換の分類 | — |
| Ishibashi–Ito–Yamada 1999（Europ. J. Combin. 20） | 書誌だけ | 有限体上の円分スキームと Jacobi 和 | — |

- **生成の型の既知の結果（照合先）。**
  - P 多項式かつ Q 多項式のスキームでは、M と M* がそれぞれ A と A* で生成されるので、T = ⟨A, A*⟩ です（距離正則グラフの標準的事実）。
  - 三重正則なら T = span{E*_i A_j E*_k} です（Kim 2011 の補題 2.3 が引用）。
  - 主部分代数 T_0 は F と F* で生成されます（順序 Hamming スキームの論文、arXiv:2407.06550 の補題 4.5）。
  - どれも、項目 66〜69 の型（M* と少数の原始べき等元、2 つの部分代数の和）とは別の問いです。
- **用語の注意。** 文献で "cyclotomic scheme" と言うと、有限体の上のスキーム（乗法群の部分群の剰余類による）を指すことが多いです（Ishibashi–Ito–Yamada）。私たちの対象は、巡回群 ℤ/N 上の Aut の軌道 Schur 環（円分 Schur 環）で、Bastian–Humphries 2026 の言葉では S(C_N, Aut(C_N)) です。辞書と今後のノートでは、混同しない書き方にします。
- **素冪の場合のスキーム。** ℤ/p^k の軌道 Schur 環は K_p の輪積です（前回の盲検が Bastian–Humphries 2026 の定理 3.7 で確認）。Song–Xu・BST の対象はこれに当たります。Kim 2011 の巡回スキームの輪積は別物です。

## 2. 導出の長さの見立て（私の見立て。確信度：中）

- **項目 66（次元の数え上げ）。**
  - Lean の `finrank_sumSub_add`（N ≥ 3）から、dim(和) = d² + 2d − 3 − 2[2 ∣ N] です（d は約数の個数）。これは dim⟨M*, J⟩ = d² + \|S′\|、その双対、共通部分の次元 d² + 1（項目 65）の組み合わせです。
  - dim T は、素冪では Song–Xu・Bastian–Humphries の式、合成数ではテンソル積で積です。
  - 確認：
    - N = p（奇数）で 5 = 5、N = p² で 12 = 12、N = p³ で 21 < 22。
    - N = 4 で 10 = 10、N = 8 で 19 = 19、N = 16 で 30 < 31。
    - N = pq（奇数）で 21 < 25。
  - 共通部分の次元（項目 65）が要る入力で、ここは文献に明示がありません（前回の盲検：初等的）。
- **項目 67〜69（素冪）。**
  - 主でない既約加群は 1 次元で、Song–Xu の中心べき等元 F_ih（1 ≤ h < i ≤ k。p = 2 では (i, i − 1) が欠ける）で番号づけられます。
  - ⟨M*, J, E_s⟩ = T は、生成元がこれらの 1 次元加群を互いに区別し、主加群とも区別することと同値です。Part 248 の (δ, u) の議論は、この区別の場合分けです。例外 (p³, p)・(16, 2) は、ラベルの重なり（u = 0 と u = 2 が区別できない）から来ます。
  - 短い場合分けです。ただし、Song–Xu の番号 (i, h) と Part 248 の (δ, u) の対応は、私はまだ書き下していません。
- **項目 67〜69（合成数）。**
  - T はテンソル積になり（Hanaki–Kim–Maekawa）、主でない加群は 1 次元とは限りません（Bastian–Humphries 2026 の定理 4.6：素冪でない位数ではほぼ可換でない）。
  - Lean の証明は、恒等式 (II)（`convL_geps_prime_mul`：E_{qt} を (1 − E_t)G_qE_tG_q(1 − E_t) で書く式）を使いました。
  - これは既知の構造の上の追加の計算で、照合した文献の結果から直ちには出ません。候補 1 の残余はここです。

## 3. 判定と、新しい規則への当てはめ

- **判定。** 候補 1 は、新規候補のまま残ります（確信度：中）。範囲は「合成数の N での生成の分類」に絞られます。新しい現象ではなく、既知の構造の上の「書かれていない計算」です。
- **新しい規則（残余の明示と対照群）への当てはめ（私の見立て）。**
  1. 幾何の言葉：殻（原点からの gcd の距離）と双対殻の射影が、少ない生成元で代数全体を生むか。
  2. 既存の言葉への翻訳：円分 Schur 環の Terwilliger 代数 T(0) の生成系の分類。
  3. 残余：合成数の N での場合分けの計算（項目 66 の合成数の場合と 67〜69）。計算の細部です。
  4. 対照群：有限の組合せ論の文で、算術的・大域的な内容を主張していません。規則の対象外と見ます。あえて当てはめると、関数体の類似（F_q[t]/(m) の単数群の軌道スキーム）でも同じ型の問いが立ちます。結論が同じ形になるかは確かめていません。
- 新しい規則に従えば、「小さいノート」として扱う候補です（著者の判断）。

## 4. 限界・未実施
- MathSciNet・zbMATH：未実施（上記）。
- 本文の確認は自動の読み取りで、人の精読ではありません。BST 2010 と Tanaka 2011 は本文を読んでいません。Hanaki–Kim–Maekawa は前回の盲検の確認に頼っています。
- 新規性に関わる判定ですが、今回の文献照合は私の文脈で行いました。前回の再監査の盲検（文脈なし）の判定と同じ向きです：(9a) は既知の帰結、(9b)(9c)(9e) は文献にないが初等的、(9d)(9f) は新しい可能性（小）。
- Song–Xu の番号と Part 248 のラベルの対応表は作っていません。小さいノートにするなら、最初に要る部分です。

## 5. 検索ログ（2026-11-12 夕方）
- Terwilliger algebra generated by dual Bose-Mesner algebra and primitive idempotent subalgebra generation（extended）
- Tanaka "almost commutative" Terwilliger algebras classification commutative association schemes
- Ishibashi Ito Yamada Terwilliger algebras of cyclotomic schemes Jacobi sums
- zbMATH Terwilliger algebra cyclic group Schur ring orbit association scheme
- Song Xu Terwilliger algebra wreath products of one-class association schemes complete structure
- "Terwilliger algebra" generated by "dual Bose-Mesner algebra" and "J" primary module subalgebra E_i^* J E_j^*
- 取得した本文：arXiv:2606.19095（Bastian–Humphries）、arXiv:1103.4216（Kim）、arXiv:1008.2228（Song–Xu）
