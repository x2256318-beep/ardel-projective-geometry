# 盲検の問いテストの出力（2026-11-18、ウェブ検索のみ、所要 約 4 分）

（照合者の出力をそのまま保存。依頼文は同じディレクトリの blind_question_request.md。）

## 文献照合の結果（ウェブ検索のみ。ファイルは読んでいない）

**3 の判定：部分的に既知。** 部品はすべて既知です。ただし、「各素点の P¹ の上で 0 と ∞ を貼り合わせる一つの構成があり、有限素点のねじれなしの貼り合わせと無限素点の U による貼り合わせはその特殊化である」という形で書いた文献は、見つかりませんでした。これは「存在しない」という意味ではありません。MathSciNet と zbMATH は使えておらず、未照合です。

### 1. 有限素点の側（ℤ/p^K 上の P¹、2 チャート、赤道での貼り合わせ、反転 W）

- **P¹(ℤ/N) そのもの：既知（確信度：高）。** 点 [x:1] と [1:y] のチャート、単数の重なりで y ↦ y⁻¹ を通す推移、[c:d] ↦ [d:c] の入れ替えは、モジュラー記号の標準的な道具です。Γ₀(N)\SL₂(ℤ) と P¹(ℤ/N) の対応（https://ar5iv.labs.arxiv.org/html/1809.04645）として計算論の教科書や講義録に出てきます（講義ノートの例：https://math-sites.uncg.edu/sites/yasaki/teaching/modform/documents/notes.pdf）。
  - 一次文献は Manin (1972)、Cremona の『Algorithms for Modular Elliptic Curves』、Stein の『Modular Forms: A Computational Approach』(AMS GSM 79, 2007) と記憶しています。ただし今回の検索では本文を開いていません（確信度：中）。
- **P¹(ℤ/p^K) と P¹(ℚ_p) の関係：記憶による見込み（確信度：中）。** P¹(ℤ/p^K) は P¹(ℚ_p) = P¹(ℤ_p) のレベル K の商です。また、Bruhat–Tits 木の基点から距離 K の頂点の集合とも同一視されます（Serre『Trees』）。
  - 今回の検索ではこの対応を述べた箇所に直接は当たらず、未確認です。
  - P¹(ℤ/p^K) 上の関数空間は、GL₂(ℤ/p^K) の P¹ 上の置換表現（ボレル部分群からの誘導表現）として扱われるのが普通です。
- **「P¹ 上の畳み込み」：特定の文献は見つかりませんでした。** P¹ は群ではありません。そのため「畳み込み」は、(i) 赤道の単数群 (ℤ/p^K)^× 上の乗法的な畳み込みか、(ii) GL₂(ℤ/p^K) の作用についての Hecke 環（ゲルファント対）の作用か、のどちらかとして読むことになります。
  - 有限のゲルファント対と木の調和解析の一般論は Ceccherini-Silberstein–Scarabotti–Tolli の木とゲルファント対の論文（https://core.ac.uk/download/54276754.pdf）などにあります。
  - ただし、ℤ/p^K 上の P¹ と 2 チャートという形を明示した文献は見つかりませんでした。

### 2. 無限素点の側（切断区間での D の自己共役拡張、U による貼り合わせ、反転との両立）

- **区間上の −i d/dt の自己共役拡張：古典（確信度：高）。** 拡張は U(1) の位相 e^{iθ} で分類され、境界ユニタリによる一般の分類もあります。
- **境界ユニタリ U と対称性の両立の一般論：既知（確信度：高）。** Ibort–Lledó–Pérez-Pardo, "On self-adjoint extensions and symmetries in quantum mechanics"（arXiv:1402.5537）。
  - 主な結果は、境界上で U と対称性の作用 v(g) が可換 [v(g), U] = 0 なら、拡張は G 不変になる、というものです（定理 6.10(i)）。
  - 例 7.1 は円柱の ℤ₂ 反転で、条件は U₂₁ = U₁₂、U₂₂ = U₁₁ です。準周期の U = [[0, e^{iα}], [e^{−iα}, 0]] の中では、周期的な α ≡ 0 だけが両立します。
  - ただしこの例は Laplace–Beltrami 作用素の例で、x ↦ 1/x そのものではありません。
  - 関連論文：Laplace–Beltrami 作用素と境界ユニタリ（arXiv:1308.0527）。
  - 掲載先は Ann. Henri Poincaré (2015)、および J. Funct. Anal. (2015) と記憶していますが、ページ上では確認できませんでした（確信度：中）。
- **xp の切断区間版：既知（確信度：高）。** Sierra, "H = xp with interaction and the Riemann zeros"（2007、https://arxiv.org/pdf/math-ph/0702034）。
  - 区間 (1, N) 上の H₀ には位相 e^{iθ} でパラメータ付けられる自己共役拡張の族があります。境界条件は e^{iθ}ψ(1) = √N ψ(N) で、q = log x により −i d/dq に写されます。
  - ただし x ↦ 1/x との両立は論じていません。
  - 掲載先は Nucl. Phys. B 776 (2007) と記憶していますが、未確認です。
- **xp の改良版と Dirichlet L 関数：** Sierra–Rodríguez-Laguna, "The H = xp model revisited and the Riemann zeros"（2011、https://arxiv.org/pdf/1102.5356）。境界条件は位相 ϑ を持つ非局所的な条件です。「別の自己共役拡張を使うことで Dirichlet L 関数に一般化する」と書かれており、これは指標ごとに境界の位相を変える例にあたります。x ↔ 1/x は使っていません。
- **Connes の切断：既知（確信度：高）。** Connes, "Trace formula in noncommutative geometry and the zeros of the Riemann zeta function"（https://arxiv.org/abs/math/9811068）, Selecta Math. 5 (1999)。
  - Λ 切断の具体的な定義の部分は、取得できた範囲には含まれておらず、本文で確認できていません。
  - 続編は Connes–Consani, "Weil positivity and trace formula, the archimedean place"（https://arxiv.org/abs/2006.13771、2020）です。切断の射影の値域の直交補空間に圧縮したスケーリング作用のトレースと、プロレート関数を使っています。
- **結論：** 「切断区間で U による貼り合わせを行い、x ↦ 1/x とも両立させる」ことの分類を、その形で書いた文献は見つかりませんでした。ただし、Ibort–Lledó–Pérez-Pardo の一般定理を ℤ₂ = {1, W} に当てはめた直接の帰結と見込みます（確信度：中〜高）。

### 3. 全素点を通した統一（有限素点の側にも指標の位相によるねじれを入れる形を含む）

部品は次のとおりすべて既知です。

- **Tate の局所関数等式（確信度：高。Tate 1950、Cassels–Fröhlich 収録）。** 各素点 v で、フーリエ変換と x ↦ 1/x の合成は ℚ_v^× 上の乗法的な作用素になり、メリン変換では指標ごとの局所因子 ρ(χ, s) を掛ける作用素になります。この因子は、分岐する素点ではガウス和、つまり ε 因子・ルート数を含みます。ℚ_v^× の 0 側と ∞ 側を指標の位相でねじって対応させる構造が、全素点で同じ形で既にここにある、と言えます。
- **Burnol（確信度：高）。** 有限素点と無限素点を同じ形で扱っています。
  - "Spectral analysis of the local conductor operator"（1998、https://ar5iv.arxiv.org/html/math/9811040）：H はフーリエ変換・伸縮・反転 I と可換で、その乗数は Tate–Gelfand–Graev のガンマ関数 Γ(χ, s) の対数微分です。分岐指標も含みます。
  - "The explicit formula in simple terms"（https://arxiv.org/abs/math/9902080）：「離散でも無限でも、分岐していてもいなくても、すべての素点を同じように扱う」と明記しています。
  - "Scattering on the p-adic field and a trace formula"（IMRN 2000, no. 2、https://www.arxiv.org/abs/math/9901051）：非アルキメデス的局所体で、流入空間と流出空間を互いのフーリエ変換に取る Lax–Phillips 散乱です。Connes のトレースにも適用しています。
  - "An adelic causality problem related to abelian L-functions"（J. Number Theory 2001、https://arxiv.org/abs/math/0001013）：大域体全体のアデール版です。
- **Jacquet–Langlands（確信度：中〜高）。** GL₂ の Kirillov モデルでは、ワイル元 w のメリン変換が局所因子を掛ける作用素になり、局所関数等式には ε(s, π, ψ) が入ります（Buzzard の要約ノートの定理 2.18 の扱い）。この w は反転 W にあたります。
- **Srednicki, "The Berry–Keating Hamiltonian and the local Riemann hypothesis"（2011、https://arxiv.org/pdf/1104.1850）。** 実数の側と p 進の側を並べ、p 進の側の量子境界条件を 2N×2N のユニタリ行列 U に帰着させています。ただし p 進の作用素は Berry–Keating の作用素と単純には関係しないと本人が断っており、p = 2 は未証明です。統一の試みとしては部分的です。
- **見つからなかったもの：**
  - P¹(𝔸_ℚ) = ∏′ P¹(ℚ_v) の上で、各素点の 0 と ∞ の貼り合わせを一つの構成とし、有限素点のねじれなしの南北の貼り合わせと無限素点の U による貼り合わせをその特殊化として並べる定式化。
  - 有限素点の P¹(ℤ/p^K) の 2 チャートの推移に、ガウス和の位相を入れる形のもの。
  - Haran の『Arithmetical Investigations』(LNM 1941, 2008) は実数と p 進を「量子補間」でつなぎ、局所 Tate の理論の q 補間を含みます。しかし扱っているのは ℤ_p と [−1, 1]、それにグラスマン多様体で、P¹ の 0 と ∞ の貼り合わせという形は書誌の記述には見当たりませんでした。

**照合者としての指摘（文献ではなく私の観察。確信度：中）：**

- (A) の F_N(y) = F_S(y⁻¹) は**チャートの座標変換**であり、関数を P¹ 上で定義するための恒等式です。
- (B) の U は**自己共役拡張を選ぶ境界条件**です。
- この 2 つは数学的に種類が違います。上の文献で「指標の位相によるねじれ」が有限素点に現れるのは、チャートの推移ではなく、反転 W とフーリエ変換の合成（Tate の ρ(χ, s)、JL の w の作用）の側です。
- したがって「同じ構成の特殊化」として並べるなら、有限素点の側で U に対応させるのはチャートの推移ではなく、W とフーリエ変換の合成でしょう。そうすると、ねじれのない (A) と U による (B) を同列に置く比較は崩れる可能性があります。

### 4. まとめ（文献と確信度）

| 問い | 判定 | 主な文献 | 確信度 |
|---|---|---|---|
| 1. P¹(ℤ/p^K)、2 チャート、W | 既知（標準） | Manin 1972、Cremona、Stein 2007（本文未確認）、モジュラー記号の講義録 | 高（構成そのもの）、畳み込みは特定できず |
| 2. 切断区間での D の U による拡張と反転との両立 | 部品は既知。その形での分類は見つからなかったが、一般定理の直接の帰結と見込む | Ibort–Lledó–Pérez-Pardo（arXiv:1402.5537）、Sierra 2007、Sierra–Rodríguez-Laguna 2011、Connes 1999、Connes–Consani 2020 | 中〜高 |
| 3. 全素点を通した統一 | **部分的に既知** | Tate 1950、Burnol 1998〜2001、Jacquet–Langlands 1970、Srednicki 2011 | 部品は高、統一の形が未発見であることは中 |

未実施：MathSciNet・zbMATH、および Connes 1999 の切断の節の本文。掲載先のうち「記憶」と書いたもの（Ann. Henri Poincaré、J. Funct. Anal.、Nucl. Phys. B など）は検索結果のページでは確認できていません。
