# 統合照合の入力（索引の第 5 版の後の尾、2026-11-19 夕方）

照合の対象は §A の差分で追加・変更された文（基礎文書の材料索引 `pag2_founding_material_index.md` と辞書 `pag2_terwilliger_dictionary.md`）と、§F の引き継ぎメモの差分です。§B〜§E は文脈と根拠です。

## §A 差分（索引と辞書、第 5 版のコミット deab9f3 から現在まで）
```diff
diff --git a/notes/pag2_founding_material_index.md b/notes/pag2_founding_material_index.md
index 1889aa4..6c8f613 100644
--- a/notes/pag2_founding_material_index.md
+++ b/notes/pag2_founding_material_index.md
@@ -166,6 +166,27 @@
   - 局所定数との一致を書くときは、イデール類指標の正規化（2.7）も併記する（出所：索引の照合者の指摘と Part 257 の冒頭の説明。CLAUDE.md §1 に正規化を足すことを 2026-11-19 06:36 に著者が承認した）。
 - ノート：`pag2_literature_ia_sign.md`、CLAUDE.md §1。
 
+**2.9 有限素点の側の代数 A_∞ と、射影の変換・貼り合わせの位相・無限素点の符号。A_∞ は、導手の区分けと小さい法（位相は N ∣ 24、符号は N ∣ 12）の場合を除いて、位相も符号も見ない（否定的な結果、数値と手計算）。**
+- 地位：読みと否定的な結果（2026-11-19 夕方の関門、`pag2_projection_interaction_preregistration.md`）。新しい Lean はない。数値と盲検の手計算が一致した。Lean にしない推薦は、2026-11-19 17:17 に著者が「進めてください」で採った。
+- 内容：
+  - 単数の乗法 R_u・パリティ P = R_{−1}（無限素点の符号）・素数冪ごとの殻の反転の CRT の積 J は、どれも A_N と可換（可換子の側、イーデルの側）。読み：A_N = End(V_N)^{G_N}（G_N は 0 を固定し、すべての d ∣ N で合同関係を保つ置換の群）、可換子はその群環の像（二重可換子定理）。
+  - 射影の変換 J∘H（2.4）は、A_N の上で D_s ↔ E_s の双対の自己同型として働く（J が可換なので Ad(JH) = Ad(H) = Ad(F)）。
+  - フーリエは角の写像の系 φ（5.5）を 0 拡張の系 ψ（スケーリング、Bost–Connes の μ_n の型）に移す（F_M ι = V F_N。Pontryagin 双対）。
+  - 単数の角 D_1 A_N D_1 は導手ごとの射影の張る可換代数。U_N はこれと可換だが、属するのは N ∣ 24（そのとき U_N = I）のときだけ。符号の単数への制限が属するのは N ∣ 12 のときだけ。P ∈ A_N も N ∣ 12 のときだけで、極限では、符号は N ∣ 12 のレベルの角の上でだけ A_∞ に入る（数値 139 組）。
+  - したがって A_∞ は、貼り合わせの位相（A1）にも無限素点の符号にも、導手の区分け以外の制約を課さない。位相はガウス和（H の中）と公準 A1 から入る。
+  - range(D_1) ∩ range(E_1) は原始指標の張る空間（2.5 の V_prim）で、J∘H はこれを保ち、そこでの制限が U_N の制限（2.5 のユニタリ性の構造上の理由づけ）。
+- 素朴な一般化の失敗（第 6 の型）：法 N の殻ごとの反転 s·w ↦ s·w⁻¹（法 N/s）は、N = 10, 14, 15, … で A_N と可換でない。可換なのは素数冪ごとの反転の CRT の積。
+- 書き方の規則：「A_∞ と射影の変換からルート数が出る」と書かない（円環の第 2 の型、注入→回収）。
+- Lean（既にあるもの）：
+  - 単数の乗法との可換：`PAG.Part218.shellAlg_comm_dil`。可換子 `PAG.Part224.fullComm`、可換子が可換 ⇔ N ∣ 12：`PAG.Part225.fullComm_commute_iff_dvd_twelve`。
+  - フーリエ共役：`PAG.Part246.fourierConj_convL_geps`・`PAG.Part246.fourierConj_mulLeft_dind`。
+  - 導手ごとの部分 `PAG.Part258.condPart`、原始部分 `PAG.Part257.Vprim`、`PAG.Part256.JH_eq_rootNum_mul`、U_N `PAG.Part258.UA1`。
+- Lean の外：Hartley 変換と殻の反転 J による共役の文、F_M ι = V F_N、単数の角の記述、N ∣ 24・N ∣ 12 の判定。
+- 対照群：関数体 F_p[t]/(t^e) でも同じ形（数値、p = 2, 3, 5）。判定の値（N ∣ 24 に当たるリスト）と位相の値は変わり、ℚ の値は Gauss の符号定理と i^a を無限素点の因子と読むこと（2.8 の規約 T）に依存する（照合者）。
+- 文献：Bastian–Humphries（arXiv:2606.19095）、Bhattacharyya–Song（arXiv:0809.1052）、arXiv:2510.17118 の式 (2)（T(v) ⊆ End_{G_v}）、Martin–Tanaka の解説（arXiv:0811.2475）、Kim–Kim（arXiv:1108.4947）、Montgomery–Vaughan 第 9 章、Shirbisheh（arXiv:0808.1767）、Arledge–Laca–Raeburn（1997）。照合者の WebSearch・WebFetch による。MathSciNet・zbMATH は未実施。
+- 推薦：Lean にしない。残余が空。
+- ノート：`pag2_projection_interaction_preregistration.md`。
+
 ## 第 3 章　解像度と有効な姿（§1 の命題 3）
 
 **3.1 定義文と、その置き方と読み。**
@@ -229,6 +250,7 @@
   - 答えの範囲の外：弱い読み、単位元を保たない写像、両立条件を別の形にした写像。
   - 対照群（盲検の申告で、未確認）の結果から、アーデル射影幾何に固有の内容としては数えない（Part 258 のノート）。
   - 文献照合（MathSciNet・zbMATH と、Hanaki–Kim–Maekawa・Bastian–Humphries の本文）が済むまで、外部で新規性として使わない。
+  - 構築側で開ける範囲の文献照合（2026-11-19、`pag2_candidate3_literature_builder.md`）：Bastian–Humphries・Watanabe（arXiv:2305.19258）・Kim（arXiv:1109.1334）の本文に、商に沿った単位的な写像の記述は見つからなかった。Hanaki–Kim–Maekawa の本文は構築側の環境から取得できず、盲検の申告のまま。MathSciNet・zbMATH は著者側の作業として残る。
 - ノート：`pag2_part258_beta_premise.md`、CLAUDE.md §3。
 
 **5.2 Part 259：フーリエとの両立を足した一意性と、帰納系の添字。**
@@ -247,8 +269,46 @@
   - どの有向な部分系も、整除の順序で共終でない。したがって関数のレベルの極限 ℂ[ℚ/ℤ]（5.3）の代数版にはならない（初等的。Lean にしていない）。
   - a が奇数のときの一意性は、数値のみ。
   - gcd ≠ 1 で (i) と D の側だけを満たす写像があるかは、未確認（小さい数値では見つからなかった。証明ではない）。
+  - 非単位的な角の写像では、上の「代数版にはならない」は当てはまらない（5.5。上の文は単位元を保つ写像についての文）。
 - ノート：`pag2_part259_unitary_step_maps.md`、`pag2_R1_assessment.md`。
 
+**5.5 角の写像（非単位的）：N ∣ M のとき、φ(S) = (N/M)·π^* ∘ S ∘ π_* は A_N を A_M に送る非単位的な代数準同型で、合成と恒等の法則を満たす（gcd(N, M/N) によらない）。**
+- 地位：定理（Part 260（PAG264）、短期層、2026-11-19）。
+  - ラベル：E 側の像は［既知］（商スキームのべき等元による角）、ほかは［再導出（小さい）］。
+  - 対照群は ℤ/p^e の段に当たる場合（F_p[t]/(t^e)）に限って同じ文が成り立つ（数値。互いに素な段は試していない）。使うのは平行移動スキームの形式だけ（盲検の手計算）なので、アーデル射影幾何に固有の内容としては数えない。
+- Lean（Part 260（PAG264））：
+  - A_M に入る：`PAG.Part264.cornerOp_mem`。写像 `PAG.Part264.cornerHom`。
+  - 生成元の像：`PAG.Part264.cornerOp_geps`（φ(E_s) = E_{(M/N)s}）、`PAG.Part264.cornerOp_one`（φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s）、`PAG.Part264.cornerOp_dind`。
+  - 引き戻しと両立：`PAG.Part264.cornerOp_pull`。
+  - 一意性：`PAG.Part264.existsUnique_corner`。条件は (a) 引き戻しとの両立と (b) φ(1) の値。(b) を外すと一意でない（照合者の手計算）。
+  - 合成：`PAG.Part264.cornerHom_comp`。恒等の法則：`PAG.Part264.cornerHom_self`（2026-11-19 午後に追加）。合成と恒等の 2 法則で、正の整数の整除の順序の上の帰納系の法則が揃う。
+  - N < M なら φ(1) ≠ 1：`PAG.Part264.cornerHom_one_ne_one`。
+  - D 側の証人：`PAG.Part264.cornerOp_dind_not_mem_span`（(2,4)）。
+- 留保：
+  - 次のものは Lean の外。
+    - 極限の具体形（Ẑ 上の局所定数関数への作用）。
+    - 像が角全体であること（数値 111 組、三重正則性からの短い帰結の見込み）。
+    - Bost–Connes の ρ との対応（6.3）。
+  - D 側は殻の span に入らないので、5.1 の強い読みの外。これは素数冪の段に固有ではない（N < M のすべての s：数値 81 組）。
+  - 極限は直極限（有限次元の代数の和集合）の側でとる。完備化は解像度が落ちる側の操作と読む（§1 の 08:41 の定義）。
+  - 照合：独立照合、再照合、統合照合（恒等の法則と尾）。統合照合の後の直しは主張を狭める・明確にするものだけで、尾の台帳は空。
+- 帰納系と極限（Part 261（PAG265）、短期層、2026-11-19 午後）：
+  - 正の整数の整除の順序（Part 254 の `Lvl`）の上の `DirectedSystem`：`PAG.Part265.cornerSys_self`・`PAG.Part265.cornerSys_comp`。
+  - 極限 `PAG.Part265.CornerLim`（Mathlib の一般の `DirectLimit`）は、非単位的な環の構造と ℂ のスカラー倍を持つ。
+  - 各段は単射に入る：`PAG.Part265.ofCorner_injective`。
+  - 局所的な単位元：1 元ごとが `PAG.Part265.exists_local_unit`、有限集合ごとが `PAG.Part265.exists_local_unit_finset`。べき等元 e_a は a について増大する（`PAG.Part265.ofCorner_one_le`）。
+  - 左単位元はない：`PAG.Part265.not_exists_left_one`。
+  - 局所的な単位元の文はどの直極限でも成り立つ一般論で、非単位的という内容を運ぶのは左単位元がないことだけ。その証明は素数冪の段を要らない見込み（手計算）。
+  - 極限は直極限の側でとり、完備化は使っていない。
+- 極限の具体形（読み。Lean の外。2026-11-19 午後の盲検の問いテスト、`pag2_limit_form_preregistration.md`）：
+  - 極限は Ẑ 上の局所定数関数の空間 V_∞ に、完備化なしに忠実に作用する（照合者の手計算）。
+  - 素点ごとに、局所の単位 e_1（定数への射影）に関する制限テンソル積 ⊗'_p に分かれる。Flath 型の当てはめ。角の写像が中国剰余定理と両立することは数値で 1098 回確かめた。
+  - 文献：Flath（1979）、Deitmar（arXiv:1002.0475）、アデールの Schwartz–Bruhat 関数、Laca–Larsen–Neshveyev（arXiv:math/0609316、定理 3.2）。
+  - 否定的な観察（照合者、確信度：中）：局所の代数は抽象的な代数としては p によらない見込みで、A_∞ に入る算術は素点が可算個あることだけ。無限素点・スケーリング・貼り合わせ U は A_∞ に現れない。
+  - 残余がないので、Lean にしない（推薦）。
+- 無限素点・スケーリング・貼り合わせ U との相互作用（読みと否定的な結果）：2.9。
+- ノート：`pag2_pag264_corner_maps.md`、`pag2_pag265_corner_limit.md`、`pag2_gamma_corner_preregistration.md`、`pag2_limit_form_preregistration.md`。
+
 **5.3 関数のレベルの帰納系。**
 - 地位：定理（Lean）。ラベルは、この索引では確かめていない。
 - Lean：
@@ -300,6 +360,8 @@
 
 **6.3 Bost–Connes との接続。**
 - 地位（骨格の記述）：関数のレベルでは既知。T(0) の側に届くかは、方向 γ の文献照合の結果による。γ の文献照合は著者側の作業（CLAUDE.md §2）。
+- 構築側で開ける範囲の照合（2026-11-19、`pag2_gamma_literature_builder.md`）：検索 5 回の範囲で、有限レベルの Bost–Connes と T(0) を結ぶ記述は見つからなかった（本文は開いていない。確信度：低〜中）。BC の有限レベルは群環 ℚ[ℤ/nℤ] の帰納系（関数のレベル、既知）。［観察］BC の帰納系は整除のすべての段を使うが、T(0) の側の単位的な写像は互いに素な段だけ（5.1・5.2）。MathSciNet・zbMATH は著者側に残る。
+- 立て直しの結果（2026-11-19、Part 260（PAG264）、5.5）：BC の ρ_n（ρ_n(1) = μ_n μ_n^*）に倣った角の写像は、T(0) に非単位的な代数準同型として延びる（A_M に入ること・合成・一意性は Lean）。群環の側で ρ と一致することは数値で、Lean の外。盲検の手計算では、L²(Ẑ) の表現で T(0) の片側（D 側）が BC に対応し、もう片側（E 側）は BC の表現の外。Terwilliger 版の角の文と、BC と T(0) を結ぶ文献は見つからなかった（確信度：低〜中）。
 - CLAUDE.md §2 には、有限レベル Bost–Connes に元の BC 系が対応する、という記載がある。
 - ノート：CLAUDE.md §2。
 
@@ -316,8 +378,8 @@
 
 - **著者の確認待ち**：なし（2026-11-19 にすべて閉じた。「貼り合わせ」は U、Part 258 の条件は強い読み）。
 - **著者側の作業**（担当は骨格と CLAUDE.md §2 の記載による）：
-  - 方向 γ の文献照合（6.3）。
-  - 候補 3 の文献照合（5.1）。
+  - 方向 γ の文献照合（6.3）。構築側で開ける範囲は 2026-11-19 に済み、MathSciNet・zbMATH が残る。
+  - 候補 3 の文献照合（5.1）。MathSciNet・zbMATH と、Hanaki–Kim–Maekawa の本文（構築側の環境から取得できない）が残る。
   - 候補 1 の MathSciNet・zbMATH（6.2。ノートの言葉では「著者側か専門家への照会」）。
 - **Lean の外・数値のみで残るもの**：
   - 構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0}（1.2・1.3）。
@@ -329,6 +391,7 @@
   - `sqLim` の代数構造（5.2）。
   - a が奇数のときの一意性（5.2）。
   - (i) と D の側だけを満たす写像の有無（5.2）。
+  - 角の写像の像が角全体であること、極限の具体形、Bost–Connes の ρ との対応（5.5・6.3）。
 - **定式化の問い**：
   - 解像度の操作に、L1 を超える定式化が要るか。骨格の記述では、現時点では L1 と 08:41 の定義で文書は書ける。
   - 「射影」の、全素点を通した一つの構成（空間と作用素のレベル）としての定式化。値のレベルについては 2.7。
diff --git a/notes/pag2_terwilliger_dictionary.md b/notes/pag2_terwilliger_dictionary.md
index 4cf0faa..af09d02 100644
--- a/notes/pag2_terwilliger_dictionary.md
+++ b/notes/pag2_terwilliger_dictionary.md
@@ -422,3 +422,42 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
 
 - 未記入の件数：0。
 - 「貼り合わせ」「素点」「重なり」は著者の言葉で、解釈の層のまま。
+
+## 17. Part 260（PAG264、短期層）で足した名前（角の写像 A_N → A_M、2026-11-19）
+
+（Part 257〜259 の名前はこの辞書に未記入。今回の分だけ足す。）
+
+| 名前・主張 | 文献の言葉 | 出典・注意 |
+|---|---|---|
+| `fsum`（繊維の和 π_*） | 押し出し（pushforward）、引き戻しの随伴（数え上げの内積で） | 標準 |
+| `cornerOp`・`cornerHom`（φ(S) = (N/M)·π^* ∘ S ∘ π_*） | 等長写像 ι = π^*/√(M/N) による共役 ι S ι^†（角への埋め込み、非単位的な *準同型）。Bose–Mesner の側では、商スキーム（部分群 H = Nℤ/Mℤ による商）の隣接代数がべき等元による角 e_H A e_H に同型という古典的事実 | 盲検（2026-11-19）が挙げた Zieschang, Theory of Association Schemes（2005）Thm 2.1.8(ii)・4.1.3、Kodalen 2019 §2.5（Lemma 2.13・2.14）。T(0) 版（T(X//H) が T(X) の角）の文献は見つからなかった（確信度：低〜中） |
+| `cornerOp_one`（φ(1) = Σ_{(M/N) ∣ s} E_s） | 商スキームのべき等元 e_H = (1/|H|) σ_H（Bose–Mesner 代数の中） | 同上 |
+| 像 = 角全体（Lean の外） | 三重正則性（T = span{E*_i A_j E*_k}）からの帰結の見込み | Munemasa 1993 Lemma 4、Bhattacharyya–Song–Tanaka 2010 Thm 3.10（盲検が本文を開いた）、ℤ/p^e が K_p のリース冪であることは Bastian–Humphries 2026 Thm 3.7 |
+| 群環の側での φ（数値） | Bost–Connes の自己準同型 ρ_n（ρ_n(e(r)) = (1/n)Σ_{ns=r} e(s)、ρ_n(1) = μ_n μ_n^*） | 盲検の手計算（L²(Ẑ) の表現で ψ ↔ Ad μ_n）。T(0) の片側だけが BC に対応する |
+
+- 未記入の件数（この節）：0。
+
+## 18. Part 261（PAG265）と極限の具体形の読みで足した名前（2026-11-19 午後）
+
+| 名前・主張 | 文献の言葉 | 出典・注意 |
+|---|---|---|
+| `CornerLim`・`ofCorner`（Mathlib の一般の `DirectLimit`） | 有限次元の代数の非単位的な直極限。局所的な単位元を持つ環（rings with local units） | Ánh–Márki の流儀の定義（照合者の記憶、本文は未照合） |
+| `exists_local_unit_finset`・`not_exists_left_one` | 局所的な単位元を持つが単位的でない環 | 同上 |
+| 極限の V_∞（Ẑ 上の局所定数関数）への作用（Lean の外） | Bruhat–Schwartz 関数の空間 C^∞(Ẑ) ≅ ⊗'_p C^∞(ℤ_p) | Bump、Ramakrishnan–Valenza（盲検が Wikipedia 経由で挙げた。未照合） |
+| 極限の素点ごとの分解 ⊗'_p（Lean の外） | Flath 型の制限テンソル積（球関数のべき等元 ↔ 定数への射影 e_1） | Flath 1979、Deitmar arXiv:1002.0475。Bost–Connes 型は Laca–Larsen–Neshveyev arXiv:math/0609316 定理 3.2 |
+| A_N = End(V_N)^{G_N}（照合者の手計算、Lean の外） | 根付き p 分木の頂点の固定部分群の中心化代数（Terwilliger 代数 = 中心化代数） | 次元の一致（Bhattacharyya–Song、Bastian–Humphries の命題 3.3）。文献での明記は未確認 |
+
+- 未記入の件数（この節）：0。
+
+## 19. 無限素点・スケーリング・貼り合わせ U との相互作用の読みで足した名前（2026-11-19 夕方。Lean は足していない）
+
+| 名前・主張 | 文献の言葉 | 出典・注意 |
+|---|---|---|
+| 素数冪ごとの殻の反転の CRT の積 J（数値、Lean の外） | 基点 0 を固定する、スキームの自己同型（固定群 G_0 の元） | 盲検の手計算。法 N の殻ごとの反転 s·w ↦ s·w⁻¹ は N = 10, 14, … で自己同型でない（数値） |
+| `fullComm`（Part 220、PAG224）の群による記述（Lean の外） | 二重可換子定理：A_N = End_{G_0}(V_N) なら A_N' は G_0 の群環の像。T(v) ⊆ End_{G_v} | arXiv:2510.17118 の式 (2)。三重推移性（木のスキーム）の明記は見つからなかった（盲検） |
+| Hartley・フーリエによる共役（`fourierConj_*` は Part 242、Hartley 版は Lean の外） | translation scheme の指標による双対性（形式的自己双対性） | Martin–Tanaka の解説 arXiv:0811.2475 §6、Kim–Kim arXiv:1108.4947 |
+| 単数の角 D_1 A_N D_1 = 導手ごとの射影（Lean の外。`condPart` は Part 254） | E*_1 T E*_1（双対冪等元の角）。単数群の部分群 ker((ℤ/N)^× → (ℤ/g)^×) の上の平均 | 盲検の手計算 |
+| range(D_1) ∩ range(E_1) = V_prim（`Vprim` は Part 253、等式は Lean の外） | E*_1 V ∩ E_1 V。原始指標 ⇔ ガウス和 τ(χ, n) = χ̄(n)τ(χ) がすべての n で成り立つ | Montgomery–Vaughan Thm 9.7・Ex. 9.2.6 |
+| F_M ι = V F_N（数値、Lean の外） | Pontryagin 双対の関手性（商 ℤ/M → ℤ/N と包含の双対）。φ と ψ は Bost–Connes の ρ_n の 2 つの見方（平行移動の側と乗法作用素の側） | Shirbisheh arXiv:0808.1767、Arledge–Laca–Raeburn 1997。有限レベルで並べた文は見つからなかった（盲検、検索は浅い） |
+
+- 未記入の件数（この節）：0。
```

## §B 索引の変更後の全文

# アーデル射影幾何 — 基礎文書の材料索引（骨格の 6 章ごと）

（2026-11-18。短期層の作業。新しいパートではない。基礎文書の骨格（著者側、2026-11-15。以下「骨格」）の章ごとに、書く主張・その地位・支える Lean の宣言・ノート・照合の状態・開いている点を並べる。起草は著者側で行う。この索引は主張を足さない。地位とラベルは各ノート・CLAUDE.md・骨格の記載を写したもので、写すときに強めないことを方針とした。第 1 版を独立照合にかけ、その指摘で直した第 2 版を統合照合（2026-11-19）にかけ、その指摘で直したのが第 3 版、同日の著者の決定を記録したのが第 4 版、同日 07:10 の著者の確定を記録したのがこの第 5 版である（§8）。）

## §0 使い方と注意

- **地位の語**：
  - 「定義」＝著者の文面（CLAUDE.md §1）。
  - 「読み」＝解釈の層。誰が出し、誰が採用したかを添える。
  - 「定理」＝Lean の文。ラベル［既知］［再導出］［新規候補］を添える。
  - 「公準」＝A1。
  - 「数値のみ」＝数値確認だけで、証明はない。
  - 「Lean の外」＝文献か手計算による。
- **番号の罠**：
  - 第 3 期（PAG 2.0）の Part n は PAG(n+4).lean。Lean の名前空間はファイル番号に従う（例：Part 252 の宣言は `PAG.Part256.…`、Part 23 の宣言は `PAG.Part27.…`）。初期のファイル（PAG.lean・PAG2〜PAG6）にはこの対応は当てはまらない。
  - この索引では「Part n（PAGm）」と併記し、宣言は完全修飾名で書く。
- **記号の罠**：
  - 反転（0 と ∞ の入れ替え）は、Lean の `PAG.Part23.W`・`PAG.Part26.Wpt`・`PAG.Part27.Wproj` とモノグラフの W。この索引では ι とも書く。
  - `PAG.Part256.rootNum` の値（τ(χ)/(i^a√N)）は 𝔀(χ) と書く。PAG256 以降の docstring とノートでは記号 W(χ) がこの値を指すので、反転の W と混同しない。
- **照合の状態**：各パートを閉じるときの独立照合と、その後の再照合・統合照合を指す。詳細は各ノートの照合の節。
- **著者側のファイル**：骨格が引く次のファイルは、このリポジトリにない。索引ではファイル名だけを挙げる。
  - `what-is-aadel-projective-geometry.md`
  - A8 の一次評価
  - δ の事前登録と帰結
  - モノグラフ層の記録
  - 骨格そのもの
- **宣言名の確認**：2026-11-18 に、この索引に出る宣言名をすべて Lean のファイルで検索し、実在を確かめた（§7）。

## 第 1 章　点と大域対象

**1.1 点は素数たちと無限素点。無限素点では無限大と無限小が重なり合う。**
- 地位：定義（著者の文面、CLAUDE.md §1）。
- Lean：定義そのものはない。関連する定理は次の 2 つで、どちらも Part 255（PAG259）の［既知］。
  - 正の有理数について、すべての素数（有限素点）の付値の組は単射：`PAG.Part259.eq_of_padicValRat_eq`。
  - 積公式 log q = Σ v_s(q) log s：`PAG.Part259.log_eq_sum_of_support`。∞ の座標は有限素点の座標から決まる。
- ノート：`pag2_part255_resolution_discrete_limit.md`。

**1.2 大域対象は、制限積の因子として最初から並列に共存する素点たち。有限レベル商と Λ 切断は、その全体への見方（切り方）。**
- 地位：読み。命題 3 の置き方として、著者側 Muse の決定（2026-11-13。著者はいつでも覆せる）。
- 書き方の規則：解像度を N・Λ と同一視する禁止は維持する。決まったのは問いの置き場であり、パラメータではない。
- Lean（関連するもの。支えではない）：
  - Ẑ^× の具体モデル `PAG.Part255.unitSys`（両立する系の群、Part 251（PAG255））。
  - 制限積・無限素点・ℚ^× での商は含まない。`unitSys` ≅ Ẑ^× と構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0} は Lean の外。
- ノート：CLAUDE.md §1、`pag2_part251_projective_limit.md`。A8 の一次評価は著者側のファイル。

**1.3 素数の類は、有限レベル (ℤ/N)^× × ℝ と、極限の具体モデル `unitSys` × ℝ で、稠密な部分群を生成する。**
- 地位：定理［既知］（再導出。新規候補なし）。
- Lean：
  - 有限レベルでは `PAG.Part253.exists_cls_near`（Part 249（PAG253））。正の有理数 m/n の類についての文。
  - 極限のモデルでは `PAG.Part255.dense_closure_allPrimes`・`PAG.Part255.dense_closure_primeGens`（Part 251（PAG255））。素数の類の一意性は `PAG.Part255.primeSys_unique`。
- 留保：「大域対象で稠密」「イデール類群で稠密」は、Lean の外の同一視（`unitSys` ≅ Ẑ^×、構造定理）を経た読み。
- ノート：`pag2_part249_idele_class_density.md`、`pag2_part251_projective_limit.md`。

**1.4 舞台は射影直線 P¹。反転が 0 と ∞ を入れ替える。**
- 地位：
  - 「舞台は P¹」は著者の言葉（2026-11-18 19:01、「射影」の読みの採用のとき）。
  - 「反転が 0 と ∞ を入れ替える」は構築側の読みで、2026-11-16 に著者が確認した。
  - P¹(ℤ/N) そのものは［既知］（モジュラー記号の標準の道具）。
- Lean（Part 19・22・23（PAG23・PAG26・PAG27））：
  - 射影直線 `PAG.Part27.ProjLine`、反転 [a:b] ↦ [b:a] の定義 `PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`（一般の N）。
  - N = p^K（K ≥ 1）では、点モデル `PAG.Part26.Pt` との点集合の全単射 `PAG.Part27.projEquiv` と、点の数 `PAG.Part27.card_ProjLine`。
  - 2 チャートモデルの貼り合わせ条件 `PAG.Part23.Compat` と、その反転 `PAG.Part23.W`。点モデルの関数との線形同型 `PAG.Part26.ptEquiv`（一般の N）。
- 留保：
  - 「0 と ∞ は別の点で、反転がこの 2 点を入れ替える」という文は Lean にない（N ≥ 2 で正しい）。
  - N が 2 つ以上の素因数を持つとき、点モデルと P¹(ℤ/N) の点の数は一致しない（数え上げ、Lean の外）。
- ノート：`pag2_projection_material.md`（第 6 版）§1・§3。

## 第 2 章　無限素点の重なりと貼り合わせ

**2.1 重なりは、ねじれた貼り合わせ（境界ユニタリ U）と読む。**
- 地位：読み（著者の決定、2026-11-12）。
- 採らなかった読み：
  - 群の商として読む読み：A1 と両立しない。反例は法 9 の 3 次指標で、`pag2_resolution_overlap_materials.md` §3 の表に［批判］［数値］として記録されている。この反例の Lean の所在は、この索引では確かめていない。
  - W（反転）による商：A1 とは両立するが、D が商に降りない。
- ノート：`pag2_resolution_overlap_materials.md`、CLAUDE.md §1。

**2.2 モノグラフ層の作用素系（D、T_p、反転 W、二面体関係）、問題 P1、定理 2.6（境界条件 U の両立分類）。**
- 地位：モノグラフ層の記録（著者側、リポジトリにない）。
- Lean（有限レベル版だけ。Part 249（PAG253）、［再導出］）：
  - 素数の平行移動と可換なら、すべての単数の平行移動と可換：`PAG.Part253.commute_transl_of_prime`。
  - 指標ごとにスカラー：`PAG.Part253.eigenFun_of_commute_prime`。
  - (a)⇒(b) の完全な形：`PAG.Part253.thm26_full`。
  - 可換性を外した反例（N ≥ 3）：`PAG.Part253.thm26_needs_commute`。
- 留保：
  - 逆向き (b)⇒(a) は数値のみ。大域の Ẑ^× での形は Lean の外。
  - 証明は Dirichlet の算術級数定理を使わない簡略化で、新しい定理ではない。
- ノート：`pag2_part249_idele_class_density.md`。

**2.3 公準 A1（内容は Tate の定理）と、定理 2.6 との両立。**
- 地位：
  - A1 は公準（解釈の層の公準）で、導かれていない。
  - 両立は「既知の結果からの短い帰結」（確信度：高）。これはかつての新規候補 2 で、2026-11-12 に候補から外れた。
- 留保：
  - 定理 2.6 の反転の条件は、𝔀(χ⁻¹) = conj 𝔀(χ)（`PAG.Part258.rootNum_inv`。すべての指標で成り立つ短い計算）と、境界ユニタリの実性 KUK = U（`PAG.Part258.UA1_star`）に帰着する。|𝔀| = 1 には原始性と |τ|² = N が要る（`PAG.Part256.normSq_rootNum`・`PAG.Part258.normSq_phaseA1`）。A1 の算術の内容は、どの位相 α を選ぶかの部分だけ（`pag2_thm26_A1_collation.md` §11 の訂正）。
  - ルート数が条件を満たすことは整合性の確認にすぎず、A1 を導いたことにはならない。
  - 近い先行：Burnol、Ibort–Lledó–Pérez-Pardo の例 7.1・7.2（CLAUDE.md §3）。
- Lean：
  - ガウス和の側の部品の 3 定理（組み合わせた 1 つの文は形式化していない）：`PAG.Part16.normSq_gaussSum`、`PAG.Part173.gauss_inv_pair`、`PAG.Part198.gauss_sign_real`。番号の対応は各ファイルの冒頭の記載による：PAG16 は Part 12、PAG173 は Part 169、PAG198 は Part 194。
  - A1 の位相そのものについて（Part 254（PAG258））：
    - 𝔀(χ⁻¹) = conj 𝔀(χ)（すべての指標）：`PAG.Part258.rootNum_inv`。
    - 位相についての同じ式：`PAG.Part258.phaseA1_inv`。
    - 絶対値 1：`PAG.Part258.normSq_phaseA1`。
    - U_N は複素共役と可換（KUK = U）：`PAG.Part258.UA1_star`。
    - 内積を保つ：`PAG.Part258.ip_UA1`。
- ノート：`pag2_thm26_A1_collation.md`、`pag2_part254_full_gluing.md`、CLAUDE.md §3。

**2.4 「射影」の変換と位相：反転（乗法の側）と加法の変換（加法の側）の合成。**
- 地位：
  - 読み（2026-11-18 19:01、著者が留保つきで採用）。
  - 著者の言葉は「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」。「反転と加法の変換の合成」は構築側の読みで、著者が 19:01 に留保つきで材料として採用した。著者の言葉「貼り合わせの合成」の貼り合わせは U（次の項）。
  - 「貼り合わせ」は U（ねじれた貼り合わせ）を指す（2026-11-19 06:36、著者の決定。`PAG.Part23.Compat`（ねじれのない座標の貼り合わせ）ではない）。
  - 標準の核は Hartley 核（著者の決定）。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは照合していない（JH_N の正規化も本文で確かめていない）。
- Lean（Part 252（PAG256）、［再導出］）：
  - 写像 `PAG.Part256.JH`、値 `PAG.Part256.rootNum`（= 𝔀）、偶奇の因子 `PAG.Part256.parFac`。
  - すべての指標で、単数の上の式：`PAG.Part256.JH_eq_rootNum_mul_any`。
  - 原始指標で絶対値 1：`PAG.Part256.normSq_rootNum`。
  - 原始指標で単数の外に漏れない：`PAG.Part256.hartley_eq_zero_of_not_isUnit`。
  - 原始性を外した反例：`PAG.Part256.removal_counterexample`・`PAG.Part256.removal_counterexample_normSq`・`PAG.Part256.removal_counterexample_four`。
- 留保：
  - `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。照合した範囲（PAG23・PAG26・PAG27・PAG256）では、P¹ のモデルと結ぶ Lean の文はない（鎖全体は検索していない）。
  - 原始指標で 𝔀 がルート数であることは Lean の外。
  - 素朴なフーリエ核 e(xy) では値が τ(χ)/√N で、奇の指標で i 倍ずれる。このずれは滑らかにしない。
- ノート：`pag2_part252_hartley_gluing.md`、`pag2_projection_material.md`、`pag2_prereg_projection.md`。

**2.5 原始部分の作用素 T とユニタリ性。**
- 地位：定理［再導出］（Part 253（PAG257））。
- Lean：
  - すべての指標で T χ = 𝔀(χ)χ：`PAG.Part257.TopL_charU`。
  - 原始部分の上でユニタリ：`PAG.Part257.unitary_Vprim`。
  - 原始指標で A1 の位相を課した任意の線形写像は、原始部分の上で T と同じ値をとる：`PAG.Part257.TopL_eq_of_A1`（ほぼ同語反復）。
- 留保：Part 253 では U を Lean で定義していない（仮定の形でだけ現れる）。U_N の定義は 2.6。
- ノート：`pag2_part253_primitive_operator.md`。

**2.6 法 N の境界ユニタリ U_N 全体と、代数的な帰納極限の上の U_∞。**
- 地位：定理［再導出］（Part 254（PAG258））。
- Lean：
  - 位相 `PAG.Part258.phaseA1` と U_N `PAG.Part258.UA1`。
  - 導手ごとの部分：`PAG.Part258.condPart_eq_map`。
  - 族の一意性：`PAG.Part258.UA1_family_unique`。
  - 帰納極限 `PAG.Part258.Lim`、その上の作用素 `PAG.Part258.Uinf`、一意性 `PAG.Part258.Uinf_unique`、内積の保存 `PAG.Part258.ipLim_Uinf`。
- 留保：
  - U_N は A1 の位相を定義として入れた作用素で、A1 は導かれていない。
  - 直和を 1 つの文にした定理はない。
  - `Lim` と Ẑ^× の上の局所定数関数との同一視、完備化 L²(Ẑ^×) は Lean の外。完備化は、読みとしては解像度が落ちる側の操作。
- ノート：`pag2_part254_full_gluing.md`。

**2.7 τ の素数冪の成分への分解と、互いに素な法の並びの形の指標についての 𝔀 の分解（交差項・符号つき。値のレベル）。**
- 地位：定理［既知（再導出）］（Part 256（PAG260）・Part 257（PAG261））。恒等式は原始性を使わない（原始的でない指標では 𝔀 は位相でないことがある：`PAG.Part256.removal_counterexample_normSq`・`PAG.Part256.removal_counterexample_four`。全称の文は Lean の外）。
- Lean：
  - 互いに素な 2 つの法：`PAG.Part260.rootNum_prodChar`・`PAG.Part260.parFac_prodChar`・`PAG.Part260.crossSign`。
  - 互いに素な法の並び：`PAG.Part261.rootNum_listChar_formII`・`PAG.Part261.parFac_listChar`。
  - 成分への分解とその一意性：`PAG.Part261.exists_listChar`・`PAG.Part261.listChar_injective`（並びの形で言う。法 n の形での一意性は文にしていない）。
  - すべての素数への τ の分解：`PAG.Part261.gaussSum_primeFactors`（τ の文で、𝔀 の文ではない）。
- Lean の外：
  - 原始指標で s = 1/2 のとき、形 (II) の素数ごとの因子は Tate の局所定数と、`parFac` は無限素点の局所定数 (−i)^a と値が一致する（値の一致で Lean の外。Part 257 では読みとして記録。文献照合ノートは PAG の量との対応に［再導出（小さい）］を付けている）。
  - この一致には、加法指標の規約 T と、イデール類指標の正規化 ω_q(q) = χ(q) の両方が要る。ω を χ̄ に対応させる規約では、積は 𝔀 の共役になる。
  - Part 257 で読みとして記録した（確信度：中〜高）ものを、2026-11-18 の文献照合で確かめ直した。確信度は、2026-11-19 06:36 の著者の判断で高とする（上の条件のもとでの値の一致として。Lean の外）。
  - 「局所因子」という語は読み。
- ノート：`pag2_part256_gluing_cross_term.md`、`pag2_part257_local_factor_decomposition.md`、`pag2_literature_ia_sign.md`。

**2.8 加法指標の規約は規約 T（Tate の学位論文の加法指標：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）。**
- 地位：著者の決定（2026-11-18 19:25）。基礎文書の標準とする。
- 書き方の規則：
  - 明示的な因子 i^{±a} が無限素点の局所定数であることは、規約によらない。
  - 符号 χ(−1) の置き場は規約による。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
  - 局所定数との一致を書くときは、イデール類指標の正規化（2.7）も併記する（出所：索引の照合者の指摘と Part 257 の冒頭の説明。CLAUDE.md §1 に正規化を足すことを 2026-11-19 06:36 に著者が承認した）。
- ノート：`pag2_literature_ia_sign.md`、CLAUDE.md §1。

**2.9 有限素点の側の代数 A_∞ と、射影の変換・貼り合わせの位相・無限素点の符号。A_∞ は、導手の区分けと小さい法（位相は N ∣ 24、符号は N ∣ 12）の場合を除いて、位相も符号も見ない（否定的な結果、数値と手計算）。**
- 地位：読みと否定的な結果（2026-11-19 夕方の関門、`pag2_projection_interaction_preregistration.md`）。新しい Lean はない。数値と盲検の手計算が一致した。Lean にしない推薦は、2026-11-19 17:17 に著者が「進めてください」で採った。
- 内容：
  - 単数の乗法 R_u・パリティ P = R_{−1}（無限素点の符号）・素数冪ごとの殻の反転の CRT の積 J は、どれも A_N と可換（可換子の側、イーデルの側）。読み：A_N = End(V_N)^{G_N}（G_N は 0 を固定し、すべての d ∣ N で合同関係を保つ置換の群）、可換子はその群環の像（二重可換子定理）。
  - 射影の変換 J∘H（2.4）は、A_N の上で D_s ↔ E_s の双対の自己同型として働く（J が可換なので Ad(JH) = Ad(H) = Ad(F)）。
  - フーリエは角の写像の系 φ（5.5）を 0 拡張の系 ψ（スケーリング、Bost–Connes の μ_n の型）に移す（F_M ι = V F_N。Pontryagin 双対）。
  - 単数の角 D_1 A_N D_1 は導手ごとの射影の張る可換代数。U_N はこれと可換だが、属するのは N ∣ 24（そのとき U_N = I）のときだけ。符号の単数への制限が属するのは N ∣ 12 のときだけ。P ∈ A_N も N ∣ 12 のときだけで、極限では、符号は N ∣ 12 のレベルの角の上でだけ A_∞ に入る（数値 139 組）。
  - したがって A_∞ は、貼り合わせの位相（A1）にも無限素点の符号にも、導手の区分け以外の制約を課さない。位相はガウス和（H の中）と公準 A1 から入る。
  - range(D_1) ∩ range(E_1) は原始指標の張る空間（2.5 の V_prim）で、J∘H はこれを保ち、そこでの制限が U_N の制限（2.5 のユニタリ性の構造上の理由づけ）。
- 素朴な一般化の失敗（第 6 の型）：法 N の殻ごとの反転 s·w ↦ s·w⁻¹（法 N/s）は、N = 10, 14, 15, … で A_N と可換でない。可換なのは素数冪ごとの反転の CRT の積。
- 書き方の規則：「A_∞ と射影の変換からルート数が出る」と書かない（円環の第 2 の型、注入→回収）。
- Lean（既にあるもの）：
  - 単数の乗法との可換：`PAG.Part218.shellAlg_comm_dil`。可換子 `PAG.Part224.fullComm`、可換子が可換 ⇔ N ∣ 12：`PAG.Part225.fullComm_commute_iff_dvd_twelve`。
  - フーリエ共役：`PAG.Part246.fourierConj_convL_geps`・`PAG.Part246.fourierConj_mulLeft_dind`。
  - 導手ごとの部分 `PAG.Part258.condPart`、原始部分 `PAG.Part257.Vprim`、`PAG.Part256.JH_eq_rootNum_mul`、U_N `PAG.Part258.UA1`。
- Lean の外：Hartley 変換と殻の反転 J による共役の文、F_M ι = V F_N、単数の角の記述、N ∣ 24・N ∣ 12 の判定。
- 対照群：関数体 F_p[t]/(t^e) でも同じ形（数値、p = 2, 3, 5）。判定の値（N ∣ 24 に当たるリスト）と位相の値は変わり、ℚ の値は Gauss の符号定理と i^a を無限素点の因子と読むこと（2.8 の規約 T）に依存する（照合者）。
- 文献：Bastian–Humphries（arXiv:2606.19095）、Bhattacharyya–Song（arXiv:0809.1052）、arXiv:2510.17118 の式 (2)（T(v) ⊆ End_{G_v}）、Martin–Tanaka の解説（arXiv:0811.2475）、Kim–Kim（arXiv:1108.4947）、Montgomery–Vaughan 第 9 章、Shirbisheh（arXiv:0808.1767）、Arledge–Laca–Raeburn（1997）。照合者の WebSearch・WebFetch による。MathSciNet・zbMATH は未実施。
- 推薦：Lean にしない。残余が空。
- ノート：`pag2_projection_interaction_preregistration.md`。

## 第 3 章　解像度と有効な姿（§1 の命題 3）

**3.1 定義文と、その置き方と読み。**
- 地位：
  - 定義文（著者の文面）：直線は解像度を落としたときに創発する有効な姿。解像度のパラメータは未決定。
  - 置き方（2026-11-13）：見方の選択として解釈の層に置く（著者側 Muse の決定）。
  - 08:41 の定義（2026-11-13、著者の原文）：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。」
  - 読み L1（2026-11-13 08:38 に著者が採った読み。構築側の案）：解像度は測る素点の集合。
- Lean：なし（数学の文ではない）。
- 書き方の規則（CLAUDE.md §1）：
  - 解像度を N・K・Λ と同一視しない。
  - 閉包・完備化に現れる連続体を「有効な姿」や目標として書かない。
  - 完備化（L²、ℝ、直積の位相）を使うときは、「解像度が落ちる側の操作と読む」と読みとして断る。極限は直極限の側（すべての素点を同時に測る側）で取る。
  - 「直線の創発」と書かない。命題 3 には「§1 の命題 3（解像度と有効な姿）」と参照で触れ、何がどう変わるかを数学の言葉で書く。
- ノート：`pag2_author_definition_0841.md`、`pag2_part255_resolution_discrete_limit.md`、CLAUDE.md §1。

**3.2 Part 250 の試み（ε-鎖による定式化）。**
- 地位：
  - 定式化は Claude の案 1・2 を、著者が 2026-11-11 に了承したもの（Part 250 のノートの記載。CLAUDE.md §2 は「著者が採用した案 1＋案 2」と書く。著者の定義そのものではない）。
  - 定理は［既知］（教科書の例の対数座標版）。否定的な結果を含む。
- Lean（Part 250（PAG254））：
  - 定義 `PAG.Part254.chainIn`。
  - ∞ の側は、どの ε > 0 でも任意の 2 点が鎖でつながる：`PAG.Part254.chainIn_dInf`。
  - p の側では「どの ε > 0 でもすべての 2 点がつながる」が成り立たない：`PAG.Part254.not_forall_chainIn_dP`。ε > 1 ではすべてつながる（ノートの記載）。
  - 稠密性 `PAG.Part254.dense_logSet`、等長性 `PAG.Part254.dInf_eq_dist`。
- 否定的な結果：
  - 「解像度を落とすと直線が現れる」は示せていない。ε-鎖の商は 1 点につぶれ、ℝ は完備化から現れ、しかも ℝ は定義に使われている。ε-鎖の商は Lean にしていない。
  - 08:41 の定義の後（Part 255）、完備化は「解像度が落ちる側」の操作と読み、Part 250 の照合の記録にあった向きの判断は取り下げた。
- ノート：`pag2_part250_resolution_emergence.md`、`pag2_part255_resolution_discrete_limit.md`。

## 第 4 章　解像度ごとの姿（設計についての定理 1）

**4.1 Part 255 の二分法：測る素点と、像の離散・稠密。**
- 地位：定理［既知（再導出）］。骨格は、証明の部品が S 単数定理・積公式・弱近似（既知）であることを明記するとしている。
- Lean（Part 255（PAG259））：
  - 有限の基礎 ⟨S⟩（S は素数の有限集合、T ⊆ S）での閾値：`PAG.Part259.threshold_iff`。
  - 測らない素数が 2 つ以上なら稠密：`PAG.Part259.dense_imgST_iff`。高々 1 つなら閉かつ離散：`PAG.Part259.isClosed_discrete_imgST`。
  - 位相の対比：
    - 直積の位相では、すべての素点の座標への像は稠密：`PAG.Part259.dense_rho_image`。
    - 有限素点の座標 `PAG.Part259.BoxCoord`（`Nat.Primes → ℤ`）に離散位相を入れると、像は閉かつ離散：`PAG.Part259.isClosed_discrete_rhoBox_image`（写像 `PAG.Part259.rhoBox`）。
    - 「すべての素点を同時に測る位相」は読み。log の成分は使わない。再照合 A2 の判定は「自明（位相の選び方でほぼ決まり、ほぼ同語反復に近い。確信度：高）」。
  - 対照群の自明な Lean 版：通約的な 2 つの対数の整数結合は離れる：`PAG.Part259.sep_of_commensurable`。
- 留保：
  - 守備範囲：ℚ_{>0} を基礎にすると、∞ を測るどの有限の解像度でも像は稠密になる（`PAG.Part259.dense_rho_image` から射影で直ちに出る。独立の Lean の文はない）。有限の解像度の中では、離散の側は有限の基礎 ⟨S⟩ でだけ起こる。すべての素点を離散位相で測ると、ℚ_{>0} でも像は閉かつ離散になる（`PAG.Part259.isClosed_discrete_rhoBox_image`）。
  - 二分法を 1 つの文にはしていない。直極限の位相と `BoxCoord` の同一視は Lean の外。
  - 閉包に現れる直線は、読みとしては解像度が落ちた印（08:41 の定義）。その直線が無限素点の座標であること、および対照群 𝔽_q(t) で直線が現れないこと（ノルムの像は q^ℤ）は、骨格の記述で、Lean の外。
- ノート：`pag2_part255_resolution_discrete_limit.md`。

## 第 5 章　有限レベルの代数の組み立て（設計についての定理 2）

**5.1 Part 258 の二分法：N ∣ M のとき、(i) 引き戻しと両立し、(ii) 殻を混ぜない（強い読み）単位的な代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、そのときに限る。**
- 地位：定理。
  - 存在の側（テンソル積）は［既知］（Hanaki–Kim–Maekawa の直積の定理。構築側は文献を開いていない。確信度：中〜高は Part 258 のノートの記載）。
  - 不存在の側は［新規候補（小さい）］（確信度：低〜中。2026-11-15 の著者側の判断）。
- Lean（Part 258（PAG262））：
  - 二分法：`PAG.Part262.exists_compatible_hom_iff`。
  - 存在 `PAG.Part262.exists_compatible_hom`、その写像 `PAG.Part262.shellLift`。
  - 不存在：`PAG.Part262.no_compatible_hom`。
- 留保：
  - 条件の番号に注意。殻を混ぜない条件は、PAG262 の docstring・Part 259・CLAUDE.md §2 の番号では (ii)、Part 258 のノートでは (3)。強い読み（写像の像が殻ごとの span に入る：φ(D_s) は D_t の、φ(E_s) は E_t の線形結合）は、Part 258 のノートでは「構築者の読みで、著者に確かめる事項」とされていた。2026-11-19 07:10 に著者が、Part 258 の定理が意味する条件として確定した。根拠は、2026-11-15 に強い読みの報告を受理したこと、事前登録の問いの鋭さと候補 3 の内容がこの読みに依存すること（CLAUDE.md §3）。弱い読みは将来の問いとして排除しない。
  - 答えの範囲の外：弱い読み、単位元を保たない写像、両立条件を別の形にした写像。
  - 対照群（盲検の申告で、未確認）の結果から、アーデル射影幾何に固有の内容としては数えない（Part 258 のノート）。
  - 文献照合（MathSciNet・zbMATH と、Hanaki–Kim–Maekawa・Bastian–Humphries の本文）が済むまで、外部で新規性として使わない。
  - 構築側で開ける範囲の文献照合（2026-11-19、`pag2_candidate3_literature_builder.md`）：Bastian–Humphries・Watanabe（arXiv:2305.19258）・Kim（arXiv:1109.1334）の本文に、商に沿った単位的な写像の記述は見つからなかった。Hanaki–Kim–Maekawa の本文は構築側の環境から取得できず、盲検の申告のまま。MathSciNet・zbMATH は著者側の作業として残る。
- ノート：`pag2_part258_beta_premise.md`、CLAUDE.md §3。

**5.2 Part 259：フーリエとの両立を足した一意性と、帰納系の添字。**
- 地位：定理。
  - 順序の性質は［既知］（ユニタリ約数、E. Cohen 1960）。
  - 一意性・非一意性・帰納系は［再導出（小さい）］。
- Lean（Part 259（PAG263））：
  - (i)(ii)(iii)（(iii) はフーリエとの両立）を満たす写像がちょうど 1 つある ⇔ gcd(N, M/N) = 1：`PAG.Part263.existsUnique_compatF_iff`。その写像の特定：`PAG.Part263.compatF_iff_eq_shellLift`。
  - (iii) を外すと一意でない場合がある：`PAG.Part263.not_existsUnique_compat`。Lean にあるのは、A_2 → A_{2b}（b > 1 は奇数）で捩れた写像 `PAG.Part263.twLift` がある場合だけ。
  - 標準の写像 `PAG.Part263.canon` は合成と両立する：`PAG.Part263.canon_comp`。
  - 添字の関係 `PAG.Part263.UDvd` は有向でない：`PAG.Part263.not_isDirected_udvd`。`UDvd N M` は Part 216（PAG220）の `PAG.Part220.InLayer N N M` と同値（N > 0。`PAG.Part263.udvd_iff_inLayer`。`InLayer` で c = d とした特別な場合）。
  - 無平方数の部分系の極限 `PAG.Part263.sqLim`。各段は単射で入る：`PAG.Part263.sqLim_of_injective`。
- 留保（Part 259 §2 の「併記する必要がある 3 点」と、その他）：
  - 無平方数の系は、極大な有向部分系のうち指数がすべて 1 の場合にすぎず、A_{p^k}（k ≥ 2）を含まない。
  - `sqLim` は ℂ 加群で、代数の構造と制限テンソル積との同型は Lean の外。
  - どの有向な部分系も、整除の順序で共終でない。したがって関数のレベルの極限 ℂ[ℚ/ℤ]（5.3）の代数版にはならない（初等的。Lean にしていない）。
  - a が奇数のときの一意性は、数値のみ。
  - gcd ≠ 1 で (i) と D の側だけを満たす写像があるかは、未確認（小さい数値では見つからなかった。証明ではない）。
  - 非単位的な角の写像では、上の「代数版にはならない」は当てはまらない（5.5。上の文は単位元を保つ写像についての文）。
- ノート：`pag2_part259_unitary_step_maps.md`、`pag2_R1_assessment.md`。

**5.5 角の写像（非単位的）：N ∣ M のとき、φ(S) = (N/M)·π^* ∘ S ∘ π_* は A_N を A_M に送る非単位的な代数準同型で、合成と恒等の法則を満たす（gcd(N, M/N) によらない）。**
- 地位：定理（Part 260（PAG264）、短期層、2026-11-19）。
  - ラベル：E 側の像は［既知］（商スキームのべき等元による角）、ほかは［再導出（小さい）］。
  - 対照群は ℤ/p^e の段に当たる場合（F_p[t]/(t^e)）に限って同じ文が成り立つ（数値。互いに素な段は試していない）。使うのは平行移動スキームの形式だけ（盲検の手計算）なので、アーデル射影幾何に固有の内容としては数えない。
- Lean（Part 260（PAG264））：
  - A_M に入る：`PAG.Part264.cornerOp_mem`。写像 `PAG.Part264.cornerHom`。
  - 生成元の像：`PAG.Part264.cornerOp_geps`（φ(E_s) = E_{(M/N)s}）、`PAG.Part264.cornerOp_one`（φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s）、`PAG.Part264.cornerOp_dind`。
  - 引き戻しと両立：`PAG.Part264.cornerOp_pull`。
  - 一意性：`PAG.Part264.existsUnique_corner`。条件は (a) 引き戻しとの両立と (b) φ(1) の値。(b) を外すと一意でない（照合者の手計算）。
  - 合成：`PAG.Part264.cornerHom_comp`。恒等の法則：`PAG.Part264.cornerHom_self`（2026-11-19 午後に追加）。合成と恒等の 2 法則で、正の整数の整除の順序の上の帰納系の法則が揃う。
  - N < M なら φ(1) ≠ 1：`PAG.Part264.cornerHom_one_ne_one`。
  - D 側の証人：`PAG.Part264.cornerOp_dind_not_mem_span`（(2,4)）。
- 留保：
  - 次のものは Lean の外。
    - 極限の具体形（Ẑ 上の局所定数関数への作用）。
    - 像が角全体であること（数値 111 組、三重正則性からの短い帰結の見込み）。
    - Bost–Connes の ρ との対応（6.3）。
  - D 側は殻の span に入らないので、5.1 の強い読みの外。これは素数冪の段に固有ではない（N < M のすべての s：数値 81 組）。
  - 極限は直極限（有限次元の代数の和集合）の側でとる。完備化は解像度が落ちる側の操作と読む（§1 の 08:41 の定義）。
  - 照合：独立照合、再照合、統合照合（恒等の法則と尾）。統合照合の後の直しは主張を狭める・明確にするものだけで、尾の台帳は空。
- 帰納系と極限（Part 261（PAG265）、短期層、2026-11-19 午後）：
  - 正の整数の整除の順序（Part 254 の `Lvl`）の上の `DirectedSystem`：`PAG.Part265.cornerSys_self`・`PAG.Part265.cornerSys_comp`。
  - 極限 `PAG.Part265.CornerLim`（Mathlib の一般の `DirectLimit`）は、非単位的な環の構造と ℂ のスカラー倍を持つ。
  - 各段は単射に入る：`PAG.Part265.ofCorner_injective`。
  - 局所的な単位元：1 元ごとが `PAG.Part265.exists_local_unit`、有限集合ごとが `PAG.Part265.exists_local_unit_finset`。べき等元 e_a は a について増大する（`PAG.Part265.ofCorner_one_le`）。
  - 左単位元はない：`PAG.Part265.not_exists_left_one`。
  - 局所的な単位元の文はどの直極限でも成り立つ一般論で、非単位的という内容を運ぶのは左単位元がないことだけ。その証明は素数冪の段を要らない見込み（手計算）。
  - 極限は直極限の側でとり、完備化は使っていない。
- 極限の具体形（読み。Lean の外。2026-11-19 午後の盲検の問いテスト、`pag2_limit_form_preregistration.md`）：
  - 極限は Ẑ 上の局所定数関数の空間 V_∞ に、完備化なしに忠実に作用する（照合者の手計算）。
  - 素点ごとに、局所の単位 e_1（定数への射影）に関する制限テンソル積 ⊗'_p に分かれる。Flath 型の当てはめ。角の写像が中国剰余定理と両立することは数値で 1098 回確かめた。
  - 文献：Flath（1979）、Deitmar（arXiv:1002.0475）、アデールの Schwartz–Bruhat 関数、Laca–Larsen–Neshveyev（arXiv:math/0609316、定理 3.2）。
  - 否定的な観察（照合者、確信度：中）：局所の代数は抽象的な代数としては p によらない見込みで、A_∞ に入る算術は素点が可算個あることだけ。無限素点・スケーリング・貼り合わせ U は A_∞ に現れない。
  - 残余がないので、Lean にしない（推薦）。
- 無限素点・スケーリング・貼り合わせ U との相互作用（読みと否定的な結果）：2.9。
- ノート：`pag2_pag264_corner_maps.md`、`pag2_pag265_corner_limit.md`、`pag2_gamma_corner_preregistration.md`、`pag2_limit_form_preregistration.md`。

**5.3 関数のレベルの帰納系。**
- 地位：定理（Lean）。ラベルは、この索引では確かめていない。
- Lean：
  - Part 197（PAG201）：
    - 引き戻し `PAG.Part201.pull`。
    - ハール正規化の保存 `PAG.Part201.zket_pull`（仮定：t の素因数がすべて M を割る）。
    - 法によらない定理 A `PAG.Part201.thmA_haar`（仮定：N の素因数がすべて d を割る。原始性）。
  - Part 202（PAG206）：
    - 引き戻しのフーリエ変換 `PAG.Part206.dft_pull_apply`。
    - 旧部分 = 引き戻しの像 `PAG.Part206.oldP_eq_self_iff`。
  - 単数の上の関数の帰納極限 `PAG.Part258.Lim`（2.6）。
- 留保：
  - 極限 ℂ[ℚ/ℤ] との同一視は骨格の記述で、この索引では Lean の文を確かめていない。
  - `PAG.Part201.thmA_haar` の docstring は、この文を「Ẑ 上の定理 A」と呼ぶ。CLAUDE.md §0 は「Ẑ 上の定理 A」を未完の大域の問いに挙げ、§4 は 2026-11-12 の棚卸し監査で既知の定理かその帰結と判定したと書いている。
- ノート：引き継ぎメモの項目 18・23。

**5.4 互いに素な段のテンソル積。**
- 地位：定理［既知］（直積スキームの一般定理 T(A×B) ≅ T(A)⊗T(B) の特別な場合）。
- Lean：
  - Part 228（PAG232）：`PAG.Part232.shellAlgTensorEquiv`、`PAG.Part232.leftHom`、`PAG.Part232.tensLift_injective`、`PAG.Part232.range_tensLift`。
  - Part 236（PAG240）：
    - 局所作用素 `PAG.Part240.locHom`。
    - 一般の族の文 `PAG.Part240.tensEquiv`（A_N に当てるには `PAG.Part240.crtMul_shellAlg`）。
    - 素数冪への分解 `PAG.Part240.ppEquiv`（これも A_N に当てるには `PAG.Part240.crtMul_shellAlg`）。
- 留保：Part 258 の `shellLift` の作用素は、`locHom` の k = 0 と同じ式（Lean ではつないでいない。第 12 の型）。
- ノート：引き継ぎメモの項目 49・57、CLAUDE.md §3。

## 第 6 章　位置づけ

**6.1 殻代数 A_N は Terwilliger 代数 T(0) そのもの。**
- 地位：［既知］（2026-11-07 の著者の定義照合）。定義からの等式で、T(0) を Lean で定義していないので Lean の定理ではない。
- Lean：A_N の定義 `PAG.Part218.shellAlg`（Part 214（PAG218））。
- 既知として扱う結果：
  - 素数冪の Wedderburn 分解と次元公式：Part 225–226（PAG229–PAG230）。
  - テンソル積分解：Part 228（PAG232）。
  - ⟨D_u, E_N⟩ の構造とフーリエ共役：Part 241–242（PAG245–PAG246）、確信度：中。
- 書き方の規則：構造が要るときは再証明せず、辞書経由で文献を引く。
- ノート：`pag2_terwilliger_dictionary.md`、CLAUDE.md §3。

**6.2 新規性の候補（未確定。断定しない）。**
- 候補 1：生成の分類。
  - 範囲は Part 245〜248（PAG249〜PAG252）。項目 66 の宣言が PAG249（Part 245）にあるため、CLAUDE.md §3 の「Part 246–248」を 2026-11-19 に著者の承認で訂正した。
  - 項目 66：`PAG.Part249.sumSub_eq_shellAlg_iff`。項目 68：`PAG.Part251.addEAlg_one_eq_shellAlg_iff`。完全な分類：`PAG.Part252.addEAlg_eq_shellAlg_iff_all`。
  - 新規候補として残る範囲は合成数の N（確信度：中）。評価は「小さいノートの水準」。
  - MathSciNet・zbMATH は未実施。ノートの言葉では「著者側か専門家への照会」をお願いしている。
  - ノート：`pag2_candidate1_generation_collation.md`、CLAUDE.md §3。
- 候補 3：Part 258 の不存在の側（5.1）。骨格は、その文献照合（MathSciNet・zbMATH）を著者自身の作業としている。
- かつての候補 2（定理 2.6 の提示形）は候補から外れた（2.3）。

**6.3 Bost–Connes との接続。**
- 地位（骨格の記述）：関数のレベルでは既知。T(0) の側に届くかは、方向 γ の文献照合の結果による。γ の文献照合は著者側の作業（CLAUDE.md §2）。
- 構築側で開ける範囲の照合（2026-11-19、`pag2_gamma_literature_builder.md`）：検索 5 回の範囲で、有限レベルの Bost–Connes と T(0) を結ぶ記述は見つからなかった（本文は開いていない。確信度：低〜中）。BC の有限レベルは群環 ℚ[ℤ/nℤ] の帰納系（関数のレベル、既知）。［観察］BC の帰納系は整除のすべての段を使うが、T(0) の側の単位的な写像は互いに素な段だけ（5.1・5.2）。MathSciNet・zbMATH は著者側に残る。
- 立て直しの結果（2026-11-19、Part 260（PAG264）、5.5）：BC の ρ_n（ρ_n(1) = μ_n μ_n^*）に倣った角の写像は、T(0) に非単位的な代数準同型として延びる（A_M に入ること・合成・一意性は Lean）。群環の側で ρ と一致することは数値で、Lean の外。盲検の手計算では、L²(Ẑ) の表現で T(0) の片側（D 側）が BC に対応し、もう片側（E 側）は BC の表現の外。Terwilliger 版の角の文と、BC と T(0) を結ぶ文献は見つからなかった（確信度：低〜中）。
- CLAUDE.md §2 には、有限レベル Bost–Connes に元の BC 系が対応する、という記載がある。
- ノート：CLAUDE.md §2。

**6.4 書かないこと。**
- CLAUDE.md §6 から：
  - リーマン予想へのアプローチと書くこと（スペクトルと零点の数え上げの不一致は確定事項）。
  - 既知の結果を新規と書くこと。
  - 著者の定義を、形式化済みの内容であるかのように書くこと。
  - A1 の導出。
  - 数値確認を証明と呼ぶこと。
- CLAUDE.md §1 から（2026-11-12 の著者の指示）：「直線の創発」という表現。

## §6 開いている点（文書に「開いている」と書くもの）

- **著者の確認待ち**：なし（2026-11-19 にすべて閉じた。「貼り合わせ」は U、Part 258 の条件は強い読み）。
- **著者側の作業**（担当は骨格と CLAUDE.md §2 の記載による）：
  - 方向 γ の文献照合（6.3）。構築側で開ける範囲は 2026-11-19 に済み、MathSciNet・zbMATH が残る。
  - 候補 3 の文献照合（5.1）。MathSciNet・zbMATH と、Hanaki–Kim–Maekawa の本文（構築側の環境から取得できない）が残る。
  - 候補 1 の MathSciNet・zbMATH（6.2。ノートの言葉では「著者側か専門家への照会」）。
- **Lean の外・数値のみで残るもの**：
  - 構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0}（1.2・1.3）。
  - 定理 2.6 の逆向き（2.2）。
  - A1 と定理 2.6 の両立を 1 つにした文（2.3）。
  - `Lim` の同一視と完備化 L²(Ẑ^×)（2.6）。
  - 局所定数との同定（2.7）。
  - 二分法の 1 つの文（4.1）。
  - `sqLim` の代数構造（5.2）。
  - a が奇数のときの一意性（5.2）。
  - (i) と D の側だけを満たす写像の有無（5.2）。
  - 角の写像の像が角全体であること、極限の具体形、Bost–Connes の ρ との対応（5.5・6.3）。
- **定式化の問い**：
  - 解像度の操作に、L1 を超える定式化が要るか。骨格の記述では、現時点では L1 と 08:41 の定義で文書は書ける。
  - 「射影」の、全素点を通した一つの構成（空間と作用素のレベル）としての定式化。値のレベルについては 2.7。

## §7 宣言名の確認の記録

- この索引に出る完全修飾名を機械的に取り出し、`PAG.PartM.name` ごとに PAGM.lean の宣言の行（`theorem`・`def`・`abbrev`・`structure`・`instance` など）を検索した。
  - スクリプトは `records/founding_index/check_names.py`、出力は `check_names.log`。
  - 第 1 版は 85 件、第 2 版は照合者の指摘で足したものを含めて 102 件で、すべて実在した。第 3 版も 102 件ですべて実在した（`udvd_iff_inLayer` が加わり、`InLayer` は引数つきの書き方になったので機械的な抜き出しから外れた。`PAG.Part220.InLayer` の実在は第 2 版で確認済み）。
- 「Part n（PAGm）」の併記がすべて m = n + 4 であることも、機械的に確かめた。
- 照合者に渡した宣言の docstring と形式文の抜き出しには、`records/founding_index/extract_decls.py` を使った。

## §8 照合の記録

- **第 1 回の独立照合**：
  - 第 1 版（`records/founding_index/before_index_v1.md`）を照合者 1 人に渡した。渡したのは、索引の全文、宣言の docstring と形式文（85 件）、引くノートの冒頭（各 45 行）、引き継ぎメモの該当項目、CLAUDE.md の全文。
  - 入力は `input_index.md`、依頼文は `request.md`、出力は `outputs/index_check_output.md`。所要は約 11 分。
- **結論**：宣言名はすべて実在した。指摘は次のとおり。
  - 形式文より強い見出し・文：10 件。
  - 地位・決定者・出所の違い：10 件。
  - 落としていた留保：14 件。
  - 宣言の当て方：8 件。
  - 番号・参照の誤り：8 件。最も重いのは、5.1 の「条件 (iii)」で、正しくは (ii)。
- **第 2 版で直したこと**：
  - 見出しを形式文の範囲に合わせた（1.3、2.7、5.1）。3.2・4.1・5.2 は本文の箇条を形式文の範囲に合わせた（第 3 版の注：統合照合の指摘で書き分けた）。
  - 記号 W と 𝔀 の注意を §0 に加えた。
  - 3.1 の規則を CLAUDE.md の文言どおりにし、08:41 の原文を全文で載せた。
  - 宣言を足した（2.3 の A1 の位相の側、2.7 の成分の一意性、4.1 の `dense_rho_image`・`sep_of_commensurable`、5.4 の `crtMul_shellAlg`・`ppEquiv`、6.2 の項目 66・68、5.3 の `Lim`、5.2 の `InLayer`・`canon`、§0 の `Wpt`。第 3 版の注：最後の 3 件は第 2 版の記録から抜けていた）。
  - 出所を書き分けた。骨格の記述（4.1 の部品、6.3、候補 3 の担当、「文書は書ける」）は骨格と明記した。決定者と時刻も直した（1.4、3.2）。
  - 留保を足した（2.3 の実性への帰着と近い先行、2.4 の未照合、2.6 の `Lim`、2.7 の ω の正規化、4.1 の守備範囲、5.1 の範囲の外と対照群、5.2 の 3 点、6.1 は Lean の定理ではないこと）。
  - 番号の併記と参照を直した（6.1・6.2、6.3 は §2 だけ、6.4 の出所）。
- **第 2 版の照合**：第 2 版は照合後の直しを照合にかけていない。直しは照合者の直し案に沿った狭め・書き分け・出所の明記と、足した宣言（実在は機械的に確認、§7）である。足した宣言の形式文は、照合者が「§B になく未確認」としたものを構築側が読んで当てた。たとえば `rootNum_inv`・`phaseA1_inv`・`UA1_star` の形式文は PAG258 の 363〜412 行で確かめた。次の統合照合の対象に含める。

- **統合照合（2026-11-19、第 3 版）**：第 2 版の差分を、前回の統合照合の後の直し（材料ノート・文献照合ノート・CLAUDE.md・概要・引き継ぎメモ）とあわせて照合者 1 人が照らした（記録 `records/tail_audit3/`、所要 約 12 分）。宣言 102 件と Part・PAG の対応は過不足なく一致した。形式文が偽・空虚・別物になったものはなかった。
  - 索引で直したこと：2.3（反転の条件の帰着と |𝔀| = 1 の条件を分けた）、2.7（見出しを形式文の範囲に、非原始指標の文に Lean の外と断った、局所定数との一致の地位）、2.8 の 3 つ目の規則の出所、4.1 の守備範囲（離散位相で測る場合と稠密の側の根拠）、2.4（構築側の読みの地位と、照合した範囲の限定）、5.2（`udvd_iff_inLayer` で同値と書いた）、5.3（`thmA_haar` の docstring と CLAUDE.md §4 の判定の併記）、2.2 の N ≥ 3、5.4 の `crtMul_shellAlg`、2.3 の番号の対応の根拠、3.2・5.1 の出所、§8 の記録。
  - 第 3 版の直しは、限定を足す・出所を書く・記録を事実に合わせる直しで、数学の主張を強めるものはない（補足 8 の「主張を変えない直し」。照合にはかけていない）。

- **著者の決定の記録（2026-11-19 06:36、第 4 版）**：「貼り合わせの合成」の貼り合わせは U（2.4、§6 の確認待ちから外した）。Part 257 の同定の確信度は高（2.7）。CLAUDE.md §3 の候補 1 の範囲は Part 245〜248 に訂正（6.2）。CLAUDE.md に足した ω の正規化は承認（2.8 の 3 つ目の規則の出所は、著者の承認を得た CLAUDE.md §1 の記載になった）。これは著者の決定の記録で、照合にはかけていない。

- **著者の確定の記録（2026-11-19 07:10、第 5 版）**：Part 258 の殻を混ぜない条件は強い読みで確定（5.1。§6 の確認待ちから外した）。弱い (ii)・非単位的な写像・別の両立条件は、従来の記録どおり主張の外の別の問いとして残る。CLAUDE.md §3 の候補 3（日英）にも記録した。著者の決定の記録で、照合にはかけていない。

## §C 差分に出る Lean の宣言（直前の docstring と形式文。定義は本体を含む）

### PAG.Part218.shellAlg_comm_dil（PAG218.lean）
```lean
/-- **5a.** A の元は U_a と可換。 -/
theorem shellAlg_comm_dil (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ shellAlg N)
    (a : (ZMod N)ˣ) (f : ZMod N → ℂ) : T (dil a f) = dil a (T f) :=
```

### PAG.Part224.fullComm（PAG224.lean）
```lean
/-- 空間全体の可換子 A′：すべての E_s = ε_s ⋆ と D_s = 1_{D_s}· と可換な線形変換。 -/
noncomputable def fullComm (N : ℕ) [NeZero N] : Submodule ℂ (Module.End ℂ (ZMod N → ℂ)) where
  carrier := {T | ∀ (s : ℕ) (f : ZMod N → ℂ),
    T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f) ∧ T (dind N s * f) = dind N s * T f}
  add_mem' := by
    intro T₁ T₂ h₁ h₂
    simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
    intro s f
    refine ⟨?_, ?_⟩
    · rw [LinearMap.add_apply, LinearMap.add_apply, (h₁ s f).1, (h₂ s f).1, ← PAG.Part15.convL_apply,
        ← PAG.Part15.convL_apply, ← PAG.Part15.convL_apply, map_add]
    · rw [LinearMap.add_apply, LinearMap.add_apply, (h₁ s f).2, (h₂ s f).2, mul_add]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    intro s f
    refine ⟨?_, ?_⟩
    · rw [LinearMap.zero_apply, LinearMap.zero_apply, ← PAG.Part15.convL_apply, map_zero]
    · rw [LinearMap.zero_apply, LinearMap.zero_apply, mul_zero]
  smul_mem' := by
    intro r T hT
    simp only [Set.mem_ofPred_eq] at hT ⊢
    intro s f
    refine ⟨?_, ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, (hT s f).1, ← PAG.Part15.convL_apply,
        ← PAG.Part15.convL_apply, map_smul]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, (hT s f).2, mul_smul_comm]
```

### PAG.Part225.fullComm_commute_iff_dvd_twelve（PAG225.lean）
```lean
/-- **4k. A′ が可換 ⇔ N ∣ 12**（step243 の (4) で数値だけだった読み取り）。 -/
theorem fullComm_commute_iff_dvd_twelve (N : ℕ) [NeZero N] :
    (∀ T ∈ fullComm N, ∀ T' ∈ fullComm N, Commute T T') ↔ N ∣ 12 :=
```

### PAG.Part246.fourierConj_convL_geps（PAG246.lean）
```lean
/-- **5b.** 𝓕 E_s 𝓕⁻¹ = D_s。 -/
theorem fourierConj_convL_geps (N s : ℕ) [NeZero N] :
    fourierConj N (PAG.Part15.convL (geps N s)) = LinearMap.mulLeft ℂ (dind N s) :=
```

### PAG.Part246.fourierConj_mulLeft_dind（PAG246.lean）
```lean
/-- **5c.** 𝓕 D_s 𝓕⁻¹ = E_s。 -/
theorem fourierConj_mulLeft_dind (N s : ℕ) [NeZero N] :
    fourierConj N (LinearMap.mulLeft ℂ (dind N s)) = PAG.Part15.convL (geps N s) :=
```

### PAG.Part256.JH_eq_rootNum_mul（PAG256.lean）
```lean
/-- χ が原始的なら、すべての単数 u で (H_N χ)(u⁻¹)/√N = W(χ)·χ(u)。式そのものは原始性なしで成り立つ
（`JH_eq_rootNum_mul_any`）。構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。
U と A1 は文に出てこない）。JH は ℤ/N の上の関数を単数の上の関数に送る写像で、同じ空間の上の固有値方程式ではない。 -/
theorem JH_eq_rootNum_mul {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u :=
```

### PAG.Part257.Vprim（PAG257.lean）
```lean
/-- 原始部分 V_prim：原始指標（を単数に制限したもの）が張る空間。 -/
noncomputable def Vprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.IsPrimitive} => charU χ.1)
```

### PAG.Part258.UA1（PAG258.lean）
```lean
/-- 法 N の A1 の境界ユニタリ U_N = Σ_χ phaseA1(χ)·P_χ。 -/
noncomputable def UA1 : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := ∑ χ : DirichletCharacter ℂ N,
    (phaseA1 χ * ip (charU χ) f / (Nat.totient N : ℂ)) • charU χ
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_add_right, mul_add, add_div, add_smul]
  map_smul' c f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_smul_right, smul_smul]
    congr 1
    ring
```

### PAG.Part258.condPart（PAG258.lean）
```lean
/-- 導手が q の指標が張る部分（法 N）。 -/
noncomputable def condPart (N : ℕ) [NeZero N] (q : ℕ) : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.conductor = q} => charU χ.1)
```

### PAG.Part264.cornerHom（PAG264.lean）
```lean
/-- **3d. 角の写像** A_N → A_M（単位元を保たない代数準同型、φ(S) = (N/M)·π^* ∘ S ∘ π_*）。 -/
noncomputable def cornerHom (h : N ∣ M) : shellAlg N →ₙₐ[ℂ] shellAlg M where
  toFun S := ⟨cornerOp h S, cornerOp_mem h S.2⟩
  map_smul' c S := Subtype.ext (show cornerOp h (c • (S : Module.End ℂ (ZMod N → ℂ))) = c • cornerOp h S from
    cornerOp_smul h c S)
  map_zero' := Subtype.ext (cornerOp_zero h)
  map_add' S T := Subtype.ext (cornerOp_add h S T)
  map_mul' S T := Subtype.ext (cornerOp_mul h S T)
```

### PAG.Part264.cornerHom_comp（PAG264.lean）
```lean

theorem cornerHom_comp {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) :
    (cornerHom h2).comp (cornerHom h1) = cornerHom (h1.trans h2) :=
```

### PAG.Part264.cornerHom_one_ne_one（PAG264.lean）
```lean
/-- **4d.** N < M なら φ は単位元を保たない。 -/
theorem cornerHom_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerHom h 1 ≠ 1 :=
```

### PAG.Part264.cornerHom_self（PAG264.lean）
```lean

theorem cornerHom_self : cornerHom (dvd_refl N) = NonUnitalAlgHom.id ℂ (shellAlg N) :=
```

### PAG.Part264.cornerOp_dind（PAG264.lean）
```lean
/-- **3b.** φ(D_s) = (π^*1_{D_s})·φ(1)（D 側の像は殻の掛け算と φ(1) の積）。 -/
theorem cornerOp_dind (h : N ∣ M) (s : ℕ) :
    cornerOp h (LinearMap.mulLeft ℂ (dind N s)) =
      LinearMap.mulLeft ℂ (pull h (dind N s)) * cornerOp h 1 :=
```

### PAG.Part264.cornerOp_dind_not_mem_span（PAG264.lean）
```lean
/-- **5.** (N, M) = (2, 4)：φ(D_2) は D_t の線形結合でない（Part 258 の強い読みの D 側を満たさない）。 -/
theorem cornerOp_dind_not_mem_span :
    cornerOp (show 2 ∣ 4 by norm_num) (LinearMap.mulLeft ℂ (dind 2 2)) ∉
      Submodule.span ℂ (Set.range fun u : ℕ => LinearMap.mulLeft ℂ (dind 4 u)) :=
```

### PAG.Part264.cornerOp_geps（PAG264.lean）
```lean
/-- **3a.** φ(E_s) = E_{(M/N)s}。 -/
theorem cornerOp_geps (h : N ∣ M) (s : ℕ) :
    cornerOp h (PAG.Part15.convL (geps N s)) = PAG.Part15.convL (geps M (M / N * s)) :=
```

### PAG.Part264.cornerOp_mem（PAG264.lean）
```lean
/-- **3c.** φ は A_N を A_M に送る（gcd(N, M/N) によらない）。 -/
theorem cornerOp_mem (h : N ∣ M) {S : Module.End ℂ (ZMod N → ℂ)} (hS : S ∈ shellAlg N) :
    cornerOp h S ∈ shellAlg M :=
```

### PAG.Part264.cornerOp_one（PAG264.lean）
```lean
/-- φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s。 -/
theorem cornerOp_one (h : N ∣ M) :
    cornerOp h 1 = ∑ s ∈ M.divisors.filter (fun s => M / N ∣ s), PAG.Part15.convL (geps M s) :=
```

### PAG.Part264.cornerOp_pull（PAG264.lean）
```lean
/-- **1b. 引き戻しと両立**：φ(S) π^* = π^* S。 -/
theorem cornerOp_pull (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) (f : ZMod N → ℂ) :
    cornerOp h S (pull h f) = pull h (S f) :=
```

### PAG.Part264.existsUnique_corner（PAG264.lean）
```lean
/-- **4a. 一意性**：引き戻しと両立し、φ(1) = Σ_{(M/N) ∣ s} E_s を満たす単位元を保たない代数準同型は φ だけ。 -/
theorem existsUnique_corner (h : N ∣ M) :
    ∃! φ : shellAlg N →ₙₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (pull h f) = pull h ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (φ 1 : Module.End ℂ (ZMod M → ℂ)) =
        ∑ s ∈ M.divisors.filter (fun s => M / N ∣ s), PAG.Part15.convL (geps M s) :=
```

### PAG.Part265.CornerLim（PAG265.lean）
```lean
/-- 角の写像の帰納極限（Mathlib の一般の `DirectLimit`。非単位的な環の構造と ℂ のスカラー倍を持つ）。 -/
abbrev CornerLim : Type := DirectLimit (fun a : Lvl => shellAlg a.val) cornerSys
```

### PAG.Part265.cornerSys_comp（PAG265.lean）
```lean
/-- 合成の法則：φ_{b,c} ∘ φ_{a,b} = φ_{a,c}。 -/
theorem cornerSys_comp {a b c : Lvl} (hab : a ≤ b) (hbc : b ≤ c) (S : shellAlg a.val) :
    cornerSys b c hbc (cornerSys a b hab S) = cornerSys a c (hab.trans hbc) S :=
```

### PAG.Part265.cornerSys_self（PAG265.lean）
```lean
/-- 恒等の法則：φ_{a,a} = id。 -/
theorem cornerSys_self (a : Lvl) (S : shellAlg a.val) : cornerSys a a le_rfl S = S :=
```

### PAG.Part265.exists_local_unit（PAG265.lean）
```lean
/-- **局所的な単位元**：極限のどの元 x にも、ある a があって、e_a = (φ(1_a) の像) は x = e_a x = x e_a を満たす。 -/
theorem exists_local_unit (x : CornerLim) :
    ∃ a : Lvl, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x :=
```

### PAG.Part265.exists_local_unit_finset（PAG265.lean）
```lean
/-- **局所的な単位元（有限集合版）**：極限の有限部分集合 F ごとに、べき等元 e_a があって、F のどの元も両側から固定する
（F ⊆ e_a·極限·e_a。局所的な単位元を持つ環の、有限集合についての定義の形）。 -/
theorem exists_local_unit_finset (F : Finset CornerLim) :
    ∃ a : Lvl, ∀ x ∈ F, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x :=
```

### PAG.Part265.not_exists_left_one（PAG265.lean）
```lean
/-- **大域の単位元はない**：極限には左単位元がない（非単位的）。 -/
theorem not_exists_left_one : ¬ ∃ u : CornerLim, ∀ x : CornerLim, u * x = x :=
```

### PAG.Part265.ofCorner_injective（PAG265.lean）
```lean
/-- 各段 A_a は極限に単射で入る。 -/
theorem ofCorner_injective (a : Lvl) : Function.Injective (ofCorner a) :=
```

### PAG.Part265.ofCorner_one_le（PAG265.lean）
```lean
/-- a ≤ b なら e_b e_a = e_a = e_a e_b。 -/
theorem ofCorner_one_le {a b : Lvl} (h : a ≤ b) :
    ofCorner b 1 * ofCorner a 1 = ofCorner a 1 ∧ ofCorner a 1 * ofCorner b 1 = ofCorner a 1 :=
```

## §D 引くノートの全文（2 本）

### §D-1 notes/pag2_limit_form_preregistration.md

# アーデル射影幾何 — 極限の具体形：着手前の 4 点（推薦案の素材、2026-11-19 午後）

（パートではない。Lean と xlsx は変えていない。数値は `records/limit_form/`。数値は証明ではない。）

## §0 問いの出所と内部照合

- **出所**：
  - Part 261（PAG265）の範囲の外に残った「極限の具体形（Ẑ 上の局所定数関数への作用）」。
  - §1 の 08:41 の定義（極限でも離散構造の観測を維持する、極限は直極限の側）と、命題 3 の置き方（素点たちは制限積の因子として並列に共存している全体が対象）に仕える。
  - 基礎文書の第 5 章（索引 5.5）の材料。
  - 2026-11-19 13:46 に著者が「進めてください」と言い、構築側が関門に通すことにした（着手の決定ではない）。
- **内部照合**（Lean の全宣言と記録を、言葉で検索した）：
  - 同じ型の先例は Part 254（PAG258）にある。単数の上の関数の引き戻しの帰納極限 `Lim`（Mathlib の `Module.DirectLimit`、添字 `Lvl`）と、その上の作用素 U_∞（`Uinf`）。その Part のノートは、`Lim` を Ẑ^× 上の局所定数関数の空間と同一視すること・完備化を、Lean の外の［既知］としていた。
  - ℤ/N の上の関数の帰納極限と、その上での角の写像の代数の作用は、鎖にない。
  - 制限テンソル積については、R1 の査定 §5（互いに素な段の部分系の極限）に読みがある（［既知］、Lean の外）。Part 259 の `sqLim` は、代数の構造と制限テンソル積との同型を Lean の外としている。

## §1 4 点

### (1) 幾何の言葉での問い

- すべての素点を同時に測る側の極限（Part 261 の `CornerLim`）は、完備化を使わずに、Ẑ 上の局所定数関数の空間 V_∞ に忠実に作用するか。V_∞ は V_N の引き戻しによる直極限で、離散構造の観測の空間にあたる。
- その作用は素点ごとに分かれるか。極限の代数は、素点 p ごとの局所の代数 A_{p^∞} の制限テンソル積になるか。制限テンソル積では、ほとんどすべての素点で局所の単位 e_1（定数関数への射影）をとる。
- 読み：素点たちが制限積の因子として並列に共存することを、代数の側で実現する問い。

### (2) 既存分野の言葉への翻訳

- **関数の側**：V_∞ = C_lc(Ẑ)（Bruhat–Schwartz 関数）≅ ⊗'_p C_lc(ℤ_p)。定数関数 1 に関する制限テンソル積で、標準の事実。
- **代数の側**：Flath 型の制限テンソル積分解（大域ヘッケ代数 ≅ ⊗' 局所ヘッケ代数、球関数のべき等元に関して）の型。
  - 部品は 2 つある。互いに素な法での T(0) のテンソル分解（Hanaki–Kim–Maekawa、Part 228（PAG232））と、直極限とテンソル積の交換。
- **作用の側**：Part 254 の U_∞ と同じ作り。S ∈ A_N をレベル M の関数に φ_{N,M}(S) として作用させる。well-defined なのは Part 260 の `cornerOp_pull` による。
- **Bost–Connes の側**：BC 系の素点ごとの分解が同じ型として挙がる見込み（盲検で確かめる）。

### (3) 残余

- **(a) 角の写像が中国剰余定理の分解と両立すること**：φ_{ab, a'b'} = φ_{a,a'} ⊗ φ_{b,b'}（a', b' が互いに素）。
  - 数値：1098 回の照合ですべて合った（`crt_corner_check.log`）。
  - 引き戻し・繊維の和・正規化がそれぞれ積に分かれることから、自動的に出る見込み（手計算）。
- **(b) V_∞ への作用の well-defined 性と忠実性**：Part 260・261 の文から短く出る見込み（手計算）。
- **(c) 制限テンソル積への分解**：(a) と直極限の一般論の組み合わせ。
- 局所の単位 e_1 = φ_{1,q}(1) は定数への射影 E^{(q)}_q と一致した（数値、q = 2, 4, 8, 16, 3, 9, 27, 5, 25）。
- **分類**：どれも既知の型の当てはめの見込みで、残余は計算の細部か空。§4 の規則では、新規パートではなく短期層か、始めない。

### (4) 対照群テスト

- **関数体**：F_q[t] の剰余環の系でも、同じ形で成り立つ見込み（中国剰余定理、素点はモニックな既約多項式）。数値は試していない。
- **Beurling の一般化素数**：有限レベルの環がないので立たない（適用外）。
- **扱い**：形式だけを使う文で、ℚ に固有の算術の内容はない。

## §2 予想（盲検の前に書いた）

`records/limit_form/expected_note.md`。

## §3 盲検の問いテスト

- **条件**：新しいエージェントに WebSearch・WebFetch だけを使わせた（ツール 48 回、約 726 秒）。依頼文は `records/limit_form/prompt_blind.md`、出力は `records/limit_form/outputs/blind_output.md`。
- **Q1（作用）**：作用は well-defined で忠実（確信度：高）。
  - D 側の像は「掛け算 × N 周期への射影」で、掛け算作用素そのもの（無限階）は極限に入らない。
  - E 側の像は、位数がちょうど d の指標の張る空間への射影 Π_d（階数 φ(d)）。
  - 極限は、Ẑ^× 不変な掛け算と Π_d たちが生成する単位的な代数の中で、有限階の部分（両側イデアル）に等しい（手計算、確信度：高）。
- **Q2（素点ごとの分解）**：A_∞ ≅ ⊗'_p (A_{p^∞}; e_1)、V_∞ ≅ ⊗'_p (V_{p^∞}; 1_{ℤ_p})。Flath の型の当てはめ（確信度：高）。
- **Q3（文献）**：同じ型の既知の結果がある。
  - Flath（1979）、Deitmar（arXiv:1002.0475）。
  - アデールの Schwartz–Bruhat 関数の制限テンソル積（Bump、Ramakrishnan–Valenza。未照合）。
  - Laca–Larsen–Neshveyev（arXiv:math/0609316、定理 3.2。Bost–Connes 型の固定点代数の素点ごとのテンソル積分解）。
  - Terwilliger 代数の帰納系・直極限・その ⊗' 分解を書いた文献は見つからなかった（確信度：低〜中）。
- **Q4（関数体）**：同じ理由で決まる（確信度：高）。
- **残余についての照合者の意見**：
  - Q1・Q2・Q4 に既知の当てはめで済まない残余はない。
  - 局所の代数 A_{p^∞} は、抽象的な代数としては p によらない見込み（確信度：中）。そうなら、A_∞ に入る算術は「素点の集合が可算個ある」ことだけで、p への依存は作用する空間 V_∞ の側（球の大きさ）にしか現れない。
  - 無限素点、ℚ_+^× によるスケーリング（Bost–Connes の μ_n）、貼り合わせ U は、A_∞ に一切現れない。残余を持つ問いは、⊗'_p の外にあるこれらとの相互作用を含める必要がある。
- **［観察］**（照合者の手計算、確信度：中〜高。Lean の外。この推薦の範囲では扱わない）：
  - A_N は、根付き p 分木の葉 0 を固定する自己同型の群の積 G_N と可換な作用素の全体 End(V_N)^{G_N} に等しい。次元の一致による（Bhattacharyya–Song の次元と、軌道の数え上げ）。
  - その系として、Part 260 で Lean の外に残した「像が角全体であること」が出る。
  - A_N は単数群 (ℤ/N)^× の可換子全体より小さい（N = 5 で 5 次元と 7 次元）。
- **予想との照合**（`expected_note.md`）：Q1〜Q4 とも予想どおり。予想になかったのは、(i) A_∞ には素点が可算個あること以外の算術が入っていないという観察、(ii) 中心化代数との一致、(iii) 残余は ⊗'_p の外にあるという意見。

## §4 推薦案（1 つ）

- **推薦**：極限の具体形は Lean にせず、新しいパートも短期層も始めない。基礎文書の材料（索引 5.5）に、読みと文献と照合者の観察を書くだけにする。
- **理由**：
  1. 残余が空。問いの中心（作用・素点ごとの分解・関数体）は、どれも既知の型（Flath、Schwartz–Bruhat、直極限とテンソル積の交換）の当てはめ。構築側の数値（1098 回）と照合者の手計算が一致している。§4 の規則では「残余が空の問いは始めない」。
  2. 対照群（関数体）でも同じ理由で成り立つ。
  3. 兆候 4（初等的な部品の組み合わせだけ）が続いている。残余のない Lean を足すより、ここで止めるほうが規則に合う。
  4. 照合者の観察（A_∞ には素点が可算個あること以外の算術が入っていない見込み）は、基礎文書にとって重要な否定的な結果。第 5 章で、角の写像の系がアーデル射影幾何に固有の内容を運ばないことを、根拠つきで書ける。
- **次に関門に通す候補**（推薦ではない。着手も決めていない）：
  - 照合者の意見に沿うと、残余のある問いは ⊗'_p の外にある。
  - 候補は、無限素点・ℚ_+^× のスケーリング・貼り合わせ U と、A_∞（有限素点・加法の側）との相互作用。
  - これは「射影」の読み（アデール幾何とイーデル幾何を射影によって融合する。§1）の章に直結する。
  - 関門に通すなら、4 点・盲検の問いテスト・対照群を最初からやり直す。

### §D-2 notes/pag2_projection_interaction_preregistration.md

# アーデル射影幾何 — 無限素点・スケーリング・貼り合わせ U と有限素点の側の代数 A_∞ の相互作用：着手前の 4 点（推薦案の素材、2026-11-19 夕方）

（パートではない。Lean と xlsx は変えていない。数値は `records/projection_interaction/`。数値は証明ではない。）

## §0 問いの出所と内部照合

- **出所**：
  - 極限の具体形の盲検（`pag2_limit_form_preregistration.md` §3）の照合者の意見：「残余を持つ問いは、⊗'_p の外にある無限素点・ℚ_+^× のスケーリング・貼り合わせ U との相互作用を含める必要がある」。
  - 基礎文書の第 2 章（索引 2.4「射影」の変換と位相、2.6 U_N と U_∞）と第 5 章（索引 5.5）をつなぐ材料。§1 の「射影」の読み（アデール幾何とイーデル幾何を射影によって融合する）に仕える。
  - 2026-11-19 15:47 に著者が「進めてください」と言い、構築側が関門に通すことにした（着手の決定ではない）。
- **内部照合**（Lean の全宣言を言葉で検索し、宣言を読んで確かめた）：
  - 単数の乗法との可換：`PAG.Part218.shellAlg_comm_dil`（PAG218）。パリティ P = R_{−1} はその特別な場合。
  - A_N の可換子：`PAG.Part224.fullComm`（Part 220、PAG224）とその次元 Σ_c m(c)²π(c)（`finrank_fullComm`）、可換子が可換 ⇔ N ∣ 12（`PAG.Part225.fullComm_commute_iff_dvd_twelve`）。根付き木の固定群 G_N による記述は鎖にない（極限の具体形の盲検の［観察］だけ）。
  - フーリエ共役で D_s と E_s が入れ替わる：`PAG.Part246.fourierConj_convL_geps`・`fourierConj_mulLeft_dind`（Part 242）。Hartley 変換による共役の文は鎖にない。
  - 導手ごとの部分：`PAG.Part258.condPart`（Part 254）。原始部分 `PAG.Part257.Vprim`。J∘H と原始指標：`PAG.Part256.JH_eq_rootNum_mul`（Part 252）。U_N：`PAG.Part258.UA1`。
  - 単数の上の反転：`PAG.Part256.JH` の中（u ↦ u⁻¹）と `PAG.Part253.globalInv`（単数の反転と実数の符号の組）。ℤ/N 全体の上の殻の反転は鎖にない。
  - 0 拡張の系 ψ：Part 260 の推薦案の数値（`records/gamma_corner/psi_corner.py`）だけで、Lean にない。

## §1 4 点

### (1) 幾何の言葉での問い

- 有限素点をすべて同時に測る側の観測の代数 A_∞（Part 261 の `CornerLim`。各段は A_N）に、次の 3 つはどう働くか。
  - 無限素点の符号（実数の ±1。有限レベルではパリティ P = R_{−1} として現れる）。
  - ℚ_+^× によるスケーリング（有限レベルでは単数 R_u と、レベルを変える 0 拡張 x ↦ kx）。
  - 貼り合わせ U と「射影」の変換 J∘H（反転と加法の変換の合成）。
- とくに：A_∞ は U の位相（A1）や無限素点の符号を「見る」か（制約を課すか）。

### (2) 既存分野の言葉への翻訳

- A_N = End(V_N)^{G_N}（G_N は gcd(x − y, N) を保つ置換の群、根付き木の葉 0 の固定群の積）。二重可換子定理で、A_N の可換子は G_N の群環の像。
  - R_u、P、素数冪ごとの殻の反転の CRT の積 J は G_N の元なので、A_N と可換。
- Hartley・フーリエ変換による共役は、円分スキームの形式的自己双対性（Terwilliger の D ↔ E の双対）。
- F_M ι = V F_N は Pontryagin 双対（Ẑ と ℚ/ℤ、射影 ℤ/M → ℤ/N と包含 (1/N)ℤ/ℤ ⊂ (1/M)ℤ/ℤ）の関手性。ψ は Bost–Connes 系の μ_n の型の等長作用素。
- range(D_1) ∩ range(E_1) = 原始指標の張る空間：原始性はガウス和が単数でない点で消えることと同値（古典）。

### (3) 残余

数値（`interaction_check.log`、N = 2〜36。`control_fqt_interaction.log`）：

| 項目 | 結果 |
|---|---|
| A_N と R_u・P の可換 | すべての N で成り立つ（Lean の `shellAlg_comm_dil` と一致） |
| 素数冪ごとの殻の反転の CRT の積 J | gcd(x − y, N) を保ち、A_N と可換。単数の上では u ↦ u⁻¹。J R_u = R_{u⁻¹} J |
| 法 N の殻ごとの反転 s·w ↦ s·w⁻¹（法 N/s） | N = 10, 14, 15, 18, … で A_N と可換でない（素朴な一般化の失敗、第 6 の型。素数冪ごとの反転の CRT の積と、p² のような因子でずれる） |
| H D_s H = E_s、H E_s H = D_s | すべての N |
| J∘H が A_N を正規化 | すべての N（J が可換なので、共役は D_s ↔ E_s の入れ替え） |
| F_M ι = V F_N | すべての組（k = 2, 3） |
| D_1 A_N D_1 の単数への制限 | 導手ごとの射影の張る可換代数（次元＝現れる導手の数、射影そのものが入る） |
| U_N と単数の角 | 可換。角に属するのは N = 2, 3, 4, 6, 8, 12, 24（単数群の指数が 2。U_N は恒等） |
| P の単数への制限と角 | 属するのは N = 2, 3, 4, 6, 12 |
| P ∈ A_N | N = 2, 3, 4, 6, 12（N ∣ 12。可換子が可換になる N で、`fullComm_commute_iff_dvd_twelve` と符合） |
| P_M φ_{N,M}(1) ∈ A_M（N ∣ M ≤ 36、139 組） | N ∣ 12 のとき、そのときに限る（`sign_corner_check.log`）。符号は、N ∣ 12 のレベルから引き戻した関数の角の上でだけ A_∞ に入る |
| range(D_1) ∩ range(E_1) | 次元＝原始指標の数。J∘H はこれを保つ |
| 対照群 F_p[t]/(t^e)（p = 2, 3, 5） | 可換・入れ替え・正規化・角の次元＝導手の数が同じ形。J∘F の位相は原始指標の間で変わり、角に属さない（e が小さい場合を除く） |

- 分類：
  - (a) 可換子の側（R_u、P、J）と、双対の自己同型（J∘H）：既知の型の当てはめ。
  - (b) A_∞ は U の位相と無限素点の符号に、導手の区分け（Part 254 の `condPart`）以外の制約を課さない。導手が同じ指標の間で位相を自由に変えても、A_∞ とは可換のまま。
  - (c) スケーリングは、フーリエで角の写像の系 φ と 0 拡張の系 ψ が入れ替わる形で現れる（Pontryagin 双対）。
- **円環の検知（第 2 の型）**：依存表。
  - U の位相（ルート数）の入力は、H の中のガウス和（`JH_eq_rootNum_mul`）と、それをモノグラフ層の境界ユニタリに同一視する公準 A1。A_∞ は入力に入っていない。
  - 除去テスト：A1 を外すと、U の位相は導手の区分けの中で自由になり、A_∞ との可換は残る。A_∞ は A1 を選ばない。
  - したがって「A_∞ と射影の変換からルート数が出る」と書けば、注入→回収になる。
- **結論**：残余は空。どれも既知の型の当てはめで、§4 の規則では始めない。否定的な結果（A_∞ は貼り合わせの位相も無限素点の符号も見ない）は、基礎文書の材料として価値がある。

### (4) 対照群テスト

- 関数体 F_p[t]/(t^e)：同じ形で成り立つ（数値、p = 2, 3, 5、e ≤ 4）。
- Beurling の一般化素数：有限レベルの環がないので立たない（適用外）。
- 扱い：形式の文で、ℚ に固有の算術はない。ℚ に固有に残るのは、無限素点の符号が実数の順序から来ること（関数体の無限素点は非アルキメデス的）だけで、その符号も A_∞ には見えない。

## §2 予想（盲検の前に書いた）

`records/projection_interaction/expected_note.md`。

## §3 盲検の問いテスト

- **条件**：新しいエージェントに WebSearch・WebFetch だけを使わせた（ツール 35 回、約 962 秒）。依頼文は `records/projection_interaction/prompt_blind.md`、出力の全文は `outputs/blind_output.md`、条件は `outputs/blind_meta.txt`。
- **答え**（すべて構築側の数値と一致した。照合者は数値を使っていない）：
  - Q1：R_u・P・J は A_N と可換（確信度：高）。J は 0 を固定するスキームの自己同型。A_N = End_{G_0}(V_N)（G_0 は 0 を固定し、すべての d ∣ N で合同関係を保つ置換の群。確信度：中〜高）。可換子は A_N' = ⊗_p A_{p^e}'、A_{p^e}' ≅ ℂ ⊕ ⊕_{c=1}^{e} M_{n_c(p)}(ℂ)^{⊕(e−c+1)}。A_N' = span{R_u} ⇔ N ∣ 12（手計算。鎖の `fullComm_commute_iff_dvd_twelve`（可換子が可換 ⇔ N ∣ 12）と同じ型で、同じ文ではない）。
  - Q2：H = F(Π_+ + iΠ_−)、H D_s H = E_s、H E_s H = D_s、H² = I。A_N の上で Ad(JH) = Ad(H) = Ad(F)（確信度：高）。
  - Q3：単数の角は導手ごとの射影 Π_f（f ∣ N、f ≢ 2 (mod 4)）の張る代数。U_N は常に可換で、角に属するのは N ∣ 24 のとき、そのときに限り、そのとき U_N = I（Gauss の符号の決定と、導手 p ≥ 5・9・16 での手計算。確信度：中〜高）。P の単数への制限は N ∣ 12 のときに限り角に属する。
  - Q4：F_M ι = V F_N。φ と ψ は Bost–Connes の共変関係 ρ_n をフーリエ変換で入れ替わる 2 つの見方（φ は平行移動の側、ψ は乗法作用素の側で μ_n の型。確信度：中〜高）。
  - Q5：range(D_1) ∩ range(E_1) は原始指標の張る空間（次元 φ*(N)、N ≡ 2 (mod 4) なら 0）。JH はこれを保ち、そこでの制限は U_N の制限と一致する（確信度：高）。
  - Q6：関数体でも Q1・Q2・Q4・Q5 と Q3 の判定の形は同じ。ただし「N ∣ 24」に当たるリストと位相の値は変わる。ℚ の値は Gauss の符号定理と、i^a を無限素点の因子と読むことに依存する。
  - Q7：照合した範囲で新しい数学の内容は見つからなかった（確信度：中。不存在の証明ではない）。文献に見つからなかったのは 4 つの短い計算（(1) 円分スキームの三重推移性・可換子の明示・N ∣ 12 の判定、(2) U_N ∈ 角 ⇔ N ∣ 24、P ∈ 角 ⇔ N ∣ 12、(3) φ と ψ を ρ_n の 2 つの見方として並べる整理、(4) D_1V ∩ E_1V の上で JH = U_N）で、評価は「せいぜい小さいノートの水準」。
  - 照合者の注意：U_N は A_N の角には（U_N = I の場合を除いて）入らず、可換子の側（単数群の群環）に属する。「A_N から U_N が出た」と読むと、ルート数を外から入れたものの読み替えになる。
- **予想との照合**（`expected_note.md`）：Q1〜Q6 とも予想どおり。予想になかったのは、(i) 可換子の明示の形と A_N' = span{R_u} ⇔ N ∣ 12、(ii) Q3 の判定の値（N ∣ 24、N ∣ 12）が関数体では変わり、ℚ では無限素点の因子 i^a の読みに依存するという指摘、(iii) Q5 の次元の式。
- 文献の照合の範囲：照合者の WebSearch 約 20 回・WebFetch 約 15 回。MathSciNet・zbMATH は未実施。Bost–Connes の有限レベルの検索は浅い（照合者の申告）。

## §4 推薦案（1 つ）

- **著者の決定**：2026-11-19 17:17、著者が「進めてください」と言い、この推薦（Lean にしない、記録だけ、構築側はこの線で新しい問いを開かない）が採られた。

- **推薦**：この相互作用は Lean にせず、新しいパートも短期層も始めない。基礎文書の材料（索引の第 2 章に新しい項目 2.9、第 5 章 5.5 から参照）に、読みと否定的な結果と文献を書くだけにする。あわせて、構築側からこの線（角の写像の系 A_∞ のまわり）で新しい問いを関門に通すのは、ここで止める。
- **理由**：
  1. 残余が空。Q1〜Q6 の核はどれも既知の型（Terwilliger 代数の構造と固定群、二重可換子定理、形式的自己双対性、原始指標のガウス和、Pontryagin 双対と Bost–Connes）の当てはめ。文献にない 4 つは短い計算で、§4 の規則では短期層に当たるが、どれも基礎文書の定義層に新しい内容を足さない（(4) は Part 253 の原始部分でのユニタリ性の構造上の理由づけで、ユニタリ性そのものは Lean にある）。
  2. 対照群（関数体）でも同じ形。ℚ に固有に残るのは判定の値（N ∣ 24・N ∣ 12）だけで、その中身は U_N = I・符号が角の上で偶奇を混ぜないという自明な場合。
  3. 円環の第 2 の型の検知：U の位相（ルート数）は H のガウス和と公準 A1 から入り、A_∞ は導手の区分け以外の制約を課さない。Lean にしても「A_∞ が A1 を選ぶ」ことは出ず、出るように書けば注入→回収になる。
  4. 否定的な結果そのものが基礎文書に要る：有限素点の側の観測の代数 A_∞ は、貼り合わせの位相（A1）も無限素点の符号も、導手の区分けと N ∣ 12（符号）・N ∣ 24（位相）の自明な場合を除いて見ない。それらは可換子の側（単数群と殻の反転 J の側、イーデルの側）にある。射影の変換 JH は A_∞ に D_s ↔ E_s の双対として働き、フーリエは角の写像の系 φ を 0 拡張の系 ψ（スケーリング）に移す。第 2 章の「射影による融合」を、加法の側の代数とイーデルの側の可換子の対として書ける。
  5. 兆候 4 が続いている。極限の具体形に続いて、残余のない 2 回目の関門。有限レベルの代数のまわりで残余のある問いを構築側で見つけられていない、という事実を記録する。
- **構築側で次に開ける問いについての正直な見立て**（推薦ではない）：残余のある問いは、公準 A1 を通るか（位相の選択。公準のまま）、完備化を通る（無限素点の連続な側。08:41 の定義では解像度が落ちる側の操作）かのどちらかに見え、どちらも有限レベルの Lean の問いとしては立たない。構築側は新しい問いを開かず、著者側の起草（第 1・2・5 章）から材料や照合の依頼が来たときに応える側に回ることを提案する。

## §E 数値の記録（スクリプトとログ）

### records/projection_interaction/interaction_check.py
```
"""無限素点・スケーリング・貼り合わせ U と、有限素点の側の代数 A_N の相互作用（着手前の見込み確認。数値。証明ではない）。2026-11-19。

記号：V_N = ℤ/N 上の関数。A_N = ⟨D_s, E_s⟩（Part 214 の shellAlg）。R_u f(x) = f(ux)（Part 218 の dil）。
P = R_{-1}（パリティ、無限素点の符号）。H = 離散 Hartley 変換/√N（核 cas(2πxy/N)）。F = フーリエ（e(−kx/N)/√N）。
J = 殻ごとの反転：x = s·w（s = gcd(x, N)、w は法 N/s の単数）↦ s·w⁻¹（w⁻¹ は法 N/s）。
U_N = Σ_χ phaseA1(χ)·P_χ（Part 254 の UA1、単数の上の関数）。phaseA1(χ) = rootNum(χ の原始指標)。
"""
import math, sys, cmath
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
from corner_check import A, orth_basis, in_span, divisors, iota, vemb, fourier

def units(N): return [x for x in range(N) if math.gcd(x, N) == 1] if N > 1 else [0]

def Rmat(N, u):
    R = np.zeros((N, N), dtype=complex)
    for x in range(N): R[x, (u * x) % N] = 1.0   # (R f)(x) = f(ux)
    return R

def hartley(N):
    return np.array([[math.cos(2*math.pi*x*y/N) + math.sin(2*math.pi*x*y/N) for y in range(N)] for x in range(N)], dtype=complex) / math.sqrt(N)

def factor(N):
    f, n, p = {}, N, 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def local_inv(q, x):
    """ℤ/q（q = p^e）の殻ごとの反転：p^k w ↦ p^k w⁻¹。"""
    if x % q == 0: return 0
    s = math.gcd(x, q); m = q // s
    return (s * pow((x // s) % m, -1, m)) % q

def crt(res):
    x, M = 0, 1
    for q, r in res:
        t = ((r - x) * pow(M, -1, q)) % q; x += M * t; M *= q
    return x % M

def shell_inv(N, naive=False):
    """naive = True：法 N の殻ごとの反転 s·w ↦ s·w⁻¹（法 N/s）。False：素数冪ごとの反転の CRT の積。"""
    J = np.zeros((N, N), dtype=complex); img = {}
    qs = [p ** e for p, e in factor(N).items()]
    for x in range(N):
        if naive:
            s = math.gcd(x, N); m = N // s
            y = 0 if m == 1 else (s * pow((x // s) % m, -1, m)) % N
        else:
            y = crt([(q, local_inv(q, x % q)) for q in qs]) if N > 1 else 0
        img[x] = y; J[x, y] = 1.0  # (J f)(x) = f(J x)
    return J, img

def comm_all(B, X, N):
    return all(np.allclose(B[:, i].reshape(N, N) @ X, X @ B[:, i].reshape(N, N)) for i in range(B.shape[1]))

def normalizes(B, X, N):
    Xi = np.linalg.inv(X)
    return all(in_span(B, X @ B[:, i].reshape(N, N) @ Xi) for i in range(B.shape[1]))

def characters(N):
    """(ℤ/N)^× の指標を、R_u の同時対角化で求める（値の辞書 u ↦ χ(u)）。"""
    U = units(N); n = len(U)
    if n == 1: return [{U[0]: 1.0}]
    idx = {u: i for i, u in enumerate(U)}
    rng = np.random.default_rng(1)
    c = rng.normal(size=n) + 1j * rng.normal(size=n)
    Mx = np.zeros((n, n), dtype=complex)
    for k, a in enumerate(U):
        for u in U: Mx[idx[u], idx[(a * u) % N]] += c[k]
    w, V = np.linalg.eig(Mx)
    chars = []
    for j in range(n):
        v = V[:, j] / V[idx[1], j]
        chars.append({u: v[idx[u]] for u in U})
    return chars

def conductor(N, chi):
    for d in divisors(N):
        if all(abs(chi[u] - 1) < 1e-8 for u in chi if (u - 1) % d == 0): return d
    return N

def root_num_prim(N, chi):
    f = conductor(N, chi)
    # 法 f の原始指標：法 f の単数 y に、y ≡ u (mod f) となる法 N の単数 u をとる
    prim = {}
    for u in chi: prim.setdefault(u % f, chi[u])
    tau = sum(prim[y] * cmath.exp(2j*math.pi*y/f) for y in prim) if f > 1 else 1.0
    even = abs(prim.get(f - 1 if f > 1 else 0, 1.0) - 1) < 1e-8
    return tau / ((1 if even else 1j) * math.sqrt(f)), f, even

def run(Nmax):
    rep = {k: [] for k in ['Jnaive_comm', 'R_comm', 'P_comm', 'P_in_A', 'J_iso', 'J_comm', 'J_in_A', 'J_in_dil', 'JR', 'H_swap', 'JH_norm',
                           'Fphi_psi', 'corner_dim', 'U_comm_corner', 'U_in_corner', 'Pu_in_corner', 'Vprim', 'JH_Vprim']}
    for N in range(2, Nmax + 1):
        B, D, E = A(N); dvs = divisors(N)
        Rs = {u: Rmat(N, u) for u in units(N)}
        P = Rmat(N, N - 1)
        rep['R_comm'].append((N, all(comm_all(B, R, N) for R in Rs.values())))
        rep['P_comm'].append((N, comm_all(B, P, N)))
        rep['P_in_A'].append((N, in_span(B, P)))
        Jn, _ = shell_inv(N, naive=True)
        rep['Jnaive_comm'].append((N, comm_all(B, Jn, N)))
        J, img = shell_inv(N)
        rep.setdefault('J_units_inv', []).append((N, all(img[u] == pow(u, -1, N) for u in units(N)) if N > 1 else True))
        rep['J_iso'].append((N, all(math.gcd(img[x] - img[y], N) == math.gcd(x - y, N) for x in range(N) for y in range(N))))
        rep['J_comm'].append((N, comm_all(B, J, N)))
        rep['J_in_A'].append((N, in_span(B, J)))
        dilB = orth_basis(list(Rs.values()))
        rep['J_in_dil'].append((N, in_span(dilB, J)))
        rep['JR'].append((N, all(np.allclose(J @ Rs[u], Rs[pow(u, -1, N)] @ J) for u in units(N))))
        H = hartley(N)
        rep['H_swap'].append((N, all(np.allclose(H @ D[s] @ H, E[s]) and np.allclose(H @ E[s] @ H, D[s]) for s in dvs)))
        rep['JH_norm'].append((N, normalizes(B, J @ H, N)))
        # F φ F⁻¹ = ψ(F · F⁻¹)（M = N·k、k ≤ 3）
        ok = True
        for k in (2, 3):
            M = N * k
            if M > Nmax: continue
            FN, FM = fourier(N), fourier(M); I, V = iota(N, M), vemb(N, M)
            ok &= np.allclose(FM @ I, V @ FN)
        rep['Fphi_psi'].append((N, ok))
        # 単数の角：D_1 A_N D_1 を単数の上の関数に制限
        Ui = units(N)
        S = np.zeros((N, len(Ui)), dtype=complex)
        for j, u in enumerate(Ui): S[u, j] = 1.0
        cor = orth_basis([S.T @ B[:, i].reshape(N, N) @ S for i in range(B.shape[1])])
        chars = characters(N)
        conds = sorted({conductor(N, c) for c in chars})
        rep['corner_dim'].append((N, cor.shape[1], len(conds)))
        # U_N = Σ phase(χ) P_χ（単数の上）。P_χ = χ χ^* / φ(N)（関数 χ(u) をベクトルに）
        phi = len(Ui)
        Umat = np.zeros((phi, phi), dtype=complex); Pu = np.zeros((phi, phi), dtype=complex)
        for c in chars:
            v = np.array([c[u] for u in Ui]); Pc = np.outer(v, v.conj()) / phi
            w, f, even = root_num_prim(N, c)
            Umat += w * Pc; Pu += (1 if even else -1) * Pc
        Pd = {}
        for c in chars:
            v = np.array([c[u] for u in Ui]); d = conductor(N, c)
            Pd[d] = Pd.get(d, 0) + np.outer(v, v.conj()) / phi
        rep.setdefault('corner_eq_condproj', []).append((N, all(in_span(cor, X) for X in Pd.values()) and cor.shape[1] == len(Pd)))
        rep['U_comm_corner'].append((N, all(np.allclose(cor[:, i].reshape(phi, phi) @ Umat, Umat @ cor[:, i].reshape(phi, phi)) for i in range(cor.shape[1]))))
        rep['U_in_corner'].append((N, in_span(cor, Umat)))
        rep.setdefault('U_is_identity', []).append((N, np.allclose(Umat, np.eye(phi))))
        rep['Pu_in_corner'].append((N, in_span(cor, Pu)))
        # V_prim = range(D_1) ∩ range(E_1)：次元 = 原始指標の数
        Q = D[1] @ E[1] @ D[1]
        ev = np.linalg.eigvalsh((Q + Q.conj().T) / 2)
        dim_int = int((ev > 1 - 1e-8).sum())
        nprim = sum(1 for c in chars if conductor(N, c) == N)
        rep['Vprim'].append((N, dim_int, nprim))
        # JH は range(D_1) ∩ range(E_1) を保つ
        W = np.linalg.eigh((Q + Q.conj().T) / 2)[1][:, ev > 1 - 1e-8]
        X = J @ H @ W
        rep['JH_Vprim'].append((N, W.shape[1] == 0 or np.allclose(W @ (W.conj().T @ X), X)))
    return rep

if __name__ == '__main__':
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    rep = run(Nmax)
    for k, v in rep.items():
        if k in ('corner_dim', 'Vprim'):
            bad = [t for t in v if t[1] != t[2]]
            print(f'{k}: 組 {len(v)}、不一致 {bad}')
        elif k in ('P_in_A', 'J_in_A', 'J_in_dil', 'U_in_corner', 'Pu_in_corner', 'U_is_identity'):
            print(f'{k}: 真となる N = {[n for n, b in v if b]}')
        else:
            print(f'{k}: 偽となる N = {[n for n, b in v if not b]}（{len(v)} 個）')
```

### records/projection_interaction/interaction_check.log
```
Jnaive_comm: 偽となる N = [10, 14, 15, 18, 20, 21, 22, 26, 28, 30, 33, 34, 35, 36]（35 個）
R_comm: 偽となる N = []（35 個）
P_comm: 偽となる N = []（35 個）
P_in_A: 真となる N = [2, 3, 4, 6, 12]
J_iso: 偽となる N = []（35 個）
J_comm: 偽となる N = []（35 個）
J_in_A: 真となる N = [2, 3, 4, 6, 8, 12, 24]
J_in_dil: 真となる N = [2, 3, 4, 6, 8, 12, 24]
JR: 偽となる N = []（35 個）
H_swap: 偽となる N = []（35 個）
JH_norm: 偽となる N = []（35 個）
Fphi_psi: 偽となる N = []（35 個）
corner_dim: 組 35、不一致 []
U_comm_corner: 偽となる N = []（35 個）
U_in_corner: 真となる N = [2, 3, 4, 6, 8, 12, 24]
Pu_in_corner: 真となる N = [2, 3, 4, 6, 12]
Vprim: 組 35、不一致 []
JH_Vprim: 偽となる N = []（35 個）
J_units_inv: 偽となる N = []（35 個）
corner_eq_condproj: 偽となる N = []（35 個）
U_is_identity: 真となる N = [2, 3, 4, 6, 8, 12, 24]
```

### records/projection_interaction/sign_corner_check.py
```
"""無限素点の符号 P = R_{−1} は、角 φ_{N,M}(1) の上で A_M に入るか（数値。証明ではない）。2026-11-19。
P_M φ_{N,M}(1) ∈ A_M となる (N, M)（N ∣ M、M ≤ 36）を数え、N ∣ 12 と一致するかを見る。"""
import sys
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/projection_interaction')
from corner_check import A, in_span, divisors, iota
from interaction_check import Rmat
bad = []; n = 0
for M in range(2, 37):
    BM, _, _ = A(M); PM = Rmat(M, M - 1)
    for N in divisors(M):
        I = iota(N, M); Q = I @ I.conj().T
        inA = in_span(BM, PM @ Q); n += 1
        if inA != (12 % N == 0): bad.append((N, M, inA))
print(f'組 {n}、「P_M φ(1) ∈ A_M ⇔ N ∣ 12」の不一致 {bad}')
```

### records/projection_interaction/sign_corner_check.log
```
組 139、「P_M φ(1) ∈ A_M ⇔ N ∣ 12」の不一致 []
```

### records/projection_interaction/control_fqt_interaction.py
```
"""対照群（関数体）：R = F_p[t]/(t^e) で、相互作用の各項目が同じ形で成り立つか（数値。証明ではない）。2026-11-19。
A_R：R^× の軌道（殻）の指示関数の掛け算 D と、双対殻への射影 E が生成する代数（records/gamma_corner/control_fqt.py と同じ構成）。
J：殻ごとの反転 t^k w ↦ t^k w⁻¹。F：加法指標 ψ_a(x) = exp(2πi λ(ax)/p)（λ = t^{e-1} の係数）によるフーリエ。
"""
import itertools, sys, cmath, math
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
from corner_check import orth_basis, in_span

def ring(p, e):
    els = list(itertools.product(range(p), repeat=e))
    idx = {x: i for i, x in enumerate(els)}
    def mul(x, y):
        z = [0] * e
        for i in range(e):
            for j in range(e - i):
                z[i + j] = (z[i + j] + x[i] * y[j]) % p
        return tuple(z)
    units = [x for x in els if x[0] % p != 0]
    return els, idx, mul, units

def alg(p, e):
    els, idx, mul, units = ring(p, e)
    n = len(els)
    F = np.array([[np.exp(2j * np.pi * mul(a, x)[e - 1] / p) for x in els] for a in els]) / np.sqrt(n)
    seen, orbs = set(), []
    for x in els:
        if x in seen: continue
        o = {mul(u, x) for u in units}; seen |= o; orbs.append(sorted(idx[y] for y in o))
    D = [np.diag([1.0 if i in o else 0.0 for i in range(n)]).astype(complex) for o in orbs]
    E = [F.conj().T @ np.diag([1.0 if i in o else 0.0 for i in range(n)]) @ F for o in orbs]
    G = D + E
    B = orth_basis([np.eye(n, dtype=complex)] + G)
    while True:
        mats = [B[:, i].reshape(n, n) for i in range(B.shape[1])]
        B2 = orth_basis(mats + [a @ g for a in mats for g in G])
        if B2.shape[1] == B.shape[1]: break
        B = B2
    return els, idx, mul, units, B, D, E, F, orbs

def val(x):
    for i, c in enumerate(x):
        if c: return i
    return len(x)

def inv_unit(mul, units, w):
    one = tuple([1] + [0] * (len(w) - 1))
    for u in units:
        if mul(u, w) == one: return u
    raise ValueError

def shell_inv(p, e, els, idx, mul, units):
    n = len(els); J = np.zeros((n, n), dtype=complex)
    for x in els:
        k = val(x)
        if k == e: y = x
        else:
            # x = t^k w、w は法 t^{e-k} の単数（代表：x を k だけ左に詰め、残りを 0 で埋める）
            m = e - k
            _, _, mul_m, units_m = ring(p, m)
            w = x[k:]; wi = inv_unit(mul_m, units_m, w)
            y = tuple([0] * k + list(wi))
        J[idx[x], idx[y]] = 1.0
    return J

for p, emax in [(2, 4), (3, 3), (5, 2)]:
    for e in range(1, emax + 1):
        els, idx, mul, units, B, D, E, F, orbs = alg(p, e)
        n = len(els)
        comm = lambda X: all(np.allclose(B[:, i].reshape(n, n) @ X, X @ B[:, i].reshape(n, n)) for i in range(B.shape[1]))
        R = {}
        for u in units:
            M = np.zeros((n, n), dtype=complex)
            for x in els: M[idx[x], idx[mul(u, x)]] = 1.0
            R[u] = M
        J = shell_inv(p, e, els, idx, mul, units)
        Fi = F.conj().T
        swap = all(any(np.allclose(F @ d @ Fi, x) for x in E) for d in D) and all(any(np.allclose(F @ x @ Fi, d) for d in D) for x in E)
        JFnorm = all(in_span(B, J @ F @ B[:, i].reshape(n, n) @ Fi @ J.T) for i in range(B.shape[1]))
        # 単数の角と、ガウス和の位相（原始指標で、導手ごとに一定か）
        Ui = [idx[u] for u in units]; phi = len(Ui)
        S = np.zeros((n, phi), dtype=complex)
        for j, i in enumerate(Ui): S[i, j] = 1.0
        cor = orth_basis([S.T @ B[:, i].reshape(n, n) @ S for i in range(B.shape[1])])
        # 指標：R_u の単数への制限の同時対角化
        rng = np.random.default_rng(2); c = rng.normal(size=phi) + 1j * rng.normal(size=phi)
        Mx = sum(c[k] * (S.T @ R[u] @ S) for k, u in enumerate(units))
        w, V = np.linalg.eig(Mx)
        one = tuple([1] + [0] * (e - 1)); i1 = units.index(one)
        phases = []; Umat = np.zeros((phi, phi), dtype=complex)
        for j in range(phi):
            v = V[:, j] / V[i1, j]
            # 導手 t^f：u ≡ 1 (mod t^f) で χ(u) = 1 となる最小の f
            f = next(f for f in range(e + 1) if all(abs(v[k] - 1) < 1e-8 for k, u in enumerate(units) if all(u[i] == one[i] for i in range(f))))
            # J F χ = λ χ の固有値 λ（原始指標ではガウス和の位相）
            g = np.zeros(n, dtype=complex); g[Ui] = v
            h = J @ F @ g
            lam = h[Ui[i1]] / v[i1]
            phases.append((f, lam))
            Umat += lam * np.outer(v, v.conj()) / phi
        prim = [lam for f, lam in phases if f == e]
        var = (max(abs(a - b) for a in prim for b in prim) if len(prim) > 1 else 0.0)
        Uin = in_span(cor, Umat)
        print(f'p={p} e={e}: dimA={B.shape[1]} R_u可換 {all(comm(X) for X in R.values())} J可換 {comm(J)} F交換 {swap} JF正規化 {JFnorm} '
              f'角の次元 {cor.shape[1]} 導手の数 {len({f for f, _ in phases})} 原始の位相の幅 {var:.3f} JF|単数∈角 {Uin}')
```

### records/projection_interaction/control_fqt_interaction.log
```
p=2 e=1: dimA=4 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 1 導手の数 1 原始の位相の幅 0.000 JF|単数∈角 True
p=2 e=2: dimA=10 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 2 導手の数 2 原始の位相の幅 0.000 JF|単数∈角 True
p=2 e=3: dimA=19 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 3 導手の数 3 原始の位相の幅 1.414 JF|単数∈角 False
p=2 e=4: dimA=31 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 4 導手の数 4 原始の位相の幅 2.000 JF|単数∈角 False
p=3 e=1: dimA=5 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 2 導手の数 2 原始の位相の幅 0.000 JF|単数∈角 True
p=3 e=2: dimA=12 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 3 導手の数 3 原始の位相の幅 2.000 JF|単数∈角 False
p=3 e=3: dimA=22 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 4 導手の数 4 原始の位相の幅 2.000 JF|単数∈角 False
p=5 e=1: dimA=5 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 2 導手の数 2 原始の位相の幅 1.747 JF|単数∈角 False
p=5 e=2: dimA=12 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 3 導手の数 3 原始の位相の幅 2.000 JF|単数∈角 False
```

### records/limit_form/crt_corner_check.log
```
(1) CRT との両立：照合 1098 回、合わない組 []
(2) e_1 = φ_(1,q)(1) = E^(q)_q（定数への射影）：合わない q []
```

### records/gamma_corner/corner_check.py（§E のスクリプトが使う A(N) などの定義）
```
"""方向 γ の立て直し：着手前の見込み確認（数値。証明ではない）。2026-11-19。

N | M、π^*：ℤ/M → ℤ/N に沿った引き戻し（Part 197 の pull）、ι = π^*/√(M/N)（等長）。φ(T) = ι T ι^†。
V：部分群への埋め込み x ↦ (M/N)x に沿った 0 拡張（等長）、ψ(T) = V T V^†。
A_N：D_s（殻の指示関数の掛け算）と E_s（双対殻への射影）が生成する代数（Part 214 の shellAlg）。
"""
import itertools, math, sys
import numpy as np

def divisors(n): return [d for d in range(1, n + 1) if n % d == 0]

def fourier(N):
    return np.array([[np.exp(-2j*np.pi*k*x/N) for x in range(N)] for k in range(N)]) / np.sqrt(N)

def gens(N):
    F = fourier(N)
    D = {s: np.diag([1.0 if math.gcd(N, x) == s else 0.0 for x in range(N)]).astype(complex) for s in divisors(N)}
    E = {s: F.conj().T @ np.diag([1.0 if math.gcd(N, k) == s else 0.0 for k in range(N)]) @ F for s in divisors(N)}
    return D, E

def orth_basis(mats, tol=1e-9):
    """行列の張る空間の正規直交基底（ベクトル化）。"""
    if not mats: return np.zeros((0, 0))
    A = np.array([m.ravel() for m in mats]).T
    U, S, _ = np.linalg.svd(A, full_matrices=False)
    r = int((S > tol * max(1.0, S[0])).sum())
    return U[:, :r]

def algebra(N):
    D, E = gens(N)
    G = list(D.values()) + list(E.values())
    B = orth_basis([np.eye(N, dtype=complex)] + G)
    while True:
        mats = [B[:, i].reshape(N, N) for i in range(B.shape[1])]
        prods = [a @ g for a in mats for g in G]
        B2 = orth_basis(mats + prods)
        if B2.shape[1] == B.shape[1]: return B, D, E
        B = B2

def in_span(B, X, tol=1e-7):
    v = X.ravel()
    return np.linalg.norm(v - B @ (B.conj().T @ v)) < tol * max(1.0, np.linalg.norm(v))

def iota(N, M):
    P = np.zeros((M, N), dtype=complex)
    for y in range(M): P[y, y % N] = 1.0
    return P / np.sqrt(M // N)

def vemb(N, M):
    k = M // N
    V = np.zeros((M, N), dtype=complex)
    for x in range(N): V[(k * x) % M, x] = 1.0
    return V

cache = {}
def A(N):
    if N not in cache: cache[N] = algebra(N)
    return cache[N]

def check_pair(N, M):
    k = M // N
    BN, DN, EN = A(N); BM, DM, EM = A(M)
    I = iota(N, M); V = vemb(N, M)
    out = {}
    out['iso'] = np.allclose(I.conj().T @ I, np.eye(N)) and np.allclose(V.conj().T @ V, np.eye(N))
    phi = lambda T: I @ T @ I.conj().T
    psi = lambda T: V @ T @ V.conj().T
    spanD = orth_basis(list(DM.values())); spanE = orth_basis(list(EM.values()))
    # φ
    out['phi_in_AM'] = all(in_span(BM, phi(X)) for X in list(DN.values()) + list(EN.values()))
    out['phi_E_strict'] = all(np.allclose(phi(EN[s]), EM[k * s]) for s in DN)
    out['phi_D_in_spanD'] = [s for s in DN if in_span(spanD, phi(DN[s]))]
    Q = sum(EM[t] for t in EM if t % k == 0)
    out['phi_one_is_Q'] = np.allclose(phi(np.eye(N)), Q)
    pullN = I * np.sqrt(k)
    out['cond_i'] = all(np.allclose(phi(X) @ pullN, pullN @ X) for X in list(DN.values()) + list(EN.values()))
    # 像の次元と角 Q A_M Q の次元
    imgs = [phi(BN[:, i].reshape(N, N)) for i in range(BN.shape[1])]
    corner = [Q @ BM[:, i].reshape(M, M) @ Q for i in range(BM.shape[1])]
    out['dimAN'] = BN.shape[1]; out['dimAM'] = BM.shape[1]
    out['dim_img'] = orth_basis(imgs).shape[1]; out['dim_corner'] = orth_basis(corner).shape[1]
    # ψ（0 拡張）
    out['psi_in_AM'] = all(in_span(BM, psi(X)) for X in list(DN.values()) + list(EN.values()))
    out['psi_D_strict'] = all(np.allclose(psi(DN[s]), DM[k * s]) for s in DN)
    out['psi_E_in_spanE'] = [s for s in EN if in_span(spanE, psi(EN[s]))]
    # フーリエ共役：F_M V F_N^† = c·ι（c は定数）
    W = fourier(M) @ V @ fourier(N).conj().T
    c = W[0, 0] / I[0, 0]
    out['fourier_conj'] = np.allclose(W, c * I) and abs(abs(c) - 1) < 1e-9
    # BC の ρ：φ(τ_x) = (N/M) Σ_{y ≡ x mod N} τ_y（τ は平行移動）
    def tau(n, x):
        T = np.zeros((n, n), dtype=complex)
        for z in range(n): T[(z + x) % n, z] = 1.0
        return T
    out['bc_rho'] = all(np.allclose(phi(tau(N, x)), sum(tau(M, y) for y in range(M) if y % N == x) / k) for x in range(N))
    return out

def check_chain(N, M, L):
    return np.allclose(iota(M, L) @ iota(N, M), iota(N, L)) and np.allclose(vemb(M, L) @ vemb(N, M), vemb(N, L))

if __name__ == '__main__':
    Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    pairs = [(N, M) for M in range(1, Mmax + 1) for N in divisors(M)]
    bad = []
    print('N M gcd(N,M/N) | dimA_N dimA_M dim像 dim角 | φ⊂A_M φ(E)厳密 φ(D)∈spanD(sの数/全) φ(1)=Q (i) | ψ⊂A_M ψ(D)厳密 ψ(E)∈spanE フーリエ共役 BCのρ')
    for N, M in pairs:
        o = check_pair(N, M)
        g = math.gcd(N, M // N)
        line = (f"{N} {M} {g} | {o['dimAN']} {o['dimAM']} {o['dim_img']} {o['dim_corner']} | {o['phi_in_AM']} {o['phi_E_strict']} "
                f"{len(o['phi_D_in_spanD'])}/{len(divisors(N))} {o['phi_one_is_Q']} {o['cond_i']} | {o['psi_in_AM']} {o['psi_D_strict']} "
                f"{len(o['psi_E_in_spanE'])}/{len(divisors(N))} {o['fourier_conj']} {o['bc_rho']}")
        print(line)
        if not (o['iso'] and o['phi_in_AM'] and o['phi_E_strict'] and o['phi_one_is_Q'] and o['cond_i'] and o['psi_in_AM']
                and o['psi_D_strict'] and o['fourier_conj'] and o['bc_rho'] and o['dim_img'] == o['dimAN']):
            bad.append((N, M))
    chains = [(N, M, L) for L in range(1, Mmax + 1) for M in divisors(L) for N in divisors(M)]
    cbad = [c for c in chains if not check_chain(*c)]
    print(f'組 {len(pairs)}、期待から外れた組 {bad}')
    print(f'合成の鎖 N|M|L：{len(chains)} 本、合成が合わない鎖 {cbad}')
    eq = [(N, M) for N, M in pairs if check_pair(N, M)['dim_img'] == check_pair(N, M)['dim_corner']]
    print(f'像 = 角（次元が等しい）組の数：{len(eq)}/{len(pairs)}')
```

## §F 引き継ぎメモの差分（deab9f3 から現在まで）
```diff
diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
index 0f8a20f..fb2e5c1 100644
--- a/handoff/PAG2_handoff_part259.md
+++ b/handoff/PAG2_handoff_part259.md
@@ -781,6 +781,59 @@
 - **統合照合（2026-11-19）**：材料索引の第 1→2 版の差分と、前回の統合照合の後の直し（材料ノート第 6 版、文献照合ノート第 4 版、CLAUDE.md と英語版、概要の日英、この引き継ぎメモ）を、宣言 102 件の形式文・PAG256 の全文・Part 257 の記録とともに照合者 1 人が照らした（`records/tail_audit3/`、所要 約 12 分）。形式文が偽・空虚・別物になったものはなく、宣言と Part・PAG の対応は過不足なく一致した。直したのは記録の側：概要の「全素点の局所因子の積への分解」が狭める前の言い方に戻っていた（τ の分解と、並びの形の指標の 𝔀 の分解に直した）、「Lean の文はない」の範囲の限定の戻り、イデール類指標の正規化 ω_q(q) = χ(q) の書き落とし（CLAUDE.md と英語版にも足した）、文献照合ノート §0 の確信度の引き上げ（地位を強める直しだったので取り下げ、著者の判断事項にした）、材料ノートの照合の状態の書き忘れ、19:25 の決定の記録の言い方のずれ、索引の 2.3・2.7・4.1・5.2 の強め、記録の列挙の抜け。直しはすべて取り下げ・限定・記録の直しで、数学の主張を強めるものはない（補足 8 の「主張を変えない直し」）。補足 8 の規約により、尾の台帳はこれで閉じる（統合照合の後の直しは主張を変えないものだけ）。著者への報告事項：確信度を「高」に上げるか（Part 257 の同定）、CLAUDE.md §3 の候補 1 の範囲（Part 245〜248 と読める）、「貼り合わせの合成」の貼り合わせは Compat か U か、CLAUDE.md に足した ω の正規化。
 - **著者の決定（2026-11-19 06:36）**：(1) Part 257 の同定（素数ごとの因子は局所定数、`parFac` は無限素点の局所定数。規約 T・ω の正規化・原始指標・s = 1/2 のもとでの値の一致、Lean の外）の確信度を高とする。(2) CLAUDE.md §1 に足した ω の正規化を承認。(3) CLAUDE.md §3 の候補 1 の範囲を Part 245〜248 に訂正。(4) 「貼り合わせの合成」の貼り合わせは U（ねじれた貼り合わせ）と読む。CLAUDE.md §1・§3 と英語版、材料ノート第 8 版 §6 の 6〜8、文献照合ノート第 6 版 §0、材料索引第 4 版、概要の日英に反映した（著者の決定の記録で、照合にはかけていない）。開いている著者の確認事項は、Part 258 の殻を混ぜない条件の強い読み（索引 5.1）だけになった。
 - **著者の確定（2026-11-19 07:10）**：Part 258 の殻を混ぜない条件（PAG262 の docstring の (ii)、Part 258 のノートの (3)）は強い読み（φ(D_s) は D_t の、φ(E_s) は E_t の線形結合）で確定。根拠は 2026-11-15 の受理、事前登録の問いの鋭さ、候補 3 の内容がこの読みに依存すること。弱い読み・非単位的な写像・別の両立条件は主張の外の別の問いとして残る。CLAUDE.md §3 の候補 3（日英）、索引 5.1（第 5 版）、Part 258 のノートに記録した。著者の確認待ちの事項はなくなった。
+- **候補 3 の文献照合（構築側で開ける範囲、2026-11-19、短期層）**：`notes/pag2_candidate3_literature_builder.md`。着手前の内部照合で、商に沿った写像の確認は 2026-11-14 の盲検の問いテストだけだったと確かめてから行った。Bastian–Humphries（arXiv:2606.19095）、Watanabe（arXiv:2305.19258、盲検では未読）、Kim（arXiv:1109.1334、同）の本文（WebFetch の要約を通して）に、商 ℤ/M → ℤ/N に沿った単位的な代数準同型 A_N → A_M の記述は見つからなかった（見つからなかったは不存在の証明ではない）。近い構造：wreath 積の角の代数（単位的でない部分代数）、超立方体の一般化 Terwilliger 代数の単位的でない準同型 T_d → T_{d−2}（arXiv:2301.08366）。どれも候補 3 の主張（単位的な写像の不存在）と食い違わない。Hanaki–Kim–Maekawa の本文は、リポジトリの PDF のリダイレクト先の URL が長すぎて構築側から取得できなかった。候補 3 の地位（［新規候補（小さい）］、確信度：低〜中）は変えない。未了は MathSciNet・zbMATH（著者側）と Hanaki–Kim–Maekawa の本文。CLAUDE.md §3 の「構築側は文献を自分で開いておらず」は、2026-11-19 07:25 の著者の承認で、照合の結果と残りに書き換えた（日英）。
+- **方向 γ の文献照合（構築側で開ける範囲、2026-11-19、短期層）**：`notes/pag2_gamma_literature_builder.md`。内部照合で、これまでの照合は 2026-11-14 の盲検の検索 1 本だけと確かめてから行った。検索 5 回の範囲で、有限レベルの Bost–Connes と円分スキームの T(0) を結ぶ記述は見つからなかった（本文は開いていない。確信度：低〜中）。BC の有限レベルは群環 ℚ[ℤ/nℤ] の帰納系と ℕ^× の交差積（関数のレベル、既知）で、D_s を含む T(0) の側は出てこない。［観察］BC の帰納系は整除のすべての段を使うが、T(0) の側で引き戻しと両立し殻を混ぜない単位的な写像は互いに素な段だけ（Part 258・259）で、そのまま持ち上げる形は取れない。γ は開いたまま、MathSciNet・zbMATH は著者側。
+- **方向 γ の立て直し：着手前の 4 点と推薦案（2026-11-19）**：`notes/pag2_gamma_corner_preregistration.md`、数値と盲検の記録は `records/gamma_corner/`。
+  - 内部照合：同じ構成が Part 258 の着手前の盲検の補足（問いの外）に 1 か所あるだけだった。Lean・xlsx にはない。
+  - 写像：φ(S) = ι S ι^†（ι は正規化した引き戻し）は単位元を保たず、どの段 N ∣ M でも A_N を A_M に送る（素数冪の段を含む）。像は角 Q A_M Q 全体。合成と両立し、整除の順序全体で直極限がとれる。群環の側では BC の ρ_{M/N}。
+  - 数値：M ≤ 30 の 111 組、鎖 276 本。像 = 角は三重正則性からの短い帰結（構築側と盲検の手計算が一致）。
+  - 対照群：関数体でも成り立つので、算術の内容はない。
+  - 盲検：Terwilliger 版の角の文、帰納系、BC と T(0) を結ぶ文献は、どれも見つからなかった（確信度：低〜中）。E 側は BC の表現の外。
+  - 推薦：新しいパートは始めず、短期層で R-b・R-c・R-d を Lean にする（PAG264）。著者の決定待ち。
+- **Part 260（PAG264.lean、短期層の小さいノート、2026-11-19）**：09:37 に著者が上の推薦案を採用した。`notes/pag2_pag264_corner_maps.md`、記録は `records/audit264/`。
+  - Lean：定理 37・定義 5、sorry 0・警告 0、#print axioms は標準の範囲。
+  - 内容：角の写像 φ(S) = (N/M)·π^* ∘ S ∘ π_*（`cornerOp`・`cornerHom`）。
+    - A_N を A_M に送る（`cornerOp_mem`、gcd によらない）。
+    - φ(E_s) = E_{(M/N)s}、φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s（Part 202 の `oldP`）、引き戻しと両立。
+    - (a)(b) による一意性（`existsUnique_corner`）、合成（`cornerHom_comp`）、N < M なら φ(1) ≠ 1、(2,4) の D 側の証人。
+  - Lean の外：恒等の法則・極限・像 = 角全体・BC との対応・随伴。
+  - 内部照合：下書きの `pull_trans`（Part 259 の `pull_pull` と同じ文）と `apply_single_two_of_mem_span`（Part 258 から直ちに出る）を消した。
+  - 照合：
+    - 独立照合：偽・空虚なし。除去テストで (b)・(a)・積のどれを外しても一意でない。
+    - 再照合：散文の 7 点（帰納系・非単位的の言い方など）を直した。その後の直しは尾。
+  - ラベル：E 側は［既知］、ほかは［再導出（小さい）］、新規候補なし（対照群でも成り立つ）。
+  - 件数：鎖全体の定理・補題は 3,677 件（3,640 + 37）。xlsx は final82（行 2〜3705）。
+  - 索引に 5.5 を足し、5.2・6.3・§6 を直した（宣言名の確認 113/113）。辞書に §17 を足した。
+- **Part 260 の追加：恒等の法則と統合照合（2026-11-19 午後）**：
+  - 足したもの：`fsum_self`・`cornerOp_self`・`cornerHom_self`（φ_{N,N} = id）。PAG264 は定理 40 になった。合成と合わせて帰納系の 2 法則が Lean に揃った。`DirectedSystem` としての束ねと極限は Lean の外。
+  - 照合：3 定理と、再照合の後の直し（尾）を、統合照合 1 回で照らした。3 定理は意図どおりだった。散文のずれ 11 点を直した（N = M の文、件数、対照群の結論を試した範囲に、反例の組など）。統合照合の後の直しは主張を狭める・明確にするものだけで、尾の台帳は空。
+  - 件数：鎖全体の定理・補題は 3,680 件、xlsx は final82（行 2〜3708）。
+- **Part 261（PAG265.lean、短期層、2026-11-19 午後）**：推薦案の R-d の残り（整除の順序全体の直極限）。12:51 に著者が採用した。`notes/pag2_pag265_corner_limit.md`、記録は `records/audit265/`。
+  - Lean：定理 10。
+    - 正の整数の整除の順序（Part 254 の `Lvl`）の上の `DirectedSystem`。
+    - Mathlib の一般の `DirectLimit` による極限 `CornerLim`。非単位的な環の構造と ℂ のスカラー倍を持つ。
+    - 各段の単射性、局所的な単位元（1 元ごと・有限集合ごと）、左単位元がないこと。
+  - 経緯：
+    - 最初の版は `Module.DirectLimit`（ℂ 加群）で、「Mathlib に非単位的な代数の直極限の道具がない」と書いていた。1 回目の独立照合の指摘で、一般の `DirectLimit` にあると分かり、組み直した。
+    - 2 回目の照合で、局所的な単位元の標準の定義（有限集合ごとに共通のべき等元）に合わせて 3 定理を足した。
+    - 3 回目の再照合の指摘 11 点を直し、尾の台帳は空。
+  - 内部照合：`Lvl` は新しく作らず Part 254 のものを使った。下書きの `cornerSys_apply`（Part 260 の `cornerHom_coe` と同じ文）を消した。
+  - 読み：局所的な単位元の文はどの直極限でも成り立つ一般論で、非単位的という内容を運ぶのは左単位元がないことだけ。
+  - 件数：鎖全体の定理・補題は 3,690 件。xlsx は final83（行 2〜3718）。
+- **極限の具体形：着手前の 4 点と推薦（2026-11-19 午後）**：`notes/pag2_limit_form_preregistration.md`、記録は `records/limit_form/`。
+  - 数値：角の写像は中国剰余定理と両立する（1098 回）。
+  - 盲検の問いテスト：作用・素点ごとの分解（⊗'_p）・関数体は、どれも既知の型（Flath、Schwartz–Bruhat）の当てはめ。
+  - 照合者の否定的な観察：A_∞ に入る算術は素点が可算個あることだけの見込み。無限素点・スケーリング・U は A_∞ に現れない。
+  - 推薦：Lean にせず、索引 5.5 に読みと文献を書くだけ（残余が空）。
+  - 次に関門に通す候補：⊗'_p の外（無限素点・スケーリング・U）と A_∞ の相互作用。「射影」の章に直結。推薦ではなく、着手も未定。
+- **無限素点・スケーリング・貼り合わせ U と A_∞ の相互作用：着手前の 4 点と推薦（2026-11-19 夕方）**：`notes/pag2_projection_interaction_preregistration.md`、記録は `records/projection_interaction/`。
+  - 内部照合：単数との可換（Part 218 の `shellAlg_comm_dil`）、可換子 `fullComm`（Part 220）と N ∣ 12 の判定（Part 225）、フーリエ共役（Part 242）、`condPart`・`Vprim`・`JH_eq_rootNum_mul`・`UA1` が既にある。Hartley と殻の反転 J による共役、F_M ι = V F_N は鎖にない。
+  - 数値（N = 2〜36）：R_u・P・J（素数冪ごとの殻の反転の CRT の積）は A_N と可換。J∘H は A_N を正規化し D_s ↔ E_s。F_M ι = V F_N。単数の角は導手ごとの射影の張る代数。U_N が角に入るのは N ∣ 24（U_N = I）、符号は N ∣ 12 だけ。range(D_1) ∩ range(E_1) = V_prim。対照群 F_p[t]/(t^e) でも同じ形。
+  - 失敗の記録（第 6 の型）：法 N の殻ごとの反転 s·w ↦ s·w⁻¹ は N = 10, 14, 15, … で A_N と可換でない（作業仮説を数値が否定した）。
+  - 盲検の問いテスト（ツール 35 回、約 962 秒）：全項目が数値と一致し、新しい内容は見つからなかった（確信度：中）。文献にない 4 つの短い計算は「せいぜい小さいノートの水準」。
+  - 円環の検知：U の位相はガウス和と A1 から入り、A_∞ は導手の区分け以外の制約を課さない。
+  - 推薦：Lean にせず、索引 2.9（新設）と 5.5 からの参照、辞書 §19 に読みと否定的な結果を書くだけ。構築側はこの線で新しい問いを開かず、著者側の起草からの依頼に応える側に回ることを提案。
+  - 著者の決定（2026-11-19 17:17）：「進めてください」で推薦を採った。索引 2.9 の見出しを内容の範囲（導手の区分けと N ∣ 24・N ∣ 12 の場合を除く）に狭めた。
 
 ## 点検（2026-10-24、Part 204 の後）
 - 全体の再ビルド：PAG.lean〜PAG208.lean（208 本）を空のディレクトリで最初からコンパイルし直した。208 本すべて成功、エラー・警告 0、約 10 分。#print axioms 1903 項目すべて標準の公理（またはその一部）。作業用の .out と 208/208 一致。
```
