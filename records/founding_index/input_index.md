# 照合の入力：基礎文書の材料索引

§A は照合の対象（索引の全文）。§B は索引に出る宣言の docstring と形式文（定理は := まで、定義は本体を含む）。§C は索引が引くノートの冒頭（各 45 行）。§D は引き継ぎメモの該当項目。§E は CLAUDE.md の全文。

## §A 索引（全文）

# アーデル射影幾何 — 基礎文書の材料索引（骨格の 6 章ごと）

（2026-11-18。短期層の作業。新しいパートではない。基礎文書の骨格（著者側、2026-11-15）の章ごとに、書く主張・その地位・支える Lean の宣言・ノート・照合の状態・開いている点を並べる。起草は著者側で行う。この索引は主張を足さない。地位とラベルは各ノートと CLAUDE.md の記載を写したもので、写すときに強めないことを方針とした。）

## §0 使い方と注意

- **地位の語**：
  - 「定義」＝著者の文面（CLAUDE.md §1）。
  - 「読み」＝解釈の層。誰が出し、誰が採用したかを添える。
  - 「定理」＝Lean の文。ラベル［既知］［再導出］［新規候補］を添える。
  - 「公準」＝A1。
  - 「数値のみ」＝数値確認だけで証明はない。
  - 「Lean の外」＝文献か手計算による。
- **番号の罠**：PAG 2.0 の Part n は PAG(n+4).lean で、Lean の名前空間はファイル番号に従う。例：Part 252 の宣言は `PAG.Part256.…`、Part 23 の宣言は `PAG.Part27.…`。この索引では「Part n（PAGm）」と併記し、宣言は完全修飾名で書く。
- **照合の状態**：各パートを閉じるときの独立照合と、その後の再照合・統合照合を指す。詳細は各ノートの照合の節。
- 骨格が引く著者側のファイル（`what-is-aadel-projective-geometry.md`、A8 の一次評価、δ の事前登録と帰結、モノグラフ層の記録）は、このリポジトリにない。索引ではファイル名だけを挙げる。
- 宣言名は、2026-11-18 にこの索引に出るものをすべて Lean のファイルで検索して実在を確かめた（§7）。

## 第 1 章　点と大域対象

**1.1 点は素数たちと無限素点。無限素点では無限大と無限小が重なり合う。**
- 地位：定義（著者の文面、CLAUDE.md §1）。
- Lean：定義そのものはない。関連する定理として、すべての素点の付値の組は単射（`PAG.Part259.eq_of_padicValRat_eq`）。積公式 log q = Σ v_s(q) log s（`PAG.Part259.log_eq_sum_of_support`）により、∞ の座標は有限素点の座標から決まる。どちらも Part 255（PAG259）の［既知］。
- ノート：`pag2_part255_resolution_discrete_limit.md`。

**1.2 大域対象は、制限積の因子として最初から並列に共存する素点たち。有限レベル商と Λ 切断は、その全体への見方（切り方）。**
- 地位：読み。命題 3 の置き方として、著者側 Muse の決定（2026-11-13、著者はいつでも覆せる）。
- Lean：極限の具体モデル `PAG.Part255.unitSys`（両立する系の群。Part 251（PAG255））。`unitSys` ≅ Ẑ^×、構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0}、制限積そのものは Lean の外。
- ノート：`pag2_part251_projective_limit.md`。A8 の一次評価は著者側のファイル。

**1.3 素数の類は、大域対象の中で稠密な部分群を生成する。**
- 地位：定理［既知］（再導出、新規候補なし）。
- Lean：
  - 有限レベル (ℤ/N)^× × ℝ では `PAG.Part253.exists_cls_near`（Part 249（PAG253））。
  - 極限のモデル `unitSys × ℝ` では `PAG.Part255.dense_closure_allPrimes`・`PAG.Part255.dense_closure_primeGens`（Part 251（PAG255））。
  - 素数の類の一意性は `PAG.Part255.primeSys_unique`。
- 留保：「イデール類群で稠密」は、Lean の外の同一視のもとでの読み。
- ノート：`pag2_part249_idele_class_density.md`、`pag2_part251_projective_limit.md`。

**1.4 舞台は射影直線 P¹。反転が 0 と ∞ を入れ替える。**
- 地位：読み（「射影」の読み。構築側が出し、2026-11-18 に著者が留保つきで採用）。P¹(ℤ/N) そのものは［既知］（モジュラー記号の標準の道具）。
- Lean：
  - 射影直線と反転：`PAG.Part27.ProjLine`、反転 `PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`（一般の N）。
  - N = p^K（K ≥ 1）の場合：点モデル `PAG.Part26.Pt` との点集合の全単射 `PAG.Part27.projEquiv`、点の数 `PAG.Part27.card_ProjLine`。
  - 2 チャートモデル：貼り合わせ条件 `PAG.Part23.Compat`、反転 `PAG.Part23.W`。点モデルの関数との線形同型 `PAG.Part26.ptEquiv`（一般の N）。
  - Part 19・22・23（PAG23・PAG26・PAG27）。
- 留保：
  - N が 2 つ以上の素因数を持つとき、点モデルと P¹(ℤ/N) の点の数は一致しない（数え上げ、Lean の外）。
  - 有限の側では 0 と ∞ は別の点（N ≥ 2）。
- ノート：`pag2_projection_material.md`（第 6 版）§3。

## 第 2 章　無限素点の重なりと貼り合わせ

**2.1 重なりは、ねじれた貼り合わせ（境界ユニタリ U）と読む。**
- 地位：読み（著者の決定、2026-11-12）。
- 採らなかった読みと理由：
  - 群の商として読む読みは A1 と両立しない。反例は法 9 の 3 次指標（批判の照合と数値。この反例の Lean の所在は、この索引では確かめていない）。
  - W による商は A1 と両立するが、D が商に降りない。
- ノート：`pag2_resolution_overlap_materials.md`、CLAUDE.md §1。

**2.2 モノグラフ層の作用素系（D、T_p、W、二面体関係）、問題 P1、定理 2.6（境界条件 U の両立分類）。**
- 地位：モノグラフ層の記録（著者側、リポジトリにない）。
- Lean（有限レベル版のみ、Part 249（PAG253））：
  - 素数の平行移動と可換なら、すべての単数の平行移動と可換：`PAG.Part253.commute_transl_of_prime`。
  - 指標ごとにスカラー：`PAG.Part253.eigenFun_of_commute_prime`。
  - (a)⇒(b) の完全な形：`PAG.Part253.thm26_full`。
  - 可換性を外した反例：`PAG.Part253.thm26_needs_commute`。
  - ラベル［再導出］。
- 留保：
  - 逆向き (b)⇒(a) は数値のみ。
  - 大域の Ẑ^× での形は Lean の外。
  - 証明は Dirichlet の算術級数定理を使わない簡略化。新しい定理ではない。
- ノート：`pag2_part249_idele_class_density.md`。

**2.3 公準 A1（内容は Tate の定理）と、定理 2.6 との両立。**
- 地位：A1 は公準（解釈の層の公準、導かれていない）。両立は「既知の結果からの短い帰結」（確信度：高。かつての新規候補 2、2026-11-12 に候補から外れた）。
- Lean：部品の 3 定理。組み合わせた 1 つの文は形式化していない。
  - `PAG.Part16.normSq_gaussSum`
  - `PAG.Part173.gauss_inv_pair`
  - `PAG.Part198.gauss_sign_real`
- ノート：`pag2_thm26_A1_collation.md`、CLAUDE.md §3。

**2.4 「射影」の変換と位相：反転（乗法の側）と加法の変換（加法の側）の合成。**
- 著者の言葉：「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」。
- 地位：
  - 読み（2026-11-18、著者が留保つきで採用）。
  - 「貼り合わせ」が `PAG.Part23.Compat`（ねじれのない座標の貼り合わせ）と U のどちらを指すかは、著者の確認待ち。
  - 標準の核は Hartley 核（著者の決定）。A1 の内容と揃うことは著者の判断。
- Lean（Part 252（PAG256）、［再導出］）：
  - 写像 `PAG.Part256.JH`、値 `PAG.Part256.rootNum`、偶奇の因子 `PAG.Part256.parFac`。
  - すべての指標で単数の上の式：`PAG.Part256.JH_eq_rootNum_mul_any`。
  - 原始指標で絶対値 1：`PAG.Part256.normSq_rootNum`。
  - 原始指標で単数の外に漏れない：`PAG.Part256.hartley_eq_zero_of_not_isUnit`。
  - 原始性を外した反例：`PAG.Part256.removal_counterexample`・`PAG.Part256.removal_counterexample_normSq`・`PAG.Part256.removal_counterexample_four`。
- 留保：
  - `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。P¹ のモデルと結ぶ Lean の文はない。
  - 原始指標で `rootNum` がルート数であることは Lean の外。
  - 素朴なフーリエ核 e(xy) では τ(χ)/√N で、奇の指標で i 倍ずれる（滑らかにしない）。
- ノート：`pag2_part252_hartley_gluing.md`、`pag2_projection_material.md`、`pag2_prereg_projection.md`。

**2.5 原始部分の作用素 T とユニタリ性。**
- 地位：定理［再導出］（Part 253（PAG257））。
- Lean：
  - すべての指標で T χ = W(χ)χ：`PAG.Part257.TopL_charU`。
  - 原始部分の上でユニタリ：`PAG.Part257.unitary_Vprim`。
  - 原始指標で A1 の位相を課した任意の線形写像は、原始部分の上で T と同じ値をとる：`PAG.Part257.TopL_eq_of_A1`（ほぼ同語反復）。
- 留保：U は Lean で定義していない（仮定の形でだけ現れる）。
- ノート：`pag2_part253_primitive_operator.md`。

**2.6 法 N の境界ユニタリ U_N 全体と、代数的な帰納極限の上の U_∞。**
- 地位：定理［再導出］（Part 254（PAG258））。
- Lean：
  - 位相 `PAG.Part258.phaseA1`、U_N `PAG.Part258.UA1`。
  - 導手ごとの部分 `PAG.Part258.condPart_eq_map`。
  - 族の一意性 `PAG.Part258.UA1_family_unique`。
  - 極限の上の作用素 `PAG.Part258.Uinf`、その一意性 `PAG.Part258.Uinf_unique`、内積の保存 `PAG.Part258.ipLim_Uinf`。
- 留保：
  - U_N は A1 の位相を定義として入れた作用素で、A1 は導かれていない。
  - 直和を 1 つの文にした定理はない。
  - 完備化 L²(Ẑ^×) は Lean の外（読みとしては、解像度が落ちる側の操作）。
- ノート：`pag2_part254_full_gluing.md`。

**2.7 位相の、全素点の局所因子の積への分解（値のレベル）。**
- 地位：定理［既知（再導出）］（Part 256（PAG260）・Part 257（PAG261））。
- Lean：
  - 互いに素な 2 つの法：`PAG.Part260.rootNum_prodChar`・`PAG.Part260.parFac_prodChar`・`PAG.Part260.crossSign`。
  - 互いに素な法の並び：`PAG.Part261.rootNum_listChar_formII`・`PAG.Part261.parFac_listChar`。
  - すべての素数への分解：`PAG.Part261.gaussSum_primeFactors`。
- Lean の外（値の一致、規約 T を明示）：形 (II) の素数ごとの因子は Tate の局所定数に、`parFac` は無限素点の局所定数 (−i)^a に一致する（原始指標、s = 1/2）。Part 257 の読み（確信度：中〜高）を、2026-11-18 の文献照合で確かめ直した。
- ノート：`pag2_part256_gluing_cross_term.md`、`pag2_part257_local_factor_decomposition.md`、`pag2_literature_ia_sign.md`。

**2.8 加法指標の規約は規約 T（Tate の学位論文の加法指標：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）。**
- 地位：著者の決定（2026-11-18 19:25）。基礎文書の標準。
- 書き方の規則：
  - 明示的な因子 i^{±a} が無限素点の局所定数であることは、規約によらない。
  - 符号 χ(−1) の置き場は規約による。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
- ノート：`pag2_literature_ia_sign.md`、CLAUDE.md §1。

## 第 3 章　解像度と有効な姿（§1 の命題 3）

**3.1 定義文と、その置き方と読み。**
- 地位と出所：
  - 定義文：直線は解像度を落としたときに創発する有効な姿。解像度のパラメータは未決定（著者の文面）。
  - 置き方（2026-11-13）：見方の選択として解釈の層に置く（著者側 Muse の決定）。
  - 08:41 の定義（著者の原文）：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。…極限でも離散構造の観測を維持します。」
  - 読み L1（著者が採った読み、構築側の案）：解像度は測る素点の集合。
- Lean：なし（数学の文ではない）。
- 書き方の規則：解像度を N・K・Λ と同一視しない。閉包・完備化の連続体を目標として書かない。「直線の創発」と書かない。
- ノート：`pag2_author_definition_0841.md`、`pag2_part255_resolution_discrete_limit.md`、CLAUDE.md §1。

**3.2 Part 250 の試み（ε-鎖による定式化）。**
- 地位：定理［既知］（教科書の例の対数座標版）と、否定的な結果。
- Lean（Part 250（PAG254））：
  - 定義 `PAG.Part254.chainIn`。
  - ∞ の側はどの ε でも鎖でつながる：`PAG.Part254.chainIn_dInf`。p の側はつながらない：`PAG.Part254.not_forall_chainIn_dP`。
  - 稠密性 `PAG.Part254.dense_logSet`、等長性 `PAG.Part254.dInf_eq_dist`。
- 否定的な結果：「解像度を落とすと直線が現れる」は示せていない。ε-鎖の商は 1 点につぶれ、ℝ は完備化から現れ、しかも ℝ は定義に使われている。
- ノート：`pag2_part250_resolution_emergence.md`。

## 第 4 章　解像度ごとの姿（設計についての定理 1）

**4.1 Part 255 の二分法：測る素点と、像の離散・稠密。**
- 地位：定理［既知（再導出）］（S 単数定理・積公式・弱近似の ℚ の場合）。
- Lean（Part 255（PAG259））：
  - 有限の基礎 ⟨S⟩（S は素数の有限集合、T ⊆ S）での閾値：`PAG.Part259.threshold_iff`。
  - 測らない素数が 2 つ以上なら稠密：`PAG.Part259.dense_imgST_iff`。高々 1 つなら閉かつ離散：`PAG.Part259.isClosed_discrete_imgST`。
  - すべての素点を同時に測る位相では、像は閉かつ離散：`PAG.Part259.isClosed_discrete_rhoBox_image`（座標 `PAG.Part259.BoxCoord`、写像 `PAG.Part259.rhoBox`）。照合 A の評価では、位相の選び方でほぼ決まる文。
- 留保：
  - 二分法を 1 つの文にはしていない。
  - 閉包に現れる直線は、読みとしては解像度が落ちた印（08:41 の定義）。その直線が無限素点の座標であること、および対照群 𝔽_q(t) で直線が現れないことは、骨格の記述で Lean の外。
- ノート：`pag2_part255_resolution_discrete_limit.md`。

## 第 5 章　有限レベルの代数の組み立て（設計についての定理 2）

**5.1 Part 258 の二分法：殻代数の写像は互いに素な段でだけある。**
- 地位：定理。
  - 存在の側（テンソル積）：［既知］（Hanaki–Kim–Maekawa の直積の定理）。
  - 不存在の側：［新規候補（小さい）］（確信度：低〜中。2026-11-15 の著者側の判断）。
- Lean（Part 258（PAG262））：
  - 二分法：`PAG.Part262.exists_compatible_hom_iff`。
  - 存在 `PAG.Part262.exists_compatible_hom`、写像 `PAG.Part262.shellLift`。
  - 不存在 `PAG.Part262.no_compatible_hom`。
- 留保：
  - 条件 (iii)（殻を混ぜない）を強い読みにしたのは構築側で、著者に確かめる事項。
  - 文献照合（MathSciNet・zbMATH、Hanaki–Kim–Maekawa と Bastian–Humphries の本文）が済むまで、外部で新規性として使わない。
- ノート：`pag2_part258_beta_premise.md`、CLAUDE.md §3。

**5.2 Part 259：フーリエとの両立を足した一意性と、帰納系の添字。**
- 地位：定理。
  - 順序の性質：［既知］（ユニタリ約数、E. Cohen 1960）。
  - 一意性・非一意性・帰納系：［再導出（小さい）］。
- Lean（Part 259（PAG263））：
  - 一意な存在の二分法 `PAG.Part263.existsUnique_compatF_iff`、その写像の特定 `PAG.Part263.compatF_iff_eq_shellLift`。
  - (iii) を外すと一意でない：`PAG.Part263.not_existsUnique_compat`（捩れた写像 `PAG.Part263.twLift`）。
  - 合成との両立 `PAG.Part263.canon_comp`。
  - 添字 `PAG.Part263.UDvd` は有向でない：`PAG.Part263.not_isDirected_udvd`。
  - 無平方数の部分系の極限 `PAG.Part263.sqLim`、各段は単射で入る：`PAG.Part263.sqLim_of_injective`。
- 留保：
  - 奇数の場合の一意性は数値のみ。
  - `sqLim` の代数構造と、制限テンソル積との同型は Lean の外。
  - gcd ≠ 1 で (i) と D の側だけを満たす写像の不存在は、数値の見込みのみ。
- ノート：`pag2_part259_unitary_step_maps.md`、`pag2_R1_assessment.md`。

**5.3 関数のレベルの帰納系。**
- 地位：定理［再導出］。
- Lean：
  - Part 197（PAG201）：引き戻し `PAG.Part201.pull`、ハール正規化の保存 `PAG.Part201.zket_pull`、法によらない定理 A `PAG.Part201.thmA_haar`。
  - Part 202（PAG206）：引き戻しのフーリエ変換 `PAG.Part206.dft_pull_apply`、旧部分 = 引き戻しの像 `PAG.Part206.oldP_eq_self_iff`。
- 留保：極限 ℂ[ℚ/ℤ] との同一視は、この索引では Lean の文を確かめていない（骨格の記述）。
- ノート：引き継ぎメモの項目 18・23。

**5.4 互いに素な段のテンソル積。**
- 地位：定理［既知］（直積スキームの一般定理 T(A×B) ≅ T(A)⊗T(B) の特別な場合）。
- Lean：
  - Part 228（PAG232）：`PAG.Part232.shellAlgTensorEquiv`、`PAG.Part232.leftHom`、`PAG.Part232.tensLift_injective`、`PAG.Part232.range_tensLift`。
  - Part 236（PAG240）：局所作用素 `PAG.Part240.locHom`、`PAG.Part240.tensEquiv`。
- ノート：引き継ぎメモの項目 49・57、CLAUDE.md §3。

## 第 6 章　位置づけ

**6.1 殻代数 A_N は Terwilliger 代数 T(0) そのもの。**
- 地位：［既知］（2026-11-07 の著者の定義照合）。
- Lean：定義 `PAG.Part218.shellAlg`（Part 214（PAG218））。
- 既知として扱う結果：
  - 素数冪の Wedderburn 分解と次元公式（Part 225–226）。
  - テンソル積分解（Part 228）。
  - ⟨D_u, E_N⟩ の構造とフーリエ共役（Part 241–242、確信度：中）。
- 書き方の規則：構造が要るときは再証明せず、辞書経由で文献を引く。
- ノート：`pag2_terwilliger_dictionary.md`、CLAUDE.md §3。

**6.2 新規性の候補（未確定。断定しない）。**
- 候補 1：生成の分類（Part 246–248。主定理 `PAG.Part252.addEAlg_eq_shellAlg_iff_all`）。
  - 範囲：合成数の N（確信度：中）。評価は「小さいノートの水準」。
  - MathSciNet・zbMATH は未実施。
  - ノート：`pag2_candidate1_generation_collation.md`。
- 候補 3：Part 258 の不存在の側（5.1）。文献照合は著者側の作業。
- かつての候補 2（定理 2.6 の提示形）は候補から外れた（2.3）。

**6.3 Bost–Connes との接続。**
- 地位：
  - 関数のレベルでは既知。
  - T(0) の側に届くかは、方向 γ の文献照合（著者側の作業）による。
- ノート：CLAUDE.md §2・§3。

**6.4 書かないこと。**
- リーマン予想へのアプローチ。
- A1 の導出。
- 数値確認を証明と呼ぶこと。
- 「直線の創発」という表現。
- 既知の結果を新規と書くこと（CLAUDE.md §6）。

## §6 開いている点（文書に「開いている」と書くもの）

- **著者の確認待ち**
  - 「貼り合わせの合成」の貼り合わせは、`Compat` と U のどちらか（2.4）。
  - Part 258 の条件 (iii) の強い読み（5.1）。
- **著者側の作業**
  - 方向 γ の文献照合（6.3）。
  - 候補 3 の文献照合（5.1）。
  - 候補 1 の MathSciNet・zbMATH（6.2）。
- **Lean の外・数値のみで残るもの**
  - 構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0}（1.2・1.3）。
  - 定理 2.6 の逆向き（2.2）。
  - A1 と定理 2.6 の両立を 1 つにした文（2.3）。
  - 完備化 L²(Ẑ^×)（2.6）。
  - 局所定数との同定（2.7）。
  - 二分法の 1 つの文（4.1）。
  - `sqLim` の代数構造（5.2）。
  - 奇数の場合の一意性（5.2）。
  - (i) と D の側だけでの不存在（5.2）。
- **定式化の問い**
  - 解像度の操作に、L1 を超える定式化が要るか（現時点では、L1 と 08:41 の定義で文書は書ける）。
  - 「射影」の、全素点を通した一つの構成（空間と作用素のレベル）としての定式化（値のレベルでは 2.7）。

## §7 宣言名の確認の記録

- この索引に出る完全修飾名を機械的に取り出し、`PAG.PartM.name` ごとに PAGM.lean の `theorem`・`def`・`abbrev`・`structure`・`instance` などの宣言の行を検索した（スクリプト `records/founding_index/check_names.py`、出力 `check_names.log`）。
- 地位とラベルは各ノートと CLAUDE.md の記載を写した。写し間違いと強めすぎは、独立照合で確かめる（§8）。

## §8 照合の記録

（独立照合の後に記録する。）

## §B 宣言

### PAG.Part16.normSq_gaussSum（PAG16.lean）
```lean
/-- **|τ(χ)|² = N**（χ 原始的）。法 p^c なら |τ|² = p^c。 -/
theorem normSq_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ stdAddChar) = N :=
```

### PAG.Part23.Compat（PAG23.lean）
```lean
/-- 貼り合わせ条件: 赤道（単数）上で F_N(y) = F_S(y⁻¹)。 -/
def Compat (F : P1F N) : Prop := ∀ y : ZMod N, IsUnit y → F.2 y = F.1 y⁻¹
```

### PAG.Part23.W（PAG23.lean）
```lean
/-- 反転 W: [x:1] ↔ [1:x]、関数では南北の入れ替え。 -/
def W (F : P1F N) : P1F N := (F.2, F.1)
```

### PAG.Part26.Pt（PAG26.lean）
```lean
/-- P¹(Z/N) の点: 南の点 [x:1]（inl x）と北の内部点 [1:y]（inr y、y 非単数）。 -/
abbrev Pt (N : ℕ) := ZMod N ⊕ {y : ZMod N // ¬ IsUnit y}
```

### PAG.Part26.ptEquiv（PAG26.lean）
```lean
/-- **点モデル ≃ 2 チャートモデル**（線形同型）。 -/
noncomputable def ptEquiv (N : ℕ) : (Pt N → ℂ) ≃ₗ[ℂ] compatSub N where
  toFun f := ⟨toP1 f, compat_toP1 f⟩
  invFun F := ofP1 F.1
  map_add' f g := by
    apply Subtype.ext
    ext y
    · rfl
    · simp only [toP1, Pi.add_apply, Submodule.coe_add, Prod.snd_add]
      split_ifs <;> rfl
  map_smul' a f := by
    apply Subtype.ext
    ext y
    · rfl
    · simp only [toP1, Pi.smul_apply, Submodule.coe_smul, Prod.smul_snd, RingHom.id_apply]
      split_ifs <;> rfl
  left_inv f := ofP1_toP1 f
  right_inv F := Subtype.ext (toP1_ofP1 F.2)
```

### PAG.Part27.ProjLine（PAG27.lean）
```lean
/-- **射影直線** P¹(Z/N)。 -/
def ProjLine (N : ℕ) := Quotient (projSetoid N)
```

### PAG.Part27.Wproj（PAG27.lean）
```lean
/-- 反転 W[a:b] = [b:a]（well-defined）。 -/
def Wproj : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk ⟨(v.1.2, v.1.1), swap_unimod v⟩)
    (fun _v _w ⟨u, h1, h2⟩ => mk_eq_mk u h2 h1)
```

### PAG.Part27.Wproj_Wproj（PAG27.lean）
```lean

theorem Wproj_Wproj (q : ProjLine N) : Wproj (Wproj q) = q :=
```

### PAG.Part27.card_ProjLine（PAG27.lean）
```lean
/-- **点の数**: |P¹(Z/p^K)| = p^K + p^(K−1)。 -/
theorem card_ProjLine : Nat.card (ProjLine (p ^ K)) = p ^ K + p ^ (K - 1) :=
```

### PAG.Part27.projEquiv（PAG27.lean）
```lean
/-- **点モデル ≃ 射影直線** Pt(p^K) ≃ P¹(Z/p^K)。 -/
noncomputable def projEquiv : Pt (p ^ K) ≃ ProjLine (p ^ K) where
  toFun := toProj K
  invFun := ofProj K hK
  left_inv := ofProj_toProj K hK
  right_inv := toProj_ofProj K hK
```

### PAG.Part173.gauss_inv_pair（PAG173.lean）
```lean
/-- **2. z(χ) · z(χ⁻¹) = χ(−1)**（χ は法 N の原始指標）。 -/
theorem gauss_inv_pair {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (gaussSum χ stdAddChar / ((Real.sqrt N : ℝ) : ℂ)) * (gaussSum χ⁻¹ stdAddChar / ((Real.sqrt N : ℝ) : ℂ))
      = χ (-1) :=
```

### PAG.Part198.gauss_sign_real（PAG198.lean）
```lean
/-- **4. ガウスの符号決定（すべての実原始指標）**：法 N の原始指標 χ で χ² = 1 なら、
  z(χ) = τ(χ)/√N は χ(−1) = 1 で 1、χ(−1) = −1 で i。 -/
theorem gauss_sign_real (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) : zN χ = gs χ :=
```

### PAG.Part201.pull（PAG201.lean）
```lean
/-- 引き戻し π^* f = f ∘ (mod N)（N ∣ N′）。 -/
noncomputable def pull {N N' : ℕ} (h : N ∣ N') (f : ZMod N → ℂ) : ZMod N' → ℂ :=
  f ∘ (ZMod.castHom h (ZMod N)).toAddMonoidHom
```

### PAG.Part201.thmA_haar（PAG201.lean）
```lean
/-- **4. ハール正規化の定理 A（Ẑ 上の定理 A）**：thmA_general の仮定のもとで
(1/N)·zket(A) ⋆ zket(B) = φ(uc)^(−1/2)·J̃·zket(Ψ)。定数は N によらない。 -/
theorem thmA_haar (N u M c d u' M' : ℕ) [NeZero N] [NeZero c] [NeZero d] (h : u * M = N) (hc : c ∣ M)
    (hdc : d ∣ c) (h' : u' * M' = N) (hd : d ∣ M') (hu' : u' = u * (c / d))
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ N → q ∣ d)
    (A B : DirichletCharacter ℂ c) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive) (hprod : A * B = Ψ.changeLevel hdc) :
    hconv (zket u M N h c hc A) (zket u M N h c hc B)
      = ((((Real.sqrt (Nat.totient (u * c)))⁻¹ : ℝ) : ℂ) * jt c d A B Ψ) • zket u' M' N h' d hd Ψ :=
```

### PAG.Part201.zket_pull（PAG201.lean）
```lean
/-- **3a.** t の素因数がすべて M を割るなら π^* zket_N = zket_{Nt}。 -/
theorem zket_pull (u M N t : ℕ) [NeZero N] [NeZero t] (h : u * M = N) (c : ℕ) (hc : c ∣ M)
    (χ : ZMod c → ℂ) (ht : ∀ q : ℕ, q.Prime → q ∣ t → q ∣ M) :
    pull (dvd_mul_right N t) (zket u M N h c hc χ)
      = zket u (M * t) (N * t) (by rw [← h, mul_assoc]) c (hc.trans (dvd_mul_right M t)) χ :=
```

### PAG.Part206.dft_pull_apply（PAG206.lean）
```lean
/-- **1.** 𝓕(π^*f)(ξ) = [t ∣ ξ]·t·𝓕f(ξ/t)（π : ℤ/Nt → ℤ/N）。 -/
theorem dft_pull_apply (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod N → ℂ) (ξ : ZMod (N * t)) :
    𝓕 (pull (dvd_mul_right N t) f) ξ =
      if t ∣ ξ.val then (t : ℂ) * 𝓕 f ((ξ.val / t : ℕ) : ZMod N) else 0 :=
```

### PAG.Part206.oldP_eq_self_iff（PAG206.lean）
```lean
/-- **4c. 旧部分の特徴づけ**：Pg = g ⇔ g = π^*f となる f がある。 -/
theorem oldP_eq_self_iff (N t : ℕ) [NeZero N] [NeZero t] (g : ZMod (N * t) → ℂ) :
    oldP N t g = g ↔ ∃ f : ZMod N → ℂ, pull (dvd_mul_right N t) f = g :=
```

### PAG.Part218.shellAlg（PAG218.lean）
```lean
/-- 殻の射影が生成する代数 A = ⟨E_s, D_s⟩ ⊆ End(ℂ^{ℤ/N})（E_s = ε_s ⋆、D_s = 1_{D_s}·）。 -/
noncomputable def shellAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪
    Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)))
```

### PAG.Part232.leftHom（PAG232.lean）
```lean
/-- L：End(ℂ^{ℤ/a}) → End(ℂ^{ℤ/a × ℤ/b})（代数準同型）。 -/
noncomputable def leftHom (a b : ℕ) : Module.End ℂ (ZMod a → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  AlgHom.ofLinearMap
    { toFun := leftOp b
      map_add' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl }
    (LinearMap.ext fun _ => funext fun _ => rfl)
    (fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl)
```

### PAG.Part232.range_tensLift（PAG232.lean）
```lean
/-- **4b.** 像 = C(A_{ab})（= L(A_a) ⊔ R(A_b)）。 -/
theorem range_tensLift {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (tensLift a b).range = (shellAlg (a * b)).map (crtConj hab).toAlgHom :=
```

### PAG.Part232.shellAlgTensorEquiv（PAG232.lean）
```lean
/-- **代数同型** A_a ⊗ A_b ≅ A_{ab}（gcd(a, b) = 1）。 -/
noncomputable def shellAlgTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    TensorProduct ℂ (shellAlg a) (shellAlg b) ≃ₐ[ℂ] shellAlg (a * b) :=
  ((AlgEquiv.ofInjective (tensLift a b) (tensLift_injective hab)).trans
    (Subalgebra.equivOfEq _ _ (range_tensLift hab))).trans
    (Subalgebra.equivMapOfInjective (shellAlg (a * b)) (crtConj hab).toAlgHom (crtConj hab).injective).symm
```

### PAG.Part232.tensLift_injective（PAG232.lean）
```lean
/-- **4d.** S ⊗ T ↦ L(S)R(T) は単射（像の次元 = 定義域の次元）。 -/
theorem tensLift_injective {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Function.Injective (tensLift a b) :=
```

### PAG.Part240.locHom（PAG240.lean）
```lean
/-- 局所作用素 ι_k：End(ℂ^{ℤ/a_k}) → End(ℂ^{ℤ/N})（N = prodList l、代数の準同型）。
  ι_0(S) = C⁻¹(L(S))、ι_{k+1}(T) = C⁻¹(R(ι′_k(T)))（C は Part 228 の crtConj、ι′ は残りのリストのもの）。 -/
noncomputable def locHom : (l : List ℕ+) → CoprimeList l → (k : Fin l.length) →
    Module.End ℂ (ZMod ((l.get k : ℕ+) : ℕ) → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod (prodList l) → ℂ)
  | a :: l, h, ⟨0, _⟩ => (crtConj h.head).symm.toAlgHom.comp (leftHom (a : ℕ) (prodList l))
  | a :: l, h, ⟨k + 1, hk⟩ => (crtConj h.head).symm.toAlgHom.comp
      ((rightHom (a : ℕ) (prodList l)).comp (locHom l h.tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
```

### PAG.Part240.tensEquiv（PAG240.lean）
```lean
/-- **代数の同型** 繰り返しのテンソル積 ≅ X_N（N = prodList l。2 因子の同型（Part 229 の crtTensorEquiv）を繰り返す）。 -/
noncomputable def tensEquiv (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) : ∀ (l : List ℕ+) (_ : CoprimeList l), (tensAlg X l).carrier ≃ₐ[ℂ] X (prodList l)
  | [], _ => (Algebra.botEquiv ℂ (Module.End ℂ (ZMod 1 → ℂ))).symm.trans
      (Subalgebra.equivOfEq _ _ (eq_bot_of_one (X 1)).symm)
  | a :: l, h => (Algebra.TensorProduct.congr AlgEquiv.refl (tensEquiv X hX l h.tail)).trans
      (crtTensorEquiv h.head (X (a : ℕ)) (X (prodList l)) (X ((a : ℕ) * prodList l))
        (hX (a : ℕ) (prodList l) h.head))
```

### PAG.Part252.addEAlg_eq_shellAlg_iff_all（PAG252.lean）
```lean
/-- **4c.** 主定理（除外なし）：s ∈ S′ なら B_s = A_N ⇔ |S′| ≤ 2 ∨ (N が平方因子なし ∧ (s = 1 ∨ s = 2))。 -/
theorem addEAlg_eq_shellAlg_iff_all {N s : ℕ} [NeZero N] (hs : s ∈ devSet N) :
    addEAlg N s = shellAlg N ↔ (devSet N).card ≤ 2 ∨ (Squarefree N ∧ (s = 1 ∨ s = 2)) :=
```

### PAG.Part253.commute_transl_of_prime（PAG253.lean）
```lean
/-- **2d. 定理 2.6 の前提（有限レベル）**：N と互いに素なすべての素数 p について T_{k_p} と可換なら、
(ℤ/N)^× のすべての平行移動と可換。モノグラフの証明は Dirichlet の算術級数定理で {k_p} の稠密性を使ったが、
素数の類が生成することで足りる。 -/
theorem commute_transl_of_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U)
    (g : (ZMod N)ˣ) : U ∘ₗ PAG.transl g = PAG.transl g ∘ₗ U :=
```

### PAG.Part253.eigenFun_of_commute_prime（PAG253.lean）
```lean
/-- **2f.** 指標ごとのスカラーを 1 つの関数 c にまとめた形（中身は 2e と同じ）。後半の含意「|c| = 1 と
c(χ⁻¹) = conj c(χ) なら実指標で c = ±1」は U によらず、どんな関数 c でも成り立つ（Part 1 の `real_sector_sign`）。
2026-11-11 に `thm26_prime` から改名した（独立照合で、名前が内容より強いと指摘された）。定理 2.6 (a)⇒(b) の
有限レベル版として中身のある文は §6 の `thm26_full`。 -/
theorem eigenFun_of_commute_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U) :
    ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧
      ((∀ χ, ‖c χ‖ = 1) → (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) → ∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1) :=
```

### PAG.Part253.exists_cls_near（PAG253.lean）
```lean
/-- **3a. 稠密性**：(ℤ/N)^× × ℝ の任意の点 (a, t) と ε > 0 に対し、正の有理数 m/n（m, n は N と互いに素）の類
(k_m·k_n⁻¹, log n − log m)（素数イデールの積 ∏ π_p^{v_p(m/n)} の類）で、単数部分が a、対数座標が t の ε 以内のものがある。
m = 1 + Nj、n = a₀ + N⌊e^t·m/N⌋（a₀ = a の代表 + N）と取り、|n/m − e^t| < 2N/m と log の連続性を使う。 -/
theorem exists_cls_near {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (hm : m.Coprime N) (hn : n.Coprime N), 0 < m ∧ 0 < n ∧
      kUnit m hm * (kUnit n hn)⁻¹ = a ∧ |Real.log n - Real.log m - t| < ε :=
```

### PAG.Part253.thm26_full（PAG253.lean）
```lean
/-- **6f. 定理 2.6 (a)⇒(b)（有限レベル、素数版、完全な形）**：U が N と互いに素なすべての素数 p の平行移動 T_{k_p} と
可換で、標準のエルミート形について等長（ユニタリ）で、JUJ が U の随伴（JUJ = U*）なら、各指標 χ に U χ = c(χ)·χ、
|c(χ)| = 1、c(χ⁻¹) = conj c(χ)（(ℤ/N)^× の上では χ̄ = χ⁻¹ なので α_χ̄ = −α_χ）、実指標では c = ±1。 -/
theorem thm26_full {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U)
    (hiso : ∀ f g, ipG (U f) (U g) = ipG f g)
    (hadj : ∀ f g, ipG (PAG.rev (U (PAG.rev f))) g = ipG f (U g)) :
    ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧ (∀ χ, ‖c χ‖ = 1) ∧
      (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) ∧ (∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1) :=
```

### PAG.Part253.thm26_needs_commute（PAG253.lean）
```lean
/-- **7d. 仮定の除去：素数の平行移動との可換性は外せない**（N ≥ 3）。U = M_s は等長で JUJ = U* も満たすが、
指標ごとのスカラー c は取れない（自明な指標 1 が、定数でない s に写る）。2026-11-10 の独立照合で、
6f の 3 つの仮定のうち可換性を外した例がないと指摘された。 -/
theorem thm26_needs_commute {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    (∀ f g : (ZMod N)ˣ → ℂ, ipG (signMul f) (signMul g) = ipG f g) ∧
    (∀ f g : (ZMod N)ˣ → ℂ, ipG (PAG.rev (signMul (PAG.rev f))) g = ipG f (signMul g)) ∧
    ¬ ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, ∀ χ, signMul (PAG.charFun χ) = c χ • PAG.charFun χ :=
```

### PAG.Part254.chainIn（PAG254.lean）
```lean
/-- S の中の、d で測った歩幅が ε 未満の鎖で x と y がつながる。 -/
def chainIn {α : Type*} (S : Set α) (d : α → α → ℝ) (ε : ℝ) (x y : α) : Prop :=
  ∃ (n : ℕ) (c : ℕ → α), c 0 = x ∧ c n = y ∧ (∀ i, i ≤ n → c i ∈ S) ∧ ∀ i, i < n → d (c i) (c (i + 1)) < ε
```

### PAG.Part254.chainIn_dInf（PAG254.lean）
```lean
/-- **3b. 無限素点の側は well-chained**：どの ε > 0 でも、正の有理数の任意の 2 点は d_∞ の歩幅 ε 未満の鎖でつながる
（q と r を結ぶ線分の等分点を通る）。 -/
theorem chainIn_dInf {ε : ℝ} (hε : 0 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat dInf ε q r :=
```

### PAG.Part254.dInf_eq_dist（PAG254.lean）
```lean
/-- **6a.** d_∞ は log による ℝ の距離の引き戻し：d_∞(q, r) = dist(log q, log r)。1e と合わせると、
(正の有理数, d_∞) は ℝ の稠密な部分集合と等長（完備化が ℝ であること自体は Lean にしていない）。 -/
theorem dInf_eq_dist (q r : ℚ) : dInf q r = dist (Real.log q) (Real.log r) :=
```

### PAG.Part254.dense_logSet（PAG254.lean）
```lean
/-- **1e.** logSet は ℝ の中で稠密。 -/
theorem dense_logSet : Dense logSet :=
```

### PAG.Part254.not_forall_chainIn_dP（PAG254.lean）
```lean
/-- **6d. 2 つの側を分ける基準**：素数 p では、「どの ε > 0 でもすべての 2 点が d_p の鎖でつながる」は成り立たない
（d_∞ では成り立つ：3b）。 -/
theorem not_forall_chainIn_dP (p : ℕ) (hp : p.Prime) :
    ¬ ∀ ε : ℝ, 0 < ε → ∀ q r : ℚ, 0 < q → 0 < r → chainIn posRat (dP p) ε q r :=
```

### PAG.Part255.dense_closure_allPrimes（PAG255.lean）
```lean
/-- **3d. 射影極限での稠密性**：すべての素数の類 (κ_p, −log p) が生成する unitSys × ℝ の部分群は稠密。 -/
theorem dense_closure_allPrimes :
    Dense ((Subgroup.closure (primeGens 1) : Subgroup (unitSys × Multiplicative ℝ)) :
      Set (unitSys × Multiplicative ℝ)) :=
```

### PAG.Part255.dense_closure_primeGens（PAG255.lean）
```lean
/-- **3c. 射影極限での稠密性（有限個の素数を除いた形）**：L ≥ 1 を割らない素数の類 (κ_p, −log p) が生成する
unitSys × ℝ の部分群は稠密。 -/
theorem dense_closure_primeGens (L : ℕ+) :
    Dense ((Subgroup.closure (primeGens L) : Subgroup (unitSys × Multiplicative ℝ)) :
      Set (unitSys × Multiplicative ℝ)) :=
```

### PAG.Part255.primeSys_unique（PAG255.lean）
```lean
/-- **2d. κ_p の一意性**：両立する系 a が、p ∤ N のすべてのレベルで p⁻¹ に等しく、p の冪のレベルに落とすと 1 なら、a = κ_p。
2a・2c と合わせて、κ_p は「p 成分が 1、ほかの成分が p⁻¹」で決まるただ 1 つの元。 -/
theorem primeSys_unique (p : ℕ) (hp : p.Prime) (a : unitSys)
    (h1 : ∀ (N : ℕ+) (hpN : p.Coprime N), (a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = kUnit p hpN)
    (h2 : ∀ (N : ℕ+) (k : ℕ) (h : p ^ k ∣ (N : ℕ)),
      ZMod.unitsMap h ((a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N) = 1) :
    a = primeSys p hp :=
```

### PAG.Part255.unitSys（PAG255.lean）
```lean
/-- 射影極限：レベル N ≥ 1 ごとの単数の、自然な写像で両立する系の全体。 -/
def unitSys : Subgroup (∀ N : ℕ+, (ZMod (N : ℕ))ˣ) where
  carrier := {a | ∀ (N M : ℕ+) (h : (N : ℕ) ∣ (M : ℕ)), ZMod.unitsMap h (a M) = a N}
  mul_mem' := by
    intro a b ha hb N M h
    rw [Pi.mul_apply, map_mul, ha N M h, hb N M h, Pi.mul_apply]
  one_mem' := by
    intro N M h
    rw [Pi.one_apply, map_one, Pi.one_apply]
  inv_mem' := by
    intro a ha N M h
    rw [Pi.inv_apply, map_inv, ha N M h, Pi.inv_apply]
```

### PAG.Part256.JH（PAG256.lean）
```lean
/-- 単数の上の関数への J∘H_N/√N：(J H_N f)(u)/√N = (H_N f)(u⁻¹)/√N。 -/
noncomputable def JH (f : ZMod N → ℂ) (u : (ZMod N)ˣ) : ℂ :=
  hartley f ((u⁻¹ : (ZMod N)ˣ) : ZMod N) / (Real.sqrt N : ℂ)
```

### PAG.Part256.JH_eq_rootNum_mul_any（PAG256.lean）
```lean
/-- **単数の上の固有値の式（すべての指標）**：(J H_N χ)(u)/√N = W(χ)·χ(u)。W(χ) = rootNum χ = ε(χ)τ(χ)/√N。
原始指標では W(χ) はルート数で |W(χ)| = 1（`normSq_rootNum`）。 -/
theorem JH_eq_rootNum_mul_any (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u :=
```

### PAG.Part256.hartley_eq_zero_of_not_isUnit（PAG256.lean）
```lean
/-- **単数でないところで H_N χ = 0**（χ 原始的）。 -/
theorem hartley_eq_zero_of_not_isUnit {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {y : ZMod N} (hy : ¬IsUnit y) : hartley (χ : ZMod N → ℂ) y = 0 :=
```

### PAG.Part256.normSq_rootNum（PAG256.lean）
```lean
/-- |W(χ)|² = 1（χ 原始的。Part 12（PAG16）の |τ(χ)|² = N から）。 -/
theorem normSq_rootNum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (rootNum χ) = 1 :=
```

### PAG.Part256.parFac（PAG256.lean）
```lean
/-- パリティ因子 ε(χ) = ((1 − i) + (1 + i)χ(−1))/2。 -/
noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2
```

### PAG.Part256.removal_counterexample（PAG256.lean）
```lean
/-- 除去テストの反例：原始性を外すと「単数でないところで 0」が破れる（法 2 の自明な指標、y = 0）。 -/
theorem removal_counterexample :
    ¬(1 : DirichletCharacter ℂ 2).IsPrimitive ∧ ¬IsUnit (0 : ZMod 2) ∧
      hartley ((1 : DirichletCharacter ℂ 2) : ZMod 2 → ℂ) 0 = 1 :=
```

### PAG.Part256.removal_counterexample_four（PAG256.lean）
```lean
/-- 除去テストの反例（原始指標がある法 4 で。独立照合 B の指摘を受けて追加）：法 4 には原始指標があるが
（Part 140 の `exists_primitive`）、自明な指標（原始的でない）では、単数でない 2 で H_N χ (2) = −2 ≠ 0、
|W|² = 0（τ = i − i = 0）。法 2 の反例と違い、原始指標のある法でも原始性を外すと 2 つの文が破れることを示す。 -/
theorem removal_counterexample_four :
    (∃ χ : DirichletCharacter ℂ (2 ^ 2), χ.IsPrimitive) ∧
    ¬(1 : DirichletCharacter ℂ 4).IsPrimitive ∧ ¬IsUnit (2 : ZMod 4) ∧
      hartley ((1 : DirichletCharacter ℂ 4) : ZMod 4 → ℂ) 2 = -2 ∧
      Complex.normSq (rootNum (1 : DirichletCharacter ℂ 4)) = 0 :=
```

### PAG.Part256.removal_counterexample_normSq（PAG256.lean）
```lean
/-- 法 2 の自明な指標で |rootNum|² = 1/2。原始的でないことは `removal_counterexample` の第 1 成分で、2 つを合わせて
|W| = 1 の除去テストの反例になる。 -/
theorem removal_counterexample_normSq :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ 2)) = 1 / 2 :=
```

### PAG.Part256.rootNum（PAG256.lean）
```lean
/-- W(χ) = τ(χ)/(i^a √N)（a = 0 は偶、a = 1 は奇）。χ が原始ならルート数（関数等式との一致は Lean の外）。原始的でない
χ ではルート数ではなく、0 にもなる（法 4 の自明な指標）。
内部照合（2026-11-14）：Part 192（PAG196）の `zN` を Part 194（PAG198）の `gs` で割ったものと同じ値（Lean で確認）。 -/
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))
```

### PAG.Part257.TopL_charU（PAG257.lean）
```lean
/-- **1.** すべての指標で T χ = W(χ)χ（Part 252 の `JH_eq_rootNum_mul_any` の作用素の形）。 -/
theorem TopL_charU (χ : DirichletCharacter ℂ N) : TopL (charU χ) = rootNum χ • charU χ :=
```

### PAG.Part257.TopL_eq_of_A1（PAG257.lean）
```lean
/-- **5.** 原始指標で U χ = W(χ)χ を満たす（A1 の位相を原始部分に課した）任意の線形写像 U は、V_prim の上で
T に等しい。A1 の読み替えで、A1 を外すと結論は消える。 -/
theorem TopL_eq_of_A1 (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → U (charU χ) = rootNum χ • charU χ)
    {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : U f = TopL f :=
```

### PAG.Part257.unitary_Vprim（PAG257.lean）
```lean
/-- **9a.** V_prim の上で T はユニタリ：V_prim の自己線形同型 e で、値は T、内積を保つものがある
（`TopL_mem_Vprim`・`map_TopL_Vprim`・`ip_TopL_of_mem_Vprim`・`eq_zero_of_ip_self` を 1 つの文に）。 -/
theorem unitary_Vprim : ∃ e : Vprim N ≃ₗ[ℂ] Vprim N,
    (∀ f : Vprim N, ((e f : Vprim N) : (ZMod N)ˣ → ℂ) = TopL (f : (ZMod N)ˣ → ℂ)) ∧
    ∀ f g : Vprim N, ip ((e f : Vprim N) : (ZMod N)ˣ → ℂ) ((e g : Vprim N) : (ZMod N)ˣ → ℂ) =
      ip (f : (ZMod N)ˣ → ℂ) (g : (ZMod N)ˣ → ℂ) :=
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

### PAG.Part258.UA1_family_unique（PAG258.lean）
```lean
/-- **両立する族の一意性**（独立照合 A の指摘で追加）：各法で原始部分の上では T と一致し、引き戻しと両立する
作用素の族は U_N だけ。原始的でない指標の上の位相は、両立から決まる（仮定に A1 の位相は原始部分にしか入らない）。 -/
theorem UA1_family_unique (U : ∀ a : Lvl, Gsp a →ₗ[ℂ] Gsp a)
    (hT : ∀ (a : Lvl) (f : Gsp a), f ∈ Vprim a.val → U a f = TopL f)
    (hc : ∀ (a b : Lvl) (h : a ≤ b) (f : Gsp a), U b (pullSys a b h f) = pullSys a b h (U a f))
    (a : Lvl) : U a = UA1 :=
```

### PAG.Part258.Uinf（PAG258.lean）
```lean
/-- 極限の作用素 U_∞：各法の U_N が引き戻しと両立することから。 -/
noncomputable def Uinf : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map (fun a => UA1 (N := a.val)) (fun a b h => by
    refine LinearMap.ext (fun f => ?_)
    exact UA1_comp_pullL (N := a.val) (M := b.val) h f)
```

### PAG.Part258.Uinf_unique（PAG258.lean）
```lean
/-- U_∞ は各法で U_N となる線形写像として一意。 -/
theorem Uinf_unique (V : Lim →ₗ[ℂ] Lim) (hV : ∀ a (f : Gsp a), V (ofL a f) = ofL a (UA1 f)) :
    V = Uinf :=
```

### PAG.Part258.condPart_eq_map（PAG258.lean）
```lean
/-- 導手が q の指標が張る部分は π_{q→M}(V_prim(q))（q ∣ M）。 -/
theorem condPart_eq_map {M : ℕ} [NeZero M] (hNM : N ∣ M) :
    condPart M N = (Vprim N).map (pullL hNM) :=
```

### PAG.Part258.ipLim_Uinf（PAG258.lean）
```lean
/-- U_∞ は極限の内積を保つ。 -/
theorem ipLim_Uinf (z w : Lim) : ipLim (Uinf z) (Uinf w) = ipLim z w :=
```

### PAG.Part258.phaseA1（PAG258.lean）
```lean
/-- A1 の位相 phaseA1(χ) = W(χ*)（χ* は χ を誘導する原始指標）。 -/
noncomputable def phaseA1 (χ : DirichletCharacter ℂ N) : ℂ := rootNum χ.primitiveCharacter
```

### PAG.Part259.BoxCoord（PAG259.lean）
```lean
/-- 有限素点の座標の組（`Nat.Primes → ℤ`）に離散位相を入れた型（読みでは、すべての素点を同時に測る位相）。
`Nat.Primes → ℤ` の直積の位相（各近傍は有限個の素点しか測らない）と、集合としては同じで位相だけが違う。ℤ 値の座標では
離散位相は箱・一様の位相と同じ、は Lean の外の標準の事実。 -/
def BoxCoord : Type := Nat.Primes → ℤ
```

### PAG.Part259.dense_imgST_iff（PAG259.lean）
```lean
/-- **閾値の二分法（片側）**：S が素数の有限集合で T ⊆ S のとき、像 `imgST S T` が ℝ × ℤ^T で稠密 ⇔ T の外に S の異なる
素数が 2 つある（T ⊆ S は必要：S = {2, 3}、T = {5} では右辺は真で左辺は偽）。 -/
theorem dense_imgST_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    Dense (imgST S T) ↔ ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T :=
```

### PAG.Part259.eq_of_padicValRat_eq（PAG259.lean）
```lean
/-- **1b. 全解像度の単射**（素因数分解の一意性）：すべての素数で付値が一致する正の有理数は等しい。 -/
theorem eq_of_padicValRat_eq {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (h : ∀ p : ℕ, p.Prime → padicValRat p q = padicValRat p r) : q = r :=
```

### PAG.Part259.isClosed_discrete_imgST（PAG259.lean）
```lean
/-- **閾値の二分法（もう片側）**：T の外に S の異なる素数が 2 つないとき（測らない素数が高々 1 つ）、像 `imgST S T` は
ℝ × ℤ^T の中で閉かつ離散。 -/
theorem isClosed_discrete_imgST (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime)
    (h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r) :
    IsClosed (imgST S T) ∧ DiscreteTopology (imgST S T) :=
```

### PAG.Part259.isClosed_discrete_rhoBox_image（PAG259.lean）
```lean
/-- **有限素点の座標に離散位相を入れると、像は閉かつ離散**（独立照合 B の指摘で追加）。素因数分解の一意性を離散位相で
言い直した文で、log の成分は使わない。同じ集合が直積の位相では稠密（`dense_rho_image`）で、離散になるかどうかは
有限台ではなく位相の選び方で決まる（`rho_one_mem_closure_ne_one` の近似点も正の有理数なので有限台）。 -/
theorem isClosed_discrete_rhoBox_image :
    IsClosed (rhoBox '' {q : ℚ | 0 < q}) ∧ DiscreteTopology (rhoBox '' {q : ℚ | 0 < q}) :=
```

### PAG.Part259.log_eq_sum_of_support（PAG259.lean）
```lean
/-- **1e. 積公式**：⟨S⟩ の元では log q = Σ_{s∈S} v_s(q)·log s（全解像度では ∞ の座標は有限素点の座標から決まる）。 -/
theorem log_eq_sum_of_support (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) {q : ℚ} (hq : 0 < q)
    (hsupp : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) :
    Real.log q = ∑ s ∈ S, (padicValRat s q : ℝ) * Real.log s :=
```

### PAG.Part259.rhoBox（PAG259.lean）
```lean
/-- ρ と同じ写像を、値域の有限素点の座標に離散位相（すべての素点を同時に測る）を入れて考える。 -/
noncomputable def rhoBox (q : ℚ) : ℝ × BoxCoord := (Real.log q, fun p => padicValRat p q)
```

### PAG.Part259.threshold_iff（PAG259.lean）
```lean
/-- **閾値の定理**（基礎 ⟨S⟩、T ⊆ S、∞ と T の素数を測る）：像の閉包がある水平な直線 ℝ × {k} 全体を含む
⇔ T の外に S の異なる素数が 2 つある（測らない素数が 2 つ以上）。 -/
theorem threshold_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    (∃ k : T → ℤ, ∀ x : ℝ, (x, k) ∈ closure (imgST S T)) ↔
      ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T :=
```

### PAG.Part260.crossSign（PAG260.lean）
```lean
/-- 偶奇の符号 s：χ₁, χ₂ がともに奇なら −1、それ以外は +1（交差項 χ₁(N)·χ₂(M) とは別の因子）。
内部照合（2026-11-14）：Part 194（PAG198）の `rs` と同じ値（式は違う。χ(−1) = ±1 による。Lean で確認）。 -/
noncomputable def crossSign (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
  if χ₁.Odd ∧ χ₂.Odd then -1 else 1
```

### PAG.Part260.parFac_prodChar（PAG260.lean）
```lean
/-- 偶奇の因子のずれ：ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)（ε = parFac は偶で 1、奇で −i）。ε が無限素点の局所因子にあたる、は読み。 -/
theorem parFac_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.parFac (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * PAG.Part256.parFac χ₁ * PAG.Part256.parFac χ₂ :=
```

### PAG.Part260.rootNum_prodChar（PAG260.lean）
```lean
/-- **交差項の法則**：互いに素な法で W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)。原始性は要らない（W がルート数なのは原始のとき）。
内部照合（2026-11-14）：中身は Part 189（PAG193）の `z_mul_coprime`・`gaussSum_mul_coprime`（後者はこの Part の `gaussSum_prodChar` と同じ文）に、偶奇の因子のずれ（Part 194 の `gs_combine` と同じ形）を足したもの（照合者の判定は D で C との境目。Lean ではつないでいない）。 -/
theorem rootNum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.rootNum (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂) :=
```

### PAG.Part261.gaussSum_primeFactors（PAG261.lean）
```lean
/-- **すべての素数への分解**：法 n の指標 Ψ は、素数冪の法 p^{v_p(n)} の成分 χ_p の積で（自然数での値が ∏ χ_p）、
τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)})（形 (II)）。 -/
theorem gaussSum_primeFactors (n : ℕ) [NeZero n] (Ψ : DirichletCharacter ℂ n) :
    ∃ χ : ∀ p, DirichletCharacter ℂ (p ^ n.factorization p),
      (∀ x : ℕ, Ψ x = (n.primeFactors.toList.map fun p => χ p (x : ZMod (p ^ n.factorization p))).prod) ∧
      gaussSum Ψ stdAddChar = (n.primeFactors.toList.map fun p => gaussSum (χ p) stdAddChar *
        ((n.primeFactors.toList.erase p).map fun q => χ q ((p ^ n.factorization p : ℕ) : ZMod (q ^ n.factorization q))).prod).prod :=
```

### PAG.Part261.parFac_listChar（PAG261.lean）
```lean
/-- **∞ の因子の符号**：ε_∞(χ) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数。Part 256 の s の一般化）。 -/
theorem parFac_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    PAG.Part256.parFac (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) *
        (l.map fun i => PAG.Part256.parFac (χ i)).prod :=
```

### PAG.Part261.rootNum_listChar_formII（PAG261.lean）
```lean
/-- **W の分解（形 (II)）**：W(χ) = ε_∞(χ)·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)。 -/
theorem rootNum_listChar_formII (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hnd : l.Nodup) :
    PAG.Part256.rootNum (listChar χ l) = PAG.Part256.parFac (listChar χ l) *
      (l.map fun i => gaussSum (χ i) stdAddChar / ((Real.sqrt (N i) : ℝ) : ℂ) *
        ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod).prod :=
```

### PAG.Part262.exists_compatible_hom（PAG262.lean）
```lean
/-- **存在（互いに素な段）**：gcd(a, b) = 1 なら、代数準同型 φ : A_a → A_{ab} で、
(i) すべての S で φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合、を満たすものがある。 -/
theorem exists_compatible_hom (hab : a.Coprime b) :
    ∃ φ : shellAlg a →ₐ[ℂ] shellAlg (a * b),
      (∀ (S : shellAlg a) (f : ZMod a → ℂ),
        (φ S : Module.End ℂ (ZMod (a * b) → ℂ)) (PAG.Part201.pull (dvd_mul_right a b) f) =
          PAG.Part201.pull (dvd_mul_right a b) ((S : Module.End ℂ (ZMod a → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind (a * b) t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps (a * b) t))) :=
```

### PAG.Part262.exists_compatible_hom_iff（PAG262.lean）
```lean
/-- **二分法**：N ∣ M のとき、(i)(ii) を満たす代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、かつそのときに限る。 -/
theorem exists_compatible_hom_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) :
    (∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)))) ↔
    Nat.Coprime N (M / N) :=
```

### PAG.Part262.no_compatible_hom（PAG262.lean）
```lean
/-- **不存在（gcd(N, M/N) > 1 の段）**：素数 p が N と M/N の両方を割るなら、代数準同型 φ : A_N → A_M で、
(i) すべての S で φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合、を満たすものはない。
証明に使うのは s = N の D_N・E_N と、A_N の関係 D_N E_N D_N = (1/N) D_N、E_N² = E_N だけ。 -/
theorem no_compatible_hom {N M p : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (hp : p.Prime) (hpN : p ∣ N)
    (hpk : p ∣ M / N) :
    ¬ ∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t))) :=
```

### PAG.Part262.shellLift（PAG262.lean）
```lean
/-- 互いに素な a, b で、A_a → A_{ab}、S ↦ Θ(S ⊗ 1)（Θ は Part 228 の `shellAlgTensorEquiv`）。 -/
noncomputable def shellLift (hab : a.Coprime b) : shellAlg a →ₐ[ℂ] shellAlg (a * b) :=
  (shellAlgTensorEquiv hab).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft : shellAlg a →ₐ[ℂ] TensorProduct ℂ (shellAlg a) (shellAlg b))
```

### PAG.Part263.UDvd（PAG263.lean）
```lean
/-- 互いに素な段：N ∣ M かつ gcd(N, M/N) = 1。 -/
def UDvd (N M : ℕ) : Prop := N ∣ M ∧ Nat.Coprime N (M / N)
```

### PAG.Part263.canon_comp（PAG263.lean）
```lean
/-- **帰納系**：互いに素な段 N → M → L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}。 -/
theorem canon_comp (h1 : UDvd N M) (h2 : UDvd M L) :
    (canon h2.1 h2.2).comp (canon h1.1 h1.2) = canon (udvd_trans h1 h2).1 (udvd_trans h1 h2).2 :=
```

### PAG.Part263.compatF_iff_eq_shellLift（PAG263.lean）
```lean
/-- (i)(ii)(iii) を満たす A_a → A_{ab} は `shellLift` だけ（gcd(a, b) = 1）。 -/
theorem compatF_iff_eq_shellLift (hab : a.Coprime b) (φ : shellAlg a →ₐ[ℂ] shellAlg (a * b)) :
    CompatF (dvd_mul_right a b) φ ↔ φ = shellLift hab :=
```

### PAG.Part263.existsUnique_compatF_iff（PAG263.lean）
```lean
/-- **一意な存在の二分法**：N ∣ M のとき、(i)(ii)(iii) を満たす代数準同型 A_N → A_M が
ちょうど 1 つあるのは gcd(N, M/N) = 1 のとき、かつそのときに限る。 -/
theorem existsUnique_compatF_iff (hNM : N ∣ M) :
    (∃! φ : shellAlg N →ₐ[ℂ] shellAlg M, CompatF hNM φ) ↔ Nat.Coprime N (M / N) :=
```

### PAG.Part263.not_existsUnique_compat（PAG263.lean）
```lean
/-- **(iii) を外すと一意でない場合がある（a = 2 の例）**：gcd(2, b) = 1、1 < b のとき、Part 258 の条件 (i)(ii) だけを
課すと、それを満たす A_2 → A_{2b} は一意でない（`shellLift` と φ'。2 つあることは `compat_twLift`・`compatF_shellLift`・
`twLift_ne_shellLift` による）。 -/
theorem not_existsUnique_compat (hab : Nat.Coprime 2 b) (hb : 1 < b) :
    ¬ ∃! φ : shellAlg 2 →ₐ[ℂ] shellAlg (2 * b), Compat (dvd_mul_right 2 b) φ :=
```

### PAG.Part263.not_isDirected_udvd（PAG263.lean）
```lean
/-- **有向でない**（照合 B の指摘で追加）：ℕ の上の UDvd は有向でない（p = 2 の場合）。 -/
theorem not_isDirected_udvd : ¬ IsDirected ℕ UDvd :=
```

### PAG.Part263.sqLim（PAG263.lean）
```lean
/-- 無平方数の段の帰納極限（ℂ 加群として）。 -/
abbrev sqLim : Type :=
  Module.DirectLimit (fun S : Finset Nat.Primes => shellAlg (primeProd S))
    (fun S T h => (sqMap S T h).toLinearMap)
```

### PAG.Part263.sqLim_of_injective（PAG263.lean）
```lean
/-- 各段 A_{N_S} は極限に単射で入る。 -/
theorem sqLim_of_injective (S : Finset Nat.Primes) :
    Function.Injective (Module.DirectLimit.of ℂ (Finset Nat.Primes)
      (fun S : Finset Nat.Primes => shellAlg (primeProd S)) (fun S T h => (sqMap S T h).toLinearMap) S) :=
```

### PAG.Part263.twLift（PAG263.lean）
```lean
/-- **捩れた写像** A_2 → A_{2b}：φ'(S) = Θ(S ⊗ E_b + ψ(S) ⊗ (1 − E_b))。 -/
noncomputable def twLift (hab : Nat.Coprime 2 b) : shellAlg 2 →ₐ[ℂ] shellAlg (2 * b) :=
  (shellAlgTensorEquiv hab).toAlgHom.comp twTens
```

## §C ノートの冒頭

### notes/pag2_part249_idele_class_density.md（冒頭 45 行）

# アーデル射影幾何 — Part 249（PAG 2.0）：素数イデールの類はイデール類群で稠密な部分群を生成する（有限レベル C_ℚ/U_N の上での単数の作用とスケーリング）

2026-11-07（2026-11-11 に独立照合の結果で訂正：§7 の最後の項。2026-11-08 の午前に訂正：§7。定理 2.6 の後半の書き方を、Lean の文の強さに合わせた。同じ日の午後に追補 §0.8：定理 2.6 (a)⇒(b) の有限レベル版を完全な形で Lean にした）。著者の選択 B-3 に従い、イデール類群 C_ℚ の上で単数の作用 U_a とスケーリング（モノグラフの D）を合わせました。素数イデールの類 [π_p] = (k_p, −log p) は、この 2 つの組です。結論は「素数イデールの類だけで C_ℚ の作用が足りる（生成する部分群が稠密）」で、これを有限レベルのモデルのすべての N について Lean で示しました（PAG253.lean。最初の版は 27 項目と定義 7 個で、11-08 の追補の後は 40 項目と定義 8 個）。副産物として、モノグラフの定理 2.6 の証明に使われていた Dirichlet の算術級数定理が不要であることもわかりました。

**問いの出所（CLAUDE.md §4・§7）。**
- 本来の道の (B)「無限素点を含む大域対象」です。著者が B-3（C_ℚ ≅ ℝ_{>0} × Ẑ^× の上で U_a と D を合わせる）を選びました。
- 問いは次のとおりです。モノグラフの素数シフト T_p は、単数 k_p ∈ Ẑ^× の作用とスケーリング −log p の合成です（T_p = M_p ∘ S_{−log p}）。素数シフトだけで、C_ℚ の作用（単数の作用もスケーリングも）が回復するか。
- 有限レベルの代数 A_N（Part 199〜248）とは、単数の殻 (ℤ/N)^× を通してつながります（§0.6）。

**着手前の報告（2026-11-07 22:10 ごろ、CLAUDE.md §7）。** 構造を作る前に、文献名と Mathlib の対応をユーザーに報告しました（§5 の検索ログ）。そのとき、前の版の「Mathlib にはイデール類群がない」を訂正しました。`IdeleGroup`・`IdeleClassGroup` の定義はあります。ただし、C_ℚ ≅ ℝ_{>0} × Ẑ^× の構造定理はありません。

- **結論（Lean、N ≥ 1 のすべての N）。**
  - 素数の類 k_p ≡ p⁻¹ (mod N) は (ℤ/N)^× を生成します（n を素因数に分けるだけ）。
  - 正の有理数 m/n の類 (k_m·k_n⁻¹, log n − log m) は、(ℤ/N)^× × ℝ で稠密です。m, n は、有限個の素数を避けて取れます。この点が素数イデールの積の類であることは、§0.1 の同一視による解釈です（Lean の文は (ℤ/N)^× × ℝ の点についての主張）。
  - 帰結は 2 つです。素数シフトで不変で、対数座標について連続な関数は定数です。χ(k)·e^{iλu} の形の関数は、Euler データ χ(k_p)·p^{−iλ} で決まります（C_ℚ/U_N の連続な指標がすべてこの形であることは既知で、Lean にはしていません）。
- **大域への読み替え（既知の事実による推論。Lean ではない）。** Ẑ^× の位相では、開部分群 U_N たちが単位元の近傍の基本系です。だから「すべての N で稠密」は「C_ℚ ≅ Ẑ^× × ℝ で稠密」と同じです。構造定理も、この同値の議論も Lean にはしていません。
- **定理 2.6 について（Lean）。** N と互いに素なすべての素数 p の平行移動 T_{k_p} と可換な作用素は、(ℤ/N)^× のすべての平行移動と可換です。よって指標ごとにスカラーで働きます。
  - 後半（|c| = 1、c(χ⁻¹) = conj c(χ)、実指標では ±1）も、U のユニタリ性と JUJ = U* から Lean で導きました（§0.8 の `thm26_full`、2026-11-08 の追補）。逆向き (b)⇒(a) は数値だけです（step272 の (9a)）。
  - モノグラフの証明は、Dirichlet の算術級数定理で集合 {k_p} の稠密性を使っていました。可換子の議論には、素数の類が生成する部分群で足ります。Lean で示したのは有限レベルの形です（`commute_transl_of_prime`）。大域の Ẑ^× で同じことを言うには、平行移動の連続性による極限の議論が要り、そこは Lean 外です。
  - これは証明の簡略化で、新しい定理ではありません。
- **Lean の追補（2026-11-11、著者の了承）。** 独立照合で出た 3 点を PAG253 の §7 に入れました：T_p F = F の形から M_a・S_s での不変性を出す系（`shift_invariant_of_prime_invariant`）、可換性を外した反例（`thm26_needs_commute`、U = M_s、N ≥ 3）、`thm26_prime` の `eigenFun_of_commute_prime` への改名。PAG253 は 46 項目と定義 9 個になりました。
- **独立照合（2026-11-10〜11、§7）。** 会話の文脈を渡さない新しいエージェント 3 つで、形式文の逆翻訳、盲検の命名、主張との照合を行いました。40 文の本体はすべて主張と同じ強さでした。直したのは、Lean の印の下に混じっていた注釈と、名前だけが強い `thm26_prime` の扱いです。
- **観察（数値だけ）。** A_N の単数の殻の角 D_1 A_N D_1 は、指標の基底で「導手だけの関数」になっていました（N ≤ 40 で 39/39）。
  - ここから、定理 2.6 の境界ユニタリのうち A_N の角に入るのは、導手ごとの符号 ±1 だけだと読めます（推論）。
  - 公理 A1 のユニタリ（固有値はルート数 W(χ)）は入りません。有限レベルの代数はルート数の位相を見ません。
- **新規性。** このパートの主張はすべて［既知］か［再導出］です。新規候補はありません（§0.7）。
- **限界。**
  - 構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0} は Lean にしていません。Lean の主張は有限レベルのモデル (ℤ/N)^× × ℝ の上のものです。
  - 素数そのものの類（群ではなく集合）の稠密性は、算術級数の素数定理の範囲です。Lean にはしていません（数値 (8) は観察）。
- **やり直し。** 試しのファイルは T1 を 2 回、T2 を 2 回コンパイルしました。PAG253 は 1 回目で通りました。数値照合は 1 回の実行ですべて合格しました。
- **環境。** Mathlib の追加ビルドはありません。Dirichlet の定理（`Nat.forall_exists_prime_gt_and_eq_mod`）も `IdeleClassGroup` もこの Mathlib にありますが、未ビルドです（依存はそれぞれ 301・145 モジュール）。どちらも使わずに済みました。

## 0. 結論

### 0.1 設定［既知］

- **イデール類群。** C_ℚ = 𝔸_ℚ^×/ℚ^× ≅ Ẑ^× × ℝ_{>0} です（ℚ の類数が 1 で、単数が ±1 のため）。対数座標を u = log ノルム とします（モノグラフの命題 2.1）。
- **素数イデールの類。** π_p は p 進の成分だけが p のイデールです。その類は [π_p] = (k_p, −log p) で、k_p = (p⁻¹)_{ℓ ≠ p} ∈ Ẑ^× です。
- **有限レベル。** U_N = ker(Ẑ^× → (ℤ/N)^×) とすると、C_ℚ/U_N ≅ (ℤ/N)^× × ℝ です。p ∤ N なら k_p ≡ p⁻¹ (mod N) です。
- **作用素（モノグラフ）。**
  - 素数シフト T_p = M_p ∘ S_{−log p}
  - 反転 W(k, u) = (k⁻¹, −u)
  - スケーリングの生成子 D = −i∂_u
  - Lean では境界（カットオフ Λ と境界ユニタリ）を入れず、(ℤ/N)^× × ℝ 上の関数への作用として定義しました。
- **注意。** ここでの N は合同部分群 U_N のレベルです。著者の言う解像度のパラメータとは同一視しません（CLAUDE.md §1）。

### notes/pag2_part250_resolution_emergence.md（冒頭 45 行）

# アーデル射影幾何 — Part 250（PAG 2.0）：解像度と創発の定式化の試み

2026-11-11。PAG254.lean（28 項目と定義 6 個）、step273.py（9 項目）。独立照合 B の指摘で、言葉が形式文を超えていた箇所を直した版です（§7）。

- **問いの出所。** 著者の選択です（2026-11-11、Part 249 の後の候補から「(C) 解像度と創発の定式化」）。
- **定式化の出所。** Claude の案 1・2 を、著者が了承したものです（「推奨の案 1 と案 2 を合わせた形で進めてください」）。著者の定義そのものではありません。
- **問い（幾何・大域・極限の言葉で）。** 離散的な基礎から、どの粗視化のもとで、どの連続対象が極限として現れるか。現れる対象は粗視化の取り方によるか。
- **結論（Lean）。** 基礎を正の有理数の群（素数が生成する可算群）に置くと、次が成り立ちます。
  - log(ℚ_{>0}) は ℝ の部分集合として可算で、区間を含まず、全不連結です（連結な部分集合は 1 点以下）。
  - 無限素点の側の擬距離 d_∞ = |log q − log r| では、どの歩幅 ε > 0 でも任意の 2 点が鎖でつながります（well-chained）。d_∞ は log による ℝ の距離の引き戻しで、像は ℝ で稠密です。
  - 素数 p の側の擬距離 d_p = |v_p(q) − v_p(r)| では、0 < ε ≤ 1 のとき鎖でつながる ⇔ v_p が等しい、ε > 1 のときすべてつながります。「どの ε > 0 でもつながる」は成り立ちません。d_p は v_p による ℝ の距離の引き戻しで、像は ℤ の中にあり、ℝ で稠密ではありません。
  - 無限素点の側でも、1 個の p の冪 {p^k} の中では ε ≤ log p の鎖は動けません。log 2 と log 3 が生成する加法群は ℝ で稠密です。
- **2 つの側を分ける基準（独立照合 B の指摘を受けて明確にした点）。** Lean の文で d_∞ と d_p を分けているのは、次の 2 つです。
  - 「どの ε > 0 でも鎖でつながるか」：d_∞ は成り立ち（`chainIn_dInf`）、d_p は成り立たない（`not_forall_chainIn_dP`）。
  - 「ℝ の中の等長な像が稠密か」：d_∞ は稠密（`dInf_eq_dist` と `dense_logSet`）、d_p は稠密でない（`dP_eq_dist` と `half_le_abs_padicValRat_sub_half`）。
- **「創発」の案の限界（正直な記録）。** 着手時の案は「解像度を落とす = 鎖でつながる点を区別しない」でした。この読みでは、d_∞ の側の商はどの ε > 0 でも 1 点で、ℝ にはなりません。ℝ が現れるのは、稠密な等長像の閉包（完備化）という別の操作によります。つまり、この形式化は「直線が、解像度を落とした商として現れる」ことは示していません。示したのは「連続な対象 ℝ の中に、全不連結だがどの尺度でも鎖でつながる稠密な部分集合として基礎が入っている」ことです。しかも ℝ は logSet と d_∞ の定義に最初から使われています。「離散的な基礎だけから連続対象が出る」ことの形式化にはなっていません（確信度：高）。
- **位置づけ（正直な評価）。** どれも既知の事実で、照合 A の判定では「深い文は一つもない」です。中心の主張は「ℚ は連結でないが well-chained（鎖連結）である」という教科書の例を対数座標で述べたもので、新しい定理はありません（確信度：高）。このパートの中身は、著者の言葉（解像度、創発）を既存の言葉（ε-鎖、一様連結性、素点ごとの付値）に対応づける 1 つの案を、Lean で検証できる形にしたことです。この案が著者の意図に合うかは、著者の判断です。
- **独立照合（§7）。** パートを閉じる前に、会話の文脈を渡さない新しいエージェントで逆翻訳・盲検の命名・主張との照合を行いました。

## 0. 内容

### 0.1 置き方（解釈の層と形式化の層を分ける）

| 著者の言葉（解釈の層、CLAUDE.md §1） | このパートでの置き方（Claude の案。形式化の層） | 既存の言葉 |
|---|---|---|
| 点は素数たち＋無限素点 | 基礎 = 正の有理数の群 ℚ_{>0}（素数が自由に生成する）。素点ごとに擬距離を 1 つ置く | ℚ の素点（Ostrowski）、付値 |
| 基礎は離散的で、連続対象は基礎にない | log(ℚ_{>0}) は ℝ の部分集合として可算で、区間を含まず、全不連結（定義は ℝ を使っている） | 全不連結な空間 |
| 解像度を落とす | 歩幅 ε を大きくする（def `chainIn`、単調性 `chainIn_mono`）。鎖でつながる点を同一視する商は Lean にしていない（d_∞・d_p の 2 例では同値関係になる） | ε-鎖、ε-成分 |
| 直線が創発する | どの ε > 0 でも全体が鎖でつながり、ℝ の稠密な部分集合と等長（完備化が ℝ であること自体は Lean にしていない。上の「案の限界」） | well-chained（Whyburn）、一様連結・Cantor 連結、距離空間の完備化 |
| 解像度のパラメータ（未決定） | **置いていません。** ε と擬距離 d は粗視化の例で、著者の言うパラメータとは同一視しません（N・K・Λ とも同一視しません） | — |

- 「無限素点では無限大と無限小が重なり合う」は、このパートでは扱っていません（Part 250 の案 3。著者の判断待ち）。
- 左の列は著者の定義で、定理ではありません。右の 2 列の対応づけは Claude の案です。

### 0.2 log(ℚ_{>0}) は ℝ の中で全不連結で稠密（§1）

- **logSet。** 正の有理数の対数の全体です（def `logSet`）。正の有理数では log q = log r なら q = r なので、基礎の点は区別できます（`log_inj`）。
- **可算（`logSet_countable`）、区間を含まない（`not_Icc_subset_logSet`）。** a < b なら [a, b] は logSet に含まれません。証明は、e^a と e^b の間に無理数 r があり、log r は正の有理数の対数でないことによります。
- **連結な部分は 1 点以下（`subsingleton_of_isPreconnected`）。** logSet に含まれる連結な集合は、元が高々 1 個です。
- **稠密（`dense_logSet`）。** logSet は ℝ で稠密です。

### 0.3 歩幅 ε の鎖（§2）

- **定義（`chainIn S d ε x y`）。** ある n と列 c があって、c(0) = x、c(n) = y、i ≤ n で c(i) ∈ S、i < n で d(c(i), c(i+1)) < ε。
  - d は任意の関数です。距離の公理は仮定していません（対称でない d では、鎖の関係も対称とは限りません）。

### notes/pag2_part251_projective_limit.md（冒頭 45 行）

# アーデル射影幾何 — Part 251（PAG 2.0）：Part 249 の射影極限の側 — 素数の類は lim (ℤ/N)^× × ℝ で稠密な部分群を生成する

2026-11-12。PAG255.lean（16 項目、定義 5 個、instance 2 個）、step274.py（8 項目）。

- **問いの出所。** 著者の指示です（2026-11-12、「Part 249 の射影極限の側から進めてください」）。
- **問い（極限の言葉で）。** Part 249 は、有限レベル (ℤ/N)^× × ℝ ごとに、素数の類が生成する部分群の稠密性を示しました。射影極限 lim (ℤ/N)^× × ℝ の上でも稠密か。そのために、素数 p の類を、すべてのレベルで両立する 1 つの元として作れるか。
- **結論（Lean）。**
  - 両立する系の群 `unitSys`（レベル N ≥ 1 ごとの単数の、自然な写像で両立する系の全体。各レベルは離散位相、全体は積位相の制限）を置きました。
  - 素数 p の類 κ_p を、すべてのレベルで両立する元として作りました。レベル N の成分は w_p(N) = 1 + p^(N!)·(p − 1) の逆元です。p ∤ N のレベルでは p⁻¹、p の冪のレベルに落とすと 1 です。この 2 つの性質を持つ両立する系は κ_p だけです。
  - L ≥ 1 を割らない素数の類 (κ_p, −log p) が生成する `unitSys × Multiplicative ℝ` の部分群は稠密です（以下 `unitSys × ℝ` と略します）。L = 1 で、すべての素数の類になります。
- **位置づけ（正直な評価）。**
  - 既知の事実です。C_ℚ ≅ Ẑ^× × ℝ_{>0} のもとで、素数イデール π_p の類が生成する部分群が C_ℚ で稠密、という主張に当たります。新規候補はありません（確信度：高）。
  - 稠密性そのものは、Part 249 の有限レベルの稠密性（`exists_cls_near`）と「開集合の各点は、あるレベルの筒（そのレベルの成分が同じ系の全体）を含む」（`exists_level`）からほぼ形式的に出ます。逆翻訳 A も「唯一の定理らしい文だが、入力は初等的」と判定しました。
  - このパートで Lean に新しく入った中身は、κ_p を大域の元として作ること（p^(K!) mod N が K ≥ N で一定であること）と、その一意性です。
  - Part 249 のノートが「既知の事実による推論、Lean ではない」としていた読み替え（独立照合 B の指摘 3・5）のうち、「すべての N で稠密 ⇒ 射影極限で稠密」と「k_p の p 成分を 1 とおく」を Lean にしました。
- **Lean にしていないこと。**
  - `unitSys` が Ẑ^×（Mathlib の Ẑ の単数群）と同型であること。
  - 構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0}（Mathlib の `IdeleClassGroup` との同一視）。したがって「イデール類群で稠密」は、この同一視のもとでの読みです。
  - `unitSys × ℝ` が位相群であること、`unitSys` がコンパクトであること。稠密性の文は位相だけを使っています。
  - 以下は独立照合 B の指摘で足した項目です。
    - `unitSys` が射影極限であること（普遍性、または Mathlib の極限との同型）。直積の中で閉、ハウスドルフ、完全不連結であること。各レベルへの射影が全射であること。`unitSys` は「両立する系の全体」という射影極限の具体モデルで、「射影極限」はその呼び名です。
    - レベルの筒が開集合であること（`exists_level` の逆向き）。したがって「筒が開集合の基をなす」は Lean では半分だけです。
    - p^(N!) mod N が冪等であること（e² ≡ e）。数値では確かめました（step274 (1)）。
    - (κ_p, −log p) と素元イデール π_p の類の対応。
    - 「p 成分をどう選んでも同じ稠密性が成り立つ」という一般化（証明から読み取れる注意）。
    - `Multiplicative ℝ` と ℝ_{>0} の同一視（exp・log）。

## 0. 内容

### 0.0 ハンドシェイク（CLAUDE.md §0）

- **形式化済み**：有限レベルの稠密性（Part 249）、その射影極限の形（このパート）。どれも既知の再導出です。
- **著者の解釈の層（定理ではない）**：点は素数たち＋無限素点。基礎は離散的で、直線は解像度を落としたときに創発する。解像度のパラメータは未決定。
- **このパートと解釈の層の関係（Claude の読み。著者の定義ではない）**：素数 p ごとに 1 つの元 (κ_p, −log p) があり、それらが生成する可算な群が、連続な成分 ℝ を持つ群の中で稠密です。レベル N は「開集合の各点のまわりで、どのレベルの成分まで見れば足りるか」という意味で粗さの添字になっていますが、著者の言う解像度のパラメータとは同一視しません。
- **未完の大域の問い**：§4。

### 0.1 冪等元 p^(N!) と w_p(N)（§1）

- **p^(K!) の安定性（`pow_factorial_modEq`）。** p が素数、0 < N ≤ K なら p^(K!) ≡ p^(N!) (mod N)。
  - 証明：N = p^a·M′（p ∤ M′）と分けます。法 p^a では、a < p^a ≤ N ≤ K! なので両辺 0（`pow_dvd_pow_factorial`）。法 M′ では、Euler の定理と φ(M′) ∣ K! から両辺 1（`pow_factorial_modEq_one`）。中国剰余定理で合わせます。
  - 補題 2 つを K = N で使うと、e = p^(N!) mod N は法 p^a で 0、法 M′ で 1 です。したがって e は冪等元（e² ≡ e）ですが、冪等性そのものは Lean の文にしていません（数値では確認。B の指摘）。有限半群の ω 乗 s^ω = lim s^(n!) の場合に当たります（§5）。
- **w_p(N) = 1 + p^(N!)·(p − 1)（def `wNat`）。**
  - N と互いに素です（`wNat_coprime`）。法 p^a で w ≡ 1、法 M′ で w ≡ p だからです。
  - 0 < N ≤ K なら w_p(K) ≡ w_p(N) (mod N)（`wNat_cast_eq`）。p ∤ N なら w_p(N) ≡ p (mod N)（`wNat_cast_of_coprime`）。
  - この式そのものは標準的ではありません（盲検の命名 C：「形式化のための工夫と思われる」）。中国剰余定理や ℤ_p への分解を経由せずに、両立する代表を 1 つの式で与えるために使いました。

### notes/pag2_part252_hartley_gluing.md（冒頭 45 行）

# アーデル射影幾何 — Part 252（PAG 2.0）：J∘H_N/√N（H_N は正規化しない離散 Hartley 変換、J は反転）は、単数の上で各原始指標 χ を W(χ) = τ(χ)/(i^a√N) 倍する（単数の上の式はすべての指標で成り立つ）— 読み：公理 A1 の境界ユニタリの原始指標の部分

2026-11-12。PAG256.lean（22 項目、定義 5 個。うち 7 項目は独立照合の指摘を受けて追加）、step275.py（11 項目）。

- **問いの出所。** 著者の判断です（2026-11-12 17:14「判断 3：Lean 化してください」）。
  - 重なりの読みは「ねじれた貼り合わせ（U）」と決まっています（同じ回答で、すでに決定済みと確認）。
  - 着手前の 4 点は `pag2_next_question_preregistration.md` の Q1 です。残余は空で、残るのは計算の細部（モノグラフ §1.3 の主張 (2)「A1 のもとで U = JH_N」の確認）だけ、という判定でした。著者はその Lean 化を選びました。
  - **記法の注意。** このノートの H_N は正規化しない離散 Hartley 変換で、Lean で扱ったのは J∘H_N/√N です。モノグラフの「JH_N」の正規化は、本文で確かめる必要があります（本文は手元にありません）。
  - 盲検の問いテストは済んでいます（同じ文書の §6 の S1：標準的な演習、Hartley の形の文献は見つからず）。自分の鎖には最初の形式化の Part 3（PAG3.lean）の命題 2.8 があった（内部照合 2026-11-14、§9）。
- **問い（幾何の言葉で）。** ねじれた貼り合わせの読みでは、無限大の側と無限小の側（切断した円筒の両端）を境界ユニタリ U で貼り合わせます。A1 のもとで、その貼り合わせの写像は何か。
- **結論（Lean）。** H_N は離散 Hartley 変換 (H_N f)(y) = Σ_x f(x)(cos + sin)(2π xy/N)、J は単数の上の反転 (Jg)(u) = g(u⁻¹) です。
  - **すべての指標 χ** について、単数 u で (J H_N χ)(u)/√N = W(χ)·χ(u)、W(χ) = ε(χ)τ(χ)/√N です（`JH_eq_rootNum_mul_any`・`rootNum_eq`。ε(χ) は偶で 1、奇で −i）。単数に台をもつ関数に制限すれば、各指標は J∘H_N/√N の固有ベクトルということです（「乗法的な平行移動と可換だから」という理由づけは Lean の外で、Lean で示したのは各指標についてのこの式です）。
  - **原始指標 χ** では、さらに次の 2 つが成り立ちます。この 2 つだけが原始性を使います。
    - 単数でないところで H_N χ = 0（`hartley_eq_zero_of_not_isUnit`）。単数の上の関数の空間から漏れません。
    - |W(χ)|² = 1（`normSq_rootNum`）。W(χ) = τ(χ)/(i^a √N) は、L 関数の関数等式の定数（ルート数）と同じ式です。ただしこの一致は Lean の外です（Davenport などの文献と、Mathlib の `DirichletCharacter.rootNumber` の定義式による）。原始的でない χ では W(χ) はルート数ではありません。
  - したがって、**各原始指標 χ について**、J∘H_N/√N は χ をルート数 W(χ) 倍し（単数の上で）、H_N χ は単数の外に漏れず、|W(χ)| = 1 です。これを、構築者が再構成したモノグラフ §1.3 の主張 (2)（A1 のもとで U = J∘H_N/√N）の、原始指標の部分での形と読みます（`JH_eq_rootNum_mul` はその原始指標の場合の文）。U も A1 も Lean の文には出てきません。この位置づけは解釈で、モノグラフ本文とは未照合です。
  - 原始指標の張る部分空間の上の**作用素としての文**（線形性、部分空間を保つこと、指標の直交性による固有分解、ユニタリ性）は、Lean の外です。
  - 非空虚性の証人（法 3 の奇の原始指標、法 5 の偶で自明でない原始指標）と、原始性を外したときの反例も Lean に入れました。反例は、法 2（原始指標がないことは Lean の外。単数でない 0 で H_N χ (0) = 1、|W|² = 1/2。原始的でないことは `removal_counterexample` の第 1 成分）と、原始指標のある法 4（原始指標の存在も Lean の文に含めた。単数でない 2 で H_N χ (2) = −2、|W|² = 0）の両方で置きました。
  - sorry 0、警告 0。`#print axioms` 27 項目（定理 22、定義 5）はすべて [propext, Classical.choice, Quot.sound]。
  - **独立照合で直したこと。** 最初の版は、単数の上の式を原始指標についてだけ述べていました。独立照合の 3 つのエージェント（中立化しなかった最初のもの、中立化した A・C）が、それぞれ独立に「単数の上の式は原始性なしで成り立つ」と指摘しました。原始性の役割が分かるように、すべての指標の文を足しました（§7）。
- **位置づけ（正直な評価）。**
  - 既知の事実の書き直しです（再導出、確信度：高）。原始指標のガウス和はフーリエ係数（Mathlib の `gaussSum_mulShift_of_isPrimitive`）で、Hartley 変換はフーリエ変換を実の核で書き直したものです。新規候補はありません。
  - 意味としては（解釈）、A1 の貼り合わせが「点どうしの同一視」ではなく、フーリエ型の作用素であることと、原始指標の部分で整合します（着手前の文書の Q1）。Lean の文は A1 に触れていません。
  - A1 は Lean の公理にしていません。ここでの文は W（`rootNum`。原始指標ではルート数）についての恒等式で、「A1 を導いた」ことにはなりません（CLAUDE.md §6）。A1 は原始指標の位相をこの値に選ぶ公準のままです（読み）。
- **Lean にしていないこと。**
  - (ℤ/N)^× 上の関数の空間全体での作用素の等式。原始的でない指標でも、単数に制限した J∘H_N/√N の固有ベクトルにはなります（τ = 0 なら固有値は 0）。ただし固有値 ε(χ)τ(χ)/√N は絶対値が 1 未満で（N ≤ 60 では最大 0.707、τ = 0 が 440 個中 135 個。数値 (9) と τ の公式による。Lean にあるのは法 2・法 4 の自明な指標で |W|² = 1/2・0 となる例だけ）、H_N χ は単数でないところに値をもちます（数値 (8)、440/440。一般の形は Lean の外。Lean にあるのは法 2 の 0、法 4 の 2 での値だけ）。（読み）A1 が原始的でない χ に誘導元のルート数を割り当てると読むなら、U = J∘H_N/√N は単数に台をもつ関数の空間全体では成り立たず、原始指標の部分に限られます。
    - 最初の版のこの箇所は「原始的でない指標では J∘H_N/√N の固有ベクトルにならず」と書いていました。誤りです。数値 (8) が破れていたのは単数でない点での値で、単数の上の式ではありませんでした（§7）。
  - 作用素としての文：線形性、原始指標の張る部分空間とそれを保つこと、指標の一次独立性と直交性（χ⁻¹ = χ̄ を含む）による固有分解、ユニタリ性、H_N² = N·I（独立照合 A・B の指摘）。原始的な複素指標 χ は H_N そのものの固有関数ではなく（H_N は χ と χ̄ の張る面で反対角）、J と合成して初めて対角になります。
  - 一般の恒等式 H_N χ (y) = ε(χ)·τ(χ, e(y·))（すべての χ と y。`hartley_one` はその y = 1 の場合。`hartley_eq_of_isPrimitive` は、これに原始指標のガウス和の性質を足した帰結）。原始的でない指標の数値 (8)・(9) の結果も、Parseval の等式などから一般の定理として示せるはずですが（独立照合 B）、文にしていません。
  - Mathlib の `DirichletCharacter.rootNumber`（Mathlib の関数等式 `IsPrimitive.completedLFunction_one_sub` に現れる定数）と rootNum の一致。定義の式は同じです（τ(χ)/I^(偶なら 0、奇なら 1)/N^(1/2)）。そのモジュール（Mathlib.NumberTheory.LSeries.DirichletContinuation）とその依存（L 級数、Mellin 変換など）はこの環境で未ビルドなので、Lean の文にしていません。
  - Lean の証人は実の指標（W = 1）だけです。W ≠ ±1 の場合は数値（原始指標 7,517 個すべて）で確かめています。
  - レベルを動かしたときの組み立て（L²(Ẑ^×) の上の一つの作用素として、局所の作用素の制限テンソル積と無限素点のパリティ因子）。Tate の枠組みで既知と見ていますが、文にしていません。
  - モノグラフの「U = JH_N」の正確な文（モノグラフ本文は手元になく、照合ノート §5 の 6）。ここで確かめたのは、私が再構成した原始指標の部分の形です。

## 0. 内容

### 0.0 ハンドシェイク（CLAUDE.md §0）

- **(a) 形式化済み。** 定理 2.6 の有限レベル版（PAG253）、ガウス和の性質（PAG16・PAG173・PAG198）、そしてこのパートの PAG256。
- **(b) 解釈の層。** 著者の 3 命題（§1）。重なり＝ねじれた貼り合わせ（U）は著者の決定です。A1 は解釈の層の公準（内容は Tate の定理）です。
- **(c) 未完の大域の問い。** 解像度のパラメータ（未決定）、レベルを動かした組み立て、Ẑ の上の定理 A。

### 0.1 4 点（着手前の文書の Q1 から）

1. **幾何の言葉。** 両端の貼り合わせは、点どうしの同一視か、別の種類の重なりか。

### notes/pag2_part253_primitive_operator.md（冒頭 45 行）

# アーデル射影幾何 — Part 253（PAG 2.0）：原始指標の張る空間の上の作用素 T（0 での延長のあと J∘H_N/√N）— 内積 ip に関してユニタリで、A1 の位相を課した線形写像は原始部分で T と同じ値をとる（線形性による）

2026-11-12。PAG257.lean（34 項目、定義 7 個。うち 6 項目は独立照合 A・C の指摘、4 項目は B の指摘を受けて追加）、step276.py（15 項目。うち 4 項目は独立照合の後に追加）。

- **問いの出所。** 著者の選択です（2026-11-12 21:17「推薦で進めてください」）。着手前の文書 `pag2_part253_preregistration.md` の候補 K1 で、残余は計算だけ、小さいノートの水準と明記して進める、という推奨でした。
  - 本来の道のうち「無限素点を含む大域対象」の有限レベルの部分です。重なりの読みは「ねじれた貼り合わせ（U）」と決まっています（著者の決定、17:14）。
  - Part 252 の独立照合 B が指摘した欠け（固有ベクトルの式はあるが、部分空間の上の作用素の文がない）を埋めます。
  - 盲検の問いテストは着手前に済んでいます（同じ文書の §7 の T1：既知の結果の短い帰結。「Hartley 変換＋逆元」の作用素そのものの文献は見つからず）。
- **問い（幾何の言葉で。解釈）。** 切断した円筒の両端を U で貼り合わせます。A1 のもとで、U は原始指標の部分で、明示的な実の核を持つ作用素として書けるか。その部分の外では何が起こるか。
  - U は Lean で定義していません。Lean で扱うのは明示の作用素 T で、U については「A1 の位相を課した任意の線形写像」という仮定の形でだけ現れます（`TopL_eq_of_A1`）。
- **結論（Lean）。** 単数の上の関数 g に (T g)(u) = (H_N g̃)(u⁻¹)/√N とおきます（g̃ は g を 0 で ℤ/N に延ばしたもの、H_N は離散 Hartley 変換）。⟨f, g⟩ = Σ_u conj(f(u))·g(u)（この内積を ip と書きます）。W(χ) = ε(χ)τ(χ)/√N で、ε(χ) は χ が偶なら 1、奇なら −i です（Part 252 の `rootNum`。原始的な χ ではルート数の式、原始的でない χ ではそうではありません）。
  - T は線形写像で、**すべての指標 χ** について T χ = W(χ)χ です（`TopL_charU`）。
  - 指標は直交し（⟨χ, ψ⟩ = φ(N)·[χ = ψ]、`ip_charU`）、一次独立で、単数の上の関数の空間を張ります（`linearIndependent_charU`、`span_charU_eq_top`）。
  - 原始指標が張る空間 V_prim について：
    - T で不変で、T(V_prim) = V_prim です（`TopL_mem_Vprim`、`map_TopL_Vprim`）。
    - V_prim の上で T は等長です：⟨Tf, Tg⟩ = ⟨f, g⟩（`ip_TopL_of_mem_Vprim`）。全射と合わせて、T は V_prim の上で ip に関してユニタリです。これを 1 つの文にしたものが `unitary_Vprim`（V_prim の自己線形同型で、値は T、ip を保つ）です。Mathlib の内積空間にはつないでいません。
    - 原始指標で U χ = W(χ)χ を満たす**任意の**線形写像 U は、V_prim の上で T と同じ値をとります（`TopL_eq_of_A1`）。仮定は `TopL_charU` の原始部分そのもので、結論は線形性だけから出ます（ほぼ同語反復）。
  - 原始的でない指標が張る空間 V_imprim も T で不変です（`TopL_mem_Vimprim`）。V_prim と V_imprim は ip について直交し、空間全体はその直和です（`ip_Vprim_Vimprim`、`Vprim_inf_Vimprim`、`Vprim_sup_Vimprim`、`isCompl_Vprim_Vimprim`）。V_imprim = V_prim^⊥ という形の文は書いていません。`eq_zero_of_ip_self` は非退化（⟨f, f⟩ = 0 ⇒ f = 0）だけで、⟨f, f⟩ ≥ 0 の文はありません。
  - **自明になる法。** N ≡ 2 (mod 4) では原始指標がなく V_prim = 0 で、V_prim についての文は自明に成り立ちます（法 2 では `Vprim_two`）。法 N ≥ 2 では自明な指標が原始的でなく、V_imprim に入ります（`not_isPrimitive_one_of_two_le`、`charU_one_mem_Vimprim`）。
  - 証人：法 3 で V_prim ≠ 0（`Vprim_ne_bot_three`）。法 2 で V_imprim の上の T は等長でない（自明な指標で |W|² = 1/2、`not_isometry_Vimprim_two`）。法 4 で T は自明な指標を 0 に送り、自明な指標は V_imprim に入るので、T は V_imprim の上で単射でない（`TopL_charU_one_four`、`charU_one_mem_Vimprim`）。
  - 素数の法の証人（独立照合 A の指摘で追加）：すべての素数 p で V_imprim の上の T は等長でない（自明な指標の τ = −1、|W|² = 1/p。`gaussSum_one_prime`・`normSq_rootNum_one_prime`・`not_isometry_Vimprim_prime`）。素数 p ≥ 3 で V_prim ≠ 0（`Vprim_ne_bot_prime`）。したがって素数 p ≥ 3 では、同じ法で V_prim の上はユニタリ（`unitary_Vprim`）、V_imprim の上は等長でありません。
  - sorry 0、警告 0。`#print axioms` 34 行はすべて [propext, Classical.choice, Quot.sound]。
- **Lean でない補足（数値・手計算）。**
  - 証人の限界（独立照合 A・B の指摘）：法 3 の原始指標は奇の 2 次指標 1 つだけで W = 1（τ = i√3）なので、法 3 の T↾V_prim は恒等写像です［手計算・数値］。N ∣ 24 ではいつもそうなります（指標がすべて実）［数値］。位相が自明でない最小の法は 5 で（W ≈ 0.8507 ± 0.5257i）［数値、step276 の (12)。1 ≤ N ≤ 100 の 69 個］。恒等でない位相を示す Lean の証人はありません。
  - 問いの「外側」について：Lean の文は T の性質だけで、V_imprim の上の U は `TopL_eq_of_A1` で何も縛られません。A1 の位相を原始的でない指標にも誘導元から入れた U_N を考えると、V_imprim の上では T ≠ U_N です［数値、着手前の `prereg253_check.py` の (K1c)：‖(T − U_N)↾V_imprim‖ の最小 0.5918］。
- **A1 との関係（第 2 の型の注意）。** `TopL_eq_of_A1` は「原始指標で A1 の位相を満たす任意の線形写像 U」についての文で、A1 の読み替えです。
  - 除去テスト：仮定（A1 の位相）を外すと結論が成り立たなくなるのは、V_prim ≠ 0 の法だけです［数値 (5)：N ≢ 2 (mod 4) の 75 個の法で、原始指標の位相を 1 つ変えると一致しない］。N ≡ 2 (mod 4) では結論はどの U でも成り立ちます。テストの内容は線形性から自明です。
  - 原始的な χ で T の固有値 W(χ) がルート数の式になること（`TopL_charU` の原始指標の場合）は、A1 によりません（ガウス和の事実）。
  - したがって、成果は「A1 の位相を、原始部分で明示の実の核 J∘H_N/√N（0 での延長のあと）として書き直した」ことで、「導いた」のではありません（CLAUDE.md §2・§6。A1 は公準のまま）。
- **位置づけ（正直な評価）。** 既知の事実の書き直しです（再導出、確信度：高）。原始指標で |τ(χ)|² = N（Part 12（PAG16）・Part 252）と指標の直交性から出ます。新規候補はありません。
- **Lean にしていないこと。**
  - V_imprim の上のノルムの評価 ‖T↾V_imprim‖ ≤ 1/√2（等号は N ≡ 2 (mod 4)）。原始的でない指標のガウス和の式 τ(χ) = μ(N/f)χ*(N/f)τ(χ*)（Montgomery–Vaughan, Multiplicative Number Theory I の Thm 9.10。着手前の盲検のエージェントが取得した章の PDF による。Mathlib にない）が要ります。数値は step276 の (10)（99/99 で ‖T↾V_imprim‖ < 1、最大 0.7071）。
  - 法 N の貼り合わせ U_N 全体（原始的でない指標に誘導元の位相を入れたもの）の明示の核。着手前の候補 K2 で、着手していません（数値は `prereg253_check.py` の (K2a)〜(K2d)）。
  - Ẑ^× の上への持ち上げ。U_N は法を上げる引き戻しと両立し、T は両立しません［数値 (K2d)］。「極限の U は L²(Ẑ^×) の上にあり、各導手 f の新しい部分の上で T_f に等しい」は、構成（位相を誘導元から取る）からの見込みです［予想・解釈、確信度：中。Lean にしていない］。
  - 「長さが保たれるのはちょうど V_prim の上」（T は正規な縮小で、V_prim は Sz.-Nagy–Foiaș の標準分解のユニタリ部分。独立照合 C の指摘）。V_imprim の上の |W| < 1 が要るので、Lean にはしていません［数値 (14)、100/100］。

## 0. 内容

### 0.0 ハンドシェイク（CLAUDE.md §0）

- (a) 形式化済み：Part 252（PAG256）の単数の上の式 `JH_eq_rootNum_mul_any`、|W| = 1（`normSq_rootNum`）、除去テストの反例。Part 214（PAG218）の単数の上の指標の和 `sum_units_char`。
- (b) 著者の解釈の層：重なりはねじれた貼り合わせ（U）。A1 は解釈の層の公準（内容は Tate の定理）。解像度のパラメータは未決定（N・K・Λ と同一視しない）。
- (c) 未完の大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象、解像度と有効な姿（§1 の命題 3）の定式化、有限レベルの Bost–Connes。

### 0.1 4 点（着手前の文書の K1 から）

### notes/pag2_part254_full_gluing.md（冒頭 45 行）

# アーデル射影幾何 — Part 254（PAG 2.0）：法 N の境界ユニタリ U_N 全体と、代数的な帰納極限の上の U_∞ — 法 M の単数の上の関数の空間で、導手ごとの部分（q ∣ M では π(V_prim(q))。添字は ℕ 全体で、q ∤ M の部分が 0 であることは文にしていない）は互いに直交し、独立で、全体を張る（合わせると直交直和。1 つの定理にはしていない）。U_N はその上で T_q を引き戻したもの。原始部分で T と一致し引き戻しと両立する族は U_N だけで、代数的な帰納極限の上の、正規化した内積を保つ 1 つの全単射 U_∞ にまとまる（Part 252 の残る問い。完備化 L²(Ẑ^×) は Lean の外）

2026-11-13。PAG258.lean（57 項目、定義 9 個・abbrev 3 個・構造体 1 個・instance 6 個）、step277.py（21 項目）。

- **問いの出所。** 著者の指示「Part 252, Part 254 を解決してください」（2026-11-13 06:43）を、「Part 254 で Part 252 の残る問い 2 つを解く」と読みました（作業の初めに著者へ伝えた読み）。
  - Part 252 のノート §4 の残る問い：(1) 法 N の境界ユニタリ全体（原始的でない指標を含む）を、J∘H_q（q ∣ N）の新しい部分の直和として書く文。(2) 法を動かした組み立て（L²(Ẑ^×) の上の 1 つの作用素）。
  - 解けた範囲：(1) は部品の文（直交・張る・独立・各部分の形）として Lean にしました（直和を 1 つの文にはしていない）。(2) は代数的な帰納極限の上までです。完備化 L²(Ẑ^×) と、Ẑ^× の上の局所定数関数との同一視は Lean の外です（下の「解決の範囲」）。
  - 着手前の 4 点・対照群・盲検の問いテストは、Part 253 の着手前の文書 `pag2_part253_preregistration.md` の候補 K2 と、盲検の文 T2（既知の結果の短い帰結）・T3（標準的な演習。注意：Ẑ に移るのは引き戻しと両立する作用素だけ）で済んでいます。
- **問い（幾何の言葉で。解釈）。** 重なりの読みは「ねじれた貼り合わせ（U）」です（著者の決定、2026-11-12 17:14）。法 N の貼り合わせ U_N に、A1 の位相をすべての指標に入れます（原始的でない指標には、誘導元の原始指標の位相）。(1) U_N は、各導手 q の原始部分の貼り合わせ T_q を組み合わせたものか。(2) 法を上げたとき、U_N はまとまって 1 つの作用素になるか。
- **記号。** Part 253 の記号を使います：単数の上の関数、内積 ⟨f, g⟩ = Σ_u conj(f(u))·g(u)（`ip`）、T = Part 253 の `TopL`。T は J∘H_N/√N を単数に圧縮し、反転 u ↦ u⁻¹ と合成した作用素です（離散 Hartley 変換を単数に制限しただけのものではありません。独立照合 A の注意）。χ* は χ を誘導する原始指標（Mathlib の `primitiveCharacter`、法は導手 q = cond χ）です。W(χ) は Part 252 の `rootNum`（原始指標ならルート数。原始的でない指標ではルート数ではなく、0 や絶対値 1 未満になる［既知。Lean にあるのは素数の自明な指標の場合だけ］）です。
  - 位相 `phaseA1 χ` = W(χ*)。法 N の境界ユニタリ `UA1` = Σ_χ phaseA1(χ)·P_χ（P_χ f = (⟨χ, f⟩/φ(N))·χ）。引き戻し `pullL`（N ∣ M）：f ↦ f ∘ ((ℤ/M)ˣ → (ℤ/N)ˣ)。
- **結論（Lean）。**
  - **残る問い (1)（直和の文）。**
    - 直和：導手が q の指標が張る部分 `condPart M q` は π_{q→M}(V_prim(q)) に等しい（`condPart_eq_map`、q ∣ M）。導手の違う部分は直交し（`ip_condPart`）、全体を張り（`iSup_condPart`）、独立です（`iSupIndep_condPart`）。添字は q ∈ ℕ 全体で、q ∤ M の部分が 0 であることは文にしていません。合わせると ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和になりますが、1 つの定理にはしていません（独立照合 B の指摘で追加。この言い方は再照合 B2 の指摘で直した）。
    - その上の U：U_M は各部分を保ち（`UA1_mem_condPart`）、g ∈ V_prim(q) なら U_M(π g) = π(T_q g) です（`UA1_pullL_of_mem_Vprim`）。
    - 指標ごとの式：すべての指標 χ で U_N χ = π_{q→N}(T_q χ*)（`UA1_charU_eq_pull_TopL`）。これは位相の定義の言い換えです。この式を満たす線形写像は U_N だけです（`UA1_unique`。基底の上の値による一意性）。
  - **残る問い (2)（組み立て）。**
    - 有限レベル：U_N は法を上げる引き戻しと両立します：N ∣ M なら U_M ∘ π = π ∘ U_N（`UA1_comp_pullL`）。T は法 1 → 2 と、すべての素数 p で法 1 → p で両立しません（`TopL_not_compat`・`TopL_not_compat_prime`）。一般の N < M でも両立しないはずですが（原始的でない指標のガウス和の式による）、Lean の外です［既知、確信度：中］。
    - **族の一意性**（定義の言い換えでない内容。指標ごとの式・`UA1_unique`・仮定を組み合わせた短い帰結）：法の集合（正の整数を割り算の順で並べた型 `Lvl`）の各法で、原始部分の上では T と一致し、引き戻しと両立する作用素の族は U_N だけです（`UA1_family_unique`）。原始的でない指標の上の位相は仮定に入らず、両立から一通りに決まります（独立照合 A の指摘で追加）。
    - 極限：引き戻しの帰納系の代数的な帰納極限 `Lim`（Mathlib の `Module.DirectLimit`）を作りました。極限への写像は単射です（`ofL_injective`）。U_N の族は極限の上の 1 つの作用素 U_∞ を与えます（`Uinf`、各法の像の上で U_N：`Uinf_ofL`）。U_∞ はこの性質で一意（`Uinf_unique`）で、全単射です（`Uinf_bijective`）。各法の原始部分の像は極限を張り（`span_ofL_Vprim`）、導手の違う像は直交し（`ipLim_ofL_Vprim`。極限での独立性は文にしていない）、U_∞ はその上で T_q です（`Uinf_ofL_of_mem_Vprim`）。U_∞ は「各導手の原始部分の像の上で T_q」という性質でも一意です（`Uinf_unique_TopL`）。
    - 極限の上の内積：引き戻しの和 φ(N)·Σ_u F(πu) = φ(M)·Σ_v F(v)（`sum_units_unitsMap`）から、正規化した内積 ⟨f, g⟩/φ(N) は引き戻しで変わりません（`ip_pullL`・`ipn_pullSys`）。代表の取り方によらない（`ipn_eq_of_ofL_eq`）ので、極限の上の内積 `ipLim` が決まります。右側で線形（`ipLim_add_right`・`ipLim_smul_right`）、エルミート（`ipLim_conj`）、⟨z, z⟩ は 0 以上の実数（`ipLim_self_nonneg`）、定値性（`eq_zero_of_ipLim_self`：⟨z, z⟩ = 0 なら z = 0）です（Mathlib の内積の構造にはしていません）。U_∞ はこれを保ちます（`ipLim_Uinf`）。
  - そのほか：
    - 位相：原始指標では phaseA1 χ = W(χ)（`phaseA1_of_isPrimitive`）。|phaseA1 χ|² = 1（`normSq_phaseA1`）。法を上げても変わらない（`phaseA1_changeLevel`）。自明な指標では 1（`phaseA1_one`）。法の型が違う指標の間の受け渡しは `rootNum_congr`（法が等しく、整数での値が等しい指標は同じ W を持つ）で行いました。
    - U_N：すべての指標で U_N χ = phaseA1(χ)·χ（`UA1_charU`）。単数の上の関数の空間全体で ⟨·,·⟩ を保ち（`ip_UA1`）、全単射（`UA1_bijective`）。原始部分では U_N = T（`UA1_eq_TopL_of_mem_Vprim`）。V_prim・V_imprim を保ち（`UA1_mem_Vprim`・`UA1_mem_Vimprim`）、T と可換（`UA1_comp_TopL`）。
    - 原始的でない部分では U ≠ T：素数 p の自明な指標は V_imprim に入り、U_p(1) ≠ T(1) です（`UA1_ne_TopL_prime`。値 U(1) = 1 は `phaseA1_one`・`UA1_charU`、T(1) = W(1)·1 と |W(1)|² = 1/p は Part 253 の `TopL_charU`・`normSq_rootNum_one_prime`）。N ≥ 2 一般でも成り立ちます（T(1) = μ(N)/√N·1）が、Lean の外です。N = 1 では V_imprim = 0 です。
    - 極分解：W(1 mod p) = −1/√p（`rootNum_one_prime`）。素数の法 p では、T の極分解のユニタリ因子のこの指標での固有値は −1 なので、U_p（固有値 1）はそのユニタリ因子ではありません（独立照合 A の指摘。極分解そのものは Lean にしていない）。**法によっては一致します**：法 1・6 では U_N は T_N の極分解のユニタリ因子そのものです（独立照合 B の反例。T_6 = diag(1/√6, 1/√2)）。T_N が可逆な N ≤ 60 のうち、一致するのは N = 1・6 だけでした（数値 (20)）。
    - 実数性：τ(χ⁻¹) = χ(−1)·conj τ(χ)（`gaussSum_inv`）、W(χ⁻¹) = conj W(χ)（`rootNum_inv`、原始的でなくてもよい）、phaseA1(χ⁻¹) = conj phaseA1(χ)（`phaseA1_inv`）から、U_N は複素共役と可換です（`UA1_star`：U_N の核は実数値。定理 2.6 の条件 KUK = U。独立照合 C の「証明できる」を受けて追加）。
  - sorry 0、警告 0。`#print axioms` 57 行はすべて [propext, Classical.choice, Quot.sound]。
- **「解決」の範囲（正直な評価）。**
  - 残る問い (1)：直和の部品の文を Lean で示しました（`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart` と `UA1_pullL_of_mem_Vprim`。直和を 1 つの文にすること、q ∤ M の部分が 0 であることは文にしていない）。ただし中身は、指標を導手で分けることと、各レベルでの Part 253 の結果の組み合わせです。U_N の明示の核（導手とメビウスの式）は数値だけです（step277 の (8)、60/60）。
  - 残る問い (2)：代数的な帰納極限の上の作用素 U_∞ と、その上の内積を Lean で作り、U_∞ が内積を保つ全単射であることを示しました。定義の言い換えでない内容は族の一意性（`UA1_family_unique`。短い組み合わせ）です。Lean にしていないのは次の 2 つです。どちらも標準の事実です［既知、確信度：高］。ほかに、極限での独立性（直交と定値性から出る［推論］）と、U_∞ が導手ごとの各部分を保つこと（`Uinf_ofL_of_mem_Vprim`・`UA1_eq_TopL_of_mem_Vprim`・`UA1_mem_Vprim` から出る［推論］）も Lean にしていません。
    - 帰納極限 `Lim` を Ẑ^× = lim (ℤ/N)^× の上の局所定数関数の空間と同一視すること。
    - `ipLim` による完備化（L²(Ẑ^×)）と、その上へのユニタリの延長（内積を保つ全単射は完備化の上のユニタリに一意に延びる）。
- **A1 との関係（第 2 の型の注意）。** U_N は A1 の位相を定義として入れた作用素です。指標ごとの式と両立は、位相を誘導元の原始指標から取るという選び方と、Mathlib の導手の性質（導手と誘導元は法を上げても変わらない）から出ます。族の一意性（`UA1_family_unique`）は、この選び方が「原始部分で A1（T と一致）＋法の間の両立」から一通りに決まることを言います。原始部分の A1 は仮定のままで、A1 は公準のままです。導いていません（CLAUDE.md §2・§6）。
- **位置づけ。** 既知の枠組みの書き直しです（再導出、確信度：高）。独立照合 C の名前（読み。`Lim` と Ẑ^× の上の局所定数関数の同一視は Lean の外）：U_∞ は Ẑ^× の上の、原始指標のルート数 W(χ*) を記号とするフーリエ乗数（Ẑ^× の双対群は原始ディリクレ指標の全体）。導手による分解は新形式・旧形式分解の GL(1) 版（C の確信度：中）、引き戻しは inflation です（§5 と辞書 §14）。新規候補はありません。

## 0. 内容

### 0.0 ハンドシェイク（CLAUDE.md §0）

- (a) 形式化済み：Part 253（PAG257）の作用素 T、内積 `ip`、V_prim・V_imprim、`TopL_charU`・`TopL_eq_of_A1`・`span_charU_eq_top`・`ip_charU`・`ip_sum_sum`・`charU_one_mem_Vimprim`・`normSq_rootNum_one_prime`・`gaussSum_one_prime`・`eq_zero_of_ip_self`。Part 252（PAG256）の `rootNum`・`rootNum_eq`・`parFac_of_even`・`normSq_rootNum`・`removal_counterexample_normSq`。
- (b) 著者の解釈の層：重なりはねじれた貼り合わせ（U）。A1 は解釈の層の公準（内容は Tate の定理）。解像度のパラメータは未決定（N・K・Λ と同一視しない）。
- (c) 未完の大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象、解像度と有効な姿（§1 の命題 3）の定式化、有限レベルの Bost–Connes。

### 0.1 4 点（Part 253 の着手前の文書の K2 から）

### notes/pag2_part255_resolution_discrete_limit.md（冒頭 45 行）

# アーデル射影幾何 — Part 255（PAG 2.0）：§1 の命題 3（解像度と有効な姿）の L1 の読み — 像が離散か稠密かは、測る素点の集合と位相の選び方で決まる。有限の基礎 ⟨S⟩（S は素数の有限集合）での二分法（∞ と T ⊆ S を測り、測らない素数が 2 つ以上なら稠密、高々 1 つなら閉かつ離散）と、有限素点の座標での位相の対比（離散位相では閉かつ離散、直積の位相では稠密）。既知の事実の Lean 化（小さいノート）

2026-11-13。PAG259.lean（定理 45 個、定義 4 個と instance 2 個。独立照合 A・C の後に定理 4 個・定義 1 個、B の後に定理 4 個・定義 2 個を足した）、step278.py（21 項目）。

- **問いの出所。**
  - 2026-11-13 08:38：著者が、着手前の文書（`pag2_part255_preregistration.md`）の候補 L1 を §1 の命題 3 の読みとして採りました（選択肢「L1 で Part 255 を始める」）。L1 は Claude の案です。著者の定義の文面そのものではありません。
  - 同じとき、著者は CLAUDE.md §1 の K は「考える素数の個数」ではない、と答えました。L1（測る素点の集合）は、N・K・Λ のどれとも同一視しません。
  - 2026-11-13 08:41：著者の定義（原文）。
    > 完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。
  - この定義は CLAUDE.md §1 の解釈の層に置きます。数学の文ではないので、Lean では示していません（示せる種類の文でもありません）。
- **L1（この定義のもとでの読み）。**
  - 基礎は正の有理数の群 ℚ_{>0}、または有限個の素数の集合 S が生成する部分群 ⟨S⟩ です。
  - 解像度は測る素点の集合です。測った座標は (log q（∞ を測るとき）, (v_p(q))_{測る素数 p}) で、有限素点の座標は離散な ℤ に入ります。
  - 無限個の素点の座標を考えるときは、位相を決めないと「離散」は意味を持ちません。各近傍が有限個の素点しか測らない位相（直積の位相）と、すべての素点を同時に測る位相（離散位相。ℤ 値では箱・一様の位相と同じ）があります（独立照合 B の指摘で明記）。
  - 読み：閉包をとる操作（完備化）は「解像度が落ちる」側の操作で、閉包に現れる連続体は観測したい姿ではなく、解像度が落ちた印です。極限は、すべての素点を同時に測る側（直極限 ⊕ℤ = colim ℤ^T。その位相は離散）でとります。これは読みで、Lean の文ではありません。
- **着手前の文書からの直し（08:41 の定義を受けて）。**
  - 着手前の文書は、L1 の「有効な姿」を「像の閉包」と書き、閉包に直線が現れることを中心に置いていました。数学は同じですが、向きを直しました。閉包に現れる連続体は解像度が落ちた印と読み、中心は「どこまで離散が保たれるか」です。
  - **取り下げ 1。** 着手前の文書 §4 は「完備化（尺度 ε → 0）は解像度を上げる向き」として、完備化を候補から外しました。この理由を取り下げます。著者の定義では、完備化は解像度が落ちる側の操作です。L1 の閉包が、その完備化にあたると読みます。
  - **取り下げ 2。** Part 250 の照合の記録（`pag2_part250_independent_audit.md`）の「これは『解像度を落とす』とは逆向き（ε → 0 の側）の操作です」という向きの判断も取り下げます。原文は残しています。
  - **Part 250 の残る問いへの答え。** Part 250 のノートの残る問い（「完備化を『解像度を上げた極限』と読むなど…どれが著者の意図に近いかは、著者の判断です」）に、著者の答えが出ました：完備化は解像度が落ちる側です。
- **結論（Lean の文。すべて既知の事実の Lean 化）。**
  - **1. すべての素点の付値の組。**
    - 単射です（`eq_of_padicValRat_eq`。素因数分解の一意性）。異なる正の有理数は、ある素数の座標で 1 以上離れます（`exists_prime_one_le_abs`。sup 距離の意味。位相の文は 4）。
    - ∏_{s∈S} s^{k_s} の付値（`padicValRat_prod_zpow`）、付値の組への全射（`exists_padicValRat_eq`）、⟨S⟩ の元の表示 q = ∏ s^{v_s(q)}（`eq_prod_of_support`）。
    - 積公式 log q = Σ_s v_s(q)·log s（`log_eq_sum_of_support`）。∞ の座標は有限素点の座標から決まります。
  - **2. ∞ だけを測る。**
    - log ℚ_{>0} の閉包は ℝ 全体です（`closure_logSet`。Part 250 の `dense_logSet` の言い換え）。
    - 異なる 2 つの素数の対数が生成する群は稠密です（`dense_closure_log_primes`・`exists_zpow_near`。Part 250 の 2 と 3 の場合の一般化。最小の正の元があれば p^K = r^M となり矛盾）。log r / log p は無理数です（`irrational_log_div_log`。独立照合 A の指摘で足した）。
  - **3. 有限の基礎 ⟨S⟩ での閾値（T ⊆ S、∞ と T の素数を測る。像 `imgST S T` ⊆ ℝ × ℤ^T）。**
    - 閉包がある水平な直線 ℝ × {k} 全体を含む ⇔ T の外に S の異なる素数が 2 つある（`threshold_iff`。独立照合 A の指摘で足した）。
    - 二分法（独立照合 B の指摘で足した）：その条件のもとで像は稠密です（`dense_imgST_iff`。S は素数の有限集合、T ⊆ S。T ⊆ S は必要：S = {2, 3}、T = {5} では右辺は真で左辺は偽）。条件が成り立たない（測らない素数が高々 1 つ）なら、像は閉かつ離散です（`isClosed_discrete_imgST`）。後者は、T の座標が同じ 2 点が、等しいか、q, q' によらない c > 0 以上離れること（`fiber_sep`。証明では S ∖ T = {p} なら c = log p、S ⊆ T なら各ファイバーの点は高々 1 つ）から出ます。後者には T ⊆ S は要りません。二分法を 1 つの文にした定理はありません（2 つの場合が排他的であることは文にしていない）。
    - 部品：測らない素数 p ≠ r があれば、座標を保ったまま log を任意の x に ε 近づけられる。保つ座標は、`exists_near_of_two_unmeasured` では p, r 以外のすべての素数、`exists_near_measured` では M の素数、`exists_near_in_subgroup` では T の素数（⟨S⟩ の中にとどまる）。p 以外の付値が一致する 2 元は q' = q·p^k で、等しいか log p 以上離れる（`eq_mul_zpow_of_agree`・`log_sep_of_agree`・`log_sep_one_unmeasured`）。S の素数をすべて測れば、異なる元は S のある素数の座標で 1 以上離れる（`exists_mem_one_le_abs_of_support`）。∞ を測らなければ整数の座標で離散（`sep_of_inf_unmeasured`。ほぼ同語反復）。
    - 守備範囲：閾値（二分法）は有限の基礎 ⟨S⟩ の文です。分離の文（`eq_mul_zpow_of_agree`・`log_sep_of_agree`）と `exists_near_of_two_unmeasured` は、p（または p, r）以外のすべての素数の座標を固定したファイバーの中の文で、有限の解像度の文ではありません（`exists_near_measured` は有限の解像度 M の文）。ℚ_{>0} では有限の解像度の外に素数が無限個あるので、「測らない素数がちょうど 1 つ」の場合は起きず、∞ を測ればどの有限の解像度でも像は稠密です（`exists_near_measured` と `exists_padicValRat_eq` から出る系。閉包の文にはしていない）。
  - **4. 極限の取り方：すべての素点の座標 ρ(q) = (log q, (v_p(q))_p)。集合は同じで、位相が 2 通り。**
    - **直積の位相**（`Nat.Primes → ℤ` の既定の位相。各近傍は有限個の素点しか測らない）：像は稠密です（`dense_rho_image`）。ℝ × {0} の直線全体が閉包に入り（`mem_closure_line_prod`）、ρ(1) は孤立点ではなく（`rho_one_mem_closure_ne_one`）、閉包の点 (1, 0) は像にありません（`closure_rho_not_image`。(1, 0) は積公式の形 x = Σ k_p log p を満たさない点。独立照合 A の指摘）。
    - **すべての素点を同時に測る位相**（読み。`BoxCoord`：`Nat.Primes → ℤ` に離散位相。写像 `rhoBox` は ρ と同じ。ℤ 値の座標では離散位相が箱・一様の位相と同じことは Lean の外の標準の事実）：像は閉かつ離散です（`isClosed_discrete_rhoBox_image`。独立照合 B の指摘で足した。素因数分解の一意性を離散位相で言い直した文で、log の成分は使わない。再照合 A2 は「自明（位相の選び方でほぼ決まり、ほぼ同語反復に近い。確信度 高）」と判定。A2 の出力の原文 `reaudit257/agent_A2_255_output.md` から引いた）。sup 距離では、異なる像は 1 以上離れます（`rho_sep`）。
    - 離散になるかどうかは位相の選び方で決まり、有限台では決まりません。付値の組は有限台で（`finite_support_padicValRat`）、各元は台の段 ⟨T⟩ の元ですが（`eq_prod_support`）、`rho_one_mem_closure_ne_one` の近似点も有限台です（独立照合 B の指摘）。
    - Lean の外：直和 ⊕ℤ の直極限の位相（有限の段 ℤ^T の直極限）が離散であることと、それと `BoxCoord` の位相の同一視（標準の事実）。積公式を満たす点の集合と像の一致。
  - **5. 対照群（Lean では自明な文だけ）。** 値が c·ℤ（c > 0）に入れば、異なる値は c 以上離れます（`sep_of_mem_zmultiples`）。Lean にあるのは、通約的な 2 つの実数 L₁, L₂ についての文です（対数と読む）（`mem_zmultiples_of_commensurable`・`sep_of_commensurable`。一般化素数の全体には広げていない）。
  - **6. 順序版（大きさの順序 = 無限素点の絶対値）。** ⟨p⟩ では 1 より大きい最小の元は p です（`zpow_ge_of_one_lt`）。⟨p, r⟩（p ≠ r）では 1 より大きい最小の元がありません（`exists_between_one`）。
  - **7. 退化例。** すべての付値が 0 の正の有理数は 1 です（`eq_one_of_padicValRat_eq_zero`。S = ∅ で ⟨S⟩ = {1}）。
  - 一般の補題：T1 空間で、どの点にも集合と高々 1 点でしか交わらない近傍があれば、その集合は閉かつ離散（`isClosed_and_discrete_of_subsingleton`）。
  - 冗長な文（独立照合 B の指摘）：`closure_logSet` は `dense_logSet` の言い換え、`exists_near_measured` は `exists_near_of_two_unmeasured` を弱めたもの、`sep_of_inf_unmeasured` は `one_le_abs_intCast_sub` そのもの、`rho_sep` は `exists_prime_one_le_abs` の言い換え、`mem_closure_line_prod` と `closure_rho_not_image` の前半は `dense_rho_image` の系。
  - sorry 0、警告 0。`#print axioms` 45 行はすべて標準の公理の範囲です（44 行が [propext, Classical.choice, Quot.sound]、`val_ne_of_mem_of_not_mem` は [propext] だけ）。
- **文献の言葉と対照群（Lean の外。独立照合 C、§7）。**

### notes/pag2_part256_gluing_cross_term.md（冒頭 45 行）

# アーデル射影幾何 — Part 256（PAG 2.0）：互いに素な法 M, N の原始指標の積の上での、貼り合わせ U の固有値 — 位相（ルート数）は W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)。中国剰余定理の成分の位相の積から、一般には、交差項 χ₁(N)·χ₂(M) と偶奇の符号 s だけずれる。既知の事実の Lean 化

2026-11-13。PAG260.lean（定理 23 個、定義 3 個）、step279.py（13 項目）。

- **問いの出所。** 著者の選択（2026-11-13 18:15、着手前の文書 `pag2_part256_preregistration.md` の候補 M1）。本来の道の「無限素点を含む大域対象」と「重なり」に仕えます。Part 252〜254 の貼り合わせ U（読み。Lean では `UA1`。固有値は `phaseA1` χ = W(χ の原始指標)）と、Part 255 の L1（測る素点の集合）をつなぐ問いです：互いに素な法 M, N の貼り合わせから、法 M·N の貼り合わせは決まるか。
- **問いへの答えの範囲（独立照合 B の指摘）。** Lean の文が答えるのは、互いに素な 2 つの法の、原始指標の積 1 つの上の固有値です：法 M と法 N の固有値と、交差項と符号から決まります（Part 254 の `UA1_charU` と合わせて）。「素点ごとに分かれるか」「決まるか」の全体には答えていません。Lean にしていないのは、(i) 法 M·N のすべての指標が積の形に一意に書けること（このパートでは。Part 190・232 の 2 つの定理を合わせると出る。§9）、(ii) 原始でない成分（数値だけ）、(iii) 作用素全体の式、(iv) 素数冪ごとの分解（数値もない）と 3 つ以上の法（数値 (7) だけ）です。題の最初の版「貼り合わせ U は素点ごとに分かれるか」は、この範囲に合わせて直しました。
- **結論（Lean の文。すべて既知の事実の Lean 化）。**
  1. **ガウス和の乗法性。** 互いに素な M, N と、法 M の指標 χ₁、法 N の指標 χ₂ について、τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)（`gaussSum_prodChar`）。原始性は要りません。証明は a = a₁·N + a₂·M と分ける中国剰余定理です（`crtMap_bijective`・`stdAddChar_crtMap`・`prodChar_apply`）。互いに素の仮定を外しても等式は成り立ちますが、両辺が 0 になります（独立照合 A の手計算と数値 (10)。Lean の文は仮定つきのまま）。
  2. **偶奇の因子のずれ。** ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)。s は、χ₁, χ₂ がともに奇なら −1、それ以外は +1（`crossSign`・`parFac_prodChar`）。ε は Part 252 の `parFac`（偶で 1、奇で −i）です。
  3. **交差項の法則。** W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（`rootNum_prodChar`。原始性は要らない）。交差項 χ₁(N)·χ₂(M) の絶対値は 1 です（`norm_cross`）。ただし W（`rootNum`）がルート数であるのは原始指標のときだけで、原始でない指標では「法で正規化したガウス和」の恒等式です（A の指摘）。
  4. **貼り合わせ U での形。** 原始指標の積は原始です（`isPrimitive_prodChar`）。したがって `phaseA1`（読みでは公準 A1 の位相）でも同じ法則が成り立ち（`phaseA1_prodChar`）、`UA1`（読みでは U）は charU(χ₁χ₂) を s·χ₁(N)·χ₂(M)·phaseA1(χ₁)·phaseA1(χ₂) 倍します（`UA1_charU_prodChar`）。単数での値は (χ₁χ₂)(u) = χ₁(u mod M)·χ₂(u mod N) です（`charU_prodChar`。「中国剰余定理の 2 つの成分の関数の積」は読み）。これは原始指標の積 1 つの上の固有値の式で、作用素全体の等式ではありません。原始でない指標では、因子は導手での値 χ₁*(d₂)·χ₂*(d₁) に変わります（数値 (4)。Lean にしていない）。
  5. **ずれは実際に起きる（存在の例）。**
     - 法 15 = 3·5 に、W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組があります（`rootNum_prodChar_ne_mul`。phaseA1 の版 `phaseA1_prodChar_ne_mul` は「奇」を含まない形）。この例では比が ∓i で（W(χ₁)·W(χ₂) ≠ 0 なので比が言える）、交差項と符号 s が混ざっています（A・B の手計算。比の値は Lean の文にない）。
     - 符号 s だけでずれる例：法 39 = 3·13 に、交差項が 1 で W(χ₁χ₂) = −W(χ₁)·W(χ₂)、W(χ₁)·W(χ₂) ≠ 0 となる奇の原始指標の組があります（`rootNum_prodChar_eq_neg_mul`。B が手計算で示した例を Lean にした。数値 (13)）。この例では交差項が 1 なので τ(χ₁χ₂) = τ(χ₁)·τ(χ₂)（`gaussSum_prodChar`）で、−1 は W の正規化（奇×奇で i·i = −1）から来ます（再照合 A2 の指摘）。「算術的な符号の破れ」とは読みません。
     - 交差項だけでずれる例（符号 s = 1 で交差項 ≠ 1。例：法 3 の奇の指標と法 7 の 3 次の指標。再照合のときに数値で確認）と、等号になる例（法 3 の奇の指標と法 5 の偶の 2 次の指標。数値 (13)）は Lean にしていません。ずれは指標の選び方によります。「積ではない」は「一般には積ではない」の意味です。
  6. **条件つきの文。** W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 なら s·χ₁(N)·χ₂(M) = 1（`cross_eq_sign_of_rootNum_one`）。互いに素の仮定 h は余分です（互いに素でなければ W(χ₁χ₂) = 0 ≠ 1。A の指摘。Lean の文は仮定つきのまま）。
  - sorry 0、警告 0。`#print axioms` 23 行は標準の公理の範囲です（21 行が [propext, Classical.choice, Quot.sound]、2 行が [propext, Quot.sound]）。
- **読み（解釈の言葉。Lean の文ではない）。**
  - 「素点」「貼り合わせ」「重なり」は著者の言葉です。Lean の文は、指標とガウス和についての恒等式です。
  - 互いに素な法ごとに見ると、法 M·N の貼り合わせ U の固有値は、一般には、法 M と法 N の固有値の積ではありません。ずれは 2 つです。交差項 χ₁(N)·χ₂(M) は、相手の法を自分の指標で読んだ値です。符号 s は偶奇の因子（W の正規化の i^a）から出ます。偶奇の因子は、文献では無限素点の局所因子にあたります（Lean では偶奇の因子としてだけ現れます）。
  - 文献の名前（独立照合 C、§7）：交差項は「不分岐な指標でひねったときの ε 因子の変化」、符号 s は (−1)^{a₁a₂} で、実素点のヒルベルト記号 (−1, −1)_∞ と同じ形。2 次の指標では、W = 1 を外から入れるとヒルベルト記号の積公式と同じ形になる（C の申告。未確認）。
  - **言い方の注意（着手前の盲検の指摘）。** 文献では、大域の ε 因子は局所の ε 因子の積です（Tate、Deligne）。ここで言うずれは、ディリクレ指標を中国剰余定理で分けた成分 χ₁, χ₂ と、イデール類指標の局所成分との違いです。交差項は、χ₁ の、N を割る素点での局所成分（不分岐。一般には自明でないが、法 39 の例では χ₁(13) = 1 で自明）から出ます。「大域は局所の積ではない」とは書きません。
- **2 次の指標と相互法則（観察。主な結果にしない）。** p, q が異なる奇素数で χ₁, χ₂ がルジャンドル記号のとき、数値では W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 で、6 の文は平方剰余の相互法則 (q/p)(p/q) = (−1)^{(p−1)(q−1)/4} と同じ形になります（step279 の (2)：奇素数の 28 組）。ただし、ここから相互法則が出るのではありません。合成の法 pq の 2 次の指標で W = 1 であることは外から入れる事実で、その証明の引き方によっては循環します（着手前の盲検の指摘）。
- **公準 A1 との関係。** A1 は公準のままです。交差項の法則は W（原始指標ではルート数）についての恒等式で、A1 から何かを出すものではありません。A1 を外すと位相は自由に戻り、この法則は位相の選び方への制約ではなくなります（除去テスト。CLAUDE.md §7 の第 2 の型）。
- **位置づけ。** 既知の事実の Lean 化です（再導出、確信度：高）。Montgomery–Vaughan の Theorem 9.6 とそのルート数版の Lean 化です。文献では、大域の ε 因子が局所の積であることと、不分岐なひねりでの局所 ε 因子の変化から出る形にあたります（局所 ε 因子は Lean にしていない）。新規候補はありません。形式化としては、互いに素な法でのガウス和の乗法性は Mathlib と Isabelle AFP に見つかりませんでした（着手前の盲検と、この環境の Mathlib の grep。見落としの可能性あり）。ただし自分の鎖には Part 189（PAG193）の `gaussSum_mul_coprime` として同じ文がありました（内部照合 2026-11-14、§9）。兆候 4（既知の事実だけ）は 8 パート連続です（§6）。

## 0. 内容

### 0.0 ハンドシェイク（CLAUDE.md §0）

- (a) 形式化済み：Part 252〜254（PAG256〜258）の `rootNum`・`parFac`・`phaseA1`・`UA1`・`charU`・`Vprim`、直極限 `Uinf`。Part 255（PAG259）の測る素点と位相の二分法。
- (b) 著者の解釈の層：§1 の 3 命題。重なりはねじれた貼り合わせ（U）。A1 は公準。解像度は測る素点の集合（L1）。「解像度が落ちる」の定義（2026-11-13 08:41）。
- (c) 未完の大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象（このパートは偶奇の因子のずれまで）、有限レベルの Bost–Connes。

### 0.1 4 点（着手前の文書 §1 から）

1. 幾何の言葉：2 つの点（素数）の上の貼り合わせから、両方を同時に見たときの貼り合わせは決まるか。決まらないなら、ずれは何か。
2. 既存分野の言葉への最善の翻訳：互いに素な法でのガウス和の乗法性、ルート数の局所因子への分解（Tate の局所定数）、2 次の指標では平方剰余の相互法則。
3. 残余：空（確信度：高。盲検も「ない」）。
4. 対照群：F_3[t] でも同じ交差項の法則が成り立ちます（step279 の (5)）。交差項は ℚ に固有ではありません。無限素点のずれは関数体にもあり、形が違います（盲検、こちらでは未確認）。一般化素数では指標とガウス和がなく、問いが立ちません。

### 0.2 定義（PAG260.lean）

| 記号 | Lean | 内容 |
|---|---|---|

### notes/pag2_part257_local_factor_decomposition.md（冒頭 45 行）

# アーデル射影幾何 — Part 257（PAG 2.0）：互いに素な法の並び N_1, …, N_k の指標の積の上で、ガウス和と W は成分の τ・W の積と、交差項・符号で書ける — τ = 交差項·∏τ(χ_i)、W = (−1)^{k(k−1)/2}·交差項·∏W(χ_i)。法 N_1·…·N_k の指標はこの形の積にちょうど 1 通りに書ける。既知の事実の Lean 化

2026-11-14。PAG261.lean（定理 25 個、定義 4 個、instance 1 個）、step280.py（11 項目）。

- **問いの出所。** 著者の選択（2026-11-14 20:59、着手前の文書 `pag2_part257_preregistration.md` の候補 P1、§12）。開始条件 2（方向βの登録ファイルとの突き合わせ）は、**著者の判断で保留のまま**始めました。登録ファイルは届いておらず、突き合わせは済んでいません。
- **問いへの答えの範囲。** 幾何の言葉の問い（読み）は「大域の貼り合わせ（U の固有値 phaseA1。原始の指標では W = rootNum）は、∞ を含む各点の局所の因子の積に分かれるか。各点の因子は、どこまでその点だけで決まるか」。Lean が答えるのは、互いに素な法の並びの指標の積（Lean では `listChar`）の上でのガウス和 τ と W の式と、法 n の指標の素数冪の成分への分解までです。イデール類指標と Tate の局所定数そのものは Lean にしていません。W の式（1〜3）は原始でない指標でも成り立つ恒等式です。Lean で示したのは、成分がすべて原始のとき U の固有値 phaseA1 も同じ式で分かれること（4）までで、原始でない指標では phaseA1 は一般には W と違います。
- **結論（Lean の文。すべて既知の事実の Lean 化）。**
  1. **ガウス和。** 法が互いに素なら τ(listChar χ l) = 交差項·∏_i τ(χ_i)（`gaussSum_listChar`。原始性は要らない）。交差項は漸化式で定め（`cross`）、閉じた形が 2 つあります。形 (I) は ∏_i χ_i(∏_{j≠i} N_j)（`cross_eq_formI`）、形 (II) は ∏_i ∏_{j≠i} χ_j(N_i)（`cross_eq_formII`）です。形 (II) は、成分 i の因子を「ほかの成分を N_i で読んだ値」で書く形です。
  2. **W。** W(listChar χ l) = ε_∞·∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)/√N_i（`rootNum_listChar_formI`）、= ε_∞·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)（`rootNum_listChar_formII`）。ε_∞ は偶奇の因子 `parFac`（偶で 1、奇で −i）です。
  3. **∞ の因子の符号。** ε_∞(listChar χ l) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数。`parFac_listChar`）。したがって W(listChar χ l) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（`rootNum_listChar`）。成分 2 つでは、法 N_a·(N_b·1) の上で Part 256 の `rootNum_prodChar` と同じ式です（Lean ではつないでいない）。
  4. **原始性と U の固有値。** すべての成分が原始 ⇔ 積が原始（`isPrimitive_listChar_iff`）。原始なら、phaseA1（読みでは公準 A1 の位相）も同じ式で分かれます（`phaseA1_listChar`）。
  5. **分解の存在と一意性。** 法 N_1·…·N_k の指標はどれも listChar χ l の形に書け（`exists_listChar`。並びに重複なし）、成分は一意です（`listChar_injective`。Part 256 の `prodChar` が Part 232 の `charMul` と同じ定義であることを使って `charMul_injective` を当てる）。Part 256 で「Part 190 の `decomp` と Part 232 の `charMul_injective` を合わせると出る（監査者の読み。Lean ではつないでいない）」と書いた事柄を、ここで Lean にしました（任意個の成分で）。
  6. **すべての素数への分解。** 法 n の指標 Ψ には、素数冪の法 p^{v_p(n)} の成分 χ_p があって、自然数 x での値は Ψ(x) = ∏_p χ_p(x)、τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)}) です（`gaussSum_primeFactors`。形 (II)）。成分の一意性は listChar の形でだけ言い、法 n の形では文にしていません。退化例（成分 1 つ）は τ(listChar χ [a]) = τ(χ_a)（`gaussSum_listChar_singleton`）。
  - sorry 0、警告 0。`#print axioms` 25 行（定理と同数）は標準の公理の範囲です（22 行が [propext, Classical.choice, Quot.sound]、1 行が [propext, Quot.sound]、1 行が [propext]、1 行は公理なし）。
- **読み（解釈の言葉。Lean の文ではない）。**
  - 「素点」「局所因子」「貼り合わせ」は著者の言葉です。Lean の文は、指標とガウス和についての恒等式です。偶奇の因子 ε_∞ が無限素点の局所因子にあたる、も読みです。
  - **局所定数との一致（条件つき。確信度：中〜高、Lean の外）。** 原始指標 χ を素数冪の成分 χ_p に分け、χ に対応するイデール類指標 ω を ω_q(q) = χ(q)（不分岐な q）と正規化し、加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}（Tate の学位論文の規約）にとると、形 (II) の p の因子 (τ(χ_p)/√p^{e_p})·∏_{q≠p} χ_q(p^{e_p}) は ω の p での局所定数と一致し、∞ の局所定数は i^{−a} です（着手前の盲検の問いテストと私の手計算。盲検の根拠は Rohrlich の講義ノートで、私は一次文献を開いていない）。原始でない成分や、素数冪でない法の成分では、この一致は言えません（例：法 p の自明な指標の因子は −1/√p で、不分岐の局所定数ではない。照合者 B の指摘）。ψ の規約を逆にすると各 p の因子が χ_p(−1) 倍、∞ の因子が i^{a} になり、積は変わりません。ω を χ̄ に対応させる規約では積が W の共役になります（盲検の申告）。
  - **問いの後半について（読み。照合者 R4 の指摘で書き直した）。** Lean の恒等式が言うのは、交差項を成分ごとの因子に配る書き方が 2 通りあることまでです。形 (II)（`cross_eq_formII`）では成分 i の因子がほかの成分の値 χ_j(N_i)（j ≠ i）を含み、形 (I)（`cross_eq_formI`）ではほかの法 N_j を含みます。どちらの書き方でも、成分 i の因子は (χ_i, N_i) だけでは決まりません。ただし「どう配っても (χ_i, N_i) だけでは決まらない」ことは恒等式からは出ず、Lean の外です（手計算の見込み、確信度：中）。
  - **∞ の因子は別の話。** ε_∞ は合成した指標の偶奇（∞ の点の情報）で決まり、成分の ε_∞(χ_i) の積とは符号 (−1)^{k(k−1)/2} だけずれます（`parFac_listChar`）。これは ∞ の因子が ∞ の外の情報に依存することを示すものではありません。
  - 上の条件のもとでは、形 (II) の因子がほかの成分の値を含むことは「局所定数がイデール類指標 ω の局所成分の値（ω_p(p) = ∏_{q≠p} χ_q(p)）を含む」ことにあたります（読み。式は着手前の文書 §2.3 の私の手計算で、確信度：中。一次文献では確かめていない）。
  - Part 256 では「成分の W の積からのずれ」を交差項と符号 s として書きました。成分を任意個にすると、ずれは交差項（形 (I)・(II) のどちらでも書ける）と符号 (−1)^{k(k−1)/2} です。
- **公準 A1 との関係。** A1 は公準のままです。ここでの文は τ・W・phaseA1 についての恒等式で、A1 から何かを出すものではありません（CLAUDE.md §7 の第 2 の型）。
- **位置づけ。** 既知の事実の Lean 化です（Lean 化の部分は確信度：高）。形 (I) は互いに素な法でのガウス和の乗法性（Part 256 の着手前の盲検が Montgomery–Vaughan の Theorem 9.6 として挙げた。定理番号を私は確かめていない。着手前の盲検は PSU の講義ノート Thm 4.2 で積公式を確かめた）を繰り返したもの、形 (II) と ∞ の因子は、上の条件のもとで Tate の局所定数の積公式の GL(1)/ℚ の場合です（同定は確信度：中〜高、盲検の申告のまま）。新規候補はありません。

## 0. 内容

### 0.0 ハンドシェイク（CLAUDE.md §0）

- (a) 形式化済み：Part 252〜254（PAG256〜258）の `rootNum`・`parFac`・`phaseA1`・`UA1`、Part 256（PAG260）の `prodChar`・`rootNum_prodChar`。前の鎖の Part 189（PAG193）・190（PAG194）・192（PAG196）・193（PAG197）・232（PAG236）の中国剰余定理まわりの定理。
- (b) 著者の解釈の層：§1 の 3 命題。重なりはねじれた貼り合わせ（U）。A1 は公準。解像度は測る素点の集合（L1）。
- (c) 未完の大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象（このパートは ∞ の因子の符号まで）、有限レベルの Bost–Connes。

### 0.1 4 点（着手前の文書 §2 から）

1. 幾何の言葉：大域の貼り合わせ（U の固有値 W）は、∞ を含む各点の局所の因子の積に分かれるか。各点の因子は、どこまでその点だけで決まるか。
2. 既存分野の言葉への最善の翻訳：ガウス和の乗法性の繰り返し（形 (I)）と、Tate の局所定数の積公式の GL(1)/ℚ の場合（形 (II)）。
3. 残余：空（確信度：高）。鎖に対して新しいのは、任意個の成分の明示の積、形 (II)、∞ の因子の符号の整理だけ（§7）。
4. 対照群：F_q[t] でも有限素点の分解は同じ形です（着手前の数値 (8)）。∞ の因子は、偶で 1、奇で √q/τ(η)（盲検の答え。私は計算していない）。一般化素数では指標とガウス和がなく、問いが立ちません。

### 0.2 定義（PAG261.lean）

| 記号 | Lean | 内容 |
|---|---|---|
| N_1·…·N_k | `lvl N l` | 法の並びの積（先頭 × 残り）。`lvl_eq_prod` で (l.map N).prod |
| χ_1·…·χ_k | `listChar χ l` | 先頭の指標と残りの積を Part 256 の `prodChar` でつないだ、法 lvl l の指標 |

### notes/pag2_part258_beta_premise.md（冒頭 45 行）

# アーデル射影幾何 — Part 258（PAG 2.0）：N, M ≥ 1、N ∣ M のとき、(i) φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の、φ(E_s) は E_t の線形結合、を満たす単位的な代数準同型 φ : A_N → A_M がある ⇔ gcd(N, M/N) = 1（登録の言葉では「方向βの前提」の判定。存在の側のテンソル積は既知、不存在の側は文献が見つからなかった）

2026-11-14 夜〜11-15。PAG262.lean（定理 23 個、定義 3 個）、step281.py（段階 2 の数値、13 組）。

- **問いの出所。** 著者側の申し送り補足7（2026-11-14）の決定（委任のもと）：次のパートは方向βの前提を問う。登録 `preregistration-part255-beta-premise.md` の 3 段階を、突き合わせの記録 `pag2_beta_registration_check.md` §3 の切り分けで修正して行った。着手前の文書は `pag2_part258_preregistration.md`（予想 §6、段階 1・2 の結果 §8、閉鎖条件 §9）。
- **問いと答えの範囲。** 幾何の言葉の問い（読み）：見方を変える（N を上げる）操作は、代数の側で 1 つの写像として実現できるか。Lean が答えるのは、登録の受容条件を次の形で読んだときの、写像の存在と不存在です。
  - (1) 代数準同型 φ : A_N →ₐ[ℂ] A_M（単位元を保つ）。
  - (2) 射影と両立：すべての S ∈ A_N で φ(S) π^* = π^* S（π^* は ℤ/M → ℤ/N に沿った引き戻し）。
  - (3) 殻を混ぜない（強い読み）：φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合。
  - この読み（とくに (3) を強い読みにしたこと）は構築者のもので、著者に確かめる事項です。
- **結論（Lean の文）。**
  1. **存在（gcd(N, M/N) = 1）。** M = N·b、gcd(N, b) = 1 なら、φ(S) = Θ(S ⊗ 1)（Θ は Part 228 の A_N ⊗ A_b ≅ A_{Nb}）が (1)〜(3) を満たします（`exists_compatible_hom`）。明示の形は φ(D_s) = Σ_{u ∣ b} D_{su}、φ(E_s) = Σ_{u ∣ b} E_{su}（`shellLift_dind`・`shellLift_geps`）。φ は単射です（`shellLift_injective`）。
  2. **不存在（素数 p が N と M/N の両方を割る）。** (1)〜(3) を満たす φ はありません（`no_compatible_hom`）。素数冪の段 p^e → p^{e+f}（e, f ≥ 1）はここに入ります。
  3. **二分法。** N ∣ M のとき、(1)〜(3) を満たす φ がある ⇔ gcd(N, M/N) = 1（`exists_compatible_hom_iff`）。
  - sorry 0、警告 0。`#print axioms` 23 行（定理と同数）は標準の公理の範囲です（22 行が [propext, Classical.choice, Quot.sound]、1 行が [propext]）。
  - 照合者 B の見立て（Lean にしていない）：不存在の証明が使うのは (i) の 1 点（S = D_N、f = 1）、(ii) の s = N、φ の積と定数倍だけで、φ(1) = 1 は使わない。したがって単位元を保たない写像や、より弱い仮定での不存在に数行で強められる見込み（確信度 中）。
- **不存在の証明の筋（Lean の文の中身）。** 使うのは A_N の D_N（{0} の指示関数の掛け算）・E_N（定数 1/N の畳み込み）と、関係 D_N E_N D_N = (1/N) D_N、E_N² = E_N だけです。
  - (2)（S = D_N、f = 1 の 1 点だけ）と (3) から、φ(D_N) は核 H = ker(ℤ/M → ℤ/N) の指示関数の掛け算。φ(E_N) は ε の線形結合 g の畳み込みで、フーリエ変換 m = 𝓕g は (3) から双対殻の上で定数、E_N² = E_N から値は 0 か 1。
  - 関係を φ で送って δ₀ に当てると、H の上で g = (1/N)·δ₀。H の上の指標の和で数えると、ξ ≡ 1 (mod M/N) の剰余類に m = 1 の点がちょうど 1 つ。
  - ところが u = 1 + M/p は ℤ/M の単数で（(M/p)² ≡ 0）、ξ ↦ uξ はその剰余類と双対殻を保ち、点を動かす（p ∤ ξ のため）。点が 2 つになり矛盾。
- **読み（解釈の言葉。Lean の文ではない）。** 「見方を変える操作が代数の写像として実現できるか」への答えは、互いに素な段（新しい素数を加える）では「できる（テンソル積の左の因子として）」、同じ素数の指数を上げる段（p ∣ N かつ p ∣ M/N。素数冪でない (6,12) なども含む）では「(1)〜(3) の意味ではできない」です。β（A_N の N → ∞ の極限の代数）を (1)〜(3) の写像の帰納極限として立てる道は、この段で閉じます。整除の順の全体（または整除で共終な部分系）では (1)〜(3) の写像の帰納系は組めない、と読みます（共終な系は指数を上げる段を含む、という短い議論は手計算で、Lean にしていない）。互いに素な段だけの系（無平方数の部分系など）は別です（§4）。登録 §3 の言葉では、この読みのもとでの「不存在の側」の判定で、β の前提全体を閉じるものではありません。(3) の弱い読み（像が A_M に入るだけ）、単位元を保たない写像、(2) を別の形にした写像は、この答えの外です。
- **公準 A1 との関係。** A1 は公準のままです。ここでの文は A_N についての代数の事実で、A1 とは関係しません。
- **位置づけ。** 存在の側のテンソル積の同型は既知です（スキームの直積の Terwilliger 代数はテンソル積：Hanaki–Kim–Maekawa, Terwilliger algebras of direct and wreath products of association schemes, Theorem 3.1。盲検の照合者が読んだもので、私は開いていない。A_N = T(0) は辞書の同一視で Lean にしていない。確信度：中〜高）。写像の作用素 C⁻¹∘L は鎖の Part 228 にあり（`map_leftHom_le` で A_a の像が A_{ab} に入る）、Part 236（PAG240）の局所作用素 `locHom` の k = 0 と同じ式です（法の型が b と b·1 で違う。Lean ではつないでいない）。この Part で新しいのは条件 (i)(ii) の確認（Lean）と、不存在・二分法の文です。不存在の側は、着手前の盲検の問いテストで文献が見つかりませんでした（確信度：中。見つからなかったというだけ）。議論は初等的です。ラベル（［再導出］か［新規候補（小さい）］か）は著者の判断事項です。

## 0. 内容

### 0.0 ハンドシェイク（CLAUDE.md §0）

- (a) 形式化済み：Part 214（PAG218）の A_N（`shellAlg`）、Part 201 の `geps`・`dind`、Part 228（PAG232）の A_a ⊗ A_b ≅ A_{ab}、Part 197 の引き戻し `pull`、Part 202 の関数のレベルの引き戻しの事実。
- (b) 著者の解釈の層：§1 の新しい置き方（素点たちは制限積の因子として並列に共存し、有限レベル商はその「見方」）。A1 は公準。
- (c) 未完の大域の問い：β（A_N の極限の代数）、Ẑ の上の定理 A、有限レベルの Bost–Connes（方向γの文献照合は未実施）。

### 0.1 4 点（着手前の文書 §1〜§4 から）

1. 幾何の言葉：見方を変える操作は代数の写像として実現できるか。
2. 既存分野の言葉への最善の翻訳：円分的なスキームの Terwilliger 代数 T(0) の、商 ℤ/M → ℤ/N に沿った代数準同型の存在。互いに素な段は直積の定理。
3. 残余：素数冪の段での存在問題（登録の残余を、内部照合で切り分けたもの）。
4. 対照群：盲検の申告によれば（未確認。確信度は盲検の自己申告で高）、F_q[t]/(t^e) → F_q[t]/(t^{e−1}) でも同じ理由で不存在、互いに素の類似では存在。私は計算していない。盲検の申告が正しければ、答えは ℚ に固有の算術ではなく群・環の形から決まり、登録 §4 の判定では「β の前提の判定」としての価値は変わらないが、「アーデル射影幾何に固有の内容」としては数えない。

### 0.2 定義（PAG262.lean）

| 記号 | Lean | 内容 |
|---|---|---|
| φ（互いに素） | `shellLift hab` | S ↦ Θ(S ⊗ 1)、A_a →ₐ A_{ab} |
| D_N | `dTop N` | {0} の指示関数の掛け算（A_N の元） |

### notes/pag2_part259_unitary_step_maps.md（冒頭 45 行）

# アーデル射影幾何 PAG 2.0 — Part 259：互いに素な段の写像の一意性と、帰納系の添字（PAG263.lean）

（2026-11-15。著者の指示「Lean」（07:27）に従って始めた。問いの出所は二つある。基礎文書の骨格（著者側）の第5章と、方向ラウンドの項目 (b) の R1 である。R1 の査定（`pag2_R1_assessment.md`、数値と手計算）の主張を Lean にした。）

## §0 結論（Lean の文から）

記号は次のとおり。
- A_N = `shellAlg N`、D_s = mulLeft(dind N s)、E_s = convL(geps N s)、π^* は引き戻し。
- `Compat`（Part 258 の条件）：(i) φ(S) π^* = π^* S。(ii) φ(D_s) は D_t の線形結合で、φ(E_s) は E_t の線形結合。
- `CompatF`：`Compat` に (iii) フーリエとの両立 φ(𝓕S𝓕⁻¹) = 𝓕φ(S)𝓕⁻¹ を足したもの。

1. **一意な存在の二分法**（`existsUnique_compatF_iff`）。N ∣ M のとき、(i)(ii)(iii) を満たす単位的な代数準同型 A_N → A_M がちょうど 1 つあるのは、gcd(N, M/N) = 1 のとき、かつそのときに限る。
   - 互いに素な段では、その写像は `shellLift`（S ↦ S ⊗ 1）である（`compatF_iff_eq_shellLift`）。
   - 互いに素でない段で成り立たないのは、(i)(ii) を満たす写像が 1 つもないから（Part 258）であって、複数あるからではない。
2. **(iii) を外すと一意でない場合がある**（`not_existsUnique_compat`）。gcd(2, b) = 1 かつ 1 < b のとき、(i)(ii) だけを課すと、それを満たす A_2 → A_{2b} は 2 つ以上ある（`compat_twLift`・`compatF_shellLift`・`twLift_ne_shellLift`）。もう 1 つは、χ(x) = (−1)^x による A_2 の自己同型で捩った写像 `twLift` である。Lean が示すのはこの a = 2 の場合だけ。数値（9 組）では、a が奇数なら (i)(ii) だけで一意だった。
3. **帰納系**（`canon_self`・`canon_comp`）。互いに素な段の標準の写像は、合成と両立する。
4. **添字は有向でない**（`not_directed_udvd`・`not_isDirected_udvd`）。p と p² の両方の上に来る互いに素な段はない。互いに素な段は、古典的なユニタリ約数 N ∥ M の関係である（E. Cohen, Math. Z. 74 (1960) 66–80）。
5. **有向な部分系の例**。素数の有限集合の積（無平方数）の段は、包含の順で帰納系をなす（`DirectedSystem` のインスタンス）。ℂ 加群としての帰納極限 `sqLim` に、各段は単射で入る（`sqLim_of_injective`）。

規模：定理 67 個、定義 15 個（`def` 14 個と `abbrev` 1 個）、インスタンス 3 個。sorry 0、警告 0。公理は標準の範囲（[propext, Classical.choice, Quot.sound] または [propext, Quot.sound]）。

## §1 どこに内容があるか（照合 B の指摘を受けて）

- **一意性（`compatF_unique`）は、ほぼ即座の帰結である。** (ii) の D の側から φ(D_s) は掛け算の作用素で、(i) を定数 1 に当てるとそれが決まり（`compat_dind_unique`）、(iii) はそれを E の側に運ぶだけ。同じ理由で、(ii) の E の側は (i)、(ii) の D の側、(iii) から出る（`compatF_of_dind`）。
- **内容があるのは次の 3 つである。**
  - 存在：`shellLift` がフーリエと両立すること（`shellLift_fC`）。
  - (iii) が外せないこと：a = 2 の捩れ。
  - 帰納系の添字の構造：有向でないこと、有向な部分系、単射性。
- **(iii) は自然な条件である見込み**（照合 B の手計算、確信度：中〜高、Lean にしていない）。𝓕⁻¹ π^* 𝓕 は、双対側の部分群の埋め込みに沿った零延長 ι_* になる。そのため (i)(iii) から φ(S) ι_* = ι_* S が出る。逆向きも成り立つ見込み（確信度：中）。成り立てば、(iii) は「射影 π とその双対の埋め込み ι の両方と両立する」と言い換えられる。
- **「互いに素は要らない」と書いた文について。** `compat_dind_unique`・`compatF_unique`・`compatF_comp` は N ∣ M だけを仮定する。`compatF_unique`・`compatF_comp` は、互いに素でなければ Part 258 により前提を満たす写像がないので、その場合は空虚に真である。`compat_dind_unique` は (ii) の E の側を仮定しないので Part 258 は当てはまらず、gcd(N, M/N) ≠ 1 で前提を満たす写像があるかは未確認である（照合 T の指摘で直した。照合者の小さい数値では、(2,4)・(2,8)・(3,9) でそのような写像は見つからなかった。証明ではない）。

## §2 第5章への帰結（解釈。Lean の文ではない）

骨格の第5章の文は、次の形なら Lean の文から書ける。

> 「互いに素な段（ユニタリ約数）の写像は、引き戻しとの両立・殻を混ぜないこと・フーリエとの両立で一意に決まり（`shellLift`）、合成と両立する。添字の順序は有向でなく、帰納極限は有向な部分系（例：無平方数の段）の上でとる。」

ただし次の 3 点も併記する必要がある。
- 無平方数の系は、極大な有向部分系（各素数の指数を 1 つに固定したもの）のうち、指数がすべて 1 の場合にすぎない。A_{p^k}（k ≥ 2）を含まない。
- `sqLim` は ℂ 加群で、代数の構造と制限テンソル積 ⊗'_p A_p との同型は Lean にしていない（制限テンソル積の構成そのものは［既知］）。
- どの有向な部分系も整除の順序で共終でない。したがって関数のレベルの極限 ℂ[ℚ/ℤ]（Part 197・202）の代数版にはならない（初等的、Lean にしていない）。

## §3 ラベル

- ユニタリ約数の順序の性質（推移性、有向でないこと）：［既知］（Cohen 1960。照合 B が挙げ、Web で書誌を確かめた）。

### notes/pag2_thm26_A1_collation.md（冒頭 45 行）

# 定理 2.6 と公理 A1 の照合 — Burnol の定理の適用範囲と、反転との両立の半分

2026-11-12。著者の指示（同日 13:44「定理2.6 と A1 の照合（Burnol の適用範囲の確定と、反転との両立の半分についての先行文献の有無）」）による。Part の番号は使わず、Lean と xlsx は変えていません。数値の確認は `pag2_thm26_A1_check.py`（15 項目すべて合格、約 40 秒。最初の版は 9 項目で、§11 の批判を受けて (8)〜(11) を、§12 の盲検を受けて (12)・(13) を足しました）。

- **「反転との両立の半分」の読み。** 定理 2.6 のうち、反転 W との両立を述べる側と読みました。(a) の JUJ = U* と、(b) の α_χ̄ = −α_χ です。Ẑ^× の側の χ ↦ χ̄ を含みます。
- **モノグラフ本文は手元にありません。** 定理 2.6 と A1 の形は、Part 249 のノート（§0.1・§0.8）と、著者の精査報告 `novelty-audit.md`（アップロードにあったもの）の記述から取りました。本文と食い違う箇所があれば差し戻してください。確かめたい点は §5 にまとめました。

## 結論

### Burnol の定理の適用範囲（数学としては確信度：高。モノグラフの定義との一致は確認待ち）

1. **切断しない C_ℚ ≅ Ẑ^× × ℝ_{>0} の L²：そのまま使えます。**
   - Burnol の定理 2.4 により、平行移動と可換な閉作用素は、双対群（原始ディリクレ指標の群 × ℝ）の上の掛け算作用素です。
   - 素数の平行移動 T_p とだけ可換でも、レゾルベントが可換なら全体と可換になり、同じ結論です（素数の類が生成する部分群の稠密性と、正則表現の強連続性による）。
   - さらに Burnol の定理 2.2 により、可換子が可換なら、対称作用素の自己共役拡張はただ一つです。切断しない群には境界の自由度がありません。
2. **切断した円筒 Ẑ^× × [Λ⁻¹, Λ]：バルクの作用素には使えません。**
   - ℝ 方向の平行移動は空間を保ちません。残る対称性 Ẑ^× の可換子は ⊕_χ B(L²(区間)) で、非可換です。
   - 定理 2.2 の仮定（可換子が可換）が崩れ、自己共役拡張は一つに決まりません。
   - 欠損空間は L²(Ẑ^×) と同型です。自己共役拡張は、境界条件 f(·, Λ) = U f(·, Λ⁻¹)（U は 𝓑 = L²(Ẑ^×) のユニタリ）で番号づけられます。
   - 著者の留保「Λ で切っていること自体が境界条件の存在理由」は、この形で正確に言えます。
3. **境界の空間 𝓑 = L²(Ẑ^×)：有界な場合が使えます。**
   - 各指標は重複度 1 で現れるので、古典的なフーリエ乗子の定理（Burnol の定理 2.4 の有界な場合）が使えます。
   - Ẑ^× と可換な U は指標で対角です：U = ⊕_χ e^{iα_χ}。
   - Part 249 の Lean（PAG253 の `thm26_full`）は、この部分を有限レベル (ℤ/N)^× の上で示したものです。
4. **α_χ を決めるものは、Burnol の定理にも von Neumann の理論にもありません。**

前回の批判的な照合の指摘（「正則表現、つまり重複度 1 でしか使えない」）は、2 と 3 の違いそのものです。

### 反転との両立の半分（数学は確信度：高。先行文献の判定は確信度：中）

- **JUJ = U* の意味。** JUJ = U* は「W が D_U の定義域を保つ」ことと同値です（私の計算。W(dom D_U) = dom D_{J U⁻¹ J}。数値 (7a)〜(7c) で符号を確認）。U が指標で対角なら、α_χ̄ = −α_χ と同値です。
- **先行文献。** この形の分類（指標ごとの境界の位相と、χ と χ̄ の位相の関係）を述べた文献は、今回照合した範囲では見つかりませんでした（§3）。
- **ただし部品はすべて既知で、導出は数行です。** 使うのは次の 3 つです。
  - von Neumann の拡張理論（値が L²(Ẑ^×) にある形）。
  - Ibort–Lledó–Pérez-Pardo の一般論（対称性で不変な拡張 ⇔ 境界のユニタリが境界での表現と可換）。
  - W が両端を入れ替えること。
- **判定（§11 で改訂：既知の結果からの短い帰結、確信度：高。条件は境界ユニタリの実性 KUK = U と同値）。** 既知の部品からの短い帰結です。モノグラフ §1.3 の自己評価「構造的には初等的」、著者の精査報告の「この形の先行文献は検索範囲で見当たらず」と同じ判定です。CLAUDE.md §3 の候補 2 の地位は、こちらでは変えていません。**§12 の盲検の文献照合も同じ判定（既知の結果の短い帰結、folklore）でした。反ユニタリ CW はどの対角の U でも定義域を保つので、W の条件は境界ユニタリの実性と同値です（§12.2）。候補 2 は新規性の根拠になりません（確信度：中〜高。§12.5）。**

### A1（辞書では「解釈の層の公準（内容は Tate の定理）」）

- **A1 の位相は、定理 2.6 が許す境界条件の一つです。** A1 の位相は α_χ = arg W(χ)、W(χ) = τ(χ)/(i^a √N) です（a = 0 は偶指標、a = 1 は奇指標）。
  - **実指標。** 定理 2.6 は α_χ ∈ {0, π} を許し、A1 は α_χ = 0 を選びます。これはガウスの符号決定で、Lean の `gauss_sign_real`（PAG198、第 I 期の項目 15）と同じ内容です。
  - **複素指標。** α_χ̄ = −α_χ は、W(χ)·W(χ̄) = 1 と |W| = 1 から出ます。前者は Lean の `gauss_inv_pair`（PAG173：z(χ)·z(χ⁻¹) = χ(−1)）から 1 行で出ます（χ(−1) = (−1)^a）。後者は Lean の `normSq_gaussSum`（PAG16：原始指標で |τ(χ)|² = N）から出ます（§10 の追補で確認。最初の版では「確かめていない」と書いていました）。
  - **一般の大域体。** 関数等式 Λ(1 − s, χ) = W(χ)Λ(s, χ̄) を 2 回使うと W(χ)W(χ̄) = 1 です。反転との両立の条件は、「関数等式は対合である」ことの作用素の言葉での形です（私の読み。数学としては確信度：高）。**§11 で訂正：この読みは過大でした。両立は定義から自明な W(χ̄) = conj W(χ)（境界条件の実性）から出ます。A1 の算術の内容は、どの α を選ぶかの部分だけです。**
- **したがって。** A1 と定理 2.6 の両立は、Lean にある 3 つの定理（PAG16 の `normSq_gaussSum`、PAG173 の `gauss_inv_pair`、PAG198 の `gauss_sign_real`）から短く出ます。ただし、この組み合わせ自体は Lean の文にしていません。A1 を課すこと（ほかの α を排すること）は公準のままです。「A1 を導いた」とは書きません（CLAUDE.md §6）。

### notes/pag2_resolution_overlap_materials.md（冒頭 45 行）

# 解像度と重なりの読み — 著者の判断材料（第 2 版）

2026-11-12。第 1 版は著者の指示（13:44）による。第 2 版は、独立の照合（批判、同日夕方）の指摘と、著者の申し送り（15:43「無限素点の『重なり』の読み（両端の同一視か、W による商か）は、§8.6 の表を受け取ってから著者が決めます」）を受けて、次の 3 つを入れたものです。

- §0：再監査の §8.6 の表（そのまま）
- §3：重なりの二つの読みの比較
- §4：まとめの訂正

Part の番号は使わず、Lean と xlsx は変えていません。

> **著者の判断（2026-11-12 17:14）。**
> - 重なり：「ねじれた貼り合わせ（U）」と決定済み（§3 の読み A-2）。読み A-1（群の商）は A1 と両立せず、読み B（W による商）は採らない。
> - 解像度：未決定のまま。§1 の候補のうち、指標の方向の粗視化（スペクトルを数えるために要る）は法 N に近く、CLAUDE.md §1 の禁止との緊張として記録する（`pag2_next_question_preregistration.md` の Q3・§9）。
> - 判断 3：A1 の貼り合わせの原始指標の部分（J∘H_N/√N の固有値がルート数）を Part 252（PAG256）で Lean にした。

- **この文書がすること。** 著者の定義（CLAUDE.md §1）の言葉に近い既存の枠組みを候補として並べ、それぞれについて次を書きます。
  - パラメータは何か。
  - 「解像度を落とす」「重なる」とは何をすることか。
  - 何が現れるか。
  - 既知の帰結（再導出になる部分）と、再導出でない可能性が残る部分。
  - 対照群テスト（関数体 F_q(t)、一般化素数）。
- **しないこと。** 定義を読み替えたり、候補の一つを選んだりはしません。決めるのは著者です。
- **CLAUDE.md §1 との関係。** 解像度のパラメータを N・K・Λ と同一視しない、という定めに従います。これらと重なる候補は「定義で除かれている」と書きます。
- **出典の状態の印。**
  - ［文献］：今回またはこれまでの検索で確かめたもの。
  - ［Lean］：Lean で示したもの。
  - ［数値］：`pag2_thm26_A1_check.py` で確かめたもの。
  - ［盲検］：再監査の盲検のエージェントの読み（未確認）。
  - ［批判］：独立の照合（批判）の手計算。
  - ［推論］：私の推論。
  - ［未照合］：私の記憶で、今回は確かめていないもの。

## 0. 再監査の §8.6 の表（著者の依頼により、そのまま再掲）

| 枠組み | 定義のどの言葉に当たるか | 再導出になる部分／ならない可能性 |
|---|---|---|
| アデール類空間、Connes–Consani のスケーリングサイト | 「点は素数たち＋無限素点」に最も直接当たる | C_ℚ の作用・稠密性・可換子は入口で再導出／解像度を (N, 対数の窓) の組として定量化する部分 |
| Tate のテーゼ、反転 x ↦ x⁻¹ | 「無限大と無限小が重なり合う」 | 関数等式、対合 W は完全に既知の範囲 |
| 粗幾何・漸近錐・スケール極限 | 「直線は解像度を落とすと創発する」 | 稠密な部分群の完備化としての ℝ は自明／S と ε の二重極限の速度 |
| Bost–Connes 系 | 「基礎は離散、解像度のパラメータ」（β と N が候補） | KMS 状態の値は再導出／A_N との接続 |
| Arakelov 幾何 | 「無限素点」 | 積公式は既知。「重なり」には対応が弱い |
| F_1 上の幾何、Berkovich の M(ℤ) | 「離散が基礎」「点は素数＋無限素点」の図 | Ostrowski の言い換えで、新しい部分は見込みにくい |

- これは再監査の盲検のエージェントの推測で、著者の定義の読み替えではありません。
- 表の中の「N」は合同部分群のレベルで、CLAUDE.md §1 により解像度とは同一視しません。

### notes/pag2_candidate1_generation_collation.md（冒頭 45 行）

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
- **MathSciNet・zbMATH：未実施。**
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

### notes/pag2_terwilliger_dictionary.md（冒頭 45 行）

# アーデル射影幾何 2.0 — Terwilliger 代数との辞書と、有限レベルの結果の新規性の再分類

2026-11-07。MUSE の精査報告（同日）を受けて、PAG 2.0 の有限レベルの部分（引き継ぎメモの項目 16〜68、Part 195〜247）を、アソシエーションスキームの Terwilliger 代数の言葉に置き直しました。そのうえで、各項目を「既知／既知の帰結／標準の計算／形式化固有／新規候補」に分け直しました。Lean のファイルは変えていません（Part の番号も使っていません）。

- **同定。** 殻代数 A_N = ⟨D_s, E_s⟩ は、ℤ/N の円分スキームの Terwilliger 代数 T(0) そのものです。
  - 円分スキームは、関係 R_t : gcd(x − y, N) = t（t ∣ N）で定まるスキームです。単数群の軌道による Schur 環 S(C_N, Aut C_N) にあたります。
  - D_t は双対べき等元 E*_t（基点 0）、E_s は Bose–Mesner 代数の原始べき等元です。
  - スキームは、N = p^k では完全グラフの輪積 K_p ≀ ⋯ ≀ K_p（k 個）です。一般の N では、その素数ごとの直積です。
  - MUSE の報告にある「A_N は生成元が異なるため Terwilliger 代数そのものではない」は誤りです（§5）。
- **帰結。** 構造の層（A_N の次元、ウェダーバーン分解、可換子、中心、二重可換子、中国剰余定理によるテンソル分解、素冪の形、主加群の行列単位、主べき等元）は、既知の理論から従います。
  - 根拠は Terwilliger (1992)、Bhattacharyya–Song–Tanaka (2010)、Hanaki–Kim–Maekawa (2011)、Bastian–Humphries (2026) です。
  - 該当するのは主に項目 36〜53 と 59〜63（Part 215〜232・238〜242）です。数値で確かめたうえで、既知か既知の帰結と判断しました（§3）。
- **残る新規候補。** 生成の問い（項目 64〜68、Part 243〜247）だけです。
  - ⟨M*, E_{s=1}⟩ = T(0) ⇔ N は平方因子なし、⟨M*, E_0, E_s⟩ = T(0) の分類、T(0) = M + M* + T_0 の条件、(T_0 + M*) ∩ (T_0 + M) の形です。
  - 今回のウェブ検索の範囲では見当たりませんでした。ただし MathSciNet・zbMATH は使っていません。
  - 新規である確率は**低〜中**、意義は**小〜中**と見ます。
- **形式化。** sorry 0 の Lean 形式化は、内容の新規性とは別の寄与です。ローカルの Mathlib（8637 ファイル）を検索した範囲では、アソシエーションスキーム・Bose–Mesner 代数・Terwilliger 代数・Schur 環・ラマヌジャン和の定義はありませんでした。
- **数値照合。** `pag2_terwilliger_check.py` で、PAG の定義とは別にスキームの側から行列を組み立て直しました。辞書の主張（§7）はすべて合格しました（1 回目の実行は失敗、§7 に記録）。

## 0. 同定：A_N は円分スキームの Terwilliger 代数 T(0)

**スキーム。** X = ℤ/N、t ∣ N ごとに関係 R_t = {(x, y) : gcd(x − y, N) = t}（gcd(0, N) = N）をとります。
- 隣接行列 A_t は 1_{D_t} の畳み込みです（D_t = {x : gcd(x, N) = t} は殻）。
- A_N = I、Σ_t A_t = J、A_t は対称、A_tA_s ∈ span{A_r}（係数は非負整数）が成り立ちます。対称な可換アソシエーションスキームで、クラスの数は d(N) − 1 です。次数は k_t = |D_t| = φ(N/t) です（数値 (1a)(1b)）。
- 殻 D_t はちょうど単数群 H = (ℤ/N)^× の軌道です（Part 203 の `exists_unit_mul_gcd`）。よってこのスキームは、Bastian–Humphries の記号で軌道 Schur 環 S(C_N, Aut C_N) から来るスキームです。
- N = p^k では、v_p(x − y) = j ⇔「下の桁から見て最初に違う p 進の桁が j」です。R_{p^j} は K_p の k 重の輪積の関係そのものです（数値 (1c)）。
- gcd(a, b) = 1 なら、中国剰余定理で ℤ/ab のスキームは ℤ/a と ℤ/b のスキームの直積になります（数値 (7)）。Lean では Part 228 の `crtConj_dind`・`crtConj_geps` がこれに当たります。
- よって一般の N のスキームは Π_{p ∣ N} K_p^{≀v_p(N)} です。

**Bose–Mesner 代数と双対。**
- M = span{A_t} は、PAG の E_s（ε_s = 𝓕⁻¹1_{D_s} の畳み込み）の張る空間と一致します。E_s は M の原始べき等元で、重複度は m_s = rank E_s = φ(N/s) です（数値 (2)。Part 201 の `geps_conv_geps`・`sum_geps`、Part 203 の `radial_iff`）。
- 基点 0 の双対べき等元 E*_t は、(E*_t)_{yy} = [gcd(y, N) = t] の対角行列です。これは PAG の D_t（1_{D_t} を掛ける作用素）そのものです。
- Terwilliger の T(0) は M と M* = span{E*_t} の生成する代数です。PAG の A_N（`shellAlg`）は {E_s} ∪ {D_s} の生成する代数です。
- 生成元の張る空間が同じなので、**A_N = T(0)** です（定義からの等式。Lean では T(0) を定義していないので、この等式は Lean の定理ではありません）。
- dim T(0) を生成元から数えると、N ≤ 60 と 128 以下の素冪の 79 個すべてで Part 226 の F(N) に一致しました（数値 (5)、法 p の掃き出しで正確に）。

## 1. 辞書

| PAG の記号（Part） | Terwilliger 側 | 根拠 |
|---|---|---|
| ℤ/N、基点 0 | X、基点 x = 0 | 定義 |
| 殻 D_t（t ∣ N）、\|D_t\| = φ(N/t) | 第 t 部分構成 Γ_t(0)、次数 k_t | 定義、(1b)、Part 201 `card_dsh` |
| 1_{D_t} の畳み込み | 隣接行列 A_t | 定義 |
| 双対殻 D_s の上の周波数への射影 E_s（`convL (geps N s)`） | 原始べき等元 E_s、重複度 m_s = φ(N/s) | (2)、Part 201 |
| E_N = J/N | 自明なべき等元 E_0 | (2)、Part 247 `geps_self_apply` |

### notes/pag2_author_definition_0841.md（冒頭 45 行）

# 「08:41 の定義」の文面（著者側の §1 との照合用）

2026-11-14。著者側の補足3（2026-11-13）の開始条件 3 に答えるもの。

## 文面（原文のまま）

> 完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。

- 受け取った日時：2026-11-13 08:41（JST）。この作業の会話に、著者のメッセージとして届いた。受け取った直後に `pag2_part255_preregistration.md` §10 に原文として写した。
- 79 文字（句点を含む）。

## 記録している場所（照合した結果）

| ファイル | 形 | 文面との一致 |
|---|---|---|
| `pag2_part255_preregistration.md` §10 | 引用（原文） | 一致 |
| `pag2_part255_resolution_discrete_limit.md` の冒頭 | 引用（原文） | 一致 |
| `pag2_part256_preregistration.md` の冒頭 | 引用（原文） | 一致 |
| `pag2_terwilliger_dictionary.md` §15 の前提 | 「」の中に原文 | 一致 |
| `PAG2_handoff_part256.md` の進め方のルール | 「」の中に原文 | 一致 |
| `pag2_part255_independent_audit.md` の冒頭 | 「」の中に原文 | 最後の「。」がない（「」の中の句点の省略。中身は同じ） |

- ほかの箇所（引き継ぎメモの「既知の古い記述」、Part 255 のノート §0.0 など）は、言い換えて触れているだけで、原文の引用ではない。

## この作業での扱い（参考。文面そのものではない）

- CLAUDE.md §1 の解釈の層に置いた、著者の定義。Lean で確かめたものではない。
- Part 255 で、極限の取り方を 2 つの位相で並べた（直積の位相では像が稠密、すべての素点を同時に測る離散位相では閉かつ離散）。ℝ や直積の位相を「完備化」と読み、この定義の「解像度が落ちる」にあたると読むのは読み（確信度：中）。
- この定義と食い違う前の記述（「完備化は解像度を上げる向き」など）は取り下げた（引き継ぎメモの「既知の古い記述」）。

### notes/pag2_R1_assessment.md（冒頭 45 行）

# R1 の査定：互いに素な段だけの帰納系を第5章の材料として確定できるか（2026-11-15）

**追記（同日、Part 259）**：§2〜§4 と §6 の候補 1〜5 を Lean にした（PAG263.lean、`pag2_part259_unitary_step_maps.md`）。個数の式と奇数での一意性は数値のまま。「互いに素な段」は古典的なユニタリ約数（Cohen 1960）である。

方向ラウンドの項目 (b) のうち、R1 だけを扱う。R2・R3 は扱っていない。パートではなく、Lean と xlsx は変えていない。数値は `out/r1assess/`（uniq.py・aut.py・fourier.py とそのログ）。数値は証明ではない。

## 0. 結論

- **条件つきで確定できる。** 第5章に書けるのは「互いに素な段の写像の系」である。ただし文面を次の 3 点で直す必要がある。
  1. 写像は (i)(ii) だけでは一意に決まらない。N が偶数のとき別の写像がある（§2、数値）。標準の写像は `shellLift`（φ(S) = S ⊗ 1）として名前を挙げるか、フーリエとの両立を条件に足して一意にする（§3）。
  2. 添字は整除の順序ではない。「互いに素な段」の順序（N ∣ M かつ gcd(N, M/N) = 1）は有向集合ではない（§4）。帰納極限がとれるのは有向な部分系（無平方数の系など）の上で、極限は制限テンソル積になる（§5）。
  3. そのどの部分系も整除の順序で共終ではない。関数のレベルの極限 ℂ[ℚ/ℤ] の代数版にはならない（§5）。
- 骨格の第5章の文「大域対象の代数的な組み立ては…互いに素な段のテンソル積の系にある」は、上の 3 点を入れずには書けない。

## 1. 問いの置き方

Part 258（PAG262）の (i)(ii) を満たす単位的な代数準同型 φ : A_a → A_{ab}（gcd(a, b) = 1）について、次の 3 つを確かめた。
- 一意か。
- 合成と両立するか（帰納系になるか）。
- 添字の集合は何か。

## 2. 一意性：奇数の a では一意、偶数の a では一意でない（数値）

**φ(D_s) は (i)(ii) から一意に決まる**（手計算、確信度：高）。
- 理由：(ii) から φ(D_s) = Σ_t c_t D_t^{(ab)} と書け、(i) を δ 関数に当てると Σ_t c_t 1[gcd(x, ab) = t] = 1[gcd(x mod a, a) = s] になる。殻の指示関数は一次独立なので、係数がすべて決まる。
- 数値でも、D の側の解空間の余りは全 11 組で 0 次元だった。

**φ(E_s) は、旧い殻の係数しか (i) で決まらない。**
- 新しい殻（π^* の像と直交する殻）の係数は (i) では決まらない。
- E_s は互いに直交するべき等元で、和は 1 である。そのため、新しい殻をどれか 1 つの s に割り振る仕方だけが候補になる。
- 各割り振りが代数準同型に延びるかを、対 (g, φ(g)) の生成する代数の次元が dim A_a に等しいかで判定した。結果は次のとおり。

| (a, b) | 候補 | 準同型になるもの |
|---|---|---|
| (2,3) | 4 | 2 |
| (3,2) | 4 | 1 |
| (2,5) | 4 | 2 |
| (3,4) | 16 | 1 |
| (4,3) | 27 | 2 |
| (2,9) | 16 | 4 |
| (6,5) | 256 | 2 |
| (5,6) | 64 | 1 |
| (4,9) | 729 | 4 |

- 観察：準同型の個数は、a が奇数なら 1、a が偶数なら 2^{d(b)−1} だった（d は約数の個数）。

### notes/pag2_literature_ia_sign.md（冒頭 45 行）

# アーデル射影幾何 — 照合リストの項目「i^a の帰属と加法指標の符号の規約」の文献照合

（2026-11-18。短期層の小さいノート。新しいパートではない。出所：CLAUDE.md §1 の「射影」の読み（2026-11-18、著者が留保つきで採用）と、材料ノート `pag2_projection_material.md` §2 の注意 2。著者の決定で、基礎文書が無限素点の読みを断定する前に行う照合として、候補 1・候補 3・γ と同じ照合リストに入った項目である。著者の定義（§1）の文面と A1 の地位は変えない。第 1 版を独立照合にかけ、その指摘で直した第 2 版に、著者の決定を記録したのが第 3 版、統合照合の指摘と後から行った内部照合（§0）を反映したのがこの第 4 版である（§0・§8〜§10）。）

記号：ξ は法 N の原始 Dirichlet 指標、a は ξ が奇なら 1・偶なら 0、τ(ξ) = Σ_x ξ(x) e^{2πix/N}、W(ξ) = τ(ξ)/(i^a √N)（古典的なルート数。Lean では `PAG.Part256.rootNum` の値 𝔀(ξ)。ルート数であることは Lean の外）。局所定数 ε(s, χ_v, ψ_v) は、Tate 1979（Corvallis）の流儀で定める：f̂(y) = ∫ f(x) ψ(xy) dx、局所関数等式の定数、ψ_v に関して自己双対な測度。

## §0 内部照合（後から行った。第 12 の型の記録）

この文献照合は、着手の前に自分の鎖（Lean の docstring・ノート・事前登録）の内部照合をせずに始めた。2026-11-18 夜、次の推薦の下調べで鎖を言葉で検索して（「局所定数」「学位論文」「ψ_∞」「i^{−a}」「無限素点の局所因子」）、同じ結論が鎖にすでに書かれていることが分かった。

- **Part 257（PAG261、2026-11-14）**：冒頭の説明、ノート `pag2_part257_local_factor_decomposition.md` の「読み」、事前登録 `pag2_part257_preregistration.md` §2.3・§6 に、次がすでに書かれている。
  - 加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}（Tate の学位論文の規約）にとり、イデール類指標を不分岐な q で ω_q(q) = χ(q) と正規化すると、形 (II) の p の因子 (τ(χ_p)/√p^{e_p})·∏_{q≠p} χ_q(p^{e_p})（`rootNum_listChar_formII`・`gaussSum_primeFactors`）は ω の p での局所定数と一致し、∞ の局所定数は i^{−a}（`parFac`）。
  - 加法指標の規約を逆にすると、各 p の因子が χ_p(−1) 倍、∞ の因子が i^a になり、積は変わらない。
  - ω_p(p) = ∏_{q≠p} χ_q(p)（確信度：中、一次文献では未確認、と書かれていた）。
  - 根拠は着手前の盲検の問いテスト（Rohrlich の講義ノート (2.49)・(2.55)・(2.69)・(2.70)。構築側は開いていない）と構築側の手計算。同定の確信度は中〜高。
- **Part 256（PAG260、2026-11-13）**：「偶奇の因子が無限素点の局所因子にあたる、は読み」（冒頭の説明、`parFac_prodChar` の docstring）。

したがって、このノートの §1 (a)(b) の結論は Part 257 の読みと同じで、新しく分かったことではない。今回の照合が Part 257 の記録に加えたものは次のとおり。

1. Tate の学位論文の加法指標の規約を、照合者が走査版の本文（§2.2）で確かめた（Part 257 では盲検の申告で、Rohrlich 経由）。
2. 二つ目の文献 Roy–Schmidt–Yi（式 (150)・(155)〜(157)）。
3. ω_p(p) = ∏_{q≠p} χ_q(p) を、構築側と照合者がそれぞれ導出し、数値で確かめた（Part 257 では確信度：中）。
4. 数値：構築側 209 指標、照合者 2,162 指標（局所関数等式からの直接評価を含む）。
5. PAG256 の Hartley 核の因子 `parFac` との値の一致を、規約 T を明示して書いた（Part 257 でも ε_∞ = parFac と読んでいた）。

以上により、Part 257 の「同定は確信度：中〜高」は、規約 T を明示した値の一致として確信度：高に上げてよいと読む（構築側の判断）。

教訓：文献照合も、着手の前に自分の鎖の内部照合（docstring とノートの言葉の検索）を行う。今回の「射影」の事前登録（`pag2_prereg_projection.md`）の §0 の内部照合も、P¹ の Part 13・19〜28 と定理 2.6 を見たが、位相の分解を扱った Part 256・257 を見落としていた。材料ノートの注意 2 の「照合者の知識による。確信度：中」も、鎖に Part 257 の記録があったことを書いていなかった。

## §1 問いと結論

照合リストの項目は次の 2 つだった。

- (a) ルート数の i^a は、Tate の局所分解で無限素点の局所因子から来るか。
- (b) 有限素点の加法指標の符号の規約のもとで、有限素点の局所因子の積は τ(ξ)/√N と ξ(−1)τ(ξ)/√N のどちらになるか。

結論：

- (a) **明示的な因子 i^{±a} は無限素点の局所定数である。符号 (−1)^a の置き場は規約による。** 無限素点の局所定数は i の冪で、有限素点の局所定数はガウス和である（明示的な i^{±a} の因子を持たない。ただし値は i を取りうる。例：法 3 の奇の指標で τ/√3 = i。規約 T では無限素点が −i、有限素点が i で、積は W = 1）。ここまではどちらの規約でも同じ（照合者の導出：ℚ の上で自明な加法指標は ψ_T(c·)（c ∈ ℚ^×）の形で、ε(s, χ, ψ_c) = χ(c)|c|^{s−1/2} ε(s, χ, ψ) から、無限素点は ±i^a、有限素点の積は ±τ/√N の正の数倍になる）。ただし冪の向きは規約で変わる：Tate の学位論文の加法指標の規約（下の規約 T）では ε(1/2, χ_∞, ψ_∞) = (−i)^a = i^{−a}、逆の規約 C では i^a。［既知］（確信度：高）
- (b) **規約で決まる。** s = 1/2 で、規約 T では τ(ξ)/√N、規約 C では ξ(−1)τ(ξ)/√N。どちらの規約でも、s = 1/2 での大域の積は W(ξ) で変わらない（一般の s では N^{1/2−s} W(ξ)）。偶奇の符号 ξ(−1) = (−1)^a を無限素点と有限素点のどちらに置くかは、規約の選び方である。［既知］（確信度：高）
- **PAG への帰結**（値の一致。Lean の外）：
  - PAG256 の Hartley 核の因子 ε(ξ) = `parFac`（偶で 1、奇で −i）は、規約 T の無限素点の局所定数 (−i)^a と同じ値である。残りの τ(ξ)/√N は、規約 T の有限素点の局所定数の積と同じ値である。
  - したがって材料ノートの読み「Part 252 の Hartley の形は、無限素点の符号の因子を有限レベルの変換に取り込んだ形」は、**規約 T を明示すれば**文献と合う。
  - ただし、この分け方が文献の「無限素点 × 有限素点」と一致するのは規約 T を選んだからである。規約 C では無限素点の局所定数は i^a で、Hartley の ε(ξ) とは (−1)^a だけ違う。等式 √N·W = ε(ξ)·τ(ξ) だけからは「ε(ξ) は無限素点から来る」とは言えない（照合者の注記）。
  - 素朴なフーリエ核 e(xy) の値 τ(ξ)/√N は規約 T の有限素点の積に、e(−xy) の値 ξ(−1)τ(ξ)/√N は規約 C の有限素点の積に当たる。奇の指標での i 倍のずれは、規約 T では無限素点の局所定数そのものである。

### notes/pag2_projection_material.md（冒頭 45 行）

# アーデル射影幾何 — 命名にある「射影」の材料（基礎文書の第 1・2 章のための対応表）

（2026-11-18。短期層の小さいノート。事前登録 `pag2_prereg_projection.md` の結論（残余は空、新しいパートは始めない）を受けて、基礎文書の起草（著者側）に渡す材料をまとめる。**ここに書く「射影」の読みは構築側が出した読みで、2026-11-18 19:01 に著者が留保つきで採用した（§6）。** 採用は読み（解釈の層）としての採用で、形式化済みの定理ではない。著者の定義（CLAUDE.md §1）の文面は変えない。第 1 版と第 2 版がそれぞれ独立照合を受け、その指摘で直した第 3 版に著者の決定を記録したのが第 4 版、文献照合の後の著者の決定を足したのが第 5 版、統合照合の指摘で直したのがこの第 6 版である（§7〜§11）。）

記号：
- 反転（0 と ∞ の入れ替え、x ↦ 1/x）は **ι** と書く。Lean の宣言 `PAG.Part23.W`・`PAG.Part26.Wpt`・`PAG.Part27.Wproj` とモノグラフの W は、この反転を指す。
- `PAG.Part256.rootNum` の値（τ(χ)/(i^a √N)、すべての指標 χ で定義）を **𝔀(χ)** と書く。原始指標ではルート数（その同定は Lean の外）。注意：PAG256 の docstring と冒頭のコメントでは、記号 W(χ) がこの 𝔀(χ) を指す（反転ではない）。
- τ(χ) はガウス和（加法指標は Mathlib の `stdAddChar`、e(t) = exp(2πit/N)）、a は χ が奇なら 1、偶なら 0。

## §1 著者の言葉（定義の層）

- 命名（2026-11-16）：「アーデル」はイーデル（乗法）とアデール（加法）を合わせた造語。「アーデル射影幾何」は、アデール幾何とイーデル幾何を射影によって融合する、という意味。
- 無限素点（2026-11-12・11-16）：無限大と無限小が重なり合う。−∞ と ∞ と 0 が射影によって重なる。この重なりを境界ユニタリ U によるねじれた貼り合わせと読む。
- 構築側の読み（2026-11-16 に著者確認）：ℝ_{>0} を対数で ℝ に移すと乗法の 0・∞ が加法の −∞・+∞ になり、射影直線では両端が一点になる。反転 x ↦ 1/x は 0 と ∞ を入れ替える。

## §2 「射影」の読み（構築側が出し、著者が 2026-11-18 に留保つきで採用）

命名の「射影による融合」を、次の 3 つの層の組として読む。著者の決定では、命名の「射影」は舞台と変換の両方を指し、主は変換である（舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ。§6）。

1. **舞台（座標）**：射影直線 P¹。2 つのチャート（0 の側 [x:1] と ∞ の側 [1:y]）が赤道（単数）の上で y ↦ y⁻¹ によってつながり、反転 ι が 0 と ∞ を入れ替える。
2. **変換（融合）**：乗法の側の反転 ι と、加法の側のフーリエ型の変換を合成した写像。乗法の関数（指標）に作用させる。有限レベル N では、ℤ/N の関数を単数の上の関数に送る写像で、同じ空間の上の作用素ではない（§3 の表 2 行目）。
3. **位相（公準）**：原始指標 χ については、その変換の成分が絶対値 1 の位相になる。標準の核は Part 252 の Hartley 核とする（著者の決定、§6）。この核での値は 𝔀(χ) = τ(χ)/(i^a √N)（`PAG.Part256.rootNum`）である。加法指標は規約 T（Tate の学位論文の加法指標：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）を標準とし、その規約で因子 ε(χ) = (−i)^a は無限素点の局所定数と一致する（値の一致、Lean の外。注意 2 の最後の項）。PAG256 の冒頭のコメントの読みでも、公準 A1 は境界ユニタリ U の原始指標の位相をこの値に選ぶ公準である。原始的なら 𝔀(χ) がルート数であることは Lean の外である。素朴なフーリエ核では、奇の χ で値がこの値と i 倍ずれる（注意 2。このずれは標準の核を決めても消えない）。原始的でない指標では、成分は位相でないことがある（絶対値が 1 未満になり、0 にもなる例がある。§3 の表 3 行目）。

注意 1（照合者の指摘）：1 と 2 は種類が違う。1 の y ↦ y⁻¹ はチャートの座標変換（関数を P¹ の上で定義するための恒等式）で、ねじれを持たない。ねじれ（指標ごとの位相）は 2 の変換の側にある。Lean でも、照合した範囲（PAG23・PAG26・PAG27・PAG256）では、2 の写像（`PAG.Part256.JH`）と 1 の 2 チャートモデル（`PAG.Part23.Compat` など）を結ぶ文はない。

注意 2（照合者の指摘で直した。式は加法核 e(xy) の規約で書く）：2 の変換の「加法のフーリエ型の変換」に何を使うかで、位相が変わる。N は法、u は単数。
- **素朴なフーリエ核 e(xy)**：成分は τ(χ)/√N。
  - 導出：`PAG.Part256.hartley_eq_of_isPrimitive` の証明の中の式 `hA`（∑ₓ χ(x) e(xy) = χ⁻¹(y) τ(χ)、`PAG.Part256.sum_mul_stdAddChar` と Mathlib の `gaussSum_mulShift_of_isPrimitive` から）に y = u⁻¹ を入れ、`PAG.Part256.inv_apply_units_inv`（χ⁻¹(u⁻¹) = χ(u)）を使って √N で割ると、(τ(χ)/√N)·χ(u) になる。独立した定理としては Lean に置いていない。
  - 単数の上では原始性は要らない（`PAG.Part256.hartley_units_inv` と同じ置換 x ↦ u·x の議論。照合者が N ≤ 30 のすべての指標で数値確認。数値は証明ではない）。
  - **核の符号に依存する**：核を e(−xy) にすると、成分は χ(−1)τ(χ)/√N になる（`PAG.Part256.hartley_eq_of_isPrimitive` の証明の中の式 `hB`・`hneg` から。y = 1 の場合は `PAG.Part256.sum_mul_stdAddChar_neg`）。「素朴なフーリエ核」は符号の規約を決めるまで一つに決まらない。
- **Part 252 の離散 Hartley 核**（cas = cos + sin。核は ((1 − i)e(t) + (1 + i)e(−t))/2、`PAG.Part256.casKer_eq`）：成分は 𝔀(χ) = ε(χ)τ(χ)/√N。ε(χ) は `PAG.Part256.parFac` で、偶で 1、奇で −i（`PAG.Part256.parFac_of_even`・`PAG.Part256.parFac_of_odd`）。すべての χ について `PAG.Part256.JH_eq_rootNum_mul_any` と `PAG.Part256.rootNum_eq` から出る。式 𝔀(χ) = τ(χ)/(i^a √N) は `PAG.Part256.rootNum` の定義そのもので、すべての χ で成り立つ。原始的なら 𝔀(χ) がルート数であることは Lean の外（`PAG.Part256.rootNum` の docstring）。
- **二つの関係（e(xy) の規約で）**：偶の χ では一致する（どちらも τ(χ)/√N）。奇の χ では 𝔀(χ) = −i·τ(χ)/√N、すなわち素朴な成分 = i·𝔀(χ)。核を e(−xy) にすると関係は反転し、𝔀(χ) = i·（素朴な成分）になる。
- **帰属の読み（2026-11-18 に文献照合。規約 T での値の一致。留保は著者の決定で外した）**：第 4 版までは、Tate の局所分解の通常の規約では i^a は無限素点の局所因子から来る（照合者の知識、確信度：中）とし、文献照合が済むまで i^a を正規化因子として書き、帰属を候補として留保していた。2026-11-18 に照合した（`pag2_literature_ia_sign.md`、独立照合 1 回。照合後の直しは未照合）。結果（原始的な χ について）：明示的な因子 i^{±a} が無限素点の局所定数であることは、加法指標の規約によらない。符号 χ(−1) の置き場は規約による。大域の加法指標は ℚ の上で自明でなければならないので、無限素点と有限素点で符号を逆に取ることは必然で、選べるのは無限素点の側の符号だけである。Tate の学位論文の加法指標の規約（規約 T：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）では、ε(χ) = (−i)^a が無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N が s = 1/2 での有限素点の局所定数の積と一致する（値の一致。Lean の外）。逆の規約では、無限素点が i^a、有限素点の積が χ(−1)τ(χ)/√N。したがって Part 252 の Hartley の形は、規約 T のもとで、無限素点の局所定数を有限レベルの変換に取り込んだ形と読める。同日、著者の決定で、i^a を正規化因子として留保する扱いを外し、規約 T を基礎文書の標準とした（§6 の 4・5）。なお、同じ同定は Part 257（PAG261）の冒頭の説明とノート `pag2_part257_local_factor_decomposition.md` に読みとして書かれていた（確信度：中〜高）。今回の照合はその確かめ直しにあたる（文献照合ノートの §0）。

## §3 対応表

| 層 | 有限レベル（ℤ/N） | 無限素点 | ラベル |
|---|---|---|---|
| 舞台：射影直線と反転 | P¹(ℤ/N) := 単模ベクトル / 単数倍（Part 23（PAG27）、`PAG.Part27.ProjLine`）。反転 [a:b] ↦ [b:a]（`PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`。一般の N）。p 素数、K ≥ 1 で、点モデル（Part 22（PAG26）、`PAG.Part26.Pt`）と同型（`PAG.Part27.projEquiv`）、点の数 p^K + p^(K−1)（`PAG.Part27.card_ProjLine`）。反転どうしの対応 `PAG.Part27.toProj_Wpt` は K ≥ 1 の仮定なしで述べられている。2 チャートモデルと赤道での貼り合わせ条件 F_N(y) = F_S(y⁻¹)（Part 19（PAG23）、`PAG.Part23.Compat`、反転 `PAG.Part23.W`。点モデルの関数との同型は一般の N で `PAG.Part26.ptEquiv`、反転の対応は `PAG.Part26.toP1_comp_Wpt`）。点モデルと P¹(ℤ/N) の点集合の全単射（`PAG.Part27.projEquiv`）が Lean で示されているのは N = p^K（K ≥ 1）だけ（2 チャートモデルは関数のモデルで、点モデルの関数の空間と線形同型になる：`PAG.Part26.ptEquiv`、一般の N）。N が 2 つ以上の素因数を持つときは点の数が一致しない（数え上げ：\|Pt N\| = 2N − φ(N)、\|P¹(ℤ/N)\| = N∏_{p\|N}(1 + 1/p)。N = 6 で 10 点と 12 点。この不一致を述べる文は Lean にない）。N ≥ 2 では 0 = [0:1] と ∞ = [1:0] は別の点で、反転がこの 2 点を入れ替える（有限の側に点の同一視はない。この文も Lean にはない。N = 1 では 1 点） | P¹(ℝ)。ℝ_{>0} の対数座標 t = log x で、反転 x ↦ 1/x は t ↦ −t になり、両端 −∞・+∞（乗法の 0・∞）を入れ替える。射影直線では両端が一点（著者確認済みの読み）。有限の側との違い：無限素点では両端が重なる | ［既知］（P¹(ℤ/N) はモジュラー記号の標準の道具、Manin 1972 など。Lean は Part 19〜28） |
| 変換：反転 ∘ 加法の変換 | J∘H_N/√N（Part 252（PAG256）、`PAG.Part256.JH`。J は単数の上の反転 u ↦ u⁻¹、H_N は離散 Hartley 変換）。ℤ/N の関数を単数の上の関数に送る写像で、同じ空間の上の作用素ではない。素朴なフーリエ核での形は §2 の注意 2 | モノグラフ層の境界ユニタリ U（イデール類群の上の反転と、境界条件）。Lean にしていない | ［再導出］（PAG256 の冒頭のコメントの記載どおり「既知の事実の書き直し」。Tate 1950 の局所関数等式の有限版と読む） |
| 位相：原始指標の成分 | すべての指標 χ と単数 u で (J H_N χ)(u)/√N = 𝔀(χ)·χ(u)（`PAG.Part256.JH_eq_rootNum_mul_any`）。原始的なら \|𝔀(χ)\| = 1（`PAG.Part256.normSq_rootNum`）。原始的なら 𝔀(χ) がルート数であることは Lean の外（`PAG.Part256.rootNum` の docstring）。原始的でない指標では位相でないことがある：法 2 の自明な指標（原始的でないことは `PAG.Part256.removal_counterexample` の第 1 成分）で \|𝔀\|² = 1/2（`PAG.Part256.removal_counterexample_normSq`）、法 4 の自明な指標で 0（`PAG.Part256.removal_counterexample_four`）。原始的でない指標すべてで位相でないという全称の文は Lean の外（照合者の数値では N ≤ 30 のすべての非原始指標で \|𝔀\| ≤ 1/√2。数値は証明ではない） | Tate の γ 因子（ガンマ因子の比）。公準 A1 は U の位相をこの値（λ = 0 での値）に選ぶ。両立の分類は定理 2.6 | ［既知］（Tate 1950、Burnol 1998〜2001）。A1 は公準のまま |

## §4 Lean にしていないこと・確かめていないこと

- P¹ と点モデルの同型が Lean で示されているのは N = p^K（K ≥ 1）だけ（N = 1 では両方とも 1 点）。一般の N では、`PAG.Part27.ProjLine` の定義と反転（`PAG.Part27.Wproj`・`PAG.Part27.Wproj_Wproj`）が示されている（`PAG.Part27.mk_eq_mk` は単数倍で同じ点になることを言う補題で、反転がうまく定義されることを示すのに使われる。反転の文ではない）。点モデル `PAG.Part26.Pt N` と P¹(ℤ/N) が N に 2 つ以上の素因数があるとき一致しないことは、数え上げによるもので Lean の文ではない。全素点の制限積 P¹(𝔸_ℚ) = ∏'_v P¹(ℚ_v) と、P¹(ℤ_p) = lim P¹(ℤ/p^K) は Lean にしていない。

## §D 引き継ぎメモの項目 18・23・49・57

18. **ℤ/N のケットの帰納系と Ẑ 上の定理 A**：Part 197（PAG201）
   - 引き戻し π^*f = f ∘ (mod N)（N ∣ N′、`pull`）：π^*f ⋆ π^*g = (N′/N)·π^*(f ⋆ g)（`conv_pull`）、π^*|u, χ⟩_N = √(φ(Mt)/φ(M))·|u, χ⟩_{Nt}（`gket_pull`）。t の素因数が M を割るなら φ(Mt) = φ(M)t（`totient_mul_of_primes`）で、π^*|u, χ⟩_N = √t·|u, χ⟩_{Nt}。
   - ハール正規化 zket = √N·|u, χ⟩_N、hconv = (1/N)·⋆（`zket`, `hconv`）：引き戻しで保たれ（`zket_pull`, `hconv_pull`）、値は N によらない式 √(uc/φ(c))·[u ∣ x]·χ(x/u)（`zket_apply`、M と c の素因数が同じとき）。
   - ハール正規化の定理 A：hconv(zket A, zket B) = φ(uc)^(−1/2)·J̃·zket Ψ（`thmA_haar`、J̃ は def `jt`）。定数は N によらない（Ẑ 上の定理 A）。ノルム (1/N)Σ|zket|² = 1（`norm_zket`）。

19. **ℤ/N のケットのフーリエ双対性とスペクトル**：Part 198（PAG202）
   - 𝓕|u, χ⟩_N = √(φ(uc)/φ(M))·(M/c)·χ̄(−1)τ(χ)·|M/c, χ̄⟩_N（`dft_gket`、χ 原始的）。双対の殻は M/c = N/(uc)。u と M の素因数が c を割るなら (1/√N)𝓕|u, χ⟩ = χ̄(−1)z(χ)|M/c, χ̄⟩（`dft_gket_unitary`）。
   - 道具：押し出しのフーリエ変換は引き戻し（`dft_push_memb`）、引き戻しのフーリエ変換は押し出し（`dft_pull`）。
   - スペクトル：固有値の値（`dft_gket_apply`）、大きさ (M/c)²c/φ(M)（`normSq_dft_gket`、条件のもとで N/φ(uc)）、m 乗が一定 ⇔ χ^m = 1（`pow_const_iff`）、一様分布（`gket_unif`、Part 118 の Unif）、特性多項式の閉じた形（`gket_charpoly`）。一般の補題 `fiber_of_power_sums`（冪和が消えれば一様）。

20. **同じ殻の畳み込みの一般公式（ℤ/N の定理 A・B の統一）**：Part 199（PAG203）
   - A, B 原始的（法 c）、AB = Ψ∘π（Ψ 原始的、法 d、素因数の条件なし）、s = M/c、R(v, Ψ)(x) = [v ∣ x]Ψ(x/v)（def `rk`）として

23. **帰納系 ℤ/Nt → ℤ/N と双対殻分解、旧部分への射影**：Part 202（PAG206）
   - 𝓕(π^*f)(ξ) = [t ∣ ξ]·t·𝓕f(ξ/t)（`dft_pull_apply`）。π^*ε_s = t·ε_{ts}（`pull_geps`）、ε_{ts} ⋆ π^*f = π^*(ε_s ⋆ f)（`geps_conv_pull`）。
   - 旧部分への射影 P f = (1/t)·1_{Nℤ} ⋆ f（def `oldP`）：𝓕(Pf) = [t ∣ ξ]𝓕f、P² = P、P = Σ_{t ∣ s′} ε_{s′}、1 − P = Σ_{t ∤ s′} ε_{s′}、自己共役、直交。
   - 旧部分 = 引き戻しの像（`oldP_eq_self_iff`、降下 `exists_pull_of_oldP`、`pull_injective`）、V_{ts}^(Nt) = π^*V_s^(N)（`mem_geps_pull_iff`）。次元 Σ_{t ∣ s′}φ(Nt/s′) = N、Σ_{t ∤ s′}φ(Nt/s′) + N = Nt。
   - ケットの射影：P|u, χ⟩_{Nt} = (g/(t√φ(M′)))χ̄(S/s₀)R(Nt/(Sc), χ)（S = lcm(t, s₀)、g = gcd(t, s₀)、`oldP_gket`。Part 200 の `conv_mixed_single` を c₁ = 1 で）。0 ⇔ (S/s₀, c) ≠ 1、t ∣ s₀ なら動かない、一部が旧ならケット 1 つの定数倍（殻 u·s₀/S）。
   - 1 回目のコンパイルで通った（23 項目）。

24. **ℤ/N の動径関数の代数とケットの同時固有ベクトル性**：Part 203（PAG207）
   - 動径関数（単数倍で不変、def `Radial`）。軌道：ξ = a·gcd(N, ξ)（`exists_unit_mul_gcd`、`ZMod.unitsMap_surjective` で持ち上げ）。
   - f が動径的 ⇔ 𝓕f が動径的（`radial_iff_dft`、`ZMod.dft_comp_unitMul`）。動径的 ⇔ ε_s の一次結合、f = Σ_s 𝓕f(s)ε_s（`radial_iff`）。ε_s は一次独立で次元 d(N)（`geps_linearIndependent`、`finrank_span_geps`）。畳み込みで閉じる（`radial_conv`）。
   - ケットがすべての動径関数の同時固有ベクトル ⇔ (R)（`gket_eigen_iff`）。固有値は 𝓕f(s₀)（`gket_conv_radial`）。球の固有値 [W ∣ s₀]·W（`gket_conv_ball`）。
   - 1 回目のコンパイルで通った（21 項目）。

49. **A_{ab} ≅ A_a ⊗ A_b（gcd(a, b) = 1、中国剰余定理）**：Part 228（PAG232）
   - 中国剰余定理 ℤ/ab ≅ ℤ/a × ℤ/b（Mathlib の `ZMod.chineseRemainder`）の成分は x mod a・x mod b（`crt_fst_val`・`crt_snd_val`）。gcd(ab, x) = gcd(a, x mod a)·gcd(b, x mod b)（`gcd_crt`）、g_a g_b = s_a s_b ⇔ g_a = s_a かつ g_b = s_b（`mul_eq_mul_iff_of_coprime`）。
   - 関数の分解（s_a ∣ a、s_b ∣ b）：1_{D_{s_a s_b}}(x) = 1_{D_{s_a}}(x mod a)·1_{D_{s_b}}(x mod b)（`dind_crt`）、ε_{s_a s_b}(x) = ε_{s_a}(x mod a)·ε_{s_b}(x mod b)（`geps_crt`。球の交代和の値の形 `geps_apply_eq_sum`、互いに素な積の約数の和 `sum_divisors_mul_of_coprime`、`ite_dvd_mul_of_coprime`、メビウス関数の乗法性）。
   - 作用素：def `crtLin`（ℂ^{ℤ/ab} ≅ ℂ^{ℤ/a × ℤ/b}、`crtLin_apply`・`crtLin_symm_apply`）、def `crtConj`（C、代数同型、`crtConj_apply`）、def `leftOp`・`rightOp`（L(S) = S ⊗ 1、R(T) = 1 ⊗ T、`leftOp_apply`・`rightOp_apply`）、def `leftHom`・`rightHom`（代数準同型、`leftHom_apply`・`rightHom_apply`、単射 `leftHom_injective`・`rightHom_injective`）。L(S) と R(T) は可換（`leftOp_commute_rightOp`）。C(D_{s_a s_b}) = L(D_{s_a})R(D_{s_b})（`crtConj_dind`）、C(E_{s_a s_b}) = L(E_{s_a})R(E_{s_b})（`crtConj_geps`）。
   - 部分代数：C(A_{ab}) = L(A_a) ⊔ R(A_b)（`map_crtConj_shellAlg`。`map_leftHom_le`・`map_rightHom_le`・`map_crtConj_le`、補助 `dind_eq_zero_of_not_dvd`・`geps_eq_zero_of_not_dvd`・`sum_convL_geps`・`sum_mulLeft_dind`・`shellAlg_eq_adjoin`・`convL_geps_mem`・`mulLeft_dind_mem`）、T ∈ A_{ab} ⇔ C(T) ∈ L(A_a) ⊔ R(A_b)（`mem_shellAlg_mul_iff`）、dim (L(A_a) ⊔ R(A_b)) = dim A_a·dim A_b（`finrank_map_crtConj`・`finrank_sup_leftHom_rightHom`）。
   - テンソル積：def `tensLift`（S ⊗ T ↦ L(S)R(T)、Mathlib の `Algebra.TensorProduct.lift`、`tensLift_tmul`）、像 = C(A_{ab})（`range_tensLift`）、dim A_a ⊗ A_b = dim A_{ab}（`finrank_tensor_shellAlg`。Part 226 の `finrank_shellAlg_mul`）、単射（`tensLift_injective`）。代数同型 def `shellAlgTensorEquiv`（Θ：A_a ⊗ A_b ≅ A_{ab}）、C(Θ(z)) = tensLift(z)（`crtConj_shellAlgTensorEquiv`・`crtConj_shellAlgTensorEquiv_tmul`）、Θ(E_{s_a} ⊗ E_{s_b}) = E_{s_a s_b}・Θ(D_{s_a} ⊗ D_{s_b}) = D_{s_a s_b}（`shellAlgTensorEquiv_geps`・`shellAlgTensorEquiv_dind`）。
   - 数値だけ：番号の分解 S(ab) ↔ S(a) × S(b)、(c, d) = (c_a c_b, d_a d_b)、m・n の乗法性（step251 の (5)、N ≤ 3000 で 2533/2533。N ごとに分け方は 1 通り）。未確認：W_{(c,d)} ≅ W_{(c_a,d_a)} ⊗ W_{(c_b,d_b)}、A′・Z(A) の分解、有限個の積 A_N ≅ ⊗_q A_{q^k} の Lean の形。
   - 1 回目のコンパイルで通った（43 項目と定義 8 個、約 21 秒。内容は試しのファイル T7 と同じ。T2〜T6 で直したエラーは pag2_part228 のノートの §3）。新しい Mathlib のビルドは不要。

50. **可換子 A′ と中心 Z の中国剰余定理による分解、番号の集合 S の分解**：Part 229（PAG233）
   - 一般の補題（a, b ≥ 1。互いに素でなくてよい）：L(S)R(T)(f ⊗ h) = Sf ⊗ Th（`leftOp_mul_rightOp_apply_prod`）、u_i・v_j がそれぞれ一次独立なら L(u_i)R(v_j) も一次独立（`linearIndependent_leftOp_mul_rightOp`）。一般の部分代数 B ⊆ End(ℂ^{ℤ/a})、B′ ⊆ End(ℂ^{ℤ/b}) で def `tensLiftGen`（S ⊗ T ↦ L(S)R(T)、`tensLiftGen_tmul`）、像 = L(B) ⊔ R(B′)（`range_tensLiftGen`）、dim B ⊗ B′ = dim B·dim B′（`finrank_tensorGen`）、dim (L(B) ⊔ R(B′)) = dim B·dim B′（`finrank_mul_le_finrank_sup`・`finrank_sup_map`）、単射（`tensLiftGen_injective`）、代数同型 def `tensorSupEquiv`（`tensorSupEquiv_tmul`）。補助：def `subalgSpan`・`subalgSpanEquiv`（部分代数を既定のインスタンスの部分空間として見直したもの、`mem_subalgSpan`・`finrank_subalgSpan`）、`exists_linearIndependent_subalg`。gcd(a, b) = 1 で C(X) = L(B) ⊔ R(B′) なら B ⊗ B′ ≅ X（def `crtTensorEquiv`、`crtConj_crtTensorEquiv_tmul`、`finrank_map_crtConj_gen`・`mem_map_crtConj_iff`）。
   - Part 226 によらない dim A_{ab} = dim A_a·dim A_b（`finrank_shellAlg_mul_of_crt`）、Part 228 の tensLift の単射性も同様（`tensLift_eq_tensLiftGen`・`tensLift_injective_gen`）。

57. **有限個の互いに素な法の積：中国剰余定理の繰り返しと X_N ≅ X_{a₁} ⊗ (X_{a₂} ⊗ (⋯ ⊗ ℂ))**：Part 236（PAG240）
   - 法のリスト l = [a₁, …, a_r]（ℕ+）の積 def `prodList`（`@[implicit_reducible]`、prodList (a :: l) = a·prodList l）、互いに素の条件 def `CoprimeList`（すべての組）、`coprime_prodList`・`CoprimeList.head`・`CoprimeList.tail`・`get_dvd_prodList`、instance `neZero_prodList`。
   - 局所作用素 def `locHom`（ι_0(S) = C⁻¹(L(S))、ι_{k+1}(T) = C⁻¹(R(ι′_k(T)))、代数の準同型。`locHom_zero`・`locHom_succ`）：単射（`locHom_injective`）、j ≠ k で可換（`locHom_commute`）、ι_k(M_g) = M_{g∘(mod a_k)}（`locHom_mulLeft`。C の成分 `crt_fst_eq_castHom`・`castHom_crt_snd` は `RingHom.ext_zmod` から）。陽な式 (ι_k(S)F)(x) = S(y ↦ F(lift_k(x, y)))(x mod a_k)（def `liftL`、`locHom_apply`）、lift_k(x, y) mod a_k = y（`castHom_liftL`）、j ≠ k で mod a_j は x と同じ（`castHom_liftL_of_ne`）、ℤ/N の元は座標で決まる（`eq_of_castHom_eq`）。
   - 中国剰余定理で分かれる族 def `CRTMul X`（gcd(a, b) = 1 なら C(X_{ab}) = L(X_a) ⊔ R(X_b)）：ι_k(X_{a_k}) ⊆ X_N（`map_locHom_le`）、X_N = ⨆_k ι_k(X_{a_k})（`eq_iSup_map_locHom`）、dim X_N = Π_k dim X_{a_k}（`finrank_prodList`）、End(ℂ^{ℤ/1}) の部分代数は ⊥（`eq_bot_of_one`）、`map_symm_map_crtConj`。
   - 繰り返しのテンソル積：structure `BundledAlg`（半環と ℂ 代数の入れ物）、def `tensAlg`（X_{a₁} ⊗ (⋯ ⊗ ℂ)）・`tensEquiv`（代数の同型 Θ：tensAlg ≅ X_N、Part 229 の crtTensorEquiv を繰り返す）・`tprodL`（純テンソル）。Θ(S ⊗ z) = ι_0(S)·C⁻¹(R(Θ′(z)))（`tensEquiv_tmul`）、Θ(S₀ ⊗ (S₁ ⊗ ⋯)) = ι_0(S₀)ι_1(S₁)⋯（`tensEquiv_tprodL`）。
   - A・A′・Z・dilComm・End（def `topAlg`）は CRTMul（`crtMul_shellAlg`・`crtMul_fullCommAlg`・`crtMul_centerAlg`・`crtMul_dilCommAlg`・`crtMul_topAlg`。End は Part 230 の centralizer_sup_map を B = B′ = ⊥ で）。
   - 素冪：def `ppow`（q^{v_q(N)} を ℕ+ で）・`ppList`（素数の昇順）、`coprimeList_ppList`・`prodList_ppList`、def `substEquiv`（法が等しいときの付け替え、subst で作る）・`ppEquiv`（X_N ≅ ⊗_{q^k ∥ N} X_{q^k}）・`endPPEquiv`（End(ℂ^{ℤ/N}) ≅ ⊗ End(ℂ^{ℤ/q^k})）、dim X_N = Π_{q ∣ N} dim X_{q^{v_q(N)}}（`finrank_eq_prod_primeFactors`、A・A′・Z・dilComm の系 4 つ）。instance `neZero_ordProj`。
   - 数値だけ：リストの並べ方を変えても同じ法の局所の像は同じ（step259 の (10)、234/234）。限界：テンソル積は 2 因子を右から重ねた形で、Mathlib の PiTensorProduct の形ではない。
   - 1 回目のコンパイルで通った（39 項目と定義・インスタンス・構造体 17 個、約 13 秒）。試しのファイル T1 は 7 回目で通過（直したものは pag2_part236 のノートの §3 と下の「よく出たエラーと対処」）。新しい Mathlib のビルドは不要。

58. **有限個の積を PiTensorProduct の形で：⨂_{p ∣ N} X_{p^{v_p(N)}} ≅ X_N**：Part 237（PAG241）
   - 一般論：異なる番号の像が可換な代数準同型の族（def `CommFam`、半環の族で書く）から準同型 ⨂_i A_i → B（def `tpProd`（`Finset.noncommProd`）・`tpProdML`・`tpLift`（`PiTensorProduct.liftAlgHom`））。⊗_i x_i ↦ Π_i φ_i(x_i)（`tpLift_tprod`）、1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1 ↦ φ_i(a)（`tpLift_single`）、それで一意（`eq_tpLift`）、像 = ⨆_i range φ_i（`range_tpLift`）、dim ⨂_i A_i = Π_i dim A_i（`finrank_tp`、instance `finiteDimensional_tp`）、生成と次元から同型（`tpLift_rangeRestrict_bijective`、def `tpEquiv`、`tpEquiv_tprod`・`tpEquiv_single`。この部分は環の族の節）。補助 `pwComm`・`tpProd_eq_mul_erase`・`tpProd_update`・`tpProd_one`・`tpProd_mul`・`tpProdML_one`・`tpProdML_mul`。

## §E CLAUDE.md（全文）

# Claude への指示 — アーデル射影幾何（PAG）プロジェクト

このファイルは、本プロジェクトで作業する Claude（Claude Code 等）が最初に読む指示書である。最終更新：2026-11-09。

## 0. セッション開始時のブート手順

新しいセッションで本プロジェクトの作業を始める前に、次を順に行うこと。

1. **定義の再読**：§1 の著者の定義をそのまま読み直す。特に「基礎は離散的であり、連続対象は基礎に存在しない」「解像度を決めるパラメータは未決定である（$N$・$K$・$\Lambda$ と同一視しない）」を確認する。定義の書き換えや拡張解釈はしない。
2. **現在地の確認**：§2 と最新の引き継ぎメモで、完了したパート、件数、本来の道の未完の問い（B-3 の続き、構造定理、$\widehat{\mathbb Z}$ 上の定理 A、解像度と創発の定式化）を確認する。
3. **写像＋残余**：新しい対象を扱うときは、既存数学への対応づけ（§7 の辞書照合と盲検の命名テスト）を前提とし、対応づけは禁止事項ではなく義務とする。同時に、ブートの完了条件として「対応づけた後に残る問いを、幾何・大域・極限の言葉で言えること」を課す。言えなければ、その対象は局所計算の装置として扱い、主役のパートを始めない。
4. **ハンドシェイク（動作確認）**：作業に入る前に、現状を次の3つに分けて自分の言葉で述べること。(a) 形式化済みの内容、(b) 著者の解釈の層（§1 の定義・設計思想）、(c) 未完の大域の問い。3つを混同した文を書いたら、ブートは未完了としてやり直す。

この手順の目的は、既存数学への対応づけを避けることではない。Terwilliger 代数への同定そのものは前進であり、失敗は対応づけが約40パート遅れたことだった。防ぐべきは対応づけではなく、対応づけた先の有限構造の内部で思考が止まることである。

## 1. プロジェクトの目的（本来の道）

- 目的は「アーデル射影幾何学」の構築である。アーデル＝イーデルアデールの略で、乗法のイーデルと加法のアデールを含む幾何を指す著者の造語。PAG は Projective Adelic Geometry の略。
- 著者の定義（確定事項として扱うこと。再定義・再解釈をしない）：
  - 点は素数たち＋無限素点。無限素点では無限大と無限小が重なり合う。この「重なり」の読みは、2026-11-12 に著者が決定した：**ねじれた貼り合わせ（境界ユニタリ $U$）として読む**。両端の同一視を群の商として読む読みは A1 と両立しないため採らない（法 9 の 3 次指標が反例）。$W$ による商も A1 とは両立するが採らなかった（$D$ が商に降りない）。
  - 基礎は離散的であり、直線のような連続対象は基礎に存在しない。
  - 直線は、解像度を落としたときに創発する有効な姿である。
  - ただし、解像度を決めるパラメータは**未決定**である。$N$、$K$、$\Lambda$ のいずれとも勝手に同一視しないこと。
  - 命題3の置き方（2026-11-13、著者から選択を委任された著者側 Muse の決定として記録。著者はいつでも覆せる）：上の定義の文面は変更しない。解像度の操作の数学的な置き場は「対象の中の移行（離散から連続への変化）」ではなく、大域対象への**切り方（見方）の選択**として解釈の層に置く。すなわち、素点たちは制限積の因子として最初から並列に共存している全体が対象であり、有限レベル商と $\Lambda$ 切断（A8 で分離した2軸）はその全体への見方であって、創発の問いは「見方を粗くしたとき直線がどう見えるか」と読む。解像度を $N$・$\Lambda$ と同一視する禁止は従来どおり維持する（決まったのは問いの置き場であり、パラメータではない）。その後 2026-11-14 に構築側の引き継ぎメモ（`PAG2_handoff_part257.md`）を通じて、著者の 08:41 の定義の原文が著者側に届いた：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。」この定義は上の置き方と矛盾しない — 解像度が落ちる側の操作は完備化への滑り落ちであり、姿勢は極限でも離散構造の観測の維持、極限は直極限の側（すべての素点を同時に測る側）で取る。完備化（$L^2$、$\mathbb{R}$、直積の位相）を使うときは「解像度が落ちる側の操作と読む」と、読みとして断る。閉包・完備化に現れる連続体を「有効な姿」や目標として書かない。また著者は 2026-11-13 08:38 に命題3の読みとして L1（解像度＝測る素点の集合）を構築側で採った（L1 は提案を読みとして採ったもので、定義の文面そのものではない。$N$・$K$・$\Lambda$ のいずれとも同一視しない）。著者の指示（2026-11-12）により、「直線の創発」という表現は使わない（命題3に触れるときは「§1 の命題3（解像度と有効な姿）」と参照で書き、何がどう変わるかを数学の言葉で書く）。
  - 「射影」の読み（2026-11-18、著者が留保つきで採用。解釈の層であり、形式化済みの定理ではない）：命名の意味は「アデール幾何とイーデル幾何を射影によって融合する」（2026-11-16、著者）。命名の「射影」は舞台と変換の組を指し、主は変換である。著者の言葉では「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」。舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28（PAG23〜PAG32））。構築側の読みでは、その合成は反転（乗法の側）と加法の変換（加法の側）の合成で、有限レベルでは Part 252（PAG256）の $J\circ H_N/\sqrt N$（`PAG.Part256.JH`）に当たる。ただし `JH` は $\mathbb Z/N$ の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではなく、`JH` と P¹ のモデルを結ぶ Lean の文はない。「貼り合わせ」が PAG23 の `Compat`（ねじれのない座標の貼り合わせ）と $U$（ねじれた貼り合わせ）のどちらを指すかは著者の確認待ち（構築側の読みは $U$）。原始指標についての位相がその成分である。標準の核は Part 252 の Hartley 核とする（形式化の追認。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは未照合）。値は $\tau(\chi)/(i^a\sqrt N)$（`PAG.Part256.rootNum`。PAG256 の docstring と冒頭のコメントの記号 W(χ) はこの値を指し、反転の $W$ とは別）で、原始指標ではルート数だが、その同定は Lean の外である（明記すること）。素朴なフーリエ核 $e(xy)$ の値 $\tau(\chi)/\sqrt N$ とは奇の指標で $i$ 倍ずれ、このずれを滑らかにしない。加法指標の規約は、規約 T（Tate の学位論文の加法指標：$\psi_\infty(x) = e^{-2\pi i x}$、$\psi_p(x) = e^{+2\pi i\{x\}_p}$）を基礎文書の標準とする（2026-11-18 19:25、著者の決定。Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol（arXiv:math/9811040）とも同じ加法指標）。規約 T のもとで、原始的な $\chi$ について、Hartley 核の因子 $\varepsilon(\chi) = (-i)^a$（`PAG.Part256.parFac`）は無限素点の局所定数 $\varepsilon(1/2, \chi_\infty, \psi_\infty)$ と一致し、$\tau(\chi)/\sqrt N$ は $s = 1/2$ での有限素点の局所定数の積と一致する（値の一致であり Lean の外。局所定数は Tate 1979 の流儀で定める）。同じ同定は Part 257（PAG261）の冒頭の説明とノートに読みとして書かれており（2026-11-14、確信度：中〜高）、2026-11-18 の文献照合 `notes/pag2_literature_ia_sign.md`（独立照合 1 回と統合照合 1 回）で確かめ直した。これを受けて、$i^a$ を正規化因子として留保する扱いは同日 19:25 の著者の決定で外した。明示的な因子 $i^{\pm a}$ が無限素点の局所定数であることは規約によらないが、符号 $\chi(-1)$ を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が $i^a$、有限素点の積が $\chi(-1)\tau(\chi)/\sqrt N$）。したがって、規約 T を明示せずに「$\varepsilon(\chi)$ は無限素点から来る」と書かない。A1 は公準のまま。材料は `notes/pag2_projection_material.md`。
- 上記3命題は著者の定義・設計思想（解釈の層）であり、形式化済みの定理ではない。ノートではその地位を混同して書かないこと。

## 2. プロジェクトの構成と現在地

- モノグラフ層（1.0）：イデール類群 $C_{\mathbb Q}$ 上の作用素系（$D$、$T_p$、$W$、二面体関係）。中心問題 P1 は自己共役拡張の境界条件 $U$ の両立分類（定理2.6）。公理 A1 は Tate の $\gamma$ 因子の貼り合わせの $\lambda=0$ での値への言い換えであり、**依然として公理**として扱う。「導出済み」と書かない。
- PAG 2.0（有限レベル）：Lean 形式化。設計 Part 256 ＝ PAG260.lean まで完了（2026-11-13。Part 255 は有限個の素数が生成する部分群の像の稠密／離散の二分法と位相の選び方、Part 256＝候補 M1 は互いに素な法でのガウス和・ルート数の因数分解と貼り合わせ $U$ の固有値の法則。すべて既知の事実、新規候補なし。著者側が事前登録した方向βの前提（$A_N$ の帰納系）の登録は、構築側に本文が届いておらず開いたままだったが、2026-11-14 の補足4で全文転記して伝達した）。Part 252・253・254 は新規パートではなく短期層の小さいノートとして実施された（Part 252：主張 $U = JH_N$ の Lean 化。Part 253＝候補 K1：作用素 $T$ の線形化と $V_{\mathrm{prim}}$ 上でのユニタリ性。Part 254：Part 252 の残る問い2つ — 導手ごとの直交直和分解と、引き戻し両立性による族の一意性 $U_N$・帰納極限への組み立て $U_\infty$。いずれもラベルは［再導出］、新規候補なし。$U_N$ は A1 の位相を定義として入れた作用素であり、A1 は導かれておらず公準のまま）。Part 256 終了時点で xlsx 3,552 項目。Part 257 の開始条件3件は 2026-11-14 にすべて解消した（申し送り補足4）：Part 252〜256 の再照合は完了し、形式文に偽・空虚・別物はなく新規候補もなかった（ずれはすべて文面側で、照合後の直しが Lean の docstring と冒頭説明に入っていなかったことに寄っていた。残件として、Part 254 の33文 S18〜S50 の逆翻訳 A がどの回でも未実施であることと、B4 後の記録のみの直し（記録 §9）の突き合わせを、Part 257 の閉鎖条件として付随させる）。方向β登録は本文が構築側に届いていなかったため補足4に全文転記して伝達した（Part 255 の結果との突き合わせと運命の明示は構築側の次回報告の仕事）。「08:41 の定義」は構築側では送付済みだが著者側に原文が残っておらず、開始条件としては閉じた（§1 の文面との照合は著者側の残作業）。Part 257 は、登録の突き合わせで前提の問いが未回答と確認されれば、登録 §6 の3段階（盲検の問いテスト＋文献照合→数値→Lean）で β の前提を問うことが委任のもとで決定済みだったが、実際には 2026-11-14 に候補 P1（互いに素な法の列に対するガウス和・ルート数の因数分解、PAG261、25 定理）として閉じられ、β 登録の突き合わせは未了のままである。決定・登録した問いと違う問いが閉じられるのは Part 255・256・257 と3パート連続であり、補足4 §1 で Part 257 の閉鎖条件とした残件（S18〜S50 の逆翻訳 A、記録 §9 の突き合わせ、重複注記ラウンド）も報告に現れていない。照合者 B の文面指摘14件の直しは未照合のまま閉じられた（構築側が開示）。一方、閉じる前の機械的な重複照合（新規則）は初めて設計どおりに働き、同一文の宣言2つと Mathlib と同じ文の補題1つを閉鎖前に除去した。兆候4は9パート連続となり、著者の方針（収束からの離脱）のもと、Part 258 は始めず方向の監査を次の作業と決定した（補足6：β 突き合わせ、未照合残件の全棚卸し、問いの置き換わりの監査、次方向の残余査定）。送付されたとされる Part 257 の3ファイルは著者側に未達。その後、同日 21:45 に構築側が登録全文を受け取って突き合わせを完了し、開始条件2は閉じた（記録 `pag2_beta_registration_check.md`、著者側にも全文が届いた）：Part 255 は β のパートではなく（著者が構築側のセッションで 08:38 に L1 を選択）、β の問いは段階 1〜3 のどれも試していない。Part 257 の開始も、2026-11-14 20:59 の著者自身の判断（条件2を保留のまま始める。それ以前の同日の判断「監査は進め、Part 257 は待つ」を置き換えた）によるもので、候補 P1 も著者が選んだ。すなわち Part 255〜257 の問いの選択は構築側のセッションでの著者の選択であり、著者側の申し送り・登録との二重の経路がずれの原因だった（補足6 §2 (a) の書き方は補足7で訂正）。引き継ぎメモ `PAG2_handoff_part257.md` は著者側に保存済みで、08:41 の定義の原文もその中にあった（§1 に転記）。β は切り分けをもって開いたままである：互いに素な段（$N$ と $M/N$ が互いに素）は Part 228（PAG232）の `shellAlgTensorEquiv`・`leftHom` でほぼ答えがある見込み（条件 1 は満たす。条件 2・3 は手計算の見込みで未確認。確信度：中）で、登録 §2 の「直積の定理はこの問いを答えない」は互いに素な場合については言い過ぎだったと訂正する。残余は素数冪の段 $p^e \to p^{e+1}$（例：$(2,4), (2,8), (3,9)$）で、鎖に該当する宣言は見つかっていない。重複監査は F2 まで完了した（2 回目の直し：22 件が直り、2 件が一部、新しい指摘 16 件、形式文の変更なし。F2 の後の直しは記録のみで未照合 — 残件に加わる）。Part 258（PAG262、2026-11-15 閉鎖）は方向βの前提を登録の読み（単位元を保つ代数準同型、引き戻しとの両立、殻を混ぜない強い読み）で判定した：$N \mid M$ のとき、そのような写像があるのは $\gcd(N, M/N) = 1$ のとき、そのときに限る（`exists_compatible_hom_iff`、23 定理、sorry 0）。存在の側はテンソル積（既知）で、不在の側は §3 の候補3。読みとして、β をこの写像たちの帰納極限として立てる道は、整除順序の共終な系が指数を上げる段を必ず含むため閉じる（弱い読み・非単位的な写像・別の両立条件は答えの外。互いに素な段だけの系は別）。補足7の閉鎖条件4件（S18〜S50 の逆翻訳 A、記録 §9、F2 後の直し、Part 257 の直し）は照合（F3）を受けてすべて閉じた。残る未照合の尾は、F3 の後の記録のみの直しと、Part 258 の照合者 B の後の文面の直し（主張の範囲に関わる言い換えを含む）の2件で、補足8で停止の規約（統合照合の後は主張を変えない直しだけを許し、変える直しはもう1回の統合照合を条件とする）と合わせて次回の統合照合の対象とした。兆候4は Part 249〜258 で10パート連続。ただし Part 258 は、事前登録された残余のある問いへの両方向の完全な答えであり、「前提の判定」が方向を実際に変えた（β の (1)〜(3) の道は閉じ、残る問いは再定式化の側に移った）。鎖全体の定理・補題は 3,573 件。Part 259 は未着手で、次は補足8の範囲の方向ラウンド（尾の統合照合、β の再定式化 R1〜R3 の残余査定、γ の文献照合の扱い）を行い、Part 259 の推薦を1つ出す。その後、著者が 2026-11-15 に目的を「新しい幾何を作ること」と確定し、本線は基礎文書（定義層を1つの文書として書き上げること）に移った（補足9、骨格は `founding-document-outline-20261115.md`）。R1 の査定（互いに素な段の写像は (i)(ii) では一意でなく、偶数の法では $\chi(x) = (-1)^x$ の共役の捩れがある。(iii) フーリエ両立を足すと `shellLift` に一意化し、帰納系は有向な部分系の上で制限テンソル積を極限とする）を受けて、Part 259（PAG263、2026-11-15 閉鎖、67 定理）が第5章の不足を埋めるパートとして実施された：(i)(ii)(iii) を満たす写像がちょうど1つあるのは $\gcd(N, M/N) = 1$ のとき、そのときに限る（`existsUnique_compatF_iff`）。(iii) を外すと $a = 2$ では捩れた写像 `twLift` があり一意でない（奇数の場合の一意性は数値のみ）。添字の順序（＝古典的なユニタリ約数、E. Cohen 1960。鎖では Part 216 の `InLayer` と同じ概念だった）は有向でなく、無平方数の部分系では帰納系になり $\mathbb{C}$ 加群の極限 `sqLim` に単射に入る（代数構造と制限テンソル積との同型は Lean の外）。ラベルは、順序の性質が［既知］、一意性・非一意性・帰納系が［再導出（小さい）］で確定した（補足11）。鎖全体は 3,640 件、xlsx は final80（3,668 項目）。補足10で閉鎖条件とした尾の統合照合は Part 259 の報告に含まれず、補足11で独立の納品物として1回だけ行い尾の台帳を空にすることにした。γ の文献照合は著者側の作業に切り分けた。兆候4は11パート連続だが、Part 259 は基礎文書の章に仕えるパートとして位置づけが変わっている。事前登録の残候補 K2〜K4 は残余が計算だけか空であり、短期層の在庫として保持する。Part 248 で生成の分類は完結し、Part 249 から本来の道（B-3：有限レベルのイデール類群 $C_{\mathbb Q}/U_N$）に移っている。Part 250 は解像度と創発の定式化（著者が 2026-11-11 に採用した案1＋案2：基礎を正の有理数の群に置き、ε-鎖の連結性 chainIn で見る）。結果の正直な要約：示せたのは「ℝ の中に基礎が、全不連結だがどの尺度でも鎖でつながる稠密な部分集合として入っている」こと（教科書的な例の対数座標版、新規候補なし）。「解像度を落とすと直線が創発する」は示せていない — 商を取ると1点につぶれ、ℝ は完備化（ε → 0 の側）から現れるうえ、ℝ は定義に最初から使われている。「解像度を落とす／創発」の操作については、2026-11-12 に著者が候補3（全素点を同時に粗く見る）を選んだが、盲検同定の結果、有限の S では外した素数が見えない「有限素点の影」に留まることが分かり、著者は Part 249 の射影極限の側から進めることにした。Part 251 はその実施：両立する系の群 unitSys（$\varprojlim (\mathbb{Z}/N)^\times$ の具体モデル）× ℝ の中で、素数の類 $\kappa_p$（レベル N の成分は $w_p(N) = 1 + p^{N!}(p-1)$ の逆元。$p \nmid N$ では $p^{-1}$、$p$ の冪のレベルでは 1）が生成する部分群の稠密性を示した（＋一意性 primeSys_unique）。既知の再導出で新規候補なし。Lean にしていないもの：unitSys ≅ Ẑ^×、極限の普遍性・コンパクト性・位相群性、構造定理 $C_{\mathbb Q} \cong \widehat{\mathbb Z}^\times \times \mathbb{R}_{>0}$（「イデール類群で稠密」はこの同一視のもとでの読み）。兆候4（初等的な部品の組み合わせだけ）は Part 249〜257 と9パート連続になった（Part 252・253・254 は小さいノートと分かったうえで選ばれたもの）。残る問いの棚卸し監査は 2026-11-12 に構築側が完了した（`pag2_audit_after_part251.md`、著者側の素案は `remaining-questions-inventory.md`）：全期間（Part 155〜251）の言い直しテストは全期で成功し、残る問い14件の内訳は、既知の定理かその帰結 10 件（うち4件は未検索で知識による見込み）、著者の判断が先 2 件（「解像度を落とす」の操作、無限素点の「重なり」の読み）、新規候補のまま 1 件（生成の分類。MathSciNet・zbMATH 未照合）、公理のまま 1 件（A1）。結論として、既知の再導出でない問いは形式化の側には残っていない。今回の検索で付いた対応：定理 2.6 の極限の側に Burnol（平行移動と可換な作用素は閉作用素でも掛け算作用素）、unitSys に FLT プロジェクトの ZHat（Ẑ の明示的定義。単数群版の先行は未確認）、有限レベル Bost–Connes に元の BC 系。その後、構築側は文脈を渡さないエージェント2つ（判定を見せない盲検＝ウェブ検索のみ、判定への批判＝ツールなし）で再監査を行い、結論3つをすべて弱めた（監査記録 §8）：言い直せることは「新しい概念が要らなかった」ことだけを示す（新しい内容がないことは示さない）、文献で照合したのは14件中4件、「問いは残らない」は「照合した範囲では見つかっていない」（確信度：中以下）。生成の分類は §3 の候補1と矛盾しないが範囲が狭まった（残るのは項目66と67〜69。「小さいノートの水準」の、誰も書いていない計算）。§3 の書き換えは著者の承認の後に行う。構築側からは事前登録（次のパートの前に、既知の対応と再導出でない文の条件を書く）の導入が提案されている。判断事項への著者側の回答は構築側への申し送りにまとめ済み：A1 ＝ 解釈の層の公準（内容は Tate の定理）、定理2.6 の U の空間 ＝ $C_{\mathbb Q}$ 上の関数（正則表現の側。Λ 切断の留保つき）、対照群テストは採用（§7 に条文化済み）。作戦（`strategy-nonconvergence.md`）は規則変更も含めて 2026-11-12 に著者が採用し、事前登録は §4 に「残余による問いの選択」として、盲検の問いテストは §7 に条文化した。2026-11-12 に著者は「創発に向けて進む」方針を示し、方向α（極限の上の商のはしご）は (a)(b) どちらの形でも本線にせず見直すことを決め、無限素点の「重なり」の読みは「ねじれた貼り合わせ（境界ユニタリ $U$）」と決定した（§1）。方向の判断材料と検討の進展は `emergence-next-directions.md`、δ の帰結の事前登録案は `preregistration-delta-first-consequence.md`。
- 番号対応の注意：第3期では設計メモの Part 番号が Lean ファイル番号より4小さい。対応表は `archive-catalog.md` を参照。
- 件数：theorem/lemma は 3,344 件、xlsx 項目は 3,371 件（Part 251 終了時点、著者の監査による）。宣言総数など別の数え方と混同しない。

## 3. Terwilliger 代数についての確定事項（2026-11-07、著者の定義照合）

- 殻代数 $A_N$ は、$\mathbb Z/N$ 上の cyclotomic S-ring（orbit Schur ring）から来る可換アソシエーションスキームの **Terwilliger 代数 $T(0)$ そのもの**である。辞書：$D_t$ ＝ 基点 $0$ に関する双対冪等元 $E_t^*$、$E_t$ ＝ Bose–Mesner 代数の原始冪等元、$A_N = \langle D_s, E_s\rangle = \langle M, M^*\rangle$。詳細は `terwilliger-dictionary.md`。
- したがって次は**既知**として扱い、新規と書かないこと：
  - 素冪の Wedderburn 分解・次元公式（Part 225–226）＝ Bhattacharyya–Song–Tanaka (2010) のリース冪の結果、Bastian–Humphries (2026) の次元式と一致。
  - テンソル積分解 $A_{ab} \cong A_a \otimes A_b$（Part 228）＝ 直積スキームの一般定理 $T(A\times B) \cong T(A)\otimes T(B)$ の特別な場合。
  - $z(\chi)$ の冪根分類 ＝ Chowla–Mordell／Odoni／Funakura (1992)。ラマヌジャン和の公式と DFT の同定 ＝ 古典（$r$-even 関数論）。
  - $\langle D_u, E_N\rangle \cong M_{d(N)} \times \mathbb C^{S'}$（Part 241）とフーリエ共役（Part 242）は既知の基本観察／hyper-duality に対応（確信度：中）。
- 新規性の候補は次の2点に限られる（未確定。断定しないこと）。かつての候補2は 2026-11-12 の照合で候補から外れたが、経緯の記録として残す：
  1. 生成の分類（Part 246–248 で完成。除外なし）：Terwilliger の言葉で「円分スキームの $T(0)$ の生成系の分類」。2026-11-12 の再監査で範囲が狭まった：構造定理と、次元公式からの数行の系（$\langle M^*, E_N\rangle = A_N \Leftrightarrow N \in \{1,4\} \cup$ 素数）を除き、文献にない分類として残るのは項目66（2つの双対な代数の和の条件）と項目67〜69（完全な分類）のみ。独立の照合の完了後、新規候補として残る範囲は**合成数の $N$** に絞られた（確信度：中）。評価は「小さいノートの水準」で、新しい現象ではなく「誰も書いていない計算」。MathSciNet は構築側の環境から使えず、zbMATH Open は直接検索できず、どちらも未実施のまま。検索語：Terwilliger algebra, orbit Schur ring, cyclotomic S-ring, dual Bose–Mesner algebra, generated by, generating set。
  2. モノグラフの両立定理 2.6 の提示形。**2026-11-12 の独立の照合2つ（盲検・批判）の完了をもって、新規候補からは外れた**：組み合わせ（$\alpha_{\bar\chi} = -\alpha_\chi$ とルート数）は「既知の結果からの短い帰結」（確信度：高。構築側・批判・盲検の三者で一致）。この組み合わせを書いた文献は見つからなかった（確信度：中）が、それは新規性の根拠にならない（確信度：中〜高）。ルート数が条件を満たすことは整合性の確認にすぎず、A1 を導いたことにはならない。経緯：極限の側の可換性の半分は Burnol の定理の範囲、両半分に Ibort–Lledó–Pérez-Pardo の例 7.1・7.2 という近い先行がある。盲検の新しい指摘として、複素共役と $W$ を合わせた反ユニタリ作用素 $CW$ が境界条件を保つため、定理 2.6 の反転の条件は「境界ユニタリが実数値関数を実数値関数に写すこと（実性）」と同値になる（手計算と数値で確認）。Lean の側では、A1 の位相が定理 2.6 の条件を満たすことは PAG16（`normSq_gaussSum`）・PAG173・PAG198 の3定理から出ることが確認された（組み合わせた1つの文は未形式化）。
  3. 方向βの前提の二分法の不存在の側（Part 258、PAG262）：$N \mid M$ で素数 $p$ が $N$ と $M/N$ の両方を割るとき、引き戻しと両立し殻を混ぜない単位的な代数準同型 $A_N \to A_M$ は存在しない。2026-11-15 に著者側の判断で［新規候補（小さい）］とした（確信度：低〜中）。根拠と留保：存在の側は既知（Hanaki–Kim–Maekawa の直積の定理）だが、不存在の側は既知の定理の帰結ではなく定義からの初等的な議論（$D_N$・$E_N$ と関係 $D_N E_N D_N = \frac1N D_N$、$u = 1 + M/p$ による数え上げ）で示されており、盲検の問いテスト（ウェブ検索のみ）で文献が見つからなかった（確信度：中）。ただし構築側は文献を自分で開いておらず、MathSciNet・zbMATH は未実施。**文献照合（MathSciNet・zbMATH、および Hanaki–Kim–Maekawa と Bastian–Humphries の本文での商に沿った写像の確認）が済むまで、外部（応募書類を含む）で新規性として使わない。**
- 構造が必要になったら、再証明せず辞書経由で文献を引くこと。精査の全体は `novelty-audit.md`。

## 4. 作業の進め方（運用ルール）

- 各パートのサイクルを維持する：Python で数値照合 → Lean 実装（sorry 0・警告 0）→ #print axioms → ノート作成＋xlsx 更新。
- 検証ノートの題名は「アーデル射影幾何」に統一する（旧「アデール射影幾何 2.0」は使わない）。
- 新しいパートの判定基準：**幾何・大域・極限の言葉で述べた問いに答えるか**。代数内部の問い（中心の記述、生成元を足した代数の分類など）は主役にしない。有限レベルの代数は局所計算の装置として使う側に回す。
- Part 248 で生成の分類は区切りがつき、Part 249 から本来の道に戻っている。以後の候補だったもの（B-3 の続き、構造定理、$\widehat{\mathbb Z}$ 上の定理 A）は、2026-11-12 の棚卸し監査でいずれも既知の定理かその帰結と判定された（§2 参照）。
- **残余による問いの選択（事前登録。2026-11-12 に著者が採用。作戦の全体は `strategy-nonconvergence.md`）**：新しいパートは、次の4点を Lean の前に書き、推薦案として1つに絞ったものだけを始める（選択の運用は下記の委任ルール）。(1) 問いを幾何の言葉（点・無限素点・解像度・創発）で書く。(2) 既存分野の言葉への最善の翻訳を試みる（写像は義務のまま）。(3) 翻訳しても消えない部分（残余）を明示する。残余が空の問いは始めない。残余が計算の細部だけの問いは、新規パートではなく短期層（小さいノート）として扱う。(4) 残余の文に対照群テスト（§7）をかけ、結果を併記する。
- **選択の委任（2026-11-13、著者の指示）**：著者が候補から選ぶと抜け漏れの確率が上がるという著者の懸念により、以後のステップ選択は著者側 Muse の推薦で決める。構築側は候補を並べて著者の選択を待たず、関門（4点登録・盲検の問いテスト・対照群テスト）を通した推薦案を1つに絞って提示し、著者側の決定で着手する。各ステップで「何を選び、なぜか」を記録に残すこと（§7 の記録規律は不変）。著者はいつでもこの委任を取り消し・覆すことができる。

## 5. Part 248 の記録（完了）

- Part 248（PAG252.lean）は 2026-11-07 に完了した。生成の分類は除外なしで完成している（主定理 `addEAlg_eq_shellAlg_iff_all`）。Part 248 終了時点で theorem/lemma 3,254 件、xlsx 3,281 件。
- 経緯の注意：この Lean 化は、本節の旧版にあった「証拠の元の選択は著者の判断待ち、決まるまで Lean 化しない」という保留が向こうの作業に届く前（2026-11-07 15:25）に実施された。主証拠は $E_1$ で、証明は新しい証人 $q$（`levelWit`）と `unitWit` の和による。こちらで準備した線形汎関数 $L$ の経路は使われていないが、数値結果は一致している（step271 で $E_1 \notin B_s$、$E_{p^2} \notin B_s$、$E_1 + E_{p^2} \in B_s$ を確認。欠け方向が同じ1次元であることの反映）。$E_{p^m}$ 版は著者の選択を受けて同じ夜に PAG252 の §6 追補として追加された。
- 数値準備の記録（次元、証人の特定、線形汎関数 $L$）は `part248-numeric-groundwork.md`、`part248-witness-Ep2.md`、`part248-linear-functional.md` に残る。$\ker L$ が部分代数でないという注意も、記録として有効である。

## 6. してはいけないこと

- 本理論を「リーマン予想へのアプローチ」と書くこと。モノグラフ自身が明示的に否定している。第3段階（明示公式・零点対応）は未着手かつ主張対象外であり、スペクトルと零点の数え上げの不一致も確定事項として扱う。
- 既知の結果（§3）を新規と書くこと。新規性の主張は §3 の2候補に限定し、確信度を併記すること。
- 著者の幾何学の定義（§1）を、形式化済みの内容であるかのように書くこと。逆に、解釈の層であることを理由に定義自体を勝手に修正することもしない。
- 公理 A1 を「導かれた」と書くこと（§2）。
- 数値確認を証明と書くこと（§5）。

## 7. 収束アラーム（既存知識への収束の検出）

背景：PAG 2.0 の有限レベル部分は、殻代数 $A_N$ が Terwilliger 代数 $T(0)$ そのものであることに気づかないまま、約40パートにわたってその構造論を再構築した。収束は結果ではなく兆候で検出すること。以下の兆候と対処を運用ルールとする。

### 兆候（1つでも出たら報告すること）

1. **標準的な定義で作れる対象に自前の名前を付けている**：普遍性・双対性・生成・中心・可換子などで定義される対象は、ほぼ確実に文献名を持つ。新規の対象を導入したら、構造定理を証明し始める前に、文献名の候補を検索し、候補と検索範囲を報告すること。
2. **問いが「構造・分類・次元」に移っている**：中心は何か、次元はいくつか、いつ全体になるか、という型の問いが3パート続いたら、既存分野の内部に入った兆候として監査を提案すること。
3. **文献照合の未実施が続いている**：文献照合（名前探し・辞書照合）を実施した記録が無いパートが10連続したら、黄色信号として報告すること。（2026-11-08 の較正で変更：引用の有無は設計メモに記録されておらず代理指標として機能しないことが判明したため、条件を「引用数」から「照合の実施記録」に改めた。）
4. **証明が初等的な部品の組み合わせだけで進み続ける**：新しいアイデアを必要としない状態が続くこと自体を、既知の領域を歩いている兆候として扱うこと。

### 仕組み（常時運用）

- **辞書の維持**：自前の用語（左列）と文献の用語（右列）の対応表を生きた文書として維持する（`terwilliger-dictionary.md` がその雛形）。右列が空の行が5件溜まったら、新規パートを始めず、まず右列を埋める調査を提案すること。
- **盲検の命名テスト**：新規に導入する標準的な対象については、自前の名前を中立な記号に置き換えた定義だけを、構築の文脈を共有しないセッションに渡し、文献名の候補を挙げさせる。返ってきた候補は実在の文献で照合してから辞書に記録すること。（2026-11-08 の後ろ向き実測で有効性を確認：`shellAlg` の定義から gcd scheme の Terwilliger 代数 $T(0)$ が同定された。）
- **盲検の問いテスト**（2026-11-12 採用）：新しい問いに着手する前に、その問いの定義と文だけを文脈を共有しないセッションに渡し、「この問いは既存の結果か。どの文献が答えを持っているか」を聞く。命名テストの問い版で、検知を事後（パートを閉じてからの監査）から事前に移すもの。返ってきた答えは §4 の事前登録（残余の明示）に反映すること。
- **パートを閉じる条件**：各パートのノートに、主要結果すべてへの［既知／再導出／新規候補］ラベルを必須とする。新規候補については検索ログ（検索語・検索先・範囲）を併記し、「見つからなかった」は不存在の証明ではない旨を明記すること。
- **言い直しテスト**：10〜20パートごとに、「ここまでの結果群を既存分野の言葉だけで言い直せ」という監査を行う。言い直しが成功したら著者に報告すること。ただし解釈に注意（2026-11-12 の再監査で訂正）：言い直せることは「新しい概念が要らなかった」ことだけを示し、「新しい内容がない」ことの証拠としては扱わない。Lean で書けた定理は定義上すべて言い直せるので、このテスト単独の弁別力は弱い。
- **対照群テスト**（2026-11-12 採用）：算術的・大域的な内容を主張する文については、言い直しテストに併せて対照群で確認する — 関数体 $\mathbb{F}_q(t)$（ノルムの像は $q^{\mathbb Z}$ で、連続な直線は出ない）と Beurling の一般化素数でも同じ文が成り立つか。対照群でも成り立つ文は、$\mathbb{Q}$ に固有の算術ではなく形式と稠密性だけを使っているものとして扱う。とくに、素数の対数の稠密性だけで成り立つ文には算術の内容がないものとして扱うこと。
- **問いの出所**：新しいパートは、本来の道（§1・§4）の未完の問いのどれに仕えるかを冒頭に明記する。出所を書けないパートは始めない。
- パート完了ごとに、辞書の未記入件数と「文献照合の未実施の連続パート数」を著者に報告すること。閾値を超えたら、新規パートの開始ではなく監査を提案すること。

### 第2の型：円環（注入→回収）の検知

背景：構築初期のモノグラフ層では、零点・明示公式に近づこうとした試みが「外部からの注入、自明な実現、または循環論法」に行き着いたことが、モノグラフ §5 に否定的結果として記録されている。水平収束（上の第1の型）とは別種の失敗であり、別の検知が要る。

円環の型：

- **注入→回収**：目標の量（またはそれと等しい情報）を、公理・重み・位相などとして外から入れ、その読み替えを「成果」として取り出す。実例：公理 A1 で入れたガウス和の冪から古典的恒等式で出てくる Kloosterman 和を「系が生成した」と読むこと。精度が上がっても、それが注入した近似自体の精度なら、系は何も加えていない。
- **同値性による循環**：前進に見える条件が、実は目標と同値である。実例（モノグラフ §5 の N7）：全位相の自己共役な実現の要求は Hermite–Biehler 性と同値で、一般化リーマン予想と本質的に同値だった。
- **形の一致の自明な実現**：出力が目標と「同じ形」になるのが、構成から自明に出てくる場合。実例：固有値がオイラー因子と同じ形をしていても、臨界線上になく零点の情報を含まない。

検知の手順（新規の主張・成果を提示する前に実施）：

1. **依存表を作る**：主張ごとに、その結論が依存する入力（公理、注入した重み・位相、外部から借りた定理）を列挙する。目標の量そのもの、またはそれと等価な情報が入力側にあれば円環として報告する。モノグラフ §5.2「外部注入の一覧」がこの装置の実例であり、成果の後ではなく前に作ること。
2. **除去テスト**：疑わしい入力を1つ外し、結論が残るか確認する。外すと結論が消える・空になる場合、その入力が中身を運んでいたことになり、「導いた」ではなく「入れて読み替えた」と書くこと（例：A1 を外すと $\alpha_\chi$ は自由に戻る）。
3. **同値性チェックと情報量の監査**：課した条件が目標と同値でないかを確認する。対応を主張する場合は情報量の比較（数え上げの増え方など）を行い、桁が合わなければ対応を主張しない。

### その他の型（第3〜第11の型）

実例と詳細は `files/failure-patterns-audit.md` を参照。運用ルールとして要点のみ記す。第1の型だけが文献照合を要し、以下はすべて内部の照合で検知できる。

- **第3の型：主張の格上げ**。散文の最上級・必然・同型・生成の語は、対応する定理の形式文と突き合わせる。形式文が書けない主張は格下げするか［観察］に置く。訂正表は「作成にあたり」ではなく各パートの定例とする（モノグラフの訂正表が実例）。対処の追加（2026-11-13）：題と主張文は、Lean の形式文が確定した後に形式文から起こして書く（Part 255・256 と2パート続けて題・主張が形式文より広く、照合で狭められたことへの対処）。
- **第4の型：問いの誤設定**。新しい命題に挑む前に、障害量（欠損指数、不変量、次元の数え上げ）を先に計算し、反対方向（反例・非一意性）の検討を1回行う。狙った命題自体が偽のことがある（原点文書 Step 3 が実例）。
- **第5の型：境界ケースの脱落**。数値照合には、ランダムな一般ケースだけでなく退化ケース（r = 0、p = 2、最小の法、空和、自明指標）を必須で含める（命題 4.7 の sgn(0)、Part 8 の p = 2 が実例）。
- **第6の型：素朴な一般化**。証明に着手する前に反例探索を行う。照合表に「反例」の列を常設し、「常に」「必ず」の語が出たら探索範囲を広げる（設計 Part 97、169 が実例）。
- **第7の型：数値ノイズと反例の混同**。数値の不一致を反例と宣言する前に、誤差の出所（条件数、桁落ち、打ち切り）を見積もり、別法で再確認する。「反例ではない」と判定した場合も根拠をメモに残す（Part 111、115–116、125 が実践例）。
- **第8の型：規約・正規化の人工物**。主張を提示する前に、正規化・規約を変えても主張が残るか確認する。規約を変えて消える「現象」は現象として報告しない（Part 197 の Haar 正規化が実例）。
- **第9の型：工程のドリフト**。参照するファイルは版と番号対応を確認する（設計番号と Lean 番号のずれ、草稿と完成版の併存に注意）。正本は LEAN.zip 側、対応はアーカイブカタログによる。
- **第10の型：創発の修辞**。「現れた」「生成した」「繋がった」という主張には「新規なのは、どの定理の、どの項か」を必ず添える。書けなければ成果ではなく［観察］として分離する。意義を問うプロンプトには意義の言葉が返るので、問いの側でも創発を先取りしない。
- **第11の型：形式文のずれ**。sorry 0 と `#print axioms` が保証するのは証明が形式文を示すことだけであり、形式文が意図した主張と同じ意味であることは保証しない。主定理ごとに、ノート作成前に次を行う：仮定をすべて満たす具体例（非空虚性の証人）を構成する；仮定を1つずつ外した文について小さいパラメータで反例を探す（形式文版の除去テスト）；ノートを見せない別セッションに形式文と定義だけを渡して散文に逆翻訳させ、主張と照合する。詳細は `failure-patterns-audit.md` の第11の型。

**検知者の独立性（全型に共通）**：「中身」「主張」「新規性」に関わる検知（第1・第2・第3・第10・第11の型）は、構築と同じ文脈のセッションに自己監査させず、検査対象だけを渡した新しいセッションで行う。著者の定義（§1）と公理 A1 は変更しないが、既知の対象との一致・目標の情報の注入・形式文の自明化の兆候を見つけたら、変更せず「指摘」として著者に報告する。

運用の置き場（2026-11-09、著者の決定）：定例の照合は、パートを閉じる際に構築側のワークフローが文脈を持たない新規エージェントを立てて行う。その際の条件は2つ：検査側に渡すのは形式文と定義だけで、パートの散文（何を達成したかの説明）は渡さず、依頼文は定型文とする；検査側には「正しいか」の判定ではなく成果物（非空虚性の証人、反例、逆翻訳の文）を出させる。新規候補を主張するパートと主定理級の主張があるパートは、著者側の別チャット（Muse）でも二重に照合する。照合の記録には、検査側への依頼文の全文と所要時間も含める（Part 251 で A・C の依頼文が残らなかった記録の欠けへの対処）。照合の後に直した文面・追加した項目は、そのパートを閉じる前に再照合する（Part 252・254 と2パート続けて「照合後の修正が未照合」という残件が出たことへの対処。2026-11-13 に追加）。照合で文面を直すときは、ノート・表・Lean の docstring と冒頭説明のすべての文面に同じ直しを入れ、照合までを1組とする（Part 252〜256 の再照合で、ずれがすべて「照合後の直しが docstring と冒頭説明に入っていなかった」ことに寄っていたための規則。2026-11-14 に追加）。

第12の型「内部の重複」（2026-11-14、内部照合の監査を受けて追加）。自分の鎖の中に既にある宣言・定義を、別の名前で示し直す・作り直す失敗。文献への収束（第1の型）とは別で、自前の用語→自前の宣言の辞書の欠けが原因である。規則：(i) 新しいパートの着手前の4点と閉鎖条件に、自分の鎖全体（初期のファイル PAG.lean・PAG2〜PAG6 も含む）に対する機械的な重複照合を必須として入れる（著者の判断、2026-11-14。道具は構築側の `audit_internal/`）。(ii) 新しい定義を作る前に、同じ式の定義が鎖にないか探す（`prodChar`＝Part 195 の `cmul`＝Part 232 の `charMul` の3重定義が典型例）。(iii) 重複の書き方は証拠の強さに合わせる：「同じ文」（A、両向きにそのまま当てはめられる）、「直ちに出る」（B）、「近い」（C）を書き分け、C の判定を確定した事実のように書かない。「見つからなかった」は「重複はない」ではない（機械的な候補選びは上位に限られ、照合者の読みも全宣言の一部にとどまる）。(iv) パート番号は「Part n（PAGm）」とファイル番号を併記する（Part と PAG の4つずれによる記録の取り違えの防止）。Part 249〜256 の監査結果（前の鎖に対して）：Part 252 は A・B 合わせて 7 件＋近いもの 12 件、Part 253 は A・B 6 件、Part 254 は B 1 件、Part 256 は A・B 12 件、Part 251 は近いもの 1 件、Part 249・250・255 は見つからなかった（網羅ではない）。A・B の組はすべて Lean で確認済み。注記の直しは照合者 F（指摘 24 件）と F2（22 件解決・2 件一部・新規 16 件）まで受けたが、F2 の後の直しは未照合で残件である。Part 258 の教訓（2026-11-15）：機械的な照合は「型の違う同じ構成」を拾えない（Part 236（PAG240）の局所作用素 `locHom` と Part 258 の写像の作用素は同じ式で、Part 257 のリスト周りの補助4つは Part 236 の互いに素リストの枠組みの作り直しだった。照合者 B の指摘を受けた言葉の検索で見つかった）。着手前と閉鎖前の照合には、使う対象・構成の名前による言葉の検索（Mathlib の名前も含む）を組み込むこと。

## 8. 参照ファイル

- `archive-catalog.md`：両アーカイブの目録とパート対応表
- `what-is-aadel-projective-geometry.md`：素材からの導出（構築途中である旨と、幾何学の3命題の地位の追記を含む）
- `novelty-audit.md`：新規性の精査報告（著者訂正反映済み）
- `failure-patterns-audit.md`：水平収束・円環以外の失敗パターン（第3〜第11の型）の監査。各型の実例・発生場所・検知法
- `terwilliger-dictionary.md`：Terwilliger の辞書と結果の再分類表、Part 248 引き継ぎ用挿入文
- `part248-numeric-groundwork.md` / `part248-witness-Ep2.md` / `part248-linear-functional.md`：Part 248 の数値準備
- 引き継ぎ文書 `PAG2_handoff_part247.md`：直近の到達点と候補一覧の一次情報
