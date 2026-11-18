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
