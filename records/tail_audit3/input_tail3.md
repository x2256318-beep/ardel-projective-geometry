# 統合照合の入力（2026-11-19）

§A は前回の照合の後に入った変更の差分。§B は変更後のファイルの全文。§C は索引に出る宣言の docstring と形式文（定理は := まで、定義は本体を含む）。§D は PAG256.lean の全文。§E は Part 257（PAG261）の冒頭の説明と、Part 257 のノートの冒頭。

## §A 差分

### A1 材料索引（照合済みの第 1 版 → 現行の第 2 版）
```diff
--- records/founding_index/before_index_v1.md	2026-11-18 20:11:24.135873938 +0900
+++ notes/pag2_founding_material_index.md	2026-11-18 20:11:24.119824229 +0900
@@ -1,6 +1,6 @@
 # アーデル射影幾何 — 基礎文書の材料索引（骨格の 6 章ごと）
 
-（2026-11-18。短期層の作業。新しいパートではない。基礎文書の骨格（著者側、2026-11-15）の章ごとに、書く主張・その地位・支える Lean の宣言・ノート・照合の状態・開いている点を並べる。起草は著者側で行う。この索引は主張を足さない。地位とラベルは各ノートと CLAUDE.md の記載を写したもので、写すときに強めないことを方針とした。）
+（2026-11-18。短期層の作業。新しいパートではない。基礎文書の骨格（著者側、2026-11-15。以下「骨格」）の章ごとに、書く主張・その地位・支える Lean の宣言・ノート・照合の状態・開いている点を並べる。起草は著者側で行う。この索引は主張を足さない。地位とラベルは各ノート・CLAUDE.md・骨格の記載を写したもので、写すときに強めないことを方針とした。第 1 版を独立照合にかけ、その指摘で直した第 2 版がこれである（§8）。）
 
 ## §0 使い方と注意
 
@@ -9,274 +9,357 @@
   - 「読み」＝解釈の層。誰が出し、誰が採用したかを添える。
   - 「定理」＝Lean の文。ラベル［既知］［再導出］［新規候補］を添える。
   - 「公準」＝A1。
-  - 「数値のみ」＝数値確認だけで証明はない。
+  - 「数値のみ」＝数値確認だけで、証明はない。
   - 「Lean の外」＝文献か手計算による。
-- **番号の罠**：PAG 2.0 の Part n は PAG(n+4).lean で、Lean の名前空間はファイル番号に従う。例：Part 252 の宣言は `PAG.Part256.…`、Part 23 の宣言は `PAG.Part27.…`。この索引では「Part n（PAGm）」と併記し、宣言は完全修飾名で書く。
+- **番号の罠**：
+  - 第 3 期（PAG 2.0）の Part n は PAG(n+4).lean。Lean の名前空間はファイル番号に従う（例：Part 252 の宣言は `PAG.Part256.…`、Part 23 の宣言は `PAG.Part27.…`）。初期のファイル（PAG.lean・PAG2〜PAG6）にはこの対応は当てはまらない。
+  - この索引では「Part n（PAGm）」と併記し、宣言は完全修飾名で書く。
+- **記号の罠**：
+  - 反転（0 と ∞ の入れ替え）は、Lean の `PAG.Part23.W`・`PAG.Part26.Wpt`・`PAG.Part27.Wproj` とモノグラフの W。この索引では ι とも書く。
+  - `PAG.Part256.rootNum` の値（τ(χ)/(i^a√N)）は 𝔀(χ) と書く。PAG256 以降の docstring とノートでは記号 W(χ) がこの値を指すので、反転の W と混同しない。
 - **照合の状態**：各パートを閉じるときの独立照合と、その後の再照合・統合照合を指す。詳細は各ノートの照合の節。
-- 骨格が引く著者側のファイル（`what-is-aadel-projective-geometry.md`、A8 の一次評価、δ の事前登録と帰結、モノグラフ層の記録）は、このリポジトリにない。索引ではファイル名だけを挙げる。
-- 宣言名は、2026-11-18 にこの索引に出るものをすべて Lean のファイルで検索して実在を確かめた（§7）。
+- **著者側のファイル**：骨格が引く次のファイルは、このリポジトリにない。索引ではファイル名だけを挙げる。
+  - `what-is-aadel-projective-geometry.md`
+  - A8 の一次評価
+  - δ の事前登録と帰結
+  - モノグラフ層の記録
+  - 骨格そのもの
+- **宣言名の確認**：2026-11-18 に、この索引に出る宣言名をすべて Lean のファイルで検索し、実在を確かめた（§7）。
 
 ## 第 1 章　点と大域対象
 
 **1.1 点は素数たちと無限素点。無限素点では無限大と無限小が重なり合う。**
 - 地位：定義（著者の文面、CLAUDE.md §1）。
-- Lean：定義そのものはない。関連する定理として、すべての素点の付値の組は単射（`PAG.Part259.eq_of_padicValRat_eq`）。積公式 log q = Σ v_s(q) log s（`PAG.Part259.log_eq_sum_of_support`）により、∞ の座標は有限素点の座標から決まる。どちらも Part 255（PAG259）の［既知］。
+- Lean：定義そのものはない。関連する定理は次の 2 つで、どちらも Part 255（PAG259）の［既知］。
+  - 正の有理数について、すべての素数（有限素点）の付値の組は単射：`PAG.Part259.eq_of_padicValRat_eq`。
+  - 積公式 log q = Σ v_s(q) log s：`PAG.Part259.log_eq_sum_of_support`。∞ の座標は有限素点の座標から決まる。
 - ノート：`pag2_part255_resolution_discrete_limit.md`。
 
 **1.2 大域対象は、制限積の因子として最初から並列に共存する素点たち。有限レベル商と Λ 切断は、その全体への見方（切り方）。**
-- 地位：読み。命題 3 の置き方として、著者側 Muse の決定（2026-11-13、著者はいつでも覆せる）。
-- Lean：極限の具体モデル `PAG.Part255.unitSys`（両立する系の群。Part 251（PAG255））。`unitSys` ≅ Ẑ^×、構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0}、制限積そのものは Lean の外。
-- ノート：`pag2_part251_projective_limit.md`。A8 の一次評価は著者側のファイル。
+- 地位：読み。命題 3 の置き方として、著者側 Muse の決定（2026-11-13。著者はいつでも覆せる）。
+- 書き方の規則：解像度を N・Λ と同一視する禁止は維持する。決まったのは問いの置き場であり、パラメータではない。
+- Lean（関連するもの。支えではない）：
+  - Ẑ^× の具体モデル `PAG.Part255.unitSys`（両立する系の群、Part 251（PAG255））。
+  - 制限積・無限素点・ℚ^× での商は含まない。`unitSys` ≅ Ẑ^× と構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0} は Lean の外。
+- ノート：CLAUDE.md §1、`pag2_part251_projective_limit.md`。A8 の一次評価は著者側のファイル。
 
-**1.3 素数の類は、大域対象の中で稠密な部分群を生成する。**
-- 地位：定理［既知］（再導出、新規候補なし）。
+**1.3 素数の類は、有限レベル (ℤ/N)^× × ℝ と、極限の具体モデル `unitSys` × ℝ で、稠密な部分群を生成する。**
+- 地位：定理［既知］（再導出。新規候補なし）。
 - Lean：
-  - 有限レベル (ℤ/N)^× × ℝ では `PAG.Part253.exists_cls_near`（Part 249（PAG253））。
-  - 極限のモデル `unitSys × ℝ` では `PAG.Part255.dense_closure_allPrimes`・`PAG.Part255.dense_closure_primeGens`（Part 251（PAG255））。
-  - 素数の類の一意性は `PAG.Part255.primeSys_unique`。
-- 留保：「イデール類群で稠密」は、Lean の外の同一視のもとでの読み。
+  - 有限レベルでは `PAG.Part253.exists_cls_near`（Part 249（PAG253））。正の有理数 m/n の類についての文。
+  - 極限のモデルでは `PAG.Part255.dense_closure_allPrimes`・`PAG.Part255.dense_closure_primeGens`（Part 251（PAG255））。素数の類の一意性は `PAG.Part255.primeSys_unique`。
+- 留保：「大域対象で稠密」「イデール類群で稠密」は、Lean の外の同一視（`unitSys` ≅ Ẑ^×、構造定理）を経た読み。
 - ノート：`pag2_part249_idele_class_density.md`、`pag2_part251_projective_limit.md`。
 
 **1.4 舞台は射影直線 P¹。反転が 0 と ∞ を入れ替える。**
-- 地位：読み（「射影」の読み。構築側が出し、2026-11-18 に著者が留保つきで採用）。P¹(ℤ/N) そのものは［既知］（モジュラー記号の標準の道具）。
-- Lean：
-  - 射影直線と反転：`PAG.Part27.ProjLine`、反転 `PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`（一般の N）。
-  - N = p^K（K ≥ 1）の場合：点モデル `PAG.Part26.Pt` との点集合の全単射 `PAG.Part27.projEquiv`、点の数 `PAG.Part27.card_ProjLine`。
-  - 2 チャートモデル：貼り合わせ条件 `PAG.Part23.Compat`、反転 `PAG.Part23.W`。点モデルの関数との線形同型 `PAG.Part26.ptEquiv`（一般の N）。
-  - Part 19・22・23（PAG23・PAG26・PAG27）。
+- 地位：
+  - 「舞台は P¹」は著者の言葉（2026-11-18 19:01、「射影」の読みの採用のとき）。
+  - 「反転が 0 と ∞ を入れ替える」は構築側の読みで、2026-11-16 に著者が確認した。
+  - P¹(ℤ/N) そのものは［既知］（モジュラー記号の標準の道具）。
+- Lean（Part 19・22・23（PAG23・PAG26・PAG27））：
+  - 射影直線 `PAG.Part27.ProjLine`、反転 [a:b] ↦ [b:a] の定義 `PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`（一般の N）。
+  - N = p^K（K ≥ 1）では、点モデル `PAG.Part26.Pt` との点集合の全単射 `PAG.Part27.projEquiv` と、点の数 `PAG.Part27.card_ProjLine`。
+  - 2 チャートモデルの貼り合わせ条件 `PAG.Part23.Compat` と、その反転 `PAG.Part23.W`。点モデルの関数との線形同型 `PAG.Part26.ptEquiv`（一般の N）。
 - 留保：
+  - 「0 と ∞ は別の点で、反転がこの 2 点を入れ替える」という文は Lean にない（N ≥ 2 で正しい）。
   - N が 2 つ以上の素因数を持つとき、点モデルと P¹(ℤ/N) の点の数は一致しない（数え上げ、Lean の外）。
-  - 有限の側では 0 と ∞ は別の点（N ≥ 2）。
-- ノート：`pag2_projection_material.md`（第 6 版）§3。
+- ノート：`pag2_projection_material.md`（第 6 版）§1・§3。
 
 ## 第 2 章　無限素点の重なりと貼り合わせ
 
 **2.1 重なりは、ねじれた貼り合わせ（境界ユニタリ U）と読む。**
 - 地位：読み（著者の決定、2026-11-12）。
-- 採らなかった読みと理由：
-  - 群の商として読む読みは A1 と両立しない。反例は法 9 の 3 次指標（批判の照合と数値。この反例の Lean の所在は、この索引では確かめていない）。
-  - W による商は A1 と両立するが、D が商に降りない。
+- 採らなかった読み：
+  - 群の商として読む読み：A1 と両立しない。反例は法 9 の 3 次指標で、`pag2_resolution_overlap_materials.md` §3 の表に［批判］［数値］として記録されている。この反例の Lean の所在は、この索引では確かめていない。
+  - W（反転）による商：A1 とは両立するが、D が商に降りない。
 - ノート：`pag2_resolution_overlap_materials.md`、CLAUDE.md §1。
 
-**2.2 モノグラフ層の作用素系（D、T_p、W、二面体関係）、問題 P1、定理 2.6（境界条件 U の両立分類）。**
+**2.2 モノグラフ層の作用素系（D、T_p、反転 W、二面体関係）、問題 P1、定理 2.6（境界条件 U の両立分類）。**
 - 地位：モノグラフ層の記録（著者側、リポジトリにない）。
-- Lean（有限レベル版のみ、Part 249（PAG253））：
+- Lean（有限レベル版だけ。Part 249（PAG253）、［再導出］）：
   - 素数の平行移動と可換なら、すべての単数の平行移動と可換：`PAG.Part253.commute_transl_of_prime`。
   - 指標ごとにスカラー：`PAG.Part253.eigenFun_of_commute_prime`。
   - (a)⇒(b) の完全な形：`PAG.Part253.thm26_full`。
   - 可換性を外した反例：`PAG.Part253.thm26_needs_commute`。
-  - ラベル［再導出］。
 - 留保：
-  - 逆向き (b)⇒(a) は数値のみ。
-  - 大域の Ẑ^× での形は Lean の外。
-  - 証明は Dirichlet の算術級数定理を使わない簡略化。新しい定理ではない。
+  - 逆向き (b)⇒(a) は数値のみ。大域の Ẑ^× での形は Lean の外。
+  - 証明は Dirichlet の算術級数定理を使わない簡略化で、新しい定理ではない。
 - ノート：`pag2_part249_idele_class_density.md`。
 
 **2.3 公準 A1（内容は Tate の定理）と、定理 2.6 との両立。**
-- 地位：A1 は公準（解釈の層の公準、導かれていない）。両立は「既知の結果からの短い帰結」（確信度：高。かつての新規候補 2、2026-11-12 に候補から外れた）。
-- Lean：部品の 3 定理。組み合わせた 1 つの文は形式化していない。
-  - `PAG.Part16.normSq_gaussSum`
-  - `PAG.Part173.gauss_inv_pair`
-  - `PAG.Part198.gauss_sign_real`
-- ノート：`pag2_thm26_A1_collation.md`、CLAUDE.md §3。
+- 地位：
+  - A1 は公準（解釈の層の公準）で、導かれていない。
+  - 両立は「既知の結果からの短い帰結」（確信度：高）。これはかつての新規候補 2 で、2026-11-12 に候補から外れた。
+- 留保：
+  - 両立は、定義から自明な 𝔀(χ̄) = conj 𝔀(χ)（境界ユニタリの実性 KUK = U）から出る。A1 の算術の内容は、どの位相 α を選ぶかの部分だけ（`pag2_thm26_A1_collation.md` §11 の訂正）。
+  - ルート数が条件を満たすことは整合性の確認にすぎず、A1 を導いたことにはならない。
+  - 近い先行：Burnol、Ibort–Lledó–Pérez-Pardo の例 7.1・7.2（CLAUDE.md §3）。
+- Lean：
+  - ガウス和の側の部品の 3 定理（組み合わせた 1 つの文は形式化していない）：`PAG.Part16.normSq_gaussSum`、`PAG.Part173.gauss_inv_pair`、`PAG.Part198.gauss_sign_real`。番号の対応は推定で、PAG16 は Part 12、PAG173 は Part 169、PAG198 は Part 194。
+  - A1 の位相そのものについて（Part 254（PAG258））：
+    - 𝔀(χ⁻¹) = conj 𝔀(χ)（すべての指標）：`PAG.Part258.rootNum_inv`。
+    - 位相についての同じ式：`PAG.Part258.phaseA1_inv`。
+    - 絶対値 1：`PAG.Part258.normSq_phaseA1`。
+    - U_N は複素共役と可換（KUK = U）：`PAG.Part258.UA1_star`。
+    - 内積を保つ：`PAG.Part258.ip_UA1`。
+- ノート：`pag2_thm26_A1_collation.md`、`pag2_part254_full_gluing.md`、CLAUDE.md §3。
 
 **2.4 「射影」の変換と位相：反転（乗法の側）と加法の変換（加法の側）の合成。**
-- 著者の言葉：「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」。
 - 地位：
-  - 読み（2026-11-18、著者が留保つきで採用）。
-  - 「貼り合わせ」が `PAG.Part23.Compat`（ねじれのない座標の貼り合わせ）と U のどちらを指すかは、著者の確認待ち。
-  - 標準の核は Hartley 核（著者の決定）。A1 の内容と揃うことは著者の判断。
+  - 読み（2026-11-18 19:01、著者が留保つきで採用）。
+  - 著者の言葉は「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」。「反転と加法の変換の合成」は構築側の言い換え。
+  - 「貼り合わせ」が `PAG.Part23.Compat`（ねじれのない座標の貼り合わせ）と U のどちらを指すかは、著者の確認待ち（構築側の読みは U）。
+  - 標準の核は Hartley 核（著者の決定）。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは照合していない（JH_N の正規化も本文で確かめていない）。
 - Lean（Part 252（PAG256）、［再導出］）：
-  - 写像 `PAG.Part256.JH`、値 `PAG.Part256.rootNum`、偶奇の因子 `PAG.Part256.parFac`。
-  - すべての指標で単数の上の式：`PAG.Part256.JH_eq_rootNum_mul_any`。
+  - 写像 `PAG.Part256.JH`、値 `PAG.Part256.rootNum`（= 𝔀）、偶奇の因子 `PAG.Part256.parFac`。
+  - すべての指標で、単数の上の式：`PAG.Part256.JH_eq_rootNum_mul_any`。
   - 原始指標で絶対値 1：`PAG.Part256.normSq_rootNum`。
   - 原始指標で単数の外に漏れない：`PAG.Part256.hartley_eq_zero_of_not_isUnit`。
   - 原始性を外した反例：`PAG.Part256.removal_counterexample`・`PAG.Part256.removal_counterexample_normSq`・`PAG.Part256.removal_counterexample_four`。
 - 留保：
   - `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。P¹ のモデルと結ぶ Lean の文はない。
-  - 原始指標で `rootNum` がルート数であることは Lean の外。
-  - 素朴なフーリエ核 e(xy) では τ(χ)/√N で、奇の指標で i 倍ずれる（滑らかにしない）。
+  - 原始指標で 𝔀 がルート数であることは Lean の外。
+  - 素朴なフーリエ核 e(xy) では値が τ(χ)/√N で、奇の指標で i 倍ずれる。このずれは滑らかにしない。
 - ノート：`pag2_part252_hartley_gluing.md`、`pag2_projection_material.md`、`pag2_prereg_projection.md`。
 
 **2.5 原始部分の作用素 T とユニタリ性。**
 - 地位：定理［再導出］（Part 253（PAG257））。
 - Lean：
-  - すべての指標で T χ = W(χ)χ：`PAG.Part257.TopL_charU`。
+  - すべての指標で T χ = 𝔀(χ)χ：`PAG.Part257.TopL_charU`。
   - 原始部分の上でユニタリ：`PAG.Part257.unitary_Vprim`。
   - 原始指標で A1 の位相を課した任意の線形写像は、原始部分の上で T と同じ値をとる：`PAG.Part257.TopL_eq_of_A1`（ほぼ同語反復）。
-- 留保：U は Lean で定義していない（仮定の形でだけ現れる）。
+- 留保：Part 253 では U を Lean で定義していない（仮定の形でだけ現れる）。U_N の定義は 2.6。
 - ノート：`pag2_part253_primitive_operator.md`。
 
 **2.6 法 N の境界ユニタリ U_N 全体と、代数的な帰納極限の上の U_∞。**
 - 地位：定理［再導出］（Part 254（PAG258））。
 - Lean：
-  - 位相 `PAG.Part258.phaseA1`、U_N `PAG.Part258.UA1`。
-  - 導手ごとの部分 `PAG.Part258.condPart_eq_map`。
-  - 族の一意性 `PAG.Part258.UA1_family_unique`。
-  - 極限の上の作用素 `PAG.Part258.Uinf`、その一意性 `PAG.Part258.Uinf_unique`、内積の保存 `PAG.Part258.ipLim_Uinf`。
+  - 位相 `PAG.Part258.phaseA1` と U_N `PAG.Part258.UA1`。
+  - 導手ごとの部分：`PAG.Part258.condPart_eq_map`。
+  - 族の一意性：`PAG.Part258.UA1_family_unique`。
+  - 帰納極限 `PAG.Part258.Lim`、その上の作用素 `PAG.Part258.Uinf`、一意性 `PAG.Part258.Uinf_unique`、内積の保存 `PAG.Part258.ipLim_Uinf`。
 - 留保：
   - U_N は A1 の位相を定義として入れた作用素で、A1 は導かれていない。
   - 直和を 1 つの文にした定理はない。
-  - 完備化 L²(Ẑ^×) は Lean の外（読みとしては、解像度が落ちる側の操作）。
+  - `Lim` と Ẑ^× の上の局所定数関数との同一視、完備化 L²(Ẑ^×) は Lean の外。完備化は、読みとしては解像度が落ちる側の操作。
 - ノート：`pag2_part254_full_gluing.md`。
 
-**2.7 位相の、全素点の局所因子の積への分解（値のレベル）。**
-- 地位：定理［既知（再導出）］（Part 256（PAG260）・Part 257（PAG261））。
+**2.7 τ と 𝔀 の、互いに素な法の成分・素数冪の成分による分解（交差項・符号つき。値のレベル）。**
+- 地位：定理［既知（再導出）］（Part 256（PAG260）・Part 257（PAG261））。恒等式は原始性を使わない（原始的でない指標では 𝔀 は位相でない）。
 - Lean：
   - 互いに素な 2 つの法：`PAG.Part260.rootNum_prodChar`・`PAG.Part260.parFac_prodChar`・`PAG.Part260.crossSign`。
   - 互いに素な法の並び：`PAG.Part261.rootNum_listChar_formII`・`PAG.Part261.parFac_listChar`。
-  - すべての素数への分解：`PAG.Part261.gaussSum_primeFactors`。
-- Lean の外（値の一致、規約 T を明示）：形 (II) の素数ごとの因子は Tate の局所定数に、`parFac` は無限素点の局所定数 (−i)^a に一致する（原始指標、s = 1/2）。Part 257 の読み（確信度：中〜高）を、2026-11-18 の文献照合で確かめ直した。
+  - 成分への分解とその一意性：`PAG.Part261.exists_listChar`・`PAG.Part261.listChar_injective`（並びの形で言う。法 n の形での一意性は文にしていない）。
+  - すべての素数への τ の分解：`PAG.Part261.gaussSum_primeFactors`（τ の文で、𝔀 の文ではない）。
+- Lean の外：
+  - 原始指標で s = 1/2 のとき、形 (II) の素数ごとの因子は Tate の局所定数と、`parFac` は無限素点の局所定数 (−i)^a と値が一致する（読み）。
+  - この一致には、加法指標の規約 T と、イデール類指標の正規化 ω_q(q) = χ(q) の両方が要る。ω を χ̄ に対応させる規約では、積は 𝔀 の共役になる。
+  - Part 257 で読みとして記録した（確信度：中〜高）ものを、2026-11-18 の文献照合で確かめ直した。
+  - 「局所因子」という語は読み。
 - ノート：`pag2_part256_gluing_cross_term.md`、`pag2_part257_local_factor_decomposition.md`、`pag2_literature_ia_sign.md`。
 
 **2.8 加法指標の規約は規約 T（Tate の学位論文の加法指標：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）。**
-- 地位：著者の決定（2026-11-18 19:25）。基礎文書の標準。
+- 地位：著者の決定（2026-11-18 19:25）。基礎文書の標準とする。
 - 書き方の規則：
   - 明示的な因子 i^{±a} が無限素点の局所定数であることは、規約によらない。
   - 符号 χ(−1) の置き場は規約による。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
+  - 局所定数との一致を書くときは、イデール類指標の正規化（2.7）も併記する。
 - ノート：`pag2_literature_ia_sign.md`、CLAUDE.md §1。
 
 ## 第 3 章　解像度と有効な姿（§1 の命題 3）
 
 **3.1 定義文と、その置き方と読み。**
-- 地位と出所：
-  - 定義文：直線は解像度を落としたときに創発する有効な姿。解像度のパラメータは未決定（著者の文面）。
+- 地位：
+  - 定義文（著者の文面）：直線は解像度を落としたときに創発する有効な姿。解像度のパラメータは未決定。
   - 置き方（2026-11-13）：見方の選択として解釈の層に置く（著者側 Muse の決定）。
-  - 08:41 の定義（著者の原文）：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。…極限でも離散構造の観測を維持します。」
-  - 読み L1（著者が採った読み、構築側の案）：解像度は測る素点の集合。
+  - 08:41 の定義（2026-11-13、著者の原文）：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。」
+  - 読み L1（2026-11-13 08:38 に著者が採った読み。構築側の案）：解像度は測る素点の集合。
 - Lean：なし（数学の文ではない）。
-- 書き方の規則：解像度を N・K・Λ と同一視しない。閉包・完備化の連続体を目標として書かない。「直線の創発」と書かない。
+- 書き方の規則（CLAUDE.md §1）：
+  - 解像度を N・K・Λ と同一視しない。
+  - 閉包・完備化に現れる連続体を「有効な姿」や目標として書かない。
+  - 完備化（L²、ℝ、直積の位相）を使うときは、「解像度が落ちる側の操作と読む」と読みとして断る。極限は直極限の側（すべての素点を同時に測る側）で取る。
+  - 「直線の創発」と書かない。命題 3 には「§1 の命題 3（解像度と有効な姿）」と参照で触れ、何がどう変わるかを数学の言葉で書く。
 - ノート：`pag2_author_definition_0841.md`、`pag2_part255_resolution_discrete_limit.md`、CLAUDE.md §1。
 
 **3.2 Part 250 の試み（ε-鎖による定式化）。**
-- 地位：定理［既知］（教科書の例の対数座標版）と、否定的な結果。
+- 地位：
+  - 定式化は Claude の案 1・2 を、著者が 2026-11-11 に了承したもの（著者の定義そのものではない）。
+  - 定理は［既知］（教科書の例の対数座標版）。否定的な結果を含む。
 - Lean（Part 250（PAG254））：
   - 定義 `PAG.Part254.chainIn`。
-  - ∞ の側はどの ε でも鎖でつながる：`PAG.Part254.chainIn_dInf`。p の側はつながらない：`PAG.Part254.not_forall_chainIn_dP`。
+  - ∞ の側は、どの ε > 0 でも任意の 2 点が鎖でつながる：`PAG.Part254.chainIn_dInf`。
+  - p の側では「どの ε > 0 でもすべての 2 点がつながる」が成り立たない：`PAG.Part254.not_forall_chainIn_dP`。ε > 1 ではすべてつながる（ノートの記載）。
   - 稠密性 `PAG.Part254.dense_logSet`、等長性 `PAG.Part254.dInf_eq_dist`。
-- 否定的な結果：「解像度を落とすと直線が現れる」は示せていない。ε-鎖の商は 1 点につぶれ、ℝ は完備化から現れ、しかも ℝ は定義に使われている。
-- ノート：`pag2_part250_resolution_emergence.md`。
+- 否定的な結果：
+  - 「解像度を落とすと直線が現れる」は示せていない。ε-鎖の商は 1 点につぶれ、ℝ は完備化から現れ、しかも ℝ は定義に使われている。ε-鎖の商は Lean にしていない。
+  - 08:41 の定義の後（Part 255）、完備化は「解像度が落ちる側」の操作と読み、Part 250 の照合の記録にあった向きの判断は取り下げた。
+- ノート：`pag2_part250_resolution_emergence.md`、`pag2_part255_resolution_discrete_limit.md`。
 
 ## 第 4 章　解像度ごとの姿（設計についての定理 1）
 
 **4.1 Part 255 の二分法：測る素点と、像の離散・稠密。**
-- 地位：定理［既知（再導出）］（S 単数定理・積公式・弱近似の ℚ の場合）。
+- 地位：定理［既知（再導出）］。骨格は、証明の部品が S 単数定理・積公式・弱近似（既知）であることを明記するとしている。
 - Lean（Part 255（PAG259））：
   - 有限の基礎 ⟨S⟩（S は素数の有限集合、T ⊆ S）での閾値：`PAG.Part259.threshold_iff`。
   - 測らない素数が 2 つ以上なら稠密：`PAG.Part259.dense_imgST_iff`。高々 1 つなら閉かつ離散：`PAG.Part259.isClosed_discrete_imgST`。
-  - すべての素点を同時に測る位相では、像は閉かつ離散：`PAG.Part259.isClosed_discrete_rhoBox_image`（座標 `PAG.Part259.BoxCoord`、写像 `PAG.Part259.rhoBox`）。照合 A の評価では、位相の選び方でほぼ決まる文。
+  - 位相の対比：
+    - 直積の位相では、すべての素点の座標への像は稠密：`PAG.Part259.dense_rho_image`。
+    - 有限素点の座標 `PAG.Part259.BoxCoord`（`Nat.Primes → ℤ`）に離散位相を入れると、像は閉かつ離散：`PAG.Part259.isClosed_discrete_rhoBox_image`（写像 `PAG.Part259.rhoBox`）。
+    - 「すべての素点を同時に測る位相」は読み。log の成分は使わない。再照合 A2 の判定は「自明（位相の選び方でほぼ決まり、ほぼ同語反復に近い。確信度：高）」。
+  - 対照群の自明な Lean 版：通約的な 2 つの対数の整数結合は離れる：`PAG.Part259.sep_of_commensurable`。
 - 留保：
-  - 二分法を 1 つの文にはしていない。
-  - 閉包に現れる直線は、読みとしては解像度が落ちた印（08:41 の定義）。その直線が無限素点の座標であること、および対照群 𝔽_q(t) で直線が現れないことは、骨格の記述で Lean の外。
+  - 守備範囲：ℚ_{>0} を基礎にすると、∞ を測るどの有限の解像度でも像は稠密になる。離散の側は、有限の基礎 ⟨S⟩ でだけ起こる。
+  - 二分法を 1 つの文にはしていない。直極限の位相と `BoxCoord` の同一視は Lean の外。
+  - 閉包に現れる直線は、読みとしては解像度が落ちた印（08:41 の定義）。その直線が無限素点の座標であること、および対照群 𝔽_q(t) で直線が現れないこと（ノルムの像は q^ℤ）は、骨格の記述で、Lean の外。
 - ノート：`pag2_part255_resolution_discrete_limit.md`。
 
 ## 第 5 章　有限レベルの代数の組み立て（設計についての定理 2）
 
-**5.1 Part 258 の二分法：殻代数の写像は互いに素な段でだけある。**
+**5.1 Part 258 の二分法：N ∣ M のとき、(i) 引き戻しと両立し、(ii) 殻を混ぜない（強い読み）単位的な代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、そのときに限る。**
 - 地位：定理。
-  - 存在の側（テンソル積）：［既知］（Hanaki–Kim–Maekawa の直積の定理）。
-  - 不存在の側：［新規候補（小さい）］（確信度：低〜中。2026-11-15 の著者側の判断）。
+  - 存在の側（テンソル積）は［既知］（Hanaki–Kim–Maekawa の直積の定理。構築側は文献を開いていない。確信度：中〜高）。
+  - 不存在の側は［新規候補（小さい）］（確信度：低〜中。2026-11-15 の著者側の判断）。
 - Lean（Part 258（PAG262））：
   - 二分法：`PAG.Part262.exists_compatible_hom_iff`。
-  - 存在 `PAG.Part262.exists_compatible_hom`、写像 `PAG.Part262.shellLift`。
-  - 不存在 `PAG.Part262.no_compatible_hom`。
+  - 存在 `PAG.Part262.exists_compatible_hom`、その写像 `PAG.Part262.shellLift`。
+  - 不存在：`PAG.Part262.no_compatible_hom`。
 - 留保：
-  - 条件 (iii)（殻を混ぜない）を強い読みにしたのは構築側で、著者に確かめる事項。
-  - 文献照合（MathSciNet・zbMATH、Hanaki–Kim–Maekawa と Bastian–Humphries の本文）が済むまで、外部で新規性として使わない。
+  - 条件の番号に注意。殻を混ぜない条件は、PAG262 の docstring・Part 259・CLAUDE.md §2 の番号では (ii)、Part 258 のノートでは (3)。強い読みは、Part 258 のノートでは「構築者の読みで、著者に確かめる事項」。CLAUDE.md §2 は「登録の読み」と書いている。
+  - 答えの範囲の外：弱い読み、単位元を保たない写像、両立条件を別の形にした写像。
+  - 対照群（盲検の申告で、未確認）の結果から、アーデル射影幾何に固有の内容としては数えない（Part 258 のノート）。
+  - 文献照合（MathSciNet・zbMATH と、Hanaki–Kim–Maekawa・Bastian–Humphries の本文）が済むまで、外部で新規性として使わない。
 - ノート：`pag2_part258_beta_premise.md`、CLAUDE.md §3。
 
 **5.2 Part 259：フーリエとの両立を足した一意性と、帰納系の添字。**
 - 地位：定理。
-  - 順序の性質：［既知］（ユニタリ約数、E. Cohen 1960）。
-  - 一意性・非一意性・帰納系：［再導出（小さい）］。
+  - 順序の性質は［既知］（ユニタリ約数、E. Cohen 1960）。
+  - 一意性・非一意性・帰納系は［再導出（小さい）］。
 - Lean（Part 259（PAG263））：
-  - 一意な存在の二分法 `PAG.Part263.existsUnique_compatF_iff`、その写像の特定 `PAG.Part263.compatF_iff_eq_shellLift`。
-  - (iii) を外すと一意でない：`PAG.Part263.not_existsUnique_compat`（捩れた写像 `PAG.Part263.twLift`）。
-  - 合成との両立 `PAG.Part263.canon_comp`。
-  - 添字 `PAG.Part263.UDvd` は有向でない：`PAG.Part263.not_isDirected_udvd`。
-  - 無平方数の部分系の極限 `PAG.Part263.sqLim`、各段は単射で入る：`PAG.Part263.sqLim_of_injective`。
-- 留保：
-  - 奇数の場合の一意性は数値のみ。
-  - `sqLim` の代数構造と、制限テンソル積との同型は Lean の外。
-  - gcd ≠ 1 で (i) と D の側だけを満たす写像の不存在は、数値の見込みのみ。
+  - (i)(ii)(iii)（(iii) はフーリエとの両立）を満たす写像がちょうど 1 つある ⇔ gcd(N, M/N) = 1：`PAG.Part263.existsUnique_compatF_iff`。その写像の特定：`PAG.Part263.compatF_iff_eq_shellLift`。
+  - (iii) を外すと一意でない場合がある：`PAG.Part263.not_existsUnique_compat`。Lean にあるのは、A_2 → A_{2b}（b > 1 は奇数）で捩れた写像 `PAG.Part263.twLift` がある場合だけ。
+  - 標準の写像 `PAG.Part263.canon` は合成と両立する：`PAG.Part263.canon_comp`。
+  - 添字の関係 `PAG.Part263.UDvd` は有向でない：`PAG.Part263.not_isDirected_udvd`。これは Part 216（PAG220）の `PAG.Part220.InLayer` と同じ概念。
+  - 無平方数の部分系の極限 `PAG.Part263.sqLim`。各段は単射で入る：`PAG.Part263.sqLim_of_injective`。
+- 留保（Part 259 §2 の「併記する必要がある 3 点」と、その他）：
+  - 無平方数の系は、極大な有向部分系のうち指数がすべて 1 の場合にすぎず、A_{p^k}（k ≥ 2）を含まない。
+  - `sqLim` は ℂ 加群で、代数の構造と制限テンソル積との同型は Lean の外。
+  - どの有向な部分系も、整除の順序で共終でない。したがって関数のレベルの極限 ℂ[ℚ/ℤ]（5.3）の代数版にはならない（初等的。Lean にしていない）。
+  - a が奇数のときの一意性は、数値のみ。
+  - gcd ≠ 1 で (i) と D の側だけを満たす写像があるかは、未確認（小さい数値では見つからなかった。証明ではない）。
 - ノート：`pag2_part259_unitary_step_maps.md`、`pag2_R1_assessment.md`。
 
 **5.3 関数のレベルの帰納系。**
-- 地位：定理［再導出］。
+- 地位：定理（Lean）。ラベルは、この索引では確かめていない。
 - Lean：
-  - Part 197（PAG201）：引き戻し `PAG.Part201.pull`、ハール正規化の保存 `PAG.Part201.zket_pull`、法によらない定理 A `PAG.Part201.thmA_haar`。
-  - Part 202（PAG206）：引き戻しのフーリエ変換 `PAG.Part206.dft_pull_apply`、旧部分 = 引き戻しの像 `PAG.Part206.oldP_eq_self_iff`。
-- 留保：極限 ℂ[ℚ/ℤ] との同一視は、この索引では Lean の文を確かめていない（骨格の記述）。
+  - Part 197（PAG201）：
+    - 引き戻し `PAG.Part201.pull`。
+    - ハール正規化の保存 `PAG.Part201.zket_pull`（仮定：t の素因数がすべて M を割る）。
+    - 法によらない定理 A `PAG.Part201.thmA_haar`（仮定：N の素因数がすべて d を割る。原始性）。
+  - Part 202（PAG206）：
+    - 引き戻しのフーリエ変換 `PAG.Part206.dft_pull_apply`。
+    - 旧部分 = 引き戻しの像 `PAG.Part206.oldP_eq_self_iff`。
+  - 単数の上の関数の帰納極限 `PAG.Part258.Lim`（2.6）。
+- 留保：
+  - 極限 ℂ[ℚ/ℤ] との同一視は骨格の記述で、この索引では Lean の文を確かめていない。
+  - 「Ẑ 上の定理 A」は、CLAUDE.md §0 で未完の大域の問いに数えられている。
 - ノート：引き継ぎメモの項目 18・23。
 
 **5.4 互いに素な段のテンソル積。**
 - 地位：定理［既知］（直積スキームの一般定理 T(A×B) ≅ T(A)⊗T(B) の特別な場合）。
 - Lean：
   - Part 228（PAG232）：`PAG.Part232.shellAlgTensorEquiv`、`PAG.Part232.leftHom`、`PAG.Part232.tensLift_injective`、`PAG.Part232.range_tensLift`。
-  - Part 236（PAG240）：局所作用素 `PAG.Part240.locHom`、`PAG.Part240.tensEquiv`。
+  - Part 236（PAG240）：
+    - 局所作用素 `PAG.Part240.locHom`。
+    - 一般の族の文 `PAG.Part240.tensEquiv`（A_N に当てるには `PAG.Part240.crtMul_shellAlg`）。
+    - 素数冪への分解 `PAG.Part240.ppEquiv`。
+- 留保：Part 258 の `shellLift` の作用素は、`locHom` の k = 0 と同じ式（Lean ではつないでいない。第 12 の型）。
 - ノート：引き継ぎメモの項目 49・57、CLAUDE.md §3。
 
 ## 第 6 章　位置づけ
 
 **6.1 殻代数 A_N は Terwilliger 代数 T(0) そのもの。**
-- 地位：［既知］（2026-11-07 の著者の定義照合）。
-- Lean：定義 `PAG.Part218.shellAlg`（Part 214（PAG218））。
+- 地位：［既知］（2026-11-07 の著者の定義照合）。定義からの等式で、T(0) を Lean で定義していないので Lean の定理ではない。
+- Lean：A_N の定義 `PAG.Part218.shellAlg`（Part 214（PAG218））。
 - 既知として扱う結果：
-  - 素数冪の Wedderburn 分解と次元公式（Part 225–226）。
-  - テンソル積分解（Part 228）。
-  - ⟨D_u, E_N⟩ の構造とフーリエ共役（Part 241–242、確信度：中）。
+  - 素数冪の Wedderburn 分解と次元公式：Part 225–226（PAG229–PAG230）。
+  - テンソル積分解：Part 228（PAG232）。
+  - ⟨D_u, E_N⟩ の構造とフーリエ共役：Part 241–242（PAG245–PAG246）、確信度：中。
 - 書き方の規則：構造が要るときは再証明せず、辞書経由で文献を引く。
 - ノート：`pag2_terwilliger_dictionary.md`、CLAUDE.md §3。
 
 **6.2 新規性の候補（未確定。断定しない）。**
-- 候補 1：生成の分類（Part 246–248。主定理 `PAG.Part252.addEAlg_eq_shellAlg_iff_all`）。
-  - 範囲：合成数の N（確信度：中）。評価は「小さいノートの水準」。
-  - MathSciNet・zbMATH は未実施。
-  - ノート：`pag2_candidate1_generation_collation.md`。
-- 候補 3：Part 258 の不存在の側（5.1）。文献照合は著者側の作業。
+- 候補 1：生成の分類。
+  - CLAUDE.md §3 は Part 246–248 と書くが、項目 66 の宣言は PAG249（Part 245）にあるので、範囲は Part 245〜248（PAG249〜PAG252）と読める。
+  - 項目 66：`PAG.Part249.sumSub_eq_shellAlg_iff`。項目 68：`PAG.Part251.addEAlg_one_eq_shellAlg_iff`。完全な分類：`PAG.Part252.addEAlg_eq_shellAlg_iff_all`。
+  - 新規候補として残る範囲は合成数の N（確信度：中）。評価は「小さいノートの水準」。
+  - MathSciNet・zbMATH は未実施。ノートの言葉では「著者側か専門家への照会」をお願いしている。
+  - ノート：`pag2_candidate1_generation_collation.md`、CLAUDE.md §3。
+- 候補 3：Part 258 の不存在の側（5.1）。骨格は、その文献照合（MathSciNet・zbMATH）を著者自身の作業としている。
 - かつての候補 2（定理 2.6 の提示形）は候補から外れた（2.3）。
 
 **6.3 Bost–Connes との接続。**
-- 地位：
-  - 関数のレベルでは既知。
-  - T(0) の側に届くかは、方向 γ の文献照合（著者側の作業）による。
-- ノート：CLAUDE.md §2・§3。
+- 地位（骨格の記述）：関数のレベルでは既知。T(0) の側に届くかは、方向 γ の文献照合の結果による。γ の文献照合は著者側の作業（CLAUDE.md §2）。
+- CLAUDE.md §2 には、有限レベル Bost–Connes に元の BC 系が対応する、という記載がある。
+- ノート：CLAUDE.md §2。
 
 **6.4 書かないこと。**
-- リーマン予想へのアプローチ。
-- A1 の導出。
-- 数値確認を証明と呼ぶこと。
-- 「直線の創発」という表現。
-- 既知の結果を新規と書くこと（CLAUDE.md §6）。
+- CLAUDE.md §6 から：
+  - リーマン予想へのアプローチと書くこと（スペクトルと零点の数え上げの不一致は確定事項）。
+  - 既知の結果を新規と書くこと。
+  - 著者の定義を、形式化済みの内容であるかのように書くこと。
+  - A1 の導出。
+  - 数値確認を証明と呼ぶこと。
+- CLAUDE.md §1 から（2026-11-12 の著者の指示）：「直線の創発」という表現。
 
 ## §6 開いている点（文書に「開いている」と書くもの）
 
-- **著者の確認待ち**
+- **著者の確認待ち**：
   - 「貼り合わせの合成」の貼り合わせは、`Compat` と U のどちらか（2.4）。
-  - Part 258 の条件 (iii) の強い読み（5.1）。
-- **著者側の作業**
+  - Part 258 の殻を混ぜない条件の強い読み（5.1）。
+- **著者側の作業**（担当は骨格と CLAUDE.md §2 の記載による）：
   - 方向 γ の文献照合（6.3）。
   - 候補 3 の文献照合（5.1）。
-  - 候補 1 の MathSciNet・zbMATH（6.2）。
-- **Lean の外・数値のみで残るもの**
+  - 候補 1 の MathSciNet・zbMATH（6.2。ノートの言葉では「著者側か専門家への照会」）。
+- **Lean の外・数値のみで残るもの**：
   - 構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0}（1.2・1.3）。
   - 定理 2.6 の逆向き（2.2）。
   - A1 と定理 2.6 の両立を 1 つにした文（2.3）。
-  - 完備化 L²(Ẑ^×)（2.6）。
+  - `Lim` の同一視と完備化 L²(Ẑ^×)（2.6）。
   - 局所定数との同定（2.7）。
   - 二分法の 1 つの文（4.1）。
   - `sqLim` の代数構造（5.2）。
-  - 奇数の場合の一意性（5.2）。
-  - (i) と D の側だけでの不存在（5.2）。
-- **定式化の問い**
-  - 解像度の操作に、L1 を超える定式化が要るか（現時点では、L1 と 08:41 の定義で文書は書ける）。
-  - 「射影」の、全素点を通した一つの構成（空間と作用素のレベル）としての定式化（値のレベルでは 2.7）。
+  - a が奇数のときの一意性（5.2）。
+  - (i) と D の側だけを満たす写像の有無（5.2）。
+- **定式化の問い**：
+  - 解像度の操作に、L1 を超える定式化が要るか。骨格の記述では、現時点では L1 と 08:41 の定義で文書は書ける。
+  - 「射影」の、全素点を通した一つの構成（空間と作用素のレベル）としての定式化。値のレベルについては 2.7。
 
 ## §7 宣言名の確認の記録
 
-- この索引に出る完全修飾名を機械的に取り出し、`PAG.PartM.name` ごとに PAGM.lean の `theorem`・`def`・`abbrev`・`structure`・`instance` などの宣言の行を検索した（スクリプト `records/founding_index/check_names.py`、出力 `check_names.log`）。
-- 地位とラベルは各ノートと CLAUDE.md の記載を写した。写し間違いと強めすぎは、独立照合で確かめる（§8）。
+- この索引に出る完全修飾名を機械的に取り出し、`PAG.PartM.name` ごとに PAGM.lean の宣言の行（`theorem`・`def`・`abbrev`・`structure`・`instance` など）を検索した。
+  - スクリプトは `records/founding_index/check_names.py`、出力は `check_names.log`。
+  - 第 1 版は 85 件、第 2 版は照合者の指摘で足したものを含めて 102 件で、すべて実在した。
+- 「Part n（PAGm）」の併記がすべて m = n + 4 であることも、機械的に確かめた。
+- 照合者に渡した宣言の docstring と形式文の抜き出しには、`records/founding_index/extract_decls.py` を使った。
 
 ## §8 照合の記録
 
-（独立照合の後に記録する。）
+- **第 1 回の独立照合**：
+  - 第 1 版（`records/founding_index/before_index_v1.md`）を照合者 1 人に渡した。渡したのは、索引の全文、宣言の docstring と形式文（85 件）、引くノートの冒頭（各 45 行）、引き継ぎメモの該当項目、CLAUDE.md の全文。
+  - 入力は `input_index.md`、依頼文は `request.md`、出力は `outputs/index_check_output.md`。所要は約 11 分。
+- **結論**：宣言名はすべて実在した。指摘は次のとおり。
+  - 形式文より強い見出し・文：10 件。
+  - 地位・決定者・出所の違い：10 件。
+  - 落としていた留保：14 件。
+  - 宣言の当て方：8 件。
+  - 番号・参照の誤り：8 件。最も重いのは、5.1 の「条件 (iii)」で、正しくは (ii)。
+- **第 2 版で直したこと**：
+  - 見出しを形式文の範囲に合わせた（1.3、2.7、3.2、4.1、5.1、5.2）。
+  - 記号 W と 𝔀 の注意を §0 に加えた。
+  - 3.1 の規則を CLAUDE.md の文言どおりにし、08:41 の原文を全文で載せた。
+  - 宣言を足した（2.3 の A1 の位相の側、2.7 の成分の一意性、4.1 の `dense_rho_image`・`sep_of_commensurable`、5.4 の `crtMul_shellAlg`・`ppEquiv`、6.2 の項目 66・68、5.3 の `Lim`）。
+  - 出所を書き分けた。骨格の記述（4.1 の部品、6.3、候補 3 の担当、「文書は書ける」）は骨格と明記した。決定者と時刻も直した（1.4、3.2）。
+  - 留保を足した（2.3 の実性への帰着と近い先行、2.4 の未照合、2.6 の `Lim`、2.7 の ω の正規化、4.1 の守備範囲、5.1 の範囲の外と対照群、5.2 の 3 点、6.1 は Lean の定理ではないこと）。
+  - 番号の併記と参照を直した（6.1・6.2、6.3 は §2 だけ、6.4 の出所）。
+- **第 2 版の照合**：第 2 版は照合後の直しを照合にかけていない。直しは照合者の直し案に沿った狭め・書き分け・出所の明記と、足した宣言（実在は機械的に確認、§7）である。足した宣言の形式文は、照合者が「§B になく未確認」としたものを構築側が読んで当てた。たとえば `rootNum_inv`・`phaseA1_inv`・`UA1_star` の形式文は PAG258 の 363〜412 行で確かめた。次の統合照合の対象に含める。
```

### A2 前回の統合照合（コミット 3522ff7 の状態を照らした）の後の変更：材料ノート・文献照合ノート・CLAUDE.md・CLAUDE.en.md・概要の日英・引き継ぎメモ
```diff
diff --git a/CLAUDE.en.md b/CLAUDE.en.md
index 2acd915..cd6a496 100644
--- a/CLAUDE.en.md
+++ b/CLAUDE.en.md
@@ -25,7 +25,7 @@ The purpose of this procedure is not to avoid mapping to existing mathematics. T
   - A line is an effective appearance that emerges when the resolution is lowered.
   - However, the parameter that determines the resolution is **undecided**. Do not arbitrarily identify it with any of $N$, $K$ or $\Lambda$.
   - Placement of Proposition 3 (2026-11-13; recorded as a decision of the author-side Muse, to whom the choice was delegated by the author; the author can overturn it at any time): the wording of the definitions above is not changed. The mathematical place of the operation of resolution is put in the interpretive layer, not as "a transition within the object (a change from discrete to continuous)" but as **a choice of a way of cutting (a view)** of the global object. That is, the object is the whole in which the places coexist in parallel from the start as the factors of a restricted product; the finite-level quotients and the $\Lambda$-cutoff (the two axes separated in A8) are views of that whole; and the question of emergence is read as "how does a line look when the view is made coarser". The prohibition on identifying the resolution with $N$ or $\Lambda$ is maintained as before (what was decided is where the question is placed, not the parameter). Later, on 2026-11-14, the original text of the author's 08:41 definition reached the author side through the construction side's handoff memo (`PAG2_handoff_part257.md`): "Escaping into the completion (limit) and sliding into the continuum is what I call the resolution dropping. I do not wish for the continuum to be observed; I maintain the observation of the discrete structure even in the limit." This definition does not contradict the placement above — the operation on the side where the resolution drops is sliding into the completion, the stance is maintaining the observation of the discrete structure even in the limit, and the limit is taken on the side of the direct limit (the side where all places are measured at once). When using completions ($L^2$, $\mathbb{R}$, the product topology), state as a reading that they are "read as operations on the side where the resolution drops". Do not write the continuum appearing in closures or completions as the "effective appearance" or as a goal. Also, on 2026-11-13 at 08:38 the author adopted, on the construction side, L1 (resolution = the set of places measured) as the reading of Proposition 3 (L1 is a proposal adopted as a reading, not the wording of the definition itself; it is not identified with any of $N$, $K$ or $\Lambda$). By the author's instruction (2026-11-12), the expression 「直線の創発」 ("emergence of the line") is not used (when touching on Proposition 3, refer to it as "Proposition 3 of §1 (resolution and effective appearance)" and write in mathematical language what changes and how).
-  - Reading of "projection" (2026-11-18, adopted with reservations by the author; interpretive layer, not a formalized theorem): the meaning of the name is "fusing adelic geometry and idelic geometry by projection" (2026-11-16, the author). The "projection" in the name refers to the pair of a stage and a transform, with the transform as the main sense. The stage is the projective line P¹ (inversion swaps 0 and ∞; at the finite level, Parts 19–28 (PAG23–PAG32)), and the composition, acting on it, of inversion (the multiplicative side) and an additive transform (the additive side) is called the projection (at the finite level, $J\circ H_N/\sqrt N$ of Part 252 (PAG256)). Its components on primitive characters are the phases. The standard kernel is the Hartley kernel of Part 252 (ratifying the formalization; consistent with the content of A1). The value is $\tau(\chi)/(i^a\sqrt N)$ (`PAG.Part256.rootNum`; the symbol W(χ) in the PAG256 docstrings denotes this value and is distinct from the inversion $W$); for primitive characters it is the root number, but that identification is outside Lean (state this explicitly). It differs from the value $\tau(\chi)/\sqrt N$ of the plain Fourier kernel $e(xy)$ by a factor $i$ for odd characters; do not smooth over this discrepancy. The convention for the additive character is convention T (the additive character of Tate's thesis: $\psi_\infty(x) = e^{-2\pi i x}$, $\psi_p(x) = e^{+2\pi i\{x\}_p}$), which is the standard for the foundational document (2026-11-18, the author's decision; its sign at the finite places agrees with Mathlib's `stdAddChar`, and it is the same convention as Burnol's). Under convention T, the factor $\varepsilon(\chi) = (-i)^a$ of the Hartley kernel (`PAG.Part256.parFac`) agrees with the local constant $\varepsilon(1/2, \chi_\infty, \psi_\infty)$ at the infinite place, and $\tau(\chi)/\sqrt N$ agrees with the product of the local constants at the finite places (an agreement of values, outside Lean; local constants are defined in the style of Tate 1979; literature check of 2026-11-18, `notes/pag2_literature_ia_sign.md`, one independent check. Following it, the treatment of $i^a$ as a reserved normalization factor was lifted on the same day). That the power of $i$ comes from the infinite place does not depend on the convention, but whether the sign $\chi(-1)$ is placed at the infinite place or at the finite places does (in the opposite convention the infinite place gives $i^a$ and the product over the finite places is $\chi(-1)\tau(\chi)/\sqrt N$). Therefore, do not write "$\varepsilon(\chi)$ comes from the infinite place" without stating convention T. A1 remains a postulate. The material is in `notes/pag2_projection_material.md`.
+  - Reading of "projection" (2026-11-18, adopted with reservations by the author; interpretive layer, not a formalized theorem): the meaning of the name is "fusing adelic geometry and idelic geometry by projection" (2026-11-16, the author). The "projection" in the name refers to the pair of a stage and a transform, with the transform as the main sense. In the author's words: "the stage is P¹, and the composition of gluings acting on it is called the projection". The stage is the projective line P¹ (inversion swaps 0 and ∞; at the finite level, Parts 19–28 (PAG23–PAG32)). In the construction side's reading, that composition is the composition of inversion (the multiplicative side) and an additive transform (the additive side), which at the finite level corresponds to $J\circ H_N/\sqrt N$ of Part 252 (PAG256) (`PAG.Part256.JH`). However, `JH` is a map sending functions on $\mathbb Z/N$ to functions on the units; it is not an operator on P¹, and no Lean statement links `JH` to the models of P¹. Whether "gluing" refers to `Compat` of PAG23 (the untwisted gluing of coordinates) or to $U$ (the twisted gluing) awaits the author's confirmation (the construction side reads it as $U$). Its components on primitive characters are the phases. The standard kernel is the Hartley kernel of Part 252 (ratifying the formalization; that this is consistent with the content of A1 is the author's judgment, based on the reading in the header comment of PAG256, not checked against the text of the monograph). The value is $\tau(\chi)/(i^a\sqrt N)$ (`PAG.Part256.rootNum`; the symbol W(χ) in the PAG256 docstrings and header comment denotes this value and is distinct from the inversion $W$); for primitive characters it is the root number, but that identification is outside Lean (state this explicitly). It differs from the value $\tau(\chi)/\sqrt N$ of the plain Fourier kernel $e(xy)$ by a factor $i$ for odd characters; do not smooth over this discrepancy. The convention for the additive character is convention T (the additive character of Tate's thesis: $\psi_\infty(x) = e^{-2\pi i x}$, $\psi_p(x) = e^{+2\pi i\{x\}_p}$), which is the standard for the foundational document (2026-11-18 19:25, the author's decision; its sign at the finite places agrees with Mathlib's `stdAddChar`, and it is the same additive character as Burnol's (arXiv:math/9811040)). Under convention T, for primitive $\chi$, the factor $\varepsilon(\chi) = (-i)^a$ of the Hartley kernel (`PAG.Part256.parFac`) agrees with the local constant $\varepsilon(1/2, \chi_\infty, \psi_\infty)$ at the infinite place, and $\tau(\chi)/\sqrt N$ agrees with the product of the local constants at the finite places at $s = 1/2$ (an agreement of values, outside Lean; local constants are defined in the style of Tate 1979). The same identification was written as a reading in the header comment and note of Part 257 (PAG261) (2026-11-14, confidence medium to high), and was re-confirmed by the literature check of 2026-11-18, `notes/pag2_literature_ia_sign.md` (one independent check and one integrated check). Following this, the treatment of $i^a$ as a reserved normalization factor was lifted by the author's decision at 19:25 on the same day. That the explicit factor $i^{\pm a}$ is the local constant at the infinite place does not depend on the convention, but whether the sign $\chi(-1)$ is placed at the infinite place or at the finite places does (in the opposite convention the infinite place gives $i^a$ and the product over the finite places is $\chi(-1)\tau(\chi)/\sqrt N$). Therefore, do not write "$\varepsilon(\chi)$ comes from the infinite place" without stating convention T. A1 remains a postulate. The material is in `notes/pag2_projection_material.md`.
 - The three propositions above are the author's definitions and design philosophy (the interpretive layer), not formalized theorems. Do not write notes that confuse their status.
 
 ## 2. Structure of the project and current position
diff --git a/CLAUDE.md b/CLAUDE.md
index 08c88d4..5de7a45 100644
--- a/CLAUDE.md
+++ b/CLAUDE.md
@@ -22,7 +22,7 @@
   - 直線は、解像度を落としたときに創発する有効な姿である。
   - ただし、解像度を決めるパラメータは**未決定**である。$N$、$K$、$\Lambda$ のいずれとも勝手に同一視しないこと。
   - 命題3の置き方（2026-11-13、著者から選択を委任された著者側 Muse の決定として記録。著者はいつでも覆せる）：上の定義の文面は変更しない。解像度の操作の数学的な置き場は「対象の中の移行（離散から連続への変化）」ではなく、大域対象への**切り方（見方）の選択**として解釈の層に置く。すなわち、素点たちは制限積の因子として最初から並列に共存している全体が対象であり、有限レベル商と $\Lambda$ 切断（A8 で分離した2軸）はその全体への見方であって、創発の問いは「見方を粗くしたとき直線がどう見えるか」と読む。解像度を $N$・$\Lambda$ と同一視する禁止は従来どおり維持する（決まったのは問いの置き場であり、パラメータではない）。その後 2026-11-14 に構築側の引き継ぎメモ（`PAG2_handoff_part257.md`）を通じて、著者の 08:41 の定義の原文が著者側に届いた：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。」この定義は上の置き方と矛盾しない — 解像度が落ちる側の操作は完備化への滑り落ちであり、姿勢は極限でも離散構造の観測の維持、極限は直極限の側（すべての素点を同時に測る側）で取る。完備化（$L^2$、$\mathbb{R}$、直積の位相）を使うときは「解像度が落ちる側の操作と読む」と、読みとして断る。閉包・完備化に現れる連続体を「有効な姿」や目標として書かない。また著者は 2026-11-13 08:38 に命題3の読みとして L1（解像度＝測る素点の集合）を構築側で採った（L1 は提案を読みとして採ったもので、定義の文面そのものではない。$N$・$K$・$\Lambda$ のいずれとも同一視しない）。著者の指示（2026-11-12）により、「直線の創発」という表現は使わない（命題3に触れるときは「§1 の命題3（解像度と有効な姿）」と参照で書き、何がどう変わるかを数学の言葉で書く）。
-  - 「射影」の読み（2026-11-18、著者が留保つきで採用。解釈の層であり、形式化済みの定理ではない）：命名の意味は「アデール幾何とイーデル幾何を射影によって融合する」（2026-11-16、著者）。命名の「射影」は舞台と変換の組を指し、主は変換である。舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28（PAG23〜PAG32））で、その上で働く反転（乗法の側）と加法の変換（加法の側）の合成を射影と呼ぶ（有限レベルでは Part 252（PAG256）の $J\circ H_N/\sqrt N$）。原始指標についての位相がその成分である。標準の核は Part 252 の Hartley 核とする（形式化の追認。A1 の内容と揃う）。値は $\tau(\chi)/(i^a\sqrt N)$（`PAG.Part256.rootNum`。PAG256 の docstring の記号 W(χ) はこの値を指し、反転の $W$ とは別）で、原始指標ではルート数だが、その同定は Lean の外である（明記すること）。素朴なフーリエ核 $e(xy)$ の値 $\tau(\chi)/\sqrt N$ とは奇の指標で $i$ 倍ずれ、このずれを滑らかにしない。加法指標の規約は、規約 T（Tate の学位論文の加法指標：$\psi_\infty(x) = e^{-2\pi i x}$、$\psi_p(x) = e^{+2\pi i\{x\}_p}$）を基礎文書の標準とする（2026-11-18、著者の決定。Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol とも同じ規約）。規約 T のもとで、Hartley 核の因子 $\varepsilon(\chi) = (-i)^a$（`PAG.Part256.parFac`）は無限素点の局所定数 $\varepsilon(1/2, \chi_\infty, \psi_\infty)$ と一致し、$\tau(\chi)/\sqrt N$ は有限素点の局所定数の積と一致する（値の一致であり Lean の外。局所定数は Tate 1979 の流儀で定める。2026-11-18 の文献照合 `notes/pag2_literature_ia_sign.md`、独立照合 1 回。これを受けて、$i^a$ を正規化因子として留保する扱いは同日に外した）。$i$ の冪が無限素点から来ることは規約によらないが、符号 $\chi(-1)$ を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が $i^a$、有限素点の積が $\chi(-1)\tau(\chi)/\sqrt N$）。したがって、規約 T を明示せずに「$\varepsilon(\chi)$ は無限素点から来る」と書かない。A1 は公準のまま。材料は `notes/pag2_projection_material.md`。
+  - 「射影」の読み（2026-11-18、著者が留保つきで採用。解釈の層であり、形式化済みの定理ではない）：命名の意味は「アデール幾何とイーデル幾何を射影によって融合する」（2026-11-16、著者）。命名の「射影」は舞台と変換の組を指し、主は変換である。著者の言葉では「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」。舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28（PAG23〜PAG32））。構築側の読みでは、その合成は反転（乗法の側）と加法の変換（加法の側）の合成で、有限レベルでは Part 252（PAG256）の $J\circ H_N/\sqrt N$（`PAG.Part256.JH`）に当たる。ただし `JH` は $\mathbb Z/N$ の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではなく、`JH` と P¹ のモデルを結ぶ Lean の文はない。「貼り合わせ」が PAG23 の `Compat`（ねじれのない座標の貼り合わせ）と $U$（ねじれた貼り合わせ）のどちらを指すかは著者の確認待ち（構築側の読みは $U$）。原始指標についての位相がその成分である。標準の核は Part 252 の Hartley 核とする（形式化の追認。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは未照合）。値は $\tau(\chi)/(i^a\sqrt N)$（`PAG.Part256.rootNum`。PAG256 の docstring と冒頭のコメントの記号 W(χ) はこの値を指し、反転の $W$ とは別）で、原始指標ではルート数だが、その同定は Lean の外である（明記すること）。素朴なフーリエ核 $e(xy)$ の値 $\tau(\chi)/\sqrt N$ とは奇の指標で $i$ 倍ずれ、このずれを滑らかにしない。加法指標の規約は、規約 T（Tate の学位論文の加法指標：$\psi_\infty(x) = e^{-2\pi i x}$、$\psi_p(x) = e^{+2\pi i\{x\}_p}$）を基礎文書の標準とする（2026-11-18 19:25、著者の決定。Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol（arXiv:math/9811040）とも同じ加法指標）。規約 T のもとで、原始的な $\chi$ について、Hartley 核の因子 $\varepsilon(\chi) = (-i)^a$（`PAG.Part256.parFac`）は無限素点の局所定数 $\varepsilon(1/2, \chi_\infty, \psi_\infty)$ と一致し、$\tau(\chi)/\sqrt N$ は $s = 1/2$ での有限素点の局所定数の積と一致する（値の一致であり Lean の外。局所定数は Tate 1979 の流儀で定める）。同じ同定は Part 257（PAG261）の冒頭の説明とノートに読みとして書かれており（2026-11-14、確信度：中〜高）、2026-11-18 の文献照合 `notes/pag2_literature_ia_sign.md`（独立照合 1 回と統合照合 1 回）で確かめ直した。これを受けて、$i^a$ を正規化因子として留保する扱いは同日 19:25 の著者の決定で外した。明示的な因子 $i^{\pm a}$ が無限素点の局所定数であることは規約によらないが、符号 $\chi(-1)$ を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が $i^a$、有限素点の積が $\chi(-1)\tau(\chi)/\sqrt N$）。したがって、規約 T を明示せずに「$\varepsilon(\chi)$ は無限素点から来る」と書かない。A1 は公準のまま。材料は `notes/pag2_projection_material.md`。
 - 上記3命題は著者の定義・設計思想（解釈の層）であり、形式化済みの定理ではない。ノートではその地位を混同して書かないこと。
 
 ## 2. プロジェクトの構成と現在地
diff --git a/docs/overview-and-comparison.en.md b/docs/overview-and-comparison.en.md
index 9052bce..7ad318a 100644
--- a/docs/overview-and-comparison.en.md
+++ b/docs/overview-and-comparison.en.md
@@ -99,7 +99,7 @@ Here $A_N$ is the shell algebra, which is the same as the known Terwilliger alge
 **Open questions**
 
 - How to formulate the "projection" in the name (the operation fusing the adelic and the idelic sides) as a specific map or construction.
-  - Adopted reading (proposed by the construction side, adopted with reservations by the author on 2026-11-18; interpretive layer, not a formalized theorem): the "projection" in the name refers to the pair of a stage and a transform, with the transform as the main sense. The stage is the projective line P¹ (Parts 19–28; inversion swaps 0 and ∞). The composition, acting on it, of inversion (the multiplicative side) and an additive transform (the additive side) is called the projection; at the finite level this is $J \circ H_N$ of Part 252. Its components on primitive characters are the phases. The standard kernel is the Hartley kernel of Part 252, with value $\tau(\chi)/(i^a\sqrt N)$ (the root number for primitive χ, but that identification is outside Lean). With the plain Fourier kernel $e(xy)$ the value is $\tau(\chi)/\sqrt N$, differing by a factor $i$ for odd characters. The additive character follows the convention of Tate's thesis ($e^{-2\pi i x}$ at the infinite place, $e^{+2\pi i\{x\}_p}$ at the finite places) as the standard; in that convention the factor $(-i)^a$ of the Hartley kernel agrees with the local constant at the infinite place, and $\tau(\chi)/\sqrt N$ agrees with the product of the local constants at the finite places (an agreement of values, outside Lean; literature check of 2026-11-18, `notes/pag2_literature_ia_sign.md`, Japanese). That the power of $i$ comes from the infinite place does not depend on the convention, but where the sign $\chi(-1)$ is placed does. Axiom A1 remains a postulate that chooses the phase of the boundary unitary to be this value. All ingredients are known, and this is not made a new Part (`notes/pag2_projection_material.md`, Japanese). Remaining question: a formulation as one construction across all places.
+  - Adopted reading (proposed by the construction side, adopted with reservations by the author on 2026-11-18; interpretive layer, not a formalized theorem): the "projection" in the name refers to the pair of a stage and a transform, with the transform as the main sense (in the author's words: "the stage is P¹, and the composition of gluings acting on it is called the projection"). The stage is the projective line P¹ (Parts 19–28 (PAG23–PAG32); inversion swaps 0 and ∞). In the construction side's reading, that composition is the composition of inversion (the multiplicative side) and an additive transform (the additive side), which at the finite level corresponds to $J \circ H_N/\sqrt N$ of Part 252 (PAG256) (a map sending functions on ℤ/N to functions on the units, not an operator on P¹; no Lean statement links it to the models of P¹). Its components on primitive characters are the phases; the standard kernel is the Hartley kernel of Part 252 (the author's decision), with value $\tau(\chi)/(i^a\sqrt N)$ (the root number for primitive χ, but that identification is outside Lean). With the plain Fourier kernel $e(xy)$ the value is $\tau(\chi)/\sqrt N$, differing by a factor $i$ for odd characters. The additive character follows the convention of the additive character of Tate's thesis ($e^{-2\pi i x}$ at the infinite place, $e^{+2\pi i\{x\}_p}$ at the finite places) as the standard (the author's decision). In that convention, for primitive χ, the factor $(-i)^a$ of the Hartley kernel agrees with the local constant at the infinite place, and $\tau(\chi)/\sqrt N$ agrees with the product of the local constants at the finite places at $s = 1/2$ (an agreement of values, outside Lean; local constants in the style of Tate 1979; literature check of 2026-11-18, `notes/pag2_literature_ia_sign.md`, Japanese, re-confirming the reading recorded in Part 257 (PAG261)). That the explicit factor $i^{\pm a}$ is the local constant at the infinite place does not depend on the convention, but where the sign $\chi(-1)$ is placed does. The postulate A1 remains a postulate that chooses the phase of the boundary unitary on primitive characters to be this value (a reading). All ingredients are known, and this is not made a new Part (`notes/pag2_projection_material.md`, Japanese). Remaining question: a formulation as one construction across all places (at the level of spaces and operators). At the level of values, the decomposition into a product of local factors over all places is in Part 257 (PAG261).
 - Whether the finite-level inductive system reaches the side of $T(0)$ (literature check for direction γ).
 - Whether the operation of resolution needs a formulation beyond L1.
 - Drafting the foundational document (author's side).
diff --git a/docs/overview-and-comparison.md b/docs/overview-and-comparison.md
index 51eafef..06e17b0 100644
--- a/docs/overview-and-comparison.md
+++ b/docs/overview-and-comparison.md
@@ -99,7 +99,7 @@
 **開いている問い**
 
 - 命名にある「射影」（アデールの側とイーデルの側を融合する操作）を、どの写像・構成として定式化するか。
-  - 採用した読み（構築側が出し、2026-11-18 に著者が留保つきで採用。解釈の層で、形式化済みの定理ではない）：命名の「射影」は舞台と変換の組を指し、主は変換。舞台は射影直線 P¹（Part 19〜28。反転が 0 と ∞ を入れ替える）。その上で働く反転（乗法の側）と加法の変換（加法の側）の合成を射影と呼び、有限レベルでは Part 252 の J∘H_N。原始指標についての位相がその成分で、標準の核は Part 252 の Hartley 核、値は τ(χ)/(i^a√N)（原始指標ではルート数だが、その同定は Lean の外）。素朴なフーリエ核 e(xy) では τ(χ)/√N で、奇の指標で i 倍ずれる。加法指標は Tate の学位論文の規約（無限素点で e^{−2πix}、有限素点で e^{+2πi{x}_p}）を標準とし、その規約で Hartley 核の因子 (−i)^a は無限素点の局所定数と、τ(χ)/√N は有限素点の局所定数の積と一致する（値の一致で Lean の外。2026-11-18 の文献照合 `notes/pag2_literature_ia_sign.md`）。i の冪が無限素点から来ることは規約によらないが、符号 χ(−1) の置き場は規約による。公準 A1 は境界ユニタリの位相をこの値に選ぶ公準のまま。部品はすべて既知で、新しいパートにはしない（`notes/pag2_projection_material.md`）。残る問い：全素点を通した一つの構成としての定式化。
+  - 採用した読み（構築側が出し、2026-11-18 に著者が留保つきで採用。解釈の層で、形式化済みの定理ではない）：命名の「射影」は舞台と変換の組を指し、主は変換（著者の言葉では「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」）。舞台は射影直線 P¹（Part 19〜28（PAG23〜PAG32）。反転が 0 と ∞ を入れ替える）。構築側の読みでは、その合成は反転（乗法の側）と加法の変換（加法の側）の合成で、有限レベルでは Part 252（PAG256）の J∘H_N/√N に当たる（ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。P¹ のモデルと結ぶ Lean の文はない）。原始指標についての位相がその成分で、標準の核は Part 252 の Hartley 核（著者の決定）、値は τ(χ)/(i^a√N)（原始指標ではルート数だが、その同定は Lean の外）。素朴なフーリエ核 e(xy) では τ(χ)/√N で、奇の指標で i 倍ずれる。加法指標は Tate の学位論文の加法指標の規約（無限素点で e^{−2πix}、有限素点で e^{+2πi{x}_p}）を標準とする（著者の決定）。その規約で、原始的な χ について、Hartley 核の因子 (−i)^a は無限素点の局所定数と、τ(χ)/√N は s = 1/2 での有限素点の局所定数の積と一致する（値の一致で Lean の外。局所定数は Tate 1979 の流儀。2026-11-18 の文献照合 `notes/pag2_literature_ia_sign.md` による、Part 257（PAG261）の読みの確かめ直し）。明示的な因子 i^{±a} が無限素点の局所定数であることは規約によらないが、符号 χ(−1) の置き場は規約による。公準 A1 は、境界ユニタリの原始指標の位相をこの値に選ぶ公準のまま（読み）。部品はすべて既知で、新しいパートにはしない（`notes/pag2_projection_material.md`）。残る問い：全素点を通した一つの構成（空間と作用素のレベル）としての定式化。値のレベルでは、全素点の局所因子の積への分解が Part 257（PAG261）にある。
 - 有限レベルの帰納系が $T(0)$ の側に届くか（方向 γ の文献照合）。
 - 解像度の操作に、L1 を超える定式化が要るか。
 - 基礎文書の起草（著者側）。
diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
index 56b8ccf..0d09733 100644
--- a/handoff/PAG2_handoff_part259.md
+++ b/handoff/PAG2_handoff_part259.md
@@ -772,9 +772,12 @@
 
 - **尾の統合照合（2026-11-18、補足 11 の独立の納品物）**：F3 の後の記録の直し、Part 258・259 の照合者 B の後の直し、Part 259 のノートと xlsx を、形式文の全文を渡した照合者 T が 1 回で照らした。偽・空虚な形式文はなし。食い違い 2 件（PAG263 の「`compat_dind_unique` は Part 258 により空虚に真」の根拠の誤り、Part 258 のノートの表の補助の行の誤り）ほかを、主張を変えない直しで直し、尾の台帳は空になった（記録 `notes/pag2_tail_audit_20261118.md`、`records/tail_audit/`、xlsx final81）。開いたまま残る問い：gcd ≠ 1 で (i) と D の側だけを満たす写像の不存在（数値の見込みのみ）。
 
-- **命名の「射影」の事前登録と材料ノート（2026-11-18、短期層）**：著者の命名（「アデール幾何とイーデル幾何を射影によって融合する」、−∞・∞・0 が射影で重なる）を受けて、「射影」を問いとして 4 点で事前登録した（`notes/pag2_prereg_projection.md`）。盲検の問いテストと内部照合（Part 13・19〜28 の P¹、定理 2.6）の結果、残余は空で、新しいパートは始めない。基礎文書の第 1・2 章のための材料ノート（`notes/pag2_projection_material.md`、第 3 版）に、構築側の読み（舞台 P¹／反転 ∘ 加法の変換／原始指標の位相、A1 は公準のまま）と対応表をまとめた。独立照合 2 回（`records/prereg_projection/outputs/`）。第 2 回の後の直しは照合者の直し案に沿った言い換えと範囲を狭める直しで、照合にかけていない（次の統合照合の対象）。注意：素朴なフーリエ核 e(xy) の成分は τ(χ)/√N、Part 252 の Hartley 核の成分は 𝔀(χ) = τ(χ)/(i^a√N)（`rootNum`）で、奇の χ で i 倍ずれ、素朴な核の値は核の符号でも変わる。PAG256 の docstring の W(χ) は 𝔀 を指す（反転ではない）。2026-11-18 19:01 の著者の決定（ノート第 4 版 §6）：読みは留保つきで採用（「ルート数であることは Lean の外」を明記し、奇の χ での i 倍のずれを滑らかにしない）。命名の「射影」は舞台と変換の両方を指し、主は変換。標準の核は Hartley 核（Part 252 の追認）。i^a は正規化因子として書き、無限素点への帰属は候補として留保。i^a の帰属と符号の規約の文献照合は、基礎文書が無限素点の読みを断定する前に行う（候補 1・候補 3・γ と同じ照合リスト）。CLAUDE.md §1（と英語版）には同日 19:03 の著者の指示で反映した。照合リストへの項目の文案はノート §9（照合リストは著者側のもので、構築側では変えていない）。
+- **命名の「射影」の事前登録と材料ノート（2026-11-18、短期層）**：著者の命名（「アデール幾何とイーデル幾何を射影によって融合する」、−∞・∞・0 が射影で重なる）を受けて、「射影」を問いとして 4 点で事前登録した（`notes/pag2_prereg_projection.md`）。盲検の問いテストと内部照合（Part 13（PAG17）・Part 19〜28（PAG23〜PAG32）の P¹、定理 2.6。位相の分解を扱った Part 256・257（PAG260・PAG261）は見落とした。下の文献照合の項）の結果、残余は空で、新しいパートは始めない。基礎文書の第 1・2 章のための材料ノート（`notes/pag2_projection_material.md`、現行は第 6 版）に、構築側の読み（舞台 P¹／反転 ∘ 加法の変換／原始指標の位相、A1 は公準のまま）と対応表をまとめた。独立照合 2 回（`records/prereg_projection/outputs/`）。第 2 回の後の直しは照合者の直し案に沿った言い換えと範囲を狭める直しで、照合にかけていない（次の統合照合の対象）。注意：素朴なフーリエ核 e(xy) の成分は τ(χ)/√N、Part 252 の Hartley 核の成分は 𝔀(χ) = τ(χ)/(i^a√N)（`rootNum`）で、奇の χ で i 倍ずれ、素朴な核の値は核の符号でも変わる。PAG256 の docstring の W(χ) は 𝔀 を指す（反転ではない）。2026-11-18 19:01 の著者の決定（ノート §6 の 1〜3）：読みは留保つきで採用（「ルート数であることは Lean の外」を明記し、奇の χ での i 倍のずれを滑らかにしない）。命名の「射影」は舞台と変換の両方を指し、主は変換。標準の核は Hartley 核（Part 252 の追認）。i^a は正規化因子として書き、無限素点への帰属は候補として留保（19:25 に外した。次項）。i^a の帰属と符号の規約の文献照合は、基礎文書が無限素点の読みを断定する前に行う（候補 1・候補 3・γ と同じ照合リスト）。CLAUDE.md §1（と英語版）には同日 19:03 の著者の指示で反映した。照合リストへの項目の文案はノート §9（照合リストは著者側のもので、構築側では変えていない）。
 
-- **照合リストの項目「i^a の帰属と符号の規約」の文献照合（2026-11-18、短期層）**：`notes/pag2_literature_ia_sign.md`（第 2 版）、記録 `records/literature_ia/`。結論：i の冪は無限素点から来る（規約によらない）。符号 ξ(−1) の置き場は加法指標の規約による。Tate の学位論文の加法指標（ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}。照合者が走査版で確認、構築側は原文未読）では、PAG256 の `parFac`（偶 1、奇 −i）が無限素点の局所定数 (−i)^a と、τ(χ)/√N が有限素点の局所定数の積と一致する（値の一致、Lean の外）。逆の規約では無限素点が i^a、有限素点の積が χ(−1)τ(χ)/√N。数値は構築側 209 指標、照合者 2,162 指標（局所関数等式からの直接評価を含む）。ラベル［既知］、PAG との対応は［再導出（小さい）］。照合後の直しは未照合（次の統合照合の対象）。2026-11-18 19:25 の著者の決定（ノート第 3 版 §9）：CLAUDE.md §1 の留保（i^a は正規化因子）を外して規約を明示した書き方に置き換え、規約 T を基礎文書の標準にした。CLAUDE.md §1 と英語版、材料ノート第 5 版 §6 の 4・5、概要に反映した。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
+- **照合リストの項目「i^a の帰属と符号の規約」の文献照合（2026-11-18、短期層）**：`notes/pag2_literature_ia_sign.md`（現行は第 4 版）、記録 `records/literature_ia/`。結論（原始的な χ について）：明示的な因子 i^{±a} は無限素点の局所定数（規約によらない）。符号 ξ(−1) の置き場は加法指標の規約による。Tate の学位論文の加法指標（ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}。照合者が走査版で確認、構築側は原文未読）では、PAG256 の `parFac`（偶 1、奇 −i）が無限素点の局所定数 (−i)^a と、τ(χ)/√N が s = 1/2 での有限素点の局所定数の積と一致する（値の一致、Lean の外）。逆の規約では無限素点が i^a、有限素点の積が χ(−1)τ(χ)/√N。数値は構築側 209 指標、照合者 2,162 指標（局所関数等式からの直接評価を含む）。ラベル［既知］、PAG との対応は［再導出（小さい）］。照合後の直しは同日夜の統合照合で照らした。2026-11-18 19:25 の著者の決定（ノート §9）：CLAUDE.md §1 の留保（i^a は正規化因子）を外して規約を明示した書き方に置き換え、規約 T を基礎文書の標準にした。CLAUDE.md §1 と英語版、材料ノート §6 の 4・5、概要に反映した。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
+  - **内部の重複（第 12 の型）**：この文献照合は着手前の内部照合をせずに始めた。同じ結論（形 (II) の素数ごとの因子が規約 T の局所定数、∞ が i^{−a}、規約を逆にすると χ_p(−1) が移る、ω_p(p) = ∏_{q≠p} χ_q(p)）は、Part 257（PAG261、2026-11-14）の冒頭の説明・ノート・事前登録に読みとして書かれていた（盲検の申告で Rohrlich の講義ノート、確信度：中〜高）。今回の照合は確かめ直しで、加えたのは、学位論文の規約の本文での確認（照合者）、二つ目の文献（Roy–Schmidt–Yi）、ω_p(p) の独立の導出と数値、数値（構築側 209 指標、照合者 2,162 指標。重なりを含む）、`parFac` との値の一致の明示（ノート §0）。教訓：文献照合も着手前に鎖の docstring とノートを言葉で検索する。
+- **尾の統合照合（2026-11-18 夜）**：材料ノート第 2〜5 版、文献照合ノート第 1〜3 版、CLAUDE.md と英語版の §1 の箇条、概要の日英の行、この引き継ぎメモの行を、差分・全文・形式文の全文（PAG23・PAG26・PAG27・PAG256）を渡した照合者 1 人が照らした（`records/tail_audit2/`、所要 約 9.6 分）。式・数値・文献の主張は検算の範囲ですべて正しかった。直したのは記録の側：材料ノートの直し忘れ 2 か所、CLAUDE.md と概要に移すときに落ちた限定（原始性、s = 1/2、JH は P¹ の上の作用素ではないこと）、地位の書き分け（「A1 の内容と揃う」は著者の判断、「公準 A1 は…（読み）」）、著者の言葉「貼り合わせの合成」と構築側の言い換えの書き分け、版の参照、Part と PAG の番号の併記、修飾されていない宣言名。直しはすべて限定を足す・記録を事実に合わせる直しで、数学の主張を強めるものはない（補足 8）。著者に確かめること：「貼り合わせの合成」の貼り合わせは `Compat`（ねじれのない座標の貼り合わせ）と U（ねじれた貼り合わせ）のどちらか（構築側の読みは U）。
+- **基礎文書の材料索引（2026-11-18 夜、短期層）**：`notes/pag2_founding_material_index.md`（第 2 版）。骨格の 6 章ごとに、主張・地位（定義／読み／定理のラベル／公準／数値のみ／Lean の外）・完全修飾名の宣言（Part と PAG を併記）・ノート・留保・開いている点を並べた。宣言名 102 件はすべて実在を機械的に確認（`records/founding_index/check_names.py`）。独立照合 1 回（`records/founding_index/`）で、形式文より強い見出し、5.1 の条件番号の取り違え（殻を混ぜない条件は (ii)）、骨格の記述と CLAUDE.md の記載の出所の混同、落ちていた留保（記号 W と 𝔀、3.1 の「有効な姿」の規則、4.1 の守備範囲、5.2 の 3 点など）を指摘され、第 2 版で直した。第 2 版の直しは未照合（次の統合照合の対象）。CLAUDE.md §3 の候補 1 の範囲「Part 246–248」は、項目 66 の宣言が PAG249（Part 245）にあるので Part 245〜248 と読める（CLAUDE.md は著者のファイルなので変えていない。著者への報告事項）。
 
 ## 点検（2026-10-24、Part 204 の後）
 - 全体の再ビルド：PAG.lean〜PAG208.lean（208 本）を空のディレクトリで最初からコンパイルし直した。208 本すべて成功、エラー・警告 0、約 10 分。#print axioms 1903 項目すべて標準の公理（またはその一部）。作業用の .out と 208/208 一致。
diff --git a/notes/pag2_literature_ia_sign.md b/notes/pag2_literature_ia_sign.md
index ef208b3..5e6a149 100644
--- a/notes/pag2_literature_ia_sign.md
+++ b/notes/pag2_literature_ia_sign.md
@@ -1,9 +1,32 @@
 # アーデル射影幾何 — 照合リストの項目「i^a の帰属と加法指標の符号の規約」の文献照合
 
-（2026-11-18。短期層の小さいノート。新しいパートではない。出所：CLAUDE.md §1 の「射影」の読み（2026-11-18、著者が留保つきで採用）と、材料ノート `pag2_projection_material.md` §2 の注意 2。著者の決定で、基礎文書が無限素点の読みを断定する前に行う照合として、候補 1・候補 3・γ と同じ照合リストに入った項目である。著者の定義（§1）の文面と A1 の地位は変えない。第 1 版を独立照合にかけ、その指摘で直した第 2 版に、著者の決定を記録したのがこの第 3 版である（§8・§9）。）
+（2026-11-18。短期層の小さいノート。新しいパートではない。出所：CLAUDE.md §1 の「射影」の読み（2026-11-18、著者が留保つきで採用）と、材料ノート `pag2_projection_material.md` §2 の注意 2。著者の決定で、基礎文書が無限素点の読みを断定する前に行う照合として、候補 1・候補 3・γ と同じ照合リストに入った項目である。著者の定義（§1）の文面と A1 の地位は変えない。第 1 版を独立照合にかけ、その指摘で直した第 2 版に、著者の決定を記録したのが第 3 版、統合照合の指摘と後から行った内部照合（§0）を反映したのがこの第 4 版である（§0・§8〜§10）。）
 
 記号：ξ は法 N の原始 Dirichlet 指標、a は ξ が奇なら 1・偶なら 0、τ(ξ) = Σ_x ξ(x) e^{2πix/N}、W(ξ) = τ(ξ)/(i^a √N)（古典的なルート数。Lean では `PAG.Part256.rootNum` の値 𝔀(ξ)。ルート数であることは Lean の外）。局所定数 ε(s, χ_v, ψ_v) は、Tate 1979（Corvallis）の流儀で定める：f̂(y) = ∫ f(x) ψ(xy) dx、局所関数等式の定数、ψ_v に関して自己双対な測度。
 
+## §0 内部照合（後から行った。第 12 の型の記録）
+
+この文献照合は、着手の前に自分の鎖（Lean の docstring・ノート・事前登録）の内部照合をせずに始めた。2026-11-18 夜、次の推薦の下調べで鎖を言葉で検索して（「局所定数」「学位論文」「ψ_∞」「i^{−a}」「無限素点の局所因子」）、同じ結論が鎖にすでに書かれていることが分かった。
+
+- **Part 257（PAG261、2026-11-14）**：冒頭の説明、ノート `pag2_part257_local_factor_decomposition.md` の「読み」、事前登録 `pag2_part257_preregistration.md` §2.3・§6 に、次がすでに書かれている。
+  - 加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}（Tate の学位論文の規約）にとり、イデール類指標を不分岐な q で ω_q(q) = χ(q) と正規化すると、形 (II) の p の因子 (τ(χ_p)/√p^{e_p})·∏_{q≠p} χ_q(p^{e_p})（`rootNum_listChar_formII`・`gaussSum_primeFactors`）は ω の p での局所定数と一致し、∞ の局所定数は i^{−a}（`parFac`）。
+  - 加法指標の規約を逆にすると、各 p の因子が χ_p(−1) 倍、∞ の因子が i^a になり、積は変わらない。
+  - ω_p(p) = ∏_{q≠p} χ_q(p)（確信度：中、一次文献では未確認、と書かれていた）。
+  - 根拠は着手前の盲検の問いテスト（Rohrlich の講義ノート (2.49)・(2.55)・(2.69)・(2.70)。構築側は開いていない）と構築側の手計算。同定の確信度は中〜高。
+- **Part 256（PAG260、2026-11-13）**：「偶奇の因子が無限素点の局所因子にあたる、は読み」（冒頭の説明、`parFac_prodChar` の docstring）。
+
+したがって、このノートの §1 (a)(b) の結論は Part 257 の読みと同じで、新しく分かったことではない。今回の照合が Part 257 の記録に加えたものは次のとおり。
+
+1. Tate の学位論文の加法指標の規約を、照合者が走査版の本文（§2.2）で確かめた（Part 257 では盲検の申告で、Rohrlich 経由）。
+2. 二つ目の文献 Roy–Schmidt–Yi（式 (150)・(155)〜(157)）。
+3. ω_p(p) = ∏_{q≠p} χ_q(p) を、構築側と照合者がそれぞれ導出し、数値で確かめた（Part 257 では確信度：中）。
+4. 数値：構築側 209 指標、照合者 2,162 指標（局所関数等式からの直接評価を含む）。
+5. PAG256 の Hartley 核の因子 `parFac` との値の一致を、規約 T を明示して書いた（Part 257 でも ε_∞ = parFac と読んでいた）。
+
+以上により、Part 257 の「同定は確信度：中〜高」は、規約 T を明示した値の一致として確信度：高に上げてよいと読む（構築側の判断）。
+
+教訓：文献照合も、着手の前に自分の鎖の内部照合（docstring とノートの言葉の検索）を行う。今回の「射影」の事前登録（`pag2_prereg_projection.md`）の §0 の内部照合も、P¹ の Part 13・19〜28 と定理 2.6 を見たが、位相の分解を扱った Part 256・257 を見落としていた。材料ノートの注意 2 の「照合者の知識による。確信度：中」も、鎖に Part 257 の記録があったことを書いていなかった。
+
 ## §1 問いと結論
 
 照合リストの項目は次の 2 つだった。
@@ -13,7 +36,7 @@
 
 結論：
 
-- (a) **i の冪は無限素点から来る。符号 (−1)^a の置き場は規約による。** 無限素点の局所定数は i の冪で、有限素点の局所定数はガウス和である（i の冪を含まない）。ここまではどちらの規約でも同じ。ただし冪の向きは規約で変わる：Tate の学位論文の加法指標の規約（下の規約 T）では ε(1/2, χ_∞, ψ_∞) = (−i)^a = i^{−a}、逆の規約 C では i^a。［既知］（確信度：高）
+- (a) **明示的な因子 i^{±a} は無限素点の局所定数である。符号 (−1)^a の置き場は規約による。** 無限素点の局所定数は i の冪で、有限素点の局所定数はガウス和である（明示的な i^{±a} の因子を持たない。ただし値は i を取りうる。例：法 3 の奇の指標で τ/√3 = i。規約 T では無限素点が −i、有限素点が i で、積は W = 1）。ここまではどちらの規約でも同じ（照合者の導出：ℚ の上で自明な加法指標は ψ_T(c·)（c ∈ ℚ^×）の形で、ε(s, χ, ψ_c) = χ(c)|c|^{s−1/2} ε(s, χ, ψ) から、無限素点は ±i^a、有限素点の積は ±τ/√N の正の数倍になる）。ただし冪の向きは規約で変わる：Tate の学位論文の加法指標の規約（下の規約 T）では ε(1/2, χ_∞, ψ_∞) = (−i)^a = i^{−a}、逆の規約 C では i^a。［既知］（確信度：高）
 - (b) **規約で決まる。** s = 1/2 で、規約 T では τ(ξ)/√N、規約 C では ξ(−1)τ(ξ)/√N。どちらの規約でも、s = 1/2 での大域の積は W(ξ) で変わらない（一般の s では N^{1/2−s} W(ξ)）。偶奇の符号 ξ(−1) = (−1)^a を無限素点と有限素点のどちらに置くかは、規約の選び方である。［既知］（確信度：高）
 - **PAG への帰結**（値の一致。Lean の外）：
   - PAG256 の Hartley 核の因子 ε(ξ) = `parFac`（偶で 1、奇で −i）は、規約 T の無限素点の局所定数 (−i)^a と同じ値である。残りの τ(ξ)/√N は、規約 T の有限素点の局所定数の積と同じ値である。
@@ -26,11 +49,11 @@
 
 - **規約 T**：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}（{x}_p は p 進の小数部分）。積は ℚ の上で自明。
   - Tate の学位論文（1950）：実数体で λ(x) = −x（本文に「負の符号に注意」の注記）、p 進体で λ(x) は λ(x) − x が p 進整数となる有理数。指標は e^{2πiΛ}（§2.2、§4.1 Lemma 4.1.5）。**照合者が走査版（Rutgers）で確認した。構築側は原文を開いていない。** 照合者の注記：同論文の Fourier 変換は e^{−2πiΛ(ξη)} を核とし（実数体では e^{+2πixy}）、局所の定数は逆向きの比 ρ(c) として定義されている。上の ε の定め方は学位論文そのものではなく、Corvallis 論文の流儀である。走査版の式は OCR が崩れており、この注記の確信度は中。
-  - Roy–Schmidt–Yi, "Classical and adelic Eisenstein series", arXiv:2109.07649 §4.3：ψ を Tate の学位論文で定義されたものとし、ψ_∞(x) = e^{−2πix} と書く。
+  - Roy–Schmidt–Yi, "Classical and adelic Eisenstein series", arXiv:2109.07649 §4.3：ψ を Tate の学位論文で定義されたものとし、ψ_∞(x) = e^{−2πix} と書く（式 (150)〜(157) は同論文の §6.1）。
   - Burnol, arXiv:math/9811040（"Spectral Analysis of the Local Conductor Operator"）：実素点で exp(−2πit)、有限素点で exp(2πi{Tr t})。モノグラフ層が引く Burnol と同じ著者。読んだ範囲には、Tate の規約への言及も符号の選び方の説明もない。
   - arXiv:1502.02633 も同じ指標を「標準の加法指標」として書く。ただし、Tate の学位論文に従うと明記しているのは Haar 測度の正規化だけである（第 1 版の「Tate の学位論文の規約として書く」は言い過ぎだったので直した）。
 - **規約 C**（逆の規約）：ψ_∞(x) = e^{+2πix}、ψ_p(x) = e^{−2πi{x}_p}。例：arXiv:2604.25288 §5.1、arXiv:1511.04265 式 (3.72)〜(3.75)（照合者が確認）。
-- 指標の対応は ψ によらない：ξ に対応するイデール類指標 χ は、不分岐の ℓ で χ_ℓ(ℓ) = ξ(ℓ)。分岐する p では、χ_p の ℤ_p^× への制限が (ξ^{(p)})^{−1}（Roy–Schmidt–Yi 式 (150)。ξ = ∏ ξ^{(p)} は中国剰余定理による分解）。χ_∞ は偶で自明、奇で符号（同 式 (151)）。
+- 指標の対応は ψ によらない：ξ に対応するイデール類指標 χ は、不分岐の ℓ で χ_ℓ(ℓ) = ξ(ℓ)。分岐する p では、χ_p の ℤ_p^× への制限が (ξ^{(p)})^{−1}（Roy–Schmidt–Yi §6.1 の式 (150) ∏_{p∣u} χ_p(a) = ξ(a)^{−1} から、a を中国剰余定理で選んで導かれる。ξ = ∏ ξ^{(p)} は中国剰余定理による分解）。χ_∞ は偶で自明、奇で符号（同 式 (151)）。
 
 ## §3 無限素点の局所定数
 
@@ -54,7 +77,7 @@
   - 規約を混ぜると（規約 T の ψ_p と規約 C の ε_∞）、奇の指標 105 個すべてで合わない。
 - 照合者（`outputs/check_eps.py`・`check_supp.py` とその出力）：
   - 法 1〜100 と 120, 128, 135, 180, 243, 256, 360, 400 の原始指標 2,162 個。
-  - p 進の局所定数を局所関数等式から有限和で直接評価し、§4 の閉じた式と比べた（6,288 回、最大差 3.1×10⁻¹³）。
+  - p 進の局所定数を局所関数等式から有限和で直接評価し、§4 の閉じた式と比べた（照合者の出力では 6,288 回、最大差 3.1×10⁻¹³。回数の内訳は出力に書かれておらず、統合照合では素因数の個数の和から見積もった数と合わないと指摘された。確かめていない）。
   - W(ξ) は θ 変換の関係で別に確かめた（3.1×10⁻¹³）。一般の s での積 N^{1/2−s} W(ξ) も確かめた。
   - 混ぜた規約では、奇の指標 1,082 個すべてで −W(ξ) になった。混ぜた ψ は ℚ の上で自明でない（x = 1/3 で e^{4πi/3}）ので、大域の選び方として許されない。
   - Hartley 和の式 Σ_x ξ(x) cas(2πxy/N) = ε(ξ)τ(ξ)ξ̄(y) はすべての y で成り立った（ξ 原始。原始でない指標では法 4 の y = 0, 2 などで崩れる）。引数の符号を逆にした cas(−2πxy/N) では ξ(−1)√N·W(ξ) になる。
@@ -92,7 +115,14 @@
 
 第 2 版の §9 で仰いだ 2 つの判断に、著者は「1 と 2 を進めてください」と答えた。
 
-1. **留保を外す。** CLAUDE.md §1（と英語版）の「i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する」を、規約を明示した書き方に置き換えた。規約 T のもとで、ε(ξ) = (−i)^a は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(ξ)/√N は有限素点の局所定数の積と一致する（値の一致、Lean の外）。i の冪が無限素点から来ることは規約によらないが、符号 ξ(−1) の置き場は規約による。規約 T を明示せずに「ε(ξ) は無限素点から来る」と書かない。
-2. **規約 T を基礎文書の標準にする。** Mathlib の `stdAddChar` と有限素点の符号が合い、Tate の学位論文の加法指標・Burnol とも同じ規約。
+1. **留保を外す。** CLAUDE.md §1（と英語版）の「i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する」を、規約を明示した書き方に置き換えた。規約 T のもとで、ε(ξ) = (−i)^a は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(ξ)/√N は有限素点の局所定数の積と一致する（値の一致、Lean の外）。明示的な因子 i^{±a} が無限素点の局所定数であることは規約によらないが、符号 ξ(−1) の置き場は規約による（第 4 版で、統合照合の指摘に合わせて言い方を直した）。規約 T を明示せずに「ε(ξ) は無限素点から来る」と書かない。
+2. **規約 T を基礎文書の標準にする。** Mathlib の `stdAddChar` と有限素点の符号が合い、Tate の学位論文の加法指標・Burnol（arXiv:math/9811040。根拠はこの 1 本で、フーリエ変換の核が指標そのものか共役かは書かれていない）とも同じ加法指標。
 
 記録：決定は CLAUDE.md §1 と英語版、材料ノート（第 5 版）の §6 の 4・5、概要の文書、引き継ぎメモに反映した。このノートの第 2 版の照合後の直しは未照合のままで、次の統合照合の対象に含める（決定の根拠にした版が照合後の直しを含むことを、ここに明記する）。第 2 版の §9 の文案は `before_decision_v2.md` に残る。
+
+## §10 統合照合の記録（第 4 版）
+
+- 2026-11-18 夜の統合照合（材料ノート §11、記録 `records/tail_audit2/`）で、このノートの第 1 版→第 3 版の差分も照らされた。式・数値・文献の主張は照合者の検算の範囲で正しかった（Tate の学位論文の走査版の λ(x) = −x とフーリエ変換の核、Roy–Schmidt–Yi の (155)・(156)・(157)、有限素点の積の明示式を N ≤ 60 の原始指標 662 個で確認）。
+- 直したこと：§1 (a) の「（i の冪を含まない）」（値は i を取りうる。例を足し、「明示的な因子 i^{±a}」と言い直した）、Roy–Schmidt–Yi の式 (150) の引き方（§6.1、積の形から導かれる）、Burnol の根拠が 1 本であること、照合者の数値の回数の内訳が未確認であること、§9 の言い方。
+- 後から行った内部照合（§0）：同じ結論が Part 257（PAG261）の記録に読みとして書かれていたことを記録した。
+- 補足 8 の停止の規約：今回の直しは、言い方を正す・根拠の書き方を狭める・記録を足す直しで、数学の主張を強めるものはない（構築側の判断）。
diff --git a/notes/pag2_projection_material.md b/notes/pag2_projection_material.md
index 8f40669..ffa6634 100644
--- a/notes/pag2_projection_material.md
+++ b/notes/pag2_projection_material.md
@@ -1,6 +1,6 @@
 # アーデル射影幾何 — 命名にある「射影」の材料（基礎文書の第 1・2 章のための対応表）
 
-（2026-11-18。短期層の小さいノート。事前登録 `pag2_prereg_projection.md` の結論（残余は空、新しいパートは始めない）を受けて、基礎文書の起草（著者側）に渡す材料をまとめる。**ここに書く「射影」の読みは構築側が出した読みで、2026-11-18 19:01 に著者が留保つきで採用した（§6）。** 採用は読み（解釈の層）としての採用で、形式化済みの定理ではない。著者の定義（CLAUDE.md §1）の文面は変えない。第 1 版と第 2 版がそれぞれ独立照合を受け、その指摘で直した第 3 版に著者の決定を記録したのが第 4 版、文献照合の後の著者の決定を足したのがこの第 5 版である（§7〜§10）。）
+（2026-11-18。短期層の小さいノート。事前登録 `pag2_prereg_projection.md` の結論（残余は空、新しいパートは始めない）を受けて、基礎文書の起草（著者側）に渡す材料をまとめる。**ここに書く「射影」の読みは構築側が出した読みで、2026-11-18 19:01 に著者が留保つきで採用した（§6）。** 採用は読み（解釈の層）としての採用で、形式化済みの定理ではない。著者の定義（CLAUDE.md §1）の文面は変えない。第 1 版と第 2 版がそれぞれ独立照合を受け、その指摘で直した第 3 版に著者の決定を記録したのが第 4 版、文献照合の後の著者の決定を足したのが第 5 版、統合照合の指摘で直したのがこの第 6 版である（§7〜§11）。）
 
 記号：
 - 反転（0 と ∞ の入れ替え、x ↦ 1/x）は **ι** と書く。Lean の宣言 `PAG.Part23.W`・`PAG.Part26.Wpt`・`PAG.Part27.Wproj` とモノグラフの W は、この反転を指す。
@@ -19,7 +19,7 @@
 
 1. **舞台（座標）**：射影直線 P¹。2 つのチャート（0 の側 [x:1] と ∞ の側 [1:y]）が赤道（単数）の上で y ↦ y⁻¹ によってつながり、反転 ι が 0 と ∞ を入れ替える。
 2. **変換（融合）**：乗法の側の反転 ι と、加法の側のフーリエ型の変換を合成した写像。乗法の関数（指標）に作用させる。有限レベル N では、ℤ/N の関数を単数の上の関数に送る写像で、同じ空間の上の作用素ではない（§3 の表 2 行目）。
-3. **位相（公準）**：原始指標 χ については、その変換の成分が絶対値 1 の位相になる。標準の核は Part 252 の Hartley 核とする（著者の決定、§6）。この核での値は 𝔀(χ) = τ(χ)/(i^a √N)（`rootNum`）である。加法指標は規約 T（Tate の学位論文の加法指標：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）を標準とし、その規約で因子 ε(χ) = (−i)^a は無限素点の局所定数と一致する（値の一致、Lean の外。注意 2 の最後の項）。PAG256 の冒頭のコメントの読みでも、公準 A1 は境界ユニタリ U の原始指標の位相をこの値に選ぶ公準である。原始的なら 𝔀(χ) がルート数であることは Lean の外である。素朴なフーリエ核では、奇の χ で値がこの値と i 倍ずれる（注意 2。このずれは標準の核を決めても消えない）。原始的でない指標では、成分は位相でないことがある（絶対値が 1 未満になり、0 にもなる例がある。§3 の表 3 行目）。
+3. **位相（公準）**：原始指標 χ については、その変換の成分が絶対値 1 の位相になる。標準の核は Part 252 の Hartley 核とする（著者の決定、§6）。この核での値は 𝔀(χ) = τ(χ)/(i^a √N)（`PAG.Part256.rootNum`）である。加法指標は規約 T（Tate の学位論文の加法指標：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）を標準とし、その規約で因子 ε(χ) = (−i)^a は無限素点の局所定数と一致する（値の一致、Lean の外。注意 2 の最後の項）。PAG256 の冒頭のコメントの読みでも、公準 A1 は境界ユニタリ U の原始指標の位相をこの値に選ぶ公準である。原始的なら 𝔀(χ) がルート数であることは Lean の外である。素朴なフーリエ核では、奇の χ で値がこの値と i 倍ずれる（注意 2。このずれは標準の核を決めても消えない）。原始的でない指標では、成分は位相でないことがある（絶対値が 1 未満になり、0 にもなる例がある。§3 の表 3 行目）。
 
 注意 1（照合者の指摘）：1 と 2 は種類が違う。1 の y ↦ y⁻¹ はチャートの座標変換（関数を P¹ の上で定義するための恒等式）で、ねじれを持たない。ねじれ（指標ごとの位相）は 2 の変換の側にある。Lean でも、照合した範囲（PAG23・PAG26・PAG27・PAG256）では、2 の写像（`PAG.Part256.JH`）と 1 の 2 チャートモデル（`PAG.Part23.Compat` など）を結ぶ文はない。
 
@@ -28,33 +28,33 @@
   - 導出：`PAG.Part256.hartley_eq_of_isPrimitive` の証明の中の式 `hA`（∑ₓ χ(x) e(xy) = χ⁻¹(y) τ(χ)、`PAG.Part256.sum_mul_stdAddChar` と Mathlib の `gaussSum_mulShift_of_isPrimitive` から）に y = u⁻¹ を入れ、`PAG.Part256.inv_apply_units_inv`（χ⁻¹(u⁻¹) = χ(u)）を使って √N で割ると、(τ(χ)/√N)·χ(u) になる。独立した定理としては Lean に置いていない。
   - 単数の上では原始性は要らない（`PAG.Part256.hartley_units_inv` と同じ置換 x ↦ u·x の議論。照合者が N ≤ 30 のすべての指標で数値確認。数値は証明ではない）。
   - **核の符号に依存する**：核を e(−xy) にすると、成分は χ(−1)τ(χ)/√N になる（`PAG.Part256.hartley_eq_of_isPrimitive` の証明の中の式 `hB`・`hneg` から。y = 1 の場合は `PAG.Part256.sum_mul_stdAddChar_neg`）。「素朴なフーリエ核」は符号の規約を決めるまで一つに決まらない。
-- **Part 252 の離散 Hartley 核**（cas = cos + sin。核は ((1 − i)e(t) + (1 + i)e(−t))/2、`PAG.Part256.casKer_eq`）：成分は 𝔀(χ) = ε(χ)τ(χ)/√N。ε(χ) は `PAG.Part256.parFac` で、偶で 1、奇で −i（`parFac_of_even`・`parFac_of_odd`）。すべての χ について `PAG.Part256.JH_eq_rootNum_mul_any` と `PAG.Part256.rootNum_eq` から出る。式 𝔀(χ) = τ(χ)/(i^a √N) は `rootNum` の定義そのもので、すべての χ で成り立つ。原始的なら 𝔀(χ) がルート数であることは Lean の外（`rootNum` の docstring）。
+- **Part 252 の離散 Hartley 核**（cas = cos + sin。核は ((1 − i)e(t) + (1 + i)e(−t))/2、`PAG.Part256.casKer_eq`）：成分は 𝔀(χ) = ε(χ)τ(χ)/√N。ε(χ) は `PAG.Part256.parFac` で、偶で 1、奇で −i（`PAG.Part256.parFac_of_even`・`PAG.Part256.parFac_of_odd`）。すべての χ について `PAG.Part256.JH_eq_rootNum_mul_any` と `PAG.Part256.rootNum_eq` から出る。式 𝔀(χ) = τ(χ)/(i^a √N) は `PAG.Part256.rootNum` の定義そのもので、すべての χ で成り立つ。原始的なら 𝔀(χ) がルート数であることは Lean の外（`PAG.Part256.rootNum` の docstring）。
 - **二つの関係（e(xy) の規約で）**：偶の χ では一致する（どちらも τ(χ)/√N）。奇の χ では 𝔀(χ) = −i·τ(χ)/√N、すなわち素朴な成分 = i·𝔀(χ)。核を e(−xy) にすると関係は反転し、𝔀(χ) = i·（素朴な成分）になる。
-- **帰属の読み（候補として留保。未確認）**：Tate の局所分解の通常の規約では、ルート数の i^a は無限素点の局所因子から来る（照合者の知識による。確信度：中）。ただし大域の加法指標は無限素点と有限素点とで符号を逆に取るのが通例で、有限素点の局所因子が τ(χ)/√N になるか χ(−1)τ(χ)/√N になるかは規約で変わりうる（再照合者の知識。確信度：低〜中）。この読みが正しければ、Part 252 の Hartley の形は、無限素点の符号の因子を有限レベルの変換に取り込んだ形と読める。著者の決定（§6）により、文献照合が済むまでは i^a を正規化因子として書き、この帰属は候補として留保する。i^a の帰属と有限素点の加法指標の符号の文献照合は、基礎文書が無限素点の読みを断定する前に行う。→ 2026-11-18 に照合した（`pag2_literature_ia_sign.md`、独立照合 1 回）。結果：i の冪は無限素点から来る（規約によらない）。符号 ξ(−1) の置き場は規約による。Tate の学位論文の加法指標の規約（ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）では、ε(χ) = (−i)^a が無限素点の局所定数と、τ(χ)/√N が有限素点の局所定数の積と一致する（値の一致。Lean の外）。同日、著者の決定で、i^a を正規化因子として留保する扱いを外し、規約 T を基礎文書の標準とした（§6 の 4・5）。
+- **帰属の読み（2026-11-18 に文献照合。規約 T での値の一致。留保は著者の決定で外した）**：第 4 版までは、Tate の局所分解の通常の規約では i^a は無限素点の局所因子から来る（照合者の知識、確信度：中）とし、文献照合が済むまで i^a を正規化因子として書き、帰属を候補として留保していた。2026-11-18 に照合した（`pag2_literature_ia_sign.md`、独立照合 1 回。照合後の直しは未照合）。結果（原始的な χ について）：明示的な因子 i^{±a} が無限素点の局所定数であることは、加法指標の規約によらない。符号 χ(−1) の置き場は規約による。大域の加法指標は ℚ の上で自明でなければならないので、無限素点と有限素点で符号を逆に取ることは必然で、選べるのは無限素点の側の符号だけである。Tate の学位論文の加法指標の規約（規約 T：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）では、ε(χ) = (−i)^a が無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N が s = 1/2 での有限素点の局所定数の積と一致する（値の一致。Lean の外）。逆の規約では、無限素点が i^a、有限素点の積が χ(−1)τ(χ)/√N。したがって Part 252 の Hartley の形は、規約 T のもとで、無限素点の局所定数を有限レベルの変換に取り込んだ形と読める。同日、著者の決定で、i^a を正規化因子として留保する扱いを外し、規約 T を基礎文書の標準とした（§6 の 4・5）。なお、同じ同定は Part 257（PAG261）の冒頭の説明とノート `pag2_part257_local_factor_decomposition.md` に読みとして書かれていた（確信度：中〜高）。今回の照合はその確かめ直しにあたる（文献照合ノートの §0）。
 
 ## §3 対応表
 
 | 層 | 有限レベル（ℤ/N） | 無限素点 | ラベル |
 |---|---|---|---|
-| 舞台：射影直線と反転 | P¹(ℤ/N) := 単模ベクトル / 単数倍（Part 23（PAG27）、`PAG.Part27.ProjLine`）。反転 [a:b] ↦ [b:a]（`PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`。一般の N）。p 素数、K ≥ 1 で、点モデル（Part 22（PAG26）、`PAG.Part26.Pt`）と同型（`PAG.Part27.projEquiv`）、点の数 p^K + p^(K−1)（`PAG.Part27.card_ProjLine`）。反転どうしの対応 `PAG.Part27.toProj_Wpt` は K ≥ 1 の仮定なしで述べられている。2 チャートモデルと赤道での貼り合わせ条件 F_N(y) = F_S(y⁻¹)（Part 19（PAG23）、`PAG.Part23.Compat`、反転 `PAG.Part23.W`。点モデルの関数との同型は一般の N で `PAG.Part26.ptEquiv`、反転の対応は `PAG.Part26.toP1_comp_Wpt`）。2 チャートモデル（点モデル）が P¹(ℤ/N) と同型であることが Lean で示されているのは N = p^K（K ≥ 1）だけ。N が 2 つ以上の素因数を持つときは点の数が一致しない（数え上げ：\|Pt N\| = 2N − φ(N)、\|P¹(ℤ/N)\| = N∏_{p\|N}(1 + 1/p)。N = 6 で 10 点と 12 点。この不一致を述べる文は Lean にない）。N ≥ 2 では 0 = [0:1] と ∞ = [1:0] は別の点で、反転がこの 2 点を入れ替える（有限の側に点の同一視はない。この文も Lean にはない。N = 1 では 1 点） | P¹(ℝ)。ℝ_{>0} の対数座標 t = log x で、反転 x ↦ 1/x は t ↦ −t になり、両端 −∞・+∞（乗法の 0・∞）を入れ替える。射影直線では両端が一点（著者確認済みの読み）。有限の側との違い：無限素点では両端が重なる | ［既知］（P¹(ℤ/N) はモジュラー記号の標準の道具、Manin 1972 など。Lean は Part 19〜28） |
+| 舞台：射影直線と反転 | P¹(ℤ/N) := 単模ベクトル / 単数倍（Part 23（PAG27）、`PAG.Part27.ProjLine`）。反転 [a:b] ↦ [b:a]（`PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`。一般の N）。p 素数、K ≥ 1 で、点モデル（Part 22（PAG26）、`PAG.Part26.Pt`）と同型（`PAG.Part27.projEquiv`）、点の数 p^K + p^(K−1)（`PAG.Part27.card_ProjLine`）。反転どうしの対応 `PAG.Part27.toProj_Wpt` は K ≥ 1 の仮定なしで述べられている。2 チャートモデルと赤道での貼り合わせ条件 F_N(y) = F_S(y⁻¹)（Part 19（PAG23）、`PAG.Part23.Compat`、反転 `PAG.Part23.W`。点モデルの関数との同型は一般の N で `PAG.Part26.ptEquiv`、反転の対応は `PAG.Part26.toP1_comp_Wpt`）。点モデルと P¹(ℤ/N) の点集合の全単射（`PAG.Part27.projEquiv`）が Lean で示されているのは N = p^K（K ≥ 1）だけ（2 チャートモデルは関数のモデルで、点モデルの関数の空間と線形同型になる：`PAG.Part26.ptEquiv`、一般の N）。N が 2 つ以上の素因数を持つときは点の数が一致しない（数え上げ：\|Pt N\| = 2N − φ(N)、\|P¹(ℤ/N)\| = N∏_{p\|N}(1 + 1/p)。N = 6 で 10 点と 12 点。この不一致を述べる文は Lean にない）。N ≥ 2 では 0 = [0:1] と ∞ = [1:0] は別の点で、反転がこの 2 点を入れ替える（有限の側に点の同一視はない。この文も Lean にはない。N = 1 では 1 点） | P¹(ℝ)。ℝ_{>0} の対数座標 t = log x で、反転 x ↦ 1/x は t ↦ −t になり、両端 −∞・+∞（乗法の 0・∞）を入れ替える。射影直線では両端が一点（著者確認済みの読み）。有限の側との違い：無限素点では両端が重なる | ［既知］（P¹(ℤ/N) はモジュラー記号の標準の道具、Manin 1972 など。Lean は Part 19〜28） |
 | 変換：反転 ∘ 加法の変換 | J∘H_N/√N（Part 252（PAG256）、`PAG.Part256.JH`。J は単数の上の反転 u ↦ u⁻¹、H_N は離散 Hartley 変換）。ℤ/N の関数を単数の上の関数に送る写像で、同じ空間の上の作用素ではない。素朴なフーリエ核での形は §2 の注意 2 | モノグラフ層の境界ユニタリ U（イデール類群の上の反転と、境界条件）。Lean にしていない | ［再導出］（PAG256 の冒頭のコメントの記載どおり「既知の事実の書き直し」。Tate 1950 の局所関数等式の有限版と読む） |
-| 位相：原始指標の成分 | すべての指標 χ と単数 u で (J H_N χ)(u)/√N = 𝔀(χ)·χ(u)（`PAG.Part256.JH_eq_rootNum_mul_any`）。原始的なら \|𝔀(χ)\| = 1（`PAG.Part256.normSq_rootNum`）。原始的なら 𝔀(χ) がルート数であることは Lean の外（`rootNum` の docstring）。原始的でない指標では位相でないことがある：法 2 の自明な指標（原始的でないことは `PAG.Part256.removal_counterexample` の第 1 成分）で \|𝔀\|² = 1/2（`PAG.Part256.removal_counterexample_normSq`）、法 4 の自明な指標で 0（`PAG.Part256.removal_counterexample_four`）。原始的でない指標すべてで位相でないという全称の文は Lean の外（照合者の数値では N ≤ 30 のすべての非原始指標で \|𝔀\| ≤ 1/√2。数値は証明ではない） | Tate の γ 因子（ガンマ因子の比）。公準 A1 は U の位相をこの値（λ = 0 での値）に選ぶ。両立の分類は定理 2.6 | ［既知］（Tate 1950、Burnol 1998〜2001）。A1 は公準のまま |
+| 位相：原始指標の成分 | すべての指標 χ と単数 u で (J H_N χ)(u)/√N = 𝔀(χ)·χ(u)（`PAG.Part256.JH_eq_rootNum_mul_any`）。原始的なら \|𝔀(χ)\| = 1（`PAG.Part256.normSq_rootNum`）。原始的なら 𝔀(χ) がルート数であることは Lean の外（`PAG.Part256.rootNum` の docstring）。原始的でない指標では位相でないことがある：法 2 の自明な指標（原始的でないことは `PAG.Part256.removal_counterexample` の第 1 成分）で \|𝔀\|² = 1/2（`PAG.Part256.removal_counterexample_normSq`）、法 4 の自明な指標で 0（`PAG.Part256.removal_counterexample_four`）。原始的でない指標すべてで位相でないという全称の文は Lean の外（照合者の数値では N ≤ 30 のすべての非原始指標で \|𝔀\| ≤ 1/√2。数値は証明ではない） | Tate の γ 因子（ガンマ因子の比）。公準 A1 は U の位相をこの値（λ = 0 での値）に選ぶ。両立の分類は定理 2.6 | ［既知］（Tate 1950、Burnol 1998〜2001）。A1 は公準のまま |
 
 ## §4 Lean にしていないこと・確かめていないこと
 
-- P¹ と点モデルの同型は N = p^K（K ≥ 1）だけ。一般の N では、`PAG.Part27.ProjLine` の定義と反転（`PAG.Part27.Wproj`・`PAG.Part27.Wproj_Wproj`）が示されている（`PAG.Part27.mk_eq_mk` は単数倍で同じ点になることを言う補題で、反転がうまく定義されることを示すのに使われる。反転の文ではない）。点モデル `PAG.Part26.Pt N` と P¹(ℤ/N) が N に 2 つ以上の素因数があるとき一致しないことは、数え上げによるもので Lean の文ではない。全素点の制限積 P¹(𝔸_ℚ) = ∏'_v P¹(ℚ_v) と、P¹(ℤ_p) = lim P¹(ℤ/p^K) は Lean にしていない。
+- P¹ と点モデルの同型が Lean で示されているのは N = p^K（K ≥ 1）だけ（N = 1 では両方とも 1 点）。一般の N では、`PAG.Part27.ProjLine` の定義と反転（`PAG.Part27.Wproj`・`PAG.Part27.Wproj_Wproj`）が示されている（`PAG.Part27.mk_eq_mk` は単数倍で同じ点になることを言う補題で、反転がうまく定義されることを示すのに使われる。反転の文ではない）。点モデル `PAG.Part26.Pt N` と P¹(ℤ/N) が N に 2 つ以上の素因数があるとき一致しないことは、数え上げによるもので Lean の文ではない。全素点の制限積 P¹(𝔸_ℚ) = ∏'_v P¹(ℚ_v) と、P¹(ℤ_p) = lim P¹(ℤ/p^K) は Lean にしていない。
 - 境界ユニタリ U と公準 A1 は、照合した範囲（Part 19・22・23・252、すなわち PAG23・PAG26・PAG27・PAG256）では Lean の形式文に出てこない（PAG256 の冒頭のコメントも「U と A1 は Lean の文に出てこない」と書く）。鎖全体については検索していない。Tate の局所関数等式そのもの、定理 2.6 も Lean にしていない（定理 2.6 の条件を A1 の位相が満たすことは PAG16・PAG173・PAG198 の 3 定理から出る、と CLAUDE.md §3 に記録あり。組み合わせた 1 つの文は未形式化）。
-- 「射影 = 舞台の P¹ と、反転 ∘ 加法の変換」は読み（2026-11-18 に著者が採用）であり、Lean の文ではない。Part 252 の J∘H_N を「変換の層の有限版」と呼ぶのも読みである。PAG256 の言葉では、`JH_eq_rootNum_mul` の docstring は「構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。U と A1 は文に出てこない）」、冒頭のコメント（`/-` で始まる通常のコメントで、docstring ではない）の読みは「公理 A1 の境界ユニタリの原始指標の部分」である。PAG256 の形式文には貼り合わせに当たる対象は出てこない。冒頭のコメントでは、重なりの読み「ねじれた貼り合わせ（U）」と、構築者が再構成した主張「U = J∘H_N/√N」を通して、間接に結びつけられている。PAG23・PAG26 の「貼り合わせ条件」は 2 チャートモデルの条件（`PAG.Part23.Compat`）である。
+- 「射影 = 舞台の P¹ と、反転 ∘ 加法の変換」は読み（2026-11-18 に著者が採用）であり、Lean の文ではない。Part 252 の J∘H_N を「変換の層の有限版」と呼ぶのも読みである。PAG256 の言葉では、`PAG.Part256.JH_eq_rootNum_mul` の docstring は「構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。U と A1 は文に出てこない）」、冒頭のコメント（`/-` で始まる通常のコメントで、docstring ではない）の読みは「公理 A1 の境界ユニタリの原始指標の部分」である。PAG256 の形式文には貼り合わせに当たる対象は出てこない。冒頭のコメントでは、重なりの読み「ねじれた貼り合わせ（U）」と、構築者が再構成した主張「A1 のもとで U = J∘H_N/√N」を通して、間接に結びつけられている。PAG23・PAG26 の「貼り合わせ条件」は 2 チャートモデルの条件（`PAG.Part23.Compat`）である。
 - 照合した範囲では、`PAG.Part256.JH` と 2 チャートモデル（`PAG.Part23.P1F`・`PAG.Part23.Compat`・`PAG.Part23.W`）・`PAG.Part27.ProjLine` を結ぶ Lean の文はない。§2 の 2 の変換が「0 の側と ∞ の側をつなぐ」に対応する Lean の文もない。
-- ルート数の i^a の帰属と、有限素点の加法指標の符号の規約（§2 の注意 2）は文献で未確認。
+- ルート数の i^a の帰属と、有限素点の加法指標の符号の規約（§2 の注意 2）は、2026-11-18 に文献で照合した（`pag2_literature_ia_sign.md`、独立照合 1 回、照合後の直しは未照合）。規約 T での値の一致であり、Lean の外。
 - 盲検の問いテストで、全素点を通して「各素点の 0 と ∞ の貼り合わせ」を一つの構成として書いた文献は見つからなかった（MathSciNet・zbMATH は未照合）。部品はすべて既知。
 
 ## §5 対照群（§7）
 
 - 関数体 𝔽_q(t) でも Tate の局所関数等式は同じ形で成り立つ（Lean の外の既知の事実）。§2 の 2 の変換の形と、§2 の 3 のうちガウス和 τ(χ)/√N の部分は、ℚ に固有の算術を使わない形式の文である。
-- ただし §2 の 3 で Hartley 核を採ると（PAG256 の冒頭の読み）、値 𝔀(χ) は偶奇による因子 ε(χ)（χ(−1) で決まる）を含む。注意 2 の帰属の読みが正しければ、この因子は無限素点の側（ℚ に固有の側）に属する。関数体での対応物は確かめていない。
+- ただし §2 の 3 で Hartley 核を採ると（PAG256 の冒頭の読み。著者の決定で標準）、値 𝔀(χ) は偶奇による因子 ε(χ)（χ(−1) で決まる）を含む。規約 T のもとで、ε(χ) は無限素点の局所定数と値が一致する（Lean の外）。i^{±a} の部分は規約によらず、符号は規約による。関数体での対応物は確かめていない（Part 257 のノートは盲検の答えとして、𝔽_q[t] の ∞ の因子を偶で 1、奇で √q/τ(η) と記録している。構築側は計算していない）。
 - 関数体では、t ↦ 1/t が素点 0 と素点 ∞ を入れ替える。ただしこの P¹_{𝔽_q} は「点が素点であるような大域の曲線」で、§2 の 1 の「各素点の座標の直線」とは別の対象である（照合者の指摘）。
-- ℚ に固有に残るのは、無限素点がアルキメデス的で、実数の順序（符号）と二つの端 ±∞ があることである（「−∞ と ∞」の重なり）。上の ε(χ) の因子も、読みが正しければここに属する。
+- ℚ に固有に残るのは、無限素点がアルキメデス的で、実数の順序（符号）と二つの端 ±∞ があることである（「−∞ と ∞」の重なり）。上の ε(χ) の因子（規約 T での無限素点の局所定数）がこの側に属するかは、関数体での対応物を確かめていないので未確認（確信度：低〜中）。
 
 ## §6 著者の決定（2026-11-18 19:01）
 
@@ -69,12 +69,14 @@
 文献照合（`pag2_literature_ia_sign.md`）の後、2026-11-18 19:25 に著者が次の 2 つを決めた（照合ノート §9 の 1・2 を「進める」）。
 
 4. **i^a の留保を外す。** CLAUDE.md §1 の「i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する」を、規約を明示した書き方に置き換える：規約 T のもとで ε(χ) = (−i)^a は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N は有限素点の局所定数の積と一致する（値の一致、Lean の外）。i の冪が無限素点から来ることは規約によらないが、符号 χ(−1) の置き場は規約による。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
-5. **規約 T を基礎文書の標準にする。** Mathlib の `stdAddChar` と有限素点の符号が合い、Tate の学位論文の加法指標・Burnol とも同じ規約。
+5. **規約 T を基礎文書の標準にする。** Mathlib の `stdAddChar` と有限素点の符号が合い、Tate の学位論文の加法指標・Burnol（arXiv:math/9811040）とも同じ加法指標。
+
+注（2026-11-18 の統合照合の指摘）：2 の著者の言葉は「その上で働く**貼り合わせの合成**を射影と呼ぶ」である。CLAUDE.md §1 と概要では、構築側がこれを断りなく「反転（乗法の側）と加法の変換（加法の側）の合成」と言い換えていた。第 6 版の反映で、著者の言葉と構築側の言い換えを書き分けた。「貼り合わせ」が PAG23 の `PAG.Part23.Compat`（ねじれのない座標の貼り合わせ）と U（ねじれた貼り合わせ）のどちらを指すかは、著者に確かめる。構築側の読みは後者で、U の原始指標の位相が変換の成分である。
 
 ## §7 照合の記録（第 1 回）
 
 - 第 1 版（`before_material_v1.md`）を、形式文の全文（PAG23・PAG26・PAG27・PAG256）を渡した新しい照合者が照らした（依頼文 `outputs/material_check_request.md`、出力 `outputs/material_check_output.md`、所要 約 6 分）。
-- 主な指摘と直し：原始性の限定の抜け（§2 の 3、表 3 行目）、素朴なフーリエ核と Hartley 核の取り違え（§2 の注意 2 を新設）、`JH_eq_rootNum_mul` を「ルート数」の根拠にした当て方（外した）、番号と名前空間の取り違えの罠（完全修飾名にした。ただし第 2 版では一部だけで、第 3 版で残りを直した。§8）、K ≥ 1 の抜け、2 チャートモデルが P¹ になる範囲、一般の N の `ProjLine` の記述、docstring の引用の但し書き、`JH` と 2 チャートモデルを結ぶ文がないこと、「無限素点の U」の書き方、記号 W の衝突（ι と 𝔀 に分けた）、有限と無限の対応のずれ、表 2 行目のラベル（［再導出］にそろえた）。
+- 主な指摘と直し：原始性の限定の抜け（§2 の 3、表 3 行目）、素朴なフーリエ核と Hartley 核の取り違え（§2 の注意 2 を新設）、`JH_eq_rootNum_mul` を「ルート数」の根拠にした当て方（外した）、番号と名前空間の取り違えの罠（完全修飾名にした。第 2 版では一部だけで、第 3 版で残りを直したとしていたが、統合照合で `rootNum`・`JH_eq_rootNum_mul`・`parFac_of_even`・`parFac_of_odd` が残っていると指摘され、第 6 版で直した。§11）、K ≥ 1 の抜け、2 チャートモデルが P¹ になる範囲、一般の N の `ProjLine` の記述、docstring の引用の但し書き、`JH` と 2 チャートモデルを結ぶ文がないこと、「無限素点の U」の書き方、記号 W の衝突（ι と 𝔀 に分けた）、有限と無限の対応のずれ、表 2 行目のラベル（［再導出］にそろえた）。
 
 ## §8 照合の記録（第 2 回：直した版の再照合）
 
@@ -82,21 +84,21 @@
 - 結論：第 2 版で新しく入った明確な誤りが 1 件（§4 の「「貼り合わせ」という語は Lean の側にはない」。PAG256 の冒頭のコメントと PAG23・PAG26 に語がある）。言い過ぎと曖昧さがいくつか。宣言名・完全修飾名・式はほかは一致。
 - 直したこと（照合者の指摘 1〜9 の順）：
   1. §4 の「貼り合わせ」の文を、照合者の直し案のとおりに差し替えた。
-  2. 注意 2 を式で書いた（奇の χ で 𝔀 = −i·τ/√N、素朴な成分 = i·𝔀）。核の符号への依存（e(−xy) で χ(−1)τ/√N、関係の反転）を明記し、§6 の 3 にも規約を添えた。文献照合の項目に有限素点の加法指標の符号を加えた。
+  2. 注意 2 を式で書いた（奇の χ で 𝔀 = −i·τ/√N、素朴な成分 = i·𝔀）。核の符号への依存（e(−xy) で χ(−1)τ/√N、関係の反転）を明記し、当時の §6 の 3（判断の依頼。現在の §6 は決定の記録）にも規約を添えた。文献照合の項目に有限素点の加法指標の符号を加えた。
   3. 表 3 行目を「位相でないことがある」に弱め、全称の文は Lean の外と断った。法 2 の非原始性の根拠に `removal_counterexample` を足した。
   4. 注意 2 と記号の行で、`rootNum` の定義（すべての χ）とルート数との同定（Lean の外）を書き分け、根拠に `JH_eq_rootNum_mul_any`・`rootNum_eq` を引いた。
   5. §2 の 3 の「この値」を、PAG256 の冒頭の読みの値 𝔀(χ)（Hartley 側）と特定し、素朴な核では奇の χ でずれることを書いた。
-  6. 記号の行と §3・§4 の宣言名を完全修飾名にし、PAG256 の W(χ) が 𝔀 を指すことを注記した。
+  6. 記号の行と §3・§4 の宣言名を完全修飾名にし、PAG256 の W(χ) が 𝔀 を指すことを注記した（第 6 版の注：修飾されていない名前が残っていた。§11）。
   7. §4 の U と A1 の文の範囲を「照合した範囲（PAG23・PAG26・PAG27・PAG256）」に狭めた。注意 1 と §4 の「結ぶ文はない」も同じ範囲に狭めた。
   8. 注意 2 の素朴な核の項に、`inv_apply_units_inv` が要ることと、単数の上では原始性が要らないことを書いた。
   9. 軽微な点：「のときだけ」を「Lean で示されているのは N = p^K だけ」と「2 つ以上の素因数で点の数が一致しない」に分け、「0 と ∞ は別の点」に N ≥ 2 を付けた。`toProj_Wpt` は K ≥ 1 なしと書いた。`mk_eq_mk` を反転の補題から外した。「有限素点の作用素」を「有限レベル N の変換」に、§2 の 2 の「作用素」を「変換（写像）」にそろえた。PAG256 の冒頭は通常のコメントと書いた。§5 の第 1 項と第 3 項の張り合いを、ε(χ) の因子を分けて書くことで解いた。
-- この第 3 版は、第 2 回の照合の後の直しを照合にかけていない。直しはすべて、照合者が示した直し案に沿った言い換えと主張の範囲を狭める直しで、新しい主張は加えていない（構築側の判断。補足 8 の停止の規約の「主張を変えない直し」に当たると読む）。§5 の第 2 項（ε(χ) の因子の帰属）は張り合いの解消のために書き足した文で、注意 2 の未確認の読みに条件づけてある。この判断が妥当かどうかは、次の統合照合で確かめる対象とする。
+- この第 3 版は、第 2 回の照合の後の直しを照合にかけていない。直しはすべて、照合者が示した直し案に沿った言い換えと主張の範囲を狭める直しで、新しい主張は加えていない（構築側の判断。第 6 版の注：統合照合の指摘では字義どおりではなく、点の数の式 2N − φ(N)・N∏(1 + 1/p)、N ≤ 30 の数値、符号の規約についての再照合者の知識が新しく入っていた。照合者の検算ではどれも正しい。補足 8 の停止の規約の「主張を変えない直し」に当たると読む）。§5 の第 2 項（ε(χ) の因子の帰属）は張り合いの解消のために書き足した文で、注意 2 の未確認の読みに条件づけてある。この判断が妥当かどうかは、次の統合照合で確かめる対象とする。
 
 ## §9 著者の決定の記録（第 4 版）
 
 - 第 3 版（`before_material_v3.md`）に、著者の決定（2026-11-18 19:01、§6）を記録した。直したところ：冒頭の地位の文（「著者の確認待ち」→「留保つきで採用」）、§2 の見出しと命名の決定（両方を指し、主は変換）、§2 の 3（標準の核を Hartley 核とし、i^a を正規化因子として書く。ルート数であることは Lean の外。奇の χ での i 倍のずれは消えない）、注意 2 の帰属の読み（候補として留保、文献照合は基礎文書が無限素点の読みを断定する前）、§4 の第 3 項（読みが採用されたこと）、§6（判断の依頼を決定の記録に置き換えた）。
 - これらは著者の決定の記録で、Lean についての主張は変えていない。照合にはかけていない（補足 8 の「主張を変えない直し」に当たると読む。次の統合照合の対象に含める）。
-- 著者側の記録に戻すための文案を次に置いた。CLAUDE.md §1 への追記は、2026-11-18 19:03 の著者の指示で、CLAUDE.md と英語版 CLAUDE.en.md の §1（命題 3 の置き方の次の箇条）に反映した。反映の際に文案へ足したもの：命名の意味（2026-11-16）、Part と PAG の番号の併記（§7 の (iv)）、PAG256 の docstring の記号 W(χ) が反転の W とは別であることの注記、「明記すること」の一句。照合リストは著者側のもので、構築側では変えていない。
+- 著者側の記録に戻すための文案を次に置いた。CLAUDE.md §1 への追記は、2026-11-18 19:03 の著者の指示で、CLAUDE.md と英語版 CLAUDE.en.md の §1（命題 3 の置き方の次の箇条）に反映した。反映の際に文案へ足したもの：命名の意味（2026-11-16）、Part と PAG の番号の併記（CLAUDE.md §7 の (iv)）、PAG256 の docstring の記号 W(χ) が反転の W とは別であることの注記、「明記すること」の一句（統合照合の指摘で列挙を補う：「留保つき」の語、「（有限レベルでは…J∘H_N/√N）」の括弧、𝔀 の記号を使わないこと、も 19:03 の反映で文案から変えた）。照合リストは著者側のもので、構築側では変えていない。
 
 **CLAUDE.md §1 への追記の文案**（解釈の層の箇条として）：
 
@@ -108,6 +110,14 @@
 
 ## §10 文献照合の後の著者の決定の記録（第 5 版）
 
-- 第 4 版（`before_material_v4.md`）に、文献照合の結果と 2026-11-18 19:25 の著者の決定（§6 の 4・5）を記録した。直したところ：冒頭の版の文、§2 の 3（i^a を正規化因子として書く扱いを、規約 T での無限素点の局所定数との一致に置き換えた）、注意 2 の帰属の読み（照合の結果と決定を追記）、§6（4・5 を追加）。
+- 第 4 版（`before_material_v4.md`）に、文献照合の結果と 2026-11-18 19:25 の著者の決定（§6 の 4・5）を記録した。直したところ：冒頭の版の文、§2 の 3（i^a を正規化因子として書く扱いを、規約 T での無限素点の局所定数との一致に置き換えた）、注意 2 の帰属の読み（照合の結果と決定を追記）、§6（4・5 を追加）。§4 の第 4 項と注意 2 の見出しは直し忘れていた（第 6 版で直した。§11）。
 - 決定は CLAUDE.md §1 と英語版にも反映した。
 - これらは著者の決定と照合の結果の記録で、Lean についての主張は変えていない。照合にはかけていない（次の統合照合の対象に含める）。根拠にした文献照合ノートの第 2 版も、照合後の直しが未照合である。
+
+## §11 統合照合の記録（第 6 版）
+
+- 2026-11-18 夜、前回の照合の後に入った変更（この材料ノートの第 2 版→第 5 版、文献照合ノートの第 1 版→第 3 版、CLAUDE.md と英語版の §1 の箇条、概要の日英の行、引き継ぎメモの行）を、差分・現行の全文・形式文の全文（PAG23・PAG26・PAG27・PAG256）を渡した新しい照合者 1 人が照らした（入力 `input_tail2.md`、依頼文 `request.md`、出力 `outputs/T2_output.md`、所要 約 9.6 分。記録は `records/tail_audit2/`）。
+- 結論：足した・変えた式は、照合者の検算の範囲ですべて正しい。問題は記録の側：このノートの中の直し忘れ 2 か所（§4 の第 4 項、注意 2 の見出し）、CLAUDE.md と概要に移すときに落ちた限定（原始性、s = 1/2、JH は P¹ の上の作用素ではないこと）、地位の書き分け（「A1 の内容と揃う」が事実として書かれている、など）、版の参照のずれ。
+- このノートで直したこと：§4 の第 4 項と注意 2 の見出し（照合済みと書いた）、注意 2 の帰属の読み（原始性、s = 1/2、「通例」→「ℚ の上で自明であるため必然」、Part 257 の記録への参照）、表 1 行目（点集合の全単射と関数の同型を分けた）、§4 の第 1 項（N = 1）、§4 の第 3 項（「A1 のもとで」）、§5 の第 2・第 4 項（規約 T を明示し、「ℚ に固有」を未確認とした）、§6 の後の注（著者の言葉「貼り合わせの合成」と構築側の言い換え）、修飾されていない名前の修飾、§7〜§10 の記録の事実との不一致。
+- 同じ指摘で、CLAUDE.md と英語版、概要の日英、文献照合ノート、引き継ぎメモも直した（各ファイルの記録を参照）。
+- 補足 8 の停止の規約：今回の直しは、限定を足す・地位を書き分ける・記録を事実に合わせる直しで、数学の主張を強めるものはない（構築側の判断）。新しく足した記録の文（Part 257 の記録への参照）は鎖の検索で確かめた事実で、引用した行は文献照合ノートの §0 にある。
```

## §B 変更後の全文

### notes/pag2_founding_material_index.md

# アーデル射影幾何 — 基礎文書の材料索引（骨格の 6 章ごと）

（2026-11-18。短期層の作業。新しいパートではない。基礎文書の骨格（著者側、2026-11-15。以下「骨格」）の章ごとに、書く主張・その地位・支える Lean の宣言・ノート・照合の状態・開いている点を並べる。起草は著者側で行う。この索引は主張を足さない。地位とラベルは各ノート・CLAUDE.md・骨格の記載を写したもので、写すときに強めないことを方針とした。第 1 版を独立照合にかけ、その指摘で直した第 2 版がこれである（§8）。）

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
  - 可換性を外した反例：`PAG.Part253.thm26_needs_commute`。
- 留保：
  - 逆向き (b)⇒(a) は数値のみ。大域の Ẑ^× での形は Lean の外。
  - 証明は Dirichlet の算術級数定理を使わない簡略化で、新しい定理ではない。
- ノート：`pag2_part249_idele_class_density.md`。

**2.3 公準 A1（内容は Tate の定理）と、定理 2.6 との両立。**
- 地位：
  - A1 は公準（解釈の層の公準）で、導かれていない。
  - 両立は「既知の結果からの短い帰結」（確信度：高）。これはかつての新規候補 2 で、2026-11-12 に候補から外れた。
- 留保：
  - 両立は、定義から自明な 𝔀(χ̄) = conj 𝔀(χ)（境界ユニタリの実性 KUK = U）から出る。A1 の算術の内容は、どの位相 α を選ぶかの部分だけ（`pag2_thm26_A1_collation.md` §11 の訂正）。
  - ルート数が条件を満たすことは整合性の確認にすぎず、A1 を導いたことにはならない。
  - 近い先行：Burnol、Ibort–Lledó–Pérez-Pardo の例 7.1・7.2（CLAUDE.md §3）。
- Lean：
  - ガウス和の側の部品の 3 定理（組み合わせた 1 つの文は形式化していない）：`PAG.Part16.normSq_gaussSum`、`PAG.Part173.gauss_inv_pair`、`PAG.Part198.gauss_sign_real`。番号の対応は推定で、PAG16 は Part 12、PAG173 は Part 169、PAG198 は Part 194。
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
  - 著者の言葉は「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」。「反転と加法の変換の合成」は構築側の言い換え。
  - 「貼り合わせ」が `PAG.Part23.Compat`（ねじれのない座標の貼り合わせ）と U のどちらを指すかは、著者の確認待ち（構築側の読みは U）。
  - 標準の核は Hartley 核（著者の決定）。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは照合していない（JH_N の正規化も本文で確かめていない）。
- Lean（Part 252（PAG256）、［再導出］）：
  - 写像 `PAG.Part256.JH`、値 `PAG.Part256.rootNum`（= 𝔀）、偶奇の因子 `PAG.Part256.parFac`。
  - すべての指標で、単数の上の式：`PAG.Part256.JH_eq_rootNum_mul_any`。
  - 原始指標で絶対値 1：`PAG.Part256.normSq_rootNum`。
  - 原始指標で単数の外に漏れない：`PAG.Part256.hartley_eq_zero_of_not_isUnit`。
  - 原始性を外した反例：`PAG.Part256.removal_counterexample`・`PAG.Part256.removal_counterexample_normSq`・`PAG.Part256.removal_counterexample_four`。
- 留保：
  - `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。P¹ のモデルと結ぶ Lean の文はない。
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

**2.7 τ と 𝔀 の、互いに素な法の成分・素数冪の成分による分解（交差項・符号つき。値のレベル）。**
- 地位：定理［既知（再導出）］（Part 256（PAG260）・Part 257（PAG261））。恒等式は原始性を使わない（原始的でない指標では 𝔀 は位相でない）。
- Lean：
  - 互いに素な 2 つの法：`PAG.Part260.rootNum_prodChar`・`PAG.Part260.parFac_prodChar`・`PAG.Part260.crossSign`。
  - 互いに素な法の並び：`PAG.Part261.rootNum_listChar_formII`・`PAG.Part261.parFac_listChar`。
  - 成分への分解とその一意性：`PAG.Part261.exists_listChar`・`PAG.Part261.listChar_injective`（並びの形で言う。法 n の形での一意性は文にしていない）。
  - すべての素数への τ の分解：`PAG.Part261.gaussSum_primeFactors`（τ の文で、𝔀 の文ではない）。
- Lean の外：
  - 原始指標で s = 1/2 のとき、形 (II) の素数ごとの因子は Tate の局所定数と、`parFac` は無限素点の局所定数 (−i)^a と値が一致する（読み）。
  - この一致には、加法指標の規約 T と、イデール類指標の正規化 ω_q(q) = χ(q) の両方が要る。ω を χ̄ に対応させる規約では、積は 𝔀 の共役になる。
  - Part 257 で読みとして記録した（確信度：中〜高）ものを、2026-11-18 の文献照合で確かめ直した。
  - 「局所因子」という語は読み。
- ノート：`pag2_part256_gluing_cross_term.md`、`pag2_part257_local_factor_decomposition.md`、`pag2_literature_ia_sign.md`。

**2.8 加法指標の規約は規約 T（Tate の学位論文の加法指標：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）。**
- 地位：著者の決定（2026-11-18 19:25）。基礎文書の標準とする。
- 書き方の規則：
  - 明示的な因子 i^{±a} が無限素点の局所定数であることは、規約によらない。
  - 符号 χ(−1) の置き場は規約による。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
  - 局所定数との一致を書くときは、イデール類指標の正規化（2.7）も併記する。
- ノート：`pag2_literature_ia_sign.md`、CLAUDE.md §1。

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
  - 定式化は Claude の案 1・2 を、著者が 2026-11-11 に了承したもの（著者の定義そのものではない）。
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
  - 守備範囲：ℚ_{>0} を基礎にすると、∞ を測るどの有限の解像度でも像は稠密になる。離散の側は、有限の基礎 ⟨S⟩ でだけ起こる。
  - 二分法を 1 つの文にはしていない。直極限の位相と `BoxCoord` の同一視は Lean の外。
  - 閉包に現れる直線は、読みとしては解像度が落ちた印（08:41 の定義）。その直線が無限素点の座標であること、および対照群 𝔽_q(t) で直線が現れないこと（ノルムの像は q^ℤ）は、骨格の記述で、Lean の外。
- ノート：`pag2_part255_resolution_discrete_limit.md`。

## 第 5 章　有限レベルの代数の組み立て（設計についての定理 2）

**5.1 Part 258 の二分法：N ∣ M のとき、(i) 引き戻しと両立し、(ii) 殻を混ぜない（強い読み）単位的な代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、そのときに限る。**
- 地位：定理。
  - 存在の側（テンソル積）は［既知］（Hanaki–Kim–Maekawa の直積の定理。構築側は文献を開いていない。確信度：中〜高）。
  - 不存在の側は［新規候補（小さい）］（確信度：低〜中。2026-11-15 の著者側の判断）。
- Lean（Part 258（PAG262））：
  - 二分法：`PAG.Part262.exists_compatible_hom_iff`。
  - 存在 `PAG.Part262.exists_compatible_hom`、その写像 `PAG.Part262.shellLift`。
  - 不存在：`PAG.Part262.no_compatible_hom`。
- 留保：
  - 条件の番号に注意。殻を混ぜない条件は、PAG262 の docstring・Part 259・CLAUDE.md §2 の番号では (ii)、Part 258 のノートでは (3)。強い読みは、Part 258 のノートでは「構築者の読みで、著者に確かめる事項」。CLAUDE.md §2 は「登録の読み」と書いている。
  - 答えの範囲の外：弱い読み、単位元を保たない写像、両立条件を別の形にした写像。
  - 対照群（盲検の申告で、未確認）の結果から、アーデル射影幾何に固有の内容としては数えない（Part 258 のノート）。
  - 文献照合（MathSciNet・zbMATH と、Hanaki–Kim–Maekawa・Bastian–Humphries の本文）が済むまで、外部で新規性として使わない。
- ノート：`pag2_part258_beta_premise.md`、CLAUDE.md §3。

**5.2 Part 259：フーリエとの両立を足した一意性と、帰納系の添字。**
- 地位：定理。
  - 順序の性質は［既知］（ユニタリ約数、E. Cohen 1960）。
  - 一意性・非一意性・帰納系は［再導出（小さい）］。
- Lean（Part 259（PAG263））：
  - (i)(ii)(iii)（(iii) はフーリエとの両立）を満たす写像がちょうど 1 つある ⇔ gcd(N, M/N) = 1：`PAG.Part263.existsUnique_compatF_iff`。その写像の特定：`PAG.Part263.compatF_iff_eq_shellLift`。
  - (iii) を外すと一意でない場合がある：`PAG.Part263.not_existsUnique_compat`。Lean にあるのは、A_2 → A_{2b}（b > 1 は奇数）で捩れた写像 `PAG.Part263.twLift` がある場合だけ。
  - 標準の写像 `PAG.Part263.canon` は合成と両立する：`PAG.Part263.canon_comp`。
  - 添字の関係 `PAG.Part263.UDvd` は有向でない：`PAG.Part263.not_isDirected_udvd`。これは Part 216（PAG220）の `PAG.Part220.InLayer` と同じ概念。
  - 無平方数の部分系の極限 `PAG.Part263.sqLim`。各段は単射で入る：`PAG.Part263.sqLim_of_injective`。
- 留保（Part 259 §2 の「併記する必要がある 3 点」と、その他）：
  - 無平方数の系は、極大な有向部分系のうち指数がすべて 1 の場合にすぎず、A_{p^k}（k ≥ 2）を含まない。
  - `sqLim` は ℂ 加群で、代数の構造と制限テンソル積との同型は Lean の外。
  - どの有向な部分系も、整除の順序で共終でない。したがって関数のレベルの極限 ℂ[ℚ/ℤ]（5.3）の代数版にはならない（初等的。Lean にしていない）。
  - a が奇数のときの一意性は、数値のみ。
  - gcd ≠ 1 で (i) と D の側だけを満たす写像があるかは、未確認（小さい数値では見つからなかった。証明ではない）。
- ノート：`pag2_part259_unitary_step_maps.md`、`pag2_R1_assessment.md`。

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
  - 「Ẑ 上の定理 A」は、CLAUDE.md §0 で未完の大域の問いに数えられている。
- ノート：引き継ぎメモの項目 18・23。

**5.4 互いに素な段のテンソル積。**
- 地位：定理［既知］（直積スキームの一般定理 T(A×B) ≅ T(A)⊗T(B) の特別な場合）。
- Lean：
  - Part 228（PAG232）：`PAG.Part232.shellAlgTensorEquiv`、`PAG.Part232.leftHom`、`PAG.Part232.tensLift_injective`、`PAG.Part232.range_tensLift`。
  - Part 236（PAG240）：
    - 局所作用素 `PAG.Part240.locHom`。
    - 一般の族の文 `PAG.Part240.tensEquiv`（A_N に当てるには `PAG.Part240.crtMul_shellAlg`）。
    - 素数冪への分解 `PAG.Part240.ppEquiv`。
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
  - CLAUDE.md §3 は Part 246–248 と書くが、項目 66 の宣言は PAG249（Part 245）にあるので、範囲は Part 245〜248（PAG249〜PAG252）と読める。
  - 項目 66：`PAG.Part249.sumSub_eq_shellAlg_iff`。項目 68：`PAG.Part251.addEAlg_one_eq_shellAlg_iff`。完全な分類：`PAG.Part252.addEAlg_eq_shellAlg_iff_all`。
  - 新規候補として残る範囲は合成数の N（確信度：中）。評価は「小さいノートの水準」。
  - MathSciNet・zbMATH は未実施。ノートの言葉では「著者側か専門家への照会」をお願いしている。
  - ノート：`pag2_candidate1_generation_collation.md`、CLAUDE.md §3。
- 候補 3：Part 258 の不存在の側（5.1）。骨格は、その文献照合（MathSciNet・zbMATH）を著者自身の作業としている。
- かつての候補 2（定理 2.6 の提示形）は候補から外れた（2.3）。

**6.3 Bost–Connes との接続。**
- 地位（骨格の記述）：関数のレベルでは既知。T(0) の側に届くかは、方向 γ の文献照合の結果による。γ の文献照合は著者側の作業（CLAUDE.md §2）。
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

- **著者の確認待ち**：
  - 「貼り合わせの合成」の貼り合わせは、`Compat` と U のどちらか（2.4）。
  - Part 258 の殻を混ぜない条件の強い読み（5.1）。
- **著者側の作業**（担当は骨格と CLAUDE.md §2 の記載による）：
  - 方向 γ の文献照合（6.3）。
  - 候補 3 の文献照合（5.1）。
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
- **定式化の問い**：
  - 解像度の操作に、L1 を超える定式化が要るか。骨格の記述では、現時点では L1 と 08:41 の定義で文書は書ける。
  - 「射影」の、全素点を通した一つの構成（空間と作用素のレベル）としての定式化。値のレベルについては 2.7。

## §7 宣言名の確認の記録

- この索引に出る完全修飾名を機械的に取り出し、`PAG.PartM.name` ごとに PAGM.lean の宣言の行（`theorem`・`def`・`abbrev`・`structure`・`instance` など）を検索した。
  - スクリプトは `records/founding_index/check_names.py`、出力は `check_names.log`。
  - 第 1 版は 85 件、第 2 版は照合者の指摘で足したものを含めて 102 件で、すべて実在した。
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
  - 見出しを形式文の範囲に合わせた（1.3、2.7、3.2、4.1、5.1、5.2）。
  - 記号 W と 𝔀 の注意を §0 に加えた。
  - 3.1 の規則を CLAUDE.md の文言どおりにし、08:41 の原文を全文で載せた。
  - 宣言を足した（2.3 の A1 の位相の側、2.7 の成分の一意性、4.1 の `dense_rho_image`・`sep_of_commensurable`、5.4 の `crtMul_shellAlg`・`ppEquiv`、6.2 の項目 66・68、5.3 の `Lim`）。
  - 出所を書き分けた。骨格の記述（4.1 の部品、6.3、候補 3 の担当、「文書は書ける」）は骨格と明記した。決定者と時刻も直した（1.4、3.2）。
  - 留保を足した（2.3 の実性への帰着と近い先行、2.4 の未照合、2.6 の `Lim`、2.7 の ω の正規化、4.1 の守備範囲、5.1 の範囲の外と対照群、5.2 の 3 点、6.1 は Lean の定理ではないこと）。
  - 番号の併記と参照を直した（6.1・6.2、6.3 は §2 だけ、6.4 の出所）。
- **第 2 版の照合**：第 2 版は照合後の直しを照合にかけていない。直しは照合者の直し案に沿った狭め・書き分け・出所の明記と、足した宣言（実在は機械的に確認、§7）である。足した宣言の形式文は、照合者が「§B になく未確認」としたものを構築側が読んで当てた。たとえば `rootNum_inv`・`phaseA1_inv`・`UA1_star` の形式文は PAG258 の 363〜412 行で確かめた。次の統合照合の対象に含める。

### notes/pag2_projection_material.md

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
- 境界ユニタリ U と公準 A1 は、照合した範囲（Part 19・22・23・252、すなわち PAG23・PAG26・PAG27・PAG256）では Lean の形式文に出てこない（PAG256 の冒頭のコメントも「U と A1 は Lean の文に出てこない」と書く）。鎖全体については検索していない。Tate の局所関数等式そのもの、定理 2.6 も Lean にしていない（定理 2.6 の条件を A1 の位相が満たすことは PAG16・PAG173・PAG198 の 3 定理から出る、と CLAUDE.md §3 に記録あり。組み合わせた 1 つの文は未形式化）。
- 「射影 = 舞台の P¹ と、反転 ∘ 加法の変換」は読み（2026-11-18 に著者が採用）であり、Lean の文ではない。Part 252 の J∘H_N を「変換の層の有限版」と呼ぶのも読みである。PAG256 の言葉では、`PAG.Part256.JH_eq_rootNum_mul` の docstring は「構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。U と A1 は文に出てこない）」、冒頭のコメント（`/-` で始まる通常のコメントで、docstring ではない）の読みは「公理 A1 の境界ユニタリの原始指標の部分」である。PAG256 の形式文には貼り合わせに当たる対象は出てこない。冒頭のコメントでは、重なりの読み「ねじれた貼り合わせ（U）」と、構築者が再構成した主張「A1 のもとで U = J∘H_N/√N」を通して、間接に結びつけられている。PAG23・PAG26 の「貼り合わせ条件」は 2 チャートモデルの条件（`PAG.Part23.Compat`）である。
- 照合した範囲では、`PAG.Part256.JH` と 2 チャートモデル（`PAG.Part23.P1F`・`PAG.Part23.Compat`・`PAG.Part23.W`）・`PAG.Part27.ProjLine` を結ぶ Lean の文はない。§2 の 2 の変換が「0 の側と ∞ の側をつなぐ」に対応する Lean の文もない。
- ルート数の i^a の帰属と、有限素点の加法指標の符号の規約（§2 の注意 2）は、2026-11-18 に文献で照合した（`pag2_literature_ia_sign.md`、独立照合 1 回、照合後の直しは未照合）。規約 T での値の一致であり、Lean の外。
- 盲検の問いテストで、全素点を通して「各素点の 0 と ∞ の貼り合わせ」を一つの構成として書いた文献は見つからなかった（MathSciNet・zbMATH は未照合）。部品はすべて既知。

## §5 対照群（§7）

- 関数体 𝔽_q(t) でも Tate の局所関数等式は同じ形で成り立つ（Lean の外の既知の事実）。§2 の 2 の変換の形と、§2 の 3 のうちガウス和 τ(χ)/√N の部分は、ℚ に固有の算術を使わない形式の文である。
- ただし §2 の 3 で Hartley 核を採ると（PAG256 の冒頭の読み。著者の決定で標準）、値 𝔀(χ) は偶奇による因子 ε(χ)（χ(−1) で決まる）を含む。規約 T のもとで、ε(χ) は無限素点の局所定数と値が一致する（Lean の外）。i^{±a} の部分は規約によらず、符号は規約による。関数体での対応物は確かめていない（Part 257 のノートは盲検の答えとして、𝔽_q[t] の ∞ の因子を偶で 1、奇で √q/τ(η) と記録している。構築側は計算していない）。
- 関数体では、t ↦ 1/t が素点 0 と素点 ∞ を入れ替える。ただしこの P¹_{𝔽_q} は「点が素点であるような大域の曲線」で、§2 の 1 の「各素点の座標の直線」とは別の対象である（照合者の指摘）。
- ℚ に固有に残るのは、無限素点がアルキメデス的で、実数の順序（符号）と二つの端 ±∞ があることである（「−∞ と ∞」の重なり）。上の ε(χ) の因子（規約 T での無限素点の局所定数）がこの側に属するかは、関数体での対応物を確かめていないので未確認（確信度：低〜中）。

## §6 著者の決定（2026-11-18 19:01）

第 3 版の §6 で仰いだ 3 つの判断に、著者が次のとおり答えた（著者の言葉を要約せずに近い形で記す）。

1. **読みの採用：採る。** 舞台の P¹、反転と加法の変換の合成、原始指標の位相を、基礎文書の第 1・2 章の材料にする。留保は二つ：「ルート数であることは Lean の外」を明記すること、奇の指標での i 倍のずれを滑らかにしないこと。
2. **命名：両方を指し、主は変換。** 舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ、という組の形にする。「射影により融合」という著者の言い方とも一致する。
3. **核：Hartley 核を標準にする。** Part 252 の形式化の追認で、A1 の内容とも揃う。i^a の帰属と符号の規約の文献照合は、基礎文書が無限素点の読みを断定する前に行う（候補 1・候補 3・γ と同じ照合リストに入れる）。それまでは i^a は正規化因子として書き、読みは候補として留保する。

決まったことは、補足 7 の規則に従い著者側の記録（CLAUDE.md §1・§2 と申し送り）に戻す。反映の文案は §9 に置き、著者の指示（19:03）で CLAUDE.md §1 と英語版に反映した。

文献照合（`pag2_literature_ia_sign.md`）の後、2026-11-18 19:25 に著者が次の 2 つを決めた（照合ノート §9 の 1・2 を「進める」）。

4. **i^a の留保を外す。** CLAUDE.md §1 の「i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する」を、規約を明示した書き方に置き換える：規約 T のもとで ε(χ) = (−i)^a は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N は有限素点の局所定数の積と一致する（値の一致、Lean の外）。i の冪が無限素点から来ることは規約によらないが、符号 χ(−1) の置き場は規約による。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
5. **規約 T を基礎文書の標準にする。** Mathlib の `stdAddChar` と有限素点の符号が合い、Tate の学位論文の加法指標・Burnol（arXiv:math/9811040）とも同じ加法指標。

注（2026-11-18 の統合照合の指摘）：2 の著者の言葉は「その上で働く**貼り合わせの合成**を射影と呼ぶ」である。CLAUDE.md §1 と概要では、構築側がこれを断りなく「反転（乗法の側）と加法の変換（加法の側）の合成」と言い換えていた。第 6 版の反映で、著者の言葉と構築側の言い換えを書き分けた。「貼り合わせ」が PAG23 の `PAG.Part23.Compat`（ねじれのない座標の貼り合わせ）と U（ねじれた貼り合わせ）のどちらを指すかは、著者に確かめる。構築側の読みは後者で、U の原始指標の位相が変換の成分である。

## §7 照合の記録（第 1 回）

- 第 1 版（`before_material_v1.md`）を、形式文の全文（PAG23・PAG26・PAG27・PAG256）を渡した新しい照合者が照らした（依頼文 `outputs/material_check_request.md`、出力 `outputs/material_check_output.md`、所要 約 6 分）。
- 主な指摘と直し：原始性の限定の抜け（§2 の 3、表 3 行目）、素朴なフーリエ核と Hartley 核の取り違え（§2 の注意 2 を新設）、`JH_eq_rootNum_mul` を「ルート数」の根拠にした当て方（外した）、番号と名前空間の取り違えの罠（完全修飾名にした。第 2 版では一部だけで、第 3 版で残りを直したとしていたが、統合照合で `rootNum`・`JH_eq_rootNum_mul`・`parFac_of_even`・`parFac_of_odd` が残っていると指摘され、第 6 版で直した。§11）、K ≥ 1 の抜け、2 チャートモデルが P¹ になる範囲、一般の N の `ProjLine` の記述、docstring の引用の但し書き、`JH` と 2 チャートモデルを結ぶ文がないこと、「無限素点の U」の書き方、記号 W の衝突（ι と 𝔀 に分けた）、有限と無限の対応のずれ、表 2 行目のラベル（［再導出］にそろえた）。

## §8 照合の記録（第 2 回：直した版の再照合）

- 第 2 版（`before_material_v2.md`）を、第 1 回と同じ形式文の全文（PAG23・PAG26・PAG27・PAG256）と第 2 版の全文を渡した新しい照合者が照らした（入力 `input_material_v2.md`、依頼文 `outputs/material_recheck_request.md`、出力 `outputs/material_recheck_output.md`、所要 約 7 分）。照合者は手元で式の数値確認（N ≤ 30）を行った。数値は証明ではない。
- 結論：第 2 版で新しく入った明確な誤りが 1 件（§4 の「「貼り合わせ」という語は Lean の側にはない」。PAG256 の冒頭のコメントと PAG23・PAG26 に語がある）。言い過ぎと曖昧さがいくつか。宣言名・完全修飾名・式はほかは一致。
- 直したこと（照合者の指摘 1〜9 の順）：
  1. §4 の「貼り合わせ」の文を、照合者の直し案のとおりに差し替えた。
  2. 注意 2 を式で書いた（奇の χ で 𝔀 = −i·τ/√N、素朴な成分 = i·𝔀）。核の符号への依存（e(−xy) で χ(−1)τ/√N、関係の反転）を明記し、当時の §6 の 3（判断の依頼。現在の §6 は決定の記録）にも規約を添えた。文献照合の項目に有限素点の加法指標の符号を加えた。
  3. 表 3 行目を「位相でないことがある」に弱め、全称の文は Lean の外と断った。法 2 の非原始性の根拠に `removal_counterexample` を足した。
  4. 注意 2 と記号の行で、`rootNum` の定義（すべての χ）とルート数との同定（Lean の外）を書き分け、根拠に `JH_eq_rootNum_mul_any`・`rootNum_eq` を引いた。
  5. §2 の 3 の「この値」を、PAG256 の冒頭の読みの値 𝔀(χ)（Hartley 側）と特定し、素朴な核では奇の χ でずれることを書いた。
  6. 記号の行と §3・§4 の宣言名を完全修飾名にし、PAG256 の W(χ) が 𝔀 を指すことを注記した（第 6 版の注：修飾されていない名前が残っていた。§11）。
  7. §4 の U と A1 の文の範囲を「照合した範囲（PAG23・PAG26・PAG27・PAG256）」に狭めた。注意 1 と §4 の「結ぶ文はない」も同じ範囲に狭めた。
  8. 注意 2 の素朴な核の項に、`inv_apply_units_inv` が要ることと、単数の上では原始性が要らないことを書いた。
  9. 軽微な点：「のときだけ」を「Lean で示されているのは N = p^K だけ」と「2 つ以上の素因数で点の数が一致しない」に分け、「0 と ∞ は別の点」に N ≥ 2 を付けた。`toProj_Wpt` は K ≥ 1 なしと書いた。`mk_eq_mk` を反転の補題から外した。「有限素点の作用素」を「有限レベル N の変換」に、§2 の 2 の「作用素」を「変換（写像）」にそろえた。PAG256 の冒頭は通常のコメントと書いた。§5 の第 1 項と第 3 項の張り合いを、ε(χ) の因子を分けて書くことで解いた。
- この第 3 版は、第 2 回の照合の後の直しを照合にかけていない。直しはすべて、照合者が示した直し案に沿った言い換えと主張の範囲を狭める直しで、新しい主張は加えていない（構築側の判断。第 6 版の注：統合照合の指摘では字義どおりではなく、点の数の式 2N − φ(N)・N∏(1 + 1/p)、N ≤ 30 の数値、符号の規約についての再照合者の知識が新しく入っていた。照合者の検算ではどれも正しい。補足 8 の停止の規約の「主張を変えない直し」に当たると読む）。§5 の第 2 項（ε(χ) の因子の帰属）は張り合いの解消のために書き足した文で、注意 2 の未確認の読みに条件づけてある。この判断が妥当かどうかは、次の統合照合で確かめる対象とする。

## §9 著者の決定の記録（第 4 版）

- 第 3 版（`before_material_v3.md`）に、著者の決定（2026-11-18 19:01、§6）を記録した。直したところ：冒頭の地位の文（「著者の確認待ち」→「留保つきで採用」）、§2 の見出しと命名の決定（両方を指し、主は変換）、§2 の 3（標準の核を Hartley 核とし、i^a を正規化因子として書く。ルート数であることは Lean の外。奇の χ での i 倍のずれは消えない）、注意 2 の帰属の読み（候補として留保、文献照合は基礎文書が無限素点の読みを断定する前）、§4 の第 3 項（読みが採用されたこと）、§6（判断の依頼を決定の記録に置き換えた）。
- これらは著者の決定の記録で、Lean についての主張は変えていない。照合にはかけていない（補足 8 の「主張を変えない直し」に当たると読む。次の統合照合の対象に含める）。
- 著者側の記録に戻すための文案を次に置いた。CLAUDE.md §1 への追記は、2026-11-18 19:03 の著者の指示で、CLAUDE.md と英語版 CLAUDE.en.md の §1（命題 3 の置き方の次の箇条）に反映した。反映の際に文案へ足したもの：命名の意味（2026-11-16）、Part と PAG の番号の併記（CLAUDE.md §7 の (iv)）、PAG256 の docstring の記号 W(χ) が反転の W とは別であることの注記、「明記すること」の一句（統合照合の指摘で列挙を補う：「留保つき」の語、「（有限レベルでは…J∘H_N/√N）」の括弧、𝔀 の記号を使わないこと、も 19:03 の反映で文案から変えた）。照合リストは著者側のもので、構築側では変えていない。

**CLAUDE.md §1 への追記の文案**（解釈の層の箇条として）：

> 「射影」の読み（2026-11-18、著者が採用。解釈の層であり、形式化済みの定理ではない）：命名の「射影」は舞台と変換の組を指し、主は変換である。舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28）、その上で働く反転（乗法の側）と加法の変換（加法の側）の合成を射影と呼ぶ。原始指標についての位相がその成分である。標準の核は Part 252 の Hartley 核とする（形式化の追認。A1 の内容と揃う）。値は 𝔀(χ) = τ(χ)/(i^a√N)（`PAG.Part256.rootNum`）で、原始指標ではルート数だが、その同定は Lean の外である。素朴なフーリエ核 e(xy) とは奇の指標で i 倍ずれ、このずれを滑らかにしない。i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する。A1 は公準のまま。材料は `notes/pag2_projection_material.md`。

**照合リストへの項目の文案**（候補 1・候補 3・γ と同じリスト）：

> i^a の帰属と符号の規約：(a) ルート数の i^a は、Tate の局所分解で無限素点の局所因子から来るか。(b) 大域の加法指標の符号の規約（無限素点と有限素点で符号を逆に取るか）のもとで、有限素点の局所因子は τ(χ)/√N と χ(−1)τ(χ)/√N のどちらになるか。期限：基礎文書が無限素点の読みを断定する前。それまで i^a は正規化因子として書く。出所：`notes/pag2_projection_material.md` §2 の注意 2。

## §10 文献照合の後の著者の決定の記録（第 5 版）

- 第 4 版（`before_material_v4.md`）に、文献照合の結果と 2026-11-18 19:25 の著者の決定（§6 の 4・5）を記録した。直したところ：冒頭の版の文、§2 の 3（i^a を正規化因子として書く扱いを、規約 T での無限素点の局所定数との一致に置き換えた）、注意 2 の帰属の読み（照合の結果と決定を追記）、§6（4・5 を追加）。§4 の第 4 項と注意 2 の見出しは直し忘れていた（第 6 版で直した。§11）。
- 決定は CLAUDE.md §1 と英語版にも反映した。
- これらは著者の決定と照合の結果の記録で、Lean についての主張は変えていない。照合にはかけていない（次の統合照合の対象に含める）。根拠にした文献照合ノートの第 2 版も、照合後の直しが未照合である。

## §11 統合照合の記録（第 6 版）

- 2026-11-18 夜、前回の照合の後に入った変更（この材料ノートの第 2 版→第 5 版、文献照合ノートの第 1 版→第 3 版、CLAUDE.md と英語版の §1 の箇条、概要の日英の行、引き継ぎメモの行）を、差分・現行の全文・形式文の全文（PAG23・PAG26・PAG27・PAG256）を渡した新しい照合者 1 人が照らした（入力 `input_tail2.md`、依頼文 `request.md`、出力 `outputs/T2_output.md`、所要 約 9.6 分。記録は `records/tail_audit2/`）。
- 結論：足した・変えた式は、照合者の検算の範囲ですべて正しい。問題は記録の側：このノートの中の直し忘れ 2 か所（§4 の第 4 項、注意 2 の見出し）、CLAUDE.md と概要に移すときに落ちた限定（原始性、s = 1/2、JH は P¹ の上の作用素ではないこと）、地位の書き分け（「A1 の内容と揃う」が事実として書かれている、など）、版の参照のずれ。
- このノートで直したこと：§4 の第 4 項と注意 2 の見出し（照合済みと書いた）、注意 2 の帰属の読み（原始性、s = 1/2、「通例」→「ℚ の上で自明であるため必然」、Part 257 の記録への参照）、表 1 行目（点集合の全単射と関数の同型を分けた）、§4 の第 1 項（N = 1）、§4 の第 3 項（「A1 のもとで」）、§5 の第 2・第 4 項（規約 T を明示し、「ℚ に固有」を未確認とした）、§6 の後の注（著者の言葉「貼り合わせの合成」と構築側の言い換え）、修飾されていない名前の修飾、§7〜§10 の記録の事実との不一致。
- 同じ指摘で、CLAUDE.md と英語版、概要の日英、文献照合ノート、引き継ぎメモも直した（各ファイルの記録を参照）。
- 補足 8 の停止の規約：今回の直しは、限定を足す・地位を書き分ける・記録を事実に合わせる直しで、数学の主張を強めるものはない（構築側の判断）。新しく足した記録の文（Part 257 の記録への参照）は鎖の検索で確かめた事実で、引用した行は文献照合ノートの §0 にある。

### notes/pag2_literature_ia_sign.md

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
  - これは値の一致であり、PAG256 の Hartley 変換を Tate の局所関数等式として形式化したものではない。

## §2 二つの規約と出典

- **規約 T**：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}（{x}_p は p 進の小数部分）。積は ℚ の上で自明。
  - Tate の学位論文（1950）：実数体で λ(x) = −x（本文に「負の符号に注意」の注記）、p 進体で λ(x) は λ(x) − x が p 進整数となる有理数。指標は e^{2πiΛ}（§2.2、§4.1 Lemma 4.1.5）。**照合者が走査版（Rutgers）で確認した。構築側は原文を開いていない。** 照合者の注記：同論文の Fourier 変換は e^{−2πiΛ(ξη)} を核とし（実数体では e^{+2πixy}）、局所の定数は逆向きの比 ρ(c) として定義されている。上の ε の定め方は学位論文そのものではなく、Corvallis 論文の流儀である。走査版の式は OCR が崩れており、この注記の確信度は中。
  - Roy–Schmidt–Yi, "Classical and adelic Eisenstein series", arXiv:2109.07649 §4.3：ψ を Tate の学位論文で定義されたものとし、ψ_∞(x) = e^{−2πix} と書く（式 (150)〜(157) は同論文の §6.1）。
  - Burnol, arXiv:math/9811040（"Spectral Analysis of the Local Conductor Operator"）：実素点で exp(−2πit)、有限素点で exp(2πi{Tr t})。モノグラフ層が引く Burnol と同じ著者。読んだ範囲には、Tate の規約への言及も符号の選び方の説明もない。
  - arXiv:1502.02633 も同じ指標を「標準の加法指標」として書く。ただし、Tate の学位論文に従うと明記しているのは Haar 測度の正規化だけである（第 1 版の「Tate の学位論文の規約として書く」は言い過ぎだったので直した）。
- **規約 C**（逆の規約）：ψ_∞(x) = e^{+2πix}、ψ_p(x) = e^{−2πi{x}_p}。例：arXiv:2604.25288 §5.1、arXiv:1511.04265 式 (3.72)〜(3.75)（照合者が確認）。
- 指標の対応は ψ によらない：ξ に対応するイデール類指標 χ は、不分岐の ℓ で χ_ℓ(ℓ) = ξ(ℓ)。分岐する p では、χ_p の ℤ_p^× への制限が (ξ^{(p)})^{−1}（Roy–Schmidt–Yi §6.1 の式 (150) ∏_{p∣u} χ_p(a) = ξ(a)^{−1} から、a を中国剰余定理で選んで導かれる。ξ = ∏ ξ^{(p)} は中国剰余定理による分解）。χ_∞ は偶で自明、奇で符号（同 式 (151)）。

## §3 無限素点の局所定数

- 規約 T：f(x) = x e^{−πx²} の ψ_∞ に関するフーリエ変換は f̂(y) = ∫ f(x) e^{−2πixy} dx = −i·y e^{−πy²}。Z(s, sgn, f) が局所 L 因子に等しいので、ε(s, sgn, ψ_∞) = −i（s によらない）。偶では f = e^{−πx²} が自己双対で ε = 1。Roy–Schmidt–Yi 式 (155) と同じ値。
- 規約 C：ε(s, χ, ψ_a) = χ(a)|a|^{s−1/2} ε(s, χ, ψ) で a = −1 とすると +i（照合者の導出）。この値を直接書いた文献の箇所は確かめていない。
- 数値：構築側（`local_eps_check.log`）は f̂(y)/f(y) を 4 点で計算し、規約 T で −i、規約 C で +i。照合者は局所関数等式を数値積分で直接評価し（s = 0.3, 0.5, 0.8）、同じ値を得た。

## §4 有限素点の局所定数の積

- p ∣ N、k = v_p(N) のとき、ε(0, χ_p, ψ_p) = ∫_{p^{−k}ℤ_p^×} χ_p^{−1}(x) ψ_p(x) dx（Roy–Schmidt–Yi 式 (157)。測度は ℤ_p が 1）。一般の s では ε(s) = p^{−ks}·ε(0)（照合者が局所関数等式から導出）。x = p^{−k}y と置くと、規約 T で ε(0, χ_p, ψ_p) = χ_p(p)^k Σ_{y mod p^k, p∤y} ξ^{(p)}(y) e^{2πiy/p^k}。
- 交差項：χ が ℚ^× の上で自明で、χ_∞(p) = 1、不分岐の ℓ で χ_ℓ(p) = 1 だから、χ_p(p) = ∏_{ℓ∣N, ℓ≠p} ξ^{(ℓ)}(p)。これは構築側の導出で、Roy–Schmidt–Yi には書かれていない（照合者が同じ式を独立に導出した）。中国剰余定理によるガウス和の分解 τ(ξ) = ∏_p ξ^{(p)}(N/p^{k_p}) τ(ξ^{(p)}) の交差項に当たる。
- 規約 T：∏_{p∣N} ε(0, χ_p, ψ_p) = τ(ξ)（Roy–Schmidt–Yi 式 (156)。同論文では演習として示されている）。s = 1/2 では τ(ξ)/√N（絶対値 1）。
- 規約 C：ψ_p の符号が変わるので、各因子に ξ^{(p)}(−1) が掛かり、積は ξ(−1)τ(ξ)。自己双対測度は変わらない（ψ_p の導手は ℤ_p のまま）。

## §5 数値確認（数値は証明ではない）

- 構築側（`local_eps_check.py`・`local_eps_check.log`。§4 の明示式そのもの）：
  - 31 個の法（1, 3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 20, 21, 24, 25, 27, 28, 32, 35, 40, 44, 45, 48, 56, 60, 63, 72, 84, 105, 120）の原始指標すべて、209 個（偶 104・奇 105）。原始指標の個数は各 N で既知の数と一致した。退化した場合（N = 1、p = 2 の法 4・8・16・32、複数の素因数）を含む。
  - 有限素点の積：規約 T で τ(ξ)（最大誤差 2.8×10⁻¹⁴）、規約 C で ξ(−1)τ(ξ)（2.9×10⁻¹⁴）。
  - s = 1/2 での大域：どちらの規約でも W(ξ)（5×10⁻¹⁵）。
  - 規約を混ぜると（規約 T の ψ_p と規約 C の ε_∞）、奇の指標 105 個すべてで合わない。
- 照合者（`outputs/check_eps.py`・`check_supp.py` とその出力）：
  - 法 1〜100 と 120, 128, 135, 180, 243, 256, 360, 400 の原始指標 2,162 個。
  - p 進の局所定数を局所関数等式から有限和で直接評価し、§4 の閉じた式と比べた（照合者の出力では 6,288 回、最大差 3.1×10⁻¹³。回数の内訳は出力に書かれておらず、統合照合では素因数の個数の和から見積もった数と合わないと指摘された。確かめていない）。
  - W(ξ) は θ 変換の関係で別に確かめた（3.1×10⁻¹³）。一般の s での積 N^{1/2−s} W(ξ) も確かめた。
  - 混ぜた規約では、奇の指標 1,082 個すべてで −W(ξ) になった。混ぜた ψ は ℚ の上で自明でない（x = 1/3 で e^{4πi/3}）ので、大域の選び方として許されない。
  - Hartley 和の式 Σ_x ξ(x) cas(2πxy/N) = ε(ξ)τ(ξ)ξ̄(y) はすべての y で成り立った（ξ 原始。原始でない指標では法 4 の y = 0, 2 などで崩れる）。引数の符号を逆にした cas(−2πxy/N) では ξ(−1)√N·W(ξ) になる。
- 構築側の数値が確かめたのは §4 の明示式の算術である。照合者の数値は、局所関数等式から直接評価した値との比較を含む。どちらも、その値が Tate の局所定数であるという文献の定理そのものを示すものではない。

## §6 PAG の記号との対応（値の一致。Lean の外）

| PAG256 の量 | 値 | 文献の量（規約 T、s = 1/2） | 規約 C では |
|---|---|---|---|
| `PAG.Part256.parFac` ξ | 偶 1、奇 −i | ε(1/2, χ_∞, ψ_∞) = (−i)^a | 無限素点は i^a = (−1)^a·ε(ξ) |
| 素朴な核 e(xy) での成分 | τ(ξ)/√N | ∏_{p∣N} ε(1/2, χ_p, ψ_p) | 有限素点の積は ξ(−1)τ(ξ)/√N（e(−xy) の値） |
| Hartley 核での成分 𝔀(ξ)（`rootNum`、`JH_eq_rootNum_mul_any`） | ε(ξ)τ(ξ)/√N = τ(ξ)/(i^a√N) | ε(1/2, χ) = ∏_v ε(1/2, χ_v, ψ_v) = W(ξ) | 同じ（大域は規約によらない） |

- Mathlib の `stdAddChar`（ZMod N の上で e(x/N) = e^{2πix/N}）は、規約 T の ψ_p(y/p^k) = e^{+2πiy/p^k} と同じ符号である。Lean の鎖の有限素点の側は、規約 T と符号が合っている。
- PAG256 の Hartley 変換が Tate の局所関数等式を（無限素点の因子を含めて）表すことは Lean の外で、Lean の文にはない。

## §7 ラベルと対照群

- ラベル：§1 の (a)(b) とも［既知］（Tate 1950、Tate 1979、Roy–Schmidt–Yi 2021 などの標準的な計算）。PAG の値との一致（§6）は［再導出（小さい）］：PAG256 の `parFac`・`rootNum` の定義と文献の局所定数の値を並べたもの。新規候補はない。
- 対照群（§7）：関数体 𝔽_q(t) では無限素点も非アルキメデス的で、局所定数はガウス和型になる見込み。そうなら、i の冪としての無限素点の因子は ℚ の実素点に固有と読める。確かめていない（確信度：低〜中）。

## §8 照合の記録

- 第 1 版（`before_check_v1.md`）の主張を C1〜C6 に分けて、文脈を渡さない照合者に渡した（依頼文 `outputs/check_request.md`、出力 `outputs/check_output.md`、照合者の計算 `outputs/check_eps.py`・`check_eps_output.txt`・`check_supp.py`・`check_supp_output.txt`、所要 約 8.5 分）。依頼は判定ではなく、計算・導出・文献の箇所・反例または直した文を出すこと。
- 結論：C1〜C6 はすべて成り立つ（確信度：高。C1 の注記の部分は中）。直しが要る点が 2 つ、注記が 1 つ。
- 直したこと：
  1. C5：「s = 1/2 で」を補い、一般の s では N^{1/2−s} W(ξ) と書いた（§1 (b)、§5）。
  2. C1：arXiv:1502.02633 が Tate の学位論文に従うと明記しているのは Haar 測度の正規化だけ、と直した。Tate の学位論文の確認は照合者が走査版で行ったこと、構築側は原文を開いていないことを明記した。同論文の Fourier 変換の核と局所定数の向きの注記を入れ、ε の定め方は Corvallis 論文の流儀であると冒頭に書いた（§2、記号）。
  3. C6 の注記：Hartley の ε(ξ) と無限素点の局所定数の一致は規約 T を選んだときの分け方で、等式だけからは「ε(ξ) は無限素点から来る」とは言えない、と §1 と §6 に書いた。§1 (a) の結論を「i の冪は無限素点から来る。符号 (−1)^a の置き場は規約による」に直した。
  4. 照合者の数値と導出（局所関数等式からの直接評価、規約 C の +i の導出、ε(s) = p^{−ks}ε(0)、χ_p(p) の独立の導出）を §3〜§5 に書き足した。
- この第 2 版は、照合の後の直しを照合にかけていない。直しは照合者の直し案・注記に沿った言い換えと、主張の範囲を狭める直しで、新しい主張は加えていない（構築側の判断。次の統合照合の対象に含める）。
- 確かめられなかったこと（照合者の報告から）：規約 C の ε_∞ = +i と §4 の規約 C の式は、文献の箇所では直接確かめていない（導出と数値だけ）。Burnol の PDF は取得できず ar5iv 版の一部、1502.02633 と 1511.04265 も一部だけを読んだ。Tate の学位論文の走査版の式の部分は OCR が崩れていた。

## §9 著者の決定（2026-11-18 19:25）

第 2 版の §9 で仰いだ 2 つの判断に、著者は「1 と 2 を進めてください」と答えた。

1. **留保を外す。** CLAUDE.md §1（と英語版）の「i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する」を、規約を明示した書き方に置き換えた。規約 T のもとで、ε(ξ) = (−i)^a は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(ξ)/√N は有限素点の局所定数の積と一致する（値の一致、Lean の外）。明示的な因子 i^{±a} が無限素点の局所定数であることは規約によらないが、符号 ξ(−1) の置き場は規約による（第 4 版で、統合照合の指摘に合わせて言い方を直した）。規約 T を明示せずに「ε(ξ) は無限素点から来る」と書かない。
2. **規約 T を基礎文書の標準にする。** Mathlib の `stdAddChar` と有限素点の符号が合い、Tate の学位論文の加法指標・Burnol（arXiv:math/9811040。根拠はこの 1 本で、フーリエ変換の核が指標そのものか共役かは書かれていない）とも同じ加法指標。

記録：決定は CLAUDE.md §1 と英語版、材料ノート（第 5 版）の §6 の 4・5、概要の文書、引き継ぎメモに反映した。このノートの第 2 版の照合後の直しは未照合のままで、次の統合照合の対象に含める（決定の根拠にした版が照合後の直しを含むことを、ここに明記する）。第 2 版の §9 の文案は `before_decision_v2.md` に残る。

## §10 統合照合の記録（第 4 版）

- 2026-11-18 夜の統合照合（材料ノート §11、記録 `records/tail_audit2/`）で、このノートの第 1 版→第 3 版の差分も照らされた。式・数値・文献の主張は照合者の検算の範囲で正しかった（Tate の学位論文の走査版の λ(x) = −x とフーリエ変換の核、Roy–Schmidt–Yi の (155)・(156)・(157)、有限素点の積の明示式を N ≤ 60 の原始指標 662 個で確認）。
- 直したこと：§1 (a) の「（i の冪を含まない）」（値は i を取りうる。例を足し、「明示的な因子 i^{±a}」と言い直した）、Roy–Schmidt–Yi の式 (150) の引き方（§6.1、積の形から導かれる）、Burnol の根拠が 1 本であること、照合者の数値の回数の内訳が未確認であること、§9 の言い方。
- 後から行った内部照合（§0）：同じ結論が Part 257（PAG261）の記録に読みとして書かれていたことを記録した。
- 補足 8 の停止の規約：今回の直しは、言い方を正す・根拠の書き方を狭める・記録を足す直しで、数学の主張を強めるものはない（構築側の判断）。

### CLAUDE.md §1 の「射影」の箇条

  - 「射影」の読み（2026-11-18、著者が留保つきで採用。解釈の層であり、形式化済みの定理ではない）：命名の意味は「アデール幾何とイーデル幾何を射影によって融合する」（2026-11-16、著者）。命名の「射影」は舞台と変換の組を指し、主は変換である。著者の言葉では「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」。舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28（PAG23〜PAG32））。構築側の読みでは、その合成は反転（乗法の側）と加法の変換（加法の側）の合成で、有限レベルでは Part 252（PAG256）の $J\circ H_N/\sqrt N$（`PAG.Part256.JH`）に当たる。ただし `JH` は $\mathbb Z/N$ の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではなく、`JH` と P¹ のモデルを結ぶ Lean の文はない。「貼り合わせ」が PAG23 の `Compat`（ねじれのない座標の貼り合わせ）と $U$（ねじれた貼り合わせ）のどちらを指すかは著者の確認待ち（構築側の読みは $U$）。原始指標についての位相がその成分である。標準の核は Part 252 の Hartley 核とする（形式化の追認。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは未照合）。値は $\tau(\chi)/(i^a\sqrt N)$（`PAG.Part256.rootNum`。PAG256 の docstring と冒頭のコメントの記号 W(χ) はこの値を指し、反転の $W$ とは別）で、原始指標ではルート数だが、その同定は Lean の外である（明記すること）。素朴なフーリエ核 $e(xy)$ の値 $\tau(\chi)/\sqrt N$ とは奇の指標で $i$ 倍ずれ、このずれを滑らかにしない。加法指標の規約は、規約 T（Tate の学位論文の加法指標：$\psi_\infty(x) = e^{-2\pi i x}$、$\psi_p(x) = e^{+2\pi i\{x\}_p}$）を基礎文書の標準とする（2026-11-18 19:25、著者の決定。Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol（arXiv:math/9811040）とも同じ加法指標）。規約 T のもとで、原始的な $\chi$ について、Hartley 核の因子 $\varepsilon(\chi) = (-i)^a$（`PAG.Part256.parFac`）は無限素点の局所定数 $\varepsilon(1/2, \chi_\infty, \psi_\infty)$ と一致し、$\tau(\chi)/\sqrt N$ は $s = 1/2$ での有限素点の局所定数の積と一致する（値の一致であり Lean の外。局所定数は Tate 1979 の流儀で定める）。同じ同定は Part 257（PAG261）の冒頭の説明とノートに読みとして書かれており（2026-11-14、確信度：中〜高）、2026-11-18 の文献照合 `notes/pag2_literature_ia_sign.md`（独立照合 1 回と統合照合 1 回）で確かめ直した。これを受けて、$i^a$ を正規化因子として留保する扱いは同日 19:25 の著者の決定で外した。明示的な因子 $i^{\pm a}$ が無限素点の局所定数であることは規約によらないが、符号 $\chi(-1)$ を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が $i^a$、有限素点の積が $\chi(-1)\tau(\chi)/\sqrt N$）。したがって、規約 T を明示せずに「$\varepsilon(\chi)$ は無限素点から来る」と書かない。A1 は公準のまま。材料は `notes/pag2_projection_material.md`。

### CLAUDE.en.md §1 の該当の箇条

  - Reading of "projection" (2026-11-18, adopted with reservations by the author; interpretive layer, not a formalized theorem): the meaning of the name is "fusing adelic geometry and idelic geometry by projection" (2026-11-16, the author). The "projection" in the name refers to the pair of a stage and a transform, with the transform as the main sense. In the author's words: "the stage is P¹, and the composition of gluings acting on it is called the projection". The stage is the projective line P¹ (inversion swaps 0 and ∞; at the finite level, Parts 19–28 (PAG23–PAG32)). In the construction side's reading, that composition is the composition of inversion (the multiplicative side) and an additive transform (the additive side), which at the finite level corresponds to $J\circ H_N/\sqrt N$ of Part 252 (PAG256) (`PAG.Part256.JH`). However, `JH` is a map sending functions on $\mathbb Z/N$ to functions on the units; it is not an operator on P¹, and no Lean statement links `JH` to the models of P¹. Whether "gluing" refers to `Compat` of PAG23 (the untwisted gluing of coordinates) or to $U$ (the twisted gluing) awaits the author's confirmation (the construction side reads it as $U$). Its components on primitive characters are the phases. The standard kernel is the Hartley kernel of Part 252 (ratifying the formalization; that this is consistent with the content of A1 is the author's judgment, based on the reading in the header comment of PAG256, not checked against the text of the monograph). The value is $\tau(\chi)/(i^a\sqrt N)$ (`PAG.Part256.rootNum`; the symbol W(χ) in the PAG256 docstrings and header comment denotes this value and is distinct from the inversion $W$); for primitive characters it is the root number, but that identification is outside Lean (state this explicitly). It differs from the value $\tau(\chi)/\sqrt N$ of the plain Fourier kernel $e(xy)$ by a factor $i$ for odd characters; do not smooth over this discrepancy. The convention for the additive character is convention T (the additive character of Tate's thesis: $\psi_\infty(x) = e^{-2\pi i x}$, $\psi_p(x) = e^{+2\pi i\{x\}_p}$), which is the standard for the foundational document (2026-11-18 19:25, the author's decision; its sign at the finite places agrees with Mathlib's `stdAddChar`, and it is the same additive character as Burnol's (arXiv:math/9811040)). Under convention T, for primitive $\chi$, the factor $\varepsilon(\chi) = (-i)^a$ of the Hartley kernel (`PAG.Part256.parFac`) agrees with the local constant $\varepsilon(1/2, \chi_\infty, \psi_\infty)$ at the infinite place, and $\tau(\chi)/\sqrt N$ agrees with the product of the local constants at the finite places at $s = 1/2$ (an agreement of values, outside Lean; local constants are defined in the style of Tate 1979). The same identification was written as a reading in the header comment and note of Part 257 (PAG261) (2026-11-14, confidence medium to high), and was re-confirmed by the literature check of 2026-11-18, `notes/pag2_literature_ia_sign.md` (one independent check and one integrated check). Following this, the treatment of $i^a$ as a reserved normalization factor was lifted by the author's decision at 19:25 on the same day. That the explicit factor $i^{\pm a}$ is the local constant at the infinite place does not depend on the convention, but whether the sign $\chi(-1)$ is placed at the infinite place or at the finite places does (in the opposite convention the infinite place gives $i^a$ and the product over the finite places is $\chi(-1)\tau(\chi)/\sqrt N$). Therefore, do not write "$\varepsilon(\chi)$ comes from the infinite place" without stating convention T. A1 remains a postulate. The material is in `notes/pag2_projection_material.md`.

### 概要（日本語）の該当の行

  - 採用した読み（構築側が出し、2026-11-18 に著者が留保つきで採用。解釈の層で、形式化済みの定理ではない）：命名の「射影」は舞台と変換の組を指し、主は変換（著者の言葉では「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」）。舞台は射影直線 P¹（Part 19〜28（PAG23〜PAG32）。反転が 0 と ∞ を入れ替える）。構築側の読みでは、その合成は反転（乗法の側）と加法の変換（加法の側）の合成で、有限レベルでは Part 252（PAG256）の J∘H_N/√N に当たる（ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。P¹ のモデルと結ぶ Lean の文はない）。原始指標についての位相がその成分で、標準の核は Part 252 の Hartley 核（著者の決定）、値は τ(χ)/(i^a√N)（原始指標ではルート数だが、その同定は Lean の外）。素朴なフーリエ核 e(xy) では τ(χ)/√N で、奇の指標で i 倍ずれる。加法指標は Tate の学位論文の加法指標の規約（無限素点で e^{−2πix}、有限素点で e^{+2πi{x}_p}）を標準とする（著者の決定）。その規約で、原始的な χ について、Hartley 核の因子 (−i)^a は無限素点の局所定数と、τ(χ)/√N は s = 1/2 での有限素点の局所定数の積と一致する（値の一致で Lean の外。局所定数は Tate 1979 の流儀。2026-11-18 の文献照合 `notes/pag2_literature_ia_sign.md` による、Part 257（PAG261）の読みの確かめ直し）。明示的な因子 i^{±a} が無限素点の局所定数であることは規約によらないが、符号 χ(−1) の置き場は規約による。公準 A1 は、境界ユニタリの原始指標の位相をこの値に選ぶ公準のまま（読み）。部品はすべて既知で、新しいパートにはしない（`notes/pag2_projection_material.md`）。残る問い：全素点を通した一つの構成（空間と作用素のレベル）としての定式化。値のレベルでは、全素点の局所因子の積への分解が Part 257（PAG261）にある。

### 概要（英語）の該当の行

  - Adopted reading (proposed by the construction side, adopted with reservations by the author on 2026-11-18; interpretive layer, not a formalized theorem): the "projection" in the name refers to the pair of a stage and a transform, with the transform as the main sense (in the author's words: "the stage is P¹, and the composition of gluings acting on it is called the projection"). The stage is the projective line P¹ (Parts 19–28 (PAG23–PAG32); inversion swaps 0 and ∞). In the construction side's reading, that composition is the composition of inversion (the multiplicative side) and an additive transform (the additive side), which at the finite level corresponds to $J \circ H_N/\sqrt N$ of Part 252 (PAG256) (a map sending functions on ℤ/N to functions on the units, not an operator on P¹; no Lean statement links it to the models of P¹). Its components on primitive characters are the phases; the standard kernel is the Hartley kernel of Part 252 (the author's decision), with value $\tau(\chi)/(i^a\sqrt N)$ (the root number for primitive χ, but that identification is outside Lean). With the plain Fourier kernel $e(xy)$ the value is $\tau(\chi)/\sqrt N$, differing by a factor $i$ for odd characters. The additive character follows the convention of the additive character of Tate's thesis ($e^{-2\pi i x}$ at the infinite place, $e^{+2\pi i\{x\}_p}$ at the finite places) as the standard (the author's decision). In that convention, for primitive χ, the factor $(-i)^a$ of the Hartley kernel agrees with the local constant at the infinite place, and $\tau(\chi)/\sqrt N$ agrees with the product of the local constants at the finite places at $s = 1/2$ (an agreement of values, outside Lean; local constants in the style of Tate 1979; literature check of 2026-11-18, `notes/pag2_literature_ia_sign.md`, Japanese, re-confirming the reading recorded in Part 257 (PAG261)). That the explicit factor $i^{\pm a}$ is the local constant at the infinite place does not depend on the convention, but where the sign $\chi(-1)$ is placed does. The postulate A1 remains a postulate that chooses the phase of the boundary unitary on primitive characters to be this value (a reading). All ingredients are known, and this is not made a new Part (`notes/pag2_projection_material.md`, Japanese). Remaining question: a formulation as one construction across all places (at the level of spaces and operators). At the level of values, the decomposition into a product of local factors over all places is in Part 257 (PAG261).

## §C 宣言

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

### PAG.Part26.Wpt（PAG26.lean）
```lean
/-- 点の反転 [x:1] ↦ [1:x]。 -/
noncomputable def Wpt : Pt N → Pt N
  | Sum.inl x => if h : IsUnit x then Sum.inl x⁻¹ else Sum.inr ⟨x, h⟩
  | Sum.inr y => Sum.inl y.1
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

### PAG.Part220.InLayer（PAG220.lean）
```lean
/-- n は d の層に入る：n = d·e（e は c と互いに素）。 -/
abbrev InLayer (c d n : ℕ) : Prop := ∃ e : ℕ, n = d * e ∧ Nat.Coprime e c
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

### PAG.Part240.crtMul_shellAlg（PAG240.lean）
```lean
/-- **4a.** A は中国剰余定理で分かれる（Part 228）。 -/
theorem crtMul_shellAlg : CRTMul shellAlg :=
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

### PAG.Part240.ppEquiv（PAG240.lean）
```lean
/-- **代数の同型** X_N ≅ X_{q₁^{k₁}} ⊗ (X_{q₂^{k₂}} ⊗ (⋯ ⊗ ℂ))（素冪のリスト）。 -/
noncomputable def ppEquiv (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) (N : ℕ) [NeZero N] : (tensAlg X (ppList N)).carrier ≃ₐ[ℂ] X N :=
  (tensEquiv X hX (ppList N) (coprimeList_ppList N)).trans (substEquiv X (prodList_ppList N))
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

### PAG.Part249.sumSub_eq_shellAlg_iff（PAG249.lean）
```lean
/-- **4b. ⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ = A_N ⇔ N = 1 ∨ N = 8 ∨ N = p ∨ N = p²（p は素数）。** -/
theorem sumSub_eq_shellAlg_iff (N : ℕ) [NeZero N] :
    sumSub N = Subalgebra.toSubmodule (shellAlg N) ↔
      N = 1 ∨ N = 8 ∨ ∃ p : ℕ, p.Prime ∧ (N = p ∨ N = p ^ 2) :=
```

### PAG.Part251.addEAlg_one_eq_shellAlg_iff（PAG251.lean）
```lean
/-- **7c.** B_1 = A_N ⇔ N は平方因子なし ∨ N = 8 ∨ N = p²（p は素数）。 -/
theorem addEAlg_one_eq_shellAlg_iff (N : ℕ) [NeZero N] :
    addEAlg N 1 = shellAlg N ↔ Squarefree N ∨ N = 8 ∨ ∃ p, p.Prime ∧ N = p * p :=
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

### PAG.Part258.Lim（PAG258.lean）
```lean
/-- 帰納極限 lim_N (単数の上の関数)。 -/
abbrev Lim : Type := Module.DirectLimit Gsp pullSys
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

### PAG.Part258.UA1_star（PAG258.lean）
```lean
/-- **実数性**：U_N は複素共役と可換（U_N の核は実数値。KUK = U）。 -/
theorem UA1_star (f : (ZMod N)ˣ → ℂ) :
    UA1 (fun u => (starRingEnd ℂ) (f u)) = fun u => (starRingEnd ℂ) (UA1 f u) :=
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

### PAG.Part258.ip_UA1（PAG258.lean）
```lean
/-- U_N は ⟨·,·⟩ を保つ（単数の上の関数の空間全体でユニタリ）。 -/
theorem ip_UA1 (f g : (ZMod N)ˣ → ℂ) : ip (UA1 f) (UA1 g) = ip f g :=
```

### PAG.Part258.normSq_phaseA1（PAG258.lean）
```lean
/-- |phaseA1 χ|² = 1（χ* は原始的）。 -/
theorem normSq_phaseA1 (χ : DirichletCharacter ℂ N) : Complex.normSq (phaseA1 χ) = 1 :=
```

### PAG.Part258.phaseA1（PAG258.lean）
```lean
/-- A1 の位相 phaseA1(χ) = W(χ*)（χ* は χ を誘導する原始指標）。 -/
noncomputable def phaseA1 (χ : DirichletCharacter ℂ N) : ℂ := rootNum χ.primitiveCharacter
```

### PAG.Part258.phaseA1_inv（PAG258.lean）
```lean
/-- phaseA1(χ⁻¹) = conj phaseA1(χ)。 -/
theorem phaseA1_inv (χ : DirichletCharacter ℂ N) :
    phaseA1 χ⁻¹ = (starRingEnd ℂ) (phaseA1 χ) :=
```

### PAG.Part258.rootNum_inv（PAG258.lean）
```lean
/-- W(χ⁻¹) = conj W(χ)（すべての指標で）。 -/
theorem rootNum_inv (χ : DirichletCharacter ℂ N) :
    rootNum χ⁻¹ = (starRingEnd ℂ) (rootNum χ) :=
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

### PAG.Part259.dense_rho_image（PAG259.lean）
```lean
/-- **直積の位相では、像は稠密**：ℝ × (素数 → ℤ) のどの点 (x, k) の近傍（∞ の座標の ε 近傍と、有限個の素数の座標の
指定）にも、正の有理数の像がある。各近傍は有限個の素点しか見ない。これを著者の言葉の「完備化（極限）」にあたると読むのは読み。 -/
theorem dense_rho_image : Dense (rho '' {q : ℚ | 0 < q}) :=
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

### PAG.Part259.sep_of_commensurable（PAG259.lean）
```lean
/-- 対照群のまとめ：通約的な 2 つの対数の整数結合は、異なれば L₁/n 以上離れる（連続体は現れない）。 -/
theorem sep_of_commensurable {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) * L₂ = m * L₁) (a b a' b' : ℤ)
    (hne : (a : ℝ) * L₁ + b * L₂ ≠ a' * L₁ + b' * L₂) :
    L₁ / n ≤ |((a : ℝ) * L₁ + b * L₂) - (a' * L₁ + b' * L₂)| :=
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

### PAG.Part261.exists_listChar（PAG261.lean）
```lean
/-- **分解の存在**：法 lvl l（互いに素な法の積）の指標は、どれも成分の積 listChar χ l の形に書ける（Part 190 の `decomp` を使う）。 -/
theorem exists_listChar (l : List ι) (hnd : l.Nodup)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (Ψ : DirichletCharacter ℂ (lvl N l)) :
    ∃ χ : ∀ i, DirichletCharacter ℂ (N i), listChar χ l = Ψ :=
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

### PAG.Part261.listChar_injective（PAG261.lean）
```lean
/-- **分解の一意性**：listChar χ l = listChar χ' l なら、l の各成分で χ_i = χ'_i（Part 232 の `charMul_injective` を使う）。 -/
theorem listChar_injective (l : List ι) (hl : l.Pairwise fun i j => (N i).Coprime (N j))
    {χ χ' : ∀ i, DirichletCharacter ℂ (N i)} (h : listChar χ l = listChar χ' l) :
    ∀ i ∈ l, χ i = χ' i :=
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

### PAG.Part263.canon（PAG263.lean）
```lean
/-- 互いに素な段の標準の写像（(i)(ii)(iii) を満たす唯一の写像）。 -/
noncomputable def canon (hNM : N ∣ M) (hc : Nat.Coprime N (M / N)) : shellAlg N →ₐ[ℂ] shellAlg M :=
  ((existsUnique_compatF_iff hNM).mpr hc).exists.choose
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

## §D PAG256.lean（全文）
```lean
/-
  PAG 2.0 Part 252（2026-11-12）— 離散 Hartley 変換と反転 J の合成 J∘H_N/√N の、単数の上での原始指標についての式
  （読み：公理 A1 の境界ユニタリの原始指標の部分）
  問いの出所：著者の判断（2026-11-12 17:14「判断 3：Lean 化してください」）。重なりの読みは「ねじれた貼り合わせ（U）」
  （同日の著者の回答）。構築者が再構成したモノグラフ §1.3 の主張 (2)（A1 のもとで U = J∘H_N/√N）の、各レベル N の
  原始指標の部分と読める恒等式を Lean にする（読み。U と A1 は Lean の文に出てこない。照合ノート §5 の 6、着手前の文書の
  Q1。盲検の問いテストの S1）。
  記号：e = stdAddChar（e(t) = exp(2πi t.val/N)）、τ(χ) = gaussSum χ e、(H_N f)(y) = Σ_x f(x) cas(2π xy/N)、
  cas = cos + sin（離散 Hartley 変換）、(J g)(u) = g(u⁻¹)（単数の上）、W(χ) = τ(χ)/(i^a √N)（a = 0 は偶、a = 1 は奇）。
  1. Hartley の核：cas(2π t/N) = ((1 − i)e(t) + (1 + i)e(−t))/2
  2. 原始指標 χ について H_N χ = ε(χ)·τ(χ)·χ⁻¹。ε(χ) = ((1 − i) + (1 + i)χ(−1))/2 は偶で 1、奇で −i
  3. 単数でないところで H_N χ = 0（原始指標の部分は、単数の上の関数の空間に留まる）
  4. 単数 u で (J H_N χ)(u)/√N = W(χ)·χ(u)。|W(χ)| = 1
  5. 非空虚性の証人（法 3 の奇の原始指標、法 5 の偶で自明でない原始指標）と、除去テストの反例（原始性を外すと 3 と |W| = 1 が破れる）
  6.（独立照合の指摘で追加）単数の上の式 4 は原始性なしで成り立つ（`JH_eq_rootNum_mul_any`）。原始性が効くのは 3 と |W| = 1 だけ。
     除去テストの反例は、法 2（原始指標がないことは Lean の外）と、原始指標のある法 4（Lean の文に含めた）の両方で置いた
  どれも既知の事実の書き直し（再導出）：原始指標のガウス和はフーリエ係数（Mathlib の `gaussSum_mulShift_of_isPrimitive`）。
  Hartley の形で書いた文献は、盲検の問いテストでは見つからなかった（書き直しであって新しい内容ではない）。
  公理 A1 は Lean の公理にしていない。ここでの文は W（`rootNum`。原始指標ではルート数）についての恒等式である（読み：A1 は原始指標の
  位相をこの値に選ぶ公準）。

内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：前の鎖と同じ文・同じ値の定義（A。Lean で確認）は、
`inv_apply_neg_one`・`neg_one_mul_self`（Part 5・21・25・77）、`isPrimitive_of_prime_of_ne_one`（Part 167）、`casKer`（最初の形式化の Part 3（PAG3.lean）
の `casK` と同じ値）。前の宣言から直ちに出るもの（B。Lean で確認）は、`rootNum`（Part 192 の `zN` ÷ Part 194 の `gs` と同じ値）、
`inv_apply_units_inv`・`sum_mul_stdAddChar_neg`（最初の形式化の Part 3（PAG3.lean））。照合者の判定で数行で出るもの（C）は、`hartley_one`・`casKer_eq`
（最初の形式化の Part 3（PAG3.lean）の命題 2.8 `hartley_char`、`casK_even_part`・`casK_odd_part` から。この 2 件は Lean で確認）、`hartley_eq_of_isPrimitive`・
`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`（`hartley_char` などから。5 件とも
確信度 低、Lean では未確認）、`normSq_rootNum`（Part 12 の `normSq_gaussSum` から。Lean で確認）、`exists_primitive_odd_three`
（Part 115・163・167 から。Lean で確認）・`exists_primitive_even_five`、`parFac`・`rootNum_eq`（Part 194 の `gs`、最初の形式化の Part 2（PAG2.lean）の
`parity_weight`）。前の鎖に見つからなかったもの（網羅ではない）は、変換としての定義（`hartley`・`JH`）と、反例（`removal_counterexample` など）。
-/
import PAG255
import PAG16
import PAG144
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

namespace PAG.Part256

open ZMod Complex Finset

variable {N : ℕ} [NeZero N]

/-! ### 1. Hartley の核と離散 Hartley 変換 -/

/-- Hartley の核 cas(2π t/N) = cos(2π t/N) + sin(2π t/N)（t の代表は t.val）。
内部照合（2026-11-14）：最初の形式化の Part 3（PAG3.lean）の `casK` と同じ値（式の書き方は違う。Lean で値の一致を確認）。 -/
noncomputable def casKer (t : ZMod N) : ℂ :=
  ((Real.cos (2 * Real.pi * t.val / N) + Real.sin (2 * Real.pi * t.val / N) : ℝ) : ℂ)

/-- 離散 Hartley 変換 (H_N f)(y) = Σ_x f(x)·cas(2π xy/N)。 -/
noncomputable def hartley (f : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * casKer (x * y)

/-- **Hartley の核と標準の加法的指標**：cas(2π t/N) = ((1 − i)e(t) + (1 + i)e(−t))/2。 -/
theorem casKer_eq (t : ZMod N) :
    casKer t = ((1 - I) * stdAddChar t + (1 + I) * stdAddChar (-t)) / 2 := by
  set θ : ℝ := 2 * Real.pi * t.val / N with hθ
  have h1 : (stdAddChar t : ℂ) = Complex.exp ((θ : ℂ) * I) := by
    rw [stdAddChar_apply, toCircle_apply, hθ]
    congr 1
    push_cast
    ring
  have h2 : (stdAddChar (-t) : ℂ) = Complex.exp (-((θ : ℂ) * I)) := by
    rw [AddChar.map_neg_eq_inv, h1, Complex.exp_neg]
  rw [h1, h2, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  unfold casKer
  rw [← hθ]
  push_cast
  linear_combination (Complex.sin (θ : ℂ)) * Complex.I_sq

/-! ### 2. 原始指標の Hartley 変換 -/

/-- パリティ因子 ε(χ) = ((1 − i) + (1 + i)χ(−1))/2。 -/
noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2

omit [NeZero N] in
theorem parFac_of_even {χ : DirichletCharacter ℂ N} (h : χ.Even) : parFac χ = 1 := by
  unfold parFac
  rw [show χ (-1) = 1 from h]
  ring

omit [NeZero N] in
theorem parFac_of_odd {χ : DirichletCharacter ℂ N} (h : χ.Odd) : parFac χ = -I := by
  unfold parFac
  rw [show χ (-1) = -1 from h]
  ring

omit [NeZero N] in
/-- χ⁻¹(−1) = χ(−1)（χ(−1) = ±1）。
内部照合（2026-11-14）：Part 5（PAG9）の `inv_apply_neg_one`、Part 21（PAG25）の `chi_inv_neg_one`、Part 77（PAG81）の `inv_neg_one` と同じ文（Lean で両向きに確認）。 -/
theorem inv_apply_neg_one (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply_eq_inv']
  rcases χ.even_or_odd with h | h
  · rw [show χ (-1) = 1 from h, inv_one]
  · rw [show χ (-1) = -1 from h, inv_neg, inv_one]

/-- Σ_x χ(x) e(xy) をガウス和の形に。 -/
theorem sum_mul_stdAddChar (χ : DirichletCharacter ℂ N) (y : ZMod N) :
    ∑ x : ZMod N, χ x * stdAddChar (x * y) = gaussSum χ (stdAddChar.mulShift y) := by
  unfold gaussSum
  congr 1 with x
  rw [AddChar.mulShift_apply, mul_comm y x]

/-- **原始指標の Hartley 変換**：H_N χ = ε(χ)·τ(χ)·χ⁻¹（ℤ/N のすべての点で）。 -/
theorem hartley_eq_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (y : ZMod N) :
    hartley (χ : ZMod N → ℂ) y = parFac χ * gaussSum χ stdAddChar * χ⁻¹ y := by
  have hA : ∑ x : ZMod N, χ x * stdAddChar (x * y) = χ⁻¹ y * gaussSum χ stdAddChar := by
    rw [sum_mul_stdAddChar, gaussSum_mulShift_of_isPrimitive _ hχ]
  have hB : ∑ x : ZMod N, χ x * stdAddChar (-(x * y)) = χ⁻¹ (-y) * gaussSum χ stdAddChar := by
    rw [← gaussSum_mulShift_of_isPrimitive _ hχ, ← sum_mul_stdAddChar]
    congr 1 with x
    rw [mul_neg]
  have hneg : χ⁻¹ (-y) = χ (-1) * χ⁻¹ y := by
    rw [neg_eq_neg_one_mul, map_mul, inv_apply_neg_one]
  have hsplit : ∀ x : ZMod N, χ x * casKer (x * y) =
      (1 - I) / 2 * (χ x * stdAddChar (x * y)) + (1 + I) / 2 * (χ x * stdAddChar (-(x * y))) := by
    intro x
    rw [casKer_eq]
    ring
  unfold hartley
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB, hneg]
  unfold parFac
  ring

/-- **単数でないところで H_N χ = 0**（χ 原始的）。 -/
theorem hartley_eq_zero_of_not_isUnit {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {y : ZMod N} (hy : ¬IsUnit y) : hartley (χ : ZMod N → ℂ) y = 0 := by
  rw [hartley_eq_of_isPrimitive hχ, MulChar.map_nonunit _ hy, mul_zero]

/-! ### 3. ルート数と、J と Hartley 変換の合成 -/

open Classical in
/-- W(χ) = τ(χ)/(i^a √N)（a = 0 は偶、a = 1 は奇）。χ が原始ならルート数（関数等式との一致は Lean の外）。原始的でない
χ ではルート数ではなく、0 にもなる（法 4 の自明な指標）。
内部照合（2026-11-14）：Part 192（PAG196）の `zN` を Part 194（PAG198）の `gs` で割ったものと同じ値（Lean で確認）。 -/
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))

/-- W(χ) = ε(χ)·τ(χ)/√N。 -/
theorem rootNum_eq (χ : DirichletCharacter ℂ N) :
    rootNum χ = parFac χ * gaussSum χ stdAddChar / (Real.sqrt N : ℂ) := by
  unfold rootNum
  rcases χ.even_or_odd with h | h
  · simp only [h, ↓reduceIte]
    rw [parFac_of_even h]
    ring
  · have hne : ¬χ.Even := by
      intro he
      have e1 : χ (-1) = 1 := he
      have e2 : χ (-1) = -1 := h
      rw [e1] at e2
      norm_num at e2
    simp only [hne, ↓reduceIte]
    rw [parFac_of_odd h, div_eq_mul_inv, div_eq_mul_inv, mul_inv, Complex.inv_I]
    ring

/-- 単数の上の関数への J∘H_N/√N：(J H_N f)(u)/√N = (H_N f)(u⁻¹)/√N。 -/
noncomputable def JH (f : ZMod N → ℂ) (u : (ZMod N)ˣ) : ℂ :=
  hartley f ((u⁻¹ : (ZMod N)ˣ) : ZMod N) / (Real.sqrt N : ℂ)

omit [NeZero N] in
/-- χ⁻¹(u⁻¹) = χ(u)（u は単数）。
内部照合（2026-11-14）：最初の形式化の Part 3（PAG3.lean）の `apply_inv_eq_inv_apply` から 1 行で出る（Lean で確認）。 -/
theorem inv_apply_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ⁻¹ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u := by
  have h1 : χ (u : ZMod N) * χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [MulChar.inv_apply_eq_inv', eq_inv_of_mul_eq_one_right h1, inv_inv]

/-- χ が原始的なら、すべての単数 u で (H_N χ)(u⁻¹)/√N = W(χ)·χ(u)。式そのものは原始性なしで成り立つ
（`JH_eq_rootNum_mul_any`）。構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。
U と A1 は文に出てこない）。JH は ℤ/N の上の関数を単数の上の関数に送る写像で、同じ空間の上の固有値方程式ではない。 -/
theorem JH_eq_rootNum_mul {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u := by
  unfold JH
  rw [hartley_eq_of_isPrimitive hχ, rootNum_eq, inv_apply_units_inv]
  ring

/-- |W(χ)|² = 1（χ 原始的。Part 12（PAG16）の |τ(χ)|² = N から）。 -/
theorem normSq_rootNum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (rootNum χ) = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpar : Complex.normSq (parFac χ) = 1 := by
    rcases χ.even_or_odd with h | h
    · rw [parFac_of_even h, map_one]
    · rw [parFac_of_odd h, Complex.normSq_neg, Complex.normSq_I]
  have hsq : Complex.normSq (Real.sqrt N : ℂ) = N := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  rw [rootNum_eq, map_div₀, map_mul, hpar, PAG.Part16.normSq_gaussSum hχ, hsq, one_mul,
    div_self hN]

/-! ### 3b. 単数の上の式は原始性なしで成り立つ（独立照合の指摘を受けて追加）

原始性が効くのは、単数でないところで 0（`hartley_eq_zero_of_not_isUnit`）と |W| = 1（`normSq_rootNum`）だけ。
単数の上の固有値の式 `JH_eq_rootNum_mul_any` は、すべての指標で成り立つ（原始的でない指標では、固有値 ε(χ)τ(χ)/√N は
誘導元の原始指標のルート数と一致せず、絶対値は 1 未満になりうる）。 -/

/-- 単数 u で H_N χ (u⁻¹) = χ(u)·H_N χ (1)（x ↦ u·x の置換。原始性は要らない）。 -/
theorem hartley_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    hartley (χ : ZMod N → ℂ) ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u * hartley (χ : ZMod N → ℂ) 1 := by
  unfold hartley
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Units.mulLeft u) _ _ (fun x => ?_)).symm
  rw [Units.mulLeft_apply, map_mul, mul_one]
  have : (u : ZMod N) * x * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = x := by
    rw [mul_comm (u : ZMod N) x, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  ring

omit [NeZero N] in
/-- χ(−1)·χ(−1) = 1。
内部照合（2026-11-14）：Part 5（PAG9）の `chi_neg_one_sq`、Part 25（PAG29）の `chi_neg_one_sq'` と同じ文（Lean で両向きに確認）。 -/
theorem neg_one_mul_self (χ : DirichletCharacter ℂ N) : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

/-- Σ_x χ(x)e(−x) = χ(−1)·τ(χ)（x ↦ −x の置換。原始性は要らない）。
内部照合（2026-11-14）：最初の形式化の Part 3（PAG3.lean）の `sum_neg_twist` の x = 1 の場合（Lean で確認）。 -/
theorem sum_mul_stdAddChar_neg (χ : DirichletCharacter ℂ N) :
    ∑ x : ZMod N, χ x * stdAddChar (-x) = χ (-1) * gaussSum χ stdAddChar := by
  unfold gaussSum
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun x => ?_)
  have hx : χ (-x) = χ (-1) * χ x := by rw [← map_mul, neg_one_mul]
  rw [Equiv.neg_apply, hx]
  linear_combination (-(χ x * stdAddChar (-x))) * neg_one_mul_self χ

/-- H_N χ (1) = ε(χ)·τ(χ)（原始性は要らない）。 -/
theorem hartley_one (χ : DirichletCharacter ℂ N) :
    hartley (χ : ZMod N → ℂ) 1 = parFac χ * gaussSum χ stdAddChar := by
  have hsplit : ∀ x : ZMod N, χ x * casKer (x * 1) =
      (1 - I) / 2 * (χ x * stdAddChar x) + (1 + I) / 2 * (χ x * stdAddChar (-x)) := by
    intro x
    rw [mul_one, casKer_eq]
    ring
  unfold hartley
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, sum_mul_stdAddChar_neg]
  unfold parFac gaussSum
  ring

/-- **単数の上の固有値の式（すべての指標）**：(J H_N χ)(u)/√N = W(χ)·χ(u)。W(χ) = rootNum χ = ε(χ)τ(χ)/√N。
原始指標では W(χ) はルート数で |W(χ)| = 1（`normSq_rootNum`）。 -/
theorem JH_eq_rootNum_mul_any (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u := by
  unfold JH
  rw [hartley_units_inv, hartley_one, rootNum_eq]
  ring

/-! ### 4. 非空虚性の証人と、除去テストの反例 -/

/-- 素数の法では、自明でない指標は原始的。
内部照合（2026-11-14）：Part 167（PAG171）の `primitive_of_ne_one` と同じ文（Lean で両向きに確認）。 -/
theorem isPrimitive_of_prime_of_ne_one {p : ℕ} [hp : Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (h : χ ≠ 1) : χ.IsPrimitive := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  rcases hp.out.eq_one_or_self_of_dvd _ χ.conductor_dvd_level with h1 | h1
  · exact absurd ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h1) h
  · exact h1

/-- 証人（奇）：法 3 の奇の原始指標がある。 -/
theorem exists_primitive_odd_three : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Odd := by
  obtain ⟨χ, hχ⟩ :=
    DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ (show (-1 : ZMod 3) ≠ 1 by decide)
  have hodd : χ.Odd := by
    rcases χ.even_or_odd with h | h
    · exact absurd h hχ
    · exact h
  have hne : χ ≠ 1 := by
    rintro rfl
    exact hχ (MulChar.one_apply (isUnit_neg_one))
  exact ⟨χ, isPrimitive_of_prime_of_ne_one hne, hodd⟩

/-- 証人（偶）：法 5 の偶で自明でない原始指標がある（奇の χ をとった場合は χ² を使う）。 -/
theorem exists_primitive_even_five :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Even ∧ χ ≠ 1 := by
  have h21 : (2 : ZMod 5) ≠ 1 := by decide
  have hm1 : (-1 : ZMod 5) = 2 * 2 := by decide
  have hu2 : IsUnit (2 : ZMod 5) := ⟨⟨2, 3, by decide, by decide⟩, rfl⟩
  have hp5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ h21
  rcases χ.even_or_odd with he | ho
  · have hne : χ ≠ 1 := by
      rintro rfl
      exact hχ (MulChar.one_apply hu2)
    exact ⟨χ, isPrimitive_of_prime_of_ne_one hne, he, hne⟩
  · -- χ(2)² = χ(−1) = −1 なので χ² は偶で、χ²(2) = −1 ≠ 1
    have h22 : χ 2 * χ 2 = -1 := by
      rw [← map_mul, ← hm1]
      exact ho
    have heven : (χ * χ).Even := by
      show (χ * χ) (-1) = 1
      rw [MulChar.mul_apply, show χ (-1) = -1 from ho]
      ring
    have hne : χ * χ ≠ 1 := by
      intro h1
      have := congrArg (fun ψ : DirichletCharacter ℂ 5 => ψ 2) h1
      simp only [MulChar.mul_apply, MulChar.one_apply hu2] at this
      rw [h22] at this
      norm_num at this
    exact ⟨χ * χ, isPrimitive_of_prime_of_ne_one hne, heven, hne⟩

/-- 除去テストの反例：原始性を外すと「単数でないところで 0」が破れる（法 2 の自明な指標、y = 0）。 -/
theorem removal_counterexample :
    ¬(1 : DirichletCharacter ℂ 2).IsPrimitive ∧ ¬IsUnit (0 : ZMod 2) ∧
      hartley ((1 : DirichletCharacter ℂ 2) : ZMod 2 → ℂ) 0 = 1 := by
  refine ⟨?_, not_isUnit_zero, ?_⟩
  · rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]
    norm_num
  · have key : ∀ b : ZMod 2, b ≠ 1 → b = 0 := by decide
    unfold hartley casKer
    simp only [mul_zero, ZMod.val_zero, Nat.cast_zero, zero_div, Real.cos_zero, Real.sin_zero,
      add_zero, Complex.ofReal_one, mul_one]
    rw [Finset.sum_eq_single (1 : ZMod 2)]
    · exact map_one _
    · intro b _ hb
      rw [key b hb]
      exact MulChar.map_nonunit _ not_isUnit_zero
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- 法 2 の自明な指標で |rootNum|² = 1/2。原始的でないことは `removal_counterexample` の第 1 成分で、2 つを合わせて
|W| = 1 の除去テストの反例になる。 -/
theorem removal_counterexample_normSq :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ 2)) = 1 / 2 := by
  have key : ∀ b : ZMod 2, b ≠ 1 → b = 0 := by decide
  have he1 : (stdAddChar (1 : ZMod 2) : ℂ) = -1 := by
    rw [stdAddChar_apply, toCircle_apply, ZMod.val_one]
    push_cast
    rw [show 2 * (Real.pi : ℂ) * I * 1 / 2 = Real.pi * I by ring, Complex.exp_pi_mul_I]
  have hg : gaussSum (1 : DirichletCharacter ℂ 2) stdAddChar = -1 := by
    unfold gaussSum
    rw [Finset.sum_eq_single (1 : ZMod 2)]
    · rw [map_one, one_mul, he1]
    · intro b _ hb
      rw [key b hb, MulChar.map_nonunit _ not_isUnit_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have heven : (1 : DirichletCharacter ℂ 2).Even := MulChar.one_apply isUnit_neg_one
  rw [rootNum_eq, parFac_of_even heven, hg, map_div₀, Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- 除去テストの反例（原始指標がある法 4 で。独立照合 B の指摘を受けて追加）：法 4 には原始指標があるが
（Part 140 の `exists_primitive`）、自明な指標（原始的でない）では、単数でない 2 で H_N χ (2) = −2 ≠ 0、
|W|² = 0（τ = i − i = 0）。法 2 の反例と違い、原始指標のある法でも原始性を外すと 2 つの文が破れることを示す。 -/
theorem removal_counterexample_four :
    (∃ χ : DirichletCharacter ℂ (2 ^ 2), χ.IsPrimitive) ∧
    ¬(1 : DirichletCharacter ℂ 4).IsPrimitive ∧ ¬IsUnit (2 : ZMod 4) ∧
      hartley ((1 : DirichletCharacter ℂ 4) : ZMod 4 → ℂ) 2 = -2 ∧
      Complex.normSq (rootNum (1 : DirichletCharacter ℂ 4)) = 0 := by
  have hu3 : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have hn2 : ¬IsUnit (2 : ZMod 4) := by
    rintro ⟨u, hu⟩
    have key : ∀ a : ZMod 4, 2 * a ≠ 1 := by decide
    exact key ((u⁻¹ : (ZMod 4)ˣ) : ZMod 4) (by rw [← hu, Units.mul_inv])
  have hn0 : ¬IsUnit (0 : ZMod 4) := by
    rintro ⟨u, hu⟩
    have key : ∀ a : ZMod 4, 0 * a ≠ 1 := by decide
    exact key ((u⁻¹ : (ZMod 4)ˣ) : ZMod 4) (by rw [← hu, Units.mul_inv])
  have key02 : ∀ y : ZMod 4, y ≠ 1 ∧ y ≠ 3 → y = 0 ∨ y = 2 := by decide
  have h13 : (1 : ZMod 4) ≠ 3 := by decide
  refine ⟨PAG.Part144.exists_primitive 2 le_rfl, ?_, hn2, ?_, ?_⟩
  · rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]
    norm_num
  · unfold hartley
    rw [Fintype.sum_eq_add (1 : ZMod 4) (3 : ZMod 4) h13]
    · have h12 : (1 : ZMod 4) * 2 = 2 := by decide
      have h32 : (3 : ZMod 4) * 2 = 2 := by decide
      have hθ : 2 * Real.pi * ((2 : ZMod 4).val : ℝ) / ((4 : ℕ) : ℝ) = Real.pi := by
        rw [show (2 : ZMod 4).val = 2 from rfl]
        push_cast
        ring
      have hc : casKer (2 : ZMod 4) = -1 := by
        unfold casKer
        rw [hθ, Real.cos_pi, Real.sin_pi]
        push_cast
        ring
      rw [h12, h32, hc, MulChar.one_apply isUnit_one, MulChar.one_apply hu3]
      ring
    · intro x hx
      rcases key02 x hx with rfl | rfl
      · rw [MulChar.map_nonunit _ hn0, zero_mul]
      · rw [MulChar.map_nonunit _ hn2, zero_mul]
  · have he1 : (stdAddChar (1 : ZMod 4) : ℂ) = I := by
      rw [stdAddChar_apply, toCircle_apply, show (1 : ZMod 4).val = 1 from rfl]
      push_cast
      rw [show 2 * (Real.pi : ℂ) * I * 1 / 4 = Real.pi / 2 * I by ring, Complex.exp_pi_div_two_mul_I]
    have he3 : (stdAddChar (3 : ZMod 4) : ℂ) = -I := by
      rw [show (3 : ZMod 4) = -1 by decide, AddChar.map_neg_eq_inv, he1, Complex.inv_I]
    have hg : gaussSum (1 : DirichletCharacter ℂ 4) stdAddChar = 0 := by
      unfold gaussSum
      rw [Fintype.sum_eq_add (1 : ZMod 4) (3 : ZMod 4) h13]
      · rw [MulChar.one_apply isUnit_one, MulChar.one_apply hu3, he1, he3]
        ring
      · intro x hx
        rcases key02 x hx with rfl | rfl
        · rw [MulChar.map_nonunit _ hn0, zero_mul]
        · rw [MulChar.map_nonunit _ hn2, zero_mul]
    rw [rootNum_eq, hg, mul_zero, zero_div, map_zero]

end PAG.Part256

#print axioms PAG.Part256.casKer
#print axioms PAG.Part256.hartley
#print axioms PAG.Part256.casKer_eq
#print axioms PAG.Part256.parFac
#print axioms PAG.Part256.parFac_of_even
#print axioms PAG.Part256.parFac_of_odd
#print axioms PAG.Part256.inv_apply_neg_one
#print axioms PAG.Part256.sum_mul_stdAddChar
#print axioms PAG.Part256.hartley_eq_of_isPrimitive
#print axioms PAG.Part256.hartley_eq_zero_of_not_isUnit
#print axioms PAG.Part256.rootNum
#print axioms PAG.Part256.rootNum_eq
#print axioms PAG.Part256.JH
#print axioms PAG.Part256.inv_apply_units_inv
#print axioms PAG.Part256.JH_eq_rootNum_mul
#print axioms PAG.Part256.normSq_rootNum
#print axioms PAG.Part256.isPrimitive_of_prime_of_ne_one
#print axioms PAG.Part256.exists_primitive_odd_three
#print axioms PAG.Part256.exists_primitive_even_five
#print axioms PAG.Part256.removal_counterexample
#print axioms PAG.Part256.hartley_units_inv
#print axioms PAG.Part256.neg_one_mul_self
#print axioms PAG.Part256.sum_mul_stdAddChar_neg
#print axioms PAG.Part256.hartley_one
#print axioms PAG.Part256.JH_eq_rootNum_mul_any
#print axioms PAG.Part256.removal_counterexample_normSq
#print axioms PAG.Part256.removal_counterexample_four
```

## §E Part 257 の記録

### PAG261.lean の冒頭 75 行
```lean
/-
アーデル射影幾何 — Part 257（PAG 2.0）：互いに素な法の並びの指標の積での、ガウス和と W の分解（成分の τ・W の積と、交差項・符号）

問いの出所：著者の選択（2026-11-14 20:59、着手前の文書 `pag2_part257_preregistration.md` の候補 P1）。開始条件 2（方向βの
登録ファイルとの突き合わせ）は、著者の判断で保留のまま始めた（登録ファイルは届いていない）。
幾何の言葉での問い（読み）：大域の貼り合わせ（U の固有値 phaseA1。原始の指標では W = rootNum）は、∞ を含む各点の局所の因子の積に
分かれるか。各点の因子は、どこまでその点だけで決まるか。
Lean が答えるのは、互いに素な法の並び N_1, …, N_k の指標の積（法 N_1·…·N_k）の上での、ガウス和 τ と W の式まで。

読みの言葉：「貼り合わせ U」「公準 A1 の位相」は Part 254（PAG258.lean）の `UA1`・`phaseA1`。W は Part 252（PAG256.lean）の
`rootNum`（= τ(χ)/(i^a·√n)。原始のときルート数）、偶奇の因子 `parFac`（偶で 1、奇で −i）。「素点」「局所因子」「重なり」は
著者の解釈の層の言葉で、Lean の文には出てこない。偶奇の因子が無限素点の局所因子にあたる、も読み。

Lean の文（すべて既知の事実の Lean 化。互いに素な法でのガウス和の乗法性を繰り返したものと、そのルート数版）：
1. 法の並びの積 `lvl`（先頭 × 残り）と指標の積 `listChar`（先頭の指標と残りの積を Part 256 の `prodChar` でつなぐ）。
   値は成分の値の積（`listChar_natCast`：自然数で、`listChar_neg_one`：−1 で）。
2. ガウス和：τ(listChar χ l) = 交差項·∏_i τ(χ_i)（`gaussSum_listChar`。法は互いに素。原始性は要らない）。交差項 `cross` は
   漸化式で定め、閉じた形が 2 つ：形 (I) ∏_i χ_i(∏_{j≠i} N_j)（`cross_eq_formI`）と形 (II) ∏_i ∏_{j≠i} χ_j(N_i)
   （`cross_eq_formII`。成分 i の因子を、ほかの成分を N_i で読んだ値で書く形）。
3. W：W(listChar χ l) = ε_∞·∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)/√N_i（`rootNum_listChar_formI`）、
   = ε_∞·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)（`rootNum_listChar_formII`）。ε_∞ = `parFac`(listChar χ l)。
4. ∞ の因子の符号：ε_∞(listChar χ l) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数 `oddCount`。`parFac_listChar`）。
   したがって W(listChar χ l) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（`rootNum_listChar`。成分 2 つでは、法 N_a·(N_b·1) の上で
   Part 256 の `rootNum_prodChar` と同じ式になる。Lean ではつないでいない）。
5. 原始性：すべての成分が原始 ⇔ 積が原始（`isPrimitive_listChar_iff`）。原始なら UA1 の固有値 phaseA1 も同じ式
   （`phaseA1_listChar`）。
6. 分解：法 lvl l の指標は、どれも成分の積 listChar χ l の形に書け（`exists_listChar`。並びに重複なし）、成分は一意
   （`listChar_injective`。Part 256 の `prodChar` が Part 232 の `charMul` と同じ定義であることを使って、`charMul_injective` を当てる）。
7. すべての素数への分解：法 n の指標 Ψ は、素数冪の法 p^{v_p(n)}（0 でないことは Part 236（PAG240）の instance `neZero_ordProj`）の成分 χ_p で、自然数での値が ∏_p χ_p(x)、
   τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)})（`gaussSum_primeFactors`。形 (II)）。退化例（成分 1 つ）は τ(listChar χ [a]) = τ(χ_a)
   （`gaussSum_listChar_singleton`）。

前の鎖の定理を使い、示し直していないもの：Part 199（PAG203）の `gaussSum_level_one`、Part 236（PAG240）の `neZero_ordProj`、Part 189（PAG193）の `gaussSum_mul_coprime`・`mul_changeLevel_apply`、
Part 190（PAG194）の `decomp`・`isPrimitive_iff`・`comp₁_mul`・`comp₂_mul`、Part 232（PAG236）の `charMul_injective`、
Part 252（PAG256）の `rootNum_eq`・`parFac_of_even`、Part 254（PAG258）の `phaseA1_of_isPrimitive`、Part 256（PAG260）の
`prodChar`・`prodChar_neg_one`・`parFac_prodChar`・`crossSign`。

言い方の注意：文献では、大域の ε 因子は局所の ε 因子の積（Tate、Deligne）。原始指標 χ を素数冪の成分 χ_p に分け、
χ に対応するイデール類指標 ω を ω_q(q) = χ(q)（不分岐な q）と正規化し、加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}
（Tate の学位論文の規約）にとると、形 (II) の p の因子 (τ(χ_p)/√p^{e_p})·∏_{q≠p} χ_q(p^{e_p}) は ω の p での局所定数と一致し、
∞ の局所定数は i^{−a}（着手前の盲検の問いテストと私の手計算。確信度 中〜高。Lean では示していない）。原始でない成分や、
素数冪でない法の成分では、この一致は言えない（例：法 p の自明な指標の因子は −1/√p）。ψ の規約を逆にすると各 p の因子が
χ_p(−1) 倍、∞ の因子が i^{a} になるが、積は変わらない。ω を χ̄ に対応させる規約では、積が W の共役になる（盲検の申告）。
問いの後半について（読み）：Lean の恒等式が言うのは、交差項を成分ごとの因子に配る書き方が 2 通りあることまで。形 (II) では
成分 i の因子がほかの成分の値 χ_j(N_i) を含み、形 (I) ではほかの法 N_j を含む。どちらの書き方でも、成分 i の因子は (χ_i, N_i)
だけでは決まらない。「どう書いても (χ_i, N_i) だけでは決まらない」ことは恒等式からは出ない（Lean の外。手計算の見込み、確信度 中）。
∞ の因子 ε_∞ は合成した指標の偶奇（∞ の点の情報）で決まり、成分の ε_∞ の積とは符号 (−1)^{k(k−1)/2} だけずれる（`parFac_listChar`）。
これは別の話で、∞ の因子が ∞ の外の情報に依存することを示すものではない。A1 は公準のまま。ここでの文は τ・W・phaseA1 についての恒等式で、A1 から何かを出すものではない。

範囲：互いに素な法の並び（リスト）の上の式。法 n の任意の指標についての文は 7 のガウス和と成分の存在まで（W の形は、listChar の形の
指標の上で 3・4。成分の一意性は listChar の形でだけ言い（`listChar_injective`）、法 n の形では文にしていない）。Lean にしていないこと（数値は step280.py の項目番号）：イデール類指標と Tate の局所定数そのもの、
原始でない指標の phaseA1 を導手を割る素点だけで書く形（着手前の数値 (5)）、並べ替えで listChar の値が変わらないこと
（数値 (10)）、対照群 F_q[t]（∞ の因子は √q/τ(η)。盲検の答えで、私は計算していない）。

内部照合（2026-11-14 からの必須の手順）：着手の前に、xlsx の「定理と証明」と Lean の全宣言の文を検索した。成分 2 つの式は
前の鎖にある（Part 189 の `gaussSum_mul_coprime`・`z_mul_coprime`、Part 256 の `rootNum_prodChar`）。任意個の成分の明示の積、
形 (II)、符号 (−1)^{k(k−1)/2} の文は見つからなかった（網羅ではない）。近いもの：Part 192（PAG196）の `z_hall`（ホール成分 2 つ、
ずれは「1 の冪根がある」の形）、Part 193（PAG197）の `LocalCrit`・`prod_root_iff_local`（平方因子のない素数成分での、1 の冪根に
なる条件）、Part 127（PAG131）以降の素数冪の成分の積の位数の定理（積 ∏ τ(χ_i)/√ の位数で、合成した指標の τ ではない）。
閉じる前の照合（全宣言の書き出し、候補選び上位 20、`#dupcheck`・`#defeqcheck` を両向きに）：1 回目（4313 件、PAG261 の 34 件、
1230 回）で、下書きの `gaussSum_level_one` が Part 199（PAG203）の同名の定理と同じ文、法 p^{v_p(n)} が 0 でないことの instance
`ppow_neZero` が Part 236（PAG240）の `neZero_ordProj` と同じ文だった（どちらも Lean で両向きに確認）。この 2 つと、instance の
ために置いた定義 `ppow`（p^{v_p(n)}。Part 236 にも別の `ppow` がある）を消して前の鎖のものを使った。2 回目（4310 件、31 件、
1132 回）は一致 0。照合者 B の指摘で、下書きの `not_odd_of_even` も Mathlib の `DirichletCharacter.Even.not_odd` と同じ文なので
消した（Mathlib との重複はこの手順では探していない）。網羅ではない（候補選びは型に現れる定数の近さで、上位 20 まで）。
追記（2026-11-15、Part 258 の照合の後の言葉の検索）：Part 236（PAG240）の互いに素な法のリストの枠組み（`prodList`・`CoprimeList`・
`coprime_prodList`・`prodList_eq_prod`・`ppList`・`prodList_ppList`）と、この Part の `lvl`・`coprime_lvl`・`lvl_eq_prod`・`lvl_primeFactors`
は同じ構成（型が違う：ℕ+ のリストと、ι で添字づけた法）。機械的な照合では拾えなかった。主な文の中身は変わらない。
-/
import PAG260

open ZMod Complex

namespace PAG.Part261

```

### notes/pag2_part257_local_factor_decomposition.md（冒頭 60 行）

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
| 交差項 | `cross χ l` | 漸化式 cross (a::l) = χ_a(lvl l)·listChar l (N_a)·cross l |
| k | `oddCount χ l` | 奇の成分の数 |

### 0.3 ラベル（CLAUDE.md §7）

| 結果 | ラベル | 根拠 |
|---|---|---|
| ガウス和の分解（形 (I)） | 既知 | Montgomery–Vaughan, Theorem 9.6 の繰り返し |
| 形 (II)、W の形、∞ の因子の符号 | 既知（再導出） | Tate の局所定数の積公式の GL(1)/ℚ の場合（盲検：Rohrlich の講義ノート (2.49)・(2.55)） |
| 原始性、分解の存在と一意性 | 既知 | 中国剰余定理と導手の標準の事実 |
| 「局所因子」「素点」「貼り合わせ」の読み | 著者の解釈の層と読み | — |

- 新規候補：なし。

## 1. 検証表
