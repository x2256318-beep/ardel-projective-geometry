# 統合照合の入力（2026-11-18 夜）

この入力は、ある研究プロジェクトの記録の一部です。§A は前回の照合の後に入った変更の差分、§B・§C は変更後のノートの全文、§D は CLAUDE.md の該当する箇条の全文、§E は Lean の形式文の全文です。

## §A 差分

### A1 材料ノート（照合済みの第 2 版 → 現行の第 5 版）
```diff
--- records/prereg_projection/before_material_v2.md	2026-11-18 18:51:36.923337038 +0900
+++ notes/pag2_projection_material.md	2026-11-18 19:26:07.062927278 +0900
@@ -1,8 +1,11 @@
 # アーデル射影幾何 — 命名にある「射影」の材料（基礎文書の第 1・2 章のための対応表）
 
-（2026-11-18。短期層の小さいノート。事前登録 `pag2_prereg_projection.md` の結論（残余は空、新しいパートは始めない）を受けて、基礎文書の起草（著者側）に渡す材料をまとめる。**ここに書く「射影」の読みは構築側の読みで、著者の確認待ちである。** 著者の定義（CLAUDE.md §1）の文面は変えない。第 1 版は独立照合を受け、その指摘で直した版がこれである（§7）。）
+（2026-11-18。短期層の小さいノート。事前登録 `pag2_prereg_projection.md` の結論（残余は空、新しいパートは始めない）を受けて、基礎文書の起草（著者側）に渡す材料をまとめる。**ここに書く「射影」の読みは構築側が出した読みで、2026-11-18 19:01 に著者が留保つきで採用した（§6）。** 採用は読み（解釈の層）としての採用で、形式化済みの定理ではない。著者の定義（CLAUDE.md §1）の文面は変えない。第 1 版と第 2 版がそれぞれ独立照合を受け、その指摘で直した第 3 版に著者の決定を記録したのが第 4 版、文献照合の後の著者の決定を足したのがこの第 5 版である（§7〜§10）。）
 
-記号：反転（0 と ∞ の入れ替え、x ↦ 1/x）は **ι** と書く。Lean の宣言名 `W`・`Wpt`・`Wproj` とモノグラフの W は、この反転を指す。ルート数は **𝔀(χ)**（Lean の `PAG.Part256.rootNum`）と書き、反転と区別する。
+記号：
+- 反転（0 と ∞ の入れ替え、x ↦ 1/x）は **ι** と書く。Lean の宣言 `PAG.Part23.W`・`PAG.Part26.Wpt`・`PAG.Part27.Wproj` とモノグラフの W は、この反転を指す。
+- `PAG.Part256.rootNum` の値（τ(χ)/(i^a √N)、すべての指標 χ で定義）を **𝔀(χ)** と書く。原始指標ではルート数（その同定は Lean の外）。注意：PAG256 の docstring と冒頭のコメントでは、記号 W(χ) がこの 𝔀(χ) を指す（反転ではない）。
+- τ(χ) はガウス和（加法指標は Mathlib の `stdAddChar`、e(t) = exp(2πit/N)）、a は χ が奇なら 1、偶なら 0。
 
 ## §1 著者の言葉（定義の層）
 
@@ -10,53 +13,101 @@
 - 無限素点（2026-11-12・11-16）：無限大と無限小が重なり合う。−∞ と ∞ と 0 が射影によって重なる。この重なりを境界ユニタリ U によるねじれた貼り合わせと読む。
 - 構築側の読み（2026-11-16 に著者確認）：ℝ_{>0} を対数で ℝ に移すと乗法の 0・∞ が加法の −∞・+∞ になり、射影直線では両端が一点になる。反転 x ↦ 1/x は 0 と ∞ を入れ替える。
 
-## §2 「射影」の読み（構築側、著者の確認待ち）
+## §2 「射影」の読み（構築側が出し、著者が 2026-11-18 に留保つきで採用）
 
-命名の「射影による融合」を、次の 3 つの層の組として読む。
+命名の「射影による融合」を、次の 3 つの層の組として読む。著者の決定では、命名の「射影」は舞台と変換の両方を指し、主は変換である（舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ。§6）。
 
 1. **舞台（座標）**：射影直線 P¹。2 つのチャート（0 の側 [x:1] と ∞ の側 [1:y]）が赤道（単数）の上で y ↦ y⁻¹ によってつながり、反転 ι が 0 と ∞ を入れ替える。
-2. **作用素（融合）**：乗法の側の反転 ι と、加法の側のフーリエ変換を合成した作用素。乗法の関数（指標）に作用させる。
-3. **位相（公準）**：原始指標 χ については、その作用素の成分が絶対値 1 の位相になる。公準 A1 は、境界ユニタリ U の原始指標の位相をこの値に選ぶ公準である。原始的でない指標では、成分は一般に位相ではない（絶対値が 1 未満になり、0 にもなる）。
+2. **変換（融合）**：乗法の側の反転 ι と、加法の側のフーリエ型の変換を合成した写像。乗法の関数（指標）に作用させる。有限レベル N では、ℤ/N の関数を単数の上の関数に送る写像で、同じ空間の上の作用素ではない（§3 の表 2 行目）。
+3. **位相（公準）**：原始指標 χ については、その変換の成分が絶対値 1 の位相になる。標準の核は Part 252 の Hartley 核とする（著者の決定、§6）。この核での値は 𝔀(χ) = τ(χ)/(i^a √N)（`rootNum`）である。加法指標は規約 T（Tate の学位論文の加法指標：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）を標準とし、その規約で因子 ε(χ) = (−i)^a は無限素点の局所定数と一致する（値の一致、Lean の外。注意 2 の最後の項）。PAG256 の冒頭のコメントの読みでも、公準 A1 は境界ユニタリ U の原始指標の位相をこの値に選ぶ公準である。原始的なら 𝔀(χ) がルート数であることは Lean の外である。素朴なフーリエ核では、奇の χ で値がこの値と i 倍ずれる（注意 2。このずれは標準の核を決めても消えない）。原始的でない指標では、成分は位相でないことがある（絶対値が 1 未満になり、0 にもなる例がある。§3 の表 3 行目）。
 
-注意 1（照合者の指摘）：1 と 2 は種類が違う。1 の y ↦ y⁻¹ はチャートの座標変換（関数を P¹ の上で定義するための恒等式）で、ねじれを持たない。ねじれ（指標ごとの位相）は 2 の作用素の側にある。Lean でも、2 の作用素（`PAG.Part256.JH`）と 1 の 2 チャートモデル（`PAG.Part23.Compat` など）を結ぶ文はない。
+注意 1（照合者の指摘）：1 と 2 は種類が違う。1 の y ↦ y⁻¹ はチャートの座標変換（関数を P¹ の上で定義するための恒等式）で、ねじれを持たない。ねじれ（指標ごとの位相）は 2 の変換の側にある。Lean でも、照合した範囲（PAG23・PAG26・PAG27・PAG256）では、2 の写像（`PAG.Part256.JH`）と 1 の 2 チャートモデル（`PAG.Part23.Compat` など）を結ぶ文はない。
 
-注意 2（照合者の指摘で直した）：2 の作用素の「加法のフーリエ変換」に何を使うかで、位相が変わる。
-- 加法のフーリエ核 e(xy) そのものを使うと、原始指標 χ と単数 u での成分は τ(χ)/√N（ガウス和を √N で割ったもの）になる。Lean では `PAG.Part256.sum_mul_stdAddChar` と Mathlib の `gaussSum_mulShift_of_isPrimitive` から数行で出る（Lean の独立した定理としては置いていない。`hartley_eq_of_isPrimitive` の証明の中の式 `hA`）。
-- Part 252 の離散 Hartley 変換（cas 核 cos + sin。核は ((1 − i)e(t) + (1 + i)e(−t))/2、`PAG.Part256.casKer_eq`）を使うと、成分は 𝔀(χ) = ε(χ)τ(χ)/√N になる。ε(χ) は偶で 1、奇で −i（`parFac`）。原始的なら 𝔀(χ) はルート数 τ(χ)/(i^a √N)（a は奇で 1、偶で 0）。
-- 二つは偶の χ で一致し、奇の χ で i 倍ずれる。Tate の局所分解の通常の規約では、ルート数の i^a は無限素点の局所因子から来る（照合者の知識による。規約による符号の違いを含め、文献で未確認。確信度：中）。そうだとすると、有限素点の作用素の位相は τ(χ)/√N で、Part 252 の Hartley の形は無限素点の符号の因子を有限レベルの作用素に取り込んだ形と読める。基礎文書で使う前に文献で確かめる。
+注意 2（照合者の指摘で直した。式は加法核 e(xy) の規約で書く）：2 の変換の「加法のフーリエ型の変換」に何を使うかで、位相が変わる。N は法、u は単数。
+- **素朴なフーリエ核 e(xy)**：成分は τ(χ)/√N。
+  - 導出：`PAG.Part256.hartley_eq_of_isPrimitive` の証明の中の式 `hA`（∑ₓ χ(x) e(xy) = χ⁻¹(y) τ(χ)、`PAG.Part256.sum_mul_stdAddChar` と Mathlib の `gaussSum_mulShift_of_isPrimitive` から）に y = u⁻¹ を入れ、`PAG.Part256.inv_apply_units_inv`（χ⁻¹(u⁻¹) = χ(u)）を使って √N で割ると、(τ(χ)/√N)·χ(u) になる。独立した定理としては Lean に置いていない。
+  - 単数の上では原始性は要らない（`PAG.Part256.hartley_units_inv` と同じ置換 x ↦ u·x の議論。照合者が N ≤ 30 のすべての指標で数値確認。数値は証明ではない）。
+  - **核の符号に依存する**：核を e(−xy) にすると、成分は χ(−1)τ(χ)/√N になる（`PAG.Part256.hartley_eq_of_isPrimitive` の証明の中の式 `hB`・`hneg` から。y = 1 の場合は `PAG.Part256.sum_mul_stdAddChar_neg`）。「素朴なフーリエ核」は符号の規約を決めるまで一つに決まらない。
+- **Part 252 の離散 Hartley 核**（cas = cos + sin。核は ((1 − i)e(t) + (1 + i)e(−t))/2、`PAG.Part256.casKer_eq`）：成分は 𝔀(χ) = ε(χ)τ(χ)/√N。ε(χ) は `PAG.Part256.parFac` で、偶で 1、奇で −i（`parFac_of_even`・`parFac_of_odd`）。すべての χ について `PAG.Part256.JH_eq_rootNum_mul_any` と `PAG.Part256.rootNum_eq` から出る。式 𝔀(χ) = τ(χ)/(i^a √N) は `rootNum` の定義そのもので、すべての χ で成り立つ。原始的なら 𝔀(χ) がルート数であることは Lean の外（`rootNum` の docstring）。
+- **二つの関係（e(xy) の規約で）**：偶の χ では一致する（どちらも τ(χ)/√N）。奇の χ では 𝔀(χ) = −i·τ(χ)/√N、すなわち素朴な成分 = i·𝔀(χ)。核を e(−xy) にすると関係は反転し、𝔀(χ) = i·（素朴な成分）になる。
+- **帰属の読み（候補として留保。未確認）**：Tate の局所分解の通常の規約では、ルート数の i^a は無限素点の局所因子から来る（照合者の知識による。確信度：中）。ただし大域の加法指標は無限素点と有限素点とで符号を逆に取るのが通例で、有限素点の局所因子が τ(χ)/√N になるか χ(−1)τ(χ)/√N になるかは規約で変わりうる（再照合者の知識。確信度：低〜中）。この読みが正しければ、Part 252 の Hartley の形は、無限素点の符号の因子を有限レベルの変換に取り込んだ形と読める。著者の決定（§6）により、文献照合が済むまでは i^a を正規化因子として書き、この帰属は候補として留保する。i^a の帰属と有限素点の加法指標の符号の文献照合は、基礎文書が無限素点の読みを断定する前に行う。→ 2026-11-18 に照合した（`pag2_literature_ia_sign.md`、独立照合 1 回）。結果：i の冪は無限素点から来る（規約によらない）。符号 ξ(−1) の置き場は規約による。Tate の学位論文の加法指標の規約（ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）では、ε(χ) = (−i)^a が無限素点の局所定数と、τ(χ)/√N が有限素点の局所定数の積と一致する（値の一致。Lean の外）。同日、著者の決定で、i^a を正規化因子として留保する扱いを外し、規約 T を基礎文書の標準とした（§6 の 4・5）。
 
 ## §3 対応表
 
 | 層 | 有限レベル（ℤ/N） | 無限素点 | ラベル |
 |---|---|---|---|
-| 舞台：射影直線と反転 | P¹(ℤ/N) := 単模ベクトル / 単数倍（Part 23、`PAG.Part27.ProjLine`）。反転 [a:b] ↦ [b:a]（`PAG.Part27.Wproj`、対合 `Wproj_Wproj`。一般の N）。p 素数、K ≥ 1 で、点モデル（Part 22、`PAG.Part26.Pt`）と同型（`PAG.Part27.projEquiv`）、点の数 p^K + p^(K−1)（`PAG.Part27.card_ProjLine`）、反転どうしが対応（`PAG.Part27.toProj_Wpt`）。2 チャートモデルと赤道での貼り合わせ F_N(y) = F_S(y⁻¹)（Part 19、`PAG.Part23.Compat`、反転 `PAG.Part23.W`。点モデルの関数との同型は `PAG.Part26.ptEquiv`、反転の対応は `PAG.Part26.toP1_comp_Wpt`）。**2 チャートモデルが P¹ のモデルになるのは N = p^K（K ≥ 1）のときだけ**（一般の N では点モデルと P¹ の点の数が違う。照合者の数え上げで N = 6 は 10 点と 12 点）。0 = [0:1] と ∞ = [1:0] は別の点で、反転がこの 2 点を入れ替える（有限の側に点の同一視はない） | P¹(ℝ)。ℝ_{>0} の対数座標 t = log x で、反転 x ↦ 1/x は t ↦ −t になり、両端 −∞・+∞（乗法の 0・∞）を入れ替える。射影直線では両端が一点（著者確認済みの読み）。有限の側との違い：無限素点では両端が重なる | ［既知］（P¹(ℤ/N) はモジュラー記号の標準の道具、Manin 1972 など。Lean は Part 19〜28） |
-| 作用素：反転 ∘ 加法の変換 | J∘H_N/√N（Part 252、`PAG.Part256.JH`。J は単数の上の反転 u ↦ u⁻¹、H_N は離散 Hartley 変換）。ℤ/N の関数を単数の上の関数に送る写像で、同じ空間の上の作用素ではない。素朴なフーリエ核での形は §2 の注意 2 | モノグラフ層の境界ユニタリ U（イデール類群の上の反転と、境界条件）。Lean にしていない | ［再導出］（Part 252 の冒頭の記載どおり「既知の事実の書き直し」。Tate 1950 の局所関数等式の有限版と読む） |
-| 位相：原始指標の成分 | すべての指標 χ と単数 u で (J H_N χ)(u)/√N = 𝔀(χ)·χ(u)（`PAG.Part256.JH_eq_rootNum_mul_any`）。原始的なら \|𝔀(χ)\| = 1（`PAG.Part256.normSq_rootNum`）。原始的なら 𝔀(χ) がルート数であることは Lean の外（`rootNum` の docstring）。原始的でない指標では位相でない（法 2 の自明な指標で \|𝔀\|² = 1/2、法 4 の自明な指標で 0：`removal_counterexample_normSq`・`removal_counterexample_four`） | Tate の γ 因子（ガンマ因子の比）。公準 A1 は U の位相をこの値（λ = 0 での値）に選ぶ。両立の分類は定理 2.6 | ［既知］（Tate 1950、Burnol 1998〜2001）。A1 は公準のまま |
+| 舞台：射影直線と反転 | P¹(ℤ/N) := 単模ベクトル / 単数倍（Part 23（PAG27）、`PAG.Part27.ProjLine`）。反転 [a:b] ↦ [b:a]（`PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`。一般の N）。p 素数、K ≥ 1 で、点モデル（Part 22（PAG26）、`PAG.Part26.Pt`）と同型（`PAG.Part27.projEquiv`）、点の数 p^K + p^(K−1)（`PAG.Part27.card_ProjLine`）。反転どうしの対応 `PAG.Part27.toProj_Wpt` は K ≥ 1 の仮定なしで述べられている。2 チャートモデルと赤道での貼り合わせ条件 F_N(y) = F_S(y⁻¹)（Part 19（PAG23）、`PAG.Part23.Compat`、反転 `PAG.Part23.W`。点モデルの関数との同型は一般の N で `PAG.Part26.ptEquiv`、反転の対応は `PAG.Part26.toP1_comp_Wpt`）。2 チャートモデル（点モデル）が P¹(ℤ/N) と同型であることが Lean で示されているのは N = p^K（K ≥ 1）だけ。N が 2 つ以上の素因数を持つときは点の数が一致しない（数え上げ：\|Pt N\| = 2N − φ(N)、\|P¹(ℤ/N)\| = N∏_{p\|N}(1 + 1/p)。N = 6 で 10 点と 12 点。この不一致を述べる文は Lean にない）。N ≥ 2 では 0 = [0:1] と ∞ = [1:0] は別の点で、反転がこの 2 点を入れ替える（有限の側に点の同一視はない。この文も Lean にはない。N = 1 では 1 点） | P¹(ℝ)。ℝ_{>0} の対数座標 t = log x で、反転 x ↦ 1/x は t ↦ −t になり、両端 −∞・+∞（乗法の 0・∞）を入れ替える。射影直線では両端が一点（著者確認済みの読み）。有限の側との違い：無限素点では両端が重なる | ［既知］（P¹(ℤ/N) はモジュラー記号の標準の道具、Manin 1972 など。Lean は Part 19〜28） |
+| 変換：反転 ∘ 加法の変換 | J∘H_N/√N（Part 252（PAG256）、`PAG.Part256.JH`。J は単数の上の反転 u ↦ u⁻¹、H_N は離散 Hartley 変換）。ℤ/N の関数を単数の上の関数に送る写像で、同じ空間の上の作用素ではない。素朴なフーリエ核での形は §2 の注意 2 | モノグラフ層の境界ユニタリ U（イデール類群の上の反転と、境界条件）。Lean にしていない | ［再導出］（PAG256 の冒頭のコメントの記載どおり「既知の事実の書き直し」。Tate 1950 の局所関数等式の有限版と読む） |
+| 位相：原始指標の成分 | すべての指標 χ と単数 u で (J H_N χ)(u)/√N = 𝔀(χ)·χ(u)（`PAG.Part256.JH_eq_rootNum_mul_any`）。原始的なら \|𝔀(χ)\| = 1（`PAG.Part256.normSq_rootNum`）。原始的なら 𝔀(χ) がルート数であることは Lean の外（`rootNum` の docstring）。原始的でない指標では位相でないことがある：法 2 の自明な指標（原始的でないことは `PAG.Part256.removal_counterexample` の第 1 成分）で \|𝔀\|² = 1/2（`PAG.Part256.removal_counterexample_normSq`）、法 4 の自明な指標で 0（`PAG.Part256.removal_counterexample_four`）。原始的でない指標すべてで位相でないという全称の文は Lean の外（照合者の数値では N ≤ 30 のすべての非原始指標で \|𝔀\| ≤ 1/√2。数値は証明ではない） | Tate の γ 因子（ガンマ因子の比）。公準 A1 は U の位相をこの値（λ = 0 での値）に選ぶ。両立の分類は定理 2.6 | ［既知］（Tate 1950、Burnol 1998〜2001）。A1 は公準のまま |
 
 ## §4 Lean にしていないこと・確かめていないこと
 
-- P¹ と点モデルの同型は N = p^K（K ≥ 1）だけ。一般の N では、`ProjLine` の定義と反転（`Wproj`・`Wproj_Wproj`・`mk_eq_mk`）が示されているが、点モデル `Pt N` は P¹(ℤ/N) と一致しない。全素点の制限積 P¹(𝔸_ℚ) = ∏'_v P¹(ℚ_v) と、P¹(ℤ_p) = lim P¹(ℤ/p^K) は Lean にしていない。
-- 境界ユニタリ U と公準 A1 は、どの素点の側でも Lean の文に出てこない（Part 252 の冒頭）。Tate の局所関数等式そのもの、定理 2.6 も Lean にしていない（定理 2.6 の条件を A1 の位相が満たすことは PAG16・PAG173・PAG198 の 3 定理から出る、と CLAUDE.md §3 に記録あり。組み合わせた 1 つの文は未形式化）。
-- 「射影 = 舞台の P¹ と、反転 ∘ 加法の変換」は読みであり、Lean の文ではない。Part 252 の J∘H_N を「作用素の層の有限版」と呼ぶのも読みである。Part 252 の docstring の言葉では、`JH_eq_rootNum_mul` は「構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。U と A1 は文に出てこない）」、冒頭の読みは「公理 A1 の境界ユニタリの原始指標の部分」で、「貼り合わせ」という語は Lean の側にはない。
-- `JH` と 2 チャートモデル（`PAG.Part23.P1F`・`Compat`・`W`）・`ProjLine` を結ぶ Lean の文はない。§2 の 2 の作用素が「0 の側と ∞ の側をつなぐ」に対応する Lean の文はない。
-- ルート数の i^a の帰属（§2 の注意 2）は文献で未確認。
+- P¹ と点モデルの同型は N = p^K（K ≥ 1）だけ。一般の N では、`PAG.Part27.ProjLine` の定義と反転（`PAG.Part27.Wproj`・`PAG.Part27.Wproj_Wproj`）が示されている（`PAG.Part27.mk_eq_mk` は単数倍で同じ点になることを言う補題で、反転がうまく定義されることを示すのに使われる。反転の文ではない）。点モデル `PAG.Part26.Pt N` と P¹(ℤ/N) が N に 2 つ以上の素因数があるとき一致しないことは、数え上げによるもので Lean の文ではない。全素点の制限積 P¹(𝔸_ℚ) = ∏'_v P¹(ℚ_v) と、P¹(ℤ_p) = lim P¹(ℤ/p^K) は Lean にしていない。
+- 境界ユニタリ U と公準 A1 は、照合した範囲（Part 19・22・23・252、すなわち PAG23・PAG26・PAG27・PAG256）では Lean の形式文に出てこない（PAG256 の冒頭のコメントも「U と A1 は Lean の文に出てこない」と書く）。鎖全体については検索していない。Tate の局所関数等式そのもの、定理 2.6 も Lean にしていない（定理 2.6 の条件を A1 の位相が満たすことは PAG16・PAG173・PAG198 の 3 定理から出る、と CLAUDE.md §3 に記録あり。組み合わせた 1 つの文は未形式化）。
+- 「射影 = 舞台の P¹ と、反転 ∘ 加法の変換」は読み（2026-11-18 に著者が採用）であり、Lean の文ではない。Part 252 の J∘H_N を「変換の層の有限版」と呼ぶのも読みである。PAG256 の言葉では、`JH_eq_rootNum_mul` の docstring は「構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。U と A1 は文に出てこない）」、冒頭のコメント（`/-` で始まる通常のコメントで、docstring ではない）の読みは「公理 A1 の境界ユニタリの原始指標の部分」である。PAG256 の形式文には貼り合わせに当たる対象は出てこない。冒頭のコメントでは、重なりの読み「ねじれた貼り合わせ（U）」と、構築者が再構成した主張「U = J∘H_N/√N」を通して、間接に結びつけられている。PAG23・PAG26 の「貼り合わせ条件」は 2 チャートモデルの条件（`PAG.Part23.Compat`）である。
+- 照合した範囲では、`PAG.Part256.JH` と 2 チャートモデル（`PAG.Part23.P1F`・`PAG.Part23.Compat`・`PAG.Part23.W`）・`PAG.Part27.ProjLine` を結ぶ Lean の文はない。§2 の 2 の変換が「0 の側と ∞ の側をつなぐ」に対応する Lean の文もない。
+- ルート数の i^a の帰属と、有限素点の加法指標の符号の規約（§2 の注意 2）は文献で未確認。
 - 盲検の問いテストで、全素点を通して「各素点の 0 と ∞ の貼り合わせ」を一つの構成として書いた文献は見つからなかった（MathSciNet・zbMATH は未照合）。部品はすべて既知。
 
 ## §5 対照群（§7）
 
-- 関数体 𝔽_q(t) でも Tate の局所関数等式は同じ形で成り立つ。したがって §2 の 2・3 は ℚ に固有の算術を使わない形式の文である。
+- 関数体 𝔽_q(t) でも Tate の局所関数等式は同じ形で成り立つ（Lean の外の既知の事実）。§2 の 2 の変換の形と、§2 の 3 のうちガウス和 τ(χ)/√N の部分は、ℚ に固有の算術を使わない形式の文である。
+- ただし §2 の 3 で Hartley 核を採ると（PAG256 の冒頭の読み）、値 𝔀(χ) は偶奇による因子 ε(χ)（χ(−1) で決まる）を含む。注意 2 の帰属の読みが正しければ、この因子は無限素点の側（ℚ に固有の側）に属する。関数体での対応物は確かめていない。
 - 関数体では、t ↦ 1/t が素点 0 と素点 ∞ を入れ替える。ただしこの P¹_{𝔽_q} は「点が素点であるような大域の曲線」で、§2 の 1 の「各素点の座標の直線」とは別の対象である（照合者の指摘）。
-- ℚ に固有に残るのは、無限素点がアルキメデス的で、実数の順序（符号）と二つの端 ±∞ があることである（「−∞ と ∞」の重なり）。§2 の注意 2 の読みが正しければ、符号の因子 i^a もこの無限素点の側に属する。
+- ℚ に固有に残るのは、無限素点がアルキメデス的で、実数の順序（符号）と二つの端 ±∞ があることである（「−∞ と ∞」の重なり）。上の ε(χ) の因子も、読みが正しければここに属する。
 
-## §6 著者に判断を仰ぐこと
+## §6 著者の決定（2026-11-18 19:01）
 
-1. §2 の読み（舞台としての P¹、反転と加法の変換の合成による作用素、原始指標の位相としての局所因子）を、基礎文書の第 1・2 章の定義の材料として採るか。
-2. 採る場合、命名の「射影」が指すのは、舞台の P¹（射影直線）か、作用素か、その両方か。
-3. 有限素点の作用素に、素朴なフーリエ核（位相 τ(χ)/√N）と Part 252 の Hartley 核（位相はルート数、無限素点の符号を含む）のどちらを置くか。文献での確認（§2 の注意 2）を先に行うか。
-4. 決まったことは、補足 7 の規則に従い著者側の記録（CLAUDE.md §1・§2 と申し送り）に戻す。
+第 3 版の §6 で仰いだ 3 つの判断に、著者が次のとおり答えた（著者の言葉を要約せずに近い形で記す）。
 
-## §7 照合の記録
+1. **読みの採用：採る。** 舞台の P¹、反転と加法の変換の合成、原始指標の位相を、基礎文書の第 1・2 章の材料にする。留保は二つ：「ルート数であることは Lean の外」を明記すること、奇の指標での i 倍のずれを滑らかにしないこと。
+2. **命名：両方を指し、主は変換。** 舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ、という組の形にする。「射影により融合」という著者の言い方とも一致する。
+3. **核：Hartley 核を標準にする。** Part 252 の形式化の追認で、A1 の内容とも揃う。i^a の帰属と符号の規約の文献照合は、基礎文書が無限素点の読みを断定する前に行う（候補 1・候補 3・γ と同じ照合リストに入れる）。それまでは i^a は正規化因子として書き、読みは候補として留保する。
+
+決まったことは、補足 7 の規則に従い著者側の記録（CLAUDE.md §1・§2 と申し送り）に戻す。反映の文案は §9 に置き、著者の指示（19:03）で CLAUDE.md §1 と英語版に反映した。
+
+文献照合（`pag2_literature_ia_sign.md`）の後、2026-11-18 19:25 に著者が次の 2 つを決めた（照合ノート §9 の 1・2 を「進める」）。
+
+4. **i^a の留保を外す。** CLAUDE.md §1 の「i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する」を、規約を明示した書き方に置き換える：規約 T のもとで ε(χ) = (−i)^a は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N は有限素点の局所定数の積と一致する（値の一致、Lean の外）。i の冪が無限素点から来ることは規約によらないが、符号 χ(−1) の置き場は規約による。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
+5. **規約 T を基礎文書の標準にする。** Mathlib の `stdAddChar` と有限素点の符号が合い、Tate の学位論文の加法指標・Burnol とも同じ規約。
+
+## §7 照合の記録（第 1 回）
 
 - 第 1 版（`before_material_v1.md`）を、形式文の全文（PAG23・PAG26・PAG27・PAG256）を渡した新しい照合者が照らした（依頼文 `outputs/material_check_request.md`、出力 `outputs/material_check_output.md`、所要 約 6 分）。
-- 主な指摘と直し：原始性の限定の抜け（§2 の 3、表 3 行目）、素朴なフーリエ核とHartley 核の取り違え（§2 の注意 2 を新設）、`JH_eq_rootNum_mul` を「ルート数」の根拠にした当て方（外した）、番号と名前空間の取り違えの罠（完全修飾名にした）、K ≥ 1 の抜け、2 チャートモデルが P¹ になる範囲、一般の N の `ProjLine` の記述、docstring の引用の但し書き、`JH` と 2 チャートモデルを結ぶ文がないこと、「無限素点の U」の書き方、記号 W の衝突（ι と 𝔀 に分けた）、有限と無限の対応のずれ、表 2 行目のラベル（［再導出］にそろえた）。
-- 直した後の照合：§8 に記録する。
+- 主な指摘と直し：原始性の限定の抜け（§2 の 3、表 3 行目）、素朴なフーリエ核と Hartley 核の取り違え（§2 の注意 2 を新設）、`JH_eq_rootNum_mul` を「ルート数」の根拠にした当て方（外した）、番号と名前空間の取り違えの罠（完全修飾名にした。ただし第 2 版では一部だけで、第 3 版で残りを直した。§8）、K ≥ 1 の抜け、2 チャートモデルが P¹ になる範囲、一般の N の `ProjLine` の記述、docstring の引用の但し書き、`JH` と 2 チャートモデルを結ぶ文がないこと、「無限素点の U」の書き方、記号 W の衝突（ι と 𝔀 に分けた）、有限と無限の対応のずれ、表 2 行目のラベル（［再導出］にそろえた）。
+
+## §8 照合の記録（第 2 回：直した版の再照合）
+
+- 第 2 版（`before_material_v2.md`）を、第 1 回と同じ形式文の全文（PAG23・PAG26・PAG27・PAG256）と第 2 版の全文を渡した新しい照合者が照らした（入力 `input_material_v2.md`、依頼文 `outputs/material_recheck_request.md`、出力 `outputs/material_recheck_output.md`、所要 約 7 分）。照合者は手元で式の数値確認（N ≤ 30）を行った。数値は証明ではない。
+- 結論：第 2 版で新しく入った明確な誤りが 1 件（§4 の「「貼り合わせ」という語は Lean の側にはない」。PAG256 の冒頭のコメントと PAG23・PAG26 に語がある）。言い過ぎと曖昧さがいくつか。宣言名・完全修飾名・式はほかは一致。
+- 直したこと（照合者の指摘 1〜9 の順）：
+  1. §4 の「貼り合わせ」の文を、照合者の直し案のとおりに差し替えた。
+  2. 注意 2 を式で書いた（奇の χ で 𝔀 = −i·τ/√N、素朴な成分 = i·𝔀）。核の符号への依存（e(−xy) で χ(−1)τ/√N、関係の反転）を明記し、§6 の 3 にも規約を添えた。文献照合の項目に有限素点の加法指標の符号を加えた。
+  3. 表 3 行目を「位相でないことがある」に弱め、全称の文は Lean の外と断った。法 2 の非原始性の根拠に `removal_counterexample` を足した。
+  4. 注意 2 と記号の行で、`rootNum` の定義（すべての χ）とルート数との同定（Lean の外）を書き分け、根拠に `JH_eq_rootNum_mul_any`・`rootNum_eq` を引いた。
+  5. §2 の 3 の「この値」を、PAG256 の冒頭の読みの値 𝔀(χ)（Hartley 側）と特定し、素朴な核では奇の χ でずれることを書いた。
+  6. 記号の行と §3・§4 の宣言名を完全修飾名にし、PAG256 の W(χ) が 𝔀 を指すことを注記した。
+  7. §4 の U と A1 の文の範囲を「照合した範囲（PAG23・PAG26・PAG27・PAG256）」に狭めた。注意 1 と §4 の「結ぶ文はない」も同じ範囲に狭めた。
+  8. 注意 2 の素朴な核の項に、`inv_apply_units_inv` が要ることと、単数の上では原始性が要らないことを書いた。
+  9. 軽微な点：「のときだけ」を「Lean で示されているのは N = p^K だけ」と「2 つ以上の素因数で点の数が一致しない」に分け、「0 と ∞ は別の点」に N ≥ 2 を付けた。`toProj_Wpt` は K ≥ 1 なしと書いた。`mk_eq_mk` を反転の補題から外した。「有限素点の作用素」を「有限レベル N の変換」に、§2 の 2 の「作用素」を「変換（写像）」にそろえた。PAG256 の冒頭は通常のコメントと書いた。§5 の第 1 項と第 3 項の張り合いを、ε(χ) の因子を分けて書くことで解いた。
+- この第 3 版は、第 2 回の照合の後の直しを照合にかけていない。直しはすべて、照合者が示した直し案に沿った言い換えと主張の範囲を狭める直しで、新しい主張は加えていない（構築側の判断。補足 8 の停止の規約の「主張を変えない直し」に当たると読む）。§5 の第 2 項（ε(χ) の因子の帰属）は張り合いの解消のために書き足した文で、注意 2 の未確認の読みに条件づけてある。この判断が妥当かどうかは、次の統合照合で確かめる対象とする。
+
+## §9 著者の決定の記録（第 4 版）
+
+- 第 3 版（`before_material_v3.md`）に、著者の決定（2026-11-18 19:01、§6）を記録した。直したところ：冒頭の地位の文（「著者の確認待ち」→「留保つきで採用」）、§2 の見出しと命名の決定（両方を指し、主は変換）、§2 の 3（標準の核を Hartley 核とし、i^a を正規化因子として書く。ルート数であることは Lean の外。奇の χ での i 倍のずれは消えない）、注意 2 の帰属の読み（候補として留保、文献照合は基礎文書が無限素点の読みを断定する前）、§4 の第 3 項（読みが採用されたこと）、§6（判断の依頼を決定の記録に置き換えた）。
+- これらは著者の決定の記録で、Lean についての主張は変えていない。照合にはかけていない（補足 8 の「主張を変えない直し」に当たると読む。次の統合照合の対象に含める）。
+- 著者側の記録に戻すための文案を次に置いた。CLAUDE.md §1 への追記は、2026-11-18 19:03 の著者の指示で、CLAUDE.md と英語版 CLAUDE.en.md の §1（命題 3 の置き方の次の箇条）に反映した。反映の際に文案へ足したもの：命名の意味（2026-11-16）、Part と PAG の番号の併記（§7 の (iv)）、PAG256 の docstring の記号 W(χ) が反転の W とは別であることの注記、「明記すること」の一句。照合リストは著者側のもので、構築側では変えていない。
+
+**CLAUDE.md §1 への追記の文案**（解釈の層の箇条として）：
+
+> 「射影」の読み（2026-11-18、著者が採用。解釈の層であり、形式化済みの定理ではない）：命名の「射影」は舞台と変換の組を指し、主は変換である。舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28）、その上で働く反転（乗法の側）と加法の変換（加法の側）の合成を射影と呼ぶ。原始指標についての位相がその成分である。標準の核は Part 252 の Hartley 核とする（形式化の追認。A1 の内容と揃う）。値は 𝔀(χ) = τ(χ)/(i^a√N)（`PAG.Part256.rootNum`）で、原始指標ではルート数だが、その同定は Lean の外である。素朴なフーリエ核 e(xy) とは奇の指標で i 倍ずれ、このずれを滑らかにしない。i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する。A1 は公準のまま。材料は `notes/pag2_projection_material.md`。
+
+**照合リストへの項目の文案**（候補 1・候補 3・γ と同じリスト）：
+
+> i^a の帰属と符号の規約：(a) ルート数の i^a は、Tate の局所分解で無限素点の局所因子から来るか。(b) 大域の加法指標の符号の規約（無限素点と有限素点で符号を逆に取るか）のもとで、有限素点の局所因子は τ(χ)/√N と χ(−1)τ(χ)/√N のどちらになるか。期限：基礎文書が無限素点の読みを断定する前。それまで i^a は正規化因子として書く。出所：`notes/pag2_projection_material.md` §2 の注意 2。
+
+## §10 文献照合の後の著者の決定の記録（第 5 版）
+
+- 第 4 版（`before_material_v4.md`）に、文献照合の結果と 2026-11-18 19:25 の著者の決定（§6 の 4・5）を記録した。直したところ：冒頭の版の文、§2 の 3（i^a を正規化因子として書く扱いを、規約 T での無限素点の局所定数との一致に置き換えた）、注意 2 の帰属の読み（照合の結果と決定を追記）、§6（4・5 を追加）。
+- 決定は CLAUDE.md §1 と英語版にも反映した。
+- これらは著者の決定と照合の結果の記録で、Lean についての主張は変えていない。照合にはかけていない（次の統合照合の対象に含める）。根拠にした文献照合ノートの第 2 版も、照合後の直しが未照合である。
```

### A2 文献照合ノート（照合済みの第 1 版 → 現行の第 3 版）
```diff
--- records/literature_ia/before_check_v1.md	2026-11-18 19:23:51.466519175 +0900
+++ notes/pag2_literature_ia_sign.md	2026-11-18 19:26:07.067526165 +0900
@@ -1,8 +1,8 @@
 # アーデル射影幾何 — 照合リストの項目「i^a の帰属と加法指標の符号の規約」の文献照合
 
-（2026-11-18。短期層の小さいノート。新しいパートではない。出所：CLAUDE.md §1 の「射影」の読み（2026-11-18、著者が留保つきで採用）と、材料ノート `pag2_projection_material.md` §2 の注意 2。著者の決定で、基礎文書が無限素点の読みを断定する前に行う照合として、候補 1・候補 3・γ と同じ照合リストに入った項目である。著者の定義（§1）の文面と A1 の地位は変えない。）
+（2026-11-18。短期層の小さいノート。新しいパートではない。出所：CLAUDE.md §1 の「射影」の読み（2026-11-18、著者が留保つきで採用）と、材料ノート `pag2_projection_material.md` §2 の注意 2。著者の決定で、基礎文書が無限素点の読みを断定する前に行う照合として、候補 1・候補 3・γ と同じ照合リストに入った項目である。著者の定義（§1）の文面と A1 の地位は変えない。第 1 版を独立照合にかけ、その指摘で直した第 2 版に、著者の決定を記録したのがこの第 3 版である（§8・§9）。）
 
-記号：ξ は法 N の原始 Dirichlet 指標、a は ξ が奇なら 1・偶なら 0、τ(ξ) = Σ_x ξ(x) e^{2πix/N}、W(ξ) = τ(ξ)/(i^a √N)（古典的なルート数。Lean では `PAG.Part256.rootNum` の値 𝔀(ξ)。ルート数であることは Lean の外）。
+記号：ξ は法 N の原始 Dirichlet 指標、a は ξ が奇なら 1・偶なら 0、τ(ξ) = Σ_x ξ(x) e^{2πix/N}、W(ξ) = τ(ξ)/(i^a √N)（古典的なルート数。Lean では `PAG.Part256.rootNum` の値 𝔀(ξ)。ルート数であることは Lean の外）。局所定数 ε(s, χ_v, ψ_v) は、Tate 1979（Corvallis）の流儀で定める：f̂(y) = ∫ f(x) ψ(xy) dx、局所関数等式の定数、ψ_v に関して自己双対な測度。
 
 ## §1 問いと結論
 
@@ -11,68 +11,88 @@
 - (a) ルート数の i^a は、Tate の局所分解で無限素点の局所因子から来るか。
 - (b) 有限素点の加法指標の符号の規約のもとで、有限素点の局所因子の積は τ(ξ)/√N と ξ(−1)τ(ξ)/√N のどちらになるか。
 
-結論（独立照合の結果は §8）：
+結論：
 
-- (a) **来る。** 無限素点の局所定数は i の冪で、有限素点の局所定数はガウス和である（i の冪を含まない）。ただし冪の向きは規約で変わる：Tate の学位論文の規約（下の規約 T）では ε(1/2, χ_∞, ψ_∞) = (−i)^a = i^{−a}、逆の規約 C では i^a。［既知］（確信度：高）
-- (b) **規約で決まる。** 規約 T では τ(ξ)/√N、規約 C では ξ(−1)τ(ξ)/√N。どちらの規約でも大域の積は W(ξ) で変わらない。偶奇の符号 ξ(−1) = (−1)^a を無限素点と有限素点のどちらに置くかは規約の選び方である。［既知］（確信度：高）
-- PAG への帰結：PAG256 の Hartley 核の因子 ε(ξ) = `parFac`（偶で 1、奇で −i）は、規約 T の無限素点の局所定数 (−i)^a と同じ値である。残りの τ(ξ)/√N は、規約 T の有限素点の局所定数の積と同じ値である。したがって材料ノートの読み「Part 252 の Hartley の形は、無限素点の符号の因子を有限レベルの変換に取り込んだ形」は、規約 T を明示すれば文献と合う。素朴なフーリエ核 e(xy) の値 τ(ξ)/√N は規約 T の有限素点の積、e(−xy) の値 ξ(−1)τ(ξ)/√N は規約 C の有限素点の積に当たる。奇の指標での i 倍のずれは、無限素点の局所定数そのものである。この対応は値の一致であり、PAG256 の Hartley 変換を Tate の局所関数等式として形式化したものではない（Lean の外）。
+- (a) **i の冪は無限素点から来る。符号 (−1)^a の置き場は規約による。** 無限素点の局所定数は i の冪で、有限素点の局所定数はガウス和である（i の冪を含まない）。ここまではどちらの規約でも同じ。ただし冪の向きは規約で変わる：Tate の学位論文の加法指標の規約（下の規約 T）では ε(1/2, χ_∞, ψ_∞) = (−i)^a = i^{−a}、逆の規約 C では i^a。［既知］（確信度：高）
+- (b) **規約で決まる。** s = 1/2 で、規約 T では τ(ξ)/√N、規約 C では ξ(−1)τ(ξ)/√N。どちらの規約でも、s = 1/2 での大域の積は W(ξ) で変わらない（一般の s では N^{1/2−s} W(ξ)）。偶奇の符号 ξ(−1) = (−1)^a を無限素点と有限素点のどちらに置くかは、規約の選び方である。［既知］（確信度：高）
+- **PAG への帰結**（値の一致。Lean の外）：
+  - PAG256 の Hartley 核の因子 ε(ξ) = `parFac`（偶で 1、奇で −i）は、規約 T の無限素点の局所定数 (−i)^a と同じ値である。残りの τ(ξ)/√N は、規約 T の有限素点の局所定数の積と同じ値である。
+  - したがって材料ノートの読み「Part 252 の Hartley の形は、無限素点の符号の因子を有限レベルの変換に取り込んだ形」は、**規約 T を明示すれば**文献と合う。
+  - ただし、この分け方が文献の「無限素点 × 有限素点」と一致するのは規約 T を選んだからである。規約 C では無限素点の局所定数は i^a で、Hartley の ε(ξ) とは (−1)^a だけ違う。等式 √N·W = ε(ξ)·τ(ξ) だけからは「ε(ξ) は無限素点から来る」とは言えない（照合者の注記）。
+  - 素朴なフーリエ核 e(xy) の値 τ(ξ)/√N は規約 T の有限素点の積に、e(−xy) の値 ξ(−1)τ(ξ)/√N は規約 C の有限素点の積に当たる。奇の指標での i 倍のずれは、規約 T では無限素点の局所定数そのものである。
+  - これは値の一致であり、PAG256 の Hartley 変換を Tate の局所関数等式として形式化したものではない。
 
 ## §2 二つの規約と出典
 
-- **規約 T**（Tate の学位論文の規約）：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}（{x}_p は p 進の小数部分）。積は ℚ の上で自明。
+- **規約 T**：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}（{x}_p は p 進の小数部分）。積は ℚ の上で自明。
+  - Tate の学位論文（1950）：実数体で λ(x) = −x（本文に「負の符号に注意」の注記）、p 進体で λ(x) は λ(x) − x が p 進整数となる有理数。指標は e^{2πiΛ}（§2.2、§4.1 Lemma 4.1.5）。**照合者が走査版（Rutgers）で確認した。構築側は原文を開いていない。** 照合者の注記：同論文の Fourier 変換は e^{−2πiΛ(ξη)} を核とし（実数体では e^{+2πixy}）、局所の定数は逆向きの比 ρ(c) として定義されている。上の ε の定め方は学位論文そのものではなく、Corvallis 論文の流儀である。走査版の式は OCR が崩れており、この注記の確信度は中。
   - Roy–Schmidt–Yi, "Classical and adelic Eisenstein series", arXiv:2109.07649 §4.3：ψ を Tate の学位論文で定義されたものとし、ψ_∞(x) = e^{−2πix} と書く。
-  - arXiv:1502.02633：Tate の学位論文に従う正規化として、ψ_ℝ(x) = e^{−2πix}、ψ_{ℚ_p}(x) = e^{2πiλ(x)} と書く。
-  - Burnol, arXiv:math/9811040：実素点で exp(−2πit)、有限素点で exp(2πi{Tr t}) を使う（モノグラフ層が引く Burnol と同じ著者）。
-- **規約 C**（逆の規約）：ψ_∞(x) = e^{+2πix}、ψ_p(x) = e^{−2πi{x}_p}。例：arXiv:2604.25288 §5.1、arXiv:1511.04265 式 (3.72)〜(3.75)。
-- 指標の対応は ψ によらない：ξ に対応するイデール類指標 χ は、不分岐の ℓ で χ_ℓ(ℓ) = ξ(ℓ)。分岐する p では χ_p の ℤ_p^× への制限が (ξ^{(p)})^{−1}（Roy–Schmidt–Yi 式 (150)。ξ = ∏ ξ^{(p)} は中国剰余定理による分解）。χ_∞ は偶で自明、奇で符号（同 式 (151)）。
-
-Tate の学位論文の原文は開いていない。規約 T が学位論文の規約であることは、上の 3 文献の記載による（確信度：高。3 文献が一致し、Burnol の規約とも合う）。
+  - Burnol, arXiv:math/9811040（"Spectral Analysis of the Local Conductor Operator"）：実素点で exp(−2πit)、有限素点で exp(2πi{Tr t})。モノグラフ層が引く Burnol と同じ著者。読んだ範囲には、Tate の規約への言及も符号の選び方の説明もない。
+  - arXiv:1502.02633 も同じ指標を「標準の加法指標」として書く。ただし、Tate の学位論文に従うと明記しているのは Haar 測度の正規化だけである（第 1 版の「Tate の学位論文の規約として書く」は言い過ぎだったので直した）。
+- **規約 C**（逆の規約）：ψ_∞(x) = e^{+2πix}、ψ_p(x) = e^{−2πi{x}_p}。例：arXiv:2604.25288 §5.1、arXiv:1511.04265 式 (3.72)〜(3.75)（照合者が確認）。
+- 指標の対応は ψ によらない：ξ に対応するイデール類指標 χ は、不分岐の ℓ で χ_ℓ(ℓ) = ξ(ℓ)。分岐する p では、χ_p の ℤ_p^× への制限が (ξ^{(p)})^{−1}（Roy–Schmidt–Yi 式 (150)。ξ = ∏ ξ^{(p)} は中国剰余定理による分解）。χ_∞ は偶で自明、奇で符号（同 式 (151)）。
 
 ## §3 無限素点の局所定数
 
-- 規約 T：f(x) = x e^{−πx²} の ψ_∞ に関するフーリエ変換は f̂(y) = ∫ f(x) e^{−2πixy} dx = −i·y e^{−πy²}。よって ε(s, sgn, ψ_∞) = −i（s によらない）。偶では f = e^{−πx²} が自己双対で ε = 1。Roy–Schmidt–Yi 式 (155) と同じ値。
-- 規約 C：同じ計算で +i。
-- 数値（`local_eps_check.log`）：f̂(y)/f(y) は規約 T で −i、規約 C で +i（y = 0.3, 0.7, 1.0, 1.9、誤差 10⁻⁶ 未満）。偶では 1。
+- 規約 T：f(x) = x e^{−πx²} の ψ_∞ に関するフーリエ変換は f̂(y) = ∫ f(x) e^{−2πixy} dx = −i·y e^{−πy²}。Z(s, sgn, f) が局所 L 因子に等しいので、ε(s, sgn, ψ_∞) = −i（s によらない）。偶では f = e^{−πx²} が自己双対で ε = 1。Roy–Schmidt–Yi 式 (155) と同じ値。
+- 規約 C：ε(s, χ, ψ_a) = χ(a)|a|^{s−1/2} ε(s, χ, ψ) で a = −1 とすると +i（照合者の導出）。この値を直接書いた文献の箇所は確かめていない。
+- 数値：構築側（`local_eps_check.log`）は f̂(y)/f(y) を 4 点で計算し、規約 T で −i、規約 C で +i。照合者は局所関数等式を数値積分で直接評価し（s = 0.3, 0.5, 0.8）、同じ値を得た。
 
 ## §4 有限素点の局所定数の積
 
-- p ∣ N、k = v_p(N) のとき、ε(0, χ_p, ψ_p) = ∫_{p^{−k}ℤ_p^×} χ_p^{−1}(x) ψ_p(x) dx（Roy–Schmidt–Yi 式 (157)。測度は ℤ_p が 1）。x = p^{−k}y と置くと、規約 T で ε(0, χ_p, ψ_p) = χ_p(p)^k Σ_{y mod p^k, p∤y} ξ^{(p)}(y) e^{2πiy/p^k}。
-- 交差項：χ が ℚ^× の上で自明で、χ_∞(p) = 1、不分岐の ℓ で χ_ℓ(p) = 1 だから、χ_p(p) = ∏_{ℓ∣N, ℓ≠p} ξ^{(ℓ)}(p)。これが古典的な τ(ξ₁ξ₂) = ξ₁(N₂)ξ₂(N₁)τ(ξ₁)τ(ξ₂) の交差項に当たる。
+- p ∣ N、k = v_p(N) のとき、ε(0, χ_p, ψ_p) = ∫_{p^{−k}ℤ_p^×} χ_p^{−1}(x) ψ_p(x) dx（Roy–Schmidt–Yi 式 (157)。測度は ℤ_p が 1）。一般の s では ε(s) = p^{−ks}·ε(0)（照合者が局所関数等式から導出）。x = p^{−k}y と置くと、規約 T で ε(0, χ_p, ψ_p) = χ_p(p)^k Σ_{y mod p^k, p∤y} ξ^{(p)}(y) e^{2πiy/p^k}。
+- 交差項：χ が ℚ^× の上で自明で、χ_∞(p) = 1、不分岐の ℓ で χ_ℓ(p) = 1 だから、χ_p(p) = ∏_{ℓ∣N, ℓ≠p} ξ^{(ℓ)}(p)。これは構築側の導出で、Roy–Schmidt–Yi には書かれていない（照合者が同じ式を独立に導出した）。中国剰余定理によるガウス和の分解 τ(ξ) = ∏_p ξ^{(p)}(N/p^{k_p}) τ(ξ^{(p)}) の交差項に当たる。
 - 規約 T：∏_{p∣N} ε(0, χ_p, ψ_p) = τ(ξ)（Roy–Schmidt–Yi 式 (156)。同論文では演習として示されている）。s = 1/2 では τ(ξ)/√N（絶対値 1）。
-- 規約 C：ψ_p の符号が変わるので、積は Σ ξ(y) e^{−2πiy/N} = ξ(−1)τ(ξ)。
+- 規約 C：ψ_p の符号が変わるので、各因子に ξ^{(p)}(−1) が掛かり、積は ξ(−1)τ(ξ)。自己双対測度は変わらない（ψ_p の導手は ℤ_p のまま）。
 
 ## §5 数値確認（数値は証明ではない）
 
-`local_eps_check.py`・`local_eps_check.log`（規約 T と C、交差項 χ_p(p) を含む §4 の式そのもの）：
+- 構築側（`local_eps_check.py`・`local_eps_check.log`。§4 の明示式そのもの）：
+  - 31 個の法（1, 3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 20, 21, 24, 25, 27, 28, 32, 35, 40, 44, 45, 48, 56, 60, 63, 72, 84, 105, 120）の原始指標すべて、209 個（偶 104・奇 105）。原始指標の個数は各 N で既知の数と一致した。退化した場合（N = 1、p = 2 の法 4・8・16・32、複数の素因数）を含む。
+  - 有限素点の積：規約 T で τ(ξ)（最大誤差 2.8×10⁻¹⁴）、規約 C で ξ(−1)τ(ξ)（2.9×10⁻¹⁴）。
+  - s = 1/2 での大域：どちらの規約でも W(ξ)（5×10⁻¹⁵）。
+  - 規約を混ぜると（規約 T の ψ_p と規約 C の ε_∞）、奇の指標 105 個すべてで合わない。
+- 照合者（`outputs/check_eps.py`・`check_supp.py` とその出力）：
+  - 法 1〜100 と 120, 128, 135, 180, 243, 256, 360, 400 の原始指標 2,162 個。
+  - p 進の局所定数を局所関数等式から有限和で直接評価し、§4 の閉じた式と比べた（6,288 回、最大差 3.1×10⁻¹³）。
+  - W(ξ) は θ 変換の関係で別に確かめた（3.1×10⁻¹³）。一般の s での積 N^{1/2−s} W(ξ) も確かめた。
+  - 混ぜた規約では、奇の指標 1,082 個すべてで −W(ξ) になった。混ぜた ψ は ℚ の上で自明でない（x = 1/3 で e^{4πi/3}）ので、大域の選び方として許されない。
+  - Hartley 和の式 Σ_x ξ(x) cas(2πxy/N) = ε(ξ)τ(ξ)ξ̄(y) はすべての y で成り立った（ξ 原始。原始でない指標では法 4 の y = 0, 2 などで崩れる）。引数の符号を逆にした cas(−2πxy/N) では ξ(−1)√N·W(ξ) になる。
+- 構築側の数値が確かめたのは §4 の明示式の算術である。照合者の数値は、局所関数等式から直接評価した値との比較を含む。どちらも、その値が Tate の局所定数であるという文献の定理そのものを示すものではない。
+
+## §6 PAG の記号との対応（値の一致。Lean の外）
+
+| PAG256 の量 | 値 | 文献の量（規約 T、s = 1/2） | 規約 C では |
+|---|---|---|---|
+| `PAG.Part256.parFac` ξ | 偶 1、奇 −i | ε(1/2, χ_∞, ψ_∞) = (−i)^a | 無限素点は i^a = (−1)^a·ε(ξ) |
+| 素朴な核 e(xy) での成分 | τ(ξ)/√N | ∏_{p∣N} ε(1/2, χ_p, ψ_p) | 有限素点の積は ξ(−1)τ(ξ)/√N（e(−xy) の値） |
+| Hartley 核での成分 𝔀(ξ)（`rootNum`、`JH_eq_rootNum_mul_any`） | ε(ξ)τ(ξ)/√N = τ(ξ)/(i^a√N) | ε(1/2, χ) = ∏_v ε(1/2, χ_v, ψ_v) = W(ξ) | 同じ（大域は規約によらない） |
 
-- 法 N ∈ {1, 3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 20, 21, 24, 25, 27, 28, 32, 35, 40, 44, 45, 48, 56, 60, 63, 72, 84, 105, 120} の原始指標すべて、209 個（偶 104・奇 105）。原始指標の個数は各 N で既知の数と一致（例：N = 27 で 12、N = 63 で 20、N = 120 で 6）。退化した場合（N = 1、p = 2 の法 4・8・16・32、複数の素因数）を含む。
-- 規約 T の有限素点の積 = τ(ξ)：最大誤差 2.8×10⁻¹⁴。規約 C の積 = ξ(−1)τ(ξ)：最大誤差 2.9×10⁻¹⁴。
-- 大域：(−i)^a × （規約 T の積）/√N = W(ξ)、i^a × （規約 C の積）/√N = W(ξ)：最大誤差 5×10⁻¹⁵。
-- 規約を混ぜる（規約 T の ψ_p と規約 C の ε_∞）と、奇の指標 105 個すべてで合わない。
-- 確かめたのは §4 の明示式の算術であり、その式が Tate の局所定数であること（文献の定理）ではない。
-
-## §6 PAG の記号との対応（値の一致）
-
-| PAG256 の量 | 値 | 文献の量（規約 T） |
-|---|---|---|
-| `PAG.Part256.parFac` ξ | 偶 1、奇 −i | ε(1/2, χ_∞, ψ_∞) = (−i)^a |
-| 素朴な核 e(xy) での成分 | τ(ξ)/√N | ∏_{p∣N} ε(1/2, χ_p, ψ_p) |
-| Hartley 核での成分 𝔀(ξ)（`rootNum`、`JH_eq_rootNum_mul_any`） | ε(ξ)τ(ξ)/√N = τ(ξ)/(i^a√N) | ε(1/2, χ) = ∏_v ε(1/2, χ_v, ψ_v) = W(ξ) |
-
-- 規約 C では、素朴な核 e(−xy) の値 ξ(−1)τ(ξ)/√N が有限素点の積に、i^a が無限素点に当たる。
-- Mathlib の `stdAddChar`（ZMod N の上で e(x/N) = e^{2πix/N}）は、規約 T の ψ_p(y/p^k) = e^{+2πiy/p^k} と同じ符号である。Lean の鎖は有限素点の側で規約 T と符号が合っている。
-- 以上は値の一致である。PAG256 の Hartley 変換が Tate の局所関数等式を（無限素点の因子を含めて）表すことは Lean の外で、Lean の文にはない。
+- Mathlib の `stdAddChar`（ZMod N の上で e(x/N) = e^{2πix/N}）は、規約 T の ψ_p(y/p^k) = e^{+2πiy/p^k} と同じ符号である。Lean の鎖の有限素点の側は、規約 T と符号が合っている。
+- PAG256 の Hartley 変換が Tate の局所関数等式を（無限素点の因子を含めて）表すことは Lean の外で、Lean の文にはない。
 
 ## §7 ラベルと対照群
 
-- ラベル：§1 の (a)(b) とも［既知］（Tate 1950、Roy–Schmidt–Yi 2021 などの標準的な計算）。PAG の値との一致（§6）は［再導出（小さい）］：PAG256 の `parFac`・`rootNum` の定義と、文献の局所定数の値を並べたもの。新規候補はない。
-- 対照群（§7）：関数体 𝔽_q(t) では無限素点も非アルキメデス的で、局所定数はガウス和型になる見込み（i の冪としての無限素点の因子は、ℚ の実素点に固有と読める）。確かめていない（確信度：低〜中）。
+- ラベル：§1 の (a)(b) とも［既知］（Tate 1950、Tate 1979、Roy–Schmidt–Yi 2021 などの標準的な計算）。PAG の値との一致（§6）は［再導出（小さい）］：PAG256 の `parFac`・`rootNum` の定義と文献の局所定数の値を並べたもの。新規候補はない。
+- 対照群（§7）：関数体 𝔽_q(t) では無限素点も非アルキメデス的で、局所定数はガウス和型になる見込み。そうなら、i の冪としての無限素点の因子は ℚ の実素点に固有と読める。確かめていない（確信度：低〜中）。
 
 ## §8 照合の記録
 
-（独立照合の結果を待っている。届いたら記録する。）
+- 第 1 版（`before_check_v1.md`）の主張を C1〜C6 に分けて、文脈を渡さない照合者に渡した（依頼文 `outputs/check_request.md`、出力 `outputs/check_output.md`、照合者の計算 `outputs/check_eps.py`・`check_eps_output.txt`・`check_supp.py`・`check_supp_output.txt`、所要 約 8.5 分）。依頼は判定ではなく、計算・導出・文献の箇所・反例または直した文を出すこと。
+- 結論：C1〜C6 はすべて成り立つ（確信度：高。C1 の注記の部分は中）。直しが要る点が 2 つ、注記が 1 つ。
+- 直したこと：
+  1. C5：「s = 1/2 で」を補い、一般の s では N^{1/2−s} W(ξ) と書いた（§1 (b)、§5）。
+  2. C1：arXiv:1502.02633 が Tate の学位論文に従うと明記しているのは Haar 測度の正規化だけ、と直した。Tate の学位論文の確認は照合者が走査版で行ったこと、構築側は原文を開いていないことを明記した。同論文の Fourier 変換の核と局所定数の向きの注記を入れ、ε の定め方は Corvallis 論文の流儀であると冒頭に書いた（§2、記号）。
+  3. C6 の注記：Hartley の ε(ξ) と無限素点の局所定数の一致は規約 T を選んだときの分け方で、等式だけからは「ε(ξ) は無限素点から来る」とは言えない、と §1 と §6 に書いた。§1 (a) の結論を「i の冪は無限素点から来る。符号 (−1)^a の置き場は規約による」に直した。
+  4. 照合者の数値と導出（局所関数等式からの直接評価、規約 C の +i の導出、ε(s) = p^{−ks}ε(0)、χ_p(p) の独立の導出）を §3〜§5 に書き足した。
+- この第 2 版は、照合の後の直しを照合にかけていない。直しは照合者の直し案・注記に沿った言い換えと、主張の範囲を狭める直しで、新しい主張は加えていない（構築側の判断。次の統合照合の対象に含める）。
+- 確かめられなかったこと（照合者の報告から）：規約 C の ε_∞ = +i と §4 の規約 C の式は、文献の箇所では直接確かめていない（導出と数値だけ）。Burnol の PDF は取得できず ar5iv 版の一部、1502.02633 と 1511.04265 も一部だけを読んだ。Tate の学位論文の走査版の式の部分は OCR が崩れていた。
+
+## §9 著者の決定（2026-11-18 19:25）
+
+第 2 版の §9 で仰いだ 2 つの判断に、著者は「1 と 2 を進めてください」と答えた。
 
-## §9 著者に判断を仰ぐこと
+1. **留保を外す。** CLAUDE.md §1（と英語版）の「i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する」を、規約を明示した書き方に置き換えた。規約 T のもとで、ε(ξ) = (−i)^a は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(ξ)/√N は有限素点の局所定数の積と一致する（値の一致、Lean の外）。i の冪が無限素点から来ることは規約によらないが、符号 ξ(−1) の置き場は規約による。規約 T を明示せずに「ε(ξ) は無限素点から来る」と書かない。
+2. **規約 T を基礎文書の標準にする。** Mathlib の `stdAddChar` と有限素点の符号が合い、Tate の学位論文の加法指標・Burnol とも同じ規約。
 
-1. CLAUDE.md §1 の留保「i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する」を外すか。外す場合の書き方の案：「規約 T（Tate の学位論文：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）のもとで、ε(ξ) = (−i)^a は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と一致し、τ(ξ)/√N は有限素点の局所定数の積と一致する（値の一致。Lean の外）。規約 C では符号 ξ(−1) が無限素点と有限素点のあいだで移る」。
-2. 基礎文書で規約 T を採るか（Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol とも同じ規約）。
+記録：決定は CLAUDE.md §1 と英語版、材料ノート（第 5 版）の §6 の 4・5、概要の文書、引き継ぎメモに反映した。このノートの第 2 版の照合後の直しは未照合のままで、次の統合照合の対象に含める（決定の根拠にした版が照合後の直しを含むことを、ここに明記する）。第 2 版の §9 の文案は `before_decision_v2.md` に残る。
```

### A3 CLAUDE.md・CLAUDE.en.md・概要の文書・引き継ぎメモ（コミット a848b27 → 現在）
```diff
diff --git a/CLAUDE.en.md b/CLAUDE.en.md
index d4e1978..2acd915 100644
--- a/CLAUDE.en.md
+++ b/CLAUDE.en.md
@@ -25,6 +25,7 @@ The purpose of this procedure is not to avoid mapping to existing mathematics. T
   - A line is an effective appearance that emerges when the resolution is lowered.
   - However, the parameter that determines the resolution is **undecided**. Do not arbitrarily identify it with any of $N$, $K$ or $\Lambda$.
   - Placement of Proposition 3 (2026-11-13; recorded as a decision of the author-side Muse, to whom the choice was delegated by the author; the author can overturn it at any time): the wording of the definitions above is not changed. The mathematical place of the operation of resolution is put in the interpretive layer, not as "a transition within the object (a change from discrete to continuous)" but as **a choice of a way of cutting (a view)** of the global object. That is, the object is the whole in which the places coexist in parallel from the start as the factors of a restricted product; the finite-level quotients and the $\Lambda$-cutoff (the two axes separated in A8) are views of that whole; and the question of emergence is read as "how does a line look when the view is made coarser". The prohibition on identifying the resolution with $N$ or $\Lambda$ is maintained as before (what was decided is where the question is placed, not the parameter). Later, on 2026-11-14, the original text of the author's 08:41 definition reached the author side through the construction side's handoff memo (`PAG2_handoff_part257.md`): "Escaping into the completion (limit) and sliding into the continuum is what I call the resolution dropping. I do not wish for the continuum to be observed; I maintain the observation of the discrete structure even in the limit." This definition does not contradict the placement above — the operation on the side where the resolution drops is sliding into the completion, the stance is maintaining the observation of the discrete structure even in the limit, and the limit is taken on the side of the direct limit (the side where all places are measured at once). When using completions ($L^2$, $\mathbb{R}$, the product topology), state as a reading that they are "read as operations on the side where the resolution drops". Do not write the continuum appearing in closures or completions as the "effective appearance" or as a goal. Also, on 2026-11-13 at 08:38 the author adopted, on the construction side, L1 (resolution = the set of places measured) as the reading of Proposition 3 (L1 is a proposal adopted as a reading, not the wording of the definition itself; it is not identified with any of $N$, $K$ or $\Lambda$). By the author's instruction (2026-11-12), the expression 「直線の創発」 ("emergence of the line") is not used (when touching on Proposition 3, refer to it as "Proposition 3 of §1 (resolution and effective appearance)" and write in mathematical language what changes and how).
+  - Reading of "projection" (2026-11-18, adopted with reservations by the author; interpretive layer, not a formalized theorem): the meaning of the name is "fusing adelic geometry and idelic geometry by projection" (2026-11-16, the author). The "projection" in the name refers to the pair of a stage and a transform, with the transform as the main sense. The stage is the projective line P¹ (inversion swaps 0 and ∞; at the finite level, Parts 19–28 (PAG23–PAG32)), and the composition, acting on it, of inversion (the multiplicative side) and an additive transform (the additive side) is called the projection (at the finite level, $J\circ H_N/\sqrt N$ of Part 252 (PAG256)). Its components on primitive characters are the phases. The standard kernel is the Hartley kernel of Part 252 (ratifying the formalization; consistent with the content of A1). The value is $\tau(\chi)/(i^a\sqrt N)$ (`PAG.Part256.rootNum`; the symbol W(χ) in the PAG256 docstrings denotes this value and is distinct from the inversion $W$); for primitive characters it is the root number, but that identification is outside Lean (state this explicitly). It differs from the value $\tau(\chi)/\sqrt N$ of the plain Fourier kernel $e(xy)$ by a factor $i$ for odd characters; do not smooth over this discrepancy. The convention for the additive character is convention T (the additive character of Tate's thesis: $\psi_\infty(x) = e^{-2\pi i x}$, $\psi_p(x) = e^{+2\pi i\{x\}_p}$), which is the standard for the foundational document (2026-11-18, the author's decision; its sign at the finite places agrees with Mathlib's `stdAddChar`, and it is the same convention as Burnol's). Under convention T, the factor $\varepsilon(\chi) = (-i)^a$ of the Hartley kernel (`PAG.Part256.parFac`) agrees with the local constant $\varepsilon(1/2, \chi_\infty, \psi_\infty)$ at the infinite place, and $\tau(\chi)/\sqrt N$ agrees with the product of the local constants at the finite places (an agreement of values, outside Lean; local constants are defined in the style of Tate 1979; literature check of 2026-11-18, `notes/pag2_literature_ia_sign.md`, one independent check. Following it, the treatment of $i^a$ as a reserved normalization factor was lifted on the same day). That the power of $i$ comes from the infinite place does not depend on the convention, but whether the sign $\chi(-1)$ is placed at the infinite place or at the finite places does (in the opposite convention the infinite place gives $i^a$ and the product over the finite places is $\chi(-1)\tau(\chi)/\sqrt N$). Therefore, do not write "$\varepsilon(\chi)$ comes from the infinite place" without stating convention T. A1 remains a postulate. The material is in `notes/pag2_projection_material.md`.
 - The three propositions above are the author's definitions and design philosophy (the interpretive layer), not formalized theorems. Do not write notes that confuse their status.
 
 ## 2. Structure of the project and current position
diff --git a/CLAUDE.md b/CLAUDE.md
index beb74c1..08c88d4 100644
--- a/CLAUDE.md
+++ b/CLAUDE.md
@@ -22,6 +22,7 @@
   - 直線は、解像度を落としたときに創発する有効な姿である。
   - ただし、解像度を決めるパラメータは**未決定**である。$N$、$K$、$\Lambda$ のいずれとも勝手に同一視しないこと。
   - 命題3の置き方（2026-11-13、著者から選択を委任された著者側 Muse の決定として記録。著者はいつでも覆せる）：上の定義の文面は変更しない。解像度の操作の数学的な置き場は「対象の中の移行（離散から連続への変化）」ではなく、大域対象への**切り方（見方）の選択**として解釈の層に置く。すなわち、素点たちは制限積の因子として最初から並列に共存している全体が対象であり、有限レベル商と $\Lambda$ 切断（A8 で分離した2軸）はその全体への見方であって、創発の問いは「見方を粗くしたとき直線がどう見えるか」と読む。解像度を $N$・$\Lambda$ と同一視する禁止は従来どおり維持する（決まったのは問いの置き場であり、パラメータではない）。その後 2026-11-14 に構築側の引き継ぎメモ（`PAG2_handoff_part257.md`）を通じて、著者の 08:41 の定義の原文が著者側に届いた：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。」この定義は上の置き方と矛盾しない — 解像度が落ちる側の操作は完備化への滑り落ちであり、姿勢は極限でも離散構造の観測の維持、極限は直極限の側（すべての素点を同時に測る側）で取る。完備化（$L^2$、$\mathbb{R}$、直積の位相）を使うときは「解像度が落ちる側の操作と読む」と、読みとして断る。閉包・完備化に現れる連続体を「有効な姿」や目標として書かない。また著者は 2026-11-13 08:38 に命題3の読みとして L1（解像度＝測る素点の集合）を構築側で採った（L1 は提案を読みとして採ったもので、定義の文面そのものではない。$N$・$K$・$\Lambda$ のいずれとも同一視しない）。著者の指示（2026-11-12）により、「直線の創発」という表現は使わない（命題3に触れるときは「§1 の命題3（解像度と有効な姿）」と参照で書き、何がどう変わるかを数学の言葉で書く）。
+  - 「射影」の読み（2026-11-18、著者が留保つきで採用。解釈の層であり、形式化済みの定理ではない）：命名の意味は「アデール幾何とイーデル幾何を射影によって融合する」（2026-11-16、著者）。命名の「射影」は舞台と変換の組を指し、主は変換である。舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28（PAG23〜PAG32））で、その上で働く反転（乗法の側）と加法の変換（加法の側）の合成を射影と呼ぶ（有限レベルでは Part 252（PAG256）の $J\circ H_N/\sqrt N$）。原始指標についての位相がその成分である。標準の核は Part 252 の Hartley 核とする（形式化の追認。A1 の内容と揃う）。値は $\tau(\chi)/(i^a\sqrt N)$（`PAG.Part256.rootNum`。PAG256 の docstring の記号 W(χ) はこの値を指し、反転の $W$ とは別）で、原始指標ではルート数だが、その同定は Lean の外である（明記すること）。素朴なフーリエ核 $e(xy)$ の値 $\tau(\chi)/\sqrt N$ とは奇の指標で $i$ 倍ずれ、このずれを滑らかにしない。加法指標の規約は、規約 T（Tate の学位論文の加法指標：$\psi_\infty(x) = e^{-2\pi i x}$、$\psi_p(x) = e^{+2\pi i\{x\}_p}$）を基礎文書の標準とする（2026-11-18、著者の決定。Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol とも同じ規約）。規約 T のもとで、Hartley 核の因子 $\varepsilon(\chi) = (-i)^a$（`PAG.Part256.parFac`）は無限素点の局所定数 $\varepsilon(1/2, \chi_\infty, \psi_\infty)$ と一致し、$\tau(\chi)/\sqrt N$ は有限素点の局所定数の積と一致する（値の一致であり Lean の外。局所定数は Tate 1979 の流儀で定める。2026-11-18 の文献照合 `notes/pag2_literature_ia_sign.md`、独立照合 1 回。これを受けて、$i^a$ を正規化因子として留保する扱いは同日に外した）。$i$ の冪が無限素点から来ることは規約によらないが、符号 $\chi(-1)$ を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が $i^a$、有限素点の積が $\chi(-1)\tau(\chi)/\sqrt N$）。したがって、規約 T を明示せずに「$\varepsilon(\chi)$ は無限素点から来る」と書かない。A1 は公準のまま。材料は `notes/pag2_projection_material.md`。
 - 上記3命題は著者の定義・設計思想（解釈の層）であり、形式化済みの定理ではない。ノートではその地位を混同して書かないこと。
 
 ## 2. プロジェクトの構成と現在地
diff --git a/docs/overview-and-comparison.en.md b/docs/overview-and-comparison.en.md
index 5af2aa6..9052bce 100644
--- a/docs/overview-and-comparison.en.md
+++ b/docs/overview-and-comparison.en.md
@@ -99,6 +99,7 @@ Here $A_N$ is the shell algebra, which is the same as the known Terwilliger alge
 **Open questions**
 
 - How to formulate the "projection" in the name (the operation fusing the adelic and the idelic sides) as a specific map or construction.
+  - Adopted reading (proposed by the construction side, adopted with reservations by the author on 2026-11-18; interpretive layer, not a formalized theorem): the "projection" in the name refers to the pair of a stage and a transform, with the transform as the main sense. The stage is the projective line P¹ (Parts 19–28; inversion swaps 0 and ∞). The composition, acting on it, of inversion (the multiplicative side) and an additive transform (the additive side) is called the projection; at the finite level this is $J \circ H_N$ of Part 252. Its components on primitive characters are the phases. The standard kernel is the Hartley kernel of Part 252, with value $\tau(\chi)/(i^a\sqrt N)$ (the root number for primitive χ, but that identification is outside Lean). With the plain Fourier kernel $e(xy)$ the value is $\tau(\chi)/\sqrt N$, differing by a factor $i$ for odd characters. The additive character follows the convention of Tate's thesis ($e^{-2\pi i x}$ at the infinite place, $e^{+2\pi i\{x\}_p}$ at the finite places) as the standard; in that convention the factor $(-i)^a$ of the Hartley kernel agrees with the local constant at the infinite place, and $\tau(\chi)/\sqrt N$ agrees with the product of the local constants at the finite places (an agreement of values, outside Lean; literature check of 2026-11-18, `notes/pag2_literature_ia_sign.md`, Japanese). That the power of $i$ comes from the infinite place does not depend on the convention, but where the sign $\chi(-1)$ is placed does. Axiom A1 remains a postulate that chooses the phase of the boundary unitary to be this value. All ingredients are known, and this is not made a new Part (`notes/pag2_projection_material.md`, Japanese). Remaining question: a formulation as one construction across all places.
 - Whether the finite-level inductive system reaches the side of $T(0)$ (literature check for direction γ).
 - Whether the operation of resolution needs a formulation beyond L1.
 - Drafting the foundational document (author's side).
diff --git a/docs/overview-and-comparison.md b/docs/overview-and-comparison.md
index 9f539b3..51eafef 100644
--- a/docs/overview-and-comparison.md
+++ b/docs/overview-and-comparison.md
@@ -99,6 +99,7 @@
 **開いている問い**
 
 - 命名にある「射影」（アデールの側とイーデルの側を融合する操作）を、どの写像・構成として定式化するか。
+  - 採用した読み（構築側が出し、2026-11-18 に著者が留保つきで採用。解釈の層で、形式化済みの定理ではない）：命名の「射影」は舞台と変換の組を指し、主は変換。舞台は射影直線 P¹（Part 19〜28。反転が 0 と ∞ を入れ替える）。その上で働く反転（乗法の側）と加法の変換（加法の側）の合成を射影と呼び、有限レベルでは Part 252 の J∘H_N。原始指標についての位相がその成分で、標準の核は Part 252 の Hartley 核、値は τ(χ)/(i^a√N)（原始指標ではルート数だが、その同定は Lean の外）。素朴なフーリエ核 e(xy) では τ(χ)/√N で、奇の指標で i 倍ずれる。加法指標は Tate の学位論文の規約（無限素点で e^{−2πix}、有限素点で e^{+2πi{x}_p}）を標準とし、その規約で Hartley 核の因子 (−i)^a は無限素点の局所定数と、τ(χ)/√N は有限素点の局所定数の積と一致する（値の一致で Lean の外。2026-11-18 の文献照合 `notes/pag2_literature_ia_sign.md`）。i の冪が無限素点から来ることは規約によらないが、符号 χ(−1) の置き場は規約による。公準 A1 は境界ユニタリの位相をこの値に選ぶ公準のまま。部品はすべて既知で、新しいパートにはしない（`notes/pag2_projection_material.md`）。残る問い：全素点を通した一つの構成としての定式化。
 - 有限レベルの帰納系が $T(0)$ の側に届くか（方向 γ の文献照合）。
 - 解像度の操作に、L1 を超える定式化が要るか。
 - 基礎文書の起草（著者側）。
diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
index a922093..56b8ccf 100644
--- a/handoff/PAG2_handoff_part259.md
+++ b/handoff/PAG2_handoff_part259.md
@@ -772,6 +772,10 @@
 
 - **尾の統合照合（2026-11-18、補足 11 の独立の納品物）**：F3 の後の記録の直し、Part 258・259 の照合者 B の後の直し、Part 259 のノートと xlsx を、形式文の全文を渡した照合者 T が 1 回で照らした。偽・空虚な形式文はなし。食い違い 2 件（PAG263 の「`compat_dind_unique` は Part 258 により空虚に真」の根拠の誤り、Part 258 のノートの表の補助の行の誤り）ほかを、主張を変えない直しで直し、尾の台帳は空になった（記録 `notes/pag2_tail_audit_20261118.md`、`records/tail_audit/`、xlsx final81）。開いたまま残る問い：gcd ≠ 1 で (i) と D の側だけを満たす写像の不存在（数値の見込みのみ）。
 
+- **命名の「射影」の事前登録と材料ノート（2026-11-18、短期層）**：著者の命名（「アデール幾何とイーデル幾何を射影によって融合する」、−∞・∞・0 が射影で重なる）を受けて、「射影」を問いとして 4 点で事前登録した（`notes/pag2_prereg_projection.md`）。盲検の問いテストと内部照合（Part 13・19〜28 の P¹、定理 2.6）の結果、残余は空で、新しいパートは始めない。基礎文書の第 1・2 章のための材料ノート（`notes/pag2_projection_material.md`、第 3 版）に、構築側の読み（舞台 P¹／反転 ∘ 加法の変換／原始指標の位相、A1 は公準のまま）と対応表をまとめた。独立照合 2 回（`records/prereg_projection/outputs/`）。第 2 回の後の直しは照合者の直し案に沿った言い換えと範囲を狭める直しで、照合にかけていない（次の統合照合の対象）。注意：素朴なフーリエ核 e(xy) の成分は τ(χ)/√N、Part 252 の Hartley 核の成分は 𝔀(χ) = τ(χ)/(i^a√N)（`rootNum`）で、奇の χ で i 倍ずれ、素朴な核の値は核の符号でも変わる。PAG256 の docstring の W(χ) は 𝔀 を指す（反転ではない）。2026-11-18 19:01 の著者の決定（ノート第 4 版 §6）：読みは留保つきで採用（「ルート数であることは Lean の外」を明記し、奇の χ での i 倍のずれを滑らかにしない）。命名の「射影」は舞台と変換の両方を指し、主は変換。標準の核は Hartley 核（Part 252 の追認）。i^a は正規化因子として書き、無限素点への帰属は候補として留保。i^a の帰属と符号の規約の文献照合は、基礎文書が無限素点の読みを断定する前に行う（候補 1・候補 3・γ と同じ照合リスト）。CLAUDE.md §1（と英語版）には同日 19:03 の著者の指示で反映した。照合リストへの項目の文案はノート §9（照合リストは著者側のもので、構築側では変えていない）。
+
+- **照合リストの項目「i^a の帰属と符号の規約」の文献照合（2026-11-18、短期層）**：`notes/pag2_literature_ia_sign.md`（第 2 版）、記録 `records/literature_ia/`。結論：i の冪は無限素点から来る（規約によらない）。符号 ξ(−1) の置き場は加法指標の規約による。Tate の学位論文の加法指標（ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}。照合者が走査版で確認、構築側は原文未読）では、PAG256 の `parFac`（偶 1、奇 −i）が無限素点の局所定数 (−i)^a と、τ(χ)/√N が有限素点の局所定数の積と一致する（値の一致、Lean の外）。逆の規約では無限素点が i^a、有限素点の積が χ(−1)τ(χ)/√N。数値は構築側 209 指標、照合者 2,162 指標（局所関数等式からの直接評価を含む）。ラベル［既知］、PAG との対応は［再導出（小さい）］。照合後の直しは未照合（次の統合照合の対象）。2026-11-18 19:25 の著者の決定（ノート第 3 版 §9）：CLAUDE.md §1 の留保（i^a は正規化因子）を外して規約を明示した書き方に置き換え、規約 T を基礎文書の標準にした。CLAUDE.md §1 と英語版、材料ノート第 5 版 §6 の 4・5、概要に反映した。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
+
 ## 点検（2026-10-24、Part 204 の後）
 - 全体の再ビルド：PAG.lean〜PAG208.lean（208 本）を空のディレクトリで最初からコンパイルし直した。208 本すべて成功、エラー・警告 0、約 10 分。#print axioms 1903 項目すべて標準の公理（またはその一部）。作業用の .out と 208/208 一致。
 - ソースに sorry・admit・axiom 宣言・native_decide・implemented_by などはない（コメントを除いて検索）。
```

## §B 材料ノート（現行の全文）

# アーデル射影幾何 — 命名にある「射影」の材料（基礎文書の第 1・2 章のための対応表）

（2026-11-18。短期層の小さいノート。事前登録 `pag2_prereg_projection.md` の結論（残余は空、新しいパートは始めない）を受けて、基礎文書の起草（著者側）に渡す材料をまとめる。**ここに書く「射影」の読みは構築側が出した読みで、2026-11-18 19:01 に著者が留保つきで採用した（§6）。** 採用は読み（解釈の層）としての採用で、形式化済みの定理ではない。著者の定義（CLAUDE.md §1）の文面は変えない。第 1 版と第 2 版がそれぞれ独立照合を受け、その指摘で直した第 3 版に著者の決定を記録したのが第 4 版、文献照合の後の著者の決定を足したのがこの第 5 版である（§7〜§10）。）

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
3. **位相（公準）**：原始指標 χ については、その変換の成分が絶対値 1 の位相になる。標準の核は Part 252 の Hartley 核とする（著者の決定、§6）。この核での値は 𝔀(χ) = τ(χ)/(i^a √N)（`rootNum`）である。加法指標は規約 T（Tate の学位論文の加法指標：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）を標準とし、その規約で因子 ε(χ) = (−i)^a は無限素点の局所定数と一致する（値の一致、Lean の外。注意 2 の最後の項）。PAG256 の冒頭のコメントの読みでも、公準 A1 は境界ユニタリ U の原始指標の位相をこの値に選ぶ公準である。原始的なら 𝔀(χ) がルート数であることは Lean の外である。素朴なフーリエ核では、奇の χ で値がこの値と i 倍ずれる（注意 2。このずれは標準の核を決めても消えない）。原始的でない指標では、成分は位相でないことがある（絶対値が 1 未満になり、0 にもなる例がある。§3 の表 3 行目）。

注意 1（照合者の指摘）：1 と 2 は種類が違う。1 の y ↦ y⁻¹ はチャートの座標変換（関数を P¹ の上で定義するための恒等式）で、ねじれを持たない。ねじれ（指標ごとの位相）は 2 の変換の側にある。Lean でも、照合した範囲（PAG23・PAG26・PAG27・PAG256）では、2 の写像（`PAG.Part256.JH`）と 1 の 2 チャートモデル（`PAG.Part23.Compat` など）を結ぶ文はない。

注意 2（照合者の指摘で直した。式は加法核 e(xy) の規約で書く）：2 の変換の「加法のフーリエ型の変換」に何を使うかで、位相が変わる。N は法、u は単数。
- **素朴なフーリエ核 e(xy)**：成分は τ(χ)/√N。
  - 導出：`PAG.Part256.hartley_eq_of_isPrimitive` の証明の中の式 `hA`（∑ₓ χ(x) e(xy) = χ⁻¹(y) τ(χ)、`PAG.Part256.sum_mul_stdAddChar` と Mathlib の `gaussSum_mulShift_of_isPrimitive` から）に y = u⁻¹ を入れ、`PAG.Part256.inv_apply_units_inv`（χ⁻¹(u⁻¹) = χ(u)）を使って √N で割ると、(τ(χ)/√N)·χ(u) になる。独立した定理としては Lean に置いていない。
  - 単数の上では原始性は要らない（`PAG.Part256.hartley_units_inv` と同じ置換 x ↦ u·x の議論。照合者が N ≤ 30 のすべての指標で数値確認。数値は証明ではない）。
  - **核の符号に依存する**：核を e(−xy) にすると、成分は χ(−1)τ(χ)/√N になる（`PAG.Part256.hartley_eq_of_isPrimitive` の証明の中の式 `hB`・`hneg` から。y = 1 の場合は `PAG.Part256.sum_mul_stdAddChar_neg`）。「素朴なフーリエ核」は符号の規約を決めるまで一つに決まらない。
- **Part 252 の離散 Hartley 核**（cas = cos + sin。核は ((1 − i)e(t) + (1 + i)e(−t))/2、`PAG.Part256.casKer_eq`）：成分は 𝔀(χ) = ε(χ)τ(χ)/√N。ε(χ) は `PAG.Part256.parFac` で、偶で 1、奇で −i（`parFac_of_even`・`parFac_of_odd`）。すべての χ について `PAG.Part256.JH_eq_rootNum_mul_any` と `PAG.Part256.rootNum_eq` から出る。式 𝔀(χ) = τ(χ)/(i^a √N) は `rootNum` の定義そのもので、すべての χ で成り立つ。原始的なら 𝔀(χ) がルート数であることは Lean の外（`rootNum` の docstring）。
- **二つの関係（e(xy) の規約で）**：偶の χ では一致する（どちらも τ(χ)/√N）。奇の χ では 𝔀(χ) = −i·τ(χ)/√N、すなわち素朴な成分 = i·𝔀(χ)。核を e(−xy) にすると関係は反転し、𝔀(χ) = i·（素朴な成分）になる。
- **帰属の読み（候補として留保。未確認）**：Tate の局所分解の通常の規約では、ルート数の i^a は無限素点の局所因子から来る（照合者の知識による。確信度：中）。ただし大域の加法指標は無限素点と有限素点とで符号を逆に取るのが通例で、有限素点の局所因子が τ(χ)/√N になるか χ(−1)τ(χ)/√N になるかは規約で変わりうる（再照合者の知識。確信度：低〜中）。この読みが正しければ、Part 252 の Hartley の形は、無限素点の符号の因子を有限レベルの変換に取り込んだ形と読める。著者の決定（§6）により、文献照合が済むまでは i^a を正規化因子として書き、この帰属は候補として留保する。i^a の帰属と有限素点の加法指標の符号の文献照合は、基礎文書が無限素点の読みを断定する前に行う。→ 2026-11-18 に照合した（`pag2_literature_ia_sign.md`、独立照合 1 回）。結果：i の冪は無限素点から来る（規約によらない）。符号 ξ(−1) の置き場は規約による。Tate の学位論文の加法指標の規約（ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）では、ε(χ) = (−i)^a が無限素点の局所定数と、τ(χ)/√N が有限素点の局所定数の積と一致する（値の一致。Lean の外）。同日、著者の決定で、i^a を正規化因子として留保する扱いを外し、規約 T を基礎文書の標準とした（§6 の 4・5）。

## §3 対応表

| 層 | 有限レベル（ℤ/N） | 無限素点 | ラベル |
|---|---|---|---|
| 舞台：射影直線と反転 | P¹(ℤ/N) := 単模ベクトル / 単数倍（Part 23（PAG27）、`PAG.Part27.ProjLine`）。反転 [a:b] ↦ [b:a]（`PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`。一般の N）。p 素数、K ≥ 1 で、点モデル（Part 22（PAG26）、`PAG.Part26.Pt`）と同型（`PAG.Part27.projEquiv`）、点の数 p^K + p^(K−1)（`PAG.Part27.card_ProjLine`）。反転どうしの対応 `PAG.Part27.toProj_Wpt` は K ≥ 1 の仮定なしで述べられている。2 チャートモデルと赤道での貼り合わせ条件 F_N(y) = F_S(y⁻¹)（Part 19（PAG23）、`PAG.Part23.Compat`、反転 `PAG.Part23.W`。点モデルの関数との同型は一般の N で `PAG.Part26.ptEquiv`、反転の対応は `PAG.Part26.toP1_comp_Wpt`）。2 チャートモデル（点モデル）が P¹(ℤ/N) と同型であることが Lean で示されているのは N = p^K（K ≥ 1）だけ。N が 2 つ以上の素因数を持つときは点の数が一致しない（数え上げ：\|Pt N\| = 2N − φ(N)、\|P¹(ℤ/N)\| = N∏_{p\|N}(1 + 1/p)。N = 6 で 10 点と 12 点。この不一致を述べる文は Lean にない）。N ≥ 2 では 0 = [0:1] と ∞ = [1:0] は別の点で、反転がこの 2 点を入れ替える（有限の側に点の同一視はない。この文も Lean にはない。N = 1 では 1 点） | P¹(ℝ)。ℝ_{>0} の対数座標 t = log x で、反転 x ↦ 1/x は t ↦ −t になり、両端 −∞・+∞（乗法の 0・∞）を入れ替える。射影直線では両端が一点（著者確認済みの読み）。有限の側との違い：無限素点では両端が重なる | ［既知］（P¹(ℤ/N) はモジュラー記号の標準の道具、Manin 1972 など。Lean は Part 19〜28） |
| 変換：反転 ∘ 加法の変換 | J∘H_N/√N（Part 252（PAG256）、`PAG.Part256.JH`。J は単数の上の反転 u ↦ u⁻¹、H_N は離散 Hartley 変換）。ℤ/N の関数を単数の上の関数に送る写像で、同じ空間の上の作用素ではない。素朴なフーリエ核での形は §2 の注意 2 | モノグラフ層の境界ユニタリ U（イデール類群の上の反転と、境界条件）。Lean にしていない | ［再導出］（PAG256 の冒頭のコメントの記載どおり「既知の事実の書き直し」。Tate 1950 の局所関数等式の有限版と読む） |
| 位相：原始指標の成分 | すべての指標 χ と単数 u で (J H_N χ)(u)/√N = 𝔀(χ)·χ(u)（`PAG.Part256.JH_eq_rootNum_mul_any`）。原始的なら \|𝔀(χ)\| = 1（`PAG.Part256.normSq_rootNum`）。原始的なら 𝔀(χ) がルート数であることは Lean の外（`rootNum` の docstring）。原始的でない指標では位相でないことがある：法 2 の自明な指標（原始的でないことは `PAG.Part256.removal_counterexample` の第 1 成分）で \|𝔀\|² = 1/2（`PAG.Part256.removal_counterexample_normSq`）、法 4 の自明な指標で 0（`PAG.Part256.removal_counterexample_four`）。原始的でない指標すべてで位相でないという全称の文は Lean の外（照合者の数値では N ≤ 30 のすべての非原始指標で \|𝔀\| ≤ 1/√2。数値は証明ではない） | Tate の γ 因子（ガンマ因子の比）。公準 A1 は U の位相をこの値（λ = 0 での値）に選ぶ。両立の分類は定理 2.6 | ［既知］（Tate 1950、Burnol 1998〜2001）。A1 は公準のまま |

## §4 Lean にしていないこと・確かめていないこと

- P¹ と点モデルの同型は N = p^K（K ≥ 1）だけ。一般の N では、`PAG.Part27.ProjLine` の定義と反転（`PAG.Part27.Wproj`・`PAG.Part27.Wproj_Wproj`）が示されている（`PAG.Part27.mk_eq_mk` は単数倍で同じ点になることを言う補題で、反転がうまく定義されることを示すのに使われる。反転の文ではない）。点モデル `PAG.Part26.Pt N` と P¹(ℤ/N) が N に 2 つ以上の素因数があるとき一致しないことは、数え上げによるもので Lean の文ではない。全素点の制限積 P¹(𝔸_ℚ) = ∏'_v P¹(ℚ_v) と、P¹(ℤ_p) = lim P¹(ℤ/p^K) は Lean にしていない。
- 境界ユニタリ U と公準 A1 は、照合した範囲（Part 19・22・23・252、すなわち PAG23・PAG26・PAG27・PAG256）では Lean の形式文に出てこない（PAG256 の冒頭のコメントも「U と A1 は Lean の文に出てこない」と書く）。鎖全体については検索していない。Tate の局所関数等式そのもの、定理 2.6 も Lean にしていない（定理 2.6 の条件を A1 の位相が満たすことは PAG16・PAG173・PAG198 の 3 定理から出る、と CLAUDE.md §3 に記録あり。組み合わせた 1 つの文は未形式化）。
- 「射影 = 舞台の P¹ と、反転 ∘ 加法の変換」は読み（2026-11-18 に著者が採用）であり、Lean の文ではない。Part 252 の J∘H_N を「変換の層の有限版」と呼ぶのも読みである。PAG256 の言葉では、`JH_eq_rootNum_mul` の docstring は「構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。U と A1 は文に出てこない）」、冒頭のコメント（`/-` で始まる通常のコメントで、docstring ではない）の読みは「公理 A1 の境界ユニタリの原始指標の部分」である。PAG256 の形式文には貼り合わせに当たる対象は出てこない。冒頭のコメントでは、重なりの読み「ねじれた貼り合わせ（U）」と、構築者が再構成した主張「U = J∘H_N/√N」を通して、間接に結びつけられている。PAG23・PAG26 の「貼り合わせ条件」は 2 チャートモデルの条件（`PAG.Part23.Compat`）である。
- 照合した範囲では、`PAG.Part256.JH` と 2 チャートモデル（`PAG.Part23.P1F`・`PAG.Part23.Compat`・`PAG.Part23.W`）・`PAG.Part27.ProjLine` を結ぶ Lean の文はない。§2 の 2 の変換が「0 の側と ∞ の側をつなぐ」に対応する Lean の文もない。
- ルート数の i^a の帰属と、有限素点の加法指標の符号の規約（§2 の注意 2）は文献で未確認。
- 盲検の問いテストで、全素点を通して「各素点の 0 と ∞ の貼り合わせ」を一つの構成として書いた文献は見つからなかった（MathSciNet・zbMATH は未照合）。部品はすべて既知。

## §5 対照群（§7）

- 関数体 𝔽_q(t) でも Tate の局所関数等式は同じ形で成り立つ（Lean の外の既知の事実）。§2 の 2 の変換の形と、§2 の 3 のうちガウス和 τ(χ)/√N の部分は、ℚ に固有の算術を使わない形式の文である。
- ただし §2 の 3 で Hartley 核を採ると（PAG256 の冒頭の読み）、値 𝔀(χ) は偶奇による因子 ε(χ)（χ(−1) で決まる）を含む。注意 2 の帰属の読みが正しければ、この因子は無限素点の側（ℚ に固有の側）に属する。関数体での対応物は確かめていない。
- 関数体では、t ↦ 1/t が素点 0 と素点 ∞ を入れ替える。ただしこの P¹_{𝔽_q} は「点が素点であるような大域の曲線」で、§2 の 1 の「各素点の座標の直線」とは別の対象である（照合者の指摘）。
- ℚ に固有に残るのは、無限素点がアルキメデス的で、実数の順序（符号）と二つの端 ±∞ があることである（「−∞ と ∞」の重なり）。上の ε(χ) の因子も、読みが正しければここに属する。

## §6 著者の決定（2026-11-18 19:01）

第 3 版の §6 で仰いだ 3 つの判断に、著者が次のとおり答えた（著者の言葉を要約せずに近い形で記す）。

1. **読みの採用：採る。** 舞台の P¹、反転と加法の変換の合成、原始指標の位相を、基礎文書の第 1・2 章の材料にする。留保は二つ：「ルート数であることは Lean の外」を明記すること、奇の指標での i 倍のずれを滑らかにしないこと。
2. **命名：両方を指し、主は変換。** 舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ、という組の形にする。「射影により融合」という著者の言い方とも一致する。
3. **核：Hartley 核を標準にする。** Part 252 の形式化の追認で、A1 の内容とも揃う。i^a の帰属と符号の規約の文献照合は、基礎文書が無限素点の読みを断定する前に行う（候補 1・候補 3・γ と同じ照合リストに入れる）。それまでは i^a は正規化因子として書き、読みは候補として留保する。

決まったことは、補足 7 の規則に従い著者側の記録（CLAUDE.md §1・§2 と申し送り）に戻す。反映の文案は §9 に置き、著者の指示（19:03）で CLAUDE.md §1 と英語版に反映した。

文献照合（`pag2_literature_ia_sign.md`）の後、2026-11-18 19:25 に著者が次の 2 つを決めた（照合ノート §9 の 1・2 を「進める」）。

4. **i^a の留保を外す。** CLAUDE.md §1 の「i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する」を、規約を明示した書き方に置き換える：規約 T のもとで ε(χ) = (−i)^a は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N は有限素点の局所定数の積と一致する（値の一致、Lean の外）。i の冪が無限素点から来ることは規約によらないが、符号 χ(−1) の置き場は規約による。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
5. **規約 T を基礎文書の標準にする。** Mathlib の `stdAddChar` と有限素点の符号が合い、Tate の学位論文の加法指標・Burnol とも同じ規約。

## §7 照合の記録（第 1 回）

- 第 1 版（`before_material_v1.md`）を、形式文の全文（PAG23・PAG26・PAG27・PAG256）を渡した新しい照合者が照らした（依頼文 `outputs/material_check_request.md`、出力 `outputs/material_check_output.md`、所要 約 6 分）。
- 主な指摘と直し：原始性の限定の抜け（§2 の 3、表 3 行目）、素朴なフーリエ核と Hartley 核の取り違え（§2 の注意 2 を新設）、`JH_eq_rootNum_mul` を「ルート数」の根拠にした当て方（外した）、番号と名前空間の取り違えの罠（完全修飾名にした。ただし第 2 版では一部だけで、第 3 版で残りを直した。§8）、K ≥ 1 の抜け、2 チャートモデルが P¹ になる範囲、一般の N の `ProjLine` の記述、docstring の引用の但し書き、`JH` と 2 チャートモデルを結ぶ文がないこと、「無限素点の U」の書き方、記号 W の衝突（ι と 𝔀 に分けた）、有限と無限の対応のずれ、表 2 行目のラベル（［再導出］にそろえた）。

## §8 照合の記録（第 2 回：直した版の再照合）

- 第 2 版（`before_material_v2.md`）を、第 1 回と同じ形式文の全文（PAG23・PAG26・PAG27・PAG256）と第 2 版の全文を渡した新しい照合者が照らした（入力 `input_material_v2.md`、依頼文 `outputs/material_recheck_request.md`、出力 `outputs/material_recheck_output.md`、所要 約 7 分）。照合者は手元で式の数値確認（N ≤ 30）を行った。数値は証明ではない。
- 結論：第 2 版で新しく入った明確な誤りが 1 件（§4 の「「貼り合わせ」という語は Lean の側にはない」。PAG256 の冒頭のコメントと PAG23・PAG26 に語がある）。言い過ぎと曖昧さがいくつか。宣言名・完全修飾名・式はほかは一致。
- 直したこと（照合者の指摘 1〜9 の順）：
  1. §4 の「貼り合わせ」の文を、照合者の直し案のとおりに差し替えた。
  2. 注意 2 を式で書いた（奇の χ で 𝔀 = −i·τ/√N、素朴な成分 = i·𝔀）。核の符号への依存（e(−xy) で χ(−1)τ/√N、関係の反転）を明記し、§6 の 3 にも規約を添えた。文献照合の項目に有限素点の加法指標の符号を加えた。
  3. 表 3 行目を「位相でないことがある」に弱め、全称の文は Lean の外と断った。法 2 の非原始性の根拠に `removal_counterexample` を足した。
  4. 注意 2 と記号の行で、`rootNum` の定義（すべての χ）とルート数との同定（Lean の外）を書き分け、根拠に `JH_eq_rootNum_mul_any`・`rootNum_eq` を引いた。
  5. §2 の 3 の「この値」を、PAG256 の冒頭の読みの値 𝔀(χ)（Hartley 側）と特定し、素朴な核では奇の χ でずれることを書いた。
  6. 記号の行と §3・§4 の宣言名を完全修飾名にし、PAG256 の W(χ) が 𝔀 を指すことを注記した。
  7. §4 の U と A1 の文の範囲を「照合した範囲（PAG23・PAG26・PAG27・PAG256）」に狭めた。注意 1 と §4 の「結ぶ文はない」も同じ範囲に狭めた。
  8. 注意 2 の素朴な核の項に、`inv_apply_units_inv` が要ることと、単数の上では原始性が要らないことを書いた。
  9. 軽微な点：「のときだけ」を「Lean で示されているのは N = p^K だけ」と「2 つ以上の素因数で点の数が一致しない」に分け、「0 と ∞ は別の点」に N ≥ 2 を付けた。`toProj_Wpt` は K ≥ 1 なしと書いた。`mk_eq_mk` を反転の補題から外した。「有限素点の作用素」を「有限レベル N の変換」に、§2 の 2 の「作用素」を「変換（写像）」にそろえた。PAG256 の冒頭は通常のコメントと書いた。§5 の第 1 項と第 3 項の張り合いを、ε(χ) の因子を分けて書くことで解いた。
- この第 3 版は、第 2 回の照合の後の直しを照合にかけていない。直しはすべて、照合者が示した直し案に沿った言い換えと主張の範囲を狭める直しで、新しい主張は加えていない（構築側の判断。補足 8 の停止の規約の「主張を変えない直し」に当たると読む）。§5 の第 2 項（ε(χ) の因子の帰属）は張り合いの解消のために書き足した文で、注意 2 の未確認の読みに条件づけてある。この判断が妥当かどうかは、次の統合照合で確かめる対象とする。

## §9 著者の決定の記録（第 4 版）

- 第 3 版（`before_material_v3.md`）に、著者の決定（2026-11-18 19:01、§6）を記録した。直したところ：冒頭の地位の文（「著者の確認待ち」→「留保つきで採用」）、§2 の見出しと命名の決定（両方を指し、主は変換）、§2 の 3（標準の核を Hartley 核とし、i^a を正規化因子として書く。ルート数であることは Lean の外。奇の χ での i 倍のずれは消えない）、注意 2 の帰属の読み（候補として留保、文献照合は基礎文書が無限素点の読みを断定する前）、§4 の第 3 項（読みが採用されたこと）、§6（判断の依頼を決定の記録に置き換えた）。
- これらは著者の決定の記録で、Lean についての主張は変えていない。照合にはかけていない（補足 8 の「主張を変えない直し」に当たると読む。次の統合照合の対象に含める）。
- 著者側の記録に戻すための文案を次に置いた。CLAUDE.md §1 への追記は、2026-11-18 19:03 の著者の指示で、CLAUDE.md と英語版 CLAUDE.en.md の §1（命題 3 の置き方の次の箇条）に反映した。反映の際に文案へ足したもの：命名の意味（2026-11-16）、Part と PAG の番号の併記（§7 の (iv)）、PAG256 の docstring の記号 W(χ) が反転の W とは別であることの注記、「明記すること」の一句。照合リストは著者側のもので、構築側では変えていない。

**CLAUDE.md §1 への追記の文案**（解釈の層の箇条として）：

> 「射影」の読み（2026-11-18、著者が採用。解釈の層であり、形式化済みの定理ではない）：命名の「射影」は舞台と変換の組を指し、主は変換である。舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28）、その上で働く反転（乗法の側）と加法の変換（加法の側）の合成を射影と呼ぶ。原始指標についての位相がその成分である。標準の核は Part 252 の Hartley 核とする（形式化の追認。A1 の内容と揃う）。値は 𝔀(χ) = τ(χ)/(i^a√N)（`PAG.Part256.rootNum`）で、原始指標ではルート数だが、その同定は Lean の外である。素朴なフーリエ核 e(xy) とは奇の指標で i 倍ずれ、このずれを滑らかにしない。i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する。A1 は公準のまま。材料は `notes/pag2_projection_material.md`。

**照合リストへの項目の文案**（候補 1・候補 3・γ と同じリスト）：

> i^a の帰属と符号の規約：(a) ルート数の i^a は、Tate の局所分解で無限素点の局所因子から来るか。(b) 大域の加法指標の符号の規約（無限素点と有限素点で符号を逆に取るか）のもとで、有限素点の局所因子は τ(χ)/√N と χ(−1)τ(χ)/√N のどちらになるか。期限：基礎文書が無限素点の読みを断定する前。それまで i^a は正規化因子として書く。出所：`notes/pag2_projection_material.md` §2 の注意 2。

## §10 文献照合の後の著者の決定の記録（第 5 版）

- 第 4 版（`before_material_v4.md`）に、文献照合の結果と 2026-11-18 19:25 の著者の決定（§6 の 4・5）を記録した。直したところ：冒頭の版の文、§2 の 3（i^a を正規化因子として書く扱いを、規約 T での無限素点の局所定数との一致に置き換えた）、注意 2 の帰属の読み（照合の結果と決定を追記）、§6（4・5 を追加）。
- 決定は CLAUDE.md §1 と英語版にも反映した。
- これらは著者の決定と照合の結果の記録で、Lean についての主張は変えていない。照合にはかけていない（次の統合照合の対象に含める）。根拠にした文献照合ノートの第 2 版も、照合後の直しが未照合である。

## §C 文献照合ノート（現行の全文）

# アーデル射影幾何 — 照合リストの項目「i^a の帰属と加法指標の符号の規約」の文献照合

（2026-11-18。短期層の小さいノート。新しいパートではない。出所：CLAUDE.md §1 の「射影」の読み（2026-11-18、著者が留保つきで採用）と、材料ノート `pag2_projection_material.md` §2 の注意 2。著者の決定で、基礎文書が無限素点の読みを断定する前に行う照合として、候補 1・候補 3・γ と同じ照合リストに入った項目である。著者の定義（§1）の文面と A1 の地位は変えない。第 1 版を独立照合にかけ、その指摘で直した第 2 版に、著者の決定を記録したのがこの第 3 版である（§8・§9）。）

記号：ξ は法 N の原始 Dirichlet 指標、a は ξ が奇なら 1・偶なら 0、τ(ξ) = Σ_x ξ(x) e^{2πix/N}、W(ξ) = τ(ξ)/(i^a √N)（古典的なルート数。Lean では `PAG.Part256.rootNum` の値 𝔀(ξ)。ルート数であることは Lean の外）。局所定数 ε(s, χ_v, ψ_v) は、Tate 1979（Corvallis）の流儀で定める：f̂(y) = ∫ f(x) ψ(xy) dx、局所関数等式の定数、ψ_v に関して自己双対な測度。

## §1 問いと結論

照合リストの項目は次の 2 つだった。

- (a) ルート数の i^a は、Tate の局所分解で無限素点の局所因子から来るか。
- (b) 有限素点の加法指標の符号の規約のもとで、有限素点の局所因子の積は τ(ξ)/√N と ξ(−1)τ(ξ)/√N のどちらになるか。

結論：

- (a) **i の冪は無限素点から来る。符号 (−1)^a の置き場は規約による。** 無限素点の局所定数は i の冪で、有限素点の局所定数はガウス和である（i の冪を含まない）。ここまではどちらの規約でも同じ。ただし冪の向きは規約で変わる：Tate の学位論文の加法指標の規約（下の規約 T）では ε(1/2, χ_∞, ψ_∞) = (−i)^a = i^{−a}、逆の規約 C では i^a。［既知］（確信度：高）
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
  - Roy–Schmidt–Yi, "Classical and adelic Eisenstein series", arXiv:2109.07649 §4.3：ψ を Tate の学位論文で定義されたものとし、ψ_∞(x) = e^{−2πix} と書く。
  - Burnol, arXiv:math/9811040（"Spectral Analysis of the Local Conductor Operator"）：実素点で exp(−2πit)、有限素点で exp(2πi{Tr t})。モノグラフ層が引く Burnol と同じ著者。読んだ範囲には、Tate の規約への言及も符号の選び方の説明もない。
  - arXiv:1502.02633 も同じ指標を「標準の加法指標」として書く。ただし、Tate の学位論文に従うと明記しているのは Haar 測度の正規化だけである（第 1 版の「Tate の学位論文の規約として書く」は言い過ぎだったので直した）。
- **規約 C**（逆の規約）：ψ_∞(x) = e^{+2πix}、ψ_p(x) = e^{−2πi{x}_p}。例：arXiv:2604.25288 §5.1、arXiv:1511.04265 式 (3.72)〜(3.75)（照合者が確認）。
- 指標の対応は ψ によらない：ξ に対応するイデール類指標 χ は、不分岐の ℓ で χ_ℓ(ℓ) = ξ(ℓ)。分岐する p では、χ_p の ℤ_p^× への制限が (ξ^{(p)})^{−1}（Roy–Schmidt–Yi 式 (150)。ξ = ∏ ξ^{(p)} は中国剰余定理による分解）。χ_∞ は偶で自明、奇で符号（同 式 (151)）。

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
  - p 進の局所定数を局所関数等式から有限和で直接評価し、§4 の閉じた式と比べた（6,288 回、最大差 3.1×10⁻¹³）。
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

1. **留保を外す。** CLAUDE.md §1（と英語版）の「i^a は正規化因子として書き、無限素点から来るという帰属は候補として留保する」を、規約を明示した書き方に置き換えた。規約 T のもとで、ε(ξ) = (−i)^a は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(ξ)/√N は有限素点の局所定数の積と一致する（値の一致、Lean の外）。i の冪が無限素点から来ることは規約によらないが、符号 ξ(−1) の置き場は規約による。規約 T を明示せずに「ε(ξ) は無限素点から来る」と書かない。
2. **規約 T を基礎文書の標準にする。** Mathlib の `stdAddChar` と有限素点の符号が合い、Tate の学位論文の加法指標・Burnol とも同じ規約。

記録：決定は CLAUDE.md §1 と英語版、材料ノート（第 5 版）の §6 の 4・5、概要の文書、引き継ぎメモに反映した。このノートの第 2 版の照合後の直しは未照合のままで、次の統合照合の対象に含める（決定の根拠にした版が照合後の直しを含むことを、ここに明記する）。第 2 版の §9 の文案は `before_decision_v2.md` に残る。

## §D CLAUDE.md §1 の「射影」の箇条（現行の全文）

  - 「射影」の読み（2026-11-18、著者が留保つきで採用。解釈の層であり、形式化済みの定理ではない）：命名の意味は「アデール幾何とイーデル幾何を射影によって融合する」（2026-11-16、著者）。命名の「射影」は舞台と変換の組を指し、主は変換である。舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28（PAG23〜PAG32））で、その上で働く反転（乗法の側）と加法の変換（加法の側）の合成を射影と呼ぶ（有限レベルでは Part 252（PAG256）の $J\circ H_N/\sqrt N$）。原始指標についての位相がその成分である。標準の核は Part 252 の Hartley 核とする（形式化の追認。A1 の内容と揃う）。値は $\tau(\chi)/(i^a\sqrt N)$（`PAG.Part256.rootNum`。PAG256 の docstring の記号 W(χ) はこの値を指し、反転の $W$ とは別）で、原始指標ではルート数だが、その同定は Lean の外である（明記すること）。素朴なフーリエ核 $e(xy)$ の値 $\tau(\chi)/\sqrt N$ とは奇の指標で $i$ 倍ずれ、このずれを滑らかにしない。加法指標の規約は、規約 T（Tate の学位論文の加法指標：$\psi_\infty(x) = e^{-2\pi i x}$、$\psi_p(x) = e^{+2\pi i\{x\}_p}$）を基礎文書の標準とする（2026-11-18、著者の決定。Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol とも同じ規約）。規約 T のもとで、Hartley 核の因子 $\varepsilon(\chi) = (-i)^a$（`PAG.Part256.parFac`）は無限素点の局所定数 $\varepsilon(1/2, \chi_\infty, \psi_\infty)$ と一致し、$\tau(\chi)/\sqrt N$ は有限素点の局所定数の積と一致する（値の一致であり Lean の外。局所定数は Tate 1979 の流儀で定める。2026-11-18 の文献照合 `notes/pag2_literature_ia_sign.md`、独立照合 1 回。これを受けて、$i^a$ を正規化因子として留保する扱いは同日に外した）。$i$ の冪が無限素点から来ることは規約によらないが、符号 $\chi(-1)$ を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が $i^a$、有限素点の積が $\chi(-1)\tau(\chi)/\sqrt N$）。したがって、規約 T を明示せずに「$\varepsilon(\chi)$ は無限素点から来る」と書かない。A1 は公準のまま。材料は `notes/pag2_projection_material.md`。

## §E Lean の形式文：PAG23.lean（全文）
```lean
/-
  PAG 2.0 Part 19（2026-10-18）— P¹(Z/p^K) の 2 チャートモデルと北チャートの鏡像定理
  P¹ 上の関数 = 南チャート座標 x（点 [x:1]）と北チャート座標 y（点 [1:y]）の関数の組 (F_S, F_N) で、
  赤道（単数）上で F_N(y) = F_S(y⁻¹) を満たすもの。反転 W は (F_S, F_N) ↦ (F_N, F_S)。
  南の畳み込み B_S と北の畳み込み B_N := W B_S(W·, W·)。
-/
import PAG22

namespace PAG.Part23

open ZMod Finset PAG.Part17 PAG.Part19 PAG.Part21

/-! ## 1. 2 チャートモデル -/

section Model

variable {N : ℕ}

/-- P¹ 上の関数（南座標の関数と北座標の関数の組）。 -/
abbrev P1F (N : ℕ) := (ZMod N → ℂ) × (ZMod N → ℂ)

/-- 貼り合わせ条件: 赤道（単数）上で F_N(y) = F_S(y⁻¹)。 -/
def Compat (F : P1F N) : Prop := ∀ y : ZMod N, IsUnit y → F.2 y = F.1 y⁻¹

/-- 反転 W: [x:1] ↔ [1:x]、関数では南北の入れ替え。 -/
def W (F : P1F N) : P1F N := (F.2, F.1)

theorem W_W (F : P1F N) : W (W F) = F := rfl

theorem inv_inv_of_unit {y : ZMod N} (hy : IsUnit y) : IsUnit y⁻¹ ∧ (y⁻¹)⁻¹ = y := by
  obtain ⟨u, rfl⟩ := hy
  rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit, inv_inv]
  exact ⟨Units.isUnit _, rfl⟩

/-- W は貼り合わせ条件を保つ。 -/
theorem compat_W {F : P1F N} (hF : Compat F) : Compat (W F) := by
  intro y hy
  obtain ⟨hy', hyy⟩ := inv_inv_of_unit hy
  simp only [W]
  rw [hF y⁻¹ hy', hyy]

open Classical in
/-- 南チャートの関数を P¹ 上へ（北の内部では 0）。 -/
noncomputable def extS (h : ZMod N → ℂ) : P1F N := (h, fun y => if IsUnit y then h y⁻¹ else 0)

open Classical in
/-- 北チャートの関数を P¹ 上へ（南の内部では 0）。 -/
noncomputable def extN (h : ZMod N → ℂ) : P1F N := (fun x => if IsUnit x then h x⁻¹ else 0, h)

theorem compat_extS (h : ZMod N → ℂ) : Compat (extS h) := fun y hy => by simp [extS, hy]

theorem compat_extN (h : ZMod N → ℂ) : Compat (extN h) := fun y hy => by
  obtain ⟨hy', hyy⟩ := inv_inv_of_unit hy
  simp [extN, hy', hyy]

theorem W_extS (h : ZMod N → ℂ) : W (extS h) = extN h := rfl

theorem extS_smul (a : ℂ) (h : ZMod N → ℂ) : extS (a • h) = a • extS h := by
  ext y <;> simp [extS]

theorem extN_smul (a : ℂ) (h : ZMod N → ℂ) : extN (a • h) = a • extN h := by
  ext y <;> simp [extN]

variable [Fintype (ZMod N)]

/-- 南の畳み込み（南チャートで畳み込み、北の内部は 0）。 -/
noncomputable def BS (F G : P1F N) : P1F N := extS (PAG.Part15.conv F.1 G.1)

/-- 北の畳み込み B_N := W B_S(W·, W·)。 -/
noncomputable def BN (F G : P1F N) : P1F N := W (BS (W F) (W G))

/-- B_N は北チャートでの畳み込み。 -/
theorem BN_eq (F G : P1F N) : BN F G = extN (PAG.Part15.conv F.2 G.2) := rfl

end Model

/-! ## 2. 殻ケットと鏡像定理 -/

section Mirror

variable {p : ℕ} [hp : Fact p.Prime]

/-- 南の殻ケット |w, χ⟩（w ≥ 0）。 -/
noncomputable def kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) : P1F (p ^ K) :=
  extS (ket K w c h χ)

/-- 北の殻ケット |−w, χ⟩: 北座標 y = p^w u で値 χ(u⁻¹)（step30 の規約）。 -/
noncomputable def kN (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) : P1F (p ^ K) :=
  extN (ket K w c h ((χ⁻¹ : DirichletCharacter ℂ (p ^ c)) : ZMod (p ^ c) → ℂ))

/-- **W|w, χ⟩ = |−w, χ̄⟩**。 -/
theorem W_kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    W (kS K w c h χ) = kN K w c h χ⁻¹ := by
  rw [kS, W_extS, kN, inv_inv]

/-- 共役指標の J̃: J̃(χ₁⁻¹, χ₂⁻¹; ψ⁻¹) = conj J̃(χ₁, χ₂; ψ)。 -/
theorem Jt_inv (n v : ℕ) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v)))
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    gaussSum χ₁⁻¹ stdAddChar * gaussSum χ₂⁻¹ stdAddChar /
        (gaussSum ψ⁻¹ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))
      = starRingEnd ℂ (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
        (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))) := by
  have hinv : ∀ {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M),
      gaussSum χ⁻¹ stdAddChar = χ (-1) * starRingEnd ℂ (gaussSum χ stdAddChar) := by
    intro M _ χ
    rw [PAG.Part9.conj_gaussSum, ← mul_assoc, PAG.Part9.chi_neg_one_sq, one_mul]
  have : NeZero (p ^ (n + 1 - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hψ : ψ (-1) = χ₁ (-1) * χ₂ (-1) := by
    have h0 := hprod (-1)
    have hπ : ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) (ZMod (p ^ (n + 1 - v))) (-1) = -1 := by
      rw [map_neg, map_one]
    rw [hπ, MulChar.coeToFun_mul, Pi.mul_apply] at h0
    exact h0.symm
  rw [hinv χ₁, hinv χ₂, hinv ψ, hψ, map_div₀, map_mul, map_mul, Complex.conj_ofReal]
  have h1 := PAG.Part9.chi_neg_one_sq χ₁
  have h2 := PAG.Part9.chi_neg_one_sq χ₂
  have hne1 : χ₁ (-1) ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
  have hne2 : χ₂ (-1) ≠ 0 := fun h => by rw [h, zero_mul] at h2; exact zero_ne_one h2
  rw [show χ₁ (-1) * starRingEnd ℂ (gaussSum χ₁ stdAddChar) * (χ₂ (-1) * starRingEnd ℂ (gaussSum χ₂ stdAddChar))
      = (χ₁ (-1) * χ₂ (-1)) * (starRingEnd ℂ (gaussSum χ₁ stdAddChar) * starRingEnd ℂ (gaussSum χ₂ stdAddChar)) by ring,
    mul_assoc (χ₁ (-1) * χ₂ (-1)), mul_div_mul_left _ _ (mul_ne_zero hne1 hne2)]

/-- **鏡像定理 A（北チャート）**: B_N(|−w,χ₁⟩, |−w,χ₂⟩) = √(p^K/|S_{w0}|)·conj(J̃)·|−(w+v), ψ⟩。 -/
theorem mirror_thmA (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    BN (kN K w (n + 1) hK χ₁) (kN K w (n + 1) hK χ₂)
      = ((Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) : ℝ) *
          starRingEnd ℂ (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
            (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))) : ℂ) •
        kN K (w + v) (n + 1 - v) (by omega) ψ := by
  have hprod' : ∀ x, (χ₁⁻¹ * χ₂⁻¹) x = ψ⁻¹ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x) := by
    intro x
    rw [← mul_inv, PAG.Part18.inv_pullback (χ₁ * χ₂) ψ _ hprod]
  have h := thmA_ket K w n v hv hK χ₁⁻¹ χ₂⁻¹ (PAG.Part16.isPrimitive_inv h₁) (PAG.Part16.isPrimitive_inv h₂)
    ψ⁻¹ (PAG.Part16.isPrimitive_inv hψ) hprod'
  rw [Jt_inv n v χ₁ χ₂ ψ hprod] at h
  rw [BN_eq, kN, kN, kN]
  show extN (PAG.Part15.conv (ket K w (n + 1) hK ((χ₁⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))
    (ket K w (n + 1) hK ((χ₂⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))) = _
  rw [h, extN_smul]

end Mirror

end PAG.Part23

#print axioms PAG.Part23.W_W
#print axioms PAG.Part23.inv_inv_of_unit
#print axioms PAG.Part23.compat_W
#print axioms PAG.Part23.compat_extS
#print axioms PAG.Part23.compat_extN
#print axioms PAG.Part23.W_extS
#print axioms PAG.Part23.extS_smul
#print axioms PAG.Part23.extN_smul
#print axioms PAG.Part23.BN_eq
#print axioms PAG.Part23.W_kS
#print axioms PAG.Part23.Jt_inv
#print axioms PAG.Part23.mirror_thmA
```

## §E Lean の形式文：PAG26.lean（全文）
```lean
/-
  PAG 2.0 Part 22（2026-10-18）— 点モデルと 2 チャートモデルの同値性
  点集合 Pt N := Z/N ⊔ {y : Z/N // y 非単数}（南の点 [x:1] と北の内部点 [1:y]）。
  1. 点の関数 f ↦ (F_S, F_N)（F_N(y) = f[y⁻¹:1]（y 単数）、f[1:y]（y 非単数））は
     貼り合わせ条件を満たす組の部分空間への線形同型
  2. 点の反転 Wpt（[x:1] ↔ [1:x]）は対合で、同型のもとで W（南北の入れ替え）に対応する
  3. |Pt (p^K)| = p^K + p^(K−1)（K ≥ 1）
-/
import PAG25

namespace PAG.Part26

open ZMod Finset PAG.Part23

open Classical

variable {N : ℕ}

/-- P¹(Z/N) の点: 南の点 [x:1]（inl x）と北の内部点 [1:y]（inr y、y 非単数）。 -/
abbrev Pt (N : ℕ) := ZMod N ⊕ {y : ZMod N // ¬ IsUnit y}

/-- 点の関数 → 2 チャートの組。 -/
noncomputable def toP1 (f : Pt N → ℂ) : P1F N :=
  (fun x => f (Sum.inl x), fun y => if h : IsUnit y then f (Sum.inl y⁻¹) else f (Sum.inr ⟨y, h⟩))

/-- 2 チャートの組 → 点の関数。 -/
def ofP1 (F : P1F N) : Pt N → ℂ
  | Sum.inl x => F.1 x
  | Sum.inr y => F.2 y.1

theorem compat_toP1 (f : Pt N → ℂ) : Compat (toP1 f) := fun y hy => by
  simp [toP1, hy]

theorem ofP1_toP1 (f : Pt N → ℂ) : ofP1 (toP1 f) = f := by
  funext z
  rcases z with x | ⟨y, hy⟩
  · rfl
  · simp [ofP1, toP1, hy]

theorem toP1_ofP1 {F : P1F N} (hF : Compat F) : toP1 (ofP1 F) = F := by
  ext y
  · rfl
  · simp only [toP1, ofP1]
    split_ifs with hy
    · exact (hF y hy).symm
    · rfl

/-- 貼り合わせ条件を満たす組の部分空間。 -/
def compatSub (N : ℕ) : Submodule ℂ (P1F N) where
  carrier := {F | Compat F}
  add_mem' := fun {F G} hF hG y hy => by
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, hF y hy, hG y hy]
  zero_mem' := fun y _ => rfl
  smul_mem' := fun a {F} hF y hy => by
    simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, hF y hy]

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

/-- 点の反転 [x:1] ↦ [1:x]。 -/
noncomputable def Wpt : Pt N → Pt N
  | Sum.inl x => if h : IsUnit x then Sum.inl x⁻¹ else Sum.inr ⟨x, h⟩
  | Sum.inr y => Sum.inl y.1

theorem Wpt_Wpt (z : Pt N) : Wpt (Wpt z) = z := by
  rcases z with x | ⟨y, hy⟩
  · by_cases h : IsUnit x
    · obtain ⟨hu, hii⟩ := inv_inv_of_unit h
      simp [Wpt, h, hu, hii]
    · simp [Wpt, h]
  · simp [Wpt, hy]

/-- Wpt は置換（対合）。 -/
noncomputable def WptEquiv (N : ℕ) : Equiv.Perm (Pt N) :=
  Function.Involutive.toPerm Wpt Wpt_Wpt

/-- **同型のもとで W は点の置換**: toP1 (f ∘ Wpt) = W (toP1 f)。 -/
theorem toP1_comp_Wpt (f : Pt N → ℂ) : toP1 (f ∘ Wpt) = W (toP1 f) := by
  ext y
  · simp only [toP1, W, Function.comp_apply, Wpt]
    split_ifs <;> rfl
  · simp only [toP1, W, Function.comp_apply]
    split_ifs with hy
    · obtain ⟨hu, hii⟩ := inv_inv_of_unit hy
      simp [Wpt, hu, hii]
    · simp [Wpt]

/-- ofP1 版: 貼り合わせ条件のもとで ofP1 (W F) = ofP1 F ∘ Wpt。 -/
theorem ofP1_W {F : P1F N} (hF : Compat F) : ofP1 (W F) = ofP1 F ∘ Wpt := by
  have h := toP1_comp_Wpt (ofP1 F)
  rw [toP1_ofP1 hF] at h
  rw [← h, ofP1_toP1]

/-- 単数の部分型と単数群の同値。 -/
noncomputable def isUnitEquiv (N : ℕ) : {x : ZMod N // IsUnit x} ≃ (ZMod N)ˣ where
  toFun x := x.2.unit
  invFun u := ⟨u, u.isUnit⟩
  left_inv x := by simp
  right_inv u := by ext; simp

variable {p : ℕ} [hp : Fact p.Prime]

/-- **点の数**: |Pt (p^K)| = p^K + p^(K−1)（K ≥ 1）。 -/
theorem card_Pt (K : ℕ) (hK : 1 ≤ K) : Fintype.card (Pt (p ^ K)) = p ^ K + p ^ (K - 1) := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [Fintype.card_sum, ZMod.card, Fintype.card_subtype_compl, ZMod.card,
    Fintype.card_congr (isUnitEquiv (p ^ K)), ZMod.card_units_eq_totient,
    Nat.totient_prime_pow hp.out (by omega)]
  congr 1
  have h1 : p ^ K = p ^ (K - 1) * p := by rw [← pow_succ]; congr 1; omega
  have h2 : 1 ≤ p := hp.out.one_lt.le
  rw [h1, Nat.mul_sub, mul_one, Nat.sub_sub_self (Nat.le_mul_of_pos_right _ (by omega))]

end PAG.Part26

#print axioms PAG.Part26.compat_toP1
#print axioms PAG.Part26.ofP1_toP1
#print axioms PAG.Part26.toP1_ofP1
#print axioms PAG.Part26.ptEquiv
#print axioms PAG.Part26.Wpt_Wpt
#print axioms PAG.Part26.WptEquiv
#print axioms PAG.Part26.toP1_comp_Wpt
#print axioms PAG.Part26.ofP1_W
#print axioms PAG.Part26.isUnitEquiv
#print axioms PAG.Part26.card_Pt
```

## §E Lean の形式文：PAG27.lean（全文）
```lean
/-
  PAG 2.0 Part 23（2026-10-18）— 射影直線 P¹(Z/p^K) の本来の定義と点モデルの同型
  P¹(Z/N) := {(a, b) 単模（∃ s t, sa + tb = 1）} / 単数倍。
  1. N = p^K（K ≥ 1）では 単模 ⇔ a または b が単数
  2. Pt(p^K) ≃ P¹(Z/p^K)（x ↦ [x:1]、y ↦ [1:y]）
  3. 反転 [a:b] ↦ [b:a] は well-defined で、同型のもとで Wpt に対応
  4. |P¹(Z/p^K)| = p^K + p^(K−1)
-/
import PAG26

namespace PAG.Part27

open ZMod PAG.Part23 PAG.Part26

open Classical

variable {N : ℕ}

/-- 単模ベクトル。 -/
def Unimod (N : ℕ) := {v : ZMod N × ZMod N // ∃ s t : ZMod N, s * v.1 + t * v.2 = 1}

/-- 単数倍の同値関係。 -/
def projSetoid (N : ℕ) : Setoid (Unimod N) where
  r v w := ∃ u : (ZMod N)ˣ, w.1.1 = u * v.1.1 ∧ w.1.2 = u * v.1.2
  iseqv := {
    refl := fun v => ⟨1, by simp, by simp⟩
    symm := fun {v w} ⟨u, h1, h2⟩ => ⟨u⁻¹, by rw [h1, ← mul_assoc, Units.inv_mul, one_mul],
      by rw [h2, ← mul_assoc, Units.inv_mul, one_mul]⟩
    trans := fun {v w z} ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩ => ⟨u' * u, by rw [h1', h1, Units.val_mul, mul_assoc],
      by rw [h2', h2, Units.val_mul, mul_assoc]⟩ }

/-- **射影直線** P¹(Z/N)。 -/
def ProjLine (N : ℕ) := Quotient (projSetoid N)

/-- 点 [a:b]。 -/
def mk (v : Unimod N) : ProjLine N := Quotient.mk (projSetoid N) v

theorem mk_eq_mk {v w : Unimod N} (u : (ZMod N)ˣ) (h1 : w.1.1 = u * v.1.1) (h2 : w.1.2 = u * v.1.2) :
    mk v = mk w := Quotient.sound ⟨u, h1, h2⟩

variable {p : ℕ} [hp : Fact p.Prime]

/-- **単模 ⇔ どちらかが単数**（N = p^K, K ≥ 1）。 -/
theorem unimod_iff {K : ℕ} (hK : 1 ≤ K) (a b : ZMod (p ^ K)) :
    (∃ s t : ZMod (p ^ K), s * a + t * b = 1) ↔ IsUnit a ∨ IsUnit b := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  constructor
  · rintro ⟨s, t, h⟩
    by_contra hn
    simp only [not_or] at hn
    rw [PAG.Part25.isUnit_iff_not_dvd hK, not_not] at hn
    rw [PAG.Part25.isUnit_iff_not_dvd hK, not_not] at hn
    have hd : p ∣ p ^ K := dvd_pow_self p (by omega)
    have e := congrArg (ZMod.castHom hd (ZMod p)) h
    rw [map_add, map_mul, map_mul, map_one, PAG.Part21.castHom_eq_natCast hd a,
      PAG.Part21.castHom_eq_natCast hd b, (ZMod.natCast_eq_zero_iff _ _).mpr hn.1,
      (ZMod.natCast_eq_zero_iff _ _).mpr hn.2, mul_zero, mul_zero, add_zero] at e
    exact zero_ne_one e
  · rintro (h | h)
    · exact ⟨a⁻¹, 0, by rw [ZMod.inv_mul_of_unit a h, zero_mul, add_zero]⟩
    · exact ⟨0, b⁻¹, by rw [ZMod.inv_mul_of_unit b h, zero_mul, zero_add]⟩

omit hp in
theorem isUnit_units_mul_iff (u : (ZMod N)ˣ) (x : ZMod N) : IsUnit ((u : ZMod N) * x) ↔ IsUnit x :=
  Units.isUnit_units_mul u x

omit hp in
/-- 単数 b について (u a)(u b)⁻¹ = a b⁻¹。 -/
theorem scale_div {u : (ZMod N)ˣ} {b : ZMod N} (hb : IsUnit b) (a : ZMod N) :
    (u * a) * ((u : ZMod N) * b)⁻¹ = a * b⁻¹ := by
  obtain ⟨ub, rfl⟩ := hb
  rw [← Units.val_mul, ZMod.inv_coe_unit, ZMod.inv_coe_unit, mul_inv, Units.val_mul,
    show (u : ZMod N) * a * (↑u⁻¹ * ↑ub⁻¹) = a * ↑ub⁻¹ * (↑u * ↑u⁻¹) by ring, Units.mul_inv, mul_one]

omit hp in
theorem nonunit_div {a b : ZMod N} (ha : IsUnit a) (hb : ¬ IsUnit b) : ¬ IsUnit (b * a⁻¹) := by
  intro h
  apply hb
  have : b = (b * a⁻¹) * a := by rw [mul_assoc, ZMod.inv_mul_of_unit a ha, mul_one]
  rw [this]
  exact h.mul ha

section Iso

variable (K : ℕ) (hK : 1 ≤ K)

/-- 点モデル → 射影直線: [x:1]、[1:y]。 -/
def toProj : Pt (p ^ K) → ProjLine (p ^ K)
  | Sum.inl x => mk ⟨(x, 1), 0, 1, by simp⟩
  | Sum.inr y => mk ⟨(1, y.1), 1, 0, by simp⟩

include hK in
theorem a_unit_of {v : Unimod (p ^ K)} (hb : ¬ IsUnit v.1.2) : IsUnit v.1.1 :=
  ((unimod_iff hK v.1.1 v.1.2).mp v.2).resolve_right hb

/-- 代表元での逆写像。 -/
noncomputable def ofRep (v : Unimod (p ^ K)) : Pt (p ^ K) :=
  if h : IsUnit v.1.2 then Sum.inl (v.1.1 * v.1.2⁻¹)
  else Sum.inr ⟨v.1.2 * v.1.1⁻¹, nonunit_div (a_unit_of K hK h) h⟩

include hK in
theorem ofRep_resp (v w : Unimod (p ^ K)) (hvw : (projSetoid (p ^ K)) v w) :
    ofRep K hK v = ofRep K hK w := by
  obtain ⟨u, h1, h2⟩ := hvw
  unfold ofRep
  by_cases hb : IsUnit v.1.2
  · have hb' : IsUnit w.1.2 := by rw [h2]; exact (isUnit_units_mul_iff u _).mpr hb
    simp only [hb, hb', ↓reduceDIte]
    rw [h1, h2, scale_div hb]
  · have hb' : ¬ IsUnit w.1.2 := by rw [h2, isUnit_units_mul_iff]; exact hb
    simp only [hb, hb', ↓reduceDIte]
    congr 2
    rw [h1, h2, scale_div (a_unit_of K hK hb)]

/-- 射影直線 → 点モデル。 -/
noncomputable def ofProj : ProjLine (p ^ K) → Pt (p ^ K) :=
  Quotient.lift (ofRep K hK) (ofRep_resp K hK)

theorem ofProj_toProj (z : Pt (p ^ K)) : ofProj K hK (toProj K z) = z := by
  rcases z with x | ⟨y, hy⟩
  · show ofRep K hK _ = _
    simp [ofRep]
  · show ofRep K hK _ = _
    simp [ofRep, hy]

theorem toProj_ofProj (q : ProjLine (p ^ K)) : toProj K (ofProj K hK q) = q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show toProj K (ofRep K hK v) = mk v
    unfold ofRep
    by_cases hb : IsUnit v.1.2
    · simp only [hb, ↓reduceDIte]
      obtain ⟨ub, hub⟩ := hb
      apply mk_eq_mk ub
      · show v.1.1 = ub * (v.1.1 * v.1.2⁻¹)
        rw [← hub, ZMod.inv_coe_unit, mul_left_comm, Units.mul_inv, mul_one]
      · show v.1.2 = ub * 1
        rw [mul_one, hub]
    · simp only [hb, ↓reduceDIte]
      obtain ⟨ua, hua⟩ := a_unit_of K hK hb
      apply mk_eq_mk ua
      · show v.1.1 = ua * 1
        rw [mul_one, hua]
      · show v.1.2 = ua * (v.1.2 * v.1.1⁻¹)
        rw [← hua, ZMod.inv_coe_unit, mul_left_comm, Units.mul_inv, mul_one]

/-- **点モデル ≃ 射影直線** Pt(p^K) ≃ P¹(Z/p^K)。 -/
noncomputable def projEquiv : Pt (p ^ K) ≃ ProjLine (p ^ K) where
  toFun := toProj K
  invFun := ofProj K hK
  left_inv := ofProj_toProj K hK
  right_inv := toProj_ofProj K hK

include hK in
/-- **点の数**: |P¹(Z/p^K)| = p^K + p^(K−1)。 -/
theorem card_ProjLine : Nat.card (ProjLine (p ^ K)) = p ^ K + p ^ (K - 1) := by
  rw [← Nat.card_congr (projEquiv K hK), Nat.card_eq_fintype_card, card_Pt K hK]

end Iso

/-! ## 反転 [a:b] ↦ [b:a] -/

omit hp in
theorem swap_unimod (v : Unimod N) : ∃ s t : ZMod N, s * v.1.2 + t * v.1.1 = 1 := by
  obtain ⟨s, t, h⟩ := v.2
  exact ⟨t, s, by rw [add_comm]; exact h⟩

/-- 反転 W[a:b] = [b:a]（well-defined）。 -/
def Wproj : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk ⟨(v.1.2, v.1.1), swap_unimod v⟩)
    (fun _v _w ⟨u, h1, h2⟩ => mk_eq_mk u h2 h1)

omit hp in
theorem Wproj_Wproj (q : ProjLine N) : Wproj (Wproj q) = q := by
  induction q using Quotient.inductionOn with
  | h v => rfl

/-- **同型のもとで W は Wpt**: toProj(Wpt z) = Wproj(toProj z)。 -/
theorem toProj_Wpt (K : ℕ) (z : Pt (p ^ K)) : toProj K (Wpt z) = Wproj (toProj K z) := by
  rcases z with x | ⟨y, hy⟩
  · by_cases hx : IsUnit x
    · simp only [Wpt, hx, ↓reduceDIte, toProj]
      obtain ⟨ux, rfl⟩ := hx
      apply mk_eq_mk ux
      · show (1 : ZMod (p ^ K)) = ux * (ux : ZMod (p ^ K))⁻¹
        rw [ZMod.inv_coe_unit, Units.mul_inv]
      · show (ux : ZMod (p ^ K)) = ux * 1
        rw [mul_one]
    · simp only [Wpt, hx, ↓reduceDIte, toProj]
      rfl
  · rfl

end PAG.Part27

#print axioms PAG.Part27.projSetoid
#print axioms PAG.Part27.mk_eq_mk
#print axioms PAG.Part27.unimod_iff
#print axioms PAG.Part27.scale_div
#print axioms PAG.Part27.nonunit_div
#print axioms PAG.Part27.ofRep_resp
#print axioms PAG.Part27.ofProj_toProj
#print axioms PAG.Part27.toProj_ofProj
#print axioms PAG.Part27.projEquiv
#print axioms PAG.Part27.card_ProjLine
#print axioms PAG.Part27.Wproj_Wproj
#print axioms PAG.Part27.toProj_Wpt
```

## §E Lean の形式文：PAG256.lean（全文）
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

