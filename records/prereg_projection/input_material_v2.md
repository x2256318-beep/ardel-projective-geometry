# 入力：「射影」の材料ノート（直した版）の再照合（2026-11-18）

## A. 照合するノート（直した版の全文）

# アーデル射影幾何 — 命名にある「射影」の材料（基礎文書の第 1・2 章のための対応表）

（2026-11-18。短期層の小さいノート。事前登録 `pag2_prereg_projection.md` の結論（残余は空、新しいパートは始めない）を受けて、基礎文書の起草（著者側）に渡す材料をまとめる。**ここに書く「射影」の読みは構築側の読みで、著者の確認待ちである。** 著者の定義（CLAUDE.md §1）の文面は変えない。第 1 版は独立照合を受け、その指摘で直した版がこれである（§7）。）

記号：反転（0 と ∞ の入れ替え、x ↦ 1/x）は **ι** と書く。Lean の宣言名 `W`・`Wpt`・`Wproj` とモノグラフの W は、この反転を指す。ルート数は **𝔀(χ)**（Lean の `PAG.Part256.rootNum`）と書き、反転と区別する。

## §1 著者の言葉（定義の層）

- 命名（2026-11-16）：「アーデル」はイーデル（乗法）とアデール（加法）を合わせた造語。「アーデル射影幾何」は、アデール幾何とイーデル幾何を射影によって融合する、という意味。
- 無限素点（2026-11-12・11-16）：無限大と無限小が重なり合う。−∞ と ∞ と 0 が射影によって重なる。この重なりを境界ユニタリ U によるねじれた貼り合わせと読む。
- 構築側の読み（2026-11-16 に著者確認）：ℝ_{>0} を対数で ℝ に移すと乗法の 0・∞ が加法の −∞・+∞ になり、射影直線では両端が一点になる。反転 x ↦ 1/x は 0 と ∞ を入れ替える。

## §2 「射影」の読み（構築側、著者の確認待ち）

命名の「射影による融合」を、次の 3 つの層の組として読む。

1. **舞台（座標）**：射影直線 P¹。2 つのチャート（0 の側 [x:1] と ∞ の側 [1:y]）が赤道（単数）の上で y ↦ y⁻¹ によってつながり、反転 ι が 0 と ∞ を入れ替える。
2. **作用素（融合）**：乗法の側の反転 ι と、加法の側のフーリエ変換を合成した作用素。乗法の関数（指標）に作用させる。
3. **位相（公準）**：原始指標 χ については、その作用素の成分が絶対値 1 の位相になる。公準 A1 は、境界ユニタリ U の原始指標の位相をこの値に選ぶ公準である。原始的でない指標では、成分は一般に位相ではない（絶対値が 1 未満になり、0 にもなる）。

注意 1（照合者の指摘）：1 と 2 は種類が違う。1 の y ↦ y⁻¹ はチャートの座標変換（関数を P¹ の上で定義するための恒等式）で、ねじれを持たない。ねじれ（指標ごとの位相）は 2 の作用素の側にある。Lean でも、2 の作用素（`PAG.Part256.JH`）と 1 の 2 チャートモデル（`PAG.Part23.Compat` など）を結ぶ文はない。

注意 2（照合者の指摘で直した）：2 の作用素の「加法のフーリエ変換」に何を使うかで、位相が変わる。
- 加法のフーリエ核 e(xy) そのものを使うと、原始指標 χ と単数 u での成分は τ(χ)/√N（ガウス和を √N で割ったもの）になる。Lean では `PAG.Part256.sum_mul_stdAddChar` と Mathlib の `gaussSum_mulShift_of_isPrimitive` から数行で出る（Lean の独立した定理としては置いていない。`hartley_eq_of_isPrimitive` の証明の中の式 `hA`）。
- Part 252 の離散 Hartley 変換（cas 核 cos + sin。核は ((1 − i)e(t) + (1 + i)e(−t))/2、`PAG.Part256.casKer_eq`）を使うと、成分は 𝔀(χ) = ε(χ)τ(χ)/√N になる。ε(χ) は偶で 1、奇で −i（`parFac`）。原始的なら 𝔀(χ) はルート数 τ(χ)/(i^a √N)（a は奇で 1、偶で 0）。
- 二つは偶の χ で一致し、奇の χ で i 倍ずれる。Tate の局所分解の通常の規約では、ルート数の i^a は無限素点の局所因子から来る（照合者の知識による。規約による符号の違いを含め、文献で未確認。確信度：中）。そうだとすると、有限素点の作用素の位相は τ(χ)/√N で、Part 252 の Hartley の形は無限素点の符号の因子を有限レベルの作用素に取り込んだ形と読める。基礎文書で使う前に文献で確かめる。

## §3 対応表

| 層 | 有限レベル（ℤ/N） | 無限素点 | ラベル |
|---|---|---|---|
| 舞台：射影直線と反転 | P¹(ℤ/N) := 単模ベクトル / 単数倍（Part 23、`PAG.Part27.ProjLine`）。反転 [a:b] ↦ [b:a]（`PAG.Part27.Wproj`、対合 `Wproj_Wproj`。一般の N）。p 素数、K ≥ 1 で、点モデル（Part 22、`PAG.Part26.Pt`）と同型（`PAG.Part27.projEquiv`）、点の数 p^K + p^(K−1)（`PAG.Part27.card_ProjLine`）、反転どうしが対応（`PAG.Part27.toProj_Wpt`）。2 チャートモデルと赤道での貼り合わせ F_N(y) = F_S(y⁻¹)（Part 19、`PAG.Part23.Compat`、反転 `PAG.Part23.W`。点モデルの関数との同型は `PAG.Part26.ptEquiv`、反転の対応は `PAG.Part26.toP1_comp_Wpt`）。**2 チャートモデルが P¹ のモデルになるのは N = p^K（K ≥ 1）のときだけ**（一般の N では点モデルと P¹ の点の数が違う。照合者の数え上げで N = 6 は 10 点と 12 点）。0 = [0:1] と ∞ = [1:0] は別の点で、反転がこの 2 点を入れ替える（有限の側に点の同一視はない） | P¹(ℝ)。ℝ_{>0} の対数座標 t = log x で、反転 x ↦ 1/x は t ↦ −t になり、両端 −∞・+∞（乗法の 0・∞）を入れ替える。射影直線では両端が一点（著者確認済みの読み）。有限の側との違い：無限素点では両端が重なる | ［既知］（P¹(ℤ/N) はモジュラー記号の標準の道具、Manin 1972 など。Lean は Part 19〜28） |
| 作用素：反転 ∘ 加法の変換 | J∘H_N/√N（Part 252、`PAG.Part256.JH`。J は単数の上の反転 u ↦ u⁻¹、H_N は離散 Hartley 変換）。ℤ/N の関数を単数の上の関数に送る写像で、同じ空間の上の作用素ではない。素朴なフーリエ核での形は §2 の注意 2 | モノグラフ層の境界ユニタリ U（イデール類群の上の反転と、境界条件）。Lean にしていない | ［再導出］（Part 252 の冒頭の記載どおり「既知の事実の書き直し」。Tate 1950 の局所関数等式の有限版と読む） |
| 位相：原始指標の成分 | すべての指標 χ と単数 u で (J H_N χ)(u)/√N = 𝔀(χ)·χ(u)（`PAG.Part256.JH_eq_rootNum_mul_any`）。原始的なら \|𝔀(χ)\| = 1（`PAG.Part256.normSq_rootNum`）。原始的なら 𝔀(χ) がルート数であることは Lean の外（`rootNum` の docstring）。原始的でない指標では位相でない（法 2 の自明な指標で \|𝔀\|² = 1/2、法 4 の自明な指標で 0：`removal_counterexample_normSq`・`removal_counterexample_four`） | Tate の γ 因子（ガンマ因子の比）。公準 A1 は U の位相をこの値（λ = 0 での値）に選ぶ。両立の分類は定理 2.6 | ［既知］（Tate 1950、Burnol 1998〜2001）。A1 は公準のまま |

## §4 Lean にしていないこと・確かめていないこと

- P¹ と点モデルの同型は N = p^K（K ≥ 1）だけ。一般の N では、`ProjLine` の定義と反転（`Wproj`・`Wproj_Wproj`・`mk_eq_mk`）が示されているが、点モデル `Pt N` は P¹(ℤ/N) と一致しない。全素点の制限積 P¹(𝔸_ℚ) = ∏'_v P¹(ℚ_v) と、P¹(ℤ_p) = lim P¹(ℤ/p^K) は Lean にしていない。
- 境界ユニタリ U と公準 A1 は、どの素点の側でも Lean の文に出てこない（Part 252 の冒頭）。Tate の局所関数等式そのもの、定理 2.6 も Lean にしていない（定理 2.6 の条件を A1 の位相が満たすことは PAG16・PAG173・PAG198 の 3 定理から出る、と CLAUDE.md §3 に記録あり。組み合わせた 1 つの文は未形式化）。
- 「射影 = 舞台の P¹ と、反転 ∘ 加法の変換」は読みであり、Lean の文ではない。Part 252 の J∘H_N を「作用素の層の有限版」と呼ぶのも読みである。Part 252 の docstring の言葉では、`JH_eq_rootNum_mul` は「構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。U と A1 は文に出てこない）」、冒頭の読みは「公理 A1 の境界ユニタリの原始指標の部分」で、「貼り合わせ」という語は Lean の側にはない。
- `JH` と 2 チャートモデル（`PAG.Part23.P1F`・`Compat`・`W`）・`ProjLine` を結ぶ Lean の文はない。§2 の 2 の作用素が「0 の側と ∞ の側をつなぐ」に対応する Lean の文はない。
- ルート数の i^a の帰属（§2 の注意 2）は文献で未確認。
- 盲検の問いテストで、全素点を通して「各素点の 0 と ∞ の貼り合わせ」を一つの構成として書いた文献は見つからなかった（MathSciNet・zbMATH は未照合）。部品はすべて既知。

## §5 対照群（§7）

- 関数体 𝔽_q(t) でも Tate の局所関数等式は同じ形で成り立つ。したがって §2 の 2・3 は ℚ に固有の算術を使わない形式の文である。
- 関数体では、t ↦ 1/t が素点 0 と素点 ∞ を入れ替える。ただしこの P¹_{𝔽_q} は「点が素点であるような大域の曲線」で、§2 の 1 の「各素点の座標の直線」とは別の対象である（照合者の指摘）。
- ℚ に固有に残るのは、無限素点がアルキメデス的で、実数の順序（符号）と二つの端 ±∞ があることである（「−∞ と ∞」の重なり）。§2 の注意 2 の読みが正しければ、符号の因子 i^a もこの無限素点の側に属する。

## §6 著者に判断を仰ぐこと

1. §2 の読み（舞台としての P¹、反転と加法の変換の合成による作用素、原始指標の位相としての局所因子）を、基礎文書の第 1・2 章の定義の材料として採るか。
2. 採る場合、命名の「射影」が指すのは、舞台の P¹（射影直線）か、作用素か、その両方か。
3. 有限素点の作用素に、素朴なフーリエ核（位相 τ(χ)/√N）と Part 252 の Hartley 核（位相はルート数、無限素点の符号を含む）のどちらを置くか。文献での確認（§2 の注意 2）を先に行うか。
4. 決まったことは、補足 7 の規則に従い著者側の記録（CLAUDE.md §1・§2 と申し送り）に戻す。

## §7 照合の記録

- 第 1 版（`before_material_v1.md`）を、形式文の全文（PAG23・PAG26・PAG27・PAG256）を渡した新しい照合者が照らした（依頼文 `outputs/material_check_request.md`、出力 `outputs/material_check_output.md`、所要 約 6 分）。
- 主な指摘と直し：原始性の限定の抜け（§2 の 3、表 3 行目）、素朴なフーリエ核とHartley 核の取り違え（§2 の注意 2 を新設）、`JH_eq_rootNum_mul` を「ルート数」の根拠にした当て方（外した）、番号と名前空間の取り違えの罠（完全修飾名にした）、K ≥ 1 の抜け、2 チャートモデルが P¹ になる範囲、一般の N の `ProjLine` の記述、docstring の引用の但し書き、`JH` と 2 チャートモデルを結ぶ文がないこと、「無限素点の U」の書き方、記号 W の衝突（ι と 𝔀 に分けた）、有限と無限の対応のずれ、表 2 行目のラベル（［再導出］にそろえた）。
- 直した後の照合：§8 に記録する。


## A2. 第 1 版からの差分（< 第 1 版、> 直した版）

```diff
3c3,5
< （2026-11-18。短期層の小さいノート。事前登録 `pag2_prereg_projection.md` の結論（残余は空、新しいパートは始めない）を受けて、基礎文書の起草（著者側）に渡す材料をまとめる。**ここに書く「射影」の読みは構築側の読みで、著者の確認待ちである。** 著者の定義（CLAUDE.md §1）の文面は変えない。）
---
> （2026-11-18。短期層の小さいノート。事前登録 `pag2_prereg_projection.md` の結論（残余は空、新しいパートは始めない）を受けて、基礎文書の起草（著者側）に渡す材料をまとめる。**ここに書く「射影」の読みは構築側の読みで、著者の確認待ちである。** 著者の定義（CLAUDE.md §1）の文面は変えない。第 1 版は独立照合を受け、その指摘で直した版がこれである（§7）。）
> 
> 記号：反転（0 と ∞ の入れ替え、x ↦ 1/x）は **ι** と書く。Lean の宣言名 `W`・`Wpt`・`Wproj` とモノグラフの W は、この反転を指す。ルート数は **𝔀(χ)**（Lean の `PAG.Part256.rootNum`）と書き、反転と区別する。
15,19c17,26
< 1. **舞台（座標）**：各素点の射影直線 P¹。2 つのチャート（0 の側 [x:1] と ∞ の側 [1:y]）が赤道（単数）の上で y ↦ y⁻¹ によってつながり、反転 W が 0 と ∞ を入れ替える。
< 2. **貼り合わせ（作用素）**：0 の側と ∞ の側をつなぐ作用素を、**反転（乗法の側、イーデル）と加法のフーリエ変換（アデールの側）の合成**として与える。これが「融合」の中身にあたる。
< 3. **位相（公準）**：その合成作用素の、乗法的な指標ごとの成分は位相（局所因子）になる。有限素点ではガウス和から作るルート数、無限素点ではガンマ因子の比（Tate の局所関数等式）。公準 A1 は、境界ユニタリ U の位相をこの値に選ぶ公準である。
< 
< 照合者（盲検の問いテスト）の指摘により、1 と 2 は種類が違うことに注意する。1 の y ↦ y⁻¹ はチャートの座標変換（関数を P¹ の上で定義するための恒等式）で、ねじれを持たない。ねじれ（指標ごとの位相）は 2 の作用素の側にある。
---
> 1. **舞台（座標）**：射影直線 P¹。2 つのチャート（0 の側 [x:1] と ∞ の側 [1:y]）が赤道（単数）の上で y ↦ y⁻¹ によってつながり、反転 ι が 0 と ∞ を入れ替える。
> 2. **作用素（融合）**：乗法の側の反転 ι と、加法の側のフーリエ変換を合成した作用素。乗法の関数（指標）に作用させる。
> 3. **位相（公準）**：原始指標 χ については、その作用素の成分が絶対値 1 の位相になる。公準 A1 は、境界ユニタリ U の原始指標の位相をこの値に選ぶ公準である。原始的でない指標では、成分は一般に位相ではない（絶対値が 1 未満になり、0 にもなる）。
> 
> 注意 1（照合者の指摘）：1 と 2 は種類が違う。1 の y ↦ y⁻¹ はチャートの座標変換（関数を P¹ の上で定義するための恒等式）で、ねじれを持たない。ねじれ（指標ごとの位相）は 2 の作用素の側にある。Lean でも、2 の作用素（`PAG.Part256.JH`）と 1 の 2 チャートモデル（`PAG.Part23.Compat` など）を結ぶ文はない。
> 
> 注意 2（照合者の指摘で直した）：2 の作用素の「加法のフーリエ変換」に何を使うかで、位相が変わる。
> - 加法のフーリエ核 e(xy) そのものを使うと、原始指標 χ と単数 u での成分は τ(χ)/√N（ガウス和を √N で割ったもの）になる。Lean では `PAG.Part256.sum_mul_stdAddChar` と Mathlib の `gaussSum_mulShift_of_isPrimitive` から数行で出る（Lean の独立した定理としては置いていない。`hartley_eq_of_isPrimitive` の証明の中の式 `hA`）。
> - Part 252 の離散 Hartley 変換（cas 核 cos + sin。核は ((1 − i)e(t) + (1 + i)e(−t))/2、`PAG.Part256.casKer_eq`）を使うと、成分は 𝔀(χ) = ε(χ)τ(χ)/√N になる。ε(χ) は偶で 1、奇で −i（`parFac`）。原始的なら 𝔀(χ) はルート数 τ(χ)/(i^a √N)（a は奇で 1、偶で 0）。
> - 二つは偶の χ で一致し、奇の χ で i 倍ずれる。Tate の局所分解の通常の規約では、ルート数の i^a は無限素点の局所因子から来る（照合者の知識による。規約による符号の違いを含め、文献で未確認。確信度：中）。そうだとすると、有限素点の作用素の位相は τ(χ)/√N で、Part 252 の Hartley の形は無限素点の符号の因子を有限レベルの作用素に取り込んだ形と読める。基礎文書で使う前に文献で確かめる。
23c30
< | 層 | 有限素点（有限レベル ℤ/N） | 無限素点 | ラベル |
---
> | 層 | 有限レベル（ℤ/N） | 無限素点 | ラベル |
25,27c32,34
< | 舞台：射影直線と反転 | P¹(ℤ/N) := 単模ベクトル / 単数倍（Part 23、PAG27 の `ProjLine`）。反転 [a:b] ↦ [b:a]（`Wproj`）。N = p^K では点モデルと同型（`projEquiv`）、点の数は p^K + p^(K−1)（`card_ProjLine`）。2 チャートモデルと赤道での貼り合わせ F_N(y) = F_S(y⁻¹)（Part 19、PAG23 の `Compat`、反転 `W`） | P¹(ℝ)。ℝ_{>0} の対数座標 t = log x で、反転 x ↦ 1/x は t ↦ −t になり、両端 −∞・+∞（乗法の 0・∞）を入れ替える。射影直線では両端が一点（著者確認済みの読み） | ［既知］（P¹(ℤ/N) はモジュラー記号の標準の道具、Manin 1972 など。Lean は Part 19〜28） |
< | 貼り合わせ：反転 ∘ 加法のフーリエ | J∘H_N/√N（Part 252、PAG256 の `JH`。J は単数の上の反転 u ↦ u⁻¹、H_N は離散 Hartley 変換＝加法のフーリエ変換の実形） | モノグラフ層の境界ユニタリ U（イデール類群の上の反転 W と、境界条件）。Lean にしていない | ［既知］（Tate 1950 の局所関数等式の有限版。Hartley の形は書き直し） |
< | 位相：指標ごとの成分 | すべての指標 χ と単数 u で (J H_N χ)(u)/√N = W(χ)·χ(u)、W(χ) = rootNum χ（`JH_eq_rootNum_mul_any`）。原始的なら W(χ) はルート数で \|W(χ)\| = 1（`JH_eq_rootNum_mul`・`normSq_rootNum`） | Tate の γ 因子（ガンマ因子の比）。公準 A1 は U の位相をこの値（λ = 0 での値）に選ぶ。両立の分類は定理 2.6 | ［既知］（Tate 1950、Burnol 1998〜2001）。A1 は公準のまま |
---
> | 舞台：射影直線と反転 | P¹(ℤ/N) := 単模ベクトル / 単数倍（Part 23、`PAG.Part27.ProjLine`）。反転 [a:b] ↦ [b:a]（`PAG.Part27.Wproj`、対合 `Wproj_Wproj`。一般の N）。p 素数、K ≥ 1 で、点モデル（Part 22、`PAG.Part26.Pt`）と同型（`PAG.Part27.projEquiv`）、点の数 p^K + p^(K−1)（`PAG.Part27.card_ProjLine`）、反転どうしが対応（`PAG.Part27.toProj_Wpt`）。2 チャートモデルと赤道での貼り合わせ F_N(y) = F_S(y⁻¹)（Part 19、`PAG.Part23.Compat`、反転 `PAG.Part23.W`。点モデルの関数との同型は `PAG.Part26.ptEquiv`、反転の対応は `PAG.Part26.toP1_comp_Wpt`）。**2 チャートモデルが P¹ のモデルになるのは N = p^K（K ≥ 1）のときだけ**（一般の N では点モデルと P¹ の点の数が違う。照合者の数え上げで N = 6 は 10 点と 12 点）。0 = [0:1] と ∞ = [1:0] は別の点で、反転がこの 2 点を入れ替える（有限の側に点の同一視はない） | P¹(ℝ)。ℝ_{>0} の対数座標 t = log x で、反転 x ↦ 1/x は t ↦ −t になり、両端 −∞・+∞（乗法の 0・∞）を入れ替える。射影直線では両端が一点（著者確認済みの読み）。有限の側との違い：無限素点では両端が重なる | ［既知］（P¹(ℤ/N) はモジュラー記号の標準の道具、Manin 1972 など。Lean は Part 19〜28） |
> | 作用素：反転 ∘ 加法の変換 | J∘H_N/√N（Part 252、`PAG.Part256.JH`。J は単数の上の反転 u ↦ u⁻¹、H_N は離散 Hartley 変換）。ℤ/N の関数を単数の上の関数に送る写像で、同じ空間の上の作用素ではない。素朴なフーリエ核での形は §2 の注意 2 | モノグラフ層の境界ユニタリ U（イデール類群の上の反転と、境界条件）。Lean にしていない | ［再導出］（Part 252 の冒頭の記載どおり「既知の事実の書き直し」。Tate 1950 の局所関数等式の有限版と読む） |
> | 位相：原始指標の成分 | すべての指標 χ と単数 u で (J H_N χ)(u)/√N = 𝔀(χ)·χ(u)（`PAG.Part256.JH_eq_rootNum_mul_any`）。原始的なら \|𝔀(χ)\| = 1（`PAG.Part256.normSq_rootNum`）。原始的なら 𝔀(χ) がルート数であることは Lean の外（`rootNum` の docstring）。原始的でない指標では位相でない（法 2 の自明な指標で \|𝔀\|² = 1/2、法 4 の自明な指標で 0：`removal_counterexample_normSq`・`removal_counterexample_four`） | Tate の γ 因子（ガンマ因子の比）。公準 A1 は U の位相をこの値（λ = 0 での値）に選ぶ。両立の分類は定理 2.6 | ［既知］（Tate 1950、Burnol 1998〜2001）。A1 は公準のまま |
31,33c38,42
< - P¹ と点モデルの同型は N = p^K だけ（一般の N の `ProjLine` は定義だけ）。全素点の制限積 P¹(𝔸_ℚ) = ∏'_v P¹(ℚ_v) は Lean にしていない。
< - 無限素点の U、Tate の局所関数等式そのもの、定理 2.6 は Lean にしていない（定理 2.6 の条件を A1 の位相が満たすことは PAG16・PAG173・PAG198 の 3 定理から出る、と CLAUDE.md §3 に記録あり。組み合わせた 1 つの文は未形式化）。
< - 「射影 = 反転 ∘ 加法のフーリエ」は読みであり、Lean の文ではない。Part 252 の J∘H_N を「有限素点の貼り合わせ」と呼ぶのも読みである（Part 252 の docstring も「モノグラフ §1.3 の主張 (2) の原始指標の部分と読む」としている）。
---
> - P¹ と点モデルの同型は N = p^K（K ≥ 1）だけ。一般の N では、`ProjLine` の定義と反転（`Wproj`・`Wproj_Wproj`・`mk_eq_mk`）が示されているが、点モデル `Pt N` は P¹(ℤ/N) と一致しない。全素点の制限積 P¹(𝔸_ℚ) = ∏'_v P¹(ℚ_v) と、P¹(ℤ_p) = lim P¹(ℤ/p^K) は Lean にしていない。
> - 境界ユニタリ U と公準 A1 は、どの素点の側でも Lean の文に出てこない（Part 252 の冒頭）。Tate の局所関数等式そのもの、定理 2.6 も Lean にしていない（定理 2.6 の条件を A1 の位相が満たすことは PAG16・PAG173・PAG198 の 3 定理から出る、と CLAUDE.md §3 に記録あり。組み合わせた 1 つの文は未形式化）。
> - 「射影 = 舞台の P¹ と、反転 ∘ 加法の変換」は読みであり、Lean の文ではない。Part 252 の J∘H_N を「作用素の層の有限版」と呼ぶのも読みである。Part 252 の docstring の言葉では、`JH_eq_rootNum_mul` は「構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。U と A1 は文に出てこない）」、冒頭の読みは「公理 A1 の境界ユニタリの原始指標の部分」で、「貼り合わせ」という語は Lean の側にはない。
> - `JH` と 2 チャートモデル（`PAG.Part23.P1F`・`Compat`・`W`）・`ProjLine` を結ぶ Lean の文はない。§2 の 2 の作用素が「0 の側と ∞ の側をつなぐ」に対応する Lean の文はない。
> - ルート数の i^a の帰属（§2 の注意 2）は文献で未確認。
38,39c47,49
< - 関数体 𝔽_q(t) でも Tate の局所関数等式は同じ形で成り立ち、無限素点は P¹_{𝔽_q} の点 ∞ そのもので、t ↦ 1/t が素点 0 と ∞ を入れ替える。したがって §2 の 1〜3 は ℚ に固有の算術を使わない形式の文である。
< - ℚ に固有に残るのは、無限素点がアルキメデス的で、実数の順序（符号）と二つの端 ±∞ があることだけである（「−∞ と ∞」の重なり）。関数体の無限素点では付値が離散で、この部分は言えない。
---
> - 関数体 𝔽_q(t) でも Tate の局所関数等式は同じ形で成り立つ。したがって §2 の 2・3 は ℚ に固有の算術を使わない形式の文である。
> - 関数体では、t ↦ 1/t が素点 0 と素点 ∞ を入れ替える。ただしこの P¹_{𝔽_q} は「点が素点であるような大域の曲線」で、§2 の 1 の「各素点の座標の直線」とは別の対象である（照合者の指摘）。
> - ℚ に固有に残るのは、無限素点がアルキメデス的で、実数の順序（符号）と二つの端 ±∞ があることである（「−∞ と ∞」の重なり）。§2 の注意 2 の読みが正しければ、符号の因子 i^a もこの無限素点の側に属する。
43,45c53,62
< 1. §2 の読み（射影 = 舞台としての P¹ と、反転 ∘ 加法のフーリエによる貼り合わせ、位相としての局所因子）を、基礎文書の第 1・2 章の定義の材料として採るか。
< 2. 採る場合、命名の「射影」が指すのは、舞台の P¹（射影直線）か、貼り合わせの作用素か、その両方か。
< 3. 決まったことは、補足 7 の規則に従い著者側の記録（CLAUDE.md §1・§2 と申し送り）に戻す。
---
> 1. §2 の読み（舞台としての P¹、反転と加法の変換の合成による作用素、原始指標の位相としての局所因子）を、基礎文書の第 1・2 章の定義の材料として採るか。
> 2. 採る場合、命名の「射影」が指すのは、舞台の P¹（射影直線）か、作用素か、その両方か。
> 3. 有限素点の作用素に、素朴なフーリエ核（位相 τ(χ)/√N）と Part 252 の Hartley 核（位相はルート数、無限素点の符号を含む）のどちらを置くか。文献での確認（§2 の注意 2）を先に行うか。
> 4. 決まったことは、補足 7 の規則に従い著者側の記録（CLAUDE.md §1・§2 と申し送り）に戻す。
> 
> ## §7 照合の記録
> 
> - 第 1 版（`before_material_v1.md`）を、形式文の全文（PAG23・PAG26・PAG27・PAG256）を渡した新しい照合者が照らした（依頼文 `outputs/material_check_request.md`、出力 `outputs/material_check_output.md`、所要 約 6 分）。
> - 主な指摘と直し：原始性の限定の抜け（§2 の 3、表 3 行目）、素朴なフーリエ核とHartley 核の取り違え（§2 の注意 2 を新設）、`JH_eq_rootNum_mul` を「ルート数」の根拠にした当て方（外した）、番号と名前空間の取り違えの罠（完全修飾名にした）、K ≥ 1 の抜け、2 チャートモデルが P¹ になる範囲、一般の N の `ProjLine` の記述、docstring の引用の但し書き、`JH` と 2 チャートモデルを結ぶ文がないこと、「無限素点の U」の書き方、記号 W の衝突（ι と 𝔀 に分けた）、有限と無限の対応のずれ、表 2 行目のラベル（［再導出］にそろえた）。
> - 直した後の照合：§8 に記録する。

```


## B. PAG23.lean の全文

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


```


## B. PAG26.lean の全文

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


```


## B. PAG27.lean の全文

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


```


## B. PAG256.lean の全文

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


```
