# アーデル射影幾何 — 方向 γ の文献照合（構築側で開ける範囲）

（2026-11-19。短期層の小さいノート。新しいパートではない。出所：骨格の第 6 章「Bost–Connes との接続（関数のレベルでは既知。T(0) の側に届くかは方向 γ の文献照合の結果による）」と、CLAUDE.md §2 の「γ の文献照合は著者側の作業に切り分けた」。候補 3 の照合（`pag2_candidate3_literature_builder.md`）に続き、構築側の環境から開ける部分だけを行う。MathSciNet・zbMATH は著者側に残す。）

## §0 問いと内部照合

- **方向 γ の問い**（Part 258 のノート §4 の言葉）：帰納系が T(0) の側に届く記述が文献にあるか。
  - 有限レベルの Bost–Connes 系と、円分スキームの Terwilliger 代数 T(0) を結ぶ記述があるか。
  - T(0) は、殻の指示関数の掛け算 D_s（双対の側）と、周波数殻への射影 E_s（Bose–Mesner の側）が生成する。
- **内部照合**：鎖と記録を「方向γ」「Bost–Connes」で検索した。
  - 方向 γ は登録（2026-11-14）で「Lean にせず並行の調査」とされ、試していなかった（`pag2_beta_registration_check.md`）。
  - これまでの照合は、2026-11-14 の盲検の問いテストの検索 1 本（「Bost-Connes system finite level Z/N association scheme Terwilliger algebra」）だけで、「Bost–Connes 系の有限レベルと Terwilliger 代数を結びつける文献は見つからなかった」と申告されていた（`records/prereg258/outputs/blind_output.md`）。
  - 棚卸し監査（2026-11-12、`pag2_audit_after_part251.md` の R9）は、「有限レベルの Bost–Connes」を既知（確信度：高）と判定していた。対象は関数のレベルで、T(0) の側は問うていない。

## §1 照合した範囲と結果

検索は 5 回。主な語：「Bost-Connes」「Terwilliger algebra」、Bost–Connes と association scheme・Schur ring・Ramanujan sums、BC のエンドモチーフ、BC 代数の有限近似。

1. **Bost–Connes と Terwilliger 代数を並べた検索**（「"Bost-Connes" "Terwilliger algebra"」）：結果はすべて Terwilliger 代数だけの文献で、Bost–Connes に触れるものは出なかった。
2. **Bost–Connes の有限レベルの標準の形**（関数のレベル。既知の側）：
   - BC 代数は、群環 C*(ℚ/ℤ) を乗法半群 ℕ^× の自己準同型の作用で割った半群の交差積である（Laca–Raeburn ほか）。
   - エンドモチーフは、有限次元の群環 ℚ[ℤ/nℤ] の帰納系と、その極限 ℚ[ℚ/ℤ] に ℕ^× を作用させた交差積である（Connes–Consani–Marcolli）。
   - BC 代数は、有限個の素数の部分の直極限として書ける（Laca 系の論文）。
   - 素数の有限集合 F に分けた部分代数（F の部分・F と互いに素な部分）もある（arXiv:1901.00020）。
   - これらの有限レベルは、どれも群環（畳み込みの側。単数で不変な部分が Bose–Mesner 代数）の帰納系で、殻の指示関数の掛け算 D_s（双対 Bose–Mesner の側）を含む T(0) を扱う記述は見つからなかった。
3. **Schur 環・アソシエーションスキームと Bost–Connes を結ぶ検索**：結び付ける文献は出なかった。
   - 近いものとして、無限群の上の Schur 環（arXiv:1806.07010。捩れのない局所巡回群の分類で、ℚ/ℤ は対象外）がある。
   - 円分スキームの融合スキームについての文献（Feng–Momihara、arXiv:1211.2864）もあるが、どちらも Bost–Connes とは無関係。

## §2 結論

- 照合した範囲で、有限レベルの Bost–Connes 系と円分スキームの Terwilliger 代数 T(0) を結ぶ記述は見つからなかった。範囲は、検索 5 回と結果の要旨。盲検（2026-11-14）の申告と一致する。
- 帰納系が T(0) の側に届く記述も見つからなかった。「見つからなかった」は不存在の証明ではない。本文を開いて確かめた文献はない（要旨と検索結果の範囲）。確信度：低〜中。
- 既知の側との切り分け：関数のレベル（群環 ℚ[ℤ/nℤ] の帰納系、その単数で不変な部分＝Bose–Mesner 代数の側）は、BC のエンドモチーフとして既知。骨格の「関数のレベルでは既知」と合う。
- ［観察］（構築側。Lean の外の比較で、文献の主張ではない）：
  - BC の群環の帰納系は、整除の順序のすべての段 n ∣ m を使う。
  - 一方、殻代数 A_N（= T(0)）の側では、引き戻しと両立し殻を混ぜない単位的な写像があるのは互いに素な段だけで（Part 258（PAG262）の `PAG.Part262.exists_compatible_hom_iff`。殻を混ぜない条件は強い読み、2026-11-19 に著者が確定）、添字の順序は有向でない（Part 259（PAG263）の `PAG.Part263.not_isDirected_udvd`）。
  - したがって、BC の帰納系をそのまま T(0) の側に持ち上げる形は、この条件のもとでは取れない。γ の問いは、この食い違いを踏まえて「どの条件のもとで、何が T(0) の側に届くか」と立て直す余地がある。
- 方向 γ は開いたまま。MathSciNet・zbMATH は著者側の作業として残る。（後注 2026-11-26 14:25、著者側（Muse）が zbMATH の公開 API で §3 の検索式を実行した結果による。構築側は zbMATH を開けていない。詳細は `pag2_literature_zbmath_20261126.md` §6。zbMATH は "Bost-Connes" & ("association scheme" | Terwilliger | "Schur ring") で 0 件（"Bost-Connes" 単独では 57 件）。残るのは MathSciNet。）

## §3 記録

- 検索 5 回（WebSearch）。WebFetch はしていない（本文は開いていない）。
- 独立照合にはかけていない。このノートは文献の範囲の記録と構築側の観察で、新規性の主張を足していない。
