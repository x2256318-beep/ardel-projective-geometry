# 統合照合 XV の入力：台帳 L41・L42・L43（2026-11-28）

入力の並び：§1 台帳の 3 項目の全文、§2 L41 の差分と XIV の出力、§3 L42 の差分と照合の記録、§4 L43 の差分（CLAUDE.md・引き継ぎメモ・台帳）、§5 玩具のノートの全文、§6 玩具の盲検の出力（段 6〜9、全文）と数値のログ（段 5〜9）。

## §1 台帳の 3 項目

### L41：統合照合 XIV の後の直し（2026-11-26 21:0x）

- 範囲：XIV（`records/ledger_XIV/outputs/integrated_XIV_output.md`）の指摘を受けた直し。
  - 射影のノート：C3 の留保を「N によらず射影した δ_x は正規直交でない（素数でも自明指標は原始的でない。N = 13 でグラム行列は対角 11/12・非対角 −1/12）。Maassen–Uffink はそのままは当てはまらず、log m 以上は N = 13・21 の数値での観察」に直した（低 a。構築側が N = 13 で数値を確かめた）。T2 の補足の「内容は薄い」を「内容がない（盲検の P2 の文言）」に（極低 f）。C1 の 2 つの値にログの行を添えた（極低 n。構築側がログで確かめた：1.2×10⁻¹⁴ は ‖U − Π(JH/√N)Π‖ の N = 13、2.5×10⁻¹⁴ は ‖U*U − Π‖ の N = 11）。
  - 重ね合わせのノート：§5 の盲検の補足の「Q2 はこの条件以外の算術を使っていない」に、稠密さについての文である旨の後注（低 b）。§0 に直す前の文を括弧で残した（極低 k）。§8 の単純さの文に模型の注（極低 m）。
  - 零点のノート：§3a の「素数の対数の稠密性」を「正の有理数の対数の集合（素数の対数が生成する群）の稠密性」に（極低 g）。R3 の記号の注の範囲を §2・§3・§4・§7 に（極低 h）。
  - 索引：§6 の叩き台の後注に XIII 極低 18 の 2 点と、置き場所・並べ替えない理由の後注（極低 e・i）。§6 に「著者に確かめる事項 3 件」の後注（低 c・d：叩き台 rev 119 の印、CLAUDE.md §3 の候補 1 の明記、草稿 5.1 の句が著者の文面か）。3.1 の後注を著者の文面の行から別の行に分けた（極低 l）。
  - この台帳と引き継ぎメモ。`records/ledger_XIV/`（入力・依頼文・出力・meta）。
- L40 の記載の漏れ（XIV の極低 j・l。閉じた記録は書き換えず、ここに書く）：
  - L40 の「閉じた記録の範囲の漏れ」の L35 は、D2 の入力・依頼文（コミット 14e5b93。L34 の範囲に記録済み）と出力・meta（a6cc4c2）の両方を指すべきだった。
  - L37〜L39 を閉じた項目の「この項目への指摘」に、XIII の極低 14（引き継ぎメモの行の漏れ）を書いていなかった。
  - 低 4 の「著者の原文との照合を著者側の作業に挙げない理由」（CLAUDE.md は著者の記録、補足 7。CLAUDE.md §2 の記載による）は、索引 3.1 の後注にだけ書いていた。
  - 極低 23 の理由（「後注は足した順に並べる決まり」）は記録に出所がなかった。理由は「並べ替えは記録の書き換えに当たるので避ける」と改める（索引 §6 の後注）。
- 直していないもの：XIV の低 c の前半（草稿 5.1 の句を直すこと）は、著者に確かめる事項 (3) にした。著者の文面かどうかが決まるまで草稿は変えない。
- 自己申告（根拠にしない）：低 a は留保の範囲を広げる直し（主張を狭める側）。ほかは留保・帰属・記録の書き足し。
- 追記（2026-11-26 21:11、著者の回答 3 件を受けて）：叩き台を rev 119 → rev 120（5.1 に 16:38 の決定で置き換わった印。表とチェックリストの 4 行は「MathSciNet は 16:0x の決定でやめた」だけで 16:38 の後も有効なので入れていない）。CLAUDE.md §3 の候補 1 に「外部での新規性の留保は付けない（2026-11-26 15:5x の著者の決定。21:11 の著者の指示で明記した）」、英語版にも同じ文。索引 §6 に回答の後注。草稿 5.1 の句は著者の文面と確認されたので変えない（XIII の低 3、XIV の低 c はこれで閉じた）。引き継ぎメモに 1 行。照合は受けていない。
- 扱い：XIV は停止規則の「もう 1 回だけ」の照合で、最後の指摘が低・極低だけなので、L40 を閉じ、L41 は次のパートの統合照合に載せる。


### L42：短縮版 CLAUDE.md の統合照合の後の直し（2026-11-27 07:1x）

- 範囲：短縮版の網羅性の統合照合（`records/claude_md_slim_check/output_recheck.md`）の指摘を受けた CLAUDE.md・CLAUDE.en.md の直し（M1〜M6、L3、L6、L7、L9、V11、V13、V14 の一部）。一覧は `records/claude_md_slim_check/fixes.md` の 2 回目の節。
- 経緯：1 回目の照合（`output.md`）の後の直し（コミット 90a438f）は主張を変える直しを含んだので、停止規則により統合照合をもう 1 回だけ行った。その結果は高 1・中 8 で、低・極低だけではなかった。
- 直していないもの：H1（「新しいパートは始めない」）・M8（判断の経路は 1 つ）は短縮版の承認で入った構築側の文で、旧版より強い。著者の判断に返した。M7 は著者の規則（2026-11-13）なので直さない。
- 自己申告（根拠にしない）：戻した文はすべて旧版の文言を grep で照らした。新しい主張は足していないつもり。
- 扱い：停止規則の「もう 1 回だけ」は使い切った。次のパートか基礎文書の統合照合の入力に CLAUDE.md の差分を含める。H1・M8 の扱いは著者の判断待ち。


### L43：玩具「∞ と −∞ と 0 が射影でねじれて繋がる」の原点からの積み上げ（2026-11-27 08:1x、新しい材料）

- 著者の依頼（08:04）と設定の回答による。新しいノート `notes/pag2_toy_origin_buildup.md` と `records/toy_origin/`（`toy_check.py` とログ）。新しいパートではなく短期層の小さいノート。解像度は使わない。
- 引き継ぎメモに 1 行。
- 基礎文書の本文・索引・CLAUDE.md は変えていない。
- 追記（2026-11-27 08:2x、著者の選択 (A)（08:21）を受けて）：ノートの §11 に選択の後注、§12（段 5：回転角の分解。PAG261 `rootNum_listChar_formII` の言い直し、実の部分の打ち消しと相互法則）と §13（残る問い）を足した。`records/toy_origin/toy_stage5.py` とログ。CLAUDE.md §1 の「重なり」の読みの下に、玩具の「ねじれて繋がる」は組の回転と読む旨の 1 行（2026-11-27 08:21、著者の選択）を足し、英語版にも同じ文。引き継ぎメモに 1 行。照合は受けていない。
- 追記（2026-11-27 17:3x、著者の選択「1」（17:09）を受けて）：ノートに §14（段 6 の事前登録の 4 点）・§15（段 6 の結果：素点ごとの分解、交差項の置き場所は ψ の取り方で動く。盲検の指摘で §14 の読みと対照群の文を訂正）・§16（残る問い）を足した。`records/toy_origin/stage6/`（依頼文、盲検の出力・meta、`local_eps.py`・`local_eps_psiN.py` とログ）。引き継ぎメモに 1 行。照合は受けていない。
- 追記（2026-11-27 17:4x、著者の選択「加法側で」（17:37）を受けて）：CLAUDE.md §1 に玩具の取り決め（結びつきは加法の側、ψ(·/N)、形 (I)）の 1 行（日英）。ノートの §16 に後注、§17（取り決めと帰結：既存の PAG260 の割り振りと同じ、ψ(·/N) は水準によって変わる）を足した。引き継ぎメモに 1 行。照合は受けていない。
- 追記（2026-11-27 18:4x、著者の選択「極限の問い」（18:23）を受けて）：ノートに §18（段 7 の事前登録の 4 点）・§19（段 7 の結果と訂正表）・§20（残る問い）を足した。`records/toy_origin/stage7/`（依頼文、`limit_check.py` とログ（盲検の後に (e) を追加）、盲検の出力と meta）。盲検の指摘で依頼文の L2・L3・L5 の文を直した（§19 の訂正表）。L3 の一意性の正しい形は PAG258 `UA1_family_unique` の仮定と同じ。盲検の出力は最初の返信をファイルに残す前に文脈が切り替わったため、同じエージェントへの「一字も変えずに再送」の依頼で得た（出力ファイルの冒頭に記載）。新規候補なし。引き継ぎメモに 1 行。
- 追記（2026-11-27 19:0x、著者の選択「§20」（18:42）を受けて）：ノートに §21（段 8 の事前登録の 4 点）・§22（段 8 の結果と訂正表）・§23（残る問い）を足した。`records/toy_origin/stage8/`（依頼文、`shell_check.py` とログ、盲検の出力と meta）。盲検の指摘で §21 の見立ての 4 か所を直した（A と単数の作用の絡み方、χ̄*、U_∞ の式は作用素としては導手の射影が要りガウス和の定義の書き直し（構成から自明な形の一致）、M5 の殻ごとの割り当ては誤り）。新規候補なし。照合者は CLAUDE.md が文脈に入っていたと申告した（盲検の条件は完全ではない。§22 の冒頭）。引き継ぎメモに 1 行。
- 追記（2026-11-27 19:4x、著者の指示「進めてください」（19:17）を受けて）：ノートに §24（段 9 の事前登録の 4 点）・§25（段 9 の結果と訂正表）・§26（残る問い）を足した。`records/toy_origin/stage9/`（依頼文、`padic_axis.py` とログ（盲検の後に (g) を追加）、盲検の出力と meta）。盲検の指摘で §24 の見立てを直した（固有ベクトルの向きと ℓ² でないこと、ホロノミーは名前の付け替え、大域の対数の軸の符号、対比は L 因子が自明か否か）。新規候補なし。照合者は CLAUDE.md が文脈に入っていたと申告した（段 8 と同じ条件）。引き継ぎメモに 1 行。
- 追記（2026-11-28 07:1x、著者の選択「無限素点に独立に置いた境界条件」（07:13）を受けて）：CLAUDE.md §1 に 1 行足した（日英）。ノートの §26 に後注、§27（選択と帰結。解釈の層の整理で、新しい数学の主張はない）を足した。引き継ぎメモに 1 行。
- 扱い：照合は受けていない。次のパートの統合照合に載せる（著者が求めれば独立の照合にかける）。


## §2 L41：差分（コミット b01b4e2・e12b4e5。records/ の下は除く）
```diff
diff --git a/CLAUDE.en.md b/CLAUDE.en.md
index 340c2ec..24f4f60 100644
--- a/CLAUDE.en.md
+++ b/CLAUDE.en.md
@@ -44,7 +44,7 @@ The purpose of this procedure is not to avoid mapping to existing mathematics. T
   - The classification of $z(\chi)$ as roots of unity = Chowla–Mordell / Odoni / Funakura (1992). The identification of Ramanujan sum formulas with the DFT = classical ($r$-even function theory).
   - $\langle D_u, E_N\rangle \cong M_{d(N)} \times \mathbb C^{S'}$ (Part 241) and the Fourier conjugation (Part 242) correspond to known basic observations / hyper-duality (confidence: medium).
 - Candidates for novelty are limited to the following two points (unsettled; do not assert). Former candidate 2 was removed from the candidates in the check of 2026-11-12, but is kept as a record of the history:
-  1. The classification of generators (completed in Parts 245–248, no exclusions; range corrected on 2026-11-19: the declaration `sumSub_eq_shellAlg_iff` of item 66 is in PAG249 (Part 245); it was previously written as "Parts 246–248"): in Terwilliger's language, "the classification of generating systems of $T(0)$ of cyclotomic schemes". In the re-audit of 2026-11-12 its scope narrowed: excluding the structure theorem and a few-line corollary of the dimension formula ($\langle M^*, E_N\rangle = A_N \Leftrightarrow N \in \{1,4\} \cup$ primes), what remains as a classification not in the literature is only item 66 (the condition for the sum of two dual algebras) and items 67–69 (the complete classification). After the independent checks were completed, the range remaining as a new candidate narrowed to **composite $N$** (confidence: medium). The assessment is "at the level of a small note": not a new phenomenon but "a computation nobody has written". MathSciNet is not done, by the author's decision of 2026-11-26. zbMATH was done on 2026-11-26, and it found no item that changes the status of candidate 1, candidate 3, or direction γ (results in `notes/pag2_literature_zbmath_20261126.md` §6). Search terms: Terwilliger algebra, orbit Schur ring, cyclotomic S-ring, dual Bose–Mesner algebra, generated by, generating set.
+  1. The classification of generators (completed in Parts 245–248, no exclusions; range corrected on 2026-11-19: the declaration `sumSub_eq_shellAlg_iff` of item 66 is in PAG249 (Part 245); it was previously written as "Parts 246–248"): in Terwilliger's language, "the classification of generating systems of $T(0)$ of cyclotomic schemes". In the re-audit of 2026-11-12 its scope narrowed: excluding the structure theorem and a few-line corollary of the dimension formula ($\langle M^*, E_N\rangle = A_N \Leftrightarrow N \in \{1,4\} \cup$ primes), what remains as a classification not in the literature is only item 66 (the condition for the sum of two dual algebras) and items 67–69 (the complete classification). After the independent checks were completed, the range remaining as a new candidate narrowed to **composite $N$** (confidence: medium). The assessment is "at the level of a small note": not a new phenomenon but "a computation nobody has written". MathSciNet is not done, by the author's decision of 2026-11-26. zbMATH was done on 2026-11-26, and it found no item that changes the status of candidate 1, candidate 3, or direction γ (results in `notes/pag2_literature_zbmath_20261126.md` §6). No reservation on external use as novelty is attached (the author's decision of 2026-11-26 15:5x; stated explicitly by the author's instruction of 2026-11-26 21:11). Search terms: Terwilliger algebra, orbit Schur ring, cyclotomic S-ring, dual Bose–Mesner algebra, generated by, generating set.
   2. The presentation of the compatibility Theorem 2.6 of the monograph. **With the completion of the two independent checks (blind and critique) on 2026-11-12, it was removed from the new candidates**: the combination ($\alpha_{\bar\chi} = -\alpha_\chi$ and the root number) is "a short consequence of known results" (confidence: high; agreed by the construction side, the critique and the blind check). No literature writing this combination was found (confidence: medium), but that is not grounds for novelty (confidence: medium to high). That the root number satisfies the condition is only a consistency check and does not amount to deriving A1. History: half of the commutativity on the limit side is within the scope of Burnol's theorem, and both halves have close precedents in Examples 7.1 and 7.2 of Ibort–Lledó–Pérez-Pardo. As a new finding of the blind check, the anti-unitary operator $CW$ combining complex conjugation and $W$ preserves the boundary conditions, so the reversal condition of Theorem 2.6 is equivalent to "the boundary unitary maps real-valued functions to real-valued functions (reality)" (confirmed by hand calculation and numerics). On the Lean side, it was confirmed that the phase of A1 satisfying the condition of Theorem 2.6 follows from three theorems, PAG16 (`normSq_gaussSum`), PAG173 and PAG198 (the single combined statement is not formalized).
   3. The non-existence side of the dichotomy for the premise of direction β (Part 258, PAG262): when $N \mid M$ and a prime $p$ divides both $N$ and $M/N$, there is no unital algebra homomorphism $A_N \to A_M$ that is compatible with pullback and does not mix shells. "Does not mix shells" is the strong reading (the image of the map lies in the span shell by shell: $\varphi(D_s)$ is a linear combination of the $D_t$, and $\varphi(E_s)$ of the $E_t$); on 2026-11-19 the author fixed it as the condition meant by the theorem of Part 258 (because the report with the strong reading was accepted on 2026-11-15, and the sharpness of the preregistered question and the content of candidate 3 depend on this reading). The weak reading, non-unital maps, and other compatibility conditions remain separate questions outside the claim. On 2026-11-15 it was made [new candidate (small)] by the author side's judgment (confidence: low to medium). Grounds and reservations: the existence side is known (the direct product theorem of Hanaki–Kim–Maekawa), but the non-existence side is shown not as a consequence of a known theorem but by an elementary argument from the definitions ($D_N$, $E_N$ and the relation $D_N E_N D_N = \frac1N D_N$, counting with $u = 1 + M/p$), and no literature was found in the blind question test (web search only) (confidence: medium). On 2026-11-19 the construction side checked the texts of Bastian–Humphries, Watanabe (arXiv:2305.19258) and Kim (arXiv:1109.1334) (reading through WebFetch summaries). No description of unital maps along the quotient ℤ/M → ℤ/N was found (`notes/pag2_candidate3_literature_builder.md`; not finding is not a proof of non-existence). Nearby structures exist — corner algebras of wreath products (non-unital subalgebras) and a non-unital homomorphism in a different setting (the generalized Terwilliger algebra of the hypercube, arXiv:2301.08366) — but they do not conflict with the claim (unital maps). The author side read the text of Hanaki–Kim–Maekawa in the authors' preprint, and no description of maps along quotients was found within that text (this is not a proof of non-existence). MathSciNet is not done, by the author's decision of 2026-11-26. zbMATH was done on 2026-11-26, and it found no item that changes the status of candidate 1, candidate 3, or direction γ (results in `notes/pag2_literature_zbmath_20261126.md` §6). **Until the rest of the literature check (MathSciNet, zbMATH, and confirming maps along quotients in the text of Hanaki–Kim–Maekawa) is done, do not use it externally (including in application documents) as novelty.** (2026-11-26 16:38, the author's decision: the reservation remains in place. Since MathSciNet checking was dropped, its condition remains unmet.)
 - When structure is needed, do not re-prove it; cite the literature via the dictionary. The full review is in `novelty-audit.md`.
diff --git a/CLAUDE.md b/CLAUDE.md
index edbe035..abe0848 100644
--- a/CLAUDE.md
+++ b/CLAUDE.md
@@ -41,7 +41,7 @@
   - $z(\chi)$ の冪根分類 ＝ Chowla–Mordell／Odoni／Funakura (1992)。ラマヌジャン和の公式と DFT の同定 ＝ 古典（$r$-even 関数論）。
   - $\langle D_u, E_N\rangle \cong M_{d(N)} \times \mathbb C^{S'}$（Part 241）とフーリエ共役（Part 242）は既知の基本観察／hyper-duality に対応（確信度：中）。
 - 新規性の候補は次の2点に限られる（未確定。断定しないこと）。かつての候補2は 2026-11-12 の照合で候補から外れたが、経緯の記録として残す：
-  1. 生成の分類（Part 245–248 で完成。除外なし。2026-11-19 に範囲を訂正：項目 66 の宣言 `sumSub_eq_shellAlg_iff` は PAG249（Part 245）にある。以前は「Part 246–248」と書いていた）：Terwilliger の言葉で「円分スキームの $T(0)$ の生成系の分類」。2026-11-12 の再監査で範囲が狭まった：構造定理と、次元公式からの数行の系（$\langle M^*, E_N\rangle = A_N \Leftrightarrow N \in \{1,4\} \cup$ 素数）を除き、文献にない分類として残るのは項目66（2つの双対な代数の和の条件）と項目67〜69（完全な分類）のみ。独立の照合の完了後、新規候補として残る範囲は**合成数の $N$** に絞られた（確信度：中）。評価は「小さいノートの水準」で、新しい現象ではなく「誰も書いていない計算」。MathSciNet は 2026-11-26 の著者の決定で実施しない。zbMATH は 2026-11-26 に実施済みで、候補 1・候補 3・方向 γ のいずれについても地位を変える項目はなかった。（結果は `notes/pag2_literature_zbmath_20261126.md` §6。）検索語：Terwilliger algebra, orbit Schur ring, cyclotomic S-ring, dual Bose–Mesner algebra, generated by, generating set。
+  1. 生成の分類（Part 245–248 で完成。除外なし。2026-11-19 に範囲を訂正：項目 66 の宣言 `sumSub_eq_shellAlg_iff` は PAG249（Part 245）にある。以前は「Part 246–248」と書いていた）：Terwilliger の言葉で「円分スキームの $T(0)$ の生成系の分類」。2026-11-12 の再監査で範囲が狭まった：構造定理と、次元公式からの数行の系（$\langle M^*, E_N\rangle = A_N \Leftrightarrow N \in \{1,4\} \cup$ 素数）を除き、文献にない分類として残るのは項目66（2つの双対な代数の和の条件）と項目67〜69（完全な分類）のみ。独立の照合の完了後、新規候補として残る範囲は**合成数の $N$** に絞られた（確信度：中）。評価は「小さいノートの水準」で、新しい現象ではなく「誰も書いていない計算」。MathSciNet は 2026-11-26 の著者の決定で実施しない。zbMATH は 2026-11-26 に実施済みで、候補 1・候補 3・方向 γ のいずれについても地位を変える項目はなかった。（結果は `notes/pag2_literature_zbmath_20261126.md` §6。）外部での新規性の留保は付けない（2026-11-26 15:5x の著者の決定。2026-11-26 21:11 の著者の指示で明記した）。検索語：Terwilliger algebra, orbit Schur ring, cyclotomic S-ring, dual Bose–Mesner algebra, generated by, generating set。
   2. モノグラフの両立定理 2.6 の提示形。**2026-11-12 の独立の照合2つ（盲検・批判）の完了をもって、新規候補からは外れた**：組み合わせ（$\alpha_{\bar\chi} = -\alpha_\chi$ とルート数）は「既知の結果からの短い帰結」（確信度：高。構築側・批判・盲検の三者で一致）。この組み合わせを書いた文献は見つからなかった（確信度：中）が、それは新規性の根拠にならない（確信度：中〜高）。ルート数が条件を満たすことは整合性の確認にすぎず、A1 を導いたことにはならない。経緯：極限の側の可換性の半分は Burnol の定理の範囲、両半分に Ibort–Lledó–Pérez-Pardo の例 7.1・7.2 という近い先行がある。盲検の新しい指摘として、複素共役と $W$ を合わせた反ユニタリ作用素 $CW$ が境界条件を保つため、定理 2.6 の反転の条件は「境界ユニタリが実数値関数を実数値関数に写すこと（実性）」と同値になる（手計算と数値で確認）。Lean の側では、A1 の位相が定理 2.6 の条件を満たすことは PAG16（`normSq_gaussSum`）・PAG173・PAG198 の3定理から出ることが確認された（組み合わせた1つの文は未形式化）。
   3. 方向βの前提の二分法の不存在の側（Part 258、PAG262）：$N \mid M$ で素数 $p$ が $N$ と $M/N$ の両方を割るとき、引き戻しと両立し殻を混ぜない単位的な代数準同型 $A_N \to A_M$ は存在しない。「殻を混ぜない」は強い読み（写像の像が殻ごとの span に入る：$\varphi(D_s)$ は $D_t$ の、$\varphi(E_s)$ は $E_t$ の線形結合）で、2026-11-19 に著者が、Part 258 の定理が意味する条件として確定した（2026-11-15 に強い読みの報告を受理したこと、事前登録の問いの鋭さと候補 3 の内容がこの読みに依存することによる）。弱い読み・非単位的な写像・別の両立条件は、主張の外の別の問いとして残る。2026-11-15 に著者側の判断で［新規候補（小さい）］とした（確信度：低〜中）。根拠と留保：存在の側は既知（Hanaki–Kim–Maekawa の直積の定理）だが、不存在の側は既知の定理の帰結ではなく定義からの初等的な議論（$D_N$・$E_N$ と関係 $D_N E_N D_N = \frac1N D_N$、$u = 1 + M/p$ による数え上げ）で示されており、盲検の問いテスト（ウェブ検索のみ）で文献が見つからなかった（確信度：中）。2026-11-19 に構築側が、Bastian–Humphries・Watanabe（arXiv:2305.19258）・Kim（arXiv:1109.1334）の本文を照合した（WebFetch の要約を通した読み）。商 ℤ/M → ℤ/N に沿った単位的な写像の記述は見つからなかった（`notes/pag2_candidate3_literature_builder.md`。見つからなかったは不存在の証明ではない）。近い構造として、wreath 積の角の代数（単位的でない部分代数）と、別の設定の単位的でない準同型（超立方体の一般化 Terwilliger 代数、arXiv:2301.08366）があるが、主張（単位的な写像）とは食い違わない。Hanaki–Kim–Maekawa の本文は著者側が著者版プレプリントで読み、商に沿った写像の記述はこの本文の範囲で見つからなかった（不存在の証明ではない）。MathSciNet は 2026-11-26 の著者の決定で実施しない。zbMATH は 2026-11-26 に実施済みで、候補 1・候補 3・方向 γ のいずれについても地位を変える項目はなかった。（結果は `notes/pag2_literature_zbmath_20261126.md` §6。）**文献照合の残り（MathSciNet・zbMATH と、Hanaki–Kim–Maekawa の本文での商に沿った写像の確認）が済むまで、外部（応募書類を含む）で新規性として使わない。**（2026-11-26 16:38、著者の決定：留保は付いたままである。MathSciNet の照合をやめたため、その条件は満たされないまま残る。）
 - 構造が必要になったら、再証明せず辞書経由で文献を引くこと。精査の全体は `novelty-audit.md`。
diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
index 4c29c57..92f1c80 100644
--- a/handoff/PAG2_handoff_part259.md
+++ b/handoff/PAG2_handoff_part259.md
@@ -1798,3 +1798,5 @@
 - **「射影」の変換の側で重ね合わせを問う案（2026-11-26 20:19〜20:3x、著者の「進めてください」）**：新しいパートにせず査定した（`notes/pag2_projection_superposition_preregistration.md`、`records/projection_superposition/`）。内部照合で、U（原始指標の空間の上の J H_N/√N）は殻（付値の情報）と可換で、可換でない相手は単数の座標だと分かった（前のノートの手がかりの半分を訂正）。殻と可換でないのは H_N で、T(0) そのもの（既知）。数値：点の状態の U による像の偏りは、W(χ) の位相で一様の約 2 倍、有限素点だけの位相（どちらの規約でも）でほぼ一様。盲検で、約 2 倍は Hartley 核の性質（cas² ≤ 2）で実性の帰結ではないと分かり（実の位相の最適化で約 1.3 倍）、読み T1 は格下げ。結論は否定的：重ね合わせの言葉で命題 3 を読む道は、可換な見方の選び方でも U でも新しい内容を出さなかった。台帳 L39。開いている台帳は L33・L35・L36・L37・L38・L39。
   - （後注 2026-11-26 20:5x、統合照合 XIII の指摘：上の重ね合わせの行の「算術は素数の対数の群が巡回群でないことしか使わない」は、連続な見え方（稠密さ）についての文。固有値の単純さは素数の対数の ℚ 上の 1 次独立（一意分解）を使う。上の「射影」の変換の行の「殻と可換でないのは H_N で、T(0) そのもの」は、「その可換でなさは T(0) の構造そのもの」と読む。）
 - **統合照合 XIII（2026-11-26 20:41〜20:54、著者の 20:39「これで進めます」）**：新しいパートを始めない方針で台帳が「次のパートの統合照合」を待ち続けるため、L33・L35〜L39 を独立に 1 回照らした（`records/ledger_XIII/`）。高なし、中 2（零点のノートの対照群の文に「零点は全素点の積に現れる」が残っていた、草稿 1.4 で構築側の読んだ帰結を著者の決定のように書いていた）、低 9、極低 14。直しは草稿 1 を rev 52 に、ノート 3 つ・索引・辞書・英語版・引き継ぎメモ（後注）に入れた。低 3（草稿 5.1・第 6 章冒頭の「打ち切った」）は著者の文面なので直していない。6 件を閉じ、直しは L40（中 1 が主張を狭める直しなので、停止規則のもう 1 回の統合照合 XIV にかける）。
+- **統合照合 XIV（2026-11-26 20:59〜21:04、停止規則のもう 1 回）**：台帳 L40（XIII の後の直し）と草稿 1 rev 52。高なし、中なし、低 4、極低 10。規則により L40 を閉じた。指摘の直し（射影のノートの C3 の留保の範囲の訂正（素数の N でも射影した δ_x は正規直交でない、N = 13 で確認）など）は L41 として次のパートの統合照合に載せる。著者に確かめる事項が 3 件生じた（索引 §6 の後注）：叩き台 rev 119 に 16:38 の印を入れるか、CLAUDE.md §3 の候補 1 に留保を付けないと明記するか、草稿 5.1 の「文献照合は zbMATH と HKM の本文で打ち切ったので」は著者の文面か。開いている台帳は L41 だけ。
+  - 著者の回答（2026-11-26 21:11）：(1) 叩き台 rev 119 に印を入れる → 5.1 に入れた（rev 120。ほかの 4 行は MathSciNet をやめた記述だけで有効なので入れていない）。(2) CLAUDE.md §3 の候補 1 に「外部での新規性の留保は付けない（15:5x の決定）」を明記 → 日英に入れた。(3) 草稿 5.1 の「文献照合は zbMATH と HKM の本文で打ち切ったので」は 16:38 の著者の文面 → 変えない。索引 §6 に後注、台帳 L41 に追記。
diff --git a/notes/pag2_founding_material_index.md b/notes/pag2_founding_material_index.md
index e810d76..bcc1194 100644
--- a/notes/pag2_founding_material_index.md
+++ b/notes/pag2_founding_material_index.md
@@ -221,7 +221,8 @@
 
 **3.1 定義文と、その置き方と読み。**
 - 地位：
-  - 定義文（著者の文面）：直線は解像度を落としたときに創発する有効な姿。解像度のパラメータは未決定。（後注 2026-11-26 20:5x、統合照合 XIII の指摘を受けて：基礎文書の草稿 1 の 3.1 は CLAUDE.md §1 の 2 つの項を全文で引く（rev 52 で 2 つ目の項の後半「N、K、Λ のいずれとも勝手に同一視しないこと」を足した）。CLAUDE.md は著者の記録（補足 7）なので、草稿の引用は CLAUDE.md の文言に合わせ、著者の原文との別の照合は著者側の作業に挙げない。）
+  - 定義文（著者の文面）：直線は解像度を落としたときに創発する有効な姿。解像度のパラメータは未決定。
+    - （後注 2026-11-26 20:5x、統合照合 XIII の指摘を受けて：基礎文書の草稿 1 の 3.1 は CLAUDE.md §1 の 2 つの項を全文で引く（rev 52 で 2 つ目の項の後半「N、K、Λ のいずれとも勝手に同一視しないこと」を足した）。CLAUDE.md は著者の記録（補足 7）なので、草稿の引用は CLAUDE.md の文言に合わせ、著者の原文との別の照合は著者側の作業に挙げない。）（2026-11-26 21:0x、統合照合 XIV の指摘で、著者の文面の行から別の行に分けた。）
   - 置き方（2026-11-13）：見方の選択として解釈の層に置く（著者側 Muse の決定）。
   - 08:41 の定義（2026-11-13、著者の原文）：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。」
   - 読み L1（2026-11-13 08:38 に著者が採った読み。構築側の案）：解像度は測る素点の集合。
@@ -427,7 +428,8 @@
 
 ## §6 開いている点（文書に「開いている」と書くもの）
 
-（後注 2026-11-26 20:5x、統合照合 XIII の指摘：叩き台（下書き）は rev 119 のままで、5.1・著者側の作業の表の 2 行・チェックリストの 2 行は、16:38 の決定で置き換わった 16:0x の記述（候補 3 の留保を解く）のまま。叩き台は 16:15 の著者の指示で起草の元として指定された版なので書き換えず、現在の扱いは草稿 1（rev 52）と上の 5.1 の 16:38 の後注による。叩き台に印を入れるかは著者に確かめる事項。）
+（後注 2026-11-26 20:5x、統合照合 XIII の指摘：叩き台（下書き）は rev 119 のままで、5.1・著者側の作業の表の 2 行・チェックリストの 2 行は、16:38 の決定で置き換わった 16:0x の記述（候補 3 の留保を解く）のまま。叩き台は 16:15 の著者の指示で起草の元として指定された版なので書き換えず、現在の扱いは草稿 1（rev 52）と上の 5.1 の 16:38 の後注による。叩き台に印を入れるかは著者に確かめる事項。）（後注 2026-11-26 21:0x、統合照合 XIV の指摘：叩き台 rev 119 の冒頭の経緯には統合照合 XII がなく、5.1 の 16:0x の文には選択肢の文面であることの帰属と「必ず」がない。どちらも置き換わった記述なので記録だけにする。この後注を §6 の冒頭に置いたのは、叩き台の版についての注で節全体にかかるため。後注は並べ替えない（並べ替えは記録の書き換えに当たるため）。）
+（後注 2026-11-26 21:0x、統合照合 XIV の指摘：下の「著者の確認待ち」の「なし」に対し、統合照合 XIII・XIV の後に著者に確かめる事項が 3 件生じた。(1) 叩き台 rev 119 に、16:0x の記述が 16:38 で置き換わった印を入れるか。(2) CLAUDE.md §3 の候補 1 に「外部での新規性の留保は付けない（2026-11-26 15:5x）」と明記するか（現状は太字の留保が候補 3 にしかないことから読み取れるだけ）。(3) 草稿 1 の 5.1 の「文献照合は zbMATH と HKM の本文で打ち切ったので」は 16:38 に著者の文面にした箇所か（第 6 章冒頭の「文献照合は打ち切った」は 16:15 の著者の文面「文献照合は打ち切りです」と合う。16:38 の原文はリポジトリになく、構築側では確かめられない。台帳 L34 の追記の「著者の文面に」の範囲も、この確認で決まる）。）（後注 2026-11-26 21:11、著者の回答：(1) 叩き台 rev 119 に印を入れる → 5.1 に入れた（rev 120）。表の 2 行とチェックリストの 2 行は「MathSciNet は 16:0x の決定でやめた」とだけ書いており、これは 16:38 の後も有効なので印は入れていない（構築側の判断）。(2) CLAUDE.md §3 の候補 1 に「外部での新規性の留保は付けない（15:5x の決定）」を明記する → 日英に入れた。(3) 草稿 1 の 5.1 の「文献照合は zbMATH と HKM の本文で打ち切ったので」は 16:38 の著者の文面である → 草稿は変えない。台帳 L34 の追記の「著者の文面に」はこの句を含む。これで 3 件の確認は閉じた。）
 
 （後注 2026-11-26、台帳 L29 の「直していないもの」を受けて：下書きの「開いている点」の冒頭の文の出所は、2026-11-25 の方向の監査 §5 で、2026-11-26 の監査（`pag2_audit_20261126.md`）でも同じ見立てだった。下書き rev 83 でこの出所を冒頭に書いた。）
 
diff --git a/notes/pag2_projection_superposition_preregistration.md b/notes/pag2_projection_superposition_preregistration.md
index b25bd25..65f0a51 100644
--- a/notes/pag2_projection_superposition_preregistration.md
+++ b/notes/pag2_projection_superposition_preregistration.md
@@ -46,12 +46,12 @@
 
 ## 6. 数値（`records/projection_superposition/ps_check.py`、ログ `ps_check.log`）
 
-- **C1（可換性）：** N = 7・11・13・15・16・21 で ‖[H_N, D_s]‖ の最大は 2.449〜4.472（可換でない）、‖[U, D_s]‖ はすべて 0.0（可換）、‖[U, P_x]‖ の最大は 0.556〜0.871（可換でない）。U を指標の基底で作ったものと Π(J H_N/√N)Π の差は 1.2×10⁻¹⁴ 以下（Part 252 の式の数値の確認）、U*U と原始指標の空間への射影 Π の差は 2.5×10⁻¹⁴ 以下（ユニタリ性、Part 253）（統合照合 XIII の指摘で直した）。
+- **C1（可換性）：** N = 7・11・13・15・16・21 で ‖[H_N, D_s]‖ の最大は 2.449〜4.472（可換でない）、‖[U, D_s]‖ はすべて 0.0（可換）、‖[U, P_x]‖ の最大は 0.556〜0.871（可換でない）。U を指標の基底で作ったものと Π(J H_N/√N)Π の差は 1.2×10⁻¹⁴ 以下（`ps_check.log` の C1 の N = 13 の行。Part 252 の式の数値の確認）、U*U と原始指標の空間への射影 Π の差は 2.5×10⁻¹⁴ 以下（同 N = 11 の行）（ユニタリ性、Part 253）（統合照合 XIII の指摘で直した）。
 - **C2（重ね合わせの度合い）：** 基底は δ_y を原始指標の空間に射影して正規化したもの。像の分布の平坦さ（m·max p。一様なら 1）の平均 / 最大 / エントロピー比（一様なら 1）。
   - 素数の法 N = 11〜31：A1（W）は 2.22→2.10 / 同 / 0.849→0.906。素朴（τ/√N）は 1.19→1.07 / 同 / 0.996→1.000。逆規約の有限素点の積（χ(−1)τ/√N）は素朴と同じ値。自明（位相 1）は m − 1（局在したまま）。乱数（200 回の平均）は 3.09→4.05 / 同 / 0.826→0.880。
   - 合成数の法 N = 15・21：A1 は 2.43・2.54、素朴と逆規約は 1.30・1.27、乱数は 2.23・2.65。合成数では A1 が乱数と同程度かそれ以上に偏る。
   - 構築側の説明：W の位相では核が cas（|cas|² は 0〜2）、有限素点だけの位相では核が絶対値一定の加法指標になるため。素数の法で A1 の平坦さが 2 に近づくのはこれと合う（確信度：中〜高、手計算の見込み）。
-- **C3（不確定性）：** （盲検の P3 の留保：合成数の N では原始指標は単数の上の関数の空間を張らず、原始指標の空間に射影した δ_x は正規直交でない。下界 log m は成り立つが、最良かは調べていない。（統合照合 XIII の指摘で直した））指標の基底での分布は位相で変わらない（差の最大 6.1×10⁻¹⁵・1.6×10⁻¹⁵）。エントロピーの和の最小は 4.535（N = 13）・3.661（N = 21）で、下限 log m = 2.485 以上。
+- **C3（不確定性）：** （盲検の P3 の留保。（統合照合 XIV の指摘で直した）N によらず、原始指標の空間に射影した δ_x は正規直交でない（素数の N でも自明指標は原始的でないので、原始指標の空間は p − 2 次元。N = 13 で、射影した δ_x のグラム行列は対角 11/12・非対角 −1/12）。そのため Maassen–Uffink はそのままは当てはまらず、エントロピーの和が log m 以上なのは N = 13・21 の数値での観察。最良かは調べていない。）指標の基底での分布は位相で変わらない（差の最大 6.1×10⁻¹⁵・1.6×10⁻¹⁵）。エントロピーの和の最小は 4.535（N = 13）・3.661（N = 21）で、下限 log m = 2.485 以上。
 - **C4（対照群）：** §5。
 - 地位：数値は既知の事実の確認で、証明ではない（CLAUDE.md §6）。
 
@@ -66,7 +66,7 @@
 ## 8. 扱いの勧め（構築側）
 
 - **新しいパートにしない。** 数学の文としての残余は空（P4 は Part 252 の恒等式からの短い帰結）。読みの残余のうち T1 は盲検の数値で格下げした（約 2 倍は Hartley 核の性質で、実性の帰結ではない）。
-- **残る結論は T2 だけで、否定的な結論：** （盲検の P2 の補足：殻との可換は、原始指標の空間が単数の殻の中にあることから自明で、内容は薄い。N ≡ 2 (mod 4) では原始指標がなく U = 0。（統合照合 XIII の指摘で直した））U は殻（付値の情報）と可換なので、U の位相は「どの素点を測るか」の見方と干渉しない。重ね合わせの言葉で命題 3（解像度）を読む道は、可換な見方の選び方（前のノートの S1、古典確率の言い直し）でも、「射影」の変換（U）でも、新しい内容を出さなかった。可換でない相手として残るのは、殻と Hartley 変換の T(0)（既知、§3）と、単数の座標と指標のフーリエ双対（既知）である。
+- **残る結論は T2 だけで、否定的な結論：** （盲検の P2 の補足：殻との可換は、原始指標の空間が単数の殻の中にあることから自明で、内容がない（盲検の P2 の文言）。（統合照合 XIV の指摘で直した）N ≡ 2 (mod 4) では原始指標がなく U = 0。（統合照合 XIII の指摘で直した））U は殻（付値の情報）と可換なので、U の位相は「どの素点を測るか」の見方と干渉しない。重ね合わせの言葉で命題 3（解像度）を読む道は、可換な見方の選び方（前のノートの S1、古典確率の言い直し）でも、「射影」の変換（U）でも、新しい内容を出さなかった。可換でない相手として残るのは、殻と Hartley 変換の T(0)（既知、§3）と、単数の座標と指標のフーリエ双対（既知）である。
 - **基礎文書の本文には入れない。** 命題 3 と無限素点の中身は著者の読みが固まるまで開いたまま置く決定（2026-11-26）に従い、このノートを材料として保存する。
 - 前のノート（`pag2_superposition_resolution_preregistration.md`）§8 の手がかりは、このノートの §0 で半分訂正した（U は付値と可換）。前のノートは書き換えていない。
 
diff --git a/notes/pag2_superposition_resolution_preregistration.md b/notes/pag2_superposition_resolution_preregistration.md
index a82d150..9060a7c 100644
--- a/notes/pag2_superposition_resolution_preregistration.md
+++ b/notes/pag2_superposition_resolution_preregistration.md
@@ -7,7 +7,7 @@
 - **出所：** §1 の命題 3（解像度と有効な姿）。
 - **解像度のパラメータ：** 未決定のまま。この登録は N・K・Λ のいずれとも同一視しない。数値の箱（素数と指数の打ち切り）は計算の打ち切りで、解像度ではない。
 - **著者の読みとの関係：** 命題 3 の置き場（大域対象への切り方（見方）の選択、2026-11-13）、L1（解像度＝測る素点の集合、2026-11-13）、08:41 の定義（完備化への滑り落ちが解像度が落ちること、極限でも離散構造の観測を維持する）。この登録はどれも変えない。
-- 零点の案（同日 17:47〜）は著者の判断待ち（`pag2_zeros_resolution_preregistration.md` §7 の判断事項）で、この登録とは独立に扱う。（統合照合 XIII の指摘で直した）
+- 零点の案（同日 17:47〜）は著者の判断待ち（`pag2_zeros_resolution_preregistration.md` §7 の判断事項）で、この登録とは独立に扱う。（統合照合 XIII の指摘で直した。最初の版は「著者の判断で保留中」と書いていたが、記録に支えがなかった。）
 
 ## 1. 問いを幾何の言葉で書く
 
@@ -39,7 +39,7 @@
 
 ## 5. 対照群テスト（残余の文に。数値 §7 の N1・N3・N5）
 
-- （盲検の補足：本当の関数体では次数 0 の元が無限個あるので、各固有値の多重度は無限。稠密さに要るのは素数の対数が生成する群が巡回群でないことだけで、ℚ は一般化素数の系の特別な場合。Q2 はこの条件以外の算術を使っていない。）
+- （盲検の補足：本当の関数体では次数 0 の元が無限個あるので、各固有値の多重度は無限。稠密さに要るのは素数の対数が生成する群が巡回群でないことだけで、ℚ は一般化素数の系の特別な場合。Q2 はこの条件以外の算術を使っていない。）（後注、統合照合 XIV の指摘：この盲検の文は稠密さ（S2）についてのもの。固有値の単純さは素数の対数の ℚ 上の 1 次独立を使う（§8）。）
 - **関数体型**（log p を次数 × log 2 に置き換えた計算模型）：L のスペクトルは (log 2)ℤ で離散、固有値は重複し、窓 [−1, 1] のビンの被覆は 0.075〜0.100、δ-鎖の類は 3 のまま（箱を広げても変わらない）。S2 の連続な見え方は起きない。
 - **一般化素数型**（対数を乱数にした模型）：ℚ と同じく、隙間が縮み（E = 8 で 0.0035）、被覆 1.000、δ-鎖の類は 1（E ≥ 4）。
 - **もつれ（S3）**：集まった状態のもつれのエントロピーは、ℚ・関数体型・一般化素数型のどれでも正（2 分割 {2}|{3,5,7} で 3.70 ビット前後）。基底ベクトルと素数ごとの積の状態は 0。
@@ -64,7 +64,7 @@
 
 ## 8. 扱いの勧め（構築側）
 
-- **新しいパートにしない。** 数学の文としての残余は空（盲検で確認）。読みの残余 S1〜S3 は盲検の後にどれも弱まった。とくに、付値の作用素はすべて可換なので、Q1・Q2 の範囲では「重ね合わせ」の言葉は古典確率の言い直しにとどまる（S1）。Q2 は Part 250 の言い直し（内部の重複の B）で、連続な見え方（稠密さ）は素数の対数の群が巡回群でないことしか使わない。固有値の単純さは素数の対数の ℚ 上の 1 次独立（一意分解、`log_inj`）を使う。（統合照合 XIII の指摘で直した）
+- **新しいパートにしない。** 数学の文としての残余は空（盲検で確認）。読みの残余 S1〜S3 は盲検の後にどれも弱まった。とくに、付値の作用素はすべて可換なので、Q1・Q2 の範囲では「重ね合わせ」の言葉は古典確率の言い直しにとどまる（S1）。Q2 は Part 250 の言い直し（内部の重複の B）で、連続な見え方（稠密さ）は素数の対数の群が巡回群でないことしか使わない。固有値の単純さは素数の対数の ℚ 上の 1 次独立（一意分解、`log_inj`）を使う（素数ごとの指数のベクトルの模型、テンソル積の側で見たとき。基底 δ_q で見るなら log の単射性から直ちに出る）。（統合照合 XIII の指摘で直した）
 - **基礎文書の本文には入れない。** 命題 3 は著者の読みが固まるまで開いた問いのまま置く決定（2026-11-26）に従い、このノートを材料として保存する。
 - **盲検から出た手がかり（構築側の読み、確信度：低〜中）：** 重ね合わせ・もつれが内容を持つのは、付値の作用素と可換でない観測量を測るときだけ（Q3 の (3)）。PAG の構成の中で付値と可換でないのは、乗法の側と加法の側をつなぐ変換、つまり「射影」の読みの変換（有限レベルでは `JH`、貼り合わせ U）である（可換でないことは構築側の見込みで、確かめていない）。重ね合わせの言葉を命題 3 に使うなら、可換な見方の選び方（S1）ではなく、「射影」の変換が見方どうしを結ぶ側で問うことになる。ただしそこは Bost–Connes 系の Hecke 代数や Connes のアデール類空間の領域で、既知の理論に入る見込みが高い（盲検の Q6）。問いとして立てるかは著者の判断。
 - **数値の人工物の記録：** N2 は打ち切りの人工物で結論に使わない（§7）。
diff --git a/notes/pag2_tail_ledger.md b/notes/pag2_tail_ledger.md
index 250c98a..42bfeb3 100644
--- a/notes/pag2_tail_ledger.md
+++ b/notes/pag2_tail_ledger.md
@@ -4,28 +4,47 @@
 
 ## 開いている項目
 
-### L40：統合照合 XIII の後の直し（2026-11-26 20:5x）
-
-- 範囲：XIII（`records/ledger_XIII/outputs/integrated_XIII_output.md`）の指摘を受けた直し。
-  - 草稿 1：rev 49 → rev 52。1.4 の「決定 (a) で…空間のレベルの対応は立てないとされた」を「決定 (a) は、重なりを作用素の側でだけ書くとした。『空間のレベルの対応は立てない』は、(a) から構築側が読んだ帰結である」に（中 2）。3.1 の 2 つ目の項を CLAUDE.md §1 の全文に（「N、K、Λ のいずれとも勝手に同一視しないこと」を足した。低 4）。記号の段落の `PAG.Part27.Wproj` をコード書式に（極低 24）。
-  - 零点のノート：§4 の結果の括弧を直した（中 1）。R3 の位相を 𝔀(χ) に直し、記号の注を足した（低 8）。§3a 内部照合を新設（低 11）。E2 の素数冪を 7・23・60 個に、比を 0.638〜0.639 に、R1 の「完備化した対象」を「完備化した L 関数」に、IK の定理番号に確信度の注（極低 12・20・22）。
-  - 重ね合わせのノート：§0 の「著者の判断で保留中」を「著者の判断待ち（零点のノート §7 の判断事項）」に（低 7）。§8 の「巡回群でないことしか使わない」を稠密さに限り、単純さは 1 次独立を使うと書いた（低 6）。S2 の元の文の「有効な姿（連続な見え方）」を「連続な見え方（解像度が落ちる側の見え方）」に（低 10）。§3 の「鎖にない」を「見つからなかった」に、`PAG254.logSet` を `PAG.Part254.logSet` に（極低 15）。
-  - 射影のノート：§8 の T2 に盲検 P2 の補足（低 9）。C1 の数値の上限を 1.2×10⁻¹⁴・2.5×10⁻¹⁴ に、§2 の規約の行に ω の正規化・s = 1/2・記号 W = 𝔀 の注、C3 に P3 の留保（極低 12・16）。
-  - 英語版 CLAUDE.en.md：候補 3 の壊れた文を直した（極低 13）。
-  - 索引：3.1 に草稿の引用の後注（低 4）。§6 の冒頭に叩き台 rev 119 の 16:0x の記述の後注（低 5）。辞書 §24 に「同じ内容」の範囲の後注（極低 17）。引き継ぎメモに L38・L39 の行の後注（低 6・極低 21）。
-  - 記録：`records/ledger_XIII/`（入力・依頼文・出力・meta）。この台帳と引き継ぎメモ。
-- 閉じた記録の範囲の漏れ（XIII の極低 14。閉じた記録は書き換えず、ここに書く）：L37・L38・L39 は、それぞれ足した引き継ぎメモの 1 行を範囲に書いていなかった。L35 は `records/founding_draft1/` の D2 の出力・meta（コミット a6cc4c2）を範囲に書いていなかった。
-- 直していないもの：
-  - 低 3（草稿 5.1 の「文献照合は zbMATH と HKM の本文で打ち切ったので」、第 6 章冒頭の「文献照合は打ち切った」）：16:38 の決定で 5.1・6.2・第 6 章冒頭は「著者の文面に」直した箇所で（L34 の追記）、「文献照合は打ち切りです」は 16:15 の著者の指示の文面でもある（D2 の入力 §0）。著者の文を構築側が書き換えないため、直さない。著者の 16:38 の文面の原文はこのリポジトリになく、草稿のどこまでが著者の文面かは照らせない（XIII の確かめられなかったこと）。
-  - 極低 18（叩き台の冒頭の経緯と 5.1 の帰属）：叩き台は書き換えない（索引 §6 の後注）。
-  - 極低 19（CLAUDE.md §3 の候補 1 に「外部での新規性の留保は付けない」を足すか）：CLAUDE.md は著者の記録で、依頼のない文は足さない。著者に確かめる事項。
-  - 極低 23（索引 5.1 の後注の時刻の順）：後注は足した順に並べる決まりで、並べ替えない。
-  - L36 の極低（候補 3 の構築側の文に日付がない）：17:28・17:44 の著者の依頼による整理の一部で、台帳 L36 に記録がある。CLAUDE.md にさらに文を足さない。
-- 自己申告（根拠にしない）：中 1 は主張を狭める直し（誤った部分を外した）。中 2 は帰属を記録に合わせる直し。ほかは数値・記号・留保の書き足し。
-- 扱い：XIII には中 2 があり、中 1 の直しはノートの主張を変える（狭める）ので、停止規則により L40 はもう 1 回だけ統合照合 XIV にかけ、その後はこの規則で閉じる。
+### L41：統合照合 XIV の後の直し（2026-11-26 21:0x）
+
+- 範囲：XIV（`records/ledger_XIV/outputs/integrated_XIV_output.md`）の指摘を受けた直し。
+  - 射影のノート：C3 の留保を「N によらず射影した δ_x は正規直交でない（素数でも自明指標は原始的でない。N = 13 でグラム行列は対角 11/12・非対角 −1/12）。Maassen–Uffink はそのままは当てはまらず、log m 以上は N = 13・21 の数値での観察」に直した（低 a。構築側が N = 13 で数値を確かめた）。T2 の補足の「内容は薄い」を「内容がない（盲検の P2 の文言）」に（極低 f）。C1 の 2 つの値にログの行を添えた（極低 n。構築側がログで確かめた：1.2×10⁻¹⁴ は ‖U − Π(JH/√N)Π‖ の N = 13、2.5×10⁻¹⁴ は ‖U*U − Π‖ の N = 11）。
+  - 重ね合わせのノート：§5 の盲検の補足の「Q2 はこの条件以外の算術を使っていない」に、稠密さについての文である旨の後注（低 b）。§0 に直す前の文を括弧で残した（極低 k）。§8 の単純さの文に模型の注（極低 m）。
+  - 零点のノート：§3a の「素数の対数の稠密性」を「正の有理数の対数の集合（素数の対数が生成する群）の稠密性」に（極低 g）。R3 の記号の注の範囲を §2・§3・§4・§7 に（極低 h）。
+  - 索引：§6 の叩き台の後注に XIII 極低 18 の 2 点と、置き場所・並べ替えない理由の後注（極低 e・i）。§6 に「著者に確かめる事項 3 件」の後注（低 c・d：叩き台 rev 119 の印、CLAUDE.md §3 の候補 1 の明記、草稿 5.1 の句が著者の文面か）。3.1 の後注を著者の文面の行から別の行に分けた（極低 l）。
+  - この台帳と引き継ぎメモ。`records/ledger_XIV/`（入力・依頼文・出力・meta）。
+- L40 の記載の漏れ（XIV の極低 j・l。閉じた記録は書き換えず、ここに書く）：
+  - L40 の「閉じた記録の範囲の漏れ」の L35 は、D2 の入力・依頼文（コミット 14e5b93。L34 の範囲に記録済み）と出力・meta（a6cc4c2）の両方を指すべきだった。
+  - L37〜L39 を閉じた項目の「この項目への指摘」に、XIII の極低 14（引き継ぎメモの行の漏れ）を書いていなかった。
+  - 低 4 の「著者の原文との照合を著者側の作業に挙げない理由」（CLAUDE.md は著者の記録、補足 7。CLAUDE.md §2 の記載による）は、索引 3.1 の後注にだけ書いていた。
+  - 極低 23 の理由（「後注は足した順に並べる決まり」）は記録に出所がなかった。理由は「並べ替えは記録の書き換えに当たるので避ける」と改める（索引 §6 の後注）。
+- 直していないもの：XIV の低 c の前半（草稿 5.1 の句を直すこと）は、著者に確かめる事項 (3) にした。著者の文面かどうかが決まるまで草稿は変えない。
+- 自己申告（根拠にしない）：低 a は留保の範囲を広げる直し（主張を狭める側）。ほかは留保・帰属・記録の書き足し。
+- 追記（2026-11-26 21:11、著者の回答 3 件を受けて）：叩き台を rev 119 → rev 120（5.1 に 16:38 の決定で置き換わった印。表とチェックリストの 4 行は「MathSciNet は 16:0x の決定でやめた」だけで 16:38 の後も有効なので入れていない）。CLAUDE.md §3 の候補 1 に「外部での新規性の留保は付けない（2026-11-26 15:5x の著者の決定。21:11 の著者の指示で明記した）」、英語版にも同じ文。索引 §6 に回答の後注。草稿 5.1 の句は著者の文面と確認されたので変えない（XIII の低 3、XIV の低 c はこれで閉じた）。引き継ぎメモに 1 行。照合は受けていない。
+- 扱い：XIV は停止規則の「もう 1 回だけ」の照合で、最後の指摘が低・極低だけなので、L40 を閉じ、L41 は次のパートの統合照合に載せる。
 
 ## 閉じた項目
 
+- L40（2026-11-26 に閉じた）：統合照合 XIV（2026-11-26 20:59〜21:04、`records/ledger_XIV/`）で、直しそのもの（コミット 1d95783 の差分）、XIII の出力、16:15 の著者の指示、直した後のノート 3 つの全文、草稿 1 rev 52・rev 49 を入力に含めて照らした。高なし、中なし、低 4、極低 10。主張を強める追加と著者の判断の記録の書き換えは見つからなかった（照合者の判定）。停止規則の「もう 1 回だけ」の照合で、最後の指摘が低・極低だけなので、規則により閉じる。XIV の指摘の直しは L41 として次のパートの統合照合に載せる。
+    ### L40：統合照合 XIII の後の直し（2026-11-26 20:5x）
+
+    - 範囲：XIII（`records/ledger_XIII/outputs/integrated_XIII_output.md`）の指摘を受けた直し。
+      - 草稿 1：rev 49 → rev 52。1.4 の「決定 (a) で…空間のレベルの対応は立てないとされた」を「決定 (a) は、重なりを作用素の側でだけ書くとした。『空間のレベルの対応は立てない』は、(a) から構築側が読んだ帰結である」に（中 2）。3.1 の 2 つ目の項を CLAUDE.md §1 の全文に（「N、K、Λ のいずれとも勝手に同一視しないこと」を足した。低 4）。記号の段落の `PAG.Part27.Wproj` をコード書式に（極低 24）。
+      - 零点のノート：§4 の結果の括弧を直した（中 1）。R3 の位相を 𝔀(χ) に直し、記号の注を足した（低 8）。§3a 内部照合を新設（低 11）。E2 の素数冪を 7・23・60 個に、比を 0.638〜0.639 に、R1 の「完備化した対象」を「完備化した L 関数」に、IK の定理番号に確信度の注（極低 12・20・22）。
+      - 重ね合わせのノート：§0 の「著者の判断で保留中」を「著者の判断待ち（零点のノート §7 の判断事項）」に（低 7）。§8 の「巡回群でないことしか使わない」を稠密さに限り、単純さは 1 次独立を使うと書いた（低 6）。S2 の元の文の「有効な姿（連続な見え方）」を「連続な見え方（解像度が落ちる側の見え方）」に（低 10）。§3 の「鎖にない」を「見つからなかった」に、`PAG254.logSet` を `PAG.Part254.logSet` に（極低 15）。
+      - 射影のノート：§8 の T2 に盲検 P2 の補足（低 9）。C1 の数値の上限を 1.2×10⁻¹⁴・2.5×10⁻¹⁴ に、§2 の規約の行に ω の正規化・s = 1/2・記号 W = 𝔀 の注、C3 に P3 の留保（極低 12・16）。
+      - 英語版 CLAUDE.en.md：候補 3 の壊れた文を直した（極低 13）。
+      - 索引：3.1 に草稿の引用の後注（低 4）。§6 の冒頭に叩き台 rev 119 の 16:0x の記述の後注（低 5）。辞書 §24 に「同じ内容」の範囲の後注（極低 17）。引き継ぎメモに L38・L39 の行の後注（低 6・極低 21）。
+      - 記録：`records/ledger_XIII/`（入力・依頼文・出力・meta）。この台帳と引き継ぎメモ。
+    - 閉じた記録の範囲の漏れ（XIII の極低 14。閉じた記録は書き換えず、ここに書く）：L37・L38・L39 は、それぞれ足した引き継ぎメモの 1 行を範囲に書いていなかった。L35 は `records/founding_draft1/` の D2 の出力・meta（コミット a6cc4c2）を範囲に書いていなかった。
+    - 直していないもの：
+      - 低 3（草稿 5.1 の「文献照合は zbMATH と HKM の本文で打ち切ったので」、第 6 章冒頭の「文献照合は打ち切った」）：16:38 の決定で 5.1・6.2・第 6 章冒頭は「著者の文面に」直した箇所で（L34 の追記）、「文献照合は打ち切りです」は 16:15 の著者の指示の文面でもある（D2 の入力 §0）。著者の文を構築側が書き換えないため、直さない。著者の 16:38 の文面の原文はこのリポジトリになく、草稿のどこまでが著者の文面かは照らせない（XIII の確かめられなかったこと）。
+      - 極低 18（叩き台の冒頭の経緯と 5.1 の帰属）：叩き台は書き換えない（索引 §6 の後注）。
+      - 極低 19（CLAUDE.md §3 の候補 1 に「外部での新規性の留保は付けない」を足すか）：CLAUDE.md は著者の記録で、依頼のない文は足さない。著者に確かめる事項。
+      - 極低 23（索引 5.1 の後注の時刻の順）：後注は足した順に並べる決まりで、並べ替えない。
+      - L36 の極低（候補 3 の構築側の文に日付がない）：17:28・17:44 の著者の依頼による整理の一部で、台帳 L36 に記録がある。CLAUDE.md にさらに文を足さない。
+    - 自己申告（根拠にしない）：中 1 は主張を狭める直し（誤った部分を外した）。中 2 は帰属を記録に合わせる直し。ほかは数値・記号・留保の書き足し。
+    - 扱い：XIII には中 2 があり、中 1 の直しはノートの主張を変える（狭める）ので、停止規則により L40 はもう 1 回だけ統合照合 XIV にかけ、その後はこの規則で閉じる。
+
 - L39（2026-11-26 に閉じた）：統合照合 XIII（2026-11-26 20:41〜20:54、`records/ledger_XIII/`）で、直しそのもの（§3 の差分）と根拠（§4）、材料索引の全文、草稿 1 rev 49・叩き台 rev 119 を入力に含めて照らした。全体で高なし、中 2、低 9、極低 14。この項目への指摘：低 9（T2 に盲検 P2 の補足）、極低（C1 の数値の上限、§2 の規約の条件と記号、P3 の留保、引き継ぎメモの句）。直しは L40。停止規則により閉じる（XIII には中 2 があり、直しに主張を変えるもの（中 1）があるので、L40 はもう 1 回だけ統合照合 XIV にかける）。
     ### L39：「射影」の変換の側で重ね合わせを問う案の事前登録（2026-11-26 20:2x、新しい材料）
 
diff --git a/notes/pag2_zeros_resolution_preregistration.md b/notes/pag2_zeros_resolution_preregistration.md
index 3e72d1f..0eef523 100644
--- a/notes/pag2_zeros_resolution_preregistration.md
+++ b/notes/pag2_zeros_resolution_preregistration.md
@@ -29,12 +29,12 @@
 - **読みとしての残余（解釈の層）：** 次の 3 つは数学の新しい文ではなく、§1 の定義の読みの材料である。
   - R1：零点は、有限の S では現れない離散構造である。（盲検の後に弱めた：最初の版は「直極限の側でだけ現れる」と書いたが、零点は部分積の極限としては現れない（Hurwitz）。零点が現れるのは、測る素点を増やす極限ではなく、解析接続とガンマ因子を含む完備化した L 関数の側（ここでの「完備化」は L 関数の完備化で、08:41 の定義の「完備化」とは別の意味。（統合照合 XIII の指摘で直した））である。08:41 の定義の「極限でも離散構造の観測を維持する」の例として書けるかは、この点で開いたまま。GHK の分解（素数 ≤ X の部分積と 1/log X 以内の零点）は、測る範囲と零点の分解能の役割分担としては最も近い形だが、X は素数の初期区間で、Λ 切断と同じ形である。）
   - R2：粗く見たときの連続な姿（ψ の主項 x、N(T) の主項）は、極と無限素点の項から来る（N(T) の +1 は極、(T/2π)log(T/2πe) − 1/8 は無限素点）。素数（と零点）は揺らぎの側を担う。
-  - R3：1 つの L の明示公式は、無限素点の重なりの読み（ねじれた貼り合わせ U）の位相 𝔀(χ)（`PAG.Part256.rootNum`。原始指標ではルート数で、その同定は Lean の外）を含まない（パリティだけ）。（統合照合 XIII の指摘で直した）（記号の注：この節と §2 のルート数の項の ε(χ) は関数等式のルート数（= 𝔀(χ)）を指す。CLAUDE.md §1 の ε(χ) = (−i)^a（`parFac`）とは別。）ただし ε は、中心の零点の強制（自己双対で ε = −1 のとき）と族の対称性の型を通して零点に効く（盲検の補足で弱めた）。明示公式による解像度の読みでは U の位相は試されないが、零点の統計の側では試されうる。
+  - R3：1 つの L の明示公式は、無限素点の重なりの読み（ねじれた貼り合わせ U）の位相 𝔀(χ)（`PAG.Part256.rootNum`。原始指標ではルート数で、その同定は Lean の外）を含まない（パリティだけ）。（統合照合 XIII の指摘で直した）（記号の注：このノートの ε(χ)（§2・§3・§4・§7）は関数等式のルート数（= 𝔀(χ)）を指す。CLAUDE.md §1 の ε(χ) = (−i)^a（`parFac`）とは別。）ただし ε は、中心の零点の強制（自己双対で ε = −1 のとき）と族の対称性の型を通して零点に効く（盲検の補足で弱めた）。明示公式による解像度の読みでは U の位相は試されないが、零点の統計の側では試されうる。
 - §4 の規則により、残余が計算の細部だけか空の問いは新しいパートにしない。**この案は新しいパートにしない。** 扱いの勧めは §7。
 
 ## 3a. 内部照合（第 12 の型）（統合照合 XIII の指摘で直した）
 
-- 言葉の検索（`rootNum`・`parFac`・`normSq_gaussSum`・`logSet`・`chainIn`・明示公式・零点）で、鎖の中の関係する宣言は次のとおり（網羅ではない）。R3 の位相 𝔀(χ) は `PAG.Part256.rootNum`（Part 252）で、|𝔀(χ)| = 1 は `PAG.Part256.normSq_rootNum`。ガウス和の絶対値は Part 12（PAG16）の `normSq_gaussSum`。Part 250（PAG254）の `PAG.Part254.dense_logSet` は素数の対数の稠密性（§2 の Λ 切断の議論とは別）。明示公式・零点を扱う宣言は見つからなかった（第 3 段階は主張の範囲外、索引 6.5）。
+- 言葉の検索（`rootNum`・`parFac`・`normSq_gaussSum`・`logSet`・`chainIn`・明示公式・零点）で、鎖の中の関係する宣言は次のとおり（網羅ではない）。R3 の位相 𝔀(χ) は `PAG.Part256.rootNum`（Part 252）で、|𝔀(χ)| = 1 は `PAG.Part256.normSq_rootNum`。ガウス和の絶対値は Part 12（PAG16）の `normSq_gaussSum`。Part 250（PAG254）の `PAG.Part254.dense_logSet` は正の有理数の対数の集合（素数の対数が生成する群）の稠密性（§2 の Λ 切断の議論とは別）。明示公式・零点を扱う宣言は見つからなかった（第 3 段階は主張の範囲外、索引 6.5）。
 
 ## 4. 対照群テスト（残余の文に）
 

```

### §2a 統合照合 XIV の出力（全文）
# 統合照合 XIV の出力（2026-11-26 20:59〜21:04）

依頼文：`../integrated/request_XIV.md`、入力：`../integrated/input_XIV.md`。文脈を渡さない新しいエージェント（general-purpose）。所要約 269 秒、ツール 13 回。以下は返信の全文（構築側は手を入れていない）。

---

# 統合照合 XIV の報告

まず読めた範囲です。文書の道具は使えました。草稿 1 の現在の rev は 52 で、指定どおりです。比べるために rev 49 も読みました。書き換えの道具は使っていません。

確かめられなかった範囲は次のとおりです。
- Lean の形式文と宣言の実在は確かめていません。§3a・`normSq_rootNum`・`log_inj` などがこれに当たります。
- 次の原文と全文は入力にありません。16:38 の著者の文面、索引の 5.1・§6・2.1 の全文、叩き台の現在の版、ログ（`ps_check.log` など）、XII の出力。

独立性の限界もあります。CLAUDE.md（日本語版）は、起動時から私の文脈に入っていました。§1 の文言との突き合わせには、その文脈を使っています。

**結論**：高なし、中なし、低 4、極低 10。

---

## 1. XIII の指摘ごとの判定

| XIII | 判定 | 根拠 |
|---|---|---|
| 中 1 | 直った | 零点 §4 は「（粗いと主項、細かいと零点）は、零点を持つ対照群（種数 g ≥ 1 の曲線）でも成り立つ。𝔽_q(t) そのものには零点がない」になり、直し案のとおりです。最初の版の句も括弧に残しています。 |
| 中 2 | 直った | 1.4 は「決定 (a) は、重なりを作用素の側でだけ書くとした。『空間のレベルの対応は立てない』は、(a) から構築側が読んだ帰結である」になりました。同じ草稿の 2.1（(a) の文面は構築側の選択肢の文）と、開いている問い（`.20930`）と食い違いません。 |
| 低 3 | 直していない。理由は一部だけ支えられる | 第 6 章冒頭の「文献照合は打ち切った」は、§4 の 16:15「文献照合は打ち切りです」が支えます。一方、5.1 の「zbMATH と HKM の本文で打ち切った」の限定の句は 16:15 にありません。XIII によれば、この句は置き換わった 16:0x の選択肢の文面です。16:38 の原文も入力にないので、著者の文面だという理由は確かめられません。L40 も自分でそう書いています。XIII 低 3 の後半（L35 の「著者の文面に」を、写した範囲に限って書く）には、L40 は触れていません。 |
| 低 4 | ほぼ直った | 草稿 3.1 は CLAUDE.md §1 の 2 つ目の項を最後まで引いています（3 で詳述）。索引 3.1 には後注を足しました。ただし、著者の原文との照合を著者側の作業に挙げない理由（「CLAUDE.md は著者の記録（補足 7）」）は索引の後注にだけあり、台帳 L40 にはありません。XIII は台帳に書くよう求めていました。「補足 7」がその根拠になるかは、入力では確かめられません。 |
| 低 5 | 直った | 索引 §6 の冒頭に、叩き台 rev 119 が 16:0x の記述のままであることの後注があります。叩き台に印を入れるかは「著者に確かめる事項」とされています。閉じた L33 は書き換えず、L40 に書いています。「16:15 で起草の元に指定された版」は §4 の「叩き台は rev 119 です」が支えます。 |
| 低 6 | 一部 | §8 と引き継ぎメモ（後注）は直りました。XIII が挙げた §5 は残っています。§5 の「Q2 はこの条件以外の算術を使っていない」は、Q2 の固有値の単純さを含むので、範囲が広すぎます。 |
| 低 7 | 直った | 新しい文は「著者の判断待ち（`…zeros…` §7 の判断事項）」です。零点ノート §7 に「著者の判断事項（1 件）」があるので、記録が支えます。 |
| 低 8 | 直った | R3 の位相は 𝔀(χ)（`PAG.Part256.rootNum`、同定は Lean の外）になり、記号の注も付きました。標準の関数等式のルート数 τ(χ)/(i^a√N) と同じ値なので、注は正しいです。ただし注の範囲は「この節と §2」だけで、§4・§7 の ε は外れています（極低）。 |
| 低 9 | 一部 | P2 の補足は入りました。しかし XIII（と盲検の P2）が言うのは「内容がない」で、ノートは「内容は薄い」と書いています。XIII が指摘した弱め方が、そのまま残っています。 |
| 低 10 | 直った | S2 は「連続な見え方（解像度が落ちる側の見え方）」になりました。 |
| 低 11 | 直った | §3a を新設し、「網羅ではない」「見つからなかった」と書いています。§3a の記述の問題は 2 で扱います。 |
| 極低 12 | 直った（一部は確かめられない） | E2 は 7・23・60 個になり、理由も書かれています。比は 0.638〜0.639 です。C1 の 1.2×10⁻¹⁴ と 2.5×10⁻¹⁴ がそれぞれどちらの量の最大値かは、ログがないので確かめられません。XIII は数値の出どころの N を書いただけで、どの量の値かは書いていません。 |
| 極低 13 | 直った | 英語版の文は「The author side read the text of Hanaki–Kim–Maekawa …」になり、日本語版の候補 3 の文と一致します。変わったのはこの文だけです。 |
| 極低 14 | 直った（記録の形で） | 閉じた記録は書き換えず、L40 に書いています。ただし、XIII は L35 に欠けているものを「D2 の入力・出力・meta」と書いたのに、L40 は「出力・meta」だけです（極低）。 |
| 極低 15 | 直った | 「見つからなかった」と `PAG.Part254.logSet` の 2 か所とも直っています。 |
| 極低 16 | 直った | 規約 T の行に、ω の正規化・s = 1/2・W = 𝔀 の注が入り、CLAUDE.md §1 と合います。P3 の留保も入りましたが、その範囲が誤っています（2・5 の低 a）。 |
| 極低 17 | 直った | 辞書に outgoing/incoming の文の後注があります。XII の出力そのものは入力にないので照らしていません。 |
| 極低 18 | 直していない。理由は支えられるが、記録が一部 | 叩き台を書き換えない理由は、索引 §6 の後注と 16:15 の指示が支えます。ただし XIII が求めたのは「記録だけ」で、新しい後注には「冒頭の経緯に XII がない」ことと「5.1 に選択肢の帰属と『必ず』がない」ことが書かれていません。 |
| 極低 19 | 直していない。理由は支えられる | L36 の記録（著者の依頼の範囲でだけ CLAUDE.md を整理）と §4（CLAUDE.md §3 の文面は著者側で直す）が理由を支えます。ただし「著者に確かめる事項」が、索引 §6 の「著者の確認待ち」（今も「なし」）に入っていません（低 d）。 |
| 極低 20 | 直った | 「完備化した L 関数（08:41 の定義の『完備化』とは別の意味）」になりました。 |
| 極低 21 | 直った | 引き継ぎメモに後注があり、元の行は残っています。 |
| 極低 22 | 直った | 「定理番号は盲検の照合者の申告で確信度：中、照らしていない」が入りました。 |
| 極低 23 | 直していない。理由は支えられない | 「後注は足した順に並べる決まり」は、入力のどの記録にも見当たりません。しかもこの差分では、索引 §6 で新しい 20:5x の後注が、前からある「（後注 2026-11-26、台帳 L29 …）」の上に置かれています。L40 が挙げた決まりと、L40 自身の直しが合っていません。 |
| 極低 24 | 直った | 文書で確かめました。`PAG.Part27.Wproj` は code の要素（`.22132`）になっています。 |
| L36 の極低 | 直していない。理由は支えられる | 閉じた項目に移した L36 の記録（17:28・17:44 の著者の依頼）が支えます。 |

## 2. 新しい主張や、強めた主張がないか

- **零点 §3a**：主張を強める文はありません。ただし、鎖の宣言についての新しい事実の申告が入っています（`normSq_rootNum` が |𝔀| = 1 を示すこと、検索語の範囲など）。形式文が入力にないので照らせません。また「`PAG.Part254.dense_logSet` は素数の対数の稠密性」は不正確です。重ね合わせノート §3 によれば、logSet は「正の有理数の対数の集合」で、稠密なのは素数の対数が生成する群です（極低）。
- **零点 §4・R1・R3**：主張を狭めたか、記号を直しただけです。R3 の「（= 𝔀(χ)）」は Lean の外の同定で、同じ段落で断っています。
- **重ね合わせ §8**：「固有値の単純さは ℚ 上の 1 次独立（一意分解、`log_inj`）を使う」は新しい文です。素数ごとの指数のベクトルの模型（V_p のテンソル積の側）では正しいです。ただし ℓ²(ℚ_{>0}) の基底 δ_q で見るなら、単純さは log の単射性から直ちに出て、一意分解は要りません（極低、明確にするかは任意）。`log_inj` の形式文は確かめていません。
- **射影 C3 の留保（直しが新しい問題を生んだ）**：「合成数の N では原始指標は単数の上の関数の空間を張らず、射影した δ_x は正規直交でない」とあります。しかし素数の N でも、自明指標は原始的でありません。そのため V_prim の次元は p − 2 で、p − 1 個の射影した δ_x は正規直交になりません。/tmp で確かめると、N = 13 で V_prim は 11 次元、グラム行列の対角は 11/12、非対角は −1/12 でした。C3 は N = 13 の数値を使っているので、留保の範囲を「合成数」に限ると、素数の場合を留保から外すことになります。「下界 log m は成り立つ」も、正規直交でないなら Maassen–Uffink をそのまま当てはめることはできません。数値で観察した値（N = 13・21）として書くのが安全です（低）。
- **射影 T2**：「内容は薄い」は盲検より弱い言い方です（1 の低 9）。強める追加ではありません。
- **索引 3.1・§6 の後注、辞書、引き継ぎメモの後注**：主張を強める追加は見つかりませんでした。ただし次の 2 点があります。
  - 索引 3.1 の後注は、「定義文（著者の文面）」の行の中に括弧で入っています。著者の文面と構築側の後注が同じ行に並ぶ形です（極低）。
  - 索引 §6 の後注は「著者に確かめる事項」を生んでいますが、同じ §6 の「著者の確認待ち」は「再びなし」のままです（低 d）。

## 3. 草稿 1 rev 52

- **rev 49 → 52 の全差分**（XML をトークン単位で比べた）：変わったのは 3 つの段落だけです。記号の段落（`.631`）、1.4 の留保（`.2588`）、3.1 の定義文（`.10390`）です。ほかの文の変化はありません。段落の rev（50・51・52）も、3 回の直しと合います。台帳 L40 の草稿の範囲は漏れなく書かれています。
- **1.4**：XIII の中 2 の直し案と同じ趣旨です。索引 §6 の帰属（XIII が引いた「(a) から構築側が読んだ帰結で、著者の文言ではない」）とも合います。草稿 2.1 によれば (a) の文面は構築側の選択肢の文なので、「(a) は…とした」も記録と食い違いません。
- **3.1**：「直線は、解像度を落としたときに創発する有効な姿である。」「ただし、解像度を決めるパラメータは未決定である。N、K、Λ のいずれとも勝手に同一視しないこと。」は、CLAUDE.md §1 の 2 つの項の文言と一致します。太字と TeX の書式は落ちていますが、文言は同じです。直後の段落「解像度を N・K・Λ と同一視しない。」とは重複しますが、直す必要はありません。定義を引用しているだけなので、「直線の創発」の禁止にも触れません。
- **記号**：コード書式になりました。

## 4. 判断の記録・閉じた項目・台帳の範囲

- **閉じた項目に移した文**：L39・L38・L37・L36・L35・L33 について、消した行（47 行）と移した行（4 字下げを外して 47 行）を機械で突き合わせました。差はなく、順序も同じです。
- **著者の判断の記録**：書き換えは見つかりませんでした。引き継ぎメモと索引には後注を足し、CLAUDE.en.md は壊れた文を日本語版に合わせただけです。
  - 重ね合わせ §0 の「著者の判断で保留中」は、後注ではなくその場で書き換えられ、元の文はノートに残っていません。著者の状態についての構築側の誤った記述を正したもので、元の文は git に残ります。零点 §4 は最初の版の句を残しているので、扱いがそろっていません（極低）。
- **台帳 L40 の差分の範囲**：差分に現れたファイルとハンク（CLAUDE.en.md、引き継ぎメモ、索引 3.1・§6、射影ノート 4 か所、重ね合わせノート 4 か所、台帳、辞書、零点ノート 6 か所）は、すべて L40 の範囲に書かれています。`records/ledger_XIII/` は差分から省かれているので照らしていません。
  - L37〜L39 を閉じた項目の「この項目への指摘」に、極低 14（引き継ぎメモの行の漏れ）が入っていません（極低）。
- **閉じた項目の要約**：件数（高なし・中 2・低 9・極低 14、D2 の 10 件の内訳）は XIII の出力と一致します。

## 5. 直すべき点（重要度順）

**高**：なし。
**中**：なし。

**低**
- a. 射影 C3 の留保：「合成数の N では」を外し、「N によらず（素数でも自明指標が原始的でないので）、原始指標の空間に射影した δ_x は正規直交でない。エントロピーの和が log m 以上なのは N = 13・21 の数値で、Maassen–Uffink の直接の適用ではない。最良かは調べていない」に直す。
- b. 重ね合わせ §5 の「Q2 はこの条件以外の算術を使っていない」を、「稠密さ（S2）はこの条件以外の算術を使っていない。固有値の単純さは 1 次独立を使う（§8）」に直す（XIII 低 6 の残り）。
- c. 低 3 の理由：L40 か索引 5.1 に後注を足す。「第 6 章冒頭の『文献照合は打ち切った』は 16:15 の著者の文面と合う。5.1 の『zbMATH と HKM の本文で』が著者の文面かは、16:38 の原文がリポジトリにないので確かめられない」と書き、著者に確かめる事項に挙げる。L35 の「著者の文面に」の範囲も同じ後注で限る。
- d. 索引 §6 の「著者の確認待ち」に後注を足す。今回生じた確かめる事項 2 件（叩き台 rev 119 に印を入れるか、CLAUDE.md §3 の候補 1 に留保を付けないと明記するか）を挙げ、「なし」と食い違わないようにする。

**極低**
- e. 極低 23 の理由：「足した順に並べる決まり」の出所を書くか、理由を「並べ替えは記録の書き換えに当たるので避ける」などに改める。あわせて、索引 §6 の新しい後注を前からある L29 の後注の後ろに移すか、置き場所の理由を書く。
- f. 射影 §8 T2 の補足の「内容は薄い」を、盲検 P2 の文言どおり「内容がない」にする。
- g. 零点 §3a の「素数の対数の稠密性」を、「正の有理数の対数の集合（素数の対数が生成する群）の稠密性」にする。
- h. 零点 R3 の記号の注の範囲を「このノートの ε(χ)（§2・§3・§4・§7）」に広げる。
- i. 索引 §6 の叩き台の後注に、XIII 極低 18 の 2 点（冒頭の経緯に XII がない、5.1 に選択肢の帰属と「必ず」がない）を書き足す。
- j. L40 の「閉じた記録の範囲の漏れ」の L35 を「D2 の入力・出力・meta」にする（入力が L34 に記録済みなら、そう書く）。L37〜L39 を閉じた項目の指摘に、極低 14 を書き足す。
- k. 重ね合わせ §0 に、直す前の文（「著者の判断で保留中」）を括弧で残し、零点 §4 と同じ扱いにする。
- l. 低 4 の「著者側の作業に挙げない理由」を、台帳 L40 にも 1 行書く。索引 3.1 の後注は、著者の文面の行から別の行に分ける。
- m. 重ね合わせ §8 の単純さの文に、「指数ベクトルの模型（テンソル積の側）では」と添える（任意）。
- n. C1 の 2 つの値がどの量に当たるかを、ログの行の番号で添える（ログを見られなかったので、確かめを促すだけ）。

---

**使ったツールと読んだ範囲**
- 計 13 回：Read 5、ToolSearch 1、`mcp__Claude_Docs__read` 2（草稿 1：現在の版 = rev 52、rev 49）、Bash 5（1 回は解析の失敗で、直して再実行）。ウェブ検索は使っていません。
- 依頼文 `request_XIV.md` と入力 `input_XIV.md` の 1〜823 行（全文）を読みました。
- 草稿 1 は rev 52 と rev 49 を全文取得し、XML を機械で比べました。rev 52 では、変わった 3 段落と、関係する段落（序、1.2、1.4、2.1、3.1、5.1、第 6 章冒頭、6.4、開いている問い）を読みました。2.2〜2.9、4.1、5.2〜5.5 の本文は読んでいません。
- 文書の道具の大きな出力はシステムが /tmp/claude-tool-results/ に保存したので、そこから読みました。計算は /tmp/indep_ledger_XIV/ の中だけで行い、リポジトリには何も書き込んでいません。


### §2b 叩き台（Claude の文書）の rev 119 → 120 は文書の道具の側の変更で、この入力には含めない（突き合わせできない範囲）。

## §3 L42：CLAUDE.md・CLAUDE.en.md の差分（コミット e5b8204）
```diff
diff --git a/CLAUDE.en.md b/CLAUDE.en.md
index ca93006..b242637 100644
--- a/CLAUDE.en.md
+++ b/CLAUDE.en.md
@@ -28,11 +28,11 @@ The purpose of these steps is not to avoid mapping. What is to be prevented is t
   - Do not use the expression "emergence of the line" (直線の創発). When referring to proposition 3, write it by reference as "proposition 3 of §1 (resolution and effective form)," and write in mathematical language what changes and how.
   - **On hold (2026-11-26 20:35, the author's decision)**: "resolution" is on hold, and may be removed from the construction of Ardel projective geometry. Reason: the word "resolution" arose after the conversations with Muse began and was not in the original conception. The items above (proposition 3 and its readings) are kept as a record.
 - Reading of "projective" (interpretive layer, with reservations):
-  - The stage is the projective line P¹ (the inversion swaps 0 and ∞; at the finite level, Parts 19–28 (PAG23–PAG32)). The **composition of gluings** acting on it is what is called projection. The transformation is primary. The gluing means U (the twisted gluing), not `Compat` of PAG23 (an untwisted gluing of coordinates).
+  - The stage is the projective line P¹ (the inversion swaps 0 and ∞; at the finite level, Parts 19–28 (PAG23–PAG32)). The **composition of gluings** acting on it is what is called projection. The transformation is primary. The gluing means U (the twisted gluing), not `Compat` of PAG23 (an untwisted gluing of coordinates). The "projective" of the name refers to the pair of stage and transformation.
   - The builder side's reading (adopted by the author as material, with reservations): that composition is the composition of the inversion (multiplicative side) and the additive transform (additive side), and at the finite level corresponds to J∘H_N/√N of Part 252 (PAG256) (`PAG.Part256.JH`). However, `JH` is a map sending functions on ℤ/N to functions on the units, not an operator on P¹. In the range checked (PAG23, PAG26, PAG27, PAG256) there is no Lean statement connecting JH with the model of P¹ (the whole chain was not searched). What Part 262 (PAG266) connected in Lean is only the value of 𝔀 and the coefficients on P¹.
   - The phase for primitive characters is a component of this composition (transformation).
   - The standard kernel is the Hartley kernel of Part 252 (ratification of the formalization; that it aligns with the content of A1 is the author's judgment, based on a reading of the header comment of PAG256, not checked against the monograph text). Its value is τ(χ)/(i^a√N) (`PAG.Part256.rootNum`, symbol 𝔀; the symbol W(χ) in the docstring and header comment of PAG256 denotes this value too, and is distinct from the inversion W). For primitive characters it is the root number, but that identification is outside Lean (say so explicitly). It differs from the value τ(χ)/√N of the naive kernel e(xy) by a factor i for odd characters; do not smooth over this discrepancy.
-  - The additive characters follow **convention T** (Tate's thesis: ψ_∞(x) = e^{−2πix}, ψ_p(x) = e^{+2πi{x}_p}) as the standard of the founding document. Under convention T, normalizing the idele class character at unramified q by ω_q(q) = χ(q) (under the convention matching χ̄ the product is conjugated), for primitive χ the factor ε(χ) = (−i)^a of the Hartley kernel (`PAG.Part256.parFac`) agrees in value with the local constant ε(1/2, χ_∞, ψ_∞) at the infinite place, and τ(χ)/√N with the product of the local constants at the finite places at s = 1/2 (outside Lean; confidence: high; local constants defined in the manner of Tate 1979). That the explicit factor i^{±a} is the local constant at the infinite place is convention-independent, but whether the sign χ(−1) is placed at the infinite place or the finite places depends on the convention (under the opposite convention the infinite place gives i^a and the product over finite places χ(−1)τ(χ)/√N). Do not write "ε(χ) comes from the infinite place" without stating convention T. A1 remains a postulate. Material: `notes/pag2_projection_material.md`.
+  - The additive characters follow **convention T** (Tate's thesis: ψ_∞(x) = e^{−2πix}, ψ_p(x) = e^{+2πi{x}_p}) as the standard of the founding document. Under convention T, normalizing the idele class character at unramified q by ω_q(q) = χ(q) (under the convention matching χ̄ the product is conjugated), for primitive χ the factor ε(χ) = (−i)^a of the Hartley kernel (`PAG.Part256.parFac`) agrees in value with the local constant ε(1/2, χ_∞, ψ_∞) at the infinite place, and τ(χ)/√N with the product of the local constants at the finite places at s = 1/2 (outside Lean; confidence: high; local constants defined in the manner of Tate 1979). That the explicit factor i^{±a} is the local constant at the infinite place is convention-independent, but whether the sign χ(−1) is placed at the infinite place or the finite places depends on the convention (under the opposite convention the infinite place gives i^a and the product over finite places χ(−1)τ(χ)/√N). Do not write "ε(χ) comes from the infinite place" without stating convention T. A1 remains a postulate. The grounds for adopting convention T: the signs at the finite places match Mathlib's `stdAddChar`, and the additive character is the same as in Burnol (arXiv:math/9811040). Material: `notes/pag2_projection_material.md`; literature check of the convention: `notes/pag2_literature_ia_sign.md`.
   - At the level of operators, U is an operator on the equator (the space of functions on the units; `Lim` in the limit), and it does not extend uniquely to all of P¹ under natural conditions alone (to be written as a property; 2026-11-26, the author's decision).
 - All of the above is the interpretive layer, not formalized theorems. In notes, do not confuse their status.
 
@@ -59,18 +59,20 @@ The purpose of these steps is not to avoid mapping. What is to be prevented is t
 - If structure is needed, cite the literature through the dictionary instead of re-proving it.
 
 **Status of Parts 250–262 (cautions when writing the founding document; details in the index and the notes)**
-- Part 250: what was shown is that "the foundation sits inside ℝ as a dense subset that is totally disconnected but chain-connected at every scale" (the log-coordinate version of a textbook example). "The line appears when the resolution is lowered" was not shown (ℝ appears from the side of completion).
-- Part 251: "dense in the idele class group" is a reading under the identification by the structure theorem C_ℚ ≅ Ẑ^× × ℝ_{>0} (the structure theorem is not in Lean).
+- Part 250: what was shown is that "the foundation sits inside ℝ as a dense subset that is totally disconnected but chain-connected at every scale" (the log-coordinate version of a textbook example). No novelty candidate. "The line appears when the resolution is lowered" was not shown (taking the quotient collapses to one point, ℝ appears from the side of completion, and ℝ is used in the definition from the start).
+- Part 251: "dense in the idele class group" is a reading under the identification by the structure theorem C_ℚ ≅ Ẑ^× × ℝ_{>0} (not in Lean: unitSys ≅ Ẑ^×, universality, compactness and topological-group property of the limit, the structure theorem).
 - The U_N of Parts 252–254 are operators with the phases of A1 put in as a definition; A1 is not derived.
+- Part 259: uniqueness in the odd case with (iii) removed is numerical only. The algebra structure and the isomorphism with the restricted tensor product are outside Lean. The index order is not directed.
+- Part 260: the bundling as a `DirectedSystem` and its limit, that the image is the whole corner (expected), and agreement with the Bost–Connes ρ on the group-ring side (numerical) are outside Lean. That the D side does not lie in the span of shells is numerical apart from the (2,4) witness. The control group was tried only where it corresponds to the stages ℤ/p^e. The reservation of chapter 5, "it does not become an algebra version," is reread as a statement about unit-preserving maps (index 5.5).
 - Part 261: the statement on local units is general theory; what carries the non-unital content is only the absence of a left unit.
 - Part 262: the attribution "the signed form is equation (10) of Long–Pigno–Pinner" was wrong (that equation is an unsigned ratio). No literature writing the signed form has been found.
 - Conclusions weakened in the re-audit of 2026-11-12: literature was checked for 4 of 14 items. "No question remains" means "not found in the range checked" (confidence: medium or lower).
-- Direction β: the route of setting it up as an inductive limit of unit-preserving maps is closed (Part 258; the weak reading, non-unital maps, and other compatibility conditions are outside the answer).
+- Direction β: the route of setting it up as an inductive limit of unit-preserving maps is closed (Part 258; the weak reading, non-unital maps, and other compatibility conditions are outside the answer; systems of coprime stages only are separate).
 - The remaining preregistered candidates K2–K4 have residue that is only computational or empty, and are kept as short-term-layer stock.
 
 ## 4. How to proceed
 
-- The cycle of a part: numerical check in Python → Lean (0 sorry, 0 warnings) → `#print axioms` → note + xlsx. Note titles use "アーデル射影幾何" (Ardel projective geometry).
+- The cycle of a part: numerical check in Python → Lean (0 sorry, 0 warnings) → `#print axioms` → note + xlsx. Note titles use "アーデル射影幾何" (Ardel projective geometry) (the old name "アデール射影幾何 2.0" is not used).
 - Criterion for a new part: does it answer a question in the language of geometry, the global, or limits? Questions internal to the algebra (describing the center, classifying algebras with added generators, etc.) are not made the main subject. Finite-level algebras are used as devices for local computation. State at the top which question of the original path (§1) it serves (if you cannot, do not start).
 - **The four points before starting** (written before Lean; only what has been narrowed to one recommendation is started): (1) write the question in geometric language (points, infinite place, resolution, emergence), (2) the best translation into the language of existing fields (the mapping is obligatory), (3) state the residue that does not vanish under translation (if empty, do not start; if only computational details, a short-term small note), (4) apply a control-group test to the statement of the residue and record the result alongside. In addition, the blind question test and the internal check (§6).
 - **Delegated selection**: the builder side narrows to one recommendation that has passed the gates (four points, blind question test, control-group test), and the start is decided by the author-side Muse. Record what was chosen and why. The author can override at any time.
@@ -100,7 +102,7 @@ Convergence is detected by signs, not by results.
 - Blind question test: before a new question, give only its definitions and statement in the same way and ask "Is this an existing result? Which literature has the answer?" Reflect the answer in the four points before starting (the statement of residue).
 - Conditions for closing a part: a [known / re-derivation / novelty candidate] label on every main result. Novelty candidates carry a search log (terms, sources, scope) and the note that "not found is not a proof of non-existence."
 - Restatement test (every 10–20 parts): have the results restated in the language of existing fields only. If it succeeds, report to the author. Being restatable shows only that "no new concept was needed"; do not treat it as evidence that "there is no new content." The discriminating power of this test alone is weak.
-- Control-group test: for statements with arithmetic or global content, check whether they also hold for the function field F_q(t) (the image of the norm is q^ℤ, and no continuous line appears) and for Beurling generalized primes. Statements that do hold are treated not as arithmetic specific to ℚ but as using only form and density.
+- Control-group test: for statements with arithmetic or global content, check whether they also hold for the function field F_q(t) (the image of the norm is q^ℤ, and no continuous line appears) and for Beurling generalized primes. Done together with the restatement test. Statements that do hold are treated not as arithmetic specific to ℚ but as using only form and density. In particular, statements that hold by the density of the logarithms of primes alone are treated as having no arithmetic content.
 - Report, per part, the number of unfilled dictionary rows and the consecutive count of parts without a literature check. When a threshold is exceeded, propose an audit rather than starting a new part.
 
 **Circle (type 2)**: injecting the target quantity (or information equal to it) as an axiom, weight or phase and reading it back (injection → recovery); treating a condition equivalent to the target as progress (circularity by equivalence); a match of form that is trivial from the construction. Before presenting a result:
@@ -109,14 +111,14 @@ Convergence is detected by signs, not by results.
 3. Equivalence and information content: check that the imposed condition is not equivalent to the target. If claiming a correspondence, compare information content (growth of counts, etc.); if the orders of magnitude do not match, do not claim the correspondence.
 
 **Other types** (only type 1 requires a literature check; the following can be detected by internal checks. Details in the author side's `failure-patterns-audit.md`; not in the repository):
-- Type 3: inflation of claims. Words in prose such as superlatives, "necessarily," "isomorphic," "generated" are matched against the formal statement of the corresponding theorem. A claim for which no formal statement can be written is downgraded or placed as [observation]. Write titles and statements from the formal statements, after the Lean formal statements are settled.
+- Type 3: inflation of claims. Words in prose such as superlatives, "necessarily," "isomorphic," "generated" are matched against the formal statement of the corresponding theorem. A claim for which no formal statement can be written is downgraded or placed as [observation]. A correction table is routine for every part. Write titles and statements from the formal statements, after the Lean formal statements are settled.
 - Type 4: mis-set questions. Compute the obstruction quantities (deficiency indices, invariants, dimension counts) first, and consider the opposite direction (counterexample, non-uniqueness) once.
 - Type 5: boundary cases. Numerics must include degenerate cases (r = 0, p = 2, the smallest modulus, empty sums, trivial characters).
 - Type 6: naive generalization. Search for counterexamples before proving. Keep a standing "counterexample" column in the check table, and widen the search when the words "always" or "necessarily" appear.
 - Type 7: numerical noise. Before calling something a counterexample, estimate the error sources (condition number, cancellation, truncation) and confirm by another method. When judging "not a counterexample," also keep the grounds.
-- Type 8: artifacts of convention. Do not report a "phenomenon" that disappears when conventions or normalizations change.
+- Type 8: artifacts of convention. Before presenting a claim, check that it survives changing normalizations and conventions. Do not report a "phenomenon" that disappears when conventions change as a phenomenon.
 - Type 9: process drift. Check file versions and number correspondences (gaps between design numbers and Lean numbers, drafts coexisting with final versions; the master is the LEAN.zip side; correspondences in the author side's `archive-catalog.md`).
-- Type 10: rhetoric of emergence. "Appeared, generated, connected" must come with which term of which theorem is new. If you cannot say, mark it [observation]. Do not presuppose emergence on the side of the question either.
+- Type 10: rhetoric of emergence. "Appeared, generated, connected" must always come with which term of which theorem is new. If you cannot say, mark it [observation]. Do not presuppose emergence on the side of the question either.
 - Type 11: drift of formal statements. For each main theorem, before writing the note: construct a witness of non-vacuity, search small parameters for counterexamples to the statement with one hypothesis removed at a time, and have another agent that is not shown the note back-translate from the formal statement and definitions alone and compare with the claim.
 - Type 12: internal duplication. Before starting and before closing, run a mechanical duplicate check over the whole chain (including PAG.lean and PAG2–6) (`records/audit_internal/`) and a word search by the names of the objects and constructions used (including Mathlib). The mechanical check cannot catch "the same construction with a different type." Before a new definition, look for a definition with the same formula. Distinguish duplicates as "same statement (A) / follows immediately (B) / close (C)," do not write a C judgment as an established fact, and do not write "not found" as "no duplicate."
 
diff --git a/CLAUDE.md b/CLAUDE.md
index 7c2089d..40c617f 100644
--- a/CLAUDE.md
+++ b/CLAUDE.md
@@ -25,11 +25,11 @@
   - 「直線の創発」という表現は使わない。命題 3 に触れるときは「§1 の命題 3（解像度と有効な姿）」と参照で書き、何がどう変わるかを数学の言葉で書く。
   - **保留（2026-11-26 20:35、著者の決定）**：「解像度」は保留とし、場合によってはアーデル射影幾何の構築から外す。理由：「解像度」は Muse との会話を始めてから生まれた言葉で、当初の構想にはなかった。上の項目（命題 3 とその読み）は記録として残す。
 - 「射影」の読み（解釈の層、留保つき）：
-  - 舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28（PAG23〜PAG32））。その上で働く**貼り合わせの合成**を射影と呼ぶ。主は変換。貼り合わせは U（ねじれた貼り合わせ）を指し、PAG23 の `Compat`（ねじれのない座標の貼り合わせ）ではない。
+  - 舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28（PAG23〜PAG32））。その上で働く**貼り合わせの合成**を射影と呼ぶ。主は変換。貼り合わせは U（ねじれた貼り合わせ）を指し、PAG23 の `Compat`（ねじれのない座標の貼り合わせ）ではない。命名の「射影」は舞台と変換の組を指す。
   - 構築側の読み（著者が留保つきで材料に採用）：その合成は反転（乗法の側）と加法の変換（加法の側）の合成で、有限レベルでは Part 252（PAG256）の J∘H_N/√N（`PAG.Part256.JH`）に当たる。ただし `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。照合した範囲（PAG23・PAG26・PAG27・PAG256）では JH と P¹ のモデルを結ぶ Lean の文はない（鎖全体は検索していない）。Part 262（PAG266）で Lean で結んだのは 𝔀 の値と P¹ の係数だけ。
   - 原始指標についての位相が、この合成（変換）の成分である。
   - 標準の核は Part 252 の Hartley 核（形式化の追認。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは未照合）。値は τ(χ)/(i^a√N)（`PAG.Part256.rootNum`、記号 𝔀。PAG256 の docstring と冒頭のコメントの記号 W(χ) もこの値を指し、反転の W とは別）。原始指標ではルート数だが、その同定は Lean の外（明記する）。素朴な核 e(xy) の値 τ(χ)/√N とは奇の指標で i 倍ずれ、このずれを滑らかにしない。
-  - 加法指標は**規約 T**（Tate の学位論文：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）を基礎文書の標準とする。規約 T のもとで、イデール類指標を不分岐な q で ω_q(q) = χ(q) と正規化して（χ̄ に対応させる規約では積が共役になる）、原始的な χ について、Hartley 核の因子 ε(χ) = (−i)^a（`PAG.Part256.parFac`）は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N は s = 1/2 での有限素点の局所定数の積と値が一致する（Lean の外、確信度：高。局所定数は Tate 1979 の流儀で定める）。明示的な因子 i^{±a} が無限素点の局所定数であることは規約によらないが、符号 χ(−1) を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が i^a、有限素点の積が χ(−1)τ(χ)/√N）。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。A1 は公準のまま。材料は `notes/pag2_projection_material.md`。
+  - 加法指標は**規約 T**（Tate の学位論文：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）を基礎文書の標準とする。規約 T のもとで、イデール類指標を不分岐な q で ω_q(q) = χ(q) と正規化して（χ̄ に対応させる規約では積が共役になる）、原始的な χ について、Hartley 核の因子 ε(χ) = (−i)^a（`PAG.Part256.parFac`）は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N は s = 1/2 での有限素点の局所定数の積と値が一致する（Lean の外、確信度：高。局所定数は Tate 1979 の流儀で定める）。明示的な因子 i^{±a} が無限素点の局所定数であることは規約によらないが、符号 χ(−1) を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が i^a、有限素点の積が χ(−1)τ(χ)/√N）。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。A1 は公準のまま。規約 T を採る根拠は、Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol（arXiv:math/9811040）とも同じ加法指標であること。材料は `notes/pag2_projection_material.md`、規約の文献照合は `notes/pag2_literature_ia_sign.md`。
   - 作用素のレベルでは、U は赤道（単数の上の関数の空間。極限では `Lim`）の上の作用素で、P¹ 全体には自然な条件だけでは一意に延びない（性質として書く。2026-11-26、著者の決定）。
 - 以上は解釈の層であり、形式化済みの定理ではない。ノートではその地位を混同して書かない。
 
@@ -56,18 +56,20 @@
 - 構造が必要なら、再証明せず辞書経由で文献を引く。
 
 **Part 250〜262 の地位（基礎文書に書くときの注意。詳細は索引と各ノート）**
-- Part 250：示せたのは「ℝ の中に基礎が、全不連結だがどの尺度でも鎖でつながる稠密な部分集合として入っている」こと（教科書的な例の対数座標版）。「解像度を落とすと直線が現れる」は示せていない（ℝ は完備化の側から現れる）。
-- Part 251：「イデール類群で稠密」は構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0} の同一視のもとでの読み（構造定理は Lean にしていない）。
+- Part 250：示せたのは「ℝ の中に基礎が、全不連結だがどの尺度でも鎖でつながる稠密な部分集合として入っている」こと（教科書的な例の対数座標版）。新規候補なし。「解像度を落とすと直線が現れる」は示せていない（商を取ると 1 点につぶれ、ℝ は完備化の側から現れるうえ、ℝ は定義に最初から使われている）。
+- Part 251：「イデール類群で稠密」は構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0} の同一視のもとでの読み（Lean にしていないもの：unitSys ≅ Ẑ^×、極限の普遍性・コンパクト性・位相群性、構造定理）。
 - Part 252〜254 の U_N は A1 の位相を定義として入れた作用素で、A1 は導かれていない。
+- Part 259：(iii) を外したときの奇数の場合の一意性は数値のみ。代数構造と制限テンソル積との同型は Lean の外。添字の順序は有向でない。
+- Part 260：`DirectedSystem` としての束ねと極限、像が角全体であること（見込み）、群環の側で Bost–Connes の ρ と一致すること（数値）は Lean の外。D 側が殻の span に入らないことは (2,4) の証人のほかは数値。対照群は ℤ/p^e の段に当たる場合だけ試した。第 5 章の留保「代数版にはならない」は単位元を保つ写像についての文と読み直す（索引 5.5）。
 - Part 261：局所的な単位元の文は一般論で、非単位的という内容を運ぶのは左単位元がないことだけ。
 - Part 262：「符号つきの形は Long–Pigno–Pinner の式 (10)」という帰属は誤り（その式は符号のない比）。符号つきの形を書いた文献は見つかっていない。
 - 2026-11-12 の再監査で弱めた結論：文献で照合したのは 14 件中 4 件。「問いは残らない」は「照合した範囲では見つかっていない」（確信度：中以下）。
-- 方向 β：単位元を保つ写像の帰納極限として立てる道は閉じた（Part 258。弱い読み・非単位的な写像・別の両立条件は答えの外）。
+- 方向 β：単位元を保つ写像の帰納極限として立てる道は閉じた（Part 258。弱い読み・非単位的な写像・別の両立条件は答えの外。互いに素な段だけの系は別）。
 - 事前登録の残候補 K2〜K4 は、残余が計算だけか空であり、短期層の在庫として保持する。
 
 ## 4. 作業の進め方
 
-- パートのサイクル：Python で数値照合 → Lean（sorry 0・警告 0）→ `#print axioms` → ノート＋xlsx。ノートの題名は「アーデル射影幾何」。
+- パートのサイクル：Python で数値照合 → Lean（sorry 0・警告 0）→ `#print axioms` → ノート＋xlsx。ノートの題名は「アーデル射影幾何」（旧称「アデール射影幾何 2.0」は使わない）。
 - 新しいパートの基準：幾何・大域・極限の言葉の問いに答えるか。代数内部の問い（中心の記述、生成元を足した代数の分類など）は主役にしない。有限レベルの代数は局所計算の装置として使う側に回す。冒頭に、本来の道（§1）のどの問いに仕えるかを書く（書けなければ始めない）。
 - **着手前の 4 点**（Lean の前に書き、推薦案として 1 つに絞ったものだけ始める）：(1) 問いを幾何の言葉（点・無限素点・解像度・創発）で書く、(2) 既存分野の言葉への最善の翻訳（写像は義務）、(3) 翻訳しても消えない残余を明示（空なら始めない。計算の細部だけなら短期層の小さいノート）、(4) 残余の文に対照群テストをかけ、結果を併記する。加えて、盲検の問いテストと内部照合（§6）。
 - **選択の委任**：構築側は関門（4 点・盲検の問いテスト・対照群テスト）を通した推薦案を 1 つに絞って出し、着手は著者側 Muse の決定による。何を選び、なぜかを記録する。著者はいつでも覆せる。
@@ -97,7 +99,7 @@
 - 盲検の問いテスト：新しい問いの前に、その定義と文だけを同様に渡し、「既存の結果か。どの文献が答えを持っているか」を聞く。返った答えは着手前の 4 点（残余の明示）に反映する。
 - パートを閉じる条件：主要結果すべてに［既知／再導出／新規候補］のラベル。新規候補には検索ログ（語・先・範囲）と「見つからなかったは不存在の証明ではない」を添える。
 - 言い直しテスト（10〜20 パートごと）：既存分野の言葉だけで言い直させる。成功したら著者に報告する。言い直せることは「新しい概念が要らなかった」ことだけを示し、「新しい内容がない」証拠にはしない。このテスト単独の弁別力は弱い。
-- 対照群テスト：算術的・大域的な内容の文は、関数体 F_q(t)（ノルムの像は q^ℤ で、連続な直線は出ない）と Beurling の一般化素数でも成り立つか確かめる。成り立つ文は ℚ に固有の算術ではなく形式と稠密性だけの文として扱う。
+- 対照群テスト：算術的・大域的な内容の文は、関数体 F_q(t)（ノルムの像は q^ℤ で、連続な直線は出ない）と Beurling の一般化素数でも成り立つか確かめる。言い直しテストに併せて行う。成り立つ文は ℚ に固有の算術ではなく形式と稠密性だけの文として扱う。とくに、素数の対数の稠密性だけで成り立つ文には算術の内容がないものとして扱う。
 - パートごとに、辞書の未記入件数と文献照合の未実施の連続数を報告する。閾値を超えたら、新規パートの開始ではなく監査を提案する。
 
 **円環（第 2 の型）**：目標の量（またはそれと等しい情報）を公理・重み・位相として入れて読み替える（注入→回収）、目標と同値な条件を前進と見る（同値性の循環）、構成から自明な形の一致。成果を出す前に：
@@ -106,14 +108,14 @@
 3. 同値性と情報量：課した条件が目標と同値でないか確かめる。対応を主張するなら情報量（数え上げの増え方など）を比べ、桁が合わなければ対応を主張しない。
 
 **その他の型**（第 1 の型だけが文献照合を要し、以下は内部の照合で検知できる。詳細は著者側の `failure-patterns-audit.md`。リポジトリにはない）：
-- 第 3：主張の格上げ。散文の最上級・必然・同型・生成の語は、対応する定理の形式文と突き合わせる。形式文が書けない主張は格下げするか［観察］に置く。題と主張文は Lean の形式文が確定した後に、形式文から起こして書く。
+- 第 3：主張の格上げ。散文の最上級・必然・同型・生成の語は、対応する定理の形式文と突き合わせる。形式文が書けない主張は格下げするか［観察］に置く。訂正表は各パートの定例とする。題と主張文は Lean の形式文が確定した後に、形式文から起こして書く。
 - 第 4：問いの誤設定。先に障害量（欠損指数、不変量、次元の数え上げ）を計算し、反対方向（反例・非一意性）を 1 回検討する。
 - 第 5：境界ケース。数値に退化ケース（r = 0、p = 2、最小の法、空和、自明指標）を必ず入れる。
 - 第 6：素朴な一般化。証明の前に反例探索。照合表に「反例」の列を常設し、「常に」「必ず」の語が出たら探索範囲を広げる。
 - 第 7：数値ノイズ。反例と言う前に誤差の出所（条件数、桁落ち、打ち切り）を見積もり、別法で確かめる。「反例ではない」と判定した場合も根拠を残す。
-- 第 8：規約の人工物。規約・正規化を変えて消える「現象」は報告しない。
+- 第 8：規約の人工物。主張を提示する前に、正規化・規約を変えても主張が残るか確かめる。規約を変えて消える「現象」は現象として報告しない。
 - 第 9：工程のドリフト。ファイルの版と番号対応を確かめる（設計番号と Lean 番号のずれ、草稿と完成版の併存。正本は LEAN.zip 側、対応は著者側の `archive-catalog.md`）。
-- 第 10：創発の修辞。「現れた・生成した・繋がった」には、新規なのはどの定理のどの項かを添える。書けなければ［観察］。問いの側でも創発を先取りしない。
+- 第 10：創発の修辞。「現れた・生成した・繋がった」には、新規なのはどの定理のどの項かを必ず添える。書けなければ［観察］。問いの側でも創発を先取りしない。
 - 第 11：形式文のずれ。主定理ごとに、ノート作成前に、非空虚性の証人の構成、仮定を 1 つずつ外した文での小さいパラメータの反例探索、ノートを見せない別のエージェントによる形式文と定義だけからの逆翻訳と主張との照合、を行う。
 - 第 12：内部の重複。着手前と閉鎖前に、自分の鎖全体（PAG.lean・PAG2〜6 を含む）の機械的な重複照合（`records/audit_internal/`）と、使う対象・構成の名前による言葉の検索（Mathlib を含む）を行う。機械的な照合は「型の違う同じ構成」を拾えない。新しい定義の前に同じ式の定義を探す。重複は「同じ文（A）／直ちに出る（B）／近い（C）」で書き分け、C の判定を確定した事実のように書かない。「見つからなかった」を「重複はない」と書かない。
 

```

### records/claude_md_slim_check/output_recheck.md（全文）
（統合照合の照合者の出力を、そのまま転記する。2026-11-27 07:03 開始、約 252 秒、ツール 2 回。入力は CLAUDE-history.md と、コミット 90a438f の版の CLAUDE.md。）

# CLAUDE.md の短縮版（新版）と全文の旧版の照合

旧版は 7〜145 行目、新版は 1〜142 行目を読みました。1 つの指示・定義・地位の主張を 1 項目として数えています。旧版の §2 には、旧版の中ですでに後の記述で置き換えられた「次の作業」の指示がいくつかあります（Part 258 の前の監査、Part 259 の方向ラウンド、尾の統合照合を独立の納品物にすること、F2 の後の残件など）。これらは効力がないものとして除きました。

## 1. 欠落・意味が変わった・弱まった・強まった の項目（重い順）

### 影響：高

**H1. 強まった ― 新しいパートを始める条件**
- 旧版：§4 の基準（幾何・大域・極限の問い）、着手前の 4 点、委任を通れば新しいパートを始めてよい。§2 には「Part 259 が第5章の不足を埋めるパートとして実施された」「次は新しいパートではなく辞書の作業である（補足16）」とある。
- 新版：§2「本線は基礎文書…新しいパートは始めない。文書の章の不足を埋めるときだけ走らせる。」
- 旧版にない常設の禁止になり、許される範囲は章の不足を埋める場合だけに狭まりました。

### 影響：中

**M1. 欠落 ― 第 3 の型の訂正表**
- 旧版 §7 第3の型：「訂正表は『作成にあたり』ではなく各パートの定例とする」
- 新版：なし（第 3 の型は形式文との突き合わせと、題・主張文を形式文から書く規則だけ）

**M2. 弱まった ― 第 8 の型の事前確認**
- 旧版：「主張を提示する前に、正規化・規約を変えても主張が残るか確認する。規約を変えて消える『現象』は現象として報告しない」
- 新版：「規約・正規化を変えて消える『現象』は報告しない。」
- 提示の前に確認する手順が消え、報告しないことだけが残っています。

**M3. 欠落 ― Part 260 の結果による第 5 章の読み直し**
- 旧版 §2：「第 5 章の留保『代数版にはならない』は単位元を保つ写像についての文と読み直す（索引 5.5）」
- 新版：なし（§3 の「Part 250〜262 の地位」に Part 260 の項目がない）
- 本線である基礎文書の書き方への指示です。

**M4. 欠落 ― Part 259・260 の「Lean の外」と「数値のみ」の留保**
- 旧版 §2：
  - Part 259：「奇数の場合の一意性は数値のみ」「代数構造と制限テンソル積との同型は Lean の外」「添字の順序は有向でない」
  - Part 260：「`DirectedSystem` としての束ねと極限、像が角全体であること（見込み）、Bost–Connes の ρ との一致（数値）は Lean の外」「D 側は殻の span に入らない（(2,4) の証人、一般には数値）」「対照群は ℤ/p^e の段に当たる場合だけ試した」
- 新版：なし（§3 は「詳細は索引と各ノート」とするだけ）

**M5. 意味が変わった ― 方向 β が閉じた範囲**
- 旧版：「β をこの写像たちの帰納極限として立てる道は…閉じる（弱い読み・単位元を保たない写像・別の両立条件は答えの外。互いに素な段だけの系は別）」
- 新版：「単位元を保つ写像の帰納極限として立てる道は閉じた（…弱い読み・非単位的な写像・別の両立条件は答えの外）」
- 「互いに素な段だけの系は別」という例外が落ち、閉じた範囲が広く読めるようになりました。旧版の Part 259 の無平方数の部分系の帰納系（`sqLim`）は、この例外の側にあたります。

**M6. 弱まった ― Part 250 の地位の留保**
- 旧版：「商を取ると1点につぶれ、ℝ は完備化（ε → 0 の側）から現れるうえ、ℝ は定義に最初から使われている」「新規候補なし」
- 新版：「（ℝ は完備化の側から現れる）」
- 「ℝ は定義に最初から使われている」（円環の型にかかわる留保）と「1点につぶれる」が落ちています。

**M7. 強まった ― 照合者に渡すもの**
- 旧版 §7 の運用の置き場：「検査側に渡すのは形式文と定義だけで、パートの散文…は渡さず」
- 新版 §6：「渡すのは形式文の全文と定義だけで、散文と他の照合者の出力の要約は渡さない。」
- 「全文」と「他の照合者の出力の要約を渡さない」が加わりました。

**M8. 強まった（新しい手続き） ― 判断の経路**
- 旧版：§2 に「二重の経路がずれの原因だった」という診断があるだけで、規則はない。§4 は「何を選び、なぜか」を記録する規則だけ。
- 新版 §4：「判断の経路は 1 つ：このファイルと著者側の申し送りを唯一の記録とする。構築側のセッションで著者が選んだことは、引き継ぎメモに残して著者側へ戻す。」

### 影響：低

**L1. 意味が変わった ― ブート手順 2 で確かめる未完の問い**
- 旧版 §0-2：「本来の道の未完の問い（B-3 の続き、構造定理、Ẑ 上の定理 A、解像度と創発の定式化）を確認する」
- 新版 §0-2：「§2 の現在地を確かめる（最新の引き継ぎメモと `notes/pag2_tail_ledger.md` も）」
- 一覧は消えました。§2 では前の 3 つが既知と判定済み、解像度は保留になっています。

**L2. 意味が変わった ― 辞書の作業**
- 旧版：「合わせて閾値の5件を超えたので、次は新しいパートではなく辞書の作業である（補足16）」
- 新版：「辞書の閾値超え（補足 16）への対応は 2026-11-20 に実施済み（コミット 4357fb4）」
- 指示から完了報告に変わりました。2 つのファイルからは確かめられません。

**L3. 弱まった ― Part 251 で Lean にしていないもの**
- 旧版：「Lean にしていないもの：unitSys ≅ Ẑ^×、極限の普遍性・コンパクト性・位相群性、構造定理」
- 新版：「（構造定理は Lean にしていない）」

**L4. 欠落 ― Part 250〜262 の各パートのラベル**
- 旧版 §2：Part 250・251 は新規候補なし。Part 252〜254 は［再導出］。Part 255〜257 はすべて既知。Part 259 は順序が［既知］、ほかは［再導出（小さい）］。Part 260 は E 側が［既知］、ほかは［再導出（小さい）］。Part 261 は［再導出（小さい）］。Part 262 はガウス和の形が［既知］、残り 4 つが［再導出（小さい）］。
- 新版：なし（「詳細は索引と各ノート」）

**L5. 欠落 ― Part 252 の内容**
- 旧版：「Part 252：主張 U = JH_N の Lean 化」
- 新版：なし（§1 に JH の性質の留保だけがある）

**L6. 弱まった ― 対照群テスト**
- 旧版：「とくに、素数の対数の稠密性だけで成り立つ文には算術の内容がないものとして扱うこと」「言い直しテストに併せて」
- 新版：一般形（「形式と稠密性だけの文として扱う」）だけで、個別の指示と実施の時機がない。

**L7. 欠落 ― 規約 T を採る根拠**
- 旧版：「Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol（arXiv:math/9811040。根拠はこの 1 本）とも同じ加法指標」
- 新版：なし

**L8. 欠落 ― i^a の留保を外した決定**
- 旧版：「i^a を正規化因子として留保する扱いは同日 19:25 の著者の決定で外した」「Part 257（PAG261）の冒頭の説明とノートに読みとして（確信度：中〜高）」
- 新版：なし（確信度は「高」とだけ書かれている）

**L9. 欠落 ― 参照ファイル**
- 旧版：`notes/pag2_literature_ia_sign.md`（規約の文献照合）
- 新版：なし

**L10. 欠落 ― 方向 α**
- 旧版：「方向α（極限の上の商のはしご）は (a)(b) どちらの形でも本線にせず見直す」
- 新版：なし（§2 の経緯の参照に「方向 α・β・γ」と名前があるだけ）

**L11. 欠落 ― 著者の方針の言明**
- 旧版：「著者は『創発に向けて進む』方針を示し」「目的を『新しい幾何を作ること』と確定し」「著者の方針（収束からの離脱）」
- 新版：なし

**L12. 欠落 ― 方向 γ の文献照合**
- 旧版：「γ の文献照合は著者側の作業に切り分けた」「構築側の検索 5 回…確信度：低〜中」
- 新版：なし

**L13. 欠落 ― 棚卸し監査で付いた文献の対応**
- 旧版：定理 2.6 の極限の側に Burnol、unitSys に FLT プロジェクトの ZHat（単数群版の先行は未確認）、有限レベル Bost–Connes に元の BC 系。
- 新版：なし

### 影響：極低

**V1. 欠落 ― 監査の内訳**
- 旧版：残る問い 14 件の内訳（既知 10 件のうち 4 件は未検索で知識による見込み、著者の判断が先 2 件、新規候補 1 件、公理 1 件）
- 新版：なし（「14 件中 4 件」と確信度だけ）

**V2. 欠落 ― 尾の台帳の個別の状態**
- 旧版：「L1〜L10 が閉じ、L11 が次のパートの統合照合に載る」
- 新版：台帳ファイルの参照だけ

**V3. 意味が変わった ― 辞書のファイルの場所**
- 旧版：`terwilliger-dictionary.md`（「結果の再分類表、Part 248 引き継ぎ用挿入文」を含む）
- 新版：`notes/pag2_terwilliger_dictionary.md`
- 同じファイルかどうかは確かめられません。

**V4. 意味が変わった ― 引き継ぎメモの参照**
- 旧版：`PAG2_handoff_part247.md` が「直近の到達点と候補一覧の一次情報」、本文に `PAG2_handoff_part257.md`（08:41 の定義を含む）
- 新版：「`handoff/`（最新は Part 259 の後）」

**V5. 欠落 ― Part 248 の記録**
- 旧版 §5：`part248-*.md` の 3 ファイル、「ker L が部分代数でないという注意も、記録として有効」、主定理 `addEAlg_eq_shellAlg_iff_all`
- 新版：なし（CLAUDE-history の §5 への参照だけ）

**V6. 意味が変わった ― 件数**
- 旧版：3,344／3,371（Part 251 終了時点）と 3,695／3,722 が併存していた。
- 新版：3,695／3,722 の 1 つだけ。

**V7. 弱まった ― 候補 3 の外部使用の禁止（形の上では強まった）**
- 旧版：「文献照合の残り…が済むまで、外部で新規性として使わない」（条件つきの形）
- 新版：「外部（応募書類を含む）で新規性として使わない」（解除条件の記述がない）

**V8. 欠落 ― 候補 3 の根拠の詳細**
- 旧版：初等的な議論（D_N E_N D_N = D_N/N、u = 1 + M/p）、照合した本文（Bastian–Humphries、Watanabe、Kim、WebFetch の要約を通した読み）、近い構造（wreath 積の角、arXiv:2301.08366）、HKM の本文
- 新版：記録ファイルの参照だけ

**V9. 欠落 ― 候補 1 の Terwilliger の言葉での呼び名**
- 旧版：「円分スキームの T(0) の生成系の分類」
- 新版：なし

**V10. 意味が変わった ― W による商の書き方**
- 旧版：「W による商も A1 とは両立するが採らなかった」（過去の決定の記録）
- 新版：「W による商は A1 とは両立するが採らない」（常設の規則）

**V11. 意味が変わった ― 「射影」が指すもの**
- 旧版：「命名の『射影』は舞台と変換の組を指し、主は変換である」
- 新版：「その上で働く貼り合わせの合成を射影と呼ぶ。主は変換。」
- 「組を指す」が明示されなくなりました。

**V12. 欠落 ― 命題 3 の置き方の付記**
- 旧版：決めたのが Muse であること、有限レベル商と Λ 切断が「A8 で分離した2軸」であること、「決まったのは問いの置き場であり、パラメータではない」、08:41 の定義が「上の置き方と矛盾しない」こと
- 新版：なし（置き方そのもの、同一視の禁止、定義の原文は保たれている）

**V13. 弱まった ― 題名の旧称**
- 旧版：「旧『アデール射影幾何 2.0』は使わない」
- 新版：なし（題名の指定だけ）

**V14. 弱まった ― 細かな語と例**
- 第 10 の型の「必ず添える」→「添える」
- 兆候 2 の例（中心は何か、次元はいくつか、いつ全体になるか）
- 兆候 3 の文献照合の定義（名前探し・辞書照合）
- 委任の「取り消し」（新版は「覆せる」だけ）

**V15. 欠落 ― 例と理由**
- 円環の型の実例（Kloosterman、N7、オイラー因子の形）、モノグラフ §5.2 の例示
- 言い直しテストの理由（Lean で書けた定理はすべて言い直せる）
- 第 11 の型の理由（sorry 0 が保証する範囲）
- 第 12 の型の理由（候補選びは上位に限られる）
- §0 の「Terwilliger 代数への同定そのものは前進」

**V16. 欠落 ― その他の小さい記録**
- Part 261：「その証明は素数冪の段を要らない見込み、手計算」
- Part 250：有限の S では外した素数が見えない「有限素点の影」
- Part 249〜256 の内部重複の監査結果（「A・B の組はすべて Lean で確認済み」を含む。新版は CLAUDE-history の §7 を参照）

## 2. 追加の項目（新版にあって旧版にない）

**高**
- **T1. 解像度の保留**（§1）：「『解像度』は保留とし、場合によってはアーデル射影幾何の構築から外す…上の項目（命題 3 とその読み）は記録として残す」。§2 の「解像度の定式化は §1 のとおり保留」も同じ決定です。なお §0-1 には「解像度を決めるパラメータは未決定」の確認が残っています。
- **T2.** H1 の「新しいパートは始めない」（強まったとして上に挙げたもの）

**中**
- **T3. 食い違いの扱い**（冒頭）：「この短縮版と食い違う箇所を見つけたら、作業を止めて著者に報告する」
- **T4. 新しい判断の書き先**（冒頭）：「新しい判断はこのファイルに短く足し、経緯は引き継ぎメモと notes に書く」
- **T5. 作用素のレベルの U**（§1）：「U は赤道（単数の上の関数の空間。極限では `Lim`）の上の作用素で、P¹ 全体には自然な条件だけでは一意に延びない（性質として書く）」
- **T6.** M7（照合者に形式文の全文を渡し、他の照合者の要約を渡さない）
- **T7.** M8（判断の経路は 1 つ）

**低**
- **T8.** §0-2 で尾の台帳 `notes/pag2_tail_ledger.md` も確かめる
- **T9.** §2「残余のある問いは A1 か完備化（無限素点の側）を通るという見立て」と `notes/pag2_partial_inversion_preregistration.md`
- **T10.** §2「草稿 1 が進行中」、CLAUDE-history の §2・§5・§7 への経緯の参照
- **T11.** §7 の参照に加わったもの：`CLAUDE-history.md`、`CLAUDE.en.md`、`CLAUDE-history.en.md`、`notes/pag2_founding_material_index.md`、`records/claude_md_slim_check/`。あわせて、`failure-patterns-audit.md`・`archive-catalog.md` などが「著者側にあってリポジトリにない」ことの明記
- **T12.** §4 の着手前の 4 点に「加えて、盲検の問いテストと内部照合（§6）」と束ねて書いた。旧版でも §7 と第 12 の型 (i) にあった内容です。

**極低**
- **T13.** §1 で rootNum に記号 𝔀 を付けた（旧版では §2 の Part 262 の記述でだけ使われていた）
- **T14.** §3 の「BST 2010」という略記。新版の中では展開されていません（旧版は Bhattacharyya–Song–Tanaka (2010)）。
- **T15.** §1 の末尾「以上は解釈の層」は、旧版の「上記3命題は…解釈の層」より範囲が広く、「射影」の読みと保留まで含みます。

## 3. 「同じ」に分類した項目

合計で約 142 項目です。粒度によって数は前後します。

| 旧版の節 | 内容 | 件数 |
|---|---|---|
| §0 | ブート手順 1・3・4 と目的の文 | 4 |
| §1 | 定義・重なりの読み・命題 3・08:41 の定義・L1・表現の禁止・射影の読み・Hartley 核・規約 T・局所定数の一致・A1 公準・材料ファイル・地位の注意 | 26 |
| §2 | モノグラフ層・定理 2.6 の U の空間・A1 の地位・現在の件数と数え方・番号対応・本線・既知と判定された問い・Part 251 の読み・U_N の注入・Part 261 の一般論・Part 262 の帰属の誤りと Lean で結んだ範囲・兆候 4・再監査で弱めた結論・§3 の書き換えの承認・著者の回答 3 点・作戦の採用・文献照合の状況・K2〜K4 | 19 |
| §3 | Terwilliger の同定と辞書・既知の 5 項目・候補を限る規則・候補 1 の 6 項目・候補 2 の 7 項目・候補 3 の 5 項目・辞書経由で文献を引く | 26 |
| §4 | サイクル・題名・基準・4 点（残余が空・計算の細部の扱いを含む）・委任の 4 要素 | 10 |
| §6 | 禁止事項 | 4 |
| §7 | 兆候 4、仕組み 14、円環 6、独立性と指摘 2、運用の置き場 9、第 3〜12 の型 20 | 55 |
| §8 | `archive-catalog.md`・`what-is-aadel-projective-geometry.md`・`novelty-audit.md`・`failure-patterns-audit.md` | 4 |

§1 の 26 件には、旧版 §2 から移った「Part 262 で Lean で結んだのは 𝔀 の値と P¹ の係数だけ」を含みます。§4 の 10 件には「問いの出所」と「Part n（PAGm）の併記」を含めず、§7 の側で数えています。

## 4. 読めなかった箇所

ありません。2 つのファイルとも全文を読めました（旧版 1〜145 行目、新版 1〜142 行目）。旧版の 37 行目はとても長い行ですが、途中で切れずに表示されました。


### records/claude_md_slim_check/fixes.md（全文）
# 短縮版 CLAUDE.md への直し（照合 output.md を受けて、2026-11-27）

**地位：未照合。** 以下の直しは、この直しを入力に含む照合をまだ受けていない（CLAUDE.md §6 の照合の手続き）。主張を変える直し（[1] で読みの範囲を狭めた、[2]・[5] で規則を強めた側に戻した）を含むため、停止規則により統合照合をもう 1 回だけ行い、その後は停止規則で閉じる。

直した文書：`CLAUDE.md`（正）と `CLAUDE.en.md`（訳、同じ直し）。根拠は `CLAUDE-history.md`（旧版の全文）。出典の文言は grep で旧版と照らした。

## 戻した項目（output.md の番号）

| 番号 | 直し | 置き場 |
|---|---|---|
| [1] | JH の文の範囲の限定（照合した範囲は PAG23・26・27・256、鎖全体は未検索、Part 262 で結んだのは 𝔀 と P¹ の係数だけ）。JH が ℤ/N の関数を単数の上の関数に送る写像であること | §1 射影 |
| [2] | 新規性の主張は §3 の候補に限る | §3 見出し・§5 |
| [4] | 候補 3：N ∣ M の仮定、強い読みの定義、主張の外の問い、存在の側は既知（Hanaki–Kim–Maekawa）、［新規候補（小さい）］、MathSciNet をやめたので条件は満たされないまま、記録ノート | §3 |
| [5] | Hartley 核の留保（形式化の追認、A1 との揃いは著者の判断、モノグラフ本文と未照合）。PAG256 の W(χ) の注記。素朴な核の値 τ(χ)/√N | §1 射影 |
| [6] | 定理 2.6 の U の空間（C_ℚ 上の関数、正則表現の側、Λ 切断の留保）。自己共役拡張・二面体関係 | §2 |
| [7] | 「本来の道」の定義 | §1 冒頭・§4 |
| [8] | §0-3「主役のパートを始めない」と「始める条件」 | §0 |
| [9] | A1 ＝解釈の層の公準（内容は Tate の定理）、U_N は A1 の位相を定義として入れた、Part 250・251・261・262 の注意、再監査で弱めた結論、方向 β の閉鎖、K2〜K4、§3 の書き換えは著者の承認の後、かつての未完の問いの棚卸し | §2・§3 |
| [10] | 依存表の報告条件、桁が合わなければ対応を主張しない | §6 円環 |
| [11] | 閾値超えで監査を提案、言い直しテストの報告と弁別力の弱さ、盲検の問いテストの反映先 | §6 |
| [12] | 第 3・6・7・9・10・11・12 の型の細部 | §6 |
| [13] | 兆候 1：候補と検索範囲を報告、例の語（普遍性・双対性など） | §6 |
| [14] | 辞書の閾値：「埋める」を「埋める調査を提案する」に戻した（強めすぎの解消） | §6 |
| [15] | 規約 T は基礎文書の標準。正規化、ε(χ) = (−i)^a（parFac）、Tate 1979、i^{±a} は規約によらないこと、逆の規約の形、材料ノート | §1 射影 |
| [16] | 地位を混同しない場所を「ノートでは」に戻した | §1 末尾 |
| [17] | W による商は A1 とは両立する（採らない理由は D が降りないこと） | §1 |
| [18] | 著者の造語・PAG の略、制限積の全体、直極限の側、数学の言葉で書く、Compat ではない、合成＝反転∘加法の変換、位相は成分、`Lim`、著者はいつでも覆せる、2026-11-26 の著者の決定 | §1 |
| [19] | 候補 1 の除外・宣言の場所・評価・検索語。かつての候補 2 の確信度・実性との同値・未形式化・近い先行 | §3 |
| [20] | 再照合の時点と組、C の判定、盲検の答えの反映、辞書への記録、結果の併記、件数の数え方、第 1 の型だけが文献照合を要すること、§0-1 の 2 点、§0 の趣旨、「兆候で検出」 | §0・§2・§4・§6 |
| [21] | リポジトリにあるノート 5 件を §7 に追加、リポジトリにない著者側のファイル 6 件を列挙 | §7 |
| A11 | `CLAUDE-history.md` の参照を §2・§5・§7 に（§7 が収束アラームと内部重複の監査） | §2 |

## 戻さなかった項目と理由

- [3] 辞書の閾値超え（補足 16）が次の作業である：2026-11-20 に実施済み（コミット 4357fb4）のため、規則としては戻さず、§2 に実施済みと書いた。
- [9] の一部（Part 255〜257・259・260 の各ラベル、方向 γ の細部）：基礎文書の索引と各ノートにあり、作業者の手順を変えないと判断。§3 の小見出しに「詳細は索引と各ノート」と書いた。
- [20] の Part 248 の主定理名（`addEAlg_eq_shellAlg_iff_all`）と ker L の注意：経緯の記録。旧版 §5 にある。
- [21] Part 248 の数値準備の 3 ファイル：経緯の記録として旧版 §8 に残す。

## 表記

- Part 250 の旧版の文「解像度を落とすと直線が創発する」は、著者の規則（「直線の創発」を使わない）に合わせて「直線が現れる」と書いた。意味は変えていない。

---

# 2 回目：統合照合（output_recheck.md）を受けた直し（2026-11-27 07:1x）

統合照合（停止規則の「もう 1 回だけ」）の結果：高 1、中 8、低 13、極低 16。

**地位：未照合。** 下の直しは照合を受けていない。台帳 L42 に載せ、次の統合照合の入力に含める。

## 戻した項目

| 番号 | 直し |
|---|---|
| M1 | 第 3 の型に「訂正表は各パートの定例とする」 |
| M2 | 第 8 の型に「主張を提示する前に、正規化・規約を変えても主張が残るか確かめる」 |
| M3・M4 | §3 に Part 259・260 の行（Lean の外・数値のみの留保、対照群の範囲、第 5 章の留保の読み直し（索引 5.5）） |
| M5 | 方向 β に「互いに素な段だけの系は別」 |
| M6 | Part 250 に「新規候補なし」「商を取ると 1 点につぶれ」「ℝ は定義に最初から使われている」 |
| L3 | Part 251 の Lean にしていないものの列挙 |
| L6 | 対照群テストの時機（言い直しテストに併せて）と、素数の対数の稠密性だけで成り立つ文の扱い |
| L7・L9 | 規約 T を採る根拠（`stdAddChar`、Burnol）と `notes/pag2_literature_ia_sign.md` |
| V11 | 命名の「射影」は舞台と変換の組を指す |
| V13 | 旧称「アデール射影幾何 2.0」は使わない |
| V14 の一部 | 第 10 の型の「必ず添える」 |

## 直さず著者に判断を返した項目

- **H1（高）・T2**：§2 の「新しいパートは始めない。文書の章の不足を埋めるときだけ走らせる」。旧版に常設の禁止としてはなく、短縮版（af41bd0）で構築側が書いた。著者は短縮版を承認しているが、この文が旧版より強いことは承認の時点で示していなかった。
- **M8（中）・T7**：§4 の「判断の経路は 1 つ」。旧版 §2 の診断（二重の経路がずれの原因）から構築側が規則にした。短縮版の承認で入ったもの。
- **M7（中）・T6**：照合者に「形式文の全文」を渡し「他の照合者の出力の要約」を渡さない。著者の 2026-11-13 以降の指示（構築側の記録にある著者の規則）で、旧版の本文には書かれていなかった。直さない。

## 戻さなかった項目（経緯の記録、旧版に残る）

L1（§2 に現状を書いた）、L2（実施済み、コミットで確かめられる）、L4（各パートのラベル：索引と各ノート）、L5、L8（i^a の留保を外した決定は旧版に残る。現行の確信度は「高」のまま）、L10〜L13、V1〜V10、V12、V14 の残り、V15、V16。


### §3a 参考：短縮版の後に足した CLAUDE.md の差分（e5b8204 → 現在。玩具の 3 行を含む）
```diff
diff --git a/CLAUDE.en.md b/CLAUDE.en.md
index b242637..974e4a2 100644
--- a/CLAUDE.en.md
+++ b/CLAUDE.en.md
@@ -19,6 +19,9 @@ The purpose of these steps is not to avoid mapping. What is to be prevented is t
 - The aim is to build "Ardel projective geometry" (**the original path**). Ardel is short for idele-adele, the author's coinage for a geometry containing the multiplicative ideles and the additive adeles. PAG stands for Projective Adelic Geometry. The name means "fusing adelic geometry and idelic geometry by projection."
 - The points are the primes plus the infinite place. At the infinite place, the infinitely large and the infinitely small overlap.
   - Reading of the "overlap": a **twisted gluing (boundary unitary U)**. The reading of the identification of the two ends as a group quotient is not adopted because it is incompatible with A1 (a cubic character mod 9 is a counterexample). A quotient by W is compatible with A1 but is not adopted either (D does not descend to the quotient).
+  - In the toy (`notes/pag2_toy_origin_buildup.md`), "twisted connection" is read as the rotation of complex character pairs (the rotation, by the A1 phase 𝔀(χ), of the plane obtained by realifying the pair χ, χ̄), not the Möbius-type −1 (the author's choice, 2026-11-27 08:21).
+  - In the toy, the coupling between places (the cross terms) is put on the additive side: the additive character is the global ψ(·/N) (trivial on ℚ), and the local gluing at the point p_i is χ_i(N/N_i)·τ(χ_i)/√N_i (form (I) of PAG261; the same allocation as PAG260 `gaussSum_prodChar` and `stdAddChar_crtMap`) (the author's choice, 2026-11-27 17:37).
+  - In the toy, the window gluing of T0 (f(n+M) = U f(n) on the logarithmic lattice of the infinite place) is read as a boundary condition placed independently at the infinite place: it is not derived from Tate's local operator, and it is not read as a copy of the form at ramified primes (a phase times a translation of width e along the valuation axis) (the author's choice, 2026-11-28 07:13; background in the note §25–§27).
 - The foundation is discrete; continuous objects such as the line do not exist in the foundation.
 - The line is the effective form that emerges when the resolution is lowered.
   - The resolution parameter is **undecided**. Do not identify it with N, K, or Λ.
diff --git a/CLAUDE.md b/CLAUDE.md
index 40c617f..28b7ff3 100644
--- a/CLAUDE.md
+++ b/CLAUDE.md
@@ -16,6 +16,9 @@
 - 目的は「アーデル射影幾何学」の構築（**本来の道**）。アーデル＝イーデルアデールの略で、乗法のイーデルと加法のアデールを含む幾何を指す著者の造語。PAG は Projective Adelic Geometry の略。命名の意味は「アデール幾何とイーデル幾何を射影によって融合する」。
 - 点は素数たち＋無限素点。無限素点では無限大と無限小が重なり合う。
   - 「重なり」の読み：**ねじれた貼り合わせ（境界ユニタリ U）**。両端の同一視を群の商として読む読みは A1 と両立しないため採らない（法 9 の 3 次指標が反例）。W による商は A1 とは両立するが採らない（D が商に降りない）。
+  - 玩具（`notes/pag2_toy_origin_buildup.md`）の「ねじれて繋がる」は、複素指標の組の回転（A1 の位相 𝔀(χ) による、χ と χ̄ の組を実化した面の回転）と読む。メビウス型の −1 ではない（2026-11-27 08:21、著者の選択）。
+  - 玩具で素点どうしの結びつき（交差項）は加法の側に置く：加法指標は大域の ψ(·/N)（ℚ の上で自明）とし、素数 p_i の点の局所の貼り合わせは χ_i(N/N_i)·τ(χ_i)/√N_i（PAG261 の形 (I)。PAG260 `gaussSum_prodChar`・`stdAddChar_crtMap` と同じ割り振り）（2026-11-27 17:37、著者の選択）。
+  - 玩具 T0 の窓の貼り合わせ（無限素点の対数の格子の上の f(n+M) = U f(n)）は、無限素点に独立に置いた境界条件と読む。Tate の局所作用素から導いたものではなく、分岐する素数の形（付値の軸の幅 e の平行移動に位相を掛けたもの）の写しとも読まない（2026-11-28 07:13、著者の選択。経緯はノート §25〜§27）。
 - 基礎は離散的であり、直線のような連続対象は基礎に存在しない。
 - 直線は、解像度を落としたときに創発する有効な姿である。
   - 解像度のパラメータは**未決定**。N、K、Λ のいずれとも同一視しない。

```

## §4 L43：差分（コミット 5b08b10〜661c76a。ノート本体と records/ は除く。ノートは §5 に全文）
```diff
diff --git a/CLAUDE.en.md b/CLAUDE.en.md
index b242637..974e4a2 100644
--- a/CLAUDE.en.md
+++ b/CLAUDE.en.md
@@ -19,6 +19,9 @@ The purpose of these steps is not to avoid mapping. What is to be prevented is t
 - The aim is to build "Ardel projective geometry" (**the original path**). Ardel is short for idele-adele, the author's coinage for a geometry containing the multiplicative ideles and the additive adeles. PAG stands for Projective Adelic Geometry. The name means "fusing adelic geometry and idelic geometry by projection."
 - The points are the primes plus the infinite place. At the infinite place, the infinitely large and the infinitely small overlap.
   - Reading of the "overlap": a **twisted gluing (boundary unitary U)**. The reading of the identification of the two ends as a group quotient is not adopted because it is incompatible with A1 (a cubic character mod 9 is a counterexample). A quotient by W is compatible with A1 but is not adopted either (D does not descend to the quotient).
+  - In the toy (`notes/pag2_toy_origin_buildup.md`), "twisted connection" is read as the rotation of complex character pairs (the rotation, by the A1 phase 𝔀(χ), of the plane obtained by realifying the pair χ, χ̄), not the Möbius-type −1 (the author's choice, 2026-11-27 08:21).
+  - In the toy, the coupling between places (the cross terms) is put on the additive side: the additive character is the global ψ(·/N) (trivial on ℚ), and the local gluing at the point p_i is χ_i(N/N_i)·τ(χ_i)/√N_i (form (I) of PAG261; the same allocation as PAG260 `gaussSum_prodChar` and `stdAddChar_crtMap`) (the author's choice, 2026-11-27 17:37).
+  - In the toy, the window gluing of T0 (f(n+M) = U f(n) on the logarithmic lattice of the infinite place) is read as a boundary condition placed independently at the infinite place: it is not derived from Tate's local operator, and it is not read as a copy of the form at ramified primes (a phase times a translation of width e along the valuation axis) (the author's choice, 2026-11-28 07:13; background in the note §25–§27).
 - The foundation is discrete; continuous objects such as the line do not exist in the foundation.
 - The line is the effective form that emerges when the resolution is lowered.
   - The resolution parameter is **undecided**. Do not identify it with N, K, or Λ.
diff --git a/CLAUDE.md b/CLAUDE.md
index 40c617f..28b7ff3 100644
--- a/CLAUDE.md
+++ b/CLAUDE.md
@@ -16,6 +16,9 @@
 - 目的は「アーデル射影幾何学」の構築（**本来の道**）。アーデル＝イーデルアデールの略で、乗法のイーデルと加法のアデールを含む幾何を指す著者の造語。PAG は Projective Adelic Geometry の略。命名の意味は「アデール幾何とイーデル幾何を射影によって融合する」。
 - 点は素数たち＋無限素点。無限素点では無限大と無限小が重なり合う。
   - 「重なり」の読み：**ねじれた貼り合わせ（境界ユニタリ U）**。両端の同一視を群の商として読む読みは A1 と両立しないため採らない（法 9 の 3 次指標が反例）。W による商は A1 とは両立するが採らない（D が商に降りない）。
+  - 玩具（`notes/pag2_toy_origin_buildup.md`）の「ねじれて繋がる」は、複素指標の組の回転（A1 の位相 𝔀(χ) による、χ と χ̄ の組を実化した面の回転）と読む。メビウス型の −1 ではない（2026-11-27 08:21、著者の選択）。
+  - 玩具で素点どうしの結びつき（交差項）は加法の側に置く：加法指標は大域の ψ(·/N)（ℚ の上で自明）とし、素数 p_i の点の局所の貼り合わせは χ_i(N/N_i)·τ(χ_i)/√N_i（PAG261 の形 (I)。PAG260 `gaussSum_prodChar`・`stdAddChar_crtMap` と同じ割り振り）（2026-11-27 17:37、著者の選択）。
+  - 玩具 T0 の窓の貼り合わせ（無限素点の対数の格子の上の f(n+M) = U f(n)）は、無限素点に独立に置いた境界条件と読む。Tate の局所作用素から導いたものではなく、分岐する素数の形（付値の軸の幅 e の平行移動に位相を掛けたもの）の写しとも読まない（2026-11-28 07:13、著者の選択。経緯はノート §25〜§27）。
 - 基礎は離散的であり、直線のような連続対象は基礎に存在しない。
 - 直線は、解像度を落としたときに創発する有効な姿である。
   - 解像度のパラメータは**未決定**。N、K、Λ のいずれとも同一視しない。
diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
index 92f1c80..f007134 100644
--- a/handoff/PAG2_handoff_part259.md
+++ b/handoff/PAG2_handoff_part259.md
@@ -1800,3 +1800,11 @@
 - **統合照合 XIII（2026-11-26 20:41〜20:54、著者の 20:39「これで進めます」）**：新しいパートを始めない方針で台帳が「次のパートの統合照合」を待ち続けるため、L33・L35〜L39 を独立に 1 回照らした（`records/ledger_XIII/`）。高なし、中 2（零点のノートの対照群の文に「零点は全素点の積に現れる」が残っていた、草稿 1.4 で構築側の読んだ帰結を著者の決定のように書いていた）、低 9、極低 14。直しは草稿 1 を rev 52 に、ノート 3 つ・索引・辞書・英語版・引き継ぎメモ（後注）に入れた。低 3（草稿 5.1・第 6 章冒頭の「打ち切った」）は著者の文面なので直していない。6 件を閉じ、直しは L40（中 1 が主張を狭める直しなので、停止規則のもう 1 回の統合照合 XIV にかける）。
 - **統合照合 XIV（2026-11-26 20:59〜21:04、停止規則のもう 1 回）**：台帳 L40（XIII の後の直し）と草稿 1 rev 52。高なし、中なし、低 4、極低 10。規則により L40 を閉じた。指摘の直し（射影のノートの C3 の留保の範囲の訂正（素数の N でも射影した δ_x は正規直交でない、N = 13 で確認）など）は L41 として次のパートの統合照合に載せる。著者に確かめる事項が 3 件生じた（索引 §6 の後注）：叩き台 rev 119 に 16:38 の印を入れるか、CLAUDE.md §3 の候補 1 に留保を付けないと明記するか、草稿 5.1 の「文献照合は zbMATH と HKM の本文で打ち切ったので」は著者の文面か。開いている台帳は L41 だけ。
   - 著者の回答（2026-11-26 21:11）：(1) 叩き台 rev 119 に印を入れる → 5.1 に入れた（rev 120。ほかの 4 行は MathSciNet をやめた記述だけで有効なので入れていない）。(2) CLAUDE.md §3 の候補 1 に「外部での新規性の留保は付けない（15:5x の決定）」を明記 → 日英に入れた。(3) 草稿 5.1 の「文献照合は zbMATH と HKM の本文で打ち切ったので」は 16:38 の著者の文面 → 変えない。索引 §6 に後注、台帳 L41 に追記。
+- **玩具の原点からの積み上げ（2026-11-27 08:04〜、著者の依頼「原点から積み上げ。Toy setting」、設定「♾️と-♾️と0が射影でねじれて繋がる」、解像度は入れない）**：`notes/pag2_toy_origin_buildup.md`、`records/toy_origin/`。基礎 q^ℤ（離散）、対数で ℤ、窓で両端を貼り合わせ f(n + M) = U f(n)。反転と両立するのは U = ±1 だけ（PAG253 `thm26_full_of_commute` の自明群の場合）。U = −1（メビウス型）では偶な関数が重なりの点で、奇な関数が加法の 0 で消える。単数の座標を足すと、A1 の位相では実の原始指標はすべて 𝔀 = 1（Gauss）で、ねじれは複素指標の組の回転としてだけ現れる。A1 はメビウス型の −1 をどこにも選ばない。すべて［既知］か［再導出（小さい）］。著者の「ねじれ」が組の回転か −1 かは著者の判断待ち。台帳 L43。
+  - 著者の選択（2026-11-27 08:21）：玩具の「ねじれて繋がる」は (A) 複素指標の組の回転（A1 の読み）。CLAUDE.md §1 に 1 行（日英）。段 5：回転角 = 無限素点の 4 分の 1 回転（奇のとき、規約 T）＋各素数の局所の角＋素数どうしの交差項（PAG261 `rootNum_listChar_formII` そのもの）。実の部分は 3 種類の項が打ち消し合って 0 で、交差項の符号は平方剰余の相互法則が決める［既知］。残る問い：素数の点そのもの（p 進の側）は玩具にまだない。台帳 L43 に追記。
+  - 段 6（2026-11-27 17:09〜、著者の選択「1」）：𝔀(χ) は素点ごとの局所定数の積に分かれる（Tate）。局所ゼータ積分を離散化した独立の数値で、標準の ψ では交差項が素数 p_i の局所定数に入り（PAG261 の形 (II)）、ψ(·/N) では形 (I) の因子が局所定数になると確かめた。交差項の置き場所は ψ ↦ ψ(a·) で動く規約の量で、不変なのは積だけ（盲検の指摘で §14 の読みを訂正）。素点どうしの結びつきは大域の有理数の構造が運び、乗法の側と加法の側のあいだで置き場所を移せる（読み、確信度：中）。ψ をどう選ぶかは著者の判断待ち。すべて［既知］。台帳 L43 に追記。
+  - 著者の選択（2026-11-27 17:37）：玩具の素点どうしの結びつきは加法の側（大域の ψ(·/N)）。素数 p_i の点の局所の貼り合わせは χ_i(N/N_i)·τ(χ_i)/√N_i（PAG261 の形 (I)）。PAG260 `gaussSum_prodChar`・`stdAddChar_crtMap` と JH の核 e(xy/N) は同じ割り振りで、既存の構成と食い違わない。帰結：ψ(·/N) は水準で変わり、すべての水準を同時に扱う極限で 1 つにまとまるかは立てていない。CLAUDE.md §1 に 1 行（日英）、ノート §17、台帳 L43 に追記。
+  - 段 7（2026-11-27 18:2x〜、著者の選択「極限の問い」（18:23））：水準ごとの加法指標 ψ_N は埋め込み x ↦ (M/N)x に沿って ℚ/ℤ の 1 つの加法指標 e にまとまる（還元に沿っては両立しない）。e は Tate の加法指標の有限部分が 𝔸_f/Ẑ ≅ ℚ/ℤ を通じて誘導するもの（規約 T）。§17 の ψ(·/N) と標準の ψ の違いは座標 x ↦ x/N だけ。単数の側では水準の核 J∘H_N/√N は f < N の指標で常に W(χ*) と違い（μ(N/f)χ*(N/f)√(f/N)W(χ*)、Montgomery–Vaughan 9.10）、両立する族の一意性は PAG258 `UA1_family_unique` の仮定 hT・hc で正しい形。交差項に不変な内容はない。すべて既知、新規候補なし。ノート §18〜§20、`records/toy_origin/stage7/`。台帳 L43 に追記。照合は盲検だけ。
+  - 段 8（2026-11-27 18:4x〜、著者の選択「§20」（18:42））：U_∞ = ε_∞·Σ_f (φ(f)/√f)·J R_f A P_f（A は Ẑ^× の上の関数を ℚ/ℤ の上の関数に送る加法の変換、R_f は軌道 O_f の読み出し、P_f は導手の射影）と書けるが、ガウス和の定義の書き直し（構成から自明な形の一致）で新しい内容はない。水準の核は A を O_N で読んだもの。殻ごとに n^{−s} で足すと f^{−s}τ/√f / L(s+1/2)（既知の帰結）。構築側の見立て（M5 の殻ごとの割り当て）は誤りだった。新規候補なし。ノート §21〜§23、`records/toy_origin/stage8/`。台帳 L43 に追記。照合者は CLAUDE.md が文脈に入っていたと申告（このリポジトリで起動したエージェントの盲検は条件が完全ではない）。
+  - 段 9（2026-11-27 19:2x〜、著者の指示「進めてください」（19:17）、§16・§23 の問い）：素数 p の点の J_p∘F_p は、分岐していれば付値の軸の上で 0 の側への幅 e（導手の指数）の平行移動に位相 τ(χ)/p^{e/2} を掛けたもの（固有値はなく、一般化固有ベクトルは Floquet–Bloch 型）。不分岐なら γ 因子 L(1−s, ω̄)/L(s, ω) を記号とするローラン作用素。交差項は記号への代入の値（ホロノミーの語は使わない）。平行移動か否かは L 因子が自明か否かで分かれ、無限素点は平行移動ではない。すべて既知（Tate、Burnol、Rohrlich）、新規候補なし。ノート §24〜§26、`records/toy_origin/stage9/`。台帳 L43 に追記。玩具 T0 の窓を Tate の作用素の側からどう位置づけるかは著者の判断事項として §26 に挙げた。
+  - 著者の選択（2026-11-28 07:13）：玩具 T0 の窓の貼り合わせは「無限素点に独立に置いた境界条件」と読む（Tate の局所作用素から導いたものでも、分岐する素数の形の写しでもない）。CLAUDE.md §1 に 1 行（日英）、ノート §27。帰結：窓の幅 M は自由なパラメータのまま、位相は選択 (A) の A1 の位相で入力。素数の点の局所作用素（計算したもの）とは地位が違い、両者の値の一致を担うのは A1（解釈の層）。
diff --git a/notes/pag2_tail_ledger.md b/notes/pag2_tail_ledger.md
index f4a5e1c..260080b 100644
--- a/notes/pag2_tail_ledger.md
+++ b/notes/pag2_tail_ledger.md
@@ -4,6 +4,20 @@
 
 ## 開いている項目
 
+### L43：玩具「∞ と −∞ と 0 が射影でねじれて繋がる」の原点からの積み上げ（2026-11-27 08:1x、新しい材料）
+
+- 著者の依頼（08:04）と設定の回答による。新しいノート `notes/pag2_toy_origin_buildup.md` と `records/toy_origin/`（`toy_check.py` とログ）。新しいパートではなく短期層の小さいノート。解像度は使わない。
+- 引き継ぎメモに 1 行。
+- 基礎文書の本文・索引・CLAUDE.md は変えていない。
+- 追記（2026-11-27 08:2x、著者の選択 (A)（08:21）を受けて）：ノートの §11 に選択の後注、§12（段 5：回転角の分解。PAG261 `rootNum_listChar_formII` の言い直し、実の部分の打ち消しと相互法則）と §13（残る問い）を足した。`records/toy_origin/toy_stage5.py` とログ。CLAUDE.md §1 の「重なり」の読みの下に、玩具の「ねじれて繋がる」は組の回転と読む旨の 1 行（2026-11-27 08:21、著者の選択）を足し、英語版にも同じ文。引き継ぎメモに 1 行。照合は受けていない。
+- 追記（2026-11-27 17:3x、著者の選択「1」（17:09）を受けて）：ノートに §14（段 6 の事前登録の 4 点）・§15（段 6 の結果：素点ごとの分解、交差項の置き場所は ψ の取り方で動く。盲検の指摘で §14 の読みと対照群の文を訂正）・§16（残る問い）を足した。`records/toy_origin/stage6/`（依頼文、盲検の出力・meta、`local_eps.py`・`local_eps_psiN.py` とログ）。引き継ぎメモに 1 行。照合は受けていない。
+- 追記（2026-11-27 17:4x、著者の選択「加法側で」（17:37）を受けて）：CLAUDE.md §1 に玩具の取り決め（結びつきは加法の側、ψ(·/N)、形 (I)）の 1 行（日英）。ノートの §16 に後注、§17（取り決めと帰結：既存の PAG260 の割り振りと同じ、ψ(·/N) は水準によって変わる）を足した。引き継ぎメモに 1 行。照合は受けていない。
+- 追記（2026-11-27 18:4x、著者の選択「極限の問い」（18:23）を受けて）：ノートに §18（段 7 の事前登録の 4 点）・§19（段 7 の結果と訂正表）・§20（残る問い）を足した。`records/toy_origin/stage7/`（依頼文、`limit_check.py` とログ（盲検の後に (e) を追加）、盲検の出力と meta）。盲検の指摘で依頼文の L2・L3・L5 の文を直した（§19 の訂正表）。L3 の一意性の正しい形は PAG258 `UA1_family_unique` の仮定と同じ。盲検の出力は最初の返信をファイルに残す前に文脈が切り替わったため、同じエージェントへの「一字も変えずに再送」の依頼で得た（出力ファイルの冒頭に記載）。新規候補なし。引き継ぎメモに 1 行。
+- 追記（2026-11-27 19:0x、著者の選択「§20」（18:42）を受けて）：ノートに §21（段 8 の事前登録の 4 点）・§22（段 8 の結果と訂正表）・§23（残る問い）を足した。`records/toy_origin/stage8/`（依頼文、`shell_check.py` とログ、盲検の出力と meta）。盲検の指摘で §21 の見立ての 4 か所を直した（A と単数の作用の絡み方、χ̄*、U_∞ の式は作用素としては導手の射影が要りガウス和の定義の書き直し（構成から自明な形の一致）、M5 の殻ごとの割り当ては誤り）。新規候補なし。照合者は CLAUDE.md が文脈に入っていたと申告した（盲検の条件は完全ではない。§22 の冒頭）。引き継ぎメモに 1 行。
+- 追記（2026-11-27 19:4x、著者の指示「進めてください」（19:17）を受けて）：ノートに §24（段 9 の事前登録の 4 点）・§25（段 9 の結果と訂正表）・§26（残る問い）を足した。`records/toy_origin/stage9/`（依頼文、`padic_axis.py` とログ（盲検の後に (g) を追加）、盲検の出力と meta）。盲検の指摘で §24 の見立てを直した（固有ベクトルの向きと ℓ² でないこと、ホロノミーは名前の付け替え、大域の対数の軸の符号、対比は L 因子が自明か否か）。新規候補なし。照合者は CLAUDE.md が文脈に入っていたと申告した（段 8 と同じ条件）。引き継ぎメモに 1 行。
+- 追記（2026-11-28 07:1x、著者の選択「無限素点に独立に置いた境界条件」（07:13）を受けて）：CLAUDE.md §1 に 1 行足した（日英）。ノートの §26 に後注、§27（選択と帰結。解釈の層の整理で、新しい数学の主張はない）を足した。引き継ぎメモに 1 行。
+- 扱い：照合は受けていない。次のパートの統合照合に載せる（著者が求めれば独立の照合にかける）。
+
 ### L42：短縮版 CLAUDE.md の統合照合の後の直し（2026-11-27 07:1x）
 
 - 範囲：短縮版の網羅性の統合照合（`records/claude_md_slim_check/output_recheck.md`）の指摘を受けた CLAUDE.md・CLAUDE.en.md の直し（M1〜M6、L3、L6、L7、L9、V11、V13、V14 の一部）。一覧は `records/claude_md_slim_check/fixes.md` の 2 回目の節。

```

## §5 玩具のノート `notes/pag2_toy_origin_buildup.md`（現在の全文）
# アーデル射影幾何 — 玩具「∞ と −∞ と 0 が射影でねじれて繋がる」の原点からの積み上げ

（2026-11-27 08:1x、構築側。著者の依頼「アーデル射影幾何学について、原点から積み上げ。Toy setting」（08:04）と、設定の問いへの著者の回答「♾️と-♾️と0が射影でねじれて繋がる」、出力は「リポジトリのノート」、保留中の「解像度」は「入れない」による。新しいパートではなく短期層の小さいノート。Lean は使わない。照合は受けていない。）

## 0. 地位・読み・使うもの

- **地位**：§1 の定義から組む玩具の積み上げで、新しい数学の主張はない。各段の文はすべて［既知］か［再導出（小さい）］（§7 の表）。玩具の文と著者の定義（解釈の層）を書き分ける。
- **玩具の設定の読み**：著者の回答「∞ と −∞ と 0 が射影でねじれて繋がる」を、2026-11-16 に確認した読みで受ける。対数で乗法の 0・∞ が加法の −∞・+∞ に対応し、その両端を貼り合わせ U で重ねる（「ねじれて」＝ねじれた貼り合わせ U、CLAUDE.md §1）。この読みは構築側が当てたもので、著者はいつでも直せる。
- **使う定義**（CLAUDE.md §1）：点は素数たち＋無限素点。無限素点では無限大と無限小が重なり合い、その重なりはねじれた貼り合わせ（境界ユニタリ U）。基礎は離散。「射影」は舞台 P¹ とその上で働く貼り合わせの合成。
- **使わないもの**：「解像度」（2026-11-26 20:35 の著者の決定で保留）と命題 3。A1 は §5 で入力として使い、導かない（公準のまま）。

## 1. 段 0：基礎（離散）と、乗法と加法の対応

- 基礎を、1 つの数 q > 1 が生成する乗法の格子 X = q^ℤ = {q^n : n ∈ ℤ} に置く（離散。連続対象は使わない）。
- 対数 n = log x / log q で X は加法の格子 ℤ になる。対応は次のとおり。
  - 乗法の 0（n → −∞ の側）↔ 加法の −∞
  - 乗法の ∞（n → +∞ の側）↔ 加法の +∞
  - 乗法の 1 ↔ 加法の 0
- 反転 W：x ↦ 1/x は、加法では n ↦ −n。乗法の 0 と ∞（加法の −∞ と +∞）を入れ替え、乗法の 1（加法の 0）を固定する。

## 2. 段 1：舞台と貼り合わせ（両端を重ねる）

- 両端を重ねるために、長さ M = 2L の窓 n ∈ {−L, …, L − 1} をとり、関数に次の条件を課す（窓の外へは条件で延ばす）：

  f(n + M) = U f(n)、|U| = 1。

- 窓の端 n = L と n = −L は同じ点になる（f(L) = U f(−L)）。この点で、乗法の 0 と ∞、加法の −∞ と +∞ が 1 点に重なる。これが §0 の読みの「−∞ と ∞ と 0 が重なる」の玩具での形で、重なり方の位相が U である。
- 窓は貼り合わせのための切断で、モノグラフ層の Λ 切断と同じ役割（境界条件が意味を持つのは切断があるから。CLAUDE.md §2 の定理 2.6 の留保）。**解像度ではない**（解像度は使わない、§0）。
- 舞台との関係：重ねた後の格子は円（ℤ/M）で、反転は円の上で 2 つの固定点 n ≡ 0（加法の 0）と n ≡ L（重なりの点）を持つ。射影直線 P¹ の反転が 0 と ∞ の 2 点を入れ替え、±1 を固定するのとは、固定点の役割が違う（P¹ の 0・∞ は入れ替えられる 2 点、ここでの 0・∞ は固定される 2 点）。玩具の円と P¹ のモデル（PAG23〜PAG32）を結ぶ文は立てていない（CLAUDE.md §1 の「JH と P¹ のモデルを結ぶ Lean の文はない」と同じ留保）。

## 3. 段 2：反転と両立する貼り合わせは U = ±1 だけ（T0.1）

- 文：(Jf)(n) = f(−n) は、条件 f(n + M) = U f(n) の空間を、条件 f(n + M) = U⁻¹ f(n) の空間に写す。したがって J がこの空間を保つのは U = U⁻¹、すなわち U = ±1 のときに限る。
- 証明：g = Jf とすると g(n + M) = f(−n − M) = U⁻¹ f(−n) = U⁻¹ g(n)。
- ラベル：［既知］（ねじれた境界条件と反転。モノグラフの定理 2.6 の、単数の座標がない場合）。鎖では PAG253 の `thm26_full_of_commute` を自明群に当てた場合で、実の指標の符号の文 c = ±1 に当たる（重複の B：直ちに出る）。
- **ねじれた貼り合わせ** U = −1 は、実射影直線の上のメビウスの帯（同語反復の直線束）の切断、すなわち反周期関数の玩具版［既知］。
- 数値（§8）：M = 6・8・10 で、U = ±1 では J のずれは 0、U = e^{iπ/3}・i ではずれが 5〜6.6（保たない）。

## 4. 段 3：ねじれの帰結（T0.2・T0.3）

- **T0.2（節の型）**：反転の 2 つの固定点 n ≡ 0（加法の 0）と n ≡ L（重なりの点）での値。
  - U = +1：J で偶な関数は両方で自由、奇な関数は両方で 0。
  - U = −1：J で偶な関数は重なりの点で 0、奇な関数は加法の 0 で 0。
  - 証明（U = −1、偶）：f(L) = f(−L)（偶）と f(L) = U f(−L) = −f(−L)（貼り合わせ）から f(L) = 0。奇なら f(0) = −f(0) から f(0) = 0、重なりの点では f(L) = −f(−L) が 2 つの条件で同じになり制約がない。
  - 読み（解釈の層、構築側）：ねじれた貼り合わせでは、加法の 0 と重なりの点（乗法の 0・∞）の役割が偶奇で入れ替わる。ねじれのない貼り合わせでは、2 点は同じ役割を持つ。
  - ラベル：［既知］（反周期境界条件のパリティの標準的な計算）。
- **T0.3（不変なベクトル）**：平行移動 T f(n) = f(n + 1)（乗法では q 倍）の固有値 ζ は ζ^M = U を満たす。U = −1 では ζ = 1 がなく、平行移動で不変な関数（定数）は貼り合わせの空間にない。ラベル：［既知］。
- 数値（§8）：M = 6・8・10 で節の型は上のとおり。偶・奇の部分空間の次元は U = +1 で (L + 1, L − 1)、U = −1 で (L, L)。T の固有値と 1 の最小の距離は U = +1 で 0、U = −1 で 0.518・0.390・0.313（= 2 sin(π/(2M))）。

## 5. 段 4：単数の座標を足す（T1）—ねじれは指標の組の回転として現れる

- 点に素数たちの単数の側を足す玩具：関数を K × ℤ（K = (ℤ/N)^×）の上に置き、f(k, n + M) = (U f(·, n))(k)（U は L²(K) のユニタリ）、反転を (k, n) ↦ (k⁻¹, −n) とする。
- **両立の分類**：U が K の平行移動と可換なら U は指標で対角（U = Σ e^{iα_χ} P_χ）で、反転と両立するのは α_χ̄ = −α_χ のとき、そのときに限る。実の指標では e^{iα_χ} = ±1。ラベル：［既知の帰結］（モノグラフの定理 2.6 の有限版。鎖では PAG253 の `thm26_full`：c(χ⁻¹) = conj c(χ)、実指標では c = ±1。CLAUDE.md §3 のかつての候補 2 の記述）。
- **A1 の位相を入れる**：原始指標 χ に e^{iα_χ} = 𝔀(χ) = τ(χ)/(i^a√N)（`PAG.Part256.rootNum`。原始指標ではルート数で、その同定は Lean の外）。A1 は公準で、ここでは入力（依存表 §6）。
  - |𝔀(χ)| = 1（鎖：PAG256 の `normSq_rootNum`）、𝔀(χ̄) = conj 𝔀(χ)（定理 2.6 の条件を満たすこと。CLAUDE.md §3：PAG16・PAG173・PAG198 から出る、組み合わせた 1 つの文は未形式化）。
  - **実の原始指標ではすべて 𝔀(χ) = 1**（数値 §8、N = 3〜21 の実の原始指標 11 個。理由は二次のガウス和の符号の定理：偶なら τ = √N、奇なら τ = i√N。Gauss の定理［既知］）。
  - 自明群の場合（N = 1、T0 に当たる）も、ζ のルート数は 1 で、A1 は U = +1 を選ぶ。
- **したがって A1 のもとでは、メビウス型のねじれ U = −1 はどこにも現れない**（原始的な実の部分と自明な部分では U = +1）。ねじれ（非自明な位相）は複素指標の組 (χ, χ̄) にだけあり、位相は互いに逆（α と −α）。
- **実化**：χ と χ̄ の組は実の 2 次元の面（Re χ と Im χ が張る）になり、U はその面の回転として働く（回転角の大きさは |arg 𝔀(χ)|、向きは基底の取り方による）。読み（解釈の層、構築側）：A1 のもとで「ねじれて繋がる」の中身は、重なりの点を通るたびに各組の面が角 arg 𝔀(χ) だけ回ること。ラベル：［再導出（小さい）］（実性（反転の条件は境界ユニタリの実性と同値、CLAUDE.md §3）からの短い帰結）。

## 6. 依存表（円環の検知、CLAUDE.md §6 第 2 の型）

| 文 | 入力 | 除去テスト |
| --- | --- | --- |
| T0.1〜T0.3 | 貼り合わせの条件、反転の定義 | 入力は定義だけ。U は自由な媒介変数で、反転が ±1 に絞る |
| T1 の両立の分類 | K の平行移動との可換、等長、反転の条件 | 反転の条件を外すと α_χ は自由に戻る |
| 位相 𝔀(χ)、実の部分で 1、組の回転角 | A1（公準）、ガウス和 | A1 を外すと位相は自由に戻る（CLAUDE.md §6 の例）。「実の部分でねじれない」は A1 の帰結で、玩具の幾何からは出ない |

## 7. ラベルの表

| 文 | ラベル | 鎖・文献 |
| --- | --- | --- |
| T0.1 反転と両立 ⇔ U = ±1 | ［既知］ | PAG253 `thm26_full_of_commute` の自明群の場合（重複の B） |
| U = −1 ＝ メビウスの帯の切断 | ［既知］ | 標準的な事実 |
| T0.2 節の型、T0.3 不変なベクトルの有無 | ［既知］ | 標準的な計算 |
| T1 の両立の分類 | ［既知の帰結］ | PAG253 `thm26_full` |
| 実の原始指標で 𝔀 = 1 | ［既知］ | 二次のガウス和の符号（Gauss）。鎖に該当する 1 つの文は見つからなかった（言葉の検索：rootNum・real・conj・one。網羅ではない） |
| 組の実化での回転 | ［再導出（小さい）］ | 実性からの短い帰結 |

新規候補はない。

## 8. 数値（`records/toy_origin/toy_check.py`、ログ `toy_check.log`）

- numpy だけ。T0 は M = 6・8・10、U = +1・−1・e^{iπ/3}・i。T1 は N = 2〜21 の 14 個の法（原始指標のない N = 2・6 を含む。N = 1 は自明群として対象外）。
- T0：§3・§4 のとおり（両立のずれは U = ±1 で 0）。
- T1：|𝔀| − 1 の最大 4.4×10⁻¹⁵、𝔀(χ̄) − conj 𝔀(χ) の最大 5.4×10⁻¹⁵。実の原始指標の 𝔀 はすべて +1.000（N = 3・4・5・7・8（2 個）・11・12・13・20・21）。複素の組の角 arg 𝔀/π は ±0.093〜±0.722（N = 5 で ±0.176、N = 13 で 5 組）。N = 9・16 は実の原始指標がない。
- 実化：N = 5・13 の組の行列は実（虚部 0）の回転行列で、回転角の大きさは |arg 𝔀| と一致した（向きは逆。基底の取り方による）。
- 地位：数値は既知の事実の確認で、証明ではない（CLAUDE.md §5）。

## 9. 対照群（CLAUDE.md §6）

- **T0 は関数体の玩具そのもの**：基礎 q^ℤ は、関数体 𝔽_q(t) のノルムの像 q^ℤ と同じ形である。T0.1〜T0.3 は形と反転だけを使い、ℚ に固有の算術を使わない（形だけの文）。ℚ の無限素点のノルムの像は ℝ_{>0} で離散でないが、玩具は基礎が離散という定義に合わせて q^ℤ を選んだ。
- **T1**：関数体の指標とガウス和でも、両立の分類（α_χ̄ = −α_χ）は同じ形で成り立つ（形だけ）。パリティの因子 i^a（無限素点の局所定数、規約 T）は関数体にはない。関数体の二次指標のルート数が 1 かどうかは確かめていない。
- 結論：玩具の文のうち ℚ に固有なのは、A1 の位相に入るパリティの因子だけ（それも A1 の入力）。

## 10. 内部照合（第 12 の型）

- 言葉の検索：thm26・globalInv・rootNum・normSq_rootNum・conj。該当：PAG253 `thm26_full_of_commute`・`thm26_full`・`globalInv`（(k, u) ↦ (k⁻¹, −u)。T1 の反転と同じ式）、PAG256 `rootNum`・`normSq_rootNum`、PAG257 `normSq_rootNum_one_prime`、PAG266 `conj_Jhat_eq_rootNum`。
- 格子 ℤ の上の擬周期の条件 f(n + M) = U f(n) を定義した宣言は見つからなかった（モノグラフ層は連続の区間で境界条件を課している。網羅ではない）。

## 11. 残る問い（幾何の言葉で）

- メビウス型のねじれ（U = −1）は反転と両立するが、A1 は原始的な実の部分にも自明な部分にもそれを選ばない。著者の「ねじれて繋がる」が、複素指標の組の回転（A1 の読み）を指すのか、メビウス型の −1 を指すのかは、著者の判断を待つ。（後注 2026-11-27 08:21、著者の選択：(A) 複素指標の組の回転（A1 の読み）。メビウス型の −1 ではない。CLAUDE.md §1 に 1 行足した。玩具は A1 の位相のまま §12 へ進めた。）−1 のルート数は、ディリクレの L の外（楕円曲線の L など）では現れるが、この玩具の設定の外である。
- 玩具の円（ℤ/M、固定点 0 と重なりの点）と舞台 P¹（0 と ∞ を入れ替える）の関係：§2 のとおり、固定点の役割が違う。射影の読み（舞台 P¹ の上の貼り合わせの合成）を玩具にどう載せるかは、立てていない。

## 12. 段 5：回転角の分解（無限素点・各素数・素数どうしの交差）

（2026-11-27 08:2x、著者の選択 (A)（08:21）を受けて。短期層の続き。照合は受けていない。）

- **文**：互いに素な法 N_1, …, N_k の原始指標 χ_i の積 χ について（規約 T）、

  𝔀(χ) = ε_∞(χ) · ∏_i (τ(χ_i)/√N_i) · ∏_i ∏_{j≠i} χ_j(N_i)、ε_∞(χ) = (−i)^a。

  角で書くと（mod 2π）、θ(χ) = θ_∞ + Σ_i θ_i + Σ_{i≠j} arg χ_j(N_i)。θ_∞ = −aπ/2 は無限素点の寄与、θ_i = arg τ(χ_i)/√N_i は素数 p_i（の冪の法）ごとの局所の角、最後の和は「素数 p_i の成分の指標を、別の素数の法 N_j で測った値」という素数どうしの交差項。
- **鎖**：PAG261 `rootNum_listChar_formII`（Lean、sorry 0）がこの式そのもの（重複の A：同じ文）。2 成分の場合は PAG260 `rootNum_prodChar`。ε_∞ の符号の規則は PAG261 の「∞ の因子の符号」（ε_∞(χ) = (−1)^{k(k−1)/2}·∏ ε_∞(χ_i)、k は奇の成分の数）。
- **読み（解釈の層、構築側）**：玩具の重なりの点で χ と χ̄ の組の面が回る角は、無限素点の 4 分の 1 回転（奇の指標のとき）、各素数の局所の角、素数どうしの交差の角の和である。各素点の項の分け方が素点ごとの局所定数（Tate の流儀）に当たるかは Lean の外で、交差項が各素点の局所定数のどこに入るか（ω_p の一意化元での値）はこのノートでは確かめていない（確信度：中）。
- **実の部分がねじれない理由**：実の原始指標では、3 種類の項が打ち消し合って θ = 0 になる（数値）。
  - 法 15（成分のパリティ 奇・偶）：θ_∞ = −π/2、局所 +π/2、交差 0。
  - 法 21（奇・奇）：θ_∞ = 0、局所 π（i·i = −1）、交差 π（(7/3)(3/7) = −1）。
  - 法 105（奇・偶・奇）：θ_∞ = 0、局所 π、交差 π。
  - 交差項の符号は平方剰余の相互法則が決める（2 つの奇素数がともに 4 を法として 3 のとき (p/q)(q/p) = −1）。「実の部分はねじれない」（二次のガウス和の符号）と相互法則は、ガウス和による相互法則の古典的な証明で結びついている［既知］。
- **規約の確認（第 8 の型）**：逆の規約（無限素点 i^a、有限素点の積 χ(−1)τ(χ)/√N）では無限と有限の分け方が変わるが、和は同じ（数値で差 10⁻¹⁵ 以下）。無限素点の寄与を「4 分の 1 回転」と言えるのは規約を明示したときだけ（CLAUDE.md §1）。
- **ラベル**：分解の式は［再導出］（鎖に同じ文がある。Lean）。実の部分での打ち消しと相互法則との関係は［既知］。新規候補はない。
- **対照群**：関数体でも、互いに素な法のガウス和の分解（交差項つき）と二次の相互法則（関数体版）は成り立つ（形だけ。確かめていない、既知の見込み、確信度：中）。ℚ に固有なのは θ_∞（無限素点のパリティの因子）だけで、これは A1 の入力の中にある。
- **数値**（`records/toy_origin/toy_stage5.py`、ログ `toy_stage5.log`）：法の組 3·5、3·7、4·5、5·7、3·5·7、4·3·5 の原始指標（3・5・3・15・15・3 個）で、分解の和と arg 𝔀 の差の最大は、両規約で 3.6×10⁻¹⁵ 以下。実の原始指標は各組で 1 個ずつ（合計 6 個）、いずれも合計の角 0。数値は証明ではない（Lean の文は PAG261）。

## 13. 段 5 の後に残る問い（幾何の言葉で）

- 玩具の円は無限素点の対数の格子を閉じたもので、有限素点は単数の座標（指標）としてだけ入っている。素数 p の点そのもの（p 進の側の幾何）は玩具にまだない。各素数の局所の角 θ_i を、その素数の点の上の貼り合わせとして読めるか（各素点に貼り合わせを持たせる形にするか）は、立てていない。
- 交差項は「ある素数の指標を別の素数の法で測る」項で、素点どうしの結びつきを運ぶ。これを玩具の幾何（点どうしの関係）として書くかどうかは、著者の判断を待つ。

## 14. 段 6 の事前登録（4 点）：各素数の局所の角を、その素数の点の上の貼り合わせとして持たせる

（2026-11-27 17:1x、構築側。著者の選択「1」（17:09。§13 の 1 つ目の問い）による。短期層の続きで、新しいパートではない。Lean は使わない。照合は受けていない。）

- **出所**：§1 の「点は素数たち＋無限素点」。玩具では素数が単数の座標（指標）としてしか入っていない（§13）。
- **(1) 問い（幾何の言葉）**：素数 p の点に、その点だけで決まる局所の貼り合わせ（局所の位相）を持たせ、無限素点の重なりの点での回転（§12 の 𝔀(χ)）が、無限素点の因子と各素数の点の局所の貼り合わせの積に分かれるか。§12 の交差項（素数どうしの結びつき）は、どの点の貼り合わせに属するか。
- **(2) 最善の翻訳**：Tate の学位論文（とその後の局所定数の理論）の、大域の ε 因子 = 局所定数 ε(1/2, ω_v, ψ_v) の積。局所定数は局所関数等式（局所フーリエ変換と局所ゼータ積分）から定まり、素数 p の局所定数は ω_p の単数での値（ガウス和）と ω_p の一意化元での値で決まる。ω が主イデールの上で 1 になることが、一意化元での値を他の素点の指標の値に結ぶ（盲検の結果は §15 に記録する）。
- **(3) 残余（構築側の見立て）**：数学の文としての残余は空（すべて既知の局所定数の理論）。読みとしての残余：交差項は「素数 p の点の貼り合わせの、p 自身の一意化元での値」で、それを決めるのは主イデール（有理数を全素点に同時に埋め込んだもの）の関係、という読み。素点どうしを結ぶものが、玩具の幾何では主イデールの関係として現れる。
- **(4) 対照群**：関数体（有限体上の 1 変数関数体）でも、大域の ε 因子は局所定数の積で、主イデールの関係も同じ形（形だけの文。確かめていない、既知の見込み、確信度：中）。ℚ に固有なのは無限素点の因子 (−i)^a（規約 T）だけで、それも A1 の入力の中にある。
- **内部照合**：PAG260 `crtMap`・`stdAddChar_crtMap`・`gaussSum_prodChar`・`rootNum_prodChar`・`phaseA1_prodChar`・`UA1_charU_prodChar`・`cross_eq_sign_of_rootNum_one`、PAG261 `rootNum_listChar_formI`・`rootNum_listChar_formII`・`rootNum_listChar`。形 (II) は交差項を素数 p_i の側に、形 (I) は χ_i の側に割り振った形。局所定数（局所ゼータ積分）を扱う宣言は見つからなかった（言葉の検索：local・zeta・eps・Tate。網羅ではない）。
- **盲検の問いテスト**：依頼文 `records/toy_origin/stage6/prompt_blind.md`（全文）。文脈を渡さない新しいエージェント（ウェブ検索あり）。開始 2026-11-27 17:1x。

## 15. 段 6 の結果：素点ごとの局所の貼り合わせ、交差項の置き場所は ψ の取り方で動く

（2026-11-27 17:3x、構築側。盲検の問いテストの結果と数値による。照合は受けていない。）

- **分かれる（はい）**：無限素点の重なりの点での回転 𝔀(χ) は、各素点の局所定数の積 ε(1/2, ω_∞, ψ_∞)·∏_i ε(1/2, ω_{p_i}, ψ_{p_i}) に分かれる。各素点の局所定数は、その素点の局所関数等式（局所フーリエ変換と局所ゼータ積分）だけから決まる（Tate の学位論文、Tate 1979 §3.2）。玩具の言葉では、素数 p の点に局所の貼り合わせ（その点の局所フーリエ変換が χ_p の部分に掛ける位相）を持たせ、無限素点の回転はそれらの積になる。ラベル：［既知］。
- **交差項の置き場所は規約による（盲検の指摘、数値で確認）**：
  - Tate の標準の ψ（規約 T：ψ_p(x) = e^{2πi{x}_p}、すべての有限素点で不分岐）では、素数 p_i の局所定数は ∏_{j≠i} χ_j(N_i)·τ(χ_i)/√N_i（PAG261 の形 (II) の因子）。交差項は p_i の局所定数に入り、それは ω_{p_i} の有理素数冪 p_i^{e_i} での値（Tate の公式で c = p_i^{e_i} と取ったとき）。（§14 の (3) と構築側の見立ての「一意化元の冪での値」は言い過ぎで、一意化元の選び方で変わる。局所定数の中での「交差項 × ガウス和」の分け方も c の選び方による。）この値は、ω が主イデール p_i の上で 1 になること（ω_∞(p_i) = 1、不分岐の q で ω_q(p_i) = 1 も使う）から決まる（Rohrlich, "Root numbers", PCMI 2009 講義録の Prop. 2.1。照合者の申告、頁は未確認）。
  - 大域の加法指標 ψ(·/N)（これも ℚ の上で自明）では、素数 p_i の局所定数は χ_i(N/N_i)·τ(χ_i)/√N_i（PAG261 の形 (I) の因子）で、χ_i だけで決まる。素点どうしの結びつきは ψ の側（ψ が ℚ の上で自明であること）に移る。
  - 一般に ψ を ψ(a·)（a ∈ ℚ^×）に替えると ε_v(1/2) は ω_v(a) 倍になり、積は ω(a) = 1 なので変わらない。**不変なのは積（大域のルート数）だけ**で、交差項を「どの点の貼り合わせに属するか」と言うことは、ψ を選んだときにだけ意味を持つ。
- **読みの訂正（第 8 の型、§14 の (3)）**：§14 の読み「交差項は素数 p の点の貼り合わせの値で、素点どうしの結びつきは主イデールの関係として現れる」は、標準の ψ を選んだときだけの読みで、数学の主張ではない。正しく言えるのは次のことまで。素点どうしの結びつきは、大域の有理数の構造（ℚ^× の上で ω が自明、ℚ の上で ψ が自明）が運ぶ。それを乗法の側（ω の主イデールでの値）に置くか、加法の側（ψ の取り方）に置くかは、ψ ↦ ψ(a·) の取り替えで動く。読み（解釈の層、構築側、確信度：中）：命名の「イーデル幾何（乗法）とアデール幾何（加法）の融合」と同じ形で、結びつきの置き場所を乗法の側と加法の側のあいだで移せる。第 10 の型（創発の修辞）に当たらないよう、新しいのはどの定理のどの項でもないこと（すべて既知）を添える。
- **ℚ に固有なもの（盲検の訂正、§14 の (4) を直す）**：「(−i)^a だけ」は言い過ぎ。関数体でも無限素点に局所定数があり（奇の指標では 𝔽_q 上の正規化したガウス和。パリティは ±1 ではなく 𝔽_q^× の指標）、一般の関数体（種数が正、素点が単項でない場合）では主イデールの機構がそのままは使えない。ℚ に固有なのは「標準の ψ がすべての有限素点で不分岐であること、類数 1、無限素点がアルキメデス的であること」の組み合わせ（照合者の計算、文献とは照合していない、確信度：中）。
- **数値**（`records/toy_origin/stage6/`。数値は証明ではない）：
  - `local_eps.py`（ログ `local_eps.log`）：Tate の公式も E1・E2 も使わず、ℚ_p の上の局所ゼータ積分を格子 p^{−M}ℤ_p / p^{M}ℤ_p（M = e + 2）で離散化して ε(1/2, ω_p, ψ_p) を求めた。法の組 3·5、3·7、4·5、5·7、8·3、9·4、3·5·7、4·3·5 の原始指標 50 個で、標準の ψ の局所定数と形 (II) の因子の差は 2.4×10⁻¹⁴ 以下、|ε_p| − 1 は 2.3×10⁻¹⁴ 以下、ε_∞∏ε_p と 𝔀 の差は 2.8×10⁻¹⁴ 以下（ω_p(p) は主イデールの関係から与えた）。ω_p(p) に共役を入れると、8 組中 5 組で積が 1.7〜2.0 ずれた（残る 4·5、8·3、3·5·7 では区別がつかなかった）。無限素点は数値積分で ε = (−i)^a（ψ_∞(x) = e^{−2πix}）。
  - `local_eps_psiN.py`（ログ `local_eps_psiN.log`）：ψ(·/N)（自己双対な測度 |1/N|_p^{1/2} dx）で、法の組 3·5、5·7、4·3·5 の原始指標 21 個。局所定数と形 (I) の因子の差は 7.4×10⁻¹⁴ 以下、形 (II) の因子とは 1.4〜2.0 ずれ、積と 𝔀 の差は 8.1×10⁻¹⁴ 以下。
  - 照合者も Tate の公式から N ∈ {15, 20, 63, 120, 140, 48, 75} の 67 組で同じ関係を確かめた（積の整合性。照合者の申告）。
- **盲検の問いテスト**：終了 17:2x（所要約 544 秒、ツール 19 回）。出力の全文は `records/toy_origin/stage6/outputs/blind_output.md`。判定：E1 既存（Rohrlich (1.47)、Vaughan の講義ノート Thm 4.2）、E2 既存からの短い帰結（言い過ぎ 2 点：一意化元、ψ による）、E3 既存（Rohrlich Prop. 2.1。後半の解釈は標準の ψ でだけ）、E4 既存（「局所定数ではない」は標準の ψ でだけ正しい）、E5 一部言い過ぎ。「交差項を局所定数の側に入れる計算」を一般のディリクレ指標について明示した文献は、照合者の検索の範囲では見つからなかった（不存在の証明ではない。虚二次体のヘッケ指標では Rohrlich の Lecture 2 §5.2 に同じ計算がある）。照合者の文脈に CLAUDE.md が自動で入っていた見込みで、完全な盲検ではない。
- **ラベル**：素点ごとの分解と、交差項の置き場所が ψ で動くことは［既知］（Tate、Rohrlich）。局所ゼータ積分による数値の確かめは［再導出（小さい）］。新規候補はない。
- **玩具への帰結**：素数の点に局所の貼り合わせを持たせることはできる。ただし素点どうしの結びつき（交差項）は特定の点の持ち物ではなく、ψ を選んで初めて置き場所が決まる。

## 16. 段 6 の後に残る問い（幾何の言葉で）

- 玩具の中で ψ をどう選ぶか（標準の ψ で乗法の側に置くか、ψ(·/N) で加法の側に置くか）は、構築側では決めない。「射影」の読み（舞台 P¹ の上の貼り合わせの合成。乗法の反転と加法の変換の合成）とどちらが合うかは、著者の判断を待つ。（後注 2026-11-27 17:37、著者の選択：加法の側（ψ(·/N)）。CLAUDE.md §1 に 1 行足した。§17 へ。）
- 素数 p の点の局所の貼り合わせ（局所フーリエ変換と反転の合成）を、無限素点と同じように「点の上の 2 つの端（p 進で小さい側 v → +∞ と大きい側 v → −∞）を重ねる」形で書けるかは、立てていない。イデール類群では、素数 p の付値の方向は主イデールで無限素点の乗法の方向に吸収される（C_ℚ ≅ Ẑ^× × ℝ_{>0}）ので、素数の点が独立に持てるのは単数の座標 ℤ_p^× の側だけになる見込み（確信度：中）。

## 17. 加法の側を選んだ後の玩具（2026-11-27 17:3x、著者の選択（17:37）を受けて）

- **玩具の取り決め**：加法指標は大域の ψ(·/N)（ℚ の上で自明）とする。素数 p_i の点の局所の貼り合わせは ε(1/2, ω_{p_i}, ψ_{p_i}(·/N)) = χ_i(N/N_i)·τ(χ_i)/√N_i（PAG261 の形 (I) の因子、§15 の数値で確認）で、その点の指標 χ_i の値だけを使う。素点どうしの結びつきは、加法指標が ℚ の上で自明であること（ψ(·/N) が中国剰余定理で各素点の加法指標の積に分かれること）が担う。
- **既存の有限レベルの構成と同じ割り振り**：PAG260 `stdAddChar_crtMap`（e((a₁N + a₂M)/(MN)) = e(a₁/M)·e(a₂/N)）と `gaussSum_prodChar`（τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)。PAG193 `gaussSum_mul_coprime` と同じ文）が、この割り振りそのもの。「射影」の有限レベルの読み（PAG256 の J∘H_N/√N）の核 e(xy/N) も水準 N の加法指標なので、加法の側の取り決めは既存の構成と食い違わない（構築側の照合、確信度：高。重複の A：同じ文）。
- **取り決めの帰結（構築側の見立て、確信度：中〜高）**：ψ(·/N) は水準 N によって変わる。標準の ψ はすべての水準で同じだが、加法の側では加法指標が水準（各部分では指標の導手）を知っている。各部分 χ ごとに導手 f_χ の ψ(·/f_χ) を使えば部分ごとの取り決めとしては閉じるが、すべての水準を同時に扱う極限（直極限の側）で 1 つの加法指標にまとまるかは立てていない。
- **ラベル**：取り決めそのものは著者の選択（解釈の層）。形 (I) の因子が局所定数になることは［既知］（§15）、既存の構成と同じ割り振りであることは鎖の文の確認。新規候補はない。

## 18. 段 7 の事前登録（4 点）：水準ごとの加法指標は極限で 1 つにまとまるか

（2026-11-27 18:2x、構築側。著者の選択「極限の問い」（18:23。§17 の帰結の問い）による。短期層の続き。Lean は使わない。照合は受けていない。）

- **出所**：§17 の帰結「ψ(·/N) は水準 N によって変わる。すべての水準を同時に扱う極限で 1 つの加法指標にまとまるかは立てていない」。§1 の「点は素数たち＋無限素点」（すべての素点を同時に扱う側）。解像度は使わない。
- **(1) 問い（幾何の言葉）**：水準ごとの加法指標 ψ_N = e(·/N) は、すべての水準（すべての素点）を同時に扱う極限で、1 つの加法指標にまとまるか。まとまるなら、どの写像に沿ってか（還元 ℤ/M → ℤ/N か、埋め込み ℤ/N → ℤ/M（x ↦ (M/N)x）か）。極限の加法指標は Tate の標準の加法指標と同じか。そのとき、加法の側の交差項（§17）は極限の対象の何に当たるか。
- **(2) 最善の翻訳**：ポントリャーギン双対（Ẑ の双対は ℚ/ℤ）。ℚ/ℤ = ⋃_N (1/N)ℤ/ℤ（埋め込みに沿った直極限）≅ ⊕_p ℚ_p/ℤ_p。ℚ/ℤ の加法指標 e は Tate の加法指標の有限部分の積 ∏_p ψ_p と一致する。Aut(ℚ/ℤ) ≅ Ẑ^×（Bost–Connes 系の対称性）。鎖では PAG258（Part 254）の `TopL_not_compat`（水準 N の核 J∘H_N/√N は引き戻しと両立しない）、`UA1`・`phaseA1_changeLevel`・`UA1_family_unique`・`Uinf`（導手で位相を決めると両立し、極限 `Lim` の上にまとまる）。
- **(3) 残余（構築側の見立て）**：数学の文としての残余は空（すべて既知）。読みとしての残余：加法の側の取り決め（水準 N で ψ(·/N)）は、極限では標準の ψ そのもので、違いは水準 N の群 ℤ/N を ℚ/ℤ の中の (1/N)ℤ/ℤ と見る座標（x ↦ x/N）にあるだけ、という読み。交差項は、すべての素数で共通の 1 点 1/f（ℚ/ℤ の点）で測ることと、素数ごとに自分の点 1/f_i で測ることの違い。
- **(4) 対照群**：関数体でも、𝔽_q[t] の剰余環の直極限（𝔽_q(t)/𝔽_q[t]）と留数による加法指標で同じ形になる見込み（形だけの文。確かめていない、確信度：中）。ℚ に固有なのは無限素点の側（極限の加法指標の無限素点の成分 ψ_∞）で、玩具の有限部分の文には入らない。
- **内部照合**：上の PAG258 の宣言のほか、PAG260 `stdAddChar_crtMap`・`gaussSum_prodChar`、PAG261 の形 (I)。ℚ/ℤ や直極限の加法指標を定義した宣言は見つからなかった（言葉の検索：QZ・ratCast・DirectLimit・AddChar。Part 261 の `CornerLim` は角の写像の直極限で、加法指標ではない。網羅ではない）。
- **盲検の問いテスト**：依頼文 `records/toy_origin/stage7/prompt_blind.md`（全文）。文脈を渡さない新しいエージェント（ウェブ検索あり）。開始 2026-11-27 18:25。

## 19. 段 7 の結果：水準ごとの加法指標は埋め込みに沿って ℚ/ℤ の 1 つの加法指標にまとまる。単数の側では水準の核は両立せず、導手で決めた位相が両立する

（2026-11-27 18:3x、構築側。照合は盲検の問いテストだけで、統合照合は受けていない。数値は証明ではない。盲検の出力は `records/toy_origin/stage7/outputs/blind_output.md`（全文。取得の経緯は同ファイルの冒頭）、数値は `records/toy_origin/stage7/limit_check.py` とログ。）

**結果（文ごと。ラベルは［既知／再導出／新規候補］）**

1. **まとまり方（文 L1）［既知］**：
   - 埋め込み ι_{N→M}(x) = (M/N)x に沿って ψ_M∘ι = ψ_N が成り立つ。数値 (b) の差は 5 組とも 0。
   - したがって {(ℤ/N, ψ_N)} は直系をなし、直極限は (ℚ/ℤ, e)。ℤ/N は ℚ/ℤ の中の (1/N)ℤ/ℤ と同一視する。
   - 還元に沿っては ψ_N∘r_{M→N} = ψ_M^{M/N} で、M = N のときしか一致しない。数値 (b) の差の最大は 1.989〜2.000。
   - 双対の側から見ると、族 {ψ_N} は lim← Hom(ℤ/N, S¹) ≅ Ẑ の元 1 に当たる（盲検の補足）。
   - 確信度：高。
2. **Tate の加法指標との関係（文 L2）［既知］。盲検の指摘で文を直した**：
   - 有限部分 ψ_f = ∏_p ψ_p は 𝔸_f の指標であり、ℚ/ℤ の指標ではない。
   - 正しい形：ψ_f は Ẑ の上で自明で、𝔸_f/Ẑ ≅ ℚ/ℤ を通じて e を誘導する。言い換えると ψ_f|_ℚ = e = ψ_∞^{−1}|_ℚ。
   - 符号が e(+x) になるのは規約 T（ψ_p = e^{+2πi{x}_p}）による。逆の規約では e(−x) になる（失敗の型 第 8）。
   - 数値 (a)：ランダムな有理数 2000 個（負の分子と p = 2 を含む）で、e(x) と ∏_p ψ_p(x) の差の最大は 2.3e-11。
     - これは分子が 10^6 までの浮動小数の誤差。
     - 最初の版は分母の素因数を 200 以下しか拾わず、差 2.0 を出していた。誤差の出所を確かめて直した。
   - 確信度：高。
3. **読み（解釈の層）**：
   - §17 の加法の側の取り決め ψ(·/N) と標準の ψ の違いは、ℤ/N を (1/N)ℤ/ℤ ⊂ ℚ/ℤ と見る座標 x ↦ x/N だけである。
   - すべての水準を同時に扱う極限では、加法指標は 1 つにまとまる。それは e（𝔸_f/Ẑ を通じた Tate の加法指標の有限部分）である。
   - この読みは上の 1・2 の既知の事実の言い直しで、新しい内容はない。
4. **単数の側（文 L3）［既知（Montgomery–Vaughan Thm 9.10 からの短い帰結）／数値で再導出］。盲検の指摘で文を直した**：
   - 式：T_N χ = μ(N/f)·χ*(N/f)·√(f/N)·W(χ*)·χ。ここで χ* は導手 f の原始指標で、gcd(N/f, f) > 1 なら χ*(N/f) = 0。
   - 直し：§18 の依頼文 L3 の「一般に W(χ_prim) と違う」は弱すぎた。正しくは「f < N なら常に違う」。
     - 絶対値は √(f/N) 以下で、1 より小さい。
     - N/f が平方因子をもつか gcd(N/f, f) > 1 なら、値は 0。
   - 数値 (c) の表の値は、すべてこの式どおりだった。
     - 1/√3：N = 12・f = 4、N = 15・f = 5（実）。
     - 1/√5：N = 15・f = 3。
     - −0.3035 ± 0.4911i：N = 15・f = 5（複素）。
     - 0：N = 8・f = 4、N = 9・f = 3、N = 12・f = 3、N = 16・f = 4・8。
   - 盲検の後に足した数値 (e)：N ≤ 60 の非自明な指標 1,042 個（うち f < N は 381 個）について、式との差の最大は 9.1e-14、固有ベクトルからのずれの最大は 9.2e-14。f < N で値が W(χ*) と一致した例は 0 個。
     - 照合者も自前の数値で同じ結果を出している（自明指標を含む 1,102 個、誤差 8e-14、一致 0 件）。
     - 個数の差 60 は、N = 1〜60 の自明指標の数。
   - 鎖では PAG258 `TopL_not_compat`・`TopL_not_compat_prime`（水準の核は引き戻しと両立しない。証人は自明指標の 1 例）に当たる。式そのものは Lean にない。
5. **一意性（文 L3 の後半）。盲検の指摘で、依頼文の文が誤りだと分かった**：
   - 依頼文の「両立する族はそれだけ」は、このままでは誤り。
   - 反例：次の族はどれも引き戻しと両立する。
     - 恒等写像。
     - χ ↦ conj(W(χ*))·χ。
     - χ ↦ χ*(−1)W(χ*)·χ。
     - 反転 J。
     - Ẑ^× の元による平行移動。
   - 正しい形：次の 2 つをともに課すと、族は U_N χ = W(χ*)χ に限られる。
     - (a) 引き戻しと両立する。
     - (b) 各 N で、導手がちょうど N の指標が張る部分（新しい部分）の上で T_N と一致する。
   - 単数の群の作用との可換性を課しても (b) は要る。N ≡ 2 mod 4 では (b) は空の条件になる。
   - これは PAG258 `UA1_family_unique` の仮定とちょうど同じである。
     - 仮定 hT は「V_prim の上で U a f = TopL f」、仮定 hc は「`pullSys` と可換」。
     - Lean の文は初めから正しい形で、誤りは構築側が依頼文に書いた散文の要約だけにあった。
   - 依存表（円環の照合）：一意性の入力は (b)、つまり原始部分での T_N の値。
     - その値が W(χ) であることは Hartley 核の計算（Part 252）であり、A1 を入れたものではない。
     - W(χ) がルート数であるという同定は Lean の外。
   - 除去テスト：(b) を外すと位相は自由に戻る（上の反例）。
   - 極限の側では、PAG258 `Uinf`（`Module.DirectLimit.map`）が `Lim` の上にまとまった作用素である。
6. **交差項（文 L4）［既知（Montgomery–Vaughan Thm 9.6）。説明は CRT による標準的な証明の言い直し］**：
   - 式：τ(χ) = ∏_i χ_i(f/f_i)τ(χ_i)。ℚ/ℤ の中で 1/f ≡ Σ_i u_i/f_i（u_i ≡ (f/f_i)^{−1} mod f_i）。
   - 数値 (d)：f = 15・28・105・72 で、誤差の最大は 1.8e-14。Σ u_i(f/f_i) ≡ 1 (mod f)。
   - ただし盲検の指摘のとおり、交差項に不変な内容はない。
     - 交差項 χ_i(f/f_i) = χ̄_i(u_i) は、p_i での和を e(·/f_i)（素数ごとの点 1/f_i）で取るか、e(u_i·/f_i)（共通の点 1/f の p_i 成分）で取るかの比にすぎない。
     - 後者で取れば、別立ての交差項は消えて局所の和に吸収される。
     - 同じ項は乗法の側にも置ける（Rohrlich, Root numbers の Prop. 2.1）。
   - §15 の結論「交差項の置き場所は ψ の取り方で動く」と同じで、規約の人工物として扱う（失敗の型 第 8）。現象としては報告しない。
   - 玩具の取り決め（形 (I)、§17）は、極限の対象の言葉では「すべての素数で共通の点 1/f の成分で測る」ことに当たる（読み）。
7. **乗法と加法の対比（文 L5）［既知（各部分）］。盲検の指摘で 2 か所を直した**：
   - 直し 1：§18 の依頼文 L5 の「乗法の側は逆極限、加法の側は直極限」は、群そのものの性質ではない。
     - ℤ/N は、還元に沿う逆系（極限 Ẑ）と埋め込みに沿う直系（極限 ℚ/ℤ）の両方をなし、2 つは双対である。
     - (ℤ/N)^× がなすのは逆系だけ。
     - 加法指標も Ẑ の連続指標として見れば、その全体は ℚ/ℤ になる。
   - 直し 2：「Bost–Connes 系の対称性の構造と同じ」は言い過ぎだった。言えるのは次のところまで。
     - τ(χ) は点 1/f の Ẑ^× 軌道を χ で重みづけた和（ラグランジュの分解式）である。
     - その作用は Bost–Connes 系の対称性群 Aut(ℚ/ℤ) ≅ Ẑ^× と同じ。
     - Bost–Connes 系の残りの構造（ℕ^× の作用、時間発展、KMS 状態）に当たるものは玩具にない。

**訂正表（§18 の文 → 直した文）**
- 依頼文 L2「直極限の加法指標は Tate の加法指標の有限部分そのもの」→「有限部分は 𝔸_f の指標で、𝔸_f/Ẑ ≅ ℚ/ℤ を通じて e を誘導する（規約 T）」。
- 依頼文 L3「一般に違う値」→「f < N なら常に違う（絶対値 √(f/N) 以下、0 もある）」。
- 依頼文 L3「両立する族はそれだけ」→「引き戻しとの両立と、新しい部分で T_N と一致する条件の 2 つで一意（PAG258 `UA1_family_unique` の形）」。
- 依頼文 L5「乗法は逆極限、加法は直極限」→ 群の性質ではない。「Bost–Connes 系の対称性の構造と同じ」→「同じ作用を使う」まで。
- §18 (3) の「数学の文としての残余は空（すべて既知）」は、照合の結果と合っていた（すべて既知か、既知の結果からの短い帰結）。
- §18 (3) の読みとしての残余（座標 x ↦ x/N だけの違い、共通の点と素数ごとの点の違い）は、読みとして残る。ただし後者は規約の人工物で、現象ではない。

**対照群（§18 (4)）**
- 関数体の形（𝔽_q(t)/𝔽_q[t] の直極限と留数による加法指標）は確かめていない。盲検も扱っていない（確信度：中のまま）。
- 大域の加法指標が大域体の上で自明であること（ψ_f|_ℚ = ψ_∞^{−1}|_ℚ の形）は関数体でも成り立つ。したがってこの形は ℚ に固有の文ではない（形の文）。
- ℚ に固有なのは無限素点の成分 ψ_∞ そのもので、玩具の有限部分の文には入らない。

**文献照合と検索の記録**
- 盲検の問いテスト（ウェブ検索だけ。MathSciNet・zbMATH・書籍の全文検索はしていない）。
- 照合者が中身を確かめた文献：Montgomery–Vaughan 第 9 章、Conrad の 2 つのノート、Rohrlich の PCMI 講義録、Shirbisheh arXiv:0808.1767 ほか。
- 「水準 N の加法指標を ℚ/ℤ の点 1/N として扱い、交差項をその点の素数成分として読む」扱いを明示的に書いた文献は、照合者の検索の範囲では見つからなかった。見つからなかったことは不存在の証明ではない。
  - 近いものは Pontryagin 双対の標準的な事実、Conrad、Montgomery–Vaughan Thm 9.6、Rohrlich。
  - この読みは既知の事実の言い直しなので、新規候補にはしない。
- 新規候補：なし。

**境界の場合（失敗の型 第 5）**
- p = 2 は (a)（分母に 2 の冪）、(c)（N = 8・16）、(d)（f = 28・72）に入れた。
- 自明指標は、W の式の形が合わないので (c)・(e) から除いた。
- N ≡ 2 mod 4 では、条件 (b) が空になる（原始指標がない）。

## 20. 段 7 の後に残る問い（幾何の言葉で）

- **加法の側（すべての素点を同時に扱う側）**：水準ごとの加法指標は、埋め込みに沿って ℚ/ℤ の 1 つの加法指標 e にまとまる。双対の側から見ると、その族は Ẑ の点 1 に当たる。数学の文としての残余はない。
- **単数の側**：水準の核 J∘H_N/√N はそのままでは極限に降りない。降りるのは導手で位相を決めた U（PAG258 `UA1`・`Uinf`）で、それを決めるには新しい部分での値（条件 (b)）が入力として要る。
- **立てていない問い**：極限で、反転（乗法の側、単数の極限の上）と加法の変換（加法の側、ℚ/ℤ の上）の合成として U_∞ を書けるか。
  - 水準ごとの合成 J∘H_N/√N は両立しないので、そのままの形では書けない。
  - 書けるとすれば、どの写像に沿った極限か。
  - この問いは §1 の「射影」の読み（反転と加法の変換の合成）の極限での形に当たる。
  - 構築側の見立て：既知の理論（Tate の局所定数の積）の内側に入る見込みが高い（確信度：中）。着手するなら事前登録の 4 点から。
- **§16 の問い（素数の点での p 進の小と大の重なり）**：段 7 では触れていない。

## 21. 段 8 の事前登録（4 点）：極限の U_∞ を、反転と加法の変換の合成として書けるか（§20 の問い）

（2026-11-27 18:5x、構築側。著者の選択「§20」（18:42）による。短期層の続き。Lean は使わない。照合は受けていない。）

- **出所**：§20 の立てていない問い。§1 の「射影」の読み（構築側の読み。著者が留保つきで材料に採用）は「反転（乗法の側）と加法の変換（加法の側）の合成で、有限レベルでは J∘H_N/√N」。
- **現状の 3 層**（CLAUDE.md §0 の 4）：
  - (a) 形式化済み：
    - PAG256：`JH_eq_rootNum_mul_any`、`hartley_eq_zero_of_not_isUnit`（原始指標の Hartley 変換は単数の外で 0）。
    - PAG257：`TopL_charU`（すべての指標で T χ = 𝔀(χ)χ。𝔀 は水準 N のガウス和で定めたもの）。
    - PAG258：`UA1_pullL_of_mem_Vprim`（q ∣ M で、q で原始的な g について U_M(π g) = π(T_q g)）、`UA1_family_unique`、`Uinf`。
    - PAG267（Part 263）：`invG_comp_pullSys`・`invL`（逆元による引き戻しは極限 `Lim` に降りる）。
  - (b) 解釈の層：「射影」を反転と加法の変換の合成と読むこと（留保つき）。A1 は公準。
  - (c) 未完の大域の問い：極限で、合成の「加法の変換」の側を何の上の変換として書くか。
- **(1) 問い（幾何の言葉）**：
  - すべての素点を同時に扱う極限で、U_∞ は「単数の極限の上の反転」と「加法の側の極限 ℚ/ℤ の点へ行く変換」の合成として書けるか。
  - 書けるなら、水準の核 J∘H_N/√N が両立しないことは、その合成のどの部品の違いとして見えるか。
- **(2) 最善の翻訳**：
  - Tate の局所理論：導手 p^e の局所指標 χ について、χ·1_{ℤ_p^×} のフーリエ変換は殻 p^{−e}ℤ_p^× に台をもち、係数はガウス和（局所定数）。
  - 大域では ℚ/ℤ の Ẑ^× 軌道 O_n（位数がちょうど n の点の集合。O_n ≅ (ℤ/n)^×）。
  - 有限レベルでは ℤ/N の殻 D_t = {x : gcd(x, N) = t}（(ℤ/N)^× の軌道。辞書では円分スキームの部分構成）。ℤ/N = (1/N)ℤ/ℤ のもとで D_t は O_{N/t} ∩ (1/N)ℤ/ℤ に当たり、単数の殻 D_1 は O_N に当たる。
  - 不分岐な素数の殻を n^{−s} で足し合わせると、局所関数等式の L 因子が現れる（Tate の γ と ε の違い）。
- **構築側の見立て（照合の前）**：
  - 定義：単数の上の関数 g（`Lim` の元、つまり Ẑ^× の上の局所定数関数）に対して、(A g)(t) = ∫_{Ẑ^×} g(x) e(xt) dx と定める。dx は Ẑ^× の正規化したハール測度、t ∈ ℚ/ℤ。
  - A は水準を使わずに定まるので、引き戻しと両立する。
  - 導手 f の χ について、Aχ が 0 でない殻は O_n（f ∣ n、n/f は平方因子をもたず f と互いに素）だけで、最小の殻は O_f。
  - T_N = ε_∞·(φ(N)/√N)·J∘R_N∘A。
    - R_N は O_N の上の値を u ↦ (·)(u/N) で単数の上の関数に戻す写像。
    - ε_∞ は Hartley 核の因子 (−i)^a（PAG256 `parFac`）。
  - U_∞ χ = ε_∞·(φ(f)/√f)·J∘R_f∘A χ。つまり χ ごとに最小の殻 O_f で読む。
  - すなわち U_∞ は次の合成になる。
    - A：加法の変換。極限で定まる。
    - 最小の殻からの読み出し：導手 f による拡大縮小で、乗法の側の元 f の作用。
    - J：反転。
    - ε_∞：無限素点の因子。
  - 水準の核が両立しないのは、読む殻を水準自身の点 1/N の軌道 O_N に固定するところから来る。
  - 殻ごとの値に n^{−s} の重みを付けて足すと、χ の上では f^{−s}·𝔀(χ*)/L(s+1/2, χ*) になる（Re s > 1/2）。
  - ℚ/ℤ = 𝔸_f/Ẑ では、p 進で小さい側（Ẑ の中の殻）が点 0 につぶれる。そのため、Tate の γ 因子の L(1−s, χ̄) の側はこの和には現れない（見立て、確信度：中）。
- **(3) 残余**：
  - 数学の文としては空の見込み（Tate の局所計算と Montgomery–Vaughan Thm 9.10 の組み立て）。
  - 読みとしての残余：極限の「射影」は 2 つではなく 4 つの部品の合成として書かれる、という読み。4 つは、加法の変換、殻の間の跳び（乗法の側）、反転、無限素点の因子。
- **(4) 対照群**：
  - 関数体では同じ形になる見込み（𝔽_q(t)/𝔽_q[t] の軌道と、留数による加法指標）。確かめていない（確信度：中）。
  - Beurling の一般化素数では、加法の構造がないので文そのものが立たない（A は ℚ/ℤ の加法指標を使う）。
  - したがってこの文は「形と稠密性だけ」の文ではないが、大域体に共通の文である。
- **内部照合**：
  - 上の (a) の宣言を使い、作り直さない。とくに、反転が極限に降りることは PAG267 `invL` として Lean にある。
  - ℚ/ℤ、その Ẑ^× 軌道、A の定義は、鎖に見つからなかった（段 7 の言葉の検索に加えて `orbit`・`軌道`。網羅ではない）。
  - 殻の言葉は PAG25x〜26x にあるが、どれも ℤ/N の殻代数（有限レベル）のもの。
  - 付記：CLAUDE.md §2 は「Lean 形式化は Part 262（PAG266）まで」と書いているが、短期層の Part 263・264（PAG267・PAG268）が索引に記録されている。
- **盲検の問いテスト**：依頼文は `records/toy_origin/stage8/prompt_blind.md`（全文）。文脈を渡さない新しいエージェント（ウェブ検索あり）。開始 2026-11-27 18:47。

## 22. 段 8 の結果：U_∞ は「A → 導手の軌道での読み出し → J → ε_∞」と書けるが、それはガウス和の定義の書き直し（構成から自明な形の一致）であり、作用素としては導手ごとの射影が要る

（2026-11-27 19:0x、構築側。照合は盲検の問いテストだけで、統合照合は受けていない。数値は証明ではない。盲検の出力は `records/toy_origin/stage8/outputs/blind_output.md`、数値は `records/toy_origin/stage8/shell_check.py` とログ。）

**盲検の条件についての注意**：
- 照合者は「CLAUDE.md がシステムによって文脈に入っていた（判断の根拠にはしていない）」と申告した。
- このリポジトリで起動した新しいエージェントには、研究の文脈を含む CLAUDE.md が自動で渡る。したがってこの盲検は「依頼文だけを渡す」という条件を完全には満たしていない。
- 段 6・7 の照合者も同じ条件だった可能性が高い（申告はない）。

**結果（文ごと。ラベルは［既知／再導出／新規候補］）**

1. **部品 A と軌道（文 M1）［既知］。盲検の指摘で直した**：
   - ℚ/ℤ は軌道 O_n（n ≥ 1）の交わらない和で、O_n ≅ (ℤ/n)^×。
   - A は水準を使わずに定まる。数値 (b)：4 組の (N, M)、軌道の点 1,960 個で、水準 N と M の計算の差の最大は 5.4e-14。
   - 直し：§21 の「A は Ẑ^× の作用と可換」は言い過ぎだった。正しくは A(g(u·)) = (Ag)(u^{−1}·) で、作用は逆元を通じて絡む。同変なのは J∘A のほうで、合成に J が要る理由の 1 つはここにある。
   - 補足（盲検）：Ẑ^× の正規化したハール測度は、加法のハール測度の制限ではない（Ẑ^× の加法の測度は 0）。水準 L ごとに L/φ(L) 倍ずれる。
   - 反転 J が極限に降りることは Lean にある（PAG267 `invL`）。数値 (a)：5 組で差は 0。
2. **軌道ごとの値（文 M2）［既知（Montgomery–Vaughan Thm 9.12。f ∣ n では Thm 9.10。局所版は Tate の学位論文 §2.5）］**：
   - 式：(Aχ)(v/n) は f ∤ n なら 0、f ∣ n なら μ(n/f)·χ*(n/f)·τ(χ*)·χ̄*(v)/φ(n)。§21 の χ̄(v) は χ̄*(v) と書くべきだった（盲検の指摘）。
   - 台は n/f が平方因子をもたず f と互いに素な O_n で、最小の軌道は O_f。自明な指標では値は μ(n)/φ(n)（ラマヌジャン和）。導手 2 の原始指標はないので、p = 2 の例外はない。
   - 数値 (c)：N ≤ 30 の指標 278 個（自明指標と p = 2 を含む）、n ≤ 90 で、式との差の最大は 1.5e-14、台の判定の食い違いは 0 件。
3. **合成の式（文 M3）［既知（MV Thm 9.10 からの短い帰結）。U_∞ の側はガウス和の定義の書き直し］**：
   - 等式そのものは正しい。
     - 数値 (d)：T_N χ = ε_∞·(φ(N)/√N)·J R_N A χ を、2 ≤ N ≤ 40 の指標 489 個でベクトルとして照合し、差の最大は 5.7e-14。両辺とも線形なので、水準 N のすべての関数で成り立つ。
     - 数値 (e)：ε_∞·(φ(f)/√f)·J R_f A χ = W(χ*)χ を、N ≤ 60 の指標 1,102 個で照合し、差の最大は 1.6e-13。
   - **円環（第 2 の型、構成から自明な形の一致）**：U_∞ の側の式は、ガウス和の定義の書き直しである。τ(χ*) = φ(f)·(Aχ)(1/f) は A の定義そのもの（盲検の指摘、確信度：高）。
     - 依存表：入力は A の定義と各指標の導手 f。目標の量 τ(χ*) は、A を点 1/f で読んだ値そのものである。
     - したがって「U_∞ を合成として書ける」は導出ではない。合成は W を説明せず、W の定義を言い換えている。
   - **作用素としての形**：U_∞ の側の等式は指標ごとにしか成り立たない。
     - R_f A は導手の小さい成分を消さない（R_p A 1 = −1/(p−1) ≠ 0）。
     - そのため作用素としては U_∞ = ε_∞·Σ_f (φ(f)/√f)·J R_f A P_f と書く必要がある。P_f は導手がちょうど f の成分への射影。
     - g = 1 + χ（χ は法 p で原始的）では、「最小の軌道」が 1 つに決まらない。
     - つまり導手による分解 P_f が入力として要る。これは PAG258 の `UA1` が導手（`primitiveCharacter`、`condPart`）で定まるのと同じ入力である。
   - **水準の核の側**：両立しないことは実際に起きる（T_1 1 = 1、T_2 1 = −1/√2、T_4 1 = 0）。N だけで決まる正規化に取り替えても直らない（N = p² では f = 1 の成分が 0 になる）。
     - したがって「水準の核の非両立は、読む軌道を水準自身の O_N に固定することから来る」という読みは妥当（盲検の判定）。
4. **軌道ごとに足した級数（文 M4）［既知（MV Thm 9.10 と Σμ(m)χ(m)m^{−w} = 1/L(w, χ) からの短い帰結。自明な指標では Ramanujan（1918）の Σ_q c_q(m)q^{−s} = σ_{1−s}(m)/ζ(s) の m = 1）］**：
   - 式：Σ_n n^{−s} S_n χ = f^{−s}·(τ(χ*)/√f)/L(s + 1/2, χ*)（Re s > 1/2 で絶対収束）。
   - 数値 (f)：導手 3・4・5・7・8・12・15 の原始指標を 1 個ずつ（奇 6 個、偶 1 個）、s = 2・3・2+3i で照合した。ガウス和は定義から直接計算した。差の最大は 5.8e-8 で、打ち切りの見積りの範囲内。
5. **局所の分解（文 M5）。構築側の見立ては誤りだった**：
   - §21 の見立て「殻 k ≥ 0 が L(1−s, χ̄) を、殻 −1 が 1/L(s, χ) を与え、ℚ/ℤ では前者が点 0 につぶれる」のうち、殻ごとの割り当ては誤り。
   - 盲検より先に構築側の数値 (g) でも確かめた（p = 2・3・7、s′ = 0.3・0.8+2i）。
     - Tate の正規化では、殻をすべて足した Z(Φ̂) は L(1−s′, χ̄)/L(s′, χ) と一致する（差は 4e-12 以下）。
     - 一方、「つぶした点 + 殻 −1」は (1 − 1/p) − χ(p)p^{−s′} で、1/L(s′, χ) ではない。
   - 正しい形（盲検）：vol(ℤ_p^×) = 1 で正規化し、ℤ_p を重み 1 の 1 点につぶすと、「つぶした点 + 殻 −1」が 1/L_p(s′, χ) になる。
   - s′ = s + 1/2 は Tate の変数。
   - 不分岐な p での χ(p) は入力の p 成分からは出ず、分岐する素点の値 χ*(n/f) から来る（§15・§19 の交差項）。
     - Tate の ω_p(p) と同一視するには積公式（ω が ℚ^× の上で自明）が要る。
     - 1/L に χ と χ̄ のどちらが出るかは規約で決まる（失敗の型 第 8）。
   - L(1−s′, χ̄) の側が見えない理由は A ではない。A の出力は Ẑ 不変で、情報を失っていない。理由は「ℚ/ℤ の上で n^{−s} の重みを付けて足すと、重みが Ẑ の上で定数になる」ことにある。
   - この説明は発見的なもので、［観察］に置く。

**訂正表（§21 の文 → 直した文）**
- 「A は Ẑ^× の作用と可換」→「A(g(u·)) = (Ag)(u^{−1}·)。同変なのは J∘A」。
- 「χ̄(v)」→「χ̄*(v)」。
- 「U_∞ = ε_∞·(φ(f)/√f)·J∘R_f∘A（χ ごとに最小の殻）」→「指標ごとの等式。作用素としては Σ_f (φ(f)/√f)·J R_f A P_f。しかもガウス和の定義の書き直し（構成から自明な形の一致）」。
- 「極限の『射影』は 4 つの部品の合成として書かれる、という読み」→ 導手の射影 P_f が要るので部品は 5 つ。合成は W を説明せず、定義を言い換えるだけなので、読みとしての残余も記法の水準にとどまる。
- 「ℚ/ℤ では Ẑ の中の殻が点 0 につぶれるので L(1−s, χ̄) は見えない」→「殻ごとの割り当ては誤り。見えないのは n^{−s} が Ẑ の上で定数だから（発見的、［観察］）」。
- §21 (3) の「数学の文としては空の見込み」は照合の結果と合っていた。

**§20 の問いへの答え**
- 書ける。U_∞ = ε_∞·Σ_f (φ(f)/√f)·J R_f A P_f。
- ただしこれは構成から自明な形の一致で、ガウス和の定義の言い換えである。作用素としては導手ごとの射影 P_f が入力として要る。
- 水準の核 J∘H_N/√N は、同じ A を水準自身の軌道 O_N で読んだもの（射影は要らない）。両立しないのは読む軌道を固定するからで、N だけで決まる正規化では直らない。

**対照群**
- 関数体の形は確かめていない（確信度：中のまま）。
- Beurling の一般化素数では、加法の構造がないので文そのものが立たない。

**文献照合と検索の記録**
- 盲検の問いテスト：ウェブ検索 12 回ほどと、文献 6 件の本文。MathSciNet と zbMATH は使っていない。
- 「ルート数を最小の軌道 1/f で読む」扱いと、「原始的でない指標のガウス和を n^{−s} で足して 1/L を得る」扱い（指標つきの形）を明示的に書いた文献は、照合者の検索の範囲では見つからなかった。見つからなかったことは不存在の証明ではない。
- 前者は原始指標ではガウス和の定義そのもの。後者は既知の結果からの短い帰結で、自明な指標では Ramanujan にある。どちらも新規候補にしない。
- 近い先行：Burnol, arXiv:math/9811040 の殻ごとの形。
- 新規候補：なし。

**境界の場合（失敗の型 第 5）**
- 自明指標と p = 2 は (c)・(e) に入れた。
- (d) は 2 ≤ N ≤ 40（N = 1 は Hartley 核の定義の外として除いた）。
- (f) は導手ごとに原始指標を 1 個だけ試した（網羅ではない）。

## 23. 段 8 の後に残る問い（幾何の言葉で）

- **§20 の問い**：上のとおり答えが出た。ただしその答えは構成から自明な形の一致で、新しい内容はない。
- **p 進で小さい側（Ẑ の中の殻）**：
  - ℚ/ℤ の上の読み出しと n^{−s} の重みでは、Tate の γ 因子の L(1−s′, χ̄) の側は現れない。
  - それを見るには、Ẑ の上で一定でない重み（ℤ_p の中の殻を分ける重み）が要り、ℚ/ℤ = 𝔸_f/Ẑ ではなく 𝔸_f の上で読むことになる。
  - これは §16 の問い（素数の点での p 進の小と大の重なり）と同じ所を指す。§16 の問いはこの段で答えておらず、立てていない。
- **不分岐な素点の値の出どころ**：不分岐な p の Euler 因子に現れる χ(p) は、分岐する素点の指標の p での値から来る（積公式。盲検の M5 (c)）。既知（Tate の大域理論）で、問いとしては立てない。

## 24. 段 9 の事前登録（4 点）：素数の点の上の貼り合わせを、付値の軸の 2 つの端（p 進で小さい側と大きい側）の言葉で書けるか

（2026-11-27 19:2x、構築側。著者の指示「進めてください」（19:17）を、§23・§16 で挙げた問いへの着手と受けた。短期層の続き。Lean は使わない。照合は受けていない。）

- **出所**：§16 の 2 つ目の問い（素数 p の点の局所の貼り合わせを、無限素点と同じように「点の上の 2 つの端を重ねる」形で書けるか）と、§23 の問い（L(1−s′, χ̄) の側は ℚ/ℤ ではなく 𝔸_f の上で、Ẑ の中の殻を分けて読まないと見えない）。
- **現状の 3 層**：
  - (a) 形式化済み：有限レベルの JH と 𝔀（PAG256）、U と極限（PAG257・PAG258）、形 (II) の交差項（PAG261 `rootNum_listChar_formII`）。ℚ_p の上のフーリエ変換は鎖にない（p 進の宣言は Part 129・185〜193 のガウス和の付値のもので、フーリエ変換ではない）。
  - (b) 解釈の層：「重なり」はねじれた貼り合わせ U。玩具 T0 の窓の貼り合わせ f(n+M) = U f(n)（§1〜§6）。
  - (c) 未完の大域の問い：素数の点の上の幾何（付値の方向）を玩具に入れること。
- **(1) 問い（幾何の言葉）**：
  - 素数 p の点の上の局所の貼り合わせ（局所フーリエ変換 F_p と反転 J_p の合成）は、付値の軸（殻 p^kℤ_p^× の番号 k ∈ ℤ。k → +∞ が点 0、k → −∞ が点 ∞）の上でどう働くか。
  - 無限素点の玩具の窓の貼り合わせと同じ形になるか。分岐する素数と分岐しない素数で違うか。
  - すべての素点を同時に扱うイデール類群では、素数の付値の軸と無限素点の対数の軸はどう関係するか。
- **(2) 最善の翻訳**：
  - Tate の局所理論：導手 p^e（e ≥ 1）の局所指標 χ で、F_p(χ·1_{p^kℤ_p^×}) は殻 −k−e だけに台をもち、係数はガウス和。局所の ε(s) = ε(1/2)·p^{e(1/2−s)}。
  - 不分岐では F_p(1_{ℤ_p^×}) = 1_{ℤ_p} − p^{−1}1_{p^{−1}ℤ_p} で、γ = L(1−s, χ̄)/L(s, χ)。
  - Burnol（arXiv:math/9811040）の殻ごとの作用素の形（段 8 の盲検が挙げた近い先行）。
  - 大域：C_ℚ ≅ Ẑ^× × ℝ_{>0}、ε(s, χ) = 𝔀(χ)·f^{1/2−s}、積公式。
- **構築側の見立て（照合の前）**：
  - 準備：ユニタリな反転 (J_p g)(x) = |x|^{−1}·g(x^{−1}) を使い、χ の成分（単数の上で χ のように変わる関数 Σ_k c_k·χ·1_{p^kℤ_p^×}）を、L² で正規化した数列 c̃_k で表す。
  - V1（分岐、e ≥ 1）：J_p∘F_p は χ の成分の上で、付値の軸の幅 e の平行移動に位相 τ(χ)/p^{e/2}（絶対値 1）を掛けたもの。
    - 固有ベクトルは c̃_{k+e} = (λ/ε)·c̃_k を満たす数列で、窓の幅が導手の指数 e の窓の貼り合わせ（玩具 T0 の f(n+M) = U f(n) と同じ形。M ↔ e）。
    - 交差項 ω_p(p)^e は作用素の側には現れない。付値の軸の 1 歩ごとに ω_p(p) を掛ける指標で測ったとき、e 歩の平行移動の「ホロノミー」として現れる。
  - V2（不分岐）：J_p∘F_p は平行移動ではない。数列の上の、差 m − k だけによる作用素（ローラン作用素）で、記号は σ(z) = (1 − p^{−1/2}z)/(1 − p^{−1/2}z^{−1})。
    - |z| = 1 で絶対値 1（ユニタリ）。z = χ(p)p^{−it} とおくと σ = L(1−s, χ̄)/L(s, χ)（s = 1/2 + it）。
    - 窓の貼り合わせはなく、1 つの殻は大きい側（k → −∞）への尾と 1 つ隣の殻に広がる。
  - V3（大域）：イデール類群では主イデール p^{e} により、p の軸の幅 e の平行移動は、無限素点の対数の軸の e·log p の平行移動と、他の素数の単数の座標への p^{−e} の掛け算に移る。
    - 後者の指標の値が交差項（積公式。§15 の形 (II)）。
    - 平行移動の合計は log f で、ε(s, χ) の因子 f^{1/2−s} に当たる。
  - V4（無限素点との対比）：Tate の理論では、無限素点の J∘F は Γ 因子の比を記号とする作用素で、平行移動ではない（位相が t について線形でない）。
    - したがって、玩具 T0 の窓の貼り合わせ（課した境界条件）は、Tate の局所作用素の形としては無限素点よりも分岐した素数に似る（見立て、確信度：中）。
- **(3) 残余**：
  - 数学の文としては空の見込み（Tate の局所計算と大域の関数等式、Burnol）。
  - 読みとしての残余：素数の点の上の貼り合わせは、分岐していれば、付値の軸の上の幅 e の窓の貼り合わせ。交差項はその平行移動のホロノミー。
- **(4) 対照群**：
  - 関数体では、すべての素点が非アルキメデス的で、付値の軸はどれも ℤ。V1・V2 は同じ形になる見込み。V3 は、イデール類群の次数写像（像は ℤ）に移る形になる見込み（確かめていない、確信度：中）。
  - Beurling の一般化素数では、各素数の点の上の加法の構造（ℚ_p）がないので、文が立たない。
- **内部照合**：
  - 上の (a)。ℚ_p のフーリエ変換・殻の作用素の宣言は鎖に見つからなかった（`Padic`・`padicValNat` の検索。網羅ではない）。
  - 索引 2.4 の後注は「JH は Tate の局所関数等式を作用素として書いたもの、Burnol の作用素の ℤ/N 版」と書いている。この段はその p 進の局所版に当たる。
- **盲検の問いテスト**：依頼文 `records/toy_origin/stage9/prompt_blind.md`（全文）。条件の注意（CLAUDE.md が自動で渡る）は段 8 と同じ。開始 2026-11-27 19:21。

## 25. 段 9 の結果：分岐する素数の点では、局所の貼り合わせは付値の軸の幅 e の平行移動に位相を掛けたもの。不分岐の素数と無限素点では平行移動ではなく、γ 因子を記号とする作用素

（2026-11-27 19:4x、構築側。照合は盲検の問いテストだけで、統合照合は受けていない。数値は証明ではない。盲検の出力は `records/toy_origin/stage9/outputs/blind_output.md`（条件の注意は段 8 と同じ：CLAUDE.md が照合者の文脈に入っていた）、数値は `records/toy_origin/stage9/padic_axis.py` とログ。）

**結果（文ごと。ラベルは［既知／再導出／新規候補］）**

1. **分岐する素数（文 P1 の作用素の部分）［既知（Tate の学位論文 §2.4–2.5 の局所関数等式からの短い帰結。Burnol, IMRN 2000（arXiv:math/9901051）定理 I）］**：
   - J_p∘F_p は χ の成分を保つ。正規化した係数の上では c̃′_{k+e} = ε·c̃_k、ε = τ(χ)/p^{e/2}（|ε| = 1）。
     - つまり付値の軸の上で 0 の側（小さい側）へ幅 e だけ平行移動し、位相 ε を掛ける。
     - 言い換えると J_p F_p|_χ g = τ(χ)·g(p^{−e}·)、つまり ε とユニタリな拡大縮小の積（盲検の補足）。
   - 数値 (a)：p = 2（e = 2・3）、p = 3（e = 1・2）、p = 5・7（e = 1）のすべての原始指標で照合した。
     - m = k + e の成分と τ/p^{e/2} の差は最大 3.5e-16、それ以外の成分は最大 9.4e-16。
     - 計算は有限和で正確に行った。和が 0 になる場合（L > max(e, 1)）の近道は、正確に計算できる範囲の 1,980 件で 0 を確かめてから使った。
   - p = 2 では e = 1 の指標はない。核を ψ(−xy) に取ると ε は χ(−1)τ(χ)/p^{e/2} になる（規約、失敗の型 第 8）。
2. **分岐する素数の固有ベクトル（文 P1 の後半）。構築側の文は誤りだった**：
   - 依頼文の「c̃_{k+e} = (λ/ε)c̃_k」は向きが逆で、正しくは c̃_{k+e} = (ε/λ)c̃_k。
     - 数値 (g)：p = 3、e = 2、λ = iε で、文の形では |JF c̃ − λc̃| が 2.0、正しい形では 1.6e-15。
   - そのうえ、これは ℓ² の固有ベクトルではない（|c̃_k| が周期 e なので ℓ² に入らない）。
     - JF は ε×（両側シフト）^e に等しく、固有値を持たない。スペクトルは単位円全体で、純絶対連続、重複度 e。
     - 正しくは「一般化固有ベクトル（Floquet–Bloch 型）」。
   - 読みの直し：「窓の幅 e の窓の貼り合わせ」は、固有ベクトルではなく、Floquet–Bloch 分解（ℓ²(ℤ) を幅 e の窓と位相で分けること）の一般化固有ベクトルの形として読む。
     - 玩具 T0 の f(n+M) = U f(n) も、有限の窓に閉じた空間（商）の上の条件であって、ℓ² の固有ベクトルの条件ではない。
3. **不分岐の素数（文 P2）［既知（Burnol, arXiv:math/9811040 の殻ごとの作用素。Burnol IMRN 2000 の Γ(1; z)。Tate §2.5）］**：
   - J_p∘F_p は平行移動ではなく、差 m − k だけによるローラン作用素。
     - 係数は M_d = (1 − 1/p)p^{d/2}（d ≤ 0）、−p^{−1/2}（d = 1）、0（d ≥ 2）。
     - 記号は σ(z) = (1 − p^{−1/2}z)/(1 − p^{−1/2}z^{−1})。
   - z = w·p^{−it} とおくと、σ は L(1−s, ω_p^{−1})/L(s, ω_p)（s = 1/2 + it）と恒等的に一致する。
   - 数値 (b)・(c)：p = 2・3・5・7 で、係数の予想との差は最大 2.6e-14、記号と閉じた式の差は最大 1.1e-9（d ≥ −60 での打ち切りが効いているのは p = 2）、|σ| − 1 は最大 2.2e-16、列のグラム行列と単位行列の差は最大 8.2e-15（ユニタリ）。
   - 数値 (d)：Tate の局所ゼータ積分を殻ごとの試験関数で直接計算すると、記号の読みと差 9.5e-14 以下で一致した。試験関数（k = −2・0・3）を変えても値は変わらなかった（差 8.0e-14 以下。γ が試験関数によらないことの確認）。
   - 盲検の追加（数値 (g) で確かめた）：巻き数は 0 で、σ の値域は単位円全体ではなく弧 |arg σ| ≤ 2 arcsin(p^{−1/2})（p = 2 で ±π/2）。
   - 窓の貼り合わせはない。1 つの殻は、隣の殻（小さい側へ 1 つ）と大きい側への尾に広がる。
   - Burnol 1998 の η_i は殻 S_{−i} に載るので、その z はこの文の z^{−1} に当たる（向きを直すと一致する）。
4. **交差項（文 P3）［既知（Rohrlich, Root numbers の (2.55)〜(2.56) の因子 χ_u(β)）。「ホロノミー」は名前の付け替え］**：
   - 交差項 w^e = ω_p(p)^e は、J_p∘F_p の作用そのものには現れない（ε は w によらない）。
   - 交差項は、作用素の記号 ε·z^e に z = w·p^{−it} を代入したときに現れる値である。
   - 数値 (d)：分岐する場合、Tate の局所ゼータ積分は τ(χ)/p^{e/2}·w^e·p^{−iet} と一致した。
   - 向き w^{+e} は、規約 T、ω_q(q) = χ(q)、Z(g, ω, s) = ∫ g ω |·|^s のもとで正しい（盲検の数値では、w^{−e} にすると最大 2.0 ずれる）。ω̄ で測るか ω_q(q) = χ̄(q) と正規化すると w^{−e} になる（規約、失敗の型 第 8）。
   - 直し：盲検の判定どおり、「ホロノミー」には接続も曲率もなく、名前の付け替えにすぎない。読みとしても採らない（失敗の型 第 3：格上げの語）。
5. **大域（文 P4）［短い帰結（照合者の確信度：中〜高）］。盲検の指摘で符号と範囲を直した**：
   - JF の向き k ↦ k + e は、p 成分に p^e を掛けることに当たる。
   - 主イデール p^{−e} を掛けて C_ℚ に移すと、ℝ_{>0} の成分は p^{−e} 倍（対数の軸で −e log p）、q ≠ p の単数の成分も p^{−e} 倍になる。
     - 指標の値に効くのは q ∣ f だけで、∏_{q∣f, q≠p} ω_q(p^{−e}) = ∏ χ_q(p)^e = w^e（積公式）。
   - 数値 (e)：f = 15・28・105・72・180 の原始指標（5 種、合計 43 個）で、ε_∞·∏_i (τ(χ_i)/p_i^{e_i/2})·w_i^{e_i} と 𝔀(χ) の差は最大 1.7e-14（§15 の形 (II) と同じ）。
   - f^{1/2−s} は正規化した係数で測った場合で、正規化しなければ f^{−s}。s への依存がすべて分岐する素数から来るのは、ε_∞ が s によらないから。
   - 各素数の平行移動は別々のテンソル因子の上にあるので、「合計 log f」は C_ℚ に移して ω で測った後でだけ意味を持つ（盲検）。
6. **無限素点との対比（文 P5）［既知（Tate §2.5、Burnol 1998、Rohrlich (2.49)）］。盲検の指摘で対比の立て方を直した**：
   - 無限素点の J∘F の記号は ε_∞·Γ_ℝ(1/2 − it + a)/Γ_ℝ(1/2 + it + a)（ε_∞ = (−i)^a）で、位相は t について線形でない。
     - 数値 (f)：数値積分と閉じた式の差は最大 4.2e-6（a = 0。積分の下端の打ち切り）。位相の 2 階差分は a = 0 で最大 1.3e-2、a = 1 で最大 1.7e-3。
     - 分岐する素数の位相の 2 階差分は 1e-14 程度で、線形。
   - 直し：対比は「無限素点か有限素点か」ではなく、「局所の L 因子が自明か否か」で分かれる。不分岐の素数でも位相は線形でない。
     - L 因子が自明（分岐）：平行移動。
     - L 因子が自明でない（不分岐の素数、無限素点）：平行移動ではない。
   - §24 V4 の見立て（玩具 T0 の窓の貼り合わせは、Tate の局所作用素の形としては、無限素点よりも分岐した素数に似る）は、この直した対比のもとで残る。ただし T0 の U は課した境界条件で、Tate の作用素から導いたものではない［観察］。

**訂正表（§24 の文 → 直した文）**
- 「固有ベクトルは c̃_{k+e} = (λ/ε)c̃_k を満たす数列」→「一般化固有ベクトル（Floquet–Bloch 型）で、c̃_{k+e} = (ε/λ)c̃_k。ℓ² の固有値はない（スペクトルは単位円全体、重複度 e）」。
- 「交差項は平行移動のホロノミー」→「交差項は、作用素の記号 ε z^e に z = w p^{−it} を代入した値。ホロノミーの語は使わない」。
- 「p の軸の幅 e の平行移動は、対数の軸の e·log p の平行移動に移る」→「主イデール p^{−e} で移すと −e log p。各素数の平行移動の合計は、C_ℚ に移して ω で測った後でだけ意味を持つ」。
- 「無限素点は平行移動ではない／分岐する素数は平行移動」の対比→「L 因子が自明か否かの対比（不分岐の素数も平行移動ではない）」。
- §24 (3) の「数学の文としては空の見込み」は照合の結果と合っていた。

**§16・§23 の問いへの答え**
- 素数 p の点の上の局所の貼り合わせは、付値の軸の上の作用素として書ける。
  - 分岐していれば、0 の側への幅 e（導手の指数）の平行移動に位相 τ(χ)/p^{e/2} を掛けたもの。
    - 付値の軸の 2 つの端（点 0 と点 ∞）を重ねるのではない。ℓ²(ℤ) を幅 e の窓に分ける Floquet–Bloch の形になる。
  - 不分岐なら平行移動ではなく、γ 因子を記号とするローラン作用素。
    - 殻 k ≥ 0 側（小さい側）の和が L(1−s, χ̄) を含む全体の記号を作る。§23 で ℚ/ℤ の上では見えなかった側は、𝔸_f（ℚ_p）の殻を分けて読むと、この作用素の記号として見える。
- 交差項は作用素の側にはなく、指標で測るときの代入の値。イデール類群に移すと、他の素数の単数の座標の上の指標の値になる（積公式）。
- すべて既知（Tate、Burnol、Rohrlich）。新規候補なし。

**対照群**
- 関数体の形は確かめていない（確信度：中のまま）。
- Beurling の一般化素数では、各素数の点の上の加法の構造がないので、文が立たない。

**文献照合と検索の記録**
- 盲検の問いテスト：ウェブ検索、Burnol の 2 論文、Vladimirov の表、Rohrlich の講義録、Tate の走査版の本文。MathSciNet と zbMATH は使っていない。
- 「局所のフーリエ変換と反転の合成を、付値の軸の上の窓の貼り合わせ（導手の指数を幅とする平行移動）として書き、交差項をそのホロノミーとして読む」扱いを明示的に書いた文献は、照合者の検索の範囲では見つからなかった。見つからなかったことは不存在の証明ではない。
- 最も近いのは Burnol IMRN 2000。分岐する成分を純粋な遅れ（平行移動）として扱っているが、ガウス和は正規化で消しており、ルート数の値と交差項は扱っていない。
- 平行移動の部分は Burnol にあり、ホロノミーの部分は名前の付け替えなので、新規候補にしない。

**境界の場合（失敗の型 第 5）**
- p = 2（e = 2・3、不分岐）を入れた。p = 2 には e = 1 の指標がない。
- 自明な指標（不分岐）は (b)・(d) で扱った。
- 実指標では交差項の向き w^{±e} を区別できない（盲検の注意）。(e) は複素指標を含む組で確かめた。

## 26. 段 9 の後に残る問い（幾何の言葉で）

- **玩具 T0 の窓と Tate の作用素の対応**：
  - Tate の作用素では、位相つきの純粋な平行移動（窓の貼り合わせの形）は分岐する素数にだけ現れ、窓の幅は導手の指数で決まる。
  - 無限素点では、J∘F は Γ 因子の比を記号とする作用素で、平行移動ではない。
  - 玩具 T0 は、無限素点の対数の格子に、幅 M の窓の貼り合わせ（課した境界条件 U）を置いた。
  - これを Tate の作用素の側からどう位置づけるか（例えば、T0 の窓を分岐する素数の形の写しと読むか、無限素点の境界条件として独立に置いたものと読むか）は、定義と読みに関わるので、構築側では決めない。著者の判断を待つ。
  - （後注 2026-11-28 07:13、著者の選択：「無限素点に独立に置いた境界条件」。CLAUDE.md §1 に 1 行足した（日英）。§27 へ。）
- **イデール類群の対数の軸の上での、平行移動の幅の比**：
  - C_ℚ に移すと、素数ごとの平行移動の幅 e·log p は対数の軸の上に並ぶ。違う素数の幅は互いに有理数倍にならないので、1 つの格子 q^ℤ には載らない。
  - 関数体では、どの幅も次数の単位の整数倍になる。
  - ただしこれは素数の対数の稠密性の文で、CLAUDE.md §6 の対照群の規則では算術の内容がないものとして扱う。問いとしては立てない。

## 27. 著者の選択：玩具 T0 の窓は無限素点に独立に置いた境界条件。その帰結

（2026-11-28 07:1x、構築側。著者の選択（07:13）「無限素点に独立に置いた境界条件」を受けた。以下は解釈の層の整理で、新しい数学の主張はない。照合は受けていない。）

- **選択**：玩具 T0 の窓の貼り合わせ（無限素点の対数の格子の上の f(n+M) = U f(n)）は、無限素点に独立に置いた境界条件と読む。
  - Tate の局所作用素から導いたものではない。
  - 分岐する素数の形（付値の軸の幅 e の平行移動に位相を掛けたもの、§25）の写しとも読まない。
  - CLAUDE.md §1 に 1 行足した（日英）。
- **帰結 1（設定との整合）**：これは §2 の設定（窓は貼り合わせのための切断で、モノグラフ層の Λ 切断と同じ役割。境界条件が意味を持つのは切断があるから）をそのまま確かめるもので、設定は変わらない。
  - 境界ユニタリ U はモノグラフ層の中心問題 P1（自己共役拡張の境界条件の両立分類、定理 2.6）の U と同じ役割で、入力である。
- **帰結 2（窓の幅と位相の地位）**：
  - 窓の幅 M は玩具の自由なパラメータのまま残る。どの導手にも結びつけない。
  - U の位相は著者の選択 (A)（A1 の位相 𝔀(χ) による複素指標の組の回転）で決まる。したがって A1 は、この境界条件の入力として玩具に入る。
  - §6 の依存表と同じく、A1 を外すと位相は自由に戻る（除去テスト）。A1 は導かれていない。
- **帰結 3（2 種類の貼り合わせ）**：玩具には、地位の違う 2 種類の貼り合わせが並ぶ。
  - (i) 無限素点：課した境界条件（入力）。
  - (ii) 素数の点：定義（局所フーリエ変換と反転）から計算した Tate の局所作用素（§15・§25。既知）。
  - 両者をつなぐのは A1 である（読み）。
    - 境界条件 (i) の位相 𝔀(χ) は、A1 のもとで、すべての素点の局所定数の積 ε_∞·∏_p ε_p（交差項を含む）に等しい。
    - この等式は §15・§25 の数値で確かめた（Lean の外。数値は証明ではない）。
    - その中身は Tate の定理であり、A1 は解釈の層の公準のままである（CLAUDE.md §2）。
  - したがって、この選択のもとでは「無限素点の境界条件は独立に置かれ、その値が素数の点の局所作用素の値の積と一致することは、A1 という公準が担う」と読む（解釈の層、確信度：中）。
- **閉じた問い**：§26 の 1 つ目の問い（T0 の窓を Tate の作用素の側からどう位置づけるか）は、この選択で閉じた。
- **残る問い**：§26 の 2 つ目（平行移動の幅の比）は、稠密性の文として立てないままにする。


## §6 玩具の盲検の出力と数値のログ

### records/toy_origin/stage6/prompt_blind.md
あなたは文献照合の担当です。以下の定義と文だけを読み、問いに答えてください。この問いを作った研究の文脈は渡しません。リポジトリ内のファイルは読まないでください（読める場合でも、判断の根拠にしないでください）。ウェブ検索は使ってかまいません。

## 定義

- N = N_1 ⋯ N_k は互いに素な素数冪 N_i = p_i^{e_i} の積。χ = χ_1 ⋯ χ_k は原始的なディリクレ指標（χ_i は法 N_i の原始指標）で、パリティ a ∈ {0, 1}（χ(−1) = (−1)^a）。
- ガウス和 τ(χ) = Σ_{x mod N} χ(x) e^{2πi x/N}。𝔀(χ) = τ(χ)/(i^a √N)（ルート数）。
- 加法指標の規約：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}（Tate の学位論文）。
- χ に対応するイデール類指標 ω = ∏_v ω_v を、χ と互いに素な素数 q で ω_q(q) = χ(q) となるように正規化する。
- 局所定数 ε(1/2, ω_v, ψ_v) は Tate の流儀（Tate, "Number theoretic background", Corvallis 1979）で定める。

## 問いとして検討している文

文 E1（既知の式）：𝔀(χ) = (−i)^a · ∏_i (τ(χ_i)/√N_i) · ∏_i ∏_{j≠i} χ_j(N_i)。

文 E2：上の規約のもとで、無限素点の局所定数は ε(1/2, ω_∞, ψ_∞) = (−i)^a、素数 p_i での局所定数は
  ε(1/2, ω_{p_i}, ψ_{p_i}) = [∏_{j≠i} χ_j(N_i)] · τ(χ_i)/√N_i
である。とくに、E1 の交差項 ∏_{j≠i} χ_j(N_i) は素数 p_i の局所定数に属し、それは ω_{p_i}(p_i^{e_i})（p_i の一意化元の冪での ω_{p_i} の値）に等しい。

文 E3：ω_{p_i}(p_i) = ∏_{j≠i} χ_j(p_i) は、ω が主イデール p_i（対角に埋め込んだ有理数 p_i）の上で 1 になること（積公式と同じ形の関係）から決まる。つまり交差項は、素点どうしを主イデールが結ぶことの反映である。

文 E4：E1 の交差項を別の仕方で割り振った形 𝔀(χ) = (−i)^a · ∏_i χ_i(∏_{j≠i} N_j) · τ(χ_i)/√N_i も成り立つが、こちらの各因子は一般に局所定数ではない。

文 E5：関数体（有限体上の 1 変数関数体）でも、大域の ε 因子は局所定数の積で、同じ形の交差項が局所定数に入る。ℚ に固有なのは無限素点の因子 (−i)^a だけである。

## 問い

各文について、次を表にしてください。
1. 既存の結果か、既存の結果からの短い帰結か、文献が見つからないか（の区別）。
2. 答えを持つ文献（著者・題・年・定理や節の番号まで。確かめられなかったものは「未確認」と書く）。
3. 文が誤り、または言い過ぎの場合は、正しい形と反例（とくに、ω の正規化や ψ の規約を変えると E2 の交差項が共役や逆数になるかどうか）。

最後に、「ディリクレ指標のルート数を素点ごとの局所定数に分け、交差項を局所定数の側に入れる」という計算を明示的に書いた文献があるかを、見つかった範囲で書いてください。「見つからなかった」は「存在しない」と書かないでください。

出力は日本語で、表と短い補足だけにしてください。


### records/toy_origin/stage6/outputs/blind_output.md
# 盲検の問いテストの出力（玩具の段 6、2026-11-27 17:1x〜17:2x）

依頼文：`../prompt_blind.md`。文脈を渡さない新しいエージェント（general-purpose、ウェブ検索あり）。所要約 544 秒、ツール使用 19 回。以下は返信の全文。構築側が変えたのは、末尾の参照リストのリンクの URL を省いたことだけ（文献名と arXiv 番号は残した）。

---

## 照合の結果（文 E1〜E5）

| 文 | 区別 | 答えを持つ文献 | 誤り・言い過ぎ、正しい形、反例 |
|---|---|---|---|
| E1 | 既存の結果。ガウス和の乗法性 τ(χ) = ∏_i χ_i(N/N_i) τ(χ_i) と W(χ) = τ(χ)/(i^a√N) を組み合わせ、添字を付け替えたもの | Rohrlich, "Root numbers", PCMI 2009 講義録。式 (1.2)–(1.4) が τ と W の定義、(1.47) が τ(χ_1χ_2) = χ_1(N_2)χ_2(N_1)τ(χ_1)τ(χ_2)。(1.47) は二次指標の節にあるが、証明は中国剰余定理だけなので一般の指標で成り立つ。所収は AMS, IAS/Park City Math. Ser. 18『Arithmetic of L-functions』(2011)、頁は未確認。Vaughan の講義ノート（Math 571, Ch. 2）Theorem 4.2。Montgomery–Vaughan の定理番号は未確認 | 誤りなし。補足：∏_i∏_{j≠i}χ_j(N_i) = ∏_j χ_j(N/N_j)（添字の付け替え）なので、E1 と E4 の交差項は全体としては同じ数 |
| E2 | 既存の結果からの短い帰結。Tate の局所定数の公式に E3 を代入したもの。値は正しい（確信度：高） | Tate 1979 §3.2（分岐の場合）。細かい式番号は未確認。公式の形 ε = ω(c) q^{−a/2} Σ_x ω^{−1}(x)ψ(x/c)（v(c) = a(ω)+n(ψ)）は、Rohrlich (2.55)–(2.56) と Biswas arXiv:1405.6145 の (2.5)・(3.9) で確かめた。無限素点の値：Rohrlich (2.49)（ψ_∞ = e^{−2πix}、(2.69)）で W = i^{−m}。Roy–Schmidt–Yi arXiv:2109.07649 の (155) で ε(s, sgn, ψ_∞) = −i。ディリクレ指標の局所定数の積：Roy–Schmidt–Yi の Lemma 6.1（∏_p ε(0, χ_p, ψ_p) = G(ξ)。Tate の ψ を使い、χ_p(p) = ξ(p) と正規化）。交差項を明示しているかは未確認 | 言い過ぎが 2 点。(a) 「一意化元の冪での値」は一意化元の選び方で変わる。ω_{p_i} は分岐しているので ω_{p_i}(u·p_i) = χ̄_i(u)ω_{p_i}(p_i)。正しくは「有理素数 p_i^{e_i} での値（Tate の公式で c = p_i^{e_i} と取ったとき）」。局所定数の中での「交差項 × ガウス和」の分け方も c の選び方による。不変なのは積だけ。(b) 「交差項は p_i の局所定数に属する」は ψ の選び方による（E4 の行を参照）。ψ を ψ(a·)（a ∈ ℚ^×）に替えると ε_v(1/2) は ω_v(a) 倍になる。積は ω(a) = 1 なので変わらない |
| E2（規約を変えた場合） | — | — | ω の正規化を ω_q(q) = χ̄(q) にした場合：交差項は共役になる（1 の冪根なので逆数と同じ）。p_i の局所定数は ∏_{j≠i}χ̄_j(N_i)·τ(χ̄_i)/√N_i = χ_i(−1)·（E2 の値の共役）。ε_∞ は (−i)^a のまま。積は W(χ̄) = conj W(χ)。ψ を逆の規約（ψ_∞ = e^{2πix}、ψ_p = e^{−2πi{x}_p}）にした場合：交差項は変わらない。動くのは符号だけで、ε_∞ = i^a、ε_{p_i} = χ_i(−1)·（E2 の値）。ψ_∞ だけを替える混合規約では ψ が ℚ 上で自明でなくなり、局所定数の積は大域の ε と一致しない |
| E3 | 既存の結果。Rohrlich の Prop. 2.1(iii) を特殊化したもの：β が p の冪のとき χ_v(β) = χ_∞^{−1}(β)∏_{q∣f, q≠p} ε_q(β)。根拠は K^× 上の自明性 (2.21)。式は正しい（確信度：高） | Rohrlich 同上 Prop. 2.1。Rohrlich の Lecture 2 §5.2、式 (2.60) は虚二次体での同じ機構の具体例 | 式は正しい。導出には ω_∞(p_i) = 1（ω_∞ = sgn^a は正の実数で自明）と、不分岐の q での ω_q(p_i) = 1 も使う。後半の「主イデールが素点を結ぶことの反映」は、Tate の標準の ψ を選んだときにだけ成り立つ解釈で、数学の主張ではない。ψ(x/N) を使うと p_i の因子は χ_i(N/N_i) という χ_i 単独の値になり、素点の間の結びつきは ψ の側（ψ が ℚ 上で自明であること）に移る |
| E4 | 既存の結果。古典的な CRT 分解そのもので、式は正しい | Rohrlich (1.47)、Vaughan Thm 4.2 | 「各因子は一般に局所定数ではない」は言い過ぎで、Tate の標準の ψ に対してだけ正しい。標準の ψ で食い違う反例：N = 15、χ_1 = (·/3)、χ_2 は法 5 の 4 次指標で χ_2(2) = i。p = 3 の因子は E4 では χ_1(5)τ(χ_1)/√3 = −i、局所定数は χ_2(3)τ(χ_1)/√3 = 1 で一致しない。一方、大域の加法指標 x ↦ ψ(x/N)（ℚ 上で自明）を使うと、E4 の各因子はちょうど ε(1/2, ω_{p_i}, ψ_{p_i}(·/N)) に等しい。理由：ω_{p_i}(1/N) = ω_{p_i}(N_i)^{−1}·χ_i(N/N_i)。ほかの素点では 1/N が単数か正の数なので、因子は 1 のまま。正しい形は「標準の ψ に対しては局所定数でないが、ψ(·/N) に対しては局所定数である」 |
| E5 | 前半の「大域の ε は局所定数の積」は既存の結果。中間の「同じ形の交差項」は、F_q(T) で dT から ψ を作る場合なら短い帰結（確信度：中。自分の計算で、文献とは照合していない）。最後の一文は言い過ぎ | Tate 1979 §3 の大域の節（番号は未確認）。Weil, Basic Number Theory, Ch. VII（節は未確認）。Rosen, Number Theory in Function Fields (2002) Ch. 4（Andrade–Miller–Pratt–Trinh arXiv:1404.2435 が、この 2 冊を関数体のディリクレ L 関数の参考文献に挙げている）。局所定数の明示式は未確認 | F_q(T) での正しい形：M = ∏P_i^{e_i}（モニック既約）、ψ = ψ_0(Res(x·dT)) はすべての有限素点で不分岐で、n(ψ_∞) = −2。このとき ω_∞ は 1/T と 1+π_∞O_∞ の上で自明、F_q^× の上で χ に等しい。モニックな P_i では ω_∞(P_i) = 1 なので ω_{P_i}(P_i) = ∏_{j≠i}χ_j(P_i) となり、交差項は同じ形になる。ただし次の 3 点がある。(i) ∞ にも局所定数がある。χ が奇（F_q^× の上で自明でない）なら ε_∞ は F_q 上の正規化したガウス和で、これが (−i)^a の類似物。パリティは ±1 ではなく F_q^× の指標になる。(ii) 一般の関数体（種数が正、または素点が単項でない場合）では E3 の機構がそのままは使えず、微分の因子（次数 2g−2）に乗る素点でも ω_v(c_v) が局所定数に入る。(iii) 交差項がどの局所定数に入るかが ψ の選び方によるのは ℚ と同じ。したがって ℚ に固有なのは「(−i)^a だけ」ではなく、「標準の ψ がすべての有限素点で不分岐であること、類数 1、無限素点がアルキメデス的であること」の組み合わせ |

## 「ルート数を素点ごとに分け、交差項を局所定数の側に入れる」計算を明示的に書いた文献

- **見つかったもの（いずれもディリクレ指標そのものではない）**
  - Rohrlich の Lecture 2 §5.2、式 (2.57)–(2.62)。Tate と同じ ψ を使い、局所ルート数 W(χ_v) に交差項 ∏_{q≠p}(p/q) を入れて計算している。ただし対象は虚二次体 ℚ(√−D) のヘッケ指標（Prop. 1.5）。同じ講義録でも、二次のディリクレ指標の節は局所分解ではなく CRT による (1.47) で済ませている。
  - Roy–Schmidt–Yi arXiv:2109.07649 の Lemma 6.1 と式 (157)。ディリクレ指標の局所定数の積がガウス和 G(ξ) になることを、Tate の ψ のもとで述べている。ただし s = 0 での主張で、p ∣ 導手での χ_p(p) を他の成分で書いているかは未確認。
- **見つからなかったもの**：一般の（二次とは限らない）ディリクレ指標について ε_{p_i} = ∏_{j≠i}χ_j(N_i)·τ(χ_i)/√N_i と明示した文献。これは存在しないという意味ではない。教科書の演習（Bump『Automorphic Forms and Representations』§3.1、Ramakrishnan–Valenza 第 7 章など）にある可能性はあるが、確かめていない。
- **検索した範囲**：一般のウェブ検索（英語）と、上に挙げた PDF の中身。MathSciNet、zbMATH、教科書の本文は見ていない。

## 補足

- **数値での確認（証明ではない）**：インラインの Python で、N ∈ {15, 20, 63, 120, 140, 48, 75} の原始指標の組 67 個について次を確かめた。
  1. W(χ) = (−i)^a·∏(E2 の p_i 因子) と、E4 の形の積が成り立つ。
  2. ψ(·/N) に対する局所定数が E4 の各因子と一致する。
  3. ψ を逆符号にした場合と、ω を共役に正規化した場合の上の表の式が成り立つ。

  最大誤差は 7×10⁻¹⁵。E2 と E4 の因子が素点ごとに食い違ったのは 67 組中 56 組。局所定数の値そのものは Tate の公式から出したもので、数値で独立に確かめたのは積の整合性だけ。
- 文献は以下を参照した：Rohrlich, Root numbers（PCMI 講義録）、AMS PCMS 18、Roy–Schmidt–Yi, arXiv:2109.07649、Biswas, arXiv:1405.6145、Vaughan, Math 571 のノート、Andrade–Miller–Pratt–Trinh, arXiv:1404.2435。
- 依頼文以外のリポジトリのファイルは読んでおらず、ファイルへの書き込みもしていない。


### records/toy_origin/stage6/outputs/blind_meta.txt
盲検 終了 17:21:34（所要 約 544 秒、ツール 19 回）


### records/toy_origin/stage7/prompt_blind.md
あなたは文献照合の担当です。以下の定義と文だけを読み、問いに答えてください。この問いを作った研究の文脈は渡しません。リポジトリ内のファイルは読まないでください（読める場合でも、判断の根拠にしないでください）。ウェブ検索は使ってかまいません。

## 定義

- e(t) = e^{2πit}（t ∈ ℚ/ℤ または ℝ/ℤ）。水準 N の加法指標 ψ_N(x) = e(x/N)（x ∈ ℤ/N）。
- N ∣ M のとき、2 種類の写像：還元 r_{M→N}：ℤ/M → ℤ/N（x mod M ↦ x mod N）と、埋め込み ι_{N→M}：ℤ/N → ℤ/M（x ↦ (M/N)x）。
- 素数 p ごとの Tate の加法指標 ψ_p(x) = e^{+2πi{x}_p}（x ∈ ℚ_p、{x}_p は p 進の小数部分）。
- χ は導手 f の原始的なディリクレ指標で、f = ∏ f_i（f_i = p_i^{e_i}）、χ = ∏ χ_i。水準 N（f ∣ N）では χ を (ℤ/N)^× の上の指標として見る（原始的でないことがある）。
- 水準 N の作用素 T_N = J∘H_N/√N：(H_N g)(y) = Σ_{x ∈ ℤ/N} g(x) cas(2πxy/N)、cas θ = cos θ + sin θ、(J h)(u) = h(u^{−1})（u ∈ (ℤ/N)^×）。単数の上の関数に作用させる。
- 引き戻し：N ∣ M のとき、(ℤ/N)^× の上の関数 g を (ℤ/M)^× の上の関数 g∘r_{M→N} に送る。

## 問いとして検討している文

文 L1：ψ_M∘ι_{N→M} = ψ_N なので、{(ℤ/N, ψ_N)} は埋め込みに沿って両立する直系をなし、その直極限は (ℚ/ℤ, e) である（ℤ/N を (1/N)ℤ/ℤ ⊂ ℚ/ℤ と同一視）。一方、還元に沿っては両立しない（ψ_N∘r_{M→N} ≠ ψ_M）。

文 L2：ℚ/ℤ ≅ ⊕_p ℚ_p/ℤ_p のもとで e(x) = ∏_p ψ_p(x)。つまり直極限の加法指標は Tate の加法指標の有限部分そのものである。

文 L3：水準 N の作用素 T_N は、原始指標 χ（f = N）の上では位相 W(χ) = τ(χ)/(i^a√f) を掛けるが、導手 f < N の指標の上では一般に W(χ) と違う値を掛ける。そのため T_N の族は引き戻しと両立しない。位相を各指標の導手で決めた作用素（χ に W(χ_prim) を掛ける）の族は引き戻しと両立し、両立する族はそれだけである。

文 L4：ガウス和 τ(χ) = Σ_{x mod f} χ(x) e(x/f) を素数ごとに分けると τ(χ) = ∏_i χ_i(f/f_i) τ(χ_i) となる。この交差項 χ_i(f/f_i) は、ℚ/ℤ の点 1/f の p_i 成分が u_i/f_i（u_i ≡ (f/f_i)^{−1} mod f_i）であることから来る。つまり、すべての素数で共通の 1 点 1/f で加法指標を測ることと、素数ごとに自分の点 1/f_i で測ることの違いが交差項である。

文 L5：乗法の側の指標（(ℤ/N)^× の指標）は還元に沿った逆極限 Ẑ^× の側で両立し、加法の側の指標は埋め込みに沿った直極限 ℚ/ℤ の側で両立する。Ẑ^× は ℚ/ℤ の自己同型群として働き（Aut(ℚ/ℤ) ≅ Ẑ^×）、ガウス和は Ẑ^× の指標と ℚ/ℤ の加法指標をこの作用で組み合わせたものである。これは Bost–Connes 系の対称性の構造と同じである。

## 問い

各文について、次を表にしてください。
1. 既存の結果か、既存の結果からの短い帰結か、文献が見つからないか（の区別）。
2. 答えを持つ文献（著者・題・年・定理や節の番号まで。確かめられなかったものは「未確認」と書く）。
3. 文が誤り、または言い過ぎの場合は、正しい形と反例（とくに L3 の「両立する族はそれだけ」が、どの条件のもとで正しいか）。

最後に、「水準 N の加法指標を ℚ/ℤ の点 1/N として扱い、ガウス和の交差項をその点の素数成分として読む」扱いを明示的に書いた文献があるかを、見つかった範囲で書いてください。「見つからなかった」は「存在しない」と書かないでください。

出力は日本語で、表と短い補足だけにしてください。


### records/toy_origin/stage7/outputs/blind_output.md
# 盲検の問いテストの出力（玩具の段 7、2026-11-27 18:25〜18:33）

依頼文：`../prompt_blind.md`。文脈を渡さない新しいエージェント（general-purpose、ウェブ検索あり）。所要約 459 秒、ツール使用 22 回。以下は返信の全文。

取得の経緯：最初の返信は構築側の会話にだけ届き、ファイルに書き出す前に会話の文脈が切り替わった。そこで 18:3x に同じエージェントへ「最終報告の全文を一字も変えずに再送。追加の調査・修正・要約・前置きはしない」と依頼し（ツール使用 0 回、約 30 秒）、その返信をここに置いた。最初の返信との字句の一致は確かめられない。判定の内容（L1〜L5 の区別、L3 の式と条件 (b)、反例の並び、数値の件数と誤差、最後の問いの答え）は、構築側が最初の返信から書き留めた要約とすべて合っている。

構築側が変えたのは 2 点だけ：末尾の出典の行からリンクの URL を省いた（文献名と arXiv 番号は残した）。通知の経路で実体参照（&amp;lt;・&amp;gt;）になっていた不等号を元の記号 < と > に戻した。

---

## 照合の結果（依頼文 `records/toy_origin/stage7/prompt_blind.md` への答え）

| 文 | 区別 | 答えを持つ文献 | 誤り・言い過ぎと正しい形 | 確信度 |
|---|---|---|---|---|
| L1 | 既存（標準的な事実） | ℚ/ℤ の構造（p 冪の捩れの直和）：K. Conrad「The Character Group of Q」（年の記載なし）Remark 2.2・2.5（確認済み）。直極限としての記述と (ℚ/ℤ)^∨ ≅ Ẑ の番号つきの出典は未確認（教科書的な事実） | 正しい。補足すると、還元に沿っては ψ_N∘r_{M→N} = ψ_M^{M/N} なので、M = N のときだけ一致する。族 {ψ_N} は lim← Hom(ℤ/N, S¹) ≅ Ẑ の元 1 に当たる | 高 |
| L2 | 既存 | Conrad 同上：式 (2.1)（r = Σ_p {r}_p ＋整数）、Remark 2.5、§4（s ∈ ℚ で e^{2πis} = ∏_p e^{2πi{s}_p}）、§3（ψ_∞ = e^{−2πix}）（確認済み）。D. Rohrlich「Root numbers」PCMI 講義録（2009）の (2.69)–(2.70) も同じ規約（確認済み）。Tate の学位論文（1950、Cassels–Fröhlich 1967 に所収）§2.2・§4.1（番号は未確認） | 軽い言い過ぎ。ψ_f = ∏ψ_p は 𝔸_f の指標で、ℚ/ℤ の指標ではない。正しい形は「ψ_f は Ẑ の上で自明で、𝔸_f/Ẑ ≅ ℚ/ℤ（𝔸_f = ℚ + Ẑ、ℚ ∩ Ẑ = ℤ）を通じて e を誘導する。言い換えると ψ_f\|_ℚ = e = ψ_∞^{−1}\|_ℚ」。符号は ψ_p = e^{+2πi{x}_p} という規約による（逆の規約では e(−x) になる） | 高 |
| L3 | 固有値の部分：既存の結果からの短い帰結。「W(χ_prim) の族が両立する」：直ちに出る。「両立する族はそれだけ」：このままでは誤り。T_N の族そのものを扱った文献は見つからなかった | Montgomery–Vaughan『Multiplicative Number Theory I』（2007）第 9 章：Thm 9.5（(n,q)=1 の場合）、Thm 9.7（原始的な場合、\|τ\| = √q）、Thm 9.10（τ(χ) = μ(q/d)χ*(q/d)τ(χ*)）（番号は確認済み）。W(χ) が関数等式のルート数であること：Davenport『Multiplicative Number Theory』第 9 章（未確認） | 単数の上で T_N χ = μ(N/f)·χ*(N/f)·√(f/N)·W(χ*)·χ となる。f < N なら絶対値は √(f/N) 以下で 1 より小さいので、W(χ*) とは**常に**違う（「一般に」ではない）。値は位相ですらなく、N/f が平方因子をもつか gcd(N/f, f) > 1 のときは 0。一意性が成り立つ条件と反例は補足 1 | 高 |
| L4 | 公式は既存。説明は標準的な CRT による証明の言い直し | Montgomery–Vaughan Thm 9.6（τ(χ1χ2) = τ(χ1)τ(χ2)χ1(q2)χ2(q1)、確認済み）。因子が 3 つ以上の形は帰納法で直ちに出る。Rohrlich 同上の Prop. 2.1・(2.60)–(2.61) は、交差項を「他の素数での局所指標の値」として乗法の側に置いている（確認済み） | 正しい（1/f ≡ Σu_i/f_i mod ℤ も成り立つ）。ただし交差項は規約によって決まる量である。Σχ(x)e(ax/f) = χ̄(a)τ(χ)（Thm 9.5）なので、交差項 χ_i(f/f_i) = χ̄_i(u_i) は、p_i での和を e(·/f_i) で取るか e(u_i·/f_i) で取るかの比にすぎない。後者は共通の e(·/f) の p_i 成分で、こちらで取れば交差項は消える。不変量としての内容はない。同じ項は乗法の側（イデール類指標の局所成分を他の素数で評価した値）にも置ける | 高 |
| L5 | 各部分は既存（標準）。「Bost–Connes 系の対称性の構造と同じ」は言い過ぎ | End(ℚ/ℤ) ≅ Ẑ：V. Shirbisheh、arXiv:0808.1767（2008 年頃）Remark 2.7(a)。Bost–Connes 系：Bost–Connes, Selecta Math. 1（1995）411–456（原論文の定理番号は未確認）。概説では Shirbisheh の Thm 2.10(c)：β = ∞ で、類体論の同型 Gal(ℚ^ab/ℚ) → Aut(ℚ/ℤ) が対称性と Galois 作用を絡める（確認済み）。この概説にはガウス和も Dirichlet 指標も出てこない（確認済み）。Dirichlet 指標 ＝ Ẑ^× の連続指標の番号つきの出典は未確認 | 正しい形は「τ(χ) = Σ_{u∈(ℤ/f)^×} χ(u)e(u·(1/f)) は、点 1/f の Ẑ^× 軌道を χ で重みづけた和（ラグランジュの分解式）で、BC 系の対称性群と同じ作用を使う」まで。BC 系の残りの構造（ℕ^× の μ_n、時間発展、KMS 状態）に当たるものは文にない。また「乗法は逆極限、加法は直極限」という対比は群そのものの性質ではない。ℤ/N は還元に沿う逆系（極限 Ẑ）と埋め込みに沿う直系（極限 ℚ/ℤ）の両方をなし、2 つは双対である。(ℤ/N)^× がなすのは逆系だけ。加法指標も Ẑ の連続指標として見れば、その全体は ℚ/ℤ（直極限）になる | 中〜高 |

## 補足

1. **L3 の「両立する族はそれだけ」について。**
   - **反例**：次の族はどれも引き戻しと両立する。恒等写像、χ ↦ conj(W(χ*))·χ、χ ↦ χ*(−1)W(χ*)·χ、反転 J（g ↦ g(u⁻¹)）、a ∈ Ẑ^× による平行移動。
   - **成り立つ条件**：次の 2 つをともに課すと、U_N χ = W(χ*)χ に限られる。
     - (a) すべての N ∣ M で U_M∘r* = r*∘U_N。
     - (b) 各 N で、U_N は導手がちょうど N の指標が張る空間（新しい部分）の上で T_N と一致する。
   - **理由**：(ℤ/N)^× の上の関数の空間は ⊕_{f∣N} r*(Prim_f) と分かれる。(a) は各 Prim_f の上の作用を上の水準へ運ぶだけなので、(b) を外すと、各 N の新しい部分での U_N を任意の線形写像に選べる。U_N に (ℤ/N)^× の乗法作用との可換性（T_N はこれを持つ）を課しても、自由度は原始指標の上の任意の関数 c(χ*) に減るだけで、一意性にはやはり (b) が要る。N ≡ 2 mod 4 では (b) は空の条件になる。
2. **数値での確認（証明ではない）。** Python で、N ≤ 60 のすべての指標（1,102 個）について、L3 の固有値の式との誤差は最大 8×10⁻¹⁴ だった。f < N で値が W(χ*) と一致した例は 0 件。L4 は、2 つ以上の素数で割れる導手 f ≤ 120 の原始指標について、誤差が最大 6×10⁻¹³ だった。
3. **最後の問い**（加法指標を ℚ/ℤ の点 1/N として扱い、交差項をその点の素数成分として読むことを明示的に書いた文献）。見つかった範囲では、**見つからなかった**。これは存在しないことを意味しない。近いものは次の 4 つ。
   - (i) ψ_N を Ẑ → ℤ/N で引き戻したものが点 1/N ∈ ℚ/ℤ ≅ Ẑ^∨ に当たること。Pontryagin 双対の標準的な事実（番号つきの出典は未確認）。
   - (ii) Conrad の ℚ/ℤ ≅ ⊕ℚ_p/ℤ_p と e = ∏e_p。
   - (iii) Montgomery–Vaughan Thm 9.6 の公式。証明の文面は確認していないので、CRT による証明がこの読みを含んでいる可能性は残る。
   - (iv) Rohrlich の、交差項を局所指標の値として乗法の側に置く読み。
4. **検索の範囲。** ウェブ検索だけで、MathSciNet・zbMATH・書籍本文の全文検索はしていない。中身を確かめたのは、Montgomery–Vaughan 第 9 章の PDF、Conrad の 2 つのノート（「The Character Group of Q」と「Gauss and Jacobi sums」）、Rohrlich の PCMI 講義録、Buzzard「Epsilon constants」、Angdinata の講演資料、Zeff の Tate の学位論文についてのノート、Shirbisheh の概説。後の 4 つには該当する記述はなかった。検索語は、Gauss sum の乗法性と CRT・部分分数・ℚ/ℤ 分解、局所 ε 因子の積、Bost–Connes と Gauss sum の組み合わせ。

出典：MV 第 9 章、Conrad, Character group of Q、Conrad, Gauss–Jacobi sums、Rohrlich, Root numbers、Shirbisheh, arXiv:0808.1767、Buzzard, Epsilon constants、Angdinata の講演、Zeff, Tate's thesis

読んだリポジトリのファイルは依頼文だけで、書き込んだファイルはない（数値の確認はファイルを作らずに実行した）。


### records/toy_origin/stage7/outputs/blind_meta.txt
盲検 終了 18:33（所要 約 459 秒、ツール 22 回）


### records/toy_origin/stage8/prompt_blind.md
あなたは文献照合の担当です。以下の定義と文だけを読み、問いに答えてください。この問いを作った研究の文脈は渡しません。リポジトリ内のファイルは読まないでください（読める場合でも、判断の根拠にしないでください）。ウェブ検索は使ってかまいません。

## 定義

- e(t) = e^{2πit}（t ∈ ℚ/ℤ）。Ẑ^× は副有限整数の単数群で、dx はその正規化したハール測度（全体の測度が 1）。
- 𝓛 = Ẑ^× の上の局所定数関数の空間（= 単数群 (ℤ/N)^× の上の関数の、引き戻し g ↦ g∘(還元) に沿った帰納極限）。
- 反転 J：(Jg)(u) = g(u^{−1})。
- 加法の変換 A：g ∈ 𝓛 に対して (Ag)(t) = ∫_{Ẑ^×} g(x) e(xt) dx（t ∈ ℚ/ℤ）。
- 軌道 O_n = {t ∈ ℚ/ℤ : t の位数がちょうど n} = {v/n : v ∈ (ℤ/n)^×}（n ≥ 1）。
- 読み出し R_n：ℚ/ℤ の上の関数 h に対して (R_n h)(u) = h(u/n)（u ∈ Ẑ^×、u/n は u mod n を使う）。
- χ はディリクレ指標で、χ* はそれを誘導する原始指標、f はその導手、a ∈ {0, 1} は χ(−1) = (−1)^a で決める。χ を 𝓛 の元（Ẑ^× の上の関数）として見る。
- τ(χ*) = Σ_{x mod f} χ*(x) e(x/f)。W(χ*) = τ(χ*)/(i^a √f)。ε_∞(χ) = (−i)^a。
- 水準 N の作用素 T_N（f ∣ N の指標に作用）：(T_N g)(u) = (1/√N) Σ_{x ∈ (ℤ/N)^×} g(x) cas(2π x u^{−1}/N)、cas θ = cos θ + sin θ。
- U_∞：𝓛 の上の線形写像で、U_∞ χ = W(χ*) χ（すべての χ）。

## 問いとして検討している文

文 M1：ℚ/ℤ は軌道 O_n（n ≥ 1）の交わらない和で、O_n ≅ (ℤ/n)^× である。A は 𝓛 の上で水準によらず定まり（引き戻しと両立し）、Ẑ^× の作用と可換である。

文 M2：導手 f の χ と t = v/n ∈ O_n について、(Aχ)(v/n) は f ∤ n なら 0、f ∣ n なら μ(n/f)·χ*(n/f)·τ(χ*)·χ̄(v)/φ(n) である。したがって Aχ が 0 でない軌道は、n/f が平方因子をもたず f と互いに素な O_n だけで、最小のものは O_f である。

文 M3：f ∣ N のすべての χ について T_N χ = ε_∞(χ)·(φ(N)/√N)·J R_N A χ（水準 N の作用素は、A を水準自身の軌道 O_N で読んだもの）。一方 U_∞ χ = ε_∞(χ)·(φ(f)/√f)·J R_f A χ（A を最小の軌道 O_f で読んだもの）。したがって U_∞ は「A → 最小の軌道からの読み出し（導手 f による拡大縮小）→ J → ε_∞」の合成として書け、T_N の族が引き戻しと両立しないのは、読む軌道を O_N に固定することから来る。

文 M4：S_n := (φ(n)/√n)·J R_n A とおくと、Re s > 1/2 で Σ_{n ≥ 1} n^{−s} S_n χ = f^{−s}·(τ(χ*)/√f)/L(s + 1/2, χ*)·χ（L はディリクレの L 関数）。

文 M5：M4 に Tate の局所関数等式の L 因子のうち 1/L(s + 1/2, χ*) だけが現れ、L(1/2 − s, χ̄*) の側が現れないのは、A が ℚ/ℤ = 𝔸_f/Ẑ の上の関数しか見ず、p 進で小さい側（ℤ_p の中の殻 p^k ℤ_p^×、k ≥ 0）が ℚ/ℤ の点 0 につぶれているからである（不分岐な p で 1_{ℤ_p^×} のフーリエ変換 1_{ℤ_p} − p^{−1}1_{p^{−1}ℤ_p} の、殻 k ≥ 0 の部分が L(1−s, χ̄) を、殻 k = −1 の部分が 1/L(s, χ) の因子を与える）。

## 問い

各文について、次を表にしてください。
1. 既存の結果か、既存の結果からの短い帰結か、文献が見つからないか（の区別）。
2. 答えを持つ文献（著者・題・年・定理や節の番号まで。確かめられなかったものは「未確認」と書く）。
3. 文が誤り、または言い過ぎの場合は、正しい形と反例（とくに、規格化の定数、ε_∞ の符号、M5 の s のずれ、自明な指標と p = 2 の場合）。

最後に、「ルート数（ε 因子）を、Ẑ^× の上の指標の加法の変換を ℚ/ℤ の最小の Ẑ^× 軌道（点 1/f の軌道）で読んだ値として書く」扱いと、「原始的でない指標のガウス和を水準 n について n^{−s} で足した級数が 1/L を与える」扱いを、明示的に書いた文献があるかを、見つかった範囲で書いてください。「見つからなかった」は「存在しない」と書かないでください。

出力は日本語で、表と短い補足だけにしてください。


### records/toy_origin/stage8/outputs/blind_output.md
# 盲検の問いテストの出力（玩具の段 8、2026-11-27 18:47〜18:57）

依頼文：`../prompt_blind.md`。文脈を渡さない新しいエージェント（general-purpose、ウェブ検索あり）。所要約 610 秒、ツール使用 30 回。以下は返信の全文。

構築側が変えたのは 2 点だけ：リンクの URL を省いた（表の中のリンクと末尾の参照の行。リンクの文字列、文献名、arXiv 番号は残した）。通知の経路で実体参照になっていた不等号を元の記号 > に戻した。

条件についての注意：照合者は「CLAUDE.md はシステムが文脈に入れたもので、判断の根拠にしていません」と申告している。このリポジトリでは、新しいエージェントにも CLAUDE.md（研究の文脈を含む）が自動で渡る。したがってこの盲検は、依頼文だけを渡すという条件を完全には満たしていない（`blind_meta.txt`）。

---

# 文献照合：文 M1〜M5

数値はファイルを作らずに標準入力の Python で確かめました。

- M2：法 ≤ 40 の全指標、n ≤ 60 で 111,720 件。最大誤差は 2×10⁻¹⁴ でした。
- M3：N ≤ 60 の全指標で、最大誤差は 7×10⁻¹⁴ でした。
- M4：s = 1.3 で 7 個の指標を試し、差は 3×10⁻⁵ 以下で、打ち切り誤差の範囲でした。
- M5：p = 3、s′ = 0.8+0.3i で局所の積分を計算しました。

## 表

| 文 | 1. 区別 | 2. 文献 | 3. 誤り・言い過ぎと正しい形 |
|---|---|---|---|
| M1 | 既知の初等的な事実と、定義から直ちに出ること（確信度：高） | 特定の定理番号は挙げません（標準的な事実） | 「Ẑ^× の作用と可換」は言い過ぎです。正しくは A(g(u·)) = (Ag)(u⁻¹·) で、作用を逆元にして絡みます（u=3、t=1/7 で数値確認）。同じ向きの作用 h ↦ h(u·) では Aχ は χ̄ で変わります。M3 に J が要るのはこのためです。補足：正規化したハール測度は加法のハール測度の制限ではありません（Ẑ^× の加法測度は 0）。水準 L ごとに L/φ(L) 倍ずれます。 |
| M2 | 既存の結果の言い換え（確信度：高） | Montgomery–Vaughan, *Multiplicative Number Theory I* (2007), **Theorem 9.12** を q = lcm(f,n)、引数 vq/n で使うと r = n になり、そのまま M2 です。f ∣ n の場合は Theorem 9.10。局所版は Tate の学位論文 §2.5 | 正しいです。χ̄(v) は χ̄*(v) と書くべきです（v は mod n でしか定まらない）。自明な指標では値は μ(n)/φ(n) です。導手 2 の原始指標はないので、p = 2 の例外はありません（f = 4, 8 も確認済み）。 |
| M3 | 等式は正しい（数値確認）。T_N の式は MV 9.10 と cas = ((1−i)/2)e + ((1+i)/2)ē からの短い帰結です。U_∞ の式は **Gauss 和の定義の書き直し**です。τ(χ*) = φ(f)·(Aχ)(1/f) は A の定義そのもので、構成から自明な形の一致です（確信度：高） | MV Thm 9.10。W(χ*) が標準のルート数であること：Davenport 第 9 章（番号は未確認） | ε_∞ = (−i)^a は、核 cas(2πx u⁻¹/N) と e(t)=e^{2πit} のもとで正しいです。**言い過ぎ (i)**：等式は指標ごとにしか成り立ちません。R_f A は導手の小さい成分を消さない（R_p A 1 = −1/(p−1) ≠ 0）ので、作用素としては U_∞ = ε_∞ Σ_f (φ(f)/√f) J R_f A P_f と書く必要があります（P_f は導手がちょうど f の成分への射影）。反例：g = 1 + χ（χ は mod p で原始的）では「最小の軌道」が一つに決まりません。(ii) 両立しないことは実際に起きます（T₁1 = 1、T₂1 = −1/√2、T₄1 = 0）。N だけで決まる正規化に取り替えても直りません（N = p² では f = 1 の成分が 0 になる）。したがって、原因を軌道の選択に置く読みは妥当です。 |
| M4 | 既存の結果からの短い帰結（確信度：高） | MV Thm 9.10 と Σμ(m)χ(m)m^{−w} = 1/L(w,χ) から出ます。自明な指標の場合は Ramanujan (1918) の Σ_q c_q(m)q^{−s} = σ_{1−s}(m)/ζ(s) で m = 1 としたもの（EoM。式番号は未確認） | 正しいです（Re s > 1/2 で絶対収束）。S_n に ε_∞ を含めていないので、定数は W ではなく τ/√f です。ずれ s+1/2 も正しいです。自明な指標では 1/ζ(s+1/2) になります。 |
| M5 | 主文は発見的な説明として概ね妥当です。括弧内は**誤り**です。説明全体を書いた文献は見つかりませんでした | Tate §2.5（ただし不分岐の検定関数は 1_{ℤ_p} で、1_{ℤ_p^×} ではない。γ が検定関数によらないことは Thm 2.4.1）。殻ごとの形は Burnol, arXiv:math/9811040 (1998) の 𝓕(θ) = −(1/p)θ₁ + (1−1/p)Σ_{i≤0}θ_i | 下の補足に詳しく書きます。 |

## M5 の訂正（数値で確認済み）

- **(a) 殻ごとの割り当ては誤りです。**
  - 殻 k ≥ 0 の寄与は (1−p⁻¹)·L(1−s′, χ̄) で、L(1−s′, χ̄) ではありません。
  - 殻 k = −1 の寄与は −χ(p)p^{−s′} という足し算の項で、1/L(s′, χ) ではありません。
  - 因子に分かれるのは別の分け方です。1_{ℤ_p} の項が L(1−s′, χ̄) を与え、全体はその (1−χ(p)p^{−s′}) 倍になります。
  - 正しい形：vol(ℤ_p^×) = 1 で正規化し、ℤ_p を重み 1 の 1 点につぶすと、「つぶした点＋殻 −1」が 1 − χ(p)p^{−s′} = 1/L_p(s′, χ) になります。
- **(b) s のずれ。** 括弧内の s は Tate の変数 s′ = s + 1/2 です。明記しないと主文の L(1/2 − s) と合いません。
- **(c) χ(p) の出どころ。** 不分岐な p での χ(p) は、入力の p 成分（指標を含まない 1_{ℤ_p^×}）からは出ません。分岐する素点の値 χ*(n/f) から来ます。Tate の ω_p(p) と同一視するには、ω が ℚ^× の上で自明であること（積公式）が要ります。1/L に χ と χ̄ のどちらが出るかは、ω_p(p) = χ(p) と置くか χ̄(p) と置くかの規約で決まります。
- **(d) 理由の置き場所。** A の出力は Ẑ 不変なので、A 自体は 𝔸_f 上のフーリエ変換の情報を失っていません（ℤ_p の上では定数 1−p⁻¹）。失われるのは、M4 の重み n^{−s} が Ẑ の上で定数であることによります。理由は「A」ではなく「ℚ/ℤ の上で n^{−s} を付けて足すこと」に置くのが正確です。

## 二つの扱いを明示した文献

- **ルート数を最小の軌道 1/f で読む扱い：** 見つかりませんでした。部品になる文献はあります。
  - Tate §2.5：分岐する指標の局所の変換が一つの殻に載り、その値がルート数になる。
  - MV Thm 9.7・Cor 9.8：原始指標では Σχ(a)e(an/q) = χ̄(n)τ(χ)。
  - ただし原始指標では、「1/f で読む」ことは τ の定義そのものです。
- **原始的でない指標の Gauss 和を n^{−s} で足して 1/L を得る扱い：** 指標つきの形を明示した文献は見つかりませんでした。
  - 自明な指標の場合は Ramanujan (1918) にあります。
  - 近いが同じ形ではないもの：指標つき Eisenstein 級数の係数計算で、法についての和から 1/L(2u, ·) が出る例があります（arXiv:1710.00914 Thm 3.4、Young, arXiv:1710.03624）。
- 検索した範囲：ウェブ検索 12 回ほど（語：imprimitive Gauss sum、Dirichlet series over moduli、Ramanujan sums with characters、Tate local Fourier transform、Bost–Connes Gauss sums、Ẑ^× Fourier transform root number）と、上の文献のうち 6 件の本文。MathSciNet と zbMATH は使っていません。見つからなかったことは、存在しないことを意味しません。

参照：MV 第 9 章、Tate 1950（OCR の質が悪く、式は未照合）

リポジトリのファイルは一つも読んでいません（CLAUDE.md はシステムが文脈に入れたもので、判断の根拠にしていません）。リポジトリへの書き込みはありません。ただし、/tmp に空のファイルを誤って 1 つ作り、すぐに削除しました。


### records/toy_origin/stage8/outputs/blind_meta.txt
盲検 開始 18:47、終了 18:57（所要 約 610 秒、ツール 30 回）。照合者の申告：リポジトリのファイルは読んでいないが、CLAUDE.md がシステムによって文脈に入っていた（判断の根拠にはしていないとのこと）。/tmp に空のファイルを誤って作り、すぐ削除したとのこと。


### records/toy_origin/stage9/prompt_blind.md
あなたは文献照合の担当です。以下の定義と文だけを読み、問いに答えてください。この問いを作った研究の文脈は渡しません。リポジトリ内のファイルは読まないでください（読める場合でも、判断の根拠にしないでください。システムが文脈に入れたファイルがあれば、それも根拠にしないでください）。ウェブ検索は使ってかまいません。

## 定義

- p は素数。ℚ_p の加法指標 ψ_p(x) = e^{+2πi{x}_p}（{x}_p は p 進の小数部分）。dx は vol(ℤ_p) = 1 のハール測度。F_p g(y) = ∫ g(x) ψ_p(xy) dx。
- ユニタリな反転 (J_p g)(x) = |x|_p^{−1} g(x^{−1})（L²(ℚ_p, dx) の上でユニタリ）。
- 殻 S_k = p^k ℤ_p^×（k ∈ ℤ）。k → +∞ が点 0（p 進で小さい側）、k → −∞ が点 ∞（大きい側）。
- χ は ℤ_p^× の指標で、導手の指数 e ≥ 0（e = 0 は自明）。χ の成分：g(x) = Σ_k c_k χ(u(x)) 1_{S_k}(x)（u(x) は x の単数部分）の形の関数。正規化した係数 c̃_k = c_k·(vol S_k)^{1/2}。
- τ(χ) = Σ_{u mod p^e} χ(u) e(u/p^e)（e ≥ 1）。
- ω は ℚ のイデール類指標で、p での成分を ω_p(p^k u) = w^k·(単数の上の指標) と書く（w = ω_p(p)）。

## 問いとして検討している文

文 P1（分岐、e ≥ 1）：J_p∘F_p は χ の成分を保ち、正規化した係数の上で c̃ ↦ (c̃′_{k+e} = ε·c̃_k)、ε = τ(χ)/p^{e/2}（|ε| = 1）と働く。つまり付値の軸の上の幅 e の平行移動に位相を掛けたものである。固有ベクトルは c̃_{k+e} = (λ/ε)c̃_k を満たす数列（幅 e の窓の両端を位相 λ/ε で貼り合わせた数列）である。

文 P2（不分岐、e = 0）：J_p∘F_p は χ の成分（単数の上で定数の関数）の上で平行移動ではなく、差 m − k だけによるローラン作用素で、その記号（Σ_d M_d z^d、M_d は c̃_k から c̃_{k+d} への係数）は σ(z) = (1 − p^{−1/2}z)/(1 − p^{−1/2}z^{−1})（|z| = 1）である。z = w·p^{−it} とおくと σ は γ 因子 L(1−s, ω_p^{−1})/L(s, ω_p)（s = 1/2 + it、ω_p は w で決まる不分岐な指標）に等しい。

文 P3：Tate の局所定数で、交差項（大域のルート数を素点ごとに分けたときの因子 w^e = ω_p(p)^e）は、J_p∘F_p の作用そのものには現れず、付値の軸の 1 歩ごとに w を掛ける指標で測ったときの、e 歩の平行移動の累積（ホロノミー）として現れる。

文 P4：イデール類群 C_ℚ ≅ Ẑ^× × ℝ_{>0} では、主イデール p^e を使うと、p の付値の軸の幅 e の平行移動は、無限素点の ℝ_{>0} の対数の軸の e·log p の平行移動と、他の素数の単数の座標への p^{−e} の掛け算に移る。後者を指標で測った値が交差項であり、すべての分岐する素数の平行移動の合計 log f（f は導手）が、大域の ε(s, χ) = ε(1/2, χ) f^{1/2−s} の因子 f^{1/2−s} に当たる。

文 P5：無限素点の J∘F（ℝ の上）は、符号の指標 sgn^a の成分の上で Γ 因子の比を記号とする作用素であり、s = 1/2 + it での位相は t について線形でない（平行移動ではない）。一方、分岐する素数では位相が t について線形（−e t log p）で、平行移動である。

## 問い

各文について、次を表にしてください。
1. 既存の結果か、既存の結果からの短い帰結か、文献が見つからないか（の区別）。
2. 答えを持つ文献（著者・題・年・定理や節の番号まで。確かめられなかったものは「未確認」と書く）。
3. 文が誤り、または言い過ぎの場合は、正しい形と反例（とくに、正規化の定数、平行移動の向き（k ↦ k+e か k ↦ k−e か）、ε の χ と χ̄ の取り違え、p = 2、P2 の記号の z と z^{−1} の向き、P3 の w^e と w^{−e} の向き）。

最後に、「素数の点の局所のフーリエ変換と反転の合成を、付値の軸の上の窓の貼り合わせ（導手の指数を幅とする平行移動）として書き、交差項をそのホロノミーとして読む」扱いを明示的に書いた文献があるかを、見つかった範囲で書いてください。「見つからなかった」は「存在しない」と書かないでください。

出力は日本語で、表と短い補足だけにしてください。数値で確かめる場合はファイルを作らずに実行してください。最後に、読んだリポジトリのファイルと書き込んだファイルの有無、システムが文脈に入れたファイルの有無を 1 行で書いてください。


### records/toy_origin/stage9/outputs/blind_output.md
# 盲検の問いテストの出力（玩具の段 9、2026-11-27 19:21〜19:33）

依頼文：`../prompt_blind.md`。文脈を渡さない新しいエージェント（general-purpose、ウェブ検索あり）。所要約 724 秒、ツール使用 33 回。以下は返信の全文。

構築側が変えたのは 2 点だけ：リンクの URL を省いた（表の中のリンク。リンクの文字列、文献名、arXiv 番号は残した）。通知の経路で実体参照になっていた不等号を元の記号 > に戻した。

条件についての注意：照合者は、CLAUDE.md がシステムによって文脈に入っていたと申告している（判断の根拠にはしていない。CLAUDE.md にあった Burnol の arXiv 番号は、独立に検索して本文で確かめたとのこと）。段 8 と同じく、盲検の条件は完全ではない（`blind_meta.txt`）。

---

## 文献照合の結果（P1〜P5）

P1 の固有ベクトルの部分は誤りです（向きが逆で、しかも ℓ² の固有ベクトルではありません）。ほかの文は、既存の結果か既存の結果からの短い帰結です。P4 は対数軸の符号の指定が足りず、P5 は対比の立て方が言い過ぎです。数値の確認はすべて標準入力で渡した Python で行い、ファイルは作っていません。

| 文 | 1. 区別 | 2. 答えを持つ文献 | 3. 判定・正しい形・反例 |
|---|---|---|---|
| P1 作用素の部分 | 既存の結果からの短い帰結（確信度：高） | Tate 学位論文 1950（走査版）§2.4 定理 2.4.1（局所関数等式）、§2.5（分岐する場合の ρ(c) は絶対値 1 のルート数。OCR が崩れていて、式の細部は未確認）。Burnol「Scattering on the p-adic field and a trace formula」IMRN 2000 no.2（arXiv math/9901051）節 "Additive and multiplicative Fourier analysis on a local field" の定理 I：F(l)(χ;z)=Γ(χ;z)·l(χ̄;z̄)。分岐では Γ(χ;z)=w(χ)z^{e(χ)+δ}、z は拡大縮小 U(1/π) のスペクトルでの表示。w(χ) の値は「使わない」と書かれている。ε の値は Vladimirov「Tables of Integrals of Complex-valued Functions of p-Adic Arguments」（arXiv math-ph/9911027）§8 の (8.16)〜(8.18) と (17.48) から出る（問いと同じ規約 ψ_p=e^{+2πi{x}_p}）。Vladimirov はこの部分の出典に Gel'fand–Graev–Pyatetskii-Shapiro 1969 を挙げているが、その章節は未確認 | 正しい。数値で確かめた範囲は p=2（e=2,3）、p=3（e=1,2）、p=5,7（e=1）で、誤差は 1e-12 以下。向き k↦k+e（0 の側へ）、ε=τ(χ)/p^{e/2}（τ(χ̄) ではない）、正規化 (vol S_k)^{1/2} のいずれも正しい。補足が 3 点ある。(a) F だけでは χ 成分は χ̄ 成分へ行き、J で χ 成分に戻る。(b) JF\|_χ g = τ(χ)·g(p^{−e}·) で、これは ε×（ユニタリな拡大縮小）である。(c) p=2 では e=1 が存在しない。e≥2 では式はそのまま成り立つ。核を ψ(−xy) に取ると、ε は χ(−1)τ(χ)/p^{e/2} になる |
| P1 固有ベクトルの部分 | 誤り（確信度：高） | — | 固有方程式は λc̃_{k+e}=εc̃_k なので、正しくは c̃_{k+e}=(ε/λ)c̃_k（言い換えると c̃_k=(λ/ε)c̃_{k+e}）。反例：λ=iε とし、文の数列 c̃_{k+e}=i·c̃_k を入れると、(JFc̃)_{k+e}=εc̃_k なのに λc̃_{k+e}=−εc̃_k となる。文の形が成り立つのは (λ/ε)²=1 のときだけ。さらに \|c̃_k\| は周期 e なので ℓ² に入らない。L²_χ≅ℓ²(ℤ) の上で JF は ε×（両側シフト）^e に等しく、固有値を持たない。スペクトルは単位円全体で、純絶対連続、重複度 e。「固有ベクトル」は「一般化固有ベクトル（Floquet–Bloch 型）」と書く必要がある |
| P2 | 記号の式は既存の結果、γ 因子との同定は短い帰結（確信度：高） | Burnol「Spectral analysis of the local conductor operator」（arXiv math/9811040、1998。掲載誌は未確認）節 "The continuous spectrum of the p-adic conductor operator"：η_i=(1−1/p)^{−1/2}p^{−i/2}θ(p^i t)、F(θ)=−θ_1/p+(1−1/p)Σ_{i≤0}θ_i。L²_inv(ℚ_p) の上の F は f(z)↦(√p−z)/(√p−z̄)·f(z̄)、反転は η_i↔η_{−i}。Burnol IMRN 2000 の定理 I の Γ(1;z)=z^δ(1−z/√q)/(1−z̄/√q)。Tate 1950 §2.5（不分岐の場合） | 正しい。p=2,3,5 で行列の各要素と記号を数値で確かめた。M_d は d≤0 で (1−1/p)p^{d/2}、d=1 で −p^{−1/2}、d≥2 で 0。規約「M_d は k→k+d、記号は Σ M_d z^d」のもとで σ は文のとおり。注意：Burnol 1998 の η_i は殻 S_{−i} に載るので、その z は問いの z^{−1} に当たる（向きを直すと一致する）。z=w·p^{−it} を代入すると L(1−s,ω_p^{−1})/L(s,ω_p) と恒等的に一致する（ψ_p の導手が ℤ_p なので ε_p=1）。追加（手計算と数値）：巻き数は 0 で、スペクトルは円全体ではなく弧 \|arg\|≤2·arcsin(p^{−1/2}) になる（p=2 で ±π/2） |
| P3 | 標準の式の言い換え（確信度：高）。「ホロノミー」という読みを書いた文献は見つからなかった | Rohrlich「Root numbers」PCMI 2009 講義録（PDF）(2.55)〜(2.56)：W(χ)=χ_u(β)q^{−a(χ)/2}Σχ^{−1}(x)e^{2πi tr(x/β)}、v(β)=a(χ)+n。この因子 χ_u(β) が文の w^e に当たる（式番号は講義録版のもの）。Tate「Number theoretic background」Corvallis 1979 §3（式番号は未確認）。ガウス和の積の公式 τ(χ_1χ_2)=χ_1(N_2)χ_2(N_1)τ(χ_1)τ(χ_2) は古典的（教科書の番号は未確認） | 向き w^{+e} は、ψ_p=e^{+2πi{x}_p}、ψ_∞=e^{−2πix}、不分岐な q で ω_q(q)=χ(q)、Z(g,ω,s)=∫gω\|·\|^s という規約で正しい。このとき χ 成分を見る ω_p の単数部分は χ̄ である（χ ではない）。数値：N=15,35,45,100 で τ(χ)/(i^a√N)=(−i)^a·Π_p w_p^{e_p}τ(χ_p)/p^{e_p/2} が誤差 1e-14 で成り立ち、w^{−e} では最大 2.0 ずれる。実指標の例（N=12,24,72）では向きを区別できない。ω̄ で測る、または ω_q(q)=χ̄(q) と正規化すると w^{−e} になる。「J_pF_p の作用そのものには現れない」は正しい（ε は w によらない）。ただし中身は ω_p(p^e) を記号 z^e に代入した値で、接続も曲率もない。「ホロノミー」は名前の付け替えである |
| P4 | 短い帰結（確信度：中〜高） | C_ℚ≅Ẑ^×× ℝ_{>0} は標準（教科書の番号は未確認）。ε(s,χ)=ε(1/2,χ)f^{1/2−s} は Tate Corvallis §3（未確認）、Davenport『Multiplicative Number Theory』第 9 章（未確認） | 対数軸の符号の指定が足りない。JF の向き k↦k+e は p 成分に p^e を掛けることに当たる。主イデール p^{−e} を掛けると、ℝ_{>0} 成分は p^{−e} 倍（対数軸で **−e log p**）、q≠p の単数成分も p^{−e} 倍になる（単数成分の p^{−e} は文と合っている）。「他の素数」はすべての q≠p だが、指標の値に効くのは q\|f だけで、Π_{q\|f,q≠p}ω_q(p^{−e})=Π χ_q(p)^e=w^e となる。f^{1/2−s} は正規化した係数 c̃ で測った場合で、正規化しない係数では f^{−s}。s への依存がすべて分岐する素数から来るのは、ε_∞ が s によらないからである。各素数の平行移動は別々のテンソル因子の上にあるので、「合計」は C_ℚ に移して ω 成分で測った後でだけ意味を持つ |
| P5 | 既存の結果（確信度：高） | Tate 1950 §2.5（無限素点）。Burnol math/9811040（無限素点を含む Tate–Gel'fand–Graev の Γ 関数、導手作用素は Γ の対数微分）。Rohrlich (2.49)：ε_∞=i^{−m}（ψ=e^{−2πix}） | 正しい。記号は ε_∞·π^{it}·Γ((1/2+a−it)/2)/Γ((1/2+a+it)/2) で、ε_∞=(−i)^a（ψ_∞=e^{−2πix} の場合）。位相の t 微分は log π − Re ψ_dig((1/2+a+it)/2)。a=0、t=0,5,10,20,40 での値は 5.37, 0.23, −0.46, −1.16, −1.85 で一定ではないので、線形ではない。分岐する p の位相は arg(εw^e) − e·t·log p で線形。言い過ぎの点：不分岐な p（P2）も位相は非線形なので、正しい対比は「∞ か有限か」ではなく「局所の L 因子が自明か否か」である |

## 「窓の貼り合わせ／交差項＝ホロノミー」と明示的に書いた文献

**見つかりませんでした。** これは「存在しない」という意味ではありません。

- **最も近いもの**：Burnol IMRN 2000。分岐する成分で Γ(χ;z)=w(χ)z^{e+δ} と書き、散乱行列は S(χ;z)=z^{1−e(χ)−δ}、時間遅れは一定値 (δ+e(χ)−1)log q としています。つまり分岐する成分は純粋な遅れ（平行移動）として扱われていますが、ガウス和は正規化で消しており、ルート数の値も交差項も扱っていません。
- **ほかに近いもの**：
  - Burnol 1998：分岐する部分で導手作用素の固有値が c·log p（離散スペクトル、重複度は無限大）。
  - Rohrlich (2.56)：因子 χ_u(β)。
- **調べた範囲**：ウェブ検索（Tate の局所関数等式、ε 因子、Burnol の散乱、p 進ガンマ関数、ホロノミーとルート数などの語）、上に挙げた Burnol の 2 論文・Vladimirov の表・Rohrlich の講義録・Tate の走査版の本文。
- **調べていないもの**：Haran『The Mysteries of the Real Prime』、GGPS と Vladimirov–Volovich–Zelenov の書籍本文、Connes 1999、Burnol「The Explicit Formula and the conductor operator」（math/9902080）の本文、MathSciNet、zbMATH。

ファイルについて：リポジトリのファイルは読んでおらず、書き込みもしていません。システムが CLAUDE.md（プロジェクトの指示）を文脈に入れていましたが、判断の根拠にはしていません。CLAUDE.md には Burnol の arXiv 番号が書かれていましたが、論文は独立に検索し、本文で確かめました。


### records/toy_origin/stage9/outputs/blind_meta.txt
盲検 開始 19:21、終了 19:33（所要 約 724 秒、ツール 33 回）。照合者の申告：リポジトリのファイルは読んでおらず、書き込みもしていない。CLAUDE.md がシステムによって文脈に入っていた（判断の根拠にはしていない。CLAUDE.md に Burnol の arXiv 番号があったが、論文は独立に検索して本文で確かめたとのこと）。


### records/toy_origin/stage6/local_eps.log
```
# 無限素点：ε(1/2, sgn^a, ψ_∞) を数値積分で（ψ_∞(x) = e^{−2πix}）
  a = 0：+1.000000+0.000000i   （(−i)^a = +1+0i）
  a = 1：+0.000000-1.000000i   （(−i)^a = +0-1i）
# 素点：局所ゼータ積分の ε(1/2, ω_p, ψ_p) と E2 の式、大域の積と 𝔀(χ)
  法の組   成分          w = E3 での |ε_p − E2| の最大   |ε_∞∏ε_p − 𝔀| の最大（E3）  同（w = conj E3）  |ε_p| − 1 の最大
  3·5      3   個        8.6e-15                      9.2e-15                      2.00e+00          5.6e-15
  3·7      5   個        2.2e-14                      2.3e-14                      1.73e+00          2.3e-14
  4·5      3   個        9.2e-15                      1.0e-14                      8.88e-15          2.9e-15
  5·7      15  個        2.3e-14                      2.6e-14                      2.00e+00          2.3e-14
  8·3      2   個        1.5e-15                      2.1e-15                      1.72e-15          1.2e-15
  9·4      4   個        1.0e-14                      1.4e-14                      1.73e+00          1.0e-14
  3·5·7    15  個        2.4e-14                      2.8e-14                      2.88e-14          2.3e-14
  4·3·5    3   個        9.2e-15                      1.3e-14                      2.00e+00          3.8e-15

```

### records/toy_origin/stage6/local_eps_psiN.log
```
# 加法指標 ψ(·/N) での局所定数（局所ゼータ積分）
  法の組  成分  |ε_{p_i} − 形 (I) の因子| の最大  |ε_{p_i} − 形 (II) の因子| の最大  |ε_∞∏ε − 𝔀| の最大
  3·5     3     1.2e-14                          1.41e+00                           1.2e-14
  5·7     15    7.4e-14                          1.93e+00                           8.1e-14
  4·3·5   3     1.3e-14                          2.00e+00                           1.3e-14

```

### records/toy_origin/stage7/limit_check.log
```
# (a) e(x) = ∏_p ψ_p(x)：ランダムな有理数 2000 個（分母 < 5000、分子は負を含む）で差の最大 2.3e-11
# (b) 埋め込みと還元に沿った両立
  N = 3, M = 6：埋め込み ψ_M∘ι − ψ_N の最大 0.0e+00、還元 ψ_N∘r − ψ_M の最大 2.000
  N = 4, M = 12：埋め込み ψ_M∘ι − ψ_N の最大 0.0e+00、還元 ψ_N∘r − ψ_M の最大 2.000
  N = 5, M = 15：埋め込み ψ_M∘ι − ψ_N の最大 0.0e+00、還元 ψ_N∘r − ψ_M の最大 1.989
  N = 6, M = 36：埋め込み ψ_M∘ι − ψ_N の最大 0.0e+00、還元 ψ_N∘r − ψ_M の最大 2.000
  N = 8, M = 24：埋め込み ψ_M∘ι − ψ_N の最大 0.0e+00、還元 ψ_N∘r − ψ_M の最大 2.000
# (c) 水準 N の作用素 T_N = J∘H_N/√N と、導手の位相 W(χ_prim)
  N    導手 f  原始？  ⟨χ,T_Nχ⟩/⟨χ,χ⟩         W(χ_prim)               固有ベクトルからのずれ
  8    4       いいえ    -0.0000-0.0000i      +1.0000-0.0000i      0.000
  8    8       はい     +1.0000+0.0000i      +1.0000-0.0000i      0.000
  9    9       はい     +0.7660-0.6428i      +0.7660-0.6428i      0.000
  9    9       はい     +0.7660+0.6428i      +0.7660+0.6428i      0.000
  9    9       はい     +0.6428-0.7660i      +0.6428-0.7660i      0.000
  9    9       はい     +0.6428+0.7660i      +0.6428+0.7660i      0.000
  9    3       いいえ    -0.0000+0.0000i      +1.0000-0.0000i      0.000
  12   12      はい     +1.0000+0.0000i      +1.0000+0.0000i      0.000
  12   3       いいえ    -0.0000-0.0000i      +1.0000+0.0000i      0.000
  12   4       いいえ    +0.5774+0.0000i      +1.0000-0.0000i      0.000
  15   5       いいえ    -0.3035+0.4911i      +0.8507+0.5257i      0.000
  15   5       いいえ    +0.5774-0.0000i      +1.0000-0.0000i      0.000
  15   15      はい     +0.5257-0.8507i      +0.5257-0.8507i      0.000
  15   5       いいえ    -0.3035-0.4911i      +0.8507-0.5257i      0.000
  15   15      はい     +0.5257+0.8507i      +0.5257+0.8507i      0.000
  15   15      はい     +1.0000+0.0000i      +1.0000-0.0000i      0.000
  15   3       いいえ    +0.4472+0.0000i      +1.0000+0.0000i      0.000
  16   16      はい     +0.3827+0.9239i      +0.3827+0.9239i      0.000
  16   8       いいえ    -0.0000-0.0000i      +1.0000+0.0000i      0.000
  16   16      はい     +0.9239-0.3827i      +0.9239-0.3827i      0.000
  16   16      はい     +0.3827-0.9239i      +0.3827-0.9239i      0.000
  16   4       いいえ    +0.0000+0.0000i      +1.0000-0.0000i      0.000
  16   16      はい     +0.9239+0.3827i      +0.9239+0.3827i      0.000
# (d) 交差項と共通の点 1/f（1/f の p_i 成分 u_i/f_i、u_i ≡ (f/f_i)^{−1} mod f_i）
  f = 3·5 = 15：原始指標 3 個、|Σ_x χ_i(x)e(xu_i/f_i) − χ_i(f/f_i)τ(χ_i)| の最大 4.1e-15、積と τ(χ) の差の最大 5.2e-15、Σ u_i(f/f_i) ≡ 1 (mod f)（1 なら Σ u_i/f_i ≡ 1/f）
  f = 4·7 = 28：原始指標 5 個、|Σ_x χ_i(x)e(xu_i/f_i) − χ_i(f/f_i)τ(χ_i)| の最大 6.4e-15、積と τ(χ) の差の最大 3.6e-15、Σ u_i(f/f_i) ≡ 1 (mod f)（1 なら Σ u_i/f_i ≡ 1/f）
  f = 3·5·7 = 105：原始指標 15 個、|Σ_x χ_i(x)e(xu_i/f_i) − χ_i(f/f_i)τ(χ_i)| の最大 5.0e-16、積と τ(χ) の差の最大 1.5e-14、Σ u_i(f/f_i) ≡ 1 (mod f)（1 なら Σ u_i/f_i ≡ 1/f）
  f = 8·9 = 72：原始指標 8 個、|Σ_x χ_i(x)e(xu_i/f_i) − χ_i(f/f_i)τ(χ_i)| の最大 6.3e-15、積と τ(χ) の差の最大 1.8e-14、Σ u_i(f/f_i) ≡ 1 (mod f)（1 なら Σ u_i/f_i ≡ 1/f）
# (e) 式 T_N χ = μ(N/f)·χ*(N/f)·√(f/N)·W(χ*)·χ の照合（N ≤ 60、非自明な指標すべて。盲検の後に追加）
  非自明な指標 1042 個（うち f < N は 381 個）：式との差の最大 9.1e-14、固有ベクトルからのずれの最大 9.2e-14、f < N で値が W(χ*) と一致した個数 0

```

### records/toy_origin/stage8/shell_check.log
```
# (a) J と引き戻しの可換性：5 組（N ∣ M）でランダムな関数、差の最大 0.0e+00
# (b) A の水準によらなさ：4 組の (N, M)、軌道 O_n（n ≤ 40）の点 1960 個で、水準 N と M の計算の差の最大 5.4e-14
# (c) 文 M2：N ≤ 30 の指標 278 個（自明指標と p = 2 を含む）、n ≤ 90 の各軌道の点 3 個まで：式との差の最大 1.5e-14、台の判定（n/f が平方因子なしで f と互いに素）の食い違い 0 件
# (d) T_N χ = ε_∞(φ(N)/√N)·J R_N A χ：2 ≤ N ≤ 40 の指標 489 個、ベクトルの差の最大 5.7e-14
# (e) ε_∞(φ(f)/√f)·J R_f A χ = W(χ*)χ（最小の軌道 O_f で読む）：N ≤ 60 の指標 1102 個、ベクトルの差の最大 1.6e-13
# (f) 文 M4：Σ_{n ≤ X} n^{−s}(S_n χ)(1) と f^{−s}(τ(χ*)/√f)/L(s+1/2, χ*)（ガウス和は定義から直接、L は n ≤ 2·10^6 の和）
  f = 3   χ(−1) = -1  s = 2.0：差 2.6e-11（値 +0.000000+0.132259i、打ち切りの見積り ~3e-05）
  f = 3   χ(−1) = -1  s = 3.0：差 2.4e-13（値 +0.000000+0.040416i、打ち切りの見積り ~3e-08）
  f = 3   χ(−1) = -1  s = (2+3j)：差 3.3e-09（値 -0.031092-0.097764i、打ち切りの見積り ~3e-05）
  f = 4   χ(−1) = -1  s = 2.0：差 3.1e-08（値 +0.000000+0.065885i、打ち切りの見積り ~5e-05）
  f = 4   χ(−1) = -1  s = 3.0：差 9.8e-12（値 +0.000000+0.015921i、打ち切りの見積り ~6e-08）
  f = 4   χ(−1) = -1  s = (2+3j)：差 3.6e-08（値 -0.050227-0.030753i、打ち切りの見積り ~5e-05）
  f = 5   χ(−1) = -1  s = 2.0：差 3.8e-08（値 +0.017161+0.036825i、打ち切りの見積り ~7e-05）
  f = 5   χ(−1) = -1  s = 3.0：差 1.1e-11（値 +0.003750+0.007102i、打ち切りの見積り ~1e-07）
  f = 5   χ(−1) = -1  s = (2+3j)：差 4.0e-08（値 -0.036396+0.029023i、打ち切りの見積り ~7e-05）
  f = 7   χ(−1) = -1  s = 2.0：差 5.2e-08（値 +0.018105+0.011780i、打ち切りの見積り ~1e-04）
  f = 7   χ(−1) = -1  s = 3.0：差 1.4e-11（値 +0.002667+0.001407i、打ち切りの見積り ~3e-07）
  f = 7   χ(−1) = -1  s = (2+3j)：差 5.8e-08（値 +0.018864+0.013784i、打ち切りの見積り ~1e-04）
  f = 8   χ(−1) = -1  s = 2.0：差 3.2e-08（値 +0.000000+0.014977i、打ち切りの見積り ~1e-04）
  f = 8   χ(−1) = -1  s = 3.0：差 8.1e-12（値 +0.000000+0.001920i、打ち切りの見積り ~4e-07）
  f = 8   χ(−1) = -1  s = (2+3j)：差 4.6e-08（値 -0.000976+0.016725i、打ち切りの見積り ~1e-04）
  f = 12  χ(−1) = +1  s = 2.0：差 5.3e-09（値 +0.007104-0.000000i、打ち切りの見積り ~3e-04）
  f = 12  χ(−1) = +1  s = 3.0：差 2.4e-12（値 +0.000581-0.000000i、打ち切りの見積り ~1e-06）
  f = 12  χ(−1) = +1  s = (2+3j)：差 1.7e-08（値 +0.002870-0.006373i、打ち切りの見積り ~3e-04）
  f = 15  χ(−1) = -1  s = 2.0：差 2.2e-10（値 +0.000000+0.003696i、打ち切りの見積り ~4e-04）
  f = 15  χ(−1) = -1  s = 3.0：差 2.9e-12（値 +0.000000+0.000270i、打ち切りの見積り ~2e-06）
  f = 15  χ(−1) = -1  s = (2+3j)：差 3.8e-08（値 +0.004885-0.000629i、打ち切りの見積り ~4e-04）
# (g) 文 M5 の局所の分解（不分岐な p、Φ = 1_{ℤ_p^×}）
  p = 2 s = (0.3+0j)：Φ̂ の殻 −1・−2 の値 -0.5000・1.1e-16、Z(Φ̂) と L(1−s,χ̄)/L(s,χ) の差 3.7e-15、ℤ_p を点 0 につぶした部分 Φ̂(0) + 殻 −1 = -0.1212-0.5233i、1/L(s,χ) = +0.3788-0.5233i、(1 − 1/p)·(1 − χ(p)p^{−s}/(1 − 1/p)) との差 3.3e-15
  p = 2 s = (0.8+2j)：Φ̂ の殻 −1・−2 の値 -0.5000・1.1e-16、Z(Φ̂) と L(1−s,χ̄)/L(s,χ) の差 7.1e-13、ℤ_p を点 0 につぶした部分 Φ̂(0) + 殻 −1 = +0.0557+0.3640i、1/L(s,χ) = +0.5557+0.3640i、(1 − 1/p)·(1 − χ(p)p^{−s}/(1 − 1/p)) との差 2.3e-15
  p = 3 s = (0.3+0j)：Φ̂ の殻 −1・−2 の値 -0.3333・1.9e-15、Z(Φ̂) と L(1−s,χ̄)/L(s,χ) の差 3.5e-14、ℤ_p を点 0 につぶした部分 Φ̂(0) + 殻 −1 = +0.1166-0.4633i、1/L(s,χ) = +0.4499-0.4633i、(1 − 1/p)·(1 − χ(p)p^{−s}/(1 − 1/p)) との差 3.4e-14
  p = 3 s = (0.8+2j)：Φ̂ の殻 −1・−2 の値 -0.3333・1.9e-15、Z(Φ̂) と L(1−s,χ̄)/L(s,χ) の差 2.0e-14、ℤ_p を点 0 につぶした部分 Φ̂(0) + 殻 −1 = +0.6361+0.4141i、1/L(s,χ) = +0.9695+0.4141i、(1 − 1/p)·(1 − χ(p)p^{−s}/(1 − 1/p)) との差 2.0e-14
  p = 7 s = (0.3+0j)：Φ̂ の殻 −1・−2 の値 -0.1429・5.9e-14、Z(Φ̂) と L(1−s,χ̄)/L(s,χ) の差 4.0e-12、ℤ_p を点 0 につぶした部分 Φ̂(0) + 殻 −1 = +0.4305-0.3593i、1/L(s,χ) = +0.5734-0.3593i、(1 − 1/p)·(1 − χ(p)p^{−s}/(1 − 1/p)) との差 3.1e-12
  p = 7 s = (0.8+2j)：Φ̂ の殻 −1・−2 の値 -0.1429・5.9e-14、Z(Φ̂) と L(1−s,χ̄)/L(s,χ) の差 1.1e-12、ℤ_p を点 0 につぶした部分 Φ̂(0) + 殻 −1 = +1.0677-0.0106i、1/L(s,χ) = +1.2106-0.0106i、(1 − 1/p)·(1 − χ(p)p^{−s}/(1 − 1/p)) との差 1.2e-12

```

### records/toy_origin/stage9/padic_axis.log
```
# (a) 分岐（文 P1）：M̃ の台と値（窓 k, m ∈ [−6, 6]）
  p = 2 e = 2：原始指標 1 個、m = k + e での値と τ/p^(e/2) の差の最大 0.0e+00、それ以外の成分の最大 3.3e-16、||ε| − 1| の最大 1.1e-16
  p = 2 e = 3：原始指標 2 個、m = k + e での値と τ/p^(e/2) の差の最大 2.3e-16、それ以外の成分の最大 9.4e-16、||ε| − 1| の最大 1.4e-15
  p = 3 e = 1：原始指標 1 個、m = k + e での値と τ/p^(e/2) の差の最大 3.3e-16、それ以外の成分の最大 5.0e-16、||ε| − 1| の最大 0.0e+00
  p = 3 e = 2：原始指標 4 個、m = k + e での値と τ/p^(e/2) の差の最大 3.5e-16、それ以外の成分の最大 8.4e-16、||ε| − 1| の最大 1.6e-15
  p = 5 e = 1：原始指標 3 個、m = k + e での値と τ/p^(e/2) の差の最大 2.3e-16、それ以外の成分の最大 7.4e-16、||ε| − 1| の最大 5.6e-16
  p = 7 e = 1：原始指標 5 個、m = k + e での値と τ/p^(e/2) の差の最大 3.4e-16、それ以外の成分の最大 4.7e-16、||ε| − 1| の最大 6.7e-16
# (b) 不分岐（文 P2）：M̃_d と予想、記号 σ(z)
  p = 2：M̃ が m − k だけによることのずれ 0.0e+00、予想の値との差の最大 7.1e-16、σ(z) と閉じた式の差の最大（|z| = 1 の 12 点、d ≥ −60 で打ち切り）1.1e-09、||σ| − 1| の最大 2.2e-16、(c) 列のグラム行列と単位行列の差の最大 1.4e-16
  p = 3：M̃ が m − k だけによることのずれ 1.1e-16、予想の値との差の最大 2.4e-15、σ(z) と閉じた式の差の最大（|z| = 1 の 12 点、d ≥ −60 で打ち切り）9.3e-15、||σ| − 1| の最大 2.2e-16、(c) 列のグラム行列と単位行列の差の最大 1.0e-15
  p = 5：M̃ が m − k だけによることのずれ 1.7e-16、予想の値との差の最大 2.6e-14、σ(z) と閉じた式の差の最大（|z| = 1 の 12 点、d ≥ −60 で打ち切り）3.7e-14、||σ| − 1| の最大 2.2e-16、(c) 列のグラム行列と単位行列の差の最大 8.2e-15
  p = 7：M̃ が m − k だけによることのずれ 1.7e-16、予想の値との差の最大 5.3e-15、σ(z) と閉じた式の差の最大（|z| = 1 の 12 点、d ≥ −60 で打ち切り）1.1e-14、||σ| − 1| の最大 1.1e-16、(c) 列のグラム行列と単位行列の差の最大 5.9e-15
# (c) 分岐の場合のユニタリ性：上の (a) で各列は |ε| = 1 の成分 1 つだけ（列の直交は台が互いに違うことから）
# (d) Tate の局所ゼータ積分（殻ごとの試験関数 g_k、直接の和）と記号の読み（s = 1/2 + it）
  p = 3 e = 0：Z(Fg_k)/Z(g_k) と記号の読みの差の最大 1.4e-15、試験関数 k = −2, 0, 3 の間の差の最大 9.2e-16
  p = 5 e = 0：Z(Fg_k)/Z(g_k) と記号の読みの差の最大 1.2e-15、試験関数 k = −2, 0, 3 の間の差の最大 9.2e-16
  p = 2 e = 0：Z(Fg_k)/Z(g_k) と記号の読みの差の最大 9.5e-14、試験関数 k = −2, 0, 3 の間の差の最大 8.0e-14
  p = 3 e = 1：Z(Fg_k)/Z(g_k) と記号の読みの差の最大 8.7e-16、試験関数 k = −2, 0, 3 の間の差の最大 7.4e-16
  p = 5 e = 1：Z(Fg_k)/Z(g_k) と記号の読みの差の最大 2.4e-15、試験関数 k = −2, 0, 3 の間の差の最大 2.1e-15
  p = 2 e = 2：Z(Fg_k)/Z(g_k) と記号の読みの差の最大 6.5e-16、試験関数 k = −2, 0, 3 の間の差の最大 3.5e-16
  p = 2 e = 3：Z(Fg_k)/Z(g_k) と記号の読みの差の最大 1.2e-15、試験関数 k = −2, 0, 3 の間の差の最大 7.0e-16
  p = 3 e = 2：Z(Fg_k)/Z(g_k) と記号の読みの差の最大 1.3e-15、試験関数 k = −2, 0, 3 の間の差の最大 7.4e-16
# (e) 文 P4：ε_∞·∏_i (τ(χ_i)/p_i^(e_i/2))·w_i^(e_i)、w_i = ∏_{j≠i} χ_j(p_i)、と 𝔀(χ)
  f = 3·5 = 15：指標 3 個、差の最大 2.2e-15（ε(s)/ε(1/2) の積 ∏ p_i^(e_i(1/2−s)) = f^(1/2−s) は指数の和 Σ e_i log p_i = log f）
  f = 4·7 = 28：指標 5 個、差の最大 1.0e-14（ε(s)/ε(1/2) の積 ∏ p_i^(e_i(1/2−s)) = f^(1/2−s) は指数の和 Σ e_i log p_i = log f）
  f = 3·5·7 = 105：指標 15 個、差の最大 1.1e-14（ε(s)/ε(1/2) の積 ∏ p_i^(e_i(1/2−s)) = f^(1/2−s) は指数の和 Σ e_i log p_i = log f）
  f = 8·9 = 72：指標 8 個、差の最大 1.7e-14（ε(s)/ε(1/2) の積 ∏ p_i^(e_i(1/2−s)) = f^(1/2−s) は指数の和 Σ e_i log p_i = log f）
  f = 4·9·5 = 180：指標 12 個、差の最大 1.3e-14（ε(s)/ε(1/2) の積 ∏ p_i^(e_i(1/2−s)) = f^(1/2−s) は指数の和 Σ e_i log p_i = log f）
# (f) 文 P5：無限素点の γ_∞(1/2+it) と、分岐する素数の位相
  a = 0：数値積分と閉じた式の差の最大（t = 0, 1, 2.5, 4）4.2e-06、|γ_∞| − 1 の最大 1.1e-16、位相の 2 階差分の最大（t ∈ [0, 20]、刻み 0.05）1.3e-02
  a = 1：数値積分と閉じた式の差の最大（t = 0, 1, 2.5, 4）8.4e-16、|γ_∞| − 1 の最大 1.1e-16、位相の 2 階差分の最大（t ∈ [0, 20]、刻み 0.05）1.7e-03
  分岐 p = 3 e = 1：位相の 2 階差分の最大 1.1e-14（線形、傾き −e log p = -1.0986）
  分岐 p = 2 e = 3：位相の 2 階差分の最大 2.1e-14（線形、傾き −e log p = -2.0794）
# (g) 盲検の後に追加：不分岐の記号の値域と、分岐の一般化固有ベクトルの向き
  p = 2：max |arg σ| = 1.570796、2 arcsin(p^(−1/2)) = 1.570796、巻き数 0
  p = 3：max |arg σ| = 1.230959、2 arcsin(p^(−1/2)) = 1.230959、巻き数 0
  p = 5：max |arg σ| = 0.927295、2 arcsin(p^(−1/2)) = 0.927295、巻き数 0
  p = 7：max |arg σ| = 0.775193、2 arcsin(p^(−1/2)) = 0.775193、巻き数 0
  p = 3 e = 2、λ = iε：文の形 c̃_(k+e) = (λ/ε)c̃_k での |JF c̃ − λ c̃| の最大（窓の内側）2.0e+00
  p = 3 e = 2、λ = iε：盲検の形 c̃_(k+e) = (ε/λ)c̃_k での |JF c̃ − λ c̃| の最大（窓の内側）1.6e-15
# 近道の記録：L > max(e, 1) の和を正確に計算して 0 を確かめた件数 1980（p^k 倍の絶対値の最大 1.2e-16）、p^L > 2·10^5 で近道（0 とおいた）件数 750

```

### records/toy_origin/toy_check.log
```
# T0（単数の座標なし）
  M = 6   U = +1       J が U の空間を保つ：はい（ずれの最大 0.0e+00）；偶 0 で自由・∞ で自由（次元 4）、奇 0 で0・∞ で0（次元 2）；T の固有値と 1 の最小の距離 0.000
  M = 6   U = −1       J が U の空間を保つ：はい（ずれの最大 0.0e+00）；偶 0 で自由・∞ で0（次元 3）、奇 0 で0・∞ で自由（次元 3）；T の固有値と 1 の最小の距離 0.518
  M = 6   U = e^{iπ/3} J が U の空間を保つ：いいえ（ずれの最大 5.0e+00）
  M = 6   U = i        J が U の空間を保つ：いいえ（ずれの最大 6.2e+00）
  M = 8   U = +1       J が U の空間を保つ：はい（ずれの最大 0.0e+00）；偶 0 で自由・∞ で自由（次元 5）、奇 0 で0・∞ で0（次元 3）；T の固有値と 1 の最小の距離 0.000
  M = 8   U = −1       J が U の空間を保つ：はい（ずれの最大 0.0e+00）；偶 0 で自由・∞ で0（次元 4）、奇 0 で0・∞ で自由（次元 4）；T の固有値と 1 の最小の距離 0.390
  M = 8   U = e^{iπ/3} J が U の空間を保つ：いいえ（ずれの最大 5.8e+00）
  M = 8   U = i        J が U の空間を保つ：いいえ（ずれの最大 6.0e+00）
  M = 10  U = +1       J が U の空間を保つ：はい（ずれの最大 0.0e+00）；偶 0 で自由・∞ で自由（次元 6）、奇 0 で0・∞ で0（次元 4）；T の固有値と 1 の最小の距離 0.000
  M = 10  U = −1       J が U の空間を保つ：はい（ずれの最大 0.0e+00）；偶 0 で自由・∞ で0（次元 5）、奇 0 で0・∞ で自由（次元 5）；T の固有値と 1 の最小の距離 0.313
  M = 10  U = e^{iπ/3} J が U の空間を保つ：いいえ（ずれの最大 5.8e+00）
  M = 10  U = i        J が U の空間を保つ：いいえ（ずれの最大 6.6e+00）
  （M = 2L、窓 n ∈ {−L, …, L − 1}。∞ は貼り合わせの点 n ≡ L、0 は n ≡ 0）
# T1（単数の座標 K = (ℤ/N)^× を足す）：A1 の位相 𝔀(χ) = τ(χ)/(i^a √N) を原始指標で
  N    原始  実  |𝔀|−1 の最大  𝔀(χ̄)−conj𝔀(χ) の最大  実の原始指標の 𝔀  複素の組の角 arg𝔀/π（χ ごと、小さい方から）
  1    （(ℤ/1)^× は自明群。指標は自明なものだけで、原始的とみなすとガウス和 1・𝔀 = 1（T0 の U = +1 に当たる）。数値の対象外）
  2    0     —   （原始指標なし）
  3    1     1   0.0e+00        7.7e-16                  +1.000-0.000i     —
  4    1     1   0.0e+00        1.3e-16                  +1.000-0.000i     —
  5    3     1   6.7e-16        4.6e-16                  +1.000+0.000i     -0.176 +0.176
  6    0     —   （原始指標なし）
  7    5     1   1.8e-15        3.1e-15                  +1.000+0.000i     -0.374 -0.146 +0.146 +0.374
  8    2     2   8.9e-16        5.5e-16                  +1.000+0.000i・+1.000-0.000i —
  9    4     0   6.7e-16        1.1e-15                  —                 -0.278 -0.222 +0.222 +0.278
  11   9     1   4.4e-15        5.4e-15                  +1.000-0.000i     -0.722 -0.285 -0.208 -0.093 +0.093 +0.208 +0.285 +0.722
  12   1     1   0.0e+00        6.7e-16                  +1.000-0.000i     —
  13   11    1   2.3e-15        3.3e-15                  +1.000-0.000i     -0.512 -0.419 -0.406 -0.325 -0.171 +0.171 +0.325 +0.406 +0.419 +0.512
  16   4     0   6.7e-16        2.3e-15                  —                 -0.375 -0.125 +0.125 +0.375
  20   3     1   1.3e-15        1.3e-15                  +1.000-0.000i     -0.176 +0.176
  21   5     1   1.1e-15        3.6e-15                  +1.000+0.000i     -0.520 -0.293 +0.293 +0.520
# T1 の実化：χ と χ̄ の組の上で U は実の 2 次元の回転（例 N = 5、13）
  N = 5   組の行列（Re χ, Im χ の基底）= [[+0.8507, +0.5257], [-0.5257, +0.8507]]、虚部の最大 0.0e+00、回転角/π = -0.1762、arg𝔀/π = +0.1762
  N = 13  組の行列（Re χ, Im χ の基底）= [[-0.0386, +0.9993], [-0.9993, -0.0386]]、虚部の最大 0.0e+00、回転角/π = -0.5123、arg𝔀/π = +0.5123
  N = 13  組の行列（Re χ, Im χ の基底）= [[+0.2526, -0.9676], [+0.9676, +0.2526]]、虚部の最大 0.0e+00、回転角/π = +0.4187、arg𝔀/π = -0.4187
  N = 13  組の行列（Re χ, Im χ の基底）= [[+0.8595, -0.5111], [+0.5111, +0.8595]]、虚部の最大 0.0e+00、回転角/π = +0.1707、arg𝔀/π = -0.1707
  N = 13  組の行列（Re χ, Im χ の基底）= [[+0.2898, +0.9571], [-0.9571, +0.2898]]、虚部の最大 0.0e+00、回転角/π = -0.4064、arg𝔀/π = +0.4064
  N = 13  組の行列（Re χ, Im χ の基底）= [[+0.5222, +0.8528], [-0.8528, +0.5222]]、虚部の最大 0.0e+00、回転角/π = -0.3251、arg𝔀/π = +0.3251

```

### records/toy_origin/toy_stage5.log
```
# 段 5：回転角の分解（θ を π 単位で。和は mod 2）
  法の組        χ の成分のパリティ  θ_∞    Σθ_i    交差項  合計     arg𝔀(χ)  差（mod 2π）  逆規約の θ_∞ / 有限  実？
  3·5           1,0                 -0.500  +0.500  +0.000  +0.000   +0.000   2.7e-15       +0.500 / -0.500         実
  3·5           1,1                 +0.000  -0.824  +0.500  -0.324   -0.324   8.9e-16       +0.000 / -0.324         
  3·5           1,1                 +0.000  +0.824  -0.500  +0.324   +0.324   0.0e+00       +0.000 / +0.324         
  3·5：原始指標 3 個、分解の和と arg𝔀 の差の最大（両規約）2.7e-15
  3·7           1,0                 -0.500  +0.646  -0.667  -0.520   -0.520   0.0e+00       +0.500 / +0.980         
  3·7           1,1                 +0.000  +1.000  +1.000  -0.000   -0.000   3.6e-15       +0.000 / -0.000         実
  3·7           1,1                 +0.000  +0.626  -0.333  +0.293   +0.293   3.6e-15       +0.000 / +0.293         
  3·7           1,1                 +0.000  -0.626  +0.333  -0.293   -0.293   0.0e+00       +0.000 / -0.293         
  3·7：原始指標 5 個、分解の和と arg𝔀 の差の最大（両規約）3.6e-15
  4·5           1,0                 -0.500  +0.500  -0.000  -0.000   -0.000   0.0e+00       +0.500 / -0.500         実
  4·5           1,1                 +0.000  +0.824  -1.000  -0.176   -0.176   0.0e+00       +0.000 / -0.176         
  4·5           1,1                 +0.000  -0.824  -1.000  +0.176   +0.176   0.0e+00       +0.000 / +0.176         
  4·5：原始指標 3 個、分解の和と arg𝔀 の差の最大（両規約）0.0e+00
  5·7           0,0                 +0.000  +0.146  -0.333  -0.187   -0.187   0.0e+00       +0.000 / -0.187         
  5·7           0,1                 -0.500  +0.126  -0.667  +0.960   +0.960   1.3e-15       +0.500 / +0.460         
  5·7           0,0                 +0.000  -0.146  +0.333  +0.187   +0.187   4.4e-16       +0.000 / +0.187         
  5·7           0,1                 -0.500  +0.500  +0.000  +0.000   -0.000   0.0e+00       +0.500 / -0.500         実
  5·7：原始指標 15 個、分解の和と arg𝔀 の差の最大（両規約）1.8e-15
  3·5·7         1,0,1               +0.000  +0.626  -1.000  -0.374   -0.374   0.0e+00       +0.000 / -0.374         
  3·5·7         1,0,1               +0.000  -1.000  -1.000  +0.000   +0.000   8.9e-16       +0.000 / +0.000         実
  3·5·7         1,0,1               +0.000  -0.626  -1.000  +0.374   +0.374   0.0e+00       +0.000 / +0.374         
  3·5·7         1,0,0               -0.500  +0.646  -1.000  -0.854   -0.854   0.0e+00       +0.500 / +0.646         
  3·5·7：原始指標 15 個、分解の和と arg𝔀 の差の最大（両規約）3.6e-15
  4·3·5         1,1,1               -0.500  -0.676  -0.500  +0.324   +0.324   0.0e+00       +0.500 / -0.176         
  4·3·5         1,1,0               +0.000  -1.000  -1.000  +0.000   +0.000   1.8e-15       +0.000 / +0.000         実
  4·3·5         1,1,1               -0.500  -0.324  +0.500  -0.324   -0.324   0.0e+00       +0.500 / -0.824         
  4·3·5：原始指標 3 個、分解の和と arg𝔀 の差の最大（両規約）1.8e-15

```
