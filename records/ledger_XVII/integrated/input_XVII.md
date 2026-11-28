# 統合照合 XVII の入力：台帳 L45（2026-11-28）

入力の並び：§1 台帳 L45、§2 差分（コミット 4d24516 → 69da7d2。records/ は除く）、§3 草稿 1 の rev 52 → 67 の変わったブロックの本文、§4 統合照合 XVI の出力（L45 の前半の根拠）、§5 CLAUDE.md の現在の全文。

## §1 台帳 L45
### L45：統合照合 XVI の後の直し（2026-11-28 09:3x）

- 範囲：XVI（`records/ledger_XVI/outputs/integrated_XVI_output.md`）の指摘を受けた直し。
  - 玩具のノート：§27 の帰結 3 の最後の項（中 B：局所定数は形 (I)、ψ(·/N) での局所作用素は計算していない）、§28 の中 2 の項（低 A：作業を止めなかったことと報告の時期）、§26・§27 の「構築側の判断」（低 D）、§17 の重複の B の文を分けた（低 F）、§0 の後注（極低 E）、§13 の後注（極低 H）、§22 の式の括弧（極低 I）。
  - 引き継ぎメモ：07:13 の行に後注（低 C）、XV の行の確認事項 (5) に Part 259 の件（極低 G）、XVI の行。
  - この台帳（L44 を閉じ、L45）。`records/ledger_XVI/`（入力・依頼文・出力・meta）。
- 直していないもの：XV から持ち越した CLAUDE.md の文に関わる項目（中 1・低 10 の後半・低 11 の規則の関係・低 13・極低 19）は、著者の承認・判断待ちのまま。
- 自己申告（根拠にしない）：中 B は主張を狭める直し。ほかは帰属・後注・記号の書き足し。
- 追記（2026-11-28 09:4x、著者の決定「これ以降、CLAUDE.md は Claude が生成したものを採用する」（09:43）を受けて）：CLAUDE.md・CLAUDE.en.md の冒頭にこの決定を記録し、XV・XVI から持ち越した CLAUDE.md の項目を Claude の判断で直した。玩具の 2 行目・3 行目を「著者の選択」と「構築側の補足」に分けた（中 1・低 13）。規約 T の根拠に「根拠はこの 1 本」を戻した（低 10）。Part 250 に「（ε → 0 の側）」を戻した（極低 19。旧版の文言を CLAUDE-history.md で確かめた）。Part 259 の「(iii) を外したとき」は旧版にある（「(iii) を外すと a = 2 では捩れた写像があり一意でない（奇数の場合の一意性は数値のみ）」）ので変えない。§2 に短期層の Part 263・264 は件数の外と追記（中 2）。保留の間の完備化の断り方を構築側の補足として §1 に追記（低 11）。§3 の書き換えの承認の行に決定の注。H1・M8 は現行の文のまま採る（Claude の判断）。
- 追記（2026-11-28 15:5x、著者の指示「アーデル射影幾何学の構築を進めてください」（15:46）を受けて）：本線（基礎文書）に玩具の材料を入れた。草稿 1 に 2.10「玩具の積み上げ」を新設し（rev 54）、「開いている問い」の「無限素点の中身」の項に 1 文足した（rev 55）。索引に 2.10 を足した。新しい主張はなく、ノート §0〜§28 の要約。引き継ぎメモに 1 行。
- 追記（2026-11-28 20:0x、著者の決定「外す前提で進めます」（20:02。解像度と命題 3 を構築から外す）を受けて）：CLAUDE.md・CLAUDE.en.md の §0・§1・§2・§4 に記録（§1 の解像度の項目は記録として残し、完備化の断り方を構築側の補足として外した後も有効にした）。草稿 1（rev 67）：第 3 章を「（記録）外した項目」に下げて冒頭に記録の段落、第 4 章の見出しと本文の解像度の語を替え、2.6・1.2・開いている問い・6.6 の表に注。索引の第 3・4 章と §6 に後注。引き継ぎメモに 1 行。
- 扱い：照合は受けていない。次の統合照合に載せる（著者が求めれば独立の照合にかける）。


## §2 差分
```diff
diff --git a/CLAUDE.en.md b/CLAUDE.en.md
index 974e4a2..aa80834 100644
--- a/CLAUDE.en.md
+++ b/CLAUDE.en.md
@@ -5,9 +5,11 @@
 
 The operating rules to read first (short version, 2026-11-27). The authoritative record of the history, rationale and timing of decisions is `CLAUDE-history.md` (the full text as of 2026-11-26, preserved without changing a character). If you find a point where this short version disagrees with it, stop and report to the author. New decisions are added to this file briefly; history goes into handoff memos and notes.
 
+**Wording of this file (the author's decision, 2026-11-28 09:43)**: to avoid confusion over CLAUDE.md, from now on CLAUDE.md adopts what Claude generates. Claude does not rewrite the author's definitions in §1 or the records of the author's choices, and writes builder-side supplements separately from them. Every change is recorded in the handoff memo and the ledger. The author can overturn this at any time.
+
 ## 0. Before starting
 
-1. Reread the definitions in §1. In particular confirm "the foundation is discrete; continuous objects do not exist in the foundation" and "the parameter that sets the resolution is undecided (do not identify it with N, K, Λ)." Do not rewrite the definitions or interpret them more broadly.
+1. Reread the definitions in §1. In particular confirm "the foundation is discrete; continuous objects do not exist in the foundation". "Resolution" and proposition 3 have been removed from the construction (2026-11-28 20:02, §1). Do not rewrite the definitions or interpret them more broadly.
 2. Check the current position in §2 (and the latest handoff memo and `notes/pag2_tail_ledger.md`).
 3. For a new object, mapping it to existing mathematics (the dictionary and the blind naming test of §6) is an obligation. Being able to state the question left after the mapping in the language of geometry, the global, or limits is at the same time a condition for starting. If it cannot be stated, treat the object as a device for local computation and do not start a part with it as the main subject.
 4. Before working, state the current position in your own words, split into (a) formalized content, (b) the author's interpretive layer (§1), and (c) open global questions. If you mix them, start over.
@@ -20,9 +22,10 @@ The purpose of these steps is not to avoid mapping. What is to be prevented is t
 - The points are the primes plus the infinite place. At the infinite place, the infinitely large and the infinitely small overlap.
   - Reading of the "overlap": a **twisted gluing (boundary unitary U)**. The reading of the identification of the two ends as a group quotient is not adopted because it is incompatible with A1 (a cubic character mod 9 is a counterexample). A quotient by W is compatible with A1 but is not adopted either (D does not descend to the quotient).
   - In the toy (`notes/pag2_toy_origin_buildup.md`), "twisted connection" is read as the rotation of complex character pairs (the rotation, by the A1 phase 𝔀(χ), of the plane obtained by realifying the pair χ, χ̄), not the Möbius-type −1 (the author's choice, 2026-11-27 08:21).
-  - In the toy, the coupling between places (the cross terms) is put on the additive side: the additive character is the global ψ(·/N) (trivial on ℚ), and the local gluing at the point p_i is χ_i(N/N_i)·τ(χ_i)/√N_i (form (I) of PAG261; the same allocation as PAG260 `gaussSum_prodChar` and `stdAddChar_crtMap`) (the author's choice, 2026-11-27 17:37).
-  - In the toy, the window gluing of T0 (f(n+M) = U f(n) on the logarithmic lattice of the infinite place) is read as a boundary condition placed independently at the infinite place: it is not derived from Tate's local operator, and it is not read as a copy of the form at ramified primes (a phase times a translation of width e along the valuation axis) (the author's choice, 2026-11-28 07:13; background in the note §25–§27).
+  - In the toy, the coupling between places (the cross terms) is put on the additive side (the author's choice, 2026-11-27 17:37). Builder-side supplement: the additive character is then the global ψ(·/N) (trivial on ℚ), and the local constant at the point p_i is χ_i(N/N_i)·τ(χ_i)/√N_i (form (I) of PAG261; the allocation of τ follows directly from PAG260 `gaussSum_prodChar` and `stdAddChar_crtMap`; the identification with local constants is outside Lean; note §15, §17).
+  - In the toy, the window gluing of T0 (f(n+M) = U f(n) on the logarithmic lattice of the infinite place) is read as a boundary condition placed independently at the infinite place (the author's choice, 2026-11-28 07:13). Builder-side supplement: so it is not derived from Tate's local operator, and it is not read as a copy of the form at ramified primes (a phase times a translation of width e along the valuation axis). Its phase is the input 𝔀(χ) set by A1; that this equals the product of local constants is Tate's theorem (injection and recovery; note §25–§27).
 - The foundation is discrete; continuous objects such as the line do not exist in the foundation.
+- **Removed (2026-11-28 20:02, the author's decision "proceed on the premise of removing it")**: "resolution" and proposition 3 (the definition on the next line) are removed from the construction of Ardel projective geometry. The items from the next line through the "On hold" item are kept as a record and are not used as rules of the construction (builder-side supplement: in the founding document, chapter 3 is lowered to a record and chapter 4 is restructured without the word resolution).
 - The line is the effective form that emerges when the resolution is lowered.
   - The resolution parameter is **undecided**. Do not identify it with N, K, or Λ.
   - Placement of proposition 3 (the author can override at any time): the wording of the definition is not changed. The place of the resolution operation is not "a transition inside the object" but **the choice of a way of cutting (viewing)** the global object (interpretive layer). The object is the whole in which the places coexist in parallel from the start as factors of the restricted product; finite-level quotients and the Λ-cutoff are two axes of viewing that whole. The question of proposition 3 is read as "how the line looks when the view is coarsened."
@@ -30,21 +33,22 @@ The purpose of these steps is not to avoid mapping. What is to be prevented is t
   - The reading L1 (resolution = the set of places measured) is adopted (as a reading, not the wording of the definition).
   - Do not use the expression "emergence of the line" (直線の創発). When referring to proposition 3, write it by reference as "proposition 3 of §1 (resolution and effective form)," and write in mathematical language what changes and how.
   - **On hold (2026-11-26 20:35, the author's decision)**: "resolution" is on hold, and may be removed from the construction of Ardel projective geometry. Reason: the word "resolution" arose after the conversations with Muse began and was not in the original conception. The items above (proposition 3 and its readings) are kept as a record.
+  - Builder-side supplement (2026-11-28, still valid after the removal): when completions (ℚ_p, 𝔸_f, L², ℝ, etc.) are used, state "used as a computational tool, not written as an effective form or a goal". Do not write continua appearing in closures or completions as goals. Do not use the term "emergence of the line".
 - Reading of "projective" (interpretive layer, with reservations):
   - The stage is the projective line P¹ (the inversion swaps 0 and ∞; at the finite level, Parts 19–28 (PAG23–PAG32)). The **composition of gluings** acting on it is what is called projection. The transformation is primary. The gluing means U (the twisted gluing), not `Compat` of PAG23 (an untwisted gluing of coordinates). The "projective" of the name refers to the pair of stage and transformation.
   - The builder side's reading (adopted by the author as material, with reservations): that composition is the composition of the inversion (multiplicative side) and the additive transform (additive side), and at the finite level corresponds to J∘H_N/√N of Part 252 (PAG256) (`PAG.Part256.JH`). However, `JH` is a map sending functions on ℤ/N to functions on the units, not an operator on P¹. In the range checked (PAG23, PAG26, PAG27, PAG256) there is no Lean statement connecting JH with the model of P¹ (the whole chain was not searched). What Part 262 (PAG266) connected in Lean is only the value of 𝔀 and the coefficients on P¹.
   - The phase for primitive characters is a component of this composition (transformation).
   - The standard kernel is the Hartley kernel of Part 252 (ratification of the formalization; that it aligns with the content of A1 is the author's judgment, based on a reading of the header comment of PAG256, not checked against the monograph text). Its value is τ(χ)/(i^a√N) (`PAG.Part256.rootNum`, symbol 𝔀; the symbol W(χ) in the docstring and header comment of PAG256 denotes this value too, and is distinct from the inversion W). For primitive characters it is the root number, but that identification is outside Lean (say so explicitly). It differs from the value τ(χ)/√N of the naive kernel e(xy) by a factor i for odd characters; do not smooth over this discrepancy.
-  - The additive characters follow **convention T** (Tate's thesis: ψ_∞(x) = e^{−2πix}, ψ_p(x) = e^{+2πi{x}_p}) as the standard of the founding document. Under convention T, normalizing the idele class character at unramified q by ω_q(q) = χ(q) (under the convention matching χ̄ the product is conjugated), for primitive χ the factor ε(χ) = (−i)^a of the Hartley kernel (`PAG.Part256.parFac`) agrees in value with the local constant ε(1/2, χ_∞, ψ_∞) at the infinite place, and τ(χ)/√N with the product of the local constants at the finite places at s = 1/2 (outside Lean; confidence: high; local constants defined in the manner of Tate 1979). That the explicit factor i^{±a} is the local constant at the infinite place is convention-independent, but whether the sign χ(−1) is placed at the infinite place or the finite places depends on the convention (under the opposite convention the infinite place gives i^a and the product over finite places χ(−1)τ(χ)/√N). Do not write "ε(χ) comes from the infinite place" without stating convention T. A1 remains a postulate. The grounds for adopting convention T: the signs at the finite places match Mathlib's `stdAddChar`, and the additive character is the same as in Burnol (arXiv:math/9811040). Material: `notes/pag2_projection_material.md`; literature check of the convention: `notes/pag2_literature_ia_sign.md`.
+  - The additive characters follow **convention T** (Tate's thesis: ψ_∞(x) = e^{−2πix}, ψ_p(x) = e^{+2πi{x}_p}) as the standard of the founding document. Under convention T, normalizing the idele class character at unramified q by ω_q(q) = χ(q) (under the convention matching χ̄ the product is conjugated), for primitive χ the factor ε(χ) = (−i)^a of the Hartley kernel (`PAG.Part256.parFac`) agrees in value with the local constant ε(1/2, χ_∞, ψ_∞) at the infinite place, and τ(χ)/√N with the product of the local constants at the finite places at s = 1/2 (outside Lean; confidence: high; local constants defined in the manner of Tate 1979). That the explicit factor i^{±a} is the local constant at the infinite place is convention-independent, but whether the sign χ(−1) is placed at the infinite place or the finite places depends on the convention (under the opposite convention the infinite place gives i^a and the product over finite places χ(−1)τ(χ)/√N). Do not write "ε(χ) comes from the infinite place" without stating convention T. A1 remains a postulate. The grounds for adopting convention T: the signs at the finite places match Mathlib's `stdAddChar`, and the additive character is the same as in Burnol (arXiv:math/9811040; this is the only source for it). Material: `notes/pag2_projection_material.md`; literature check of the convention: `notes/pag2_literature_ia_sign.md`.
   - At the level of operators, U is an operator on the equator (the space of functions on the units; `Lim` in the limit), and it does not extend uniquely to all of P¹ under natural conditions alone (to be written as a property; 2026-11-26, the author's decision).
 - All of the above is the interpretive layer, not formalized theorems. In notes, do not confuse their status.
 
 ## 2. Current position (2026-11-26)
 
 - **Monograph layer (1.0)**: the operator system (D, T_p, W, dihedral relations) on the idele class group C_ℚ. The central problem P1 is the compatibility classification of the boundary condition U of self-adjoint extensions (Theorem 2.6). The space of U in Theorem 2.6 is functions on C_ℚ (the regular-representation side, with the Λ-cutoff reservation). **Axiom A1** is a restatement of the value at λ = 0 of the gluing of Tate's γ-factors, and **remains a postulate of the interpretive layer (its content is Tate's theorem)** (do not write that it has been derived).
-- **PAG 2.0 (finite level)**: the Lean formalization goes up to Part 262 (PAG266). 3,695 theorems and lemmas; xlsx final84 (3,722 items). Do not confuse these counts with other counts such as total declarations. Part n is PAG(n+4).lean (third period).
+- **PAG 2.0 (finite level)**: the Lean formalization goes up to Part 262 (PAG266) (the short-term-layer Parts 263–264 (PAG267, PAG268) are outside this count; recorded in the index; added 2026-11-28). 3,695 theorems and lemmas; xlsx final84 (3,722 items). Do not confuse these counts with other counts such as total declarations. Part n is PAG(n+4).lean (third period).
 - **The main line is the founding document** (collecting the definitional layer into one document; draft 1 in progress). No new parts are started. Parts run only to fill gaps in the document's chapters.
-- The open questions of the original path once listed (continuation of B-3, structure theorems, theorem A over Ẑ) were judged in the inventory audit of 2026-11-12 to be known theorems or their consequences (`notes/pag2_audit_after_part251.md`). The formulation of resolution is on hold as in §1.
+- The open questions of the original path once listed (continuation of B-3, structure theorems, theorem A over Ẑ) were judged in the inventory audit of 2026-11-12 to be known theorems or their consequences (`notes/pag2_audit_after_part251.md`). Resolution has been removed from the construction as in §1 (2026-11-28 20:02).
 - The response to the dictionary threshold being exceeded (supplement 16) was done on 2026-11-20 (commit 4357fb4).
 - Sign 4 of the convergence alarm has continued for 14 parts (Parts 249–262). The assessment that residue-bearing questions pass through A1 or completion (the side of the infinite place) agrees with the results of the gates (`notes/pag2_partial_inversion_preregistration.md`).
 - Literature checks: MathSciNet will not be used (the author's decision). zbMATH has been done, with no item changing the status of the candidates (`notes/pag2_literature_zbmath_20261126.md`).
@@ -58,11 +62,11 @@ The purpose of these steps is not to avoid mapping. What is to be prevented is t
   1. The generation classification (Parts 245–248). Excluding the structure theorem and the few-line corollary of the dimension formula (⟨M*, E_N⟩ = A_N ⇔ N ∈ {1,4} ∪ primes), what remains is item 66 (the condition for the sum of two dual algebras; the declaration `sumSub_eq_shellAlg_iff` is in PAG249 (Part 245)) and items 67–69 (the complete classification), for composite N (confidence: medium). Assessed as "at the level of a small note": not a new phenomenon but "a computation nobody has written down." No reservation on external use as novel. Search terms: Terwilliger algebra, orbit Schur ring, cyclotomic S-ring, dual Bose–Mesner algebra, generated by, generating set.
   3. The non-existence side of Part 258 (PAG262) [novelty candidate (small)]: when N ∣ M and a prime p divides both N and M/N, there is no unital algebra homomorphism A_N → A_M that is compatible with pullback and does not mix shells (confidence: low–medium). "Does not mix shells" is the strong reading (φ(D_s) is a linear combination of the D_t, φ(E_s) of the E_t). The weak reading, non-unital maps, and other compatibility conditions remain as separate questions outside the claim. The existence side is known (the direct-product theorem of Hanaki–Kim–Maekawa). **Do not use it externally (including in applications) as novel** (the reservation remains; since MathSciNet was dropped, the condition remains unmet). Literature check record: `notes/pag2_candidate3_literature_builder.md`.
   - The former candidate 2 (the presentation of Theorem 2.6) dropped out. The combination (α_{χ̄} = −α_χ and root numbers) is a short consequence of known results (confidence: high). No literature writing this combination was found (confidence: medium), but that is no ground for novelty (confidence: medium–high). That root numbers satisfy the condition is a consistency check, not a derivation of A1. The inversion condition is equivalent to reality of the boundary unitary (CW preserves the boundary condition; by hand and numerically). In Lean it follows from three theorems of PAG16, PAG173 and PAG198, but a single combined statement is not formalized. Close precedents: Burnol; Ibort–Lledó–Pérez-Pardo, examples 7.1 and 7.2.
-- §3 is rewritten only after the author's approval.
+- §3 is rewritten only after the author's approval (from 2026-11-28, by the decision "Wording of this file" at the top, Claude does this at its own judgment and records it).
 - If structure is needed, cite the literature through the dictionary instead of re-proving it.
 
 **Status of Parts 250–262 (cautions when writing the founding document; details in the index and the notes)**
-- Part 250: what was shown is that "the foundation sits inside ℝ as a dense subset that is totally disconnected but chain-connected at every scale" (the log-coordinate version of a textbook example). No novelty candidate. "The line appears when the resolution is lowered" was not shown (taking the quotient collapses to one point, ℝ appears from the side of completion, and ℝ is used in the definition from the start).
+- Part 250: what was shown is that "the foundation sits inside ℝ as a dense subset that is totally disconnected but chain-connected at every scale" (the log-coordinate version of a textbook example). No novelty candidate. "The line appears when the resolution is lowered" was not shown (taking the quotient collapses to one point, ℝ appears from completion (the side ε → 0), and ℝ is used in the definition from the start).
 - Part 251: "dense in the idele class group" is a reading under the identification by the structure theorem C_ℚ ≅ Ẑ^× × ℝ_{>0} (not in Lean: unitSys ≅ Ẑ^×, universality, compactness and topological-group property of the limit, the structure theorem).
 - The U_N of Parts 252–254 are operators with the phases of A1 put in as a definition; A1 is not derived.
 - Part 259: uniqueness in the odd case with (iii) removed is numerical only. The algebra structure and the isomorphism with the restricted tensor product are outside Lean. The index order is not directed.
@@ -77,7 +81,7 @@ The purpose of these steps is not to avoid mapping. What is to be prevented is t
 
 - The cycle of a part: numerical check in Python → Lean (0 sorry, 0 warnings) → `#print axioms` → note + xlsx. Note titles use "アーデル射影幾何" (Ardel projective geometry) (the old name "アデール射影幾何 2.0" is not used).
 - Criterion for a new part: does it answer a question in the language of geometry, the global, or limits? Questions internal to the algebra (describing the center, classifying algebras with added generators, etc.) are not made the main subject. Finite-level algebras are used as devices for local computation. State at the top which question of the original path (§1) it serves (if you cannot, do not start).
-- **The four points before starting** (written before Lean; only what has been narrowed to one recommendation is started): (1) write the question in geometric language (points, infinite place, resolution, emergence), (2) the best translation into the language of existing fields (the mapping is obligatory), (3) state the residue that does not vanish under translation (if empty, do not start; if only computational details, a short-term small note), (4) apply a control-group test to the statement of the residue and record the result alongside. In addition, the blind question test and the internal check (§6).
+- **The four points before starting** (written before Lean; only what has been narrowed to one recommendation is started): (1) write the question in geometric language (points, infinite place, gluing, global, limit; "resolution" and "emergence" removed on 2026-11-28), (2) the best translation into the language of existing fields (the mapping is obligatory), (3) state the residue that does not vanish under translation (if empty, do not start; if only computational details, a short-term small note), (4) apply a control-group test to the statement of the residue and record the result alongside. In addition, the blind question test and the internal check (§6).
 - **Delegated selection**: the builder side narrows to one recommendation that has passed the gates (four points, blind question test, control-group test), and the start is decided by the author-side Muse. Record what was chosen and why. The author can override at any time.
 - A single path for decisions: this file and the author side's handovers are the only record. Anything the author chose in a builder-side session is recorded in the handoff memo and returned to the author side.
 - Write part numbers as "Part n (PAGm)."
diff --git a/CLAUDE.md b/CLAUDE.md
index 28b7ff3..35af09f 100644
--- a/CLAUDE.md
+++ b/CLAUDE.md
@@ -2,9 +2,11 @@
 
 最初に読む運用の規則（短縮版、2026-11-27）。判断の経緯・根拠・日時の正文は `CLAUDE-history.md`（2026-11-26 時点の全文を一字も変えずに保存）。この短縮版と食い違う箇所を見つけたら、作業を止めて著者に報告する。新しい判断はこのファイルに短く足し、経緯は引き継ぎメモと notes に書く。
 
+**この文書の文面（2026-11-28 09:43、著者の決定）**：CLAUDE.md の混乱を避けるため、これ以降、CLAUDE.md は Claude が生成したものを採用する。Claude は、§1 の著者の定義と著者の選択の記録を書き換えず、構築側の補足とは分けて書く。直したら引き継ぎメモと台帳に記録する。著者はいつでも覆せる。
+
 ## 0. 始める前に
 
-1. §1 の定義を読み直す。特に「基礎は離散的であり、連続対象は基礎に存在しない」と「解像度を決めるパラメータは未決定（N・K・Λ と同一視しない）」を確かめる。定義は書き換えない・広げて解釈しない。
+1. §1 の定義を読み直す。特に「基礎は離散的であり、連続対象は基礎に存在しない」を確かめる。「解像度」とそれにかかわる命題 3 は構築から外した（2026-11-28 20:02、§1）。定義は書き換えない・広げて解釈しない。
 2. §2 の現在地を確かめる（最新の引き継ぎメモと `notes/pag2_tail_ledger.md` も）。
 3. 新しい対象は、既存数学への対応づけ（§6 の辞書・盲検の命名テスト）が義務。同時に、対応づけた後に残る問いを幾何・大域・極限の言葉で言えることを、始める条件とする。言えなければ、その対象は局所計算の装置として扱い、主役のパートを始めない。
 4. 作業の前に、現状を (a) 形式化済みの内容、(b) 著者の解釈の層（§1）、(c) 未完の大域の問い、に分けて自分の言葉で述べる。混ぜたらやり直す。
@@ -17,9 +19,10 @@
 - 点は素数たち＋無限素点。無限素点では無限大と無限小が重なり合う。
   - 「重なり」の読み：**ねじれた貼り合わせ（境界ユニタリ U）**。両端の同一視を群の商として読む読みは A1 と両立しないため採らない（法 9 の 3 次指標が反例）。W による商は A1 とは両立するが採らない（D が商に降りない）。
   - 玩具（`notes/pag2_toy_origin_buildup.md`）の「ねじれて繋がる」は、複素指標の組の回転（A1 の位相 𝔀(χ) による、χ と χ̄ の組を実化した面の回転）と読む。メビウス型の −1 ではない（2026-11-27 08:21、著者の選択）。
-  - 玩具で素点どうしの結びつき（交差項）は加法の側に置く：加法指標は大域の ψ(·/N)（ℚ の上で自明）とし、素数 p_i の点の局所の貼り合わせは χ_i(N/N_i)·τ(χ_i)/√N_i（PAG261 の形 (I)。PAG260 `gaussSum_prodChar`・`stdAddChar_crtMap` と同じ割り振り）（2026-11-27 17:37、著者の選択）。
-  - 玩具 T0 の窓の貼り合わせ（無限素点の対数の格子の上の f(n+M) = U f(n)）は、無限素点に独立に置いた境界条件と読む。Tate の局所作用素から導いたものではなく、分岐する素数の形（付値の軸の幅 e の平行移動に位相を掛けたもの）の写しとも読まない（2026-11-28 07:13、著者の選択。経緯はノート §25〜§27）。
+  - 玩具で素点どうしの結びつき（交差項）は加法の側に置く（2026-11-27 17:37、著者の選択）。構築側の補足：そのとき加法指標は大域の ψ(·/N)（ℚ の上で自明）で、素数 p_i の点の局所定数は χ_i(N/N_i)·τ(χ_i)/√N_i（PAG261 の形 (I)。τ の割り振りは PAG260 `gaussSum_prodChar`・`stdAddChar_crtMap` から直ちに出る。局所定数との同定は Lean の外。ノート §15・§17）。
+  - 玩具 T0 の窓の貼り合わせ（無限素点の対数の格子の上の f(n+M) = U f(n)）は、無限素点に独立に置いた境界条件と読む（2026-11-28 07:13、著者の選択）。構築側の補足：したがって Tate の局所作用素から導いたものではなく、分岐する素数の形（付値の軸の幅 e の平行移動に位相を掛けたもの）の写しとも読まない。境界条件の位相は A1 で 𝔀(χ) と置く入力で、それが局所定数の積に等しいことは Tate の定理（注入→回収。ノート §25〜§27）。
 - 基礎は離散的であり、直線のような連続対象は基礎に存在しない。
+- **外した（2026-11-28 20:02、著者の決定「外す前提で進めます」）**：「解像度」と、それにかかわる命題 3（次の行の定義文）は、アーデル射影幾何の構築から外す。次の行から「保留」の項までは記録として残し、構築の規則としては使わない（構築側の補足：基礎文書では第 3 章を記録に下げ、第 4 章は解像度の語を使わない形に組み替える）。
 - 直線は、解像度を落としたときに創発する有効な姿である。
   - 解像度のパラメータは**未決定**。N、K、Λ のいずれとも同一視しない。
   - 命題 3 の置き方（著者はいつでも覆せる）：定義の文面は変えない。解像度の操作の置き場は「対象の中の移行」ではなく、大域対象への**切り方（見方）の選択**（解釈の層）。素点たちは制限積の因子として最初から並列に共存している全体が対象で、有限レベル商と Λ 切断はその全体への見方の 2 軸。命題 3 の問いは「見方を粗くしたとき直線がどう見えるか」と読む。
@@ -27,21 +30,22 @@
   - 読みとして L1（解像度＝測る素点の集合）を採っている（定義の文面ではない）。
   - 「直線の創発」という表現は使わない。命題 3 に触れるときは「§1 の命題 3（解像度と有効な姿）」と参照で書き、何がどう変わるかを数学の言葉で書く。
   - **保留（2026-11-26 20:35、著者の決定）**：「解像度」は保留とし、場合によってはアーデル射影幾何の構築から外す。理由：「解像度」は Muse との会話を始めてから生まれた言葉で、当初の構想にはなかった。上の項目（命題 3 とその読み）は記録として残す。
+  - 構築側の補足（2026-11-28、外した後も有効）：完備化（ℚ_p、𝔸_f、L²、ℝ など）を使うときは「計算の道具として使い、有効な姿や目標としては書かない」と断る。閉包・完備化に現れる連続体を目標として書かない。「直線の創発」の語は使わない。
 - 「射影」の読み（解釈の層、留保つき）：
   - 舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28（PAG23〜PAG32））。その上で働く**貼り合わせの合成**を射影と呼ぶ。主は変換。貼り合わせは U（ねじれた貼り合わせ）を指し、PAG23 の `Compat`（ねじれのない座標の貼り合わせ）ではない。命名の「射影」は舞台と変換の組を指す。
   - 構築側の読み（著者が留保つきで材料に採用）：その合成は反転（乗法の側）と加法の変換（加法の側）の合成で、有限レベルでは Part 252（PAG256）の J∘H_N/√N（`PAG.Part256.JH`）に当たる。ただし `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。照合した範囲（PAG23・PAG26・PAG27・PAG256）では JH と P¹ のモデルを結ぶ Lean の文はない（鎖全体は検索していない）。Part 262（PAG266）で Lean で結んだのは 𝔀 の値と P¹ の係数だけ。
   - 原始指標についての位相が、この合成（変換）の成分である。
   - 標準の核は Part 252 の Hartley 核（形式化の追認。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは未照合）。値は τ(χ)/(i^a√N)（`PAG.Part256.rootNum`、記号 𝔀。PAG256 の docstring と冒頭のコメントの記号 W(χ) もこの値を指し、反転の W とは別）。原始指標ではルート数だが、その同定は Lean の外（明記する）。素朴な核 e(xy) の値 τ(χ)/√N とは奇の指標で i 倍ずれ、このずれを滑らかにしない。
-  - 加法指標は**規約 T**（Tate の学位論文：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）を基礎文書の標準とする。規約 T のもとで、イデール類指標を不分岐な q で ω_q(q) = χ(q) と正規化して（χ̄ に対応させる規約では積が共役になる）、原始的な χ について、Hartley 核の因子 ε(χ) = (−i)^a（`PAG.Part256.parFac`）は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N は s = 1/2 での有限素点の局所定数の積と値が一致する（Lean の外、確信度：高。局所定数は Tate 1979 の流儀で定める）。明示的な因子 i^{±a} が無限素点の局所定数であることは規約によらないが、符号 χ(−1) を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が i^a、有限素点の積が χ(−1)τ(χ)/√N）。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。A1 は公準のまま。規約 T を採る根拠は、Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol（arXiv:math/9811040）とも同じ加法指標であること。材料は `notes/pag2_projection_material.md`、規約の文献照合は `notes/pag2_literature_ia_sign.md`。
+  - 加法指標は**規約 T**（Tate の学位論文：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）を基礎文書の標準とする。規約 T のもとで、イデール類指標を不分岐な q で ω_q(q) = χ(q) と正規化して（χ̄ に対応させる規約では積が共役になる）、原始的な χ について、Hartley 核の因子 ε(χ) = (−i)^a（`PAG.Part256.parFac`）は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N は s = 1/2 での有限素点の局所定数の積と値が一致する（Lean の外、確信度：高。局所定数は Tate 1979 の流儀で定める）。明示的な因子 i^{±a} が無限素点の局所定数であることは規約によらないが、符号 χ(−1) を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が i^a、有限素点の積が χ(−1)τ(χ)/√N）。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。A1 は公準のまま。規約 T を採る根拠は、Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol（arXiv:math/9811040。根拠はこの 1 本）とも同じ加法指標であること。材料は `notes/pag2_projection_material.md`、規約の文献照合は `notes/pag2_literature_ia_sign.md`。
   - 作用素のレベルでは、U は赤道（単数の上の関数の空間。極限では `Lim`）の上の作用素で、P¹ 全体には自然な条件だけでは一意に延びない（性質として書く。2026-11-26、著者の決定）。
 - 以上は解釈の層であり、形式化済みの定理ではない。ノートではその地位を混同して書かない。
 
 ## 2. 現在地（2026-11-26）
 
 - **モノグラフ層（1.0）**：イデール類群 C_ℚ 上の作用素系（D、T_p、W、二面体関係）。中心問題 P1 は自己共役拡張の境界条件 U の両立分類（定理 2.6）。定理 2.6 の U の空間は C_ℚ 上の関数（正則表現の側。Λ 切断の留保つき）。**公理 A1** は Tate の γ 因子の貼り合わせの λ = 0 での値の言い換えで、**解釈の層の公準（内容は Tate の定理）のまま**（導出済みと書かない）。
-- **PAG 2.0（有限レベル）**：Lean 形式化は Part 262（PAG266）まで。定理・補題 3,695 件、xlsx final84（3,722 項目）。件数は宣言総数など別の数え方と混同しない。Part n は PAG(n+4).lean（第 3 期）。
+- **PAG 2.0（有限レベル）**：Lean 形式化は Part 262（PAG266）まで（短期層の Part 263・264（PAG267・PAG268）はこの件数の外。索引に記録。2026-11-28 に追記）。定理・補題 3,695 件、xlsx final84（3,722 項目）。件数は宣言総数など別の数え方と混同しない。Part n は PAG(n+4).lean（第 3 期）。
 - **本線は基礎文書**（定義層を 1 つの文書にまとめる。草稿 1 が進行中）。新しいパートは始めない。文書の章の不足を埋めるときだけ走らせる。
-- 本来の道の未完の問いとしてかつて挙げていたもの（B-3 の続き、構造定理、Ẑ 上の定理 A）は、2026-11-12 の棚卸し監査で既知の定理かその帰結と判定された（`notes/pag2_audit_after_part251.md`）。解像度の定式化は §1 のとおり保留。
+- 本来の道の未完の問いとしてかつて挙げていたもの（B-3 の続き、構造定理、Ẑ 上の定理 A）は、2026-11-12 の棚卸し監査で既知の定理かその帰結と判定された（`notes/pag2_audit_after_part251.md`）。解像度は §1 のとおり構築から外した（2026-11-28 20:02）。
 - 辞書の閾値超え（補足 16）への対応は 2026-11-20 に実施済み（コミット 4357fb4）。
 - 収束アラームの兆候 4 は Part 249〜262 で 14 パート連続。残余のある問いは A1 か完備化（無限素点の側）を通るという見立てが、関門の結果と合っている（`notes/pag2_partial_inversion_preregistration.md`）。
 - 文献照合：MathSciNet は実施しない（著者の決定）。zbMATH は実施済みで、候補の地位を変える項目はなかった（`notes/pag2_literature_zbmath_20261126.md`）。
@@ -55,11 +59,11 @@
   1. 生成の分類（Part 245–248）。構造定理と、次元公式からの数行の系（⟨M*, E_N⟩ = A_N ⇔ N ∈ {1,4} ∪ 素数）を除き、残るのは項目 66（2 つの双対な代数の和の条件。宣言 `sumSub_eq_shellAlg_iff` は PAG249（Part 245））と項目 67〜69（完全な分類）で、範囲は合成数の N（確信度：中）。評価は「小さいノートの水準」で、新しい現象ではなく「誰も書いていない計算」。外部での新規性の留保は付けない。検索語：Terwilliger algebra, orbit Schur ring, cyclotomic S-ring, dual Bose–Mesner algebra, generated by, generating set。
   3. Part 258（PAG262）の不存在の側［新規候補（小さい）］：N ∣ M で素数 p が N と M/N の両方を割るとき、引き戻しと両立し殻を混ぜない単位的な代数準同型 A_N → A_M はない（確信度：低〜中）。「殻を混ぜない」は強い読み（φ(D_s) は D_t の、φ(E_s) は E_t の線形結合）。弱い読み・非単位的な写像・別の両立条件は、主張の外の別の問いとして残る。存在の側は既知（Hanaki–Kim–Maekawa の直積の定理）。**外部（応募書類を含む）で新規性として使わない**（留保は付いたまま。MathSciNet をやめたので条件は満たされないまま残る）。文献照合の記録は `notes/pag2_candidate3_literature_builder.md`。
   - かつての候補 2（定理 2.6 の提示形）は外れた。組み合わせ（α_{χ̄} = −α_χ とルート数）は既知の結果からの短い帰結（確信度：高）。この組み合わせを書いた文献は見つからなかった（確信度：中）が、新規性の根拠にならない（確信度：中〜高）。ルート数が条件を満たすことは整合性の確認で、A1 の導出ではない。反転の条件は境界ユニタリの実性と同値（CW が境界条件を保つ。手計算と数値）。Lean では PAG16・PAG173・PAG198 の 3 定理から出るが、組み合わせた 1 つの文は未形式化。近い先行は Burnol、Ibort–Lledó–Pérez-Pardo の例 7.1・7.2。
-- §3 の書き換えは著者の承認の後に行う。
+- §3 の書き換えは著者の承認の後に行う（2026-11-28 以降は、冒頭の「この文書の文面」の決定により Claude の判断で行い、記録する）。
 - 構造が必要なら、再証明せず辞書経由で文献を引く。
 
 **Part 250〜262 の地位（基礎文書に書くときの注意。詳細は索引と各ノート）**
-- Part 250：示せたのは「ℝ の中に基礎が、全不連結だがどの尺度でも鎖でつながる稠密な部分集合として入っている」こと（教科書的な例の対数座標版）。新規候補なし。「解像度を落とすと直線が現れる」は示せていない（商を取ると 1 点につぶれ、ℝ は完備化の側から現れるうえ、ℝ は定義に最初から使われている）。
+- Part 250：示せたのは「ℝ の中に基礎が、全不連結だがどの尺度でも鎖でつながる稠密な部分集合として入っている」こと（教科書的な例の対数座標版）。新規候補なし。「解像度を落とすと直線が現れる」は示せていない（商を取ると 1 点につぶれ、ℝ は完備化（ε → 0 の側）から現れるうえ、ℝ は定義に最初から使われている）。
 - Part 251：「イデール類群で稠密」は構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0} の同一視のもとでの読み（Lean にしていないもの：unitSys ≅ Ẑ^×、極限の普遍性・コンパクト性・位相群性、構造定理）。
 - Part 252〜254 の U_N は A1 の位相を定義として入れた作用素で、A1 は導かれていない。
 - Part 259：(iii) を外したときの奇数の場合の一意性は数値のみ。代数構造と制限テンソル積との同型は Lean の外。添字の順序は有向でない。
@@ -74,7 +78,7 @@
 
 - パートのサイクル：Python で数値照合 → Lean（sorry 0・警告 0）→ `#print axioms` → ノート＋xlsx。ノートの題名は「アーデル射影幾何」（旧称「アデール射影幾何 2.0」は使わない）。
 - 新しいパートの基準：幾何・大域・極限の言葉の問いに答えるか。代数内部の問い（中心の記述、生成元を足した代数の分類など）は主役にしない。有限レベルの代数は局所計算の装置として使う側に回す。冒頭に、本来の道（§1）のどの問いに仕えるかを書く（書けなければ始めない）。
-- **着手前の 4 点**（Lean の前に書き、推薦案として 1 つに絞ったものだけ始める）：(1) 問いを幾何の言葉（点・無限素点・解像度・創発）で書く、(2) 既存分野の言葉への最善の翻訳（写像は義務）、(3) 翻訳しても消えない残余を明示（空なら始めない。計算の細部だけなら短期層の小さいノート）、(4) 残余の文に対照群テストをかけ、結果を併記する。加えて、盲検の問いテストと内部照合（§6）。
+- **着手前の 4 点**（Lean の前に書き、推薦案として 1 つに絞ったものだけ始める）：(1) 問いを幾何の言葉（点・無限素点・貼り合わせ・大域・極限）で書く（2026-11-28 に「解像度・創発」を外した）、(2) 既存分野の言葉への最善の翻訳（写像は義務）、(3) 翻訳しても消えない残余を明示（空なら始めない。計算の細部だけなら短期層の小さいノート）、(4) 残余の文に対照群テストをかけ、結果を併記する。加えて、盲検の問いテストと内部照合（§6）。
 - **選択の委任**：構築側は関門（4 点・盲検の問いテスト・対照群テスト）を通した推薦案を 1 つに絞って出し、着手は著者側 Muse の決定による。何を選び、なぜかを記録する。著者はいつでも覆せる。
 - 判断の経路は 1 つ：このファイルと著者側の申し送りを唯一の記録とする。構築側のセッションで著者が選んだことは、引き継ぎメモに残して著者側へ戻す。
 - パート番号は「Part n（PAGm）」と併記する。
diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
index 26735be..cd9739a 100644
--- a/handoff/PAG2_handoff_part259.md
+++ b/handoff/PAG2_handoff_part259.md
@@ -1812,3 +1812,6 @@
     - （後注 2026-11-28、統合照合 XV の中 3・XVI の低 C：値の一致は A1 で入れた値を Tate の定理で読み替えたもの（注入→回収）。𝔀 ＝ 局所定数の積は A1 によらない。ノート §27）
 - 統合照合 XV（2026-11-28 09:15〜09:23、台帳 L41〜L43、`records/ledger_XV/`）：高なし・中 3・低 11・極低 8。ノート §27 の帰結 3 を直した（𝔀 ＝ 局所定数の積は Tate の定理で A1 によらない。値の一致は注入→回収）ほか、ノート・射影ノート・fixes.md の直し（ノート §28）。著者への報告と確認事項：(1) CLAUDE.md §2「Part 262 まで」と短期層の Part 263・264（PAG267・268）の食い違い、(2) CLAUDE.md §1 の玩具の 2 行目・3 行目の書き分けの承認（中 1・低 13）、(3) 完備化の断り書きの規則と「解像度」の保留の関係、(4) CLAUDE.md の規約 T の根拠の「根拠はこの 1 本」を戻すか（低 10）、(5) Part 250 の「（ε → 0 の側）」を戻すか、Part 259 の「(iii) を外したとき」が旧版にあるか（極低 19、XVI の極低 G）。L42 の H1（「新しいパートは始めない」）・M8（判断の経路は 1 つ）は著者の判断待ちのまま（この行で著者側へ戻す。低 10）。直しは台帳 L44 として統合照合 XVI（停止規則のもう 1 回）にかける。
 - 統合照合 XVI（2026-11-28 09:29〜09:32、台帳 L44、停止規則のもう 1 回）：高なし・中 1・低 5・極低 4。中 B（§27 の最後の項が局所定数の範囲を越えて局所作用素について言っていた）ほかを直した。規則（もう 1 回の後はこの規則で閉じる。L32 の前例）により L44 を閉じ、直しは L45 として次の統合照合に載せる。照合者は「B を直した後にもう 1 回」と読んでいるので、閉じ方の読みは著者の確認事項に足す。
+- 著者の決定（2026-11-28 09:43）：CLAUDE.md の混乱を避けるため、これ以降 CLAUDE.md は Claude が生成したものを採用する。CLAUDE.md・CLAUDE.en.md の冒頭に記録。XV の行の確認事項 (1)〜(5) と XVI の (6) を Claude の判断で処理した：玩具の 2・3 行目を著者の選択と構築側の補足に分けた、規約 T の「根拠はこの 1 本」と Part 250 の「（ε → 0 の側）」を旧版の文言どおり戻した、Part 259 は旧版にあるので変えない、§2 に短期層の Part 263・264 は件数の外と追記、保留の間の完備化の断り方を構築側の補足として追記。L44 は XVI の後に閉じた扱いのまま（L32 の前例）。H1・M8 は現行の文のまま採る。台帳 L45 に追記。
+- 本線（2026-11-28 15:5x、著者の指示「アーデル射影幾何学の構築を進めてください」）：玩具の材料を基礎文書に入れた。草稿 1 に 2.10「玩具の積み上げ」（rev 54）、「開いている問い」の無限素点の項に 1 文（rev 55）、索引に 2.10。台帳 L45 に追記。
+- 著者の決定（2026-11-28 20:02）：「解像度」と命題 3 をアーデル射影幾何の構築から外す（「外す前提で進めます」）。CLAUDE.md §0・§1・§2・§4（日英）、草稿 1 rev 67（第 3 章を記録に下げ、第 4 章を「有限個の素数の像（稠密と離散の二分法）」に）、索引の後注。台帳 L45 に追記。
diff --git a/notes/pag2_founding_material_index.md b/notes/pag2_founding_material_index.md
index bcc1194..316f65a 100644
--- a/notes/pag2_founding_material_index.md
+++ b/notes/pag2_founding_material_index.md
@@ -217,8 +217,21 @@
 - 依存と既知のラベルの候補（後注 2026-11-26、監査 `pag2_audit_20261126.md` の照合 B の指摘を受けて構築側が足した。著者の 10:29 の「お勧めで進めて」による）：「N ∣ 24」は、位相に無限素点の局所定数を含めるときの値で、素朴な位相では N = 2, 3, 4, 6, 12（上の対照群の行）。N ∣ 24 は、すべての単数 a で a² ≡ 1 (mod N) ⇔ N ∣ 24（(ℤ/N)^× の指数が 2 を割る条件。古典）から、法 N の指標がすべて実になる条件と同じで、実の原始指標では Gauss の符号定理により 𝔀 = 1。したがって 2.9 の N ∣ 24 は［既知］の候補（照合 B と構築側の手の読み、Lean の外、確信度：中〜高。照合 B が挙げた出所は arXiv:1104.5052）。（後注 2026-11-26、統合照合 IX の指摘による）この 2 つの事実が支えるのは N ∣ 24 ⇒ U_N = I の向きだけ。逆向き（N ∤ 24 なら U_N は単数の角に入らない）には、ある導手 f ∣ N の原始指標で W が実でないこと（W(χ̄) = conj W(χ) から位相が導手ごとに一定でなくなる）が要り、Chowla–Mordell 型の事実による（後注 2026-11-26 14:5x、統合照合 XI の指摘で下書きに揃える：「による」は「が要る」と読む。一般の合成数の導手での形は確かめていない）。照合者の計算では、f ∣ N のすべての導手で W が一定になる N は N ≤ 200 でちょうど {1, 2, 3, 4, 6, 8, 12, 24}（「角に入るには導手ごとに位相が一定である必要がある」という読みのもとで）。
 - ノート：`pag2_projection_interaction_preregistration.md`。数値：`records/projection_interaction/`（`interaction_check.log`、`extra_checks.log`、`sign_corner_check.log`、`control_fqt_interaction.log`）。
 
+**2.10 玩具の積み上げ（無限素点の境界条件、素数の点の局所作用素、極限の加法指標）。**（2026-11-28 に追加。草稿 1 rev 54 の 2.10）
+- 地位：どの段も［既知］か［再導出（小さい）］。新規候補なし。新しい Lean はない。著者の選択 3 件（2026-11-27 08:21・17:37、2026-11-28 07:13）は CLAUDE.md §1。
+- 内容（段ごと）：
+  - 無限素点（T0・T1）：窓の貼り合わせ f(n+M) = U f(n) は独立に置いた境界条件。ねじれは複素指標の組の回転（A1 の位相、入力）。
+  - 交差項（段 5〜7）：加法の側（ψ(·/N)）に置く。置き場所は規約の量で、不変な内容はない。
+  - 極限の加法指標（段 7）：埋め込みに沿って ℚ/ℤ の e にまとまる。水準の核は f < N で常に 𝔀(χ*) と違う（Montgomery–Vaughan Thm 9.10）。一意性は `PAG.Part258.UA1_family_unique` の仮定の形でだけ。
+  - 極限の合成（段 8）：U_∞ を加法の変換・導手の軌道の読み出し・反転・ε_∞ の合成で書けるが、導手ごとの射影が要り、中身はガウス和の定義の書き直し（円環の第 2 の型）。
+  - 素数の点（段 9）：分岐なら付値の軸の幅 e の平行移動に位相、不分岐なら γ 因子を記号とするローラン作用素（Tate、Burnol）。無限素点は平行移動ではない。
+- 留保：𝔀 ＝ 局所定数の積は Tate の定理で A1 によらない。境界条件と局所作用素の値の一致は注入→回収。ℚ_p・𝔸_f・L² は計算の道具。照合は盲検の問いテストと統合照合 XV・XVI（照合者の文脈に CLAUDE.md が入っていた）。
+- ノート：`pag2_toy_origin_buildup.md`。数値：`records/toy_origin/`。
+
 ## 第 3 章　解像度と有効な姿（§1 の命題 3）
 
+（後注 2026-11-28 20:0x：著者の決定（20:02「外す前提で進めます」）で、解像度と命題 3 は構築から外した。草稿 1 では第 3 章を「（記録）外した項目」に下げた（rev 67）。この章の項目は記録として残す。CLAUDE.md §1。）
+
 **3.1 定義文と、その置き方と読み。**
 - 地位：
   - 定義文（著者の文面）：直線は解像度を落としたときに創発する有効な姿。解像度のパラメータは未決定。
@@ -250,6 +263,8 @@
 
 ## 第 4 章　解像度ごとの姿（設計についての定理 1）
 
+（後注 2026-11-28 20:0x：解像度を外したので、草稿 1 では第 4 章の見出しを「有限個の素数の像（稠密と離散の二分法）」に替え、本文の「有限の解像度」を「有限の素点の集合」に、閉包の直線の読みを「完備化の側のもので目標としては書かない」に替えた（rev 67）。定理の地位は変わらない。）
+
 **4.1 Part 255 の二分法：測る素点と、像の離散・稠密。**
 - 地位：定理［既知（再導出）］。骨格は、証明の部品が S 単数定理・積公式・弱近似（既知）であることを明記するとしている。
 - Lean（Part 255（PAG259））：
@@ -451,6 +466,7 @@
   - 角の写像の像が角全体であること、極限の具体形、Bost–Connes の ρ との対応（5.5・6.3）。
   - A_∞ と射影の変換・貼り合わせ・符号の相互作用の文（2.9 の「Lean の外」の行。Lean にしない推薦が採られている）。
 - **定式化の問い**：
+  - （後注 2026-11-28 20:0x：命題 3 と解像度の操作についての問い（下の 1 つ目の追記と「解像度の操作に、L1 を超える定式化が要るか」）は、著者の決定（20:02）で構築から外したので閉じた。記録として残す。）
   - 追記（後注 2026-11-26、監査 `pag2_audit_20261126.md` の照合 B の指摘を受けて構築側が足した。著者の 10:29 の「お勧めで進めて」による）：§1 の命題 3（解像度と有効な姿）には、まだ数学の文がない（第 3・4 章は解像度ごとの姿を与えるものではない）。素点の集合（点）と舞台 P¹ の関係：P¹(Ẑ) = ∏ P¹(ℤ_p) の点は素点ではなく、素点を点とする空間（既知の類似は Spec ℤ ∪ {∞}、未照合）は出てこない（後注 2026-11-26、統合照合 IX の指摘：6.6 との食い違いを直す。第 3・4 章は命題 3 の「有効な姿」を与えるものではない（下書きの第 3 章冒頭の言い方に揃える）。素点を点とする空間はこの文書の構成には出てこない。既知の対応は 6.6 の Spec ℤ̄ で、主 Arakelov 因子の定義は構築側が Schoof で確認）。定義の「重なり」（無限素点で無限大と無限小が重なる）と、P¹ で 0 ≠ ∞ で反転が 2 点を入れ替えること（1.4）の関係：U による読みはあるが、空間のレベルの対応は書かれていない。（後注 2026-11-26 11:02、著者の決定 (a)：重なりは作用素の側でだけ書き、空間のレベルの対応は立てない（2.1）。）（後注、統合照合 IX の指摘：「空間のレベルの対応は立てない」は (a) から構築側が読んだ帰結で、著者の文言ではない。）無限素点の中身：注入（A1）を除いた中身はまだない（2.1・2.9）。
   - 解像度の操作に、L1 を超える定式化が要るか。骨格の記述では、現時点では L1 と 08:41 の定義で文書は書ける。
   - 「射影」の、全素点を通した一つの構成（空間と作用素のレベル）としての定式化。値のレベルについては 2.7。（後注 2026-11-25：空間のレベルは Part 263（1.4 の追記）。作用素のレベルは、持ち上げが自然な条件だけでは一意でない（2.4 の追記、読み）。局所性の条件を定義として採るかどうかは著者の判断。）（後注 2026-11-26：2026-11-26 05:55、著者の決定：方向の監査 §4 の選択肢 1。U は赤道（極限では単数の上の関数の空間 `Lim`）の上の作用素で、P¹ 全体には自然な条件だけでは一意に延びない、と性質として書く。局所性の条件は定義として採らない。新しい Lean は作らない。作用素のレベルの問いは、この書き方で閉じる。）（後注 2026-11-26、統合照合 V-b の指摘：著者の回答の原文は「1」（方向の監査 §4 の選択肢 1：留保を性質として書く、新しい Lean は要らない）。この記録のうち「局所性の条件は定義として採らない」「層別の持ち上げの Lean は作らない／新しい Lean は作らない」「作用素のレベルの問いは、この書き方で閉じる」は、選択肢 1 を選んだ帰結として構築側が読んだもの（選択肢 2・3 を採らない）。書く性質「自然な条件だけでは一意に延びない」の中身は読み（Lean の外：盲検の照合者の数値の反例と手の議論、照合者の確信度：高）で、基礎文書でもその地位を添える（この一文は構築側の方針で、著者は未確認。統合照合 VI の指摘で 2026-11-26 に足した）。挙げた句のうち、この記録にないものは当てはまらない（統合照合 VI の指摘）。）
diff --git a/notes/pag2_tail_ledger.md b/notes/pag2_tail_ledger.md
index 097db89..83f68c3 100644
--- a/notes/pag2_tail_ledger.md
+++ b/notes/pag2_tail_ledger.md
@@ -12,6 +12,9 @@
   - この台帳（L44 を閉じ、L45）。`records/ledger_XVI/`（入力・依頼文・出力・meta）。
 - 直していないもの：XV から持ち越した CLAUDE.md の文に関わる項目（中 1・低 10 の後半・低 11 の規則の関係・低 13・極低 19）は、著者の承認・判断待ちのまま。
 - 自己申告（根拠にしない）：中 B は主張を狭める直し。ほかは帰属・後注・記号の書き足し。
+- 追記（2026-11-28 09:4x、著者の決定「これ以降、CLAUDE.md は Claude が生成したものを採用する」（09:43）を受けて）：CLAUDE.md・CLAUDE.en.md の冒頭にこの決定を記録し、XV・XVI から持ち越した CLAUDE.md の項目を Claude の判断で直した。玩具の 2 行目・3 行目を「著者の選択」と「構築側の補足」に分けた（中 1・低 13）。規約 T の根拠に「根拠はこの 1 本」を戻した（低 10）。Part 250 に「（ε → 0 の側）」を戻した（極低 19。旧版の文言を CLAUDE-history.md で確かめた）。Part 259 の「(iii) を外したとき」は旧版にある（「(iii) を外すと a = 2 では捩れた写像があり一意でない（奇数の場合の一意性は数値のみ）」）ので変えない。§2 に短期層の Part 263・264 は件数の外と追記（中 2）。保留の間の完備化の断り方を構築側の補足として §1 に追記（低 11）。§3 の書き換えの承認の行に決定の注。H1・M8 は現行の文のまま採る（Claude の判断）。
+- 追記（2026-11-28 15:5x、著者の指示「アーデル射影幾何学の構築を進めてください」（15:46）を受けて）：本線（基礎文書）に玩具の材料を入れた。草稿 1 に 2.10「玩具の積み上げ」を新設し（rev 54）、「開いている問い」の「無限素点の中身」の項に 1 文足した（rev 55）。索引に 2.10 を足した。新しい主張はなく、ノート §0〜§28 の要約。引き継ぎメモに 1 行。
+- 追記（2026-11-28 20:0x、著者の決定「外す前提で進めます」（20:02。解像度と命題 3 を構築から外す）を受けて）：CLAUDE.md・CLAUDE.en.md の §0・§1・§2・§4 に記録（§1 の解像度の項目は記録として残し、完備化の断り方を構築側の補足として外した後も有効にした）。草稿 1（rev 67）：第 3 章を「（記録）外した項目」に下げて冒頭に記録の段落、第 4 章の見出しと本文の解像度の語を替え、2.6・1.2・開いている問い・6.6 の表に注。索引の第 3・4 章と §6 に後注。引き継ぎメモに 1 行。
 - 扱い：照合は受けていない。次の統合照合に載せる（著者が求めれば独立の照合にかける）。
 
 ## 閉じた項目

```

## §3 草稿 1 の変わったブロック
草稿 1（Claude の文書、プロジェクト 738511fa…）の rev 52 → rev 67 で変わったブロックの本文（read の sinceRev=52 の結果からタグを外して写したもの。2026-11-28 20:2x、構築側）

[1.2 の太字の文と括弧]
大域対象は、制限積の因子として最初から並列に共存する素点たちである。有限レベル商と Λ 切断は、その全体への見方（切り方）である。（読み。§1 の命題 3 の置き方として、著者側 Muse が 2026-11-13 に決めた。著者はいつでも覆せる。命題 3 は 2026-11-28 に構築から外したが、大域対象と見方の読みはそのまま使う（構築側の判断））

[1.2 の次の段落（直す前は「解像度を N・Λ と同一視しない。この読みで決まったのは問いの置き場であり、パラメータではない。」）]
（記録）外す前は、解像度を N・Λ と同一視せず、この読みで決まったのは問いの置き場でありパラメータではない、としていた。解像度は 2026-11-28 に外した（第 3 章）。

[2.6 の留保（直す前の末尾は「完備化は、読みとしては解像度が落ちる側の操作である。」）]
留保：U_N は A1 の位相を定義として入れた作用素で、A1 は導かれていない。直和を 1 つの文にした定理はない。PAG.Part258.Lim と Ẑ^× の上の局所定数関数との同一視、完備化 L²(Ẑ^×) は Lean の外である。完備化は計算の道具として扱い、有効な姿や目標としては書かない（2026-11-28 に解像度を外した後の断り方）。

[2.10（新設、rev 54）]
### 2.10 玩具の積み上げ
玩具「∞ と −∞ と 0 が射影でねじれて繋がる」を原点から積み上げると、無限素点の貼り合わせは独立に置いた境界条件、素数の点の貼り合わせは Tate の局所作用素、極限の加法指標は ℚ/ℤ の 1 つの指標になる。（どの段も［既知］か［再導出（小さい）］。新規候補はない。ノート notes/pag2_toy_origin_buildup.md、2026-11-27〜28）
- 無限素点（段 T0・T1）：対数の格子の上の窓の貼り合わせ f(n+M) = U f(n) は、無限素点に独立に置いた境界条件と読む（2026-11-28 07:13、著者の選択）。窓の幅 M は自由なパラメータで、ねじれは複素指標の組の回転（A1 の位相 𝔀(χ) による。2026-11-27 08:21、著者の選択）。位相は A1 で入れた入力で、導いたものではない。
- 交差項（段 5〜7）：素点どうしの結びつきは加法の側に置く（ψ(·/N)。2026-11-27 17:37、著者の選択）。交差項の置き場所は加法指標の取り方で動く規約の量で、不変な内容はない。
- 極限の加法指標（段 7）：水準ごとの ψ_N は埋め込み x ↦ (M/N)x に沿って ℚ/ℤ の 1 つの指標 e にまとまる（還元に沿っては両立しない）。e は規約 T の有限部分 ψ_f が 𝔸_f/Ẑ ≅ ℚ/ℤ を通じて誘導するもの。水準の核 J∘H_N/√N は導手 f < N の指標の上で常に 𝔀(χ*) と違い（μ(N/f)χ*(N/f)√(f/N)𝔀(χ*)、Montgomery–Vaughan Thm 9.10）、両立する族の一意性は 2.6 の PAG.Part258.UA1_family_unique の仮定の形でだけ成り立つ。
- 極限での合成（段 8）：U_∞ は「ℚ/ℤ の点への加法の変換 → 導手の軌道での読み出し → 反転 → ε_∞」の合成として書けるが、作用素としては導手ごとの射影が要り、中身はガウス和の定義の書き直し（構成から自明な形の一致）。
- 素数の点（段 9）：J_p∘F_p は、分岐していれば付値の軸の上で幅 e（導手の指数）の平行移動に位相 τ(χ)/p^{e/2} を掛けたもの、不分岐なら γ 因子を記号とするローラン作用素（Tate、Burnol）。平行移動か否かは局所の L 因子が自明か否かで分かれ、無限素点の J∘F（Γ 因子の比）は平行移動ではない。
留保：境界条件の位相 𝔀(χ) が局所定数の積に等しいことは Tate の定理（規約 T、ω_q(q) = χ(q)、Lean の外）で、A1 によらない。したがって無限素点の境界条件と素数の点の局所作用素の値の一致は、A1 で入れた値を Tate の定理で読み替えたもの（注入→回収）であり、玩具の幾何からの導出ではない。ℚ_p・𝔸_f・L² は計算の道具として使い、有効な姿としては書かない。数値は証明ではない。照合は盲検の問いテストと統合照合 XV・XVI（照合者の文脈に CLAUDE.md が入っていた）。

[第 3 章の見出し（直す前は「第 3 章　解像度と有効な姿（§1 の命題 3）」）]
第 3 章　（記録）外した項目：解像度と有効な姿（§1 の命題 3）

[第 3 章の冒頭に新設した段落]
この章は記録である。 2026-11-28 20:02 の著者の決定で、「解像度」とそれにかかわる命題 3 はアーデル射影幾何の構築から外した。以下は外す前の定義・置き方・読みと、否定的な結果を含む 1 つの試み（Part 250）の記録で、この文書の主張でも書き方の規則でもない。完備化（ℚ_p、𝔸_f、L²、ℝ など）を使うときは、外した後は「計算の道具として使い、有効な姿や目標としては書かない」と断る。

[第 3 章の段落（直す前は「第 3・4 章は、命題 3 の「有効な姿」を与えるものではない。第 4 章の見出しの「姿」は、像が離散か稠密かのことである（構築側の説明）。」）]
第 4 章は命題 3 によらない。2026-11-28 に第 4 章の見出しから解像度の語を外した。第 4 章の内容は、有限個の素数の像が離散か稠密かの二分法である（構築側の説明）。

[第 4 章の見出し（直す前は「第 4 章　解像度ごとの姿」）]
第 4 章　有限個の素数の像（稠密と離散の二分法）

[4.1 の守備範囲の項（直す前は 2 か所とも「有限の解像度」）]
守備範囲：ℚ_{>0} を基礎にすると、∞ を測るどの有限の素点の集合でも像は稠密になる（PAG.Part259.dense_rho_image から射影で直ちに出る。独立の Lean の文はない）。有限の素点の集合の中では、離散の側は有限の基礎 ⟨S⟩ でだけ起こる。

[4.1 の留保（直す前は「閉包に現れる直線は、読みとしては解像度が落ちた印（08:41 の定義）である。」）]
留保：二分法を 1 つの文にはしていない。直極限の位相と PAG.Part259.BoxCoord の同一視は Lean の外。閉包に現れる直線は完備化の側のもので、この文書の目標としては書かない（解像度による読みは 2026-11-28 に外した。第 3 章の記録）。その直線が無限素点の座標であること、および対照群 𝔽_q(t) で直線が現れないこと（ノルムの像は q^ℤ）は、骨格の記述で Lean の外である。

[6.6 の表の 1 行目のセル（直す前は「解像度 L1」）]
解像度 L1（外した項目。記録）

[開いている問いの冒頭の段落]
計算以上の残余を持つ問いは、形式化の側には見つかっていない（2026-11-25 の方向の監査の §5。2026-11-26 の監査でも同じ見立て。「見つかっていない」は「ない」ではない）。残るのは、著者側の作業と判断、定式化の問い、そして Lean の外・数値のみで残るもの（読み・数値・未確認の問いを含む）である。このうち §1 の命題 3（解像度と有効な姿。2026-11-28 に構築から外した）と無限素点の中身は、著者の読みが固まるまで、形式化の問いに置き換えて始めない（2026-11-26 16:15、著者の指示）。

[開いている問い・定式化の問いの 3 項]
- （外した。2026-11-28 20:02、著者の決定。記録として残す）§1 の命題 3（解像度と有効な姿）には、まだ数学の文がない（第 3・4 章は命題 3 の「有効な姿」を与えるものではない）。
- 無限素点の中身：注入（A1）を除いた中身はまだない（2.1・2.9）。玩具の積み上げでも、無限素点の貼り合わせは独立に置いた境界条件で、その位相は A1 の入力のまま（2.10）。
- （外した。2026-11-28 20:02、著者の決定。記録として残す）解像度の操作に、L1 を超える定式化が要るか（骨格の記述では、現時点では L1 と 08:41 の定義で文書は書ける）。


## §4 統合照合 XVI の出力
# 統合照合 XVI の出力（2026-11-28 09:29〜09:32）

依頼文：`../integrated/request_XVI.md`、入力：`../integrated/input_XVI.md`。以下は返信の全文（構築側は変えていない）。

---

# 統合照合 XVI の報告（台帳 L44）

**結論**：高はありません。中が 1 件、低が 5 件、極低が 4 件です。主張を強める直しも、著者の判断の記録の書き換えも見つかりませんでした。中の 1 件は、直しのうち 1 か所が、確かめた範囲（局所定数）を越えて局所作用素について言っている点です。

**照合の根拠**
- 根拠は入力 `input_XVI.md` の全文です（1〜1143 行）。
- 文脈に入っていた CLAUDE.md は 2 点だけに使いました。
  - §2 が今も「Part 262（PAG266）まで」と書いていること。
  - 玩具の 3 行が XV の記述のまま変わっていないこと。差分に CLAUDE.md のハンクがないこととも合います。
- ユーザーの記憶は判定の根拠にしていません。

**確かめられなかったこと**
- Lean の形式文。
- 盲検の出力の原文：段 6 の E2、段 9 の P1 (a)・P3。後注の要旨が原文と合っているかは照らせていません。
- `local_eps.py` の既定値 M = e + 2。
- 台帳 L34・L35 の原文（極低 20 の説明の根拠）。
- 著者へ実際に報告が届いたか。

---

## 1. XV の指摘ごとの判定

| XV | 判定 | 根拠 |
|---|---|---|
| 中 1 | 直していない（理由は支えられている） | XV 自身が「CLAUDE.md の文なので、著者の承認を得てから直す」と書いています。引き継ぎメモの XV の行 (2) と §28 に記録があります。文脈の CLAUDE.md でも 17:37 の行はそのままです。 |
| 中 2 | 一部 | §21 (a) に「短期層の宣言で、CLAUDE.md §2 の件数（Part 262 まで）の外」とあり、§28 と引き継ぎメモ (1) にも記録があります。ただし §28 は「…に従い、著者に報告した（2026-11-28）」と書いており、規則どおりに動いたように読めます。実際には、食い違いの付記は 11-27 18:5x の §21 にあり、その後も段 8・9 を続けています。「作業を止める」ことはしていません。このことが記録にありません（低 A）。 |
| 中 3 | 一部（新しい行き過ぎが 1 つ） | XV の案とほぼ同じ文になりました。A1 は入力、𝔀 ＝ ∏ε は Tate の定理で A1 によらない、値の一致は注入→回収、と書いています。ただし最後の項「玩具の取り決め ψ(·/N)（§17）では局所の因子は形 (I) になり、積は同じ」は、§25 の局所作用素についての文として置かれています。§15 で形 (I) を確かめたのは局所定数 ε(1/2, …) だけです。ψ(·/N) の側で作用素 J_p F_p を計算した記録はありません（中 B）。また、引き継ぎメモの 07:13 の行「両者の値の一致を担うのは A1（解釈の層）」には後注がありません（低 C）。 |
| 低 4 | 直った（理由に残りあり） | 「log p の ℚ 上の 1 次独立（素因数分解の一意性）」に直りました。Beurling・関数体の違いの書き方も正しいです。ただし直した後の文では対照群に違いが出るので、CLAUDE.md §6 の規則（形と稠密性だけの文は算術の内容なし）は理由になりません。「算術の新しい内容は運ばない」は構築側の判断ですが、そうと示されていません（低 D）。 |
| 低 5 | 直った | §13 の後注で §12 の読みもまとめて扱いました。§15 の後注と、引き継ぎメモの段 6 の行の後注もあります。§12 そのものではなく §13 に置いたのは、記録の形として問題ありません。 |
| 低 6 | 直った | /tmp で数え直しました。挙げた 14 個の法の実の原始指標は 11 個です（3・4・5・7・8×2・11・12・13・20・21）。N = 15・17・19 はそれぞれ 1 個あり、計算外です。N = 10・14・18 は 0 個なので、書かなくても正しいです。 |
| 低 7 | 一部 | §0 は、本文を書き換えずに対応づけの後注を置く形です。後注は［観察］を 3 種のラベルのどれに当てるかを書いていません（極低 E）。§17 の A → B の文は「『局所の貼り合わせ ＝ ψ(·/N) での局所定数』はそこから直ちに出る割り振り」と書いています。Lean の文から直ちに出るのは τ の割り振り（形 (I) の因子）までです。それが局所定数であることは Tate の局所理論（Lean の外、§15 の数値）によります。B の範囲が広すぎます（低 F）。 |
| 低 8 | 直った | 手で導きました。S_n χ = μ(n/f)χ*(n/f)τ(χ*)/√n · χ で、n = fm で足すと式どおりになります。/tmp の数値でも確かめました。f = 5、s = 2、u = 1 で −0.017160 + 0.036824i に対し、右辺は −0.017161 + 0.036825i です（打ち切りの範囲）。訂正表の 𝔀 → τ/√f は、ε_∞ = (−i)^a を除いた差 i^a と合います。 |
| 低 9 | 直った | §25 の冒頭と §22 の Burnol の行に後注があります。 |
| 低 10 | 前半は直った。後半は直していない（理由は支えられている） | H1・M8 は引き継ぎメモの XV の行で著者側へ戻しました。「根拠はこの 1 本」は確認事項 (4) にしました。XV は「戻さない理由を fixes.md に書く」という道も示していましたが、CLAUDE.md の文なので著者の判断待ちにするという理由が L44 にあります。 |
| 低 11 | 一部（理由は支えられている） | 1 行は §0 ではなく §28 に置かれました。規則の関係を著者に確かめる事項 (3) にしたことは、記録どおりです。 |
| 低 12 | 直った（形は違う） | 段 5 で盲検をしなかった理由は §28 にあります。訂正表は見出しではなく、§15 の後注で 2 項を当てる形です。 |
| 低 13 | 直していない（理由は支えられている） | 中 1 と同じです。 |
| 低 14 | 直った | 「log m = 2.485 を上回る（数値での観察）」です。log 12 = 2.4849 で、φ(13) = φ(21) = 12 と合います。 |
| 極低 15 | 直った | §19 の訂正表に足しました。 |
| 極低 16 | 直った（原文とは照らせない） | §15 の E2 の要旨、§25 の P1 (a)・P3 を足しました。内容は数学として正しいです。F_p は χ を χ̄ へ送り、J_p で χ に戻ります。ω_q(q) = χ(q) のとき ω_p|ℤ_p^× = χ_p^{−1} です。CLAUDE.md の規約の文とも合います。 |
| 極低 17 | 直った | |
| 極低 18 | 直った | fixes.md に後注があります。 |
| 極低 19 | 直していない（理由は支えられている） | CLAUDE.md の文で、確認事項 (5) にしています。Part 259 の限定を旧版と照らす件は、確認事項に入っていません（極低 G）。 |
| 極低 20 | 直していない（理由は一部しか確かめられない） | 「閉じた記録は書き換えない」は、これまでの台帳の運用（L41 の記載）と合います。「L35 の最初の項目と L34 の追記の両方に記録がある」という事実は、L34・L35 の原文が入力にないので確かめられません。 |
| 極低 21 | 直った（一部は確かめられない） | §19 の後注は、ログにあるものとないものを分けて書いています。§15 の「M = e + 2 はスクリプトの既定値」は新しい事実の申告で、照らせません。 |
| 極低 22 | 直った | §5 の題に添えました。 |

**「直していないもの」の理由**：中 1・低 13・低 10 の後半・極低 19・低 11 の規則の関係は、どれも CLAUDE.md の文に関わります。XV 自身の「著者の承認を得てから」と、引き継ぎメモの確認事項 (2)〜(5) が、この理由を支えています。極低 20 は上の表のとおりです。

## 2. 新しい主張・主張の強化

- **§27 の帰結 3**：全体として主張を狭める直しです。A1 の役割を入力に限り、一致を注入→回収と明記しています。ただし最後の項は、局所定数の文（§15）を局所作用素の文に広げています（上の中 B）。
- **§28（新設）**：数学の主張はありません。「規則に従い報告した」という書き方は、手続きを守ったように読めて、実際より強いです（低 A）。
- **§26 の「1 次独立」**：数学としては正しいです。2 つの素数の幅が有理数倍にならないことには 2 元の一意分解で足り、1 次独立はそれより強いですが、誤りではありません。対照群の違いを認めたうえで「算術の新しい内容は運ばない」と言い切っていますが、これは規則による理由ではなく判断です（低 D）。
- **§17 の重複の判定**：A から B に弱めました。ただし B の対象に局所定数との同定まで含めています（低 F）。
- **後注**：
  - §13 の後注の「不変な内容はない」は、§19 の 6 と同じ文言で、新しい強化ではありません。§12 の相互法則の文（［既知］）を規約のもとの恒等式として残すことは否定していません。ただ、読む側が §12 の相互法則の文まで「規約の人工物」と受け取るおそれはあります（極低 H）。
  - §0 の後注は、§25 P4 の［短い帰結（照合者の確信度：中〜高）］を［既知］に当てています。文献の出所がない項目なので、［再導出（小さい）］の方が近いです（極低 E に含めます）。

## 3. 著者の判断の記録・閉じた記録・範囲

- **著者の判断の記録**：
  - ノート §11・§16・§26 の後注、§17 の「ラベル」の行、§27 の「選択」の項は、差分のハンクに含まれていません。書き換えはありません。
  - 引き継ぎメモの 08:21・17:37・07:13 の行も、文脈の行としてそのまま残っています。
  - CLAUDE.md のハンクはありません。文脈の CLAUDE.md の玩具の 3 行も XV の記述のままです。
- **閉じた項目に移した L41〜L43**：消した行（57〜95 行）と足した行（4 字下げを外したもの）を機械で比べました。34 行すべてが一字一致しました。§1 の台帳 L44 と、差分の L44 の 11 行も一致しました。
- **閉じた項目への指摘の割り振り**：XV の 22 件がどれも 1 回ずつ L41〜L43 のどれかに割り振られています（中 3・低 11・極低 8）。
- **L44 の範囲の漏れ**：玩具のノートの 18 ハンク、射影ノート C3、fixes.md、引き継ぎメモの 2 か所、台帳は、すべて範囲の行と 1 対 1 で対応します。漏れはありません。
  - ファイル名は `pag2_projection_superposition_preregistration.md` ですが、L41 以来「射影ノート」と呼んでおり、一貫しています。

## 4. 直すべき点（重要度順）

**高**：なし。

**中**
- **B**：§27 の帰結 3 の最後の項を直す。案：「§25 の局所作用素は標準の ψ_p で計算した。玩具の取り決め ψ(·/N)（§17）では、局所定数は形 (I) の因子になり（§15 の数値）、積は同じ。ψ(·/N) での局所作用素そのものは計算していない」。

**低**
- **A**：§28 の中 2 の項に、次の 1 文を足す。「付記を書いた 2026-11-27 18:5x の時点では作業を止めず、段 8・9 を続けた。報告は 2026-11-28 の XV の後」。
- **C**：引き継ぎメモの 07:13 の行に後注を足す。案：「（後注 2026-11-28、統合照合 XV の中 3：値の一致は A1 で入れた値を Tate の定理で読み替えたもの（注入→回収）。𝔀 ＝ 局所定数の積は A1 によらない。ノート §27）」。CLAUDE.md §6 の「すべてに同じ直しを入れる」に当たります。
- **D**：§26 の「算術の新しい内容は運ばない…問いとしては立てない」を、構築側の判断として書く。案：「…問いとしては立てない（構築側の判断。CLAUDE.md §6 の稠密性の規則は、この文には当たらない）」。§27 の「残る問い」も同じにする。
- **F**：§17 の B の文を分ける。案：「重複の B：τ の割り振り（形 (I) の因子）は CRT 分解の Lean の文から直ちに出る。その因子が ψ(·/N) での局所定数であることは Tate の局所理論（Lean の外、§15 の数値）」。

**極低**
- **E**：§0 の後注に「［観察］は 3 種のラベルの外で、主張ではなく観察として置く」を足す。§25 P4 は［再導出（小さい）］に当てる。
- **G**：極低 19 の後半（Part 259 の「(iii) を外したとき」が旧版にあるか）も、確認事項 (5) に含める。
- **H**：§13 の後注に「§12 の相互法則との関係（［既知］）は、この規約のもとでの恒等式として残る」を添える。
- **I**：§22 の M4 の式に括弧を足し、「(f^{−s}·τ(χ*)/(√f·L(s+1/2, χ*)))·χ」とする。「/L(…)·χ」は、L·χ で割るとも読めます。

**閉じ方**：中が 1 件あり、主張を変える直しです。停止規則どおりなら、B を直した後にもう 1 回統合照合が要ります。B を構築側が「主張を狭める直し」とみなすかどうかは自己申告になるので、閉じる根拠にはなりません。

---

**使ったツールと読んだ範囲**
- 計 10 回：Read 4（うち 1 回は大きさの上限で失敗）、Bash 6。ウェブ検索は使っていません。
- 依頼文の全文と、入力 `input_XVI.md` の 1〜1143 行を読みました。966〜1007 行（§24、事前登録の本文）は読んでいません。差分のハンクはなく、XV の判定にもかかわらないためです。
- ほかのリポジトリのファイルは読んでいません。
- 計算は /tmp/indep_ledger_XVI/ の中だけで行いました（閉じた記録の機械照合、実の原始指標の数え上げ、S_n の級数の数値）。


## §5 CLAUDE.md（現在の全文）
# Claude への指示 — アーデル射影幾何（PAG）プロジェクト

最初に読む運用の規則（短縮版、2026-11-27）。判断の経緯・根拠・日時の正文は `CLAUDE-history.md`（2026-11-26 時点の全文を一字も変えずに保存）。この短縮版と食い違う箇所を見つけたら、作業を止めて著者に報告する。新しい判断はこのファイルに短く足し、経緯は引き継ぎメモと notes に書く。

**この文書の文面（2026-11-28 09:43、著者の決定）**：CLAUDE.md の混乱を避けるため、これ以降、CLAUDE.md は Claude が生成したものを採用する。Claude は、§1 の著者の定義と著者の選択の記録を書き換えず、構築側の補足とは分けて書く。直したら引き継ぎメモと台帳に記録する。著者はいつでも覆せる。

## 0. 始める前に

1. §1 の定義を読み直す。特に「基礎は離散的であり、連続対象は基礎に存在しない」を確かめる。「解像度」とそれにかかわる命題 3 は構築から外した（2026-11-28 20:02、§1）。定義は書き換えない・広げて解釈しない。
2. §2 の現在地を確かめる（最新の引き継ぎメモと `notes/pag2_tail_ledger.md` も）。
3. 新しい対象は、既存数学への対応づけ（§6 の辞書・盲検の命名テスト）が義務。同時に、対応づけた後に残る問いを幾何・大域・極限の言葉で言えることを、始める条件とする。言えなければ、その対象は局所計算の装置として扱い、主役のパートを始めない。
4. 作業の前に、現状を (a) 形式化済みの内容、(b) 著者の解釈の層（§1）、(c) 未完の大域の問い、に分けて自分の言葉で述べる。混ぜたらやり直す。

この手順の目的は対応づけを避けることではない。防ぐべきは、対応づけた先の有限構造の内部で思考が止まることである。

## 1. 著者の定義（確定事項。再定義・再解釈をしない）

- 目的は「アーデル射影幾何学」の構築（**本来の道**）。アーデル＝イーデルアデールの略で、乗法のイーデルと加法のアデールを含む幾何を指す著者の造語。PAG は Projective Adelic Geometry の略。命名の意味は「アデール幾何とイーデル幾何を射影によって融合する」。
- 点は素数たち＋無限素点。無限素点では無限大と無限小が重なり合う。
  - 「重なり」の読み：**ねじれた貼り合わせ（境界ユニタリ U）**。両端の同一視を群の商として読む読みは A1 と両立しないため採らない（法 9 の 3 次指標が反例）。W による商は A1 とは両立するが採らない（D が商に降りない）。
  - 玩具（`notes/pag2_toy_origin_buildup.md`）の「ねじれて繋がる」は、複素指標の組の回転（A1 の位相 𝔀(χ) による、χ と χ̄ の組を実化した面の回転）と読む。メビウス型の −1 ではない（2026-11-27 08:21、著者の選択）。
  - 玩具で素点どうしの結びつき（交差項）は加法の側に置く（2026-11-27 17:37、著者の選択）。構築側の補足：そのとき加法指標は大域の ψ(·/N)（ℚ の上で自明）で、素数 p_i の点の局所定数は χ_i(N/N_i)·τ(χ_i)/√N_i（PAG261 の形 (I)。τ の割り振りは PAG260 `gaussSum_prodChar`・`stdAddChar_crtMap` から直ちに出る。局所定数との同定は Lean の外。ノート §15・§17）。
  - 玩具 T0 の窓の貼り合わせ（無限素点の対数の格子の上の f(n+M) = U f(n)）は、無限素点に独立に置いた境界条件と読む（2026-11-28 07:13、著者の選択）。構築側の補足：したがって Tate の局所作用素から導いたものではなく、分岐する素数の形（付値の軸の幅 e の平行移動に位相を掛けたもの）の写しとも読まない。境界条件の位相は A1 で 𝔀(χ) と置く入力で、それが局所定数の積に等しいことは Tate の定理（注入→回収。ノート §25〜§27）。
- 基礎は離散的であり、直線のような連続対象は基礎に存在しない。
- **外した（2026-11-28 20:02、著者の決定「外す前提で進めます」）**：「解像度」と、それにかかわる命題 3（次の行の定義文）は、アーデル射影幾何の構築から外す。次の行から「保留」の項までは記録として残し、構築の規則としては使わない（構築側の補足：基礎文書では第 3 章を記録に下げ、第 4 章は解像度の語を使わない形に組み替える）。
- 直線は、解像度を落としたときに創発する有効な姿である。
  - 解像度のパラメータは**未決定**。N、K、Λ のいずれとも同一視しない。
  - 命題 3 の置き方（著者はいつでも覆せる）：定義の文面は変えない。解像度の操作の置き場は「対象の中の移行」ではなく、大域対象への**切り方（見方）の選択**（解釈の層）。素点たちは制限積の因子として最初から並列に共存している全体が対象で、有限レベル商と Λ 切断はその全体への見方の 2 軸。命題 3 の問いは「見方を粗くしたとき直線がどう見えるか」と読む。
  - 著者の定義（原文）：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。」極限は直極限の側（すべての素点を同時に測る側）で取る。完備化（L²、ℝ、直積の位相）を使うときは「解像度が落ちる側の操作と読む」と断る。閉包・完備化に現れる連続体を「有効な姿」や目標として書かない。
  - 読みとして L1（解像度＝測る素点の集合）を採っている（定義の文面ではない）。
  - 「直線の創発」という表現は使わない。命題 3 に触れるときは「§1 の命題 3（解像度と有効な姿）」と参照で書き、何がどう変わるかを数学の言葉で書く。
  - **保留（2026-11-26 20:35、著者の決定）**：「解像度」は保留とし、場合によってはアーデル射影幾何の構築から外す。理由：「解像度」は Muse との会話を始めてから生まれた言葉で、当初の構想にはなかった。上の項目（命題 3 とその読み）は記録として残す。
  - 構築側の補足（2026-11-28、外した後も有効）：完備化（ℚ_p、𝔸_f、L²、ℝ など）を使うときは「計算の道具として使い、有効な姿や目標としては書かない」と断る。閉包・完備化に現れる連続体を目標として書かない。「直線の創発」の語は使わない。
- 「射影」の読み（解釈の層、留保つき）：
  - 舞台は射影直線 P¹（反転が 0 と ∞ を入れ替える。有限レベルは Part 19〜28（PAG23〜PAG32））。その上で働く**貼り合わせの合成**を射影と呼ぶ。主は変換。貼り合わせは U（ねじれた貼り合わせ）を指し、PAG23 の `Compat`（ねじれのない座標の貼り合わせ）ではない。命名の「射影」は舞台と変換の組を指す。
  - 構築側の読み（著者が留保つきで材料に採用）：その合成は反転（乗法の側）と加法の変換（加法の側）の合成で、有限レベルでは Part 252（PAG256）の J∘H_N/√N（`PAG.Part256.JH`）に当たる。ただし `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。照合した範囲（PAG23・PAG26・PAG27・PAG256）では JH と P¹ のモデルを結ぶ Lean の文はない（鎖全体は検索していない）。Part 262（PAG266）で Lean で結んだのは 𝔀 の値と P¹ の係数だけ。
  - 原始指標についての位相が、この合成（変換）の成分である。
  - 標準の核は Part 252 の Hartley 核（形式化の追認。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは未照合）。値は τ(χ)/(i^a√N)（`PAG.Part256.rootNum`、記号 𝔀。PAG256 の docstring と冒頭のコメントの記号 W(χ) もこの値を指し、反転の W とは別）。原始指標ではルート数だが、その同定は Lean の外（明記する）。素朴な核 e(xy) の値 τ(χ)/√N とは奇の指標で i 倍ずれ、このずれを滑らかにしない。
  - 加法指標は**規約 T**（Tate の学位論文：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）を基礎文書の標準とする。規約 T のもとで、イデール類指標を不分岐な q で ω_q(q) = χ(q) と正規化して（χ̄ に対応させる規約では積が共役になる）、原始的な χ について、Hartley 核の因子 ε(χ) = (−i)^a（`PAG.Part256.parFac`）は無限素点の局所定数 ε(1/2, χ_∞, ψ_∞) と、τ(χ)/√N は s = 1/2 での有限素点の局所定数の積と値が一致する（Lean の外、確信度：高。局所定数は Tate 1979 の流儀で定める）。明示的な因子 i^{±a} が無限素点の局所定数であることは規約によらないが、符号 χ(−1) を無限素点と有限素点のどちらに置くかは規約による（逆の規約では無限素点が i^a、有限素点の積が χ(−1)τ(χ)/√N）。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。A1 は公準のまま。規約 T を採る根拠は、Mathlib の `stdAddChar` と有限素点の符号が合い、Burnol（arXiv:math/9811040。根拠はこの 1 本）とも同じ加法指標であること。材料は `notes/pag2_projection_material.md`、規約の文献照合は `notes/pag2_literature_ia_sign.md`。
  - 作用素のレベルでは、U は赤道（単数の上の関数の空間。極限では `Lim`）の上の作用素で、P¹ 全体には自然な条件だけでは一意に延びない（性質として書く。2026-11-26、著者の決定）。
- 以上は解釈の層であり、形式化済みの定理ではない。ノートではその地位を混同して書かない。

## 2. 現在地（2026-11-26）

- **モノグラフ層（1.0）**：イデール類群 C_ℚ 上の作用素系（D、T_p、W、二面体関係）。中心問題 P1 は自己共役拡張の境界条件 U の両立分類（定理 2.6）。定理 2.6 の U の空間は C_ℚ 上の関数（正則表現の側。Λ 切断の留保つき）。**公理 A1** は Tate の γ 因子の貼り合わせの λ = 0 での値の言い換えで、**解釈の層の公準（内容は Tate の定理）のまま**（導出済みと書かない）。
- **PAG 2.0（有限レベル）**：Lean 形式化は Part 262（PAG266）まで（短期層の Part 263・264（PAG267・PAG268）はこの件数の外。索引に記録。2026-11-28 に追記）。定理・補題 3,695 件、xlsx final84（3,722 項目）。件数は宣言総数など別の数え方と混同しない。Part n は PAG(n+4).lean（第 3 期）。
- **本線は基礎文書**（定義層を 1 つの文書にまとめる。草稿 1 が進行中）。新しいパートは始めない。文書の章の不足を埋めるときだけ走らせる。
- 本来の道の未完の問いとしてかつて挙げていたもの（B-3 の続き、構造定理、Ẑ 上の定理 A）は、2026-11-12 の棚卸し監査で既知の定理かその帰結と判定された（`notes/pag2_audit_after_part251.md`）。解像度は §1 のとおり構築から外した（2026-11-28 20:02）。
- 辞書の閾値超え（補足 16）への対応は 2026-11-20 に実施済み（コミット 4357fb4）。
- 収束アラームの兆候 4 は Part 249〜262 で 14 パート連続。残余のある問いは A1 か完備化（無限素点の側）を通るという見立てが、関門の結果と合っている（`notes/pag2_partial_inversion_preregistration.md`）。
- 文献照合：MathSciNet は実施しない（著者の決定）。zbMATH は実施済みで、候補の地位を変える項目はなかった（`notes/pag2_literature_zbmath_20261126.md`）。
- 詳しい経緯（Part 248〜262、方向 α・β・γ、監査、内部重複の監査結果）は `CLAUDE-history.md` §2・§5・§7 と各ノート。

## 3. 結果の地位

- 殻代数 A_N は ℤ/N 上の軌道 Schur 環（cyclotomic S-ring）から来る可換アソシエーションスキームの **Terwilliger 代数 T(0) そのもの**（D_t ＝ 基点 0 の双対冪等元 E*_t、E_t ＝ Bose–Mesner の原始冪等元、A_N = ⟨D_s, E_s⟩ = ⟨M, M*⟩）。辞書は `notes/pag2_terwilliger_dictionary.md`。
- **既知**として扱う（新規と書かない）：素冪の Wedderburn 分解・次元（Part 225–226 ＝ BST 2010、Bastian–Humphries 2026）、テンソル分解（Part 228 ＝ 直積の T(A×B) ≅ T(A)⊗T(B)）、z(χ) の冪根分類（Chowla–Mordell／Odoni／Funakura）、ラマヌジャン和と DFT（古典）、Part 241・242（既知の基本観察／hyper-duality、確信度：中）。
- **新規性の主張は次の候補に限る**（未確定。断定せず、確信度を添える）：
  1. 生成の分類（Part 245–248）。構造定理と、次元公式からの数行の系（⟨M*, E_N⟩ = A_N ⇔ N ∈ {1,4} ∪ 素数）を除き、残るのは項目 66（2 つの双対な代数の和の条件。宣言 `sumSub_eq_shellAlg_iff` は PAG249（Part 245））と項目 67〜69（完全な分類）で、範囲は合成数の N（確信度：中）。評価は「小さいノートの水準」で、新しい現象ではなく「誰も書いていない計算」。外部での新規性の留保は付けない。検索語：Terwilliger algebra, orbit Schur ring, cyclotomic S-ring, dual Bose–Mesner algebra, generated by, generating set。
  3. Part 258（PAG262）の不存在の側［新規候補（小さい）］：N ∣ M で素数 p が N と M/N の両方を割るとき、引き戻しと両立し殻を混ぜない単位的な代数準同型 A_N → A_M はない（確信度：低〜中）。「殻を混ぜない」は強い読み（φ(D_s) は D_t の、φ(E_s) は E_t の線形結合）。弱い読み・非単位的な写像・別の両立条件は、主張の外の別の問いとして残る。存在の側は既知（Hanaki–Kim–Maekawa の直積の定理）。**外部（応募書類を含む）で新規性として使わない**（留保は付いたまま。MathSciNet をやめたので条件は満たされないまま残る）。文献照合の記録は `notes/pag2_candidate3_literature_builder.md`。
  - かつての候補 2（定理 2.6 の提示形）は外れた。組み合わせ（α_{χ̄} = −α_χ とルート数）は既知の結果からの短い帰結（確信度：高）。この組み合わせを書いた文献は見つからなかった（確信度：中）が、新規性の根拠にならない（確信度：中〜高）。ルート数が条件を満たすことは整合性の確認で、A1 の導出ではない。反転の条件は境界ユニタリの実性と同値（CW が境界条件を保つ。手計算と数値）。Lean では PAG16・PAG173・PAG198 の 3 定理から出るが、組み合わせた 1 つの文は未形式化。近い先行は Burnol、Ibort–Lledó–Pérez-Pardo の例 7.1・7.2。
- §3 の書き換えは著者の承認の後に行う（2026-11-28 以降は、冒頭の「この文書の文面」の決定により Claude の判断で行い、記録する）。
- 構造が必要なら、再証明せず辞書経由で文献を引く。

**Part 250〜262 の地位（基礎文書に書くときの注意。詳細は索引と各ノート）**
- Part 250：示せたのは「ℝ の中に基礎が、全不連結だがどの尺度でも鎖でつながる稠密な部分集合として入っている」こと（教科書的な例の対数座標版）。新規候補なし。「解像度を落とすと直線が現れる」は示せていない（商を取ると 1 点につぶれ、ℝ は完備化（ε → 0 の側）から現れるうえ、ℝ は定義に最初から使われている）。
- Part 251：「イデール類群で稠密」は構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0} の同一視のもとでの読み（Lean にしていないもの：unitSys ≅ Ẑ^×、極限の普遍性・コンパクト性・位相群性、構造定理）。
- Part 252〜254 の U_N は A1 の位相を定義として入れた作用素で、A1 は導かれていない。
- Part 259：(iii) を外したときの奇数の場合の一意性は数値のみ。代数構造と制限テンソル積との同型は Lean の外。添字の順序は有向でない。
- Part 260：`DirectedSystem` としての束ねと極限、像が角全体であること（見込み）、群環の側で Bost–Connes の ρ と一致すること（数値）は Lean の外。D 側が殻の span に入らないことは (2,4) の証人のほかは数値。対照群は ℤ/p^e の段に当たる場合だけ試した。第 5 章の留保「代数版にはならない」は単位元を保つ写像についての文と読み直す（索引 5.5）。
- Part 261：局所的な単位元の文は一般論で、非単位的という内容を運ぶのは左単位元がないことだけ。
- Part 262：「符号つきの形は Long–Pigno–Pinner の式 (10)」という帰属は誤り（その式は符号のない比）。符号つきの形を書いた文献は見つかっていない。
- 2026-11-12 の再監査で弱めた結論：文献で照合したのは 14 件中 4 件。「問いは残らない」は「照合した範囲では見つかっていない」（確信度：中以下）。
- 方向 β：単位元を保つ写像の帰納極限として立てる道は閉じた（Part 258。弱い読み・非単位的な写像・別の両立条件は答えの外。互いに素な段だけの系は別）。
- 事前登録の残候補 K2〜K4 は、残余が計算だけか空であり、短期層の在庫として保持する。

## 4. 作業の進め方

- パートのサイクル：Python で数値照合 → Lean（sorry 0・警告 0）→ `#print axioms` → ノート＋xlsx。ノートの題名は「アーデル射影幾何」（旧称「アデール射影幾何 2.0」は使わない）。
- 新しいパートの基準：幾何・大域・極限の言葉の問いに答えるか。代数内部の問い（中心の記述、生成元を足した代数の分類など）は主役にしない。有限レベルの代数は局所計算の装置として使う側に回す。冒頭に、本来の道（§1）のどの問いに仕えるかを書く（書けなければ始めない）。
- **着手前の 4 点**（Lean の前に書き、推薦案として 1 つに絞ったものだけ始める）：(1) 問いを幾何の言葉（点・無限素点・貼り合わせ・大域・極限）で書く（2026-11-28 に「解像度・創発」を外した）、(2) 既存分野の言葉への最善の翻訳（写像は義務）、(3) 翻訳しても消えない残余を明示（空なら始めない。計算の細部だけなら短期層の小さいノート）、(4) 残余の文に対照群テストをかけ、結果を併記する。加えて、盲検の問いテストと内部照合（§6）。
- **選択の委任**：構築側は関門（4 点・盲検の問いテスト・対照群テスト）を通した推薦案を 1 つに絞って出し、着手は著者側 Muse の決定による。何を選び、なぜかを記録する。著者はいつでも覆せる。
- 判断の経路は 1 つ：このファイルと著者側の申し送りを唯一の記録とする。構築側のセッションで著者が選んだことは、引き継ぎメモに残して著者側へ戻す。
- パート番号は「Part n（PAGm）」と併記する。

## 5. してはいけないこと

- 既知の結果（§3）を新規と書くこと。新規性の主張は §3 の候補に限り、確信度を添える。
- 著者の定義（§1）を形式化済みのように書くこと。解釈の層だからといって定義を勝手に直すこと。
- A1 を「導かれた」と書くこと。
- 数値確認を証明と書くこと。

## 6. 失敗の検知（収束アラームと照合）

収束は結果ではなく兆候で検出する。

**兆候（出たら報告）**
1. 標準的な定義で作れる対象に自前の名前を付けている（普遍性・双対性・生成・中心・可換子などで定義される対象は、ほぼ確実に文献名を持つ）→ 構造定理を証明し始める前に文献名の候補を検索し、候補と検索範囲を報告する。
2. 問いが「構造・分類・次元」型で 3 パート続いた → 監査を提案する。
3. 文献照合の実施記録がないパートが 10 連続 → 黄色信号として報告する。
4. 初等的な部品の組み合わせだけで進み続ける → 既知の領域を歩いている兆候として扱う。

**常時の仕組み**
- 辞書（自前の用語 → 文献の用語）を生きた文書として維持する。右列が空の行が 5 件たまったら、新規パートを始めず、まず右列を埋める調査を提案する。
- 盲検の命名テスト：自前の名前を中立な記号に置き換えた定義だけを、文脈を共有しない新しいエージェントに渡し、文献名の候補を挙げさせる。返った候補は実在の文献で照合してから辞書に記録する。
- 盲検の問いテスト：新しい問いの前に、その定義と文だけを同様に渡し、「既存の結果か。どの文献が答えを持っているか」を聞く。返った答えは着手前の 4 点（残余の明示）に反映する。
- パートを閉じる条件：主要結果すべてに［既知／再導出／新規候補］のラベル。新規候補には検索ログ（語・先・範囲）と「見つからなかったは不存在の証明ではない」を添える。
- 言い直しテスト（10〜20 パートごと）：既存分野の言葉だけで言い直させる。成功したら著者に報告する。言い直せることは「新しい概念が要らなかった」ことだけを示し、「新しい内容がない」証拠にはしない。このテスト単独の弁別力は弱い。
- 対照群テスト：算術的・大域的な内容の文は、関数体 F_q(t)（ノルムの像は q^ℤ で、連続な直線は出ない）と Beurling の一般化素数でも成り立つか確かめる。言い直しテストに併せて行う。成り立つ文は ℚ に固有の算術ではなく形式と稠密性だけの文として扱う。とくに、素数の対数の稠密性だけで成り立つ文には算術の内容がないものとして扱う。
- パートごとに、辞書の未記入件数と文献照合の未実施の連続数を報告する。閾値を超えたら、新規パートの開始ではなく監査を提案する。

**円環（第 2 の型）**：目標の量（またはそれと等しい情報）を公理・重み・位相として入れて読み替える（注入→回収）、目標と同値な条件を前進と見る（同値性の循環）、構成から自明な形の一致。成果を出す前に：
1. 依存表：主張ごとに入力（公理、注入した重み・位相、借りた定理）を列挙する。目標の量そのもの、またはそれと等価な情報が入力側にあれば円環として報告する。
2. 除去テスト：疑わしい入力を 1 つ外して結論が残るか確かめる。消えるなら「導いた」ではなく「入れて読み替えた」と書く（例：A1 を外すと位相は自由に戻る）。
3. 同値性と情報量：課した条件が目標と同値でないか確かめる。対応を主張するなら情報量（数え上げの増え方など）を比べ、桁が合わなければ対応を主張しない。

**その他の型**（第 1 の型だけが文献照合を要し、以下は内部の照合で検知できる。詳細は著者側の `failure-patterns-audit.md`。リポジトリにはない）：
- 第 3：主張の格上げ。散文の最上級・必然・同型・生成の語は、対応する定理の形式文と突き合わせる。形式文が書けない主張は格下げするか［観察］に置く。訂正表は各パートの定例とする。題と主張文は Lean の形式文が確定した後に、形式文から起こして書く。
- 第 4：問いの誤設定。先に障害量（欠損指数、不変量、次元の数え上げ）を計算し、反対方向（反例・非一意性）を 1 回検討する。
- 第 5：境界ケース。数値に退化ケース（r = 0、p = 2、最小の法、空和、自明指標）を必ず入れる。
- 第 6：素朴な一般化。証明の前に反例探索。照合表に「反例」の列を常設し、「常に」「必ず」の語が出たら探索範囲を広げる。
- 第 7：数値ノイズ。反例と言う前に誤差の出所（条件数、桁落ち、打ち切り）を見積もり、別法で確かめる。「反例ではない」と判定した場合も根拠を残す。
- 第 8：規約の人工物。主張を提示する前に、正規化・規約を変えても主張が残るか確かめる。規約を変えて消える「現象」は現象として報告しない。
- 第 9：工程のドリフト。ファイルの版と番号対応を確かめる（設計番号と Lean 番号のずれ、草稿と完成版の併存。正本は LEAN.zip 側、対応は著者側の `archive-catalog.md`）。
- 第 10：創発の修辞。「現れた・生成した・繋がった」には、新規なのはどの定理のどの項かを必ず添える。書けなければ［観察］。問いの側でも創発を先取りしない。
- 第 11：形式文のずれ。主定理ごとに、ノート作成前に、非空虚性の証人の構成、仮定を 1 つずつ外した文での小さいパラメータの反例探索、ノートを見せない別のエージェントによる形式文と定義だけからの逆翻訳と主張との照合、を行う。
- 第 12：内部の重複。着手前と閉鎖前に、自分の鎖全体（PAG.lean・PAG2〜6 を含む）の機械的な重複照合（`records/audit_internal/`）と、使う対象・構成の名前による言葉の検索（Mathlib を含む）を行う。機械的な照合は「型の違う同じ構成」を拾えない。新しい定義の前に同じ式の定義を探す。重複は「同じ文（A）／直ちに出る（B）／近い（C）」で書き分け、C の判定を確定した事実のように書かない。「見つからなかった」を「重複はない」と書かない。

**照合の手続き**
- 中身・主張・新規性の検知（第 1・2・3・10・11 の型）は、構築と同じ文脈で自己監査せず、検査対象だけを渡した新しいエージェントで行う。定例の照合はパートを閉じる際に行う。渡すのは形式文の全文と定義だけで、散文と他の照合者の出力の要約は渡さない。依頼文は定型文。検査側には判定ではなく成果物（証人・反例・逆翻訳の文）を出させる。依頼文の全文と所要時間を記録する。
- 新規候補を主張するパートと主定理級の主張があるパートは、著者側の別チャット（Muse）でも二重に照合する。
- 照合で文面を直すときは、ノート・表・Lean の docstring と冒頭説明のすべてに同じ直しを入れ、照合までを 1 組とする。照合の後に直した文面・追加した項目は、閉じる前に再照合する（止め方は下の停止規則）。
- 照合の後の直しは、主張を変えない直しでも、その直しを入力に含む照合を受けるまで台帳（`notes/pag2_tail_ledger.md`）に残す。台帳の閉鎖は、直しを入力に含んだ照合に基づいてだけ宣言し、「主張を足していない」という自己申告を根拠にしない。
- **停止規則**：最後の照合の指摘が低・極低だけで、主張を強める文の追加と、著者の判断の記録の書き換えがどちらもなければ、残りの直しは次のパートの統合照合に載せて閉じてよい。主張を変える直しがあれば、もう 1 回だけ統合照合を行い、その後はこの規則で閉じる。判断の記録は書き換えず、根拠の内訳は後注として足す。
- 既知の対象との一致・目標の情報の注入・形式文の自明化の兆候を見つけたら、定義と A1 は変えず「指摘」として著者に報告する。

## 7. 参照

- `CLAUDE-history.md`：2026-11-26 時点の全文（判断の経緯・根拠の正文）。英語版は `CLAUDE.en.md`（短縮版の訳）と `CLAUDE-history.en.md`（旧英訳の全文）
- `notes/pag2_founding_material_index.md`：基礎文書の索引
- `notes/pag2_terwilliger_dictionary.md`：辞書
- `notes/pag2_tail_ledger.md`：照合の尾の台帳
- `notes/pag2_projection_material.md`：「射影」の材料
- `notes/pag2_candidate3_literature_builder.md`：候補 3 の文献照合
- `notes/pag2_audit_after_part251.md`：残る問いの棚卸し監査
- `notes/pag2_beta_registration_check.md`・`notes/pag2_gamma_corner_preregistration.md`：方向 β・γ の記録
- `handoff/`：引き継ぎメモ（最新は Part 259 の後。それ以降の経緯は notes とコミットの記録）
- `records/audit_internal/`：内部照合の道具
- `records/claude_md_slim_check/`：短縮版の網羅性の照合（依頼文・出力・直し）
- 著者側にあってリポジトリにないもの：`failure-patterns-audit.md`（失敗の型の監査）、`novelty-audit.md`（新規性の精査）、`archive-catalog.md`（アーカイブの目録とパート対応表）、`what-is-aadel-projective-geometry.md`、`strategy-nonconvergence.md`、`emergence-next-directions.md`、`preregistration-delta-first-consequence.md`、`founding-document-outline-20261115.md`、`remaining-questions-inventory.md`
