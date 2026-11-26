# Instructions for Claude — Ardel Projective Geometry (PAG) Project

> **About this translation**
> This is an English translation of [`CLAUDE.md`](CLAUDE.md) (Japanese, short version of 2026-11-27). The Japanese original is authoritative; if the two differ, follow the Japanese. This translation is for reference by readers and is not itself the instruction file. The full text of the previous English translation is preserved in [`CLAUDE-history.en.md`](CLAUDE-history.en.md).

The operating rules to read first (short version, 2026-11-27). The authoritative record of the history, rationale and timing of decisions is `CLAUDE-history.md` (the full text as of 2026-11-26, preserved without changing a character). If you find a point where this short version disagrees with it, stop and report to the author. New decisions are added to this file briefly; history goes into handoff memos and notes.

## 0. Before starting

1. Reread the definitions in §1. In particular confirm "the foundation is discrete; continuous objects do not exist in the foundation" and "the parameter that sets the resolution is undecided (do not identify it with N, K, Λ)." Do not rewrite the definitions or interpret them more broadly.
2. Check the current position in §2 (and the latest handoff memo and `notes/pag2_tail_ledger.md`).
3. For a new object, mapping it to existing mathematics (the dictionary and the blind naming test of §6) is an obligation. Being able to state the question left after the mapping in the language of geometry, the global, or limits is at the same time a condition for starting. If it cannot be stated, treat the object as a device for local computation and do not start a part with it as the main subject.
4. Before working, state the current position in your own words, split into (a) formalized content, (b) the author's interpretive layer (§1), and (c) open global questions. If you mix them, start over.

The purpose of these steps is not to avoid mapping. What is to be prevented is thinking that stops inside the finite structure one has mapped to.

## 1. The author's definitions (settled; do not redefine or reinterpret)

- The aim is to build "Ardel projective geometry" (**the original path**). Ardel is short for idele-adele, the author's coinage for a geometry containing the multiplicative ideles and the additive adeles. PAG stands for Projective Adelic Geometry. The name means "fusing adelic geometry and idelic geometry by projection."
- The points are the primes plus the infinite place. At the infinite place, the infinitely large and the infinitely small overlap.
  - Reading of the "overlap": a **twisted gluing (boundary unitary U)**. The reading of the identification of the two ends as a group quotient is not adopted because it is incompatible with A1 (a cubic character mod 9 is a counterexample). A quotient by W is compatible with A1 but is not adopted either (D does not descend to the quotient).
- The foundation is discrete; continuous objects such as the line do not exist in the foundation.
- The line is the effective form that emerges when the resolution is lowered.
  - The resolution parameter is **undecided**. Do not identify it with N, K, or Λ.
  - Placement of proposition 3 (the author can override at any time): the wording of the definition is not changed. The place of the resolution operation is not "a transition inside the object" but **the choice of a way of cutting (viewing)** the global object (interpretive layer). The object is the whole in which the places coexist in parallel from the start as factors of the restricted product; finite-level quotients and the Λ-cutoff are two axes of viewing that whole. The question of proposition 3 is read as "how the line looks when the view is coarsened."
  - The author's definition (original wording, translated): "Slipping into the continuum by escaping into completion (the limit) is what I call the resolution falling. I do not want the continuum to be observed; even in the limit, the observation of discrete structure is maintained." The limit is taken on the direct-limit side (the side that measures all places at once). When using completion (L², ℝ, the product topology), say that it is "read as an operation on the side where the resolution falls." Do not write a continuum appearing in a closure or completion as the "effective form" or as a goal.
  - The reading L1 (resolution = the set of places measured) is adopted (as a reading, not the wording of the definition).
  - Do not use the expression "emergence of the line" (直線の創発). When referring to proposition 3, write it by reference as "proposition 3 of §1 (resolution and effective form)," and write in mathematical language what changes and how.
  - **On hold (2026-11-26 20:35, the author's decision)**: "resolution" is on hold, and may be removed from the construction of Ardel projective geometry. Reason: the word "resolution" arose after the conversations with Muse began and was not in the original conception. The items above (proposition 3 and its readings) are kept as a record.
- Reading of "projective" (interpretive layer, with reservations):
  - The stage is the projective line P¹ (the inversion swaps 0 and ∞; at the finite level, Parts 19–28 (PAG23–PAG32)). The **composition of gluings** acting on it is what is called projection. The transformation is primary. The gluing means U (the twisted gluing), not `Compat` of PAG23 (an untwisted gluing of coordinates). The "projective" of the name refers to the pair of stage and transformation.
  - The builder side's reading (adopted by the author as material, with reservations): that composition is the composition of the inversion (multiplicative side) and the additive transform (additive side), and at the finite level corresponds to J∘H_N/√N of Part 252 (PAG256) (`PAG.Part256.JH`). However, `JH` is a map sending functions on ℤ/N to functions on the units, not an operator on P¹. In the range checked (PAG23, PAG26, PAG27, PAG256) there is no Lean statement connecting JH with the model of P¹ (the whole chain was not searched). What Part 262 (PAG266) connected in Lean is only the value of 𝔀 and the coefficients on P¹.
  - The phase for primitive characters is a component of this composition (transformation).
  - The standard kernel is the Hartley kernel of Part 252 (ratification of the formalization; that it aligns with the content of A1 is the author's judgment, based on a reading of the header comment of PAG256, not checked against the monograph text). Its value is τ(χ)/(i^a√N) (`PAG.Part256.rootNum`, symbol 𝔀; the symbol W(χ) in the docstring and header comment of PAG256 denotes this value too, and is distinct from the inversion W). For primitive characters it is the root number, but that identification is outside Lean (say so explicitly). It differs from the value τ(χ)/√N of the naive kernel e(xy) by a factor i for odd characters; do not smooth over this discrepancy.
  - The additive characters follow **convention T** (Tate's thesis: ψ_∞(x) = e^{−2πix}, ψ_p(x) = e^{+2πi{x}_p}) as the standard of the founding document. Under convention T, normalizing the idele class character at unramified q by ω_q(q) = χ(q) (under the convention matching χ̄ the product is conjugated), for primitive χ the factor ε(χ) = (−i)^a of the Hartley kernel (`PAG.Part256.parFac`) agrees in value with the local constant ε(1/2, χ_∞, ψ_∞) at the infinite place, and τ(χ)/√N with the product of the local constants at the finite places at s = 1/2 (outside Lean; confidence: high; local constants defined in the manner of Tate 1979). That the explicit factor i^{±a} is the local constant at the infinite place is convention-independent, but whether the sign χ(−1) is placed at the infinite place or the finite places depends on the convention (under the opposite convention the infinite place gives i^a and the product over finite places χ(−1)τ(χ)/√N). Do not write "ε(χ) comes from the infinite place" without stating convention T. A1 remains a postulate. The grounds for adopting convention T: the signs at the finite places match Mathlib's `stdAddChar`, and the additive character is the same as in Burnol (arXiv:math/9811040). Material: `notes/pag2_projection_material.md`; literature check of the convention: `notes/pag2_literature_ia_sign.md`.
  - At the level of operators, U is an operator on the equator (the space of functions on the units; `Lim` in the limit), and it does not extend uniquely to all of P¹ under natural conditions alone (to be written as a property; 2026-11-26, the author's decision).
- All of the above is the interpretive layer, not formalized theorems. In notes, do not confuse their status.

## 2. Current position (2026-11-26)

- **Monograph layer (1.0)**: the operator system (D, T_p, W, dihedral relations) on the idele class group C_ℚ. The central problem P1 is the compatibility classification of the boundary condition U of self-adjoint extensions (Theorem 2.6). The space of U in Theorem 2.6 is functions on C_ℚ (the regular-representation side, with the Λ-cutoff reservation). **Axiom A1** is a restatement of the value at λ = 0 of the gluing of Tate's γ-factors, and **remains a postulate of the interpretive layer (its content is Tate's theorem)** (do not write that it has been derived).
- **PAG 2.0 (finite level)**: the Lean formalization goes up to Part 262 (PAG266). 3,695 theorems and lemmas; xlsx final84 (3,722 items). Do not confuse these counts with other counts such as total declarations. Part n is PAG(n+4).lean (third period).
- **The main line is the founding document** (collecting the definitional layer into one document; draft 1 in progress). No new parts are started. Parts run only to fill gaps in the document's chapters.
- The open questions of the original path once listed (continuation of B-3, structure theorems, theorem A over Ẑ) were judged in the inventory audit of 2026-11-12 to be known theorems or their consequences (`notes/pag2_audit_after_part251.md`). The formulation of resolution is on hold as in §1.
- The response to the dictionary threshold being exceeded (supplement 16) was done on 2026-11-20 (commit 4357fb4).
- Sign 4 of the convergence alarm has continued for 14 parts (Parts 249–262). The assessment that residue-bearing questions pass through A1 or completion (the side of the infinite place) agrees with the results of the gates (`notes/pag2_partial_inversion_preregistration.md`).
- Literature checks: MathSciNet will not be used (the author's decision). zbMATH has been done, with no item changing the status of the candidates (`notes/pag2_literature_zbmath_20261126.md`).
- The detailed history (Parts 248–262, directions α, β, γ, audits, results of the internal-duplication audit) is in `CLAUDE-history.md` §2, §5 and §7 and in the notes.

## 3. Status of results

- The shell algebra A_N is **exactly the Terwilliger algebra T(0)** of the commutative association scheme coming from the orbit Schur ring (cyclotomic S-ring) on ℤ/N (D_t = dual idempotent E*_t with base point 0, E_t = primitive idempotent of the Bose–Mesner algebra, A_N = ⟨D_s, E_s⟩ = ⟨M, M*⟩). Dictionary: `notes/pag2_terwilliger_dictionary.md`.
- Treat as **known** (do not write as new): the Wedderburn decomposition and dimension for prime powers (Parts 225–226 = BST 2010, Bastian–Humphries 2026), the tensor decomposition (Part 228 = T(A×B) ≅ T(A)⊗T(B) for direct products), the classification of z(χ) as roots of unity (Chowla–Mordell / Odoni / Funakura), Ramanujan sums and the DFT (classical), Parts 241 and 242 (known basic observations / hyper-duality; confidence: medium).
- **Claims of novelty are limited to the following candidates** (unsettled; do not assert; state confidence):
  1. The generation classification (Parts 245–248). Excluding the structure theorem and the few-line corollary of the dimension formula (⟨M*, E_N⟩ = A_N ⇔ N ∈ {1,4} ∪ primes), what remains is item 66 (the condition for the sum of two dual algebras; the declaration `sumSub_eq_shellAlg_iff` is in PAG249 (Part 245)) and items 67–69 (the complete classification), for composite N (confidence: medium). Assessed as "at the level of a small note": not a new phenomenon but "a computation nobody has written down." No reservation on external use as novel. Search terms: Terwilliger algebra, orbit Schur ring, cyclotomic S-ring, dual Bose–Mesner algebra, generated by, generating set.
  3. The non-existence side of Part 258 (PAG262) [novelty candidate (small)]: when N ∣ M and a prime p divides both N and M/N, there is no unital algebra homomorphism A_N → A_M that is compatible with pullback and does not mix shells (confidence: low–medium). "Does not mix shells" is the strong reading (φ(D_s) is a linear combination of the D_t, φ(E_s) of the E_t). The weak reading, non-unital maps, and other compatibility conditions remain as separate questions outside the claim. The existence side is known (the direct-product theorem of Hanaki–Kim–Maekawa). **Do not use it externally (including in applications) as novel** (the reservation remains; since MathSciNet was dropped, the condition remains unmet). Literature check record: `notes/pag2_candidate3_literature_builder.md`.
  - The former candidate 2 (the presentation of Theorem 2.6) dropped out. The combination (α_{χ̄} = −α_χ and root numbers) is a short consequence of known results (confidence: high). No literature writing this combination was found (confidence: medium), but that is no ground for novelty (confidence: medium–high). That root numbers satisfy the condition is a consistency check, not a derivation of A1. The inversion condition is equivalent to reality of the boundary unitary (CW preserves the boundary condition; by hand and numerically). In Lean it follows from three theorems of PAG16, PAG173 and PAG198, but a single combined statement is not formalized. Close precedents: Burnol; Ibort–Lledó–Pérez-Pardo, examples 7.1 and 7.2.
- §3 is rewritten only after the author's approval.
- If structure is needed, cite the literature through the dictionary instead of re-proving it.

**Status of Parts 250–262 (cautions when writing the founding document; details in the index and the notes)**
- Part 250: what was shown is that "the foundation sits inside ℝ as a dense subset that is totally disconnected but chain-connected at every scale" (the log-coordinate version of a textbook example). No novelty candidate. "The line appears when the resolution is lowered" was not shown (taking the quotient collapses to one point, ℝ appears from the side of completion, and ℝ is used in the definition from the start).
- Part 251: "dense in the idele class group" is a reading under the identification by the structure theorem C_ℚ ≅ Ẑ^× × ℝ_{>0} (not in Lean: unitSys ≅ Ẑ^×, universality, compactness and topological-group property of the limit, the structure theorem).
- The U_N of Parts 252–254 are operators with the phases of A1 put in as a definition; A1 is not derived.
- Part 259: uniqueness in the odd case with (iii) removed is numerical only. The algebra structure and the isomorphism with the restricted tensor product are outside Lean. The index order is not directed.
- Part 260: the bundling as a `DirectedSystem` and its limit, that the image is the whole corner (expected), and agreement with the Bost–Connes ρ on the group-ring side (numerical) are outside Lean. That the D side does not lie in the span of shells is numerical apart from the (2,4) witness. The control group was tried only where it corresponds to the stages ℤ/p^e. The reservation of chapter 5, "it does not become an algebra version," is reread as a statement about unit-preserving maps (index 5.5).
- Part 261: the statement on local units is general theory; what carries the non-unital content is only the absence of a left unit.
- Part 262: the attribution "the signed form is equation (10) of Long–Pigno–Pinner" was wrong (that equation is an unsigned ratio). No literature writing the signed form has been found.
- Conclusions weakened in the re-audit of 2026-11-12: literature was checked for 4 of 14 items. "No question remains" means "not found in the range checked" (confidence: medium or lower).
- Direction β: the route of setting it up as an inductive limit of unit-preserving maps is closed (Part 258; the weak reading, non-unital maps, and other compatibility conditions are outside the answer; systems of coprime stages only are separate).
- The remaining preregistered candidates K2–K4 have residue that is only computational or empty, and are kept as short-term-layer stock.

## 4. How to proceed

- The cycle of a part: numerical check in Python → Lean (0 sorry, 0 warnings) → `#print axioms` → note + xlsx. Note titles use "アーデル射影幾何" (Ardel projective geometry) (the old name "アデール射影幾何 2.0" is not used).
- Criterion for a new part: does it answer a question in the language of geometry, the global, or limits? Questions internal to the algebra (describing the center, classifying algebras with added generators, etc.) are not made the main subject. Finite-level algebras are used as devices for local computation. State at the top which question of the original path (§1) it serves (if you cannot, do not start).
- **The four points before starting** (written before Lean; only what has been narrowed to one recommendation is started): (1) write the question in geometric language (points, infinite place, resolution, emergence), (2) the best translation into the language of existing fields (the mapping is obligatory), (3) state the residue that does not vanish under translation (if empty, do not start; if only computational details, a short-term small note), (4) apply a control-group test to the statement of the residue and record the result alongside. In addition, the blind question test and the internal check (§6).
- **Delegated selection**: the builder side narrows to one recommendation that has passed the gates (four points, blind question test, control-group test), and the start is decided by the author-side Muse. Record what was chosen and why. The author can override at any time.
- A single path for decisions: this file and the author side's handovers are the only record. Anything the author chose in a builder-side session is recorded in the handoff memo and returned to the author side.
- Write part numbers as "Part n (PAGm)."

## 5. Do not

- Write known results (§3) as new. Claims of novelty are limited to the candidates of §3, with confidence attached.
- Write the author's definitions (§1) as if formalized. Change the definitions at will because they are an interpretive layer.
- Write that A1 was "derived."
- Write a numerical check as a proof.

## 6. Detecting failures (convergence alarm and checks)

Convergence is detected by signs, not by results.

**Signs (report when they appear)**
1. An object definable by a standard definition is given a home-made name (objects defined by universality, duality, generation, center, commutant, etc. almost certainly have literature names) → before starting to prove structure theorems, search for candidate literature names and report the candidates and the search scope.
2. Questions of the "structure, classification, dimension" type for 3 consecutive parts → propose an audit.
3. 10 consecutive parts without a record of a literature check → report as a yellow flag.
4. Progress continues only by combining elementary parts → treat as a sign of walking in known territory.

**Standing mechanisms**
- Maintain the dictionary (home-made term → literature term) as a living document. When 5 rows with an empty right column accumulate, do not start a new part; first propose an investigation to fill the right column.
- Blind naming test: give only the definitions with home-made names replaced by neutral symbols to a new agent sharing no context, and have it list candidate literature names. Check the returned candidates against actual literature before recording them in the dictionary.
- Blind question test: before a new question, give only its definitions and statement in the same way and ask "Is this an existing result? Which literature has the answer?" Reflect the answer in the four points before starting (the statement of residue).
- Conditions for closing a part: a [known / re-derivation / novelty candidate] label on every main result. Novelty candidates carry a search log (terms, sources, scope) and the note that "not found is not a proof of non-existence."
- Restatement test (every 10–20 parts): have the results restated in the language of existing fields only. If it succeeds, report to the author. Being restatable shows only that "no new concept was needed"; do not treat it as evidence that "there is no new content." The discriminating power of this test alone is weak.
- Control-group test: for statements with arithmetic or global content, check whether they also hold for the function field F_q(t) (the image of the norm is q^ℤ, and no continuous line appears) and for Beurling generalized primes. Done together with the restatement test. Statements that do hold are treated not as arithmetic specific to ℚ but as using only form and density. In particular, statements that hold by the density of the logarithms of primes alone are treated as having no arithmetic content.
- Report, per part, the number of unfilled dictionary rows and the consecutive count of parts without a literature check. When a threshold is exceeded, propose an audit rather than starting a new part.

**Circle (type 2)**: injecting the target quantity (or information equal to it) as an axiom, weight or phase and reading it back (injection → recovery); treating a condition equivalent to the target as progress (circularity by equivalence); a match of form that is trivial from the construction. Before presenting a result:
1. Dependency table: for each claim, list the inputs (axioms, injected weights and phases, borrowed theorems). If the target quantity itself, or equivalent information, is on the input side, report it as a circle.
2. Removal test: remove one suspicious input and see whether the conclusion remains. If it disappears, write "put in and read back," not "derived" (e.g., removing A1 frees the phases again).
3. Equivalence and information content: check that the imposed condition is not equivalent to the target. If claiming a correspondence, compare information content (growth of counts, etc.); if the orders of magnitude do not match, do not claim the correspondence.

**Other types** (only type 1 requires a literature check; the following can be detected by internal checks. Details in the author side's `failure-patterns-audit.md`; not in the repository):
- Type 3: inflation of claims. Words in prose such as superlatives, "necessarily," "isomorphic," "generated" are matched against the formal statement of the corresponding theorem. A claim for which no formal statement can be written is downgraded or placed as [observation]. A correction table is routine for every part. Write titles and statements from the formal statements, after the Lean formal statements are settled.
- Type 4: mis-set questions. Compute the obstruction quantities (deficiency indices, invariants, dimension counts) first, and consider the opposite direction (counterexample, non-uniqueness) once.
- Type 5: boundary cases. Numerics must include degenerate cases (r = 0, p = 2, the smallest modulus, empty sums, trivial characters).
- Type 6: naive generalization. Search for counterexamples before proving. Keep a standing "counterexample" column in the check table, and widen the search when the words "always" or "necessarily" appear.
- Type 7: numerical noise. Before calling something a counterexample, estimate the error sources (condition number, cancellation, truncation) and confirm by another method. When judging "not a counterexample," also keep the grounds.
- Type 8: artifacts of convention. Before presenting a claim, check that it survives changing normalizations and conventions. Do not report a "phenomenon" that disappears when conventions change as a phenomenon.
- Type 9: process drift. Check file versions and number correspondences (gaps between design numbers and Lean numbers, drafts coexisting with final versions; the master is the LEAN.zip side; correspondences in the author side's `archive-catalog.md`).
- Type 10: rhetoric of emergence. "Appeared, generated, connected" must always come with which term of which theorem is new. If you cannot say, mark it [observation]. Do not presuppose emergence on the side of the question either.
- Type 11: drift of formal statements. For each main theorem, before writing the note: construct a witness of non-vacuity, search small parameters for counterexamples to the statement with one hypothesis removed at a time, and have another agent that is not shown the note back-translate from the formal statement and definitions alone and compare with the claim.
- Type 12: internal duplication. Before starting and before closing, run a mechanical duplicate check over the whole chain (including PAG.lean and PAG2–6) (`records/audit_internal/`) and a word search by the names of the objects and constructions used (including Mathlib). The mechanical check cannot catch "the same construction with a different type." Before a new definition, look for a definition with the same formula. Distinguish duplicates as "same statement (A) / follows immediately (B) / close (C)," do not write a C judgment as an established fact, and do not write "not found" as "no duplicate."

**Check procedure**
- Detection concerning content, claims or novelty (types 1, 2, 3, 10, 11) is not self-audited in the same context as the construction; it is done by a new agent given only the object of the check. The routine check is done when closing a part. Give it only the full formal statements and the definitions, not prose and not summaries of other checkers' outputs. Use a standard request text. Have the checker produce artifacts (witnesses, counterexamples, back-translations) rather than verdicts. Record the full request text and the time taken.
- Parts that claim a novelty candidate and parts with main-theorem-level claims are also checked a second time in a separate author-side chat (Muse).
- When fixing wording in a check, make the same fix in all wording (notes, tables, Lean docstrings and header explanations), and treat everything up to the check as one set. Wording fixed and items added after a check are re-checked before closing (see the stop rule below for when to stop).
- Fixes made after a check, even fixes that do not change claims, stay in the ledger (`notes/pag2_tail_ledger.md`) until they have undergone a check that includes the fixes themselves as input. Declare the ledger closed only on the basis of a check that included the fixes as input, never on the self-report "no claim was added."
- **Stop rule**: if the last check returned only low / very-low findings, and there is neither an added sentence that strengthens a claim nor a rewrite of a record of the author's judgment, the remaining fixes may be carried to the integrated check of the next part and the round closed. If there is a fix that changes a claim, do one more integrated check only, and then close by this rule. Do not rewrite records of judgments; add the breakdown of grounds as a postscript.
- If you find signs of agreement with a known object, injection of target information, or trivialization of a formal statement, do not change the definitions or A1; report them to the author as "findings."

## 7. References

- `CLAUDE-history.md`: the full text as of 2026-11-26 (authoritative record of the history and rationale of decisions); English: `CLAUDE-history.en.md`
- `notes/pag2_founding_material_index.md`: index of the founding document
- `notes/pag2_terwilliger_dictionary.md`: dictionary
- `notes/pag2_tail_ledger.md`: ledger of check tails
- `notes/pag2_projection_material.md`: material on "projective"
- `notes/pag2_candidate3_literature_builder.md`: literature check for candidate 3
- `notes/pag2_audit_after_part251.md`: inventory audit of remaining questions
- `notes/pag2_beta_registration_check.md`, `notes/pag2_gamma_corner_preregistration.md`: records of directions β and γ
- `handoff/`: handoff memos (the latest is after Part 259; later history is in the notes and the commit record)
- `records/audit_internal/`: tools for the internal check
- `records/claude_md_slim_check/`: coverage check of the short version (request, output, fixes)
- On the author side and not in the repository: `failure-patterns-audit.md` (audit of failure types), `novelty-audit.md` (novelty review), `archive-catalog.md` (catalog of archives and part correspondences), `what-is-aadel-projective-geometry.md`, `strategy-nonconvergence.md`, `emergence-next-directions.md`, `preregistration-delta-first-consequence.md`, `founding-document-outline-20261115.md`, `remaining-questions-inventory.md`
