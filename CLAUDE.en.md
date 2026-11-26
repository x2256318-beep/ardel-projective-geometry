# Instructions for Claude — Ardel Projective Geometry (PAG) Project

> **About this translation**
> This is an English translation of [`CLAUDE.md`](CLAUDE.md) (Japanese, short version of 2026-11-27). The Japanese original is authoritative; if the two differ, follow the Japanese. This translation is for reference by readers and is not itself the instruction file. The full text of the previous English translation is preserved in [`CLAUDE-history.en.md`](CLAUDE-history.en.md).

The operating rules to read first (short version, 2026-11-27). The authoritative record of the history, rationale and timing of decisions is `CLAUDE-history.md` (the full text as of 2026-11-26, preserved without changing a character). If you find a point where this short version disagrees with it, stop and report to the author. New decisions are added to this file briefly; history goes into handoff memos and notes.

## 0. Before starting

1. Reread the definitions in §1. Do not rewrite the definitions or interpret them more broadly.
2. Check the current position in §2 (and the latest handoff memo and `notes/pag2_tail_ledger.md`).
3. For a new object, mapping it to existing mathematics (the dictionary and the blind naming test of §6) is an obligation. If the question left after the mapping cannot be stated in the language of geometry, the global, or limits, treat the object as a device for local computation.
4. Before working, state the current position in your own words, split into (a) formalized content, (b) the author's interpretive layer (§1), and (c) open global questions. If you mix them, start over.

## 1. The author's definitions (settled; do not redefine or reinterpret)

- The aim is to build "Ardel projective geometry." Ardel = idele-adele (a geometry containing the multiplicative ideles and the additive adeles). The name means "fusing adelic geometry and idelic geometry by projection."
- The points are the primes plus the infinite place. At the infinite place, the infinitely large and the infinitely small overlap.
  - Reading of the "overlap": a **twisted gluing (boundary unitary U)**. It is not read as a group quotient (incompatible with A1; a cubic character mod 9 is a counterexample). A quotient by W is not adopted either (D does not descend to the quotient).
- The foundation is discrete; continuous objects such as the line do not exist in the foundation.
- The line is the effective form that emerges when the resolution is lowered.
  - The resolution parameter is **undecided**. Do not identify it with N, K, or Λ.
  - Its place is not "a transition inside the object" but **the choice of a way of cutting (viewing)** the global object (interpretive layer). Finite-level quotients and the Λ-cutoff are two axes of that viewing.
  - The author's definition (original wording, translated): "Slipping into the continuum by escaping into completion (the limit) is what I call the resolution falling. I do not want the continuum to be observed; even in the limit, the observation of discrete structure is maintained." When using completion (L², ℝ, the product topology), say that it is "read as an operation on the side where the resolution falls." Do not write a continuum appearing in a closure or completion as the "effective form" or as a goal.
  - The reading L1 (resolution = the set of places measured) is adopted (as a reading, not the wording of the definition).
  - Do not use the expression "emergence of the line" (直線の創発). When referring to proposition 3, write it by reference as "proposition 3 of §1 (resolution and effective form)."
- Reading of "projective" (interpretive layer, with reservations):
  - The stage is the projective line P¹ (the inversion swaps 0 and ∞; at the finite level, Parts 19–28 (PAG23–PAG32)). The **composition of gluings U** acting on it is what is called projection. The transformation is primary.
  - At the finite level it corresponds to J∘H_N/√N of Part 252 (PAG256) (`PAG.Part256.JH`), but `JH` is not an operator on P¹, and there is no Lean statement connecting JH with the model of P¹.
  - The standard kernel is the Hartley kernel. Its value is τ(χ)/(i^a√N) (`PAG.Part256.rootNum`, symbol 𝔀; distinct from the inversion W). For primitive characters it is the root number, but that identification is outside Lean (say so explicitly). It differs from the value of the naive kernel e(xy) by a factor i for odd characters; do not smooth over this discrepancy.
  - The additive characters follow **convention T** (Tate's thesis: ψ_∞(x) = e^{−2πix}, ψ_p(x) = e^{+2πi{x}_p}). Under convention T (with the normalization ω_q(q) = χ(q), primitive characters, s = 1/2), (−i)^a agrees in value with the local constant at the infinite place, and τ(χ)/√N with the product of the local constants at the finite places (outside Lean; confidence: high). Where χ(−1) is placed depends on the convention. Do not write "ε(χ) comes from the infinite place" without stating convention T.
  - At the level of operators, U is an operator on the equator (the space of functions on the units), and it does not extend uniquely to all of P¹ under natural conditions alone (to be written as a property).
- All of the above is the interpretive layer, not formalized theorems. Do not confuse their status in writing.

## 2. Current position (2026-11-26)

- **Monograph layer (1.0)**: the operator system (D, T_p, W) on the idele class group C_ℚ. The central problem P1 is the compatibility classification of the boundary condition U (Theorem 2.6). **Axiom A1** is a restatement of the value at λ = 0 of the gluing of Tate's γ-factors, and **remains a postulate** (do not write that it has been derived).
- **PAG 2.0 (finite level)**: the Lean formalization goes up to Part 262 (PAG266). 3,695 theorems and lemmas; xlsx final84 (3,722 items). Part n is PAG(n+4).lean (third period).
- **The main line is the founding document** (collecting the definitional layer into one document; draft 1 in progress). No new parts are started. Parts run only to fill gaps in the document's chapters.
- Sign 4 of the convergence alarm has continued for 14 parts (Parts 249–262). The assessment that residue-bearing questions pass through A1 or completion (the side of the infinite place) agrees with the results of the gates (`notes/pag2_partial_inversion_preregistration.md`).
- Literature checks: MathSciNet will not be used (the author's decision). zbMATH has been done, with no item changing the status of the candidates (`notes/pag2_literature_zbmath_20261126.md`).
- The detailed history (Parts 248–262, directions α, β, γ, audits) is in `CLAUDE-history.md` §2 and §5 and in the notes.

## 3. Status of results

- The shell algebra A_N is **exactly the Terwilliger algebra T(0)** of the scheme of the orbit Schur ring (cyclotomic S-ring) on ℤ/N (D_t = dual idempotent E*_t, E_t = primitive idempotent of the Bose–Mesner algebra). Dictionary: `notes/pag2_terwilliger_dictionary.md`.
- Treat as **known** (do not write as new): the Wedderburn decomposition and dimension for prime powers (Parts 225–226 = BST 2010, Bastian–Humphries 2026), the tensor decomposition (Part 228 = T(A×B) ≅ T(A)⊗T(B) for direct products), the classification of z(χ) as roots of unity (Chowla–Mordell / Odoni / Funakura), Ramanujan sums and the DFT (classical), Parts 241 and 242 (known basic observations; confidence: medium).
- **Novelty candidates** (unsettled; do not assert; state confidence):
  1. Of the generation classification (Parts 245–248), items 66 and 67–69 for composite N (confidence: medium; "at the level of a small note"). No reservation on external use as novel.
  3. The non-existence side of Part 258 (PAG262): when p divides both N and M/N, there is no unital algebra homomorphism A_N → A_M that is compatible with pullback and does not mix shells (strong reading) (confidence: low–medium). **Do not use it externally (including in applications) as novel** (the reservation remains).
  - The former candidate 2 (the presentation of Theorem 2.6) dropped out (a short consequence of known results). That root numbers satisfy the condition is a consistency check, not a derivation of A1.
- If structure is needed, cite the literature through the dictionary instead of re-proving it.

## 4. How to proceed

- The cycle of a part: numerical check in Python → Lean (0 sorry, 0 warnings) → `#print axioms` → note + xlsx. Note titles use "アーデル射影幾何" (Ardel projective geometry).
- Criterion for a new part: does it answer a question in the language of geometry, the global, or limits? Questions internal to the algebra are not made the main subject. State at the top which question of the original path it serves (if you cannot, do not start).
- **The four points before starting** (before Lean): (1) the question in geometric language, (2) the best translation into existing fields, (3) the residue that does not vanish (if empty, do not start; if only computational details, a short-term small note), (4) a control-group test on the residue. In addition, the blind question test and the internal check (§6).
- **Delegated selection**: the builder side narrows to one recommendation that has passed the gates, and the start is decided by the author-side Muse. Record what was chosen and why. The author can override at any time.
- A single path for decisions: this file and the author side's handovers are the only record. Anything the author chose in a builder-side session is recorded in the handoff memo and returned to the author side.
- Write part numbers as "Part n (PAGm)."

## 5. Do not

- Write known results (§3) as new.
- Write the author's definitions (§1) as if formalized. Change the definitions at will because they are an interpretive layer.
- Write that A1 was "derived."
- Write a numerical check as a proof.

## 6. Detecting failures (convergence alarm and checks)

**Signs (report when they appear)**: (1) an object definable by a standard definition was given a home-made name → search for literature names before proving structure theorems. (2) questions of the "structure, classification, dimension" type for 3 consecutive parts → propose an audit. (3) 10 consecutive parts without a record of a literature check → yellow flag. (4) progress continues only by combining elementary parts → a sign of being in known territory.

**Standing mechanisms**
- Maintain the dictionary (home-made term → literature term). When 5 rows with an empty right column accumulate, fill them before a new part.
- Blind naming test and blind question test: give only the definitions with home-made names removed (and the statement of the question) to a new agent sharing no context, and have it list literature names and existing results. Check the returned candidates against actual literature.
- Conditions for closing a part: a [known / re-derivation / novelty candidate] label on every main result. Novelty candidates carry a search log (terms, sources, scope) and the note that "not found is not a proof of non-existence."
- Control-group test: for statements with arithmetic or global content, check whether they also hold for the function field F_q(t) and for Beurling generalized primes. Statements that do hold are treated as using only form and density.
- Restatement test (every 10–20 parts): being restatable shows only that "no new concept was needed"; do not treat it as evidence that "there is no new content."
- Report, per part, the number of unfilled dictionary rows and the consecutive count of parts without a literature check.

**Circle (type 2)**: injecting the target quantity as an axiom, weight or phase and reading it back (injection → recovery); treating a condition equivalent to the target as progress (circularity by equivalence); a match of form that is trivial from the construction. Before presenting a result: (1) a dependency table (list the inputs), (2) a removal test (remove a suspicious input and see whether the conclusion remains; if it disappears, write "put in and read back"; e.g., removing A1 frees the phases again), (3) checks of equivalence and information content.

**Other types** (details in the author side's `failure-patterns-audit.md`; not in the repository):
- Type 3: inflation of claims. Write titles and statements from the formal statements, after the Lean formal statements are settled.
- Type 4: mis-set questions. Compute the obstruction quantities first, and consider the opposite direction (counterexample, non-uniqueness) once.
- Type 5: boundary cases. Numerics must include degenerate cases (r = 0, p = 2, the smallest modulus, empty sums, trivial characters).
- Type 6: naive generalization. Search for counterexamples before proving.
- Type 7: numerical noise. Before calling something a counterexample, estimate the error sources and confirm by another method.
- Type 8: artifacts of convention. Do not report a "phenomenon" that disappears when conventions or normalizations change.
- Type 9: process drift. Check file versions and number correspondences (the master is the LEAN.zip side; correspondences in the author side's `archive-catalog.md`).
- Type 10: rhetoric of emergence. "Appeared, generated, connected" must come with which term of which theorem is new. If you cannot say, mark it [observation].
- Type 11: drift of formal statements. For each main theorem: a witness of non-vacuity, a counterexample search removing one hypothesis at a time, and a back-translation from the formal statement and definitions alone (by another agent).
- Type 12: internal duplication. Before starting and before closing, run a mechanical duplicate check over the whole chain (including PAG.lean and PAG2–6) (`records/audit_internal/`) and a word search by the names of the objects and constructions used (including Mathlib). Before a new definition, look for a definition with the same formula. Distinguish duplicates as "same statement (A) / follows immediately (B) / close (C)," and do not write "not found" as "no duplicate."

**Check procedure**
- Detection concerning content, claims or novelty (types 1, 2, 3, 10, 11) is done by a new agent given only the object of the check (no self-audit). Give it only the full formal statements and the definitions, not prose and not summaries of other checkers' outputs. Use a standard request text. Have the checker produce artifacts (witnesses, counterexamples, back-translations) rather than verdicts. Record the full request text and the time taken.
- Novelty candidates and main-theorem-level claims are also checked a second time in a separate author-side chat (Muse).
- When fixing wording in a check, make the same fix in all wording: notes, tables, Lean docstrings and header explanations.
- Fixes made after a check, even fixes that do not change claims, stay in the ledger (`notes/pag2_tail_ledger.md`) until they have undergone a check that includes the fixes themselves as input. Declare the ledger closed only on the basis of a check that included the fixes as input, never on self-report.
- **Stop rule**: if the last check returned only low / very-low findings, and there is neither an added sentence that strengthens a claim nor a rewrite of a record of the author's judgment, the remaining fixes may be carried to the integrated check of the next part and the round closed. If there is a fix that changes a claim, do one more integrated check only, and then close by this rule. Do not rewrite records of judgments; add the breakdown of grounds as a postscript.
- If you find signs of agreement with a known object, injection of target information, or trivialization of a formal statement, do not change the definitions or A1; report them to the author as "findings."

## 7. References

- `CLAUDE-history.md`: the full text as of 2026-11-26 (authoritative record of the history and rationale of decisions); English: `CLAUDE-history.en.md`
- `notes/pag2_founding_material_index.md`: index of the founding document
- `notes/pag2_terwilliger_dictionary.md`: dictionary
- `notes/pag2_tail_ledger.md`: ledger of check tails
- `handoff/`: handoff memos (the latest is after Part 259; later history is in the notes and the commit record)
- `records/audit_internal/`: tools for the internal check
- On the author side and not in the repository: `failure-patterns-audit.md` (audit of failure types), `novelty-audit.md` (novelty review), `archive-catalog.md` (catalog of archives and part correspondences)
