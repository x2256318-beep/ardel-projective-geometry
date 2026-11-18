# Ardel Projective Geometry: Basic Structure and Comparison with Existing Frameworks

> **About this document**
> Written on 2026-11-16. An overview based on the outline of the foundational document (2026-11-15) and the Lean formalization up to Part 259.
> It keeps the author's definitions and readings separate from what has been formalized in Lean.
> The frameworks compared are adelic geometry (the standard theory), Connes's framework, Arakelov geometry, and anabelian geometry.
> This is an English translation of [`overview-and-comparison.md`](overview-and-comparison.md) (Japanese). If the two differ, the Japanese version takes precedence.

## Contents

1. [In one sentence](#1-in-one-sentence)
2. [Basic structure (four layers)](#2-basic-structure-four-layers)
3. [Honest status](#3-honest-status)
4. [Comparison with adelic geometry (the standard theory)](#4-comparison-with-adelic-geometry-the-standard-theory)
5. [Comparison with the framework of Connes (and Consani)](#5-comparison-with-the-framework-of-connes-and-consani)
6. [Comparison with Arakelov geometry](#6-comparison-with-arakelov-geometry)
7. [Comparison with anabelian geometry](#7-comparison-with-anabelian-geometry)
8. [Positioning](#8-positioning)
9. [References](#references)

---

## 1. In one sentence

Ardel projective geometry takes the primes and the infinite place as its "points". Its global object is the whole in which these places coexist side by side, from the start, as the factors of a restricted product.

Its novelty lies not in individual theorems but in four design choices:

- what counts as a point,
- what counts as the global object,
- how the infinite place is glued,
- how the whole is viewed (resolution).

### Origin of the name (by the author, 2026-11-16)

- "Ardel" is the author's coinage, combining *idele* (the multiplicative side) and *adele* (the additive side).
- "Ardel projective geometry" means **fusing adelic geometry and idelic geometry by projection**.
- Which map or construction this "projection" denotes mathematically is left open, to be fixed in the foundational document ([§3](#3-honest-status)).

---

## 2. Basic structure (four layers)

### 2.1 Points and the global object (author's definitions)

- The points are the primes 2, 3, 5, … and the infinite place ♾️.
- The global object is the whole in which these places coexist in parallel, from the start, as the factors of a restricted product.
- The finite levels (quotients modulo $N$) and the $\Lambda$-cutoff are "views" (ways of cutting) of that whole. They are two mutually orthogonal axes.
- The foundation is discrete. Continuous objects such as lines do not exist in the foundation.

### 2.2 Gluing at the infinite place (author's definitions and the postulate)

**Author's definitions**

- At the infinite place, the infinitely large and the infinitely small overlap.
- In the author's words, **$-\infty$, $\infty$ and $0$ overlap by projection** (2026-11-16).
- The author decided to read this overlap as "a twisted gluing by a boundary unitary $U$" (2026-11-12).
- The reading that identifies the two ends as a group quotient is not adopted, because it is incompatible with postulate A1.

**Reading (proposed by the construction side, confirmed by the author on 2026-11-16)**

- Map the positive reals $\mathbb{R}_{>0}$ (the multiplicative side) to the line $\mathbb{R}$ (the additive side) by the logarithm.
- Then the multiplicative $0$ corresponds to the additive $-\infty$, and the multiplicative $\infty$ to the additive $+\infty$.
- So "the overlap of $-\infty$, $\infty$ and $0$" can be read as joining the two ends of the logarithmic line (which, seen multiplicatively, are $0$ and $\infty$) into one.
- This matches the shape of two familiar facts: on the projective line $\mathbb{P}^1(\mathbb{R})$, $+\infty$ and $-\infty$ are a single point, and the inversion $x \mapsto 1/x$ exchanges $0$ and $\infty$.
- It is also consistent with the name's "fusion by projection" (fusion of the additive and the multiplicative).

**The monograph layer and the postulate**

- The monograph layer deals with an operator system ($D$, $T_p$, $W$) on the idele class group $C_{\mathbb{Q}}$.
- Its central question P1 is the classification of compatible boundary conditions $U$ for self-adjoint extensions (Theorem 2.6).
- The content of postulate A1 is Tate's theorem (the gluing of $\gamma$-factors). A1 is placed as a postulate and has not been derived.

### 2.3 Resolution (author's definition and reading)

- **Reading L1**: the resolution is "the set of places that are measured". The parameter that fixes the resolution is undecided and is not identified with any of $N$, $K$ or $\Lambda$.
- **Author's definition (summary)**: escaping into the completion (the limit) and sliding into the continuum is what it means for the resolution to drop. The aim is to keep observing the discrete structure even in the limit.
- The limit is taken on the side of the direct limit, where all places are measured at once.
- When completions ($L^2$, $\mathbb{R}$, the product topology) are used, they are read as "operations on the side where the resolution drops".

### 2.4 Theorems about the design (formalized in Lean)

| Part (file) | Content |
|---|---|
| Part 255 (`PAG259.lean`) | For the image of the subgroup generated by finitely many primes: a line $\mathbb{R} \times \lbrace k \rbrace$ in the direction of the infinite-place coordinate appears in the closure if and only if at least two primes are left unmeasured. If everything is measured at once, the image is closed and discrete. In the control case, the function field $\mathbb{F}_q(t)$, no line appears (the image of the norm is $q^{\mathbb{Z}}$). The ingredients of the proof (the $S$-unit theorem, the product formula, weak approximation) are known |
| Part 258 (`PAG262.lean`) | For $N \mid M$, a unital algebra homomorphism $A_N \to A_M$ that is compatible with pullback and does not mix shells exists if and only if $\gcd(N, M/N) = 1$ |
| Part 259 (`PAG263.lean`) | Adding compatibility with the Fourier transform to these conditions makes the map unique (`shellLift`). Without it, the map is not unique for $a = 2$. The index order (the classical unitary-divisor relation) is not directed. The square-free levels form an inductive system |

Here $A_N$ is the shell algebra, which is the same as the known Terwilliger algebra $T(0)$.

---

## 3. Honest status

- About 3,640 theorems and lemmas have been formalized. Most of them re-derive known facts.
- There are two small candidates for novelty: the classification of generators, and the non-existence result for β. Neither has been checked against the literature (MathSciNet, zbMATH), so neither is used as a novelty claim.
- This theory is not an approach to the Riemann hypothesis.

**Open questions**

- How to formulate the "projection" in the name (the operation fusing the adelic and the idelic sides) as a specific map or construction.
  - Adopted reading (proposed by the construction side, adopted with reservations by the author on 2026-11-18; interpretive layer, not a formalized theorem): the "projection" in the name refers to the pair of a stage and a transform, with the transform as the main sense (in the author's words: "the stage is P¹, and the composition of gluings acting on it is called the projection"). The stage is the projective line P¹ (Parts 19–28 (PAG23–PAG32); inversion swaps 0 and ∞). In the construction side's reading, that composition is the composition of inversion (the multiplicative side) and an additive transform (the additive side), which at the finite level corresponds to $J \circ H_N/\sqrt N$ of Part 252 (PAG256) (a map sending functions on ℤ/N to functions on the units, not an operator on P¹; no Lean statement links it to the models of P¹). Its components on primitive characters are the phases; the standard kernel is the Hartley kernel of Part 252 (the author's decision), with value $\tau(\chi)/(i^a\sqrt N)$ (the root number for primitive χ, but that identification is outside Lean). With the plain Fourier kernel $e(xy)$ the value is $\tau(\chi)/\sqrt N$, differing by a factor $i$ for odd characters. The additive character follows the convention of the additive character of Tate's thesis ($e^{-2\pi i x}$ at the infinite place, $e^{+2\pi i\{x\}_p}$ at the finite places) as the standard (the author's decision). In that convention, for primitive χ, the factor $(-i)^a$ of the Hartley kernel agrees with the local constant at the infinite place, and $\tau(\chi)/\sqrt N$ agrees with the product of the local constants at the finite places at $s = 1/2$ (an agreement of values, outside Lean; local constants in the style of Tate 1979; literature check of 2026-11-18, `notes/pag2_literature_ia_sign.md`, Japanese, re-confirming the reading recorded in Part 257 (PAG261)). That the explicit factor $i^{\pm a}$ is the local constant at the infinite place does not depend on the convention, but where the sign $\chi(-1)$ is placed does. The postulate A1 remains a postulate that chooses the phase of the boundary unitary on primitive characters to be this value (a reading). All ingredients are known, and this is not made a new Part (`notes/pag2_projection_material.md`, Japanese). Remaining question: a formulation as one construction across all places (at the level of spaces and operators). At the level of values, the decomposition into a product of local factors over all places is in Part 257 (PAG261).
- Whether the finite-level inductive system reaches the side of $T(0)$ (literature check for direction γ).
- Whether the operation of resolution needs a formulation beyond L1.
- Drafting the foundational document (author's side).

---

## 4. Comparison with adelic geometry (the standard theory)

**What they share**

- Taking the restricted product of the places as the global object is exactly the adeles.
- The content of postulate A1 is Tate's theorem.
- $A_N$ is the known Terwilliger algebra.

**Differences (design choices)**

| Aspect | Standard theory | This theory |
|---|---|---|
| Treatment of the continuum | Starts from the completions at each place ($\mathbb{Q}_p$, $\mathbb{R}$) | Places the foundation in the discrete, and reads completion as "an operation by which the resolution drops" |
| Infinite place | One factor $\mathbb{R}$ | Reads the overlap of the infinitely large and the infinitely small as a gluing by a boundary unitary $U$ |
| Resolution | No operation of that name | Puts at the center the operation of switching views by choosing which places to measure (although what happens under the switch is itself explained by known ingredients; Part 255) |

---

## 5. Comparison with the framework of Connes (and Consani)

**Overview of Connes's framework**

- It considers the adele class space $\mathbb{A}_K/K^\times$ (the adeles divided by the multiplicative group of the global field).
- The Riemann–Weil explicit formulas are interpreted as a trace formula for the scaling action on this space.
- More recently there are the arithmetic site and the scaling site. The points of the scaling site coincide with the adele class space divided by the maximal compact subgroup, and carry the structure of a tropical curve. Algebra in characteristic 1 is used.

**Where they overlap**

- The setting of the monograph layer (the operator system on $C_{\mathbb{Q}}$) sits in almost the same place as Connes's spectral picture.
- The limit side of Theorem 2.6 falls within the scope of Burnol's theorem.

**Differences**

| Aspect | Connes's framework | This theory |
|---|---|---|
| Aim | Centered on an inequality equivalent to the Riemann hypothesis | Does not take that direction (§5 of the monograph records, as a negative result, that attempts to approach the zeros ended in external injection or circular reasoning) |
| How to take the quotient | The noncommutative quotient by $\mathbb{Q}^\times$ (and toposes) is the main object | Keeps the whole of the places undivided, and changes the view by the way of cutting (resolution) |
| Continuum | The scaling action of $\mathbb{R}_{>0}^\times$ is essential | Reads the passage to the continuum as "an operation by which the resolution drops" |

---

## 6. Comparison with Arakelov geometry

**Overview of Arakelov geometry**

- It adds to $\operatorname{Spec}\mathbb{Z}$ (the set of primes) a point corresponding to the infinite place, to "compactify" it.
- In place of the information at the infinite place, it puts Hermitian metrics on vector bundles.
- This yields intersection theory on arithmetic surfaces and the arithmetic Riemann–Roch theorem (Faltings, Gillet–Soulé). The product formula plays an important role.

**Where they overlap**

- The point set "points = primes + the infinite place" is almost the same.
- Part 255 uses the product formula as an ingredient.

**Differences**

| Aspect | Arakelov geometry | This theory |
|---|---|---|
| What is put at the infinite place | A metric (analytic data) | Reads the overlap as a gluing by a boundary unitary $U$ |
| Toolkit | Has divisors, intersection numbers and arithmetic degrees | Has no quantities corresponding to these yet |
| Aim | A tool of Diophantine geometry | Resolution and how things look |

---

## 7. Comparison with anabelian geometry

**Overview of anabelian geometry**

- It asks how much of an arithmetic variety $X$ can be recovered from its étale fundamental group (a noncommutative profinite group).
- Its starting point is Grothendieck's letter to Faltings (27 June 1983), which states the conjecture that "anabelian" schemes are determined by their étale fundamental groups.
- For number fields there is the Neukirch–Uchida theorem (Neukirch 1969, Uchida 1976): number fields with isomorphic absolute Galois groups are isomorphic.
- For hyperbolic curves, after partial results by Nakamura and Tamagawa, Shinichi Mochizuki gave a proof (including the pro-$p$ version of 1999).
- It is seen as one of the generalizations of class field theory. Unlike higher class field theory and the Langlands program, it is noncommutative and strongly nonlinear.
- Work continues, for example on extensions to hyperbolic curves over rings of $S$-integers (Shimizu–Yamaguchi 2025).

**Where they overlap**

- Both treat the primes (places) as points.
- The group of compatible systems `unitSys` in Part 251 is a concrete model of $\widehat{\mathbb{Z}}^\times$, which in class field theory is the Galois group of the maximal abelian extension of $\mathbb{Q}$ (a standard fact). What this theory deals with is the abelian part, which is the starting point beyond which anabelian geometry asks its questions.

**Differences**

| Aspect | Anabelian geometry | This theory |
|---|---|---|
| Data | Noncommutative fundamental groups | Commutative data: the idele class group, characters, Gauss sums, the commutative algebra $T(0)$ |
| Type of question | Reconstruction and rigidity | The design of a geometry, and how things look under resolution |
| Infinite place | Centered on the finite places and the $p$-adic side | Puts the gluing at the infinite place (boundary unitary $U$) at the center |
| Tools | Group theory and $p$-adic Hodge theory | Operators and Fourier analysis |

**Assessment and cautions**

- Reading L1 of resolution (the set of measured places) resembles in shape the anabelian setting in which a set of places $S$ is specified and Galois groups are considered (for example, Neukirch–Uchida type results over rings of $S$-integers). This is a candidate for comparison, but the relation has not been checked (confidence: low to medium).
- Mochizuki's inter-universal Teichmüller theory is built on anabelian geometry, but its assessment as a proof of the abc conjecture is divided. In their 2018 report, Scholze and Stix asserted a serious gap at a key step of the proof (Corollary 3.12 of the third paper), and Mochizuki disputes this. This document does not claim that this theory is close to it.
- As a precedent close in method, there is Project LANA (Lean for ANAbelian Geometry) at ZEN University. One of its goals is to formalize the main theorems of anabelian geometry in Lean and build a library (interim report, July 2026).

---

## 8. Positioning

(Interpretation. Confidence: medium.)

- This theory can be positioned as "gluing the point set of Arakelov geometry in the language of Connes's operators, and viewing it through resolution".
- Put the other way, each of the point set, the operators and the gluing has strong precedents. What is new lies in how they are combined and in where the view called resolution is placed.
- Having no quantities like divisors or degrees is a task for the future.
- The data of this theory stay on the commutative (abelian) side. It has not yet touched the information in the noncommutative fundamental groups that anabelian geometry deals with.
- A recent attempt to treat the adele class space in the language of Arakelov geometry is Connes–Consani, *On the Jacobian of Spec ℤ* (2026). According to its abstract, it interprets the Riemann sector of the adele class space of the rationals as an extension of the Picard group of $\operatorname{Spec}\mathbb{Z}$, and the additional data there extend the metrized line bundles of Arakelov geometry. It is a candidate for a literature check as a bridge between the two (the full text has not been read).

---

## References

The existence and bibliographic data of each item were checked on 2026-11-16. The brackets at the end of each item give where it was checked.

**Connes's framework**

1. A. Connes, C. Consani, *The Scaling Site*, C. R. Math. Acad. Sci. Paris 354(1) (2016) 1–6. arXiv:1507.05818 [arXiv; Springer reference list]
2. A. Connes, C. Consani, *Geometry of the Scaling Site*, Selecta Math. (N.S.) (2017). doi:10.1007/s00029-017-0313-y. arXiv:1603.03191 [arXiv; authors' public PDF]
3. A. Connes, C. Consani, *The Riemann–Roch strategy, Complex lift of the Scaling Site*. arXiv:1805.10501 [arXiv]
4. A. Connes, C. Consani, *On the Jacobian of Spec ℤ* (2026). arXiv:2602.15941 [arXiv; abstract only, full text not read]

**Arakelov geometry**

5. S. Ju. Arakelov, *Intersection theory of divisors on an arithmetic surface*, Math. USSR Izv. 8(6) (1974) 1167–1180 [nLab reference list]
6. H. Gillet, C. Soulé, *An arithmetic Riemann–Roch theorem*, Invent. Math. 110 (1992) 473–543 [nLab reference list]
7. S. Takagi, *Compactifying Spec ℤ*. arXiv:1203.4914 [arXiv]

**Anabelian geometry**

8. A. Grothendieck, *Brief an G. Faltings* (27 June 1983). In: L. Schneps, P. Lochak (eds.), *Geometric Galois Actions 1*, London Math. Soc. Lecture Note Ser. 242, Cambridge Univ. Press (1997) [Cambridge table of contents; Grothendieck Circle]
9. J. Neukirch, *Kennzeichnung der p-adischen und der endlichen algebraischen Zahlkörper*, Invent. Math. 6 (1969) 296–314. doi:10.1007/BF01425420 [MaRDI; Numdam reference list]
10. K. Uchida, *Isomorphisms of Galois groups*, J. Math. Soc. Japan 28(4) (1976) 617–620. doi:10.2969/jmsj/02840617 [Project Euclid; MaRDI]
11. S. Mochizuki, *The local pro-p anabelian geometry of curves*, Invent. Math. 138 (1999) 319–423 [author's public PDF; reference lists of other papers]
12. R. Shimizu, N. Yamaguchi, *Étale fundamental groups of smooth arithmetic surfaces and the Grothendieck conjecture* (2025). arXiv:2511.06725 [arXiv]
13. P. Scholze, J. Stix, *Why abc is still a conjecture* (report, 2018) [Scholze's public PDF]
14. Project LANA, *Project LANA Interim Report on IUT Theory* (July 2026) [ZEN University announcement; report PDF]

**Other (sources of terms used in the text)**

15. E. Cohen, *Arithmetical functions associated with the unitary divisors of an integer*, Math. Z. 74 (1960) 66–80 [EuDML; zbMATH 0094.02601]
16. P. Terwilliger, *The subconstituent algebra of an association scheme I, II, III*, J. Algebraic Combin. 1(4) (1992) 363–388; 2(1) (1993) 73–103; 2(2) (1993) 177–210 [EMIS; MaRDI]
