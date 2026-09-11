# Manuscript drafts

The canonical unified manuscript candidate is:

- [`main.tex`](main.tex), *A Formal Projector Spine for the Rational Hodge
  Target: Collisions, Marked Galois Sheets, and Boundary Interfaces*.

It follows the dependency-ordered components reflected by the active Lean
modules, from the precise abstract rational Hodge target through graph projectors, collision and finite-etale
correspondences, marked normal-closure sheets, the codimension-one boundary
endpoint, compactified projector interfaces, and the exact conditional
coverage gap. It is a formalization report and does not claim a new case of
the Hodge conjecture.

The two earlier drafts remain as provenance and focused technical sources:

- [`paper1.tex`](paper1.tex), *Height-One Fixed-Ring Descent: Localization
  and Formal Unramifiedness*;
- [`paper2.tex`](paper2.tex), *Finite-Étale Span Projectors and Marked
  Galois-Sheet Blocks in Lean*.

Paper I documents the proved commutative-algebra bridge and its exact Lean
correspondence. It treats Stacks Project Tag `0BST` as an explicit external
premise in the current Lean endpoint, while using the cited result to
discharge that premise mathematically.

Paper II documents the finite-étale free span algebra, transport of
group-algebra and Hecke idempotents to formal convolution projectors, the
marked Galois-sheet block calculation, the self-contained formal implication
from supplied center/ramification comparisons and boundary separation to its
codimension-one endpoint, and a separately labeled conditional realization
criterion. It also states the different-avoidance boundary endpoint only as
a forward conditional corollary with every remaining input visible. Its free
span algebra is not identified with a Chow correspondence algebra. It does
not claim an unconditional boundary extension or a new case of the Hodge
conjecture. Literature and novelty review remain pending.

Build from this directory with:

```bash
latexmk -pdf main.tex
latexmk -pdf paper1.tex
latexmk -pdf paper2.tex
```

The shared source bibliography is [`references.bib`](references.bib). These
drafts contain no license assertion; authorship, citations, mathematical
content, novelty positioning, and release terms require final author review
before publication.
