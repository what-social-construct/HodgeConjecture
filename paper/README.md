# Canonical manuscript

The single current manuscript is:

- [`main.tex`](main.tex), *A Formal Projector Spine for the Rational Hodge
  Target: Collisions, Marked Galois Sheets, and Boundary Interfaces*.
- [`main.pdf`](main.pdf), the compiled author-review candidate.

It follows the dependency-ordered components reflected by the active Lean
modules, from the precise abstract rational Hodge target through graph projectors, collision and finite-etale
correspondences, marked normal-closure sheets, the codimension-one boundary
endpoint, compactified projector interfaces, and the exact conditional
coverage gap. It is a formalization report and does not claim a new case of
the Hodge conjecture.

The earlier Paper I and Paper II sources and PDFs are preserved in
[`research/archive/manuscripts/`](../research/archive/manuscripts/README.md).
They are historical snapshots and are excluded from the current build and
release checks.

Build from this directory with:

```bash
latexmk -pdf main.tex
```

The current bibliography is [`references.bib`](references.bib). The
manuscript contains no license assertion; authorship, citations, mathematical
content, novelty positioning, and release terms require final author review
before publication.
