# Canonical manuscript

The single current manuscript is:

- [`main.tex`](main.tex), *Galois Correspondences and the Hodge Conjecture*.
- [`main.pdf`](main.pdf), the compiled manuscript.

The six main sections follow the rational Hodge target and graph-projector
equivalence, collision and marked Galois projectors, the boundary mechanism,
compactified graph calculus, the split geometric realization, and residual
realization and coverage. Three appendices retain the detailed graph/cycle/
dimension proofs, split computations, and the centralized Lean declaration
crosswalk with source inputs. These all build into the same PDF.

The theorem hypotheses stay in the manuscript; working proof-status and gap
records are maintained in [`research/GAP_MAP.md`](../research/GAP_MAP.md) and
the [semantic-parity queue](../research/working/0005-semantic-parity-cleanup.md).

The earlier Paper I and Paper II sources and PDFs are preserved in
[`research/archive/manuscripts/`](../research/archive/manuscripts/README.md).
They are historical snapshots and are excluded from the current build and
release checks.

Build from this directory with:

```bash
latexmk -pdf main.tex
```

The current bibliography is [`references.bib`](references.bib).
[`hodgealpha.bst`](hodgealpha.bst) retains the standard `alpha` style,
with its permitted local rename and a single functional change: same-label
disambiguation continues `a,…,z,aa,ab,…` rather than overflowing into
punctuation after 26 entries. This accommodates the Stacks references
without changing corporate authorship or publication dates. The original
style's copyright and redistribution notice are retained in the file.
The manuscript contains no license assertion; authorship, citations, mathematical
content, novelty positioning, and release terms require final author review
before publication.
