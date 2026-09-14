# Release checklist

Record a date, commit hash, and reviewer beside each completed item.
The boxes below are release sign-offs, so successful working-tree checks
recorded at the end of this file do not mark them complete before clean-clone
and human review.

## Formal integrity

- [ ] `lake build` succeeds from a clean clone at the pinned Mathlib revision.
- [ ] `rg -n '\b(sorry|admit|axiom)\b' HodgeConjecture --glob '*.lean'`
      returns no project proof gaps.
- [ ] The exact theorem names in the canonical manuscript still resolve.
- [ ] `lake env lean research/Verification.lean` succeeds.
- [ ] Every headline theorem is tested through the root import.
- [ ] The release commit contains all currently untracked source modules.

## Mathematical integrity

- [ ] A human expert has checked that each prose theorem matches its Lean
      quantifiers, typeclasses, structures, and explicit hypotheses.
- [ ] Packaged structures are not described as proved existence theorems.
- [ ] Each selected literature-input consumer prints its own precise premise;
      there is no blanket hypothesis or global source instance. The packages
      are not described as formalizations of the complete cited theorems.
- [ ] Free span algebras are not called Chow rings.
- [ ] Coordinate-ring idempotence is not conflated with convolution
      idempotence.
- [ ] A defect killed by generic restriction is a kernel element. Boundary
      image membership is attributed to the separate exactness premise and
      algebra restriction; the geometric map identification and vanishing
      are checked independently.
- [ ] `CompactifiedDeckGraphComparison` is described as supplied comparison
      data, not as a constructed compactification or Chow realization.
- [ ] `ConjugateBoundarySeparation`, its center/ramification realizations, and
      every global purity/gluing package remain visible hypotheses.
- [ ] The prescribed-target realization equality is supported by its actual
      comparison proof, not inferred merely from constructing a projector.
- [ ] Fixed-codimension, one-model/all-codimension, and all-varieties Hodge
      quantifiers are distinguished in every headline claim.
- [ ] The graph/Hodge-morphism compatibility and the Tate-block
      construction/detection maps are instantiated geometrically before an
      abstract graph-projector iff is called a theorem about a concrete
      variety.
- [ ] Finite-Galois coverage is presented only as a sufficient condition
      unless a separate factorization/generation theorem proves the reverse
      implication. The abstract rational marked-sheet block is distinguished
      from the actual finite-split Chow residual realization of A11m; neither
      supplies arbitrary class coverage. Subgroup averaging is not identified
      with pointwise selector multiplication.
- [ ] The marked-selector endpoint keeps the generic sheet algebra separate
      from the noncommutative compactified correspondence algebra.  Its
      lower-left conclusion is described as conditional on the residual map
      and action square, while surjectivity is required only for whole-
      operator cancellation. Geometric instances are claimed only where the
      residual map and square have actually been constructed, as in A11m.

## Sources and novelty

- [ ] Every literature input has an exact theorem/tag and a completed
      hypothesis match in `SOURCE_LEDGER.md`.
- [ ] A conditional submission explicitly states any unmatched source
      conclusion as a premise; it does not claim that the source theorem or
      its intended application has thereby been formalized.
- [ ] The closest formalization and mathematical literature has been searched.
- [ ] Any “first,” “new,” or “previously unknown” wording is supported.
- [ ] The title and abstract do not imply a proof or special case of the Hodge
      conjecture unless a concrete nontrivial case is actually derived.

## Reproducibility and submission

- [ ] Build the single canonical manuscript `paper/main.tex` to
      `paper/main.pdf`; historical files in `research/archive/manuscripts/`
      are preserved snapshots, not release build targets.
- [ ] The Challenge has no transitive project-source dependency. Any future
      local bundle is fully stated and auditable; matching Solution types
      preserve its explicit premises. See the current
      [Palomar handoff](working/PALOMAR_FIXED_RING_HANDOFF.md).
- [ ] Add an explicit repository license.
- [ ] Add author names, affiliations, acknowledgements, and contribution
      statements supplied by the authors.
- [ ] Add a citation file and archival identifier after the release is frozen.
- [ ] Tag the exact code version accompanying the manuscript.
- [ ] Archive the tagged release, then update the manuscript with its DOI.

Build observation for the current working tree on 2026-09-11:
the full default `lake build` completed successfully after the localized
fixed-ring descent, exact prime-inertia endpoint, Palomar wrappers, abstract
Hodge target/equivalence, marked Galois block and conditional realization,
compactified graph comparison, raw closure-defect calculus, and self-contained
conjugate-boundary separation modules were added (2795 jobs).  The separation
wrappers discharge the local side of the existing selector and subgroup-
projector extension criteria while leaving actual purity/gluing explicit. The
only build warnings are the two deliberate statement holes in
`Challenge.lean`; there are no `sorry`, `admit`, or project-level `axiom`
tokens under `HodgeConjecture/`.  `research/Verification.lean`, JSON parsing of
`comparator.json`, and `git diff --check` also succeed. The canonical
manuscript `paper/main.tex` builds with `latexmk` to `paper/main.pdf`; its log
contains no warning, undefined-reference,
undefined-citation, overfull, or underfull diagnostics.  This is not yet a
clean-clone or Comparator/NanoDa check, and the current Lean 4.24 toolchain is
below Palomar's current 4.28 minimum.

The earlier successful builds of Paper I and Paper II are historical checks.
Their sources and PDFs now live in `research/archive/manuscripts/`, outside
the active manuscript and release build requirements.

The 2026-09-14 input-packaging checkpoint is recorded separately in
`working/0016-source-input-packages.md`. Full build (3028 jobs), integrated
verification without warnings, the 99-report standard-axiom allowlist audit,
explicit-premise/nonzero-boundary-defect regressions, unchanged submission
statements, source/parity review, and the single-PDF build and visual review
pass. No Comparator/NanoDa or clean-clone run is claimed. These worktree
checks do not complete the human or clean-clone release sign-offs above.
