# Release checklist

Record a date, commit hash, and reviewer beside each completed item.

## Formal integrity

- [ ] `lake build` succeeds from a clean clone at the pinned Mathlib revision.
- [ ] `rg -n '\b(sorry|admit|axiom)\b' HodgeConjecture --glob '*.lean'`
      returns no project proof gaps.
- [ ] The exact theorem names in the manuscript still resolve.
- [ ] `lake env lean research/Verification.lean` succeeds.
- [ ] Every headline theorem is tested through the root import.
- [ ] The release commit contains all currently untracked source modules.

## Mathematical integrity

- [ ] A human expert has checked that each prose theorem matches its Lean
      quantifiers, typeclasses, structures, and explicit hypotheses.
- [ ] Packaged structures are not described as proved existence theorems.
- [ ] Free span algebras are not called Chow rings.
- [ ] Coordinate-ring idempotence is not conflated with convolution
      idempotence.
- [ ] The prescribed-target realization equality is never presented as a
      consequence of the construction.
- [ ] Fixed-codimension, one-model/all-codimension, and all-varieties Hodge
      quantifiers are distinguished in every headline claim.
- [ ] The graph/Hodge-morphism compatibility and the Tate-block
      construction/detection maps are instantiated geometrically before an
      abstract graph-projector iff is called a theorem about a concrete
      variety.
- [ ] Finite-Galois coverage is presented only as a sufficient condition
      unless a separate factorization/generation theorem proves the reverse
      implication.  The proved rational marked-sheet block comparison is not
      described as a Chow-motivic residual realization, and subgroup averaging
      is not identified with pointwise selector multiplication.
- [ ] The marked-selector endpoint keeps the generic sheet algebra separate
      from the noncommutative compactified correspondence algebra.  Its
      lower-left conclusion is described as conditional on the residual map
      and action square, while surjectivity is required only for whole-
      operator cancellation; none is presented as a geometric instance.

## Sources and novelty

- [ ] Every literature input has an exact theorem/tag and a completed
      hypothesis match in `SOURCE_LEDGER.md`.
- [ ] The closest formalization and mathematical literature has been searched.
- [ ] Any “first,” “new,” or “previously unknown” wording is supported.
- [ ] The title and abstract do not imply a proof or special case of the Hodge
      conjecture unless a concrete nontrivial case is actually derived.

## Reproducibility and submission

- [ ] Add an explicit repository license.
- [ ] Add author names, affiliations, acknowledgements, and contribution
      statements supplied by the authors.
- [ ] Add a citation file and archival identifier after the release is frozen.
- [ ] Tag the exact code version accompanying the manuscript.
- [ ] Archive the tagged release, then update the manuscript with its DOI.

Build observation for the current working tree on 2026-09-11:
the full default `lake build` completed successfully after the localized
fixed-ring descent, exact prime-inertia endpoint, Palomar wrappers, abstract
Hodge target/equivalence, and marked Galois block and conditional realization
modules were added, together with the transparent conditional
different-avoidance corollary
(2794 jobs).  The only warnings are the two deliberate statement holes in
`Challenge.lean`; there are no `sorry`, `admit`, or project-level `axiom`
tokens under `HodgeConjecture/`.  `research/Verification.lean`, JSON parsing of
`comparator.json`, and `git diff --check` also succeed.  Both manuscript PDFs
build with `latexmk`; their logs contain no warning, undefined-reference,
undefined-citation, overfull, or underfull diagnostics.  This is not yet a
clean-clone or Comparator/NanoDa check, and the current Lean 4.24 toolchain is
below Palomar's current 4.28 minimum.
