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
clean-clone or Comparator/NanoDa check, and the Lean 4.24 toolchain used in that assessment was
below the Palomar 4.28 minimum recorded then.

The earlier successful builds of Paper I and Paper II are historical checks.
Their sources and PDFs now live in `research/archive/manuscripts/`, outside
the active manuscript and release build requirements.

The 2026-10-27 SP113 working-tree assessment passes the full build (3273
jobs; only the two deliberate `Challenge.lean` warnings), the integrated
verification (1255 declaration checks, 565 examples, 1147 axiom reports),
and the new root-import finite-pushforward composition suite (ten examples,
ten enforced standard-three axiom audits). The existing finite norm/Chow,
localization, marked-cycle, supported-class and proof-dependency suites
also pass. All observed theorem axioms are within `propext`,
`Classical.choice` and `Quot.sound`. Active-library proof-gap scanning,
local links, notation-table widths and `git diff --check` pass. This
assessment preserves the pre-existing uncommitted work. It does not mark
the clean-clone, manuscript-rendering, submission or human-review release
sign-offs above complete.

The 2026-09-14 input-packaging checkpoint is recorded separately in
`working/0016-source-input-packages.md`. Full build (3028 jobs), integrated
verification without warnings, the 99-report standard-axiom allowlist audit,
explicit-premise/nonzero-boundary-defect regressions, unchanged submission
statements, source/parity review, and the single-PDF build and visual review
pass. No Comparator/NanoDa or clean-clone run is claimed. These worktree
checks do not complete the human or clean-clone release sign-offs above.

The 2026-11-05 working-tree migration uses Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The complete default build passes
3676 jobs, including the new finite-fiber cycle modules. All 52 current
research verification/diagnostic files pass in the isolated migration copy
and byte-match the applied sources; the integrated verification also passes
again from the actual repository path (1255 declaration checks, 565 examples,
1147 axiom reports). Observed theorem axioms stay within `propext`,
`Classical.choice` and `Quot.sound`; the production source scan is clear.
Lean 4.35 style/deprecation warnings and the two existing `Challenge.lean`
statement placeholders remain. Current documentation file/heading links,
exact dependency pins, Comparator JSON parsing and `git diff --check` pass.
The migration preserved the existing uncommitted work and retained a local
source/cache backup. General flat Chow pullback/descent and locally free
rank comparison remain open. No clean-clone, Comparator/NanoDa, manuscript
rendering, publication or human-review sign-off is added. See
[the migration record](working/0020-lean-4-35-migration.md).

The subsequent 2026-11-05 finite flat checkpoint closes the finite flat
Chow-descent and geometric-rank gaps left open by that migration. The
complete default build passes 4142 jobs. Seven selected standalone files
pass, including the integrated 1255-check/565-example/1147-axiom-report
inventory and the new rank/Chow suites with five examples and 32 enforced
standard-three axiom audits. The root-import Chow regression retains degree
two for a square-zero thickening. Finite-fiber, norm/Chow, pushforward
composition and localization regressions pass. Production proof-token
scanning, dependency pins, local file links and `git diff --check` pass;
the main README is 69 lines. General Betti/purity comparison and prescribed
Hodge-class generation remain open. These working-tree checks leave the
clean-clone and human-release boxes above unchanged. See
[the finite flat record](working/0021-finite-flat-chow-transfer.md).

The affine de Rham and modular-build checkpoint adds a constructed affine
complex, a bounded degree-zero algebra trace and finite split comparison.
The full build passes 4,172 jobs. The core, Chow and comparison entry points
also build independently; the core imports six project modules and excludes
project geometry, Chow and Betti. All five selected standalone suites pass,
including eight new examples and 37 enforced standard-three axiom audits.
The root inventory retains its 1,255 checks, 565 examples and 1,147 axiom
reports. Import-boundary checks, the production proof-token scan, dependency
pins, local file links and whitespace checks pass. The main README remains
69 lines. No Axiom Stacks package dependency is added; local proof adaptations
retain source attribution and licensing. General scheme trace and
positive-dimensional Betti comparison remain open. See
[the checkpoint](working/0022-affine-derham-trace-comparison.md) and
[focused build commands](BUILDING.md). Release sign-off boxes above retain
their previous status.

The polynomial/component extension passes the full 4,174-job build and the
root inventory with 1,264 checks, 565 examples and 1,156 axiom reports.
Seven new regression examples and 15 enforced axiom audits pass, as do the
existing comparison suite's 25 audits. The separate component target has
five project modules; the original core retains six. All 385 production
modules pass proof-token and external-Stacks-import scanning. Dependency
pins, import boundaries, local links and whitespace checks pass. See the
[implementation record](working/0023-polynomial-derham-components.md).
The Palomar preparation commands described in the
[handoff](working/PALOMAR_FIXED_RING_HANDOFF.md) are distinct from release
sign-off and independent Comparator/kernel replay.

The affine-line comparison checkpoint passes its 2,905-job focused build,
eight regressions and 23 enforced standard-three axiom audits. The existing
comparison suite retains its 25 passing audits. The full default build
passes 4,177 jobs; root verification passes 1,274 checks, 565 examples and
1,166 axiom reports. All 388 production modules pass proof-token scanning.
The new eight-module comparison target excludes project Chow/cycles and
boundary geometry, while the core/component targets retain their original
boundaries. Both indirect-negative import checks, pins, links and whitespace
checks pass. This is a degree-zero comparison for the complex affine line;
higher-degree and positive-codimension realization remain open. See the
[checkpoint](working/0024-affine-line-betti-comparison.md). No submission
candidate or release sign-off is finalized by these working-tree checks.

The graph-Chow checkpoint passes its 3,274-job focused build, 18 regressions
and 29 enforced standard-three axiom audits. The full default build passes
4,181 jobs; root verification passes 1,297 declaration checks, 568 examples
and 1,189 axiom reports. All reported axioms are within the standard three.
The 392 library modules plus the root pass proof-token and external-import
scanning. Six import boundaries, pins, local links and whitespace checks
pass; the focused graph-Chow closure has 151 project modules and excludes
project realization and collision geometry. See the
[checkpoint](working/0025-graph-chow-convolution.md) for the exact actual-Chow
scope and remaining prescribed-realization gap. README and module accounts
distinguish these results from the two fixed-ring Challenge statements;
historical/build exclusion is not treated as submission exclusion. Release
sign-offs and candidate selection remain unchanged.

The ordinary positive-degree checkpoint (2026-11-06) passes its combined
3,318-job focused build, 34 permanent examples and 48 enforced standard-three
axiom audits. The full default build passes 4,215 jobs; root verification
passes 1,334 declaration checks, 574 examples and 1,226 axiom reports, all
within the standard three (one report needs no axioms). All 421 library
modules plus the root pass proof-token/external-import scanning. Eight
import boundaries, three indirect-negative checks, pins, local links and
whitespace checks pass; the main README remains 69 lines. The actual
ordinary projective-line Chow-source cycle map lands in the constructed
and computed Čech–de Rham H². Scheme/singular/Hodge comparison and general
prescribed-class coverage remain open. See
[0026](working/0026-positive-degree-cycle-realization.md). Existing release
sign-offs, comparator selection and submission packaging remain unchanged.

The projective-line scheme checkpoint (2026-11-06) passes its 3,693-job
focused Make build, 38 permanent examples, a named logarithmic representative
regression and 58 enforced standard-three axiom audits, with no focused-suite
warnings. The full default build passes 4,578 jobs; root verification passes
1,350 declaration checks, 574 examples and 1,236 axiom reports within the
standard three (one report needs no axioms). All 460 library modules plus
the root pass proof-token/external-import scanning. Ten import boundaries,
three indirect-negative checks, pins, local documentation links and whitespace
checks pass. The main README remains 69 lines; existing warning scope remains.
The actual ordinary P¹ Chow map now lands in actual scheme de Rham H²,
through the proved sheaf/derived comparison. Singular/Betti realization,
generality and prescribed Hodge-class coverage remain open. See
[0027](working/0027-projective-line-scheme-comparison.md). Existing release
sign-offs, comparator selection and submission packaging remain unchanged.

The projective-line Betti-input checkpoint (2026-11-06) passes its 3,049-job
topology/cochain and 4,397-job analytic-period focused Make builds. Its three
suites pass 39 examples, five named calculations and 82 enforced
standard-three axiom audits, with zero suite warnings. The full default
build passes 4,976 jobs; root verification passes 1,368 declaration checks,
574 examples and 1,246 axiom reports within the standard three (one report
needs no axioms). The 466 library modules plus the root pass source scans;
twelve import boundaries, three indirect-negative checks, pins, local links
and whitespace checks pass. Existing warning scope remains; the main README
remains 69 lines. Actual P¹ complex topology, full rational singular
cochains and analytic scheme periods are constructed. Singular H²
computation, the oriented Betti comparison and general prescribed-class
coverage remain open. See [0028](working/0028-projective-line-betti-inputs.md).
Release sign-offs, comparator selection and submission packaging remain unchanged.

The rational small-chain checkpoint (2026-11-06) passes the 2,263-job pure
focused target and separate 2,949-job P¹ chart-topology regression build.
Its eleven suites pass 111 examples, 13 named calculations and 264 enforced
standard-three axiom audits with zero suite warnings. The full default
build passes 5,012 jobs; root verification passes 1,395 declaration checks,
574 examples and 1,263 axiom reports within the standard three (one report
needs no axioms). All 487 library modules plus the root pass source scans;
thirteen import boundaries, three indirect-negative checks, pins, local
links and whitespace checks pass. Existing warning scope remains; the main
README remains 69 lines. The actual native small-chain inclusion is now a
rational homology quasi-isomorphism for a genuine two-open cover. Full
singular cochain dualization, the P¹ H² calculation and oriented Betti
comparison remain open. See [0029](working/0029-small-singular-chains.md).
Release sign-offs, comparator selection and submission packaging remain unchanged.
