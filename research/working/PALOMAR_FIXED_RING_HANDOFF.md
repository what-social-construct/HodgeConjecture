# Palomar handoff: height-one fixed-ring descent

Status: **packaging draft, not yet submittable**.

The repository now has a Mathlib-only `Challenge.lean`, a matching
`Solution.lean`, and `comparator.json` for two generic results:

1. height-one contraction to a finite subgroup-fixed ring; and
2. conditional height-one unramified descent from `S^I` to `S^H` for
   `I ≤ H`.

The Challenge text explicitly says what remains outside the result: it does
not identify `I` as the actual inertia group, does not prove the fixed-inertia
theorem of Stacks Project Tag `0BST`, controls only one selected prime, and
does not state the Hodge conjecture.

## Explicit input packaging (2026-09-14)

`Inputs/FixedInertia.lean` now owns the single existing
`InertiaFixedRingUnramifiedAt` record. Its lossless unbundling theorem
identifies it with the printed Mathlib premise. `Challenge.lean`,
`Solution.lean`, and `comparator.json` retain the same two statements and
signatures. The selected extension/deck and Chow-localization packages in
[0016](0016-source-input-packages.md) are not additional submission claims.

For a future conditional wrapper, state Mathlib maps and the exact premises
in `Challenge.lean`. If a small local bundle is needed, fully state and
document its fields there; compare relevant definitions as well as theorem
types when necessary. Do not import project-specific definitions into the
Challenge, even transitively. The Solution may import the implementation,
but its proof must use only the permitted logical axioms, with the selected
literature conclusions remaining visible hypotheses. This follows the
[official statement/dependency policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
rechecked on 2026-09-14. A package name or citation is not a substitute for
its proposition in the compared statement.

No license, metadata, toolchain, or publication-scope decision is made by this
refactor. The migration values below are the historical policy snapshot
listed at the end, and must be rechecked before submission.

## Blocking choices and migrations

- **Human identity:** `formalization.yaml` requires nonempty human-only
  `project.authors` and `project.responsible_maintainers`.  The user must
  supply the names that should appear publicly.
- **Licence:** the repository currently has no root licence.  The user must
  choose a standard SPDX licence and authorize adding its exact text.
  Palomar requires exactly one conventional root licence file and an exact
  match with `project.license`; this is not a choice an agent should make.
- **Toolchain:** the repository uses Lean `v4.24.0`, while Palomar's current
  minimum is `v4.28.0`.  Upgrade Lean and the matching Mathlib revision, then
  rebuild the full project and both wrappers before submission.  The official
  template currently uses Lean `v4.32.0`; using the minimum `v4.28.0` may be
  the smaller port, but either choice needs a real migration check.
- **Public immutable snapshot:** confirm that the GitHub repository is
  public, commit every submitted file (including `lake-manifest.json`), and
  submit a full 40-character commit SHA rather than a branch or tag.
- **Review disclosure:** the user must confirm the honest pre-submission
  review status and any human reviewers.  `unchecked` is appropriate if no
  distinct review has occurred.
- **Editorial scope:** mechanical correctness alone does not meet Palomar's
  research-interest floor.  Before submission, add a restrained account of
  the specialist value of this particular formal composite and complete a
  literature/novelty check.  Do not present standard invariant-theory lemmas
  as new mathematics merely because their Lean combination is new to this
  repository.

## Metadata draft

Do not copy this block to a root `formalization.yaml` until every angle-bracket
placeholder has been resolved and the chosen licence exists at repository
root.

```yaml
version: "v0.4"
project:
  name: "Height-One Localized Descent for Finite Fixed Rings"
  description: >-
    A Lean formalization of a local commutative-algebra bridge for finite
    group actions on domains. It proves that height-one primes remain height
    one after contraction to subgroup-fixed rings and that, at a selected
    height-one prime, unramifiedness for an I-fixed ring descends to an
    H-fixed ring when I is contained in H, under the stated finite-module,
    Noetherian-base, and integrally-closed fixed-ring hypotheses. The
    fixed-inertia unramifiedness theorem itself is not formalized and remains
    an explicit hypothesis.
  authors:
    - "<HUMAN AUTHOR NAME>"
  license: "<CHOSEN SPDX IDENTIFIER>"
  responsible_maintainers:
    - "<HUMAN RESPONSIBLE MAINTAINER>"

classification:
  arxiv: [math.AC, math.AG]
  msc2020: [13A50, 13B21, 13B30, 13B40, 14E22]

sources:
  - title: "The Stacks Project, Lemma 15.112.8 (Tag 0BRI)"
    id: "Stacks-0BRI"
    location: "https://stacks.math.columbia.edu/tag/0BRI"
    relationship: adapts
    note: >-
      Supplies integrality of finite-group invariants and transitivity of
      primes over one contraction; the Lean proof combines these with lying
      over and going up to obtain the needed going-down statement.
  - title: "The Stacks Project, Lemmas 10.36.17 and 10.36.22 (Tags 00GQ and 00GU)"
    id: "Stacks-00GQ-00GU"
    location: "https://stacks.math.columbia.edu/tag/00GU"
    relationship: background
    note: "Lying over and going up for integral extensions."
  - title: "The Stacks Project, Lemma 10.119.7 (Tag 00PD)"
    id: "Stacks-00PD"
    location: "https://stacks.math.columbia.edu/tag/00PD"
    relationship: adapts
    note: >-
      The DVR criterion used after localizing a Noetherian normal domain at
      the contracted height-one prime.
  - title: "The Stacks Project, Lemma 58.12.4 (Tag 0BST)"
    id: "Stacks-0BST"
    location: "https://stacks.math.columbia.edu/tag/0BST"
    relationship: background
    note: >-
      Proves a stronger fixed-inertia etaleness theorem. It is not formalized
      here; the compared descent theorem retains its unramified consequence
      as the explicit hypothesis hI.

related_formalizations: []

status:
  scope: >-
    The compared declarations prove height-one contraction for finite fixed
    rings and, assuming a Noetherian base, a finite ambient algebra, normality
    of the target fixed ring, and the source unramifiedness premise, a
    selected-prime unramified descent theorem. They do not prove Stacks Tag
    0BST, global etaleness, a purity theorem, or any form of the Hodge
    conjecture.
  sorry_count: 0
  sorry_in_definitions: 0
  axioms: [propext, Quot.sound, Classical.choice]

automation:
  methods:
    - method: agent
      models: ["<EXACT MODEL OR PRODUCT DISCLOSURE>"]
      framework: "OpenAI Codex"
      tool_setup: "Agent-assisted Lean development with local compilation"
      prompting_notes: "<BRIEF ACCURATE SUMMARY OR POINTER TO A LOG>"
  spend_usd: "not tracked"
  notes: >-
    <DESCRIBE HUMAN DIRECTION, AGENT IMPLEMENTATION, AND SUBSEQUENT HUMAN
    CHECKING WITHOUT ATTRIBUTING HUMAN AUTHORSHIP TO AN AI SYSTEM.>

fidelity:
  divergences: >-
    Tag 0BST concludes etaleness for the actual inertia group. This
    formalization proves only selected-prime unramified descent after taking
    that fixed-inertia input as a hypothesis. It also exposes hypotheses in
    Mathlib's ring-theoretic vocabulary rather than claiming global etaleness.

review:
  status: "<HONEST STATUS, OR unchecked>"
  notes: "<WHAT WAS ACTUALLY CHECKED BEFORE SUBMISSION>"

alignment:
  namespace: "HodgeConjecture.Palomar"
  statements:
    - source: "Stacks Tags 0BRI, 00GQ, and 00GU"
      lean: "HodgeConjecture.Palomar.fixedPoints_heightOne_contraction"
      module: "Challenge"
      status: adapted
      note: >-
        A derived height-one contraction theorem for finite subgroup-fixed
        rings.
    - source: "Localized fixed-ring descent; Tag 0BST only as conditional background"
      lean: "HodgeConjecture.Palomar.heightOne_fixedRing_unramified_descent"
      module: "Challenge"
      status: partial
      note: >-
        The fixed-inertia unramifiedness conclusion is the explicit premise
        hI; the Lean result proves the subsequent subgroup descent.

acknowledgements: "Mathlib and The Stacks Project."
```

## Mechanical checks after migration

1. Build the proof development and both wrapper targets with `lake build`.
2. Re-run `#print axioms` on both Solution declarations.  On Lean 4.24 they
   use exactly `propext`, `Quot.sound`, and `Classical.choice`.
3. Validate `formalization.yaml` against v0.4 and confirm that no placeholder
   remains.
4. Run Comparator with `comparator.json`; Palomar will independently force
   NanoDa replay even though the checked-in config already enables it.
5. Confirm that no compiled artifacts are committed outside `.lake`, that
   every Git dependency is a credential-free public GitHub URL pinned to a
   full lowercase commit SHA in `lake-manifest.json`, and that the checked-out
   repository is below Palomar's size cap.

Policy sources checked on 2026-09-10:

- <https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md>
- <https://github.com/PalomarRegistry/PalomarTemplate>
- <https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json>
