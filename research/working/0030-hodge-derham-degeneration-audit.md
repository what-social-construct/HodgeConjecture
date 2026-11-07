# Hodge–de Rham degeneration audit

Assessed: 2026-11-06. This is a proof-scope audit, not a new degeneration
theorem or a submission package. The general theorem at issue is
`E₁`-degeneration for a smooth proper scheme over a characteristic-zero
field; characteristic zero alone is not its full hypothesis.

Update, 2026-11-07: the bounded P¹ H² degree filtration is now constructed
and computed in the [0034 checkpoint](0034-projective-line-hodge-filtration.md).
Its F¹ inclusion is an actual derived isomorphism and F² is zero, over
every field. This does not construct the general Hodge spectral-sequence
pages or prove general E₁-degeneration. The general extraction decision
below is unchanged; no outside general-theorem submission copy was made.

## Current repository

The active library and archived Lean sources contain no construction of
the Hodge-to-de Rham spectral sequence or theorem asserting its general
`E₁`-degeneration. The pinned Mathlib provides generic spectral-sequence
machinery, but no general algebraic Hodge–de Rham degeneration theorem.

The nearest proved statements here are in
[ProjectiveLineSchemeComparison.lean](../../HodgeConjecture/Realization/DeRham/ProjectiveLineSchemeComparison.lean):

- `ProjectiveLineDeRham.schemeH2IsoSheafH1 k` identifies actual degree-two
  scheme de Rham hypercohomology of the original glued P¹ with actual
  derived global sections `H¹(Ω¹)`.
- `ProjectiveLineDeRham.schemeResidueEquiv k` identifies that actual
  degree-two target linearly with `k`, with the original Chern coordinate
  sent to one.

Both statements require only `[Field k]`; their existing checks use the
standard-three axiom allowlist. A fresh direct Lean check of both aliases
and their axiom reports passes with only `propext`, `Classical.choice` and
`Quot.sound`. These are bounded computations and derived
comparisons. The Hodge filtration, its spectral-sequence pages and the
vanishing of all higher differentials are not formalized by those
statements. They should not be renamed or packaged as the general
characteristic-zero degeneration theorem.

## Pinned Axiom Stacks reference

The audited external source is AxiomMath/Stacks revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`, recorded in
[the provenance file](../../third_party/axiom-stacks/README.md). It is a
proof reference, not a dependency of this repository.

The upstream
[characteristic-zero spreading-out theorem](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/DeRham/HodgeSpreadingOut/CharZero.lean)
is named
`AlgebraicGeometry.HodgeSpreadingOut.sum_hodgeNumbers_eq_deRhamBetti_of_charZero`.
For a proper smooth `f : X ⟶ Spec k`, with `[Field k] [CharZero k]`, it
proves equality of the Hodge-number sum and the de Rham dimension in every
degree **from an explicit hypothesis `hDI`**. That hypothesis supplies the
corresponding dimension equality for proper smooth schemes over finite
fields, with the required higher-form vanishing and proper smooth lift to
length-two Witt vectors. The proof applies `hDI` to its chosen special
fiber. Its documentation explicitly identifies this as the Deligne–Illusie
input, unproved in that module. No use elsewhere in the pinned source
discharges the argument to obtain a closed general endpoint.

The upstream
[numerical degeneration criterion](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/DeRham/HodgeWeil/Degeneration.lean)
`Stacks.HodgeWeil.degeneratesAt_one_iff_finrank_deRham_eq_sum_hodge`
is an equivalence between degeneration and that dimension equality, for
an actual abutting Hodge spectral sequence with finite-dimensional Hodge
groups. It does not establish the equality for all smooth proper schemes.

The separate upstream
[Weil-theory consequence](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/DeRham/HodgeWeil/HodgeWeilCohomologyTheory.lean)
`Stacks.HodgeWeil.degeneratesAt_one_of_finrank_grade_eq` has an explicit
`hbetti` premise asserting independence of Betti dimensions across Weil
cohomology theories. This is a proved conditional implication, rather than
an unconditional proof of the desired general degeneration theorem.

The upstream projective-space computation is a further bounded result;
it does not remove these general-theorem hypotheses. The reductions above
are mathematically useful, but their remaining inputs must stay visible.

## Extraction decision

No outside submission copy was created: the requested condition, an
already completed general degeneration proof in this repository, is not
met. A separately scoped P¹ comparison submission would require its own
statement and preparation; it would not be a duplicate of a general
Hodge–de Rham degeneration theorem.
