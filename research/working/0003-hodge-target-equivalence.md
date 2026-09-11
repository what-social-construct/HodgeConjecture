# Hodge target and graph-projector equivalence queue

Status: active working note; not a publication claim.

## Exact target

For a fixed smooth projective complex variety and codimension `p`, the target
is cycle-class surjectivity onto rational Hodge classes:

```text
for every α in H^(2p)(X, ℚ) ∩ H^(p,p),
  there exists z in CH^p(X)_ℚ with cl(z) = α.
```

This logical form is now represented by
`RationalHodgeConjectureAt` in `Realization/HodgeClasses.lean`.
`RationalHodgeConjectureForModel` quantifies over every codimension of one
modeled variety and uses cohomological degree `2 * p`;
`RationalHodgeConjectureForFamily` also quantifies over a supplied variety
index.  These are abstract schemas until the genuine Chow, cohomology, Hodge,
and variety-index data are constructed.

## Formal reformulation

For a class `α`, let

```text
e_α = [[1, 0], [α, 0]]
```

act on the underlying rational module of
`ℚ(-p) ⊕ H^(2p)(X, ℚ)`.  It is idempotent and its lower-left block recovers
`α`.

The formal arrows are

```text
α is algebraic
  -- ClassGraphProjectorConstruction --> e_α has an algebraic lift

e_α has an algebraic lift
  -- ClassGraphProjectorDetection --> α is algebraic.
```

Both arrows compile separately.  Together they give the pointwise and global
equivalences in `Realization/Chow/TateGraphProjector.lean`.  Neither interface
mentions Hodge membership, cycle-class surjectivity, or the desired
implication.

The Hodge-theoretic reading requires a third independent interface:

```text
α is a rational (p,p) class
  <-> e_α is a morphism of rational Hodge structures.
```

`ClassGraphProjectorHodgeCompatibility` names this law, using the convention
that `ℚ(-p)` has type `(p,p)` and weight `2p`.  The corresponding Lean iff is
proved for an explicit `IsHodgeMorphism` predicate, but no concrete Hodge
structure instance is present.

## Connection to the finite-Galois branch

`Realization/Chow/GaloisHodgeTarget.lean` proves the available one-way bridge:

```text
PrescribedChowProjectorLift χ E (projector α)
  + lower-left Chow-block detection
  -> α is algebraic.
```

`ClassIndexedFiniteCoverGraphCoverage` quantifies this supplied lift over
every rational Hodge class while allowing the extension package to depend on
the class; with detection it proves `RationalHodgeConjectureAt`.  It still
fixes the cover morphism, deck group and action, finite subgroup,
correspondence algebras, and realization model.  The abstract context does
not itself assume that `pX` is finite or étale.  No instance is constructed.

The reverse direction is not yet connected to the finite-cover branch.  It
would need more than the abstract graph-projector equivalence: an algebraic
class must factor through a compactified `E.Extension` with the required
generic restriction, and every Hodge class under consideration must occur in
the cover-generated image.  Hodge alone gives an arbitrary Chow lift and does
not imply this factorization, so finite-cover coverage may be strictly
stronger than the conjecture and may only hold for a named family or subspace.
`GraphProjectorLiftFactorizationThroughFixedDeckData` now gives this missing
arrow an exact Lean name for a supplied target predicate.  Applying it to the
rational Hodge classes, together with graph construction and detection, Lean
proves the conditional equivalence between
`RationalHodgeConjectureAt` and class-indexed prescribed coverage.  The
factorization itself remains open.

The marked-sheet construction gives a more precise route.  If `q` is the
base-sheet selector in `ℚ^(G/H)` and `E = ker(ev_base)`, multiplication by
`q` is `diag(1,0)` in selector/CRT coordinates and becomes

```text
(t, x) ↦ (t, t · (q - 1))
```

in constant-unit coordinates.  Lean proves both forms, their lower-shear
transition, and identification of the second operator with the canonical
Tate graph projector.  A residual linear map `θ : E → H^(2p)(X, ℚ)` sends
this to the graph projector of `θ(q - 1)`.

This last naturality is only rational linear algebra.  The substantive arrow
is to construct `θ` from the cover at the Chow-motivic level and prove that
its cohomological realization sends `q - 1` to the desired class.  Choosing
an arbitrary linear `θ`, or constructing it from an already known Chow
representative, would not advance the conjecture.

The conditional endpoint is now explicit in
`Realization/Chow/GaloisMarkedRealization.lean`.  It uses
`AlgebraProjectorExtension` to keep the commutative generic sheet algebra
separate from the possibly noncommutative compactified correspondence algebra
`Γ`.  Its comparison structure requires a compactified idempotent restricting
to `q`, a residual realization `θ`, `θ(q - 1) = α`, and a square intertwining
the compactified action with generic selector multiplication.  Evaluating
that square at `(1, 0)` identifies the lower-left class and lets detection
extract a Chow representative without surjectivity.  If `θ` is surjective,
cancellation and marked-block naturality derive the entire equality with
`e_α`, hence an algebraic graph-projector lift.

The class-dependent coverage schema fixes only `Γ` and its action.  For each
class it may choose a different finite group, subgroup, abstract extension
package and element, and residual comparison.  This avoids the false fixed-
commutative-algebra architecture, which would force every image projector to
commute even though distinct graph projectors do not.  Coverage by the
surjective witnesses implies the modeled fixed-codimension Hodge target.  No
witness is constructed, and the schema does not yet bundle an actual cover
or normal closure.  A separately named strong *replacement* assertion, not a
purported factorization of a chosen lift, is required for the conditional
reverse implication.

The flexible Galois coverage target must therefore have quantifier order

```text
∀ α, IsRationalHodgeClass M α →
  ∃ (Gα, coverα, Hα ≤ Gα, θα, Eα),
    θα(qα - 1) = α ∧ Eα is a compatible algebraic compactification.
```

The cover, group, marked stabilizer, residual realization, and extension may
all vary with `α`.  The existing fixed-deck coverage remains a useful special
case but does not express this dependent witness package.

## Execution queue

- [x] **H0. Target schemas.** State rational Hodge classes, algebraic classes,
  `RationalHodgeConjectureAt`, the one-model all-codimension target, and the
  indexed-family target without assuming surjectivity.
- [x] **H1. Canonical graph projector.** Construct `e_α`, prove idempotence,
  and prove lower-left recovery/injectivity.
- [x] **H2. Split equivalence.** Separate Chow graph construction from
  lower-left detection and prove both implications plus the pointwise/global
  iff.
- [x] **H3. Finite-cover implication.** Show that a prescribed finite-cover
  graph-projector lift yields an algebraic representative, define
  class-indexed extension coverage, and prove that coverage plus detection
  implies `RationalHodgeConjectureAt`.  Name the reverse arbitrary-lift
  factorization and prove the conditional iff under that explicit hypothesis.
- [ ] **H4. Concrete variety model.** Choose a named smooth projective complex
  variety or family and construct its rational Chow module, degree-`2p`
  cohomology, rational Hodge-class subspace, and cycle-class map.
- [ ] **H5. Tate-block Chow algebra.** Construct
  `End_Chow(ℚ(-p) ⊕ h(X))`, fix covariant/contravariant and opposite-algebra
  conventions, and derive `ClassGraphProjectorConstruction` and
  `ClassGraphProjectorDetection` from the biproduct and the relevant
  `CH^p`/Tate-Hom identification.  Do not assume an algebraic Künneth summand
  `h^(2p)(X)`.
- [ ] **H6. Hodge compatibility.** Construct the rational Hodge structures and
  prove `ClassGraphProjectorHodgeCompatibility` with the explicit Tate-twist
  convention.
- [x] **H7. Rational marked-block algebra.** Prove that the Tate graph
  projector is a shear-conjugate of `diag(1,0)` and a normalized `C₂`
  reflection average.  For the Galois sheet algebra, construct the
  selector/CRT and constant-unit decompositions, prove diagonal and graph
  forms of selector multiplication, identify their shear transition, and
  prove naturality under a residual rational linear map.
- [x] **H7b. Conditional marked-selector endpoint.** Separate the commutative
  generic sheet algebra from the noncommutative compactified correspondence
  algebra.  Package a compactified selector extension, residual realization,
  target-class equality, and action square.  Detect the lower-left class
  without surjectivity; under surjectivity derive the exact graph action and
  algebraic projector lift.  Do not count the package as a constructed
  geometric instance.
- [ ] **H8. Geometric residual realization.** For a named variety/family or
  Hodge subspace, construct a Chow-motivic map from the marked Galois residual
  block `Eα(-p)` to `h(X)` whose realization sends `qα - 1` to `α` and
  supplies the global-selector action square required by H7b.  Prove the
  needed surjectivity or replace it with a precisely scoped image argument.
  Do not use a pre-existing Chow representative of `α` in this construction.
- [x] **H9a. Abstract class-dependent coverage.** Introduce a universe-bounded
  witness in which the finite group, marked subgroup, residual realization,
  abstract compactified extension, and extension element may vary with `α`,
  while the ambient noncommutative correspondence algebra/action stays fixed.
  Prove that surjective witnesses for every rational Hodge class, plus
  lower-left detection, imply `RationalHodgeConjectureAt`.
- [ ] **H9b. Geometric flexible coverage.** Refine H9a by bundling a genuine
  finite cover or normal-closure datum and its maps to the generic sheet and
  compactified correspondence algebras.  Construct witnesses for a named
  family or subspace.  Retain the existing fixed-deck theorem as a separate
  specialization.
- [x] **H10a. Reverse assertion interface.** Name the strong assertion that
  an ambient graph-projector lift can be replaced by some class-dependent
  marked-selector witness, and prove the conditional iff using it.  Record
  that this is existence replacement, not a constructed factorization of the
  supplied lift.
- [ ] **H10b. Reverse generation theorem.** Prove H10a's replacement only
  where geometrically justified.  It may be stronger than Hodge for the
  chosen class of covers.
- [ ] **H11. Restricted partial result.** If H8--H10 hold only for a named
  proper subspace of rational Hodge classes or a named family, state
  algebraicity for exactly that subspace/family.
- [ ] **H12. Manuscript parity.** Add the classical target,
  graph-projector equivalence, marked Galois block comparison, and exact
  coverage quantifiers to a manuscript and release ledger before any
  Hodge-related publication claim.

## Current verdict

The repository now has exact abstract target schemas, an honest Tate-block
projector equivalence, and the Jacobian-style marked Galois block calculation.
Block diagonal versus graph-shaped is no longer a formal obstruction: the two
forms are proved to be different coordinates on the same selector action.  A
conditional theorem now detects the lower-left class from an explicit action
square and derives the exact graph action under a separate surjectivity
hypothesis.  The generic and noncommutative compactified algebras are no
longer conflated, and the formal coverage quantifiers may vary the finite
sheet data with the class.  The unresolved point is geometric and
non-circular: construct the extension, residual map, action square, and
detection from a genuine cover, then produce witnesses for a named family or
subspace.  Until that is done, the Galois branch establishes no new Hodge
case.
