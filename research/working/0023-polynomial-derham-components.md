# Polynomial degree-zero de Rham cohomology and affine components

Date: 2026-11-05. Lean 4.35.0 and the existing dependency pins are retained.

## Constructed calculations

`Realization/DeRham/Polynomial.lean` computes the actual closed-function
kernel after adjoining a polynomial variable. For a commutative `k`-algebra
`A` with `HasUniqueDiv A` (no additive torsion), forgetting coefficient
differentials shows that a closed polynomial has zero ordinary derivative.
The coefficient calculation then makes it constant, and evaluation recovers
its original closed coefficient. Thus the original algebra maps give

```text
polynomialCoordinates : H0 k A[X] ≃ₐ[k] H0 k A.
```

The coefficient algebra need not be a field, a domain or reduced. Every
commutative rational algebra has the required additive torsion-freeness.
`polynomialCohomologyZeroIso` transports this calculation to categorical
degree-zero homology of the constructed complexes. All point evaluations
agree on closed polynomials. Iterating computes, for example, the degree-zero
kernel of the affine plane over a characteristic-zero field.

`Realization/DeRham/AffineComponents.lean` treats the finite product ring
`I → k[X]`, the coordinate ring of disjoint affine lines. Pullback by the
original component evaluations detects each constant polynomial. The
original componentwise inclusion supplies the inverse, proving

```text
affineLinesCoordinates : H0 k (I → k[X]) ≃ₐ[k] (I → k).
```

The transported standard basis is the actual component characteristic
functions, proved idempotent. Over a characteristic-zero field the dimension
is `Fintype.card I`, including the empty product. A separate proof establishes
that every coordinate-ring idempotent is closed, in all characteristics and
without a reducedness assumption. This asserts no convolution idempotence.

## Scope and dependencies

These are direct local proofs using Mathlib's existing polynomial/Kähler
constructions and the existing project complex. They do not import an
external Stacks package or assume a theorem from the supplied papers.
The component perspective is motivated by the
[reviewed references](../SOURCE_LEDGER.md#further-de-rham-references-2026-11-05);
their degree bounds and nonreduced examples are not formalized here.

This is degree-zero algebraic polynomial invariance, not general nilpotent
invariance. It preserves the entire original closed-function kernel rather
than replacing it by a reduced quotient. The characteristic-two regression
exhibits a nonconstant closed square, so the torsion-freeness hypothesis is
substantive. Higher de Rham cohomology, positive-dimensional Betti/cycle
comparison and prescribed-Hodge-class generation remain open.

## Focused verification

`make check-derham-components` builds the new algebraic entry point and runs
`research/DeRhamComponentsVerification.lean`. The import guard enforces the
same geometry/Chow/Betti exclusions as the existing core. Its project closure
has five modules; the original six-module core is unchanged. The new modules
are also exported through `Realization.DeRham` and checked by the root-import
inventory.

The seven regressions cover arbitrary rational coefficient algebras without
reducedness assumptions, the affine plane, distinct basis components,
three-component dimension, the empty product, evaluation independence and a
nonconstant closed square in characteristic two. Fifteen declarations have
enforced standard-three axiom audits.

The final focused build passes 2,349 dependency jobs and all seven examples
and 15 audits. The existing comparison suite passes another 25 enforced
audits after its 3,561-job build. The complete default build passes 4,174
jobs, and the root inventory passes 1,264 declaration checks, 565 examples
and 1,156 axiom reports. All reported axioms are among `propext`,
`Classical.choice` and `Quot.sound`; one root report needs no axioms.
These job counts include cached dependencies. All 385 production modules
pass the proof-token/import scan. Import boundaries and their indirect
negative test, exact dependency pins, local links and whitespace checks pass.
The main README remains 69 lines. Existing release sign-offs are unchanged.
