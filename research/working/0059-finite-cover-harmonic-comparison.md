# Finite harmonic comparison from the original covers (2026-11-26)

The rational finite complex has two chart coordinates and two overlap-component
coordinates, with differential `(a,b) ↦ (a-b,a-b)`. Its differential is nonzero.
The cellular real realization uses the same incidences and one-dimensional
stalks, and literal rational-to-real coefficient inclusion intertwines the
two differentials.

`CircleCoverHarmonicComparison.quotientCircleEquiv` identifies the native
finite quotient with the original circle singular H¹ through the actual
Mayer–Vietoris boundary. Its forward-map theorem retains that boundary;
`witness_componentBoundary` proves the harmonic projection square. The jump
functional is invariant under projection and proves witness injectivity.

`ProjectiveLineCoverHarmonicComparison.quotientBettiEquiv` composes this
with the original radial pullback, original projective-line connecting
isomorphism, and canonical scheme-point homeomorphism. It computes actual
canonical rational Betti H². The component step retains the existing
positive cover generator, and `witness_canonicalCycleClass` compares with
the original ordinary Chow map.

`ProjectiveLineCoverHodgeComparison` transports the existing actual scheme
Hodge filtration through this rational cover equivalence, using native
complexification and canonical conjugation. Its Hodge-target membership
criterion retains the independently defined geometric target. The finite
cycle map is ordinary Chow degree followed by the component-step quotient;
`finiteCycleClass_commutes` proves that its Betti image is the original
ordinary cycle map.

The manuscript proposition `prop:p1-cover-harmonic-comparison` represents
these maps. Focused validation is `make check-cover-harmonic-comparison`:
three controls and twenty enforced standard-three axiom audits. The pure
circle comparison and the separation of the Betti and de Rham branches
have explicit import guards.

This is a bounded P¹ result. The general geometric finite-model comparison,
intrinsic analytic harmonic operators, proper/purity comparisons and
prescribed-class cycle generation remain open. The real metric is the
finite cover metric, and the finite quotient's Hodge filtration is the
transport of the existing geometric filtration.

## Working-tree validation (2026-11-26)

- `lake build HodgeConjecture` passes (5,396 jobs), including the public
  harmonic and geometric-comparison exports.
- `lake env lean research/Verification.lean` passes. All 1,858 printed
  axiom lists stay within `propext`, `Classical.choice`, and `Quot.sound`.
- `make check-harmonic-witness check-cover-harmonic-comparison` passes:
  43 enforced axiom audits, six controls, and 124 import boundaries.
- The 730 active library/root/solution sources have no proof-gap tokens;
  the two intentional `Challenge.lean` statement placeholders are separate.
- The 104-page canonical manuscript builds with no overfull boxes or
  undefined references. The changed theorem, comparison, source and
  crosswalk pages were rendered and visually checked.
- Documentation links and whitespace checks pass. Clean-clone validation
  and human release sign-offs retain their separate scope.
