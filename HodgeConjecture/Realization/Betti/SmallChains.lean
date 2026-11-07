module

public import HodgeConjecture.Realization.Betti.SmallSingularComparison
public import HodgeConjecture.Realization.Betti.SubcomplexCochains
public import HodgeConjecture.Realization.Betti.AffineSingularRealization

@[expose] public section

/-!
# Rational small singular chains for a two-open cover

Actual singular simplices contained in either cover member form the small
simplicial subcomplex. Barycentric subdivision and its explicit local chain
homotopy are constructed on Mathlib's original rational singular chains.
The actual support shrinks uniformly on every finite chain, giving the
small-chain inclusion's homology comparison for a two-open cover.

The associated subcomplex cochains have an actual short exact gluing
sequence and connecting maps. The separate `SingularMayerVietorisMaps`
entry point constructs exact rational dualization and the full singular
cover sequence. Separate projective-line cohomology and boundary-period
entry points now compute actual H² and compare its positive boundary period.
General analytic/Gysin comparison remains a separate construction.
-/
