module

public import HodgeConjecture.Realization.Betti.SmallSingularComparison
public import HodgeConjecture.Realization.Betti.CoverSmallCochains
public import HodgeConjecture.Realization.Betti.SubcomplexCochains
public import HodgeConjecture.Realization.Betti.AffineSingularRealization

@[expose] public section

/-!
# Rational small singular chains for arbitrary open covers

Actual singular simplices contained in either cover member form the small
simplicial subcomplex. Barycentric subdivision and its explicit local chain
homotopy are constructed on Mathlib's original rational singular chains.
The actual support shrinks uniformly on every finite chain, giving the
small-chain inclusion's homology comparison for arbitrary indexed open
covers. The two-open API specializes that proof and retains its native
complexes and public names. Exact rational dualization gives the actual
cochain restriction quasi-isomorphism; extension by zero makes it
degreewise surjective, and its existing relative kernel is acyclic.

The associated subcomplex cochains have an actual short exact gluing
sequence and connecting maps. The separate `SingularMayerVietorisMaps`
entry point constructs exact rational dualization and the full singular
cover sequence. Separate projective-line cohomology and boundary-period
entry points now compute actual H² and compare its positive boundary period.
General analytic/Gysin comparison remains a separate construction.
-/
