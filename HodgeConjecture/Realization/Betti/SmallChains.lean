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
sequence and connecting maps. Comparing their cohomology with the full
singular cochains requires the separate rational dualization step; the
projective-line H² calculation and oriented period comparison remain open.
-/
