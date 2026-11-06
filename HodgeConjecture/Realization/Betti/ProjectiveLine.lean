module

public import HodgeConjecture.Realization.Betti.SingularCochains
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineComplexPoints

@[expose] public section

/-!
# Independent topological inputs for projective-line Betti comparison

The original glued scheme has its actual complex-valued points and final
affine-atlas topology, proved homeomorphic to the native one-point
compactification of `ℂ`. Rational singular cochains are constructed in
every degree from actual continuous simplices and alternating faces.

This entry point provides the genuine singular H² target. It does not
compute that target or compare it with scheme de Rham H². The separate
`SmallChains` entry point proves the rational chain-homology cover comparison.
Full-cochain dualization and oriented normalization remain open.
-/
