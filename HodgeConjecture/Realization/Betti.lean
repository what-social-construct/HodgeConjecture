module

public import HodgeConjecture.Realization.Betti.Examples.SplitGaloisAction
public import HodgeConjecture.Realization.Betti.ZeroSimplexTransfer
public import HodgeConjecture.Realization.Betti.SingularPathConnected
public import HodgeConjecture.Realization.Betti.Examples.AffineLineComplexPoints
public import HodgeConjecture.Realization.Betti.ProjectiveLine
public import HodgeConjecture.Realization.Betti.SmallChains

@[expose] public section

/-!
# Constructed Betti realization

For path-connected spaces, actual paths and singular one-simplices prove
that degree-zero cocycles are constant. The complex affine line has the
topology of regular-function evaluations, proved homeomorphic to `ℂ`.
The actual projective-line complex points have the final affine-atlas
topology, proved homeomorphic to `OnePoint ℂ`. Singular cochains in every
degree use the original simplices and alternating faces; their H⁰ agrees
with the existing kernel construction. P¹'s singular H² computation and
positive-degree comparison remain open.
The small-chain development constructs actual barycentric subdivision,
its local homotopy, and finite-chain shrinking for a two-open cover.
The inclusion of the small singular subcomplex compares its rational
homology with the original singular complex. The small cochain gluing
sequence has a constructed connecting map; full-cochain dualization
and the sphere/projective-line calculations remain separate obligations.

The finite split complex example uses actual complex-algebra points with
their evaluation topology, actual continuous singular simplices and faces,
and degree-zero cohomology defined by the singular coboundary kernel.
The normalized point cycle-class map is a proved linear equivalence.

Continuous pullback, singular cup product, and finite transfer construct
the cohomological action. The transfer formula is also identified with the
sum over actual lifts of each zero-simplex. Cycle classes intertwine this
action with geometric Chow pull--intersection--push, yielding an algebra
homomorphism into the actual cohomology endomorphism algebra.

The finite degree-zero Hodge structure is specified on the genuine tensor
complexification, independently of cycle classes, with directness and
conjugation compatibility proved. Adding a distinguished scheme point
constructs the Tate block. Actual Chow pushforward and lower-left pullback
instantiate the graph construction, detection, and Hodge compatibility,
and prove the corresponding finite degree-zero Palomar target.

For homogeneous sheets of a constructed split finite-group torsor, the
residual map is an actual point-cycle construction followed by cycle class.
An invertible Chow shear realizes the constant-marked coordinate change,
and the full sheet-algebra action comparison is proved. The marked
selector's universal target square follows for the resulting negative
fundamental class.
-/
