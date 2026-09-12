import HodgeConjecture.Realization.Betti.Examples.SplitTateBlock
import HodgeConjecture.Realization.Betti.ZeroSimplexTransfer

/-!
# Constructed Betti realization

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
-/
