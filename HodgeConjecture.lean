import HodgeConjecture.Collision
import HodgeConjecture.Correspondence
import HodgeConjecture.Boundary
import HodgeConjecture.Realization

/-!
# Collision decompositions and correspondence projector lifting

The root library follows the five-stage construction:

1. collision ideals and scheme decomposition;
2. scheme correspondences, the finite étale admissible algebra,
   Galois graph sheets, averaging projectors, and algebraic projector
   targets;
3. boundary normalization, inertia averaging, purity-controlled extension,
   and compactified algebraic projector lifts;
4. noncommutative Chow-correspondence realization of prescribed
   cohomological projectors and diagonal decompositions;
5. the abstract rational Hodge cycle-class target and its Tate-block
   graph-projector reformulation, together with the marked Galois-sheet block
   calculation, under explicit construction and detection maps.

The second stage deliberately separates the formal span algebra from its
eventual Chow realization.  Thus a clopen component selector is not silently
treated as a convolution projector.  The marked-sheet calculation identifies
selector multiplication with a graph operator only after an explicit change
of linear coordinates.  A conditional endpoint keeps the generic sheet
algebra separate from a noncommutative compactified correspondence algebra;
it detects the target class from an action-intertwining square and derives the
whole target operator when the residual realization is surjective.  It does
not construct those data geometrically.  Likewise, the fifth stage does not
claim that the current finite-cover family supplies every Hodge-class graph
projector or instantiate the abstract target for a concrete variety.
-/
