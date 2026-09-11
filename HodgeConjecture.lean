import HodgeConjecture.Collision
import HodgeConjecture.Correspondence
import HodgeConjecture.Boundary
import HodgeConjecture.Realization

/-!
# Collision decompositions and correspondence projector lifting

The root library exports the active five-stage construction:

1. collision ideals and scheme decomposition;
2. scheme correspondences, the finite étale admissible algebra,
   Galois graph sheets, averaging projectors, and algebraic projector
   targets;
3. marked sheets, normalization, inertia, and the conditional codimension-one
   boundary endpoint;
4. raw closure-defect calculus and the supplied compactified deck-graph route;
5. noncommutative correspondence realization and the abstract rational Hodge
   target's Tate-block graph-projector reformulation, under explicit
   construction, detection, comparison, and coverage inputs.

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

Height-one fixed-ring localization and the valuation/prime-inertia comparison
form a supporting branch inside `Boundary.Normalization`; they do not replace
the compactification, Chow, or residual-realization inputs.  Historical
commutative selector and broad normalization-triviality prototypes remain
directly importable but are not re-exported by the active umbrellas.
-/
