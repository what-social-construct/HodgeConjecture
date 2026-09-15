import HodgeConjecture.Collision
import HodgeConjecture.Correspondence
import HodgeConjecture.Boundary
import HodgeConjecture.Realization
import HodgeConjecture.Inputs

/-!
# Collision decompositions and correspondence projector lifting

The root library exports five related proof components, not a completed
composite proof of the Hodge conjecture:

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
it presents the selector comparison as a morphism of representations of the
universal one-idempotent algebra, detects the target class from its selector
square, and derives the Palomar-style equality of algebra-homomorphism
composites when the residual realization is surjective. Those data are now
constructed for homogeneous sheets of a split finite-group torsor: the
residual map is an actual point-cycle construction and the coordinate shear
is an invertible Chow correspondence. The finite split degree-zero Hodge
target is also instantiated using actual singular cohomology. These concrete
checkpoints do not assert that the finite-cover family supplies every
Hodge-class graph projector for general varieties.

Height-one fixed-ring localization and the valuation/prime-inertia comparison
form a supporting branch inside `Boundary.Normalization`; they do not replace
the compactification, Chow, or residual-realization inputs. The block and
shear calculations are supporting coordinate identities, not constructions
of algebraic representatives for prescribed Hodge classes. Historical
commutative selector and broad normalization-triviality prototypes are
preserved under `research/archive/legacy-lean/`, outside the Lean library.

`Inputs` collects the selected literature conclusions as explicit local
hypotheses. Their conditional consumers construct finite-étale extension
data and lifted deck actions, or raw Chow lifts and boundary-image defects,
without assuming geometric realization or class-dependent coverage.
-/
