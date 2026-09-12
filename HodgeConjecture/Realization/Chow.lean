import HodgeConjecture.Realization.Chow.GaloisProjector
import HodgeConjecture.Realization.Chow.GaloisHodgeTarget
import HodgeConjecture.Realization.Chow.IdempotentRepresentation
import HodgeConjecture.Realization.Chow.MarkedAugmentedRealization
import HodgeConjecture.Realization.Chow.GaloisMarkedBlock
import HodgeConjecture.Realization.Chow.GaloisMarkedRealization
import HodgeConjecture.Realization.Chow.Model
import HodgeConjecture.Realization.Chow.Presentation
import HodgeConjecture.Realization.Chow.TateGraphProjector
import HodgeConjecture.Realization.Chow.TransferProjector
import HodgeConjecture.Realization.Chow.Examples.SplitPoints
import HodgeConjecture.Realization.Chow.Examples.SplitSpanRealization
import HodgeConjecture.Realization.Chow.Examples.GeometricSplitPoints
import HodgeConjecture.LinearAlgebra.MatrixRestrictionObstruction

/-!
# Rational Chow-correspondence realization

This umbrella module collects the noncommutative Chow-correspondence model,
its presentation by two-sided relation ideals, and its finite-cover/Galois
projector realization theorem, the Tate-block graph-projector reduction
connecting algebraic projector lifts to the modeled rational Hodge
cycle-class target, the rational-linear
comparison from the marked Galois residual block to that graph operator, and
the universal one-idempotent representation morphism, and the conditional
lower-left and surjective-cancellation endpoints for a
chosen correspondence, with extension-based selector comparisons retained
as stronger specializations. The endpoint
uses the augmentation ideal of the commutative sheet algebra and keeps the
residual cohomological realization linear.  Its universal-algebra formulation
exposes the projector homomorphisms without requiring a map from the whole
pointwise sheet algebra to the convolution algebra, or a restriction in the
reverse direction. It still requires an
explicit geometric residual realization and action square; it constructs
neither geometrically.  The auxiliary linear coset-average comparison remains
available by directly importing `Realization.Chow.SheetLinearization`, but is
not part of this active umbrella because pointwise and convolution products
differ.

The split-span realization now connects actual split-presentable geometric
classes to rational matrices by a surjective algebra map, killing geometric
coproduct and empty-span relations. The two-point comparison and target square
therefore have an actual scheme-span source. The coefficient model is not yet
identified with genuine Chow/cohomology, and no realization on all nonsplit
finite-étale classes is claimed. The matrix restriction obstruction
explains why the full ambient algebra cannot in general map back to sheets.

The superseded commutative selector-generated specialization remains
available by directly importing `Realization.Chow.SelectorRealization`; it is
intentionally absent from this active umbrella.
-/
