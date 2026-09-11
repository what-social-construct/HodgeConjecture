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
compactified correspondence extending the marked selector.  The endpoint
uses the augmentation ideal of the commutative sheet algebra and keeps the
residual cohomological realization linear.  Its universal-algebra formulation
exposes the projector homomorphisms without requiring a map from the whole
pointwise sheet algebra to the convolution algebra.  It still requires an
explicit geometric residual realization and action square; it constructs
neither geometrically.  The auxiliary linear coset-average comparison remains
available by directly importing `Realization.Chow.SheetLinearization`, but is
not part of this active umbrella because pointwise and convolution products
differ.

The superseded commutative selector-generated specialization remains
available by directly importing `Realization.Chow.SelectorRealization`; it is
intentionally absent from this active umbrella.
-/
