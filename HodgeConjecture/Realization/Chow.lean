import HodgeConjecture.Realization.Chow.GaloisProjector
import HodgeConjecture.Realization.Chow.GaloisHodgeTarget
import HodgeConjecture.Realization.Chow.GaloisMarkedBlock
import HodgeConjecture.Realization.Chow.GaloisMarkedRealization
import HodgeConjecture.Realization.Chow.Model
import HodgeConjecture.Realization.Chow.Presentation
import HodgeConjecture.Realization.Chow.SelectorRealization
import HodgeConjecture.Realization.Chow.TateGraphProjector
import HodgeConjecture.Realization.Chow.TransferProjector

/-!
# Rational Chow-correspondence realization

This umbrella module collects the noncommutative Chow-correspondence model,
its presentation by two-sided relation ideals, and its finite-cover/Galois
projector realization theorem.  It also retains the separate commutative
selector-generated realization used by the earlier clopen-selector branch,
the Tate-block graph-projector reduction connecting algebraic projector lifts
to the modeled rational Hodge cycle-class target, the rational-linear
comparison from the marked Galois residual block to that graph operator, and
the conditional lower-left and surjective-cancellation endpoints for a
compactified correspondence extending the marked selector.  The endpoint
requires an explicit residual realization and action square; it constructs
neither one geometrically.
-/
