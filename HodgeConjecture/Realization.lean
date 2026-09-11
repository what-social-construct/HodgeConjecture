import HodgeConjecture.Realization.BoundaryProjector
import HodgeConjecture.Realization.Chow
import HodgeConjecture.Realization.CohomologicalProjector
import HodgeConjecture.Realization.CompactificationProjector
import HodgeConjecture.Realization.HodgeTarget

/-!
# Realization stage

This umbrella module collects the correspondence, compactification, Chow,
and cohomological interfaces that turn an extended scheme-theoretic
idempotent into a realized projector.  The Galois-Chow endpoint uses a
generally noncommutative convolution algebra and requires equality with a
prescribed cohomological projector, rather than defining the target from the
constructed action.  Raw correspondence algebras may be presented by
two-sided relation ideals in the dedicated `Realization.Chow` sublayer.

`Realization.HodgeTarget` separately states fixed-model and indexed-family
rational Hodge schemas as cycle-class surjectivity and proves their canonical
Tate-block graph-projector reformulations under explicit construction and
detection maps.  The Hodge-morphism reading has its own compatibility
interface.  A marked Galois-sheet calculation identifies selector
multiplication with a Tate graph operator after a rational change of
coordinates.  A conditional realization theorem separates the generic sheet
algebra from the noncommutative compactified correspondence algebra, detects
the lower-left class from an explicit comparison square, and obtains the
exact target action by surjective cancellation.  No Chow-motivic residual
realization or such square is constructed.  The finite-cover branch has not
been identified with the full target; only implications from explicit
class-indexed witness packages are formalized.
-/
