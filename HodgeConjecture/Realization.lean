module

public import HodgeConjecture.Realization.Chow
public import HodgeConjecture.Realization.Betti
public import HodgeConjecture.Realization.HodgeTarget
public import HodgeConjecture.Realization.DeRham

@[expose] public section

/-!
# Realization stage

This umbrella module collects the active noncommutative correspondence,
Chow, and cohomological interfaces that turn a compactified idempotent into a
realized projector.  The Galois-Chow endpoint uses a
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
algebra from the noncommutative compactified correspondence algebra and
exposes the comparison as a morphism of representations of the universal
one-idempotent algebra.  It detects the lower-left class from the selector
square and, by surjective cancellation, proves the exact target equality of
algebra-homomorphism composites. No such residual realization or action square
is constructed for a general variety. The finite split specialization below
constructs both; its canonical marked residual class is minus the fundamental
class. The finite-cover branch has not
been identified with the full target; only implications from explicit
class-indexed witness packages are formalized.

`Realization.Betti` constructs canonical complex point spaces and their
rational singular cohomology functor for schemes over ℂ. Affine and P¹
models are identified with these spaces by proved homeomorphisms; the
existing P¹ period and purity computation uses this canonical target.
General geometric comparison and purity remain separate obligations.
It also constructs the finite split complex degree-zero case:
actual complex points, singular cohomology, the normalized cycle-class
isomorphism, and the cohomological action of the actual Chow algebra.
Its compatibility with geometric Chow action is proved. Higher-dimensional
Betti/Hodge realization and the general residual comparison remain separate.

The earlier commutative selector-realization chain is preserved under
`research/archive/legacy-lean/`, outside the library. The retained block
calculations certify operator identities; they do not supply the general
geometric realization or class-dependent coverage hypotheses.
-/
