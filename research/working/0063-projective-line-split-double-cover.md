# The actual split double cover of P¹ in native H² (2026-11-26)

The cover is the actual scheme fold `P¹ ⨿ P¹ ⟶ P¹`, restricting to the
identity on both original projective-line components. This is a disconnected
positive-dimensional example. The downstairs ordinary Chow group, original
cycle map, independently defined Hodge target and full basis are retained.
The upstairs structure morphism is exactly the fold followed by the original
P¹ structure morphism.

`Geometry/SplitDoubleCover.lean` proves the generic fold finite, étale, flat,
surjective and of geometric rank two at every point. The rank calculation
uses the actual affine product-ring presentation and original flat-rank base
change. Actual fold stalk maps are isomorphisms. The original upstairs scheme
retains Noetherianity whenever the base scheme is Noetherian.

`Geometry/ComplexPointsCoproduct.lean` identifies the canonical analytic
complex points of an actual scheme coproduct with the topological disjoint
union of the component spaces. The forward map is induced by the two original
open scheme inclusions. Its proof uses the original analytic maps and their
proved open-embedding ranges, retaining the exact supplied structure map.

`Realization/Betti/SingularDoubleCover.lean` constructs the split transfer on
the original singular cochain complexes. A singular simplex lies in one
component by connectedness of the standard simplex. Extension by zero commutes
with the original coboundary, and the two extensions and restrictions reassemble
every original cochain. Their induced maps give native cohomology decomposition
in every degree. Fold pullback is diagonal; transfer is the sum of the two
actual inclusion pullbacks. These maps satisfy push–pull equals twice identity
already on the original construction, independently of chosen cohomology
coordinates or Chow groups.

`Realization/Betti/SplitDoubleCover.lean` transports that decomposition through
the canonical analytic coproduct homeomorphism to the actual scheme-valued
complex points. Its transfer is also proved to be induced by the sum of the
two original scheme-inclusion cochain pullbacks. It supplies a degree-two
`RationalDegreeTransfer` on the native singular groups in every degree.

`Realization/Chow/SplitDoubleCover.lean` decomposes the original rational
Chow quotient with the actual structural grading upstairs. Its components
are the original clopen restrictions, with proved grading identifications;
its inverse is the sum of original closed-inclusion pushforwards. All laws
retain actual cycle representatives and principal-divisor relations. These
relations need not vanish in this positive-dimensional example. Original
finite flat fold pullback becomes diagonal, and original finite fold
pushforward sums the two components. The actual local fiber multiplicities
are one, using the proved fold stalk isomorphisms.

`Realization/DeRham/ProjectiveLineDoubleCoverCoverage.lean` keeps the original
P¹ Hodge-cycle model and complete basis. Its upstairs cycle map is uniquely
determined by requiring its restrictions to agree with the two original P¹
cycle maps, through the independently constructed native Betti decomposition.
Both comparison squares for the original Chow maps and native singular maps
hold. The native upstairs H² has dimension two; the fixed downstairs Hodge
target has dimension one and its original geometric type (1,1).

The selected upstairs cycle is the actual flat pullback of the original
ordinary infinity class. Its native components are both the original P¹
generator. Normalized geometric pushforward recovers that same infinity
class. The existing aggregate adapter accepts the rank-one identity matrix,
denominator one and modulus three, proving coverage of the same fixed full
target through the positive-dimensional geometric cover.

This does not construct a connected cover, a ramified trace, a general Gysin
map or prescribed-class generation for other varieties. A connected degree-two
P¹ selfmap would be a branched finite-flat example requiring further geometry
and native cohomological comparison. No new classical Hodge-conjecture case,
cryptographic backend or byte codec is asserted.

Provenance: local proofs and existing project/pinned Mathlib APIs; no new
external source copy, package dependency or license input.

Validation on 2026-11-26: `make check-p1-double-cover` passes 14
controls, 51 enforced standard-three axiom audits and all 139 import guards.
The controls include the two native component generators, failed diagonal
generation by one component, failed unnormalized binding, and a nonzero
anti-diagonal class killed by original Chow and native cohomological push.
The complete public-library build `lake build HodgeConjecture` passes
5,421 jobs. The root declaration inventory passes with 1,858 nonempty
standard-three axiom reports and 1 axiom-free report. All 751 active
library/root/Solution sources pass proof-gap scanning; intentional Challenge
statement placeholders remain separate. The pinned dependencies are unchanged.
Changed-document links, unique manuscript labels and whitespace checks pass.
The canonical 111-page manuscript rebuilds without overfull boxes,
undefined references or LaTeX errors. Its new proposition, construction and
declaration crosswalk pass rendered visual review. Nonblocking
Lean style/deprecation warnings and one existing bibliography underfull-box notice
remain. This is cached working-tree validation; clean-clone and human release
sign-offs remain separate.
