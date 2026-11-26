# The connected branched square cover of P¹ (2026-11-26)

The cover is the actual scheme selfmap `[u:v] ↦ [u²:v²]` of the existing glued
projective line. Its source is connected. The map is finite, flat, surjective
and has geometric rank two. This is a branched cover: over zero and infinity
there is one underlying point, with original local fiber multiplicity two.
It is not étale. The original ordinary Chow groups and independently defined
full Hodge target are retained.

`CommutativeAlgebra/PolynomialSquare.lean` proves the actual coordinate map
`T ↦ X²` finite free of rank two by even/odd coefficient extraction, with basis
`1,X`. A target type copy keeps the square-algebra action distinct from the
regular self-algebra action. The coordinate origin ideal maps to `(X²)`.
Its quotient has length two over the base field and a nonzero square-zero
root. These coordinate facts are separate from the scheme multiplicity proof.

`Geometry/ProjectiveLineSquare.lean` glues the two actual affine square maps
using the Laurent overlap. Its chart diagrams are actual pullback squares.
The resulting scheme morphism is finite flat and has rank two at every point.
It preserves the original base structure morphism, fixes zero and infinity,
and has unique underlying preimages at those branch points. Its canonical
complex-point map is the original map induced by that scheme morphism.

`Realization/Betti/Examples/CircleSquare.lean` computes native singular H¹
pullback for the actual circle map `z ↦ z²`. Literal angular singular triangles
prove the cocycle addition law, and the original positive-loop pairing detects
the factor two. No Chow groups or Hodge coordinates enter this computation.

`Realization/Betti/SingularMayerVietorisNaturality.lean` constructs a morphism
of the original restriction/difference short exact cochain sequences for a
continuous map respecting two covers. Native connecting naturality, the
original small-cochain comparison and the actual intersection subtype map
prove naturality of the existing full-singular boundary.

`Realization/Betti/ProjectiveLineSquarePullback.lean` binds the actual scheme
square map to the existing P¹ point model and the canonical scheme complex
points. It preserves the original two-open cover. The inverse circle inclusion
in their overlap intertwines the two square maps. The circle H¹ computation
and the original Mayer–Vietoris connecting isomorphism prove that actual native
H² pullback is twice identity. This proof is independent of Chow classes.

`Realization/Betti/ProjectiveLineSquareGysin.lean` constructs a limited supported
trace. Restrict the actual square map to its fixed singleton zero support.
This map is a homeomorphism, so inverse native H⁰ pullback gives its support
transfer. Transport through the existing oriented zero-point Gysin isomorphism
`H⁰({0}) ≅ H²(P¹)` defines the supported trace. It is proved identity after
construction, and its composition with the independently computed native
pullback is twice identity. This is a singleton-supported degree-two trace;
general proper or branched trace and arbitrary point-Gysin naturality remain
open. The singleton is a native topological support, not a newly constructed
reduced subscheme.

`Realization/Chow/ProjectiveLineSquare.lean` retains the source Chow quotient
with the exact composite structural morphism. Its proved equality with the
original base structure gives a representative-preserving grading equivalence.
The actual original finite pushforward preserves degree: closed-point residue
degrees are one over the algebraically closed base, proved using actual scheme
sections. Original finite flat push–pull and geometric rank two then prove
that original pullback doubles degree. Actual weighted fiber degree, unique
branch preimages and residue degree one compute the original local
multiplicities two. This does not assume a normal-form theorem for CH₀.

`Realization/DeRham/ProjectiveLineSquareCoverage.lean` uses the original P¹ cycle
map with only the proved source-grading transport. Both original Chow/native
comparison squares hold. The actual original flat pullback of the ordinary
infinity class supplies the column of the unchanged full Hodge target.
Half its original finite pushforward recovers that same infinity class.
The existing exact aggregate accepts the identity matrix, denominator one and
modulus three. No new classical Hodge-conjecture case, general prescribed-class
construction, byte codec or cryptographic backend is asserted.

The parity table and manuscript proposition `prop:p1-square-aggregate` record
the same maps and scope. Provenance: local proofs and existing project/pinned
Mathlib APIs; no new external source copy, package dependency or license input.

Validation on 2026-11-26: `make check-p1-square-cover` passes 18
controls, 67 enforced standard-three axiom audits and all 146 import guards.
The controls retain the actual composite source grading and original maps,
separate singleton fibers from multiplicity two, compute the actual nilpotent
coordinate quotient, bind the native scheme map, reject an unnormalized
column and a degree-one transfer, and accept the unchanged full target.
All three realization exports pass serialized integration builds. The complete
public-library build `lake build HodgeConjecture` passes 5,430 jobs.
The root inventory passes 2,351 declaration checks and 574 examples, with
1,858 nonempty standard-three axiom reports and 1 axiom-free report.
All 759 active library/root/Solution sources pass proof-gap scanning;
intentional Challenge statement placeholders remain separate. Dependencies
and source pins are unchanged. Local document links, whitespace, 155 unique
manuscript labels and 178 resolved manuscript references pass inspection.
The canonical 112-page PDF rebuilds without overfull boxes, undefined
references or LaTeX errors. Pages 9–10 and 83–84 pass rendered visual review.
Only existing Lean style/deprecation notices and one bibliography underfull
notice remain. This is cached working-tree validation; clean-clone and human
release sign-offs remain separate.

Canonical manuscript source SHA-256:
`fdc1f709174bec327eb88fc6bbb8e70241c7143a6a48a119e441b87143fccfa5`.
Canonical PDF SHA-256:
`4b3226bac661e3c071b6d6ea60f7f54b95271727415bd35213218a43d9a65c6a`.
