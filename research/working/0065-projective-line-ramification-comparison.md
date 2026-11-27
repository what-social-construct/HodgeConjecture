# Actual relative Thom and ramified point-Gysin comparison (2026-11-26)

The original square map now has a local-to-global ramification comparison at
zero. The native relative Thom class pulls back to twice itself. The same
coefficient is the actual scheme-fiber multiplicity in the original ordinary
zero-cycle pullback. The comparison uses the original normal chart, excision,
support forgetting and cycle map, retaining the same independent full Hodge
target. It supplies a new zero-point aggregate through this local proof route.

`Realization/Betti/RelativeCochainsNaturality.lean` proves identity and composition
for the original maps of vanishing-cochain kernels. Its native homology maps
commute with original forgetting. The actual contained-simplex comparison
commutes with a supplied genuine subtype map and its inclusion square; the
original relative boundary retains that naturality. No geometry or Chow
module is used by this generic layer.

`Realization/Betti/Examples/ComplexSquareThom.lean` constructs the actual square
on the complex line and its punctured complement. Actual circle inclusion
intertwines the two square maps. The existing angular singular-triangle proof
and native circle pairing give punctured-plane H¹ pullback by two. Naturality
of the original relative connecting isomorphism then gives multiplication by
two on actual H²(ℂ,ℂ\{0}), in particular on its original positive Thom class.
The actual singleton H⁰ pullback is identity. Consequently the unweighted
Gysin pullback square fails. This calculation uses no P¹, Chow or old global
square-map cohomology theorem.

`Realization/Betti/ProjectiveLineSquareRamification.lean` acts on the actual
P¹ relative pair with the zero point removed. Relative restriction along the
original finite chart is proved equal to the original excision restriction
followed by the original normal-chart comparison. The original cochain square
intertwines global and local square maps in every degree. Its native homology
square transports the independent local result to the original supported
Thom class. Original support forgetting gives the absolute ramified Gysin
formula. The geometric point-Gysin isomorphism then gives absolute H²
pullback by two and the degree-transfer law through this local proof route.

`Realization/Chow/ProjectiveLineSquareRamification.lean` starts with the original
reduced scheme-zero cycle and its original rational Chow class. Original
finite-fiber pullback is computed on actual cycle coefficients, with the
actual local multiplicity as weight. The corresponding original quotient
identity follows by retaining those same cycle representatives and the proved
structural grading transport. No Chow-degree injectivity is assumed. The
complex algebraic-closedness instance is imported explicitly from pinned
Mathlib, independently of Betti modules.

`Realization/DeRham/ProjectiveLineRamificationComparison.lean` binds both Gysin
formulas and the actual zero-cycle coefficient to the same original local
scheme-fiber multiplicity. In this fully ramified fiber it equals global
geometric rank two. The new transfer's degree is that actual multiplicity;
its law comes from the new relative proof. The independently defined Hodge
model, full basis, ordinary cycle map and identity arithmetic modulo three
are retained. The aggregate column proof consumes both the actual weighted
zero-cycle formula and the local-to-global native degree result. Half the
original geometric pushforward of the selected actual flat pullback recovers
the same ordinary zero class.

The singleton is a topological support. The reduced scheme-point square
commutes but is not claimed cartesian: the actual zero fiber is nonreduced
of length two. This is a ramification-corrected comparison at the distinguished
zero point. General point transport, coordinate independence, higher
codimension Gysin, general proper/branched trace and prescribed classes on
other varieties remain open. No new Hodge-conjecture case, cryptographic
backend or byte codec is claimed.

The parity table and manuscript proposition `prop:p1-square-ramification`
record the same objects. Provenance is local proofs and existing project/pinned
Mathlib APIs; no external source copy, package dependency or license input.

Validation on 2026-11-26: `make check-p1-ramification` passes 17 controls,
59 enforced standard-three axiom audits and all 150 import guards. The three
checked proof closures exclude all three earlier global-square H² results
and every declaration originating in the earlier square-cover aggregate,
including private/generated declarations. Final acceptance contains all five
required dependencies: the new local relative calculation, original relative
boundary naturality, actual chart/excision naturality, raw weighted zero-cycle
pullback and its original Chow quotient identity. These audit the current
formal proof route, rather than asserting minimal mathematical assumptions.
The controls reject the unweighted Gysin formula, reversed local orientation,
unnormalized target binding and a degree-one transfer, while retaining the
original model, full basis, actual maps, source grading and zero class.

All three realization exports pass serialized integration builds. The complete
public-library build `lake build HodgeConjecture` passes 5,435 jobs. The root
inventory passes 2,382 declaration checks and 574 examples, with 1,858 nonempty
standard-three axiom reports and 1 axiom-free report. All 764 active
library/root/Solution sources pass proof-gap scanning; intentional Challenge
statement placeholders remain separate. Dependencies and source pins are
unchanged. Local document links, whitespace, 157 unique manuscript labels
and 179 resolved references pass inspection. The canonical 114-page PDF
rebuilds without overfull boxes, undefined references or LaTeX errors.
Pages 10–12 and 84–86 pass rendered visual review. Only existing Lean
style/deprecation notices and one bibliography underfull notice remain.
This is cached working-tree validation; clean-clone and human release
sign-offs remain separate.

Canonical manuscript source SHA-256:
`ec4f0773379237d6e279b72b17945c2dddf0d4145a33a7e5754e6dbc3fd46a4e`.
Canonical PDF SHA-256:
`a54d625ac8ac78ae8dcaf326af7c179795a1129cb34bf1632bc791d22e01253d`.
