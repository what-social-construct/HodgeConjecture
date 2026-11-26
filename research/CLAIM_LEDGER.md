# Claim ledger

Last audited: 2026-11-26 (actual split geometric-cover aggregate and original
P¹ finite-cover/harmonic/Hodge comparison; the product P¹ × P¹ ordinary
Chow/Betti checkpoint was audited 2026-11-15). Earlier checkpoint records
retain their original scope.

Status vocabulary:

- `FORMAL`: proved in the current Lean build without project-level axioms or
  proof placeholders.
- `CONDITIONAL`: proved from a structure or proposition whose fields include
  substantive geometric input.
- `OPEN`: required for the intended Hodge-theoretic application and not
  established in this repository.
- `LITERATURE`: standard mathematics used as motivation or awaiting an exact
  source-to-hypothesis match.
- `BENCHED`: preserved and separately checkable, but excluded from active
  library exports and manuscript claims.

The current target-first sketch is [TARGET_BRIDGE.md](TARGET_BRIDGE.md).

## Actual geometric cover aggregate (2026-11-26)

Status: `FORMAL` for the adapter from a positive-degree cohomological transfer,
an original cycle pushforward comparison square, and supplied upstairs column
representatives to the existing exact aggregate. It constructs normalized
pushforward cycles in the original target. The independently fixed full finite Hodge
basis, original cycle map, and arithmetic checker are retained. General
upstairs generation remains an explicit input, including in the faithful
harmonic variant.

`FORMAL` for the actual finite étale projection from four reduced complex points
to two. Its original geometric rank is two. A representative-preserving bridge
identifies ordinary rational CH₀ with the existing split-cycle quotient;
original pushforward residue degrees and flat-pullback local multiplicities
are one. Canonical scheme-valued complex points agree naturally with the native
point model. Both original Chow/native singular H⁰ comparison squares hold,
including the actual composite upstairs structure morphism.

The actual pullbacks of the two reduced point classes supply every column of
the independent full Hodge target. Original geometric push–pull proves that
half their pushforward recovers those point classes. The rank-two identity
matrix with denominator one and modulus three passes the exact aggregate.
This is a complete zero-dimensional comparison and introduces no new Hodge
conjecture case. Positive-dimensional cover comparisons and general geometric
generation remain open. See [0062](working/0062-geometric-cover-coverage.md).

## Galois coefficient descent and harmonic transport (2026-11-26)

Status: `FORMAL` for fixed-tensor descent over a finite Galois extension,
generalized from algebras to arbitrary vector spaces. Inclusion is injective,
and every invariant tensor descends uniquely. This concerns coefficients in
the existing rational Chow module; geometric Chow base change remains open.

`FORMAL` for the native real cellular cohomology/harmonic equivalence,
morphism-induced quotient maps, and naturality under symmetric same-complex
endomorphisms. The aggregate uses quotient-defined transport and requires
injectivity of the transported witness. A symmetric projector alone does
not supply this faithfulness gate.

`FORMAL` for constructors binding the original fixed Hodge target through
Galois-invariant coefficient tensors, exact extended cycle columns, and/or
faithful harmonic transport. Actual P¹ instances over ℚ(i) use the original
infinity Chow class and full Hodge basis. Multiplication by two exercises
nonisometric transport; conjugation moves an imaginary infinity tensor,
and zero transport fails faithfulness.

The source copies retain SHA-256 provenance and MIT notices. See
[0061](working/0061-galois-harmonic-coverage.md). General geometric comparison,
cycle-family generation, extension-field batching, codecs and a sound
concrete SNARK backend remain separate obligations.

## Exact fixed-target aggregate coverage (2026-11-26)

Status: `FORMAL` for an executable rational/integer/prime-field rank checker:
nonzero denominator, exact rational matrix binding, primality, and a modular
right inverse are all mandatory. Accepted rank evidence lifts to rational
surjectivity without an entry-size bound; no map ℚ → Fp is assumed.

`FORMAL` for aggregate acceptance implying `RationalHodgeConjectureAt M` for
a fixed model with a complete independently specified target basis. Actual
cycle classes and every coordinate-column equality are proof gates; the
harmonic constructor discharges those equalities through a supplied faithful
realization. Surjectivity is a conclusion, not a certificate field.

`FORMAL` for an accepted actual P¹ instance using its original infinity Chow
class, geometric Hodge target, cover-harmonic realization, and the identity
matrix modulo three. See [0060](working/0060-finite-coverage-certificate.md).

`OPEN`: construction of spanning cycle families and geometric comparisons
for general varieties; generic executable geometric decoding, full circuit
refinement, and a concrete sound succinct-proof backend. The code does not
advertise the inner checker as a SNARK or extension-field batching system.

## Finite cover, harmonic and Hodge comparison on P¹ (2026-11-26)

Status: `FORMAL` for the nonzero two-chart/two-component finite complex,
its rational-to-real differential square, the native quotient equivalence
to actual circle singular H¹, and harmonic projection compatibility with
the original Mayer–Vietoris boundary.

`FORMAL` for transport through the original radial pullback and original
projective-line boundary to actual canonical scheme-point Betti H²,
including the original positive generator and ordinary Chow cycle map.
The actual scheme Hodge filtration transports to the same finite quotient;
its rational target is exactly the preimage of the independently defined
geometric Hodge target. The finite cycle map retains ordinary Chow degree,
and its Betti image is proved equal to the original ordinary cycle map.

`OPEN`: general finite-model/geometric comparison, intrinsic analytic
harmonic operators, general proper/purity comparison and prescribed-class
generation. This P¹ comparison does not establish any of these general
statements. See [0059](working/0059-finite-cover-harmonic-comparison.md).

## Finite harmonic class certificates (2026-11-25)

Status: `FORMAL` for the copied finite cellular core, its genuine degree-one
Laplacian and energy/kernel identity, and isometric cochain transport. The
four source modules are adapted from `homotopical-encrypt` at
`b388870613f770cea64d03b4c4ff2c34905020e1`; each copy points to its original,
and `HodgeConjecture/LinearAlgebra/Harmonic/LICENSE` retains the MIT notice.
No external package dependency is added.

`FORMAL` for unique harmonic representatives of closed finite real cochains,
exactness of their projection residual, and equality in the native
kernel/range quotient iff harmonic projections agree. Only the harmonic
representative is unique; an exact primitive remains existential.

`CONDITIONAL` for `normalizedPushforward_cycleClass_of_harmonicWitness`:
an injective rational linear realization into the finite harmonic space and
an exact-difference certificate supply the equality argument of the existing
upstairs descent theorem. Its original transfer/pushforward hypotheses and
the supplied cycle remain explicit.

`FORMAL` for `ProjectiveLineProductHarmonicWitness.witness_injective` and
`.fiberChowClass_harmonic_certificate`: the existing actual product Betti
coordinates embed in a two-dimensional real zero-differential presentation,
and the original fiber-cycle recipe passes the certificate. This is a chosen
coordinate metric, not a geometric Laplacian or triangulation comparison.

`OPEN`: a general finite-model/Betti comparison respecting rational and Hodge
structures, geometric harmonic/cycle compatibility, and prescribed-class
coverage. The finite coordinate control does not discharge these obligations.
Focused validation is `make check-harmonic-witness`; full release sign-offs
remain separate.

## Ordinary rational Chow and Betti H² on P¹ × P¹ (2026-11-15)

Status: `FORMAL` for the actual scheme product's integrality and generic
degree two, the opposite affine tensor chart with closed complement equal to
the two named zero fibers, and degree-one rational Chow localization. The
two-variable polynomial chart has zero ordinary degree-one rational Chow
group: its height-one prime cycles are actual principal divisors in the
existing quotient. Every degree-one boundary carrier is one of the two
zero fibers, so their ordinary rational Chow classes span the product's
degree-one Chow group. Rational relation denominator clearing, the affine
UFD zero-divisor unit criterion, base-scalar transport, and distinctness of
the two carriers prove those classes independent. See
`ProjectiveLineProductZeroBoundaryGenerators.rationalChowGroup_span_zero_fibers`
and `ProjectiveLineProductFiberChowIndependence.rational_zero_fiber_classes_independent`.

Status: `FORMAL` for the resulting unconditional linear map from that actual
ordinary rational Chow quotient to actual rational singular H² of the same
scheme product. It sends the two zero-fiber classes to the independently
constructed supported Thom--Gysin images, and is a linear equivalence. It
realizes every product H² class by the corresponding rational fiber cycle. See
`ProjectiveLineProductChowFiberRealization.ordinaryChowCycleClass_first`,
`.ordinaryChowCycleClass_second`, and
`.ordinaryChowCycleClass_fiberChowClass`, and `.ordinaryChowBettiEquiv`.

`OPEN`: a general natural cycle-class map for arbitrary divisors or smooth
projective varieties, compatibility with a separately constructed universal
first-Chern/Gysin map on every divisor, and prescribed-class coverage in the
main Hodge target. The product map is determined by the proved two-fiber
bases; it does not assert those general comparisons.

## Original holomorphic Betti comparison on canonical P¹ (2026-11-10)

Status: `FORMAL` for invertibility in degree two of the original
`Scheme.ComplexPoints.holomorphicBettiComparison` on canonical scheme
complex points of P¹. The source has a proved one-dimensional coordinate;
the target dimension follows from the separately proved complex
singular-to-holomorphic isomorphism. The original map has a nonzero value
on the transported rational cover generator, so its scalar coordinate is
nonzero and the original map is bijective. Its categorical `IsIso` theorem
and inverse equivalence retain that exact forward map.

`OPEN`: equality of the generic cochain-induced and original holomorphic
maps, general invertibility, scheme topology, proper comparison, periods,
purity and prescribed-class coverage. See
[0056](working/0056-projective-line-holomorphic-comparison-iso.md).

## Complex singular cochains and derived constant-sheaf cohomology (2026-11-10)

Status: `FORMAL` for the literal ℚ-to-ℂ coefficient map on the original
singular cochain complexes, presheaves, sheafifications, constant-sheaf
augmentations and complete local resolutions. The original global units
commute with this map as cochain complexes and on induced cohomology.

`FORMAL` for the indexed small-cover comparison with unrestricted complex
functionals, local-zero kernel acyclicity, global-unit quasi-isomorphism on
paracompact Hausdorff spaces, open section lifting, and flasqueness under
the stated open-subspace hypotheses. The same native complex cochains map
isomorphically to right-derived sections of the native complex constant
sheaf on locally compact second-countable Hausdorff, strongly locally
contractible spaces. Generic naturality of extension by zero, nonnegative
sections, flasque hypercohomology and derived postcomposition also has
direct proofs.

`FORMAL` for the composed map from complex singular cohomology to the
intrinsic holomorphic derived target. Its composition with the separately
proved finite-cohomology coefficient map is an isomorphism under the stated
topology and finiteness hypotheses. This cochain-induced composite has its
own name and is not yet identified with the earlier 0053 map.

`OPEN`: equality of the induced coefficient map with the exact ordinary
derived scalar-restriction map, and hence with the constructed holomorphic
comparison. Its general invertibility, general scheme topology, proper comparison,
periods, purity and prescribed-class coverage remain open. See
[0055](working/0055-complex-singular-derived-comparison.md).

## Coefficient change with finite-dimensional cohomology (2026-11-10)

Status: `FORMAL` for shared exact functionals V ↦ Hom_k(V,A) on arbitrary
vector spaces, with original `RationalDual.functor` delegated to k = A = ℚ.
Original rational complexes and transpose maps retain their interfaces.
Native scalar extension is exact over the source field. Coefficient
evaluation is a natural transformation between the resulting exact functors.

`FORMAL` for invertibility of the induced cochain coefficient map in a degree
where the original chain homology is finite dimensional. The terms and sets
of simplices may be infinite. The isomorphism has the actual cochain map as
its induced map, through the native tensor-homology comparison.

`FORMAL` for specialization to the original rational singular chains and
cochains, with source exactly the existing tensor complexification of
`SingularCochains.Cohomology`. The target is unrestricted complex-valued
functionals on those same native chains, with their original transpose
differential. Native duality shows finiteness of the original rational
cohomology in that degree suffices. P¹ discharges that hypothesis, and its
original generator has nonzero image in the actual complex-functional target.

`OPEN`: the remaining derived naturality needed to identify this
cochain-induced map with the exact holomorphic map in 0053; the latter map's
invertibility is not yet proved. General geometric finiteness,
scheme topology, proper comparison, periods, purity and prescribed-class
coverage retain their earlier scope. See
[0054](working/0054-finite-cohomology-coefficient-change.md).

## Complex coefficients and the original holomorphic derived target (2026-11-10)

Status: `FORMAL` for native scalar restriction on fixed-ring module sheaves,
its exactness, the coefficient map between the original constant sheaves,
and commutation of actual ordinary derived global sections with restriction.
The proof uses the same larger-coefficient injective resolution and its
restricted flasque terms; preservation of injectives is not assumed.

`FORMAL` for the isomorphism from ordinary derived sections of the native
complex constant sheaf to the existing intrinsic holomorphic hypercohomology,
with the original Poincaré resolution map fixed. Coefficient inclusion and
the previous rational comparison give a complex-linear map from the existing
tensor complexification of rational Betti cohomology to that actual target.
The tensor map uses the native universal property and existing algebra action.

`FORMAL` for injectivity of the rational comparison, using a rational-linear
splitting only in its proof, and zero detection on the rational diagonal.
The existing P¹ generator has nonzero image in actual holomorphic degree-two
hypercohomology. Smooth-scheme wrappers use the existing atlas and leave the
additional general point-topology hypotheses explicit.

The subsequent 0054 checkpoint above proves finite-cohomology coefficient
change on the original cochains. Its identification with this exact
holomorphic map remains open. `OPEN`: general invertibility of this holomorphic comparison,
general scheme topology, proper algebraic/analytic comparison, general periods,
purity and prescribed-class Chow coverage. No scalar extension through
infinite products of simplex functions is asserted. See
[0053](working/0053-complex-coefficients-holomorphic-comparison.md).

## Original rational singular groups and derived constant-sheaf cohomology (2026-11-10)

Status: `FORMAL` for the assembled map from the original rational singular
cohomology to ordinary right-derived global sections of the original
rational constant sheaf. It composes the original global unit, native
extension by zero, the proved whole-complex comparison, the inverse of the
original local resolution map, and the existing single-sheaf derived comparison.

`FORMAL` for its invertibility in every nonnegative degree on locally
compact second-countable Hausdorff spaces with a basis of contractible
neighborhoods. Source and target are the existing native objects, and the
resolution square and zero-class detection are proved for the actual map.
The comparison is objectwise; no new derived pullback functor between spaces
or natural-isomorphism statement against such a functor is asserted here.

`FORMAL` for smooth-scheme wrappers with the remaining point-topology
hypotheses explicit. The existing atlas supplies strong local contractibility.
Canonical affine spaces in every dimension and the original P¹ meet the
hypotheses. The original P¹ generator has a proved nonzero image in the
actual derived constant-sheaf degree-two target.

The subsequent 0053 checkpoint above constructs the complex-linear map
to the original holomorphic derived target and proves rational-diagonal
detection. Its invertibility, general scheme topology, proper algebraic/analytic
comparison, general periods, purity and prescribed-class Chow coverage remain open. See
[0052](working/0052-rational-singular-constant-sheaf-comparison.md).

## Original whole-complex derived comparison for flasque terms (2026-11-10)

Status: `FORMAL` for invertibility of the original bounded-below
derived-functor unit on native flasque fixed-ring module sheaf complexes.
Native cycle short exact sequences, flasque section lifting, the native
monomorphic injective replacement and its native acyclic cokernel prove
the comparison. No comparison isomorphism is supplied as a premise.

`FORMAL` for the original singular sheaf complex under its proved
flasqueness hypotheses, including canonical affine spaces in every
dimension and the original P¹. The induced original comparison is
invertible in every integer homology degree. The actual module category,
global-sections functor, complex, differential and map are retained.

`FORMAL` for moving the generic hypercohomology construction into the
shared sheaf layer with its original public names. The old de Rham entry
point re-exports it and retains the scheme wrappers.

The subsequent 0052 checkpoint above exports the composite with the
existing global-unit quasi-isomorphism and local rational constant-sheaf
resolution. General scheme topology, complex coefficients and later
proper/purity/coverage obligations retain their earlier scope. See
[0051](working/0051-singular-derived-comparison.md).

## Positive derived sections of the existing flasque terms (2026-11-10)

Status: `FORMAL` for positive right-derived sections of any native
flasque fixed-ring module sheaf on every original open, on any topological
space. The existing full Čech-to-derived criterion is specialized to all
opens and all covers, using the existing flasque Čech vanishing proof.
Exact coefficient forgetting and its original injective-resolution
comparison identify the actual module-valued derived cohomology.

`FORMAL` for the original singular sheaf terms under their already proved
flasqueness hypotheses, including canonical affine spaces in all dimensions
and the original glued P¹. The global statement uses the existing
`SheafHypercohomology.globalSections` functor directly. Arbitrary opens,
including the same noncompact P¹ affine chart, are covered. The sheaf
index and positive derived degree are independent; the original nonzero
P¹ total singular H² class is retained.

`FORMAL` for shared ownership of the original postcomposition comparison,
with its public name retained. The old de Rham module-cohomology helper
delegates to the shared all-space construction with the same endpoints.

The subsequent 0051 checkpoint above proves invertibility of the
existing bounded-below comparison for the whole singular sheaf complex.
`OPEN`: the subsequent singular/constant-sheaf comparison on derived
sections, general scheme topology, complex
coefficients and later proper/purity/coverage obligations. See
[0050](working/0050-flasque-derived-sections.md).

## Open-subspace lifting and native flasque cochain sheaves (2026-11-09)

Status: `FORMAL` for the native sheafification/restriction isomorphism,
using the existing `restrictPresheaf` and `local_restrictSheaf` owners,
with actual unit compatibility. The original singular cochain functor
identifies the original cochains on a subopen with those on its ambient
image. No alternative cochain or sheaf model is used.

`FORMAL` for surjectivity of the existing ambient unit on any paracompact
Hausdorff open. Every sheaf section there lifts to an original global
cochain, using the existing extension by zero. Restriction maps of the
original cochain sheaf are surjective whenever the smaller open has
these properties; the ambient and larger open need no paracompactness
assumption for that statement.

`FORMAL` for the native module-valued `TopCat.Sheaf.IsFlasque` property
in every degree when the ambient space is Hausdorff and every open is
paracompact. Locally compact second-countable Hausdorff spaces satisfy
that condition. These properties are proved on the original canonical
affine spaces in every dimension and the original glued P¹. General
scheme wrappers retain the explicit topology hypotheses.

The subsequent 0050 checkpoint above proves positive right-derived
section vanishing for these terms on all opens. The bounded-below
whole-complex comparison, general scheme point-topology properties,
complex coefficients and later proper/purity/coverage obligations remain
`OPEN`. See
[0049](working/0049-open-singular-sheaf-restrictions.md).

## The actual global singular sheafification unit (2026-11-09)

Status: `FORMAL` for degreewise surjectivity of the existing
`globalCochainsToSheaf` on paracompact Hausdorff spaces. Actual local
representatives extend using the existing relative extension by zero;
a locally finite closed refinement patches original cochains.

`FORMAL` for the quasi-isomorphism of that same map in every degree,
using its native short exact kernel sequence and the already proved
kernel acyclicity. Its target is ordinary termwise global sections of
the original singular sheaf complex. The original unit induces the
constructed homology isomorphism. Canonical affine spaces in every
dimension and the original glued P¹ have independently proved
paracompact Hausdorff point topologies; the real line and empty space
also apply. General scheme wrappers retain explicit topology hypotheses.

`OPEN`: sheaf-term acyclicity and comparison with actual derived global
sections, the needed topology on general scheme point spaces, complex
coefficients and the subsequent proper/purity/coverage obligations.
This is not yet the full singular/sheaf-cohomology comparison. See
[0048](working/0048-global-singular-sheaf-sections.md).

## Actual global singular sheafification kernel (2026-11-09)

Status: `FORMAL` for the kernel criterion on the existing
`globalCochainsToSheaf`: an original rational singular cochain maps to
zero exactly when it is locally zero. Every such cochain vanishes on
some actual point-indexed open cover. Its degreewise linear kernel is
the join of the existing cover restriction kernels.

`FORMAL` for acyclicity in every degree of
`Limits.kernel (globalCochainsToSheaf X)`, with actual primitives in
that native kernel. The proof reuses the original cover kernels and
native inclusion; degree zero is a zero object. No separation, local
contractibility or finiteness assumption is required. The theorem applies
to every canonical scheme point space, without smoothness assumptions.

The subsequent 0048 checkpoint above proves global-unit surjectivity
and its quasi-isomorphism on paracompact Hausdorff spaces. Sheaf-term
acyclicity, the derived-section and complex-coefficient comparisons
remain `OPEN`. Kernel acyclicity alone did not establish the global
comparison; the additional surjectivity proof is used. See
[0047](working/0047-global-sheafification-kernel.md).

## Arbitrary open-cover comparison (2026-11-09)

Status: `FORMAL` for the indexed small simplicial subcomplex, its original
native chain complex, and actual finite-chain shrinking under the
existing barycentric subdivision. The index type need not be finite or
countable. The restricted original homotopy proves that the original
inclusion is a quasi-isomorphism in every degree, on any topological
space with a genuine indexed open cover. No separation or local
contractibility hypothesis is needed for this cover comparison.

`FORMAL` for the original rational cochain restriction quasi-isomorphism,
using existing exact dualization, and degreewise surjectivity using the
existing extension by zero. The original relative kernel is acyclic,
including degree zero, and closed positive-degree vanishing cochains
have actual primitives vanishing on the same cover. Original native
refinement maps commute with the comparisons. The two-open API reuses
these proofs with its original native complexes and retained names.

The actual global-unit kernel identification and acyclicity are now
proved in [0047](working/0047-global-sheafification-kernel.md), using
these cover kernels. Global-unit surjectivity and comparison with
termwise sections are now proved under the stated topology hypotheses
in 0048 above. The derived-section and complex-coefficient comparisons
remain `OPEN`. The per-cover construction
is recorded in [0046](working/0046-arbitrary-open-cover-small-chains.md).

## Rational singular sheaf resolution (2026-11-09)

Status: `FORMAL` for the original rational singular cochain presheaves,
with the existing restrictions and differential. Evaluation recovers the
original singular complex. Native sheafification gives a sheaf complex
and an actual map from original global singular cochains to its global
sections.

`FORMAL` for actual local primitives, local constancy, augmentation
monomorphism and all-degree sheaf exactness on strongly locally
contractible spaces. These prove the full rational constant-sheaf
quasi-isomorphism. The topological hypothesis is proved from the existing
canonical analytic atlas for smooth schemes of fixed relative dimension;
canonical affine spaces in all dimensions and the original P¹ apply.
The existing sheafification, constant-sheaf and global-sections owners
are reused, with shared local proofs and retained de Rham interfaces.

`OPEN`: proving the global-cochain map computes derived global sections,
and comparing coefficients with the complex holomorphic resolution.
Neither follows merely from the sheaf quasi-isomorphism. General proper
comparison, periods, purity and prescribed-class coverage remain open.
See [0045](working/0045-singular-cochain-sheaf-resolution.md).

## Intrinsic local Poincaré comparison (2026-11-09)

Status: `FORMAL` for the chart identification of the original descended
forms and complexes. Derivative pullback constructs coordinate sections'
full compatible families; the transition cocycle and both inverse laws
are proved. The actual chart equivalence commutes with d.

`FORMAL` for intrinsic local constancy in degree zero, actual local
primitives in every positive degree and the genuine constant-sheaf
augmentation. This augmentation is mono and exact in degree zero;
positive exactness gives its full sheaf quasi-isomorphism. The proofs
transport the existing coordinate constants and radial primitives.
The old coordinate comparison reuses the shared constant-lift and
augmented-complex proofs and retains its API.

`FORMAL` on native complex C∞ manifolds with the compatible real scalar
structure used by the coordinate proof, including the canonical analytic
points of schemes smooth of fixed relative dimension. Actual canonical
affine spaces in all dimensions and the original glued P¹ instantiate
the same comparison. No replacement topology or supplied comparison data
is introduced.

Analytic constant-sheaf/singular comparison, proper algebraic/analytic
comparison, the general period isomorphism and purity remain `OPEN`.
This is a quasi-isomorphism of analytic sheaf complexes, without asserting
a general global-section or singular comparison. See
[0044](working/0044-intrinsic-holomorphic-poincare.md).

## Atlas forms descent and the all-degree algebraic map (2026-11-09)

Status: `FORMAL` for derivative pullback of the original coordinate forms,
composition and commutation with d. Compatible chart families form the
intrinsic forms module on any native complex C∞ manifold. The same
coordinate differential descends, squares to zero and respects restriction.
The sheaf property is proved by gluing the original coordinate sections,
giving the intrinsic all-degree de Rham sheaf complex.

`FORMAL` for the map from the original Kähler exterior powers to these
forms on canonical analytic points of schemes smooth of fixed relative
dimension. The determinant wedge extends the existing degree-one map;
all degrees commute with the original algebraic differential, coordinate
pullback and original section restrictions. Actual chart evaluation gives
the map without a supplied evaluation or descent premise. Its components
are natural transformations from the existing algebraic forms presheaves,
compatible with their complex differential, and form a native morphism
from the original algebraic de Rham presheaf complex. Shared section algebras and
holomorphic-function scalar actions have a single owner.

The intrinsic constant-sheaf/Poincaré comparison is now proved in
[0044](working/0044-intrinsic-holomorphic-poincare.md). Analytic/singular and
proper algebraic/analytic comparison, the general period isomorphism and
purity remain `OPEN`. This constructs a map, without asserting that it is
a comparison isomorphism. See [0043](working/0043-holomorphic-forms-descent.md).

## Canonical analytic atlas and actual regular evaluations (2026-11-09)

Status: `FORMAL` for the native analytic manifold structure on the original
canonical complex points of schemes smooth of fixed relative dimension d.
Standard-smooth algebraic local structure gives actual étale coordinates;
complex analytic implicit inverses give the original open partial
homeomorphisms. The proved chart family covers every point, and all
transition maps are complex analytic. No atlas or holomorphic transition
compatibility is supplied as a premise.

`FORMAL` for analytic regular-function evaluations on every scheme open
and analytic scheme maps, including maps between different dimensions.
The actual section evaluations are bundled as complex-algebra maps into
native C∞ functions on analytic opens and coordinate charts. Source
scalars are the original structure-morphism constants. Restriction and
pullback compatibility and equality of chartwise/intrinsic values are
proved. The original glued P¹ is proved smooth of relative dimension one
using its existing affine cover.

Intrinsic forms descent and the all-degree algebraic forms map are now
constructed in [0043](working/0043-holomorphic-forms-descent.md).
Intrinsic local Poincaré comparison is proved in [0044](working/0044-intrinsic-holomorphic-poincare.md).
Analytic/singular and proper algebraic/analytic comparisons, and general
purity remain `OPEN`. This is not a claim for arbitrary
singular or variable-relative-dimension schemes. See
[0042](working/0042-canonical-analytic-atlas.md).

## Holomorphic complex and local Poincaré comparison (2026-11-09)

Status: `FORMAL` for the all-degree complex of native complex C∞
alternating-form sections on complex normed coordinate spaces. Native
exterior differentiation gives the actual arrows; local-extension
independence, restriction compatibility, complex linearity and d² = 0
are proved. The existing bundled-map sheaf supplies the coefficients.
Actual sheafification constructs the constant-sheaf augmentation and
the cochain comparison map.

`FORMAL` for the actual holomorphic radial operator in every positive
degree, its complex C∞ regularity, and dK + Kd = id. Shrinking to a ball
proves local exactness in every positive degree. The actual constant-sheaf
comparison is a full quasi-isomorphism in every coordinate dimension.
The degree-one radial primitive equals the existing normalized segment
primitive; the old degree-one and complex-line comparison theorems now
specialize the general proof. This is a sheaf quasi-isomorphism, not an
identification of arbitrary global-section cohomology with singular
cohomology. See [0041](working/0041-higher-degree-holomorphic-poincare.md).

`FORMAL` for the degree-one Kähler map associated to a genuine algebra
map into holomorphic functions: da maps to the actual derivative d(φ(a)).
The native polynomial evaluation map is constructed and agrees with
ordinary evaluation. Evaluation on smooth canonical scheme points is now
constructed above. The all-degree algebraic/analytic forms map is now
constructed in [0043](working/0043-holomorphic-forms-descent.md).

Intrinsic local Poincaré comparison is now proved in
[0044](working/0044-intrinsic-holomorphic-poincare.md). Analytic/singular and
proper algebraic/analytic comparisons, and general purity remain `OPEN`. No such input is installed as a project
axiom or supplied as a new substantive comparison structure. See
[0040](working/0040-holomorphic-derham-local-poincare.md).

## Canonical scheme Betti target and existing P¹ identification (2026-11-08)

Status: `FORMAL` for the constructed topology on actual sections over
Spec ℂ, regular-function continuity, scheme-morphism functoriality and
open/closed immersion embeddings. Affine algebra-point and original P¹
chart models have proved homeomorphisms to these independently defined
spaces. `SchemeBetti.Cohomology` is the existing rational singular
cohomology on this space, and the original pullbacks form its
contravariant scheme functor. The topology proofs are adapted from pinned
Axiom Weil with attribution, using native Mathlib only.

`FORMAL` for transport of canonical conjugation and pure rational Hodge
structures along rational equivalences, and for the existing P¹ period,
geometric filtration, purity and ordinary Chow square on this canonical
target. The Chern period remains 2πi. This identifies an already proved
example, without adding a new geometric class of Hodge-conjecture cases.

`CONDITIONAL` on an explicit period isomorphism for the general canonical
scheme-filtration adapter. General scheme holomorphic/Poincaré
comparison, analytic/singular identification, proper algebraic/analytic
comparison and general opposedness/purity remain `OPEN`. No general
comparison or purity theorem is obtained from the audited Stacks
realization or Weil Artin comparison. See
[0039](working/0039-canonical-scheme-betti-target.md).

## Proved Tate/Hodge graph compatibility (2026-11-08)

Status: `FORMAL` for pure rational Hodge structures in the independently
constructed target framework. The genuine Tate line has type (p,p),
weight 2p and a proved bounded opposed filtration. The product uses native
tensor distribution on the original rational carrier ℚ × H; canonical
conjugation and pure product conditions are proved. Rational filtered maps
preserve all recovered Hodge pieces.

`graph_isHodge_iff` proves that the original graph projector is a Hodge
morphism exactly for classes in the independent rational Hodge subspace.
`classGraphHodgeCompatibility` discharges that input of the old equivalence.
`rationalHodgeConjectureAt_iff_hodgeGraphLifts` retains the cycle map's type
proof, correspondence action, Chow graph construction and lower-left
detection as explicit inputs. Its equivalence is therefore `CONDITIONAL`
on those independent geometric data. The actual P¹ model instantiates the
Hodge compatibility, with no new full Chow-motive construction asserted.
General geometric comparison/purity and coverage remain `OPEN`.
See [0038](working/0038-tate-hodge-graph-bridge.md).

## Cyclic filtered projector-defect detector (2026-11-08)

Status: `FORMAL` as an algebraic construction on the existing raw closure.
`ProjectorDefectModule` uses the native polynomial action by the original
closure class q and the cyclic submodule generated by its original defect
q²−q. Its inclusion into that same possibly noncommutative algebra is
injective. The module is finitely presented over ℚ[T]; the quotient degree
filtration has finite rational stages, is exhaustive and satisfies the
native filtered-module interface. Its annihilator is exactly the polynomials
p with p(q)(q²−q)=0. The module, or any stage, is zero exactly when q is
idempotent. No cohomological faithfulness is used.

`AlgebraProjectorClosure.DefectModule` specializes this same carrier. The
original restriction kills every element and filtration stage; existing
Chow localization places their images in the additive boundary image.
Object vanishing gives the existing `ZeroDefectWitness`. It is not proved
for arbitrary closures. Geometric coherent-sheaf/D-module identification,
a Hodge or Rees construction, a connection across the relevant boundary
and vanishing remain `OPEN`. The polynomial control has a nonzero detector,
strictly growing filtration and zero annihilator despite zero restriction.
See [0037](working/0037-filtered-projector-defect.md).

## General filtered rational target (2026-11-08)

Status: `FORMAL` as a general construction, with geometric instantiation
`OPEN` beyond the proved examples. `RationalComplexification` owns the
actual tensor product, injective rational embedding and canonical
conjugation. `HodgeFiltration.rationalHodgeClasses` derives the rational
diagonal intersection without cycles. `PureRationalHodgeStructure`
records finite dimension, boundedness and opposedness; its target is
derived rather than supplied. `FilteredHodgeTarget` connects this target
to the existing model with the cycle map and its type proof explicit.

`SchemeDeRham.bettiHodgeFiltration` transports the actual derived scheme
filtration through an explicit isomorphism to actual complexified rational
singular cohomology. This does not prove a general geometric comparison,
identify arbitrary topological spaces with analytic complex points, or
prove general purity. The existing P¹ geometric filtration provides a
proved pure instance; its original target and ordinary Chow map are
preserved. General Hodge coverage and the geometric equivalence bridge
remain `OPEN`. The vanishing/source comparison in
[0036](working/0036-filtered-hodge-target-and-vanishing.md) is `RESEARCH`,
not an installed source theorem or an asserted zero-defect result.

## Actual P¹ zero-point Gysin and cycle comparison (2026-11-07)

Status: `FORMAL`. `RelativeCochains` is the actual kernel of restriction
of original rational singular cochains, with original differential,
short exact pair sequence, native connecting maps and pair pullbacks.
`RelativeUnion` proves strict excision inside a union by actual cochain
gluing. `RelativeExcision` uses the proved full-to-small quasi-isomorphism
and the native short-exact-sequence comparison to prove actual open-cover
excision. `RelativeMayerVietoris` identifies local relative boundary,
inverse excision and forgetting with the existing full Mayer–Vietoris
boundary. The positive sign follows from the actual map `(a, 0)` into
the first-minus-second sequence.

`ComplexPointThom.thomClass` is the native relative boundary of the
original radial pullback of the positively paired circle class, in
actual H²(ℂ, ℂ∖{0}). It is nonzero, has boundary pairing +1, and gives
an isomorphism from actual singleton H⁰. Its image in local absolute H²
is zero. The original P¹ finite chart identifies this pair with the
local zero-point pair; inverse excision places the class in actual
cohomology supported at that point. Forgetting support has nonzero image
equal to the existing positive P¹ generator.

`ProjectiveLinePointGysin.gysin` retains those actual maps and is an
isomorphism from original support H⁰ to actual P¹ singular H². The support
point is proved to map to the original scheme `projectiveLineZero`.
`ProjectiveLineGysinCycleClass` identifies the Gysin unit with both ordinary
cycle-class images of the integral and rational Chow classes of that same
scheme point. Both ordinary cycle maps factor through this actual zero-point Gysin and
the original Chow degree.

This constructs only the distinguished zero-point Gysin in its original
finite chart. Transport to other points, coordinate independence, general
Gysin/Poincaré duality, a singular fundamental two-cycle, general
characteristic-zero degeneration and prescribed-class coverage remain
`OPEN`. See [0035](working/0035-projective-line-zero-point-gysin.md).

## Actual P¹ Hodge filtration and fixed cycle model (2026-11-07)

Status: `FORMAL`. Native brutal degree truncation retains the original
terms and differential above its index, with actual inclusions and
decreasing transitions. Hypercohomology uses the original extension by
zero, derived global sections and homology. The scheme Hodge filtration
is defined as the linear range of the induced actual inclusion, including
integer indices. Its top/bottom values are proved rather than assigned.

For the original P¹ over any field, the original form sheaves vanish
above degree one and the regular-function term has vanishing H¹ and H².
The actual F¹ inclusion is consequently an isomorphism on actual scheme
H², retaining the original comparison with H¹(Ω¹). Thus Fᵖ = H² for
p ≤ 1 and Fᵖ = 0 for p ≥ 2. The nonzero Chern coordinate has filtration
degree exactly one. No general spectral-sequence degeneration is inferred.

The actual rational singular H² has an independently defined weight-two
tensor decomposition, canonical rational conjugation, directness,
exhaustion and an opposed filtration. The bounded period equivalence
preserves the actual geometric filtration in every integer index. Its
transported filtration and conjugate recover exactly type (1,1); rational
Hodge classes are defined by inverse image of that geometric piece.
No cycle map is used to define those pieces or their rational subspace.

`ProjectiveLineHodgeCycleClass.model` instantiates the existing
fixed-codimension target predicate with the original zero-cycle Chow
quotient, actual rational singular H² and this geometric Hodge subspace.
`model_satisfies_rationalHodgeTarget` is proved using the independently
constructed ordinary cycle map; `infinity_class_witness` gives an explicit
rational multiple of the original reduced infinity class for every target
class. This is a model specialization under the bounded period comparison,
not an identification with a separately constructed general Gysin map
or an assertion of a new classical Hodge-conjecture case.

The zero-point Gysin comparison is now proved above. A singular fundamental two-cycle,
general analytic/Gysin comparison, general characteristic-zero degeneration
and general prescribed-class coverage remain `OPEN`. See
[0034](working/0034-projective-line-hodge-filtration.md).

## Positive circle pairing and P¹ boundary-period comparison (2026-11-07)

Status: `FORMAL`. Actual cochain evaluation on native closed rational
chains descends to actual cohomology and is natural for original chain
maps/cochain pullback. Actual native connecting representatives have the
positive lift-and-differentiate sign. The two explicit circle arcs follow
angles `−π/2 → π/2 → 3π/2`; their actual endpoint boundaries cancel.
Evaluating the actual connecting class gives upper minus lower endpoint
value. The original circle cover generator therefore pairs +1 with this
counterclockwise singular cycle.

The original P¹ inverse connecting isomorphism and actual radial map
define its positive boundary-loop functional. Its scalar extension is a
functional on the genuine tensor product `ℂ ⊗[ℚ] H²_B`, agreeing with the
proved coordinates. Rational embedding is the original pure tensor and
is injective. Ordinary integral/rational maps from the existing Chow
quotients are constructed independently of de Rham as actual geometric
degree times the singular cover generator. Point normalization, principal
invariance, rationalization, nonvanishing and rational surjectivity hold.

`ProjectiveLinePeriodComparison` specifies a linear equivalence from actual
scheme de Rham H² to that tensor target by the actual analytic boundary
period, with uniqueness proved using the independently constructed positive
boundary pairing. Every original overlap form has its actual Laurent
circle integral as coefficient; the Chern coordinate maps to `2πi` times
the embedded singular generator. Dividing by `2πi` gives the proved square
with the independently constructed ordinary Chow maps.

This is a bounded boundary-period comparison. It does not construct a
singular fundamental two-cycle, Poincaré duality, a general analytic-sheaf
comparison or a topological Gysin map. Identification with separately
constructed general cycle classes, Hodge-structure comparison beyond this
computed P¹ and general prescribed-class coverage remain `OPEN`. General
characteristic-zero degeneration also remains `OPEN`. See
[0033](working/0033-oriented-boundary-period-comparison.md).

## Actual circle H¹ and projective-line singular H² (2026-11-06)

Status: `FORMAL`. Actual rational singular cochains are homotopy invariant
through the dual of the original native chain homotopy. Native point-chain
exactness and exact rational dualization prove positive-degree cohomology
vanishes on contractible spaces. Canonical H⁰ coordinates commute with
original continuous pullback.

For native `Circle`, the two punctured opens have actual interval
homeomorphisms and contractions. Their overlap is homeomorphic to the
disjoint union of the negative and positive argument intervals. Proved
path-component evaluation identifies its actual H⁰ with `Bool → ℚ`.
Original chart pullback has exactly the constant-pair image. Exactness
makes the actual boundary onto with that kernel, proving
`H¹(Circle, ℚ) ≃ₗ[ℚ] ℚ`. Its nonzero cover generator is the boundary of
the upper-component indicator.

For the original over-ℂ points of P¹, the actual affine-chart ranges are
contractible. Their original native Mayer–Vietoris boundary
`H¹(U ∩ V) → H²(P¹)` is itself an isomorphism. A proved radial homotopy
equivalence of the actual overlap with `Circle` gives the actual pullback.
Composing these maps computes `H²(P¹(ℂ), ℚ) ≃ₗ[ℚ] ℚ`; every actual class
is a unique rational multiple of the resulting boundary generator.

These statements supply no topological or cohomological computation as a
premise at the concrete endpoints. Positive loop pairing, complex scalar
extension and the bounded boundary-period comparison are now formalized
above. Identification with general analytic/Gysin constructions, general
Hodge-class coverage and general characteristic-zero degeneration remain
`OPEN`. See
[0032](working/0032-circle-projective-line-singular-cohomology.md).

## Exact rational dualization and full singular Mayer–Vietoris (2026-11-06)

Status: `FORMAL`. The unrestricted rational linear dual is an actual
additive exact functor, with proved homology and quasi-isomorphism
preservation, without a finite-dimensionality premise. Its native dual
chain complex is identified with the original rational simplicial
cochains, retaining the actual alternating differential and map naturality.
The proved small-chain comparison therefore gives an actual full-to-small
singular cochain restriction quasi-isomorphism for a genuine two-open cover.

The resulting full singular Mayer–Vietoris sequence has the actual subtype
cohomologies of the two opens and their intersection, with the pair product
comparison fixed by original projections and inclusions. All three
exactness positions, adjacent zero compositions and the initial H⁰
injection are proved. Its restriction and difference maps agree with the
original continuous inclusion pullbacks, using first minus second for
the difference. The connecting morphism comes from the original native
short exact sequence and proved small-cochain comparison.

This uses literal ℚ coefficients and universe-zero topological spaces,
including the original P¹(ℂ). The circle H¹/P¹ H² calculations are now
proved above. Positive boundary-period comparison is also now formalized;
the general analytic/Gysin comparison and prescribed Hodge-class coverage
remain `OPEN`.
General characteristic-zero Hodge–de Rham degeneration is also `OPEN`
here: no Hodge filtration/spectral-sequence construction or closed general
degeneration endpoint is supplied. See the
[cohomology checkpoint](working/0031-singular-cohomology-mayer-vietoris.md)
and [proof-scope audit](working/0030-hodge-derham-degeneration-audit.md).

## Rational singular subdivision and small chains (2026-11-06)

Status: `FORMAL` in the following scope. Subset-contained original singular
simplices form an actual simplicial subcomplex, identified with the
singular set of the subtype space. Native coproduct coordinates identify
Mathlib's literal rational chain modules with finite-support simplex
functions and identify actual subcomplex-inclusion ranges with supported
chains, retaining the original differential.

Explicit finite vertex-cone recursions construct subdivision and its
homotopy, with boundary, naturality and locality laws proved in all degrees.
Native standard-simplex affine realization and barycenters give an actual
subdivision chain map on the original singular complex. The realized
homotopy is a native chain homotopy to identity, including degree zero.
Each occurring recursive barycentric tuple has a proved nested-face flag,
yielding the `n/(n+1)` mesh bound and shrinking of actual chain iterates.
A proved Lebesgue number on the native compact domain makes every finite
singular chain small in a genuine two-open cover after one common count.
The local homotopy and subdivision preserve small chains; the actual
small-chain inclusion supplies the native rational homology comparison.
This chain specialization uses universe-zero spaces and literal ℚ
coefficients, including the constructed P¹(ℂ).

Rational cochains on an arbitrary simplicial union carry the actual short
exact gluing sequence and connecting maps. Its first term for a topological
cover is cochains on the small singular subcomplex. Exact rational
dualization and full singular Mayer–Vietoris are now formalized in the
entry above. The P¹ H² computation is proved in the current checkpoint;
general analytic/Gysin comparison and Hodge-class coverage remain `OPEN`. See
[0029](working/0029-small-singular-chains.md).

## Projective-line Betti inputs and analytic periods (2026-11-06)

Status: `FORMAL` in the following scope. Actual over-ℂ morphisms
`Spec ℂ ⟶ projectiveLine ℂ` are covered by the original affine evaluation
charts. Their final atlas topology is proved homeomorphic to native
`OnePoint ℂ`, using the original Laurent gluing map and native complex
inversion at zero and infinity. Both charts are open embeddings.

`SingularCochains.lean` constructs rational cochains in every degree from
actual continuous standard simplices, the alternating face differential,
its square-zero law and contravariant continuous pullback. The concrete
closed/coboundary quotient is identified with categorical cohomology;
H⁰ agrees with the existing singular kernel construction.

`LaurentPeriods.lean` evaluates actual Kähler forms and proves their actual
unit-circle integral is `2πi` times residue. `ProjectiveLinePeriods.lean`
descends this integral through all original total boundaries and the proved
scheme comparison. The original scheme Chern coordinate has period `2πi`;
the normalized period of every ordinary rational Chow class is its actual
rational degree embedded in ℂ.

P¹'s rational singular H² and positive boundary-period comparison are now
proved above. General analytic/Gysin comparison remains `OPEN`. The two-open small-chain
comparison and full singular cohomology Mayer–Vietoris are now formalized
above. The analytic functional does not define an independent rational
singular lattice or establish positive-degree Betti comparison by itself. General
Hodge-class coverage remains `OPEN`. See
[0028](working/0028-projective-line-betti-inputs.md).

## Projective-line scheme de Rham comparison (2026-11-06)

Status: `FORMAL`. For the same glued P¹ over a field,
`ProjectiveLineSchemeComparison.lean` identifies the original Čech H²
linearly over that field with actual degree-two derived global sections
of the constructed sheaf de Rham complex. Section scalars and restrictions
come from the original structural morphism. The canonical affine
sheafification units, local one-form bases and higher-form vanishing are
proved. Actual affine acyclicity, the signed Mayer–Vietoris boundary and
the two-term derived inclusion fix the comparison on overlap representatives.
No comparison or acyclicity premise is supplied at this P¹ endpoint.

`ProjectiveLineSchemeCycleClass.lean` carries the original integral and
rational Chow maps into this actual scheme target and proves the original
comparison square, point normalization, principal invariance,
rationalization, nonvanishing and rational coefficient bound. The integral
source requires an algebraically closed field; rational classes additionally
require characteristic zero. The scheme comparison itself needs only a field.

General analytic/Gysin comparison, Hodge structures beyond this computed P¹,
general varieties/codimensions and identification with a separately
formalized general Picard/Chern API remain `OPEN`. No prescribed Hodge-class
coverage or new Hodge-conjecture case is claimed. See
[0027](working/0027-projective-line-scheme-comparison.md).

## Positive-degree realization and ordinary projective-line cycle classes (2026-11-06)

Status: `FORMAL` in the following scope. `AffineCohomology.lean` constructs
actual closed/exact quotients in every degree and identifies them with
categorical homology of the original Kähler de Rham complex.
`CohomologyProduct.lean` proves actual `H¹ × H¹ → H²` quotient cup descent.
The logarithmic unit map has proved closedness and group/power/pullback
laws. Laurent residue kills all actual exacts and detects a nonzero `H¹`
class. The auxiliary Milnor-symbol map into actual `H²` kills its
multiplicativity and Steinberg relations; no Bloch comparison is claimed.

The actual glued projective-line cover has a proved overlap pullback.
Its coordinate-ring Čech–de Rham complex uses the original Kähler maps,
proved square zero and proved vanishing of higher polynomial chart forms.
`cechCohomologyTwoIso` identifies `CechH2` with categorical total degree-two
homology. `firstChern` descends from actual transition units modulo both
chart coboundaries; their logarithmic forms are explicit total boundaries.
The coordinate transition has residue one, proving nonvanishing.

The first-Chern source is explicitly the Čech transition quotient.
Separately, the actual projective-line principal divisor now has proved
coefficient degree zero over an algebraically closed field. Actual point,
stalk, function-field and chart-inversion comparisons derive that theorem;
top-degree carrier transport covers every original principal relation.
`ProjectiveLineChow.lean` therefore descends degree through the existing
integral/rational Chow groups. `ProjectiveLineCycleClass.lean` constructs
the ordinary rational Chow-source map into scalar restriction of `CechH2`
in characteristic zero, with all coefficient-one points mapping to the
nonzero first-Chern class. The integral map, rationalization compatibility,
actual principal invariance and residue degree recovery are proved.
`ProjectiveLineCohomology.lean` computes the entire actual Čech degree-two
target by residue over every commutative base ring, with a corresponding
categorical homology isomorphism. Positive/negative Laurent monomials are
proved actual chart boundaries; no integer division is used.

Identification of the entire transition quotient with geometric Picard or
Chow groups and singular/Hodge comparison remain `OPEN`. The separate P¹
scheme-hypercohomology comparison is now formalized above. No Chow-degree injectivity or
coverage of prescribed Hodge classes follows. See
[0026](working/0026-positive-degree-cycle-realization.md).

## Actual graph-generated rational Chow convolution (2026-11-05)

Status: `FORMAL`. For a separated `p : X → S` with integral `X`, a field
structure `b : S → Spec k`, locally finite-type source/pair structures and
a Noetherian pair product, `Correspondence/GraphChow.lean` derives graph
homogeneity from the actual graph-subscheme isomorphism. `graphChowClass`
and `graphChowLinearMap` use the existing principal-relation quotient;
no graph-degree or relation-preservation premise is supplied.

`GraphChowAction.lean` constructs the actual pair-isomorphism pullbacks on
all Chow degrees. Preservation of principal relations and the formulas
`R_τ[Γ_σ] = [Γ_(στ)]`, `L_τ[Γ_σ] = [Γ_(τσ)]` are proved, including their
respective reversed/ordinary multiplication laws and weighted extensions.
`GraphChowAlgebra.lean` proves that the exact `graphChowLinearMap` kernel is
two-sided, then forms its rational quotient algebra. `graphChowRealization`
is injective and its range is exactly the graph-generated Chow submodule.
Multiplication there is characterized by the actual left/right pullbacks.
Finite-group and subgroup averages yield idempotents; the complementary
idempotent is orthogonal on both sides and their sum realizes the diagonal.

`GraphChowBaseComparison.lean`, under separated `b` and the corresponding
absolute-product finite-type/Noetherian hypotheses, proves degree
preservation and actual closed Chow pushforward of relative graph classes
to their absolute graphs. The weighted assembly square carries the exact
relative Chow kernel into the absolute kernel. `graphChowBaseAlgHom` is
therefore an actual algebra map, its realization is that closed Chow
pushforward (after the proved degree equality), and it preserves idempotents.

No product on the whole ambient Chow group, nonvanishing, compactification
existence, general Betti realization, or prescribed-class coverage is
claimed. These last geometric/realization obligations remain `OPEN`.
This extends the original marked-Galois proof spine at its actual Chow
bridge, rather than closing the Hodge target. See the
[checkpoint](working/0025-graph-chow-convolution.md).

## Complex affine-line Betti–de Rham comparison in degree zero (2026-11-05)

Status: `FORMAL`. `Betti/Examples/AffineLineComplexPoints.lean` uses actual
complex-algebra points `ℂ[X] →ₐ[ℂ] ℂ` and the topology induced by all regular
function evaluations. `coordinateHomeomorph` identifies it with ordinary
`ℂ`; path connectedness follows. Polynomial substitution gives continuous
point maps, corresponding to the original affine-scheme morphisms.

`Betti/SingularPathConnected.lean` turns actual paths into standard singular
one-simplices with the existing face convention. The coboundary equation
proves equal evaluations on joined points. `equivConstants` computes the
rational singular `H0` of a path-connected space, independently of cycles.

`DeRham/AffineLineComparison.lean` constructs `bettiComparison`, an algebra
equivalence from the actual closed-function kernel of `ℂ[X]` to the genuine
tensor product `ℂ ⊗[ℚ] H0_B`. Independently extended singular evaluation at
every actual point agrees with evaluation of the original closed polynomial.
Complex and rational normalizations, multiplication and actual polynomial
pullback naturality are proved. `cohomologyZeroComparison` identifies
categorical homology of the constructed de Rham complex with the same target.
The class with coordinate `I` is proved outside the rational embedding.

This establishes a positive-dimensional degree-zero comparison. Higher
cohomology, general scheme/analytic comparison, general positive-codimension cycle
classes and prescribed-Hodge-class generation remain `OPEN`. Pullback
naturality is asserted on the actual closed-function model; no general
cochain map on exterior powers is supplied. See the
[checkpoint](working/0024-affine-line-betti-comparison.md).

## Polynomial degree-zero de Rham cohomology and components (2026-11-05)

Status: `FORMAL`. `Realization/DeRham/Polynomial.lean` proves
`closed_polynomial_iff` for a commutative `k`-algebra `A` with no additive
torsion (`HasUniqueDiv A`): a polynomial is closed precisely when it is
constant with a closed coefficient. The original constant inclusion and
evaluation at zero construct `polynomialCoordinates : H0 k A[X] ≃ₐ[k] H0 k A`.
`polynomialCohomologyZeroIso` identifies categorical homology of the same
constructed complexes. Every evaluation agrees on closed functions.
Neither a field assumption nor reducedness of `A` is required.

`Realization/DeRham/AffineComponents.lean` computes the actual kernel for
finite products `I → k[X]` over an additively torsion-free commutative base.
`affineLinesCoordinates` identifies it with `I → k`, and
`affineLinesCohomologyZeroIso` identifies categorical homology.
`affineLinesBasis` is the actual component-characteristic-function basis,
with `affineLinesBasis_isIdempotent` and the characteristic-zero field
dimension formula `affineLines_finrank`. Empty products are included.
Independently, `idempotent_closed` holds in every characteristic for every
commutative algebra, without a reducedness hypothesis.

This is an algebraic degree-zero result for positive-dimensional coordinate
rings. Higher cohomology, a general positive-dimensional Betti or cycle comparison,
general component theorems and prescribed-class generation remain `OPEN`.
See the [implementation record](working/0023-polynomial-derham-components.md).

## Affine de Rham complex and degree-zero trace/comparison (2026-11-05)

Status: `FORMAL`. `CommutativeAlgebra/DeRham/Differential.lean` constructs
the differential on exterior powers of actual Kähler differentials for any
commutative algebra, proves its defining rule, uniqueness and square-zero
identity. `Complex.lean` packages it as a cochain complex. The selected proof
adaptations use the pinned Axiom Stacks source and retain its attribution.

`Realization/DeRham/AffineDegreeZero.lean` identifies the actual categorical
homology in degree zero with the universal-derivation kernel. For source and
target formally unramified over the base, `FiniteUnramifiedTrace.lean`
restricts the ordinary algebra trace to these kernels. An actual finite basis
proves its degree identity. Over ℚ, a nonzero finite degree supplies the
existing rational transfer, injectivity and normalized projector.
`AffineGeometricDegree.lean` identifies the degree with the original affine
scheme map's geometric rank and the existing computed cycle-fiber degree.

For finite split complex schemes, `SplitComparison.lean` constructs a
normalized cycle-class map from the existing finite split Chow quotient.
Its pullback, pushforward and intersection squares are proved. Evaluation
gives a linear equivalence with the genuine tensor complexification of
existing rational singular cohomology. Both pullback and trace intertwine;
the algebra trace is identified componentwise for split projections.

Status: `OPEN` for scheme-hypercohomology comparison, general finite-syntomic
trace, positive-dimensional Chow–Betti realization and prescribed-class
generation. No new general Hodge-conjecture case is claimed. Scope and
validation are recorded in [the checkpoint](working/0022-affine-derham-trace-comparison.md).

## Finite-fiber cycle pullback (2026-11-05)

Status: `FORMAL`. `Cycles/FiniteFiberPullback.lean` constructs a linear map
on the existing `Cycles` module for every finite scheme morphism, using
actual local fiber lengths as multiplicities. It proves finite support,
positive multiplicities, identity, equality with the existing restriction
for finite open immersions, integer-to-rational coefficient compatibility,
and preservation of the canonical field dimension grading.
`Cycles/FiberResidueField.lean` adapts the pinned Axiom Stacks proof to
identify the actual fiber residue field with the source residue field,
retaining the independent structural scalar actions.

`Cycles/FiniteFiberDegree.lean` proves the weighted length formula for
the actual fiber degree, then identifies the existing finite pushforward
after this pullback with pointwise multiplication by that computed degree.
A constant value of the computed degree gives the cycle degree law.
Coefficients may be any commutative semiring, including rings with zero
divisors; neither an operator degree law nor a residue comparison is assumed.

Status: `FORMAL` for finite flat Chow pullback and its degree law.
`Cycles/FiniteFlatRank.lean` identifies the computed fiber degree with
Mathlib's geometric rank of the same finite flat morphism, without a
Noetherian or field-base assumption. The raw degree law holds over every
commutative semiring, including rings with zero divisors.

`FiniteFlatPrincipalDivisor.lean` proves the weighted sum over actual reduced
source components, retaining the original nilpotent multiplicities.
`FiniteFiberClosedBaseChange.lean` proves compatibility with the existing
closed pushforward. `FiniteFlatPrincipalRelations.lean` then proves
preservation of the existing genuine principal-relation span.
`FiniteFlatChowPullback.lean` descends the same pullback to the existing
integral and rational quotients and proves compatibility with rationalization.
These Chow maps require Noetherian source and target schemes and a locally
finite-type target structural map to a field; ambient integrality is unnecessary.

`FiniteFlatChowDegree.lean` proves `f_* f^* = d • id` on both quotients from
constant geometric rank `d`, including `d = 0`. With `d ≠ 0`,
`Realization/Chow/FiniteFlatTransfer.lean` instantiates the existing
`RationalDegreeTransfer` using these actual maps, proving rational pullback
injectivity and idempotence of normalized pull--push. No relation-preservation
or operator degree law is supplied as a hypothesis.

Status: `OPEN` for flat pullback beyond the finite case, general Betti/purity
comparison, and prescribed Hodge-class generation. Validation and source
attribution are recorded in the [finite flat checkpoint](working/0021-finite-flat-chow-transfer.md).

## Finite pushforward functoriality (SP113)

Status: `FORMAL`. `Cycles/FinitePushforwardComposition.lean` proves the
degree tower law for the actual scheme residue maps, composition of the
original integral scheme-theoretic images, multiplication of the existing
finite pushforward weights, and covariant composition of the original
finite cycle maps over every coefficient semiring. It also proves identity
and composition after restriction to compatible homogeneous submodules.
Raw cycle functoriality needs no ambient integrality, Noetherianity, field
base, dominance or etaleness assumption. The residue `finrank` identity
itself needs no finiteness assumption; its interpretation as a positive
pushforward weight uses the existing finite-map theorem.

`Cycles/FiniteChowPushforwardComposition.lean` proves identity and
composition for the existing integral and rational Chow maps, with their
canonical field dimension functions and principal-relation quotients.
Its inputs are Noetherian schemes, finite morphisms and a target structural
map locally of finite type over a field. Grading compatibility is already
proved; no new map, quotient, source axiom or cycle-class hypothesis is
introduced. This proves the finite specialization of
[Stacks 02R5](https://stacks.math.columbia.edu/tag/02R5), not the general
proper-map case.

Validation (2026-10-27): full `lake build` passes (3273 jobs; only the two
deliberate `Challenge.lean` statement-hole warnings). The root-import
`research/FinitePushforwardCompositionVerification.lean` passes ten
regressions and ten enforced standard-three axiom audits. The existing
integrated verification passes 1255 declaration checks, 565 examples and
1147 axiom reports without warnings or errors; all reported axioms are
within `propext`, `Classical.choice` and `Quot.sound`. The finite norm/Chow,
localization, marked-cycle, supported-class and proof-dependency suites
also pass. Local links, notation-table widths, the active-library
proof-placeholder scan and `git diff --check` pass. These are working-tree
checks; release sign-offs remain in `RELEASE_CHECKLIST.md`.

Status: `OPEN`. Flat pullback and its degree law, general Betti pullback/trace
and the same-cover cycle-class square, and prescribed Hodge-class generation
remain unfinished. Functorial pushforward alone supplies none of these inputs.

## Chern-character trial (SP112)

Status: `FORMAL` from explicit transfer data. `RationalDegreeTransfer.pull_injective`
and `pull_eq_zero_iff` derive injectivity and zero detection from the existing
positive-degree law. No new public object or source axiom is introduced.

Status: `LITERATURE` and mathematical deduction. Algebraic bounded coherent
complexes on the open extend to perfect complexes on smooth projective $X$.
Their Chern characters can therefore feed SP108. The tested finite-monodromy
bundles have zero positive rational Chern character, by trivialization and
transfer. This rules out that particular source of a nonzero open class.

Status: `OPEN`. Constructing the algebraic complex with the prescribed open
class, general Chern/Betti comparison, and geometric flat pullback remain
unimplemented. A holomorphic complex on a Stein open is not supplied with
an algebraic extension. See the [trial](TARGET_BRIDGE.md#chern-character-trial-within-the-cycle-induction-sp112).

Validation: full `lake build` passes (3271 jobs; the two existing
`Challenge.lean` placeholder warnings remain). Both new transfer theorems
pass the enforced standard-three axiom audit; notation and local-link checks
also pass.

## Supported-class extraction (SP111)

Status: `CONDITIONAL`. `Realization/Chow/SupportedClass.lean` proves the
component-expansion class formula, extraction of an actual homogeneous
cycle on a closed support from open vanishing, and the reverse implication
under the cycle-class/restriction square. The cohomological basis,
localization equality and fundamental-class comparison are explicit
hypotheses. Finite expansion, graded closed pushforward, the ambient Chow
quotient and cycle-level zero restriction use existing constructed objects.
The three theorems introduce no new public object or source axiom.

Validation: full `lake build` passes (3271 jobs; the two existing
`Challenge.lean` placeholder warnings remain). The focused verification
passes four examples and three enforced axiom audits.

Status: `OPEN`. Constructing general supported Betti cohomology, deriving
its component basis from a codimension bound, and finding an algebraic
support off which the prescribed class vanishes remain unfinished.

## Open representative investigation (2026-10-13)

Status: `LITERATURE` and mathematical deductions, **not new Lean theorems**.
The [smooth ample boundary calculation](TARGET_BRIDGE.md#open-representative-the-smooth-ample-boundary-calculation)
constructs the zero open cycle when $2p>\dim Y$. In the complementary
range, weak Lefschetz, Gysin exactness and hard Lefschetz identify the
restriction kernel with the Lefschetz image and prove injectivity on the
primitive summand. This excludes killing a nonzero primitive class by
varying smooth divisors in powers of a fixed polarization, including after
finite pullback with the pulled-back polarization. It does not exclude
nonzero open cycles or other auxiliary constructions.

Status: `OPEN`. A cycle representing an arbitrary prescribed primitive
open class has not been constructed. Under the remaining SP108 hypotheses,
existence of an open representative is equivalent to algebraicity of the
ambient class. The general realization, degree comparisons and supported
Hodge lift remain uninstantiated. No new assumptions, production objects or
formal coverage claims are added by this investigation.

## Actual open/closed Chow localization (SP110)

Status: `FORMAL`. The L1--L3 stream is implemented on the existing cycles,
principal relations and Chow quotients. `Cycles/OpenClosedLocalization.lean`
constructs the reduced closed complement of the actual open image and
proves boundary image equals restriction kernel on raw and homogeneous
cycles. This works over any coefficient semiring, without Noetherianity or
ambient reducedness. Closed pushforward preserves the original coefficients;
the source dimension function is the actual restricted grading.

`Cycles/PrincipalRelationLifting.lean` lifts an open relation carrier by
reduced closure and its unit by the inverse of the actual function-field
equivalence. Restriction recovers the original datum. The integral and
rational relation spans therefore map onto the open relation spans.
`Cycles/ChowLocalization.lean` subtracts a lifted relation and applies
cycle exactness to prove kernel equals boundary image on both actual Chow
quotients. Only the ambient scheme is assumed Noetherian; both sources
inherit it. Existing open surjectivity completes the right-exact sequences.
This is [Stacks 02RX](https://stacks.math.columbia.edu/tag/02RX) for the
repository's Noetherian, dimension-function-graded convention.

`ChowLocalization.ofOpenComplement` proves the existing input package for
these exact rational maps, enabling its two-lift consumer without a supplied
exactness premise. It is a named theorem, not a blanket instance. Closure
does not descend to a Chow section; closed Chow pushforward need not be
injective. This additive result neither constructs Betti/Gysin maps nor
proves projector idempotence or prescribed Hodge-class generation.

Validation: full `lake build` passes (3270 jobs; only the two pre-existing
`Challenge.lean` warnings). `research/ChowLocalizationVerification.lean`
passes seven focused checks and the standard-three axiom allowlist for all
twenty new public declarations. Checks cover full/empty opens, reduction of
a possibly nonreduced ambient scheme, a nonzero boundary cycle, trivial
coefficients, integral full-open exactness, the existing rational two-lift
consumer and marked-recipe boundary ambiguity. The registry covers all 909
public object declarations in 1040 classified rows; table structure, local
links, new-file placeholder scan and `git diff --check` pass. Historical
full `research/Verification.lean` results retain their SP107 scope.

## Marked cycle-to-Chow map (SP109)

Status: `FORMAL` for the construction from supplied cycles. In
`Realization/Chow/MarkedCycleMap.lean`, `MarkedSheetChow.cycleMap` forms a
finite rational combination of actual homogeneous cycles on a fixed
ambient scheme; `chowMap` takes its class in the existing principal-relation
quotient. The marked element gives $[C_{s_0}]-\sum_s[C_s]$. The image is
exactly the rational span of the nonmarked cycle classes. Componentwise
rational equivalence preserves the whole map. Open restriction and finite
Chow pushforward commute with it, using the actual scheme maps already
constructed. Degree and dimension remain arbitrary.

The image after any supplied linear realization is also computed exactly.
Reweighting the supplied cycles realizes any residual input at the canonical
marked vector. These are linear constructions; they assume neither a
multiplicative residual map nor a new correspondence algebra. The family
of cycles, a geometric Betti realization, and selection for a prescribed
Hodge class remain inputs or `OPEN` obligations. No cover or incidence
family is inferred from the sheet labels, and no new Hodge case is proved.

Validation: the full `lake build` passes (3267 jobs; only the two
pre-existing `Challenge.lean` placeholder warnings). The five checks in
`research/MarkedCycleMapVerification.lean` pass: marked-support vanishing,
signed rational weighting, actual principal-relation invariance, nonzero
generic-degree output on an arbitrary integral Noetherian scheme, and the
exact existing generation condition. All twelve new public declarations
pass the standard-three axiom allowlist. The notation registry covers all
908 public object declarations, with 1036 classified rows; table structure,
local links and the new-file placeholder scan pass. The earlier full
`research/Verification.lean` run retains its SP107 scope.

## Conditional boundary correction on actual Chow groups (SP108)

Status: `CONDITIONAL`. In `Realization/Chow/BoundaryCorrection.lean`,
`exists_boundary_correction` proves that an ambient cycle agreeing with a
prescribed Hodge class on the open can be corrected by a boundary cycle.
Its inputs are a supported Hodge lift, algebraicity on the boundary, and
cycle-class compatibility with boundary pushforward.
`isAlgebraicHodgeClass_of_openRestriction` first lifts an open cycle;
`isAlgebraicHodgeClass_of_schemeOpenRestriction` uses the actual rational
Chow groups, open restriction and its proved surjectivity, and closed
pushforward with the induced dimension function. No new quotient, model
record, projector or Chow-exactness hypothesis is introduced.

For a smooth divisor, boundary algebraicity can be the codimension-$p-1$
induction hypothesis, uniformly in dimension. The open representative,
general Betti/Gysin realization and comparison squares, supported Hodge
lift, and suitable boundary geometry remain application obligations. This
does not complete the induction or cover a new class of varieties.
Validation: `lake build` passes (3266 jobs; only the two pre-existing
`Challenge.lean` placeholder warnings). `BoundaryCorrectionVerification.lean`
passes eight checks, including a nonzero correction through a noninjective
boundary map, failure without boundary algebraicity, and composition with
normalized descent. All three new production theorems pass the enforced
standard-three axiom allowlist. The notation tables, public-object name
coverage, local links and new-file proof-placeholder scan pass. The earlier
full `research/Verification.lean` run is the SP107 checkpoint below; it was
not repeated for this addition.

## Finite scheme norm identity and Chow descent (SP107)

Status: `FORMAL`. `Cycles/FinitePrincipalDivisor.lean` proves
`finitePushforward_principalDivisor`:
`finitePushforward ℤ f (principalDivisor X g) = principalDivisor Y (functionFieldNorm f g)`.
Here `f : X → Y` is finite and dominant, both schemes are integral,
locally Noetherian and quasi-compact, and `Y → Spec k` is locally of finite
type for a field `k`. This is the finite specialization of
[Stacks 02RT](https://stacks.math.columbia.edu/tag/02RT), using the proved
02MJ identity. No normality, freeness or separability is assumed.

The proof localizes the whole affine inverse-image algebra at the target
prime. Its maximal localizations identify with actual source stalks, with
compatible embeddings into the original function field. Quotient residue
degrees identify with actual scheme residue degrees and with the existing
support-to-image weights. The existing finite-type codimension formula
supplies the codimension-one comparison. Individual source stalks are not
assumed module-finite over the target stalk.

`finitePushforward_ambientPrincipalDivisor` applies this identity to the
actual finite dominant support-to-image map. `PrincipalRelationData.finiteImage`
constructs its norm relation. `FiniteChowPushforward.lean` and
`RationalFiniteChowPushforward.lean` prove relation-span preservation and
construct `chowFinitePushforward` and `rationalChowFinitePushforward` on the
existing canonically graded quotients. These maps require Noetherian
ambient schemes and a locally finite-type structural map to a field;
ambient integrality and dominance are unnecessary. They take no supplied
grade-compatibility or relation-preservation premise. The class-map
squares, agreement with the integral closed-immersion map, and commutation
with `chowRationalize` are proved.

Validation: the full build passes (3265 jobs), with only the two
pre-existing `Challenge.lean` placeholder warnings.
`research/FiniteNormChowVerification.lean` passes signed inverse-divisor,
rational-equivalence and quotient-hypothesis checks, and an enforced
standard-three axiom allowlist for all 67 new public declarations.
The SP106 numerical norm regressions (including orders `1` and `-1`)
and their nine-declaration audit also pass. The main root-import inventory
passes all 1255 declaration checks, 565 examples and 1147 axiom reports,
without warnings or errors; its reported axioms stay within the standard
three. The semantic table structure, LaTeX delimiters, source links and
project proof-token scan pass. These are working-tree checks, not a
clean-clone or human release sign-off.

At SP107, finite-pushforward composition remained open; SP113 now proves it
for these same maps. The finite flat checkpoint above also proves Chow
pullback and its degree law. Status: `OPEN` for more general flat pullback,
actual Betti transfer and cycle-class compatibility, and class-dependent
geometric generation. This checkpoint does not prove the
general proper-morphism version of 02RT or a Hodge-conjecture instance.

## Full weighted norm--order formula (SP106)

Status: `FORMAL`. `Cycles/LocalOrderNormFormula.lean` proves
`localOrder_norm_eq_sum`: for a finite domain extension over a Noetherian
local domain of dimension at most one, and every unit `y` of the original
fraction field `L`,
`ord_R(Norm_L/K(y)) = ∑ᶠ q, [B/q : R/m] * ord_Bq(y)`.
This is [Stacks 02MJ](https://stacks.math.columbia.edu/tag/02MJ), also
allowing a field as the base. Both sides use the existing `Algebra.norm`
and `localOrder`; the right-hand sum is proved finite.

`CommutativeAlgebra/FiniteSemilocal.lean` derives contraction of maximal
ideals, finite residue degrees and semilocality from module-finiteness over
the local base. Its semilocal proof needs neither Noetherianity nor a domain.
The dimension bound for integral domain extensions is also proved.
`CommutativeAlgebra/AtPrimeFractionField.lean` constructs scoped canonical
actions of each prime localization on the original fraction field and
proves their scalar towers and fraction-field properties. The endpoint
derives upstairs Noetherianity and the dimension bound; it requires no
supplied semilocal enumeration, residue-finiteness proof or localization
action, and no normality, freeness or separability assumption.

Validation: `research/NormLocalOrderVerification.lean` checks derived
semilocality for the nonlocal finite algebra `ℚ × ℚ`, then applies the
complete formula at the localization of `ℤ` at `(2)` to obtain weighted
sums `1` and `-1` for `2` and its inverse. All nine new public declarations
pass the standard-three axiom allowlist. The full build passes (3246 jobs),
as does the refreshed SP105 localized-quotient suite and its eight-declaration
axiom audit. Only the pre-existing `Challenge.lean` placeholder warnings remain.

Status at SP106: `OPEN`; SP107 above completes the finite scheme identity
and integral/rational Chow descent. Fixed-target realization and
class-dependent geometric generation remain separate.

## Localized principal quotients (SP105)

Status: `FORMAL`. `CommutativeAlgebra/LocalizedPrincipalQuotient.lean`
proves the canonical `Localization S`-linear equivalence
`LocalizedModule S (B/(b)) ≃ Localization S/(b/1)`, its formulas on
representatives and arbitrary fractions, and length preservation. It
specializes Mathlib's module-quotient localization, corresponding to
[Stacks 02C8](https://stacks.math.columbia.edu/tag/02C8). This part holds
for every commutative ring, submonoid and generator, including zero
divisors and zero localizations. Inverting the generator gives length zero.

`Cycles/LocalOrderLocalization.lean` proves that each such length at a
prime computes the existing `localOrder`, and gives the signed fraction
formula and vanishing outside the prime. Here `B` is a Noetherian domain
of dimension at most one. The dimension bound after localization and the
fraction-field property are derived; the supplied localization action on
the original fraction field must form the actual scalar tower. Normality
and valuation-ring assumptions are not used.

Validation: the focused suite
`research/LocalizedPrincipalQuotientVerification.lean` checks an actual
denominator, inversion in `ZMod 4`, and length one for the localized integer
quotient at `(2)`. All eight public declarations pass the standard-three
axiom allowlist. The full build passes; its only proof-placeholder warnings
are the pre-existing ones in `Challenge.lean`.

Status at SP105: `OPEN` (the local formula is completed in SP106 above).
Derive the semilocal, lying-over, residue-degree and
localization-tower data from the finite extension, and assemble the full
02MJ statement before transporting it to the scheme divisor identity 02RT.
Chow descent and class-dependent generation remain separate.

## Semilocal lengths and determinant/norm comparison (SP104)

Status: `FORMAL`. `CommutativeAlgebra/SemilocalLength.lean` proves the full
finite-length sum of [Stacks 02M0](https://stacks.math.columbia.edu/tag/02M0)
over the actual `LocalizedModule`s. For a local base, maximal ideals lying
over its maximal ideal and finite residue extensions, the weights are the
canonical quotient-field degrees. No Noetherian or domain assumption is
needed for this length formula.

`CommutativeAlgebra/LatticeIndex.lean` proves finiteness of the relevant
quotients, the relative-index addition law, invariance under linear
equivalence and independence from the lattice. `Cycles/LocalOrderDeterminant.lean`
proves `latticeIndex_eq_localOrder_det` and the stable-lattice cokernel
formula. This is the comparison of
[Stacks 02MI](https://stacks.math.columbia.edu/tag/02MI), using the existing
`Submodule.IsLattice` and existing `localOrder`. Its Lean hypotheses allow
any Noetherian domain of dimension at most one with its fraction field.

`Cycles/LocalOrderNorm.lean` constructs the actual image of a finite algebra
`B` in its fraction field `L` as a lattice over `R`, and derives finite
dimensionality over `K = Frac(R)`. It proves
`ord_R(Norm(b)) = length_R(B/bB)` for nonzero `b`, the signed fraction
formula, and the residue-degree-weighted sum of localized quotient lengths.
The semilocal consumer explicitly takes finiteness of the maximal spectrum,
the lying-over conditions and finite residue degrees. At SP104 these were
not yet derived automatically; SP106 above now supplies them. Freeness,
normality and separability are absent from the hypotheses; the norm is
Mathlib's actual `Algebra.norm`.

At SP104, status: `OPEN`. Identify localized principal quotients with principal
quotients of localized rings, assemble the full weighted local-order law
02MJ under its finite-extension hypotheses, and transport it to the actual
scheme principal-divisor pushforward 02RT. Finite Chow descent, the same-cover
Betti compatibility laws and class-dependent generation remain separate.

Validation: the full build passes (3241 jobs), with only the pre-existing
`Challenge.lean` proof-placeholder warnings. The focused suite in
`research/SemilocalNormVerification.lean` checks a two-component semilocal
ring, an arbitrary lattice's inverse sign and stable quotient, and the
actual norm orders of `2` and `1/2` over `ℤ ⊂ ℚ`. All 31 public declarations
in the four modules pass the standard-three axiom allowlist. The central
declaration inventory is extended; no manuscript update is claimed.

## Local residue-degree length comparison (SP103)

Status: `FORMAL`. `CommutativeAlgebra/LocalLength.lean` proves restriction
of finite length along a local homomorphism with finite residue degree:
`length_A M = [κ(B):κ(A)] * length_B M`, with finiteness over `A`.
The rings may have nilpotents and need not be Noetherian. The residue
degree uses Mathlib's canonical map of residue fields.

`Cycles/LocalOrderLength.lean` applies this to the existing principal
quotients and signed fraction orders when `B` is a Noetherian domain of
dimension at most one. Normality, separability and freeness are not premises.
The six public declarations introduce no replacement order, cycle carrier,
norm operation or source-input proposition.

At SP103, status: `OPEN`. The semilocal localization sum, lattice/determinant
comparison, norm-order identity, principal-divisor pushforward and resulting
finite Chow pushforward remain unproved. SP103 establishes the local length
component, not those subsequent results or class-dependent generation.

Validation: the scoped build and full `lake build` pass (3235 jobs for the
full build), with only the existing `Challenge.lean` warnings. The five
examples in `research/LocalLengthVerification.lean` check finite-algebra
specialization, principal-quotient finiteness, the inverse-order sign and
agreement with field degree and dimension. All six public declarations
pass the axiom allowlist, each using exactly `propext`, `Classical.choice`
and `Quot.sound`. The central declaration inventory is extended; no full
historical verification replay or manuscript update is claimed.

## Canonical finite-map grading (A11ch / SP102)

Status: `FORMAL`. Five public theorems in `Cycles/FiniteResidueField.lean`
and `FiniteGrading.lean` discharge the degree-compatibility premise of SP101
for the existing canonical field-induced grading.

The literal residue map of a finite morphism is algebraic on arbitrary
schemes. No ambient integrality, dominance, normality, Noetherianity,
etaleness, separability or structural field is required. With a structural
field map, the two existing base actions and the original residue map form
the scalar tower supplied by `residueFieldBaseMap_comp`. The resulting
transcendence-degree equality is at the cardinal level and requires no
locally finite-type structural hypothesis.

Locally finite type of the target structural map supplies the existing
dimension function; the source has the composite structural map. Pointwise
equality and the old image-generic-point identity give image-support degree
equality. The existing finite pushforward preserves the canonical homogeneous
cycles over every semiring without a supplied `hdeg`. Independently chosen
dimension functions retain SP101's explicit compatibility requirement.

The manuscript counterpart is `prop:finite-field-grading`, with the actual
map `f_x^#`, existing `δ_{X/k},δ_{Y/k}` and unchanged `f_{*,cyc}`. No new
field, scalar-action definition, dimension function, cycle carrier,
pushforward, global instance, project axiom or literature package is added.
Finite-dimensionality or separability of the residue extension, finite
stalk maps, codimension preservation, principal/norm compatibility, Chow
descent, finite-map composition, Betti compatibility and generation are
not new conclusions of this checkpoint. No object is removed or archived.

The residue/grading scoped builds pass 2331/2859 jobs without warnings.
The focused suite passes twenty examples, five declaration checks and five
axiom audits; every observed set is exactly `propext`, `Classical.choice`
and `Quot.sound`. The full build passes 3233 jobs with only the unchanged
Challenge warnings at lines 33 and 46. The dependency audit passes six
primary contracts and two supporting reports. The fresh SP101 regression
passes thirty examples, twenty checks and twenty axiom audits, with exactly
the standard three and no warnings. No additional fresh neighbor-suite run
or full historical central replay is claimed.

Independent scope/source review and five-API parity pass. The 97-page PDF
(905084 bytes) has a clean final log and visually checked pages 40, 54, 55,
79 and 90. The central static inventory is 1134 checks, 565 examples and
1026 axiom reports. Both complete historical prefixes and the SP101-to-EOF
queue record remain byte-identical to `41f15b3`. SP102 is validated.

## Degree-weighted finite cycle pushforward (A11cg / SP101)

Status: `FORMAL`. `Cycles/FinitePushforward.lean` and
`GradedFinitePushforward.lean` provide twenty public APIs on the existing
cycle carrier. The general integral image is literally `W.val.map f`,
identified with the reduced closure of `f(ξ_W)` and with the old closed
image whenever that construction applies. For a finite support map, its
original `toImage` map is finite and dominant. The actual function-field
extension supplies the positive degree, rather than a chosen multiplicity.

The raw map for any finite `f` sends `[W]` to `[K(W):K(f(W))] [f(W)]` over
any coefficient semiring. It agrees with closed-immersion pushforward and
the identity map. Ambient integrality, normality, dominance, Noetherianity,
etaleness and separability are not required. The graded map is the literal
restriction to existing `cyclesOfDegree` for explicitly compatible
dimension functions. Integer-to-rational coefficient extension commutes
with both raw and graded maps.

The manuscript counterpart is `prop:finite-cycle-pushforward`, with
`q_W`, `d_f(W)` and the existing `f_{*,cyc}` notation. No replacement cycle
module, relation space, field or degree is supplied, and no project axiom
or literature hypothesis is introduced. The raw map is new because the
old map was limited to closed immersions; their agreement is proved.
Canonical field-grading compatibility, finite-map composition and norm
preservation of the actual principal relations are not proved here.
Neither a general Chow map nor Betti compatibility or generation follows
from this checkpoint. No object is removed or archived.

Scoped raw and graded builds pass 2779 and 2820 jobs respectively, without
warnings. The corrected focused suite passes 30 examples, twenty declaration
checks and twenty axiom audits; every observed set is exactly `propext`,
`Classical.choice` and `Quot.sound`. The full build passes 3231 jobs with
only the unchanged Challenge warnings at lines 33 and 46. The dependency
audit passes six primary contracts and two supporting reports.

Fresh SP72 and SP88 regressions pass respectively 18 examples/eleven axiom
audits and twenty examples/two axiom audits, without warnings. Every observed
axiom set is exactly the standard three. No other fresh neighbor-suite pass
or full historical central replay is claimed.

Independent scope review and twenty-API parity pass. The 96-page PDF
(901510 bytes) has a clean final log and visually checked pages 40, 41,
75 and 88. The central static inventory is 1129 checks, 565 examples and
1021 axiom reports. Both complete historical prefixes and the SP100-to-EOF
queue record remain byte-identical to `85662d0`. SP101 is validated.

## Sheet points and the original normalization action (A11cf / SP100)

Status: `FORMAL`. Four public theorems in `GenericSplitFiberAction.lean`
compare individual evaluations in the existing sheet algebra with the
original scheme maps. For finite dominant formally unramified `p:Y→X`
between integral schemes, evaluation at `s` followed by SP99's isomorphism
has `Y`-projection `Spec(D.sheetEmbedding s)` followed by the generic map,
and `N_p`-projection the identity. These statements need no normality.

With the existing normal-stalk input on `Y`, the sheet `gH` maps to `Y`
by `λ ∘ a_{N_p}(g⁻¹) ∘ γ_{N_p}`, where
`γ_{N_p}=ι_{η_Z} ∘ Spec(e_{N_p})` uses the original field comparison.
This identity of maps to `Y` needs only finite dominance, integral schemes
and normal stalks upstairs; no formal unramifiedness is used. Combining
it with the evaluation projections identifies the full pullback point.

All fields, markings, evaluators, actions, normalization models and the
SP99 comparison remain unchanged. There is no new public construction or
global instance, and no new commutative/tensor algebra or separability proof.
Two module-local instance bridges reuse the existing base-surjectivity
theorem and actual function-field algebra for elaboration.
The manuscript counterpart is `prop:split-fiber-sheet-action`, with
`ε_s^{N_p}`, `ξ_{p,s}`, `γ_{N_p}` and the existing `a_{N_p},λ,e_{N_p}`.
The new generic map notation does not reuse `j_N`, already assigned to
the normal closure's inclusion into the ambient algebraic closure.
No base-normality, Noetherian or perfect-field premise is added.

The result identifies the labelled points, not an unspecified action on
the whole fiber or a `G`-deck action on `Y` for nonnormal `H`. It does not
prove an arbitrary-geometric-fiber, torsor or Chow--Betti generation theorem.
No object is removed or archived.

Scoped validation passes 2795 jobs without warnings. The corrected focused
suite passes 18 examples, four declaration checks and four axiom audits;
each observed set is exactly `propext`, `Classical.choice` and `Quot.sound`.
The full build passes 3229 jobs with only the unchanged Challenge warnings
at lines 33 and 46. The dependency audit passes six primary contracts and
two supporting reports.

Fresh SP99 and SP93 regressions pass respectively 18 examples/four checks/
four axiom audits and 35 examples/19 checks/19 axiom audits, without warnings;
every observed axiom set is exactly the standard three. SP99's two
dependency-direction checks also pass. No other fresh neighbor-suite pass
or full historical central replay is claimed.

Independent production/manuscript/documentation scope review and all four
API parity checks pass. The 96-page PDF (898680 bytes) has a clean final
log and passes visual review of pages 23, 24, 71 and 84. The central static
inventory is 1109 checks, 565 examples and 1001 axiom reports. Both complete
historical prefixes and the SP99-to-EOF queue record remain byte-identical
to `5b0572c`. SP100 is validated.

## Marked split generic fiber (A11ce / SP99)

Status: `FORMAL`. Four public APIs in `GenericSplitFiber.lean` identify
the spectrum of the existing sheet algebra with the actual generic base
change over the original `N_p`. The assumptions are finite dominant formally
unramified `p:Y→X` and integral `X/Y`; the actual field algebra uses `κ_p`.
The normal-closure datum, fixing subgroup and marked embedding are exactly
those of `functionFieldNormalClosureData p`.

The comparison is `Spec` of the existing tensor/sheet equivalence followed
by SP98's canonical pullback comparison. Its two projections are the
spectrum of the original sheet-embedding map followed by the generic-stalk
map, and the spectrum of the constant-function map. The base-sheet point
maps to the actual pullback lift of the marked embedding and the identity.
Actual separability and the augmentation square are reused, not hypotheses
to be supplied or results reproved here. No new tensor algebra, evaluator,
field, cover, marking or action is introduced.

The manuscript counterpart is `prop:marked-split-generic-fiber`, with
comparison `ψ_p`, sheet map `j_p`, constant map `c_p`, base-sheet point
`b_H` and marked generic map `y_ι`. No normality, Noetherianity, perfectness
or separate Galois hypothesis is added. Individual sheet/action comparison,
arbitrary geometric fibers, torsors and same-cover Chow--Betti generation
are not consequences claimed here. No object is removed or archived.

Scoped validation passes 2753 jobs. The corrected focused suite passes
18 examples, four declaration checks and four axiom audits, each observed
set exactly `propext`, `Classical.choice` and `Quot.sound`, without warnings.
Two transitive declaration audits verify the dependency direction:
actual separability uses the established unramifiedness/Mathlib inputs,
not the named downstream collision or splitting declarations; the new
isomorphism uses that separability and the existing tensor equivalence.

The full build passes 3228 jobs with only the unchanged Challenge warnings
at lines 33 and 46. The dependency audit passes six primary contracts and
two supporting reports. Fresh SP98 and separability regressions pass
19 examples/one axiom audit and 16 examples/three axiom audits respectively,
each observed set exactly the standard three, without warnings. No other
fresh neighbor-suite pass is claimed.

Independent production/manuscript/documentation scope review and all four
API parity checks pass. The 94-page PDF (893990 bytes) has a clean final
log and passes visual review of pages 23, 24, 70 and 82. The central static
inventory is 1105 checks, 565 examples and 997 axiom reports; its historical
prefix was not re-elaborated in full. Both complete historical prefixes
and the SP98-to-EOF queue record remain byte-identical to `4cf7b71`.
SP99 is validated.

## Tensor base change of the actual generic fiber (A11cd / SP98)

Status: `FORMAL`. The single public API
`functionFieldMapOfDominant_baseChange_isPullback` in
`GenericFiberBaseChange.lean` identifies the actual base change of finite
dominant `p:Y→X` between integral schemes along `Spec E → Spec K(X) → X`.
The algebra `E` is any commutative `K(X)`-algebra. The actual upstairs
scalar map is `κ_p`, and the tensor order is `E ⊗_{K(X)} K(Y)`.
The proof pastes the tensor-spectrum pullback horizontally with SP97.

The first leg is the spectrum of the right tensor inclusion followed by
the upstairs generic-stalk map; the second is the spectrum of the left
inclusion. The existing `IsPullback.isoPullback` identifies the tensor
spectrum with the actual fiber product and retains both projections.
There is no new carrier, isomorphism wrapper, marking, action or private
support lemma. No normality, etaleness or separability is added; `E` need
not be a field, finite, reduced or nontrivial.

The manuscript counterpart is `cor:generic-fiber-base-change`, with
`T_E=E⊗_K L`, inclusions `u_E,v_E`, structure map `α_E`, base map `β_E`,
and canonical comparison `θ_{p,E}`. This does not yet identify the
normal-closure specialization with a sheet algebra or identify its
marked point; nor does it prove an all-geometric-fiber, torsor or
Chow--Betti generation statement. No object is deleted or archived.

Scoped validation passes 2738 jobs. The corrected focused suite passes
19 examples, one declaration check and one axiom audit, whose observed
set is exactly `propext`, `Classical.choice` and `Quot.sound`, without
warnings. The full build passes 3227 jobs with only the unchanged
Challenge warnings at lines 33 and 46. The unchanged dependency audit
passes six primary contracts and two supporting reports; a fresh SP97
regression passes 18 examples, two declaration checks and two standard-three
axiom audits. No other fresh neighbor-suite pass is claimed.

The production/manuscript/API parity review and bounded overlap audit pass.
The 94-page PDF (891430 bytes) has a clean final log and passes visual
review of pages 9, 10, 11, 70 and 82. The central static inventory is
1101 checks, 565 examples and 993 axiom reports; its historical prefix
was not re-elaborated in full. Both complete historical prefixes and the
SP97-to-EOF queue record are byte-identical to `cd3341a`. SP98 is validated.

## Actual generic fiber and affine function-field pushout (A11cc / SP97)

Status: `FORMAL`. Two public APIs in `FiniteFunctionField.lean` and
`GenericFiber.lean` prove the actual affine function-field pushout and
the cartesian generic-stalk square for finite dominant `p:Y→X` between
integral schemes. The affine scalar structures are the existing section
pullback, generic germs and actual function-field map; their compatibility
is proved, not separately assumed. Finite affine section algebras and
fraction-field localization give the pushout. Passing to spectra and
composing with the actual affine-preimage pullback gives the global square.

The theorem is oriented with `Y.fromSpecStalk` as first leg, so the
existing `IsPullback.isoPullback` directly gives
`Spec K(Y) ≅ Y ×_X Spec K(X)` with the original maps as projections.
No new generic-fiber carrier, isomorphism package, field or action is
introduced. Only the two chart-transport lemmas are private helpers.
There is no normality, etaleness, separability, Noetherianity or separately
supplied finite-extension premise. The manuscript counterpart is
`prop:actual-generic-fiber`; its generic points are `η_X`, and their
scheme maps are `ι_{η_X}`. The generic-extensionality proof uses the
same map notation.

This identifies the generic fiber, not the generic split fiber over `N`,
all geometric fibers, coset labels, a torsor or Chow--Betti generation.
The split comparison is the next bounded geometric step. No module or
object is deleted or archived.

Scoped validation passes 2736 jobs for the affine pushout and 2737 for
the scheme square. The focused suite passes 18 examples, two declaration
checks and two axiom audits, each observed set exactly `propext`,
`Classical.choice` and `Quot.sound`, without warnings. Independent
production, manuscript and documentation scope reviews and both API
parity checks pass. The 93-page PDF (887663 bytes) has a clean final log
and passes visual review of pages 8, 9, 10, 20, 69 and 81.

The static central inventory is 1100 checks, 565 examples and 992 axiom
reports; its historical prefix was not re-elaborated in full. Both complete
historical prefixes and the SP96-to-EOF semantic-queue record remain
byte-identical to `e6b06a7`.

The full build passes 3226 jobs with only the two unchanged Challenge
warnings at lines 33 and 46. The unchanged dependency audit passes six
primary contracts and two supporting reports. Fresh finite-function-field
and SP96 regressions pass 18 examples/11 axiom audits and 22 examples/six
axiom audits respectively; all observed sets are exactly the standard
three, without warnings. No additional neighbor-suite pass is claimed.
SP97 is validated.

## Full marked stabilizer and the original marked deck group (A11cb / SP96)

Status: `FORMAL`. Six public APIs in
`Boundary/Normalization/GluedNormalClosureStabilizer.lean` characterize
preservation of the original marked refinement by the original field
fixing subgroup, characterize the same condition for arbitrary base deck
transformations through SP95's reconstruction, and identify the existing
marked action with the full deck group over the original cover.

The hypotheses remain finite dominant `p:Y→X`, integral `X/Y`, and
integrally closed stalks of `Y`. Pullback of the preserved refinement,
followed by the existing marked field comparison, gives
`σ⁻¹(ι(c)) = ι(c)` for each `c`; applying `σ` gives the required
subgroup membership. The reverse implication is SP90's existing action.
Every deck map over `Y` is privately viewed over `X` through the original
triangle, and its reconstructed field automorphism lies in `H` by the
criterion. The marked group equivalence has literally the original
forward action; its inverse has the same actual inverse-pullback formula.

No separability, etaleness, normality of `X`, Noetherianity or finiteness
of the normalization morphism is added. No new public deck package or
source axiom is introduced. The manuscript counterpart is
`thm:normalization-marked-stabilizer`. Geometric-fiber/coset comparison,
torsor assertions, fixed-field equality and Chow--Betti generation are
not conclusions of this checkpoint. No object is deleted or archived.

The 2783-job scoped build and 3225-job full build pass. The latter has
only the two unchanged Challenge placeholder warnings at lines 33 and 46.
The focused suite passes 22 examples, six declaration checks and six
axiom audits, every actual set exactly `propext`, `Classical.choice`
and `Quot.sound`, without warnings. The 93-page PDF (885899 bytes) has
a clean final LaTeX log and passes visual review of pages 20, 21, 22,
71 and 84. Independent production and Lean--TeX scope reviews and all
six API parity checks pass. The static central inventory is 1098 checks,
565 examples and 990 axiom reports; its historical prefix is preserved,
not re-elaborated in full. Both historical prefixes and the SP95-to-EOF
semantic-queue record remain byte-identical to `864100b`.

The unchanged dependency audit passes six primary contracts and two
supporting reports. A fresh SP95 regression passes 27 examples, eight
declaration checks and eight exact standard-three axiom audits without
warnings. No other fresh neighbor-suite pass is claimed. SP96 is validated.

## Generic extensionality and the full original deck group (A11ca / SP95)

Status: `FORMAL`; all eight public APIs compile across
`Cycles/FunctionFieldExtensionality.lean` and
`Boundary/Normalization/GluedNormalizationDeckComparison.lean`.
Generic-stalk naturality identifies the restriction of any dominant
morphism of integral schemes with its actual function-field pullback.
For maps over a common base into a relatively separated target,
equality of these pullbacks implies equality of morphisms.

Thus two deck transformations of the original glued normalization agree
if their generic pullbacks agree, for arbitrary ambient `N/K(X)`.
Its existing affineness supplies relative separatedness; no separatedness
or normality of `X` is added. For finite `N/K(X)`, the reconstructed
automorphism `b_N(d)=e_N ∘ (d⁻¹)^* ∘ e_N⁻¹` fixes the actual base map.
The original action satisfies `a_N(b_N(d))=d`; its existing faithfulness
gives the other inverse identity. The resulting `MulEquiv` has exactly
the original action as forward map and the displayed reconstruction as
inverse. No separability, etaleness, Noetherianity or finiteness of the
normalization morphism is assumed.

The manuscript counterparts are `lem:generic-pullback-extensionality`
and `thm:normalization-full-deck-group`. Full marked stabilizers,
fiber/coset and torsor comparisons, actual Chow--Betti transfer and
geometric generation remain separate. This is not a new Hodge case.
No object is deleted or archived; existing forward maps are reused.

SP95 is validated: generic and deck scoped builds pass 2327 and 2780
jobs respectively. The focused suite passes 27 examples, eight declaration
checks and eight axiom audits, every actual set exactly `propext`,
`Classical.choice` and `Quot.sound`, without warnings. The full build
passes 3224 jobs with only the two unchanged Challenge placeholder
warnings at lines 33 and 46. The unchanged dependency audit passes six
primary contracts and two supporting reports. A fresh SP94 regression
passes its 26 examples, seven standard-three axiom audits and two
direct-descent dependency assertions without warnings; no other fresh
neighbor-suite pass is claimed.

The 92-page PDF (882837 bytes) has a clean final LaTeX log and passes
visual review of pages 19, 20, 21, 70 and 83. Independent production,
Lean--TeX and six-document scope reviews pass, as do all eight API parity
checks. The central static inventory is 1092 checks, 565 examples and
984 axiom reports; its historical prefix was preserved, not re-elaborated
in full. That prefix, the geometric-audit prefix and the SP94-to-EOF
semantic-queue record are byte-identical to `05d8601`.

## Arbitrary-class upstairs generation and normalized descent (A11bz / SP94)

Status: `CONDITIONAL`. Seven public APIs in
`Realization/Chow/UpstairsGeneration.lean` define the fixed-recipe
pullback-image inclusion, prove its elementwise form, define indexed
class-dependent generation, and prove degree-normalized descent to the
existing `RationalHodgeConjectureAt` target. For each prescribed Hodge
class, the witness is the explicit cycle
`degree_i⁻¹ • pushCH_i (recipe_i c)`. The Hodge subspace is specified
independently of the cycle-class map. Recipes and realization maps are
fixed before the class is quantified; the chosen index and coefficient
may vary with the class.

The existing `RationalDegreeTransfer` supplies a positive degree and the
cohomological push-pull law. Compatibility of Chow pushforward with the
cycle-class map and the generation condition are explicit theorem
hypotheses. There is no new input axiom, phantom geometric morphism,
projector package, residual-surjectivity premise, or claim that this
construction already supplies geometric transfer. The manuscript
counterparts are `def:upstairs-generation` and
`thm:upstairs-generation-descent`.

The open substantive obligations are full deck-group comparison on the
constructed cover, actual same-cover Chow--Betti maps and their laws, and
generation by the specified geometric recipes for the intended `X,p`.
The conditional implication does not prove generation or a new Hodge case.
The pruning queue distinguishes dependencies of this minimal cycle
conclusion from the live stronger projector/action endpoints; no object
is moved or deleted at this checkpoint.

SP94 is validated. The scoped production build passes 2466 jobs; the
focused suite passes 26 examples, seven declaration checks and seven
axiom audits, each with exactly `propext`, `Classical.choice` and
`Quot.sound`. Both new Hodge endpoints pass transitive-dependency checks:
they consume the existing degree law, but neither the normalized
projector nor declarations from the `LinearAlgebra`, `Boundary` or
`Correspondence` modules. The full build passes 3222 jobs with only the
two unchanged Challenge placeholder warnings at lines 33 and 46.
The unchanged dependency regression passes six primary contracts and
two supporting reports. Scoped, focused and dependency logs are clean;
no fresh neighbor-suite replay is claimed.

The single PDF has 92 pages and 880675 bytes, a clean final LaTeX log,
and visual review of pages 3, 4, 67, 80 and 81. Independent Lean--TeX and
documentation scope reviews pass. All seven public APIs occur in the
manuscript registry, semantic table and central checks/audits. The central
inventory is statically 1084 checks, 565 examples and 976 axiom reports;
its historical prefix was preserved, not re-elaborated in full. The
geometric-audit prefix and SP93-to-EOF queue record are also byte-identical
to `9539dc6`.

## Marked function-field comparison and action faithfulness (A11by / SP93)

Status: `FORMAL`; all 19 public APIs compile and the checkpoint is
validated. The checkpoint has 19 public APIs across four production
modules. For integral `X` and finite `N/K(X)`, the comparison of
the intrinsic function field of the original glued normalization with
`N` is constructed through the original nonempty affine charts and is
chart-independent. It preserves the actual structural function-field
map. The original inverse-ring action has comparison
`e(a_sigma^* b) = sigma^{-1}(e(b))`; this yields faithfulness of that
action. No ambient-field identification for arbitrary `N/K(X)` is claimed.

For finite dominant `p : Y -> X`, integral `X/Y` and normal stalks
of `Y`, the marked comparison is `e(lambda^* c) = D.embedding c`
for the original `functionFieldNormalClosureData p`. It keeps the
actual refinement, affine-preimage isomorphism, generic germs and
normal-closure marking. No normality of `X`, etaleness, separability
or Noetherianity is added. The manuscript counterparts are
`prop:normalization-function-field-comparison` and
`cor:normalization-marked-function-field`.

SP93 is validated: all 19 production APIs compile in the 2779-job
scoped build. The focused suite passes 35 examples, 19 declaration checks
and 19 axiom audits; every observed axiom set is exactly the standard
three, with no warnings. The full build passes 3221 jobs with only the
two unchanged Challenge placeholder warnings at lines 33 and 46 and
no new production warnings. The unchanged dependency audit passes six
primary contracts and two support reports without warnings. Fresh
SP92 and SP90 focused reruns pass 24 examples/four audits and 30
examples/15 audits respectively, all with exactly the standard three
axioms and no warnings; no other fresh neighbor-suite pass is claimed.
The 90-page PDF (874726 bytes) has a clean final log and passes visual
review of pages 18, 19, 69, 81 and 82. All 19 API parity checks and
independent Lean--TeX scope review pass. The static central inventory
is 1077 checks, 565 examples and 969 axiom reports; its historical
prefix is unchanged and was not re-elaborated in full.

Full deck-group reconstruction/equivalence, fiber/torsor comparison and
a full-stabilizer characterization remain separate. Normal stalks from
smooth geometry and Chow--Betti generation remain separate; this is not
a new Hodge case.

## Integrality of the original glued normalization (A11bx / SP92)

Status: `FORMAL`; all four public APIs compile and the checkpoint is
validated. Four public APIs in
`Boundary/Normalization/GluedNormalizationIntegrality.lean` prove that
any two original affine normalization chart images intersect, that the
same glued scheme is reduced and irreducible, and supply its global
`IsIntegral` instance. Integral `X` and arbitrary `N/K(X)` suffice,
without algebraicity, finite degree, separability, base normality,
Noetherianity or separatedness.

An actual nonempty common affine refinement witnesses the chart
intersection. The charts are integral because their coordinate rings
are subrings of `N`; their irreducible open images cover the scheme.
The proved intersections force irreducibility, with nonemptiness
constructed from a base chart. SP91's domain stalks imply reducedness,
and reducedness plus irreducibility imply integrality. The manuscript
counterpart is `prop:normalization-global-integral`.

All original carriers, maps, generic germs and field markings remain
fixed. The actual `N_p` specialization needs no normal-stalk premise on
`X` or `Y`. The intrinsic function field is now available, without an
asserted identification with arbitrary ambient `N`.

SP92 is validated: all four production APIs compile in the 2744-job
scoped build. The focused suite passes 24 examples and four exact
standard-three axiom audits without warnings. The full build passes
3217 jobs with only the two unchanged Challenge placeholder warnings.
The unchanged dependency audit passes six primary contracts and two
support reports without warnings. A fresh rerun of the unchanged SP91
focused suite passes its 24 examples and four exact standard-three
axiom audits without warnings; no other fresh neighbor-suite pass is
claimed. The 89-page PDF (867807 bytes) has a clean final log and passes
visual review of pages 15, 16, 67, 68, 80 and 87. All four exact API
parity checks and independent Lean--TeX review pass. The static central
inventory is 1058 checks, 565 examples and 950 axiom reports; its
historical prefix is unchanged and was not re-elaborated in full.

Next: marked function-field comparison. Faithfulness, fiber/torsor
comparison, normal stalks from smooth geometry and Chow--Betti generation
remain separate. Global integrality supplies no new Hodge case.

## Normal local rings of the original glued normalization (A11bw / SP91)

Status: `FORMAL`; all four public APIs compile and the checkpoint is
validated. Four public APIs in
`Boundary/Normalization/GluedNormalizationNormality.lean` prove normality
of the same glued scheme by proving that every actual local ring is a
domain and integrally closed. The affine coordinate-ring theorem needs
only a commutative ring `B`, a field `N`, and an algebra map `B -> N`;
neither injectivity nor normality of `B` is assumed. Integral closure
in `N` is integrally closed in `N`, and the injective map from its own
fraction field to `N` gives integral closedness in that fraction field.
It is not asserted that this embedding is onto.

Localization and the actual spectrum stalk isomorphisms give the affine
stalk result. The original chart open immersions and covering property
then transfer domain and integral-closedness properties to every stalk
of `gluedNormalizationModel X N`. These global assertions need integral
`X` and any extension `N/K(X)`, without algebraicity, finite degree,
separability, normality of `X`, Noetherianity, or separatedness. The
original scheme, chart carriers, generic germs, and marked fields remain
fixed. The manuscript counterpart is `prop:normalization-global-normal`.

Normality here is the pair of actual local-ring properties. No scheme
`IsNormal` class or global `IsIntegral` instance is introduced. For the
actual `N_p`, the specialization needs no normal-stalk hypotheses on
`X` or `Y`; the existing marked refinement still has its own hypotheses.

SP91 is validated: all four production APIs compile in the 2743-job
scoped build. The focused suite passes 24 examples and four exact
standard-three axiom audits without warnings. The full build passes
3216 jobs with only the two unchanged Challenge placeholder warnings.
The unchanged dependency audit passes six primary contracts and two
support reports without warnings; no fresh neighbor-suite pass is claimed.
The 89-page PDF (866193 bytes) has a clean final log and passes visual
review of pages 15, 16, 67, 68 and 80. All four exact API parity checks
and independent Lean--TeX review pass. The static central inventory is
1054 checks, 565 examples and 946 axiom reports; its historical prefix
is unchanged and was not re-elaborated in full.

Next: global integrality and the marked function-field comparison.
Faithfulness, fiber comparison and a torsor or Galois-cover identification
remain separate, as do normal stalks from smooth geometry and Chow--Betti
generation. Normalization normality does not prove a new Hodge case.

## Compatible global normalization and marked-subgroup actions (A11bv / SP90)

Status: `FORMAL`; all 15 public APIs compile and the checkpoint
is validated. Ten public APIs
in `Boundary/Normalization/GluedNormalizationAction.lean` preserve
the existing inverse-ring convention
`a_U(sigma) = Spec(sigma^-1 restricted to IntCl)`. For integral `X`
and any field extension `N/K(X)`, they prove compatibility with actual
chart restrictions, construct the natural diagram automorphism and
its automorphism `a_N(sigma)` of the same scheme colimit, and prove
the exact chart formula, compatibility over `X`, identity and
multiplication. The action packages as
`a_N : Aut_(K(X))(N) -> Aut_X(Z_N)` with the same underlying maps.
Its manuscript counterpart is `prop:normalization-global-action`.

Five APIs in `Boundary/Normalization/GluedNormalClosureAction.lean`
give the marked compatibility. The first is the affine statement for
the existing `NormalClosureData` and compatible scalar towers: an
automorphism in the subgroup fixing the marked intermediate field
preserves its normalization leg. Its inverse fixes that field too,
which proves the required affine ring-map equality. The four actual
consumers require finite dominant `p : Y -> X`, integral `X` and `Y`,
and explicitly integrally closed stalks of `Y` only. They transport
the identity through the actual affine chart isomorphism and exact
global chart formulas, then package the fixing subgroup into
`Aut_Y(Z_(N_p))` with the same underlying global automorphisms.
The manuscript counterpart is `prop:normalization-marked-action`.

No etaleness, normal-stalk assumption on `X`, separability,
Noetherianity or perfectness is added. The proof cancels the existing
affine normalization comparison isomorphism, not `p` from the global
triangle. No chart, carrier, field marking, scalar map, source axiom
or geometric hypothesis package is replaced or introduced.

SP90 is validated: the generic and combined action scoped builds pass
2743 and 2771 jobs. The focused suite passes 30 examples and 15 exact
standard-three axiom audits without warnings. The full build passes
3215 jobs with only the two unchanged Challenge placeholder warnings.
The unchanged dependency audit passes six primary contracts and two
support reports without warnings; no fresh neighbor-suite pass is claimed.
The 89-page PDF (864292 bytes) has a clean final log and passes visual
review of pages 17, 18, 19, 67, 68 and 80. All 15 exact API parity
checks and independent Lean--TeX review pass. The static central inventory
is 1050 checks, 565 examples and 942 axiom reports; its historical prefix
is unchanged and was not re-elaborated in full.

Remaining: global normality, faithfulness, fiber comparison and a
torsor or Galois-cover identification, normal stalks from smooth
geometry, and Chow--Betti generation. The full group acts over `X`,
and the fixing subgroup preserves `lambda`; the latter is a sufficient
condition, not a proved converse or full-stabilizer identification.
No new Hodge case is asserted by the action construction.

## Surjectivity of the original global normalization and marked refinement (A11bu / SP89)

Status: `FORMAL`; both production APIs compile and the checkpoint
is validated. Two public APIs
in `Boundary/Normalization/GluedNormalizationSurjectivity.lean` prove
surjectivity of the existing global maps under distinct hypotheses.
`gluedNormalizationToBase_surjective X N` assumes integral `X` and
any field extension of its original function field. Injectivity and
integrality of the original chart scalar map into `IntCl_B(N)` give
lying over, and SP86's target-local comparison gives surjectivity of
`mu_N : Z_N -> X`. No algebraicity or finite-degree premise on `N`,
normality of `X`, Noetherianity or separatedness is required.

`gluedNormalClosureToCover_surjective p hY` assumes finite dominant
`p : Y -> X`, integral `X` and `Y`, and explicitly integrally closed
stalks of `Y` only. It lifts a point of `Y` through SP81's original
surjective affine refinement into an entire inverse image of an
affine base chart. SP87's exact marked chart formula then gives the
global lift. No etaleness or normal-stalk premise on `X` is needed,
and surjectivity is not inferred by cancelling `p` from the triangle.

The manuscript counterpart is `prop:normalization-global-surjective`.
Under SP86/SP88's stronger finite-etale and normal-stalk hypotheses,
both original global maps are finite etale and surjective. No new
carrier, field marking, scalar map, source axiom or geometric input
package is introduced; the surjectivity theorems concern the same
`mu_N` and marked `lambda` already constructed.

SP89 is validated: both production APIs compile in the 2772-job scoped
build. The focused suite passes 24 examples and two exact standard-three
axiom audits without warnings on its first run. The full build passes
3213 jobs with only the two unchanged Challenge placeholder warnings.
The unchanged dependency audit passes six primary contracts and two
support reports without warnings. No fresh neighbor-suite pass is
claimed. The 87-page PDF (859905 bytes) has a clean final log and passes
visual review of pages 17, 18, 66, 78 and 86. Both exact API parity
checks and independent Lean--TeX review pass. The static central
inventory is 1035 checks, 565 examples and 927 axiom reports; its
historical prefix is unchanged and was not re-elaborated in full.

SP90 above supplies compatible global actions under the stated
hypotheses. Remaining: global normality,
normal stalks from smooth geometry and Chow--Betti generation. The
intended full-group action is over `X`; only the subgroup fixing the
marked `K(Y)` preserves `lambda`. No global action, global normality
or new Hodge case is asserted by SP89.

## Finite etaleness of the actual global marked refinement (A11bt / SP88)

Status: `FORMAL`; both production APIs compile cleanly and the
checkpoint is validated. Two public APIs
in `Boundary/Normalization/FiniteEtaleGluedRefinement.lean` establish
generic finite cancellation and finite etaleness of the original
global marked refinement. `isFinite_of_comp_of_isSeparated` assumes
only finiteness of `f` followed by `g` and separatedness of `g`.
It does not require `g` finite or any integral, normality, Noetherian
or field hypotheses.

`gluedNormalClosureToCover_finite_etale p hX hY` retains the actual
`lambda = gluedNormalClosureToCover p hY`. Its hypotheses are integral
`X` and `Y`, dominant finite etale `p : Y -> X`, and explicitly
integrally closed stalks on both schemes. SP87's triangle identifies
`p lambda` with SP86's finite-etale `mu_(N_p)`. Finiteness of `p`
supplies separatedness; finite cancellation and standard etale
cancellation prove the two asserted properties of `lambda`.
The manuscript counterpart is
`cor:normal-closure-refinement-finite-etale`.

The SP87 construction retains its weaker finite-dominant and `hY`
scope. SP88 adds inputs only to prove properties of that map; it does
not re-glue, replace a chart or normalization carrier, change the
original field marking or germ-derived scalars, or introduce a new
source axiom. Stacks 035D and 02GW state the standard cancellation
facts used in the manuscript; the Lean theorems are proved from the
existing Mathlib interfaces.

SP88 is validated: both production APIs compile cleanly on the first
2773-job scoped build. The focused suite passes 20 examples and two
exact standard-three axiom audits without warnings on its first run.
The full build passes 3212 jobs with only the two unchanged Challenge
placeholder warnings. The unchanged dependency audit passes six primary
contracts and two support reports without warnings. No fresh neighbor-suite
pass is claimed. The 86-page PDF (856518 bytes) has a clean final log
and passes visual review of pages 16, 17, 65, 77 and 84. Both exact
API parity checks and independent Lean--TeX review pass. The static
central inventory is 1033 checks, 565 examples and 925 axiom reports;
its historical prefix is unchanged and was not re-elaborated in full.

SP89 above supplies surjectivity under the stated weaker hypotheses.
Remaining: compatible Galois-action descent, global
normality, normal stalks from smooth geometry and Chow--Betti
generation. The full Galois group acts over `X`; only the subgroup
fixing the marked `K(Y)` preserves `lambda`. No new global action,
surjectivity, global normality or Hodge case is asserted by SP88.

## Descent of the original marked refinement (A11bs / SP87)

Status: `FORMAL`; all five production APIs compile cleanly and the
checkpoint is validated. Five public APIs
in `Boundary/Normalization/GluedNormalClosureRefinement.lean` form the
cocone of original marked affine refinements and descend it to the
actual global `lambda : Z_(N_p) -> Y`. The exact marked chart formula
identifies `lambda jmath_U` with `iota_(V_U) lambda_U`, where
`V_U = p^-1(U)` and `iota_(V_U) : V_U -> Y` is the actual open inclusion. The global triangle
`p lambda = mu_(N_p)` is proved, as is uniqueness among maps satisfying
those same marked chart formulas. The triangle alone is not the
uniqueness hypothesis. The manuscript counterpart is
`prop:normal-closure-marked-refinement`.

The hypotheses are integral `X` and `Y`, finite dominant `p : Y -> X`,
and explicitly integrally closed stalks of `Y` only. No etaleness,
normal-stalk assumption on `X`, Noetherianity or perfectness is needed.
The field is the original marked
`N_p = normalClosure K(X) K(Y) (AlgebraicClosure K(Y))`, using the
generic map induced by `p`. All normalization carriers and
germ-derived scalar maps are retained. There is no source axiom or
new geometric input package: the proved actual restriction square and
the existing colimit mapping property construct the cocone and its map.

SP87 is validated: all five production APIs compile cleanly in the
2769-job scoped build. The focused suite passes 24 examples and five
exact standard-three axiom audits without warnings on its first run.
The full build passes 3211 jobs with only the two unchanged Challenge
placeholder warnings. The unchanged dependency audit passes six primary
contracts and two support reports without warnings. No fresh older
neighbor-suite pass is claimed. The 86-page PDF (854782 bytes) has a
clean final log and passes visual review of pages 13, 14, 16, 17, 65
and 77. All five exact API parity checks and independent Lean--TeX
review pass. The static central inventory is 1031 checks, 565 examples
and 923 axiom reports; its historical prefix is unchanged and was not
re-elaborated in full.

SP88 above supplies finite etaleness of the marked refinement with
its stated additional inputs. Remaining: surjectivity,
Galois-action descent, global normality,
normal stalks from smooth geometry, and Chow--Betti generation.
The full `G = Gal(N_p/K(X))` acts over `X`; only the marked subgroup
`H = Gal(N_p/K(Y))` preserves `lambda`. No global action is constructed
by SP87, and the finite-etale property of SP86's `mu_(N_p)` is not
reasserted as a proved property of `lambda` here.

## Target-local properties and actual global finite-etale normal closure (A11br / SP86)

Status: `FORMAL`; all six production APIs compile cleanly and the
checkpoint is validated. The five public
APIs in `Boundary/Normalization/GluedNormalizationProperties.lean`
prove that nonempty affine opens cover every scheme and transport any
target-local morphism property through the exact chart comparison
`e_U`. For integral `X` and any fixed extension `N` of its original
function field, this gives `P(mu_N) iff forall U, P(pi_U)`, global
`IsAffineHom mu_N`, and exact finite/etale chartwise equivalences.
The original chart map is
`pi_U = normalizedModelToBase Γ(X,U) N` followed by `hU.isoSpec.inv`.
The manuscript counterpart is `prop:normalization-target-local`.

The sixth API,
`functionFieldNormalClosure_glued_finite_etale` in
`Boundary/Normalization/FiniteEtaleGluedNormalClosure.lean`, proves
finite etaleness of the actual global map for the original marked
`N_p = normalClosure K(X) K(Y) (AlgebraicClosure K(Y))`.
Its hypotheses are an actual dominant finite etale `p : Y -> X`,
integral `X` and `Y`, and explicitly integrally closed stalks of both
schemes. The function-field map is the original map induced by `p`.
SP81 supplies the original finite-etale chart maps and the new
equivalences transport their properties to the existing glued map.
The manuscript counterpart is `cor:normal-closure-global-finite-etale`.

Neither result introduces a source axiom, replacement normalization
carrier, or new geometric hypothesis package. No Noetherian or
perfect-field hypothesis is needed. Affineness does not require the
normal-stalk assumptions of the actual finite-etale specialization.

SP86 is validated: all six production APIs compile cleanly in the
2770-job scoped build. The focused suite passes 31 examples and six
exact standard-three axiom audits without warnings. The full build
passes 3210 jobs with only the two unchanged Challenge placeholder
warnings. The unchanged dependency audit passes six primary contracts
and two support reports without warnings. No fresh older neighbor-suite
pass is claimed. The 86-page PDF (852527 bytes) has a clean final log
and passes visual review of pages 15, 16, 65, 77, 82, 83 and 84. All
six exact API parity checks and independent Lean--TeX review pass.
The static central inventory is 1026 checks, 565 examples and 918 axiom
reports; its historical prefix is unchanged and was not re-elaborated
in full.

SP87 above supplies descent of the marked refinement to `Y`.
Remaining: its applicable global properties and Galois-action descent,
global normality and surjectivity, normal stalks from
smooth geometry, and Chow--Betti generation. No new Hodge case follows
from the finite-etale result alone.

## Actual global inverse-image normalization charts (A11bq / SP85)

Status: `FORMAL`; seven production APIs compile cleanly and the checkpoint
is validated. `Boundary/Normalization/GluedNormalizationChart.lean` identifies
each original chart with its actual global inverse image:
`range(jmath_U) = mu_N^-1(U)` as sets and opens, and
`e_U : Z_U ~= mu_N^-1(U)` as schemes. The two inclusion identities,
the exact comparison of the restricted global map with the original
normalization map to `U`, and restriction naturality are proved without
replacing any normalization carrier, field marking or germ-derived
scalar map. The manuscript counterpart is
`prop:normalization-global-chart`.

The only ambient hypotheses remain integral `X` and a fixed field
extension of its original function field. The proof lifts a point from
the existing global open cover through a common principal neighborhood
and the existing exact transition range. It needs no finite-degree,
normality, Noetherianity, separatedness or affine-intersection premise.
The inverse-image isomorphism is then the canonical open-immersion
comparison, with its actual scheme-map compatibilities. No literature
axiom or new geometric hypothesis package is introduced.

SP85 is validated: all seven production APIs compile cleanly in the
2743-job scoped build. The focused suite passes 29 examples and seven
exact standard-three axiom audits without warnings. The full build
passes 3208 jobs with only the two unchanged Challenge placeholder
warnings. The unchanged dependency audit passes six primary contracts
and two support reports without warnings. No fresh neighbor-suite pass
is claimed. The 84-page PDF (848404 bytes) has a clean final log and
passes visual review of pages 15, 16, 64, 65, 75, 76 and 84. All seven
exact API parity checks and independent Lean--TeX review pass. The
static central inventory is 1020 checks, 565 examples and 912 axiom
reports; its historical prefix is unchanged and was not re-elaborated
in full.

SP86 above supplies target-local `IsAffineHom` and finite/etale transfer
under the appropriate hypotheses. Remaining: marked refinement and compatible
Galois-action descent, global normality, normal stalks from smooth
geometry and Chow--Betti generation. The chart isomorphisms are not a
claim about global sections of a non-affine intersection.

## Actual affine diagram and global gluing (A11bp / SP84)

Status: `FORMAL`; 16 public APIs construct the inclusion-indexed
normalization diagram and its glued scheme. `NonemptyAffineChart X`
indexes actual nonempty affine opens. The functor `F_N` uses the same
normalization models and restriction maps; `c_N` is their original
structural cocone to `X`. All diagram arrows are open immersions with
the previously proved inverse-image ranges. Common principal
neighborhoods, those exact ranges and injectivity prove locally
directedness, rather than postulating it as an input.

`Z_N = colimit F_N` is an actual scheme. The original charts map into
it by open immersions `jmath_U` forming an open cover. Their structural
maps descend to `mu_N : Z_N -> X`, with the exact original chart
formula and transition naturality. Chart points agree globally if and
only if they lift from a common smaller affine chart. Morphisms out of
the glued scheme are determined by their chart restrictions.

The only ambient hypotheses are integral `X` and a fixed field
extension of its original function field. There is no finite-degree,
normality, Noetherianity or separatedness hypothesis. The local
normalization carriers and germ-derived scalar maps are unchanged;
there is no new source axiom or geometric hypothesis package.
The Lean witnesses are `Boundary/Normalization/AffineNormalizationDiagram.lean`
and `Boundary/Normalization/GluedNormalization.lean`; the manuscript
counterpart is `prop:normalization-gluing`.

SP84 is validated: both production modules compile cleanly in
2741/2742-job scoped builds. The focused suite passes 40 examples and
16 exact standard-three axiom audits. With the unchanged SP83, SP82
and SP81 suites, the total is 125 examples and 73 audits, all clean.
The full build passes 3207 jobs with only the two unchanged Challenge
placeholder warnings. The unchanged dependency audit passes six primary
contracts and two support reports without warnings. The 84-page PDF
(845594 bytes) has a clean final log and passes visual review of pages
14, 15, 63, 64, 75, 76 and 82. All 16 API parity checks and independent
Lean--TeX review pass. The static central inventory is 1013 checks,
565 examples and 905 reports; its historical prefix is unchanged and
was not re-elaborated in full.

The exact global chart image `range(jmath_U) = mu_N^-1(U)` is supplied
by SP85 above; SP86 supplies global affine/finite/etale properties under
the appropriate hypotheses. Remaining:
marked refinement and compatible Galois-action descent, normal stalks
from smooth geometry, and Chow--Betti generation. The construction does
not identify the section normalization of a non-affine intersection
with its geometric overlap.

## Coherent actual affine inverse-image opens (A11bo / SP83)

Status: `FORMAL`; ten production APIs compile cleanly in the 2740-job
scoped build. Actual restriction has identity, composition and diamond
laws on nonempty opens. For nested nonempty affine opens `W <= U`, it
is an open immersion with image exactly `mu_U^-1(W)`, where `mu_U` is
the existing normalization structural map composed with the original
affine chart map to `X`. The only ambient hypotheses are integral `X`
and a fixed field extension of its original function field. No finite
degree, etaleness, normality, Noetherianity or separatedness is added.

The proof lifts points through neighborhoods principal in both affine
charts, uses principal injectivity, and applies the local open-immersion
criterion. No replacement normalization, field marking or input axiom
is introduced. On non-affine opens only the restriction-chain identities
are asserted, not a geometric-overlap interpretation of their section
normalizations. The manuscript proposition uses affine opens throughout.
SP83 is validated: the focused suite passes 21 examples and ten exact
standard-three axiom audits. With the unchanged SP82 and SP81 suites,
the total is 85 examples and 57 audits, all clean. The full build passes
3205 jobs with only the two existing Challenge placeholder warnings;
the unchanged dependency audit passes six primary contracts and two
support reports. The 83-page PDF (839977 bytes), final log, seven-page
visual review and all ten API parity checks pass. The static central
inventory is 997 checks, 565 examples and 889 reports; its historical
prefix is unchanged and was not re-elaborated in full.

Remaining: locally directed diagram and gluing, global marked/Galois-map
compatibility, normal stalks from smooth geometry and Chow--Betti generation.

## Same-ambient localization and actual affine restriction (A11bn / SP82)

Status: `FORMAL`; checkpoint validated. The 17 APIs in
`NormalizationLocalization.lean` construct the
same-element inclusion `rho^E_{B,C}:IntCl_B(E) -> IntCl_C(E)`, prove its
injectivity and strict identity/composition and ambient-map naturality,
and exhibit the target as the corresponding localization whenever
`B -> C` is one. The canonical tensor base-change equivalence preserves
the actual ambient/scalar formula. Compatible scalar maps encode
invertible denominators in `E`; normality, Noetherianity and finite
degree are not additional hypotheses. Contravariant `j^E=Spec(rho)`
has structural/naturality squares and identity/composition laws.
Principal localization gives an open immersion with exact inverse-image
range; arbitrary multiplicative-set localization is not asserted open.

The nine APIs in `AffineNormalizationRestriction.lean` derive actual
section scalar towers, construct restriction and structural squares,
prove principal-open localization/open immersion and naturality of the
whole-preimage normalization isomorphism. The two APIs
`finiteEtaleAffineNormalClosureToChart_restriction` and
`finiteEtaleAffineNormalClosureToPreimage_restriction` in
`FiniteEtaleNormalClosureRestriction.lean` give the actual structural
and marked-refinement squares for any nonempty affine `W <= U` on the
same normal closure. The first needs dominant `p`; the second adds
finite `p` and normal stalks on the inverse images. Neither assumes
etaleness, base normality or Noetherianity. No replacement field,
marking, normalization carrier or input axiom is introduced.

All 28 APIs compile without warnings in the 2764-job scoped build. The
focused suite passes 39 examples and 28 enforced standard-three axiom
audits. Three fresh neighbor suites also pass; the four suites total
107 examples and 71 audits, without warnings or errors. The full build
passes 3203 jobs with only the two unchanged Challenge warnings. The
unchanged dependency audit passes six primary contracts and two support
reports. All 28 API parity checks and independent review pass. The
81-page PDF (835379 bytes) has a clean final log and seven-page visual
review. The static central inventory is 987 checks, 565 examples and
879 reports; its historical prefix is unchanged and was not re-elaborated
in full. The SP82 parity-queue entry records the complete validation.

Generic self/composition identities are proved; actual overlap
comparisons and cocycle assembly,
global gluing/Galois compatibility, normal-stalk hypotheses from smooth
geometry and Chow--Betti generation remain separate obligations.

## The actual finite etale affine refinement (A11bm / SP81)

Status: `FORMAL`; checkpoint validated. For a finite dominant
etale morphism `p:Y -> X` of integral schemes and a nonempty affine `U`,
`FiniteEtaleNormalClosure.lean` constructs the existing `NormalizedCover`
from the original marked function-field normal closure and the actual
inverse image `V=p⁻¹U`. Its visible map is the existing normalization
isomorphism, and its normal-closure datum is literally the original one.
Normal stalks on both opens are explicit; no Noetherianity is assumed.
The normalization structural maps to `Spec Γ(X,U)` and the actual `U`
are finite etale. The refinement to `V` uses the original marked
normalization leg and is finite etale. Its composite with `p|_U` is
exactly the chart structural map, with the original composite over `X`
also proved. Full visibility gives boundary separation.
Both maps are surjective by lying over. The separate chart-surjectivity
theorem only assumes dominant `p`, integral schemes and the nonempty
affine chart; it omits finiteness, etaleness and both normal-stalk
hypotheses. Refinement surjectivity assumes finite dominant `p` and
normal stalks on `V`, with no etaleness or base-normality premise.
The finite-etale endpoints still use both normal-stalk hypotheses.

The two tensor helpers are `piTensorProduct_ringHomProperty` in
`FiniteTensorProduct.lean` and `piTensorProduct_isEtale` in
`EtaleTensorSource.lean`. They retain the actual intermediate scheme's
local standard-smooth presentations through finite tensor products.
`NormalClosureData.normalizationTensorEvaluation_isOpenImmersion` uses
SP80's actual surjection and complementary-idempotent kernel.
`.normalizationToBase_isEtale_of_etaleModel` composes this open immersion
with the scheme-etale tensor source. No general converse from
`Algebra.Etale` to `IsEtale` is assumed.

The actual-chart interfaces are
`functionFieldNormalClosure_normalization_finite_etale`,
`finiteEtaleAffinePreimageNormalizedCover`, its `_normalClosure` formula
and `conjugateBoundarySeparation_finiteEtaleAffinePreimageNormalizedCover`;
`finiteEtaleAffineNormalClosureToBase_finite_etale`;
`finiteEtaleAffineNormalClosureToChart`, `_comp_inclusion`, `_finite_etale`,
`_surjective`;
and `finiteEtaleAffineNormalClosureToPreimage`, `_comp_normalizationIso`,
`_comp_toBase`, `_comp_restrict`, `_finite_etale`, `_surjective`. The final
inventory is 19 APIs: seventeen main declarations and two tensor helpers.
All 19 APIs compile without warnings in the 2761-job scoped build.
The 81-page PDF (831678 bytes) passes its final
warning/reference/box scan and visual checks of pages 12, 13, 61, 72 and
78; independent geometry and Lean--TeX reviews pass. The focused suite
passes 25 examples and 19 enforced standard-three axiom audits without
warnings. Five fresh neighbor suites also pass; the six suites total
146 examples and 89 enforced audits, with no warnings or errors. The
full build passes 3200 jobs with only the two unchanged Challenge
warnings. The unchanged dependency audit passes six primary contracts
and two support reports. All nineteen API parity checks pass. The static
central inventory is 959 checks, 565 examples and 851 reports; its
historical prefix is unchanged and the historical file was not
re-elaborated. The SP81 parity-queue entry records the complete validation.

No replacement field, normalization carrier, cover type, source axiom or
gluing hypothesis is added. Compatibility under
localization and on overlaps, cocycle identities, gluing and the global
Galois action remain to be proved. Deriving normal stalks from smooth
geometry and Chow--Betti generation remain separate.

## The actual integral evaluation factor (A11bl / SP80)

Status: `FORMAL`; checkpoint validated. For a normal base
domain `B` with fraction field `K`, finite `N/K`, and the actual integral
closure `T=IntCl_B(N)`, the unramified separability tensor and integral
trace construct a `B`-linear section `r:T -> S` for an actual evaluation
`f:S -> T`. The generic theorem assumes that `S/B` is formally unramified
and essentially of finite type, and that its image spans `N` over `K`.
It derives `f∘r=id` and `r(f(s)*t)=s*r(t)`. Thus `E=r(1)` satisfies
`E²=E`, `f(E)=1`, `E*s=r(f(s))`, `E*s=0 ↔ f(s)=0`, and
`ker(f)=(1-E)`. It requires neither Noetherianity of `B`, nor normality
or flatness of `S`, nor supplied evaluation surjectivity.

For `S=P_B` and the existing marked `ev_B`, SP78's evaluator square and
generic surjectivity derive the spanning condition. An actual finite
normal etale intermediate model `A/B` with fraction field `L` supplies
the finite etale tensor source. The construction gives `r_B`, its
integral selector `E_m=r_B(1)`, and `P_B/(1-E_m) ≃_B IntCl_B(N)`
preserving `ev_B` on every representative. The target is finite as this
actual quotient, and etale because the same evaluation identifies it
with localization away from `E_m`. Under separability, the base-change
comparison gives `β_Σ(1⊗E_m)=e_m`, the existing SP79 generic selector.
There is no additional separability premise in the integral-factor or
whole-ring finite-etale conclusion.

The 28 new interfaces are:

- `SeparabilityTrace.lean`: `traceContraction`, `_tmul`,
  `_eq_lmul_of_central`, `_eq_one_of_central`, and `_one_tmul_mul`.
- `UnramifiedIntegralFactor.lean`: `unramifiedIntegralSection`, `_mul`,
  `_rightInverse`; `unramifiedIntegralEvaluation_surjective`;
  `unramifiedIntegralIdempotent`, `_map`, `_mul`, `_baseChange_mul`,
  `_isIdempotentElem`, `_mul_eq_zero_iff`; and
  `unramifiedIntegralEvaluation_ker_eq_span_one_sub`.
- `NormalizationBaseChange.lean`:
  `NormalClosureData.normalizationTensorEvaluation_span`.
- `NormalizationIntegralFactor.lean`:
  `NormalClosureData.normalizationTensorSection`, `_mul`, `_rightInverse`;
  `.normalizationTensorEvaluation_surjective`;
  `.normalizationTensorIdempotent`, `_spec`, `_baseChange`;
  `.normalizationTensorQuotientEquiv`, `_mk`;
  `.normalization_finite_of_etaleModel` and
  `.normalization_etale_of_etaleModel`.

The proposed whole-source integral-closedness route is bypassed, not
proved. The trace section is a linear map with an explicit source-action
law, not a claimed unital algebra section or Chow projector. No new
tensor carrier, normalization model, field marking, geometric input
package, literature axiom, or renamed factor-selection hypothesis is
introduced. All 28 APIs compile without warnings; the full build passes
3198 jobs with only the two unchanged Challenge warnings. The focused
suite and five fresh neighbors pass 153 examples and 88 enforced
standard-three axiom audits. The unchanged dependency audit passes six
primary contracts and two support reports. The central inventory is
940 checks, 565 examples and 832 reports, with its historical prefix
unchanged and not rerun in full. The 79-page PDF (826296 bytes), eight-page
visual review and independent mathematical/Lean--TeX reviews pass; the
SP80 parity-queue entry records the complete validation.

The focused suite verifies the actual finite-etale
scheme-chart ring specialization, deriving both section-ring normality
inputs from stalks without Noetherianity. SP81 above implements the named
actual affine cover and finite-etale structural/refinement morphisms,
with validation complete. Localization/overlap compatibility, cocycles,
gluing and the global Galois action remain to be proved.
Normal stalks from smooth geometry, global finite etale Galois refinement
and Chow--Betti generation remain separate.

## The selected generic evaluation factor (A11bk / SP79)

Status: `FORMAL`; checkpoint validated. For a reduced
Artinian commutative algebra `P` and a surjective algebra map `f:P -> N`
to a field, `ReducedArtinianFactor.lean` constructs
`P ≃ N × Π_{I ≠ ker(f)} P/I` from the actual maximal-ideal decomposition.
Its first projection is exactly `f`, both pointwise and as an algebra
homomorphism. The inverse image `e` of `(1,0)` is idempotent, has `f(e)=1`,
annihilates exactly the kernel, and satisfies `ker(f)=(1-e)`. Value one
and annihilation of the kernel characterize `e` uniquely; the uniqueness
statement does not assume idempotence as an extra premise.

`NormalClosureFactor.lean` proves the existing source `P_K` finite over
`K` without separability. Under `Algebra.IsSeparable K L`, it proves
`P_K` etale, derives reduced Artinianness, and applies that construction
to the already proved surjection `ev_K`. Thus
`Φ_m:P_K ≃_K N × Q_m`, with `Q_m` the actual product of residue quotients
away from `m=ker(ev_K)`, satisfies `pr₁∘Φ_m=ev_K`. The canonical
selecting idempotent is `e_m=Φ_m⁻¹(1,0)` with the preceding properties.
No replacement tensor carrier or marked field, chosen splitting input,
literature axiom, unital section `N -> P_K` or new Chow projector is used.

The sixteen new declarations are:

- `ReducedArtinianFactor.lean`: `fieldQuotientProductEquiv`,
  `_fst`, `fst_comp_fieldQuotientProductEquiv`,
  `fieldQuotientIdempotent`, `_isIdempotentElem`, `_map`,
  `_mul_eq_zero_iff`, `_unique`, and `fieldQuotient_ker_eq_span_one_sub`.
- `NormalClosureFactor.lean`: `NormalClosureData.tensorSource_finite`,
  `.tensorSource_etale`, `.tensorEvaluationProductEquiv`,
  `.fst_comp_tensorEvaluationProductEquiv`, `.tensorEvaluationIdempotent`,
  `.tensorEvaluationIdempotent_spec`, and `.tensorEvaluationIdempotent_unique`.

Both new leaves compile without warnings; the full build passes 3195
jobs with only the two existing Challenge warnings. The focused suite
and four fresh neighbor suites pass 123 examples and 60 enforced
standard-three axiom audits. The fresh unchanged dependency audit passes
six primary endpoint contracts and two support reports. The PDF and
independent mathematical/Lean--TeX reviews pass, with all sixteen APIs
registered; detailed validation is in
the SP79 parity-queue entry.

SP80 above proves the integral selector and actual normalization
factor by a trace section. This bypasses the
whole-source integral-closedness route; the idempotent equation alone
does not prove descent. The preceding SP79 validation record retains
its original scope. SP81 implements the actual affine cover and morphisms,
with validation complete. Localization/overlap compatibility, cocycles,
gluing, the global Galois action and independent Chow--Betti generation
remain separate.

## Tensor base change and the full evaluator square (A11bj / SP78)

Status: `FORMAL`. The existing finite-index tensor product
commutes with scalar extension as an algebra, with exact factor and
pure-tensor formulas; factorwise algebra equivalences induce an algebra
equivalence of the same tensor carriers without a finite-index premise.
The generic base-change theorem works over commutative rings, not only
fields, with the indexing and algebra carriers in independent universes.
These generic constructions are
in `CommutativeAlgebra/PiTensorBaseChange.lean`.

`Boundary/Normalization/NormalizationBaseChange.lean` identifies
`K⊗_B IntCl_B(L) ≃_K L` by localization at the base non-zero-divisors.
Only the fraction-field structure, compatible scalar towers and
algebraicity of `L/K` are needed. Normality/Noetherianity of `B`,
separability and finite degree are not assumptions of this one-factor
theorem. The pure-tensor formula is `k⊗x ↦ algebraMap K L k * x`.

For the existing marked normal closure, these comparisons construct
`β_Σ:K⊗_B P_B ≃_K P_K` and prove the full algebra-homomorphism equality
`ev_K∘β_Σ=β_N∘(1_K⊗ev_B)`. All embeddings, inclusions and tensor carriers
are the existing ones. The equality is proved, not supplied as a premise;
it is stronger than SP77's agreement on integral pure tensors alone.

The three existing `piTensorProductEvaluation` declarations move unchanged
from `NormalClosureTensor.lean` to `FiniteTensorProduct.lean`, with their
public names and proofs preserved. No duplicate evaluator, field carrier,
normal-closure package or source axiom is introduced. The thirteen new
declarations are:

- `PiTensorBaseChange.lean`: `piTensorProductCongr`, its `_tprod` and
  `_singleAlgHom` formulas; `piTensorProductBaseChangeEquiv`, its
  `_tmul_singleAlgHom`, `_symm_singleAlgHom_tmul` and `_tmul_tprod`
  formulas.
- `NormalizationBaseChange.lean`:
  `normalizedCoordinateRingBaseChangeEquiv` and `_tmul`;
  `NormalClosureData.normalizationTensorBaseChangeEquiv`, its
  `_tmul_singleAlgHom` and `_tmul_tprod` formulas, and
  `NormalClosureData.normalizationTensorEvaluation_baseChange`.

The central inventory is 896 checks, 565 examples and 788 reports; its
historical prefix is unchanged and was not rerun in full. The 76-page PDF
(812185 bytes) passes its build, warning scan and visual checks. Both new
leaves compile without warnings. `NormalizationBaseChangeVerification.lean`
passes 25 examples and 13 enforced standard-three axiom audits, including
three actual function-field cases. The full build passes (3189 jobs; only
the two existing Challenge placeholder warnings). Fresh SP77, SP76 and
SP74 reruns pass 28/17, 23/7 and 22/7, respectively: 98 examples and 44
enforced axiom audits across the four suites. The fresh unchanged
dependency audit passes six primary endpoint contracts and two support
reports.

SP79 above supplies the separable generic direct-factor/idempotent
construction for the actual maximal quotient. SP80 proves the
integral section, selector and evaluation-preserving normalization
quotient, together with whole-ring finite-etale structure. SP81 implements
the actual affine cover and morphisms, with validation complete.
Localization/overlap compatibility, cocycles, gluing and the global
Galois action remain separate. The Chow--Betti obligation is unchanged.

## Finite tensor source and marked evaluations (A11bi / SP77)

Status: `FORMAL`. For a finite index type, the existing
`PiTensorProduct` of copies of a module-finite algebra is module-finite;
copies of an etale algebra give an etale tensor algebra. These two
properties are proved independently, using the existing binary tensor
instances and algebra equivalences, including the empty index case.

For marked `NormalClosureData K L N`, let `Σ=Hom_K(L,N)` and
`P_K=⊗_{Σ,K} L`. The constructed algebra map `ev_K:P_K -> N` multiplies
the corresponding embedded factors. Its range, viewed as an intermediate
field because `N/K` is algebraic, contains every conjugate field. Thus the
normal-closure property proves surjectivity. The actual kernel `m` is
maximal, and the canonical quotient equivalence `P_K/m ≃_K N` agrees
with evaluation on every quotient representative. No separability,
perfectness or supplied surjectivity hypothesis is used.

For compatible `B`-algebras and scalar towers, those same embeddings
restrict to the existing integral closures. Their tensor evaluation
`ev_B:P_B -> IntCl_B(N)`, for `P_B=⊗_{Σ,B} IntCl_B(L)`, agrees factorwise
and on pure tensors with `ev_K` after inclusion into `N`. A supplied
actual finite normal intermediate algebra `A` with fraction field `L`
proves `P_B` finite, and etaleness of `A/B` proves `P_B` etale. The
existing normalization equivalence transports these properties; the two
source-property theorems omit the four unused assumptions `Algebra B K`,
`Algebra B N`, `IsScalarTower B K L`, and `IsScalarTower B K N`. No new
tensor carrier, normalization ring, field package or source axiom is used.

Witnesses:

- `CommutativeAlgebra/FiniteTensorProduct.lean`:
  `piTensorProduct_finite`, `piTensorProduct_etale`.
- `Boundary/Normalization/NormalClosureTensor.lean`:
  `piTensorProductEvaluation`, its pure-tensor and factor formulas;
  `NormalClosureData.tensorEvaluation`, its factor and surjectivity
  theorems, `tensorEvaluation_ker_isMaximal`,
  `tensorEvaluationQuotientEquiv` and its representative formula.
- `Boundary/Normalization/NormalizationTensor.lean`:
  `NormalClosureData.normalizationTensorEvaluation`, its factor,
  ambient-field factor and pure-tensor formulas,
  `normalizationTensor_finite`, `normalizationTensor_etale`.

All 17 new APIs compile. The central inventory is 883 checks, 565 examples
and 775 reports after appending 17 checks and reports; its historical
prefix is unchanged and was not rerun in full. The 76-page PDF (805454
bytes) passes its build, warning scan and visual checks; independent code
and Lean--TeX review pass. The full build passes (3187 jobs; only the two
existing Challenge placeholder warnings). The new suite passes 28
examples and 17 enforced standard-three axiom audits without warnings.
Fresh SP76 and SP74 reruns pass 23/7 and 22/7, respectively: 73 examples
and 31 audits in these three suites. The fresh unchanged dependency audit
passes six primary endpoint contracts and two support reports.

The generic quotient identification is not an integral direct-factor
identification or proof of integral evaluation surjectivity. SP77 did not
assert a scalar-extension/localization isomorphism between the integral
and field tensor constructions.
SP78 above implements the comparison `K⊗_B P_B ≃ P_K` and full evaluator
homomorphism equality left open at this checkpoint; the preceding
validation figures retain their SP77 scope. SP79 supplies the separable
generic direct-factor/idempotent construction. SP80 proves the
integral comparison and whole-ring finite-etale normalization by a trace
section, bypassing whole-source normality. SP81 implements the actual
affine cover and morphisms, with validation complete. Localization/overlap
compatibility, cocycles, gluing, the global Galois action and Chow--Betti
generation remain separate; none is renamed as an input hypothesis here.

## Finite normal-closure normalization and actual affine cover (A11bh / SP76)

Status: `FORMAL`. For normal Noetherian `B`, compatible
fraction-field/scalar-tower data and finite separable `E/K`, the actual
`normalizedCoordinateRing B E` is finite over `B`. Specialization to a
marked normal closure derives its finite normalization model from
`Algebra.IsSeparable K L`, without a perfectness or dimension-one premise.
A single finite normal intermediate algebra `A` now constructs the
existing `NormalizedCover`; no independently supplied second algebra
`S` is needed. Its full-visible boundary separation follows directly.

For a finite dominant formally unramified morphism `p:Y -> X` of integral
schemes, the normalization in its constructed function-field normal
closure is finite over every nonempty normal Noetherian affine base
chart. With normal stalks explicitly supplied on the inverse-image
open `V`, that actual `V.toScheme` constructs the visible scheme of the
existing cover. The map is the existing affine-preimage normalization
isomorphism, and the marked closure is `functionFieldNormalClosureData p`.
No `S`, marked-closure datum, new field carrier or cover package is
independently supplied. Etaleness supplies the formal-unramifiedness
premise; dominance and the normality inputs retain their stated roles.

Witnesses in `Boundary/Normalization/FiniteNormalClosure.lean`:

- `CollisionFoundations.normalizedCoordinateRing_finite_of_isSeparable`;
- `NormalizationInertia.normalClosureNormalizationRing_finite`;
- `NormalizationInertia.normalizedCoverOfFiniteNormalAffineModel` and
  `conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModel`;
- `CollisionFoundations.functionFieldNormalClosure_normalization_finite`;
- `CollisionFoundations.finiteAffinePreimageNormalizedCover` and
  `conjugateBoundarySeparation_finiteAffinePreimageNormalizedCover`.

The full build passes (3180 jobs; only the two existing Challenge
placeholder warnings). The new suite passes 23 examples and seven enforced
standard-three axiom audits; fresh consumer, affine-chart and normal-closure
reruns pass 24/29, 18/11 and 22/7. The central inventory has 866 checks,
565 examples and 758 reports after appending seven checks and reports;
its historical prefix is unchanged and was not rerun in full. The
74-page PDF (788608 bytes) passes its build, warning scan and visual
checks; independent code and Lean--TeX reviews pass. The fresh unchanged
dependency audit passes six endpoint contracts and two support reports.

No source axiom is introduced. Normality/Noetherianity of the base and
normal stalks upstairs stay explicit in these SP76 interfaces. SP80
proves the actual integral factor and whole-ring finite-etale
normalization from the finite etale intermediate algebra.
Generic etaleness, finiteness and full-visible separation alone
do not supply that result. SP81 implements the actual affine cover and
morphisms, with validation complete. Localization/overlap compatibility,
cocycles, gluing, the global Galois action and Chow--Betti generation
remain subsequent tasks.

## Local separability and consumer hypothesis cleanup (A11bg / SP75)

Status: `FORMAL`. Fourteen existing signatures replace
`PerfectField K` with explicit `Algebra.IsSeparable K L`: one fixed-field
identification, two intermediate-invariant comparisons, one full-invariant
base equivalence, three selector/tensor comparisons and seven trace/pole
results. Core-freeness and eleven full-visible/inertia/sheet/projector
consumers drop perfectness with no separability replacement. Their other
normalization, formal-unramifiedness and purity hypotheses are unchanged.

The existing `NormalClosureData.isSeparable` and
`.isGalois_of_isSeparable` move to `NormalClosure.lean` with unchanged
names. The old `.isGalois [PerfectField K]` is retained as the sole
perfect-field compatibility wrapper and delegates via separability of
the finite marked extension. These are 26 signature generalizations,
two moved declarations and one wrapper-proof change; no new library declaration,
alias, package, field carrier, map, projector or source axiom is added.

The new consumer suite passes 24 regressions and 29 enforced
standard-axiom audits; the trace and pole suites pass 14/11 and 12/9.
Fresh SP74 and finite-affine-cover reruns pass 22/7 and 20/17. The
central inventory has 859 checks, 565 examples and 751 reports after
appending 29 checks and reports; its historical prefix is unchanged
and was not rerun in full. The 74-page PDF (785575 bytes) passes its
build, warning scan and visual checks, and independent Lean--TeX review
passes. The full build passes (3179 jobs; only the two existing Challenge
placeholder warnings). The fresh unchanged dependency audit passes six
endpoint contracts and two support reports.

SP76 above implements the finite-normalization step identified at this
checkpoint, with base normality and Noetherianity still explicit. The
preceding validation figures describe SP75. Etaleness of the resulting
`N`-model, overlaps, gluing, global Galois refinement and Chow--Betti
generation remain separate.

## Constructed marked normal closure and Galois bridge (A11bf / SP74)

Status: `FORMAL`. A finite extension `L/K` constructs the
existing `NormalClosureData K L N`, with
`N=IntermediateField.normalClosure K L (AlgebraicClosure L)`. Its marked
embedding, viewed in the ambient algebraic closure, equals the original
`algebraMap L (AlgebraicClosure L)`. This constructor does not require
separability or perfectness.

For any supplied `D : NormalClosureData K L N`, the hypothesis
`Algebra.IsSeparable K L` gives `Algebra.IsSeparable K N`, then `IsGalois K N`.
This is not limited to the newly constructed datum and does not require
`PerfectField K`. The actual finite generic extension of a finite dominant
morphism of integral schemes therefore constructs marked normal-closure
data; scheme formal unramifiedness additionally makes that closure Galois
via SP73. Finite etale morphisms are a specialization.

Witnesses:

- `Boundary/Normalization/NormalClosureConstruction.lean`, namespace
  `CollisionFoundations.NormalClosureData`: `ofAlgebraicClosure`,
  `ofAlgebraicClosure_embedding_apply`. The existing `isSeparable` and
  `isGalois_of_isSeparable`, introduced at SP74, now reside in
  `Boundary/Normalization/NormalClosure.lean` after SP75's move.
- `Boundary/Normalization/FunctionFieldNormalClosure.lean`, namespace
  `CollisionFoundations`: `functionFieldNormalClosureData`,
  `functionFieldNormalClosureData_embedding_apply`,
  `functionFieldNormalClosure_isGalois`.

The existing package and Mathlib intermediate-field carrier are reused;
no parallel normal-closure package or source axiom is introduced. SP74
did not refactor existing consumer signatures; SP75 above implements
that generalization. A scheme-level Galois refinement, normal stalks from smoothness,
normalization gluing and Chow--Betti generation remain separate tasks.
The 74-page PDF (785530 bytes) passes its build, warning scan, visual
checks and independent core/scheme/manuscript review. The full build
passes (3179 jobs; only the two expected unchanged Challenge placeholder
warnings). Twenty-two focused regressions and seven enforced
standard-axiom audits pass. The fresh SP73 rerun passes sixteen regressions
and three audits; the fresh unchanged dependency audit passes six endpoint
contracts and two support reports. The central inventory now has 830
checks, 565 examples and 722 reports, with seven checks and reports
appended; its historical prefix is unchanged and was not rerun in full.

## Separability of the actual generic extension (A11be / SP73)

Status: `FORMAL`. A dominant affine formally unramified
morphism of integral schemes gives formal unramifiedness of the actual
function-field algebra induced by `functionFieldMapOfDominant`. The
affine-chart version accepts a nonempty affine base open; the global
version chooses that chart internally. Finiteness is not required for
this formal-unramifiedness result.

For a finite dominant formally unramified morphism, SP72 supplies
finite-dimensionality and therefore essential finite type; the actual
field extension is separable. A finite etale morphism satisfies the
scheme formal-unramifiedness hypothesis automatically. No normality,
perfectness, characteristic-zero or Noetherian premise is added.

The three witnesses, in `CollisionFoundations` and
`Boundary/Normalization/SeparableFunctionField.lean`, are
`functionFieldMapOfDominant_formallyUnramified_of_affine`,
`functionFieldMapOfDominant_formallyUnramified` and
`functionFieldMapOfDominant_isSeparable`.

These are properties of the existing `kappa_p` algebra, not a replacement
field map, a new cover package or a source axiom. SP74 above constructs
marked normal-closure field data from this finite extension. SP73 did
not discharge the downstream `PerfectField K` hypotheses; SP75 above
generalizes those consumers. Actual global Galois refinement, normal stalks from smooth
geometry, gluing and Chow--Betti generation remain separate tasks.
The manuscript's generic-separability proposition states the same
hypotheses and uses the same `kappa_p`. Its 73-page PDF (781158 bytes)
passes the build, warning scan and visual checks. The full build passes
(3177 jobs; only the two expected unchanged Challenge placeholder
warnings). Sixteen focused regressions and three enforced standard-axiom
audits pass. The fresh SP72 rerun passes eighteen regressions and eleven
audits; the fresh unchanged dependency audit passes six endpoint
contracts and two support reports. The central inventory now has 823
checks, 565 examples and 715 reports, with three checks and reports
appended; its historical prefix is unchanged and was not rerun in full.

## Actual dominant function fields and finite extension (A11bd / SP72)

Status: `FORMAL`. A dominant morphism of integral schemes gives
the actual generic-stalk map `K(X) -> K(Y)`, not a chosen fraction-field
replacement. Its injectivity, germ square on every nonempty base open,
identity and contravariant composition laws are proved; on an open
immersion it equals the existing function-field isomorphism. The
nonempty-preimage lemma needs only dominance; generic-point preservation
needs irreducible source and target, not integrality.

The germ square proves the section scalar tower for every nonempty base
open. For a finite dominant morphism of integral schemes, the actual
finite affine section algebra and the existing fraction-field structures
give finite-dimensionality of `K(Y)` over `K(X)` for this exact field map.
The final global theorem chooses a nonempty affine chart internally.
There is no normality, etaleness, Noetherianity, supplied-chart or
independently postulated extension premise.

Witnesses:

- `Cycles/FunctionFieldMap.lean`, namespace `SchemeCycles`:
  `nonempty_preimage_of_isDominant`, `genericPoint_eq_of_isDominant`,
  `functionFieldMapOfDominant`, `functionFieldMapOfDominant_injective`,
  `functionFieldMapOfDominant_germ`,
  `functionFieldMapOfDominant_eq_openImmersion`,
  `functionFieldMapOfDominant_id`, `functionFieldMapOfDominant_comp`.
- `Boundary/Normalization/FiniteFunctionField.lean`, namespace
  `CollisionFoundations`: `functionFieldMapOfDominant_sectionScalarTower`,
  `functionFieldMapOfDominant_finiteDimensional_of_affine`,
  `functionFieldMapOfDominant_finiteDimensional`.

SP72 establishes the finite extension; SP73 above derives its separability
from scheme formal unramifiedness, and SP74 constructs its marked
normal-closure field data.
Global finite etale Galois refinement, normal stalks
from smoothness, chart gluing and Chow--Betti generation remain separate.
No new field carrier, geometric input package, projector or source axiom
is introduced. The manuscript uses the same map and hypotheses;
its 72-page PDF (778658 bytes) passes the build, warning scan, visual
checks and independent core/manuscript review. The full build passes
(3176 jobs; only the two expected unchanged Challenge placeholder
warnings). Eighteen focused regressions and eleven enforced standard-axiom
audits pass without warnings. The fresh SP71 rerun passes eighteen
regressions and eleven audits; the fresh unchanged dependency audit
passes six endpoint contracts and two support reports. The central
inventory now has 820 checks, 565 examples and 712 reports, with eleven
checks and reports appended. Its historical prefix is unchanged and
was not rerun in full.

## Actual finite-morphism affine charts (A11bc / SP71)

Status: `FORMAL`. For any scheme smooth morphism, the actual
coordinate map on compatible affine source and target charts is smooth;
for an etale morphism, that map defines an etale algebra. The affine
global-sections specialization is also proved. For a finite morphism
`p:Y -> X` and affine `U`, its whole inverse image is affine and its actual
section ring `A_U` is finite over `B_U=Gamma(X,U)`; it is etale when `p`
is etale. This finite/etale algebra layer does not require an integral
source, nonempty inverse image or normal stalks.

For integral `Y` and a nonempty affine inverse image, normality of its
actual stalks implies that `A_U` is integrally closed. The existing
`Y.functionField` is its fraction field. The canonical affine presentation
and SP70 normalization map therefore give an isomorphism from the actual
open subscheme to the normalization in that field. Here integral closure
is over the image of the actual `B_U -> Y.functionField` map; injectivity
is not an added premise. Its hom formula and
structural equality over the original `X` are proved; the normalization
is finite and, if `p` is etale, etale over `B_U`.

Witnesses:

- `Boundary/Normalization/AffineEtaleAlgebra.lean`, namespace
  `CollisionFoundations`: `affine_appLE_smooth`, `affine_appLE_etale`,
  `affine_appTop_etale`.
- `Boundary/Normalization/AffineNormality.lean`, namespace
  `NormalizationInertia`: `affineSections_isIntegrallyClosed_of_stalks`.
- `Boundary/Normalization/FiniteAffineChart.lean`, namespace
  `CollisionFoundations`: `finiteAffinePreimage_moduleFinite`,
  `finiteAffinePreimage_etale`, `finiteAffinePreimageNormalizationIso`,
  `finiteAffinePreimageNormalizationIso_hom`,
  `finiteAffinePreimageNormalizationIso_hom_comp_toBase`,
  `finiteAffinePreimage_normalization_finite` and
  `finiteAffinePreimage_normalization_etale`.

No abstract cover package or substitute function field is introduced.
Normal stalks from smooth geometry, an actual global Galois refinement,
and chart gluing remain unproved here. The generic extension and marked
normal-closure field layer, open at SP71, are supplied by SP72--SP74 above.
The actual Chow--Betti class-generation obligation and the
main smooth-projective target are unchanged. The manuscript states the
chart result with its exact hypotheses. Its 72-page PDF (775350 bytes)
passes the build, warning scan, visual checks and independent Lean--TeX
review. The full build passes (3174 jobs; only the two expected unchanged
Challenge placeholder warnings). Eighteen focused regressions and
enforced standard-axiom audits for all eleven new declarations pass
without warnings. The SP70 suite was freshly rerun: twenty regressions
and seventeen audits pass. The fresh unchanged dependency audit passes
six endpoint contracts and two support reports. The central inventory
now has 809 checks, 565 examples and 701 reports, with only eleven checks
and reports appended; its historical prefix is unchanged and was not
rerun in full.

## Finite-affine normalization and full visibility (A11bb / SP70)

Status: `FORMAL`. The selected branch starts
with actual finite normal affine algebras and compatible marked fraction
fields. It identifies the canonical normalization map with an equivalence,
transports the finite models and etaleness, and constructs the existing
`NormalizedCover` with the whole intermediate model visible. For any
surjective visible open and perfect base field, empty conjugate boundaries
and the core-free sheet action make `J_mov(I)=J_fm(I)=top` for every
nontrivial subgroup. Separation follows directly, with no Noetherian,
regular-pair or uniform-landing hypothesis in that implication.

This is an affine construction from supplied rings and normal-closure
field data, not an existence theorem for global smooth-projective covers
or their Galois closures. General etale-to-normality, chart gluing and
Chow--Betti generation are not established by it. No new ideal, input
bundle, projector or axiom is introduced. The single manuscript has
matching finite-normal-affine and full-visible-boundary propositions,
with the same hypotheses. Its 71-page PDF (771887 bytes) passes the build,
warning scan, visual checks and independent Lean--TeX review. The full
build passes (3163 jobs; only the two expected unchanged Challenge
placeholder warnings). Twenty focused regressions and enforced
standard-axiom audits for all seventeen new declarations pass without
warnings. The fresh unchanged dependency audit passes its six endpoint
contracts and two support reports. The centralized inventory now has 798
checks, 565 examples and 690 reports, with only seventeen new checks and
reports appended; its historical prefix was preserved and not rerun in full.

Witnesses:

- `Boundary/Normalization/FiniteAffineCover.lean`, namespace
  `CollisionFoundations`: `normalizationToIntermediate_surjective`,
  `normalizationIntermediateEquiv` and its `toAlgHom` formula,
  `intermediateNormalizationIso` and its `hom` formula,
  `intermediateToNormalization_isIso`,
  `intermediateToNormalization_base_surjective`,
  `normalizedCoordinateRing_finite` and `normalizedCoordinateRing_etale`.
  Normality is supplied as `IsIntegralClosure A A E` for the general
  integral-algebra identification; the finite cover specialization uses
  integrally closed rings with chosen fraction fields.
- In namespace `NormalizationInertia`,
  `normalizedCoverOfFiniteNormalAffineModels` constructs the cover from
  supplied finite normal `A,S` and `NormalClosureData K L N`. Etaleness is
  not required for this constructor; the separate transport theorem
  preserves it when supplied.
  `conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModels`
  proves separation for this constructed cover over perfect `K`.
- `Boundary/Normalization/FullVisibleBoundary.lean`, namespace
  `NormalizationInertia`:
  `pulledBackConjugateVisibleOpen_eq_univ_of_surjective`,
  `pulledBackConjugateBoundary_eq_empty_of_surjective`,
  `pulledBackConjugateBoundaryIdeal_eq_top_of_surjective`,
  `movingBoundaryIdeal_eq_top_of_surjective`,
  `fixedMovingBoundaryIdeal_eq_top_of_surjective` and
  `conjugateBoundarySeparation_of_surjective`.

## Geometric-pair input audit (SP69)

Status: `OPEN` for geometric witness construction. The
[audit](working/0018-geometric-pair-input-audit.md) checks what the existing
package actually supplies; it adds no production declaration, source
axiom, manuscript theorem or PDF revision. Research-only algebra
diagnostics in `RegularPairGeometryControls.lean` pass: eight named
theorems and eight enforced standard-axiom audits, with no warnings.
The full library build also passes (3161 jobs; only the two existing
Challenge placeholder warnings). The unchanged historical verification
inventory was not rerun, and the unchanged manuscript/PDF was not rebuilt.

No instantiated `NormalizedCover` was found in the active library. Its
normal-closure datum does give a core-free intermediate fixing subgroup
over perfect `K`, but its marked open need not be surjective. The
characteristic-zero example `x=t^2`, `U=D(t)` has an etale visible map
and `J_fix=J_mov=J_fm=(t)`, so the supplied package cannot imply the
regular-pair premise in general. This is audited mathematics, not a Lean
construction of that cover. It does not contradict the conditional SP68
theorem or any Hodge target.

The separate algebra controls use `A=(x), M=(y)` in `Q[y][x]`:
`f=x,g=y` is a positive control, whereas `f=xy` admits no regular
`g in M`. These ideals are not identified with geometric fixed/moving
ideals. Associated-prime avoidance is analyzed as a possible tool for
choosing `f,g`; no general avoidance theorem or geometric application is
newly proved here.

Next choose and construct the actual geometry. Full-visible affine
normalization for a finite etale smooth-projective cover would make
`J_mov=top` and permit `g=1`; that subclass is not yet implemented.
A genuinely nonempty-boundary construction instead needs independent
quotient-regularity or all-section trace-landing input. Neither option
has been chosen by this checkpoint, and neither yields Hodge-class
generation on its own.

## Fixed--moving regular-pair checkpoint (A11ba / SP68)

Status: `FORMAL`. The full build, ten focused regressions and enforced
standard-axiom checks for all three new declarations pass. The previous
boundary-pole suite was freshly rerun after the refinement; its twelve
examples and nine-declaration allowlist pass. The appended umbrella-export
checks, fresh unchanged dependency audit, independent Lean--TeX review
and 70-page single-PDF checks also pass. Three direct theorems refine the
denominator construction and give a sufficient condition for the existing
boundary-separation endpoint. They do not construct geometric regular
pairs or establish uniform trace landing.

For a Noetherian domain `T`, a height-one prime `p` containing `J`, and any
specified `f != 0`, the refined denominator theorem constructs
`t` outside `p` and `n` with `t J^n <= (f)`. The earlier existential
theorem is preserved as a wrapper, not a parallel proof. The refinement
does not require `f in J`. For the separation criterion, require `f in J`;
if also `g in J` acts injectively on `T/(f)`, multiplication by `g^n`
is also injective;
`t g^n in (f)` therefore forces `t in (f)`, contradicting `t` outside
`p`. Thus an ideal containing such a pair is contained in no height-one
prime. No normality, perfectness or trace condition is used. The unit-ideal
case is permitted: a nonzero final quotient is not required, so the
criterion is not a claim of a full regular sequence in that convention.

For `NormalizedCover C`, Noetherian `B` and the supplied finite model make
the existing normalization ring `T` Noetherian. For every nontrivial `I`,
the explicit premise supplies `0 != f_I in J_fix(I)` and
`g_I in J_mov(I)`, with `g_I` acting injectively on `T/(f_I)`.
Their membership in the two existing summands gives membership in
`J_fm(I)`, and the generic criterion proves
`ConjugateBoundarySeparation C`. Perfectness of `K` is not required.

Witnesses, in namespace `NormalizationInertia`:

- `Boundary/Normalization/HeightOneBoundaryPole.lean`:
  `exists_heightOne_boundary_denominator_of_ne_zero`.
- `Boundary/Normalization/RegularPairBoundary.lean`:
  `not_le_heightOne_of_regularPair` and
  `conjugateBoundarySeparation_of_fixedMoving_regularPairs`.

No ideal, quotient carrier, input package or projector is added.
`f_I,g_I` denote supplied witnesses rather than newly defined canonical
objects. Separated-summand pairs are sufficient, not a necessary or
equivalent reformulation of the generic ideal criterion. Arbitrary
algebraic ideals with zero moving summand and proper fixed summand of
codimension at least two demonstrate that distinction; no normalized-cover
realization of that example is claimed. The generic theorem also accepts
both elements in `J_fm(I)`.
The next geometric step is to test this criterion on identified geometry,
construct these elements where applicable, and prove quotient injectivity
for every nontrivial subgroup. The already proved nonzero fixed-locus
ideal does not supply a compatible moving element.
Independent all-section uniform landing remains B4's alternative, not a
premise solved by this criterion. Neither boundary separation for actual
geometric data, convolution-defect vanishing nor Hodge-class generation
has been derived from newly constructed pairs here.

## Actual boundary-pole checkpoint (A11az / SP67)

Status: `FORMAL`. The full build, twelve focused regressions and enforced
standard-axiom checks for all nine new declarations pass. The appended
umbrella-export checks, fresh unchanged dependency audit, independent
Lean--TeX review and updated single-PDF checks also pass. These results
construct an actual pole and prove a conditional separation criterion,
rather than assume a pole witness or geometric landing.

For a Noetherian domain `T`, a nonzero ideal `J`, and a height-one prime
`p` containing `J`, choose `f != 0` in `J`. The dimension-one localization
and finite generation give `t` outside `p` and `n` with `t J^n <= (f)`.
Thus `t/f` has local integral fraction presentations on every nonempty
`V` contained in `D(J)`. These presentations are glued into an actual
structure-sheaf section and identified under the existing `eta_V` map.
Its image is outside `T`, because membership in `T` would force `t` into
`p`. Normality, perfectness, trace landing and a supplied pole are not
hypotheses of this generic construction.

For `NormalizedCover C`, Noetherian `B` and the supplied finite
normalization model make `T` Noetherian. Every height-one prime containing
`J_fm(I)` for a nontrivial `I` therefore forces `R_I != T`. If every such
section algebra instead equals `T`, the existing
`ConjugateBoundarySeparation C` follows. With the additional perfect-field
hypothesis on `K`, B2 implies that every nonzero trace multiplier fails
on some actual boundary section, and `(T^vee_B:R_I)=0` at a removed
height-one prime. Consequently the hypothesis
`forall I != bottom, exists s != 0, s R_I <= T^vee_B` implies separation.
The uniform-landing statement remains an explicit hypothesis of this
last implication, not an asserted geometric construction.

Witnesses, all in namespace `NormalizationInertia`:

- `Boundary/Normalization/SectionLocalization.lean`:
  `mem_affineSectionSubalgebra_of_localFractions` and
  `mem_affineSectionSubalgebra_of_ideal_pow_mul`.
- `Boundary/Normalization/HeightOneBoundaryPole.lean`:
  `exists_heightOne_boundary_denominator` and
  `affineSectionSubalgebra_ne_bot_of_heightOne`.
- `Boundary/Normalization/BoundaryPole.lean`:
  `boundarySectionSubalgebra_ne_bot_of_heightOne`,
  `conjugateBoundarySeparation_of_boundarySectionSubalgebra_eq_bot`,
  `boundarySection_tracePoleWitness`,
  `normalizationTraceDual_colon_eq_bot_of_heightOne`, and
  `conjugateBoundarySeparation_of_traceLanding`.

These nine public results reuse the existing section image, trace dual,
fixed--moving ideal and colon; the finite-generation denominator helper is
private. B4 remains to construct a nonzero geometric uniform multiplier
and prove landing of every section for every nontrivial subgroup. Naming a
candidate ideal or bounding finitely many coefficients does not discharge
that premise. No Hodge-class generation or convolution-defect vanishing
follows from this checkpoint alone.

## Normalization trace-dual checkpoint (A11ay / SP66)

Status: `FORMAL`. The full build, fourteen focused regressions and enforced
standard-axiom checks for all eleven new declarations pass. For a finite separable
extension `N/K`, where `K = Frac(B)` and `T` is the integral closure of
`B` in `N` with `Frac(T) = N`, the existing Mathlib submodule
`Submodule.traceDual B K (1 : Submodule T N)` is denoted `T^vee_B`.
It consists of those `z` for which `Tr_{N/K}(zt)` lies in the image of `B`
for every `t : T`. An integral generic basis bounds it by the finite
`T`-span of the trace-dual basis. One nonzero `d : T` therefore clears the
entire submodule: `d T^vee_B <= T`. No Noetherianity, normality of `B`,
or finite freeness of `T` over `B` is assumed. In particular `T <= T^vee_B`
is not asserted over a nonnormal base.

`normalizationTraceDual C` is an alias for this same carrier, specialized
to the existing `NormalizedCover`. The normal closure supplies finiteness
and, over perfect `K`, separability; the existing normalization
fraction-field comparison then supplies the denominator bound.
Under `[IsNoetherianRing B]`, the supplied finite normalization model also
makes `T` Noetherian, and its integral closure is integrally closed.
B0 thus proves
`0 != s in (T^vee_B:R_I) => R_I=T`, including a formulation quantifying
all actual boundary sections. If `R_I != T`, the colon ideal is zero.
The colon is Mathlib's existing `Submodule.colon`, not a new transporter.

Witnesses in `Boundary/Normalization/TraceDualBound.lean`, namespace
`NormalizationInertia`: `mem_traceDual_unit_iff`,
`traceDual_unit_le_span_traceDual`, and
`exists_nonzero_traceDual_unit_denominator`. Witnesses in
`Boundary/Normalization/NormalizationTraceBound.lean`:
`normalizationTraceDual`, `mem_normalizationTraceDual_iff`,
`normalization_isNoetherianRing`, `normalization_isIntegrallyClosed`,
`exists_nonzero_normalizationTraceDual_denominator`,
`boundarySectionSubalgebra_eq_bot_of_mem_traceDual_colon`,
`boundarySectionSubalgebra_eq_bot_of_trace_landing`, and
`normalizationTraceDual_colon_eq_bot_of_boundarySectionSubalgebra_ne_bot`.

This proves boundedness and its conditional overring consequences, not
existence of a nonzero uniform geometric multiplier. The boundary pole
witness and comparison to `ConjugateBoundarySeparation` are the subsequent
SP67 construction above. A bound on finitely many coefficients cannot replace landing
of every section; none of these results establishes Hodge-class generation.

## Actual boundary-section checkpoint (A11ax / SP65)

Status: `FORMAL`. The full build, sixteen focused regressions and enforced
standard-axiom checks for all twenty-one new declarations pass. For a domain `T`
and a specified fraction field `F`, actual structure-sheaf sections on a
nonempty open `V` of `Spec T` embed by an injective `T`-algebra map into
`F`. Its range is canonically algebra-equivalent to the section ring.
Constants and restrictions have the same rational function; shrinking the
open enlarges the range, and the full-open range is the embedded base.
Normality and Noetherianity are not needed. The construction uses Mathlib's
existing section action, generic stalk and function field, not a replacement
field or a supplied geometric comparison.

For the existing `NormalizedCover C`, the normal-closure normalization ring
`T` has the existing `N` as fraction field. A subgroup `I != bottom` has
nonzero fixed-locus ideal, because an automorphism trivial on `T` is trivial
on its fraction field. Hence the complement of the existing fixed--moving
boundary ideal is nonempty. Its actual section ring embeds in `N`, and
its image is the constructed `boundarySectionSubalgebra`.

Witnesses in `Boundary/Normalization/AffineSections.lean`, namespace
`NormalizationInertia`: `affineSectionsToFractionField`,
`affineSectionsToFractionField_injective`,
`affineSectionsToFractionField_algebraMap`,
`affineSectionsToFractionField_restrict`, `affineSectionSubalgebra`,
`affineSectionsEquivSubalgebra`, `affineSectionSubalgebra_anti`, and
`affineSectionSubalgebra_top`. Witnesses in
`Boundary/Normalization/BoundarySections.lean`: `normalization_isFractionRing`,
`fixedMovingBoundaryOpen`, `fixedLocusIdeal_ne_bot`,
`fixedMovingBoundaryOpen_nonempty`, `BoundarySectionRing`,
`boundarySectionsToNormalClosure`, `boundarySectionsToNormalClosure_injective`,
`boundarySectionSubalgebra`, and `boundarySectionsEquivSubalgebra`.

This constructs the actual overring used by the boundary route. It assumes
neither boundary separation nor trace landing and proves neither. The
genuine trace dual and its denominator are the subsequent SP66 construction,
and the pole/separation implication is the SP67 construction above. A
nonzero uniform transporter remains the separate B4 obligation.
The underlying section module is the existing `.toSubmodule`, with no
second section-module definition. No new source hypothesis or project axiom
is introduced, and no Hodge-class generation is asserted.

## Bounded-overring checkpoint (A11aw / SP64)

Status: `FORMAL`. The full build and six focused regressions pass; the
enforced axiom allowlist accepts only `propext`, `Classical.choice` and
`Quot.sound` for all three declarations.

For a normal Noetherian domain `T` with fraction field `N`, a `T`-subalgebra
`R` of `N` admitting one nonzero `a : T` with `a R` contained in the base
equals the base subalgebra (`R = ⊥`, not the zero ring). Multiplication
embeds `R` into a Noetherian module, so `R` is finite and integral; normality
then concludes. No finiteness or integrality of `R` is assumed.

If a submodule `M` has a uniform nonzero denominator `d`, a nonzero member
of the existing ideal `M.colon R.toSubmodule` supplies such a bound using
`d*s`. Consequently a proper overring has zero transporter into `M`.
There is no converse for arbitrary `M`, and no new transporter definition.

Witnesses in `Boundary/Normalization/BoundedOverring.lean`, namespace
`NormalizationInertia`: `subalgebra_eq_bot_of_nonzero_mul_mem_base`,
`subalgebra_eq_bot_of_mem_colon`, `colon_eq_bot_of_subalgebra_ne_bot`.
This is a generic algebraic input, not an instantiation of actual boundary
sections, trace duality, uniform geometric landing, boundary separation,
projector-defect vanishing or Hodge-class generation.

## Candidate A: finite-etale correspondence and projector calculus

This is currently the strongest self-contained publication unit. Its safest
framing is a Lean formalization report, not a partial proof of the Hodge
conjecture.

| ID | Status | Prose claim | Lean witness |
| --- | --- | --- | --- |
| A1 | FORMAL | Scheme correspondences over a base compose by fiber product and are unital and associative up to canonical scheme isomorphism. | `SchemeCorrespondence.identityCompIsom`, `compIdentityIsom`, `assocIsom` in `HodgeConjecture/Correspondence/Scheme.lean` |
| A2 | FORMAL | Isomorphism classes of endocorrespondences form a monoid, and their rational monoid algebra is a generally noncommutative free span algebra. | `HodgeConjecture/Correspondence/Classes.lean`, `Linearized.lean` |
| A3 | FORMAL | Correspondences with finite-etale legs are closed under identity, transpose, and composition and define a convolution submonoid and rational algebra. | `HasFiniteEtaleLegs.identity`, `.transpose`, `.comp` in `Etale.lean`; `finiteEtaleClassSubmonoid` in `EtaleClasses.lean` |
| A4 | FORMAL | Transpose reverses convolution and induces involutions on the unrestricted and finite-etale free rational algebras. | `classTranspose_mul`, `freeTranspose_mul`, `finiteEtaleFreeTranspose_mul` and the corresponding involutions in `TransposeAlgebra.lean` |
| A5 | FORMAL | A deck action induces an algebra map from the rational group algebra to the finite-etale correspondence algebra, transporting supplied idempotents and orthogonal decompositions. | `FiniteDeckAction.toFiniteEtaleAlgebra` in `FiniteGroupProjector.lean`; `groupAlgebraCorrespondence_isIdempotent` and `GroupAlgebraDiagonalDecomposition.toDiagonalDecompositionLift` in `GroupAlgebraProjector.lean` |
| A5a | CONDITIONAL | Given generic and compactified deck actions, algebra realizations of their finite-etale graph spans, and a restriction algebra map whose square commutes on `ℚ[G]`, every supplied group-algebra idempotent has a compactified idempotent image with the prescribed generic restriction and zero convolution defect. The finite-subgroup average gives an `AlgebraProjectorExtension`. The comparison structure does not construct a compactification, a Chow algebra, either cycle map, or the restriction square. | `CompactifiedDeckGraphComparison`, `compactifiedGroupAlgebraProjector_isIdempotent`, `compactifiedGroupAlgebraProjector_restricts`, `compactifiedGroupAlgebraProjector_defect_eq_zero`, `groupAlgebraProjectorExtension`, and `subgroupAveragingProjectorExtension` in `Boundary/CompactifiedGraphProjector.lean` |
| A6 | FORMAL | For a finite group, the normalized graph average and its complement are convolution idempotents. | `averagingProjector_isIdempotent`, `complementaryAveragingProjector_isIdempotent` in `FiniteGroupProjector.lean` |
| A7 | FORMAL | For a finite subgroup, the normalized Hecke corner is constructed, `e_H[g]e_H` depends only on the double coset, and idempotents in the corner map to correspondence idempotents. | `SubgroupHeckeAlgebra`, `heckeElement_eq_of_rel`, `doubleCosetOperator`, `heckeCorrespondence_isIdempotent` in `HeckeProjector.lean` |
| A8 | CONDITIONAL | For a finite group and a finite-etale cover, given an explicit torsor comparison and a `FiniteEtaleAlgebraModel`, the collision class is the finite sum of graph classes, its normalized class realizes the averaging projector, and that normalized class is convolution-idempotent. The model is an algebra realization of the finite-etale free correspondence algebra and assumes additivity only for finite coproducts; it does not range over arbitrary spans. | `FiniteEtaleAlgebraModel` in `HodgeConjecture/Correspondence/FiniteEtaleModel.lean`; `GaloisCollisionDecomposition`, `classOf_collision_eq_sum_graph`, `averagingProjector_realizes_normalizedCollisionClass`, and `normalizedCollisionClass_isIdempotent` in `GaloisCollision.lean` |
| A9 | FORMAL | `NormalClosureData` already supplies the normal-closure witness and finite-dimensionality of `L/K` and `N/K`.  It derives normality, and from `Algebra.IsSeparable K L` derives `IsGalois K N`; no duplicate normality or Galois hypothesis is required.  Normality keeps conjugate embeddings inside the same `N` and one Galois group; it does not make that group abelian.  The finite `galoisGroup`, `intermediateFixingSubgroup`, and canonical action by deck transformations on the affine integral-closure normalization are available to the marked-sheet and graph-projector layers; the final class-dependent witness still does not construct or bundle this geometric input.  Each deck map lies over the affine base because the automorphism fixes `K` and hence the `B`-scalars through the scalar tower, not because `G` commutes.  Pointwise sheet multiplication is separately commutative, while the group/convolution and Chow-correspondence algebras may be noncommutative.  Despite the API name `FiniteDeckAction`, this does not assert that the normalization map is finite étale; those properties remain separate inputs. | `NormalClosureData.normal`, `.finiteGaloisGroup`, `.isGalois_of_isSeparable` (with `.isGalois` retained as the perfect-field compatibility wrapper), `.galoisGroup`, and `.intermediateFixingSubgroup` in `Boundary/Normalization/NormalClosure.lean`; `NormalizationInertia.normalClosureNormalizationRingEquiv`, `normalClosureNormalizationSchemeIso_hom_comp_toBase`, `normalClosureDeckTransformation`, and `normalClosureFiniteDeckAction` in `Boundary/Normalization/DeckAction.lean` |
| A10 | FORMAL | For a subgroup `H` of `Gal(N/K)`, the integral closure of `B` in the fixed field `N^H` is canonically equivalent, as a `B`-algebra, to the `H`-fixed subalgebra of the integral closure of `B` in `N`. For a marked normal closure with `Algebra.IsSeparable K L`, this identifies the marked intermediate normalization with the fixed ring of its intermediate fixing subgroup. No purity or unramifiedness is used. | `NormalizationInertia.fixedFieldNormalizationEquivFixedRing` and `intermediateNormalizationEquivFixedRing` in `Boundary/Normalization/InvariantIntermediate.lean` |
| A11 | FORMAL | A marked normal closure defines algebra maps from `L ⊗[K] L` and `N ⊗[K] L` to functions on `G/H`.  Base-sheet evaluation is an algebra homomorphism, and its composite with `normalClosureTensorToGenericSheets` is exactly the tensor-diagonal algebra map `N ⊗[K] L → N`.  Under formal unramifiedness and essential finite type, the diagonal element maps exactly to the characteristic function of the marked base sheet and is itself idempotent. For separable `L/K`, the normal-closure sheet map is an `N`-algebra equivalence and satisfies the same augmentation square. | `NormalClosureData.normalClosureBaseSheetAugmentation_comp_tensorToGenericSheets`, `collisionToGenericSheets_elem_eq_baseSheetSelector`, `sheetDeltaTensor_maps_to_selector`, `normalClosureTensorGenericSheetsEquiv`, `normalClosureBaseSheetAugmentation_comp_tensorGenericSheetsEquiv`, and `formallyUnramifiedElem_isIdempotent` in `Boundary/Normalization/SelectorComparison.lean` |
| A11b | FORMAL | For the pointwise sheet algebra `A_H = ℚ^(G/H)`, base-sheet evaluation is an augmentation algebra map and its kernel is the augmentation ideal `E_H = (1 - q_H)`.  Giving that ideal the internal unit `1-q_H` produces the residual corner and a genuine algebra equivalence `A_H ≃ₐ[ℚ] ℚ × E_H^corner`, carrying `q_H` to `(1,0)` and `1-q_H` to `(0,1)`.  The source regular action is multiplicative.  After forgetting the corner unit, multiplication by `q_H` is `diag(1,0)` in the underlying selector coordinates and is the graph operator of `q_H - 1` in the separate constant-unit linear coordinates; the linear coordinate changes differ by an explicit lower shear.  Any rational linear map from the underlying module of `E_H` carries this graph operator to the canonical Tate graph projector of the resulting class.  The auxiliary direct-only sheet linearization is not an algebra map and is not part of the active realization route. | `MarkedAugmentedAlgebra.augmentationIdeal_eq_span_one_sub_selector`, `.regularAction`, and the generic block identities are in `LinearAlgebra/MarkedAugmentedAlgebra.lean`; `ResidualCorner` and `selectorAlgebraDecomposition` are in `LinearAlgebra/MarkedAugmentedAlgebraDecomposition.lean`; their sheet specializations are in `Boundary/Sheets/MarkedBlockProjector.lean`; generic and sheet realization naturality are in `Realization/Chow/MarkedAugmentedRealization.lean` and `GaloisMarkedBlock.lean`. |
| A11c | FORMAL | The universal one-idempotent algebra `U = ℚ × ℚ` maps canonically by algebra homomorphisms to every associative rational algebra containing a chosen idempotent.  Restriction of a compactified projector is therefore an equality of algebra-map composites out of `U`.  A selector action square is equivalently a morphism between the two induced `U`-representations, and every algebraic projector lift has a realization square stated as equality of algebra-homomorphism composites.  This construction requires no algebra map from the full pointwise sheet algebra to `ℚ[G]`. | `UniversalIdempotentAlgebra.mapOfIdempotent` and `.comp_mapOfIdempotent` in `LinearAlgebra/UniversalIdempotentAlgebra.lean`; `UniversalIdempotentAlgebra.RepresentationMorphism` in `Realization/Chow/IdempotentRepresentation.lean`; `AlgebraProjectorExtension.restriction_comp_compactifiedIdempotentMap` in `Boundary/GaloisProjectorExtension.lean`; `AlgebraicProjectorLift.realization_idempotentMap_square` in `Correspondence/ProjectorLift.lean` |
| A11d | FORMAL | For finite `I`, `Spec(k^I)` is finite, étale, and proper over `Spec k`; each point inclusion defines a finite-étale span whose self-pullback proves its free span basis class idempotent. Separately, in the two-point rational matrix coefficient model, `Π=E₀₀`, residual evaluation `θ(0,b)=b`, and constant-unit coordinates `(a,b)↦(a,b−a)` give `θ(q−1)=−1`, surjectivity, `ρ(Π)=P₋₁`, a constructed marked comparison and projector lift, and the Palomar target square. A11f now connects the actual scheme-span source to this matrix model; A11j constructs the finite-split geometric Chow composition. | `SplitPointGeometry.pointSpan_comp_self_iso` and `.pointProjector_isIdempotent` in `Correspondence/Examples/SplitPoints.lean`; `SplitPointCorrespondence.realization_firstPointProjector`, `.markedComparison`, `.projectorLift`, and `.palomarTargetSquare` in `Realization/Chow/Examples/SplitPoints.lean`. |
| A11e | BENCHED | Valid standalone exclusion of unital ring maps from the full `M₂(ℚ)` to a nontrivial commutative ring. It does not rule out a suitable correspondence subalgebra, a noncommutative generic target, or the restriction-free comparison, and is not an obstruction in the current target sketch. | `MatrixRestrictionObstruction.no_ringHom_to_commutative` and `.no_algHom_to_pointwise_sheets`, preserved unchanged in `research/bench/MatrixRestrictionObstruction.lean`; checked separately, not exported by the library. |
| A11f | FORMAL | Actual finite split scheme spans are closed under geometric fiber-product composition and coproducts. Scheme-span isomorphisms induce label bijections, so rational incidence counts descend to their existing geometric isomorphism classes. The split-presentable submonoid's free rational algebra embeds injectively into the existing finite-étale free algebra and has a surjective matrix realization, multiplicative for actual fiber products and additive for geometric disjoint unions, sending empty carriers to zero. The original point projector is recovered under the source embedding and maps to `E₀₀`; composing with the earlier coefficient action constructs its marked comparison, projector lift, and Palomar square from an actual geometric source. A11g identifies the exact finite point-decomposition kernel. A11j supplies the actual finite-split Chow operations and composition, and A11k its degree-zero Betti realization; extension to all finite-étale classes remains separate. | `SplitPointGeometry.span_comp_iso` and `.span_sum_iso`; `SplitSpanRealization.matrix_eq_of_isom`, `.realization`, `.realization_surjective`, `.realization_sum`, `.realization_empty`, and `.toFiniteEtaleFreeAlgebra_injective`; `GeometricSplitPoints.projector_toFiniteEtaleFreeAlgebra`, `.coefficientRealization_projector`, and `.palomarTargetSquare`. |
| A11g | FORMAL | An actual finite split scheme span is the indexed scheme coproduct of its point-pair spans. The two-sided ideal `J_sp` generated by all finite point-decomposition differences equals `ker χ_sp`, by reduction to point-pair normal form and independence of the matrix units. Hence `C_sp^add := C_sp / J_sp ≃ₐ[ℚ] M_I(ℚ)`; empty-span and binary-coproduct defects lie in this ideal. The two-point coefficient action and Palomar square descend to this quotient. The generators are finite indexed decompositions; binary-only generation is not asserted. The free source remains distinct from its additive quotient; A11j identifies the quotient with the actual Chow algebra. | `SplitPointGeometry.span_pointDecomposition_iso`; `SplitSpanRealization.additiveRelations_eq_ker`, `.AdditiveQuotient`, and `.quotientRealizationEquiv` in `Realization/Chow/Examples/SplitSpanQuotient.lean`; `GeometricSplitPoints.additiveCoefficientRealization_comp_classMap` and `.additivePalomarTargetSquare`. |
| A11h | FORMAL | For any field `k` and finite `I`, every integral closed immersion `f : X → Spec(k^I)` has a unique label `i` and an isomorphism `e : X ≅ Spec k` with `s_i ∘ e = f`. The actual integral ideal-sheaf subschemes are therefore equivalent to `I`. Every closed subscheme has topological Krull dimension at most zero, exactly zero when nonempty, so no integral closed curve exists. Separately, every prime of `k^I` is a unique coordinate-evaluation kernel and its quotient is isomorphic to `k` as a `k`-algebra. These provide the actual integral generators and no-curves input used in A11i. | `SplitPointGeometry.existsUnique_pointIso_of_isIntegral` and `.labelEquivIntegralClosedSubscheme` in `Correspondence/Examples/SplitIntegralSubschemes.lean`; `.topologicalKrullDim_le_zero_of_isClosedImmersion`, `.topologicalKrullDim_eq_zero_of_isClosedImmersion`, and `.not_one_le_topologicalKrullDim_of_isClosedImmersion` in `Examples/SplitPointDimension.lean`; `SplitFieldQuotient.existsUnique_prime_eq_ker_eval`, `.evalQuotientEquiv`, and `.exists_prime_quotient_equiv` in `CommutativeAlgebra/SplitFieldQuotient.lean`. |
| A11i | FORMAL | Zero-cycles on `Spec(k^I)` are defined as finitely supported coefficients on its actual integral closed subschemes. Classification constructs their point-coordinate linear equivalence. The actual integral-curve type and its pairs with units in the scheme function field are empty; hence the submodule generated by principal-divisor cycles is zero. Rational equivalence is equality, and the actual cycle quotient has a constructed equivalence `CH_0(Z_I;R) ≃ₗ[R] (I → R)`, in particular for `R = ℤ` and `R = ℚ`. Coefficient extension from integral to rational cycles and Chow classes is injective and preserves point generators. The canonical scalar-extension equivalences for cycles and Chow groups are proved, including `ℚ ⊗[ℤ] CH_0(Z_I;ℤ) ≃ₗ[ℚ] CH_0(Z_I;ℚ)` and its point-generator formula. A11j constructs the actual product and pull--push correspondence composition. | `SplitZeroCycles.Cycles`, `.coordinates`, `.coordinates_pointCycle`, `.rationalize_injective`, and `.coordinates_rationalize` in `Realization/Chow/Examples/SplitZeroCycles.lean`; `.rationalizationEquiv` in `Examples/SplitZeroCycleBaseChange.lean`; `.IntegralCurve`, `.PrincipalDivisorData`, `.relations_eq_bot`, `.Chow`, `.chowCoordinates`, `.chowRationalize_injective`, and `.chowRationalizationEquiv_tmul_pointCycle` in `Examples/SplitRationalEquivalence.lean`. |
| A11j | FORMAL | For finite split schemes, the scheme-theoretic image of an integral point is the labelled image point, and its actual restriction map is an isomorphism of residue-field degree one. Actual scheme product and point-fiber isomorphisms respect their projections and identify the inverse-image ideal sheaf. The ambient-stalk multiplicity of each fiber point is one. These geometric computations construct proper pushforward, flat pullback, external product, and diagonal intersection on the actual cycle groups, and descend them to their Chow quotients. Rational Chow correspondences on the actual products compose by `p13_* (p12^* a · p23^* b)`; point-pair coordinates give a linear equivalence to matrices, under which this composition is matrix multiplication. The diagonal is the identity and composition is associative. Keeping that geometric composition as multiplication constructs the Chow endomorphism algebra and its rational algebra equivalences with matrices and the additive split-span quotient, respecting actual point-span/point-pair generators. More generally, every finite split span maps to the proper pushforward of its carrier's fundamental cycle along the actual pair map. The actual Chow action `p2_* (c · p1^* z)` has the matrix-vector coefficient formula and respects composition. | `SplitPointGeometry.imageIntegralSubscheme`, `.imageIntegralSubschemeMap`, and `.imageIntegralSubschemeIso` in `Correspondence/Examples/SplitCycleGeometry.lean`; `.productIso`, `.pointFiberIso`, and `.pointIdealSheaf_comap_mapOfFunction` in `Examples/SplitProductGeometry.lean`; `.stalkMap_length_of_isOpenImmersion` and `.residueFieldMap_finrank_of_isIso` in `Examples/SplitPointMultiplicity.lean`; `SplitZeroCycles.pushforward`, `.pullback`, `.externalProduct`, `.intersection`, and their Chow operations in `Realization/Chow/Examples/SplitCycleOperations.lean`; `SplitChowCorrespondence.comp`, `.matrixCoordinates`, and `.matrixCoordinates_comp` in `Examples/SplitChowComposition.lean`; `.matrixAlgEquiv`, `.spanQuotientEquiv`, `.spanQuotientEquiv_pointSpanClass`, and `.spanQuotientEquiv_ofSchemeSpan` in `Examples/SplitChowAlgebra.lean`; `.action`, `.chowCoordinates_action`, and `.action_comp` in `Examples/SplitChowAction.lean`; the degree/length-weighted basis comparisons are in `Examples/SplitCycleMultiplicity.lean`. |
| A11k | FORMAL | The actual complex points `Hom_ℂ-alg(ℂ^I,ℂ)` of a finite split scheme are uniquely classified by evaluations. Their regular-function evaluation topology is Hausdorff and finite, hence discrete; point maps and products agree with the actual scheme maps. Singular degree-zero cohomology is constructed from actual continuous simplices and the two-face coboundary, with its face operation identified with Mathlib's singular simplicial set. Evaluation gives an equivalence to point functions. The cycle-class isomorphism from actual rational Chow sends each point to its characteristic cocycle and commutes with proper pushforward/finite transfer, flat pullback, and intersection/cup product. The cohomological pull--cup--transfer action intertwines the geometric Chow action and respects composition and the diagonal. It constructs an algebra homomorphism from the actual Chow endomorphism algebra to endomorphisms of singular degree-zero cohomology and instantiates the existing rational correspondence-action interface. | `SplitComplexPoints.Point`, `.existsUnique_eq_evalPoint`, `.pointTopology`, `.pointDiscreteTopology`, `.schemeMorphism_map`, and `.productHomeomorph` in `Realization/Betti/Examples/SplitComplexPoints.lean`; `SingularDegreeZero.simplexEquivSingularSet_face`, `.coboundary`, `.H0`, `.equivFunctions`, `.cup`, and `.pullback` in `Realization/Betti/SingularDegreeZero.lean`; `.transfer` in `Realization/Betti/FiniteTransfer.lean` and `.transfer_simplex_eq_sum_lifts` in `Realization/Betti/ZeroSimplexTransfer.lean`; `SplitBetti.cycleClass`, `.cycleClass_pointCycle`, `.cycleClass_pushforward`, `.cycleClass_pullback`, and `.cycleClass_intersection` in `Realization/Betti/Examples/SplitCycleClass.lean`; `.action`, `.cycleClass_action`, `.realization`, `.realization_cycleClass`, and `.correspondenceAction` in `Realization/Betti/Examples/SplitCorrespondenceAction.lean`. |
| A11l | FORMAL | The actual tensor complexification of finite split singular degree-zero cohomology has its computed complex point coordinates, injective rational embedding, and canonical tensor conjugation. The explicitly specified effective type-`(0,0)` bigrading satisfies directness, exhaustion, weight zero, and conjugation symmetry. Its rational `(0,0)` inverse image defines the Hodge subspace independently of cycle classes, then is proved to equal the full rational space. Actual Chow correspondences on `Spec ℂ ⨿ Z_I` encode a class as the distinguished point-pair cycle plus column pushforward; decoding is actual column flat pullback. The encoding is idempotent and decoding recovers its input. Under the fixed decomposition of actual Betti cohomology as `ℚ(0) ⊕ H_B^0(X_I;ℚ)`, encoding realizes the canonical class graph, and decoding every correspondence has the cycle class of its lower-left action block. This constructs the finite codimension-zero Hodge model and instantiates construction, detection, Hodge-morphism compatibility, and the graph/Palomar target equivalences. The geometric Hodge identification is the cited effective degree-zero specialization, not a formalized general analytic Hodge theorem. | `SplitHodgeStructure.Complexification`, `.complexCoordinates`, `.rationalEmbedding_injective`, `.conjugation_tmul`, `.bigrading_direct`, `.bigrading_exhaustive`, `.rationalHodgeClasses`, and `.IsHodgeMorphism` in `Realization/Betti/Examples/SplitHodgeStructure.lean`; `SplitChowTateBlock.encode`, `.decode`, `.decode_encode`, `.encode_isIdempotent`, and `.optionSchemeIso` in `Realization/Chow/Examples/SplitTateBlock.lean`; `SplitBettiTateBlock.blockCoordinates`, `.realization_encode`, `.cycleClass_decode`, `.hodgeModel`, `.construction`, `.detection`, `.hodgeCompatibility`, `.hodgeConjectureAt`, `.hodgeConjectureAt_iff_palomarTargetSquare`, `.everyHodgeClassHasPalomarTargetSquare`, and `.hodgeConjectureAt_iff_hodgeMorphismLift` in `Realization/Betti/Examples/SplitTateBlock.lean`. |
| A11m | FORMAL | For finite G and any subgroup D, the actual regular split torsor has a constructed graph-sheet collision isomorphism; its homogeneous quotient-label cover is finite, étale, proper, and surjective. The residual ideal on G/D maps bijectively to actual Chow of the marked-sheet complement by a literal point-cycle sum, preserving multiplication as geometric intersection and carrying q−1 to the negative fundamental class. Actual diagonal pushforward embeds sheet functions into Chow convolution. An invertible actual Chow shear conjugates the marked point projector into the existing graph encoding, and the constructed Betti action realizes this as the constant-marked coordinate change. The embedding intertwines full sheet multiplication with the actual Betti action in constant-marked coordinates. The residual cycle-class map and source-action comparison instantiate the restriction-free marked comparison and its Palomar square for the canonical generated class. General multiplicative residual rigidity proves α²=−α and, for a surjective multiplicative map into a rational algebra, α=−1. | `SplitGaloisSheets.regularCollisionDecomposition` and `.quotientMap` in `Correspondence/Examples/SplitGaloisSheets.lean`; `SplitGaloisResidual.residualChowEquiv`, `.residualChow_mul`, and `.residualChow_residualClass` in `Realization/Chow/Examples/SplitGaloisResidual.lean`; `SplitChowDiagonal.diagonalAlgHom` in `Realization/Chow/Examples/SplitChowDiagonal.lean`; `SplitChowShear.shearUnit` and `.shear_point_shear_neg` in `Realization/Chow/Examples/SplitChowShear.lean`; `SplitGaloisMarkedComparison.comparison` and `.palomarTargetSquare` in `Realization/Betti/Examples/SplitGaloisMarkedComparison.lean`; `.markedEmbedding_action` in `Realization/Betti/Examples/SplitGaloisAction.lean`; `MarkedAugmentedAlgebra.generatedClass_eq_neg_one_of_surjective` in `Realization/Chow/MultiplicativeResidualRigidity.lean`. |
| A11n | FORMAL / CONDITIONAL | Selected literature conclusions have separate explicit interfaces: the canonical fixed-inertia unramifiedness record is moved unchanged and proved equivalent to its Mathlib premise; an actual finite étale extension witness has a separate existence hypothesis; bijectivity of its actual automorphism restriction map conditionally lifts deck actions. Rational-linear localization exactness and surjectivity give raw lifts and boundary preimages of differences; with a separate algebra restriction they give boundary preimages of every raw convolution defect. No global source instance, full Stacks theorem, geometric input instantiation, defect vanishing, idempotent correction, graph/action comparison, or coverage follows from this packaging. The existing two Palomar statement signatures are unchanged. | `InertiaFixedRingUnramifiedAt` and `inertiaFixedRingUnramifiedAt_iff` in `Inputs/FixedInertia.lean`; `LiteratureInputs.FiniteEtaleExtension`, `FiniteEtaleExtensionHypothesis`, `DeckExtensionHypothesis`, and `FiniteEtaleExtension.liftDeckAction` in `Inputs/FiniteEtaleExtension.lean`; `ChowLocalizationHypotheses`, `ChowLocalization.projectorClosure_nonempty`, and `exists_boundary_of_convolutionDefect` in `Inputs/ChowLocalization.lean`. |
| A11o | FORMAL | For a separated structural morphism, the actual graph of a deck transformation is a closed immersion, is proper as a morphism into the relative product, and identifies its source with its kernel-defined closed subscheme. For a supplied actual finite étale extension over an open immersion, the induced pair inclusion is open and the graph of the restricted automorphism is the scheme-theoretic pullback of the extended graph, with equality of their actual ideal sheaves under `comap`. Restriction of an already extended automorphism needs no deck-extension premise; the corollary lifting a prescribed original action explicitly assumes bijectivity of automorphism restriction. This constructs neither the geometric extension itself nor dimensions, graph fundamental cycles, Chow convolution/restriction, or a target cohomological action. | `SchemeCorrespondence.graphMorphism`, `graphIdeal`, `graphSubschemeIso`, `graphMorphism_isClosedImmersion`, and `graphMorphism_isProper` in `Correspondence/GraphSubscheme.lean`; `LiteratureInputs.FiniteEtaleExtension.pairInclusion_isOpenImmersion`, `graphRestriction_isPullback`, `graphIdeal_restriction`, and `graphIdeal_liftDeckAction` in `Boundary/GraphRestriction.lean`. |
| A11p | FORMAL | Finite ungraded cycles are sums of actual integral ideal-sheaf subschemes; the finite split cycle types are definitional specializations. Actual open inverse image restricts generators, with zero for empty intersections and proved integrality otherwise. The resulting linear restriction has identity and composition laws. A separated integral source gives an integral graph generator with the source's Krull dimension, and rational deck-group sums map linearly to actual graph cycles. For a supplied finite étale extension with integral extended carrier and nonempty original carrier, generator restriction and the rational weighted square follow from the graph-ideal equality. Finiteness, original integrality, and pair openness are derived, and no deck-extension bijectivity is assumed. This does not yet give component multiplicities for nonintegral carriers, dimension-graded Chow groups, convolution, rational-equivalence descent, or Hodge realization. | `SchemeCycles.Cycles` and `.fundamentalCycle` in `Cycles/Basic.lean`; `.openRestriction`, `.openRestriction_fundamentalCycle_of_comap_eq`, `.openRestriction_id`, and `.openRestriction_comp` in `Cycles/OpenRestriction.lean`; `SchemeCorrespondence.graphIntegralSubscheme`, `.graphIdeal_topologicalKrullDim`, `.graphCycle`, and `.graphCycleLinearMap` in `Correspondence/GraphCycles.lean`; `FiniteEtaleExtension.original_isIntegral`, `.graphCycle_restriction`, and `.graphCycleLinearMap_restriction` in `Boundary/GraphCycleRestriction.lean`. |
| A11q | FORMAL | For a separated structural morphism, the supremum of the two inverse-image graph ideals in the actual relative triple product defines a subscheme isomorphic to the source. Its first/last projection factors isomorphically onto the graph of the product automorphism, with the exact noncommutative order and equality of scheme-theoretic image ideals. No finiteness, smoothness, integrality, or ambient-projection properness is assumed for these scheme statements. Separately, an integral closed immersion has generic stalk length one over the ambient stalk through its actual stalk map. This verifies the integral fundamental multiplicity, not a Chow intersection-product or rational-equivalence comparison. | `SchemeCorrespondence.tripleProduct`, `.graphCompositionMorphism`, `.graphIntersectionIdeal`, `.graphIntersectionIso`, `.graphCompositionIso`, and `.graphIntersectionIdeal_map_p13` in `Correspondence/GraphComposition.lean`; `SchemeCycles.genericStalk_length_of_isClosedImmersion` and `.integralSubscheme_genericStalk_length` in `Cycles/IntegralMultiplicity.lean`. |
| A11r | FORMAL | Actual closed-support image cycles use the mapped ideal sheaf and a proved support-to-image isomorphism, generic-point identification, and degree-one residue map. Closed-immersion cycle pushforward is linear and satisfies identity/composition. The graph slice is the actual inverse image of the first graph in the relative triple product; its last-pair map is an isomorphism. Pullback along that isomorphism sends the graph of σ to the graph of σ*τ; closed slice pushforward gives the integral intersection cycle, whose supportwise outer image is the composite graph cycle. The graph-slice maps preserve rational weights. Étaleness additionally proves the graphs, slice, and inverse-image/intersection inclusions open; neither the pair scheme nor inverse-image graph subschemes are assumed integral. These are finite relative-cycle pull–push operations, not a general Chow convolution or an absolute-product intersection comparison. | `SchemeCycles.closedImageSubschemeIso`, `.closedImageSubschemeIso_genericPoint`, `.closedImageCycle_eq_residueDegree_smul`, and `.closedImmersionPushforward_comp` in `Cycles/ClosedImmersionPushforward.lean`; canonical `.residueFieldMap_finrank_of_isIso` in `Cycles/ResidueDegree.lean` (old split name retained as adapter); openness instances in `Correspondence/EtaleGraphIntersection.lean`; `graphSlice_isPullback` and `graphIdeal_comap_p12_eq_graphSlice_ker` in `Correspondence/GraphSlice.lean`; `graphRightPullback_graphCycle`, `graphSlicePullPush_graphCycle`, `graphIntersectionCycle_image_p13`, and `graphSlicePullPush_graphCycleLinearMap_single` in `Correspondence/GraphCycleComposition.lean`. |
| A11s | FORMAL | For actual structural maps p : Y → S and b : S → B, deck-base forgetting is an injective group homomorphism retaining the scheme automorphism. Separated b gives actual closed pair/triple inclusions into products over B. Graph image ideals are preserved without further hypotheses; separated p as well gives graph-intersection image-ideal preservation. With integral Y these comparisons preserve the corresponding integral cycles and weighted graph assembly. On entire finite-cycle modules their closed pushforwards intertwine pair-isomorphism pullback and graph-slice pull–push; these squares need no integrality hypothesis. Isomorphism pullback is proved equal to inverse-isomorphism closed pushforward. For B = Spec k the destination products are absolute. No arbitrary intersection-product or rational-equivalence comparison is asserted. | `forgetDeckBase`, `forgetDeckBase_injective` in `Correspondence/DeckBaseChange.lean`; pair/triple maps in `Correspondence/RelativeProductComparison.lean`; actual morphism/image-ideal identities in `Correspondence/GraphBaseComparison.lean`; the five comparison theorems in `Correspondence/GraphCycleBaseComparison.lean`; `SchemeCycles.openRestriction_iso_eq_pushforward_inv` and `pushforward_openRestriction_iso` in `Cycles/IsomorphismTransport.lean`. |
| A11t | FORMAL | The existing quotient-length fraction-field order gives signed integer orders of nonzero rational functions, with finite principal-quotient lengths, product/inverse laws, the fraction formula, and zero on units of the base ring. Ring equivalences preserve actual quotient lengths and compatible field equivalences preserve orders. Scheme isomorphisms give actual contravariant function-field maps through the generic stalk and commute with every local stalk map. Points with one-dimensional stalks are transported bijectively; affine height-one primes supply such points. On integral locally Noetherian schemes the resulting local divisor coefficients are invariant under these actual maps, without normality or DVR hypotheses. A computed integer-ring example has orders 1 and −1. Actual codimension-one closed support identification is recorded in A11u, local/finite support in A11v, and finite principal-divisor assembly and isomorphism transport in A11w; A11x provides homogeneous pieces for a supplied dimension function, while A11y supplies the principal-relation quotient and closed/isomorphism descent. Its intended geometric dimension-function instantiation and further Chow operations remain open. | `localOrder`, `localOrder_algebraMap`, `localOrder_fraction`, `localOrder_map_unit` in `Cycles/LocalOrder.lean`; `ord_ringEquiv` and `ordFrac_ringEquiv` in `Cycles/LocalOrderTransport.lean`; `functionFieldEquiv` and `functionFieldEquiv_algebraMap` in `Cycles/FunctionFieldTransport.lean`; `DivisorPoint`, `divisorPointOfAffineHeightOne`, `divisorPointEquiv`, `divisorOrder_iso` in `Cycles/SchemeLocalOrder.lean`; `Examples.localOrder_int_two` and `Examples.localOrder_int_two_inv` in `Cycles/Examples/LocalOrder.lean`. |
| A11u | FORMAL | On any scheme, reduced point closure is an actual integral ideal-sheaf subscheme, and the image of a subscheme's generic point is its inverse; no ambient integrality or Noetherianity is assumed. The coheight of the actual support in the inclusion order on irreducible closed subsets equals the dimension of its ambient generic-point stalk. Hence the existing one-dimensional-stalk point index is equivalent to the codimension-one subtype of the existing integral cycle generators. Closed support-to-image isomorphisms carry the ambient generic point to its actual image; scheme isomorphisms preserve codimension, and prime-divisor transport is literally the existing ideal-sheaf image. Closed-immersion cycle pushforward agrees with reduced point closure. On integral locally Noetherian schemes, reindexing the unique existing local order by these supports gives the corresponding isomorphism-invariance law. A11v supplies local/finite support and A11w assembles the resulting principal-divisor cycles and their isomorphism transport. SP36 itself is the support-identification checkpoint; no grading or rational-equivalence quotient is constructed there. | `pointSupport`, `ambientGenericPoint`, and `pointEquivIntegralClosedSubscheme` in `Cycles/PointSupport.lean`; `point_coheight_eq_stalkDim` and `support_coheight_eq_stalkDim` in `Cycles/SupportCodimension.lean`; `supportCodimension_eq_stalkDim`, `divisorPointEquivPrimeDivisor`, `ambientGenericPoint_closedImageSubscheme`, `primeDivisorEquiv_val`, `closedImmersionPushforward_pointSupport`, and `primeDivisorOrder_iso` in `Cycles/DivisorSupport.lean`. |
| A11v | FORMAL | A height-one prime containing a nonzero element of a domain is minimal over its principal ideal; Noetherianity makes the set of such primes finite. On a nonempty affine open of an integral scheme, every actual nonzero rational function is a fraction of nonzero sections, and the canonical section-to-field map factors through the actual stalk. Unit germs force zero local order. For integral locally Noetherian schemes this proves finiteness of nonzero divisor-point coefficients in each affine open, including the empty-open case. The generic-point/open-intersection equivalence gives local finiteness of the actual closed prime-divisor supports indexed by nonzero coefficients, not just point-finiteness. Quasi-compactness then gives finite support of both the prime-divisor and equivalent point-indexed coefficient functions. No normality, properness, finite-type, or global one-dimensionality assumption is used. SP37 is the finiteness checkpoint; A11w assembles the resulting finite ungraded principal-divisor cycles and their isomorphism transport. A11x provides homogeneous pieces for a supplied dimension function, and A11y constructs the corresponding Noetherian principal-relation quotient and closed/isomorphism descent. | `heightOne_mem_minimalPrimes_span` and `finite_heightOne_primes_containing` in `Cycles/HeightOneFiniteness.lean`; `exists_affine_fraction`, `sectionToFunctionField_through_stalk`, `affineGerm_isUnit_iff`, and `divisorOrder_eq_zero_of_affine_fraction` in `Cycles/RationalFunctionPresentation.lean`; `finite_divisorPoints_in_affine`, `primeDivisorSupports_locallyFinite`, `finite_primeDivisorOrder_support`, and `finite_divisorOrder_support` in `Cycles/DivisorFiniteness.lean`. |
| A11w | FORMAL | On an integral locally Noetherian quasi-compact scheme, the actual signed prime-divisor coefficients define a finite integral cycle in the existing ungraded cycle module by extension by zero from the codimension-one subtype. The full coefficient formula, exact support, and zero criterion are proved. Multiplication of nonzero rational functions gives addition of these cycles, with one, inverse and quotient laws and a bundled multiplicative-to-additive group homomorphism. An actual scheme isomorphism induces the literal closed-image equivalence of integral subschemes; existing closed-immersion cycle pushforward transports their coefficients, for any semiring and without ambient scheme hypotheses. Applied to principal divisors, actual support/codimension and function-field/stalk transport prove pushforward invariance. The existing open restriction, specialized to an isomorphism, gives the matching pullback identity. No normality, new cycle module, dimension-function grading, rational-equivalence relation or Chow quotient is assumed. Vanishing is characterized by zero local coefficients, not by being a global unit. A11x proves homogeneity separately for an explicitly supplied dimension function; A11y then constructs the genuine principal-relation quotient and its closed/isomorphism maps. | `principalDivisor`, `principalDivisor_apply`, `principalDivisor_support`, `principalDivisor_eq_zero_iff`, `principalDivisor_one`, `principalDivisor_mul`, `principalDivisor_inv`, `principalDivisor_div`, and `principalDivisorAddHom` in `Cycles/PrincipalDivisor.lean`; `closedImageSubschemeEquiv`, `closedImmersionPushforward_iso_eq_lmapDomain`, and `closedImmersionPushforward_iso_apply_image` in `Cycles/IsomorphismTransport.lean`; `principalDivisor_iso` and `openRestriction_principalDivisor` in `Cycles/PrincipalDivisorTransport.lean`. |
| A11x | FORMAL | A dimension function on actual scheme points explicitly requires strict monotonicity in the closure-inclusion order and a unit step on covers. Closed immersion restricts it by the actual point map, respecting identity and composition. The degree of an existing integral closed subscheme is its ambient generic-point value. On an integral scheme, actual chain codimension one makes this generic point immediately below the ambient generic point, giving degree one less without Noetherianity. Homogeneous finite cycles are supported submodules of the existing cycle module; distinct degrees are disjoint. Existing closed-immersion pushforward preserves degree for the proved restricted dimension function, with no separately assumed compatibility. On integral locally Noetherian quasi-compact schemes, the actual finite principal divisor lies in degree δ(η)−1. For an integral closed carrier W, its pushed principal divisor lies in ambient degree degδ(W)−1; only W must be locally Noetherian and quasi-compact. No existence of a dimension function for arbitrary schemes, absolute Krull-dimension subtraction, new free cycle module or full direct-sum equivalence is asserted. SP39 is the homogeneity checkpoint; A11y constructs the principal-relation subgroup and its Chow quotient. | `DimensionFunction`, `primeDivisor_covBy_genericPoint`, `supportDegree_primeDivisor`, and `supportDegree_closedImageSubscheme` in `Cycles/DimensionFunction.lean`; `DimensionFunction.comapClosedImmersion` and `supportDegree_comapClosedImmersion` in `Cycles/DimensionFunctionRestriction.lean`; `cyclesOfDegree`, `mem_cyclesOfDegree_iff`, `cyclesOfDegree_disjoint`, and `closedImmersionPushforward_mem_cyclesOfDegree` in `Cycles/CycleDegree.lean`; `principalDivisor_mem_cyclesOfDegree`, `closedImmersionPushforward_mem_cyclesOfDegree_comap`, `closedImmersionPushforward_principalDivisor_mem_cyclesOfDegree`, and `principalDivisor_closedSupport_mem_cyclesOfDegree` in `Cycles/PrincipalDivisorDegree.lean`. |
| A11y | FORMAL | On a Noetherian scheme with a supplied dimension function, actual integral closed carriers of degree n+1 with units in their own function fields define degree-n principal relations in the existing homogeneous cycle module. Closed carriers inherit the required finiteness properties by affine quotients and closed embeddings. The integer span of the actual generators equals unweighted finite sums of those generators, with integer coefficients absorbed into actual function powers. Local finiteness of the actual nonempty carrier family is proved equivalent to a finite index on a quasi-compact ambient scheme, even when all associated divisor cycles are zero. The quotient and class map satisfy actual rational-equivalence, surjectivity and zero-generator laws. Existing closed pushforward maps each generator to the genuine generator on its actual image carrier using the constructed support-to-image function-field isomorphism, then preserves the span and descends to the quotient with identity/composition. For a scheme isomorphism it gives a quotient equivalence whose inverse on cycle representatives is the existing open restriction. The canonical closed case uses the proved restriction of the target dimension function; relation preservation is proved, not supplied. Arbitrary proper/flat/Gysin operations remain open. A11z records the dimension-at-most-one instance; A11ak constructs the general field-induced grading and A11al identifies its actual carrier dimensions. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. The earlier scalar-extension theorem is finite-split. | `ambientPrincipalDivisor`, `closedImmersionPushforward_ambientPrincipalDivisor`, and carrier finiteness lemmas in `Cycles/PrincipalDivisorImage.lean`; `PrincipalRelationData`, `principalRelation_zpow`, `principalRelationData_family_locallyFinite_iff`, `principalRelations`, `mem_principalRelations_iff_exists_list`, `RationallyEquivalent`, `ChowGroup`, and `classMap` in `Cycles/PrincipalRelations.lean`; `gradedClosedImmersionPushforward` in `Cycles/GradedPushforward.lean`; `gradedClosedImmersionPushforward_principalRelation`, `principalRelations_le_comap_closedImmersionPushforward`, and `chowClosedImmersionPushforward` in `Cycles/ChowPushforward.lean`; `principalRelations_map_gradedIsoEquiv`, `chowIsoEquiv`, `gradedIsoEquiv_symm_val`, and quotient representative formulas in `Cycles/ChowIsomorphism.lean`. |
| A11z | FORMAL | The actual points of an integral closed carrier are order-isomorphic to the specializations of its ambient generic point, so its topological dimension equals that point's height, without ambient assumptions. Finite ambient dimension makes closure heights finite integers and proves strict decrease under proper specialization. An actual polynomial presentation gives a finite dimension bound for every finite-type algebra over a field, including the zero algebra and its empty spectrum. For an actual structural morphism locally of finite type and quasi-compact over a field, its affine chart algebras and finite affine subcover give a global finite-dimensionality theorem, without an independently supplied sections algebra. If actual scheme dimension is at most one, integer point height constructs a dimension function with both strict and unit-step laws proved; no integrality, Noetherianity, nonemptiness or separate grading-law input is required. The constructed degree of every integral carrier equals its actual dimension, and a coefficient-one cycle lies in degree n exactly when its carrier has dimension n, for natural n and nontrivial coefficients. The actual affine line Spec(k[T]) has dimension one; the constructed function gives degree one at its generic point and degree zero at the actual constant-coefficient-kernel origin. Finite-dimensionality alone does not prove the higher-dimensional unit-step law. A11aa subsequently proves the affine transcendence-degree comparison and A11af proves the affine prime-spectrum unit step in every dimension. A11ag constructs the actual affine dimension functions. A11ak constructs the global field-based dimension function. A11al proves the global point-height and closure/carrier dimension comparisons. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | `integralSubschemePointOrderIso`, `ambientGenericPoint_height_eq_supportDim`, `point_height_toNat_eq`, `point_height_toNat_strictMono` in `Cycles/SupportDimension.lean`; `ringKrullDim_le_bound_of_surjective`, `ringKrullDim_lt_top_of_finiteType`, and affine/quotient spectrum bounds in `Cycles/FiniteTypeDimension.lean`; `topologicalKrullDim_lt_top_of_finite_openCover`, `topologicalKrullDim_lt_top_of_finiteType` in `Cycles/FiniteTypeSchemeDimension.lean`; `DimensionFunction.ofKrullDimLEOne`, `supportDegree_ofKrullDimLEOne_eq_iff`, `fundamentalCycle_mem_ofKrullDimLEOne_iff` in `Cycles/LowDimensionalDimensionFunction.lean`; `Examples.affineLine_dimension`, `affineLineDimensionFunction_genericPoint`, `affineLineDimensionFunction_origin` in `Cycles/Examples/DimensionFunction.lean`. |
| A11aa | FORMAL | An actual integral injective map of commutative rings preserves extended Krull dimension, without Noetherianity, domain, nontriviality or finiteness hypotheses. A surjective noninjective algebra map between domains strictly lowers transcendence degree when the source degree is finite; actual prime quotients of a finite-type algebra therefore give strictly decreasing finite degrees, even when the ambient algebra is reducible. Noether normalization's actual integral injection identifies its variable count with the domain's transcendence degree and supplies the lower dimension bound; the independently proved quotient drop gives the prime-chain upper bound. Thus a finite-type domain has dimension equal to the finite transcendence degree of the domain and its actual fraction field, and an n-variable polynomial algebra over a field has exact dimension n. For every prime of any finite-type algebra, its existing actual reduced point-closure carrier has dimension equal to that of the prime quotient and to the finite transcendence degree of the actual prime-localization residue field. Proper specialization strictly lowers this affine value. A11ab and A11ac subsequently supply polynomial and finite-type-domain maximal-local equality, and A11af supplies the affine prime-spectrum unit-step law. A11ag constructs the actual affine dimension functions; A11ak subsequently constructs the global field-based dimension function. A11al proves the global point-height and closure/carrier dimension comparisons. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | `ringKrullDim_eq_of_injective_integral` and actual prime-chain lifting in `Cycles/IntegralDimension.lean`; `trdeg_lt_of_surjective_of_not_injective`, `primeQuotient_trdeg_strictAnti`, `primeQuotient_trdeg_toNat_strictAnti` in `Cycles/TranscendenceDegreeDrop.lean`; `trdeg_eq_normalization_size`, `normalization_size_le_ringKrullDim`, `trdeg_toNat_le_ringKrullDim_of_finiteType` in `Cycles/NormalizationDimension.lean`; `trdeg_eq_of_isFractionRing`, `ringKrullDim_eq_trdeg_toNat_of_finiteType`, `ringKrullDim_eq_fractionRing_trdeg_toNat_of_finiteType`, `mvPolynomial_ringKrullDim_eq_card`, and actual spectrum comparison in `Cycles/AffineDimension.lean`; `spec_pointSupport_dimension_eq_quotientDim`, `primeQuotient_trdeg_eq_residueField`, `spec_pointSupport_dimension_eq_residueField_trdeg`, `spec_point_height_toNat_eq_residueField_trdeg`, `prime_residueField_trdeg_toNat_strictAnti` in `Cycles/AffineSupportDimension.lean`. |
| A11ab | FORMAL | Extension along the actual constant-polynomial map embeds prime spectra, and extending then contracting recovers every ideal. Over any commutative ring, an extended ideal is never maximal; extending the contraction of a polynomial maximal ideal lies strictly below it and gives at least one additional prime-height step. These generic helpers require no field, domain, Jacobson or Noetherian hypothesis. For polynomial algebras in n variables over any field, Jacobson maximal contraction and induction combine with the proved sharp global dimension to show that every maximal ideal has height n, including n=0. Its actual prime localization has dimension n. The actual structure-sheaf stalk at every closed point of the polynomial spectrum has dimension n, and its scheme-point coheight is n in the closure-inclusion order; this is not the closed-carrier height used by the grading. No rational-point or residue-field-degree-one assumption is made. A11ac subsequently proves the normal-base going-down comparison and finite-type-domain maximal-local equality. This polynomial checkpoint does not assert regularity, generator bounds or uniform chains; A11af subsequently supplies the affine prime-spectrum unit step, while A11ag constructs the affine dimension functions. A11ak subsequently constructs the global field-based dimension function and its open-value compatibility. A11al proves the global point-height and closure/carrier dimension comparisons. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | `polynomial_comap_map_C`, `polynomialPrimeExtension`, `polynomialPrimeExtension_height_le`, `polynomial_map_C_not_isMaximal`, `polynomial_map_comap_C_lt`, `polynomial_primeHeight_comap_add_one_le` in `Cycles/PolynomialPrimeHeight.lean`; `mvPolynomial_primeHeight_eq_card_of_isMaximal`, `mvPolynomial_height_eq_card_of_isMaximal`, `mvPolynomial_localization_dimension_of_isMaximal` in `Cycles/PolynomialMaximalHeight.lean`; `mvPolynomial_stalk_dimension_of_isMaximal`, `mvPolynomial_stalk_dimension_of_isClosed`, `mvPolynomial_closedPoint_coheight` in `Cycles/PolynomialClosedPointDimension.lean`. |
| A11ac | FORMAL | Actual finite witnesses in an extended ideal of any integral algebra produce a monic annihilator with the required ideal powers in its coefficients, without an ambient finite-module, domain or Noetherian hypothesis. The actual quotient/fraction-field monic-divisor calculation gives the scaled prime-coefficient lemma. For an injective integral extension of domains with integrally closed base, these polynomial results prove scalar cancellation and construct an actual going-down prime below the prescribed terminal prime. No Noetherianity, finite generation, separability, normality of the upper domain or supplied going-down package is assumed. Integral incomparability and the reused prime-chain lifting inequality give equality of prime height with contraction height. An actual integral injective polynomial normalization therefore computes every maximal height upstairs without requiring the upper domain to be finite type. Noether normalization then gives every maximal localization of any finite-type domain over any field the full global dimension, equal to its finite fraction-field transcendence degree. Actual closed-point structure-sheaf stalks have that dimension, and the corresponding scheme-point coheight has that value; the domain need not be normal and the point need not be rational. This uses prime-chain comparison, not an unproved integrality claim for selected local-ring maps. A11af subsequently supplies the affine prime-spectrum immediate-specialization law. A11ag constructs the actual affine dimension functions. A11ak supplies the global field-based dimension function. A11al proves the global height and carrier-dimension comparisons. A11am supplies actual integral chain codimension and complementary degree. A11an supplies relation reindexing and top-degree vanishing. A11ao supplies general rational coefficient extension. Uniform-chain results and reducible/componentwise targets remain separate. | `exists_monic_annihilator_coeff_mem_pow_of_mem_map`, `exists_monic_annihilator_of_mem_map` in `CommutativeAlgebra/IntegralIdealPolynomial.lean`; `monic_map_eq_X_pow_of_lower_coeff_zero`, `coeff_mem_prime_of_monic_dvd_scaled`, `coeff_mem_prime_of_monic_dvd` in `CommutativeAlgebra/MonicPrimeCoefficients.lean`; `mem_prime_of_mul_mem_map_of_isIntegrallyClosed`, `hasGoingDown_of_isIntegrallyClosed` in `CommutativeAlgebra/NormalGoingDown.lean`; `primeHeight_eq_under_of_isIntegral_of_hasGoingDown`, `normalization_primeHeight_eq_size`, `primeHeight_eq_trdeg_toNat_of_isMaximal`, `height_eq_trdeg_toNat_of_isMaximal`, `localization_dimension_eq_of_isMaximal` in `Cycles/NormalizationLocalDimension.lean`; `affine_stalk_dimension_of_isMaximal`, `affine_stalk_dimension_of_isClosed`, `affine_closedPoint_coheight_eq_trdeg` in `Cycles/AffineClosedPointDimension.lean`. |
| A11ad | FORMAL | For every prime q of any finite-type algebra B over a field, actual Noether normalization of B/q lifts through the quotient map by polynomial variable representatives, with the quotient composite exactly equal to the original normalization. Its injectivity proves that the lifted polynomial map is injective and that the images of nonzero polynomials avoid q; only the quotient composite is claimed integral. The literal localization B′ at those images carries the existing fraction-field algebra K=Frac(P) and proved compatible scalar towers, with no replacement carrier or global algebra instance. Its actual localization pushout proves finite type over K. The localized quotient is an actual domain integral over K and hence a field, proving that q′ is maximal with exact contraction q. The actual prime-interval localization correspondence preserves full prime height; contraction, primality and height need quotient injectivity but not its integrality. These conclusions do not require B to be a domain, reduced or normal. If B is a domain, B′ is a domain and the A11ac maximal-height theorem gives ht(q)=trdeg_K(B′). A11ae subsequently compares this value with transcendence degrees over the original field and proves the arbitrary-prime dimension formula for finite-type domains. Finite transcendence degree of K is obtained from its polynomial variable count, not a generally false finite-type k-algebra assumption. A11af subsequently supplies the affine prime-spectrum unit-step law; A11ag constructs the actual affine dimension functions, and A11ak constructs the global field-based function. A11al proves the global point-height and closure/carrier dimension comparisons. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | `quotientPolynomialLift`, `quotient_comp_quotientPolynomialLift`, `polynomial_map_nonZeroDivisors_disjoint`, and `exists_lifted_residue_normalization` in `Cycles/ResidueNormalizationLift.lean`; `genericFiberAlgebra`, `genericFiberAlgebra_isScalarTower`, `genericFiber_finiteType`, `genericFiber_isDomain`, `genericFiber_localization_injective`, `genericFiber_baseField_injective`, and `genericFiber_isScalarTower_base` in `CommutativeAlgebra/GenericFiberAlgebra.lean`; `residueLocalization_comap_map`, `residueLocalization_map_isPrime`, `residueLocalization_map_isMaximal`, and `residueLocalization_primeHeight_map` in `CommutativeAlgebra/ResidueLocalization.lean`; `residueNormalization_localization`, `exists_residueNormalization_localization`, and `primeHeight_eq_residueNormalization_trdeg` in `Cycles/ResidueNormalizationLocalization.lean`. |
| A11ae | FORMAL | Actual localization of a domain over a field at non-zero-divisors preserves the full transcendence-degree cardinal, with compatible scalar towers and universe lifts; no finite-type or finite-degree assumption is imposed. Domain and injectivity of the localization are derived, and the numeric comparison is only a corollary, not a finiteness assertion. For a finite-type domain B and any injective polynomial map P=k[T₁,…,Tₙ]→B, the actual scalar tower through K=Frac(P) and the literal generic localization B′ proves n+trdeg_K(B′)=trdeg_k(B); no integrality or quotient premise is required for this helper. The proof obtains trdeg_k(K)=n from the actual fraction-field comparison and proves the two cardinal summands finite before passing to natural numbers. Applying the helper to the actual lifted normalization of B/q and the A11ad height comparison gives ht(q)+trdeg_k(B/q)=trdeg_k(B) for every prime q. The same equality uses the actual prime-localization residue field in place of B/q. Ordinary ideal height and actual ring dimensions satisfy ht(q)+dim(B/q)=dim(B), hence dim(B_q)+dim(B/q)=dim(B). The domain is not assumed normal, the field arbitrary, and q need not be maximal or rational. This formula uses no finite-type k-algebra assumption on K and does not assert a reducible global formula or a uniform-chain theorem. A11af supplies the consecutive-prime unit-step law in the actual quotient B/p. A11ag constructs the actual affine dimension functions. A11ak constructs the global field-based dimension function. A11al proves the global point-height and closure/carrier dimension comparisons. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | `lift_trdeg_eq_of_isLocalization`, `trdeg_eq_of_isLocalization`, `trdeg_toNat_eq_of_isLocalization` in `Cycles/LocalizationTranscendenceDegree.lean`; `polynomial_genericFiber_trdeg_toNat_add`, `primeHeight_add_quotient_trdeg_eq`, `height_add_quotient_trdeg_eq`, `primeHeight_add_residueField_trdeg_eq`, `height_add_quotient_dimension_eq`, `localization_dimension_add_quotient_dimension_eq` in `Cycles/AffinePrimeDimension.lean`. |
| A11af | FORMAL | A cover p⋖q in the prime spectrum of any commutative ring becomes a cover of zero by the actual image of q in B/p. The actual quotient-prime order correspondence therefore proves that this image has prime height one, without an ambient domain, Noetherian, finite-type or catenarity hypothesis. The cover is among prime ideals, not all ideals, and its height is derived rather than supplied. For a finite-type algebra B over any field, apply A11ae to the actual finite-type domain B/p and this height-one prime. The actual double-quotient k-algebra equivalence then proves trdeg_k(B/q)+1=trdeg_k(B/p). The same unit drop holds for the actual prime-localization residue fields, and the actual quotient dimensions satisfy dim(B/q)+1=dim(B/p). The ambient algebra may be reducible or nonreduced; no normality, equidimensionality, separability or rational-point hypothesis is imposed. This checkpoint proves the affine prime-spectrum law; A11ag subsequently constructs its actual affine dimension-function adapters. No unit increase of ambient stalk dimension for arbitrary reducible schemes, general catenarity or uniform-chain theorem is asserted. A11ak constructs the global field-based dimension function. A11al proves the global point-height and closure/carrier dimension comparisons. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | `primeQuotient_map_isPrime`, `primeQuotient_bot_covBy_map`, `primeQuotient_primeHeight_eq_one_of_covBy` in `CommutativeAlgebra/PrimeQuotientCover.lean`; `primeQuotient_trdeg_toNat_add_one_of_covBy`, `prime_residueField_trdeg_toNat_add_one_of_covBy`, `primeQuotient_dimension_add_one_of_covBy` in `Cycles/ConsecutivePrimeDimension.lean`. |
| A11ag | FORMAL | The existing identity-on-points affine order isomorphism is exposed and reused, not duplicated. For any finite-type algebra A over any field k, the literal scheme Spec A carries an actual dimension function whose value is the integer cast of the finite transcendence degree of the existing prime-localization residue field. The proved strict degree drop and A11af cover law supply both defining axioms after reversing prime inclusion. Its values are nonnegative and equal actual integer scheme-point height, hence reduced point-closure dimension. For an actual affine scheme X with structural p:X→Spec k locally of finite type, the morphism supplies the finite-type sections algebra; the canonical affine isomorphism and existing closed-immersion restriction prove both dimension-function laws for literal integer point height on X. No independently supplied sections algebra, dimension function or grading law is used. Both constructions allow reducible, nonreduced and empty affine schemes, without normality or a dimension-at-most-one hypothesis. The constructed degree of every actual integral closed carrier matches its topological dimension; for n∈ℕ and nontrivial semiring coefficients, existing fundamental-cycle homogeneity is exactly that dimension test. The degree submodule and cycle type are unchanged. A11ah subsequently constructs the structural actions, actual affine residue-field algebra comparison and general open-immersion residue-degree invariance. A11ai identifies this height-defined function for arbitrary structural affine X with the actual scheme-residue degree and proves affine-open value agreement. A11aj proves pointwise finiteness and chart-value agreement over a nonaffine ambient scheme. A11ak proves both common-chart laws and constructs the global field-based dimension function. A11al proves the global point-height and closure/carrier dimension comparisons. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. No unrestricted open-immersion invariance of absolute point height is asserted. | Reused public `specPointOrderIso` in `Cycles/AffineSupportDimension.lean`; `DimensionFunction.ofSpecFiniteType`, `DimensionFunction.ofSpecFiniteType_apply`, `DimensionFunction.ofSpecFiniteType_eq_pointHeight`, `DimensionFunction.ofSpecFiniteType_nonneg`, `supportDegree_ofSpecFiniteType_eq_iff`, `fundamentalCycle_mem_ofSpecFiniteType_iff` in `Cycles/AffineDimensionFunction.lean`; `DimensionFunction.ofAffineLocallyOfFiniteType`, `DimensionFunction.ofAffineLocallyOfFiniteType_apply`, `DimensionFunction.ofAffineLocallyOfFiniteType_nonneg`, `supportDegree_ofAffineLocallyOfFiniteType_eq_iff`, `fundamentalCycle_mem_ofAffineLocallyOfFiniteType_iff` in `Cycles/AffineSchemeDimensionFunction.lean`. |
| A11ah | FORMAL | An actual structural morphism to Spec k defines the base-ring action on each existing scheme-stalk residue field by pulling back global constants and evaluating. The algebra is an ordinary definition used locally, not a global instance or an action transferred from a proxy residue field. Naturality proves that the actual contravariant residue-field map of a morphism over k is a k-algebra homomorphism; for an open immersion it is a k-algebra equivalence with the same underlying geometric map. On an actual spectrum, the canonical stalk-localization isomorphism induces a ring equivalence with the existing prime-localization residue field. Its equality on every ambient-ring constant proves compatibility with the structural k-action and upgrades it to a k-algebra equivalence. These comparisons allow arbitrary commutative base rings and affine rings; no finite-type, domain, reducedness or normality premise is used. Over a field, the affine and arbitrary-open-immersion comparisons preserve the full transcendence-degree cardinal without finite-type assumptions. For a finite-type affine algebra, the actual scheme-residue degree is proved finite before passing to the integer value of the existing literal-spectrum dimension function. No new dimension function is defined. A11ai identifies the height-defined function on arbitrary structural affine X with its actual scheme-residue degree and proves affine-open value agreement. A11aj proves chart values and pointwise finiteness over a nonaffine ambient scheme. A11ak proves both common-chart laws and constructs the global dimension function. A11al proves the global point-height and closure/carrier dimension comparisons. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | `residueFieldBaseMap`, `residueFieldBaseAlgebra`, `residueFieldBaseAlgebra_algebraMap`, `residueFieldBaseMap_comp`, `residueFieldBaseAlgHom`, `residueFieldBaseAlgHom_apply`, `residueFieldBaseAlgEquivOfIsOpenImmersion`, `residueFieldBaseAlgEquivOfIsOpenImmersion_apply` in `Cycles/StructuralResidueField.lean`; `specResidueFieldEquiv`, `specResidueFieldEquiv_evaluation`, `specResidueFieldAlgEquiv`, `specResidueFieldAlgEquiv_apply` in `Cycles/AffineResidueField.lean`; `spec_schemeResidueField_trdeg_eq`, `spec_schemeResidueField_trdeg_lt_aleph0`, `DimensionFunction.ofSpecFiniteType_eq_schemeResidueField_trdeg`, `residueFieldBase_trdeg_eq_of_isOpenImmersion` in `Cycles/AffineResidueFieldDimension.lean`. |
| A11ai | FORMAL | For any actual affine scheme X with a locally finite-type structural morphism p:X→Spec k over a field, the existing scheme-stalk residue field with its independently defined structural action has finite transcendence degree. The canonical affine isomorphism supplies the actual finite-type sections algebra; equality of the transported structural map retains scalar compatibility in the SP49 residue comparison. The existing height-defined dimension function therefore equals the finite residue degree, without a new function, action, sections-algebra input or compatibility hypothesis. The actual point-height isomorphism theorem is exposed and reused with its proof unchanged. For an open immersion between affine schemes, the existing dimension functions for the compatible structural morphisms agree at corresponding points. No domain, reducedness, normality, nonemptiness or dimension bound is required; finiteness concerns transcendence degree, not finite type of the residue field. A11aj proves pointwise residue-degree finiteness and agreement of chart values over a nonaffine ambient scheme. A11ak subsequently proves both common-chart laws and constructs the global function. A11al proves the global point-height and closure/carrier dimension comparisons. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | Reused public `point_height_iso` in `Cycles/AffineSchemeDimensionFunction.lean`; `affine_schemeResidueField_trdeg_lt_aleph0`, `DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg`, `DimensionFunction.ofAffineLocallyOfFiniteType_apply_of_isOpenImmersion` in `Cycles/AffineSchemeResidueDegree.lean`. |
| A11aj | FORMAL | Every point of an actual scheme X with a locally finite-type structural morphism p:X→Spec k over a field has finite transcendence degree in its existing scheme-stalk residue field with the independently defined structural action. The proof chooses one actual affine chart through that point and uses the proved base-compatible open-immersion residue comparison. No affineness of X, quasi-compactness, finite subcover, global dimension bound, integrality, reducedness or normality premise is required. The existing dimension function on any affine open chart equals the finite residue-degree value at its actual ambient image. Two such chart values agree whenever their ambient point images are equal; the dependent residue carrier and its structural action are transported together. No affine-intersection assumption, new global function, dimension-function object or gluing package is introduced. This checkpoint proves pointwise finiteness and numerical chart agreement; A11ak subsequently proves the common-chart order/cover laws and constructs the global dimension function. A11al proves the global point-height and closure/carrier dimension comparisons. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | `schemeResidueField_trdeg_lt_aleph0`, `affineChart_dimension_eq_schemeResidueField_trdeg`, `affineChart_dimension_eq_of_eq_image` in `Cycles/ChartResidueDegree.lean`. |
| A11ak | FORMAL | Every actual scheme X locally of finite type over a field k carries a constructed dimension function given by the integer value of its actual structural residue degree. A specialization pair lies in one actual affine open; the actual chart inclusion transfers strict specialization and reflects the ambient cover into that chart. The previously proved affine laws and actual chart-value comparison prove both strict monotonicity and the immediate-specialization unit step, not merely one of them. The construction inhabits the existing DimensionFunction structure and retains the independently derived structural residue action. Pointwise finiteness is already proved, and values are nonnegative. On an affine scheme, the whole dimension-function object equals the previous affine construction. Any actual open immersion preserves values for the compatible structural morphisms, without affineness on either side. There is no quasi-compactness, finite subcover, integrality, reducedness, normality, global dimension bound or supplied gluing/grading-law hypothesis. A11al subsequently identifies this function with actual finite point height and integral-carrier dimension. A11am proves actual chain codimension versus complementary degree on integral schemes. A11an reindexes the existing principal relations by codimension and proves top-degree relation vanishing. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. A11ap supplies representative-preserving rational naturality for closed immersions and isomorphisms. A11at–A11au supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | `exists_isAffineOpen_mem_of_le`, `DimensionFunction.ofLocallyOfFiniteType`, `DimensionFunction.ofLocallyOfFiniteType_apply`, `DimensionFunction.ofLocallyOfFiniteType_nonneg`, `DimensionFunction.ofLocallyOfFiniteType_eq_ofAffineLocallyOfFiniteType`, `DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion` in `Cycles/FieldDimensionFunction.lean`. |
| A11al | FORMAL | On any actual scheme locally of finite type over a field, the constructed global dimension function equals actual finite point height and the dimension of the actual reduced point closure. Nonnegative strictness gives the upper height bound; one actual affine chart, its finite height and existing normalization, and its strict geometric point map give the reverse bound. No affine ambient, quasi-compactness, finite subcover, integrality, reducedness, normality or global dimension bound is used. The existing support degree of every actual integral closed carrier equals its finite dimension. For n∈ℕ, the carrier-degree iff and, over a nontrivial semiring, the existing fundamental-cycle homogeneity iff detect that dimension. Actual open immersions over the structural field preserve point height in this locally finite-type setting, not for arbitrary schemes without those hypotheses. No dimension function, scalar action, closed carrier, cycle module or Chow quotient is replaced. A11am subsequently proves actual integral chain codimension plus degree equal to generic degree and the degree-(d−n) criterion. A11an supplies relation reindexing and top-degree vanishing. A11ao supplies general rational coefficient extension. Target comparison, reducible/componentwise conventions and a uniform shift across mixed-dimensional components remain separate. | `point_height_eq_ofLocallyOfFiniteType`, `point_height_ne_top_of_locallyOfFiniteType`, `DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight`, `pointSupport_dimension_eq_ofLocallyOfFiniteType`, `supportDegree_ofLocallyOfFiniteType_eq_iff`, `fundamentalCycle_mem_ofLocallyOfFiniteType_iff`, `point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType` in `Cycles/FieldSupportDimension.lean`. |
| A11am | FORMAL | For an actual integral scheme locally of finite type over a field, the generic point's finite structural degree equals full ambient dimension. Actual point coheights and existing support codimensions are finite. Finite-coheight induction and the proved immediate-specialization unit law give codimension plus existing carrier degree equal to the generic degree, not a new definition of codimension as a dimension difference. The actual support-dimension comparison gives codimension plus carrier dimension equal to ambient dimension in the full extended dimension type. For every natural n, existing degree d−n detects actual chain codimension n; the existing coefficient-one cycle satisfies the same iff over any nontrivial semiring. Over any semiring, the entire existing homogeneous submodule consists exactly of finite cycles whose nonzero coefficients have actual codimension n. Subtraction is in the integers, so n>d requires no exception or truncation premise. No affineness, quasi-compactness, separate Noetherian premise, supplied uniform-chain theorem, replacement grading or Chow quotient is used. A11an subsequently reindexes the existing principal-relation data by codimension while retaining the literal carrier and its rational function. For arbitrary integral schemes with a supplied dimension function, top-degree relation data are empty; the existing Noetherian premise suffices for the relation span to vanish. A11ao supplies general rational coefficient extension and the scalar-extension quotient comparison. Reducible/componentwise targets and geometric target identification remain separate. | `integral_topologicalKrullDim_eq_ofLocallyOfFiniteType`, `point_coheight_ne_top_of_integral_locallyOfFiniteType`, `point_coheight_add_dimension_of_integral_locallyOfFiniteType`, `supportCodimension_ne_top_of_integral_locallyOfFiniteType`, `supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType`, `supportCodimension_add_dimension_of_integral_locallyOfFiniteType`, `supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType`, `fundamentalCycle_mem_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType`, `mem_cyclesOfDegree_sub_iff_supportCodimension_of_integral_locallyOfFiniteType` in `Cycles/IntegralCodimension.lean`. |
| A11an | FORMAL | On an actual integral scheme locally of finite type over a field, the existing principal-relation data in degree d−(n+1) are equivalent to actual codimension-n integral closed carriers with units in their own function fields. Both directions retain the literal carrier and rational function; only the proof of the degree/codimension condition changes. This equivalence needs no Noetherian or quasi-compactness premise. Under the existing Noetherian hypothesis for the relation map, the inverse-indexed generator is definitionally the same ambient principal divisor. Its homogeneous degree identifies its nonzero coefficients with codimension n+1, and the existing relation span is generated by those unchanged cycles. Separately, on any integral scheme with any supplied dimension function δ, every support degree is at most δ(η), so principal-relation data in generic degree are empty. No field, finite-type or Noetherian premise is needed for this emptiness theorem. With the existing Noetherian premise, the top-degree relation span is zero and rational equivalence there is equality. No cycle, divisor, dimension function, relation subgroup or quotient is replaced. A11ao supplies rational coefficient extension of the existing homogeneous cycles and the scalar-extension quotient comparison. A11ap proves representative-preserving rational naturality for existing closed-pushforward/isomorphism maps; geometric target identification remains separate. The quotient map into its rationalization is not presumed injective, since torsion can occur. Reducible/componentwise target conventions remain separate. | `principalRelationDataEquivCodimension`, `principalRelationDataEquivCodimension_apply_carrier`, `principalRelationDataEquivCodimension_apply_function`, `principalRelationDataEquivCodimension_symm_apply_carrier`, `principalRelationDataEquivCodimension_symm_apply_function`, `principalRelation_equivCodimension_symm_coe` in `Cycles/PrincipalRelationCodimension.lean`; `isEmpty_principalRelationData_genericDegree`, `principalRelations_genericDegree_eq_bot`, `rationallyEquivalent_genericDegree_iff_eq` in `Cycles/PrincipalRelations.lean`. |
| A11ao | FORMAL | For any actual scheme and supplied dimension function, coefficientwise ℤ→ℚ extension is an injective ℤ-linear map on the existing homogeneous finite-cycle modules. It retains each actual support and coefficient, and a ℚ-linear equivalence identifies rational homogeneous cycles with ℚ⊗[ℤ] of the integral module, sending q⊗z to q·z_ℚ. No integral, Noetherian, field-base, finite-type, compactness or finite-label premise is imposed. A general commutative-ring scalar-extension theorem identifies the quotient by the span of actual generators with the quotient by their scalar-extended span, preserving pure-tensor representatives; it requires neither flatness nor injectivity. On Noetherian X the rational relation space is the ℚ-span of casts of the existing actual principal relations, and the rational Chow group is its quotient. The rational class map is surjective, has precisely that relation space as its kernel and kills each cast generator. The scalar-extension comparison ℚ⊗CH_ℤ≃CH_ℚ sends q⊗[z] to [q·z_ℚ]; tensoring with 1 gives the canonical integral-to-rational Chow map and its class-map square. That Chow map is not asserted injective, since quotient torsion may be killed. On integral Noetherian X with any supplied δ, generic-degree rational relations vanish by the existing empty carrier index. These constructions use the existing cycle supports, dimension function and actual principal divisors, not a freely chosen relation space. A11ap proves rational coefficient naturality for the already constructed graded closed-pushforward and isomorphism maps, preserving representatives. A11aq proves actual integral-open function-field/stalk compatibility and divisor-point/local-order transport. A11ar proves actual open-support restriction, its reduced-closure inverse and the finite-cycle coefficient formula, then principal-divisor restriction for integral schemes with locally Noetherian, quasi-compact target. A11as supplies graded open restriction and the actual open/closed finite-cycle square. A11at proves both ambient principal-divisor branches, graded relation-generator transport, preservation of the integer relation span and rational equivalence. A11au proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. A11av proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. Identification with the intended geometric target, localization, general proper/flat/Gysin relation laws and reducible/componentwise conventions remain separate. | `cyclesOfDegreeRationalize`, `cyclesOfDegreeRationalize_apply`, `cyclesOfDegreeRationalize_injective`, `cyclesOfDegreeRationalize_single`, `cyclesOfDegreeRationalizationEquiv`, `cyclesOfDegreeRationalizationEquiv_tmul`, `cyclesOfDegreeRationalizationEquiv_one_tmul` in `Cycles/CoefficientExtension.lean`; `scalarExtensionQuotientEquiv`, `scalarExtensionQuotientEquiv_tmul_mk` in `Cycles/ScalarExtensionQuotient.lean`; `rationalPrincipalRelations`, `RationalChowGroup`, `rationalClassMap`, `rationalClassMap_eq_zero_iff`, `rationalClassMap_surjective`, `rationalClassMap_principalRelation`, `chowRationalizationEquiv`, `chowRationalizationEquiv_tmul_classMap`, `chowRationalize`, `chowRationalize_classMap`, `rationalPrincipalRelations_genericDegree_eq_bot` in `Cycles/RationalChow.lean`. |
| A11ap | FORMAL | The existing graded closed-immersion cycle pushforward is coefficient-parametric over any semiring, with the same actual closed-image supports, identity/composition laws and support-degree compatibility. The four original integer APIs remain specializations with unchanged signatures. Integer-to-rational coefficient cast commutes with the actual raw cycle map and its homogeneous restriction. For an actual scheme isomorphism, existing open restriction preserves homogeneous cycles for the canonical restricted dimension function over any semiring. None of these cycle results requires Noetherianity. For Noetherian source and target, actual principal-divisor image transport and coefficient compatibility prove that the rational relation span is preserved; this is not assumed as part of the degree comparison. The induced rational Chow closed pushforward retains the actual representative formula and identity/composition laws, with a canonical restricted-dimension specialization. Both the integral-to-rational Chow square and the entire tensor scalar-extension square commute. For an isomorphism, base change of the existing integral Chow equivalence, conjugated by the coefficient comparisons, is proved equal to this actual rational closed pushforward; its inverse on rational representatives is literally the existing openRestriction ℚ. The isomorphism also commutes with the integral rationalization map. No second graded isomorphism model, new cycle carrier, new relation predicate or injectivity for arbitrary closed Chow pushforward is introduced. A11aq proves actual integral-open function-field/stalk compatibility and divisor-point/local-order transport. A11ar proves actual open-support restriction and its coefficient formula, together with integral principal-divisor restriction under the target finiteness hypotheses. A11as supplies graded open restriction and the actual open/closed finite-cycle square. A11at proves ambient principal-divisor restriction, both graded generator branches and integer relation-span/rational-equivalence preservation. A11au proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. A11av proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. General proper/flat/Gysin relation laws, geometric target identification and reducible/componentwise conventions remain separate. | `gradedClosedImmersionPushforwardWithCoefficients`, `gradedClosedImmersionPushforwardWithCoefficients_val`, `gradedClosedImmersionPushforwardWithCoefficients_id`, `gradedClosedImmersionPushforwardWithCoefficients_comp` in `Cycles/GradedPushforward.lean`; `closedImmersionPushforward_rationalize`, `gradedClosedImmersionPushforward_rationalize`, `openRestriction_iso_mem_cyclesOfDegree` in `Cycles/CoefficientPushforward.lean`; `rationalPrincipalRelations_le_comap_closedImmersionPushforward`, `rationalChowClosedImmersionPushforward`, `rationalChowClosedImmersionPushforward_classMap`, `rationalChowClosedImmersionPushforward_restricted_classMap`, `rationalChowClosedImmersionPushforward_id`, `rationalChowClosedImmersionPushforward_comp`, `rationalChowClosedImmersionPushforward_chowRationalize`, `rationalChowClosedImmersionPushforward_chowRationalizationEquiv` in `Cycles/RationalChowPushforward.lean`; `rationalChowIsoEquiv`, `rationalChowIsoEquiv_chowRationalizationEquiv`, `rationalChowIsoEquiv_toLinearMap`, `rationalChowIsoEquiv_classMap`, `rationalChowIsoEquiv_symm_classMap`, `rationalChowIsoEquiv_chowRationalize` in `Cycles/RationalChowIsomorphism.lean`. |
| A11aq | FORMAL | An actual open immersion between integral schemes induces a contravariant equivalence of their existing function fields by its generic-point stalk map. Naturality proves compatibility with actual stalk-specialization maps and the canonical local-ring algebra maps into those fields. No Noetherian, compactness, affine, finite-type, normality or field-base premise is used for this comparison. For an open immersion of arbitrary schemes, actual stalk isomorphisms preserve local dimension and define an injective map on existing divisor points; its image consists exactly of target divisor points whose underlying point lies in the actual open image. This is not a global divisor-point bijection. For integral source and target with target locally Noetherian, signed local orders are preserved under the contravariant function-field map; source local Noetherianity is derived from the open immersion. The proof uses the actual stalk and field isomorphisms with their proved compatibility, not a DVR or normality assumption. The four old isomorphism function-field APIs remain specializations, the old stalk/order laws reuse the general proof, and the old divisor-point equivalence is retained with its forward map equal to the new embedding. A11ar now identifies actual open-support restriction and its reduced-closure inverse, proves the finite-cycle coefficient formula and derives integral principal-divisor restriction with locally Noetherian, quasi-compact target. A11as proves graded open restriction and the actual open/closed finite-cycle square. A11at proves ambient principal-divisor restriction with separate nonempty and empty carrier branches, graded generator transport and integer relation-span/rational-equivalence preservation. A11au proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. A11av proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. An arbitrary open immersion is not treated as a closed-image map. The principal-cycle identity is supplied by A11ar rather than this local checkpoint; Chow quotient descent is supplied by A11au; localization remains open; general proper/flat/Gysin laws and geometric target identification remain separate. | `functionFieldIsoOfOpenImmersion`, `functionFieldEquivOfOpenImmersion`, `functionFieldIsoOfOpenImmersion_stalkSpecializes`, `functionFieldEquivOfOpenImmersion_algebraMap` in `Cycles/FunctionFieldTransport.lean`; `stalkDimension_openImmersion`, `divisorPointEmbedding`, `divisorPointEmbedding_val`, `mem_range_divisorPointEmbedding_iff`, `divisorPointEmbedding_iso`, `divisorOrder_openImmersion` in `Cycles/SchemeLocalOrder.lean`. |
| A11ar | FORMAL | For an open immersion of arbitrary schemes, the actual reduced closure of an integral closed support in the source is the existing pointSupport of its ambient image generic point. Its actual ideal-sheaf comap recovers the original support. Conversely, reduced closure recovers every ambient integral support with nonempty restriction; nonemptiness is equivalent to its generic point lying in the open image. The generic-point formulas and actual stalk isomorphism preserve existing chain codimension and identify the closure of a prime support with the A11aq divisor-point embedding. Over any semiring, the existing finite-cycle restriction reads exactly the original coefficient at this reduced closure; generators with empty inverse image contribute zero. This support/coefficient layer has no ambient integrality, Noetherianity, quasi-compactness, grading or field-base premise. For integral source and target with target locally Noetherian, the signed order on a source prime support is the target order on its actual reduced closure after the actual generic-stalk function-field pullback. With target quasi-compactness, source local Noetherianity and compactness are derived, and actual openRestriction ℤ carries the existing finite principal divisor to the principal divisor of that pullback. The old isomorphism restriction theorem keeps its signature as a specialization. No carrier is replaced by an arbitrary chosen closure, and the open immersion is not treated as a closed-image pushforward. A11as proves graded open restriction from actual δ∘j and compatibility of the actual open/closed finite-cycle square. A11at proves restriction of ambientPrincipalDivisor in its nonempty and empty branches, then preservation of graded generators, the integer relation span and rational equivalence. A11au proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. A11av proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. General proper/flat/Gysin laws and geometric target identification remain separate. | `openClosureSubscheme`, `openClosureSubscheme_ambientGenericPoint`, `ambientGenericPoint_openRestrictionSubscheme`, `nonempty_openRestrictionSubscheme_iff`, `openClosureSubscheme_comap`, `openClosureSubscheme_openRestrictionSubscheme`, `supportCodimension_openClosureSubscheme`, `supportCodimension_openRestrictionSubscheme`, `openClosureSubscheme_divisorPoint`, `openRestriction_apply` in `Cycles/OpenSupport.lean`; `primeDivisorOrder_openImmersion`, `openRestriction_principalDivisor_of_isOpenImmersion` in `Cycles/PrincipalDivisorTransport.lean`. |
| A11as | FORMAL | For an open immersion of arbitrary schemes and a supplied dimension function, literal composition with the actual point map is again a dimension function: both strict specialization monotonicity and the immediate-specialization unit step are proved using the order-convex open image. Restriction respects identity and composition and agrees with the existing closed restriction when the map is also closed. Actual reduced open closure and nonempty ideal-comap restriction preserve support degree. Over every semiring, the existing finite-cycle restriction therefore preserves the existing homogeneous submodules and defines the graded open map with its unchanged underlying representative and identity/composition laws. No new cycle carrier, dimension convention or relation predicate is introduced. For each actual integral closed carrier Z in X, the literal ideal-comap subscheme Z_U and its existing map to Z form the Cartesian open/closed square. Actual finite-cycle open restriction commutes with the two closed pushforwards around that square, including empty Z_U and empty inverse images of individual generators. The carrier inclusion equation itself holds even for arbitrary scheme maps. No ambient integrality, Noetherianity, quasi-compactness, finite-type, field-base or nonempty-source premise is used in these results. A11at proves restriction of ambientPrincipalDivisor with both nonempty and empty carrier branches, graded relation-generator transport and integer relation-span/rational-equivalence preservation. A11au proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. A11av proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. Localization, general proper/flat/Gysin laws, geometric target identification and reducible/componentwise conventions remain separate. | `openImmersion_covBy`, `DimensionFunction.comapOpenImmersion`, `DimensionFunction.comapOpenImmersion_apply`, `DimensionFunction.comapOpenImmersion_id`, `DimensionFunction.comapOpenImmersion_comp`, `DimensionFunction.comapOpenImmersion_eq_comapClosedImmersion`, `supportDegree_openClosureSubscheme`, `supportDegree_openRestrictionSubscheme`, `openRestriction_mem_cyclesOfDegree`, `gradedOpenRestriction`, `gradedOpenRestriction_val`, `gradedOpenRestriction_id`, `gradedOpenRestriction_comp` in `Cycles/OpenGrading.lean`; `openRestrictionSubschemeMap_subschemeι` in `Cycles/OpenSupport.lean`; `openRestriction_closedImmersionPushforward_subscheme` in `Cycles/OpenClosedBaseChange.lean`. |
| A11at | FORMAL | For an actual open immersion j:U→X, the existing ambient principal divisor on an integral closed carrier W restricts through the actual Cartesian carrier square. Only W is assumed locally Noetherian and quasi-compact; the ambient schemes need not be integral or finite. When the ideal-comap carrier W_U is nonempty, its integrality and finiteness are derived and the restricted cycle is the existing ambient principal divisor of the actual contravariant generic-stalk pullback of f. When W_U is empty, the restricted cycle is zero, without constructing a function field or replacement relation datum on the empty carrier. For an arbitrary supplied δ and degree m, genuine principal-relation data restrict on the nonempty branch to the literal W_U and actual pulled-back function, retaining carrier degree m+1; this data construction has no finiteness hypothesis. If X is Noetherian, U is proved Noetherian and the existing graded open map sends each actual principal generator to that restricted generator or zero. Therefore it preserves the existing integer relation span and the actual rational-equivalence predicate. This is a proved consequence of the two geometric carrier identities, not a supplied relation-preservation hypothesis. A11au proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. A11av proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. Localization, general proper/flat/Gysin laws, geometric target identification and reducible/componentwise conventions remain separate; the quotient maps are supplied by A11au rather than this generator checkpoint. | `openRestriction_ambientPrincipalDivisor_of_nonempty`, `openRestriction_ambientPrincipalDivisor_of_isEmpty` in `Cycles/PrincipalDivisorRestriction.lean`; `openImmersion_isNoetherian`, `PrincipalRelationData.openRestriction`, `PrincipalRelationData.openRestriction_carrier`, `PrincipalRelationData.openRestriction_function`, `gradedOpenRestriction_principalRelation_of_nonempty`, `gradedOpenRestriction_principalRelation_of_isEmpty`, `principalRelations_le_comap_openRestriction`, `rationallyEquivalent_openRestriction` in `Cycles/PrincipalRelationRestriction.lean`. |
| A11au | FORMAL | The existing graded open restriction descends through the proved integer principal-relation span inclusion to the existing integral Chow quotient. Only the target scheme is assumed Noetherian; the source and intermediate open schemes inherit that property, and their dimension functions are the literal restrictions δ∘j. The map preserves the actual cycle representative and satisfies identity and contravariant composition. Independently of all finiteness hypotheses, raw and homogeneous finite-cycle open restriction commute with coefficientwise ℤ→ℚ extension. This coefficient compatibility and the genuine nonempty/empty relation-generator identities preserve the rational principal-relation span. The resulting rational Chow restriction is defined on the existing rational quotient, keeps the actual representative formula and is contravariantly functorial. It commutes with the integral-to-rational Chow map, and under the existing tensor comparisons it is exactly scalar extension of integral restriction on every tensor element. No new cycle, relation or quotient carrier, no additional descent hypothesis and no injectivity of Chow rationalization are introduced. A11av proves raw/graded cycle and integral/rational Chow restriction surjectivity via actual reduced support closures and class representatives. SP110 now proves the actual closed-complement support/kernel/image comparisons and integral/rational Chow localization exactness; see the current localization entry above. General proper/flat/Gysin laws, geometric target identification and reducible/componentwise conventions remain separate. | `chowOpenRestriction`, `chowOpenRestriction_classMap`, `chowOpenRestriction_id`, `chowOpenRestriction_comp` in `Cycles/ChowOpenRestriction.lean`; `openRestriction_rationalize`, `gradedOpenRestriction_rationalize` in `Cycles/CoefficientRestriction.lean`; `rationalPrincipalRelations_le_comap_openRestriction`, `rationalChowOpenRestriction`, `rationalChowOpenRestriction_classMap`, `rationalChowOpenRestriction_id`, `rationalChowOpenRestriction_comp`, `rationalChowOpenRestriction_chowRationalize`, `rationalChowOpenRestriction_chowRationalizationEquiv` in `Cycles/RationalChowOpenRestriction.lean`. |
| A11av | FORMAL | For an open immersion of arbitrary schemes, every finite cycle over any semiring lifts by taking the actual reduced ambient closures of its integral supports with unchanged coefficients. The actual ideal-comap identities prove that restriction recovers the original cycle. The proved support-degree comparison makes this lift homogeneous for the supplied dimension function and its literal restriction, so the existing raw and graded restriction maps are surjective. No ambient integrality, Noetherianity, quasi-compactness, field-base or nonempty-source hypothesis is needed at cycle level. For a Noetherian target, the source is derived Noetherian; choosing an actual homogeneous cycle representative and lifting it proves surjectivity of both the existing integral and rational Chow restriction maps. Closure is used to lift cycles and is not asserted to preserve rational equivalence or define a Chow right inverse. No new cycle or quotient carrier is introduced. SP110 now supplies the actual closed-complement support/kernel/image comparison and integral/rational Chow localization exactness; see the current localization entry above. General proper/flat/Gysin laws, geometric target identification and reducible/componentwise conventions remain separate. | `openRestriction_surjective`, `gradedOpenRestriction_surjective` in `Cycles/OpenRestrictionSurjectivity.lean`; `chowOpenRestriction_surjective` in `Cycles/ChowOpenRestriction.lean`; `rationalChowOpenRestriction_surjective` in `Cycles/RationalChowOpenRestriction.lean`. |
| A12 | CONDITIONAL | Given the exact local input that the selected prime of the inertia fixed ring is unramified, containment `I ≤ H` implies unramifiedness of the selected prime in the `H`-fixed ring. The basic theorem imposes Dedekind only on the selected localization. For a finite group and a height-one prime, invariant-theoretic going down preserves height one; normality and Noetherianity therefore make that localization a DVR. The normal-closure endpoint composes this with the formal valuation-to-prime-inertia comparison and remains based over the literal full invariant ring `S^G`; it does not silently replace `S^G` by `B`. The former global-Dedekind theorem remains as a wrapper. This controls one selected branch, not the entire `G/H` cover, and Tag `0BST` remains an explicit premise. | `NormalizationInertia.InertiaFixedRingUnramifiedAt` in `Inputs/FixedInertia.lean`; `fixedPointsLocalRingHom`, `fixedPointsLocalRingHom_injective`, and `fixedRing_isUnramifiedAt_of_inertia_le_localized` in `Boundary/Normalization/FixedRingUnramified.lean`; `fixedPoints_primeHeight_under_eq_one` and `fixedRing_isUnramifiedAt_of_inertia_le_of_primeHeight_eq_one` in `Boundary/Normalization/FixedRingLocalization.lean`; `normalizationFixedRing_isUnramifiedAt_of_primeInertia_le` and `Diagram.fixedRing_isUnramifiedAt_of_valuationInertia_le` in `Boundary/Normalization/PrimeInertiaDescent.lean` |
| A12b | FORMAL (DVR) | For the integral closure of a discrete valuation ring in a finite Galois field extension, at a selected maximal prime, the ring fixed by its actual inertia group has an étale selected localization over the DVR. The proof adapts the AxiomMath/Stacks formalization of the étaleness component of Stacks Tag 09EH, with Apache-2.0 attribution. The project also proves its prime-inertia kernel equals Mathlib's inertia and that selected étaleness implies the existing local unramifiedness input. Transport from a height-one prime of the original normalization through base localization and fixed rings remains open; neither the general Tag 0BST theorem nor the arbitrary-base `hI` is claimed. | `primeInertiaSubgroup_eq_inertia` in `Boundary/Normalization/PrimeInertia.lean`; `ramificationIdx_eq_one_and_isSeparable_of_inertia` in `Boundary/Normalization/DvrInertiaEtale.lean`; `inertia_fixedSubalgebra_etale_atPrime` in `Boundary/Normalization/DvrInertiaFixedRing.lean`; `inertiaFixedRingUnramifiedAt_of_etaleAtPrime` in `Boundary/Normalization/FixedInertiaEtaleBridge.lean`; focused audit `research/FixedInertiaVerification.lean` |
| A13 | FORMAL | Rational pull and push maps satisfying `push ∘ pull = d · id`, with nonzero integral degree `d`, define an idempotent normalized pull--push operator. The theorem proves the algebraic transfer calculation but does not construct Chow groups or the geometric pull/push maps. | `normalizedPullPush_isIdempotent` and `RationalDegreeTransfer.normalizedProjector_isIdempotent` in `Realization/Chow/TransferProjector.lean` |
| A14 | FORMAL | Ring-theoretic prime inertia is realized as the stabilizer kernel of the residue action. A selected prime is the unique prime above its contraction to its own inertia-fixed ring; this needs only finiteness of the acting group. For every centered valuation in a normalization diagram, valuation inertia acts trivially modulo the center and is contained in prime inertia. For marked finite normal-closure data with separable `L/K`, an affine base integrally closed in that field is equivalent to the full invariant normalization ring. | `primeInertiaSubgroup`, `eq_of_under_primeInertiaSubgroup_eq`, `mem_primeInertiaSubgroup_iff`, `baseEquivFullInvariantNormalizationRing`, `Diagram.valuationInertia_sub_centerPrime`, and `Diagram.valuationInertia_le_normalizationPrimeInertiaGroup` in `Boundary/Normalization/PrimeInertia.lean` |
| A15 | FORMAL | Compatible localization data supply the reverse containment from prime inertia to valuation inertia. For a normalization diagram over a Noetherian affine base, those data follow from the supplied finite normalization, height-one center, and centered discrete valuation: the height-one localization is a valuation ring and maximality in the common fraction field identifies it with the centered valuation ring. Hence `I_val ≤ H` implies the prime-inertia containment `I_Q ≤ H` required by the fixed-ring descent. Combining this with the independent Jacobian-inherited forward containment gives equality, but equality is not a dependency of the main endpoint. Without Noetherianity or direct localization data, the reverse comparison remains conditional. | `ValuationLocalizationAt.primeInertia_le_valuationInertia`, `Diagram.hasValuationLocalizationAt_of_isNoetherianRing`, and `Diagram.normalizationPrimeInertia_le_of_valuationInertia_le_of_isNoetherianRing` in `Boundary/Normalization/LocalizationBridge.lean`; equality is the optional `Diagram.valuationInertia_eq_normalizationPrimeInertiaGroup_of_isNoetherianRing` |

## Candidate B: collision decomposition

| ID | Status | Prose claim | Lean witness |
| --- | --- | --- | --- |
| B1 | FORMAL | For a separated etale morphism, the self-fiber product decomposes as the relative diagonal and its open complement, with both inclusions clopen. | `separatedEtaleCollisionSchemeDecomposition` (and its finite-etale specialization `finiteEtaleCollisionSchemeDecomposition`) in `HodgeConjecture/Collision/EtaleDecomposition.lean`, together with the inclusion instances in `ClopenDecomposition.lean` |
| B2 | FORMAL | The affine collision construction identifies the relative diagonal and produces a coproduct decomposition under the proved selector hypotheses. | `HodgeConjecture/Collision/AffineGeometry.lean`, `SchemeDecomposition.lean`, and `ClopenDecomposition.lean` |
| B3 | OPEN | Extract the relevant pure-dimensional/proper cycle classes and prove compatibility of fiber-product composition with refined Chow convolution. | Listed under “Next geometric layer” in `README.md`; A11j establishes the finite split specialization. |

## Candidate C: boundary and Hodge realization

| ID | Status | Prose claim | Lean witness |
| --- | --- | --- | --- |
| C0a | FORMAL | An abstract fixed-codimension model records rational Chow classes, a rational cohomology module intended to be degree `2p`, an independently specified rational Hodge-class submodule, and a cycle-class map whose image consists of Hodge classes. Containment of the Hodge submodule in the cycle-class image is equivalent to the explicit `∀ α, ∃ z` statement and to equality of the two submodules. The graded and family wrappers enforce degree `2 * p` while quantifying over every codimension of one model or an indexed family. They become the classical statements only after genuine variety-level data are supplied. A11l constructs the finite split codimension-zero model; general all-codimension and universal-family instantiations remain separate. | `RationalHodgeCycleClassModel`, `RationalHodgeConjectureAt`, `rationalHodgeConjectureAt_iff`, `rationalHodgeConjectureAt_iff_range_eq`, `RationalHodgeConjectureForModel`, and `RationalHodgeConjectureForFamily` in `Realization/HodgeClasses.lean` |
| C0b | CONDITIONAL | A class `α` is injectively encoded by the graph projector `[[1,0],[α,0]]` on the underlying rational module of `ℚ(-p) ⊕ H^(2p)`.  Pure linear algebra identifies it with the shear-conjugate of `diag(1,0)` and with the normalized average of the identity and an involution; these identities alone do not construct a geometric shear or involution. A11m now constructs an actual Chow shear in the finite split case.  Composition satisfies `e_α e_β = e_α`, so two graph projectors commute exactly when their classes agree.  Given independent Chow-level graph construction and lower-left-block detection maps with realization compatibility, the modeled rational Hodge conjecture is equivalent pointwise, for one model in all codimensions, and for an indexed family to algebraic liftability of every Hodge-class graph projector. A separate compatibility interface identifies rational `(p,p)` classes with graph operators that are morphisms of Hodge structures. A11l instantiates these interfaces with actual finite split degree-zero Chow and Betti objects and an independent effective Hodge structure. Their general cover-generated instantiation remains separate. | `ClassGraphProjector.operator`, `operator_injective`, `operator_mul_operator`, `operator_mul_comm_iff`, `operator_eq_shear_diagonal_shear_symm`, `reflection_isInvolution`, `operator_eq_average_reflection`, `ClassGraphProjectorConstruction`, `ClassGraphProjectorDetection`, `ClassGraphProjectorHodgeCompatibility`, and the graph-lift equivalences in `Realization/Chow/TateGraphProjector.lean` |
| C1 | FORMAL | A generic characteristic-function selector is inertia invariant exactly when the selected sheets form a union of inertia orbits. | `genericSheetSelector_invariant_iff_saturated` in `HodgeConjecture/Boundary/Sheets/GenericProjector.lean` |
| C2 | FORMAL | For an essentially finite-type commutative algebra `R -> S`, the collision Noether different is contained in the annihilator of `Omega[S/R]`, the reverse inclusion holds after taking the radical, and the two ideals have the same prime zero locus. Consequently the collision different detects the non-unramified locus at every prime. This is a support/radical statement, not an equality with the classical Dedekind different. | `collisionNoetherDifferentIdeal_le_kaehlerDifferential_annihilator`, `kaehlerDifferential_annihilator_le_collisionNoetherDifferentIdeal_radical`, `collisionNoetherDifferentIdeal_le_prime_iff_kaehlerDifferential_annihilator_le`, and `collisionDifferentDetectsRamificationAt_of_essFiniteType` in `HodgeConjecture/Boundary/NoetherDifferentRamification.lean` |
| C3 | CONDITIONAL | At the base class of a finite normalization diagram over a Noetherian base, avoidance of the collision different implies inertia saturation using only the explicit comparison between the geometric and group-theoretic inertia indices. It does not require the converse `ramification index one -> unramified`. | `NormalizationInertia.Diagram.baseClass_inertiaSaturated_of_different_not_le` in `Boundary/Normalization/ExtensionBridge.lean`; the remaining substantive input is `ConjugateRamificationRealization`. |
| C3a | CONDITIONAL | Canonical conjugate normalization legs are invariant under the marked fixing subgroup and lie over the affine base. Their pulled-back visible boundaries define a fixed--moving boundary ideal. Over a Noetherian base, supplied center and ramification realizations, formal unramifiedness of the marked visible morphism, and `ConjugateBoundarySeparation` imply absence of ramification at every height-one point of the normal-closure normalization. The theorem does not prove separation, global étaleness, a compactified correspondence, or Chow defect vanishing. | `conjugateNormalClosureToIntermediateNormalization_right_mul` and `conjugateNormalClosureToIntermediateNormalization_comp_toBase` in `Boundary/Normalization/ConjugateNormalization.lean`; `fixedMovingBoundaryIdeal`, `ConjugateBoundarySeparation`, and `Diagram.noCodimensionOneRamification_of_conjugateBoundarySeparation` in `Boundary/Normalization/ConjugateBoundary.lean` |
| C3-iff | CONDITIONAL | The equivalence between collision-different avoidance and inertia extension remains conditional on the stronger supplied `HeightOneInertiaRealization`. C2 discharges the separate `CollisionDifferentDetectsRamificationAt` input under essential finite type. | Combine `collisionDifferentDetectsRamificationAt_of_essFiniteType` with `baseSheet_projector_extends_iff_different_not_le` in `Boundary/ExtensionCriterion.lean`. |
| C4 | CONDITIONAL | Global selector/projector extension follows from all boundary inertia conditions. The conjugate-boundary route now proves those local conditions from supplied center and ramification realizations, visible formal unramifiedness, and `ConjugateBoundarySeparation`; the actual gluing/extension equivalence remains an explicit purity input. This claim stops at an idempotent extension and does not use the compatibility wrappers whose target operator is defined to be that extension's own action. | `GaloisProjectorExtensionPurity` and `CompactifiedSubgroupProjectorExtension` package the purity/comparison input; `Diagram.globalSheetSelectorExtension_of_conjugateBoundarySeparation` and `compactifiedSubgroupProjectorExtension_nonempty_of_conjugateBoundarySeparation` are the active separation-based wrappers. |
| C4a | FORMAL | For a raw compactified closure of a generic idempotent through a supplied restriction algebra map, the convolution defect `Π² - Π` restricts to zero. Vanishing of that defect is equivalent to compactified idempotence, and zero-defect closure witnesses produce an `AlgebraProjectorExtension`. This bare theorem proves restriction-kernel membership only. A11n adds boundary-image membership conditional on selected rational-linear exactness for the same restriction; the geometric map identification and defect vanishing remain separate. | `AlgebraProjectorClosure.convolutionDefect`, `restriction_convolutionDefect`, `convolutionDefect_eq_zero_iff`, `ZeroDefectWitness`, and `toAlgebraProjectorExtension` in `Boundary/ProjectorClosureDefect.lean` |
| C5 | CONDITIONAL | A compactified class lifts a separately prescribed cohomological projector when the restriction comparison and target realization equality are supplied. If that target is the canonical graph projector of a class and the compactified algebra has lower-left Chow-block detection, Lean extracts an algebraic representative. `ClassIndexedFiniteCoverGraphCoverage` allows the extension package to vary with the Hodge class over fixed deck-action data and a finite subgroup and implies the modeled fixed-codimension Hodge target. This abstract context does not assert that `pX` is finite or étale. Under the separately named graph-lift factorization condition targeted to rational Hodge classes, construction and detection give a conditional iff with the Hodge target. The theorem with one fixed extension package is a stronger fixed-package corollary. No coverage or factorization instance is constructed. | `PrescribedChowProjectorLift` and `nonempty_iff_forall_different_not_le` in `Realization/Chow/GaloisProjector.lean`; `ClassIndexedFiniteCoverGraphCoverage`, `GraphProjectorLiftFactorizationThroughFixedDeckData`, `rationalHodgeConjectureAt_of_classIndexedFiniteCoverGraphCoverage`, `rationalHodgeConjectureAt_iff_classIndexedFiniteCoverGraphCoverage`, and `rationalHodgeConjectureAt_of_every_classGraphProjector_for_fixed_extensionData` in `Realization/Chow/GaloisHodgeTarget.lean` |
| C5a | CONDITIONAL | Under essential finite type, avoidance of the collision Noether different at every indexed prime produces an explicit compactified element restricting to the subgroup average and realizing a separately prescribed operator, provided cycle extraction, compactified convolution-idempotence, one-way purity, the named height-one inertia comparison, restriction, and realization are all supplied as visible hypotheses. The theorem does not assert that the indexed primes have height one or exhaust a boundary. This transparent forward corollary discharges only different detection; it is not an unconditional boundary-purity or Hodge theorem. | `exists_prescribed_subgroupAverage_chowProjector_of_different_away` in `Realization/Chow/GaloisProjector.lean` |
| C5b | CONDITIONAL | The canonical `MarkedProjectorActionComparison` compares a chosen correspondence element with the marked selector through a residual linear map and its action square, without any ambient restriction to sheets. Lower-left evaluation and the core Chow-detection bridge give the generated class without surjectivity or original idempotence. For an idempotent correspondence, the square is a morphism of `U = ℚ × ℚ` representations; surjectivity additionally gives the original projector's exact graph action, projector lift, and equality of algebra-homomorphism composites. Its supplied extension data remain available separately, not as fields of the ordinary lift. The extension-based selector and presented comparisons are lossless specializations. The existing Galois coverage schema still requires an extension with ambient restriction to the sheet algebra, lets its marked data vary over fixed `Γ` and `ρ`, and gives the Hodge implication with detection; its converse additionally needs strong replacement, which is existential for the same target class and does not assert equality of projectors. A11d and A11f instantiate the restriction-free coefficient comparison, now with an actual split scheme-span source, but not Chow detection or class-dependent Galois coverage. A11l supplies actual lower-left Chow detection for the finite split block. A11m constructs the actual split torsor, multiplicative residual Chow map, and geometric marked action comparison for the canonical negative fundamental class, without the ambient restriction. No general Chow-motivic residual realization, class-dependent genuine-cover witness, coverage, or replacement instance is constructed. | `MarkedProjectorActionComparison`, `.lowerLeftClass_action_eq_generatedClass`, `.cycleClass_decode_eq_generatedClass`, `.toIdempotentRepresentationMorphism`, and `.action_comp_idempotentMap_eq_classGraph` in `Realization/Chow/MarkedAugmentedRealization.lean`; extension square in `Boundary/GaloisProjectorExtension.lean`; specialized coverage in `Realization/Chow/GaloisMarkedRealization.lean`. |
| C6 | OPEN BEYOND FINITE SPLIT DEGREE ZERO | Extend the genuine Tate-augmented Chow block, its motive variance conventions, graph construction/detection, and Hodge compatibility beyond the finite split degree-zero model, and connect them to geometric marked residual data. A11f--A11k construct the actual split-span/Chow/Betti objects and their maps. A11l supplies the independent finite Hodge structure, actual point-plus-scheme block, and geometric construction/detection with target equivalences. A11m connects actual split torsor/sheet geometry to a multiplicative residual Chow map and fixed-action comparison via an invertible Chow shear. The next bridge is class-dependent generation beyond its canonical negative fundamental class, non-split or positive-dimensional cover geometry, and nontrivial compactification comparisons. Surjective multiplicative residual maps alone are rigid: their generated class is necessarily minus the target unit. Extension to every finite-étale carrier and any required strong replacement remain separate. | `Realization/Betti/Examples/SplitHodgeStructure.lean`, `Realization/Chow/Examples/SplitTateBlock.lean`, and `Realization/Betti/Examples/SplitTateBlock.lean` instantiate the finite split model and block interfaces. The canonical split residual/action instance is in `Realization/Betti/Examples/SplitGaloisMarkedComparison.lean`; general geometric residual maps, class-dependent genuine-cover witnesses, coverage, and strong replacement remain separate. |
| C7 | FINITE DEGREE-ZERO MODEL CONSTRUCTED; GENERAL MODEL OPEN | The combined actual Chow/Betti model, independent effective Hodge subspace, and Tate-block target comparison are constructed for `Spec(ℂ^I)` at codimension zero in A11l. Construct these data beyond that finite split case. Universal Hodge additionally requires the all-codimension data and an indexing family containing all smooth projective complex varieties. | `SplitBettiTateBlock.hodgeModel` and `.hodgeConjectureAt` give the concrete finite codimension-zero instance. No universal `RationalHodgeConjectureForFamily` instance is present. |

## Prohibited headline claims on the current tree

- “Proof of the Hodge conjecture.”
- “Partial proof of the Hodge conjecture” without naming a concrete new class
  of varieties or Hodge classes covered.
- “Construction of arbitrary algebraic Hodge projectors.”
- “Unconditional compactification of the generic projector.”
- “Equality of the collision Noether different with the classical Dedekind
  different” without additional comparison hypotheses.
