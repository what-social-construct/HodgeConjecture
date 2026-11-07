# Implementation reference

Detailed module and theorem inventory moved from the main README. Start with
[the project overview](../README.md) and use the
[current claim ledger](CLAIM_LEDGER.md) for exact theorem scope.
Module paths and shell commands below are relative to the repository root.
Dated build observations and older API spellings below retain their historical
scope; the [Lean 4.35 record](working/0020-lean-4-35-migration.md) gives the
current toolchain and migration checks.

The [graph-Chow checkpoint](working/0025-graph-chow-convolution.md) adds
`Correspondence.GraphChow`, `GraphChowAction`, `GraphChowAlgebra` and
`GraphChowBaseComparison`. They construct canonically graded actual graph
classes, genuine Chow pullbacks, convolution modulo exactly their Chow
relations, and multiplicative passage to the absolute product realized by
closed Chow pushforward. This is the graph-generated algebra; the
general ambient intersection product and prescribed Hodge action remain open.

The [positive-degree checkpoint](working/0026-positive-degree-cycle-realization.md)
constructs all-degree affine cohomology, logarithmic maps and an actual
ordinary projective-line Chow-to-Čech-de Rham degree-two cycle map.
`ProjectiveLineChow` derives principal invariance from the actual local
orders and chart/infinity decomposition. `ProjectiveLineCycleClass` retains
the existing integral/rational Chow source and point normalization;
`ProjectiveLineCohomology` computes the entire constructed Čech target.
The [scheme checkpoint](working/0027-projective-line-scheme-comparison.md)
adds actual fixed-ring form sheaves, canonical affine section comparisons,
proved local affine acyclicity and a two-term derived comparison.
`ProjectiveLineSchemeComparison` identifies the original Čech target with
actual scheme de Rham H² over a field; `ProjectiveLineSchemeCycleClass`
retains the original ordinary Chow source and comparison square. The
comparison is fixed on actual logarithmic representatives.

The [Betti-input checkpoint](working/0028-projective-line-betti-inputs.md)
adds `Betti.SingularCochains`, `Betti.Examples.OnePointComplexInversion` and
`Betti.Examples.ProjectiveLineComplexPoints`, with the focused entry point
`Betti.ProjectiveLine`. These construct actual all-degree rational cochains,
the H⁰ bridge and the affine-atlas homeomorphism to native `OnePoint ℂ`.
`DeRham.LaurentPeriods` proves the actual circle-integral residue formula;
`DeRham.ProjectiveLinePeriods` descends it to the original Čech and scheme
targets and proves normalized ordinary Chow period equals degree.
The singular H² computation is completed in the current checkpoint below.
Positive boundary-period comparison is completed below. General
analytic/Gysin comparison, varieties/codimensions and Hodge-class coverage
remain open.

The [small-chain checkpoint](working/0029-small-singular-chains.md) adds the
focused `Betti.SmallChains` entry point. `SingularSubcomplexes` and native
chain-coordinate adapters retain original simplices and inclusions.
`VertexSubdivision` and `BarycentricMesh` construct the actual recursion,
local homotopy and finite-support mesh shrinking. `SingularSubdivision`
and its homotopy/smallness companions transfer these to original rational
singular chains. `SmallSingularComparison` supplies the two-open homology
comparison. `SubcomplexCochains` supplies the actual small-union gluing
sequence; its full-cochain comparison is completed in the next checkpoint.

The [full singular cohomology checkpoint](working/0031-singular-cohomology-mayer-vietoris.md)
discharges that obligation. `RationalDual` proves exact unrestricted
dualization and native chain/cochain quasi-isomorphism preservation.
`CochainDualCoordinates` and `CochainDualComparison` identify actual
cochains and the canonical full-to-small restriction. `CochainPair` and
`SingularMayerVietoris` construct the full cover sequence on actual subtype
cohomologies; `SingularMayerVietorisMaps` proves the original continuous
pullback formulas and first-minus-second difference.

The [circle/P¹ checkpoint](working/0032-circle-projective-line-singular-cohomology.md)
adds `SingularHomotopy`, `SingularContractible`, `SingularDegreeZeroNaturality`
and `SingularComponents`. The focused `Betti.Circle` entry point computes
actual circle H¹ by the original two-chart boundary quotient, using native
circle topology and actual path components. `TwoComponentBoundary` supplies
the proved quotient by constant pairs. The focused
`Betti.ProjectiveLineCohomology` entry point combines this with actual radial
pullback and the original P¹ affine-chart connecting isomorphism.
`ProjectiveLineBettiCohomology.h2Equiv` computes actual singular H² as ℚ;
`coverGenerator_eq_connecting` retains the original maps, and
`eq_smul_coverGenerator` expresses every actual class in that basis.
The next checkpoint below fixes the positive boundary-period normalization
and supplies independent ordinary maps into the actual singular target.

The [positive boundary-period checkpoint](working/0033-oriented-boundary-period-comparison.md)
adds native `SingularCyclePairing`, computational
`SubcomplexConnectingRepresentative` and the degree-zero representative
bridge. `CircleOrientedCycle` constructs the literal counterclockwise
two-arc cycle; `CircleOrientedPairing.loopPairing_coverGenerator` proves
its pairing with the original cover generator is +1.
`DeRham.LaurentOrientedArcs` proves the original analytic unit-circle
integral equals the derivative-weighted integral over these same angular
arcs. `Betti.ProjectiveLineOrientation` fixes the P¹ boundary sign;
`ProjectiveLineComplexification` retains the genuine tensor product and
original rational embedding. `Betti.ProjectiveLineCycleClass` independently
constructs ordinary Chow maps into actual singular H² by the proved degree
and cover normalization. The map is onto, with original infinity witness.

`DeRham.ProjectiveLinePeriodComparison` is the unique bounded linear
equivalence preserving actual analytic and positive boundary periods.
It retains the factor `2πi` on the Chern class; its normalized version
intertwines the independent ordinary cycle maps. This does not construct
a singular fundamental two-cycle, Poincaré duality, a general analytic
comparison or a geometric Gysin comparison.


This Lean project develops collision ideals as scheme-theoretic input to
algebraic correspondences, with boundary inertia measuring whether a generic
sheet decomposition extends over a compactification.

**Scope.** This work formalizes collision and finite-group correspondence
mechanisms. It constructs a finite split degree-zero Chow/Betti/Hodge model,
but does not establish a new case of the Hodge conjecture or construct the
required general realization.

For the intended statement and its existing Lean equivalence, start with the
[target bridge sketch](../research/TARGET_BRIDGE.md). For component evidence, use the
[gap map](../research/GAP_MAP.md) and
[proof-dependency/archive audit](../research/working/0017-proof-spine-and-archive.md).
The [semantic parity registry](../research/working/0005-semantic-parity-cleanup.md#proof-role-index-core-objects-and-objects-under-investigation)
separates core target/Chow objects from objects specific to candidate proof routes,
with LaTeX notation, Lean representations, and independent implementation status.
It also distinguishes the active unfinished realization from archived branches.
The [claim ledger](../research/CLAIM_LEDGER.md) records theorem scope; dated
checkpoints and [archived plans](../research/archive/planning/README.md) are not
alternative current proof outlines.
The [object bench](../research/bench/README.md) preserves the standalone
matrix-restriction diagnostic outside the active proof path; matrix
coordinates used by the actual finite Chow constructions remain active.

The central distinction is now explicit:

- a coordinate-ring idempotent gives a clopen decomposition of a scheme;
- a correspondence projector is idempotent for **convolution**.

The first statement does not automatically imply the second. One formal
branch, with its missing geometric step displayed, is

\[
\begin{aligned}
\text{collision defects vanish}
&\Longrightarrow
R_f \simeq \Delta_X \amalg R_f^{\mathrm{off}}\\
&\Longrightarrow
[R_f]=1+[R_f^{\mathrm{off}}]
\quad\text{in every additive class model}\\
&\xrightarrow{\ \substack{\text{required geometric input: cycle extraction}\\
                    \text{and convolution compatibility}}\ }
\text{algebraic correspondence idempotent}\\
&\Longrightarrow
\text{cohomological projector}.
\end{aligned}
\]

The middle arrow is genuine geometry.  It includes properness and dimension
conditions, passage to cycles modulo rational equivalence, refined
intersection, and a proof of convolution idempotence.  None of those facts is
smuggled in by the existence of a clopen selector.

## The Hodge-theoretic target

For a smooth projective complex variety \(X\), the usual rational Hodge
conjecture in codimension \(p\) is the surjectivity statement

\[
  \mathrm{cl}^p:\mathrm{CH}^p(X)_{\mathbf Q}
    \longrightarrow \operatorname{Hdg}^p(X).
\]

`Realization/HodgeClasses.lean` now states an abstract schema with exactly
this logical shape: a `RationalHodgeCycleClassModel` keeps the Hodge-class
subspace independent of the cycle-class map, `RationalHodgeConjectureAt` says
every Hodge class lies in its image,
`RationalHodgeConjectureForModel` quantifies over every codimension of one
modeled variety, and `RationalHodgeConjectureForFamily` also quantifies over a
supplied indexing family. The finite split degree-zero model is now
constructed from actual Chow and singular cohomology, with an independent
effective Hodge structure and its geometric Tate-block comparison. The
general variety-level and all-varieties indexing data needed to instantiate
the classical conjecture remain separate.

The class-first generation condition (SP94) is in
[`Realization/Chow/UpstairsGeneration.lean`](../HodgeConjecture/Realization/Chow/UpstairsGeneration.lean).
For each independently specified Hodge class `α`, it asks for an index `i`
and a coefficient `c` in a fixed upstairs recipe with
`cl_i (recipe_i c) = pull_i α`. The index and coefficient may depend on
the class; the family of maps is fixed in advance. The fixed-index version
is the inclusion of the pulled-back Hodge subspace in the recipe's
cycle-class image, not surjectivity onto all upstairs cohomology.

The conditional descent theorem reuses `RationalDegreeTransfer`: given
positive degree, `push_i ∘ pull_i = degree_i • id`, and compatibility of
Chow pushforward with cycle classes, the normalized cycle
`degree_i⁻¹ • pushCH_i (recipe_i c)` represents `α`. These maps and laws
are explicit inputs, not a construction of geometric transfer or a proof
of recipe generation. No new projector or Galois witness package is added.

SP108 adds conditional boundary correction in
[`Realization/Chow/BoundaryCorrection.lean`](../HodgeConjecture/Realization/Chow/BoundaryCorrection.lean).
It lifts an open cycle using the existing Chow restriction and corrects its
class by closed pushforward, given the supported Hodge lift, boundary
algebraicity and cycle-class comparison squares. These geometric inputs and
the open-cycle construction remain to be supplied. For a smooth divisor,
boundary algebraicity can be an induction hypothesis in codimension; the
ambient dimension stays arbitrary.

SP95 now proves the full deck-group comparison in
[`GluedNormalizationDeckComparison.lean`](../HodgeConjecture/Boundary/Normalization/GluedNormalizationDeckComparison.lean).
For integral `X` and finite `N/K(X)`, the original action is an explicit
group equivalence `Aut_{K(X)}(N) ≃ Aut_X(Z_N)`. Its inverse is actual
pullback by the inverse deck transformation through the original field
comparison. Generic pullback already determines a deck transformation
for arbitrary `N/K(X)`. Relative separatedness comes from the existing
affine normalization map; no base normality or separability is added.
SP96 identifies the full marked stabilizer in
[`GluedNormalClosureStabilizer.lean`](../HodgeConjecture/Boundary/Normalization/GluedNormalClosureStabilizer.lean).
For the original finite dominant `p:Y→X` with integral `X/Y` and normal
stalks of `Y`, `λ ∘ a_N(σ) = λ` holds exactly when `σ` fixes the
original embedded `K(Y)`. The existing marked action is a group equivalence
`H ≃ Aut_Y(Z_N)`, with the same inverse-deck pullback formula.
SP97's first fiber bridge is in
[`GenericFiber.lean`](../HodgeConjecture/Boundary/Normalization/GenericFiber.lean).
For finite dominant `p` between integral schemes, the actual generic-stalk
square is a pullback, canonically identifying `Spec K(Y)` with
`Y ×_X Spec K(X)`. The affine proof uses the original section-ring and
function-field pushout; it requires neither normality nor separability.
SP98's
[`GenericFiberBaseChange.lean`](../HodgeConjecture/Boundary/Normalization/GenericFiberBaseChange.lean)
identifies `Spec(E ⊗_{K(X)} K(Y))` with the actual base change
`Y ×_X Spec E` for any commutative `K(X)`-algebra `E`. The map to `Y`
uses the right tensor inclusion followed by the generic-stalk map; the
map to `Spec E` uses the left inclusion. Both are retained by the canonical
comparison, with no new fiber package or field hypothesis on `E`.
SP99's
[`GenericSplitFiber.lean`](../HodgeConjecture/Boundary/Normalization/GenericSplitFiber.lean)
composes this identification with the existing normal-closure tensor/sheet
equivalence. For finite dominant formally unramified `p`, it gives
`Spec(N_p^{G/H}) ≅ Y ×_X Spec N_p`, with both projections and the marked
base-sheet point identified using the original embedding. No new field,
cover, evaluator or splitting is introduced.
SP100's
[`GenericSplitFiberAction.lean`](../HodgeConjecture/Boundary/Normalization/GenericSplitFiberAction.lean)
identifies each coset's evaluation point with its original sheet embedding.
With the existing normal-stalk hypothesis on `Y`, the label `gH` is the
original normalization's generic point followed by `a_N(g⁻¹)` and the
marked refinement. The full pullback-point identity keeps the projection
to `Spec N_p` equal to the identity; no new action or cover is constructed.
SP101's [`FinitePushforward.lean`](../HodgeConjecture/Cycles/FinitePushforward.lean)
constructs degree-weighted pushforward on the existing finite cycles for
any finite morphism. Each support uses its actual mapped ideal and actual
function-field degree; the operation agrees with the existing closed-immersion
map. [`GradedFinitePushforward.lean`](../HodgeConjecture/Cycles/GradedFinitePushforward.lean)
restricts that same map to explicitly compatible dimension functions and
proves integer-to-rational coefficient compatibility. SP107 below descends
this map through the principal relations defining Chow groups.
SP102's [`FiniteResidueField.lean`](../HodgeConjecture/Cycles/FiniteResidueField.lean)
and [`FiniteGrading.lean`](../HodgeConjecture/Cycles/FiniteGrading.lean) identify
the actual finite-map residue extension as algebraic and retain both
structural field actions. The existing transcendence-degree tower formula
then gives canonical field-grading compatibility, discharging that premise
of the same finite cycle pushforward without defining a replacement map.
SP103's [`LocalLength.lean`](../HodgeConjecture/CommutativeAlgebra/LocalLength.lean)
proves the local residue-degree length formula and finite-length descent.
[`LocalOrderLength.lean`](../HodgeConjecture/Cycles/LocalOrderLength.lean) applies
it to the existing principal quotients and signed orders.
SP104 proves the actual semilocal localization sum in
[`SemilocalLength.lean`](../HodgeConjecture/CommutativeAlgebra/SemilocalLength.lean).
[`LatticeIndex.lean`](../HodgeConjecture/CommutativeAlgebra/LatticeIndex.lean) and
[`LocalOrderDeterminant.lean`](../HodgeConjecture/Cycles/LocalOrderDeterminant.lean)
prove the lattice-independent determinant comparison. The resulting
[`LocalOrderNorm.lean`](../HodgeConjecture/Cycles/LocalOrderNorm.lean) identifies
the order of the actual field norm with the base length of `B/bB`, and with
its residue-degree-weighted localized lengths. Freeness, normality and
separability are not assumed. SP105's
[`LocalizedPrincipalQuotient.lean`](../HodgeConjecture/CommutativeAlgebra/LocalizedPrincipalQuotient.lean)
proves the canonical comparison with the principal quotient of the localized
ring, including its formula on fractions and length equality.
[`LocalOrderLocalization.lean`](../HodgeConjecture/Cycles/LocalOrderLocalization.lean)
identifies these lengths with the existing local orders in the same fraction
field. SP106's
[`FiniteSemilocal.lean`](../HodgeConjecture/CommutativeAlgebra/FiniteSemilocal.lean)
derives the semilocal hypotheses and dimension bound from the finite extension;
[`AtPrimeFractionField.lean`](../HodgeConjecture/CommutativeAlgebra/AtPrimeFractionField.lean)
supplies the canonical compatible localization actions. Together,
[`LocalOrderNormFormula.lean`](../HodgeConjecture/Cycles/LocalOrderNormFormula.lean)
proves the full weighted norm--order identity of
[Stacks 02MJ](https://stacks.math.columbia.edu/tag/02MJ) for every nonzero
fraction, with no extra semilocal or local-action premises.
SP107 transports this formula through the actual affine fibers and stalks.
[`FinitePrincipalDivisor.lean`](../HodgeConjecture/Cycles/FinitePrincipalDivisor.lean)
proves `f_*(div_X g) = div_Y(Norm_f g)` for finite dominant maps of integral,
locally Noetherian, quasi-compact schemes locally of finite type over a field.
The established codimension comparison and cycle modules are reused.
[`FiniteChowPushforward.lean`](../HodgeConjecture/Cycles/FiniteChowPushforward.lean)
and [`RationalFiniteChowPushforward.lean`](../HodgeConjecture/Cycles/RationalFiniteChowPushforward.lean)
construct the induced maps on the existing integral and rational Chow
quotients for finite maps of Noetherian schemes locally of finite type over
a field. Each image relation uses the actual support-to-image norm;
grading and relation preservation are proved. The integral map agrees
with the existing closed-immersion map, and rationalization commutes.
SP113 proves composition of these same finite pushforwards on raw and
homogeneous cycles and on integral and rational Chow groups, with identity
laws on the existing quotients. The actual residue-field tower supplies
the product of the two field-degree weights; no new compatibility premise
is added to the Chow maps. See
[`FinitePushforwardComposition.lean`](../HodgeConjecture/Cycles/FinitePushforwardComposition.lean)
and [`FiniteChowPushforwardComposition.lean`](../HodgeConjecture/Cycles/FiniteChowPushforwardComposition.lean).
The next obligations are flat pullback and its degree law, and the
same-cover Chow--Betti comparisons, followed by
class-dependent generation for the intended `X,p`. Generic and arbitrary
geometric fibers remain distinct steps.
Pruning follows checked dependencies and mathematical roles; objects are
queued before any move to the bench. See [the live plan](../research/TARGET_BRIDGE.md#0-operative-plan-chow-to-betti-first).

For a smooth projective \(d\)-fold, the correspondence language is

\[
\operatorname{Corr}_{\mathrm{alg}}(X)
  = \mathrm{CH}^d(X\times X)_{\mathbf Q}
\longrightarrow
\operatorname{End}_{\mathrm{HS}}\!\bigl(H^\ast(X,\mathbf Q)\bigr).
\]

A cohomological Hodge summand has an idempotent projector.  The desired
lifting theorem asks when that idempotent is induced by an algebraic
correspondence, and a decomposition of the diagonal asks for a finite family
of orthogonal algebraic idempotents summing to \([\Delta_X]\).

This projector language is related to, but not automatically identical with,
the usual Hodge-conjecture cokernel

\[
\operatorname{Hdg}^p(X)/
  \operatorname{im}\bigl(\mathrm{cl}^p\bigr).
\]

`Realization/Chow/TateGraphProjector.lean` makes the exact reduction explicit.
A Hodge class \(\alpha\) determines the canonical graph projector

\[
e_\alpha=
\begin{pmatrix}1&0\\ \alpha&0\end{pmatrix}
\quad\text{on}\quad
\mathbf Q(-p)\oplus H^{2p}(X,\mathbf Q).
\]

Its lower-left block recovers \(\alpha\).  Under explicit Chow-level graph
construction and lower-left-block detection maps, Lean proves—pointwise and
in every codimension—that the rational Hodge conjecture is equivalent to
algebraic liftability of every such canonical projector.  The two directions
use separate interfaces, and neither interface assumes Hodge surjectivity.
An additional interface records the still-geometric equivalence between
“\(\alpha\) has type \((p,p)\)” and “\(e_\alpha\) is a morphism of Hodge
structures”; the rational-module layer does not silently assume it.

The cover-intended deck-action endpoint follows that separation literally.  A
`RationalCohomologicalProjector` is supplied independently, and a
`PrescribedChowProjectorLift` must prove that the compactified correspondence
acts as that exact operator.  The target is never defined to be the action of
the correspondence being constructed.  Connecting this family to a concrete
Hodge target still requires a Tate-block Chow model and a coverage theorem
showing that every Hodge class's canonical graph projector occurs in the
finite-cover family.

The generic one-way connection is now formal: a prescribed deck-action/
extension lift of a canonical graph projector, together with lower-left
Chow-block detection, produces an algebraic representative of that class;
supplying such lifts for every rational Hodge class proves
`RationalHodgeConjectureAt`. No concrete class-dependent deck-action or
cover-extension instance of those hypotheses is asserted; the finite
degree-zero Chow block construction and detection are instantiated below.

The cover-intended deck-action hypothesis now has an explicitly class-indexed
form: each Hodge class may choose its own extension package over fixed deck
data and a fixed finite subgroup.  At this abstract layer `pX` is not itself
assumed finite or étale, and the condition remains only sufficient.

The marked Galois-sheet calculation now explains the relevant block form.
Write \(A_H=\mathbf Q^{G/H}\) and let \(q\) be its base-sheet selector.  The
residual object is not merely a vector-space kernel: it is the augmentation
ideal
\[
E_H=\ker(\operatorname{ev}_H)=(1-q)\triangleleft A_H.
\]
Giving its underlying ideal the internal unit \(1-q\) produces the residual
corner \(E_H^{\mathrm{corner}}\), and Lean proves the genuine algebra
equivalence
\[
  A_H\simeq_{\mathbf Q\text{-alg}}\mathbf Q\times E_H^{\mathrm{corner}}.
\]
It sends \(q\) to \((1,0)\) and \(1-q\) to \((0,1)\); multiplication by
\(q\) is therefore \(\operatorname{diag}(1,0)\) in these multiplicative
selector/CRT coordinates.
The regular source action
\(A_H\to\operatorname{End}_{\mathbf Q}(A_H)\) is a
multiplicative algebra map.  For the active comparison, however, the common
multiplicative source is only the universal one-idempotent algebra
\(U=\mathbf Q\times\mathbf Q\).  Every chosen idempotent determines an honest
algebra map from \(U\), so the generic restriction, compactified projector,
and cohomological action are compared by equalities of algebra-homomorphism
composites without postulating a map between the larger sheet and convolution
algebras. A map from the entire commutative sheet algebra into a generic
correspondence algebra is an optional stronger interface in the general
schema. The finite split model separately constructs such an embedding by
actual diagonal Chow classes and an invertible Chow shear.
In the separate
constant-unit linear splitting
\(A_H\simeq_{\mathbf Q}\mathbf Q\oplus E_H\), multiplication by \(q\) is the
graph projector of the residual class \(q-1\).  Lean proves the ideal
identification, both block formulas, and their shear transition.  A residual
realization \(\theta:E_H\to V\) is only rational linear. The archived
`SheetLinearization.lean` experiment defines an auxiliary linear
coset construction, but is outside the library and supplies no
map of algebras from \(A_H\) to \(\mathbf Q[G]\).

These coordinate identities are supporting calculations. A graph projector
exists for every vector, whether or not that vector is algebraic. Neither
its linear idempotence nor the multiplicative source decomposition constructs
a Chow representative of a separately prescribed Hodge class.

The next conditional arrow is also formalized.  An
`AlgebraProjectorExtension` keeps the generic algebra separate from a
possibly noncommutative compactified correspondence algebra.  It canonically
produces maps \(U\to\Gamma_\eta\) and \(U\to\overline\Gamma\), and Lean proves
that restriction composed with the compactified map equals the generic map.
The canonical `MarkedProjectorActionComparison` needs only the chosen
projector and the residual action square, not an ambient restriction map.
The extension-based comparison remains its stronger specialization.
The realization comparison is an honest morphism between the corresponding
\(U\)-representations.  Under surjectivity, `palomarTargetSquare` states that
the cohomological action composed with the compactified map from \(U\) equals
the canonical map from \(U\) presenting the class-graph projector.  No
general geometric residual realization or comparison square is constructed.
This is essential: Lean proves that two class-graph projectors commute exactly
when their classes agree, so one fixed commutative action could not cover a
nonzero Hodge-class space.
Given a compactified idempotent restricting to the base-sheet selector, a
residual realization \(\theta\), and an explicit square intertwining its
correspondence action with generic selector multiplication, evaluation at the
marked unit identifies the lower-left class with \(\theta(q-1)\).  Lower-left
Chow-block detection therefore extracts an algebraic representative without
requiring \(\theta\) to be surjective.  If \(\theta\) is surjective,
cancellation gives the exact graph-projector action and an algebraic
projector lift.  Class-dependent coverage by such surjective witnesses
implies the modeled `RationalHodgeConjectureAt`; the reverse direction
additionally requires a separately named strong replacement hypothesis.

The first concrete check is now implemented in
[`Correspondence/Examples/SplitPoints.lean`](../HodgeConjecture/Correspondence/Examples/SplitPoints.lean)
and [`Realization/Chow/Examples/SplitPoints.lean`](../HodgeConjecture/Realization/Chow/Examples/SplitPoints.lean):
the actual finite-étale point span on `Spec(k^I)` is idempotent, and a separate
two-point matrix calculation proves `ρ(E₀₀)=P₋₁` and its Palomar square.
The [split-span cycle-coefficient realization](../HodgeConjecture/Realization/Chow/Examples/SplitSpanRealization.lean)
now connects these layers by a proved surjective algebra homomorphism on
actual split-presentable span classes. It respects geometric fiber products
and disjoint unions and takes empty spans to zero. The
[geometric-source endpoint](../HodgeConjecture/Realization/Chow/Examples/GeometricSplitPoints.lean)
therefore recovers the same projector action and Palomar square from the
original point span. The Chow-correspondence composition and its degree-zero
Betti comparison are constructed below. Extension from split-presentable
to arbitrary finite-étale carriers is a separate step. The
free source algebra is not itself identified with matrices. Its
[additive quotient](../HodgeConjecture/Realization/Chow/Examples/SplitSpanQuotient.lean)
is: the two-sided ideal generated by finite point-decomposition differences
is proved equal to the matrix realization kernel. Thus
`C_sp / J_sp ≃ₐ[ℚ] M_I(ℚ)`, using actual indexed scheme-coproduct
decompositions, a point-pair normal form, and matrix-unit independence.
The [actual integral-subscheme classification](../HodgeConjecture/Correspondence/Examples/SplitIntegralSubschemes.lean)
now identifies every integral closed subscheme of `Spec(k^I)` with a unique
reduced rational point, by an isomorphism commuting with its closed
immersion. Closed subschemes have dimension at most zero, so there are no
integral closed curves. The [zero-cycle construction](../HodgeConjecture/Realization/Chow/Examples/SplitZeroCycles.lean)
forms the cycle module on these actual integral subschemes. The
[rational-equivalence quotient](../HodgeConjecture/Realization/Chow/Examples/SplitRationalEquivalence.lean)
uses integral curves and units in their actual scheme function fields as
principal-divisor data. That indexing type is empty, so its generated
relation submodule is zero. Thus `CH_0(Z_I;R) ≃ₗ[R] (I → R)` for
`R = ℤ` and `R = ℚ`, taking fundamental point cycles to unit vectors.
The canonical scalar-extension comparison
`ℚ ⊗[ℤ] CH_0(Z_I;ℤ) ≃ₗ[ℚ] CH_0(Z_I;ℚ)` is also proved, including its
formula on point generators.
The [actual product and point-fiber comparison](../HodgeConjecture/Correspondence/Examples/SplitProductGeometry.lean)
identifies the product points and inverse-image subschemes. Image point
maps have residue-field degree one, and the actual fiber inclusions have
ambient-stalk multiplicity one. These calculations give the
[cycle and Chow operations](../HodgeConjecture/Realization/Chow/Examples/SplitCycleOperations.lean):
proper pushforward sums over fibers, flat pullback copies point coefficients,
and intersection is diagonal pullback of the external product. The
[Chow correspondence composition](../HodgeConjecture/Realization/Chow/Examples/SplitChowComposition.lean)
is defined by `p13_* (p12^* a · p23^* b)` on the actual Chow groups and
proved to be matrix multiplication in point-pair coordinates. The diagonal
is its identity, and composition is associative. The
[Chow endomorphism algebra](../HodgeConjecture/Realization/Chow/Examples/SplitChowAlgebra.lean)
retains that geometric composition and diagonal unit. It is proved
algebra-isomorphic to both the additive split-span quotient and `M_I(ℚ)`,
with the point-span class mapping to the actual Chow point-pair class.
For every finite split span, this equivalence maps its quotient class to
the proper pushforward of its carrier's fundamental cycle along the pair map.
The [geometric Chow action](../HodgeConjecture/Realization/Chow/Examples/SplitChowAction.lean)
`p2_* (c · p1^* z)` is proved to be matrix action on point coordinates.
Over `ℂ`, the actual point space is `Hom_ℂ-alg(ℂ^I, ℂ)`, with topology
induced by regular-function evaluation in the ordinary complex topology.
Classification by evaluation points proves this space finite and discrete,
and its maps agree with the actual scheme morphisms. Singular degree-zero
cohomology is constructed as the kernel of the face coboundary on actual
continuous simplices. Its cycle-class isomorphism
`CH_0(Z_I;ℚ) ≃ₗ[ℚ] H_B^0(Z_I(ℂ);ℚ)` sends each actual point cycle to
its characteristic cocycle. It respects proper pushforward/finite transfer,
flat pullback, and intersection/cup product. The cohomological action
`p2_* (cl(c) ∪ p1^* u)` is proved to intertwine the geometric Chow action.
It gives a rational algebra homomorphism from the actual Chow endomorphism
algebra to endomorphisms of singular degree-zero cohomology, instantiating
the existing `RationalCorrespondenceAction` interface.
The [independent finite Hodge structure](../HodgeConjecture/Realization/Betti/Examples/SplitHodgeStructure.lean)
uses the actual complexification `ℂ ⊗[ℚ] H_B^0`, computed as complex
point functions, with canonical tensor conjugation and the effective
type-`(0,0)` bigrading. Rational Hodge classes are the inverse image of
its complex `(0,0)` piece, and are then proved to be the whole rational
space, without using the cycle-class map.
On the actual disjoint union `Spec ℂ ⨿ Z_I`, the
[Chow Tate block](../HodgeConjecture/Realization/Chow/Examples/SplitTateBlock.lean)
constructs `enc(z) = [(*,*)] + j_*z`, with `j(i)=(*,i)`, and decodes by
the actual flat pullback `j^*`. Encoding is idempotent and decoding it
recovers `z`. The
[Betti block comparison](../HodgeConjecture/Realization/Betti/Examples/SplitTateBlock.lean)
proves that its action is `P_cl(z)` and that decoding any correspondence
has the cycle class of its lower-left action block. This instantiates the
finite degree-zero Hodge model, graph construction, detection, Hodge-morphism
compatibility, and the graph/Palomar target equivalences.
The [split marked-sheet geometry](../HodgeConjecture/Correspondence/Examples/SplitGaloisSheets.lean)
constructs the actual regular split `G`-torsor and the finite étale
homogeneous intermediate cover on `S=G/D`, for any subgroup `D`.
On `I=S∖{D}`, the
[residual Chow map](../HodgeConjecture/Realization/Chow/Examples/SplitGaloisResidual.lean)
sends `x∈ker(ev_D)` to the sum of actual point classes `∑ x(i)[i]`.
It is bijective and carries multiplication to geometric intersection;
in particular, `q−1` maps to `−[Z_I]`. Composing with the constructed
cycle class gives the residual Betti realization.
The [actual Chow shear](../HodgeConjecture/Realization/Chow/Examples/SplitChowShear.lean)
`U_z=1+j_*z` is invertible with inverse `U_(-z)` and conjugates the
marked point projector to `enc(z)`. Thus the marked-coordinate change is
implemented by a Chow correspondence inside the existing Tate block.
The actual diagonal-then-shear algebra embedding intertwines full sheet
multiplication with the constructed Betti action.
For the canonical generated class `−cl[Z_I]`, this gives the actual
selector-action comparison and Palomar square. It requires no algebra
restriction from the full Chow algebra to the commutative sheet algebra.
The test also proves
that `M₂(ℚ)` has no unital map to a nontrivial commutative ring; consequently
the old full-algebra restriction to sheets is not an admissible general
requirement. The existing Galois coverage interface retains it as an extra
specialized condition. See the
[split-span working note](../research/working/0008-split-span-cycle-realization.md)
and its [exact additive quotient](../research/working/0009-split-span-additive-quotient.md),
followed by the [integral-subscheme checkpoint](../research/working/0010-split-integral-subschemes.md)
and the [zero-cycle and rational-equivalence construction](../research/working/0011-split-zero-cycles.md),
then [geometric Chow composition](../research/working/0012-split-chow-composition.md)
and [actual degree-zero Betti cycle classes](../research/working/0013-split-betti-cycle-class.md),
then the [finite Hodge/Tate-block comparison](../research/working/0014-split-hodge-tate-block.md)
and [split marked-sheet residual/action comparison](../research/working/0015-split-galois-marked-comparison.md).

## Explicit literature inputs

The [input modules](../HodgeConjecture/Inputs.lean) separate selected standard
conclusions from their applications. The canonical fixed-inertia
unramifiedness record now lives in `Inputs/FixedInertia.lean`, unchanged;
existing descent theorems still take it explicitly. Actual finite étale
extension data, selected existence, and bijectivity of the actual deck
restriction map are separate inputs. Conditional deck-action lifting uses
only the corresponding premise.

Rational-linear Chow localization is also an explicit selected hypothesis.
It gives raw lifts and differences in the boundary image. With a separately
supplied algebra restriction, every raw convolution defect has a boundary
preimage; its vanishing is not a consequence of exactness. These packages
do not formalize the complete cited Stacks theorems or establish their
geometric hypotheses in the intended compactification. No global literature
instance is added. The two existing Mathlib-only Palomar statements and
their explicit premises remain unchanged. See the
[input checkpoint](../research/working/0016-source-input-packages.md) and
[submission handoff](../research/working/PALOMAR_FIXED_RING_HANDOFF.md).

Beyond the canonical split example, the primary geometric task is to
construct cycles and prove that their Betti classes generate the intended
Hodge subspace. In the optional marked route, construct a geometric
Chow-valued residual map whose cycle-class composite carries \(q-1\) to the
prescribed class. A chosen-projector conclusion additionally requires an
idempotent Chow correspondence with the prescribed action; an extension-based
implementation also retains its extension package and compatibility square.
A compatible Chow-motivic construction is one stronger possible route.
An arbitrary rational linear map is
insufficient, and a map built from an already known Chow representative would
be circular.  Surjectivity is also a strong sufficient hypothesis: it is what
upgrades equality on the realized sheet module to equality on the whole
Tate-augmented target.  In the formal coverage package the ambient
correspondence algebra and action remain fixed, while the group, marked
subgroup, compactified extension, and residual comparison may vary with the
class.  It does not yet bundle an actual finite cover or normal closure.
Conversely, the Hodge conjecture only supplies an arbitrary Chow lift and
does not force it to be replaceable by such a selected finite-Galois witness.
The new finite cover is a split torsor, disconnected when `G` is nontrivial;
it supplies no field normal-closure datum. Moreover, a multiplicative residual map satisfies
`θ(q−1)^2=−θ(q−1)`; if it is surjective onto a rational algebra, its
generated class is necessarily `−1`. Arbitrary class coverage therefore
cannot follow merely by varying these surjective multiplicative maps.
The general linear residual interface and any nontrivial boundary
extension still require their own geometric constructions.

`GraphProjectorLiftFactorizationThroughFixedDeckData` names that missing
factorization for a supplied target predicate, here the rational Hodge
classes.  If it is explicitly assumed together with Tate-block graph
construction and detection, Lean proves a conditional equivalence between
the modeled Hodge target and class-indexed prescribed coverage.  This does
not prove the factorization; it makes the exact additional generation claim
auditable and allows a smaller named subspace to be substituted.

Finite covers give an abstract, noncircular branch:

\[
\text{Galois sheets}
\longrightarrow
\text{group/Hecke correspondence algebra}
\longrightarrow
\text{formal correspondence projectors}
\longrightarrow
\text{chosen rational-module summands}.
\]

After a concrete Chow/Hodge realization is separately supplied, this branch
can produce finite-monodromy or cover-generated projectors. No such
general Chow/Hodge realization instance is constructed here, and it is not asserted
that every Hodge class arises from a finite Galois cover.  The formal
group/Hecke step transports supplied idempotents; it neither asserts that
every normalized double-coset operator is idempotent nor infers algebraicity
of an arbitrary Hodge projector.

## Boundary inertia

On the generic locus, a sheet selector is a characteristic-function
idempotent.  At a boundary valuation, inertia acts on the generic sheets.
The formal orbit criterion is

\[
\text{the generic selector is inertia-invariant}
\iff
\text{the selected sheets form a union of inertia orbits}.
\]

Together with normalization and purity inputs, this is the proposed
mechanism controlling extension of the clopen decomposition across the
boundary.  It controls whether the **scheme component** extends; a separate
convolution calculation is still required to obtain a correspondence
projector.

`NormalClosureData` already packages the normal-closure witness and the
finiteness of both `L/K` and `N/K`; downstream normality and finite-group
instances are therefore derived from this datum rather than imposed as new
mathematical hypotheses. Separability of `L/K` gives `IsGalois K N`
through `NormalClosureData.isGalois_of_isSeparable`; the old `isGalois`
name is retained as a perfect-base-field compatibility specialization.
The resulting `galoisGroup`,
`intermediateFixingSubgroup`, and canonical normalization deck action feed
the marked-sheet layer directly.  Normality is used to keep all conjugate
embeddings inside the same field `N`, hence under one Galois group; it does
not make that group abelian.  The deck automorphisms commute with the map to
the affine base because they fix `K` and therefore the `B`-scalars through
the scalar tower, not because the group commutes.  The pointwise sheet
algebra is separately commutative, while the group algebra and the full Chow
correspondence algebra may be noncommutative.  For this marked normal closure, the
intermediate normalization is identified formally with the subgroup-fixed
normalization ring when `L/K` is separable. Using
chosen quotient representatives, the collision tensor algebra also has an
evaluation map to functions on `G/H`, and its separability element is proved
to map to the marked singleton-sheet selector.  The multiplicative diagram is
also explicit: base-sheet augmentation composed with
`normalClosureTensorToGenericSheets` equals the tensor-diagonal algebra map
`normalClosureTensorDiagonal`. For separable `L/K`,
the normal-closure base change `N ⊗[K] L` is further proved equivalent to the
full sheet-function algebra.  At a boundary prime, the Stacks fixed-inertia
unramified theorem remains one explicit source input.  Lean now constructs
the exact prime-inertia subgroup used by that theorem.  The
commutative-algebra localization bridge proves that, over a Noetherian affine
base, the diagram's centered valuation ring is the localization of the
finite normalization at its height-one center.  Consequently valuation
inertia and prime inertia agree, and Lean derives the formerly missing
implication from valuation-inertia containment to the prime-inertia
containment required for fixed-ring descent.  Without the Noetherian
hypothesis, the reverse comparison remains available as the explicit
`PrimeInertiaComparisonAt` interface.  This is a selected-branch statement,
not an assertion that inertia fixes the whole `G/H` cover.  The subsequent
fixed-ring descent is now local as well: it constructs
`(S^H)_{q_H} → (S^I)_{q_I}` and assumes Dedekind only for the selected
localization `(S^H)_{q_H}`, rather than for the whole higher-dimensional
fixed ring.  For a finite group at height one, Lean further proves the
contraction remains height one and derives this local ring to be a DVR in the
finite normal-closure normalization over a Noetherian base.
`PrimeInertiaDescent.lean` composes these arrows with the valuation/prime
inertia comparison.  Its conclusion is deliberately based over the literal
full invariant ring `S^G`, exactly as in Tag `0BST`; it does not silently
identify `S^G` with an arbitrary affine base `B`.  The Tag `0BST`
fixed-inertia unramifiedness remains an explicit premise in the current Lean
endpoint; mathematically, Tag `0BST` supplies it.

### Canonical manuscript

[*Galois Correspondences and the Hodge Conjecture*](../paper/main.pdf) is the canonical
author-review candidate.  Its section order follows the dependency-ordered
components reflected by the active Lean modules: target equivalence,
collision and finite-etale convolution, group and
Hecke projectors, the marked-sheet block form, the codimension-one boundary
endpoint, the compactification fork, and the exact conditional realization
gap.  Fixed-ring localization and source inputs are supporting appendices.
The abstract states the conjecture and the proposed route directly; the
[Chow--Betti-first plan](../research/TARGET_BRIDGE.md#0-operative-plan-chow-to-betti-first)
organizes the next geometric work around which varieties and codimensions
the construction covers, and records its acceptance criteria.
Its [candidate comparison](../research/TARGET_BRIDGE.md#g0-smooth-projective-setting-and-candidate-constructions)
keeps smooth projective varieties as the main setting and abelian-covered
targets as an optional worked subclass. Projective bundles over curves or
surfaces and their polynomial-chart checkpoint remain optional deferred
examples; their detailed generation and Galois-closure analysis is preserved
in the plan. The immediate checkpoint returns to the
[boundary-section ideal route](../research/TARGET_BRIDGE.md#b0-boundary-section-algebra-and-uniform-trace-landing).
The self-contained
[`BoundedOverring.lean`](../HodgeConjecture/Boundary/Normalization/BoundedOverring.lean)
proves the generic normal-Noetherian bounded-overring implication and its
formulation using the existing `Submodule.colon`; the full build and six
focused regressions pass, and all three theorems use only the permitted
standard axioms. The section-algebra checkpoint constructs actual sections as a
subalgebra of the specified fraction field in
[`AffineSections.lean`](../HodgeConjecture/Boundary/Normalization/AffineSections.lean)
and specializes it to the existing fixed--moving boundary complement in
[`BoundarySections.lean`](../HodgeConjecture/Boundary/Normalization/BoundarySections.lean).
The generic-germ algebra map is injective, respects constants and
restriction, and identifies the actual section ring with its image. A
nontrivial normalization subgroup supplies nonemptiness of that complement;
normality and Noetherianity are not assumptions of the section embedding.
SP65 passes the full build, sixteen focused regressions in
[`BoundarySectionsVerification.lean`](../research/BoundarySectionsVerification.lean),
and an enforced standard-axiom allowlist for all twenty-one new declarations.
The trace-dual checkpoint in
[`TraceDualBound.lean`](../HodgeConjecture/Boundary/Normalization/TraceDualBound.lean)
and
[`NormalizationTraceBound.lean`](../HodgeConjecture/Boundary/Normalization/NormalizationTraceBound.lean)
reuses
`Submodule.traceDual B K (1 : Submodule T N)` for
`T^vee_B = {z in N : Tr_{N/K}(zT) subset B}`. An integral generic basis and
its trace-dual basis give one nonzero denominator for the entire submodule,
without Noetherianity, normality of `B` or a free normalization hypothesis.
For the existing normal closure of a separable `L/K`,
`normalizationTraceDual C` is this same object. Under the additional
Noetherian-base hypothesis, a nonzero member of the existing colon
`(T^vee_B:R_I)` forces `R_I=T`; a proper `R_I` instead has zero colon.
SP66 passes the full build, fourteen focused regressions in
[`NormalizationTraceBoundVerification.lean`](../research/NormalizationTraceBoundVerification.lean),
and enforced standard-axiom checks for all eleven new declarations.
The unchanged dependency audit and updated single-manuscript PDF checks pass.
The boundary-pole checkpoint constructs the geometric pole and separation comparison in
[`SectionLocalization.lean`](../HodgeConjecture/Boundary/Normalization/SectionLocalization.lean),
[`HeightOneBoundaryPole.lean`](../HodgeConjecture/Boundary/Normalization/HeightOneBoundaryPole.lean)
and
[`BoundaryPole.lean`](../HodgeConjecture/Boundary/Normalization/BoundaryPole.lean).
For a nonzero ideal `J` of a Noetherian domain and a height-one prime
containing it, a fraction `t/f` is constructed as an actual section on
every nonempty open `V` contained in `D(J)`, but lies outside the base
ring. The fixed--moving specialization therefore gives `R_I != T` at
such a prime. With separable `L/K`, every nonzero proposed trace multiplier
then fails on some actual boundary section, and the existing trace-dual
colon is zero. Conversely, a nonzero uniform landing multiplier for each
nontrivial subgroup implies `ConjugateBoundarySeparation`.
SP67 passes the full build, twelve focused regressions in
[`BoundaryPoleVerification.lean`](../research/BoundaryPoleVerification.lean),
and enforced standard-axiom checks for all nine new declarations. The fresh
dependency audit, appended umbrella-export checks and updated 69-page
single-manuscript PDF checks pass.
The regular-pair checkpoint adds a direct sufficient condition in
[`RegularPairBoundary.lean`](../HodgeConjecture/Boundary/Normalization/RegularPairBoundary.lean).
In a Noetherian domain, if `f,g` belong to `J`, `f != 0`, and multiplication
by `g` is injective on `T/(f)`, no height-one prime contains `J`. The
height-one denominator theorem now permits any prescribed `f != 0`,
without requiring `f in J`; its previous
existential statement is retained as a wrapper. For the normalization,
choose nonzero `f_I` in the existing fixed-locus ideal and `g_I` in the existing
moving-boundary ideal, with this quotient-injectivity property. Such pairs
for every nontrivial `I` imply `ConjugateBoundarySeparation`, without
perfectness or trace data. The unit-ideal case is allowed; no full regular
sequence with nonzero final quotient is asserted. SP68 passes the full
build, ten focused regressions in
[`RegularPairBoundaryVerification.lean`](../research/RegularPairBoundaryVerification.lean)
and enforced standard-axiom checks for all three new declarations. The
previous twelve boundary-pole regressions and their nine-declaration
allowlist were freshly rerun after the denominator refactor and pass.
The appended umbrella-export checks, fresh unchanged dependency audit,
independent Lean--TeX review and 70-page single-manuscript checks pass.

The SP69 geometry audit is recorded in
[the geometric-pair input audit](../research/working/0018-geometric-pair-input-audit.md).
At that checkpoint no instantiated `NormalizedCover` was found in the active library; its
finite models and marked open are supplied data. Those hypotheses do not
force regular pairs: the characteristic-zero cover `x=t^2` with marked
open `D(t)` has an etale visible map but
`J_fix=J_mov=J_fm=(t)`. This is an audited mathematical example, not a Lean
instance of the normalization package.

The research-only [algebra controls](../research/RegularPairGeometryControls.lean)
test the choice of first element: for `A=(x), M=(y)` in `Q[y][x]`, the
pair `x,y` works, while choosing `f=xy` prevents every `g in M` from
acting injectively modulo `f`. All eight diagnostic theorems and their
enforced standard-axiom checks pass; the full library build also passes.
These diagnostics do not identify `A,M` with an actual cover's
fixed/moving ideals.

No production declaration or manuscript/PDF changes belong to SP69;
Hodge-class generation remains a separate obligation.

The user selected the finite etale/full-visible branch for SP70. The
bounded construction identifies supplied finite normal affine algebras
with their existing normalization rings, transports their finite models,
and builds the existing `NormalizedCover` with the whole intermediate
model visible in
[`FiniteAffineCover.lean`](../HodgeConjecture/Boundary/Normalization/FiniteAffineCover.lean).
Etaleness, when supplied for the affine algebra, transports separately.
For a surjective visible open, every conjugate boundary
is empty. The core-free sheet action, without a separability assumption, makes
`J_mov(I)=J_fm(I)=top` for every nontrivial `I`, giving boundary separation
directly in
[`FullVisibleBoundary.lean`](../HodgeConjecture/Boundary/Normalization/FullVisibleBoundary.lean),
without regular-pair or uniform-landing hypotheses.
The full build, twenty focused regressions and enforced standard-axiom
audits of all seventeen new declarations pass, as does the fresh unchanged
dependency audit. The centralized inventory now has 798 checks, 565
examples and 690 reports; its historical prefix is unchanged and was not
rerun in full. This affine bridge does not
construct a global smooth-projective cover, its Galois closure, or the
required Chow--Betti classes. The main target is unchanged; the single
manuscript records the affine identification and full-visible separation
with the same explicit hypotheses. Its 71-page PDF build, warning scan,
visual checks and independent Lean--TeX review pass.

SP71 connects that affine bridge to an actual finite morphism
`p : Y -> X`. For affine `U` in `X`, take the existing section rings
`B_U=Gamma(X,U)` and `A_U=Gamma(Y,p^-1 U)`, using the whole inverse image.
Finiteness of `A_U` follows from `p`; if `p` is etale, its actual section
map is an etale algebra map. These results do not require integral `Y`
or normal stalks. For integral `Y` and nonempty inverse image, explicit
normality of the actual stalks gives normal `A_U`, whose fraction field
is the existing `Y.functionField`. The resulting canonical isomorphism
from the open subscheme to the normalization commutes with the original
map to `X`, not merely an abstract coordinate-ring identification.
See [`FiniteAffineChart.lean`](../HodgeConjecture/Boundary/Normalization/FiniteAffineChart.lean),
supported by
[`AffineEtaleAlgebra.lean`](../HodgeConjecture/Boundary/Normalization/AffineEtaleAlgebra.lean)
and [`AffineNormality.lean`](../HodgeConjecture/Boundary/Normalization/AffineNormality.lean).
The full build, eighteen focused regressions and eleven enforced
standard-axiom audits pass. The SP70 suite was freshly rerun and passes
its twenty regressions and seventeen audits, as does the unchanged
dependency audit. The centralized inventory now has 809 checks, 565
examples and 701 reports; its historical prefix is unchanged and was not
rerun in full. Normal stalks from the intended smooth geometry,
the actual Galois refinement and marked field data, chart gluing and
Chow--Betti generation remain separate geometric tasks. No new cover
package is introduced; the manuscript follows the same hypotheses.
The 72-page manuscript PDF passes its build, warning scan, visual checks
and independent Lean--TeX review.

SP72 supplies the canonical map `kappa_p:K(X) -> K(Y)` for an actual
dominant morphism of integral schemes in
[`FunctionFieldMap.lean`](../HodgeConjecture/Cycles/FunctionFieldMap.lean).
It is the generic-stalk map, is injective, commutes with section germs,
respects identity and composition, and agrees with the existing
open-immersion isomorphism. In
[`FiniteFunctionField.lean`](../HodgeConjecture/Boundary/Normalization/FiniteFunctionField.lean),
the same map gives compatible scalar towers on every nonempty open.
For a finite dominant morphism its field extension is finite-dimensional,
using the actual finite affine section algebra; the final theorem needs
no supplied chart, normality, etaleness or Noetherianity. The full build,
eighteen focused regressions and eleven enforced standard-axiom audits
pass. The SP71 suite was freshly rerun and passes its eighteen regressions
and eleven audits; the fresh unchanged dependency audit also passes.
The central inventory now has 820 checks, 565 examples and 712 reports;
its historical prefix is unchanged and was not rerun in full.
The updated 72-page PDF passes its build, warning scan, visual checks
and independent core/manuscript review.

SP73 proves separability for the same actual generic embedding in
[`SeparableFunctionField.lean`](../HodgeConjecture/Boundary/Normalization/SeparableFunctionField.lean).
A dominant affine formally unramified morphism of integral schemes gives
a formally unramified function-field algebra. If the morphism is finite,
SP72's finite-dimensionality then gives separability. Finite etale
morphisms qualify automatically; normality, perfectness and characteristic
zero are not assumed. The full build, sixteen focused regressions and
three enforced standard-axiom audits pass, as do the fresh SP72 rerun
(eighteen regressions and eleven audits) and unchanged dependency audit.
The central inventory now has 823 checks, 565 examples and 715 reports;
its historical prefix is unchanged and was not rerun in full.
SP73 alone did not discharge the downstream `PerfectField K` inputs;
SP75 below generalizes those consumers. It does not construct
a global Galois refinement. Normal stalks from smoothness, chart gluing
and Chow--Betti generation remain separate tasks.
The 73-page PDF passes its build, warning scan and visual checks.

SP74 constructs the existing marked `NormalClosureData` from a finite
field extension in
[`NormalClosureConstruction.lean`](../HodgeConjecture/Boundary/Normalization/NormalClosureConstruction.lean),
using `IntermediateField.normalClosure K L (AlgebraicClosure L)` and
preserving the canonical upstairs embedding. For any supplied marked
normal closure, separability of `L/K` gives separability and Galoisness
of the normal closure without a perfect-base-field assumption.
[`FunctionFieldNormalClosure.lean`](../HodgeConjecture/Boundary/Normalization/FunctionFieldNormalClosure.lean)
applies this to the actual finite generic extension, and scheme formal
unramifiedness supplies its Galois conclusion through SP73. The full
build, twenty-two focused regressions and seven enforced standard-axiom
audits pass, as do the fresh SP73 rerun (sixteen regressions and three
audits) and unchanged dependency audit. The central inventory now has
830 checks, 565 examples and 722 reports; its historical prefix is
unchanged and was not rerun in full. SP75 below connects this result to
the existing consumers. A scheme-level Galois refinement, gluing and Chow--Betti generation
are not constructed by this field-level bridge.
The updated 74-page PDF passes its build, warning scan, visual checks
and independent core/scheme/manuscript review.

SP75 aligns the existing consumer hypotheses with their proofs. Fourteen
fixed-field, invariant-ring, selector/tensor and trace/pole declarations
now assume only `Algebra.IsSeparable K L`. Core-freeness and eleven
full-visible/inertia/sheet/projector consumers need neither perfectness
nor separability. The two separability/Galois lemmas move into
[`NormalClosure.lean`](../HodgeConjecture/Boundary/Normalization/NormalClosure.lean)
under their existing names; `NormalClosureData.isGalois` is the sole
perfect-field compatibility wrapper. No production declarations, maps, packages or
projectors are added. The new consumer suite passes 24 regressions and
29 enforced standard-axiom audits; the updated trace and pole suites
pass 14/11 and 12/9 respectively. Fresh SP74 and finite-affine-cover
reruns pass 22/7 and 20/17. The central inventory has 859 checks,
565 examples and 751 reports after appending 29 checks and reports;
its historical prefix is unchanged and was not rerun in full. The
74-page PDF (785575 bytes) passes its build, warning scan and visual
checks; independent Lean--TeX review passes. The full build passes
(3179 jobs; only the two existing Challenge placeholder warnings).
The fresh unchanged dependency audit passes six endpoint contracts and
two support reports. SP76 below implements the next finite-normalization
bridge; the preceding validation figures describe SP75.

SP76 derives finiteness of the actual normal-closure normalization over
an explicitly normal Noetherian affine base in
[`FiniteNormalClosure.lean`](../HodgeConjecture/Boundary/Normalization/FiniteNormalClosure.lean).
The generic theorem uses Mathlib's `IsIntegralClosure.finite`, with no
dimension-one, Dedekind or perfectness premise. A single finite normal
intermediate algebra now constructs the existing `NormalizedCover`;
no independently supplied second algebra `S` is needed. For an actual
finite dominant formally unramified morphism `p:Y -> X` of integral
schemes, a nonempty normal Noetherian affine base chart and normal stalks
on its whole inverse image construct that cover directly. Its visible
scheme is the actual inverse-image open, its map is the existing
normalization isomorphism, and its marked field closure is constructed
from the actual generic extension. Full visibility gives boundary
separation. Finite etale morphisms satisfy the formal-unramifiedness
premise. No new carrier, cover package or source axiom is introduced.
The full build passes (3180 jobs; only the two existing Challenge
placeholder warnings). The new suite passes 23 examples and seven enforced
standard-three axiom audits. Fresh consumer, affine-chart and normal-closure
reruns pass 24/29, 18/11 and 22/7 respectively. The central inventory has
866 checks, 565 examples and 758 reports after appending seven checks and
reports; its historical prefix is unchanged and was not rerun in full.
The 74-page PDF (788608 bytes) passes its build, warning scan and visual
checks; independent code and Lean--TeX reviews pass. The fresh unchanged
dependency audit passes six endpoint contracts and two support reports.
SP77 constructs the finite tensor source and its actual evaluations in
[`FiniteTensorProduct.lean`](../HodgeConjecture/CommutativeAlgebra/FiniteTensorProduct.lean),
[`NormalClosureTensor.lean`](../HodgeConjecture/Boundary/Normalization/NormalClosureTensor.lean)
and [`NormalizationTensor.lean`](../HodgeConjecture/Boundary/Normalization/NormalizationTensor.lean).
For `Σ=Hom_K(L,N)`, the field tensor `P_K=⊗_{Σ,K} L` maps onto the
existing marked `N`: its algebraic range contains every conjugate field,
so normal-closure generation proves surjectivity. The actual kernel is
maximal and its quotient is canonically `N`. No separability or supplied
surjectivity premise is needed for that argument. Restrictions of those
same embeddings give `ev_B:P_B -> IntCl_B(N)`, with
`P_B=⊗_{Σ,B} IntCl_B(L)`. On pure tensors its inclusion into `N` agrees
with the field evaluation. An actual finite normal etale intermediate
model makes `P_B` finite and etale over `B`; no new tensor carrier or
normal-closure package is introduced. All 17 new APIs compile; the two
source-property theorems omit four unused base/target scalar assumptions.
The central inventory is 883 checks, 565 examples and 775 reports after
appending 17 checks and reports; its historical prefix is unchanged and
was not rerun in full. The 76-page PDF (805454 bytes) passes its build,
warning scan and visual checks; independent code and Lean--TeX review pass.
The full build passes (3187 jobs; only the two existing Challenge
placeholder warnings). The new suite passes 28 examples and 17 enforced
standard-three axiom audits without warnings. Fresh SP76 and SP74 reruns
pass 23/7 and 22/7, respectively: 73 examples and 31 audits in these three
suites. The fresh unchanged dependency audit passes six primary endpoint
contracts and two support reports.

SP78 constructs the canonical comparison `K⊗_B P_B ≃_K P_K` and proves
the full equality of evaluator homomorphisms in
[`NormalizationBaseChange.lean`](../HodgeConjecture/Boundary/Normalization/NormalizationBaseChange.lean).
Its one-factor comparison `K⊗_B IntCl_B(L) ≃_K L` uses the fraction-field
localization and algebraicity of `L/K`, with compatible scalar towers;
normality, Noetherianity, separability and finite degree are not required.
[`PiTensorBaseChange.lean`](../HodgeConjecture/CommutativeAlgebra/PiTensorBaseChange.lean)
supplies the generic finite-index tensor base-change equivalence and
factorwise algebra congruence. The three existing finite-family evaluation
helpers move unchanged to `FiniteTensorProduct.lean`; their names and maps
are preserved. The central inventory is 896 checks, 565 examples and
788 reports; its historical prefix is unchanged and was not rerun in full.
The 76-page PDF (812185 bytes) passes its build, warning scan and visual
checks. Both new leaves compile without warnings. The focused suite passes
25 examples and 13 enforced standard-three axiom audits, including three
actual function-field cases. The full build passes (3189 jobs; only the
two existing Challenge placeholder warnings). Fresh SP77, SP76 and SP74
reruns pass 28/17, 23/7 and 22/7, respectively: 98 examples and 44 enforced
axiom audits across the four suites. The fresh unchanged dependency audit
passes six primary endpoint contracts and two support reports.

SP79 selects the actual generic evaluation factor in
[`NormalClosureFactor.lean`](../HodgeConjecture/Boundary/Normalization/NormalClosureFactor.lean),
using the generic reduced-Artinian construction in
[`ReducedArtinianFactor.lean`](../HodgeConjecture/CommutativeAlgebra/ReducedArtinianFactor.lean).
Finiteness of `P_K` needs no separability; separability of `L/K` makes
`P_K` etale and hence reduced Artinian. Its decomposition
`Φ_m:P_K ≃_K N × Q_m` has first projection exactly `ev_K`, where `Q_m`
is the product of the residue quotients at the other maximal ideals.
The selected element `e_m=Φ_m⁻¹(1,0)` is idempotent, evaluates to one,
annihilates exactly `ker(ev_K)`, and satisfies `ker(ev_K)=(1-e_m)`.
Value one and annihilation of the kernel determine `e_m` uniquely.
This is an algebra factor selector, not a new Chow projector or a
unital algebra section `N -> P_K`. Both new leaves compile without
warnings; the full build passes 3195 jobs with only the two existing
Challenge warnings. The focused suite and four fresh neighbor suites
pass 123 examples and 60 enforced standard-three axiom audits in total.
The fresh unchanged dependency audit passes six primary endpoint
contracts and two support reports.
The 78-page PDF (819834 bytes) passes build, warning scan and visual
review; independent mathematical and Lean--TeX review passes. The
full validation record is in the SP79 parity-queue entry.

SP80 proves the actual integral factor in
[`NormalizationIntegralFactor.lean`](../HodgeConjecture/Boundary/Normalization/NormalizationIntegralFactor.lean).
Over normal `B`, the unramified separability tensor
and integral field trace construct a `B`-linear section `r_B` of the
existing `ev_B:P_B -> T`, where `T=IntCl_B(N)`. The source action law is
`r_B(ev_B(s)*t)=s*r_B(t)`. SP78's evaluator square and the proved generic
surjectivity supply the spanning condition used to prove `ev_B∘r_B=id`.
Thus `E_m=r_B(1)` is an integral idempotent, has value one, and satisfies
`ker(ev_B)=(1-E_m)`. The resulting quotient comparison
`P_B/(1-E_m) ≃_B T` preserves the actual evaluator. Localization away
from `E_m` supplies whole-ring etaleness, and the finite source supplies
finiteness of `T`. The generic comparison identifies
`β_Σ(1⊗E_m)=e_m` under separability.

This construction uses an actual finite normal etale intermediate model
with fraction field `L`; it assumes neither Noetherianity of `B` nor
normality or flatness of the whole tensor source. It bypasses the proposed
whole-source integral-closedness route without proving that stronger
statement. No integral-evaluation surjectivity, selector, selected image,
or second normalization model is supplied as an input. The generic
trace-section and trace-contraction proofs are in
[`UnramifiedIntegralFactor.lean`](../HodgeConjecture/CommutativeAlgebra/UnramifiedIntegralFactor.lean)
and [`SeparabilityTrace.lean`](../HodgeConjecture/CommutativeAlgebra/SeparabilityTrace.lean).
All 28 new APIs compile without warnings. The full build passes 3198
jobs with only the two unchanged Challenge warnings. The focused suite
and five fresh neighbor suites pass 153 examples and 88 enforced
standard-three axiom audits; the unchanged dependency audit passes six
primary contracts and two support reports. The central inventory is
940 checks, 565 examples and 832 reports; its historical prefix is
unchanged and was not rerun in full. The 79-page PDF (826296 bytes)
passes its build, warning scan and eight-page visual review. Independent
mathematical and Lean--TeX review pass. The SP80 parity-queue entry records
the full validation details.

The focused suite verifies the ring-level specialization to an actual
finite etale affine inverse image, deriving both section-ring normality
inputs from normal stalks without Noetherianity.

SP81 proves the named actual affine refinement in
[`FiniteEtaleNormalClosure.lean`](../HodgeConjecture/Boundary/Normalization/FiniteEtaleNormalClosure.lean).
For a finite dominant etale morphism `p:Y -> X`
of integral schemes and a nonempty affine chart `U`, it constructs the
existing `NormalizedCover` using the same function-field normal closure,
the actual inverse image `V=p⁻¹U`, and its existing normalization
isomorphism. Normal stalks on `U` and `V` remain explicit; no
Noetherian-base premise or replacement marking is added. The normalization
structural maps to `Spec Γ(X,U)` and to the actual `U` are finite etale.
Its actual refinement to `V` is finite etale, recovers the original marked
normalization leg, and composes with `p|_U` to exactly the structural map.
The composite over the original `X` is also proved, and full visibility
gives boundary separation for the constructed cover.
Both actual maps are surjective by lying over. Chart surjectivity needs
only dominance, integral schemes and the nonempty affine chart; refinement
surjectivity needs finiteness and normal stalks on `V`, with no etaleness
or base-normality premise.

Scheme etaleness is transported from the actual intermediate morphism:
[`EtaleTensorSource.lean`](../HodgeConjecture/Boundary/Normalization/EtaleTensorSource.lean)
preserves its local standard-smooth presentations through the finite
tensor source, and SP80's complementary idempotent makes `Spec(ev_B)` an
open immersion. This bypasses the missing general converse from
`Algebra.Etale` to scheme `IsEtale` in the pinned library. The two helper
APIs and all seventeen main declarations compile without warnings; the
scoped build passes 2761 jobs. The inventory is frozen at 19 APIs. The 81-page PDF
(831678 bytes) passes its final warning/reference/box scan and visual
review of pages 12, 13, 61, 72 and 78; independent geometry and
Lean--TeX review pass. The focused suite passes 25 examples and all
19 enforced standard-three axiom audits without warnings. Five fresh
neighbor suites also pass; the six suites total 146 examples and
89 enforced audits, with no warnings or errors. The full build passes
3200 jobs with only the two unchanged Challenge warnings. The unchanged
dependency audit passes six primary contracts and two support reports.
All nineteen API parity checks pass. The static central inventory is
959 checks, 565 examples and 851 reports; its historical prefix is
unchanged and the historical file was not re-elaborated. The SP81
parity-queue entry records the complete validation.

SP82 proves same-ambient localization and actual affine restriction in
`NormalizationLocalization.lean`, `AffineNormalizationRestriction.lean`
and `FiniteEtaleNormalClosureRestriction.lean`. The existing integral
closures localize along their same-element inclusion; the tensor
base-change equivalence preserves scalars and ambient elements. Generic
identity/composition and normalization-map naturality are strict
equalities. Principal localization gives an open immersion with the
exact inverse-image range. On actual nonempty affine subcharts, both
the structural map and the marked refinement commute with restriction,
using the original normal closure and visible normalization isomorphism.
Neither square needs etaleness; the refinement square retains finiteness
and explicit upstairs normal-stalk inputs, with no base-normality or
Noetherian hypothesis.

All 28 APIs compile cleanly in the 2764-job scoped build. The focused
suite passes 39 examples and 28 enforced standard-three axiom audits;
with three fresh neighbor suites, the total is 107 examples and 71
audits, without warnings or errors. The full build passes 3203 jobs
with only the two unchanged Challenge warnings. The unchanged dependency
audit passes six primary contracts and two support reports. All 28 API
parity checks and independent review pass. The 81-page PDF (835379 bytes)
has a clean final log and seven-page visual review. The static central
inventory is 987 checks, 565 examples and 879 reports; its historical
prefix is unchanged and was not re-elaborated in full. The SP82
parity-queue entry records the complete validation.

SP83 proves identity, composition and common-refinement coherence for the
actual restrictions. For any nested nonempty affine opens `W <= U`,
`AffineNormalizationOpenImmersion.lean` identifies `Z_W` with exactly
the open inverse image of `W` under the original `Z_U -> X`. Common
principal neighborhoods supply the comparison, without assuming
separatedness or affine intersections, and without finiteness, normality
or Noetherian hypotheses. The same ambient field and germ-derived scalar
maps are retained. The ten APIs compile in the 2740-job scoped build.
SP83 is validated: the focused suite passes 21 examples and ten exact
standard-three axiom audits. With the unchanged SP82 and SP81 suites,
the total is 85 examples and 57 audits, all clean. The full build passes
3205 jobs with only the two existing Challenge placeholder warnings;
the unchanged dependency audit passes six primary contracts and two
support reports. The 83-page PDF (839977 bytes), final log, seven-page
visual review and all ten API parity checks pass. The static central
inventory is 997 checks, 565 examples and 889 reports; its historical
prefix is unchanged and was not re-elaborated in full.

SP84 packages all actual nonempty affine opens as the inclusion-ordered
diagram `F_N` of the existing normalization charts. Its structural maps
form the original cocone `c_N` to `X`; every transition is an open
immersion with SP83's exact range. Common principal refinements prove
the locally directed condition required by Mathlib's scheme gluing.
`GluedNormalization.lean` then constructs the actual scheme
`Z_N = colimit F_N`, its open cover by the original charts `jmath_U`,
and the descended map `mu_N : Z_N -> X`. Its restriction to each chart
is exactly the original `mu_U`. Equality of chart points in `Z_N` is
equivalent to a common smaller-chart lift, and maps from `Z_N` are
determined by their chart restrictions. Integral `X` and the same fixed
field extension suffice; no normality, finite degree, Noetherianity or
separatedness assumption is introduced.

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

SP85 proves the exact global chart image
`range(jmath_U) = mu_N^-1(U)` in `GluedNormalizationChart.lean` and
constructs the actual open-subscheme isomorphism
`e_U : Z_U ~= mu_N^-1(U)`. It preserves the original chart inclusion,
identifies the restricted global map with the original normalization
map to `U`, and commutes with every actual affine chart restriction.
The proof uses the constructed open cover and common principal
refinements; no replacement chart, field marking, or extra geometric
hypothesis is introduced. Its seven public APIs have manuscript
counterpart `prop:normalization-global-chart`.

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

SP86 uses these actual inverse-image isomorphisms to transfer every
target-local morphism property from the original chart maps
`pi_U : Z_U -> U` to `mu_N`. The actual nonempty affine opens cover any
scheme, including the empty scheme. Thus the local-property proof
needs no exceptional empty-chart normalization. It proves global
`IsAffineHom` for integral `X` and any fixed field extension of its
original function field, and exact finite/etale equivalences with the
original chart maps.

For an actual dominant finite etale map `p : Y -> X` of integral schemes,
SP86 then applies SP81 to the same marked field
`N_p = normalClosure K(X) K(Y) (AlgebraicClosure K(Y))`. With explicit
normal-stalk hypotheses on both `X` and `Y`, the actual global map
`mu_(N_p)` is finite etale. There is no Noetherian or perfect-field
premise and no replacement normalization model. The six public APIs
are in `GluedNormalizationProperties.lean` and
`FiniteEtaleGluedNormalClosure.lean`; their manuscript counterparts are
`prop:normalization-target-local` and
`cor:normal-closure-global-finite-etale`.

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

SP87 descends the original marked affine refinements to an actual map
`lambda : Z_(N_p) -> Y` in `GluedNormalClosureRefinement.lean`.
The original chart maps form a cocone by the proved restriction
compatibility, and its colimit descent retains the exact chart formula
`jmath_U` followed by `lambda` equals `lambda_U` followed by the
inclusion of `p^-1(U)` into `Y`. It proves `lambda` followed by `p`
equals `mu_(N_p)` and uniqueness among maps with those same marked
chart formulas. The triangle over `X` alone is not its uniqueness
hypothesis.

These five public APIs need only integral `X` and `Y`, finite dominant
`p : Y -> X`, and explicitly integrally closed stalks of `Y`.
No etaleness, normal-stalk input on `X`, Noetherianity or perfectness
is assumed. The original normal-closure field, chart carriers and
germ-derived scalar maps are unchanged. The manuscript counterpart is
`prop:normal-closure-marked-refinement`.

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

SP88 proves finite etaleness of that same marked refinement
`lambda : Z_(N_p) -> Y` in `FiniteEtaleGluedRefinement.lean`. A generic
finite-morphism cancellation lemma proves that `f` is finite whenever
`f` followed by `g` is finite and `g` is separated; `g` need not itself
be finite. For the actual finite etale `p`, finiteness gives
separatedness, and SP87's exact triangle and SP86's finite-etale
`mu_(N_p)` give both finiteness and etaleness of `lambda`.

The actual specialization assumes integral `X` and `Y`, dominant
finite etale `p : Y -> X`, and explicitly integrally closed stalks on
both schemes. These are additional inputs for the property theorem;
the SP87 definition of `lambda` still needs only finite dominance and
normal stalks of `Y`. The proof does not re-glue or replace a chart,
carrier, field marking or scalar map. Its manuscript counterpart is
`cor:normal-closure-refinement-finite-etale`.

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

SP89 proves surjectivity of both original global maps in
`GluedNormalizationSurjectivity.lean`, with distinct minimal scopes.
For integral `X` and any field extension `N` of its original function
field, `mu_N : Z_N -> X` is surjective. The original chart algebra
maps into its integral closure injectively and integrally; lying over
gives chart surjectivity and the proved target-local comparison gives
the global result. No algebraicity or finite-degree assumption on `N`
is needed.

For finite dominant `p : Y -> X` with integral `X` and `Y` and
explicitly integrally closed stalks of `Y`, the same original marked
`lambda : Z_(N_p) -> Y` is surjective. This proof lifts a point of `Y`
through an actual affine inverse image and the already proved
surjective chart refinement, then uses SP87's exact chart formula.
It does not infer surjectivity of `lambda` from that of `p lambda`.
No etaleness or normal-stalk assumption on `X` is required for this
surjectivity theorem. Under SP86/SP88's stronger finite-etale and
normal-stalk hypotheses, both global maps are therefore finite etale
and surjective. The manuscript counterpart is
`prop:normalization-global-surjective`.

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

SP90 glues the original inverse-ring chart actions to the same global
normalization. For integral `X` and any field extension `N/K(X)`, the
original `Spec(sigma^-1)` maps commute with every actual chart
restriction. Their natural diagram automorphisms descend to global
automorphisms with the exact chart formula, compatibility over `X`,
identity and multiplication laws, and a homomorphism
`Aut_(K(X))(N) -> Deck(mu_N)` retaining those underlying maps.

For finite dominant `p : Y -> X` with integral `X` and `Y` and
explicitly integrally closed stalks of `Y` only, the subgroup fixing
the marked `K(Y)` preserves the original refinement `lambda`.
Inverse fixing, the original marked affine ring map and its existing
chart isomorphism prove the local compatibility; chart extensionality
then proves the global equality. This proof does not cancel `p` from
the structural triangle. The subgroup action packages into
`Deck(lambda)` with the same underlying global automorphisms.

These 15 APIs are in `GluedNormalizationAction.lean` and
`GluedNormalClosureAction.lean`; their manuscript counterparts are
`prop:normalization-global-action` and
`prop:normalization-marked-action`. The action theorems need no
etaleness, normal-stalk assumption on `X`, separability, Noetherianity
or perfectness, and change no carrier, field marking or scalar map.

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

SP91 proves normal local rings of the same glued normalization through
four APIs in `GluedNormalizationNormality.lean`. Integral closure of
any commutative ring `B` in a field `N` is integrally closed in its
own fraction field, which embeds into `N` without an asserted equality.
Prime localization gives the affine stalk result. The original chart
open immersions identify those local rings with all global stalks,
proving that each is a domain and integrally closed.

For `Z_N`, integral `X` and arbitrary `N/K(X)` suffice, without
algebraicity, finite degree, separability, normality of `X`, or
Noetherianity. The same conclusion for the actual marked `N_p` needs
no normal-stalk premise on `Y`. No chart, field marking, generic germ
or glued carrier changes. The manuscript counterpart is
`prop:normalization-global-normal`. Normality is expressed through
the actual local rings; global `IsIntegral` and the marked function-field
identification remain separate results to prove.

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

SP92 proves integrality of the same glued normalization through four
APIs in `GluedNormalizationIntegrality.lean`. Actual common affine
refinements witness pairwise chart intersections. The charts' irreducible
open images cover the scheme and give global irreducibility, including
nonemptiness. SP91's domain stalks give reducedness; together these
properties supply the global `IsIntegral` instance.

Integral `X` and arbitrary `N/K(X)` suffice, without algebraicity,
finite degree, separability, base normality, Noetherianity or
separatedness. The actual `N_p` specialization needs no normal-stalk
premise on either scheme. All original chart maps, germs, fields and
markings remain fixed. The manuscript counterpart is
`prop:normalization-global-integral`. The intrinsic function field is
now available, without an asserted equality with arbitrary ambient `N`.

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

SP93 adds 19 public APIs across four production modules. The comparison
in `GluedNormalizationFunctionField.lean` uses the actual generic-stalk
coordinate formulas in `Cycles/FunctionFieldComparison.lean`.
For integral `X` and finite `N/K(X)`, the comparison `K(Z_N) ≃ N`
is independent of the original nonempty affine chart and preserves
the actual structural field map. The existing action satisfies
`e(a_sigma^* b) = sigma^{-1}(e(b))`; this gives faithfulness of that
action, with the inverse dictated by its original ring convention.
The action comparison is in `GluedNormalizationFunctionFieldAction.lean`.

`GluedNormalClosureFunctionField.lean` retains the original marking:
for finite dominant `p : Y -> X`, integral `X/Y`, and normal stalks
of `Y`, it compares pullback through the actual `lambda` with
`(functionFieldNormalClosureData p).embedding`. No normality of `X`,
etaleness, separability or Noetherianity is added. The manuscript
counterparts are `prop:normalization-function-field-comparison` and
`cor:normalization-marked-function-field`. The ambient-field
identification here has a finite-extension hypothesis; SP91/SP92's
arbitrary-extension normality and integrality retain their broader scope.

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

Next address reconstruction of arbitrary deck transformations and full
deck-group comparison. Fiber comparison and a Galois-cover or torsor
identification remain separate: subgroup fixing is a sufficient condition for preserving
`lambda`, not a characterization of its entire stabilizer.
Normal stalks from smooth geometry
and Chow--Betti generation remain separate. No model built
from global sections of a non-affine intersection is substituted for
its geometric overlap. The earlier SP76 constructor retains its
stronger assumptions.

`paper/main.pdf` is the single current manuscript PDF. The earlier drafts
and their sources are preserved in the
[manuscript archive](../research/archive/manuscripts/README.md), outside the
current build and release checks. No manuscript has been placed in the publication
queue.  The canonical draft does not identify the free span algebra with Chow
correspondences, does not claim an unconditional boundary extension, and does
not prove a new Hodge case.  Licensing, literature/novelty review, and final
author review remain release blockers. Current proof roles and retained
dependencies are recorded in the
[proof-spine audit](../research/working/0017-proof-spine-and-archive.md).
The superseded section/module plan is preserved only in the planning archive.

### Palomar packaging status

`Challenge.lean`, `Solution.lean`, and `comparator.json` expose the two generic
height-one fixed-ring results through a small Mathlib-only statement surface.
This is a packaging draft, not a submitted or registered result.  The exact
remaining release work—including the Lean-toolchain migration, root licence,
human authorship/maintainer fields, and Comparator/NanoDa run—is recorded in
[`research/working/PALOMAR_FIXED_RING_HANDOFF.md`](../research/working/PALOMAR_FIXED_RING_HANDOFF.md).
Those advertised fixed-ring statements do not prove Tag `0BST` or global
étaleness, and are separate from the finite degree-zero Hodge model above.

## Module organization

- [`Collision`](../HodgeConjecture/Collision) contains the diagonal and
  collision ideals, the global self-fiber product
  \(R_f=X\times_YX\), the relative diagonal ideal sheaf, intrinsic and
  ambient sheaf-colon residuals, decomposition defects, component selectors,
  and the literal clopen scheme decomposition.
- [`Correspondence`](../HodgeConjecture/Correspondence) contains scheme
  correspondences \(X\leftarrow Z\to Y\) over a base, the diagonal identity,
  transpose, fiber-product composition, canonical unit and associativity
  isomorphisms, coproduct, isomorphism classes, and the free rational span
  algebra, with no commutativity assumption.  It also gives:
  - finite étale correspondences, their closure under identity, transpose,
    and fiber-product composition, and their convolution submonoid and free
    rational algebra;
  - transpose reversal on correspondence classes and anti-involutions of the
    unrestricted and finite étale free rational algebras, carrying
    \(\Gamma_g\) to \(\Gamma_{g^{-1}}\);
  - finite indexed coproducts of spans and an explicit finite-additivity
    compatibility property for cycle models;
  - a `FiniteEtaleAlgebraModel` whose source is the admissible finite-etale
    convolution algebra and whose additivity laws cover only finite
    coproducts remaining in that class;
  - deck actions and their algebra maps
    \(\mathbf Q[G]\to\operatorname{Corr}_{\mathrm{fe}}(X)\), transporting
    supplied group-algebra idempotents to algebraic-projector lifts and
    finite ordered-orthogonal families summing to \(1\) to
    diagonal-decomposition lifts; prescribed targets require explicit
    realization equalities;
  - finite-group averaging and complementary convolution idempotents,
    together with their algebraic-projector lifts, as a named special case;
  - for every finite subgroup \(H\leq G\), the rational Hecke corner
    \(e_H\mathbf Q[G]e_H\), normalized double-coset operators
    \(e_H[g]e_H\), and their map to the corresponding correspondence corner;
  - an explicit Galois/torsor collision datum
    \[
    \coprod_{g\in G}X\;\simeq\;X\times_YX
    \]
    compatible with both collision projections;
  - an explicit additive/convolution-compatible algebra-model interface;
  - the collision correspondence
    \(R_f\simeq 1_X\amalg R_f^{\mathrm{off}}\);
  - algebraic-projector and diagonal-decomposition lift structures.
- [`Boundary/Sheets`](../HodgeConjecture/Boundary/Sheets) contains generic
  \(G/H\)-sheets, relative inertia indices, characteristic-function
  selectors, the inertia-orbit criterion, and the marked selector/CRT versus
  graph-coordinate decomposition.
- [`LinearAlgebra/BlockGraphProjector.lean`](../HodgeConjecture/LinearAlgebra/BlockGraphProjector.lean)
  is the shared graph/diagonal/shear core used by both the marked-sheet and
  Tate-block realizations.
- [`LinearAlgebra/MarkedAugmentedAlgebraDecomposition.lean`](../HodgeConjecture/LinearAlgebra/MarkedAugmentedAlgebraDecomposition.lean)
  gives the augmentation ideal its internal corner unit and proves the genuine
  product-algebra decomposition, separately from the constant-unit linear
  shear coordinates.
- [`LinearAlgebra/UniversalIdempotentAlgebra.lean`](../HodgeConjecture/LinearAlgebra/UniversalIdempotentAlgebra.lean)
  gives the common algebra `ℚ × ℚ` for presenting one idempotent and its
  complement in any associative rational algebra; it is the active
  multiplicative source for the compactification and Palomar target squares.
- [`Boundary/AveragingAction.lean`](../HodgeConjecture/Boundary/AveragingAction.lean)
  relates the convolution idempotent averaging over a boundary inertia
  subgroup to its contragredient action on the pointwise generic-sheet
  algebra.
- [`Boundary/SheetProjectorExtension.lean`](../HodgeConjecture/Boundary/SheetProjectorExtension.lean)
  records actual global selector extensions, their generic restriction, and
  the explicit purity/gluing and selection-dependent ramification inputs.
- [`Boundary/GaloisProjectorExtension.lean`](../HodgeConjecture/Boundary/GaloisProjectorExtension.lean)
  connects finite subgroup graph averages to generic and compactified
  correspondence algebras through explicit extension packages.
- [`Boundary/Normalization`](../HodgeConjecture/Boundary/Normalization)
  contains marked normal closures, valuation inertia, affine normalization
  models, invariant-ring descriptions of intermediate normalizations, exact
  prime inertia and its Noetherian height-one localization comparison with
  centered valuation inertia, canonical conjugate normalization legs,
  fixed--moving boundary ideals and their conditional separation endpoint,
  the collision-to-sheet-selector comparison, visible-unramifiedness lemmas,
  and the normalization–inertia diagram.
  The marked normal-closure record itself supplies normality and finiteness;
  separability of `L/K` gives its derived Galois structure. Core-freeness,
  the fixing subgroup and canonical deck action do not need perfectness
  or separability. These same objects are reused by the downstream layers.
  The local fixed-inertia theorem and every global cover-extension or gluing
  input remain explicit assumptions.
- [`Boundary`](../HodgeConjecture/Boundary) contains the collision different,
  height-one comparison, and selector-extension criteria.
- [`Realization`](../HodgeConjecture/Realization) packages conditional
  correspondence, Chow-style, compactification, and cohomological
  consequences, together with the abstract Hodge target schemas.
  [`HodgeClasses.lean`](../HodgeConjecture/Realization/HodgeClasses.lean)
  separates fixed-codimension, one-model, and indexed-family quantifiers;
  [`HodgeTarget.lean`](../HodgeConjecture/Realization/HodgeTarget.lean) is the
  target umbrella.  The
  [`Realization/Chow`](../HodgeConjecture/Realization/Chow) sublayer is organized
  by mathematical role:
  - [`Model.lean`](../HodgeConjecture/Realization/Chow/Model.lean) records the
    generic and compactified rational correspondence algebras, with no
    commutativity assumption,
    their cycle-class/restriction maps, and cohomological action;
  - [`Presentation.lean`](../HodgeConjecture/Realization/Chow/Presentation.lean)
    constructs quotients of supplied, not-necessarily-commutative raw
    correspondence algebras by two-sided relation ideals and descends
    restriction and action;
  - [`GaloisProjector.lean`](../HodgeConjecture/Realization/Chow/GaloisProjector.lean)
    identifies the boundary-extended subgroup projector with a prescribed
    cohomological target;
  - [`TateGraphProjector.lean`](../HodgeConjecture/Realization/Chow/TateGraphProjector.lean)
    proves the abstract class/graph-projector equivalence through independent
    construction, detection, and Hodge-compatibility interfaces, together
    with the shear and rational `C₂`-reflection forms of the graph operator;
  - [`IdempotentRepresentation.lean`](../HodgeConjecture/Realization/Chow/IdempotentRepresentation.lean)
    packages linear intertwiners as morphisms of representations of the
    universal one-idempotent algebra `ℚ × ℚ`;
  - [`MarkedAugmentedRealization.lean`](../HodgeConjecture/Realization/Chow/MarkedAugmentedRealization.lean)
    carries the augmentation-ideal source model into the Tate block, packages
    the comparison as a morphism of representations of the universal
    one-idempotent algebra, and keeps the residual realization linear; its
    full sheet-algebra presentation is an optional stronger interface;
  - [`GaloisMarkedBlock.lean`](../HodgeConjecture/Realization/Chow/GaloisMarkedBlock.lean)
    identifies the marked sheet selector action with the canonical Tate graph
    operator and proves rational naturality under a residual realization map;
  - [`GaloisMarkedRealization.lean`](../HodgeConjecture/Realization/Chow/GaloisMarkedRealization.lean)
    separates the generic selector from the noncommutative compactified
    correspondence algebra, exposes `palomarTargetSquare` as an equality of
    algebra-homomorphism composites, detects the lower-left class from an
    explicit representation square, derives the exact graph action under
    surjectivity, and
    records class-dependent conditional coverage and replacement endpoints;
  - [`GaloisHodgeTarget.lean`](../HodgeConjecture/Realization/Chow/GaloisHodgeTarget.lean)
    records the one-way implication from class-indexed prescribed
    finite-cover lifts to the modeled Hodge target;
  - [`TransferProjector.lean`](../HodgeConjecture/Realization/Chow/TransferProjector.lean)
    proves the normalized pull--push projector identity from an explicit
    rational degree formula, while leaving construction of Chow pullback and
    pushforward to the geometric model.

  The historical commutative selector realization is preserved in the
  [Lean archive](../research/archive/legacy-lean/README.md), outside the library. The
  presentation layer does not claim that ordinary raw cycles already
  possess an everywhere-defined refined-convolution product, nor that its
  quotient is a Chow algebra without the required geometric identification.

The root library imports the active proof components. Six unused historical
or auxiliary modules, including the nonmultiplicative sheet linearization,
have been physically archived; their former import paths are retired.
The declaration-free `InertiaSaturation.lean` import shim and compatibility
declarations inside active modules remain. Their retention is not evidence
of an additional theorem or of a completed geometric bridge.

## Correspondence layer: what is formalized

For schemes over a fixed base \(S\), the project proves:

- a scheme correspondence is a span over \(S\), equivalently a carrier
  mapping to \(X\times_S Y\);
- correspondences compose using the fiber product over the middle scheme;
- the diagonal span is the identity;
- raw composition is unital and associative up to canonical scheme
  isomorphism;
- transpose reverses composition,
  \((Q\circ P)^{\mathsf t}\simeq
  P^{\mathsf t}\circ Q^{\mathsf t}\), and fixes the diagonal up to the
  canonical isomorphism;
- isomorphism classes of endocorrespondences form a monoid, with no
  commutativity assumption;
- the monoid algebra over \(\mathbf Q\) is a free rational span algebra;
- the older unrestricted `AdditiveClassMap`/`AlgebraModel` records formal
  laws on all spans and is retained only as an exploratory interface; it is
  not used for the normalized finite-etale collision theorem because
  arbitrary infinite coproducts make that domain too broad for ordinary
  ring-valued cycle theories;
- a `FiniteEtaleAlgebraModel` instead consists of an algebra realization of
  the finite-etale free algebra plus binary and finite-indexed coproduct
  additivity within that admissible class;
- the clopen collision decomposition yields
  \[
  [R_f]=1+[R_f^{\mathrm{off}}]
  \]
  under every additive class map;
- finite étale admissibility is invariant under span isomorphism and defines
  a convolution submonoid of strict correspondence classes;
- transpose preserves finite étale admissibility and extends linearly to
  convolution-reversing involutions on both free rational correspondence
  algebras;
- the collision and off-diagonal correspondences of a finite étale morphism
  belong to that admissible class;
- deck transformations define finite étale graph correspondences satisfying
  \(\Gamma_g\Gamma_h=\Gamma_{gh}\);
- graph transpose is inverse graph:
  \(\Gamma_g^{\mathsf t}=\Gamma_{g^{-1}}\) at the class and free-algebra
  levels;
- every supplied idempotent \(q\in\mathbf Q[G]\) transports through a finite
  deck action to a correspondence idempotent and an algebraic-projector
  lift; a lift of a separately prescribed operator requires its realization
  equality as an explicit input;
- a finite ordered-orthogonal family of group-algebra idempotents summing to
  \(1\) transports to an algebraic decomposition of the diagonal;
- for a finite deck action, the normalized graph sum
  \[
  e_G=\frac{1}{|G|}\sum_{g\in G}\Gamma_g
  \]
  and its complement are convolution idempotents;
- every finite subgroup \(H\leq G\) similarly gives the convolution
  idempotent
  \[
  e_H=\frac{1}{|H|}\sum_{h\in H}\Gamma_h,
  \]
  the structured class used by the boundary bridge;
- the subgroup Hecke algebra is constructed as the honest unital corner
  \(e_H\mathbf Q[G]e_H\), whose unit is \(e_H\); the normalized operator
  \(e_H[g]e_H\) depends only on \(HgH\) and maps to the expected
  projector--graph--projector sandwich in the correspondence corner;
- any supplied idempotent in that Hecke corner gives canonical and prescribed
  algebraic-projector lifts; no commutativity, double-coset basis, structure
  constants, or idempotence of every double-coset operator is asserted;
- for a finite etale morphism, an explicit Galois collision decomposition
  gives, in every supplied `FiniteEtaleAlgebraModel`,
  \[
  [R_f]=\sum_{g\in G}[\Gamma_g],
  \qquad
  \frac{1}{|G|}[R_f]=e_G;
  \]
- consequently the normalized full collision class is conditionally
  idempotent in the supplied realization and has a formal projector lift
  under every supplied correspondence action; no concrete nontrivial Chow
  realization for this general Galois interface is constructed here;
- the off-diagonal class is
  \(\sum_g[\Gamma_g]-1\), and is deliberately not asserted to be
  convolution-idempotent;
- any supplied rational correspondence action carries algebraic idempotents
  to cohomological idempotents;
- one algebraic projector lift canonically gives the two-term algebraic
  diagonal decomposition
  \(p+(1-p)=1\), with both ordered cross-products zero;
- a finite algebraic decomposition of the diagonal realizes to a finite
  cohomological decomposition into orthogonal projectors.

The free span algebra is deliberately **not** called a Chow algebra.  In
particular, it does not itself impose

\[
[P\amalg Q]=[P]+[Q],
\]

rational equivalence, refined-intersection relations, or pure-dimension
conditions.  Those enter only through the explicit realization interfaces.

## Collision and inertia content

The project also formalizes:

- the obstruction ideal sheaf
  \(\mathcal I_{\Delta/R_f}\), its annihilator residual, and the ambient
  sheaf-colon \(\mathcal I_{R_f}:\mathcal I_\Delta\);
- the affine identification
  \[
  \operatorname{Spec}A\times_{\operatorname{Spec}B}\operatorname{Spec}A
  \cong \operatorname{Spec}(A\otimes_BA),
  \]
  with relative diagonal induced by tensor multiplication;
- square-zero overlap and contact defects;
- the Chinese-remainder product decomposition when both defects vanish;
- the induced affine-scheme coproduct decomposition, whose first component
  is proved to be the actual relative diagonal;
- for every separated étale morphism—and therefore every finite étale
  morphism—the global collision scheme decomposes as the diagonal plus its
  open complement;
- split generic sheet selectors and their exact inertia-orbit criterion;
- the fixed-ring equivalence
  \(\operatorname{IntCl}_B(N^H)\simeq
  (\operatorname{IntCl}_B N)^H\), including its marked-intermediate-field
  specialization;
- chosen-representative maps from `L ⊗[K] L` and `N ⊗[K] L` to functions on
  the Galois sheets, with the formal-unramified diagonal element mapped
  exactly to the marked singleton-sheet selector, and the latter map promoted
  to an algebra equivalence for separable `L/K`;
- the ring-theoretic prime-inertia subgroup at a normalization prime, the
  inclusion of centered valuation inertia into it, equality of the two
  inertia groups at height one over a Noetherian base via localization, and
  identification of the full invariant normalization ring with the affine
  base for marked finite normal-closure data under explicit separability
  of `L/K` and integrally closedness of the base ring;
- descent of selected-prime unramifiedness from the inertia fixed ring to
  the `H`-fixed ring when `I ≤ H`, conditional only on the explicitly named
  fixed-inertia source input and the stated finiteness hypotheses, with the
  Dedekind condition required only at the selected localization and derived
  automatically for the height-one finite-normalization specialization;
- under an explicit graph-action compatibility, the inertia averaging
  correspondence fixes a generic characteristic-function selector exactly
  when its selected sheets form a union of inertia orbits;
- for arbitrary selected sheets, equivalence with the ordinary collision
  different is conditional on an explicit selection-dependent
  ramification-detection input; the base singleton recovers the existing
  height-one criterion automatically;
- for every essentially finite-type algebra, the collision Noether different
  detects the unramified locus at prime ideals; this discharges the separate
  `CollisionDifferentDetectsRamificationAt` input in that setting, while the
  inertia and purity bridges remain conditional;
- actual global selector extensions record equality with the prescribed
  generic selector and exist precisely under an explicit purity/gluing
  hypothesis;
- a compactified subgroup correspondence projector records both maps
  \[
  \mathbf Q[\text{finite étale spans}]\longrightarrow\Gamma_\eta,
  \qquad
  \Gamma_{\overline X}\longrightarrow\Gamma_\eta,
  \]
  so the extended idempotent restricts to the realized subgroup average
  without reversing the natural cycle-realization map;
- a supplied generic--compactified graph comparison square transports every
  rational group-algebra idempotent directly to a compactified idempotent
  with the prescribed restriction; the resulting convolution defect is
  formally zero, but the comparison does not construct a compactification or
  identify the supplied algebra with a Chow ring;
- for a raw compactified closure not obtained from such a global graph map,
  its convolution defect `Π * Π - Π` is proved to restrict to zero; the
  zero-defect witnesses recover `AlgebraProjectorExtension`, while geometric
  boundary support and actual defect vanishing remain separate inputs;
- locally and over a family of height-one components, such an extension—and
  hence its induced algebraic projector lift—exists exactly when the
  collision different avoids the relevant primes, subject to the stated
  comparison inputs;
- after supplying a not-necessarily-commutative rational Chow model, equality of its
  restriction map with the boundary restriction, and identification of the
  extended class with a prescribed cohomological projector, the prescribed
  Chow lift—and hence its complementary two-term diagonal decomposition—exists
  exactly under the same collision-different avoidance criterion;
- under essential finite type, the forward corollary
  `exists_prescribed_subgroupAverage_chowProjector_of_different_away` exposes
  the inputs individually and returns an explicit compactified idempotent;
  compactified cycle extraction and convolution-idempotence, one-way purity,
  inertia comparison, generic restriction, and prescribed realization all
  remain hypotheses of that corollary, and the indexed primes are not proved
  there to be an exhaustive codimension-one boundary family;
- formal unramifiedness on the visible locus together with no hidden inertia
  supplies the normalization-side saturation needed by the compactified
  extension package;
- normalization towers and conjugate centers indexed by double cosets;
- canonical conjugate normalization legs and pulled-back boundary ideals are
  constructed internally; under supplied center/ramification realizations,
  visible formal unramifiedness, and the explicit fixed--moving boundary
  separation condition, they imply no codimension-one ramification and
  discharge the local side of the existing selector and subgroup-projector
  extension criteria; actual gluing remains the explicit purity input;
- visible-unramifiedness results sending positive-inertia centers to the
  deleted boundary;
- abstract height-one different and purity interfaces used by the extension
  criterion;
- the rational identity that `(1/d) pull ∘ push` is idempotent whenever
  `push ∘ pull = d · id`, without claiming a construction of the Chow maps.

## Next geometric layer

Beyond the constructed finite split degree-zero model and its regular
torsor comparison, a concrete smooth projective compactification still
requires:

1. refine the finite étale admissible algebra, or another chosen
   proper/equidimensional class, to the concrete geometric application;
2. construct its cycle classes in
   \(\mathrm{CH}^d(X\times X)_{\mathbf Q}\) and prove coproduct additivity;
3. prove that fiber-product composition agrees with refined Chow
   convolution under the required transversality or Tor-independence
   hypotheses;
4. construct the concrete torsor comparison isomorphism for the chosen
   cover (the abstract Galois graph-composition and averaging calculation is
   now formalized);
5. supply the raw generic proper-support/graph-generated and compactified
   convolution algebras, and prove that the two-sided relation quotients in
   `Realization.Chow.Presentation` identify with the intended Chow or
   bivariant correspondence algebras;
6. instantiate the restriction and cohomological action, and prove the
   universal one-idempotent restriction square and representation-morphism
   comparison; a full sheet-algebra presentation is needed only for the
   optional stronger interface;
7. instantiate the selected finite étale/deck-extension inputs and construct
   the graph-cycle comparison square, or instantiate the rational Chow
   localization input and prove that the resulting boundary-valued raw
   closure defect vanishes or admits a correction;
8. prove the explicit target equality identifying the resulting extended
   subgroup average, or a supplied idempotent from its Hecke corner, with the
   prescribed motivic or Hodge summand;
9. extend beyond the finite-monodromy branch when a genuinely broader source
   of algebraic correspondence idempotents is available.

Mathlib does not currently provide a general Chow-correspondence or pure
Hodge-structure library, so these geometric constructions are exposed as
interfaces rather than asserted as universal facts.

The source library is locally owned and independent of the
Jacobian/Keller-specific `collision-ideals` project.  The original
`collision-ideals` worktree remains unchanged.
