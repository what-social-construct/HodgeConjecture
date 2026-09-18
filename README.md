# Collision Decompositions and Correspondence Projector Lifting

This Lean project develops collision ideals as scheme-theoretic input to
algebraic correspondences, with boundary inertia measuring whether a generic
sheet decomposition extends over a compactification.

**Scope.** This work formalizes collision and finite-group correspondence
mechanisms. It constructs a finite split degree-zero Chow/Betti/Hodge model,
but does not establish a new case of the Hodge conjecture or construct the
required general realization.

For the intended statement and its existing Lean equivalence, start with the
[target bridge sketch](research/TARGET_BRIDGE.md). For component evidence, use the
[gap map](research/GAP_MAP.md) and
[proof-dependency/archive audit](research/working/0017-proof-spine-and-archive.md).
The [claim ledger](research/CLAIM_LEDGER.md) records theorem scope; dated
checkpoints and [archived plans](research/archive/planning/README.md) are not
alternative current proof outlines.
The [object bench](research/bench/README.md) preserves the standalone
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
[`Correspondence/Examples/SplitPoints.lean`](HodgeConjecture/Correspondence/Examples/SplitPoints.lean)
and [`Realization/Chow/Examples/SplitPoints.lean`](HodgeConjecture/Realization/Chow/Examples/SplitPoints.lean):
the actual finite-étale point span on `Spec(k^I)` is idempotent, and a separate
two-point matrix calculation proves `ρ(E₀₀)=P₋₁` and its Palomar square.
The [split-span cycle-coefficient realization](HodgeConjecture/Realization/Chow/Examples/SplitSpanRealization.lean)
now connects these layers by a proved surjective algebra homomorphism on
actual split-presentable span classes. It respects geometric fiber products
and disjoint unions and takes empty spans to zero. The
[geometric-source endpoint](HodgeConjecture/Realization/Chow/Examples/GeometricSplitPoints.lean)
therefore recovers the same projector action and Palomar square from the
original point span. The Chow-correspondence composition and its degree-zero
Betti comparison are constructed below. Extension from split-presentable
to arbitrary finite-étale carriers is a separate step. The
free source algebra is not itself identified with matrices. Its
[additive quotient](HodgeConjecture/Realization/Chow/Examples/SplitSpanQuotient.lean)
is: the two-sided ideal generated by finite point-decomposition differences
is proved equal to the matrix realization kernel. Thus
`C_sp / J_sp ≃ₐ[ℚ] M_I(ℚ)`, using actual indexed scheme-coproduct
decompositions, a point-pair normal form, and matrix-unit independence.
The [actual integral-subscheme classification](HodgeConjecture/Correspondence/Examples/SplitIntegralSubschemes.lean)
now identifies every integral closed subscheme of `Spec(k^I)` with a unique
reduced rational point, by an isomorphism commuting with its closed
immersion. Closed subschemes have dimension at most zero, so there are no
integral closed curves. The [zero-cycle construction](HodgeConjecture/Realization/Chow/Examples/SplitZeroCycles.lean)
forms the cycle module on these actual integral subschemes. The
[rational-equivalence quotient](HodgeConjecture/Realization/Chow/Examples/SplitRationalEquivalence.lean)
uses integral curves and units in their actual scheme function fields as
principal-divisor data. That indexing type is empty, so its generated
relation submodule is zero. Thus `CH_0(Z_I;R) ≃ₗ[R] (I → R)` for
`R = ℤ` and `R = ℚ`, taking fundamental point cycles to unit vectors.
The canonical scalar-extension comparison
`ℚ ⊗[ℤ] CH_0(Z_I;ℤ) ≃ₗ[ℚ] CH_0(Z_I;ℚ)` is also proved, including its
formula on point generators.
The [actual product and point-fiber comparison](HodgeConjecture/Correspondence/Examples/SplitProductGeometry.lean)
identifies the product points and inverse-image subschemes. Image point
maps have residue-field degree one, and the actual fiber inclusions have
ambient-stalk multiplicity one. These calculations give the
[cycle and Chow operations](HodgeConjecture/Realization/Chow/Examples/SplitCycleOperations.lean):
proper pushforward sums over fibers, flat pullback copies point coefficients,
and intersection is diagonal pullback of the external product. The
[Chow correspondence composition](HodgeConjecture/Realization/Chow/Examples/SplitChowComposition.lean)
is defined by `p13_* (p12^* a · p23^* b)` on the actual Chow groups and
proved to be matrix multiplication in point-pair coordinates. The diagonal
is its identity, and composition is associative. The
[Chow endomorphism algebra](HodgeConjecture/Realization/Chow/Examples/SplitChowAlgebra.lean)
retains that geometric composition and diagonal unit. It is proved
algebra-isomorphic to both the additive split-span quotient and `M_I(ℚ)`,
with the point-span class mapping to the actual Chow point-pair class.
For every finite split span, this equivalence maps its quotient class to
the proper pushforward of its carrier's fundamental cycle along the pair map.
The [geometric Chow action](HodgeConjecture/Realization/Chow/Examples/SplitChowAction.lean)
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
The [independent finite Hodge structure](HodgeConjecture/Realization/Betti/Examples/SplitHodgeStructure.lean)
uses the actual complexification `ℂ ⊗[ℚ] H_B^0`, computed as complex
point functions, with canonical tensor conjugation and the effective
type-`(0,0)` bigrading. Rational Hodge classes are the inverse image of
its complex `(0,0)` piece, and are then proved to be the whole rational
space, without using the cycle-class map.
On the actual disjoint union `Spec ℂ ⨿ Z_I`, the
[Chow Tate block](HodgeConjecture/Realization/Chow/Examples/SplitTateBlock.lean)
constructs `enc(z) = [(*,*)] + j_*z`, with `j(i)=(*,i)`, and decodes by
the actual flat pullback `j^*`. Encoding is idempotent and decoding it
recovers `z`. The
[Betti block comparison](HodgeConjecture/Realization/Betti/Examples/SplitTateBlock.lean)
proves that its action is `P_cl(z)` and that decoding any correspondence
has the cycle class of its lower-left action block. This instantiates the
finite degree-zero Hodge model, graph construction, detection, Hodge-morphism
compatibility, and the graph/Palomar target equivalences.
The [split marked-sheet geometry](HodgeConjecture/Correspondence/Examples/SplitGaloisSheets.lean)
constructs the actual regular split `G`-torsor and the finite étale
homogeneous intermediate cover on `S=G/D`, for any subgroup `D`.
On `I=S∖{D}`, the
[residual Chow map](HodgeConjecture/Realization/Chow/Examples/SplitGaloisResidual.lean)
sends `x∈ker(ev_D)` to the sum of actual point classes `∑ x(i)[i]`.
It is bijective and carries multiplication to geometric intersection;
in particular, `q−1` maps to `−[Z_I]`. Composing with the constructed
cycle class gives the residual Betti realization.
The [actual Chow shear](HodgeConjecture/Realization/Chow/Examples/SplitChowShear.lean)
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
[split-span working note](research/working/0008-split-span-cycle-realization.md)
and its [exact additive quotient](research/working/0009-split-span-additive-quotient.md),
followed by the [integral-subscheme checkpoint](research/working/0010-split-integral-subschemes.md)
and the [zero-cycle and rational-equivalence construction](research/working/0011-split-zero-cycles.md),
then [geometric Chow composition](research/working/0012-split-chow-composition.md)
and [actual degree-zero Betti cycle classes](research/working/0013-split-betti-cycle-class.md),
then the [finite Hodge/Tate-block comparison](research/working/0014-split-hodge-tate-block.md)
and [split marked-sheet residual/action comparison](research/working/0015-split-galois-marked-comparison.md).

## Explicit literature inputs

The [input modules](HodgeConjecture/Inputs.lean) separate selected standard
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
[input checkpoint](research/working/0016-source-input-packages.md) and
[submission handoff](research/working/PALOMAR_FIXED_RING_HANDOFF.md).

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
mathematical hypotheses.  Over a perfect base field (in particular in the
characteristic-zero setting), `NormalClosureData.isGalois` derives
`IsGalois K N`.  The resulting `galoisGroup`,
`intermediateFixingSubgroup`, and canonical normalization deck action feed
the marked-sheet layer directly.  Normality is used to keep all conjugate
embeddings inside the same field `N`, hence under one Galois group; it does
not make that group abelian.  The deck automorphisms commute with the map to
the affine base because they fix `K` and therefore the `B`-scalars through
the scalar tower, not because the group commutes.  The pointwise sheet
algebra is separately commutative, while the group algebra and the full Chow
correspondence algebra may be noncommutative.  For this marked normal closure, the
intermediate normalization is identified formally with the subgroup-fixed
normalization ring.  Using
chosen quotient representatives, the collision tensor algebra also has an
evaluation map to functions on `G/H`, and its separability element is proved
to map to the marked singleton-sheet selector.  The multiplicative diagram is
also explicit: base-sheet augmentation composed with
`normalClosureTensorToGenericSheets` equals the tensor-diagonal algebra map
`normalClosureTensorDiagonal`.  Over a perfect base field,
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

[*Galois Correspondences and the Hodge Conjecture*](paper/main.pdf) is the canonical
author-review candidate.  Its section order follows the dependency-ordered
components reflected by the active Lean modules: target equivalence,
collision and finite-etale convolution, group and
Hecke projectors, the marked-sheet block form, the codimension-one boundary
endpoint, the compactification fork, and the exact conditional realization
gap.  Fixed-ring localization and source inputs are supporting appendices.
The abstract states the conjecture and the proposed route directly; the
[Chow--Betti-first plan](research/TARGET_BRIDGE.md#0-operative-plan-chow-to-betti-first)
organizes the next geometric work around which varieties and codimensions
the construction covers, and records its acceptance criteria.
Its [candidate comparison](research/TARGET_BRIDGE.md#g0-smooth-projective-setting-and-candidate-constructions)
keeps smooth projective varieties as the main setting and abelian-covered
targets as an optional worked subclass. Projective bundles over curves or
surfaces and their polynomial-chart checkpoint remain optional deferred
examples; their detailed generation and Galois-closure analysis is preserved
in the plan. The immediate checkpoint returns to the
[boundary-section ideal route](research/TARGET_BRIDGE.md#b0-boundary-section-algebra-and-uniform-trace-landing).
The self-contained
[`BoundedOverring.lean`](HodgeConjecture/Boundary/Normalization/BoundedOverring.lean)
proves the generic normal-Noetherian bounded-overring implication and its
formulation using the existing `Submodule.colon`; the full build and six
focused regressions pass, and all three theorems use only the permitted
standard axioms. The next geometric constructions are the actual
boundary-section algebra and a genuine uniformly bounded trace dual.
Uniform landing of all boundary sections remains a separate implication
to prove; none of these algebraic steps asserts Hodge-class generation.

`paper/main.pdf` is the single current manuscript PDF. The earlier drafts
and their sources are preserved in the
[manuscript archive](research/archive/manuscripts/README.md), outside the
current build and release checks. No manuscript has been placed in the publication
queue.  The canonical draft does not identify the free span algebra with Chow
correspondences, does not claim an unconditional boundary extension, and does
not prove a new Hodge case.  Licensing, literature/novelty review, and final
author review remain release blockers. Current proof roles and retained
dependencies are recorded in the
[proof-spine audit](research/working/0017-proof-spine-and-archive.md).
The superseded section/module plan is preserved only in the planning archive.

### Palomar packaging status

`Challenge.lean`, `Solution.lean`, and `comparator.json` expose the two generic
height-one fixed-ring results through a small Mathlib-only statement surface.
This is a packaging draft, not a submitted or registered result.  The exact
remaining release work—including the Lean-toolchain migration, root licence,
human authorship/maintainer fields, and Comparator/NanoDa run—is recorded in
[`research/working/PALOMAR_FIXED_RING_HANDOFF.md`](research/working/PALOMAR_FIXED_RING_HANDOFF.md).
Those advertised fixed-ring statements do not prove Tag `0BST` or global
étaleness, and are separate from the finite degree-zero Hodge model above.

## Module organization

- [`Collision`](HodgeConjecture/Collision) contains the diagonal and
  collision ideals, the global self-fiber product
  \(R_f=X\times_YX\), the relative diagonal ideal sheaf, intrinsic and
  ambient sheaf-colon residuals, decomposition defects, component selectors,
  and the literal clopen scheme decomposition.
- [`Correspondence`](HodgeConjecture/Correspondence) contains scheme
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
- [`Boundary/Sheets`](HodgeConjecture/Boundary/Sheets) contains generic
  \(G/H\)-sheets, relative inertia indices, characteristic-function
  selectors, the inertia-orbit criterion, and the marked selector/CRT versus
  graph-coordinate decomposition.
- [`LinearAlgebra/BlockGraphProjector.lean`](HodgeConjecture/LinearAlgebra/BlockGraphProjector.lean)
  is the shared graph/diagonal/shear core used by both the marked-sheet and
  Tate-block realizations.
- [`LinearAlgebra/MarkedAugmentedAlgebraDecomposition.lean`](HodgeConjecture/LinearAlgebra/MarkedAugmentedAlgebraDecomposition.lean)
  gives the augmentation ideal its internal corner unit and proves the genuine
  product-algebra decomposition, separately from the constant-unit linear
  shear coordinates.
- [`LinearAlgebra/UniversalIdempotentAlgebra.lean`](HodgeConjecture/LinearAlgebra/UniversalIdempotentAlgebra.lean)
  gives the common algebra `ℚ × ℚ` for presenting one idempotent and its
  complement in any associative rational algebra; it is the active
  multiplicative source for the compactification and Palomar target squares.
- [`Boundary/AveragingAction.lean`](HodgeConjecture/Boundary/AveragingAction.lean)
  relates the convolution idempotent averaging over a boundary inertia
  subgroup to its contragredient action on the pointwise generic-sheet
  algebra.
- [`Boundary/SheetProjectorExtension.lean`](HodgeConjecture/Boundary/SheetProjectorExtension.lean)
  records actual global selector extensions, their generic restriction, and
  the explicit purity/gluing and selection-dependent ramification inputs.
- [`Boundary/GaloisProjectorExtension.lean`](HodgeConjecture/Boundary/GaloisProjectorExtension.lean)
  connects finite subgroup graph averages to generic and compactified
  correspondence algebras through explicit extension packages.
- [`Boundary/Normalization`](HodgeConjecture/Boundary/Normalization)
  contains marked normal closures, valuation inertia, affine normalization
  models, invariant-ring descriptions of intermediate normalizations, exact
  prime inertia and its Noetherian height-one localization comparison with
  centered valuation inertia, canonical conjugate normalization legs,
  fixed--moving boundary ideals and their conditional separation endpoint,
  the collision-to-sheet-selector comparison, visible-unramifiedness lemmas,
  and the normalization–inertia diagram.
  The marked normal-closure record itself supplies normality and finiteness;
  over a perfect/characteristic-zero base its derived Galois structure,
  fixing subgroup, and canonical deck action are reused by these layers.
  The local fixed-inertia theorem and every global cover-extension or gluing
  input remain explicit assumptions.
- [`Boundary`](HodgeConjecture/Boundary) contains the collision different,
  height-one comparison, and selector-extension criteria.
- [`Realization`](HodgeConjecture/Realization) packages conditional
  correspondence, Chow-style, compactification, and cohomological
  consequences, together with the abstract Hodge target schemas.
  [`HodgeClasses.lean`](HodgeConjecture/Realization/HodgeClasses.lean)
  separates fixed-codimension, one-model, and indexed-family quantifiers;
  [`HodgeTarget.lean`](HodgeConjecture/Realization/HodgeTarget.lean) is the
  target umbrella.  The
  [`Realization/Chow`](HodgeConjecture/Realization/Chow) sublayer is organized
  by mathematical role:
  - [`Model.lean`](HodgeConjecture/Realization/Chow/Model.lean) records the
    generic and compactified rational correspondence algebras, with no
    commutativity assumption,
    their cycle-class/restriction maps, and cohomological action;
  - [`Presentation.lean`](HodgeConjecture/Realization/Chow/Presentation.lean)
    constructs quotients of supplied, not-necessarily-commutative raw
    correspondence algebras by two-sided relation ideals and descends
    restriction and action;
  - [`GaloisProjector.lean`](HodgeConjecture/Realization/Chow/GaloisProjector.lean)
    identifies the boundary-extended subgroup projector with a prescribed
    cohomological target;
  - [`TateGraphProjector.lean`](HodgeConjecture/Realization/Chow/TateGraphProjector.lean)
    proves the abstract class/graph-projector equivalence through independent
    construction, detection, and Hodge-compatibility interfaces, together
    with the shear and rational `C₂`-reflection forms of the graph operator;
  - [`IdempotentRepresentation.lean`](HodgeConjecture/Realization/Chow/IdempotentRepresentation.lean)
    packages linear intertwiners as morphisms of representations of the
    universal one-idempotent algebra `ℚ × ℚ`;
  - [`MarkedAugmentedRealization.lean`](HodgeConjecture/Realization/Chow/MarkedAugmentedRealization.lean)
    carries the augmentation-ideal source model into the Tate block, packages
    the comparison as a morphism of representations of the universal
    one-idempotent algebra, and keeps the residual realization linear; its
    full sheet-algebra presentation is an optional stronger interface;
  - [`GaloisMarkedBlock.lean`](HodgeConjecture/Realization/Chow/GaloisMarkedBlock.lean)
    identifies the marked sheet selector action with the canonical Tate graph
    operator and proves rational naturality under a residual realization map;
  - [`GaloisMarkedRealization.lean`](HodgeConjecture/Realization/Chow/GaloisMarkedRealization.lean)
    separates the generic selector from the noncommutative compactified
    correspondence algebra, exposes `palomarTargetSquare` as an equality of
    algebra-homomorphism composites, detects the lower-left class from an
    explicit representation square, derives the exact graph action under
    surjectivity, and
    records class-dependent conditional coverage and replacement endpoints;
  - [`GaloisHodgeTarget.lean`](HodgeConjecture/Realization/Chow/GaloisHodgeTarget.lean)
    records the one-way implication from class-indexed prescribed
    finite-cover lifts to the modeled Hodge target;
  - [`TransferProjector.lean`](HodgeConjecture/Realization/Chow/TransferProjector.lean)
    proves the normalized pull--push projector identity from an explicit
    rational degree formula, while leaving construction of Chow pullback and
    pushforward to the geometric model.

  The historical commutative selector realization is preserved in the
  [Lean archive](research/archive/legacy-lean/README.md), outside the library. The
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
  to an algebra equivalence over a perfect base field;
- the ring-theoretic prime-inertia subgroup at a normalization prime, the
  inclusion of centered valuation inertia into it, equality of the two
  inertia groups at height one over a Noetherian base via localization, and
  identification of the full invariant normalization ring with the affine
  base for marked finite normal-closure data under explicit perfectness and
  integrally closedness hypotheses;
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
