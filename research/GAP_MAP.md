# Current gap map

Last reviewed: 2026-09-29 (SP102 canonical finite-map grading validated;
earlier checkpoint records retain
their original validation scope).

Start with [the target and equivalence sketch](TARGET_BRIDGE.md): it fixes
the geometric statement, separates the two directions of the proved bridge,
and identifies the minimal prescribed-class construction. This longer map
records the component-level evidence. The standalone matrix diagnostic is
[benched](bench/README.md), not a premise or obstruction in that route.

When used, the marked realization spine follows one chosen algebraic
projector `Π` for each prescribed class and detects its cycle `D(Π)`.
Residual surjectivity belongs to the current cancellation proof for the
chosen projector's entire action. The named Galois replacement belongs
to the reverse coverage equivalence and gives another witness for the same
class, not an equality of projectors. Construction `C` remains part of the
Hodge-to-graph equivalence proof. See the target sketch for the roles of
these maps and hypotheses.

This note follows the semantic discipline of the sibling
`jacobian-collision-geometry` project: source and target propositions are
named exactly, proved arrows are separated from parameterized arrows, and a
geometric interface is not treated as a theorem merely because later record
assembly is formal.

## Current work order

Follow the [Chow--Betti-first plan](TARGET_BRIDGE.md#0-operative-plan-chow-to-betti-first).
Start from the actual cycle map and the independently defined Hodge
subspace, then ask: **for which varieties `X`, and which codimensions `p`,
does our geometric construction generate the rational Hodge classes?**
The candidate comparison must name explicit geometric cycles, their Betti
images and the property of the variety supporting the generation argument.
Galois actions and projectors are mechanisms to use when needed, not
prerequisites for a direct cycle-class construction.

SP94 makes this first obligation explicit in
`Realization/Chow/UpstairsGeneration.lean`: for every independently
specified Hodge class `α`, some member of a fixed indexed family of
upstairs recipes has cycle class `pull_i α`. Both a fixed-index subspace
inclusion and its class-dependent indexed form are defined. With explicit
positive-degree transfer and cycle-class compatibility, the normalized
Chow pushforward represents `α`; this conditional implication is proved.
The geometric generation hypothesis itself has not been discharged.

The live order is now:

1. **Completed SP94:** the arbitrary-class condition and its conditional
   descent implication; no additional marked-Galois witness package.
2. **Completed SP95/SP96:** the existing actions identify the full base and marked
   deck groups; preservation of the original refinement is exactly
   membership in the original fixing subgroup. SP97 identifies the actual
   generic fiber via its generic-stalk pullback square; SP98 identifies
   its base change with the actual tensor spectrum and both projections.
   SP99 composes the existing splitting to identify the sheet spectrum with
   that actual base change and carries its base-sheet point to the original
   marked embedding. SP100 identifies every coset evaluation point with
   the original sheet embedding and, using normal stalks of `Y`, the
   original inverse-labelled normalization action followed by the refinement.
3. SP101 constructs actual degree-weighted finite cycle pushforward and its
   restriction to explicitly compatible existing gradings. SP102 supplies
   compatibility for the canonical field grading. Next prove the principal/norm
   identity needed for Chow descent. Instantiate Betti pullback/trace and their two
   compatibility laws for the same actual cover. Supply smooth-geometric
   normality where the construction needs it.
4. Construct named upstairs cycle recipes and prove generation of the
   pulled-back rational Hodge classes for the intended varieties and
   codimensions, then apply normalized descent.

A parallel pruning queue records actual theorem dependencies and
mathematical consumers before moving objects. The minimal cycle conclusion
need not consume all projector/action machinery; that does not make the
stronger existing endpoints or their dependencies redundant. No module is
removed or archived at SP94, SP95, SP96, SP97, SP98, SP99, SP100, SP101 or SP102.

SP101 uses `Cycles/FinitePushforward.lean` and `GradedFinitePushforward.lean`.
Its generalized image is literally the existing `W.val.map f`; comparison
with the old closed-image object is proved, not a choice of another carrier.
The actual support-to-image map gives a positive finite function-field
degree, so `[W]` maps to `[K(W):K(f(W))] [f(W)]`. No ambient integrality,
normality, dominance or etaleness is required. Coefficients may lie in any
semiring. Grading uses an explicit support-degree equality, not an automatic
codimension assertion or a new free module.

SP102's `Cycles/FiniteResidueField.lean` proves algebraicity for the literal
`f.residueFieldMap x`, with no ambient normality, integrality, Noetherianity,
etaleness or base-field hypothesis. `FiniteGrading.lean` uses the existing
structural maps and `residueFieldBaseMap_comp` to install their actual scalar
tower. Mathlib's transcendence-degree formula gives equality of cardinals
before taking integer values. Over a locally finite-type field base this
preserves the existing dimension function and every actual image-support
degree. SP101's existing raw/graded cycle maps therefore preserve the canonical
grading without a supplied compatibility premise. No second map or grading
is constructed; arbitrary independently chosen dimension functions still
require SP101's explicit comparison. Dimension degree is not relabelled
as codimension without its existing complementary-degree hypotheses.

The next relation obligation is
`f_*(ambientPrincipalDivisor W u) = ambientPrincipalDivisor f(W) (Norm u)`
for the actual field norm. Arbitrary integral carriers need not be normal,
even for a finite etale cover of smooth varieties, and their maps to their
images need not be etale. A DVR-only argument will not establish preservation
of the repository's general length-order principal relations. The exact
source is [Stacks 02RT](https://stacks.math.columbia.edu/tag/02RT); quotient
descent must use that geometric identity, not assume preservation of the
relation submodule. This norm law, finite pushforward composition,
flat pullback/degree, Betti transfer,
the cycle-class square and class-dependent generation remain separate.

The first local norm obligation is the weighted length-order formula of
[Stacks 02MJ](https://stacks.math.columbia.edu/tag/02MJ) for a finite
extension of domains over a one-dimensional Noetherian local domain.
Reuse `Algebra.norm`; the missing assertion is its compatibility with
those local orders, not the existence of a norm operation. The pinned
norm-localization API assumes freeness and is insufficient on its own
for the potentially nonnormal relation carriers.

SP102 validation passes the residue/grading scoped builds, full build,
twenty-example focused suite, endpoint dependency audit and fresh SP101
regression. All five new public APIs have exactly the standard three Lean
axioms. Lean--TeX parity and historical preservation checks pass; see A11ch
in the claim ledger for the precise validation scope.

SP95 uses `Cycles/FunctionFieldExtensionality.lean` and
`Boundary/Normalization/GluedNormalizationDeckComparison.lean`.
Actual generic pullback determines dominant morphisms over a common base
when the target is relatively separated and source/target are integral.
For the original normalization, relative separatedness comes from its
already proved affineness. This proves uniqueness of deck transformations
without a finite-extension assumption. For finite `N/K(X)`, the field
automorphism reconstructed from `d` is `e_N ∘ (d⁻¹)^* ∘ e_N⁻¹`.
The old action recovers `d`, giving surjectivity and an explicit group
equivalence. All maps, carriers and markings are unchanged. No normality
of the base, separability, etaleness or finiteness of the normalization
morphism is required for this comparison. This does not yet identify
fibers as coset spaces or supply a torsor or Chow--Betti realization.

SP96's `GluedNormalClosureStabilizer.lean` retains finite dominance of
`p:Y→X`, integrality of both schemes and normal stalks of `Y`. The new
converse takes actual pullback of `λ ∘ a_N(σ) = λ`; SP93 then gives
`σ⁻¹(ι(c)) = ι(c)`, hence `σ` fixes the marked field. SP90 already
supplies the other direction. SP95 reconstructs arbitrary base deck
transformations, so this is the full stabilizer, not only an inclusion.
Viewing a marked deck transformation over `X` through `p ∘ λ = μ_N`
gives an explicit inverse for the unchanged marked action and hence
`H ≃ Aut_Y(Z_N)`. The promotion is private implementation data, not a
second public deck or cover package. No separability, etaleness, normality
of `X`, Noetherianity or finiteness of `μ_N` is added. A geometric-fiber
identification, fixed-field equality or torsor theorem is not inferred
from this group equivalence.

SP97 uses `functionFieldMapOfDominant_isPushout_of_affine` in
`FiniteFunctionField.lean` and `functionFieldMapOfDominant_isPullback`
in `GenericFiber.lean`. For finite dominant `p:Y→X` between integral
schemes, the actual generic-stalk square is cartesian. Its standard
`IsPullback.isoPullback` gives `Spec K(Y) ≅ Y ×_X Spec K(X)`, with
the actual generic-stalk and field-pullback maps as projections. The
section-ring algebra structures are the original pullback and generic
germs, not separately supplied compatible maps. No normality, etaleness,
separability, Noetherianity, or additional finite-extension premise is
assumed. This identifies the generic fiber; it does not yet identify its
split base change with a coset space, all geometric fibers, or a torsor.

SP98's `functionFieldMapOfDominant_baseChange_isPullback` in
`GenericFiberBaseChange.lean` identifies
`Spec(E ⊗_{K(X)} K(Y)) ≅ Y ×_X Spec E`, where the base map is the
actual `Spec E → Spec K(X) → X`. Here `E` is any commutative
`K(X)`-algebra, not necessarily a field, finite, reduced or nontrivial.
The upstairs algebra structure is the original `κ_p`; the two maps are
the right tensor inclusion followed by the upstairs generic-stalk map
and the left tensor inclusion to `Spec E`. The existing
`IsPullback.isoPullback` retains both projections. No new isomorphism
wrapper, carrier or action is introduced. The result needs no
separability and does not assert that this tensor algebra splits.
SP99 performs the specialization to `E=N_p` in `GenericSplitFiber.lean`.
Its four public APIs give the canonical isomorphism from the existing
sheet spectrum, its two projection formulas and the marked-point identity.
Separability is derived from finite formal unramifiedness of the original
map. The map to `Y` evaluates the original sheet embeddings and then uses
the generic-stalk map; the map to `Spec N_p` comes from constant functions.
The base-sheet point is exactly the pullback lift of the original marked
embedding and the identity. No normal-stalk, Noetherian, perfect-field or
additional Galois premise is needed. The proof reuses the old splitting
and augmentation square rather than constructing another evaluator.

SP100's four APIs in `GenericSplitFiberAction.lean` use SP99's existing
comparison to identify the two projections of every evaluation point.
The `Y`-projection uses `D.sheetEmbedding s`, and the `N_p`-projection
is the identity. For `s=gH`, the old fixing subgroup identifies that
embedding with `g ∘ ι`. Let `γ_{N_p}=ι_{η_Z} ∘ Spec(e_{N_p})` use
the old function-field comparison of the same normalization. With the
existing normal-stalk input for `Y`, the point is exactly
`⟨λ ∘ a_{N_p}(g⁻¹) ∘ γ_{N_p}, id⟩` in the actual pullback.
The equality of maps to `Y` alone needs no formal unramifiedness;
that hypothesis belongs to the existing split-fiber comparison.

This discharges the individual generic sheet/orbit comparison, not an
action of `G` by deck maps on `Y` when `H` is not normal, nor an
equivariance theorem for an unspecified action on the entire fiber.
There is no new field, evaluator, carrier, action or splitting. Arbitrary
geometric fibers, torsors and actual Chow--Betti realization/generation
remain distinct obligations. Follow the live order with actual same-cover
realization maps; add further fiber classification only for a named consumer.

The [candidate comparison](TARGET_BRIDGE.md#g0-smooth-projective-setting-and-candidate-constructions)
retains smooth projective complex varieties as the main setting. When a
connected finite etale cover `f:Y -> X` is useful, its connected Galois
closure is again smooth projective; no abelian hypothesis is needed for
that construction or for trace descent. A useful nontrivial cover is not
presumed to exist for every target. The generation obligation is to
construct cycles on `Y` representing `f^*Hdg^p(X)`, not necessarily all
Hodge classes on `Y`. Degree-normalized pushforward then descends those
cycles; Galois closure alone does not construct them.

Targets finite-etale-covered by abelian varieties isogenous to `E^n`, for
a fixed complex elliptic `E`, remain an optional worked subclass. Their
upstairs isogeny class is stable under Galois closure and has known divisor
generation. An elliptic `p=1` seed and then `E^2` are an optional example
sequence, not the main work order. Kuga--Sato remains a later projector
test: Scholl's selected cuspidal factor has no nonzero diagonal Hodge
classes. Sources and the precise scope are in the linked comparison.

The candidate comparison also records
[projective bundles over bases of dimension at most two](TARGET_BRIDGE.md#optional-deferred-construction-projective-bundles-over-low-dimensional-bases)
as an optional deferred non-abelian example: `X <- Y=P_S(V) -> S`, with the
left map finite etale and the right map a projective bundle. The relative
hyperplane operation applied to pulled-back fundamental classes, divisors
and points gives the explicit upstairs recipe. The Hodge-compatible bundle
formula computes its image; normalized trace gives the downstairs class.
This is a classical known-case deduction, not a new Lean instance or a
reduction of arbitrary `X` to this geometry.

The upstairs projective-bundle presentation survives Galois closure by
finite etale base change `S' -> S`. The full deck group over `X` is not
automatically compatible with this presentation. Sources, precise
codimension bounds, typed maps and the cycle-class equation are recorded
in the linked construction.

If that example is resumed,
[PB0's actual standard chart](TARGET_BRIDGE.md#pb0-optional-deferred-scheme-checkpoint)
is its first bounded implementation: construct `(R[X_0,X_1]_{X_0})_0`
as `R[T]`, with constants and structural map compatibility, then compose
with `Proj.basicOpenIsoSpec`.
Relative bundle gluing, `O(1)`/Chow operations, positive-degree Betti/Hodge
comparison and finite-cover trace are separate missing constructions.
Existing field normal closure is not a global finite etale cover adapter.

The construction history below follows the existing
[boundary-section ideal route](TARGET_BRIDGE.md#b0-boundary-section-algebra-and-uniform-trace-landing).
The first checkpoint is the normal-Noetherian implication
`T <= R <= Frac(T)`, `0 != a in T`, `a R <= T` implies `R = T`,
adapted self-containedly in
[`Boundary/Normalization/BoundedOverring.lean`](../HodgeConjecture/Boundary/Normalization/BoundedOverring.lean).
Its namespace is `HodgeConjecture.NormalizationInertia`; the three endpoints
are `subalgebra_eq_bot_of_nonzero_mul_mem_base`,
`subalgebra_eq_bot_of_mem_colon`, and
`colon_eq_bot_of_subalgebra_ne_bot`. Here `R = bottom` means equality to
the base algebra, not the zero ring. The transporter is the existing
`Submodule.colon`, not a new ideal object. The full build and six focused
regressions pass. An enforced axiom allowlist verifies that all three
theorems use only `propext`, `Classical.choice` and `Quot.sound`.

The next section-algebra constructor is now implemented in
[`Boundary/Normalization/AffineSections.lean`](../HodgeConjecture/Boundary/Normalization/AffineSections.lean)
and
[`Boundary/Normalization/BoundarySections.lean`](../HodgeConjecture/Boundary/Normalization/BoundarySections.lean);
The full build and sixteen focused regressions pass, with the standard-axiom
allowlist enforced for all twenty-one new declarations. For a domain `T` and its specified fraction
field `F`, the actual generic germ gives an injective `T`-algebra map
`affineSectionsToFractionField` from every nonempty open of `Spec T`.
Its range `affineSectionSubalgebra` is canonically equivalent to the
section ring; constants and restriction commute with this map, smaller
opens give larger subalgebras, and the full-open image is the base algebra.
This uses the existing Mathlib section action and generic stalk, without
normality, Noetherianity, a replacement function field or a supplied
section comparison.

For the same `NormalizedCover`, take `T` to be its normal-closure
normalization ring and the open to be the complement of
`fixedMovingBoundaryIdeal C I`. The proved fraction-field identification
and faithful normalization action imply that a nontrivial subgroup `I`
has nonzero fixed-locus ideal, hence this open is nonempty. The actual
`boundarySectionsToNormalClosure` then embeds its structure-sheaf sections
into the existing `N`; its range is `boundarySectionSubalgebra`. The
underlying module is the existing `.toSubmodule`, not a second carrier.

The trace-dual checkpoint in
[`TraceDualBound.lean`](../HodgeConjecture/Boundary/Normalization/TraceDualBound.lean)
and
[`NormalizationTraceBound.lean`](../HodgeConjecture/Boundary/Normalization/NormalizationTraceBound.lean)
uses the existing Mathlib
`Submodule.traceDual B K (1 : Submodule T N)`:
`T^vee_B = {z in N : Tr_{N/K}(zT) subset B}`. The base of trace-integrality
is explicitly `B`, not the normalization `T`. A finite separable extension
provides an integral generic basis and its trace-dual basis. The entire
trace dual lies in the finite `T`-span of the latter, so clearing the finitely
many basis denominators gives one nonzero `d : T` with `d T^vee_B <= T`.
Neither Noetherianity nor normality of `B`, nor finite freeness of the
normalization, is needed for this bound. In particular the argument does
not assert `T <= T^vee_B` for a nonnormal `B`.

For the same `NormalizedCover C`, `normalizationTraceDual C` is an alias
for that existing submodule. With separable `L/K`, the supplied normal closure
is finite separable, and the existing fraction-field comparison gives the
uniform normalization denominator. Under the additional Noetherian-base
hypothesis, the finite normalization model makes `T` Noetherian; its
integral-closure construction supplies normality. B0 then implies that a
nonzero member of `(T^vee_B:R_I)` forces the actual section algebra to equal
the base. Equivalently, a proper `R_I` has zero such colon ideal. The
trace landing formulation quantifies every actual section on `U_I`.
These are conditional consumers of the proved denominator, not an existence
theorem for a nonzero geometric landing multiplier. SP66 passes the full
build, fourteen focused regressions, and enforced standard-axiom checks
for all eleven new declarations. The unchanged dependency audit and the
68-page single-manuscript PDF checks pass.

B3 now constructs the pole and comparison in
[`SectionLocalization.lean`](../HodgeConjecture/Boundary/Normalization/SectionLocalization.lean),
[`HeightOneBoundaryPole.lean`](../HodgeConjecture/Boundary/Normalization/HeightOneBoundaryPole.lean)
and
[`BoundaryPole.lean`](../HodgeConjecture/Boundary/Normalization/BoundaryPole.lean).
Pointwise local fractions are glued into an actual structure-sheaf section;
clearing a rational function by a power of `J` supplies those local
fractions on a nonempty open `V` contained in `D(J)`. If `T` is a
Noetherian domain and a height-one prime `p` contains `J != 0`, localized
dimension one and finite generation produce `f != 0` in `J`, `t` outside
`p`, and `t J^n <= (f)`. Hence `z=t/f` is a genuine section image, whereas
`z` in `T` would force `t` into `p`. No normality, trace-landing premise
or supplied pole is used in this generic construction.

For the existing normalization, Noetherian `B` and the supplied finite
model make `T` Noetherian, so a height-one prime containing `J_fm(I)`
forces `R_I != T`. With separable `L/K`, B2 then constructs a failing actual
section for every nonzero proposed trace multiplier and proves
`(T^vee_B:R_I)=0` at that prime. The implemented
`conjugateBoundarySeparation_of_traceLanding` proves the exact endpoint
from `forall I != bottom, exists s != 0, s R_I <= T^vee_B`, with landing
quantified over actual `BoundarySectionRing C I` elements. No extra
transporter ideal, section carrier or pole hypothesis is introduced.
SP67 passes the full build, twelve focused regressions, an enforced
standard-axiom allowlist for all nine new declarations, the appended
umbrella-export checks and the freshly run unchanged dependency audit.
The 69-page single manuscript passes its build and visual checks. The full
historical verification inventory was not rerun.

B4a / SP68 adds a direct commutative-algebra sufficient condition in
[`RegularPairBoundary.lean`](../HodgeConjecture/Boundary/Normalization/RegularPairBoundary.lean).
The refined `exists_heightOne_boundary_denominator_of_ne_zero` fixes any
specified `f != 0`, without requiring `f in J`, before constructing `t`
outside `p` and `t J^n <= (f)`; the previous theorem is retained as a
wrapper. If additionally `f,g in J` and `g` acts injectively on `T/(f)`,
the relation `t g^n in (f)` forces
`t in (f)`, contradicting `t` outside `p`. Hence
`not_le_heightOne_of_regularPair` excludes every height-one prime containing
`J`. This only assumes a Noetherian domain, not normality or trace data.

For each nontrivial subgroup, use the existing summands of `J_fm(I)`:
choose `0 != f_I in fixedLocusIdeal I` and
`g_I in movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I`, with
`g_I` acting injectively on `T/(f_I)`. Under Noetherian `B` and the supplied
finite normalization model,
`conjugateBoundarySeparation_of_fixedMoving_regularPairs` then proves the
existing separation condition. Perfectness is not needed. The unit-ideal
case is allowed; these injectivity witnesses are not a claim of a full
regular sequence with nonzero final quotient. No new ideal, section carrier,
projector or input package is introduced. SP68 passes the full build,
ten new focused regressions and three enforced standard-axiom checks.
The previous boundary-pole suite was freshly rerun after the refinement:
its twelve examples and nine-declaration allowlist pass. The appended
three umbrella-export checks and axiom reports, fresh unchanged dependency
audit, independent Lean--TeX review and 70-page single-PDF checks pass.
The historical inventory prefix is preserved; that entire suite was not rerun.

This separated-summand condition is sufficient, not an equivalence or a
necessary condition for the generic ideal criterion. An algebra-only
example takes a zero moving summand and a proper fixed summand of
codimension at least two; no realization of those arbitrary ideals as
`J_fix(I),J_mov(I)` of a normalized cover is asserted.

**SP69: the geometry must supply more than the current package.** The
[geometric-pair input audit](working/0018-geometric-pair-input-audit.md)
found no instantiated `NormalizedCover` in the active library at SP69. The package
supplies finite normalization models and a marked open immersion, not
full visibility or quotient regularity. In the characteristic-zero model
`x=t^2` with visible open `D(t)`, the visible map is etale while the
nontrivial subgroup has `J_fix=J_mov=J_fm=(t)`. The height-one boundary
therefore remains. This is a mathematical audit of the package's scope,
not a Lean-formalized geometric instance or a Hodge counterexample.

The research-only
[`RegularPairGeometryControls.lean`](RegularPairGeometryControls.lean)
tests separate algebraic controls in `Q[y][x]`: `A=(x), M=(y)` admit the
pair `f=x,g=y`, but the bad choice `f=xy` admits no regular `g in M`.
The generic obstruction is cancellation in a domain: for `a != 0` and a
nonunit `b`, every `g in (b)` kills the nonzero class of `a` modulo `ab`.
All eight diagnostic theorems and their enforced standard-axiom checks
pass without warnings; the full build passes with only the two existing
Challenge placeholder warnings. The controls do not construct boundary
ideals. Associated-prime avoidance is a source/API analysis, not another
proved theorem or a supplied geometric witness. The unchanged historical
verification inventory was not rerun, and the unchanged manuscript/PDF
was not rebuilt for this research checkpoint.

**SP70: finite affine models and the full-visible branch.** The user
selected the finite etale route first. Construct the existing
`NormalizedCover` from supplied finite normal affine algebras with the
marked fraction fields, by proving that the canonical normalization map
is an equivalence and transporting finiteness. Use the whole intermediate
model as the visible scheme, with etaleness transported from its affine
algebra. Surjective `j.base` makes every conjugate boundary empty; without
perfectness or separability, the existing core-free sheet action makes
`J_mov(I)=J_fm(I)=top` for nontrivial `I`, so separation follows directly.
There is no need to choose a regular pair or prove uniform trace landing
for this branch. The single manuscript has matching propositions;
its 71-page PDF build, warning scan, visual checks and independent
Lean--TeX review pass. The full Lean build passes (3163 jobs), with only
the two expected unchanged Challenge placeholder warnings. Twenty focused
regressions and enforced standard-axiom audits for all seventeen new
declarations pass without warnings, as does the fresh unchanged
dependency audit. The centralized inventory has 798 checks, 565 examples
and 690 reports after appending seventeen checks and reports; its unchanged
historical prefix was not rerun in full.

**SP71: the actual whole inverse-image affine chart.** For a finite
morphism `p:Y -> X` and affine open `U`,
[`FiniteAffineChart.lean`](../HodgeConjecture/Boundary/Normalization/FiniteAffineChart.lean)
uses `B_U=Gamma(X,U)` and `A_U=Gamma(Y,p^-1 U)` with their actual section
map. It derives finiteness of `A_U`, and etaleness when `p` is etale,
without normality, integrality or nonemptiness assumptions.
[`AffineEtaleAlgebra.lean`](../HodgeConjecture/Boundary/Normalization/AffineEtaleAlgebra.lean)
also proves the general affine smooth/etale chart bridge. For integral
`Y` and a nonempty inverse image,
[`AffineNormality.lean`](../HodgeConjecture/Boundary/Normalization/AffineNormality.lean)
derives normality of `A_U` from explicit normality of its actual stalks.
Using the actual `Y.functionField`, the whole inverse-image open subscheme
is canonically isomorphic to the normalization of `B_U`, with the
structural equality proved over the original `X`. The normalization is
finite and, when `p` is etale, etale. No new ring, field or cover package
replaces these objects. The 72-page PDF build, warning scan, visual checks
and independent Lean--TeX review pass. The full build passes (3174 jobs;
only the two expected unchanged Challenge warnings). Eighteen focused
regressions and eleven enforced standard-axiom audits pass without
warnings. The SP70 rerun passes twenty regressions and seventeen audits;
the fresh unchanged dependency audit passes six endpoint contracts and
two support reports. The central inventory now has 809 checks, 565
examples and 701 reports after appending eleven checks and reports;
its unchanged historical prefix was not rerun in full.

**SP72: the actual generic extension.**
[`FunctionFieldMap.lean`](../HodgeConjecture/Cycles/FunctionFieldMap.lean)
constructs `functionFieldMapOfDominant` from the actual generic stalks of
integral schemes. It is injective, commutes with section germs on every
nonempty base open, satisfies identity and contravariant composition,
and equals the existing open-immersion isomorphism where applicable.
Nonempty inverse images use only dominance; generic-point preservation
uses irreducibility rather than integrality.
[`FiniteFunctionField.lean`](../HodgeConjecture/Boundary/Normalization/FiniteFunctionField.lean)
derives the scalar tower on every nonempty open. For a finite dominant
morphism the actual finite section algebra localizes to a finite extension
of the existing function fields. The global endpoint chooses a nonempty
affine chart internally, with no normality, etaleness, Noetherianity or
separately supplied field-extension premise. The 72-page PDF build,
warning scan, visual checks and independent core/manuscript review pass;
the full build passes (3176 jobs; only the two expected unchanged Challenge
warnings). Eighteen focused regressions and eleven enforced standard-axiom
audits pass without warnings. The fresh SP71 rerun passes eighteen
regressions and eleven audits; the fresh unchanged dependency audit
passes six endpoint contracts and two support reports. The central
inventory has 820 checks, 565 examples and 712 reports after appending
eleven checks and reports; its historical prefix is unchanged and was
not rerun in full.

**SP73: separability for the same actual embedding.**
[`SeparableFunctionField.lean`](../HodgeConjecture/Boundary/Normalization/SeparableFunctionField.lean)
implements the localization route. A dominant affine formally unramified
morphism of integral schemes induces a formally unramified algebra on
the actual function fields. The chart theorem uses a nonempty affine
base open; the global theorem chooses one internally. For finite `p`,
SP72 supplies finite-dimensionality and hence essential finite type, so
the same algebra is separable. Etaleness supplies scheme formal
unramifiedness automatically. No normality, perfectness or characteristic
zero is required. The full build passes (3177 jobs), with only the two
expected unchanged Challenge warnings. The fresh SP72 rerun passes
eighteen examples and eleven enforced standard-axiom audits, and the
fresh unchanged dependency audit passes six endpoint contracts and two
support reports. The 73-page PDF build, warning scan and visual checks
pass. Sixteen focused SP73 regressions and three enforced standard-axiom
audits pass. The central inventory now has 823 checks, 565 examples and
715 reports after appending three checks and reports; its historical
prefix is unchanged and was not rerun in full.

**SP74: construct the marked finite normal closure.**
[`NormalClosureConstruction.lean`](../HodgeConjecture/Boundary/Normalization/NormalClosureConstruction.lean)
constructs the existing `NormalClosureData K L N` from `FiniteDimensional K L`,
with `N=IntermediateField.normalClosure K L (AlgebraicClosure L)`.
Its marking is the original inclusion of `L` into that algebraic closure,
as proved by the embedding formula. Independently of this particular
construction, any supplied normal-closure datum of a separable `L/K`
gives separability of `N/K` and hence `IsGalois K N`; perfectness of `K`
is not required.
[`FunctionFieldNormalClosure.lean`](../HodgeConjecture/Boundary/Normalization/FunctionFieldNormalClosure.lean)
constructs this datum for the actual generic embedding of a finite
dominant morphism of integral schemes. Formal unramifiedness of the
morphism supplies separability and Galoisness, so finite etale morphisms
qualify. The full build passes (3179 jobs; only the two expected unchanged
Challenge warnings), as do the fresh SP73 rerun (sixteen regressions and
three enforced audits) and unchanged dependency audit (six endpoint
contracts and two support reports). The 74-page PDF build, warning scan,
visual checks and independent core/scheme/manuscript review pass;
twenty-two focused SP74 regressions and seven enforced standard-axiom
audits also pass. The central inventory now has 830 checks, 565 examples
and 722 reports after appending seven checks and reports; its historical
prefix is unchanged and was not rerun in full.

**SP75: consume local separability and remove unnecessary assumptions.**
Fourteen fixed-field, invariant-ring, selector/tensor and trace/pole
declarations now use explicit `Algebra.IsSeparable K L`. Core-freeness
and eleven full-visible/inertia/sheet/projector consumers lose their
perfect-field hypotheses without any separability replacement. The two
SP74 generic separability/Galois lemmas move, with unchanged names, into
`NormalClosure.lean`; `NormalClosureData.isGalois` remains the sole
perfect-field compatibility wrapper. Its proof delegates to the local
separability result. These are 26 signature generalizations, two moved
declarations and one wrapper-proof change, not new library declarations,
objects or axioms.
All other geometric hypotheses, including formal unramifiedness, finite
models and purity inputs where present, are retained. The new consumer
suite passes 24 regressions and 29 enforced standard-axiom audits;
the trace and pole suites pass 14/11 and 12/9. Fresh SP74 and
finite-affine-cover reruns pass 22/7 and 20/17. The central inventory
has 859 checks, 565 examples and 751 reports after appending 29 checks
and reports; its historical prefix is unchanged and was not rerun in
full. The 74-page PDF (785575 bytes) passes its build, warning scan and
visual checks, and independent Lean--TeX review passes. The full build
passes (3179 jobs; only the two existing Challenge placeholder warnings).
The fresh unchanged dependency audit passes six endpoint contracts and
two support reports.

**SP76: finite normal-closure normalization and the actual affine cover.**
`FiniteNormalClosure.lean` derives
`Module.Finite B (normalizedCoordinateRing B E)` for a finite separable
extension of the fraction field of normal Noetherian `B`. Specializing
to the existing marked normal closure removes the independently supplied
second finite normal algebra `S`: one finite normal intermediate model
constructs the existing `NormalizedCover`, with full-visible separation.
For an actual finite dominant formally unramified morphism of integral
schemes, the same construction uses the actual inverse-image open of a
nonempty affine base chart, its existing normalization isomorphism and
the constructed function-field normal closure. Base-chart normality
and Noetherianity and normal stalks on that inverse image are explicit.
Etaleness supplies formal unramifiedness; there is no perfectness, dimension-one
or Dedekind premise, new carrier, cover package or source axiom.
The full build passes (3180 jobs; only the two existing Challenge
placeholder warnings). The new suite passes 23 examples and seven enforced
standard-three axiom audits; fresh consumer, affine-chart and normal-closure
reruns pass 24/29, 18/11 and 22/7. The central inventory has 866 checks,
565 examples and 758 reports after appending seven checks and reports;
its historical prefix is unchanged and was not rerun in full. The
74-page PDF (788608 bytes) passes its build, warning scan and visual
checks; independent code and Lean--TeX reviews pass. The fresh unchanged
dependency audit passes six endpoint contracts and two support reports.

**SP77: finite tensor source and marked evaluations.**
`FiniteTensorProduct.lean` proves finiteness and etaleness for the existing
finite-index tensor product of copies of a finite etale algebra, including
the empty index case. `NormalClosureTensor.lean` uses all embeddings
`Σ=Hom_K(L,N)` to construct `ev_K:P_K -> N`, where `P_K=⊗_{Σ,K} L`.
Every conjugate field lies in its algebraic range, so the given
normal-closure property proves surjectivity without adding a premise.
Its actual kernel `m` is maximal and `P_K/m ≃_K N` commutes with evaluation.
Neither the evaluation nor this surjectivity proof needs separability.

`NormalizationTensor.lean` restricts the same embeddings to the existing
integral closures, giving `ev_B:P_B -> IntCl_B(N)` for
`P_B=⊗_{Σ,B} IntCl_B(L)`. It proves the factor formula and agreement with
`ev_K` on integral pure tensors after inclusion into `N`. An actual finite
normal etale intermediate algebra with fraction field `L` makes this
integral tensor source finite and etale. The source, target, field marking
and scalar maps are not replaced by supplied objects. All 17 new APIs
compile; the two source-property theorems omit four unused base/target
scalar assumptions. The central inventory is 883 checks, 565 examples
and 775 reports after appending 17 checks and reports; its historical
prefix is unchanged and was not rerun in full. The 76-page PDF (805454
bytes) passes its build, warning scan and visual checks; independent code
and Lean--TeX review pass. The full build passes (3187 jobs; only the two
existing Challenge placeholder warnings). The new suite passes 28
examples and 17 enforced standard-three axiom audits without warnings.
Fresh SP76 and SP74 reruns pass 23/7 and 22/7, respectively: 73 examples
and 31 audits in these three suites. The fresh unchanged dependency audit
passes six primary endpoint contracts and two support reports.

**SP78: canonical tensor base change and the full evaluator square.**
`PiTensorBaseChange.lean` constructs finite-index tensor base change and
factorwise algebra congruence on the existing carriers, with factor and
pure-tensor formulas. `NormalizationBaseChange.lean` first identifies
`K⊗_B IntCl_B(L)` with `L` from fraction-field localization, algebraicity
and compatible scalar towers. It requires neither base normality nor
Noetherianity, separability or finite degree. Applying this comparison
factorwise constructs `β_Σ:K⊗_B P_B ≃_K P_K`. Its full evaluator equality
is `ev_K∘β_Σ=β_N∘(1_K⊗ev_B)`, where `β_N` is the corresponding
one-factor comparison for the same marked `N`. This strengthens the
earlier pure-tensor formula to equality of algebra homomorphisms. No
surjectivity, factor selection or replacement field/map is supplied as
an assumption. The three existing evaluation helpers move unchanged to
`FiniteTensorProduct.lean`. The central inventory is 896 checks, 565
examples and 788 reports; its historical prefix is unchanged and was not
rerun in full. The 76-page PDF (812185 bytes) passes its build, warning
scan and visual checks. Both new leaves compile without warnings. The
focused suite passes 25 examples and 13 enforced standard-three axiom
audits, including three actual function-field cases. The full build passes
(3189 jobs; only the two existing Challenge placeholder warnings).
Fresh SP77, SP76 and SP74 reruns pass 28/17, 23/7 and 22/7, respectively:
98 examples and 44 enforced axiom audits across the four suites. The fresh
unchanged dependency audit passes six primary endpoint contracts and two
support reports.

**SP79: the selected generic evaluation factor.**
`ReducedArtinianFactor.lean` constructs the factor selected by any
surjective algebra map from a reduced Artinian algebra to a field.
`NormalClosureFactor.lean` specializes it to the existing `ev_K`:
finiteness of `P_K` follows without separability, while separability of
`L/K` makes `P_K` etale and hence reduced Artinian. The resulting
`Φ_m:P_K ≃_K N × Q_m`, with `Q_m` the product over the other maximal
ideals of their residue quotients, satisfies `pr₁∘Φ_m=ev_K` as algebra
homomorphisms. The element `e_m=Φ_m⁻¹(1,0)` is idempotent and satisfies
`ev_K(e_m)=1`, `e_m*x=0 ↔ ev_K(x)=0`, and `m=(1-e_m)`.
Value one and kernel annihilation characterize it uniquely, without
assuming idempotence separately. No selected factor, field map or
surjectivity is supplied as a new hypothesis. There is no asserted
unital section `N -> P_K` and no new Chow projector. Both leaves compile
without warnings; the full build passes 3195 jobs with only the two
existing Challenge warnings. The focused suite and four fresh neighbor
suites pass 123 examples and 60 enforced standard-three axiom audits.
The fresh unchanged dependency audit passes six primary endpoint
contracts and two support reports. The PDF and independent
mathematical/Lean--TeX reviews pass; see
the SP79 parity-queue entry for the complete validation record.

**SP80: the actual integral evaluation factor.**
`SeparabilityTrace.lean` contracts a central separability tensor by the
field trace. `UnramifiedIntegralFactor.lean` combines this identity with
the existing unramified section and integral trace over normal `B`.
For `f:S -> T=IntCl_B(N)`, with `S/B` formally unramified and essentially
of finite type and `N/K` finite, it constructs a `B`-linear map `r`
satisfying `r(f(s)*t)=s*r(t)`. If the image of `S` spans `N` over `K`,
the trace calculation gives `f∘r=id`. Consequently `E=r(1)` is
idempotent, `f(E)=1`, `E*s=0 ↔ f(s)=0`, and `ker(f)=(1-E)`.
Neither normality nor flatness of `S` is assumed.

For the existing marked evaluation, the new
`normalizationTensorEvaluation_span` derives this spanning condition
from SP78's evaluator square and the existing generic surjectivity.
`NormalizationIntegralFactor.lean` specializes to the actual finite
normal etale intermediate model with fraction field `L`, constructing
`r_B` and `E_m` inside `P_B`. Its quotient equivalence
`P_B/(1-E_m) ≃_B IntCl_B(N)` preserves `ev_B` on every representative.
The normalization is finite as a quotient of the finite tensor source;
the kernel formula identifies it with localization away from `E_m`,
so etaleness follows by localization and composition. Separability is
used only for comparison with SP79's selector:
`β_Σ(1⊗E_m)=e_m`. No Noetherian-base or integral-surjectivity premise,
new carrier, field marking, or geometric input package is added.

The proposed proof of integral-closedness of all `P_B` inside `P_K` is
bypassed, not proved. Constructing the actual integral selector and
identifying its quotient directly suffices for this factor. The source
reference, Stacks Lemma 10.151.4, Tag 02FL, concerns the unramified
diagonal localization/separability tensor; the trace-section construction
and normalization comparison are direct project proofs. All 28 APIs
compile without warnings; the 3198-job full build passes with only the
two unchanged Challenge warnings. The focused suite and five fresh
neighbors pass 153 examples and 88 enforced standard-three axiom audits.
The unchanged dependency audit passes six primary contracts and two
support reports. The central inventory is 940 checks, 565 examples and
832 reports; its historical prefix is unchanged and was not rerun in
full. The 79-page PDF (826296 bytes), eight-page visual review and
independent mathematical/Lean--TeX reviews pass. The SP80 parity-queue
entry records the complete validation.

The focused suite passes the ring-level specialization to an actual
finite etale affine inverse image, deriving both section-ring normality
inputs from normal stalks without Noetherianity.

**SP81: the actual finite etale affine refinement.**
`FiniteEtaleNormalClosure.lean` constructs the existing `NormalizedCover`
for a finite dominant etale morphism `p:Y -> X` of integral schemes and
a nonempty affine chart `U`. The same constructed function-field normal
closure supplies the marking. The visible scheme is the actual
`V=p⁻¹U`, through its existing normalization isomorphism. Normal stalks
on both opens give normal section rings; no Noetherianity is assumed.
The normalization structural maps to `Spec Γ(X,U)` and the actual `U`
are finite etale. The constructed refinement to `V` is finite etale,
recovers the marked normalization leg, factors the structural map through
`p|_U`, and has the original composite over `X`. Full visibility gives
boundary separation for this actual cover.
Both maps are surjective by lying over for the actual injective integral
normalization maps. Chart surjectivity requires only dominant `p`,
integral schemes and the nonempty affine chart; it needs neither finite
nor etale `p` nor either normal-stalk premise. Refinement surjectivity
uses finite dominant `p` and normal stalks on `V`, with no etale or
base-normality premise. Finite-etale conclusions retain both normal-stalk
hypotheses.

The pinned library does not provide the general converse from algebraic
to scheme etaleness. `piTensorProduct_ringHomProperty` therefore transports
any ring-map property stable under isomorphism, identity, composition and
base change through the existing finite tensor source.
`EtaleTensorSource.lean` applies it to the local standard-smooth
presentations defining scheme etaleness. SP80's actual complementary
idempotent then makes `Spec(ev_B)` an open immersion, so composition
gives the required scheme-etale normalization. The actual intermediate
scheme supplies these presentations; no new converse theorem is assumed.
All 19 APIs compile without warnings in the 2761-job scoped build:
seventeen in `FiniteEtaleNormalClosure.lean` and two tensor helpers. The 81-page PDF
(831678 bytes), its final warning/reference/box scan, five-page visual
review and independent geometry/Lean--TeX review pass. The focused suite
passes 25 examples and 19 enforced standard-three axiom audits without
warnings. Five fresh neighbor suites also pass; the six suites total
146 examples and 89 enforced audits, with no warnings or errors. The
full build passes 3200 jobs with only the two unchanged Challenge
warnings. The unchanged dependency audit passes six primary contracts
and two support reports. All nineteen API parity checks pass. The static
central inventory is 959 checks, 565 examples and 851 reports; its
historical prefix is unchanged and the historical file was not
re-elaborated. The SP81 parity-queue entry records the complete validation.

**SP82: same-ambient localization and actual affine restriction.**
The 17 generic APIs in `NormalizationLocalization.lean` construct the
same-element map `rho^E_{B,C}:IntCl_B(E) -> IntCl_C(E)`, its injectivity,
strict identity/composition and ambient-map naturality. For a compatible
localization `B -> C`, its target is the corresponding localization and
`C tensor_B IntCl_B(E)` is canonically equivalent to `IntCl_C(E)`, with
the original scalar/inclusion formula. Contravariant `j^E=Spec(rho)`
has the structural, naturality and identity/composition equalities.
The open-immersion/range endpoints are principal-localization only;
arbitrary multiplicative-set localization is not claimed to be open.

The nine APIs in `AffineNormalizationRestriction.lean` derive scalar
towers from actual section restriction/germ maps, construct the existing
model's restriction and its structural squares, prove principal-open
localization/open immersion, and prove naturality of the whole-preimage
normalization isomorphism. The two APIs in
`FiniteEtaleNormalClosureRestriction.lean` give the actual structural
and marked-refinement squares for any nonempty affine `W <= U`, not
only principal opens. They retain the same normal closure and marking.
The structural square needs dominant `p`; the refinement square adds
finite `p` and normal stalks on its inverse images. Neither needs
etaleness, base normality or Noetherianity.

All 28 APIs compile without warnings in the 2764-job scoped build. The
focused suite passes 39 examples and 28 enforced standard-three axiom
audits. Three fresh neighbor suites also pass; the four suites total
107 examples and 71 audits, without warnings or errors. The full build
passes 3203 jobs with only the two unchanged Challenge warnings. The
unchanged dependency audit passes six primary contracts and two support
reports. All 28 API parity checks and independent review pass. The
81-page PDF (835379 bytes) has a clean final log and visual checks of
pages 13, 14, 61, 62, 73, 74 and 81. The static central inventory is
987 checks, 565 examples and 879 reports; its historical prefix is
unchanged and was not re-elaborated in full. The SP82 parity-queue entry
records the complete validation.

**SP83: coherent actual affine inverse-image opens.**
The seven APIs in `AffineNormalizationCoherence.lean` prove identity,
composition, common-refinement diamonds, compatibility over the original
`X`, and the principal/equal-principal range adapters. The three APIs in
`AffineNormalizationOpenImmersion.lean` prove pointwise injectivity,
open immersion and the exact range for any nested nonempty affine opens:
`range(j^N_{W,U}) = mu_U^-1(W)`. The existing normalization models and
germ-derived ambient scalars are unchanged. Common principal neighborhoods
in both charts supply the proof, with no separatedness, affine-intersection,
finite-degree, normality or Noetherianity premise. The scoped build passes
2740 jobs without warnings.
SP83 is validated: the focused suite passes 21 examples and ten exact
standard-three axiom audits. With the unchanged SP82 and SP81 suites,
the total is 85 examples and 57 audits, all clean. The full build passes
3205 jobs with only the two existing Challenge placeholder warnings;
the unchanged dependency audit passes six primary contracts and two
support reports. The 83-page PDF (839977 bytes), final log, seven-page
visual review and all ten API parity checks pass. The static central
inventory is 997 checks, 565 examples and 889 reports; its historical
prefix is unchanged and was not re-elaborated in full.

**SP84: the actual locally directed diagram and glued scheme.**
`AffineNormalizationDiagram.lean` uses the inclusion-ordered subtype
`NonemptyAffineChart X`, retaining nonemptiness from each original open.
The existing `Z_U` and actual restrictions form `F_N`; their original
maps to `X` form `c_N`. The open-immersion and exact-range endpoints
feed a direct proof of `(F_N comp Scheme.forget).IsLocallyDirected`:
equal images in an upper chart lift through one common principal
neighborhood in the two base charts. No global upper affine chart is
required, and intersections need not be affine.

`GluedNormalization.lean` constructs `Z_N = colimit F_N`, canonical
open immersions `jmath_U : Z_U -> Z_N` forming an open cover, and the
descended `mu_N : Z_N -> X`. It proves the exact structural formula
`mu_N jmath_U = mu_U`, transition naturality, equality of chart points
if and only if they lift from a common smaller chart, and chartwise
extensionality of morphisms out of `Z_N`. These 16 public APIs retain
integral `X` and the fixed extension of its original function field;
normality, finite degree, Noetherianity and separatedness are not added.
No source axiom or replacement local normalization is introduced.

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

**SP85: the actual global inverse-image chart comparison.**
`GluedNormalizationChart.lean` proves
`range(jmath_U) = mu_N^-1(U)` as sets and as opens of the glued scheme.
For the reverse inclusion, lift a global point through the original
chart cover, choose a common principal neighborhood in that base chart
and `U`, and use the SP83 transition range and SP84 naturality to lift
the point into `Z_U`. The forward inclusion is the exact structural
formula. Thus the comparison uses actual geometric overlaps rather
than a section-ring model of a possibly non-affine intersection.

The canonical open-immersion isomorphism then gives
`e_U : Z_U ~= mu_N^-1(U)` as schemes. Both inclusion formulas,
the exact restricted structural map to `U`, and compatibility with
every smaller affine chart are proved. These seven APIs keep integral
`X`, the original fixed function-field extension, normalization carriers
and germ-derived scalar maps; they add no finite-degree, normality,
Noetherianity or separatedness premise. The manuscript counterpart is
`prop:normalization-global-chart`.

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

**SP86: target-local properties and the actual finite-etale global map.**
`GluedNormalizationProperties.lean` proves that the actual nonempty
affine opens cover every scheme, including the empty scheme. For a
target-local morphism property `P`, SP85's exact isomorphism and
structural formula identify `P(mu_N)` with `P(pi_U)` for every original
chart map `pi_U : Z_U -> U`. This proves `IsAffineHom mu_N` for integral
`X` and any fixed extension of its original function field, without a
finite-degree, normal-base, Noetherian or separatedness premise.
Finiteness and scheme etaleness are each equivalent to the respective
property of these exact chart maps.

`FiniteEtaleGluedNormalClosure.lean` then specializes to an actual
dominant finite etale `p : Y -> X`, with integral `X` and `Y` and
explicit integrally closed stalks on both. SP81 supplies the chart
properties for the original marked normal closure
`N_p = normalClosure K(X) K(Y) (AlgebraicClosure K(Y))`; the target-local
equivalences prove that the already constructed `mu_(N_p)` is finite
etale. Its field map remains the actual map induced by `p`. No
Noetherian or perfect-field premise, source axiom, or new geometric
hypothesis package is added. The six APIs correspond to
`prop:normalization-target-local` and
`cor:normal-closure-global-finite-etale` in the manuscript.

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

**SP87: descent of the original marked refinement.**
`GluedNormalClosureRefinement.lean` uses the actual chart refinements
`lambda_U : Z_U -> p^-1(U)` and their proved restriction square to
form a cocone to `Y` for the existing normalization diagram. Colimit
descent gives the actual `lambda : Z_(N_p) -> Y`, with its exact marked
chart formulas and the global triangle `lambda` followed by `p`
equals `mu_(N_p)`. Chart extensionality proves uniqueness for maps
with the same marked chart formulas; the triangle over `X` alone does
not identify the marked refinement.

The five APIs assume integral `X` and `Y`, finite dominant
`p : Y -> X`, and explicitly integrally closed stalks of `Y` only.
They do not assume etaleness of `p`, normal stalks of `X`, Noetherianity
or perfectness. The original marked normal closure, actual chart
carriers and germ-derived scalar maps are retained. No new source
axiom or geometric hypothesis package is added. The manuscript
counterpart is `prop:normal-closure-marked-refinement`.

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

**SP88: finite etaleness of the same actual marked refinement.**
`FiniteEtaleGluedRefinement.lean` proves a generic finite-cancellation
theorem: for composable scheme maps `f` and `g`, finiteness of the
composite and separatedness of `g` imply finiteness of `f`. The right
map need not be finite, and this generic theorem has no integral,
normality, Noetherian or field hypotheses.

The second API applies that theorem to the existing
`lambda : Z_(N_p) -> Y`. For dominant finite etale `p : Y -> X` between
integral schemes, with explicitly integrally closed stalks on both,
SP86 proves finite etaleness of `mu_(N_p)` and SP87 proves the exact
triangle `p lambda = mu_(N_p)`. Finiteness of `p` supplies separatedness,
so finite cancellation proves `lambda` finite. Standard etale
cancellation proves it etale. No charts or carriers are replaced and
no gluing is repeated. The manuscript counterpart is
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

**SP89: surjectivity of both original global maps.**
`GluedNormalizationSurjectivity.lean` proves surjectivity of
`mu_N : Z_N -> X` for integral `X` and any field extension `N` of its
original function field. On each actual nonempty affine chart, the
original scalar map into the integral closure is injective and
integral. Lying over proves the chart map surjective, and SP86's
target-local comparison proves the global result. Algebraicity or
finite degree of `N`, normality of `X`, Noetherianity and separatedness
of `X` are not required.

The second API proves surjectivity of the original marked
`lambda : Z_(N_p) -> Y` for finite dominant `p : Y -> X`, integral
`X` and `Y`, and explicitly integrally closed stalks of `Y` only.
For a point of `Y`, take an actual affine neighborhood of its image
in `X`, use SP81's surjective refinement into that entire inverse
image, and apply SP87's exact marked chart formula. This is a direct
point lift, not cancellation of surjectivity from `p lambda`.
No etaleness or normal-stalk hypothesis on `X` is used.

The two scopes are kept distinct in
`prop:normalization-global-surjective`. With SP86/SP88's stronger
finite-etale and normal-stalk hypotheses, both original global maps
are finite etale and surjective. The field, maps, normalization
carriers and germ-derived scalars remain unchanged; there is no new
source axiom or geometric input package.

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

**SP90: compatible actions on the same glued normalization.**
`GluedNormalizationAction.lean` begins with the existing affine
`Spec(sigma^-1)` convention. For integral `X` and an arbitrary field
extension `N/K(X)`, the chart automorphisms commute with the actual
restriction maps and form a natural automorphism of the original
diagram. Descent to its same colimit gives the global automorphism,
its exact chart formula, compatibility over `X`, identity and
multiplication laws, and the homomorphism
`Aut_(K(X))(N) -> Deck(mu_N)`. No algebraicity or separability is
required to construct this action.

`GluedNormalClosureAction.lean` uses the original marked normal
closure for finite dominant `p : Y -> X`, integral `X` and `Y`,
and explicitly integrally closed stalks of `Y` only. If a field
automorphism fixes the marked `K(Y)`, its inverse does too. The
original marked affine ring formula and cancellation of the existing
affine chart isomorphism prove compatibility with each refinement
chart; global chart extensionality proves compatibility with
`lambda`. This does not cancel `p` from the triangle. The fixing
subgroup therefore maps into `Deck(lambda)` with the same underlying
global automorphisms as its action over `X`.

These are 15 APIs, with manuscript counterparts
`prop:normalization-global-action` and
`prop:normalization-marked-action`. The marked theorem needs no
etaleness, normal-stalk input on `X`, separability, Noetherianity or
perfectness. No carrier, marking, scalar map, source axiom or new
geometric hypothesis package is introduced.

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

**SP91: normal local rings of the same glued normalization.**
Four APIs in `GluedNormalizationNormality.lean` prove integral closedness
of `IntCl_B(N)`, integral closedness of its actual affine stalks, and
domain plus integral closedness for every actual stalk of `Z_N`.
The affine result permits any commutative `B` mapping to a field `N`.
The global result permits integral `X` and any extension `N/K(X)`.
The fraction field of the integral closure embeds in `N`; equality
with `N` is not required or claimed. Localization gives the affine
stalk result, and the original chart open immersions identify these
local rings with all global stalks.

No algebraicity, finite degree, separability, base normality,
Noetherianity, separatedness or new geometric input package is used.
The same colimit scheme, original germs, chart carriers and marked
fields are retained. The manuscript counterpart is
`prop:normalization-global-normal`. Normality is expressed by local
domains that are integrally closed, without a new scheme `IsNormal`
class or a global `IsIntegral` assertion. For the original `N_p`, no
normal-stalk premise on `X` or `Y` is needed for this conclusion.

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

**SP92: integrality of the same glued normalization.**
Four APIs in `GluedNormalizationIntegrality.lean` prove pairwise
intersection of original chart images, global reducedness, global
irreducibility and the `IsIntegral` instance. Actual nonempty common
affine refinements witness the overlaps. Each chart is integral,
and its irreducible open image belongs to the original covering family.
The overlaps force irreducibility; nonemptiness comes from a base
chart. SP91's domain stalks give reducedness and hence integrality.

The manuscript counterpart is `prop:normalization-global-integral`.
Integral `X` and arbitrary `N/K(X)` suffice, without algebraicity,
finite degree, separability, base normality, Noetherianity or
separatedness. The same carriers, germs, chart maps and marked field
remain fixed. The original `N_p` specialization needs no normal-stalk
premise on either scheme. The intrinsic function field is available;
its marked comparison with the ambient field remains separate.

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

**SP93: marked function-field comparison and action faithfulness.**
The checkpoint has 19 public APIs across four production modules.
For integral `X` and finite `N/K(X)`, the original affine integral
closures have fraction field `N`. Actual open-immersion generic-stalk
maps give a chart-independent comparison `e : K(Z_N) ≃ N`, preserving
the existing structural field embedding. The existing inverse-ring
action has pullback formula `e(a_sigma^* b) = sigma^{-1}(e(b))`;
surjectivity of `e` gives faithfulness. This checkpoint does not identify
`K(Z_N)` with arbitrary transcendental ambient extensions.

For the original marked normal closure of finite dominant `p : Y -> X`,
integral `X/Y` and normal stalks of `Y` suffice to compare the actual
`lambda` pullback with the original `D.embedding`. No normality of `X`,
etaleness, separability or Noetherianity is used. The new modules are
`GluedNormalizationFunctionField.lean`,
`GluedNormalizationFunctionFieldAction.lean` and
`GluedNormalClosureFunctionField.lean`, with generic-stalk support in
`Cycles/FunctionFieldComparison.lean`. The manuscript counterparts are
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

**Next bounded bridge:** reconstruct arbitrary deck transformations and
compare the full deck group. Fiber comparison and Galois-cover or torsor
identification remain separate.
The fixing-subgroup result is sufficient for preservation of `lambda`,
not an equality with its full stabilizer. Normal
stalks from smooth geometry and Chow--Betti generation are separate. The older
SP76 constructor retains its stronger assumptions; SP81 removes its
Noetherian-base requirement. SP84 supplies the locally directed gluing,
and SP85 identifies its original charts with the actual global inverse
images. SP86 transfers the properties and proves finite etaleness of
the actual normal-closure map with its explicit normal-stalk inputs.
The main target is unchanged. Nonempty-boundary geometry remains an
alternative if needed; Chow--Betti generation and convolution compatibility
remain separate.

In the separate localization stream, the next bounded checkpoint is L1's
actual closed-complement cycle kernel/image comparison. It can run alongside
the boundary-section construction when it has a named consumer; additive localization
is not a prerequisite for every
direct geometric projector construction. L2 and L3 then address relation
lifting and quotient exactness. None of these checkpoints replaces the
prescribed-class action/generation argument or supplies a reduction from
the full Hodge conjecture to abelian varieties.

## Current proof roles

There is no completed general Hodge proof spine whose missing geometry can
be supplied by a change of linear coordinates. The library has distinct
roles:

| Component | What is established | What it does not establish |
| --- | --- | --- |
| Local normalization and inertia | Selected fixed-ring descent from explicit unramifiedness; conditional codimension-one separation | General compactification or Chow-projector existence |
| Correspondence mechanisms | Span and group/Hecke algebra identities; projector consequences of supplied graph maps | The general graph-to-Chow algebra maps and their action on a prescribed class |
| Graph geometry and integral cycles | Actual graph intersection/image, generic multiplicity one, relative graph-slice cycle pull–push with degree-one outer image, and open restriction for a supplied finite étale extension | General component multiplicities, absolute Chow intersection/convolution/descent, or a target cohomological action |
| Block, shear, and one-idempotent calculations | Coordinate identities and faithful reformulations of one operator square | Algebraicity of the vector used to define that operator |
| Finite split geometry | Actual Chow, degree-zero Betti/Hodge data, and the marked action comparison for the canonical generated class | Non-split/positive-dimensional realization or arbitrary-class Galois coverage |
| Selected source-input packages | Conditional cover/action extension and boundary-image defects | Their geometric instantiation, multiplicative restriction, or defect vanishing |

For a genuine Chow/Betti model, the primary construction target is an
actual cycle whose Betti class is the prescribed Hodge class. The marked
correspondence route can achieve this through geometric lower-left
detection. Alternatively, a constructed Chow-valued map `r_CH` with
`θ = cl ∘ r_CH` and proved `θ(a_H) = α` supplies `r_CH(a_H)` directly;
no projector argument is then needed for that class conclusion. These maps
must come from geometry, not an assumed representative of `α`.
The generic class-dependent construction and the full geometric model
remain open. The surjective multiplicative residual route is constrained to
the negative unit and does not by itself provide arbitrary-class coverage.

The [proof-dependency/archive audit](working/0017-proof-spine-and-archive.md)
distinguishes actual proof calls, supporting APIs, and retired modules.
It supersedes the old planning outline in `archive/planning/`; the claim and
source ledgers remain the current theorem-level records.

## Classical target and formal model schema

### First concrete checkpoint: split points

The first concrete test now has connected geometric and coefficient parts:

- `Correspondence/Examples/SplitPoints.lean` constructs `Spec(k^I)` for finite
  `I`, proves its structure map finite, étale, and proper, and proves that
  each point-supported diagonal span is convolution-idempotent by its actual
  self-pullback isomorphism.
- `Realization/Chow/Examples/SplitPoints.lean` computes the two-point matrix
  coefficient action. With `q=(1,0)`, residual map `θ(0,b)=b`, and constant-unit
  coordinates `T(a,b)=(a,b-a)`, it proves `ρ(E₀₀)=P₋₁`, instantiates
  `MarkedProjectorActionComparison`, and derives the Palomar target square.

**The split-span-to-matrix arrow is now proved.**
`Realization/Chow/Examples/SplitSpanRealization.lean` constructs a surjective
rational algebra homomorphism on the free algebra of split-presentable
actual finite-étale span classes. It embeds this source into the existing
finite-étale free algebra. Actual scheme isomorphisms give presentation
independence, and an actual scheme fiber-product isomorphism proves the
multiplication law. Geometric coproducts map to sums and empty spans to zero.
`Examples/GeometricSplitPoints.lean` sends the original point projector to
`E₀₀` and derives its coefficient Palomar square from this geometric source.

**The exact additive quotient is now identified.**
`Examples/SplitSpanQuotient.lean` proves that the two-sided ideal
`J_sp` generated by finite point-decomposition differences equals `ker χ_sp`.
The actual finite indexed scheme-coproduct isomorphism is proved in
`Correspondence/Examples/SplitSpanDecomposition.lean`. Reduction to point-pair
normal form and matrix-unit independence give
`C_sp^add := C_sp / J_sp ≃ₐ[ℚ] M_I(ℚ)`. Empty and binary-coproduct defects
belong to this ideal; the generating family is finite indexed, not asserted
to be binary-only. The free source, additive quotient, and matrix target
retain distinct definitions.

**The actual integral generators and no-curves theorem are now proved.**
`Correspondence/Examples/SplitIntegralSubschemes.lean` classifies every
integral closed immersion into `Spec(k^I)` as the inclusion of a unique
reduced rational point, with a commuting scheme isomorphism. The canonical
ideal-sheaf subschemes are equivalent to the labels `I`.
`Examples/SplitPointDimension.lean` proves every closed subscheme has
topological Krull dimension at most zero, exactly zero when nonempty.
The coordinate-ring companion `CommutativeAlgebra/SplitFieldQuotient.lean`
classifies all primes as unique evaluation kernels with quotient `k`.

**The additive Chow group is now constructed.**
`Examples/SplitZeroCycles.lean` defines cycles as finitely supported
coefficients on the actual integral closed subschemes. In
`Examples/SplitRationalEquivalence.lean`, principal-divisor data consist of
an actual integral closed curve and a unit in its scheme function field.
The no-curves theorem makes that domain empty, so the generated
rational-equivalence relation submodule is zero. The quotient and its
point-coordinate equivalence give `CH_0(Z_I;R) ≃ₗ[R] (I → R)` for
`R = ℤ` and `R = ℚ`.
The scalar-extension equivalences for both cycles and Chow groups are
constructed; on Chow groups the map sends `q ⊗ [s_i]` to `q • [s_i]` and
identifies the rational group with `ℚ ⊗[ℤ] CH_0(Z_I;ℤ)`.

**Geometric Chow composition is now constructed.** Actual product and
point-fiber isomorphisms identify the relevant integral subschemes. The
scheme-theoretic image map restricts to an isomorphism on each point,
giving residue-field degree one. Actual fiber inclusions have module
length one over the ambient stalk. These computations construct proper
pushforward, flat pullback, external product, and diagonal-pullback
intersection on cycles and Chow classes. `SplitChowCorrespondence.comp`
uses `p13_* (p12^* a · p23^* b)`, and `matrixCoordinates_comp` proves the
matrix law with outputs in rows. The diagonal is the identity and
composition is associative.

**The actual Chow algebra is identified with the additive span quotient.**
`EndAlgebra` keeps Chow addition and scalars, uses the constructed
composition as multiplication, and uses the diagonal as its unit.
`matrixAlgEquiv` and `spanQuotientEquiv` are rational algebra equivalences;
the point-span class maps to its actual Chow point-pair class. The actual
class of any finite split span maps to the pair-map pushforward of its
carrier's fundamental cycle, by `spanQuotientEquiv_ofSchemeSpan`. The actual
action `p2_* (c · p1^* z)` has the matrix-vector coefficient formula and
respects composition.

**The degree-zero Betti cycle-class comparison is constructed.** Over `ℂ`,
the actual point space `Hom_ℂ-alg(ℂ^I,ℂ)` carries the topology induced by
regular-function evaluations. Prime-kernel classification gives its
evaluation-point bijection; Hausdorffness and finiteness prove discreteness.
The associated actual `Spec` morphisms commute with the complex base and
the scheme maps, and the product homeomorphism respects both projections.
Singular degree-zero cohomology is the kernel of the two-face coboundary
on actual continuous simplices. Its point evaluation equivalence constructs
`CH_0(Z_I;ℚ) ≃ₗ[ℚ] H_B^0(Z_I(ℂ);ℚ)` with the characteristic-cocycle
normalization. The map respects pushforward/finite transfer,
pullback, and intersection/cup product. The geometric cohomological action
`p2_* (cl(c) ∪ p1^*u)` intertwines the Chow action and has its matrix law.
The constructed `SplitBetti.realization` is an algebra homomorphism from
the actual Chow endomorphism algebra to `Module.End` of this singular
cohomology. `correspondenceAction` packages it in the existing interface.

**The finite Hodge/Tate-block comparison is constructed.** The actual
tensor complexification of singular degree-zero cohomology has its complex
point coordinates and canonical conjugation. The explicit effective
type-`(0,0)` bigrading satisfies directness, exhaustion, and conjugation;
the cited geometric degree-zero specialization identifies this as the
appropriate Hodge structure. Rational Hodge classes are defined as the
inverse image of its complex `(0,0)` piece, independently of cycle classes,
and only then proved to be the whole rational space.

For the actual scheme `Z_(Option I) ≅ Spec ℂ ⨿ Z_I`, the geometric Chow
encoding is `enc(z)=[(*,*)]+j_*z`, where `j(i)=(*,i)`; decoding is `j^*`.
The constructed Betti block coordinates identify its actual cohomology
with `ℚ(0) ⊕ H_B^0(X_I;ℚ)`. The encoding is idempotent, realizes the graph
of `cl(z)`, and is recovered by decoding. For every correspondence, the
cycle class of its decoded block is the lower-left class of its action.
The finite model therefore instantiates graph construction, detection,
Hodge compatibility, and the graph/Palomar target equivalences.

**The split marked-sheet residual and action comparison is constructed.**
For a finite group `G` and any subgroup `D`, the actual regular split
torsor has its graph-sheet collision decomposition and an actual finite
étale quotient-label map to `Z_(G/D)`. On the complement `I` of the marked
sheet, the residual ideal maps bijectively to actual Chow by the point-cycle
sum. Its multiplication is geometric intersection and its marked value
is `−[Z_I]`. Composition with cycle class gives the residual Betti map.

The fixed Tate-block action remains unchanged. Instead, the actual Chow
unit `U_z=1+j_*z`, with inverse `U_(-z)`, conjugates the marked point
projector to its graph encoding. For `z=−[Z_I]`, this realizes the
constant-marked sheet coordinates and proves the restriction-free
selector-action and Palomar squares for `−cl[Z_I]`.
The actual diagonal-then-shear embedding also intertwines full sheet
multiplication with the constructed Betti action.

**The next gap is class-dependent geometric coverage beyond that class.**
The split torsor has disconnected source when `G` is nontrivial and supplies
no field normal-closure datum. Its already proper geometry supplies no
nontrivial boundary extension.
Multiplicative residual rigidity is exact: the generated class satisfies
`α²=−α`, and a surjective multiplicative residual map forces `α=−1`.
Varying such maps alone cannot provide arbitrary target classes. The general
linear residual interface, class-dependent cover data, and non-split or
positive-dimensional realization/compactification comparisons remain
separate. The span realization still applies to split-presentable spans,
not to all finite-étale carriers over arbitrary fields.

The canonical `MarkedProjectorActionComparison` takes the chosen
correspondence directly and requires only the residual map and its action
square. Neither a full matrix ambient nor a restriction to commutative
sheets is required. The extension-based selector comparison is a lossless
specialization; the existing Galois coverage interface retains that extra
restriction and is not the general target. The narrow full-matrix diagnostic
is preserved on the object bench, outside the active proof and gap list.

See `working/0015-split-galois-marked-comparison.md` for the split torsor,
multiplicative residual map, actual Chow shear, and marked action square;
`working/0014-split-hodge-tate-block.md` for the independent Hodge data
and geometric graph construction/detection;
`0013` records the actual point topology,
singular cocycles, cycle class, and cohomological action;
`0012` records the geometric operations and composition;
`0011` records the cycle quotient, `0010` its actual
generators, and `0009` the exact additive span quotient.

### Selected literature inputs now have explicit packages

`HodgeConjecture/Inputs/` separates three source-known ingredients from their
still-open geometric applications. `FixedInertia.lean` owns the unchanged
canonical unramifiedness record. `FiniteEtaleExtension.lean` records an actual
extension and pullback isomorphism, assumes its existence separately, and
lifts deck actions only from bijectivity of the actual automorphism
restriction map. `ChowLocalization.lean` assumes selected rational-linear
exactness and surjectivity; it proves raw-lift existence and, with a separately
supplied algebra restriction, that every raw idempotence defect belongs to
the boundary image.

These are conditional consumers of selected source conclusions, not Lean
proofs of the full cited geometric theorems. Each instance still needs its
exact source-hypothesis and map identification. No source class is installed
globally, and the existing Palomar statements retain their Mathlib-only
explicit premises. See `working/0016-source-input-packages.md` (A11n / SP26).
The application-specific Chow-valued graph square, defect correction or vanishing,
prescribed action, and class-dependent coverage remain separate tasks.

### Closed graph subschemes and their restriction are constructed

[`GraphSubscheme.lean`](../HodgeConjecture/Correspondence/GraphSubscheme.lean)
constructs the actual graph morphism `SchemeCorrespondence.graphMorphism`
and its kernel ideal `graphIdeal`. Separatedness proves closed immersion;
`graphSubschemeIso` identifies its source with the resulting closed
subscheme. The graph morphism is proper as a map to the relative product.

For a supplied actual finite étale extension `E` over an open immersion,
[`GraphRestriction.lean`](../HodgeConjecture/Boundary/GraphRestriction.lean)
constructs the open map `E.pairInclusion` of relative products.
`E.graphRestriction_isPullback σ` proves that the graph of
`E.restriction σ` is the scheme-theoretic pullback of the graph of `σ`, and
`E.graphIdeal_restriction σ` identifies their actual ideal sheaves by
`IdealSheafData.comap`. Restricting an already extended automorphism needs
no `DeckExtensionHypothesis`; `graphIdeal_liftDeckAction` uses that
additional hypothesis only when lifting a prescribed original action.

This is the scheme-level part of the first geometric checkpoint (A11o),
not a construction of a geometric extension from purity.

### Integral graph cycles and open restriction

The canonical `SchemeCycles.Cycles W R` is now the finite, ungraded module
on actual integral ideal-sheaf subschemes. The finite split cycle types are
definitionally its specializations, not a second competing cycle object.
`SchemeCycles.openRestriction` uses actual comap subschemes and returns
zero for empty intersections; nonempty inverse images are proved integral.
It has identity and composition laws.

`SchemeCorrespondence.graphCycle` constructs a coefficient-one generator
when the source is integral and separated over its base. Its dimension
agrees with the source through `graphSubschemeIso`.
`graphCycleLinearMap` assembles rational weighted sums of these generators.
For an integral extended cover and nonempty original cover,
`FiniteEtaleExtension.graphCycle_restriction` and
`graphCycleLinearMap_restriction` prove the actual generator restriction
and equality of linear-map composites with the induced deck-group map.
No deck-extension bijectivity is used. This is A11p / SP31.

### Actual graph intersection and composite image

`Correspondence/GraphComposition.lean` constructs the actual relative
triple product and the sum of the two inverse-image graph ideals,
\(\mathcal J_{\sigma,\tau}=p_{12}^*\mathcal I_\tau+p_{23}^*\mathcal I_\sigma\).
Its subscheme is isomorphic to the source via
\(y\mapsto(y,\tau y,\sigma(\tau y))\). The restricted first/last projection
is an isomorphism onto the actual graph of \(\sigma\tau\), and the
scheme-theoretic image ideal is exactly that graph's ideal. Separatedness
is the only geometric premise; the order does not assume a commutative
deck group.

`Cycles/IntegralMultiplicity.lean` also proves generic length one for an
integral closed subscheme as a module over the ambient stalk, through the
actual stalk map. It does not replace that scalar structure with a
self-length computation. These are A11q / SP32.

### Graph-slice cycle pull–push and closed-support images

`Cycles/ClosedImmersionPushforward.lean` constructs actual integral image
cycles for supports whose composite into the target is a closed immersion.
The image is isomorphic to the support, its generic point is identified,
and its actual residue map has degree one. The global closed-immersion
pushforward is linear, with identity and composition laws. The generic
degree lemma has one canonical proof in `Cycles/ResidueDegree.lean`; the
older split namespace retains a compatibility adapter.

`GraphSlice.lean` identifies \(s_\tau:(y,z)\mapsto(y,\tau y,z)\) with the
actual first-graph inverse image. The last-pair map \(u_\tau=(\tau,\mathrm{id})\)
is an isomorphism, so existing open restriction gives a genuine cycle map.
`GraphCycleComposition.lean` proves that this pullback takes the graph of
\(\sigma\) to the graph of \(\sigma\tau\); closed slice pushforward
then gives the integral intersection cycle. Its supportwise outer image is
the composite graph cycle. The two linear slice maps preserve weights.
`EtaleGraphIntersection.lean` additionally proves the graph, inverse-image,
and intersection inclusions open for an étale structural map. None of these
steps assumes the pair product or an inverse-image graph integral. This is
A11r / SP33.

### Relative-to-absolute product and cycle comparison

For actual maps \(p:Y\to S\), \(b:S\to B\), put \(r=b\circ p\).
`DeckBaseChange.lean` constructs the injective homomorphism
\(\operatorname{Aut}_S(Y)\to\operatorname{Aut}_B(Y)\), retaining each
underlying scheme map. `RelativeProductComparison.lean` constructs the
actual pair and triple inclusions \(\kappa_2:W_p\to W_r\) and
\(\kappa_3:T_p\to T_r\); separatedness of \(b\) alone makes them
closed. These are absolute products when \(B=\operatorname{Spec}k\).
`GraphBaseComparison.lean` proves graph, intersection, and slice
compatibility at the actual morphism and image-ideal levels.

`GraphCycleBaseComparison.lean` carries the integral graph and intersection
cycles to their structural-base counterparts, including weighted graph
assembly. More strongly, on the entire finite-cycle modules it proves
\[
 \kappa_{2,*\mathrm{cyc}}\mathsf R^p_\tau
   =\mathsf R^r_{\bar\tau}\kappa_{2,*\mathrm{cyc}},\qquad
 \kappa_{3,*\mathrm{cyc}}\mathsf K^p_\tau
   =\mathsf K^r_{\bar\tau}\kappa_{2,*\mathrm{cyc}}.
\]
The first square needs only separated \(b\); the second also needs
separated \(p\). Neither needs an integral pair or triple product.
`Cycles/IsomorphismTransport.lean` proves the generic mechanism:
isomorphism pullback equals inverse-isomorphism closed pushforward.
No second cycle type or relation package is introduced. This is A11s / SP34.

### Signed local orders and actual isomorphism transport

`Cycles/LocalOrder.lean` extracts an integer order on nonzero fraction-field
elements from Mathlib's existing length-defined `Ring.ordFrac`. It proves
the product/inverse laws, zero for local units, finite principal-quotient
lengths, and the numerator-minus-denominator formula.
`Cycles/LocalOrderTransport.lean` proves that actual ring equivalences
preserve those quotient lengths and their fraction-field orders.

`Cycles/FunctionFieldTransport.lean` constructs the contravariant field
equivalence of an actual scheme isomorphism from its generic-point stalk
map. Its square with every local stalk map is proved from specialization
naturality. `Cycles/SchemeLocalOrder.lean` defines
\(\operatorname{DivPt}(X)=\{x:\dim\mathcal O_{X,x}=1\}\), constructs
such points from affine height-one primes, and gives their signed local
coefficients on integral locally Noetherian schemes. For an actual
isomorphism \(e:X\simeq Y\), it proves
\[
  \operatorname{ord}_x(e^*f)=\operatorname{ord}_{e_1(x)}(f).
\]
This is A11t / SP35. Neither normality nor a DVR hypothesis is imposed.
The point index is not a second cycle type. Its identification with actual
codimension-one integral closed supports is constructed in A11u / SP36.

### Actual prime supports and their local coefficients

`Cycles/PointSupport.lean` constructs \(Z_x=(\overline{\{x\}})_{\mathrm{red}}\)
as an actual ideal-sheaf subscheme. It proves that this construction and
\(\xi_Z=\iota_Z(\eta_Z)\) are mutually inverse between points and the
existing integral cycle generators. Reducedness and the uniqueness of the
defining radical ideal are proved from the actual scheme structure.

`Cycles/SupportCodimension.lean` proves that the coheight of an irreducible
closed support equals the dimension of its ambient generic-point stalk.
This is chain codimension, not a difference of absolute Krull dimensions.
`Cycles/DivisorSupport.lean` therefore gives
\[
 \operatorname{DivPt}(X)\simeq\operatorname{PrimeDiv}(X),\qquad
 x\longmapsto Z_x.
\]
The right side is the codimension-one subtype of `IntegralClosedSubscheme`,
not a new cycle module. For an actual scheme isomorphism, the transported
support is proved to be the existing scheme-theoretic image. Its local
coefficient is the existing point order reindexed through this equivalence,
and satisfies \(\operatorname{ord}_Z(e^*f)=\operatorname{ord}_{e(Z)}(f)\).
The support and codimension results hold for arbitrary schemes; the
coefficient statements retain integral locally Noetherian hypotheses.
This is A11u / SP36.

### Locally finite prime supports and quasi-compact finite coefficients

`Cycles/HeightOneFiniteness.lean` gives the commutative-algebra bound:
height-one primes containing a nonzero element are minimal over its
principal ideal, and there are finitely many in a Noetherian domain.
The ambient ring is not assumed one-dimensional.
`Cycles/RationalFunctionPresentation.lean` supplies actual nonzero
numerator and denominator sections on a nonempty affine chart. Their
germs factor the canonical map to the function field, and the existing
coefficient vanishes where both germs are units.

`Cycles/DivisorFiniteness.lean` proves that only finitely many nonzero
coefficients have their divisor points in each affine chart. Since an
integral closed support meets an open set exactly when its generic point
belongs to that open, the family
\[
  (|Z|)_{Z\in\operatorname{PrimeDiv}(X),\ \operatorname{ord}_Z(f)\ne0}
\]
is locally finite on an integral locally Noetherian scheme. With
quasi-compactness, the nonzero prime coefficient set, equivalently its
existing divisor-point index, is finite. This is A11v / SP37.
Neither normality nor properness is assumed, and the total prime-divisor
index is not asserted finite.

### Finite principal-divisor cycles and actual isomorphism transport

`Cycles/PrincipalDivisor.lean` assembles the proved finite coefficients into
the existing ungraded integral cycle module, for integral locally
Noetherian quasi-compact schemes:
\[
 \operatorname{div}_X(f)=
 \sum_{Z\in\operatorname{PrimeDiv}(X)}\operatorname{ord}_Z(f)[Z]
 \in Z_{\mathrm{fin}}(X;\mathbf Z).
\]
The coefficient at every other integral support is zero. Its support is
exactly the image of the nonzero prime coefficient set. Product, inverse,
and quotient laws are proved, and `principalDivisorAddHom` packages the
same construction as a multiplicative-to-additive group homomorphism.

`Cycles/IsomorphismTransport.lean` proves coefficient reindexing for the
existing closed pushforward via the actual ideal-image equivalence.
`Cycles/PrincipalDivisorTransport.lean` combines this with the previously
proved order and codimension comparisons. For an actual isomorphism
\(e:X\simeq Y\) and \(f\in k(Y)^\times\),
\[
 e_{*,\mathrm{cyc}}\operatorname{div}_X(e^*f)=\operatorname{div}_Y(f),
 \qquad
 e^*_{\mathrm{cyc}}\operatorname{div}_Y(f)=\operatorname{div}_X(e^*f).
\]
Here cycle pullback is the existing open restriction along the
isomorphism, not a new operation. This is A11w / SP38. No extra axiom,
relation hypothesis, normality assumption, or second cycle module is used.

### Dimension functions and homogeneous principal-divisor images

`Cycles/DimensionFunction.lean` supplies the explicit pointwise interface
\(\delta:X\to\mathbf Z\), retaining both strict decrease on proper
specializations and decrement one on immediate specializations. The
degree of an existing integral support is
\(\deg_\delta(Z)=\delta(\xi_Z)\). On an integral scheme, the proved
coheight-one condition makes a prime divisor's generic point an immediate
specialization of the ambient generic point. Its degree is therefore
\(\delta(\eta_X)-1\), without local Noetherianity in this topological step.

`Cycles/DimensionFunctionRestriction.lean` proves that a closed immersion
preserves immediate specialization: its actual image is order-convex.
Thus \(\delta\circ i\) is a dimension function, and the degree of an
integral source support agrees with the degree of its actual closed image.
This compares degrees, not ambient codimensions.

`Cycles/CycleDegree.lean` defines
\(Z^{\delta}_{\mathrm{fin},n}(X;R)\) as a supported submodule of the
existing finite cycles. It proves coefficientwise membership, disjointness
of distinct degrees and preservation by the existing closed pushforward
under compatible support degrees. `Cycles/PrincipalDivisorDegree.lean`
discharges that compatibility for the actual restricted dimension function
and proves the finite principal cycle homogeneous of the required degree.
In particular, for an actual integral closed support \(W\subset X\)
which is locally Noetherian and quasi-compact,
\[
 (\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)
 \in Z^{\delta}_{\mathrm{fin},\deg_\delta(W)-1}(X;\mathbf Z).
\]
No integrality or Noetherianity of the ambient scheme is required.
The dimension function is explicit input; this checkpoint, A11x / SP39,
does not construct one on arbitrary schemes or identify its degree with
absolute Krull dimension.

### Genuine principal relations and closed-pushforward quotient descent

On a Noetherian scheme with a supplied dimension function, the relation
index consists of actual integral closed carriers of degree \(n+1\)
together with units in their actual function fields.
`Cycles/PrincipalDivisorImage.lean` derives the finiteness hypotheses on
closed carriers and transports their ambient principal cycles through
the actual closed support-to-image isomorphism.
`Cycles/PrincipalRelations.lean` defines
\[
 \mathcal R_n^\delta(X)=\left\langle
   (\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f):
   \deg_\delta(W)=n+1,\ f\in k(W)^\times
 \right\rangle_{\mathbf Z},\qquad
 \mathrm{CH}_n^\delta(X)=
 Z^\delta_{\mathrm{fin},n}(X;\mathbf Z)/\mathcal R_n^\delta(X).
\]
Membership in the span is proved equivalent to an **unweighted finite
sum of these actual principal cycles**: integer coefficients are absorbed
using \(\operatorname{div}(f^m)=m\operatorname{div}(f)\).
The carrier-family criterion proves that a locally finite family of these
nonempty closed carriers on a quasi-compact scheme has finite index,
and conversely every finite family is locally finite. This includes
carriers with zero principal cycle; finiteness is not tested only on
the nonzero divisor supports. Thus this finite construction matches
the locally finite relation convention on the specified domain.

`Cycles/GradedPushforward.lean` restricts the existing cycle pushforward.
`Cycles/ChowPushforward.lean` proves its actual principal-generator image
identity, derives preservation of the generated submodule, and constructs
the quotient pushforward with its class-map square, identity and
composition laws. Degree compatibility is proved for the actual
restricted dimension function \(\delta_X=\delta_Y\circ i\); no
relation-preservation hypothesis is supplied. `Cycles/ChowIsomorphism.lean`
proves exact transport of the relation submodule through an actual
scheme isomorphism and constructs the quotient equivalence. Its inverse
on representatives is the existing open restriction along that
isomorphism. This is A11y / SP40; arbitrary open restriction is not yet
descended.

### Actual support dimension and a proved low-dimensional instance

`Cycles/SupportDimension.lean` identifies the points of an actual integral
closed carrier \(W\) with the specialization interval below its ambient
generic point. Consequently
\[
 \dim W=\operatorname{height}(\xi_W),\qquad
 \dim\overline{\{x\}}=\operatorname{height}(x).
\]
Here dimension is actual topological Krull dimension, not ambient
codimension. No integrality, Noetherianity or finiteness of the ambient
scheme is needed for these identities. Finite-dimensionality makes the
height a finite integer, and this integer is strictly increasing in the
closure-inclusion order.

`Cycles/FiniteTypeDimension.lean` proves finite-dimensionality for
finite-type algebras over a field using actual polynomial presentations
and the proved bound \(\dim A[T]\leq 2\dim A+1\). It does not use the
unproved exact multivariate-polynomial dimension formula in the pinned
Mathlib. `Cycles/FiniteTypeSchemeDimension.lean` passes to an actual
finite affine subcover: open immersions preserve point coheight through
their actual stalk isomorphisms, so finitely many chart bounds bound the
whole scheme. Thus every finite-type scheme over a field has finite
dimension, including an empty scheme.

If \(\dim X\leq1\), `Cycles/LowDimensionalDimensionFunction.lean`
constructs \(\delta_X(x)=\dim\overline{\{x\}}\) as an actual
`DimensionFunction`. Every strict pair has heights zero and one, proving
both laws rather than supplying them as hypotheses. The existing support
degree equals \(\dim W\), and membership of \([W]\) in the existing
homogeneous cycle module is exactly its dimension test. This applies to
nonintegral and empty schemes as well. `Cycles/Examples/DimensionFunction.lean`
instantiates the construction on \(\operatorname{Spec}k[T]\), proves its
dimension is one, and computes degrees one at the generic point and zero
at the origin defined by the constant-coefficient kernel. With the
existing Noetherian hypotheses, SP40's quotient now accepts this
constructed grading without a supplied dimension-function input.
This is A11z / SP41, the first substep of geometric grading instantiation.

### Affine dimension and actual residue-field comparison

The affine-dimension subcheckpoint is A11aa / SP42.
`Cycles/TranscendenceDegreeDrop.lean` proves strict transcendence-degree
drop for an actual noninjective surjection between domains of finite
transcendence degree. Lifting a quotient transcendence basis makes the
map injective on its generated subalgebra; a nonzero kernel element
prevents that lift from being a full basis. This proves strict decrease
on the actual prime quotients of a finite-type algebra, even when the
ambient algebra is reducible.

`Cycles/IntegralDimension.lean` proves dimension invariance under an
injective integral algebra map. Incomparability bounds chains in one
direction; lying over and going up construct finite-chain lifts in the
other. `Cycles/NormalizationDimension.lean` uses an actual Noether
normalization to identify its variable count with transcendence degree
and prove the dimension lower bound. The independent prime-chain upper
bound then gives, in `Cycles/AffineDimension.lean`,
\[
 \dim A=\operatorname{trdeg}_k A
       =\operatorname{trdeg}_k\operatorname{Frac}(A)
\]
for every finite-type domain over a field. The fraction-field comparison
uses the actual algebra map and scalar tower. In particular the exact
field-polynomial formula \(\dim k[T_1,\ldots,T_n]=n\) is proved without
using the pinned library's unproved general polynomial-dimension formula.
The older recursive finite bound remains a separately proved result.

`Cycles/AffineSupportDimension.lean` connects this result to the existing
actual reduced carrier of every point \(p\) of \(\operatorname{Spec}A\):
\[
 \dim\overline{\{p\}}=\dim(A/p)
   =\operatorname{trdeg}_k\kappa(p).
\]
Here \(\kappa(p)\) is the actual residue field of the prime localization,
with its proved fraction-field structure over \(A/p\). Scheme point
height uses the closure-inclusion order, the reverse of prime inclusion;
prime coheight therefore computes this dimension. The ambient finite-type
algebra need not be a domain. The finite integer height equals this
residue-field transcendence degree, which strictly decreases under proper
specialization. These are identities for the existing carrier and its
actual dimension, not a new cycle type or an assumed grading law.

### Polynomial maximal height and actual closed-point local dimension

A11ab / SP43 proves the next local algebraic case.
`Cycles/PolynomialPrimeHeight.lean` constructs the actual order embedding
of primes under extension along \(R\to R[T]\), with contraction as a left
inverse. An extended ideal is never maximal: its quotient is a polynomial
ring, which is not a field. Thus, for every maximal ideal \(m\subset R[T]\),
\[
 (m\cap R)R[T]\subsetneq m,
 \qquad \operatorname{ht}(m\cap R)+1\leq\operatorname{ht}(m).
\]
This helper needs only a commutative ring. In
`Cycles/PolynomialMaximalHeight.lean`, Jacobson maximal contraction permits
induction on the variables over a field, while SP42 supplies the independent
upper bound. For every maximal ideal of \(R_n=k[T_1,\ldots,T_n]\),
\[
 \operatorname{ht}(m)=\dim (R_n)_m=n.
\]
The zero-variable case and non-rational closed points are included.
`Cycles/PolynomialClosedPointDimension.lean` computes the actual
structure-sheaf stalk dimension as \(n\), and hence scheme-point coheight
as \(n\). Closed-point carrier dimension and scheme-point height remain
zero; these are distinct quantities. No regularity or generator bound is
asserted.

### Normal-base going down and finite-type-domain local dimension

A11ac / SP44 proves going down for an actual integral injection of domains
\(R\hookrightarrow S\) when \(R\) is integrally closed in its fraction
field. `CommutativeAlgebra/IntegralIdealPolynomial.lean` constructs a
monic annihilator for each \(y\in IS\), with its degree-\(i\)
coefficient in \(I^{d-i}\), using finite ideal-membership witnesses
and an actual finite integral subalgebra. The ambient integral algebra
need not itself be finite or Noetherian. In
`CommutativeAlgebra/MonicPrimeCoefficients.lean`, reduction modulo a prime
and passage to its actual fraction field control coefficients of a monic
divisor, including the scalar-substitution case.

`CommutativeAlgebra/NormalGoingDown.lean` uses the actual minimal polynomial
over the normal base to prove cancellation relative to the chosen prime:
\[
 p\subseteq Q\cap R,\quad a\notin p,\quad ab\in pS
 \quad\Longrightarrow\quad b\in Q.
\]
An actual prime disjoint from \((R\setminus p)(S\setminus Q)\)
then lies below the prescribed \(Q\) and contracts to \(p\).
There is no supplied going-down hypothesis or global instance, and no
separability, flatness, Noetherianity or normality-of-\(S\) premise.

`Cycles/NormalizationLocalDimension.lean` combines this construction with
integral incomparability and reuses
`NormalizationInertia.primeHeight_under_le_of_hasGoingDown`; it does not
duplicate that generic height comparison. Prime heights are equal under
an integral map with going down. For an actual injective integral
normalization \(k[T_1,\ldots,T_s]\hookrightarrow A\) of a domain, every
maximal ideal of \(A\) therefore has height \(s\). Noether normalization
supplies such a map for every finite-type domain, giving
\[
 \dim A_m=\operatorname{ht}(m)=\dim A
   =\operatorname{trdeg}_k\operatorname{Frac}(A).
\]
`Cycles/AffineClosedPointDimension.lean` computes the actual closed-point
structure-sheaf stalk dimension and scheme-point coheight accordingly.
The domain \(A\) need not be normal and the point need not be rational.
The local comparison uses prime chains, not an assumption that localizing
at one selected upstairs prime preserves integrality of the local-ring map.

### Residue-normalization localization

A11ad / SP45 constructs that localization. For a finite-type algebra
\(B\) over a field and an actual prime \(q\),
`Cycles/ResidueNormalizationLift.lean` chooses an injective integral
normalization \(g:P=k[T_1,\ldots,T_n]\to B/q\) and lifts the variables
to an actual algebra map \(f:P\to B\). The quotient square commutes
exactly: \(\pi_q f=g\). Consequently \(f\) is injective and
\(M=f(P\setminus\{0\})\) is disjoint from \(q\).

`CommutativeAlgebra/GenericFiberAlgebra.lean` equips the actual localization
\(B'=M^{-1}B\) with its canonical \(K=\operatorname{Frac}(P)\)-algebra
map and compatible scalar tower. Finite type over \(K\) follows from
the actual localization pushout. `CommutativeAlgebra/ResidueLocalization.lean`
proves \(q'=qB'\) is maximal: the same-denominator localization of
\(B/q\) is a domain integral over \(K\), hence a field, and the
actual surjective localized quotient map has kernel \(q'\).
Its contraction is \(q\), and localization preserves its full height.
Contraction, primality and height need only the quotient injection, not
integrality; the ambient ring need not be a domain for these results or
for maximality and finite type.

`Cycles/ResidueNormalizationLocalization.lean` supplies the existential
construction without a normalization input. When \(B\) is a domain,
the actual \(B'\) is also a domain, so SP44 gives the additional endpoint
\[
 \operatorname{ht}_B(q)=\operatorname{ht}_{B'}(q')
   =\operatorname{trdeg}_K B'.
\]
Neither integrality of \(P\to B\) nor a maximality or height-comparison
premise is assumed. No replacement carrier, source axiom or target package
is introduced.

### Original-field prime dimension formula

A11ae / SP46 completes the original-field comparison.
`Cycles/LocalizationTranscendenceDegree.lean` proves full cardinal-valued
transcendence-degree invariance for an actual localization of a domain at
non-zero-divisors. It derives the actual localization injection, faithful
scalar action and domain instance, then uses algebraicity of localization
and tower additivity. No finite-type or finite-transcendence-degree hypothesis is needed;
universe lifts are retained in the general equality. The numeric adapter
is a consequence of cardinal invariance, not a substitute for it.

`Cycles/AffinePrimeDimension.lean` installs the canonical compatible
\(k\to P\to K\to B'\) scalar tower on the literal SP45 localization.
For any injective polynomial map \(P=k[T_1,\ldots,T_n]\to B\) into
a finite-type domain, it proves
\[
 n+\operatorname{trdeg}_K B'=\operatorname{trdeg}_k B.
\]
This comparison needs no integrality premise. It derives
\(\operatorname{trdeg}_k K=n\) from the actual polynomial fraction
field and obtains finite transcendence degree over \(K\) from the proved finite-type
generic fiber. It does not assume that \(K\) is finite type over \(k\).
The finite-cardinal sum is converted to natural numbers only after these
finiteness facts have been established.

Applying this to the constructed residue normalization, SP45 supplies
\(\operatorname{ht}_B(q)=\operatorname{trdeg}_K B'\), while the
quotient normalization gives \(\operatorname{trdeg}_k(B/q)=n\).
Thus, for every prime of any finite-type domain over any field,
\[
 \operatorname{ht}_B(q)+\operatorname{trdeg}_k(B/q)
   =\operatorname{trdeg}_k B,\qquad
 \dim B_q+\dim(B/q)=\dim B.
\]
The first equality is proved in extended natural numbers, so no finite
height of \(q\) is assumed. The actual `Ideal.ResidueField` variant
reuses the existing quotient/fraction-field comparison. The second uses
the actual `Localization.AtPrime` carrier, not a replacement local ring.
No normality, rational-point, characteristic-zero or maximal-prime premise
is required. The ambient-domain hypothesis is retained; the corresponding
local topological formula on arbitrary reducible algebras is not asserted
by replacing local dimension with global dimension.

### Consecutive-prime unit drop

A11af / SP47 proves the algebraic unit-step law.
`CommutativeAlgebra/PrimeQuotientCover.lean` takes a cover
\(p\lessdot q\) in the actual `PrimeSpectrum B`, restricts it to
the primes containing \(p\), and transports it through the existing
quotient-spectrum order isomorphism. The lower prime maps to zero and
the upper prime maps to its actual quotient ideal
\(\bar q=q(B/p)\). Thus \(0\lessdot\bar q\) in
\(\operatorname{Spec}(B/p)\), and \(\operatorname{ht}(\bar q)=1\).
These conclusions require only a commutative ambient ring, not a field,
domain, Noetherianity or catenarity assumption. The cover is among prime
ideals, not in the full ideal lattice.

`Cycles/ConsecutivePrimeDimension.lean` applies SP46 to the actual domain
\(B/p\) and this height-one prime. The actual \(k\)-algebra equivalence
`DoubleQuot.quotQuotEquivQuotOfLEₐ` identifies its further quotient with
\(B/q\). For any finite-type algebra over a field, it therefore proves
\[
 \operatorname{trdeg}_k(B/q)+1=\operatorname{trdeg}_k(B/p),\qquad
 \operatorname{trdeg}_k\kappa(q)+1=\operatorname{trdeg}_k\kappa(p),
\]
and \(\dim(B/q)+1=\dim(B/p)\). The residue-field version reuses
`primeQuotient_trdeg_eq_residueField` for the existing actual prime-localization
residue fields. Finite type supplies finite transcendence degrees; no
unjustified inference from a numeric projection at infinity is used.
The ambient algebra may be reducible or nonreduced. This is a unit drop
in quotient dimensions, not a claim that ambient local-ring dimensions
increase by one on every mixed-dimensional algebra.

### Actual affine dimension functions

A11ag / SP48 constructs the existing `DimensionFunction` on actual affine
schemes in every finite dimension. `Cycles/AffineDimensionFunction.lean`
defines \(\delta_{A/k}(x)=\operatorname{trdeg}_k\kappa(x)\) on the
literal \(\operatorname{Spec}A\), using the actual prime-localization
residue field and its finite transcendence degree. It exposes and reuses
the existing `specPointOrderIso`, whose point map is the identity and whose
target order is dual prime inclusion. Strict degree drop and SP47 prove
both required laws; they are not extra inputs. The values equal integer
scheme-point height and hence actual point-closure dimension.

`Cycles/AffineSchemeDimensionFunction.lean` supplies
`DimensionFunction.ofAffineLocallyOfFiniteType` for an actual affine
\(X\) and a structural morphism \(p:X\to\operatorname{Spec}k\)
locally of finite type. It extracts the actual finite-type sections
algebra through `X.isoSpec`, following the existing finite-dimensionality
construction, and reuses closed-immersion restriction along that
isomorphism. Its values are definitionally integer point height, so the
result does not depend on a new residue-field model or an independently
supplied sections algebra. Actual carrier isomorphisms prove the needed
height comparison. Neither constructor assumes an integral, reduced,
normal, nonempty or dimension-at-most-one ambient scheme.

For either constructor, the degree of an existing integral closed support
equals its actual finite dimension. For natural \(n\), its fundamental
cycle over a nontrivial coefficient semiring belongs to degree \(n\)
exactly when that carrier has dimension \(n\). These use the existing
support and cycle objects, not a new grading module or Chow quotient.

### Structural residue fields and their affine comparison

A11ah / SP49 constructs the structural base map in
`Cycles/StructuralResidueField.lean` as the literal composite
\[
 k\longrightarrow\Gamma(\operatorname{Spec}k,\mathcal O)
 \xrightarrow{p^*}\Gamma(X,\mathcal O_X)
 \xrightarrow{\operatorname{ev}_x}\kappa_X(x).
\]
The associated algebra is an ordinary definition used locally, not a
global instance or an action defined by transporting through the desired
equivalence. Actual evaluation naturality proves that the existing
residue-field map for any morphism commutes with these actions. For an
open immersion, the existing residue-field isomorphism is upgraded to a
base-algebra equivalence with the same underlying map. These constructions
work over any commutative base ring, without finite type or affineness.

`Cycles/AffineResidueField.lean` uses the actual `StructureSheaf.stalkIso`
and `IsLocalRing.ResidueField.mapEquiv` to compare
\(\kappa_{\operatorname{Spec}A}(x)\) with the actual prime-localization
residue field \(\kappa(\mathfrak p_x)\). Evaluation of every actual
\(A\)-constant maps to its canonical prime-residue-field image. Global
section naturality and the existing scalar tower therefore give a genuine
\(k\)-algebra equivalence for the structural map induced by
\(k\to A\). No domain, reducedness, normality or finite type is needed.

Over a field, `Cycles/AffineResidueFieldDimension.lean` identifies the full
transcendence-degree cardinals of these two actual residue fields, without
a finiteness premise. Finite type of \(A\) separately proves finiteness
of that degree, not finite type of the residue field. The existing
\(\delta_{A/k}\) then equals the integer transcendence degree of the
actual scheme residue field. Actual open immersions preserve the full
structural residue degree without affine or finite-type hypotheses.

### Structural residue-degree values on arbitrary affine schemes

A11ai / SP50 proves the arbitrary-affine value comparison in
`Cycles/AffineSchemeResidueDegree.lean`. For an actual affine \(X\) and
locally finite-type structural morphism \(p:X\to\operatorname{Spec}k\),
the actual structural residue degree is finite and
\[
 \delta_{X/k}(x)=h_X(x)=\operatorname{trdeg}_k\kappa_X(x).
\]
The proof extracts the finite-type sections algebra from the actual
morphism `X.isoSpec.inv ≫ p`,
retains its actual spectrum-morphism equality and checks that pulling
back along `X.isoSpec.hom` recovers \(p\). SP49's base-compatible residue
map then transfers the full-cardinal degree before numeric conversion.
The existing `point_height_iso` is exposed with its proof unchanged;
no second order isomorphism, scalar action or dimension function is added.
No independently supplied sections algebra, ambient integrality,
reducedness or nonemptiness is required.

For an open immersion \(f:X\to Y\) between affine schemes and locally
finite-type \(p:Y\to\operatorname{Spec}k\), the same comparison proves
\(\delta_{X/k}(x)=\delta_{Y/k}(f(x))\), with the source structural
morphism \(p\circ f\). This is a value theorem for the existing affine
functions, not unrestricted open-immersion invariance of point height.

### Pointwise residue degrees and affine-chart agreement

A11aj / SP51 proves the chartwise value comparison in
`Cycles/ChartResidueDegree.lean`. For arbitrary \(X\) with locally
finite-type \(p:X\to\operatorname{Spec}k\), each actual structural
residue degree \(\operatorname{trdeg}_k\kappa_X(x)\) is finite.
The proof uses `Scheme.affineCover` and `Cover.exists_eq` to represent
the point by an actual affine-chart point before installing its
point-dependent scalar action. SP50 gives finiteness on that chart,
and SP49's actual residue map transfers the full cardinal. No ambient
affineness, quasi-compactness, finite subcover, integrality or reducedness
is required; this is not a global dimension bound.

For any actual affine open chart \(i:U\to X\), its existing function
satisfies
\[
 \delta_{U/k}(u)=\operatorname{trdeg}_k\kappa_X(i(u)),
\]
with the source structural morphism \(p\circ i\). Thus for another
chart \(j:V\to X\), equality \(i(u)=j(v)\) implies
\(\delta_{U/k}(u)=\delta_{V/k}(v)\). The proof packages the point,
residue field and structural scalar action in one local proof expression;
it does not identify dependent field carriers by fiat or introduce a new
global dimension-function object.

### The global structural dimension function

A11ak / SP52 constructs `DimensionFunction.ofLocallyOfFiniteType` in
`Cycles/FieldDimensionFunction.lean` with the literal value
\[
 \delta_{X/k}(x)=\operatorname{trdeg}_k\kappa_X(x)\in\mathbb Z.
\]
SP51 supplies pointwise finiteness before conversion to an integer.
Both defining laws are proved by placing a specialization pair in an
actual affine neighbourhood of its specialized point and transferring
the existing affine laws through the structural residue-degree comparison.
In the repository's closure-inclusion order, choose the neighbourhood of
\(x\) when \(x\leq y\): `Scheme.le_iff_specializes` and
`Specializes.mem_open` then place \(y\) in the same open. The existing
`exists_isAffineOpen_mem_and_subset` supplies an actual affine open.
Its actual open embedding reflects specialization, transferring strict
order and the cover relation between the scheme and chart. No second
point-order object or supplied gluing package is added.
The resulting function is nonnegative, equals the existing affine
dimension-function object on affine schemes, and preserves its values
under arbitrary actual open immersions over the field. No ambient
affineness, quasi-compactness, integrality or global dimension bound is
assumed.

### Global point height and actual carrier dimension

A11al / SP53 proves the comparison in `Cycles/FieldSupportDimension.lean`:
\[
 h_X(x)=\delta_{X/k}(x)=\dim\overline{\{x\}}<\infty.
\]
Here height uses the scheme's closure-inclusion point order, and the
closure is the existing actual reduced closed carrier. Nonnegative
strictness bounds height above by the finite dimension value. One actual
affine chart, its finite point height and the affine normalization supply
the lower bound through the actual open embedding's strict point map.
Thus the comparison uses the normalization, not just the two abstract
dimension-function laws, which would allow additive shifts.
The equalities retain the full extended height/dimension types before
integer conversion. No global dimension bound, affineness,
quasi-compactness, integrality or Noetherian premise on \(X\) is needed.

For every existing integral closed carrier \(W\), the support degree is
its actual finite dimension. For \(n\in\mathbb N\) and nontrivial
coefficient semiring \(R\), its existing fundamental cycle belongs to
degree \(n\) exactly when \(\dim W=n\). Actual open immersions over
the field preserve point height in this locally finite-type setting;
no unrestricted assertion about arbitrary schemes is made.

### Integral chain codimension and the target degree convention

A11am / SP54 proves the integral comparison in
`Cycles/IntegralCodimension.lean`. For actual integral \(X\), put
\(d=\delta_{X/k}(\eta_X)=\dim X\). Ambient dimension, point coheight
and actual support codimension are finite, without affineness,
quasi-compactness or Noetherianity as inputs. The proved formulas are
\[
 \operatorname{codim}_X W+\deg_{\delta_{X/k}}W=d,
 \qquad
 \operatorname{codim}_X W+\dim W=\dim X.
\]
Codimension remains the existing supremum of lengths of chains of
irreducible closed supersets, not a newly defined dimension difference.
The generic-point height comparison gives finite ambient dimension.
Induction on finite coheight reaches the generic point at zero and uses
the existing unit-step law at a proved cover for the successor step.
No catenarity or uniform-chain theorem is an input. The geometric sum
equality is retained in the full extended dimension type.

For every \(n\in\mathbb N\), support degree \(d-n\) is equivalent
to actual codimension \(n\); the subtraction is in \(\mathbb Z\),
with no premise \(n\leq d\). The existing degree-\(d-n\) submodule
is exactly the finite cycles whose nonzero coefficients have that
codimension. Nontrivial coefficients are needed only for the
coefficient-one fundamental-cycle converse.

### Actual codimension indexing of principal relations

A11an / SP55 proves the reindexing in
`Cycles/PrincipalRelationCodimension.lean`. `PrincipalRelationData` in
degree \(d-(n+1)\) is equivalent to actual codimension-\(n\) carriers
with units in their unchanged function fields. Thus these are relations
on codimension-\(n+1\) cycles. Both directions preserve the carrier and
function literally, and the inverse generator is the existing ambient
principal divisor by definitional equality. No Noetherian hypothesis is
needed for the data equivalence; the generator map retains its existing
Noetherian premise.

The top-degree statements are proved more generally in the existing
`Cycles/PrincipalRelations.lean`. For any integral scheme and any supplied
dimension function \(\delta\), every carrier degree is at most
\(d_\delta=\delta(\eta_X)\). Hence
`PrincipalRelationData δ dδ` is empty: it would require degree
\(d_\delta+1\). This uses actual specialization antisymmetry and strict
monotonicity, without a field, finite-type or Noetherian assumption.
Under the existing `IsNoetherian X` premise, the relation span is zero
and rational equivalence in generic degree is equality.
The codimension reindexing at \(n=0\) instead concerns degree \(d-1\)
and has data on the whole carrier. A negative cycle degree alone does not
make its relation data empty: at \(n=d\), carriers have degree zero.

### Rational coefficients on the actual principal-relation quotient

A11ao / SP56 constructs coefficientwise extension in
`Cycles/CoefficientExtension.lean` on the existing degree submodule:
\[
 c\longmapsto c_{\mathbb Q},\qquad
 \mathbb Q\otimes_{\mathbb Z}Z^\delta_{\mathrm{fin},m}(X;\mathbb Z)
 \simeq Z^\delta_{\mathrm{fin},m}(X;\mathbb Q),\qquad
 q\otimes c\longmapsto q c_{\mathbb Q}.
\]
The map preserves the actual integral supports and their coefficients.
It is injective before taking the quotient and needs only an arbitrary
scheme and a supplied dimension function, not integrality, finite type,
Noetherianity or finitely many supports.

`Cycles/RationalChow.lean` retains the existing quotient's Noetherian
premise, takes the rational span of coefficient extensions of the same
`principalRelation` generators, and proves
\[
 \mathbb Q\otimes_{\mathbb Z}\operatorname{CH}_m^\delta(X)
 \simeq \operatorname{CH}_m^\delta(X;\mathbb Q),\qquad
 q\otimes[c]\longmapsto[q c_{\mathbb Q}].
\]
Here the right side is the quotient of actual rational homogeneous cycles
by that rational relation span. Its class map is surjective, has exactly
that kernel, and kills the unchanged principal generators. The comparison
gives the canonical integral-to-rational Chow map. Generic-degree relation
vanishing also holds for rational coefficients on an integral scheme.
The general `Cycles/ScalarExtensionQuotient.lean` lemma constructs both
directions from tensor and quotient universal properties; flatness and
quotient injectivity are not premises. General Chow rationalization need
not be injective: it may kill torsion.

### Rational closed pushforward and scheme-isomorphism naturality

A11ap / SP57 factors the existing graded closed pushforward through one
semiring-parametric construction in `Cycles/GradedPushforward.lean`.
The integer API is its definitional specialization; the actual image
supports and the identity/composition laws are unchanged.
`Cycles/CoefficientPushforward.lean` proves coefficient-cast compatibility
on actual ungraded and homogeneous cycles. Actual open restriction along
a scheme isomorphism preserves the corresponding homogeneous submodule
over any semiring. These cycle statements require no Noetherian or
integrality premise.

`Cycles/RationalChowPushforward.lean` uses the existing integer
principal-generator image identity to preserve the rational relation
span. It descends to rational Chow with the same cycle representative,
identity and composition laws. The original source/target Noetherianity
and support-degree compatibility are retained; the latter is already
proved for the actual restricted dimension function. The rationalization
and tensor-comparison squares commute on all classes and tensors.

`Cycles/RationalChowIsomorphism.lean` transports scalar extension of the
existing integral Chow isomorphism into the actual rational-cycle
quotients, then proves that its forward map is the independently
constructed geometric closed pushforward. Its inverse on rational
cycle representatives is exactly the existing open restriction. No
second graded-isomorphism model or new inverse cycle operation is used.
The proof never cancels the generally non-injective Chow rationalization
map.

### Actual integral-open function fields and signed local orders

A11aq / SP58 generalizes `Cycles/FunctionFieldTransport.lean` to an
actual open immersion \(j:X\to Y\) of integral schemes. The actual
generic-point stalk map gives \(j^*:k(Y)\simeq k(X)\); its compatibility
with specialization and with each local ring's canonical map to the
function field is proved. These statements need no Noetherianity,
compactness, finite-type, normality or field-base premise. The old
isomorphism APIs definitionally specialize this same construction.

In `Cycles/SchemeLocalOrder.lean`, the actual stalk isomorphisms preserve
local ring dimension for open immersions of arbitrary schemes. They
give an embedding of the existing divisor-point types, with image exactly
the divisor points whose underlying points lie in the open image.
This does not require integrality or Noetherianity. For integral source
and target, local Noetherianity of the target suffices for
\[
 \operatorname{ord}_x(j^*f)=\operatorname{ord}_{j(x)}(f).
\]
Local Noetherianity on the source is derived from the actual open
immersion. The proof reuses the existing local-order invariance under
compatible local-ring/function-field isomorphisms. The old isomorphism
order theorem is now a specialization, and the point embedding agrees
definitionally with the old isomorphism equivalence's forward map.

### Actual reduced open-support closure and principal-divisor restriction

A11ar / SP59 proves the support and coefficient comparison in
`Cycles/OpenSupport.lean`. For an actual open immersion \(j:U\to X\),
`openClosureSubscheme j W` is the existing reduced point support
`pointSupport X (j.base (ambientGenericPoint W))`. Its literal defining
ideal sheaf pulls back to `W.val`. Conversely, reduced closure of a
nonempty `openRestrictionSubscheme` recovers the original integral
closed support. Nonemptiness is equivalent to its ambient generic point
lying in the actual open image. The existing chain codimension is
preserved, and the prime-support comparison agrees with SP58's
`divisorPointEmbedding`.

For every semiring and existing finite cycle, `openRestriction_apply`
proves
\[
 (j^*c)(W)=c\bigl(\overline{j(W)}_{\mathrm{red}}\bigr).
\]
These support and coefficient statements impose no ambient integrality,
Noetherianity or compactness. The existing empty-restriction generator
remains zero; reduced closure is not a closed-image operation on \(j\).

In `Cycles/PrincipalDivisorTransport.lean`,
`primeDivisorOrder_openImmersion` gives the signed-order comparison on
these actual prime supports. For integral source and target, target
local Noetherianity and quasi-compactness suffice for
`openRestriction_principalDivisor_of_isOpenImmersion`:
\[
 j^*\operatorname{div}_X(f)=\operatorname{div}_U(j^*f).
\]
The source's local Noetherianity is derived, and local Noetherianity of
the target supplies `QuasiCompact j`; target compactness then yields
source compactness by `QuasiCompact.compactSpace_of_compactSpace`.
Thus both sides use the existing finite principal-divisor construction
with its finiteness hypotheses proved. The previous isomorphism
restriction theorem retains its signature and specializes this proof.

### Graded open restriction and the closed-carrier cycle square

A11as / SP60 constructs `DimensionFunction.comapOpenImmersion` in
`Cycles/OpenGrading.lean`. Its value is literally \(\delta\circ j\).
The actual open point map reflects specialization and has order-convex
image; it preserves immediate specialization, proving both conditions
of the existing dimension-function structure. Identity and composition
are preserved. On a morphism that is both open and closed, this is
definitionally the existing closed restriction, not another grading.

The actual reduced-closure and nonempty restriction support degrees
agree for these dimension functions. `openRestriction_mem_cyclesOfDegree`
therefore proves homogeneity using the existing coefficient formula.
`gradedOpenRestriction` is the same geometric cycle map restricted to
the existing homogeneous submodules, over any semiring. Its literal
representative, identity and contravariant composition formulas are
proved. The previous isomorphism-only homogeneity theorem retains its
signature and now specializes the general result. No ambient
integrality, Noetherianity, compactness or global-dimension convention
is imposed, and no dimension function is assumed to exist universally.

`Cycles/OpenClosedBaseChange.lean` proves the actual cycle square
`openRestriction_closedImmersionPushforward_subscheme`. For any integral
closed carrier `Z` in `X`, including an empty inverse image, it states

```lean
(openRestriction R j).comp (closedImmersionPushforward R Z.val.subschemeι) =
  (closedImmersionPushforward R (Z.val.comap j).subschemeι).comp
    (openRestriction R (openRestrictionSubschemeMap j Z))
```

The original `openRestrictionSubschemeMap_subschemeι` is now public,
with the same actual Cartesian inclusion equation. No replacement
pullback is introduced. Actual generic-point comparison identifies the
nonempty integral generators on both sides; the empty branches are
zero. Linear extension proves the square over every semiring without
ambient finiteness hypotheses. This square is stated on raw finite
cycles, separately from the homogeneous restriction construction.

### Ambient principal generators and open relation preservation

A11at / SP61 applies the actual carrier square and SP59's identity in
`Cycles/PrincipalDivisorRestriction.lean`. For an actual integral closed
carrier `W`, only its own local Noetherianity and quasi-compactness are
assumed. In the nonempty branch,
`openRestriction_ambientPrincipalDivisor_of_nonempty` identifies the
restricted ambient principal divisor with the ambient principal divisor
on the literal ideal-comap carrier. Its rational function is the unit
pulled back through `functionFieldEquivOfOpenImmersion` of the existing
`openRestrictionSubschemeMap`; the map is not inverted. The restricted
carrier's integrality and finiteness are proved, and its scheme is
definitionally the actual comap subscheme. No replacement carrier or
function-field comparison is chosen. In the empty branch,
`openRestriction_ambientPrincipalDivisor_of_isEmpty` proves that the
cycle is zero, without assigning a function field to the empty scheme.
Neither identity requires an integral or Noetherian ambient scheme.

`Cycles/PrincipalRelationRestriction.lean` constructs
`PrincipalRelationData.openRestriction` for a nonempty restricted
carrier. SP60's support-degree equality preserves its degree `n + 1`.
The carrier and rational-function projection formulas retain the literal
geometry; this indexing construction needs no Noetherianity. For an
open immersion into Noetherian `X`, `openImmersion_isNoetherian` derives
Noetherianity of `U`, using both local Noetherianity and quasi-compactness
of the open map. The two ambient identities then prove the nonempty
and empty graded principal-generator formulas. Checking these generators
proves `principalRelations_le_comap_openRestriction`, and linearity
proves `rationallyEquivalent_openRestriction` for the existing predicate.
No relation-preservation or quotient-descent hypothesis is introduced.

### Actual open Chow maps and coefficient compatibility

A11au / SP62 constructs `chowOpenRestriction` in
`Cycles/ChowOpenRestriction.lean` by the existing quotient universal
property and SP61's proved relation-span inclusion. Its class-map
formula is literal restriction of the actual homogeneous representative.
Identity and contravariant composition follow from the existing graded
cycle laws, with the canonical dimension function `δ.comapOpenImmersion j`.
Only the target is assumed Noetherian; source and intermediate
Noetherianity are derived from the actual open immersions. There is no
new Chow quotient or supplied descent hypothesis.

`Cycles/CoefficientRestriction.lean` proves that actual open restriction
commutes with coefficientwise integer-to-rational extension, both on raw
finite cycles and on the existing homogeneous submodules. Coefficients
are compared at the existing reduced open closure. This layer has no
Noetherian, compactness or integrality premise.

`Cycles/RationalChowOpenRestriction.lean` uses that comparison and
SP61's actual nonempty/empty generator identities to prove preservation
of the existing rational relation span. `rationalChowOpenRestriction`
then descends the same rational cycle map, with literal representatives,
identity and contravariant composition. It commutes with `chowRationalize`
and, on every tensor element, with the full `chowRationalizationEquiv`
comparison. The tensor square is proved by tensor induction and
surjectivity of the existing class map, not by cancelling rationalization
or assuming that torsion survives. These quotient results retain the
target-only Noetherian premise.

### Surjectivity by reduced closure of cycle supports

A11av / SP63 proves `openRestriction_surjective` and
`gradedOpenRestriction_surjective` in
`Cycles/OpenRestrictionSurjectivity.lean`. The cycle lift is the finite
linear combination of fundamental cycles of the existing reduced ambient
closures. The actual ideal-comap identity proves that restriction recovers
each generator, and the existing support-degree comparison shows that the
lift preserves the supplied grading. These statements hold over any
semiring, without Noetherianity, ambient integrality or compactness.
They also include empty opens and trivial coefficient semirings.

`chowOpenRestriction_surjective` and
`rationalChowOpenRestriction_surjective` choose an existing homogeneous
cycle representative of an open Chow class, lift it, and apply SP62's
literal representative formulas. Only the target scheme is assumed
Noetherian; source Noetherianity is derived. No new quotient, relation
or surjectivity hypothesis is introduced. The closure lift is kept private
at the cycle layer: its preservation of rational equivalence is neither
assumed nor asserted, and it is not descended as a Chow right inverse.

**The next bounded Lean checkpoint in the localization stream is the
closed-complement cycle kernel/image comparison (L1).** Identify the
integral supports disjoint from the open with
the actual closed-complement supports, and compare their finite cycles
and homogeneous submodules under the existing closed pushforward.
Quotient-level localization exactness then requires its own
principal-relation lifting argument. SP63 proves surjectivity, not the
remaining kernel/image equality, a localization sequence or general
flat pullback.

Comparison with the prescribed target rational Chow groups and its
intersection/Betti structure remains a separate geometric identification.
An extension to reducible schemes must use an actual pure-dimensional
hypothesis or componentwise grading; even smooth schemes may have
components of different dimensions. The existing finite-cycle quotient's
Noetherian premise is not removed by the codimension formulas.
The general comparison is now proved independently of the earlier
finite-split scalar-extension theorem. General proper pushforward requires its
norm compatibility, and flat/Gysin operations require their own
principal-relation comparison before descent; these are not supplied
by the closed-immersion case.
The relative-to-absolute inclusions do not identify arbitrary intersection
products or make closed pushforward injective on Chow groups: ambient
relations may use supports outside the relative product. General component
cycles, intersection-product comparison, and Chow convolution remain further
obligations. In particular, étaleness of \(p\) is not étaleness of \(r\). The
restricted first/last map is proper on its graph support; separatedness does
not make the ambient projection proper. The current graph map is
linear, not a claimed Chow algebra map. Open restriction need not preserve
absolute Krull dimension; finite étaleness alone does not imply reducedness.
The auxiliary cover base and carrier still need a separate geometric
comparison with the prescribed Hodge target, and class generation remains
open. See the [operative plan](TARGET_BRIDGE.md#0-operative-plan-chow-to-betti-first)
and [construction inventory](TARGET_BRIDGE.md#6-construction-inventory-and-detailed-dependencies).

### Geometric model still to be instantiated

For a fixed smooth projective complex variety `X` and a codimension `p`, the
classical rational Hodge target is

```text
HodgeConjectureAt(X, p) :=
  for every α in H^(2p)(X, ℚ) ∩ H^(p,p),
    there exists z in CH^p(X)_ℚ with cl(z) = α.
```

`Realization/HodgeClasses.lean` records exactly this logical shape for
supplied linear-algebra data.  A
`RationalHodgeCycleClassModel Chow H` specifies the rational Chow module, the
degree-`2p` rational cohomology module, the independently defined submodule of
rational Hodge classes, and the cycle-class map.  Then

```lean
RationalHodgeConjectureAt M :=
  M.hodgeClasses ≤ LinearMap.range M.cycleClass

RationalHodgeConjectureForModel M :=
  ∀ p, RationalHodgeConjectureAt (M p)

RationalHodgeConjectureForFamily M :=
  ∀ X p, RationalHodgeConjectureAt (M X p)
```

The all-codimension model uses cohomological degree `2 * p`; the family form
also quantifies over an explicit indexing type.  It becomes the universal
classical conjecture only when that type indexes all smooth projective
complex varieties and `M` supplies their genuine geometric data.  Lean proves
that the pointwise statement is equivalent both to the explicit `∀ α, ∃ z`
formulation and to equality of the cycle-class image with the Hodge-class
submodule. The finite split construction above now supplies the combined
model for `X=Spec(ℂ^I)` in codimension zero, using actual Chow, singular
cohomology, and an independently defined Hodge subspace. It also supplies
the geometric Tate-block construction and detection. The all-codimension
and universal-family geometric models are not constructed by this step.

There is now a non-circular projector reformulation in
`Realization/Chow/TateGraphProjector.lean`.  A class `α` is encoded by the
canonical graph projector on the underlying rational module of
`ℚ(-p) ⊕ H^(2p)(X, ℚ)`:

```text
e_α(t, x) = (t, t α),       e_α^2 = e_α.
```

Evaluation at `(1, 0)` followed by the second projection recovers `α`.
`ClassGraphProjectorConstruction` records construction and realization of the
Chow block `[[1, 0], [z, 0]]`; `ClassGraphProjectorDetection` records
extraction of the lower-left Chow block and its cycle-class compatibility.
Neither interface mentions Hodge membership, surjectivity, or the conjecture.
The two directions are formalized separately, and together give

```lean
RationalHodgeConjectureAt M ↔
  EveryHodgeClassHasGraphProjectorLift M ρ.
```

This is the equivalence target.  It is conditional only on the displayed
Tate-block construction and detection maps, not on the two implications being
postulated. To instantiate it geometrically beyond finite split degree zero
still requires the actual Chow
correspondence algebra of `ℚ(-p) ⊕ h(X)`, its action on cohomology, and the two
block-comparison laws.  `ClassGraphProjectorHodgeCompatibility` separately
names the expected equivalence

```text
α is a rational (p,p) class  <->  e_α is a morphism of Hodge structures.
```

With that interface, Lean also proves the equivalent formulation quantifying
over graph operators that are Hodge morphisms. Both the independent Hodge
structure and this compatibility are instantiated in the finite split
degree-zero block; the general version remains a geometric input.

The current finite-cover branch does **not** yet prove the right-hand side for
every Hodge class.  A `PrescribedChowProjectorLift` for
`ClassGraphProjector.projector α` gives the appropriate algebraic projector
lift for one `α` once its abstract action is identified with the Tate-block
action.  With lower-left block detection,
`PrescribedChowProjectorLift.isAlgebraicHodgeClass_of_classGraphProjector`
formally extracts its Chow representative, and
`ClassIndexedFiniteCoverGraphCoverage` permits the extension package to vary
with `α` over fixed deck-action data and a fixed finite subgroup.  The
abstract context does not assert that `pX` is finite or étale; those are
requirements on a genuine cover instance.  Together with detection, coverage
implies the Hodge target.  The older theorem with one fixed extension package
is retained as a stronger fixed-package sufficient hypothesis.  A realistic
formulation may need even the cover and subgroup to vary with `α`.

This remains a one-way sufficient criterion, not an equivalence with the
finite-cover branch.  The Hodge conjecture gives an arbitrary Chow graph
lift; it does not imply that the lift factors through some `E.Extension`, has
the prescribed generic restriction, or belongs to a cover-generated image.
`GraphProjectorLiftFactorizationThroughFixedDeckData` now names exactly that
missing arrow, for a supplied target predicate, from an algebraic graph lift
to a prescribed lift through class-indexed extension data.  Using the
rational Hodge-class predicate, this explicit unproved factorization plus
construction and detection gives a Lean conditional iff between the Hodge
target and class-indexed coverage.  The factorization may be strictly
stronger than Hodge and may only be plausible for a specified family or
Hodge subspace.

The quantifier order of this existing coverage declaration is important.  The
map `pX`, group and deck action, subgroup, correspondence model, and generic
and compactified algebras are fixed; only the extension package varies with
the class:

```text
[pX, G, deck, D, χ fixed],
  ∀ α, IsRationalHodgeClass M α →
    ∃ Eα, PrescribedChowProjectorLift χ Eα e_α.
```

A faithful class-indexed Galois target may instead need

```text
∀ α, IsRationalHodgeClass M α →
  ∃ (Gα, coverα, Hα ≤ Gα, χα, Pα, θα, Eα),
    θα carries the marked residual class to α ∧
    Eα compactifies Pα compatibly with χα.
```

Thus the cover, Galois group, marked stabilizer, comparison, and extension may
all depend on `α`.  The new
`ClassDependentMarkedGaloisSelectorWitness` represents the finite group,
marked subgroup, abstract extension package, and residual comparison with
this quantifier order while keeping one ambient noncommutative algebra and
action.  It still omits the actual cover or normal-closure datum, its map to
the sheet algebra, and a geometric construction of the comparison.  Thus it
is a logically correct intermediate schema, not yet the faithful geometric
witness displayed above.

There is also a motivic algebra mismatch to resolve explicitly.  The conventional
compactified algebra `CH^d(X × X)_ℚ` described by the current `χ` has no
Tate-to-`X` lower-left block by itself.  The graph reduction instead needs the
Tate-augmented algebra `End(ℚ(-p) ⊕ h(X))`, with its action restricted to the
Tate line and degree-`2p` cohomology, plus a comparison from the finite-cover
model.  Constructing that algebra must fix the covariant/contravariant motive
convention and, if correspondence composition reverses the chosen action,
use the appropriate opposite algebra.

### Marked Galois block route

Block diagonality is not itself an obstruction.  For the standard Tate graph,
put

```text
P₀(t, x) = (t, 0),
U_α(t, x) = (t, x + t α).
```

Lean now proves that `U_α` is a rational linear equivalence with inverse
`U_{-α}` and

```text
e_α = U_α P₀ U_α⁻¹.
```

It also proves that `r_α = 2e_α - 1` is an involution and
`e_α = (1 + r_α)/2`. These abstract identities alone do not construct
an algebraic shear or deck involution. The finite split Chow shear and its
actual Betti action are constructed separately in checkpoint `0015`; no
general geometric lift follows from changing linear coordinates.

The Galois-sheet algebra supplies a non-circular source for the same block
shape.  Let `A_H = ℚ^(G/H)` and let `q` be the characteristic function of
the marked base sheet.  Base-sheet evaluation is an augmentation algebra map
and

```text
E = ker(ev_base) = (1 - q)
```

as an ideal of the commutative algebra `A_H`.  Give the same underlying ideal
the internal unit `1-q` and call the resulting unital algebra
`E_H^corner`.  Lean proves the actual algebra equivalence

```text
A_H ≃ₐ[ℚ] ℚ × E_H^corner,
q ↦ (1, 0),       1-q ↦ (0, 1).
```

This is the multiplicative selector/CRT split, and the regular source action
`A_H →ₐ[ℚ] Endℚ(A_H)` is multiplicative.  The active comparison uses the
smaller universal one-idempotent algebra `U = ℚ × ℚ`: every chosen
idempotent gives a canonical algebra map out of `U`.  This exposes honest
homomorphisms without requiring a map between the whole pointwise sheet
algebra and a convolution algebra.  A full algebra map from `A_H` into a
generic correspondence algebra is an optional stronger presentation.
Multiplication by `q` is `diag(1,0)` in the multiplicative coordinates.  In
the separate constant-unit linear decomposition `A_H ≃ₗ ℚ1 ⊕ E`, the same multiplication map
is

```text
(t, x) ↦ (t, t · (q - 1)).
```

The two decompositions differ by the lower shear with residual class `q - 1`.
The augmentation ideal, regular algebra action, block formulas, and shear are
formalized through `LinearAlgebra/MarkedAugmentedAlgebra.lean`; the genuine
algebra split and its corner unit are in
`LinearAlgebra/MarkedAugmentedAlgebraDecomposition.lean`; these are specialized
in `Boundary/Sheets/MarkedBlockProjector.lean`.  The identification with
`ClassGraphProjector.operator (q - 1)` and its naturality under a residual
linear map are in `Realization/Chow/MarkedAugmentedRealization.lean` and
`Realization/Chow/GaloisMarkedBlock.lean`.  The residual realization
`θ : E →ₗ V` remains linear because the cohomological target is only a
module. The former `Realization/Chow/SheetLinearization.lean` is preserved
under `archive/legacy-lean/`, outside the library; its auxiliary linear
construction is not an algebra map `A_H → ℚ[G]` and is not a geometric bridge.

`MarkedProjectorActionComparison` is the canonical restriction-free action
comparison for a chosen projector. Its lower-left conclusion does not need
surjectivity; its full graph-action conclusion does. The following existing
`Realization/Chow/GaloisMarkedRealization.lean` route is the stronger
extension-based specialization. An `AlgebraProjectorExtension` separates the generic
algebra from a possibly noncommutative compactified correspondence algebra
`Γ`; its chosen compactified idempotent restricts to `q` in the sheet
specialization.  From the generic and compactified idempotents it constructs
canonical algebra maps out of `U`, and
`restriction_comp_compactifiedIdempotentMap` proves equality of the two
restriction composites.  A
`MarkedGaloisSelectorComparison` consists of a residual realization
`θ`, the equality `θ(q - 1) = α`, and the square intertwining the compactified
idempotent's action with multiplication by `q`.  Equivalently, it is a
morphism between the two `U`-representations.  Evaluating the square at the
marked unit proves that the lower-left class is `α`, so Chow-block detection
already yields an algebraic representative without surjectivity.  If `θ` is
surjective, naturality and cancellation additionally prove—rather than
assume—the whole target equality

```text
ρ(e) = e_α.
```

At the homomorphism level the same conclusion is
`palomarTargetSquare`: the cohomological action composed with the
compactified map `U → Γ` equals the canonical map `U → Endℚ(ℚ × V)`
determined by `e_α`.  This is the Palomar-facing equality of composites.
The older full `A_H` presentation remains an optional stronger interface and
is not consumed by this active specialization.

This algebra separation is necessary, not cosmetic.  If one fixed
commutative selector algebra were also used as the correspondence algebra for
all classes, all induced projectors would commute.  But
`e_α e_β = e_α` and `e_β e_α = e_β`, so two graph projectors commute only
when `α = β`; since the zero class is always Hodge, such fixed-commutative
coverage could cover only the zero Hodge subspace.  Allowing the ambient
correspondence algebra to be noncommutative removes that artificial collapse.

Under this surjectivity, the compactified idempotent is consequently an
`AlgebraicProjectorLift`.  The
class-dependent witness package keeps `Γ` and its action fixed but permits the
finite group, marked subgroup, extension package and element, and residual
comparison to vary with `α`.  Coverage by surjective witnesses implies the
modeled `RationalHodgeConjectureAt`.  A reverse conditional iff uses the
separately named strong replacement predicate
`StrongGraphProjectorLiftReplacementByClassDependentMarkedGaloisSelector`.
That predicate asserts existence replacement; it does not produce or relate
a particular factorization map.

A stronger possible motivic formulation of the Galois-to-Hodge comparison
is a geometrically constructed Chow-motivic map

```text
θ_α : E_α(-p) → h(X)
```

whose cohomological realization sends `q_α - 1` to `α` and supplies the
compactified action square.  An arbitrary rational linear map satisfies only
the pure graph-naturality identity; it does not supply that geometric square
or prove algebraicity.  Constructing `θ_α` from an already known Chow
representative of `α` would be circular; it must arise independently from the
cover geometry.  The conditional structure does not provide `θ_α`, the
extension package, the action square, or Chow detection.  Surjectivity is a
strong additional sufficient hypothesis used to identify the action on all
of `ℚ × H`, rather than only on the image of the sheet realization.  The
abstract class-dependent witness also does not yet bundle an actual finite
cover or normal-closure datum.
The minimal class-generation goal does not require this full motivic
formulation: a geometric Chow-valued map `r_CH`, with `θ = cl ∘ r_CH`
and proved `θ(a_H) = α`, already supplies the desired cycle. Additional
action comparisons are needed only for the chosen-projector conclusion.

The subgroup-average branch remains distinct.  Under the obvious blockwise
action on `ℚ(-p) ⊕ H`, its matrix is `diag(1, Av_D)`.  It can be used only
after isolating a marked summand on which the invariant line and residual
kernel have the required block form, or after an explicit comparison with the
sheet-selector construction.  Fixedness of a selector under averaging is not
equality of the two algebra elements.

## The adjacent finite-cover endpoint

For fixed compactification data `E`, an abstract rational
Chow-correspondence model `χ`, and a separately prescribed rational
cohomological projector `e`, the nearest source and target propositions in
the finite-cover branch are

```lean
P := Nonempty E.Extension

Q := Nonempty
  (HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift χ E e)
```

The conditional bridge is
`PrescribedChowProjectorLift.nonempty_iff_extension_nonempty` in
`HodgeConjecture/Realization/Chow/GaloisProjector.lean`.  Besides restriction
compatibility, its substantive input is

```lean
∀ x : E.Extension,
  χ.cohomologicalAction.action (E.projector x) = e.operator
```

Once this equality is supplied, constructing the target is record assembly.
Thus this conditional iff is not a proof that `e` is algebraic: its
`hRealizes` hypothesis already supplies the hard target-identification
equality.  Proving that equality for an independently specified `e` is
geometric or Hodge-theoretic.  Generic restriction does not prove it:
boundary-supported corrections can have nonzero cohomological action.

The forward-facing theorem
`exists_prescribed_subgroupAverage_chowProjector_of_different_away` now
unpacks this interface instead of hiding it in an extension structure.  Under
essential finite type it discharges collision-different detection and returns
an explicit compactified idempotent, but it takes compactified cycle
extraction, convolution-idempotence, one-way purity, height-one inertia
comparison, generic restriction, and prescribed realization as separate
hypotheses.  Its indexed ideals are prime, but their height-one status and
completeness as a boundary family are not asserted by the theorem.  It is
therefore the strongest honest form of the slogan
"different avoidance produces the prescribed subgroup-average projector" on
the current tree, not a proof of the proposed unconditional boundary theorem.

The current API asks for the equality for every extension witness.  For the
single implication `P -> Q`, the logically minimal missing proposition would
instead be one compatible witness:

```lean
∃ x : E.Extension,
  χ.cohomologicalAction.action (E.projector x) = e.operator
```

## The compactification lift before that endpoint

Let `γ` be the generic finite-group or subgroup averaging projector.  The
relevant diagram is

```text
                         restriction
  compactified algebra  ------------->  generic algebra
          Π              |------------>       γ
          |
          | cohomological action
          v
      End(H*)
       e.operator
```

The problem is to find a compactified idempotent `Π` over `γ` and then prove
that its action is the prescribed operator.  It should not be represented by
a global algebra map from the generic algebra back to the compactified
algebra: such a section would assert that every generic correspondence
extends and is much stronger than the projector-specific claim.

Two narrower algebraic bridges are now formal.  First,
`AlgebraProjectorClosure` records a raw compactified closure `Π` satisfying
only `restriction Π = γ`.  Its convolution defect

```lean
Π * Π - Π
```

is proved to restrict to zero. This places the defect in the kernel of the
supplied restriction map. With the separately supplied
`ChowLocalizationHypotheses i restriction.toLinearMap`, the new
`ChowLocalization.convolutionDefect_mem_range` identifies it with an element
of the supplied boundary image. Instantiating these maps as the geometric
Chow localization sequence remains open, and no defect-vanishing theorem
follows from exactness. The zero-defect witnesses form exactly the subtype from which an
`AlgebraProjectorExtension` can be constructed.

Second, `CompactifiedDeckGraphComparison` treats the stronger situation in
which the deck action itself and its graph-algebra realization have already
been extended, and the generic--compactified restriction square commutes on
`ℚ[G]`.  In that case every group-algebra idempotent maps directly to a
compactified idempotent with the correct restriction; its defect is zero by
multiplicativity.  This is a projector-specific sufficient construction, not
a section of the entire generic correspondence algebra.  The remaining
geometric problem is to construct that square in an actual Chow model.

An upstream source proposition is boundary avoidance

```lean
P_boundary :=
  ∀ i, ¬ collisionNoetherDifferentIdeal R A ≤ P i
```

and the adjacent target is `Nonempty E.Extension`.  The current implication
from inertia saturation to this target is a field of
`CompactifiedSubgroupProjectorExtension`; it packages the still-unproved
cycle-extraction, support, refined-convolution, and purity/gluing comparison.

## Active codimension-one boundary endpoint

The self-contained conjugate boundary-separation layer constructs canonical
conjugate normalization legs and pulls the
marked visible boundary back to the common normal-closure normalization.
For a nontrivial subgroup, `fixedMovingBoundaryIdeal` adds its fixed-locus
ideal to all boundary ideals of sheets it moves.
`ConjugateBoundarySeparation` says this sum lies in no height-one prime.
Given the separately named center and ramification realizations and formal
unramifiedness of the marked visible morphism, Lean proves
`NoCodimensionOneRamification`.  It does not prove the separation hypothesis
or promote that local conclusion to global étaleness.  Separate wrappers now
feed the resulting empty ramified-point family into the existing selector and
subgroup-projector extension criteria; those wrappers still take the actual
purity/gluing packages as inputs.  The active proof spine stops at this
codimension-one statement and does not include the broader historical
normalization-triviality prototype.

There is nevertheless a more precise source chain for a *one-way*, concrete
compactification theorem under additional hypotheses:

```text
codimension-one unramified finite étale cover of a dense open
  -- Stacks 0H2W, under regular locally Noetherian boundary hypotheses
      --> finite étale cover of the compactification
  -- Stacks 0BQF, under its punctured strict-henselian connectedness hypotheses
      --> extension of deck transformations
  -- Stacks 0FG3 / 0FG0 plus the finite-group averaging calculation
      --> graph-average Chow idempotent
```

Tags `0EY6` and `0EY7` describe related extension mechanisms rather than
interchangeable proofs of the first arrow: `0EY6` constructs a finite
reflexive-algebra extension under depth-two hypotheses and needs local
freeness for étaleness, while `0EY7` assumes purity at every omitted local
ring.  None applies automatically to a singular compactification.

Tag `0BQF` proves full faithfulness of restriction; extending an automorphism
uses it for the automorphism and its inverse.  Tags `0FG3` and `0FG0` supply
correspondence composition and graph functoriality in the smooth projective
setting.  Idempotence of the normalized graph average is the rational
finite-group corollary, not the literal statement of either tag.  This chain
would prove the existence direction needed here only after the concrete
cover, compactification, action, and restriction comparisons are constructed.
It does not prove the current abstract equivalence

```lean
Nonempty E.Extension ↔ ∀ i, inertiaSaturatedAtBaseClass ...
```

and the global cover theorem requires unramifiedness at every relevant
boundary point.  A condition at one selected sheet cannot be substituted
without proving the conjugacy/intermediate-cover comparison.

The first two selected conclusions now have explicit interfaces in
`Inputs/FiniteEtaleExtension.lean`: an actual extension witness with separate
existence, and bijectivity of its actual automorphism restriction map with
conditional deck-action transport. The source hypotheses above are production
obligations, not hidden assumptions discharged by those definitions.

At the level of cycles, Stacks Tags `02RA` and `02RX` give only a raw lift:

```text
generic Chow class lifts to the compactification
  -> its idempotence defect is supported on the boundary.
```

The conditional boundary-image implication is now formal in
`Inputs/ChowLocalization.lean`. It takes rational-linear exactness and
surjectivity explicitly, and uses a separately supplied algebra restriction
to obtain compatibility with correspondence composition. Applying the
integral source sequence requires its geometric hypotheses, rationalization,
and map identification; Tags `02RA` and `02RX` do not supply the multiplicative
comparison or show that the boundary defect is zero. Thus the compactification gap should be tracked as
three separate tasks:

1. extend the finite étale cover and its deck action;
2. construct an idempotent graph average (or correct a boundary-supported
   defect);
3. identify the resulting cohomological action with `e.operator`.

Wildeshaus, *Intermediate extension of Chow motives of Abelian type*,
Theorem 0.1(d), extends an idempotent on the relevant direct factor of a
proper smooth Kuga-family motive to its motivic intermediate extension in the
paper's neat pure-Shimura/Baily--Borel setting and under its technical
Shimura-datum hypothesis.  Realization compatibility is a separate theorem in
that paper.  This is a plausible route to a publishable conditional or
special-case theorem if the intended family and the repository's abstract
Chow model are identified with that setting; it is not a general discharge of
`CompactifiedSubgroupProjectorExtension` or of the equality with `e.operator`.
The G0 comparison currently defers this branch while assessing geometric
class-generation mechanisms in the smooth projective setting. The elliptic
seed and its finite-etale-covered subclass remain optional worked examples.

For the near-term Lean architecture, the source-backed interface should ask
first for the implication

```lean
(∀ i, inertiaSaturatedAtBaseClass ...) → Nonempty E.Extension
```

rather than requiring an if-and-only-if whose reverse direction none of the
identified compactification sources supplies.

## What is inherited from the Jacobian-collision project

The Jacobian repository does not begin with a bundled finite-étale cover.
Its `PolynomialNormalizedCover` packages a marked normal closure, module
finiteness of the two integral-closure models, and an open immersion of the
visible affine sheet.  It then keeps the arrows

```text
finite normalized cover
  -> no codimension-one ramification
  -> étale normalization                 [branch-purity input]
  -> trivial normal-closure extension      [base-specific rigidity input]
```

separate.  In the optional planar research spine, the last two arrows are
installed as project axioms `branchPurityA2` and
`affinePlaneFiniteEtaleRigidity`; they are not proved by the finite-cover
record.  The active degree-two paper does not use that normalization spine.

The Hodge files `Normalization/Model.lean`, `NormalClosure.lean`,
`ValuationInertia.lean`, and `InertiaDiagram.lean` already contain the
presentation-independent version of this architecture.  Copying the planar
cover record again would therefore add no theorem.

In particular, `NormalClosureData` itself packages `IsNormalClosure K L N`,
`FiniteDimensional K L`, and `FiniteDimensional K N`.  It derives normality
from the normal-closure witness and finiteness of its Galois group from the
finite-dimensional field data; `NormalClosureData.isGalois_of_isSeparable`
derives `IsGalois K N` from `Algebra.IsSeparable K L`. The old `isGalois`
name remains a perfect-field compatibility specialization.
No second normality or Galois hypothesis belongs in the sheet spine.  The
derived `galoisGroup` and `intermediateFixingSubgroup` index `G/H`, while
`normalClosureFiniteDeckAction` supplies the canonical deck action on the
affine normal-closure normalization.

The normal-closure-to-sheet comparison is multiplicative as well.  Lean
constructs algebra maps

```text
N ⊗[K] L  --normalClosureTensorToGenericSheets-->  N^(G/H)
    | normalClosureTensorDiagonal                         | ev_base
    v                                                     v
    N  -------------------------------------------------> N
```

and proves
`normalClosureBaseSheetAugmentation_comp_tensorToGenericSheets`, i.e. that
the two composites are equal. For separable `L/K` the top arrow is upgraded
to an algebra equivalence, with the same augmentation square.  This is the
honest multiplicative normal-closure bridge; it does not create a map from
the pointwise sheet algebra to `ℚ[G]`.

The roles must not be conflated.  Normality says that the conjugate embeddings
extend inside the same `N`, so one Galois group controls all sheets; it says
nothing about that group being abelian.  The identity
`normalClosureNormalizationSchemeIso_hom_comp_toBase` holds because every
Galois automorphism fixes `K` and hence the `B`-scalars along the scalar tower,
not because two group elements commute.  The function algebra on `G/H` is
commutative by its pointwise product.  The group/convolution algebra and the
ambient Chow-correspondence algebra remain potentially noncommutative.

One construction had not been exposed on the Hodge side.  The Jacobian
boundary code observes that a Galois automorphism of `N / K` restricts to an
automorphism of the integral closure of `B` in `N`.  This has now been
packaged scheme-theoretically as

```lean
normalClosureFiniteDeckAction :
  Gal(N / K) →*
    Aut_{Spec B}(Norm_N(Spec B)).
```

in `Boundary/Normalization/DeckAction.lean`.  This fills the normalization
deck-action morphism without a purity assumption and can be fed directly to
the finite-group graph-projector calculus.  It removes the need to supply an
abstract deck action when the scheme in question is the affine
normal-closure normalization.

Here `FiniteDeckAction` means an action of a finite group by automorphisms;
it does not assert that the normalization's structure map is finite étale.
The Galois-collision decomposition later requires finiteness and étaleness of
that map, plus an explicit torsor/coproduct comparison, as separate inputs.

This port also exposes a distinction that must not be suppressed in the gap
statement.  There are currently three different algebras in play:

```text
pointwise functions on generic sheets     (characteristic-function selector)
convolution/group algebra of deck maps    (normalized graph average)
compactified Chow correspondences         (the desired geometric projector).
```

The commutative-algebra maps between the normalization and selector levels
are now formal.  First,

```lean
intermediateNormalizationEquivFixedRing :
  IntCl_B(L) ≃ₐ[B] (IntCl_B(N))^H
```

identifies the marked intermediate normalization with the invariant ring.
Second,

```lean
collisionToGenericSheets :
  L ⊗[K] L →ₐ[K] (G / H → N)
```

is defined using chosen quotient representatives and sends
`Algebra.FormallyUnramified.elem K L` exactly to the singleton
base-sheet selector.  This proves the projector comparison without assuming
tensor splitting. Separately, under `Algebra.IsSeparable K L`, Lean proves that the
base-changed evaluation map `N ⊗[K] L → (G / H → N)` is bijective and packages
it as `normalClosureTensorGenericSheetsEquiv`.  Base-sheet evaluation is an
algebra homomorphism, and
`normalClosureBaseSheetAugmentation_comp_tensorToGenericSheets` states that
its composite with the base-changed evaluation map is exactly the
tensor-diagonal algebra map.  This last equality is the multiplicative
augmentation square; none of these declarations factors through `ℚ[G]`.

At a selected prime `Q` of the normal-closure normalization, the exact
ring-theoretic subgroup used by Stacks is now formalized as

```lean
primeInertiaSubgroup Q =
  {g | g • Q = Q ∧ ∀ x, g • x - x ∈ Q}.
```

Lean also proves the unique-prime statement

```lean
eq_of_under_primeInertiaSubgroup_eq :
  Q'.under S^(I_Q) = Q.under S^(I_Q) → Q' = Q.
```

It uses only finite-group invariant-prime transitivity and the containment of
prime inertia in the stabilizer; it needs no domain, height-one, Noetherian,
DVR, or unramifiedness assumption.  This closes the unique-prime-over-`q_I`
component of an internal DVR proof.  It does not prove that the fixed-inertia
map is unramified.

The normalization specialization is `normalizationPrimeInertiaGroup`, based
on `FullInvariantNormalizationRing = S^G`.  The proposition
`NormalizationPrimeInertiaFixedRingUnramifiedAt Q` names the exact local
formal-unramifiedness conclusion still consumed by Lean.  Tag `0BST` proves
the stronger statement that `S^G → S^(I_Q)` is étale at the exact contraction
`q_I = Q ∩ S^(I_Q)`, but that theorem is not in Mathlib.  For the marked finite
normal closure, when `L/K` is separable and the affine base is
integrally closed in it,
`baseEquivFullInvariantNormalizationRing` formally identifies that source
ring with `B`; without these hypotheses the source is generally the
normalization of `B` in `K`, not `B`.

The valuation inertia already present in `Diagram` is deliberately kept
separate.  The ported Jacobian lemma proves only

```lean
Diagram.valuationInertia_le_normalizationPrimeInertiaGroup :
  I_val ≤ I_Q.
```

This is enough to verify that valuation inertia acts trivially at its center,
but by itself it is in the wrong direction for replacing a hypothesis
`I_val ≤ H` by the prime-inertia hypothesis `I_Q ≤ H` required by the
fixed-ring descent.  `LocalizationBridge.lean` now supplies the reverse
direction.  `HasValuationLocalizationAt` records a compatible identification
of the centered valuation ring with the localization at `Q`, and
`ValuationLocalizationAt.primeInertia_le_valuationInertia` proves
`I_Q ≤ I_val` by extending a prime stabilizer to the localization and
comparing residue actions.

The localization datum and the containment needed by the main path are
derived from the existing diagram under the single additional hypothesis
`[IsNoetherianRing B]`:

```lean
Diagram.hasValuationLocalizationAt_of_isNoetherianRing
Diagram.normalizationPrimeInertia_le_of_valuationInertia_le_of_isNoetherianRing
```

Indeed, the finite normalization ring is then Noetherian and normal; its
localization at the supplied height-one prime is a one-dimensional normal
Noetherian local domain, hence a valuation ring.  The centered local map into
the diagram's valuation ring is an isomorphism by maximality of valuation
subrings in the common fraction field.  The minimal Noetherian proof path uses
only

```text
I_Q ≤ I_val ≤ H  ->  I_Q ≤ H.
```

The separately recorded equality `I_val = I_Q` combines this reverse
containment with the Jacobian-inherited forward containment and is an optional
comparison corollary, not a dependency of the descent endpoint.  Without
Noetherianity (or a direct localization realization),
`PrimeInertiaComparisonAt` remains a generic compatibility interface;
centeredness alone is not enough.  It is not an exposed premise of the
intended Noetherian endpoint.

Tag `09EH` gives an alternative local route in its DVR setting: a DVR
base, a finite Galois field extension, its integral closure, and a selected
maximal ideal.  It identifies the inertia fixed ring with the integral
closure in the inertia fixed field and proves the selected localization
étale.  The Lean localization bridge proves the height-one identification and
the needed containment `I_Q ≤ I_val`; it does not prove unramifiedness of the
inertia-fixed map.  Equality `I_val = I_Q` follows only after adding the
independent forward containment.  Formalizing the local fixed-inertia
unramifiedness consequence remains the next normalization step.  Tag `09EH`
still does not establish global étaleness over an arbitrary affine base.

The former dimension mismatch in the downstream helper is now removed.
`fixedRing_isUnramifiedAt_of_inertia_le_localized` contracts `Q` to
`q_H \subset S^H` and `q_I \subset S^I`, constructs the induced local map
`(S^H)_{q_H} \to (S^I)_{q_I}`, proves that its maximal ideals lie over one
another, and runs the Dedekind descent there.  Its Dedekind hypothesis is only
on `(S^H)_{q_H}`, so it is compatible with a higher-dimensional fixed ring.
The original `fixedRing_isUnramifiedAt_of_inertia_le` is retained as a
global-Dedekind compatibility wrapper.  This closes the localization
plumbing.  Moreover, `fixedPoints_primeHeight_under_eq_one` proves the
required height transfer for finite group actions by an invariant-theoretic
going-down argument, and
`fixedSubgroupNormalizationRing_localization_isDiscreteValuationRing` shows
that the local Dedekind hypothesis is automatic for the finite
normal-closure normalization over a Noetherian affine base.  The status split
is therefore: unique-prime, localization, containment, and local descent are
formal; the fixed-inertia unramifiedness conclusion is open as a compiled Lean
theorem; the forward containment and two-sided inertia equality are optional
comparisons.  These local algebra lemmas do not themselves prove the open
input or any compactification-purity statement.
`PrimeInertiaDescent.lean` now records the exact composite endpoint:
`normalizationFixedRing_isUnramifiedAt_of_primeInertia_le` consumes the
literal `NormalizationPrimeInertiaFixedRingUnramifiedAt` premise, and
`Diagram.fixedRing_isUnramifiedAt_of_valuationInertia_le` first converts
`I_val ≤ H` to `I_Q ≤ H`.  Both conclusions remain over the full invariant
ring `S^G`; transport to `B` is a separate operation and is not assumed here.

The first projector extends across an integral model only when the selected
generic components remain clopen; inertia saturation is the local criterion
for that descent problem.  The second projector already exists on the affine
normal-closure normalization for every subgroup, because every Galois
automorphism preserves the integral closure and hence has a global graph.
Its existence therefore cannot be equivalent to `I <= H`.  The sibling
Jacobian code does not identify the pointwise sheet algebra with the graph
convolution algebra, and `SheetActionCompatibility` in
`Boundary/AveragingAction.lean` compares their actions only; it is not an
algebra isomorphism or a compactification theorem.

Accordingly, the remaining comparison problem is no longer the generic
collision-to-sheet-selector map.  It is the passage from the selector or
graph average to an actual compactified Chow correspondence, followed by
identification of its cohomological action.  The abstract
`RationalDegreeTransfer` calculation proves that `(1/d) q^* q_*` is
idempotent once the degree formula is supplied, but Mathlib does not yet
construct the required Chow pullback and pushforward maps.  The mere
existence of the affine graph average must not be advertised as an
inertia-controlled extension theorem.

It does **not** extend that action to an independently chosen proper or
projective compactification, identify a Chow-correspondence restriction map,
or prove the prescribed cohomological action.  Those remain the next
morphisms after this port.

The sibling lemma does **not** prove a full equivalence between local
ramification and nontrivial inertia.  Its structure
`ConjugateRamificationRealization` explicitly assumes that the
group-theoretic inertia index equals the geometric ramification index.  It
then uses only

```text
unramified at the selected prime
  -> geometric ramification index = 1
  -> group-theoretic inertia index = 1.
```

The more concrete sibling lemma `inertia_sub_mem_ramifiedPrime` is reusable
but points in a different direction: an element already known to lie in the
valuation-theoretic inertia group acts trivially modulo the centered prime.
It does not deduce nontrivial inertia from a ramified local ring.  That fact
is useful for residue-action comparisons, but it is not the missing premise
of the present extension-existence argument and has therefore not been used
as a substitute for the explicit index-realization input.

The Hodge repository already contains the same one-way argument in
`Boundary/Normalization/InertiaDiagram.lean`.  It must not be cited as if it
discharged `HeightOneInertiaRealization`, whose field is the stronger
equivalence

```lean
(¬ Algebra.IsUnramifiedAt B P) ↔ inertiaIndexAtSheet I H baseSheet ≠ 1.
```

For extension existence, however, the full equivalence is unnecessary.  The
proved Lean chain is now

```text
collision different avoids P
  -> unramified at P
  -> geometric ramification index = 1
  -> base-sheet inertia index = 1
  -> the base sheet is inertia-saturated.
```

The first arrow is
`collisionDifferentDetectsRamificationAt_of_essFiniteType`, the second is
Mathlib's `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`, and the last two
use `ConjugateRamificationRealization` and
`inertiaIndexAtBaseSheet_eq_one_iff_saturated`.  The assembled theorem is
`NormalizationInertia.Diagram.baseClass_inertiaSaturated_of_different_not_le`
in `Boundary/Normalization/ExtensionBridge.lean`.

Therefore:

- retain `ConjugateRamificationRealization` as an explicit input; the sibling
  project also assumes it;
- do not require the stronger `HeightOneInertiaRealization` merely to prove
  the extension-existence direction;
- retain `HeightOneInertiaRealization` for any claimed *if and only if* until
  the reverse local implication is proved under precise hypotheses.

## Scope boundary

The repository now has fixed-model and indexed-family schemas expressing the
cycle-class target, plus a proved class/graph-projector equivalence under
explicit block construction and detection maps. The compatibility identifying
`(p,p)` classes with graph operators that are Hodge morphisms is instantiated
in finite degree zero; the general interface remains separate. The concrete finite split degree-zero
Chow/Betti/Hodge model and both geometric block maps are now constructed.
Their Hodge description is the explicitly verified effective type-`(0,0)`
structure on actual Betti complexification, identified geometrically by
the cited degree-zero specialization, not a formalized general analytic
Hodge theorem. Higher-dimensional and all-codimension models remain open.

The marked Galois sheet calculation now resolves the former source-algebra and
operator-shape questions: the residual object is the augmentation ideal
`ker(ev_base) = (1 - q)`, the regular source action is multiplicative, and the
normal-closure augmentation bridge is an equality of algebra-map composites.
The residual corner
with unit `1-q` gives the genuine product-algebra split
`A_H ≃ₐ[ℚ] ℚ × E_H^corner`; selector multiplication is block diagonal
there and graph-shaped in the distinct constant-unit linear coordinates.  The
general residual realization remains linear; its constructed finite split
instance also preserves multiplication as Chow intersection and Betti cup
product. The universal algebra `U = ℚ × ℚ`
canonically presents the chosen generic, compactified, and cohomological
idempotents, while `palomarTargetSquare` gives the final equality of
algebra-homomorphism composites.  A full map from `A_H` to a generic
correspondence algebra is optional and stronger; the auxiliary direct-only
sheet linearization is not part of this route.
The conditional
endpoint detects the lower-left class from an explicit comparison square and,
under surjectivity, derives the exact graph action.  Its source and ambient
algebras are correctly separated. The split-span coefficient construction
above now supplies an actual-source comparison square for the two-point
test. The split marked-sheet checkpoint now adds the actual torsor geometry,
Chow-motivic residual map, geometric shear, and Hodge realization square
for the canonical negative fundamental class; the earlier block already
supplies actual Chow detection. These are not general Chow/Hodge realization
or class-dependent coverage results. No strong replacement instance is
present, and the existing class-dependent witness type still does not bundle
a genuine cover or normal closure. Such a generation theorem may be stronger
than Hodge itself. The finite split degree-zero case supplies a verified
known model, not a new case of the general conjecture.
